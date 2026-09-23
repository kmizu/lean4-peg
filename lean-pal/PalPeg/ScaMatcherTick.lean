import PalPeg.ScaMatcherRun
import PalPeg.ScaMatcherLife

/-!
# The main loop through ticks: segments, waits, and the report deadline

The matcher's main loop runs `seg` segments of the verifier orbit `Z j` while letters arrive, one
per tick of 2048 steps. This file carries a state description across single steps and letter
arrivals (`Cur`): the head VM is either waiting at a loop head whose next letter has not arrived,
or inside a segment started at a loop head `Z j`.

Timing is measured against a reference `(gr, pr)`: the global step slot `gr` at which the VM last
stopped waiting (or started the loop) and the potential `pr` there. Since the VM does not idle
after the reference, `g + 35·pr ≤ gr + 35·Φ(Z j) + e` (each segment of `n` steps raises `35·Φ` by at
least `n`). `RefOK` says that every later report is reached, with its `match` step, before the end
of the tick of its last letter; after a wait at `L` letters it holds by the potential arithmetic
(`refOK_wait`).
-/
set_option autoImplicit false
namespace PalPeg.ScaMatcherTick
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe PalPeg.ScaMatcherLoop PalPeg.ScaMatcherRun

section Defs
variable (x T : List (Fin 2)) (s p₁ r : ℕ)

/-- The verifier orbit the loop follows (`k = 8`). -/
abbrev Z (j : ℕ) : PalPeg.VState := PalPeg.GSDrained.orbit (x.take s) (x.drop s) 8 p₁ r T j

/-- The potential at orbit index `j`. -/
abbrev Φ (j : ℕ) : ℕ := PalPeg.Phi 8 (Z x T s p₁ r j).1

/-- The segment started at `Z j` reports (the state after `Z j` carries a `match` event). -/
def isRep (j : ℕ) : Bool :=
  PalPeg.GSDrained.matchEvent (x.take s) (x.drop s) (Z x T s p₁ r (j + 1))

/-- The text length at which that report's occurrence ends. -/
def endOf (j : ℕ) : ℕ := (Z x T s p₁ r (j + 1)).1.pos + (x.length - s)

/-- **The reference is good**: every report from `j` on is reached, with its `match`, inside the
tick of its last letter. -/
def RefOK (gr pr j : ℕ) : Prop :=
  ∀ j', j ≤ j' → isRep x T s p₁ r j' = true →
    gr + 35 * (Φ x T s p₁ r j' - pr) + 11 < 2048 * (endOf x T s p₁ r j' + 1)

end Defs

theorem vs_orbit (x T : List (Fin 2)) (s p₁ r j d : ℕ) :
    (VS x T 8 s p₁ r)^[d] (Z x T s p₁ r j) = Z x T s p₁ r (j + d) := by
  rw [VS, PalPeg.GSDrained.iterate_orbit, Nat.add_comm]

theorem vs_orbit_one (x T : List (Fin 2)) (s p₁ r j : ℕ) :
    VS x T 8 s p₁ r (Z x T s p₁ r j) = Z x T s p₁ r (j + 1) :=
  vs_orbit x T s p₁ r j 1

theorem phi_mono (x T : List (Fin 2)) (s p₁ r : ℕ) (hp : 0 < p₁) {j j' : ℕ} (h : j ≤ j') :
    Φ x T s p₁ r j ≤ Φ x T s p₁ r j' := by
  obtain ⟨i, rfl⟩ : ∃ i, j' = j + i := ⟨j' - j, by omega⟩
  have := PalPeg.GSDrained.phi_iterate (u := x.take s) (v := x.drop s) (T := T) (k := 8) (r := r)
    (by norm_num) hp i (Z x T s p₁ r j)
  rw [PalPeg.GSDrained.iterate_orbit] at this
  show PalPeg.Phi 8 (Z x T s p₁ r j).1 ≤ PalPeg.Phi 8 (Z x T s p₁ r (j + i)).1
  rw [Nat.add_comm j i]
  exact le_trans (Nat.le_add_right _ _) this

/-! ## Letter arrivals -/

theorem loopRel_append {lx s p₁ r k : ℕ} {pe : Bool} {pos q c : ℕ} {v : HVM} (a : Fin 2)
    (h : LoopRel lx s p₁ r k pe pos q c v.pos) : LoopRel lx s p₁ r k pe pos q c (v.append a).pos := by
  unfold LoopRel at h ⊢
  simp only [append_pos_ne v a (show "Origin" ≠ OE by decide), append_pos_ne v a (show "Cut" ≠ OE by decide),
    append_pos_ne v a (show "End" ≠ OE by decide), append_pos_ne v a (show "First" ≠ OE by decide),
    append_pos_ne v a (show "KFirst" ≠ OE by decide), append_pos_ne v a (show "Reach" ≠ OE by decide),
    append_pos_ne v a (show "P" ≠ OE by decide), append_pos_ne v a (show "A" ≠ OE by decide),
    append_pos_ne v a (show "B" ≠ OE by decide), append_pos_ne v a (show "Walk" ≠ OE by decide),
    append_pos_ne v a (show "U" ≠ OE by decide)]
  exact h

theorem atHead_append {x T : List (Fin 2)} {m k s p₁ r : ℕ} {pe ok : Bool} {z : PalPeg.VState}
    {v : HVM} (h : AtHead x T m k s p₁ r pe ok z v) (hm : m < T.length) :
    AtHead x T (m + 1) k s p₁ r pe ok z (v.append T[m]) where
  ctl := h.ctl
  word := by
    show v.word ++ [T[m]] = _
    rw [h.word, List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.append_assoc]
  rel := loopRel_append _ h.rel
  dead := h.dead
  cut := h.cut
  sx := h.sx
  qv := h.qv
  cs := h.cs
  arr := by have := h.arr; omega
  tl := hm

/-! ## Reports on the orbit, and the reference after a wait -/

theorem gsNextQ_lt {k p₁ r q : ℕ} (hp : 0 < p₁) (hq : 0 < q) : PalPeg.gsNextQ k p₁ r q < q := by
  unfold PalPeg.gsNextQ; split_ifs <;> omega

/-- A report is a hit completing `v`: the state before has `q = |v| − 1` at the same `pos`. -/
theorem rep_shape (x T : List (Fin 2)) (s p₁ r j : ℕ) (hp : 0 < p₁) (hv : 0 < x.length - s)
    (hq : (Z x T s p₁ r j).1.q ≤ x.length - s) (hrep : isRep x T s p₁ r j = true) :
    (Z x T s p₁ r j).1.pos = (Z x T s p₁ r (j + 1)).1.pos ∧
      (Z x T s p₁ r j).1.q + 1 = x.length - s := by
  have hvl : (x.drop s).length = x.length - s := by simp
  unfold isRep at hrep
  simp only [PalPeg.GSDrained.matchEvent, decide_eq_true_eq] at hrep
  obtain ⟨hq1, -⟩ := hrep
  simp only [Z, PalPeg.GSDrained.orbit_succ, PalPeg.vStep_fst] at hq1 hq ⊢
  rw [hvl] at hq1
  set st := (PalPeg.GSDrained.orbit (x.take s) (x.drop s) 8 p₁ r T j).1 with hst
  unfold PalPeg.scanStep at hq1 ⊢
  split_ifs at hq1 ⊢ with h1 h2 <;> dsimp only at hq1 ⊢
  · exfalso
    rw [hvl] at h1
    have := gsNextQ_lt (k := 8) (r := r) hp (show 0 < st.q by omega)
    omega
  · exact ⟨rfl, by simpa using hq1⟩
  · exfalso
    rw [hvl] at h1
    have := PalPeg.GSReportDeadline.gsNextQ_le 8 p₁ r st.q
    omega

/-- **After a wait**: the VM waits at a loop head `Z j` with `pos + q = L` (its next letter is
`L + 1`) and restarts at the first slot of tick `L + 1`; every later report then makes its
deadline. -/
theorem refOK_wait (x T : List (Fin 2)) (s p₁ r j L : ℕ) (hp : 0 < p₁) (hv : 0 < x.length - s)
    (hq : ∀ i, (Z x T s p₁ r i).1.q ≤ x.length - s)
    (hL : (Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q = L)
    (hqj : (Z x T s p₁ r j).1.q < x.length - s) :
    RefOK x T s p₁ r (2048 * (L + 1)) (Φ x T s p₁ r j) j := by
  intro j' hj' hrep
  obtain ⟨hpos, hq'⟩ := rep_shape x T s p₁ r j' hp hv (hq j') hrep
  have hmono := phi_mono x T s p₁ r hp hj'
  have hposm : (Z x T s p₁ r j).1.pos ≤ (Z x T s p₁ r j').1.pos :=
    PalPeg.GSDrained.orbit_pos_mono hj'
  unfold endOf
  rw [← hpos]
  simp only [Φ, PalPeg.Phi] at hmono ⊢
  omega

/-! ## One segment, as the tick layer sees it -/

theorem stepMatch_patternSize {v w : HVM} (h : stepMatch v = some w) : w.patternSize = v.patternSize := by
  obtain ⟨c, e, hctl, -⟩ := ScaHeadRun.stepMatch_ctl h
  obtain ⟨-, rfl⟩ := stepMatch_some hctl h
  rfl

theorem iterStep_patternSize : ∀ (n : ℕ) {v w : HVM}, iterStep n v = some w →
    w.patternSize = v.patternSize
  | 0, v, w, h => by simp [iterStep] at h; rw [h]
  | n + 1, v, w, h => by
    simp only [iterStep] at h
    cases hs : stepMatch v with
    | none => simp [hs] at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      rw [iterStep_patternSize n h, stepMatch_patternSize hs]

theorem loopRel_inj {lx s p₁ r k : ℕ} {pe : Bool} {pos q c pos' q' c' : ℕ} {π : String → ℤ}
    (h : LoopRel lx s p₁ r k pe pos q c π) (h' : LoopRel lx s p₁ r k pe pos' q' c' π)
    (hs : s ≤ pos) (hs' : s ≤ pos') : pos = pos' ∧ q = q' := by
  obtain ⟨-, -, -, -, hP, hA, -⟩ := h
  obtain ⟨-, -, -, -, hP', hA', -⟩ := h'
  constructor <;> omega

theorem phi_lt_add (x T : List (Fin 2)) (s p₁ r j d : ℕ) (hp : 0 < p₁) (hd : 1 ≤ d) :
    Φ x T s p₁ r j < Φ x T s p₁ r (j + d) := by
  have := PalPeg.GSDrained.phi_iterate (u := x.take s) (v := x.drop s) (T := T) (k := 8)
    (r := r) (by norm_num) hp d (Z x T s p₁ r j)
  rw [PalPeg.GSDrained.iterate_orbit] at this
  show PalPeg.Phi 8 (Z x T s p₁ r j).1 < PalPeg.Phi 8 (Z x T s p₁ r (j + d)).1
  rw [Nat.add_comm j d]
  exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hd) this

section Seg
variable (ρ : String → Bool) (x T : List (Fin 2)) (s p₁ r : ℕ) (pe : Bool)

/-- The segment from the loop head `v` at `Z j`, on `L` letters: `n` guarded steps to the loop
head `w` at `Z (j + d)`, paid by the potential, with its output and `match` state. -/
def SegOK (L j : ℕ) (v : HVM) (d n : ℕ) (w : HVM) : Prop :=
  1 ≤ d ∧ d ≤ 2 ∧ 0 < n ∧ n + 35 * Φ x T s p₁ r j ≤ 35 * Φ x T s p₁ r (j + d) ∧
  iterS x.length ρ n v = some w ∧
  (∃ ok', AtHead x T L 8 s p₁ r pe ok' (Z x T s p₁ r (j + d)) w) ∧
  w.outputs = v.outputs ++
    (if isRep x T s p₁ r j = true then [((endOf x T s p₁ r j : ℕ) : ℤ)] else []) ∧
  (isRep x T s p₁ r j = true →
    ∃ n₁ u, n₁ ≤ 11 ∧ n₁ < n ∧ iterS x.length ρ n₁ v = some u ∧ u.outputs = v.outputs ∧
      (∃ c, u.ctl = .pending c (.«match» "B")) ∧
      u.pos "B" = x.length + endOf x T s p₁ r j) ∧
  (d = 2 → isRep x T s p₁ r (j + 1) = false)

variable {ρ x T s p₁ r pe}

/-- `seg`, on the orbit. -/
theorem segOK_of (hρ : Orient ρ) {L j ok} {v : HVM}
    (h : AtHead x T L 8 s p₁ r pe ok (Z x T s p₁ r j) v)
    (hen : (Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q < L)
    (hdl : PalPeg.GSReportDeadline.DeadlineInv (x.take s) (x.drop s) T (Z x T s p₁ r j))
    (hps : v.patternSize = x.length)
    (hnoper : pe = false → x.length - s < 8 * p₁) (hp1 : pe = true → 1 ≤ p₁) (hp : 0 < p₁) :
    ∃ d n w, SegOK ρ x T s p₁ r pe L j v d n w := by
  obtain ⟨d, n, w, ok', hd1, hd2, hphi, -, hrun, hat, hout, hmatch, hmid⟩ :=
    seg hρ x T L 8 s p₁ r (by norm_num) le_rfl pe ok _ v h hen hdl hps hnoper hp1
  rw [vs_orbit] at hphi hat
  rw [vs_orbit_one] at hout hmatch hmid
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp only [iterS, Option.some.injEq] at hrun
      subst hrun
      obtain ⟨hpq, hqq⟩ := loopRel_inj h.rel hat.rel h.cut hat.cut
      have hlt := phi_lt_add x T s p₁ r j d hp hd1
      simp only [Φ, PalPeg.Phi] at hlt
      rw [hpq, hqq] at hlt
      exact absurd hlt (lt_irrefl _)
    · exact h0
  refine ⟨d, n, w, hd1, hd2, hn, hphi, hrun, ⟨ok', hat⟩, ?_, ?_, ?_⟩
  · rw [hout]; rfl
  rotate_left
  · intro hd
    have hq := hmid hd
    by_contra hc
    have hc' : isRep x T s p₁ r (j + 1) = true := by simpa using hc
    have := rep_shape x T s p₁ r (j + 1) hp (by have := h.qv; omega) (le_of_eq hq) hc'
    omega
  · intro hr
    obtain ⟨n₁, u, h1, h2, h3, h4, h5, h6⟩ := hmatch hr
    refine ⟨n₁, u, h1, h2, h3, h4, h5, ?_⟩
    rw [h6]; unfold endOf; rw [Nat.cast_add, Nat.cast_sub h.sx]; ring

/-- A segment survives a letter arrival. -/
theorem segOK_append {L j : ℕ} {v : HVM} {d n : ℕ} {w : HVM}
    (h : SegOK ρ x T s p₁ r pe L j v d n w) (hL : L < T.length) :
    SegOK ρ x T s p₁ r pe (L + 1) j (v.append T[L]) d n (w.append T[L]) := by
  obtain ⟨hd1, hd2, hn, hphi, hrun, ⟨ok', hat⟩, hout, hmatch, hmid⟩ := h
  refine ⟨hd1, hd2, hn, hphi, iterS_append _ hrun, ⟨ok', atHead_append hat hL⟩, hout, ?_, hmid⟩
  intro hr
  obtain ⟨n₁, u, h1, h2, h3, h4, h5, h6⟩ := hmatch hr
  exact ⟨n₁, u.append T[L], h1, h2, iterS_append _ h3, h4, h5,
    by rw [append_pos_ne u _ (show "B" ≠ OE by decide)]; exact h6⟩

end Seg

/-! ## Where the `match` step of a segment is -/

theorem iterStep_mid {a b : ℕ} {v y z : HVM} (h1 : iterStep a v = some y)
    (h2 : iterStep (a + b) v = some z) : iterStep b y = some z := by
  rw [iterStep_add, h1, Option.bind_some] at h2; exact h2

theorem iterS_prefix {W : ℕ} {ρ : String → Bool} {n e : ℕ} {v w : HVM}
    (h : iterS W ρ n v = some w) (he : e ≤ n) :
    ∃ u, iterS W ρ e v = some u ∧ iterS W ρ (n - e) u = some w := by
  rw [show n = e + (n - e) by omega, iterS_add] at h
  cases hu : iterS W ρ e v with
  | none => rw [hu] at h; simp at h
  | some u => rw [hu, Option.bind_some] at h; exact ⟨u, rfl, h⟩

/-- A state whose pending event is a `match`. -/
def IsMatch (u : HVM) : Prop := ∃ c h, u.ctl = .pending c (.«match» h)

theorem step_outputs_match {u u' : HVM} (h : stepMatch u = some u') (hm : IsMatch u) :
    u'.outputs.length = u.outputs.length + 1 := by
  obtain ⟨c, h', hctl⟩ := hm
  obtain ⟨-, rfl⟩ := stepMatch_some hctl h
  simp [matchOut]

theorem step_outputs_nomatch {u u' : HVM} (h : stepMatch u = some u') (hm : ¬ IsMatch u) :
    u'.outputs = u.outputs := by
  obtain ⟨c, e, hctl, -⟩ := ScaHeadRun.stepMatch_ctl h
  obtain ⟨-, rfl⟩ := stepMatch_some hctl h
  cases e with
  | «match» h' => exact absurd ⟨c, h', hctl⟩ hm
  | _ => simp [matchOut]

theorem outputs_len_le {n : ℕ} {v w : HVM} (h : iterStep n v = some w) :
    v.outputs.length ≤ w.outputs.length :=
  (ScaMatcherLife.iterStep_outputs n h).length_le

/-- **The only `match` of a segment is its reported one.** -/
theorem match_unique {ρ : String → Bool} {x T : List (Fin 2)} {s p₁ r : ℕ} {pe : Bool}
    {L j : ℕ} {v : HVM} {d n : ℕ} {w : HVM} (hseg : SegOK ρ x T s p₁ r pe L j v d n w)
    {e : ℕ} {u : HVM} (he : e < n) (hu : iterStep e v = some u) (hm : IsMatch u) :
    isRep x T s p₁ r j = true ∧
      ∀ n₁ u₁, iterStep n₁ v = some u₁ → u₁.outputs = v.outputs → IsMatch u₁ → n₁ < n → e = n₁ := by
  obtain ⟨-, -, -, -, hrun, -, hout, -, -⟩ := hseg
  have hw := iterS_iterStep hrun
  have hlenw : w.outputs.length =
      v.outputs.length + (if isRep x T s p₁ r j = true then 1 else 0) := by
    rw [hout]; split_ifs <;> simp
  -- the step out of `u`
  have hrest := iterStep_mid hu (show iterStep (e + (n - e)) v = some w by
    rw [show e + (n - e) = n by omega]; exact hw)
  obtain ⟨u1, hu1, hrest'⟩ : ∃ u1, stepMatch u = some u1 ∧ iterStep (n - e - 1) u1 = some w := by
    rw [show n - e = (n - e - 1) + 1 by omega] at hrest
    simp only [iterStep] at hrest
    cases hs : stepMatch u with
    | none => rw [hs] at hrest; simp at hrest
    | some u1 => rw [hs, Option.bind_some] at hrest; exact ⟨u1, rfl, hrest⟩
  have hl1 := step_outputs_match hu1 hm
  have hvu := outputs_len_le hu
  have hu1w := outputs_len_le hrest'
  have hrep : isRep x T s p₁ r j = true := by
    by_contra hc
    rw [if_neg hc] at hlenw
    omega
  refine ⟨hrep, fun n₁ u₁ hu₁ ho₁ hm₁ hn₁ => ?_⟩
  rw [if_pos hrep] at hlenw
  have hlen₁ : u₁.outputs.length = v.outputs.length := by rw [ho₁]
  rcases Nat.lt_trichotomy e n₁ with hlt | heq | hgt
  · -- `u1` (step `e+1`) comes before or at `u₁`
    have := iterStep_mid (a := e + 1) (b := n₁ - (e + 1))
      (show iterStep (e + 1) v = some u1 by
        rw [iterStep_add, hu, Option.bind_some]; simp [iterStep, hu1])
      (show iterStep (e + 1 + (n₁ - (e + 1))) v = some u₁ by
        rw [show e + 1 + (n₁ - (e + 1)) = n₁ by omega]; exact hu₁)
    have := outputs_len_le this
    omega
  · exact heq
  · -- `u₁`'s own step comes before `u`
    have hrest₁ := iterStep_mid hu₁ (show iterStep (n₁ + (n - n₁)) v = some w by
      rw [show n₁ + (n - n₁) = n by omega]; exact hw)
    obtain ⟨u₁', hs₁, -⟩ : ∃ u₁', stepMatch u₁ = some u₁' ∧ True := by
      rw [show n - n₁ = (n - n₁ - 1) + 1 by omega] at hrest₁
      simp only [iterStep] at hrest₁
      cases hs : stepMatch u₁ with
      | none => rw [hs] at hrest₁; simp at hrest₁
      | some y => exact ⟨y, rfl, trivial⟩
    have hl₁ := step_outputs_match hs₁ hm₁
    have := iterStep_mid (a := n₁ + 1) (b := e - (n₁ + 1))
      (show iterStep (n₁ + 1) v = some u₁' by
        rw [iterStep_add, hu₁, Option.bind_some]; simp [iterStep, hs₁])
      (show iterStep (n₁ + 1 + (e - (n₁ + 1))) v = some u by
        rw [show n₁ + 1 + (e - (n₁ + 1)) = e by omega]; exact hu)
    have := outputs_len_le this
    omega

/-! ## The worker's side conditions from the guard -/

/-- **`SafeAt` gives the worker's `StepSide`**, except the `match` timing, supplied separately. -/
theorem stepSide_of_safe {W : ℕ} {ρ : String → Bool} {u : HVM} (hs : SafeAt W ρ u)
    (hmB : IsMatch u → u.len ≤ u.pos "B") : ScaWorkerLink.StepSide W ρ u where
  reads c a b hc := by
    have h := hs; simp only [SafeAt, hc] at h; exact ⟨h.1, h.2.1⟩
  available c h hc := by
    have h' := hs; simp only [SafeAt, hc] at h'; exact h'.1
  moves c ms hc h hcol hr hd := by
    have h' := hs; simp only [SafeAt, hc] at h'
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hcol
    exact h'.1 h (ScaWorkerLink.notBlind h i hi) hr hd
  matchB c h hc := by
    have h' := hs; simp only [SafeAt, hc] at h'
    exact ⟨h'.1, hmB ⟨c, h, hc⟩⟩

theorem stepMatch_word {v w : HVM} (h : stepMatch v = some w) : w.word = v.word := by
  obtain ⟨c, e, hctl, -⟩ := ScaHeadRun.stepMatch_ctl h
  obtain ⟨-, rfl⟩ := stepMatch_some hctl h
  rfl

theorem iterStep_word : ∀ (n : ℕ) {v w : HVM}, iterStep n v = some w → w.word = v.word
  | 0, v, w, h => by simp [iterStep] at h; rw [h]
  | n + 1, v, w, h => by
    simp only [iterStep] at h
    cases hs : stepMatch v with
    | none => simp [hs] at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      rw [iterStep_word n h, stepMatch_word hs]

theorem orient_of_safe {W : ℕ} {ρ : String → Bool} {u : HVM} (hs : SafeAt W ρ u) :
    ScaWorkerLink.orientStep u ρ = ρ := by
  unfold ScaWorkerLink.orientStep
  split
  · rename_i c e hc
    have h := hs; simp only [SafeAt, hc] at h
    cases e with
    | copy t s' => simp only [moveRev]; rw [← h.1]; exact Function.update_eq_self t ρ
    | _ => rfl
  · rfl

theorem atHead_len {x T : List (Fin 2)} {m k s p₁ r : ℕ} {pe ok : Bool} {z : PalPeg.VState} {v : HVM}
    (h : AtHead x T m k s p₁ r pe ok z v) : v.len = x.length + m := by
  simp only [HVM.len, h.word, List.length_append, List.length_take]
  rw [Nat.min_eq_left h.tl]; push_cast; ring

section Tick
variable (ρ : String → Bool) (x T : List (Fin 2)) (s p₁ r : ℕ) (pe : Bool)

/-- The loop's parameters, as the tick layer needs them. -/
structure Params : Prop where
  sx : s < x.length
  noper : pe = false → x.length - s < 8 * p₁
  p1 : pe = true → 1 ≤ p₁
  ppos : 0 < p₁
  sd : PalPeg.GSReportDeadline.ShiftDeadline (x.take s) (x.drop s) 8 p₁ r
  qle : ∀ i, (Z x T s p₁ r i).1.q ≤ x.length - s

/-- **The main loop at slot `g` with `L` letters**: waiting at `Z j`, or `e` steps into the
segment started at `Z j`, with the timing reference `(gr, pr)`. The outputs are the ends of the
reports passed so far, all at most `L`. -/
def Cur (L g : ℕ) (u : HVM) : Prop :=
  ∃ j v gr pr ok, AtHead x T L 8 s p₁ r pe ok (Z x T s p₁ r j) v ∧ v.patternSize = x.length ∧
    RefOK x T s p₁ r gr pr j ∧ pr ≤ Φ x T s p₁ r j ∧
    (∀ z ∈ u.outputs, z ≤ L) ∧
    (∀ j'', j'' < j → isRep x T s p₁ r j'' = true →
      ((endOf x T s p₁ r j'' : ℕ) : ℤ) ∈ v.outputs) ∧
    (((Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q = L ∧ u = v ∧ gr = 2048 * (L + 1) ∧
        pr = Φ x T s p₁ r j) ∨
     ((Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q < L ∧
       ∃ d n w e, SegOK ρ x T s p₁ r pe L j v d n w ∧ e < n ∧ iterS x.length ρ e v = some u ∧
         g + 35 * pr ≤ gr + 35 * Φ x T s p₁ r j + e ∧
         ((u.outputs = v.outputs ∧
            ∀ n₁ u₁, iterS x.length ρ n₁ v = some u₁ → IsMatch u₁ → e ≤ n₁) ∨
          (isRep x T s p₁ r j = true ∧
            u.outputs = v.outputs ++ [((endOf x T s p₁ r j : ℕ) : ℤ)]))))

variable {ρ x T s p₁ r pe}

/-- A loop head starts the tick layer: waiting (with its own reference) or a fresh segment. -/
theorem cur_of_head (hρ : Orient ρ) (hP : Params x T s p₁ r pe) {L g j gr pr : ℕ} {ok : Bool}
    {v : HVM} (hat : AtHead x T L 8 s p₁ r pe ok (Z x T s p₁ r j) v) (hps : v.patternSize = x.length)
    (href : RefOK x T s p₁ r gr pr j) (hpr : pr ≤ Φ x T s p₁ r j)
    (htime : g + 35 * pr ≤ gr + 35 * Φ x T s p₁ r j) (hvals : ∀ z ∈ v.outputs, z ≤ L)
    (hrec : ∀ j'', j'' < j → isRep x T s p₁ r j'' = true →
      ((endOf x T s p₁ r j'' : ℕ) : ℤ) ∈ v.outputs) :
    Cur ρ x T s p₁ r pe L g v := by
  have harr := hat.arr
  rcases Nat.lt_or_ge ((Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q) L with hlt | hge
  · obtain ⟨d, n, w, hseg⟩ := segOK_of (pe := pe) hρ hat hlt
      (PalPeg.GSReportDeadline.orbit_deadlineInv hP.sd j) hps hP.noper hP.p1 hP.ppos
    exact ⟨j, v, gr, pr, ok, hat, hps, href, hpr, hvals, hrec,
      Or.inr ⟨hlt, d, n, w, 0, hseg, hseg.2.2.1, rfl, by omega,
        Or.inl ⟨rfl, fun _ _ _ _ => Nat.zero_le _⟩⟩⟩
  · have hL : (Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q = L := by omega
    exact ⟨j, v, 2048 * (L + 1), Φ x T s p₁ r j, ok, hat, hps,
      refOK_wait x T s p₁ r j L hP.ppos (by have := hP.sx; omega) hP.qle hL hat.qv, le_rfl,
      hvals, hrec, Or.inl ⟨hL, rfl, rfl, rfl⟩⟩

/-- **One step of the main loop**: it exists, keeps the worker's side conditions and orientation,
and keeps `Cur`; the output grows only by the current letter count `L`, and then a report ends
at `L`. -/
theorem cur_step (hρ : Orient ρ) (hP : Params x T s p₁ r pe) {L g : ℕ} {u : HVM}
    (hc : Cur ρ x T s p₁ r pe L g u) (hg1 : 2048 * L ≤ g) (hg2 : g < 2048 * (L + 1)) :
    ∃ u', stepMatch u = some u' ∧ ScaWorkerLink.StepSide x.length ρ u ∧
      ScaWorkerLink.orientStep u ρ = ρ ∧ Cur ρ x T s p₁ r pe L (g + 1) u' ∧
      (u'.outputs = u.outputs ∨
        (u'.outputs = u.outputs ++ [(L : ℤ)] ∧
          ∃ j, isRep x T s p₁ r j = true ∧ endOf x T s p₁ r j = L)) := by
  obtain ⟨j, v, gr, pr, ok, hat, hps, href, hpr, hvals, hrec, hcase⟩ := hc
  rcases hcase with ⟨hL, rfl, hgr, hpr'⟩ | ⟨hlt, d, n, w, e, hseg, hen, hu, htime, hbook⟩
  · -- waiting at a loop head
    obtain ⟨ph, hctl⟩ := hat.ctl
    have hB : u.len ≤ u.pos "B" := by
      rw [atHead_len hat, hat.rel.2.2.2.2.2.2.1]; push_cast; omega
    have e1 := head_wait 8 (some pe) ok ph u hctl hB
    refine ⟨u, stepMatch_of_one e1, ?_, ?_, ⟨j, u, gr, pr, ok, hat, hps, href, hpr, hvals, hrec,
      Or.inl ⟨hL, rfl, hgr, hpr'⟩⟩, Or.inl rfl⟩
    · refine ⟨fun c a b hc => ?_, fun c h hc => ?_, fun c ms hc => ?_, fun c h hc => ?_⟩
      · rw [hctl] at hc; cases hc
      · rw [hctl] at hc; cases hc; exact hρ.b
      · rw [hctl] at hc; cases hc
      · rw [hctl] at hc; cases hc
    · simp [ScaWorkerLink.orientStep, hctl, moveRev]
  · -- inside a segment
    have hseg' := hseg
    obtain ⟨hd1, hd2, hn0, hphi, hrun, ⟨ok', hat'⟩, hout, hmatch, hmid⟩ := hseg'
    obtain ⟨u', hu', hrest⟩ := iterS_prefix hrun (show e + 1 ≤ n by omega)
    have hs1 : stepS x.length ρ u = some u' := by
      rw [iterS_add, hu, Option.bind_some] at hu'
      simpa [iterS] using hu'
    obtain ⟨hsafe, hsm⟩ := stepS_some hs1
    have hlenu : u.len = x.length + L := by
      show (u.word.length : ℤ) = _
      rw [iterStep_word _ (iterS_iterStep hu)]; exact atHead_len hat
    have hpsu : u.patternSize = x.length := by
      rw [iterStep_patternSize _ (iterS_iterStep hu)]; exact hps
    -- the `match` step, if this is one
    have key : IsMatch u → isRep x T s p₁ r j = true ∧ u.pos "B" = x.length + L ∧
        endOf x T s p₁ r j = L ∧ u.outputs = v.outputs ∧
        (∃ c, u.ctl = .pending c (.«match» "B")) := by
      intro hm
      obtain ⟨hrep, huniq⟩ := match_unique hseg hen (iterS_iterStep hu) hm
      obtain ⟨n₁, u₁, hn₁, hlt₁, hu₁, ho₁, ⟨c₁, hc₁⟩, hB₁⟩ := hmatch hrep
      have he := huniq n₁ u₁ (iterS_iterStep hu₁) ho₁ ⟨c₁, _, hc₁⟩ hlt₁
      subst he
      have huu : u = u₁ := by rw [hu] at hu₁; exact Option.some_inj.mp hu₁
      subst huu
      have hr := href j le_rfl hrep
      obtain ⟨hpos, hq⟩ := rep_shape x T s p₁ r j hP.ppos (by have := hP.sx; omega) (hP.qle j) hrep
      have hend : endOf x T s p₁ r j ≤ L := by unfold endOf; rw [← hpos]; omega
      have hge : L ≤ endOf x T s p₁ r j := by
        by_contra hcon
        push Not at hcon
        have h512 : 2048 * (endOf x T s p₁ r j + 1) ≤ 2048 * L := Nat.mul_le_mul_left _ hcon
        omega
      exact ⟨hrep, by rw [hB₁]; push_cast; omega, by omega, ho₁, c₁, hc₁⟩
    have hmB : IsMatch u → u.len ≤ u.pos "B" := by
      intro hm; obtain ⟨-, hB, -⟩ := key hm; rw [hlenu, hB]
    -- the output of this step
    have hout' : (IsMatch u → u'.outputs = u.outputs ++ [(L : ℤ)]) ∧
        (¬ IsMatch u → u'.outputs = u.outputs) := by
      refine ⟨fun hm => ?_, fun hm => step_outputs_nomatch hsm hm⟩
      obtain ⟨-, hB, -, -, c, hc⟩ := key hm
      obtain ⟨-, hv'⟩ := stepMatch_some hc hsm
      rw [hv']
      simp only [matchOut]
      rw [hB, hpsu]; congr 2; ring
    have hvals' : ∀ z ∈ u'.outputs, z ≤ L := by
      intro z hz
      by_cases hm : IsMatch u
      · rw [hout'.1 hm, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact hvals z hz
        · exact le_rfl
      · rw [hout'.2 hm] at hz; exact hvals z hz
    refine ⟨u', hsm, stepSide_of_safe hsafe hmB, orient_of_safe hsafe, ?_, ?_⟩
    · by_cases hlast : e + 1 = n
      · have hw : u' = w := by
          rw [← hlast, Nat.sub_self] at hrest
          simpa [iterS] using hrest
        subst hw
        have hps' : u'.patternSize = x.length := by
          rw [iterStep_patternSize _ (iterS_iterStep hrun)]; exact hps
        refine cur_of_head hρ hP hat' hps' (fun j'' hj'' hrep => href j'' (by omega) hrep)
          (hpr.trans (phi_mono x T s p₁ r hP.ppos (by omega))) (by omega) hvals' ?_
        intro j'' hj'' hrep
        rw [hout]
        rcases Nat.lt_or_ge j'' j with hlt' | hge'
        · exact List.mem_append_left _ (hrec j'' hlt' hrep)
        · rcases Nat.eq_or_lt_of_le hge' with heq | hgt
          · subst heq; rw [if_pos hrep]; exact List.mem_append_right _ (List.mem_singleton_self _)
          · have hd2' : d = 2 := by omega
            have : j'' = j + 1 := by omega
            subst this
            rw [hmid hd2'] at hrep; exact absurd hrep (by simp)
      · refine ⟨j, v, gr, pr, ok, hat, hps, href, hpr, hvals', hrec,
          Or.inr ⟨hlt, d, n, w, e + 1, hseg, by omega, hu', by omega, ?_⟩⟩
        by_cases hm : IsMatch u
        · obtain ⟨hrep, -, hend, hov, -⟩ := key hm
          right
          refine ⟨hrep, ?_⟩
          rw [hout'.1 hm, hov, hend]
        · rw [hout'.2 hm]
          rcases hbook with ⟨heq, hle⟩ | hpast
          · left
            refine ⟨heq, fun n₁ u₁ hu₁ hm₁ => ?_⟩
            have h1 := hle n₁ u₁ hu₁ hm₁
            rcases Nat.eq_or_lt_of_le h1 with h2 | h2
            · subst h2
              rw [hu] at hu₁
              rw [Option.some_inj.mp hu₁] at hm
              exact absurd hm₁ hm
            · omega
          · right; exact hpast
    · by_cases hm : IsMatch u
      · obtain ⟨hrep, -, hend, -, -⟩ := key hm
        exact Or.inr ⟨hout'.1 hm, j, hrep, hend⟩
      · exact Or.inl (hout'.2 hm)

/-- **A letter arrives** at the end of tick `L`. -/
theorem cur_append (hρ : Orient ρ) (hP : Params x T s p₁ r pe) {L : ℕ} {u : HVM}
    (hc : Cur ρ x T s p₁ r pe L (2048 * (L + 1)) u) (hL : L < T.length) :
    Cur ρ x T s p₁ r pe (L + 1) (2048 * (L + 1)) (u.append T[L]) := by
  obtain ⟨j, v, gr, pr, ok, hat, hps, href, hpr, hvals, hrec, hcase⟩ := hc
  have hvals' : ∀ z ∈ (u.append T[L]).outputs, z ≤ (L + 1 : ℕ) := by
    intro z hz; have := hvals z hz; push_cast; omega
  rcases hcase with ⟨hL', rfl, hgr, hpr'⟩ | ⟨hlt, d, n, w, e, hseg, hen, hu, htime, hbook⟩
  · exact cur_of_head hρ hP (atHead_append hat hL) hps href hpr (by omega) hvals' hrec
  · refine ⟨j, v.append T[L], gr, pr, ok, atHead_append hat hL, hps, href, hpr, hvals', hrec,
      Or.inr ⟨by omega, d, n, w.append T[L], e, segOK_append hseg hL, hen, iterS_append _ hu, htime,
        ?_⟩⟩
    rcases hbook with ⟨heq, hle⟩ | hpast
    · left
      refine ⟨heq, fun n₁ u₁ hu₁ hm₁ => ?_⟩
      rcases Nat.lt_or_ge n₁ n with h1 | h1
      · obtain ⟨y, hy, -⟩ := iterS_prefix hseg.2.2.2.2.1 h1.le
        have := iterS_append (a := T[L]) hy
        rw [hu₁] at this
        have hyu : u₁ = y.append T[L] := Option.some_inj.mp this
        subst hyu
        exact hle n₁ y hy hm₁
      · omega
    · right; exact hpast

/-- **`b` steps inside tick `L`.** -/
theorem cur_run (hρ : Orient ρ) (hP : Params x T s p₁ r pe) {L : ℕ} :
    ∀ (b : ℕ) {g : ℕ} {u : HVM}, Cur ρ x T s p₁ r pe L g u → 2048 * L ≤ g → g + b ≤ 2048 * (L + 1) →
      ∃ u', iterStep b u = some u' ∧
        (∀ i, i < b → ∀ ui, iterStep i u = some ui → ScaWorkerLink.StepSide x.length ρ ui) ∧
        (∀ i, i ≤ b → ScaWorkerLink.orientAt i u ρ = ρ) ∧
        Cur ρ x T s p₁ r pe L (g + b) u' ∧ u.outputs <+: u'.outputs ∧
        (u'.outputs = u.outputs ∨ ∃ j, isRep x T s p₁ r j = true ∧ endOf x T s p₁ r j = L)
  | 0, g, u, hc, _, _ =>
    ⟨u, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => by rw [Nat.le_zero.mp hi]; rfl, hc, List.prefix_refl _, Or.inl rfl⟩
  | b + 1, g, u, hc, hg1, hg2 => by
    obtain ⟨u1, hs, hside, horient, hc1, hout1⟩ := cur_step hρ hP hc hg1 (by omega)
    obtain ⟨u', hrun, hsides, horients, hc', hpre, hout⟩ :=
      cur_run hρ hP b (g := g + 1) hc1 (by omega) (by omega)
    refine ⟨u', ?_, ?_, ?_, by rw [show g + (b + 1) = g + 1 + b by omega]; exact hc', ?_, ?_⟩
    · simp only [iterStep, hs, Option.bind_some]; exact hrun
    · intro i hi ui hui
      cases i with
      | zero => simp only [iterStep, Option.some.injEq] at hui; subst hui; exact hside
      | succ i =>
        simp only [iterStep, hs, Option.bind_some] at hui
        exact hsides i (by omega) ui hui
    · intro i hi
      cases i with
      | zero => rfl
      | succ i =>
        rw [ScaWorkerLink.orientAt_succ ρ hs, horient]
        exact horients i (by omega)
    · have h1 : u.outputs <+: u1.outputs := by
        rcases hout1 with h | ⟨h, -⟩
        · rw [h]
        · rw [h]; exact List.prefix_append _ _
      exact h1.trans hpre
    · rcases hout1 with h1 | ⟨-, hj⟩
      · rcases hout with h2 | h2
        · left; rw [h2, h1]
        · right; exact h2
      · right; exact hj

/-- **Every report ending by `L` is out by the end of tick `L`.** -/
theorem cur_live (hP : Params x T s p₁ r pe) {L : ℕ} {u : HVM}
    (hc : Cur ρ x T s p₁ r pe L (2048 * (L + 1)) u) {j' : ℕ}
    (hrep : isRep x T s p₁ r j' = true) (hend : endOf x T s p₁ r j' ≤ L) :
    ((endOf x T s p₁ r j' : ℕ) : ℤ) ∈ u.outputs := by
  obtain ⟨j, v, gr, pr, ok, hat, hps, href, hpr, hvals, hrec, hcase⟩ := hc
  obtain ⟨hpos', hq'⟩ := rep_shape x T s p₁ r j' hP.ppos (by have := hP.sx; omega) (hP.qle j') hrep
  -- a report at or after `j` is not yet due, or it is out
  have hlate : ∀ jj, j ≤ jj → isRep x T s p₁ r jj = true →
      (Z x T s p₁ r j).1.pos + (Z x T s p₁ r j).1.q < endOf x T s p₁ r jj := by
    intro jj hjj hr
    obtain ⟨hp2, hq2⟩ := rep_shape x T s p₁ r jj hP.ppos (by have := hP.sx; omega) (hP.qle jj) hr
    have hm : (Z x T s p₁ r j).1.pos ≤ (Z x T s p₁ r jj).1.pos := PalPeg.GSDrained.orbit_pos_mono hjj
    have hqv := hat.qv
    unfold endOf; rw [← hp2]; omega
  rcases Nat.lt_or_ge j' j with hlt | hge
  · have hin := hrec j' hlt hrep
    rcases hcase with ⟨-, rfl, -⟩ | ⟨-, d, n, w, e, -, -, -, -, hbook⟩
    · exact hin
    · rcases hbook with ⟨heq, -⟩ | ⟨-, heq⟩ <;> rw [heq]
      · exact hin
      · exact List.mem_append_left _ hin
  · rcases hcase with ⟨hL, -, -⟩ | ⟨hlt, d, n, w, e, hseg, hen, hu, htime, hbook⟩
    · have := hlate j' hge hrep; omega
    · obtain ⟨hd1, hd2, hn0, hphi, -, -, -, hmatch, hmid⟩ := hseg
      have hr := href j' hge hrep
      have h512 : 2048 * (endOf x T s p₁ r j' + 1) ≤ 2048 * (L + 1) := Nat.mul_le_mul_left _ (by omega)
      rcases Nat.eq_or_lt_of_le hge with heq | hgt
      · subst heq
        rcases hbook with ⟨-, hle⟩ | ⟨-, heq⟩
        · exfalso
          obtain ⟨n₁, u₁, hn₁, -, hu₁, -, ⟨c₁, hc₁⟩, -⟩ := hmatch hrep
          have := hle n₁ u₁ hu₁ ⟨c₁, _, hc₁⟩
          omega
        · rw [heq]; exact List.mem_append_right _ (List.mem_singleton_self _)
      · exfalso
        have hjd : j + d ≤ j' := by
          rcases Nat.lt_or_ge j' (j + d) with h | h
          · have : j' = j + 1 := by omega
            have hd : d = 2 := by omega
            subst this; rw [hmid hd] at hrep; exact absurd hrep (by simp)
          · exact h
        have hm := phi_mono x T s p₁ r hP.ppos hjd
        omega

/-- **The reference at the first loop head** `Z 0 = (⟨s, 0⟩, 0)`: reached at slot `g₀` early
enough, every report makes its deadline. -/
theorem refOK_start (x T : List (Fin 2)) (s p₁ r g₀ : ℕ) (hp : 0 < p₁) (hsx : s < x.length)
    (hq : ∀ i, (Z x T s p₁ r i).1.q ≤ x.length - s)
    (hg₀ : g₀ < 2048 * s + 2013 * (x.length - s) + 2072) :
    RefOK x T s p₁ r g₀ (Φ x T s p₁ r 0) 0 := by
  intro j' _ hrep
  obtain ⟨hpos, hq'⟩ := rep_shape x T s p₁ r j' hp (by omega) (hq j') hrep
  have hge : (x.take s).length ≤ (Z x T s p₁ r j').1.pos := PalPeg.GSDrained.orbit_pos_ge j'
  have hz0 : Z x T s p₁ r 0 = ((⟨(x.take s).length, 0⟩ : PalPeg.ScanState), 0) := rfl
  have hts : (x.take s).length = s := by simp [List.length_take]; omega
  unfold endOf
  rw [← hpos]
  simp only [Φ, PalPeg.Phi, hz0, hts] at hge ⊢
  omega

end Tick

end PalPeg.ScaMatcherTick
