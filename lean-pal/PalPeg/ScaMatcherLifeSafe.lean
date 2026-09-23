import PalPeg.ScaMatcherLife2
import PalPeg.ScaMatcherStart
import PalPeg.ScaMatcherTick
import PalPeg.ScaMatcherAnswer

/-!
# The matcher's lives are safe

A matcher life born on the pattern `x ≠ []` and fed the text `T` (`ScaMatcherLife.lifeIn'` /
`lifeOut'`, from a start orientation `ρ₀`): one quantum of `2048` head-VM steps per tick, the
letter `T[t]` appended before tick `t + 1`. Global slot `g` counts the steps from birth; tick `t`
(with `t` letters of `T` available) is slots `2048·t … 2048·t + 2047`.

The life goes through three phases (`Good t g u ρ`: the VM `u` with ghost orientation `ρ` at slot
`g` of tick `t`):

* **pre** (`PreG`): the startup run `start_pre` under `ρ₀` (`n₁` steps), then the five
  orientation-changing copies (`start_copies`); every step is a guarded step, so letters commute
  with it (`iterS_append`); the ghost orientation is `orientAt g v₀ ρ₀`, which is `ρ₀` during
  `start_pre` and `loopOrient ρ₀` after the copies;
* **walk** (`WalkMove` / `WalkWait`): the offset walk (`walk_entry`, `walk_step`), under
  `loopOrient ρ₀`, waiting at `WalkHead i` while text cell `i` has not arrived (`walk_wait`);
* **loop** (`ScaMatcherTick.Cur`): the main loop.

The startup is timed against `B₀ = 2048·s + 2013·|v| + 2071` (`|v| = |x| − s`): while moving,
`g + (remaining startup steps) ≤ B₀`, so the first loop head is reached at `g₀ ≤ B₀`, which is
what `ScaMatcherTick.refOK_start` asks. The only assumption is on the length of `start_pre`
(`StartupFast`): `n₁ ≤ 2013·|x| + 32·s + 2063` (implied by `n₁ ≤ 2013·|x| + 2063`); this is exactly
what the budget needs (`n₁ + 5 + 3·s + 3 ≤ B₀`). The run reaching site 3 is unique
(`iterS_site3_unique`: the guarded run cannot pass `copy P Tail`), so `StartupFast` bounds the run
of `ScaMatcherStart.start_pre`.

## Results

* `lifeSafe'`: `LifeSafe' ρ₀ x T` for every `T` (every quantum runs its `2048` steps and keeps
  the worker's side conditions with the ghost orientation).
* `tick_output`: in tick `t ≤ |T|`, the quantum appends to `outputs` iff a report of the orbit
  ends at `t` (`∃ j, isRep … j ∧ endOf … j = t`); stated on `lifeIn`/`lifeVM` (independent of
  `ρ₀`), as `ScaMatcherLife.answering_output'` gives them. `tick_output_last`: the last tick.
* `scheduledLivesSafe'_of_startupFast`: the hypothesis of `ScaMatcherLife2`.
-/

set_option autoImplicit false

namespace PalPeg.ScaMatcherLifeSafe

open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe PalPeg.ScaHeadDecompose
  PalPeg.ScaMatcherTick
open PalPeg.ScaMatcherLoop (mc Orient AtHead head_wait)
open PalPeg.ScaMatcherAnswer (normP1)
open PalPeg.ScaWorkerLink (startCtl orientAt orientAt_succ orientStep orientStep_pending StepSide
  SideRun orientAt_add iterStep_succ_of)
open PalPeg.ScaMatcherStart (loopOrient WalkRel WalkHead)
open PalPeg.ScaMatcherLife (lifeIn lifeVM lifeIn' lifeOut' lifeIn'_append lifeOut'_eq_bind
  lifeIn'_fst lifeOut'_fst quantum_def QuantumSafe LifeSafe' ScheduledLivesSafe' StartOrients)

/-! ## Letters appended to a VM -/

/-- The letters `L` appended, in order. -/
def appendAll (v : HVM) (L : List (Fin 2)) : HVM := L.foldl HVM.append v

theorem appendAll_nil (v : HVM) : appendAll v [] = v := rfl

theorem appendAll_snoc (v : HVM) (L : List (Fin 2)) (a : Fin 2) :
    appendAll v (L ++ [a]) = (appendAll v L).append a := by
  unfold appendAll
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem appendAll_fields (v : HVM) (L : List (Fin 2)) :
    (appendAll v L).ctl = v.ctl ∧ (appendAll v L).outputs = v.outputs ∧
      (appendAll v L).patternSize = v.patternSize ∧ (appendAll v L).word = v.word ++ L ∧
      ∀ h, h ≠ OE → (appendAll v L).pos h = v.pos h := by
  induction L using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl, by simp [appendAll], fun _ _ => rfl⟩
  | append_singleton L a ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    rw [appendAll_snoc]
    refine ⟨h1, h2, h3, ?_, fun h hh => ?_⟩
    · show (appendAll v L).word ++ [a] = _
      rw [h4, List.append_assoc]
    · rw [append_pos_ne _ _ hh, h5 h hh]

section Guarded
variable {W : ℕ} {ρ : String → Bool}

theorem iterS_appendAll (L : List (Fin 2)) {n : ℕ} {v w : HVM} (h : iterS W ρ n v = some w) :
    iterS W ρ n (appendAll v L) = some (appendAll w L) := by
  induction L using List.reverseRecOn with
  | nil => exact h
  | append_singleton L a ih =>
    rw [appendAll_snoc, appendAll_snoc]
    exact iterS_append a ih

theorem safeAt_appendAll (L : List (Fin 2)) {v : HVM} (h : SafeAt W ρ v) :
    SafeAt W ρ (appendAll v L) := by
  induction L using List.reverseRecOn with
  | nil => exact h
  | append_singleton L a ih =>
    rw [appendAll_snoc]
    exact safeAt_append a ih

theorem stepS_appendAll (L : List (Fin 2)) {v w : HVM} (h : stepS W ρ v = some w) :
    stepS W ρ (appendAll v L) = some (appendAll w L) := by
  induction L using List.reverseRecOn with
  | nil => exact h
  | append_singleton L a ih =>
    rw [appendAll_snoc, appendAll_snoc]
    exact stepS_append a ih

/-- One more step of a guarded run: it is a guarded step. -/
theorem seg_next {n e : ℕ} {v w y : HVM} (hrun : iterS W ρ n v = some w) (he : e < n)
    (hy : iterS W ρ e v = some y) :
    ∃ y', stepS W ρ y = some y' ∧ iterS W ρ (e + 1) v = some y' := by
  obtain ⟨u, hu, -⟩ := iterS_prefix hrun (show e + 1 ≤ n by omega)
  rw [iterS_add, hy, Option.bind_some] at hu
  refine ⟨u, ?_, ?_⟩
  · simpa [iterS] using hu
  · rw [iterS_add, hy, Option.bind_some, hu]

/-- The rest of a guarded run after `e` steps. -/
theorem seg_rest {n e : ℕ} {v w y : HVM} (hrun : iterS W ρ n v = some w) (he : e ≤ n)
    (hy : iterS W ρ e v = some y) : iterS W ρ (n - e) y = some w := by
  rw [show n = e + (n - e) by omega, iterS_add, hy, Option.bind_some] at hrun
  exact hrun

/-- The ghost orientation stays `ρ` along a guarded run. -/
theorem orientAt_of_iterS : ∀ {n : ℕ} {v w : HVM}, iterS W ρ n v = some w →
    ∀ i, i ≤ n → orientAt i v ρ = ρ
  | 0, v, w, _, i, hi => by rw [Nat.le_zero.mp hi]; rfl
  | n + 1, v, w, h, i, hi => by
    simp only [iterS] at h
    cases hs : stepS W ρ v with
    | none => rw [hs] at h; simp at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨hsafe, hst⟩ := stepS_some hs
      cases i with
      | zero => rfl
      | succ i =>
        rw [orientAt_succ ρ hst, orient_of_safe hsafe]
        exact orientAt_of_iterS h i (by omega)

end Guarded

theorem orientStep_congr {u v : HVM} (h : u.ctl = v.ctl) (ρ : String → Bool) :
    orientStep u ρ = orientStep v ρ := by
  unfold orientStep; rw [h]

/-- The last step of an orientation run. -/
theorem orientAt_succ_right {g : ℕ} {v y y' : HVM} (ρ : String → Bool)
    (hy : iterStep g v = some y) (hy' : stepMatch y = some y') :
    orientAt (g + 1) v ρ = orientStep y (orientAt g v ρ) := by
  rw [orientAt_add g 1 ρ hy, orientAt_succ _ hy']
  rfl

theorem isMatch_congr {u v : HVM} (h : u.ctl = v.ctl) : IsMatch u ↔ IsMatch v := by
  unfold IsMatch; rw [h]

/-- A state whose run keeps `outputs` is not a `match` state. -/
theorem not_isMatch_of_run {a b : ℕ} {v y y' w : HVM} (hy : iterStep a v = some y)
    (hstep : stepMatch y = some y') (hw : iterStep b y' = some w) (hout : w.outputs = v.outputs) :
    ¬ IsMatch y := by
  intro hm
  have h1 := step_outputs_match hstep hm
  have h2 := outputs_len_le hy
  have h3 := outputs_len_le hw
  rw [hout] at h3
  omega

/-! ## The startup's hypothesis and setup -/

/-- The site-3 control of the startup (`copy P Tail`), with the decomposition's flag. -/
abbrev site3 (pe : Bool) : Ctl := .pending [mc 8 (some pe) none none 3] (.copy "P" "Tail")

/-- **The startup is fast**: the startup run `start_pre` (under `ρ₀`, from the birth state) reaches
the site-3 state in at most `2013·|x| + 32·s + 2063` steps. -/
def StartupFast (x : List (Fin 2)) (ρ₀ : String → Bool) : Prop :=
  ∃ n π', n ≤ 2013 * x.length + 32 * (decompose x 8).1 + 2063 ∧
    iterS x.length ρ₀ n (matchInitial x startCtl) = some { matchInitial x startCtl with
      ctl := site3 (decide ((decompose x 8).2.1 ≠ 0))
      pos := π' }

/-- The guarded startup cannot pass `copy P Tail`: `P` is reversed and `Tail` forward. -/
theorem stepS_site3 {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀) {y : HVM}
    {pe : Bool} (hy : y.ctl = site3 pe) (W : ℕ) : stepS W ρ₀ y = none := by
  unfold stepS
  rw [if_neg]
  intro hs
  simp only [SafeAt, hy, EvOk] at hs
  have := hs.1
  rw [hA.dec.p, hA.tail] at this
  exact absurd this (by decide)

theorem iterS_site3_unique {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀) {W : ℕ}
    {v y y' : HVM} {pe pe' : Bool} {n n' : ℕ} (h : iterS W ρ₀ n v = some y)
    (h' : iterS W ρ₀ n' v = some y') (hy : y.ctl = site3 pe) (hy' : y'.ctl = site3 pe') :
    n = n' ∧ y = y' := by
  have key : ∀ {m m' : ℕ} {z z' : HVM} {q : Bool}, iterS W ρ₀ m v = some z →
      iterS W ρ₀ m' v = some z' → z.ctl = site3 q → m ≤ m' → m = m' ∧ z = z' := by
    intro m m' z z' q hz hz' hzc hle
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · subst heq
      rw [hz] at hz'
      exact ⟨rfl, Option.some_inj.mp hz'⟩
    · exfalso
      have hr := seg_rest hz' hle hz
      rw [show m' - m = (m' - m - 1) + 1 by omega] at hr
      simp only [iterS, stepS_site3 hA hzc W] at hr
      simp at hr
  rcases le_total n n' with hle | hle
  · exact key h h' hy hle
  · obtain ⟨h1, h2⟩ := key h' h hy' hle
    exact ⟨h1.symm, h2.symm⟩

/-! ## One life's setup -/

/-- The data of one life: the pattern, the text, the decomposition, the start orientation, and
the startup run `start_pre` (`n₁` steps to the site-3 heads `π₃`). -/
structure Setup where
  x : List (Fin 2)
  T : List (Fin 2)
  s : ℕ
  p : ℕ
  r : ℕ
  ρ₀ : String → Bool
  n₁ : ℕ
  π₃ : String → ℤ

/-- An orientation under which every `copy` is a guarded step. -/
abbrev ρtriv : String → Bool := fun _ => false

namespace Setup
variable (S : Setup)

abbrev pe : Bool := decide (S.p ≠ 0)
abbrev p₁ : ℕ := normP1 S.x
abbrev v₀ : HVM := matchInitial S.x startCtl
abbrev w₃ : HVM := { S.v₀ with ctl := site3 S.pe, pos := S.π₃ }
abbrev ρL : String → Bool := loopOrient S.ρ₀
/-- The startup's time budget: the first loop head is reached by slot `B₀`. -/
abbrev B₀ : ℕ := 2048 * S.s + 2013 * (S.x.length - S.s) + 2071

/-- The heads after the startup copies (site 7, `less Walk Cut`). -/
abbrev w₇ : HVM :=
  { S.w₃ with
    ctl := .pending [mc 8 (some S.pe) none none 8] (.less "Walk" "Cut")
    pos := ScaMatcherStart.cp5 S.w₃.pos }

end Setup

/-- What a setup must satisfy. -/
structure Setup.OK (S : Setup) : Prop where
  dec : decompose S.x 8 = (S.s, S.p, S.r)
  hx : S.x ≠ []
  orient : ScaMatcherStart.StartOrient S.ρ₀
  run3 : iterS S.x.length S.ρ₀ S.n₁ S.v₀ = some S.w₃
  fast : S.n₁ ≤ 2013 * S.x.length + 32 * S.s + 2063
  keep : Keeps ("End" :: dHeads) S.v₀.pos S.π₃
  endP : S.π₃ "End" = S.x.length
  cut : S.π₃ "Cut" = S.s
  per : S.p ≠ 0 → S.π₃ "First" = (S.s : ℤ) + S.p ∧
    S.π₃ "KFirst" = (S.s : ℤ) + ((8 : ℕ) : ℤ) * S.p ∧ S.π₃ "Reach" = (S.s : ℤ) + S.r

theorem v₀_fields (x : List (Fin 2)) :
    (matchInitial x startCtl).word = x ∧ (matchInitial x startCtl).outputs = [] ∧
      (matchInitial x startCtl).patternSize = x.length ∧
      (matchInitial x startCtl).pos "Origin" = 0 ∧
      (matchInitial x startCtl).pos "Tail" = x.length := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> simp [matchInitial]

/-- **A setup from `start_pre` and `StartupFast`.** -/
theorem setup_of {x : List (Fin 2)} (hx : x ≠ []) {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀) (hfast : StartupFast x ρ₀)
    (T : List (Fin 2)) :
    ∃ S : Setup, S.OK ∧ S.x = x ∧ S.T = T ∧ S.s = s ∧ S.p = p ∧ S.r = r ∧ S.ρ₀ = ρ₀ := by
  obtain ⟨n, π', hn, hrun⟩ := hfast
  rw [hdec] at hn hrun
  obtain ⟨hw, -, -, hO, hT⟩ := v₀_fields x
  obtain ⟨n', π'', -, hrun', hkeep, hE, hC, hper⟩ :=
    ScaMatcherStart.start_pre (rest := []) hdec hx hA (matchInitial x startCtl) rfl
      (by rw [hw, List.append_nil]) hO hT
  obtain ⟨hnn, hyy⟩ := iterS_site3_unique hA hrun hrun' rfl rfl
  have hπ : π' = π'' := by
    have := congrArg HVM.pos hyy
    exact this
  subst hnn hπ
  exact ⟨⟨x, T, s, p, r, ρ₀, n, π'⟩, ⟨hdec, hx, hA, hrun, hn, hkeep, hE, hC, hper⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Setup
variable {S : Setup}

theorem OK.params (hS : S.OK) : Params S.x S.T S.s S.p₁ S.r S.pe where
  sx := by
    have := ScaMatcherAnswer.drop_length_pos hS.dec hS.hx
    rw [List.length_drop] at this
    omega
  noper := (ScaMatcherAnswer.normP1_pe hS.dec).1
  p1 := fun h => ((ScaMatcherAnswer.normP1_pe hS.dec).2 h).1
  ppos := ScaMatcherAnswer.normP1_pos S.x
  sd := ScaMatcherAnswer.shiftDeadline_normP1 hS.dec
  qle := fun i => by
    have := (PalPeg.GSDrained.orbit_scanInv (u := S.x.take S.s) (T := S.T)
      (ScaMatcherAnswer.ksimple_normP1 hS.dec) i).2
    rw [List.length_drop] at this
    exact this

theorem OK.loopOrient (hS : S.OK) : Orient S.ρL := ScaMatcherStart.loopOrient_orient hS.orient

theorem OK.sx (hS : S.OK) : S.s < S.x.length := hS.params.sx

theorem OK.z0 (hS : S.OK) : Z S.x S.T S.s S.p₁ S.r 0 = ((⟨S.s, 0⟩ : PalPeg.ScanState), 0) := by
  show ((⟨(S.x.take S.s).length, 0⟩ : PalPeg.ScanState), 0) = _
  rw [ScaMatcherAnswer.take_length hS.dec]

theorem OK.w₃_fields (hS : S.OK) :
    S.w₃.word = S.x ∧ S.w₃.outputs = [] ∧ S.w₃.patternSize = S.x.length ∧
      S.w₃.pos "Origin" = 0 ∧ S.w₃.pos "Tail" = S.x.length ∧ S.w₃.pos "End" = S.x.length ∧
      S.w₃.pos "Cut" = S.s := by
  obtain ⟨hw, ho, hps, hO, hT⟩ := v₀_fields S.x
  refine ⟨hw, ho, hps, ?_, ?_, hS.endP, hS.cut⟩
  · show S.π₃ "Origin" = 0
    rw [hS.keep "Origin" (by decide)]; exact hO
  · show S.π₃ "Tail" = S.x.length
    rw [hS.keep "Tail" (by decide)]; exact hT

/-! ## The copies, as a guarded run under `ρtriv` -/

theorem evOk_copy (W : ℕ) (π : String → ℤ) (len : ℤ) {t s' : String} (ht : t ≠ OE)
    (hs : s' ≠ OE) : EvOk W ρtriv π len (.copy t s') := ⟨rfl, ht, hs⟩

theorem copies_iterS (W : ℕ) : iterS W ρtriv 5 S.w₃ = some S.w₇ := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := ScaMatcherStart.copies_chain S.pe S.w₃ rfl
  exact iterS_step rfl (evOk_copy W _ _ (by decide) (by decide)) e1
    (iterS_step rfl (evOk_copy W _ _ (by decide) (by decide)) e2
      (iterS_step rfl (evOk_copy W _ _ (by decide) (by decide)) e3
        (iterS_step rfl (evOk_copy W _ _ (by decide) (by decide)) e4
          (iterS_step rfl (evOk_copy W _ _ (by decide) (by decide)) e5 rfl))))

/-- Every state inside the copies has a pending `copy`. -/
theorem copies_ctl (W : ℕ) {c : ℕ} (hc : c < 5) {y : HVM} (hy : iterS W ρtriv c S.w₃ = some y) :
    ∃ cfg t s', y.ctl = .pending cfg (.copy t s') := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := ScaMatcherStart.copies_chain S.pe S.w₃ rfl
  have hy' := iterS_iterStep hy
  interval_cases c
  · simp only [iterStep, Option.some.injEq] at hy'; subst hy'; exact ⟨_, _, _, rfl⟩
  · simp only [iterStep, e1, Option.bind_some, Option.some.injEq] at hy'; subst hy'
    exact ⟨_, _, _, rfl⟩
  · simp only [iterStep, e1, e2, Option.bind_some, Option.some.injEq] at hy'; subst hy'
    exact ⟨_, _, _, rfl⟩
  · simp only [iterStep, e1, e2, e3, Option.bind_some, Option.some.injEq] at hy'; subst hy'
    exact ⟨_, _, _, rfl⟩
  · simp only [iterStep, e1, e2, e3, e4, Option.bind_some, Option.some.injEq] at hy'; subst hy'
    exact ⟨_, _, _, rfl⟩

/-- The ghost orientation after the startup is `loopOrient ρ₀`. -/
theorem OK.orient_walk (hS : S.OK) : orientAt (S.n₁ + 5) S.v₀ S.ρ₀ = S.ρL := by
  rw [orientAt_add S.n₁ 5 S.ρ₀ (iterS_iterStep hS.run3),
    orientAt_of_iterS hS.run3 S.n₁ le_rfl]
  exact ScaMatcherStart.start_copies_orient S.pe S.w₃ rfl hS.orient

end Setup

/-! ## Phase 1: the startup before the walk -/

namespace Setup
variable (S : Setup)

/-- `y` is the state after `g` steps of the startup before the walk (letters aside): `start_pre`
under `ρ₀`, then the copies (under `ρtriv`, which guards every `copy`). -/
def PreAt (g : ℕ) (y : HVM) : Prop :=
  (g < S.n₁ ∧ iterS S.x.length S.ρ₀ g S.v₀ = some y) ∨
    (S.n₁ ≤ g ∧ g ≤ S.n₁ + 5 ∧ iterS S.x.length ρtriv (g - S.n₁) S.w₃ = some y)

/-- **Phase 1** at slot `g` of tick `t`: the startup state with the letters of `t` ticks
appended, and the ghost orientation of the birth run. -/
def PreG (t g : ℕ) (u : HVM) (ρ : String → Bool) : Prop :=
  g < S.n₁ + 5 ∧ ρ = orientAt g S.v₀ S.ρ₀ ∧ ∃ y, S.PreAt g y ∧ u = appendAll y (S.T.take t)

variable {S}

theorem OK.preAt_facts (hS : S.OK) {g : ℕ} {y : HVM} (h : S.PreAt g y) :
    iterStep g S.v₀ = some y ∧ y.outputs = [] := by
  rcases h with ⟨hg, hy⟩ | ⟨hg1, hg2, hy⟩
  · refine ⟨iterS_iterStep hy, ?_⟩
    have hpre := ScaMatcherLife.iterStep_outputs _ (iterS_iterStep (seg_rest hS.run3 hg.le hy))
    exact List.prefix_nil.mp hpre
  · refine ⟨?_, ?_⟩
    · rw [show g = S.n₁ + (g - S.n₁) by omega, iterStep_add, iterS_iterStep hS.run3,
        Option.bind_some]
      exact iterS_iterStep hy
    · have hpre := ScaMatcherLife.iterStep_outputs _
        (iterS_iterStep (seg_rest (copies_iterS S.x.length) (show g - S.n₁ ≤ 5 by omega) hy))
      exact List.prefix_nil.mp hpre

/-- **One step of phase 1.** -/
theorem OK.preG_step (hS : S.OK) {t g : ℕ} {u : HVM} {ρ : String → Bool}
    (h : S.PreG t g u ρ) :
    ∃ u', stepMatch u = some u' ∧ StepSide S.x.length ρ u ∧ u'.outputs = u.outputs ∧
      (S.PreG t (g + 1) u' (orientStep u ρ) ∨
        (g + 1 = S.n₁ + 5 ∧ orientStep u ρ = S.ρL ∧ u' = appendAll S.w₇ (S.T.take t))) := by
  obtain ⟨hg, hρ, y, hy, rfl⟩ := h
  have hctlA := (appendAll_fields y (S.T.take t)).1
  rcases hy with ⟨hgn, hy⟩ | ⟨hg1, hg2, hy⟩
  · -- `start_pre`, guarded under `ρ₀`
    obtain ⟨y', hs, hy'⟩ := seg_next hS.run3 hgn hy
    obtain ⟨hsafe, hsm⟩ := stepS_some hs
    obtain ⟨hsafeA, hsmA⟩ := stepS_some (stepS_appendAll (S.T.take t) hs)
    have hρ₀ : orientAt g S.v₀ S.ρ₀ = S.ρ₀ := orientAt_of_iterS hS.run3 g hgn.le
    have hnm : ¬ IsMatch y :=
      not_isMatch_of_run (iterS_iterStep hy) hsm
        (iterS_iterStep (seg_rest hS.run3 (show g + 1 ≤ S.n₁ by omega) hy')) rfl
    have hnmA : ¬ IsMatch (appendAll y (S.T.take t)) := fun hm => hnm ((isMatch_congr hctlA).mp hm)
    have horient : orientStep (appendAll y (S.T.take t)) ρ = orientAt (g + 1) S.v₀ S.ρ₀ := by
      rw [orientStep_congr hctlA, hρ, orientAt_succ_right S.ρ₀ (iterS_iterStep hy) hsm]
    refine ⟨_, hsmA, ?_, step_outputs_nomatch hsmA hnmA, Or.inl ⟨by omega, horient, ?_⟩⟩
    · rw [hρ, hρ₀]
      exact stepSide_of_safe hsafeA (fun hm => absurd hm hnmA)
    · rcases Nat.lt_or_ge (g + 1) S.n₁ with hlt | hge
      · exact ⟨y', Or.inl ⟨hlt, hy'⟩, rfl⟩
      · have heq : g + 1 = S.n₁ := by omega
        have hy3 : y' = S.w₃ := by
          rw [heq, hS.run3] at hy'; exact (Option.some_inj.mp hy').symm
        refine ⟨y', Or.inr ⟨by omega, by omega, ?_⟩, rfl⟩
        rw [show g + 1 - S.n₁ = 0 by omega, hy3]
        rfl
  · -- the copies, guarded under `ρtriv`
    have hc : g - S.n₁ < 5 := by omega
    obtain ⟨y', hs, hy'⟩ := seg_next (copies_iterS S.x.length) hc hy
    obtain ⟨-, hsm⟩ := stepS_some hs
    obtain ⟨-, hsmA⟩ := stepS_some (stepS_appendAll (S.T.take t) hs)
    obtain ⟨cfg, t', s', hctl⟩ := copies_ctl S.x.length hc hy
    have hnmA : ¬ IsMatch (appendAll y (S.T.take t)) := by
      rintro ⟨c', h', hc'⟩
      rw [hctlA, hctl] at hc'
      cases hc'
    have hyv : iterStep g S.v₀ = some y := (hS.preAt_facts (Or.inr ⟨hg1, hg2, hy⟩)).1
    have horient : orientStep (appendAll y (S.T.take t)) ρ = orientAt (g + 1) S.v₀ S.ρ₀ := by
      rw [orientStep_congr hctlA, hρ, orientAt_succ_right S.ρ₀ hyv hsm]
    refine ⟨_, hsmA, ScaMatcherStart.stepSide_copy (by rw [hctlA, hctl]),
      step_outputs_nomatch hsmA hnmA, ?_⟩
    rcases Nat.lt_or_ge (g + 1) (S.n₁ + 5) with hlt | hge
    · refine Or.inl ⟨hlt, horient, y', Or.inr ⟨by omega, by omega, ?_⟩, rfl⟩
      rw [show g + 1 - S.n₁ = g - S.n₁ + 1 by omega]
      exact hy'
    · have heq : g + 1 = S.n₁ + 5 := by omega
      have hy7 : y' = S.w₇ := by
        rw [show g - S.n₁ + 1 = 5 by omega, copies_iterS] at hy'
        exact (Option.some_inj.mp hy').symm
      refine Or.inr ⟨heq, ?_, by rw [hy7]⟩
      rw [horient, heq]
      exact hS.orient_walk

end Setup

/-! ## Phase 2: the offset walk -/

namespace Setup
variable (S : Setup)

/-- **Moving in the walk** at slot `g` of tick `t`: `e` guarded steps into a run of `nb` steps
from `vb` to the next stop `vend` (a `WalkHead` or the first loop head), timed so that the loop
head is reached by `B₀` if the walk does not wait again. -/
def WalkMove (t g : ℕ) (u : HVM) : Prop :=
  ∃ vb nb vend e, e < nb ∧ iterS S.x.length S.ρL e vb = some u ∧
    iterS S.x.length S.ρL nb vb = some vend ∧ vend.outputs = [] ∧
    vend.patternSize = S.x.length ∧
    ((∃ i, WalkHead S.x S.T t S.s S.p₁ S.r S.pe i vend ∧ g + (nb - e) + 3 * (S.s - i) + 2 ≤ S.B₀) ∨
      (AtHead S.x S.T t 8 S.s S.p₁ S.r S.pe true (Z S.x S.T S.s S.p₁ S.r 0) vend ∧
        g + (nb - e) ≤ S.B₀))

/-- **Waiting in the walk** at `WalkHead i`, text cell `i` not yet arrived. -/
def WalkWait (t g : ℕ) (u : HVM) : Prop :=
  ∃ i, WalkHead S.x S.T t S.s S.p₁ S.r S.pe i u ∧ t ≤ i ∧ u.outputs = [] ∧ g ≤ S.B₀

/-- The loop's state. -/
abbrev LoopCur (t g : ℕ) (u : HVM) : Prop := Cur S.ρL S.x S.T S.s S.p₁ S.r S.pe t g u

variable {S}

/-- **A stop of the walk**: continue moving, wait, or start the main loop. -/
theorem OK.stop (hS : S.OK) {t g : ℕ} {u : HVM} (hg : g ≤ 2048 * (t + 1)) (hout : u.outputs = [])
    (hps : u.patternSize = S.x.length)
    (h : (∃ i, WalkHead S.x S.T t S.s S.p₁ S.r S.pe i u ∧ g + 3 * (S.s - i) + 2 ≤ S.B₀) ∨
      (AtHead S.x S.T t 8 S.s S.p₁ S.r S.pe true (Z S.x S.T S.s S.p₁ S.r 0) u ∧ g ≤ S.B₀)) :
    S.WalkMove t g u ∨ S.WalkWait t g u ∨ S.LoopCur t g u := by
  have hsx := hS.sx
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  rcases h with ⟨i, hwh, hgi⟩ | ⟨hat, hgB⟩
  · have hi := hwh.lt
    by_cases hit : i < t
    · obtain ⟨h1, h2⟩ := ScaMatcherStart.walk_step hS.dec hS.hx hS.orient u hwh hit
      rcases Nat.lt_or_ge (i + 1) S.s with hlt | hge
      · obtain ⟨w, hrun, hwo, hwh'⟩ := h1 hlt
        exact Or.inl ⟨u, 3, w, 0, by norm_num, rfl, hrun, hwo.trans hout, hwh'.psize,
          Or.inl ⟨i + 1, hwh', by omega⟩⟩
      · obtain ⟨w, hrun, hwo, hwps, hat⟩ := h2 (by omega)
        rw [← hS.z0] at hat
        exact Or.inl ⟨u, 5, w, 0, by norm_num, rfl, hrun, hwo.trans hout, hwps,
          Or.inr ⟨hat, by omega⟩⟩
    · refine Or.inr (Or.inl ⟨i, hwh, by omega, hout, ?_⟩)
      have : 2048 * (t + 1) ≤ 2048 * S.s := Nat.mul_le_mul_left _ (by omega)
      omega
  · refine Or.inr (Or.inr ?_)
    exact cur_of_head hS.loopOrient hS.params hat hps
      (refOK_start S.x S.T S.s S.p₁ S.r g hS.params.ppos hsx hS.params.qle (by omega)) le_rfl
      le_rfl (by rw [hout]; simp) (fun j hj _ => absurd hj (Nat.not_lt_zero _))

/-- **Entering the walk** after the copies, with the letters of `t` ticks. -/
theorem OK.walk_entry (hS : S.OK) {t : ℕ} (ht : t ≤ S.T.length) :
    S.WalkMove t (S.n₁ + 5) (appendAll S.w₇ (S.T.take t)) := by
  have hsx := hS.sx
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  have hfast := hS.fast
  have hA0 : S.s = 0 → S.n₁ + 5 + (3 - 0) ≤ S.B₀ := by intro; omega
  have hA1 : S.n₁ + 5 + (1 - 0) + 3 * (S.s - 0) + 2 ≤ S.B₀ := by omega
  obtain ⟨hw, ho, hps, hO, hT, hE, hC⟩ := hS.w₃_fields
  obtain ⟨fctl, fout, fps, fword, fpos⟩ := appendAll_fields S.w₃ (S.T.take t)
  obtain ⟨v2, h5, hv2o, hv2c, hrel⟩ := ScaMatcherStart.copies_walkRel (T := S.T) (m := t) hS.dec
    (appendAll S.w₃ (S.T.take t)) fctl (by rw [fword, hw]) ht (by rw [fps, hps])
    (by rw [fpos _ (by decide), hO]) (by rw [fpos _ (by decide), hT])
    (by rw [fpos _ (by decide), hE]) (by rw [fpos _ (by decide), hC])
    (fun hp => by
      rw [fpos _ (by decide), fpos _ (by decide), fpos _ (by decide)]
      exact hS.per hp)
  have h5' := iterS_iterStep (iterS_appendAll (S.T.take t) (copies_iterS (S := S) S.x.length))
  rw [h5] at h5'
  have hv2 : v2 = appendAll S.w₇ (S.T.take t) := Option.some_inj.mp h5'
  subst hv2
  have hv2out : (appendAll S.w₇ (S.T.take t)).outputs = [] := by rw [hv2o, fout, ho]
  obtain ⟨hs0, hspos⟩ := ScaMatcherStart.walk_entry hS.dec hS.hx hS.orient _ hv2c hrel
  rcases Nat.eq_zero_or_pos S.s with hz | hpos
  · obtain ⟨w, hrun, hwo, hwps, hat⟩ := hs0 hz
    rw [← hS.z0] at hat
    exact ⟨_, 3, w, 0, by norm_num, rfl, hrun, by rw [hwo, hv2out], hwps,
      Or.inr ⟨hat, hA0 hz⟩⟩
  · obtain ⟨w, hrun, hwo, hwh⟩ := hspos hpos
    exact ⟨_, 1, w, 0, by norm_num, rfl, hrun, by rw [hwo, hv2out], hwh.psize,
      Or.inl ⟨0, hwh, hA1⟩⟩

/-- **One step while moving.** -/
theorem OK.walkMove_step (hS : S.OK) {t g : ℕ} {u : HVM} (hg : g < 2048 * (t + 1))
    (h : S.WalkMove t g u) :
    ∃ u', stepMatch u = some u' ∧ StepSide S.x.length S.ρL u ∧ orientStep u S.ρL = S.ρL ∧
      u'.outputs = u.outputs ∧
      (S.WalkMove t (g + 1) u' ∨ S.WalkWait t (g + 1) u' ∨ S.LoopCur t (g + 1) u') := by
  obtain ⟨vb, nb, vend, e, he, hu, hrun, hvo, hvps, hstop⟩ := h
  obtain ⟨u', hs, hu'⟩ := seg_next hrun he hu
  obtain ⟨hsafe, hsm⟩ := stepS_some hs
  have hrest := seg_rest hrun (show e + 1 ≤ nb by omega) hu'
  have huo : u.outputs = [] := by
    have := ScaMatcherLife.iterStep_outputs _ (iterS_iterStep (seg_rest hrun he.le hu))
    rw [hvo] at this
    exact List.prefix_nil.mp this
  have hnm : ¬ IsMatch u :=
    not_isMatch_of_run (a := 0) rfl hsm (iterS_iterStep hrest) (by rw [hvo, huo])
  have hout' := step_outputs_nomatch hsm hnm
  refine ⟨u', hsm, stepSide_of_safe hsafe (fun hm => absurd hm hnm), orient_of_safe hsafe, hout',
    ?_⟩
  by_cases hlast : e + 1 = nb
  · have hu'v : u' = vend := by
      rw [← hlast, Nat.sub_self] at hrest
      simpa [iterS] using hrest
    subst hu'v
    refine hS.stop (by omega) hvo hvps ?_
    rcases hstop with ⟨i, hwh, hgi⟩ | ⟨hat, hgB⟩
    · exact Or.inl ⟨i, hwh, by omega⟩
    · exact Or.inr ⟨hat, by omega⟩
  · refine Or.inl ⟨vb, nb, vend, e + 1, by omega, hu', hrun, hvo, hvps, ?_⟩
    rcases hstop with ⟨i, hwh, hgi⟩ | ⟨hat, hgB⟩
    · exact Or.inl ⟨i, hwh, by omega⟩
    · exact Or.inr ⟨hat, by omega⟩

/-- **One step while waiting.** -/
theorem OK.walkWait_step (hS : S.OK) {t g : ℕ} {u : HVM} (hg : g < 2048 * (t + 1))
    (h : S.WalkWait t g u) :
    stepMatch u = some u ∧ StepSide S.x.length S.ρL u ∧ orientStep u S.ρL = S.ρL ∧
      S.WalkWait t (g + 1) u := by
  obtain ⟨i, hwh, hti, hout, -⟩ := h
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  obtain ⟨h1, hctl, hB⟩ := ScaMatcherStart.walk_wait hS.orient u hwh hti
  have hi := hwh.lt
  refine ⟨stepMatch_of_one h1, ⟨fun c a b hc => ?_, fun c h hc => ?_, fun c ms hc => ?_,
    fun c h hc => ?_⟩, ?_, ⟨i, hwh, hti, hout, ?_⟩⟩
  · rw [hctl] at hc; cases hc
  · rw [hctl] at hc; cases hc; exact hB
  · rw [hctl] at hc; cases hc
  · rw [hctl] at hc; cases hc
  · simp [orientStep, hctl, moveRev]
  · have : 2048 * (t + 1) ≤ 2048 * S.s := Nat.mul_le_mul_left _ (by omega)
    omega

end Setup

/-! ## The phases together -/

namespace Setup
variable (S : Setup)

/-- **The life at slot `g` of tick `t`**: phase 1, the walk, or the main loop. -/
def Good (t g : ℕ) (u : HVM) (ρ : String → Bool) : Prop :=
  S.PreG t g u ρ ∨ (ρ = S.ρL ∧ (S.WalkMove t g u ∨ S.WalkWait t g u)) ∨
    (ρ = S.ρL ∧ S.LoopCur t g u)

/-- A report of the orbit ends at `t`. -/
def RepAt (t : ℕ) : Prop :=
  ∃ j, isRep S.x S.T S.s S.p₁ S.r j = true ∧ endOf S.x S.T S.s S.p₁ S.r j = t

variable {S}

theorem good_of_stop {t g : ℕ} {u : HVM}
    (h : S.WalkMove t g u ∨ S.WalkWait t g u ∨ S.LoopCur t g u) : S.Good t g u S.ρL := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
  · exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  · exact Or.inr (Or.inr ⟨rfl, h⟩)

/-- **One step of the life.** -/
theorem OK.good_step (hS : S.OK) {t g : ℕ} {u : HVM} {ρ : String → Bool} (ht : t ≤ S.T.length)
    (hg1 : 2048 * t ≤ g) (hg2 : g < 2048 * (t + 1)) (h : S.Good t g u ρ) :
    ∃ u', stepMatch u = some u' ∧ StepSide S.x.length ρ u ∧ S.Good t (g + 1) u' (orientStep u ρ) ∧
      (u'.outputs = u.outputs ∨ S.RepAt t) := by
  rcases h with hpre | ⟨rfl, hwm | hww⟩ | ⟨rfl, hc⟩
  · obtain ⟨u', hsm, hside, hout, hnext⟩ := hS.preG_step hpre
    refine ⟨u', hsm, hside, ?_, Or.inl hout⟩
    rcases hnext with hpre' | ⟨heq, hρ, rfl⟩
    · exact Or.inl hpre'
    · rw [hρ, heq]
      exact Or.inr (Or.inl ⟨rfl, Or.inl (hS.walk_entry ht)⟩)
  · obtain ⟨u', hsm, hside, hρ, hout, hnext⟩ := hS.walkMove_step hg2 hwm
    refine ⟨u', hsm, hside, ?_, Or.inl hout⟩
    rw [hρ]
    exact good_of_stop hnext
  · obtain ⟨hsm, hside, hρ, hnext⟩ := hS.walkWait_step hg2 hww
    refine ⟨u, hsm, hside, ?_, Or.inl rfl⟩
    rw [hρ]
    exact Or.inr (Or.inl ⟨rfl, Or.inr hnext⟩)
  · obtain ⟨u', hsm, hside, hρ, hc', hout⟩ := cur_step hS.loopOrient hS.params hc hg1 hg2
    refine ⟨u', hsm, hside, ?_, ?_⟩
    · rw [hρ]
      exact Or.inr (Or.inr ⟨rfl, hc'⟩)
    · rcases hout with h | ⟨-, hj⟩
      · exact Or.inl h
      · exact Or.inr hj

/-- **A letter arrives** at the end of tick `t`. -/
theorem OK.good_append (hS : S.OK) {t : ℕ} {u : HVM} {ρ : String → Bool} (ht : t < S.T.length)
    (h : S.Good t (2048 * (t + 1)) u ρ) : S.Good (t + 1) (2048 * (t + 1)) (u.append S.T[t]) ρ := by
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  have htake : S.T.take (t + 1) = S.T.take t ++ [S.T[t]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  rcases h with ⟨hg, hρ, y, hy, rfl⟩ | ⟨rfl, hwm | hww⟩ | ⟨rfl, hc⟩
  · exact Or.inl ⟨hg, hρ, y, hy, by rw [htake, appendAll_snoc]⟩
  · obtain ⟨vb, nb, vend, e, he, hu, hrun, hvo, hvps, hstop⟩ := hwm
    refine Or.inr (Or.inl ⟨rfl, Or.inl ⟨vb.append S.T[t], nb, vend.append S.T[t], e, he,
      iterS_append _ hu, iterS_append _ hrun, hvo, hvps, ?_⟩⟩)
    rcases hstop with ⟨i, hwh, hgi⟩ | ⟨hat, hgB⟩
    · exact Or.inl ⟨i, ScaMatcherStart.walkHead_append vend hwh ht, hgi⟩
    · exact Or.inr ⟨atHead_append hat ht, hgB⟩
  · obtain ⟨i, hwh, hti, hout, hgB⟩ := hww
    have hwh' := ScaMatcherStart.walkHead_append u hwh ht
    rcases Nat.lt_or_ge t i with hlt | hge
    · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨i, hwh', by omega, hout, hgB⟩⟩)
    · have hit : i = t := by omega
      subst hit
      have hi := hwh.lt
      refine good_of_stop (hS.stop (by omega) hout (by rw [← hwh.psize]; rfl) ?_)
      exact Or.inl ⟨i, hwh', by omega⟩
  · exact Or.inr (Or.inr ⟨rfl, cur_append hS.loopOrient hS.params hc ht⟩)

/-- Before the main loop, the slot is at most `B₀` and nothing has been output. -/
theorem OK.good_early (hS : S.OK) {t g : ℕ} {u : HVM} {ρ : String → Bool} (h : S.Good t g u ρ) :
    S.LoopCur t g u ∨ (g ≤ S.B₀ ∧ u.outputs = []) := by
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  have hfast := hS.fast
  have hsx := hS.sx
  rcases h with ⟨hg, -, y, hy, rfl⟩ | ⟨-, hwm | hww⟩ | ⟨-, hc⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [(appendAll_fields y _).2.1]
    exact (hS.preAt_facts hy).2
  · obtain ⟨vb, nb, vend, e, he, hu, hrun, hvo, -, hstop⟩ := hwm
    refine Or.inr ⟨?_, ?_⟩
    · rcases hstop with ⟨i, -, hgi⟩ | ⟨-, hgB⟩ <;> omega
    · have := ScaMatcherLife.iterStep_outputs _ (iterS_iterStep (seg_rest hrun he.le hu))
      rw [hvo] at this
      exact List.prefix_nil.mp this
  · obtain ⟨i, -, -, hout, hgB⟩ := hww
    exact Or.inr ⟨hgB, hout⟩
  · exact Or.inl hc

/-- The values output so far are at most the letter count. -/
theorem OK.good_vals (hS : S.OK) {t g : ℕ} {u : HVM} {ρ : String → Bool} (h : S.Good t g u ρ) :
    ∀ z ∈ u.outputs, z ≤ (t : ℤ) := by
  rcases hS.good_early h with hc | ⟨-, hout⟩
  · obtain ⟨j, v, gr, pr, ok, -, -, -, -, hvals, -⟩ := hc
    exact hvals
  · rw [hout]; simp

/-- **`b` steps inside tick `t`.** -/
theorem OK.good_run (hS : S.OK) {t : ℕ} (ht : t ≤ S.T.length) :
    ∀ (b : ℕ) {g : ℕ} {u : HVM} {ρ : String → Bool}, S.Good t g u ρ → 2048 * t ≤ g →
      g + b ≤ 2048 * (t + 1) →
      ∃ u', iterStep b u = some u' ∧ SideRun S.x.length ρ b u ∧
        S.Good t (g + b) u' (orientAt b u ρ) ∧ (u'.outputs = u.outputs ∨ S.RepAt t)
  | 0, g, u, ρ, h, _, _ =>
    ⟨u, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), h, Or.inl rfl⟩
  | b + 1, g, u, ρ, h, hg1, hg2 => by
    obtain ⟨u1, hs, hside, hgood, hout1⟩ := hS.good_step ht hg1 (by omega) h
    obtain ⟨u', hrun, hsides, hgood', hout⟩ := hS.good_run ht b hgood (by omega) (by omega)
    refine ⟨u', ?_, ?_, ?_, ?_⟩
    · simp only [iterStep, hs, Option.bind_some]; exact hrun
    · intro i hi ui hui
      cases i with
      | zero =>
        simp only [iterStep, Option.some.injEq] at hui
        subst hui
        exact hside
      | succ i =>
        rw [iterStep_succ_of hs] at hui
        rw [orientAt_succ ρ hs]
        exact hsides i (by omega) ui hui
    · rw [orientAt_succ ρ hs, show g + (b + 1) = g + 1 + b by omega]
      exact hgood'
    · rcases hout with h2 | h2
      · rcases hout1 with h1 | h1
        · exact Or.inl (h2.trans h1)
        · exact Or.inr h1
      · exact Or.inr h2

end Setup

/-! ## The life, tick by tick -/

namespace Setup
variable {S : Setup}

theorem OK.good_initial (hS : S.OK) : S.Good 0 0 S.v₀ S.ρ₀ := by
  refine Or.inl ⟨by omega, rfl, S.v₀, ?_, rfl⟩
  rcases Nat.eq_zero_or_pos S.n₁ with h0 | hpos
  · refine Or.inr ⟨by omega, by omega, ?_⟩
    have h3 := hS.run3
    rw [h0] at h3
    have hv : S.v₀ = S.w₃ := Option.some_inj.mp h3
    rw [h0, Nat.sub_zero, ← hv]
    rfl
  · exact Or.inl ⟨hpos, rfl⟩

theorem take_succ_eq {T : List (Fin 2)} {t : ℕ} (ht : t < T.length) :
    T.take (t + 1) = T.take t ++ [T[t]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]

/-- **The life at the start of every tick**, with the values output so far below the tick. -/
theorem OK.life (hS : S.OK) : ∀ t, t ≤ S.T.length →
    ∃ u ρ, lifeIn' S.ρ₀ S.x (S.T.take t) = some (u, ρ) ∧ S.Good t (2048 * t) u ρ ∧
      ∀ z ∈ u.outputs, z < (t : ℤ)
  | 0, _ => ⟨S.v₀, S.ρ₀, rfl, hS.good_initial, by intro z hz; simp [(v₀_fields S.x).2.1] at hz⟩
  | t + 1, ht => by
    obtain ⟨u, ρ, hin, hgood, -⟩ := hS.life t (by omega)
    obtain ⟨u', hrun, -, hgood', -⟩ := hS.good_run (by omega) 2048 hgood le_rfl (by omega)
    have hout : lifeOut' S.ρ₀ S.x (S.T.take t) = some (u', orientAt 2048 u ρ) := by
      rw [lifeOut'_eq_bind, hin, Option.bind_some, quantum_def]
      show (iterStep 2048 u).map _ = _
      rw [hrun]
      rfl
    have hgood'' : S.Good t (2048 * (t + 1)) u' (orientAt 2048 u ρ) := by
      rw [show 2048 * (t + 1) = 2048 * t + 2048 by ring]
      exact hgood'
    refine ⟨u'.append S.T[t], orientAt 2048 u ρ, ?_, hS.good_append (by omega) hgood'', ?_⟩
    · rw [take_succ_eq (by omega), lifeIn'_append, hout]
      rfl
    · intro z hz
      have := hS.good_vals hgood'' z hz
      push_cast
      omega

theorem OK.endOf_ge (hS : S.OK) (j : ℕ) : S.x.length ≤ endOf S.x S.T S.s S.p₁ S.r j := by
  have hge : (S.x.take S.s).length ≤ (Z S.x S.T S.s S.p₁ S.r (j + 1)).1.pos :=
    PalPeg.GSDrained.orbit_pos_ge (j + 1)
  rw [ScaMatcherAnswer.take_length hS.dec] at hge
  have hsx := hS.sx
  unfold endOf
  omega

/-- **The quantum of tick `t`**: it runs `2048` steps with the side conditions, and appends to
`outputs` iff a report ends at `t`. -/
theorem OK.tick (hS : S.OK) {t : ℕ} (ht : t ≤ S.T.length) :
    ∃ u ρ u', lifeIn' S.ρ₀ S.x (S.T.take t) = some (u, ρ) ∧ iterStep 2048 u = some u' ∧
      QuantumSafe S.x.length ρ u ∧
      (decide (u.outputs.length < u'.outputs.length) = true ↔ S.RepAt t) := by
  have hB₀ : S.B₀ = 2048 * S.s + 2013 * (S.x.length - S.s) + 2071 := rfl
  have hsx := hS.sx
  obtain ⟨u, ρ, hin, hgood, hvals⟩ := hS.life t ht
  obtain ⟨u', hrun, hside, hgood', hrep⟩ := hS.good_run ht 2048 hgood le_rfl (by omega)
  refine ⟨u, ρ, u', hin, hrun, ⟨by rw [hrun]; rfl, hside⟩, ?_, ?_⟩
  · intro hlt
    rcases hrep with heq | hj
    · rw [heq] at hlt; simp at hlt
    · exact hj
  · rintro ⟨j, hj, hend⟩
    have hge := hS.endOf_ge j
    rw [show 2048 * t + 2048 = 2048 * (t + 1) by ring] at hgood'
    rcases hS.good_early hgood' with hc | ⟨hgB, -⟩
    · have hmem := cur_live hS.params hc hj (le_of_eq hend)
      rw [hend] at hmem
      have hpre := ScaMatcherLife.iterStep_outputs 2048 hrun
      simp only [decide_eq_true_eq]
      by_contra hle
      push Not at hle
      have heq : u.outputs = u'.outputs := hpre.eq_of_length (le_antisymm hpre.length_le hle)
      rw [← heq] at hmem
      have := hvals _ hmem
      omega
    · exfalso
      have : 2048 * (t + 1) < 2048 * (S.x.length + 1) := by omega
      omega

end Setup

/-! ## The results -/

/-- **The matcher's lives are safe**: from a start orientation `ρ₀` agreeing with the startup
(`ScaMatcherStart.StartOrient`), every quantum of the life born on `x ≠ []` and fed any `T`
runs its `2048` steps and keeps the worker's side conditions, provided `start_pre` is fast. -/
theorem lifeSafe' {x : List (Fin 2)} (hx : x ≠ []) {ρ₀ : String → Bool}
    (hA : ScaMatcherStart.StartOrient ρ₀) (hfast : StartupFast x ρ₀) (T : List (Fin 2)) :
    LifeSafe' ρ₀ x T := by
  rcases hdec : decompose x 8 with ⟨s, p, r⟩
  obtain ⟨S, hS, rfl, rfl, -, -, -, rfl⟩ := setup_of hx hdec hA hfast T
  intro T' hpre p0 hp0
  have ht : T'.length ≤ S.T.length := hpre.length_le
  have hT' : T' = S.T.take T'.length := List.prefix_iff_eq_take.mp hpre
  obtain ⟨u, ρ, u', hin, -, hq, -⟩ := hS.tick ht
  rw [← hT', hp0] at hin
  rw [Option.some_inj.mp hin]
  exact hq

/-- **The output of every tick**: in tick `t ≤ |T|` of the life born on `x ≠ []` (whose head VM
before the quantum is `(lifeIn x (T.take t)).map Prod.fst` and after it `lifeVM x (T.take t)`),
the quantum appends to `outputs` iff a report of the orbit ends at `t`. -/
theorem tick_output {x : List (Fin 2)} (hx : x ≠ []) {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀) (hfast : StartupFast x ρ₀)
    (T : List (Fin 2)) {t : ℕ} (ht : t ≤ T.length) {v0 v : HVM}
    (hin : (lifeIn x (T.take t)).map Prod.fst = some v0) (hout : lifeVM x (T.take t) = some v) :
    decide (v0.outputs.length < v.outputs.length) = true ↔
      ∃ j, isRep x T s (normP1 x) r j = true ∧ endOf x T s (normP1 x) r j = t := by
  obtain ⟨S, hS, rfl, rfl, rfl, rfl, rfl, rfl⟩ := setup_of hx hdec hA hfast T
  obtain ⟨u, ρ, u', hin', hrun, -, hiff⟩ := hS.tick ht
  have hv0 : v0 = u := by
    rw [← lifeIn'_fst S.ρ₀, hin'] at hin
    exact (Option.some_inj.mp hin).symm
  have hv : v = u' := by
    rw [← lifeOut'_fst S.ρ₀, lifeOut'_eq_bind, hin', Option.bind_some, quantum_def] at hout
    rw [show (iterStep 2048 (u, ρ).1) = some u' from hrun] at hout
    exact (Option.some_inj.mp hout).symm
  subst hv0 hv
  exact hiff

/-- `tick_output` for the last tick (`t = |T|`). -/
theorem tick_output_last {x : List (Fin 2)} (hx : x ≠ []) {s p r : ℕ}
    (hdec : decompose x 8 = (s, p, r)) {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀)
    (hfast : StartupFast x ρ₀) (T : List (Fin 2)) {v0 v : HVM}
    (hin : (lifeIn x T).map Prod.fst = some v0) (hout : lifeVM x T = some v) :
    decide (v0.outputs.length < v.outputs.length) = true ↔
      ∃ j, isRep x T s (normP1 x) r j = true ∧ endOf x T s (normP1 x) r j = T.length := by
  have h := tick_output hx hdec hA hfast T (t := T.length) le_rfl (v0 := v0) (v := v)
    (by rw [List.take_length]; exact hin) (by rw [List.take_length]; exact hout)
  exact h

/-- The start orientation of the startup is one for `ScaMatcherLife2`. -/
theorem startOrients_of {ρ₀ : String → Bool} (hA : ScaMatcherStart.StartOrient ρ₀) :
    StartOrients fun _ => ρ₀ :=
  fun _ => ⟨hA.dec.origin, hA.tail⟩

/-- **The hypothesis of `ScaMatcherLife2`** from `StartupFast` for the scheduled patterns. -/
theorem scheduledLivesSafe'_of_startupFast {ρ₀ : String → Bool}
    (hA : ScaMatcherStart.StartOrient ρ₀)
    (hfast : ∀ x : List (Fin 2), (∃ j, 1 ≤ j ∧ x.length = 2 ^ j) → StartupFast x ρ₀) :
    ScheduledLivesSafe' fun _ => ρ₀ := by
  intro x T hj _
  have hx : x ≠ [] := by
    obtain ⟨j, hj1, hlen⟩ := hj
    intro h
    rw [h] at hlen
    have : 0 < 2 ^ j := Nat.two_pow_pos j
    simp at hlen
    omega
  exact lifeSafe' hx hA (hfast x hj) T

/-! ## Axiom audit -/

/-- info: 'PalPeg.ScaMatcherLifeSafe.lifeSafe'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifeSafe'

/-- info: 'PalPeg.ScaMatcherLifeSafe.tick_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tick_output

/-- info: 'PalPeg.ScaMatcherLifeSafe.tick_output_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tick_output_last

/-- info: 'PalPeg.ScaMatcherLifeSafe.scheduledLivesSafe'_of_startupFast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scheduledLivesSafe'_of_startupFast

end PalPeg.ScaMatcherLifeSafe
