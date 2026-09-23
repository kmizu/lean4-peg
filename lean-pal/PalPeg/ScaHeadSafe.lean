import PalPeg.ScaHeadGen

/-!
# Matcher steps that keep the worker's side conditions

The real matcher worker follows the logical head VM only while each step keeps the worker's side
conditions (`ScaWorkerLink.StepSide`): a `symbols` reads both heads on their side of the pattern
boundary `W`, `available` tests a forward head, a moved reversed head stays inside the pattern.
`stepS W ρ` is `stepMatch` guarded by these conditions (orientation `ρ`), plus two conditions
that make the step commute with a letter arrival (`HVM.append`): no event names `OriginalEnd`
(the head `append` moves), and an `available` test succeeds. A run of `iterS` therefore carries
the side conditions at every state it leaves (`iterS_safe`), and letters may arrive anywhere
inside it (`iterS_append`).

A `copy t s` must keep the orientation (`ρ t = ρ s`), so the worker's ghost orientation stays `ρ`
along an `iterS` run.
-/
set_option autoImplicit false
namespace PalPeg.ScaHeadSafe
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen

/-- The head that `append` moves with the frontier; the matcher's main loop never names it. -/
abbrev OE : String := "OriginalEnd"

/-- The side conditions of one event, at positions `π` and word length `len`. -/
def EvOk (W : ℕ) (ρ : String → Bool) (π : String → ℤ) (len : ℤ) : Event → Prop
  | .move ms => (∀ h, h ∉ blind → ρ h = true → sumDelta ms h ≠ 0 → π h + sumDelta ms h ≤ W) ∧
      OE ∉ ms.map (·.head)
  | .copy t s => ρ t = ρ s ∧ t ≠ OE ∧ s ≠ OE
  | .equal a b => a ≠ OE ∧ b ≠ OE
  | .less a b => a ≠ OE ∧ b ≠ OE
  | .symbols a b => OnSide W (ρ a) (π a) ∧ OnSide W (ρ b) (π b) ∧ a ≠ OE ∧ b ≠ OE
  | .available h => ρ h = false ∧ π h < len ∧ h ≠ OE
  | .assertEqual a b => a ≠ OE ∧ b ≠ OE
  | .«match» h => ρ "B" = false ∧ h ≠ OE
  | _ => True

/-- The side conditions of the pending event of `v`. -/
def SafeAt (W : ℕ) (ρ : String → Bool) (v : HVM) : Prop :=
  match v.ctl with
  | .pending _ e => EvOk W ρ v.pos v.len e
  | _ => True

open Classical in
/-- A matcher step that keeps the side conditions. -/
noncomputable def stepS (W : ℕ) (ρ : String → Bool) (v : HVM) : Option HVM :=
  if SafeAt W ρ v then stepMatch v else none

/-- `n` guarded matcher steps. -/
noncomputable def iterS (W : ℕ) (ρ : String → Bool) : ℕ → HVM → Option HVM
  | 0, v => some v
  | n + 1, v => (stepS W ρ v).bind (iterS W ρ n)

section Basic
variable {W : ℕ} {ρ : String → Bool}

theorem iterS_add (m n : ℕ) (v : HVM) :
    iterS W ρ (m + n) v = (iterS W ρ m v).bind (iterS W ρ n) := by
  induction m generalizing v with
  | zero => simp [iterS]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [iterS]
    cases stepS W ρ v with
    | none => rfl
    | some v' => simp [ih]

theorem iterS_trans {m n : ℕ} {u v w : HVM} (h1 : iterS W ρ m u = some v)
    (h2 : iterS W ρ n v = some w) : iterS W ρ (m + n) u = some w := by
  rw [iterS_add, h1, Option.bind_some, h2]

theorem stepS_eq {v : HVM} {c : Config} {e : Event} (hv : v.ctl = .pending c e)
    (hok : EvOk W ρ v.pos v.len e) : stepS W ρ v = stepMatch v := by
  have : SafeAt W ρ v := by simp only [SafeAt, hv]; exact hok
  simp [stepS, this]

theorem iterS_one {v w : HVM} {c : Config} {e : Event} (hv : v.ctl = .pending c e)
    (hok : EvOk W ρ v.pos v.len e) (h : stepMatch v = some w) : iterS W ρ 1 v = some w := by
  simp [iterS, stepS_eq hv hok, h]

theorem iterS_step {n : ℕ} {v u w : HVM} {c : Config} {e : Event} (hv : v.ctl = .pending c e)
    (hok : EvOk W ρ v.pos v.len e) (h1 : stepMatch v = some u) (h2 : iterS W ρ n u = some w) :
    iterS W ρ (n + 1) v = some w := by
  simp only [iterS, stepS_eq hv hok, h1, Option.bind_some, h2]

theorem stepMatch_of_one {v w : HVM} (h : iterStep 1 v = some w) : stepMatch v = some w := by
  simpa [iterStep] using h

/-- A move keeps the side conditions when every moved reversed head stays inside the pattern. -/
theorem evOk_move {π : String → ℤ} {len : ℤ} {ms : List Movement}
    (hms : ∀ m ∈ ms, m.head ∉ blind → ρ m.head = true → π m.head + sumDelta ms m.head ≤ W)
    (hoe : OE ∉ ms.map (·.head)) : EvOk W ρ π len (.move ms) := by
  refine ⟨fun h hb hr hd => ?_, hoe⟩
  have : ∃ m ∈ ms, m.head = h := by
    by_contra hn
    push Not at hn
    apply hd
    simp only [sumDelta]
    rw [List.filter_eq_nil_iff.mpr (by intro m hm; simpa using hn m hm)]
    rfl
  obtain ⟨m, hm, rfl⟩ := this
  exact hms m hm hb hr

theorem stepS_some {v w : HVM} (h : stepS W ρ v = some w) : SafeAt W ρ v ∧ stepMatch v = some w := by
  unfold stepS at h
  split_ifs at h with hs
  · exact ⟨hs, h⟩

theorem iterS_iterStep : ∀ {n : ℕ} {v w : HVM}, iterS W ρ n v = some w → iterStep n v = some w
  | 0, v, w, h => by simpa [iterS, iterStep] using h
  | n + 1, v, w, h => by
    simp only [iterS] at h
    cases hs : stepS W ρ v with
    | none => simp [hs] at h
    | some v' =>
      rw [hs, Option.bind_some] at h
      simp only [iterStep, (stepS_some hs).2, Option.bind_some]
      exact iterS_iterStep h

/-- **Every state an `iterS` run leaves keeps the side conditions.** -/
theorem iterS_safe : ∀ {n : ℕ} {v w : HVM}, iterS W ρ n v = some w →
    ∀ i < n, ∃ u, iterStep i v = some u ∧ SafeAt W ρ u
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, v, w, h, i, hi => by
    simp only [iterS] at h
    cases hs : stepS W ρ v with
    | none => simp [hs] at h
    | some v' =>
      rw [hs, Option.bind_some] at h
      obtain ⟨hsafe, hst⟩ := stepS_some hs
      cases i with
      | zero => exact ⟨v, rfl, hsafe⟩
      | succ i =>
        obtain ⟨u, hu, hsu⟩ := iterS_safe h i (by omega)
        exact ⟨u, by simp [iterStep, hst, hu], hsu⟩

end Basic

/-! ## Inside a caller -/

section Lift
variable {W : ℕ} {ρ : String → Bool}

theorem iterS_lift (f : Frame) :
    ∀ (n : ℕ) (v w : HVM), NonEmptyCtl v.ctl → iterS W ρ n v = some w →
      iterS W ρ n (liftVM f v) = some (liftVM f w)
  | 0, v, w, _, h => by simp [iterS] at h; subst h; rfl
  | n + 1, v, w, hv, h => by
    simp only [iterS] at h ⊢
    cases hs : stepS W ρ v with
    | none => simp [hs] at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨hsafe, hst⟩ := stepS_some hs
      obtain ⟨cs, e, hc, -⟩ := stepMatch_ctl hst
      have hne : cs ≠ [] := by rw [hc] at hv; exact hv
      have hl : liftVM f v = { v with ctl := .pending (f :: cs) e } := by
        simp only [liftVM, hc, liftCtl]
      have hok : EvOk W ρ v.pos v.len e := by simpa only [SafeAt, hc] using hsafe
      rw [hl, stepS_eq (v := { v with ctl := .pending (f :: cs) e }) rfl hok,
        stepMatch_lift f v cs e hc hne, hst, Option.map_some, Option.bind_some]
      exact iterS_lift f n v1 w (nonEmpty_step hv (MStep.step hst)) h

end Lift

/-! ## Letter arrivals commute with guarded steps -/

theorem moveSeq_len_mono {B : List String} {L L' : ℤ} (hL : L ≤ L') :
    ∀ (ms : List Movement) (π π' : String → ℤ), moveSeq B L ms π = some π' →
      moveSeq B L' ms π = some π'
  | [], π, π', h => h
  | m :: ms, π, π', h => by
    simp only [moveSeq] at h ⊢
    split_ifs at h with h1
    rw [if_neg (by
      intro h2
      exact h1 ⟨h2.1, fun h3 => h2.2 ⟨h3.1, h3.2.trans hL⟩⟩)]
    exact moveSeq_len_mono hL ms _ _ h

theorem moveSeq_other {B : List String} {L : ℤ} {o : String} :
    ∀ (ms : List Movement) (π π' : String → ℤ), o ∉ ms.map (·.head) →
      moveSeq B L ms π = some π' → π' o = π o
  | [], π, π', _, h => by simp [moveSeq] at h; rw [h]
  | m :: ms, π, π', ho, h => by
    simp only [moveSeq] at h
    simp only [List.map_cons, List.mem_cons, not_or] at ho
    split_ifs at h
    rw [moveSeq_other ms _ π' ho.2 h, Function.update_of_ne ho.1]

theorem moveSeq_update {B : List String} {L : ℤ} {o : String} (d : ℤ) :
    ∀ (ms : List Movement) (π π' : String → ℤ), o ∉ ms.map (·.head) →
      moveSeq B L ms π = some π' →
      moveSeq B L ms (Function.update π o d) = some (Function.update π' o d)
  | [], π, π', _, h => by simp [moveSeq] at h ⊢; rw [h]
  | m :: ms, π, π', ho, h => by
    simp only [moveSeq] at h ⊢
    simp only [List.map_cons, List.mem_cons, not_or] at ho
    have hne : m.head ≠ o := fun e => ho.1 e.symm
    split_ifs at h with h1
    have e1 : Function.update (Function.update π o d) m.head (Function.update π o d m.head + m.delta) =
        Function.update (Function.update π m.head (π m.head + m.delta)) o d := by
      rw [Function.update_of_ne hne, Function.update_comm hne]
    rw [e1, Function.update_of_ne hne, if_neg (by rw [Function.update_self] at h1 ⊢; exact h1)]
    exact moveSeq_update d ms _ _ ho.2 h

section Append
variable {W : ℕ} {ρ : String → Bool}

theorem append_len (v : HVM) (a : Fin 2) : (v.append a).len = v.len + 1 := by
  simp [HVM.append, HVM.len]

theorem append_pos_ne (v : HVM) (a : Fin 2) {h : String} (hh : h ≠ OE) :
    (v.append a).pos h = v.pos h := by
  simp [HVM.append, Function.update_of_ne hh]

theorem append_word_get (v : HVM) (a : Fin 2) {i : ℤ} (h0 : 0 ≤ i) (hi : i < v.len) :
    (v.append a).word[i.toNat]? = v.word[i.toNat]? := by
  simp only [HVM.append]
  rw [List.getElem?_append_left (by simp [HVM.len] at hi; omega)]

theorem safeAt_append {v : HVM} (a : Fin 2) (hs : SafeAt W ρ v) : SafeAt W ρ (v.append a) := by
  unfold SafeAt at hs ⊢
  have hctl : (v.append a).ctl = v.ctl := rfl
  rw [hctl]
  split at hs
  · rename_i c e hv
    have hl := append_len v a
    cases e with
    | move ms =>
      obtain ⟨h1, h2⟩ := hs
      refine ⟨fun h hb hr hd => ?_, h2⟩
      have hh : h ≠ OE := by
        intro e; subst e
        apply hd
        simp only [sumDelta]
        rw [List.filter_eq_nil_iff.mpr (by
          intro m hm; simp only [decide_eq_true_eq]
          intro e; exact h2 (List.mem_map.mpr ⟨m, hm, e⟩))]
        rfl
      rw [append_pos_ne v a hh]; exact h1 h hb hr hd
    | copy t s => exact hs
    | equal a' b => exact hs
    | less a' b => exact hs
    | symbols a' b =>
      obtain ⟨h1, h2, h3, h4⟩ := hs
      exact ⟨by rw [append_pos_ne v a h3]; exact h1, by rw [append_pos_ne v a h4]; exact h2, h3, h4⟩
    | available h =>
      obtain ⟨h1, h2, h3⟩ := hs
      exact ⟨h1, by rw [append_pos_ne v a h3, hl]; omega, h3⟩
    | assertEqual a' b => exact hs
    | «match» h => exact hs
    | border h => exact hs
    | flag b => exact hs
    | halt => exact hs
  · trivial

theorem stepMatch_append {v w : HVM} (a : Fin 2) (hs : SafeAt W ρ v) (h : stepMatch v = some w) :
    stepMatch (v.append a) = some (w.append a) := by
  obtain ⟨c, e, hv, -⟩ := stepMatch_ctl h
  have hok : EvOk W ρ v.pos v.len e := by simpa only [SafeAt, hv] using hs
  have hctl : (v.append a).ctl = .pending c e := hv
  have hl := append_len v a
  cases e with
  | move ms =>
    obtain ⟨-, hoe⟩ := hok
    unfold stepMatch at h
    rw [hv] at h
    simp only at h
    cases hm : moveSeq blind v.len ms v.pos with
    | none => simp [hm] at h
    | some π =>
      rw [hm, Option.map_some, Option.some_inj] at h
      subst h
      have hπ := moveSeq_other ms v.pos π hoe hm
      have hm' := moveSeq_update (v.pos OE + 1) ms _ _ hoe
        (moveSeq_len_mono (L' := v.len + 1) (by omega) ms _ _ hm)
      rw [step_move hctl (π := Function.update π OE (v.pos OE + 1)) (by rw [hl]; exact hm')]
      simp [HVM.append, hπ, hv]
  | copy t s =>
    obtain ⟨-, ht, hs'⟩ := hok
    rw [step_copy hv] at h
    rw [step_copy hctl, ← Option.some_inj.mp h]
    simp only [HVM.append, Option.some_inj, HVM.mk.injEq, true_and]
    refine ⟨?_, trivial⟩
    rw [Function.update_of_ne hs', Function.update_comm ht, Function.update_of_ne (Ne.symm ht)]
  | equal a' b =>
    obtain ⟨h1, h2⟩ := hok
    rw [step_equal hv] at h
    rw [step_equal hctl, ← Option.some_inj.mp h, append_pos_ne v a h1, append_pos_ne v a h2]
    rfl
  | less a' b =>
    obtain ⟨h1, h2⟩ := hok
    rw [step_less hv] at h
    rw [step_less hctl, ← Option.some_inj.mp h, append_pos_ne v a h1, append_pos_ne v a h2]
    rfl
  | symbols a' b =>
    obtain ⟨-, -, h3, h4⟩ := hok
    unfold stepMatch at h
    rw [hv] at h
    simp only at h
    split_ifs at h with hr
    obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := hr
    have hr' : (v.append a).inRange a' ∧ (v.append a).inRange b := by
      simp only [HVM.inRange, append_pos_ne v a h3, append_pos_ne v a h4, hl]
      omega
    rw [step_symbols hctl hr'.1 hr'.2, ← Option.some_inj.mp h, append_pos_ne v a h3,
      append_pos_ne v a h4, append_word_get v a ha0 ha1, append_word_get v a hb0 hb1]
    rfl
  | available h' =>
    obtain ⟨-, h2, h3⟩ := hok
    rw [step_available hv] at h
    rw [step_available hctl, ← Option.some_inj.mp h, append_pos_ne v a h3, hl,
      show decide (v.pos h' < v.len + 1) = decide (v.pos h' < v.len) by simp; omega]
    rfl
  | assertEqual a' b =>
    obtain ⟨h1, h2⟩ := hok
    unfold stepMatch at h
    rw [hv] at h
    simp only at h
    split_ifs at h with he
    rw [step_assertEqual hctl (by rw [append_pos_ne v a h1, append_pos_ne v a h2]; exact he),
      ← Option.some_inj.mp h]
    rfl
  | «match» h' =>
    obtain ⟨-, h2⟩ := hok
    rw [step_match hv] at h
    rw [step_match hctl, ← Option.some_inj.mp h, append_pos_ne v a h2]
    rfl
  | border h' => unfold stepMatch at h; rw [hv] at h; simp at h
  | flag b => unfold stepMatch at h; rw [hv] at h; simp at h
  | halt => unfold stepMatch at h; rw [hv] at h; simp at h

theorem stepS_append {v w : HVM} (a : Fin 2) (h : stepS W ρ v = some w) :
    stepS W ρ (v.append a) = some (w.append a) := by
  obtain ⟨hs, hst⟩ := stepS_some h
  unfold stepS
  rw [if_pos (safeAt_append a hs), stepMatch_append a hs hst]

/-- **Letters may arrive inside a guarded run.** -/
theorem iterS_append (a : Fin 2) :
    ∀ {n : ℕ} {v w : HVM}, iterS W ρ n v = some w → iterS W ρ n (v.append a) = some (w.append a)
  | 0, v, w, h => by simp [iterS] at h ⊢; rw [h]
  | n + 1, v, w, h => by
    simp only [iterS] at h ⊢
    cases hs : stepS W ρ v with
    | none => simp [hs] at h
    | some v' =>
      rw [hs, Option.bind_some] at h
      rw [stepS_append a hs, Option.bind_some]
      exact iterS_append a h

end Append

end PalPeg.ScaHeadSafe
