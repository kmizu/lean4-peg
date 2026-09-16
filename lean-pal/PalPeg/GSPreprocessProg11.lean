import PalPeg.GSPreprocessProg10

/-! # Arithmetic invariant for a one-scratch scaled comparison

Each successful transaction removes `k` marks from the right counter and
one from the left counter. A failed transaction restores its partial work.
The recursion below describes completed transactions, not program fuel.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {blank mark : Fin sc}

/-- A temporary flag is overwritten by the next write before any movement.
This equality is for the entire machine state, including untouched tapes. -/
theorem ct_overwrite_stay (c : CT sc) (t : Tapes sc)
    (a b : Fin sc) (m : Move) :
    applyAct blank (applyAct blank t (c.act a .stay)) (c.act b m) =
      applyAct blank t (c.act b m) := by
  apply tapes_ext
  intro j
  simp only [getT_applyAct, c.tape_eq, c.write_eq, c.move_eq]
  by_cases h : j = c.idx
  · subst j
    simp only [c.get_eq]
    cases c.get t
    cases m <;> rfl
  · simp only [if_neg h]

/-- The false marker used to exit a failed scaled comparison leaves no
trace: the positive operand is restored exactly, not just numerically. -/
theorem ct_false_probe_restore (c : CT sc) {n : ℕ} (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) (n + 1)) :
    applyActs blank [c.act blank .left, c.act mark .stay,
      c.act blank .right] t = t := by
  simp only [applyActs, List.foldl_cons, List.foldl_nil]
  rw [ct_overwrite_stay]
  have hp : probe blank (c.get t) = blank := (probe_eq hq).trans (by simp)
  simpa only [hp] using ct_probe_restore c t hq

/-- Clearing the failure flag at a normal counter head restores its whole
tape, since a normal head was blank before the flag was written. -/
theorem ct_flag_restore (c : CT sc) {n : ℕ} (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) n) :
    applyActs blank [c.act mark .stay, c.act blank .stay] t = t := by
  simp only [applyActs, List.foldl_cons, List.foldl_nil]
  rw [ct_overwrite_stay]
  apply tapes_ext
  intro j
  simp only [getT_applyAct, c.tape_eq, c.write_eq, c.move_eq]
  by_cases h : j = c.idx
  · subst j
    simp only [c.get_eq]
    have hf := hq.focus_blank
    cases he : c.get t
    simp only [he] at hf
    simp [Tape.step, TapeConfiguration.applyAction, hf]
  · simp only [if_neg h]

theorem ct_other_step (c d : CT sc) (hne : c.idx ≠ d.idx)
    (t : Tapes sc) (a : Fin sc) (m : Move) :
    c.get (applyAct blank t (d.act a m)) = c.get t := by
  rw [← c.get_eq, getT_applyAct]
  simp only [d.tape_eq, if_neg hne, c.get_eq]

/-- The full failed-loop exit clears the scratch flag and the operand's
false probe. No assumption about the other ten tapes is needed. -/
theorem cmul_failure_flags_restore (left scratch : CT sc)
    (hne : left.idx ≠ scratch.idx) {a e : ℕ} (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) (a + 1))
    (he : Tape.CounterView' blank mark (scratch.get t) e) :
    applyActs blank [scratch.act mark .stay, left.act blank .left,
      left.act mark .stay, left.act blank .right, scratch.act blank .stay] t = t := by
  have ha' : Tape.CounterView' blank mark
      (left.get (applyAct blank t (scratch.act mark .stay))) (a + 1) := by
    rw [ct_other_step left scratch hne]
    exact ha
  have hr := ct_false_probe_restore left _ ha'
  simp only [applyActs, List.foldl_cons, List.foldl_nil] at hr ⊢
  rw [hr]
  exact ct_flag_restore scratch t he

/-- Complete transactions can also be undone exactly by `k` increments.
This is stronger than restoring the counter view: untouched tapes and the
original finite tape representation are recovered as well. -/
theorem tryDec_success_restore (c : CT sc) (k n : ℕ) (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) n) (hk : k ≤ n) :
    applyActs blank (List.replicate k (c.act blank .right))
      (applyActs blank (tryDecL c blank mark k n t) t) = t := by
  induction k generalizing n t with
  | zero => rfl
  | succ k ih =>
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hq1 : Tape.CounterView' blank mark (c.get (dStep c blank t)) n := by
      rw [dStep, c.step_eq, c.step_eq]
      exact Tape.counter'_dec hq
    have hi := ih n _ hq1 (by omega)
    rw [List.replicate_succ']
    simp only [tryDecL, if_neg (by omega : ¬ n < k), applyActs,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
    change applyAct blank (applyActs blank (List.replicate k (c.act blank .right))
      (applyActs blank (tryDecL c blank mark k n (dStep c blank t))
        (dStep c blank t))) (c.act blank .right) = t
    rw [hi]
    exact ct_dec_inc_restore c t hq

theorem ct_repeat_other (c d : CT sc) (hne : c.idx ≠ d.idx)
    (a : Fin sc) (m : Move) (k : ℕ) (t : Tapes sc) :
    c.get (applyActs blank (List.replicate k (d.act a m)) t) = c.get t := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, applyActs, List.foldl_cons]
    change c.get (applyActs blank (List.replicate k (d.act a m))
      (applyAct blank t (d.act a m))) = c.get t
    rw [ih, ct_other_step c d hne]

theorem ct_repeat_inc {Terminal : Type} {endSym : Fin sc}
    (c : CT sc) (k : ℕ) (t : Tapes sc) :
    ExecA Terminal blank endSym mark (repeatProg (.act (c.idx, .blk, .right)) k)
      t (List.replicate k (c.act blank .right)) := by
  induction k generalizing t with
  | zero => exact execA_skip
  | succ k ih =>
    exact execA_seq (execA_ct_put c .right t) (ih _)

def CMUL_RESTORE (left right : Fin 12) (k : ℕ) : Prog A9 Cond9 :=
  DLOOP tCe (.seq (.act (left, .blk, .right))
    (repeatProg (.act (right, .blk, .right)) k))

def cmulRestoreUnit (left right : CT sc) (blank : Fin sc) (k : ℕ) : List (Act sc) :=
  left.act blank .right :: List.replicate k (right.act blank .right)

def cmulRestoreL (left right : CT sc) (blank mark : Fin sc) (k e : ℕ) : List (Act sc) :=
  dPow ctCe blank (cmulRestoreUnit left right blank k) e ++ dTest ctCe blank mark

theorem CMUL_RESTORE_exec {Terminal : Type} {endSym : Fin sc}
    (left right : CT sc) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (hmark : mark ≠ blank) (k e : ℕ) (t : Tapes sc)
    (he : Tape.CounterView' blank mark t.Ce e) :
    ExecA Terminal blank endSym mark (CMUL_RESTORE left.idx right.idx k) t
      (cmulRestoreL left right blank mark k e) := by
  apply dLoop_exec ctCe _ _ hmark
  · intro u
    exact execA_seq (execA_ct_put left .right u) (ct_repeat_inc right k _)
  · intro u
    change ctCe.get (applyActs blank (List.replicate k (right.act blank .right))
      (applyAct blank u (left.act blank .right))) = ctCe.get u
    rw [ct_repeat_other ctCe right hr, ct_other_step ctCe left hl]
  · exact he

theorem cmulRestoreL_length (left right : CT sc) (k e : ℕ) :
    (cmulRestoreL left right blank mark k e).length = e * (k + 3) + 2 := by
  simp [cmulRestoreL, cmulRestoreUnit, dTest, Nat.add_comm]

theorem ct_repeat_inc_counter (c : CT sc) (k n : ℕ) (t : Tapes sc)
    (h : Tape.CounterView' blank mark (c.get t) n) :
    Tape.CounterView' blank mark
      (c.get (applyActs blank (List.replicate k (c.act blank .right)) t)) (n + k) := by
  induction k generalizing n t with
  | zero => exact h
  | succ k ih =>
    have h1 : Tape.CounterView' blank mark
        (c.get (applyAct blank t (c.act blank .right))) (n + 1) := by
      rw [c.step_eq]
      exact Tape.counter'_inc h
    simpa only [List.replicate_succ, applyActs, List.foldl_cons, Nat.add_assoc,
      Nat.add_comm 1 k] using ih (n + 1) _ h1

theorem cmulRestoreUnit_counter (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (k a b e : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce e) :
    let u := applyActs blank (cmulRestoreUnit left right blank k) t
    Tape.CounterView' blank mark (left.get u) (a + 1) ∧
    Tape.CounterView' blank mark (right.get u) (b + k) ∧
    Tape.CounterView' blank mark u.Ce e := by
  dsimp only
  change Tape.CounterView' blank mark (left.get
    (applyActs blank (List.replicate k (right.act blank .right))
      (applyAct blank t (left.act blank .right)))) (a + 1) ∧ _
  constructor
  · rw [ct_repeat_other left right hlr, left.step_eq]
    exact Tape.counter'_inc ha
  constructor
  · apply ct_repeat_inc_counter
    rw [ct_other_step right left (Ne.symm hlr)]
    exact hb
  · change Tape.CounterView' blank mark (ctCe.get
      (applyActs blank (List.replicate k (right.act blank .right))
        (applyAct blank t (left.act blank .right)))) e
    rw [ct_repeat_other ctCe right hr, ct_other_step ctCe left hl]
    exact he

theorem cmulRestorePow_counter (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (k e a b : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce e) :
    let u := applyActs blank (dPow ctCe blank (cmulRestoreUnit left right blank k) e) t
    Tape.CounterView' blank mark (left.get u) (a + e) ∧
    Tape.CounterView' blank mark (right.get u) (b + k * e) ∧
    Tape.CounterView' blank mark u.Ce 0 := by
  induction e generalizing a b t with
  | zero => exact ⟨ha, hb, he⟩
  | succ e ih =>
    have ha1 : Tape.CounterView' blank mark (left.get (dStep ctCe blank t)) a := by
      simp only [dStep, ct_other_step left ctCe (Ne.symm hl)]
      exact ha
    have hb1 : Tape.CounterView' blank mark (right.get (dStep ctCe blank t)) b := by
      simp only [dStep, ct_other_step right ctCe (Ne.symm hr)]
      exact hb
    have he1 : Tape.CounterView' blank mark (dStep ctCe blank t).Ce e :=
      Tape.counter'_dec he
    have hu := cmulRestoreUnit_counter left right hlr hl hr k a b e _ ha1 hb1 he1
    have hi := ih (a + 1) (b + k) _ hu.1 hu.2.1 hu.2.2
    simpa only [dPow, dUnit, applyActs, List.foldl_append, List.foldl_cons,
      dStep, Nat.mul_succ, Nat.add_assoc, Nat.add_comm 1 e, Nat.add_comm k (k * e)]
      using hi

theorem CMUL_RESTORE_counter (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (hmark : mark ≠ blank) (k e a b : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce e) :
    let u := applyActs blank (cmulRestoreL left right blank mark k e) t
    Tape.CounterView' blank mark (left.get u) (a + e) ∧
    Tape.CounterView' blank mark (right.get u) (b + k * e) ∧
    Tape.CounterView' blank mark u.Ce 0 := by
  have hp := cmulRestorePow_counter left right hlr hl hr k e a b t ha hb he
  dsimp only at hp ⊢
  rw [cmulRestoreL, applyActs_append, ct_dTest_restore ctCe hmark _ hp.2.2]
  exact hp

/-- Finite scaled comparison candidate, with `tCe` as its sole scratch
counter. The operands must be distinct from each other and from `tCe`.
On an unsuccessful transaction, the left probe is marked to stop the loop;
the scratch head records failure until the exit branch clears both flags.
Semantic execution and restoration are proved separately from the arithmetic
invariant below; this definition alone is not a correctness theorem. -/
def CMUL_LE (left right : Fin 12) (k : ℕ)
    (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  let restore := CMUL_RESTORE left right k
  let success := .seq (.act (left, .blk, .left))
    (.seq (.act (left, .blk, .stay))
      (.seq (.act (tCe, .blk, .right)) (.act (left, .blk, .left))))
  let failure := .seq (.act (tCe, .mrk, .stay))
    (.seq (.act (left, .blk, .left)) (.act (left, .mrk, .stay)))
  .seq (.act (left, .blk, .left))
    (.seq (.loop (.notMark left) (left, .keep, .right)
      (TRY_DEC right k success failure))
      (.ite (.notMark tCe)
        (.seq (.act (left, .keep, .right)) (.seq restore yes))
        (.seq (.act (left, .blk, .right))
          (.seq (.act (tCe, .blk, .stay)) (.seq restore no)))))

def scaledGroups (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | a + 1, b => if k ≤ b then scaledGroups k a (b - k) + 1 else 0

theorem scaledGroups_spec (k a b : ℕ) :
    scaledGroups k a b ≤ a ∧
    k * scaledGroups k a b ≤ b ∧
    (scaledGroups k a b = a ∨ b - k * scaledGroups k a b < k) := by
  induction a generalizing b with
  | zero => simp [scaledGroups]
  | succ a ih =>
    by_cases h : k ≤ b
    · have hi := ih (b - k)
      simp only [scaledGroups, if_pos h, Nat.mul_add, Nat.mul_one]
      constructor
      · omega
      constructor
      · omega
      · rcases hi.2.2 with he | he
        · left; omega
        · right; omega
    · simp [scaledGroups, h]
      omega

theorem scaledGroups_complete_iff (k a b : ℕ) :
    scaledGroups k a b = a ↔ k * a ≤ b := by
  have h := scaledGroups_spec k a b
  constructor
  · intro he
    simpa only [he] using h.2.1
  · intro hab
    rcases h.2.2 with he | hr
    · exact he
    · by_contra hn
      have hs : scaledGroups k a b + 1 ≤ a := by omega
      have hm := Nat.mul_le_mul_left k hs
      simp only [Nat.mul_add, Nat.mul_one] at hm
      omega

theorem scaledGroups_restore (k a b : ℕ) :
    a - scaledGroups k a b + scaledGroups k a b = a ∧
    b - k * scaledGroups k a b + k * scaledGroups k a b = b := by
  have h := scaledGroups_spec k a b
  omega

theorem scaledGroups_eq_min_div {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    scaledGroups k a b = min a (b / k) := by
  have h := scaledGroups_spec k a b
  have hd : scaledGroups k a b ≤ b / k :=
    (Nat.le_div_iff_mul_le hk).2 (by simpa [Nat.mul_comm] using h.2.1)
  rcases h.2.2 with he | hr
  · omega
  · have hb : b < (scaledGroups k a b + 1) * k := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (scaledGroups k a b) k]
      omega
    have hu : b / k < scaledGroups k a b + 1 :=
      (Nat.div_lt_iff_lt_mul hk).2 hb
    omega

/-- Successful transactions inspect at most the original right counter;
the final failed transaction can inspect fewer than `k` further marks. -/
theorem scaledGroups_work_bound (k a b : ℕ) :
    k * scaledGroups k a b + min k (b - k * scaledGroups k a b) ≤ b := by
  have h := scaledGroups_spec k a b
  have hm := Nat.min_le_right k (b - k * scaledGroups k a b)
  omega

/-- info: 'PalPeg.GSPreProg.scaledGroups_complete_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms scaledGroups_complete_iff

/-- info: 'PalPeg.GSPreProg.cmul_failure_flags_restore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cmul_failure_flags_restore

/-- info: 'PalPeg.GSPreProg.tryDec_success_restore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tryDec_success_restore

/-- info: 'PalPeg.GSPreProg.CMUL_RESTORE_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMUL_RESTORE_exec

/-- info: 'PalPeg.GSPreProg.CMUL_RESTORE_counter' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CMUL_RESTORE_counter

end PalPeg.GSPreProg
