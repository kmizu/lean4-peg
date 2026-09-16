import PalPeg.GSPreprocessProg9

/-! # Bounded decrement with rollback

The bound is static. If the counter is too small, every decrement is undone
before the failure continuation runs. This lets a scaled comparison use one
scratch counter, storing only complete groups.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

theorem tapes_ext {t u : Tapes sc} (h : ∀ j, getT t j = getT u j) : t = u := by
  cases t
  cases u
  simp only [Tapes.mk.injEq]
  exact ⟨h tV1, h tV2, h tCd, h tCq, h tCe, h tCp, h tCf, h tCs, h tCr,
    h tCa, h tCb, h tCc⟩

theorem ct_probe_restore (c : CT sc) {n : ℕ} (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) n) :
    applyAct blank (applyAct blank t (c.act blank .left))
      (c.act (probe blank (c.get t)) .right) = t := by
  apply tapes_ext
  intro j
  simp only [getT_applyAct, c.tape_eq, c.write_eq, c.move_eq]
  by_cases h : j = c.idx
  · subst j
    simp only [if_pos rfl, c.get_eq]
    exact counter_probe_restore hq
  · simp only [if_neg h]

theorem ct_dec_inc_restore (c : CT sc) {n : ℕ} (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) (n + 1)) :
    applyAct blank (dStep c blank t) (c.act blank .right) = t := by
  have hp : probe blank (c.get t) = blank := by
    exact (probe_eq hq).trans (by simp)
  have hs : dStep c blank t = applyAct blank t (c.act blank .left) := by
    apply tapes_ext
    intro j
    simp only [dStep, getT_applyAct, c.tape_eq, c.write_eq, c.move_eq]
    by_cases h : j = c.idx
    · subst j
      simp only [if_pos rfl, c.get_eq]
      have hf : (Tape.step blank (c.get t) blank .left).focus = blank := hp
      cases he : Tape.step blank (c.get t) blank .left
      simp only [he] at hf
      simp [Tape.step, TapeConfiguration.applyAction, hf]
    · simp only [if_neg h]
  have h := ct_probe_restore c t hq
  rw [hp] at h
  rw [hs]
  exact h

theorem ct_dTest_restore (c : CT sc) (hmark : mark ≠ blank) (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) 0) :
    applyActs blank (dTest c blank mark) t = t := by
  have h := ct_probe_restore c t hq
  rw [(probe_iff hmark hq).2 rfl] at h
  exact h

def TRY_DEC (j : Fin 12) : ℕ → Prog A9 Cond9 → Prog A9 Cond9 → Prog A9 Cond9
  | 0, yes, _ => yes
  | k + 1, yes, no => .seq (.act (j, .blk, .left))
      (.ite (.notMark j)
        (.seq (.act (j, .blk, .stay)) (TRY_DEC j k yes (.seq (.act (j, .blk, .right)) no)))
        (.seq (.act (j, .mrk, .right)) no))

def tryDecL (c : CT sc) (blank mark : Fin sc) : ℕ → ℕ → Tapes sc → List (Act sc)
  | 0, _, _ => []
  | _ + 1, 0, _ => dTest c blank mark
  | k + 1, n + 1, t => [c.act blank .left, c.act blank .stay] ++
      tryDecL c blank mark k n (dStep c blank t) ++
        (if n < k then [c.act blank .right] else [])

theorem tryDec_failure (c : CT sc) (hmark : mark ≠ blank) (k n : ℕ) (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) n) (hfail : n < k) :
    applyActs blank (tryDecL c blank mark k n t) t = t := by
  induction k generalizing n t with
  | zero => omega
  | succ k ih =>
    cases n with
    | zero => exact ct_dTest_restore c hmark t hq
    | succ n =>
      have hq1 : Tape.CounterView' blank mark (c.get (dStep c blank t)) n := by
        rw [dStep, c.step_eq, c.step_eq]
        exact Tape.counter'_dec hq
      have hi := ih n _ hq1 (by omega)
      simp only [tryDecL, if_pos (by omega : n < k), applyActs, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      change applyAct blank (applyActs blank (tryDecL c blank mark k n (dStep c blank t))
        (dStep c blank t)) (c.act blank .right) = t
      rw [hi]
      exact ct_dec_inc_restore c t hq

theorem tryDec_counter (c : CT sc) (hmark : mark ≠ blank) (k n : ℕ) (t : Tapes sc)
    (hq : Tape.CounterView' blank mark (c.get t) n) :
    Tape.CounterView' blank mark (c.get (applyActs blank (tryDecL c blank mark k n t) t))
      (if k ≤ n then n - k else n) := by
  by_cases h : k ≤ n
  · rw [if_pos h]
    induction k generalizing n t with
    | zero => exact hq
    | succ k ih =>
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hq1 : Tape.CounterView' blank mark (c.get (dStep c blank t)) n := by
        rw [dStep, c.step_eq, c.step_eq]
        exact Tape.counter'_dec hq
      have hi := ih n _ hq1 (by omega)
      simpa only [tryDecL, if_neg (by omega : ¬ n < k), applyActs, List.foldl_append,
        List.foldl_cons, List.foldl_nil, Nat.succ_sub_succ, dStep] using hi
  · rw [if_neg h, tryDec_failure c hmark k n t hq (by omega)]
    exact hq

theorem tryDec_length (c : CT sc) (k n : ℕ) (t : Tapes sc) :
    (tryDecL c blank mark k n t).length ≤ 3 * min k n + 2 := by
  induction k generalizing n t with
  | zero => simp [tryDecL]
  | succ k ih =>
    cases n with
    | zero => simp [tryDecL, dTest]
    | succ n =>
      have hi := ih n (dStep c blank t)
      simp only [tryDecL, List.length_append, List.length_cons, List.length_nil,
        Nat.succ_min_succ]
      split <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem TRY_DEC_exec (c : CT sc) (hmark : mark ≠ blank) (k : ℕ) :
    ∀ (n : ℕ) (yes no : Prog A9 Cond9) (t : Tapes sc) (L : List (Act sc)),
    Tape.CounterView' blank mark (c.get t) n →
    ExecA Terminal blank endSym mark (if k ≤ n then yes else no)
      (applyActs blank (tryDecL c blank mark k n t) t) L →
    ExecA Terminal blank endSym mark (TRY_DEC c.idx k yes no) t
      (tryDecL c blank mark k n t ++ L) := by
  induction k with
  | zero =>
    intro n yes no t L hq hx
    simpa only [TRY_DEC, tryDecL, if_pos (Nat.zero_le n), applyActs, List.foldl_nil,
      List.nil_append] using hx
  | succ k ih =>
    intro n yes no t L hq hx
    have hread : (getT (applyActs blank [c.act blank .left] t) c.idx).focus =
        if n = 0 then mark else blank := by
      simp only [applyActs, List.foldl_cons, List.foldl_nil, c.get_eq, c.step_eq]
      exact Tape.counter'_read_after_probe hq
    cases n with
    | zero =>
      have hn : ¬ k + 1 ≤ 0 := by omega
      simp only [if_neg hn, tryDecL] at hx ⊢
      apply execA_seq (execA_ct_put c .left t)
      apply execA_ite_neg
      · simp only [condOf9, hread, ite_true, ne_eq, not_true_eq_false, decide_false]
      · exact execA_seq (execA_ct_mark c .right _) hx
    | succ n =>
      have hq1 : Tape.CounterView' blank mark (c.get (dStep c blank t)) n := by
        rw [dStep, c.step_eq, c.step_eq]
        exact Tape.counter'_dec hq
      have hc : condOf9 endSym mark (.notMark c.idx)
          (fun j => (getT (applyActs blank [c.act blank .left] t) j).focus) = true := by
        simp only [condOf9, hread, if_neg (Nat.succ_ne_zero n), decide_eq_true_eq]
        exact Ne.symm hmark
      by_cases h : n < k
      · have hn : ¬ k ≤ n := by omega
        have hn' : ¬ k + 1 ≤ n + 1 := by omega
        simp only [if_neg hn', tryDecL, if_pos h, applyActs_append] at hx
        have hm : ExecA Terminal blank endSym mark (.seq (.act (c.idx, .blk, .right)) no)
            (applyActs blank (tryDecL c blank mark k n (dStep c blank t)) (dStep c blank t))
            ([c.act blank .right] ++ L) := execA_seq (execA_ct_put c .right _) hx
        have hi := ih n yes (.seq (.act (c.idx, .blk, .right)) no) _ _ hq1
          (by simpa only [if_neg hn] using hm)
        have hh := execA_seq (execA_ct_put c .left t)
          (execA_ite_pos (Q := .seq (.act (c.idx, .mrk, .right)) no) hc
            (execA_seq (execA_ct_put c .stay _) hi))
        exact execA_of_eq (by simp only [tryDecL, if_pos h, List.append_assoc]; rfl) hh
      · have hn : k ≤ n := by omega
        have hn' : k + 1 ≤ n + 1 := by omega
        simp only [if_pos hn', tryDecL, if_neg h, List.append_nil, applyActs_append] at hx
        have hi := ih n yes (.seq (.act (c.idx, .blk, .right)) no) _ _ hq1
          (by simpa only [if_pos hn, applyActs, List.foldl_cons, List.foldl_nil, dStep] using hx)
        have hh := execA_seq (execA_ct_put c .left t)
          (execA_ite_pos (Q := .seq (.act (c.idx, .mrk, .right)) no) hc
            (execA_seq (execA_ct_put c .stay _) hi))
        exact execA_of_eq (by simp only [tryDecL, if_neg h, List.append_nil, List.append_assoc]; rfl) hh

theorem tryDec_other (c : CT sc) (j : Fin 12) (h : j ≠ c.idx)
    (k n : ℕ) (t : Tapes sc) :
    getT (applyActs blank (tryDecL c blank mark k n t) t) j = getT t j := by
  induction k generalizing n t with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => simp [tryDecL, dTest, applyActs, getT_applyAct, c.tape_eq, h]
    | succ n =>
      simp only [tryDecL, applyActs_append]
      split
      · change getT (applyAct blank
          (applyActs blank (tryDecL c blank mark k n (dStep c blank t)) (dStep c blank t))
          (c.act blank .right)) j = getT t j
        rw [getT_applyAct, c.tape_eq, if_neg h, ih]
        simp [dStep, getT_applyAct, c.tape_eq, h]
      · change getT (applyActs blank (tryDecL c blank mark k n (dStep c blank t))
          (dStep c blank t)) j = getT t j
        rw [ih]
        simp [dStep, getT_applyAct, c.tape_eq, h]

theorem tryDec_cq_enc {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k : ℕ) {a b D Q E P F S R : ℕ} {g : Ctr3} {t : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g t) :
    EncS blank startSym endSym mark x a b
      ⟨D, (if k ≤ Q then Q - k else Q), E, P, F, S, R⟩ g
      (applyActs blank (tryDecL ctCq blank mark k Q t) t) := by
  have ho (j : Fin 12) (h : j ≠ tCq) :=
    tryDec_other (blank := blank) (mark := mark) ctCq j h k Q t
  have hq := tryDec_counter ctCq hmark k Q t he.base.cq
  refine ⟨⟨?_, ?_, ?_, hq, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change Tape.SeqView blank (getT _ tV1) (pword startSym endSym x) (a + 1)
    rw [ho tV1 (by decide)]
    exact he.base.v1
  · change Tape.SeqView blank (getT _ tV2) (pword startSym endSym x) (b + 1)
    rw [ho tV2 (by decide)]
    exact he.base.v2
  · change Tape.CounterView' blank mark (getT _ tCd) D
    rw [ho tCd (by decide)]
    exact he.base.cd
  · change Tape.CounterView' blank mark (getT _ tCe) E
    rw [ho tCe (by decide)]
    exact he.base.ce
  · change Tape.CounterView' blank mark (getT _ tCp) P
    rw [ho tCp (by decide)]
    exact he.base.cp
  · change Tape.CounterView' blank mark (getT _ tCf) F
    rw [ho tCf (by decide)]
    exact he.base.cf
  · change Tape.CounterView' blank mark (getT _ tCs) S
    rw [ho tCs (by decide)]
    exact he.base.cs
  · change Tape.CounterView' blank mark (getT _ tCr) R
    rw [ho tCr (by decide)]
    exact he.base.cr
  · change Tape.CounterView' blank mark (getT _ tCa) g.ap
    rw [ho tCa (by decide)]
    exact he.ca
  · change Tape.CounterView' blank mark (getT _ tCb) g.an
    rw [ho tCb (by decide)]
    exact he.cb
  · change Tape.CounterView' blank mark (getT _ tCc) g.bn
    rw [ho tCc (by decide)]
    exact he.cc

/-- info: 'PalPeg.GSPreProg.TRY_DEC_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TRY_DEC_exec

end PalPeg.GSPreProg
