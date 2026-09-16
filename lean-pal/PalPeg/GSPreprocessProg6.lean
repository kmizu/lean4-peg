import PalPeg.GSPreprocessProg5

/-! # Bounded blocks for counter-driven finite control

A block consumes at most its static bound, stopping early when `Cq` is zero.
The bound will be the fixed exponent, never an input length.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def QBLOCK (rest : Prog A9 Cond9) : ℕ → Prog A9 Cond9
  | 0 => .skip
  | k + 1 => .seq (.act (tCq, .blk, .left))
      (.ite (.notMark tCq)
        (.seq (.act (tCq, .blk, .stay)) (.seq rest (QBLOCK rest k)))
        (.act (tCq, .mrk, .right)))

def qBlockL (blank mark : Fin sc) (restL : Tapes sc → List (Act sc)) :
    ℕ → ℕ → Tapes sc → List (Act sc)
  | 0, _, _ => []
  | _ + 1, 0, _ => dTest ctCq blank mark
  | k + 1, n + 1, ts =>
      [Act.Cq blank .left, Act.Cq blank .stay] ++ restL (dStep ctCq blank ts) ++
        qBlockL blank mark restL k n
          (applyActs blank (restL (dStep ctCq blank ts)) (dStep ctCq blank ts))

theorem qBlock_exec (rest : Prog A9 Cond9) (restL : Tapes sc → List (Act sc))
    (hmark : mark ≠ blank)
    (hrest : ∀ ts, ExecA Terminal blank endSym mark rest ts (restL ts))
    (hget : ∀ ts, (applyActs blank (restL ts) ts).Cq = ts.Cq)
    (k n : ℕ) (ts : Tapes sc) (hq : Tape.CounterView' blank mark ts.Cq n) :
    ExecA Terminal blank endSym mark (QBLOCK rest k) ts (qBlockL blank mark restL k n ts) := by
  induction k generalizing n ts with
  | zero => exact execA_skip
  | succ k ih =>
    have hread : (getT (applyActs blank [ctCq.act blank .left] ts) tCq).focus =
        if n = 0 then mark else blank := Tape.counter'_read_after_probe hq
    cases n with
    | zero =>
      apply execA_seq (execA_ct_put ctCq .left ts)
      apply execA_ite_neg
      · simp only [condOf9, decide_eq_false_iff_not, not_not]
        exact hread.trans (by simp)
      · exact execA_ct_mark ctCq .right _
    | succ n =>
      have hq1 : Tape.CounterView' blank mark (dStep ctCq blank ts).Cq n :=
        Tape.counter'_dec hq
      have hq2 : Tape.CounterView' blank mark
          (applyActs blank (restL (dStep ctCq blank ts)) (dStep ctCq blank ts)).Cq n := by
        rw [hget]; exact hq1
      have hi := ih n _ hq2
      have hx := execA_seq (execA_ct_put ctCq .left ts)
        (execA_ite_pos (P := .seq (.act (tCq, .blk, .stay)) (.seq rest (QBLOCK rest k)))
          (Q := .act (tCq, .mrk, .right))
          (c := .notMark tCq)
          (by simp only [condOf9, hread, if_neg (Nat.succ_ne_zero n), decide_eq_true_eq];
              exact Ne.symm hmark)
          (execA_seq (execA_ct_put ctCq .stay _)
            (execA_seq (hrest _) hi)))
      exact execA_of_eq (by simp [qBlockL, List.append_assoc, ctCq, dStep]) hx

theorem dTest_cq_effect (hmark : mark ≠ blank) (ts : Tapes sc)
    (hq : Tape.CounterView' blank mark ts.Cq 0) :
    applyActs blank (dTest ctCq blank mark) ts = ts := by
  have hp := (probe_iff hmark hq).2 rfl
  have he := counter_probe_restore hq
  rw [hp] at he
  change { ts with Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) mark .right } = ts
  rw [he]

theorem qBlock_effect (restL : Tapes sc → List (Act sc)) (hmark : mark ≠ blank)
    (hget : ∀ ts, (applyActs blank (restL ts) ts).Cq = ts.Cq)
    (k n : ℕ) (ts : Tapes sc) (hq : Tape.CounterView' blank mark ts.Cq n) :
    applyActs blank (qBlockL blank mark restL k n ts) ts =
      applyActs blank (dPowS ctCq blank restL (min k n) ts) ts := by
  induction k generalizing n ts with
  | zero => rfl
  | succ k ih =>
    cases n with
    | zero => exact dTest_cq_effect hmark ts hq
    | succ n =>
      have hq1 : Tape.CounterView' blank mark (dStep ctCq blank ts).Cq n := Tape.counter'_dec hq
      have hq2 : Tape.CounterView' blank mark
          (applyActs blank (restL (dStep ctCq blank ts)) (dStep ctCq blank ts)).Cq n := by
        rw [hget]; exact hq1
      have hi := ih n _ hq2
      simpa only [qBlockL, Nat.succ_min_succ, dPowS, applyActs, List.foldl_append,
        List.foldl_cons, List.foldl_nil, dStep, ctCq] using hi

theorem qBlock_length (restL : Tapes sc → List (Act sc)) (L : ℕ)
    (hL : ∀ ts, (restL ts).length ≤ L) (k n : ℕ) (ts : Tapes sc) :
    (qBlockL blank mark restL k n ts).length ≤ min k n * (L + 2) + 2 := by
  induction k generalizing n ts with
  | zero => simp [qBlockL]
  | succ k ih =>
    cases n with
    | zero => simp [qBlockL]
    | succ n =>
      have hi := ih n (applyActs blank (restL (dStep ctCq blank ts)) (dStep ctCq blank ts))
      have hr := hL (dStep ctCq blank ts)
      simp only [qBlockL, List.length_append, List.length_cons, List.length_nil, Nat.succ_min_succ]
      nlinarith

theorem qPow_counter (restL : Tapes sc → List (Act sc))
    (hget : ∀ ts, (applyActs blank (restL ts) ts).Cq = ts.Cq)
    (n m : ℕ) (ts : Tapes sc) (hq : Tape.CounterView' blank mark ts.Cq (m + n)) :
    Tape.CounterView' blank mark (applyActs blank (dPowS ctCq blank restL n ts) ts).Cq m := by
  induction n generalizing ts with
  | zero => exact hq
  | succ n ih =>
    have hq1 : Tape.CounterView' blank mark (dStep ctCq blank ts).Cq (m + n) :=
      Tape.counter'_dec (by simpa [Nat.add_assoc] using hq)
    have hq2 : Tape.CounterView' blank mark
        (applyActs blank (restL (dStep ctCq blank ts)) (dStep ctCq blank ts)).Cq (m + n) := by
      rw [hget]; exact hq1
    have hi := ih _ hq2
    simpa only [dPowS, applyActs, List.foldl_append, List.foldl_cons, dStep] using hi

theorem qBlock_counter (restL : Tapes sc → List (Act sc)) (hmark : mark ≠ blank)
    (hget : ∀ ts, (applyActs blank (restL ts) ts).Cq = ts.Cq)
    (k n : ℕ) (ts : Tapes sc) (hq : Tape.CounterView' blank mark ts.Cq n) :
    Tape.CounterView' blank mark (applyActs blank (qBlockL blank mark restL k n ts) ts).Cq
      (n - min k n) := by
  rw [qBlock_effect restL hmark hget k n ts hq]
  exact qPow_counter restL hget (min k n) (n - min k n) ts
    (by convert hq using 1; omega)

/-- Counting one block matches the original cyclic phase counter exactly. -/
theorem stays_block (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    stays k n 0 = stays k (n - min k n) 0 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases h : k ≤ m + 1
  · rw [Nat.min_eq_left h]
    simp only [stays]
    have hm : m = (m + 1 - k) + (k - 1) := by omega
    have he : stays k m (k - 1) = stays k (m + 1 - k) 0 := by
      calc
        _ = stays k ((m + 1 - k) + (k - 1)) (k - 1) := congrArg (fun t => stays k t (k - 1)) hm
        _ = _ := stays_shift k (k - 1) (m + 1 - k)
    rw [he]
  · rw [Nat.min_eq_right (by omega)]
    simp only [Nat.sub_self, stays]
    rw [stays_small k m (k - 1) (by omega)]

end PalPeg.GSPreProg
