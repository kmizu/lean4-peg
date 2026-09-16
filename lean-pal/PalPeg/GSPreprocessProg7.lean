import PalPeg.GSPreprocessProg6

/-! # Counter-driven groups

The loop tests `Cq`, restores its normal head position, runs one group, and
tests again. The decreasing natural number below belongs only to the proof;
the program uses no input-dependent unrolling or external fuel.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def qProbe (blank : Fin sc) (ts : Tapes sc) : Tapes sc :=
  applyAct blank ts (Act.Cq blank .left)

def qGroupRun (body : Prog A9 Cond9) : Prog A9 Cond9 :=
  .loop (.notMark tCq) (tCq, .keep, .right)
    (.seq body (.act (tCq, .blk, .left)))

def QGROUP (body : Prog A9 Cond9) : Prog A9 Cond9 :=
  .seq (.act (tCq, .blk, .left))
    (.seq (qGroupRun body) (.act (tCq, .keep, .right)))

theorem qProbe_restore {n : ℕ} (ts : Tapes sc)
    (hq : Tape.CounterView' blank mark ts.Cq n) :
    applyAct blank (qProbe blank ts) (Act.Cq (qProbe blank ts).Cq.focus .right) = ts := by
  have h := counter_probe_restore hq
  change Tape.step blank (Tape.step blank ts.Cq blank .left)
    (Tape.step blank ts.Cq blank .left).focus .right = ts.Cq at h
  change { ts with Cq := (Tape.step blank (Tape.step blank ts.Cq blank .left)
      (Tape.step blank ts.Cq blank .left).focus .right) } = ts
  rw [h]

theorem qGroup_cont (body : Prog A9 Cond9) {n : ℕ} (ts : Tapes sc)
    (hmark : mark ≠ blank) (hq : Tape.CounterView' blank mark ts.Cq n) (hn : 0 < n)
    {B L : List (Act sc)} (hb : ExecA Terminal blank endSym mark body ts B)
    (hl : ExecA Terminal blank endSym mark (qGroupRun body)
      (qProbe blank (applyActs blank B ts)) L) :
    ExecA Terminal blank endSym mark (qGroupRun body) (qProbe blank ts)
      ([Act.Cq (qProbe blank ts).Cq.focus .right] ++
        (B ++ [Act.Cq blank .left]) ++ L) := by
  have hr := qProbe_restore ts hq
  have hread : (qProbe blank ts).Cq.focus = blank := by
    have h := Tape.counter'_read_after_probe hq
    simpa only [if_neg (by omega : n ≠ 0), qProbe, applyAct, Tape.read] using h
  apply execA_loop_cont (L₁ := B ++ [Act.Cq blank .left]) (L₂ := L) rfl rfl rfl
  · simp only [condOf9, getT, tCq, hread, decide_eq_true_eq]
    exact Ne.symm hmark
  · rw [hr]
    exact execA_seq hb (execA_ct_put ctCq .left _)
  · simp only [applyActs, List.foldl_append, List.foldl_cons, List.foldl_nil, hr]
    exact hl

/-- An arbitrary semantic invariant can be carried across the finite grouping
loop. One iteration consumes `min k n`; its overhead is charged explicitly. -/
theorem qGroupRun_spec (body : Prog A9 Cond9) (R : ℕ → Tapes sc → Prop)
    (k C : ℕ) (hk : 0 < k) (hmark : mark ≠ blank)
    (hq : ∀ n ts, R n ts → Tape.CounterView' blank mark ts.Cq n)
    (hbody : ∀ n ts, R n ts → 0 < n →
      ∃ B, ExecA Terminal blank endSym mark body ts B ∧
        R (n - min k n) (applyActs blank B ts) ∧
        B.length ≤ min k n * C + 3)
    (n : ℕ) (ts : Tapes sc) (hR : R n ts) :
    ∃ L fin, ExecA Terminal blank endSym mark (qGroupRun body) (qProbe blank ts) L ∧
      applyActs blank L (qProbe blank ts) = qProbe blank fin ∧ R 0 fin ∧
      L.length ≤ n * C + 5 * stays k n 0 := by
  induction n using Nat.strong_induction_on generalizing ts with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      refine ⟨[], ts, ?_, rfl, hR, by simp [stays]⟩
      apply execA_loop_stop
      have hp := (probe_iff hmark (hq 0 ts hR)).2 rfl
      change decide ((qProbe blank ts).Cq.focus ≠ mark) = false
      change decide (probe blank ts.Cq ≠ mark) = false
      simp only [hp, ne_eq, not_true_eq_false, decide_false]
    · obtain ⟨B, hb, hnext, hlen⟩ := hbody n ts hR (by omega)
      have hlt : n - min k n < n := by omega
      obtain ⟨L, fin, hl, he, hf, hc⟩ := ih _ hlt _ hnext
      refine ⟨[Act.Cq (qProbe blank ts).Cq.focus .right] ++
        (B ++ [Act.Cq blank .left]) ++ L, fin,
        qGroup_cont body ts hmark (hq n ts hR) (by omega) hb hl, ?_, hf, ?_⟩
      · simp only [applyActs, List.foldl_append, List.foldl_cons, List.foldl_nil,
          qProbe_restore ts (hq n ts hR)]
        exact he
      · have hs := stays_block k n hk (by omega)
        have hm : n = min k n + (n - min k n) := by omega
        simp only [List.length_append, List.length_cons, List.length_nil]
        have hmC : n * C = min k n * C + (n - min k n) * C := by
          conv_lhs => rw [hm, Nat.add_mul]
        rw [hs, hmC]
        nlinarith

theorem QGROUP_spec (body : Prog A9 Cond9) (R : ℕ → Tapes sc → Prop)
    (k C : ℕ) (hk : 0 < k) (hmark : mark ≠ blank)
    (hq : ∀ n ts, R n ts → Tape.CounterView' blank mark ts.Cq n)
    (hbody : ∀ n ts, R n ts → 0 < n →
      ∃ B, ExecA Terminal blank endSym mark body ts B ∧
        R (n - min k n) (applyActs blank B ts) ∧
        B.length ≤ min k n * C + 3)
    (n : ℕ) (ts : Tapes sc) (hR : R n ts) :
    ∃ L, ExecA Terminal blank endSym mark (QGROUP body) ts L ∧
      R 0 (applyActs blank L ts) ∧ L.length ≤ n * C + 5 * stays k n 0 + 2 := by
  obtain ⟨L, fin, hl, he, hf, hc⟩ :=
    qGroupRun_spec body R k C hk hmark hq hbody n ts hR
  let tail := [Act.Cq (qProbe blank fin).Cq.focus .right]
  have hr : applyActs blank tail (qProbe blank fin) = fin := qProbe_restore fin (hq 0 fin hf)
  refine ⟨[Act.Cq blank .left] ++ (L ++ tail), ?_, ?_, ?_⟩
  · apply execA_seq (execA_ct_put ctCq .left ts)
    apply execA_seq hl
    change ExecA Terminal blank endSym mark (.act (tCq, .keep, .right))
      (applyActs blank L (qProbe blank ts)) tail
    rw [he]
    exact execA_ct_keep ctCq .right _
  · simp only [applyActs_append, applyActs, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change R 0 (applyActs blank tail (applyActs blank L (qProbe blank ts)))
    rw [he, hr]
    exact hf
  · simpa only [List.length_append, List.length_cons, List.length_nil, tail] using
      (by omega : 1 + (L.length + 1) ≤ n * C + 5 * stays k n 0 + 2)

end PalPeg.GSPreProg
