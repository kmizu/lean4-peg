import PalPeg.GSPreprocessProg13

/-! # Read-only finite control for the second-phase abort test -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

/-- This decision tree is evaluated with the positive signed counters probed. -/
def sAbortBranch (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .ite .v2NotEnd (.ite .v12Eq
    (.ite (.notMark tCa) no (.ite (.notMark tCd) no yes)) no) no

theorem sAbortBranch_exec (ts : Tapes sc) (yes no : Prog A9 Cond9)
    (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark
      (if sAbort endSym (orcAB blank mark) ts then yes else no)
      (applyActs blank (sProbe blank) ts) L) :
    ExecA Terminal blank endSym mark (sAbortBranch yes no)
      (applyActs blank (sProbe blank) ts) L := by
  have hv2 : condOf9 endSym mark .v2NotEnd
      (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) =
      decide (Tape.read ts.V2 ≠ endSym) := rfl
  have hv12 : condOf9 endSym mark .v12Eq
      (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) =
      decide (Tape.read ts.V1 = Tape.read ts.V2) := rfl
  have ha : condOf9 endSym mark (.notMark tCa)
      (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) =
      decide (probe blank ts.Ca ≠ mark) := rfl
  have hd : condOf9 endSym mark (.notMark tCd)
      (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) =
      decide (probe blank ts.Cd ≠ mark) := rfl
  unfold sAbortBranch
  by_cases h2 : Tape.read ts.V2 ≠ endSym
  · apply execA_ite_pos (by simpa only [hv2, decide_eq_true_eq] using h2)
    by_cases he : Tape.read ts.V1 = Tape.read ts.V2
    · apply execA_ite_pos (by simpa only [hv12, decide_eq_true_eq] using he)
      by_cases hA : probe blank ts.Ca = mark
      · apply execA_ite_neg (by simp [ha, hA])
        by_cases hD : probe blank ts.Cd = mark
        · apply execA_ite_neg (by simp [hd, hD])
          have hs : sAbort endSym (orcAB blank mark) ts :=
            ⟨h2, he, by simp only [orcAB, hA, hD, true_and, decide_true]⟩
          simpa only [if_pos hs] using hx
        · apply execA_ite_pos (by simp [hd, hD])
          simpa [sAbort, orcAB, h2, he, hA, hD] using hx
      · apply execA_ite_pos (by simp [ha, hA])
        simpa [sAbort, orcAB, h2, he, hA] using hx
    · apply execA_ite_neg (by simp only [hv12, he, decide_false])
      simpa only [sAbort, he, false_and, and_false, ite_false] using hx
  · apply execA_ite_neg (by simp only [hv2, h2, decide_false])
    simpa only [sAbort, h2, false_and, ite_false] using hx

/-- Probe, decide, restore both heads, and then execute the chosen continuation. -/
def SABORT (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .seq sProbeProg (sAbortBranch (.seq sRestoreProg yes) (.seq sRestoreProg no))

def sAbortTest (blank : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  sProbe blank ++ sRestore (applyActs blank (sProbe blank) ts)

theorem sAbortTest_length (ts : Tapes sc) : (sAbortTest blank ts).length = 4 := rfl

theorem sAbortTest_restore (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    applyActs blank (sAbortTest blank ts) ts = ts := by
  rw [sAbortTest, applyActs_append, sProbe_restore ts ha hd]

theorem SABORT_exec (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d)
    (yes no : Prog A9 Cond9) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark
      (if sAbort endSym (orcAB blank mark) ts then yes else no) ts L) :
    ExecA Terminal blank endSym mark (SABORT yes no) ts (sAbortTest blank ts ++ L) := by
  have hr := sProbe_restore ts ha hd
  have ht : ExecA Terminal blank endSym mark
      (if sAbort endSym (orcAB blank mark) ts then .seq sRestoreProg yes
       else .seq sRestoreProg no)
      (applyActs blank (sProbe blank) ts)
      (sRestore (applyActs blank (sProbe blank) ts) ++ L) := by
    by_cases h : sAbort endSym (orcAB blank mark) ts
    · rw [if_pos h] at hx ⊢
      exact execA_seq (sRestoreProg_exec _) (by simpa only [hr] using hx)
    · rw [if_neg h] at hx ⊢
      exact execA_seq (sRestoreProg_exec _) (by simpa only [hr] using hx)
  have h := execA_seq (sProbeProg_exec ts) (sAbortBranch_exec ts _ _ _ ht)
  simpa only [SABORT, sAbortTest, List.append_assoc] using h

/-- info: 'PalPeg.GSPreProg.SABORT_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SABORT_exec

/-- info: 'PalPeg.GSPreProg.sAbortTest_restore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sAbortTest_restore

end PalPeg.GSPreProg
