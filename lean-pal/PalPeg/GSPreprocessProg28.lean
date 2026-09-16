import PalPeg.GSPreprocessProg27

/-! # Finite second-phase control using the maintained difference -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def SO_BODY_R (k : ℕ) : Prog A9 Cond9 :=
  .seq SCAN_R (SABORT (.act (tCe, .blk, .right))
    (ORC2_FAST k (PERIOD_R k) (RESET_R k)))

def SO_RUN_R (k : ℕ) : Prog A9 Cond9 :=
  .loop .soReady (tCe, .keep, .right)
    (.seq (.act (tCq, .keep, .right)) (.seq (SO_BODY_R k) soProbeProg))

/-- Candidate assembled second phase, with no input-dependent syntax or fuel. -/
def SECOND_OUTER_R (k : ℕ) : Prog A9 Cond9 :=
  .seq soProbeProg (.seq (SO_RUN_R k) soRestoreProg)

theorem SO_RUN_R_stop (k : ℕ) (ts : Tapes sc)
    (h : ¬ (probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)) :
    ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((soReady_iff ts).1 hh))

theorem SO_RUN_R_cont (k : ℕ) (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e)
    (hc : probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)
    {L T : List (Act sc)}
    (hb : ExecA Terminal blank endSym mark (SO_BODY_R k) ts L)
    (hn : ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank (soProbe blank) (applyActs blank L ts)) T) :
    ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank (soProbe blank) ts) (soIter blank ts L ++ T) := by
  have hr := soProbe_restore ts hq he
  have hbody : ExecA Terminal blank endSym mark
      (.seq (.act (tCq, .keep, .right)) (.seq (SO_BODY_R k) soProbeProg))
      (applyAct blank (applyActs blank (soProbe blank) ts)
        (Act.Ce (probe blank ts.Ce) .right))
      ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCq .right _)
    have hr' : applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right)) = ts := hr
    change ExecA Terminal blank endSym mark (.seq (SO_BODY_R k) soProbeProg)
      (applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) (L ++ soProbe blank)
    rw [hr']
    exact execA_seq hb (soProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank))
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) T := by
    have hv := soIter_effect ts hq he L
    change ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank (soIter blank ts L) (applyActs blank (soProbe blank) ts)) T
    rw [hv]
    exact hn
  have hh := execA_loop_cont (w := .keep) rfl rfl rfl
    ((soReady_iff ts).2 hc) hbody hn'
  exact execA_of_eq (by simp only [soIter, soRestore, List.append_assoc]; rfl) hh

/-- Close the finite outer program once its loop has reached a probed final state. -/
theorem SECOND_OUTER_R_finish (k : ℕ) (ts u : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark u.Cq q)
    (he : Tape.CounterView' blank mark u.Ce e) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (SO_RUN_R k)
      (applyActs blank (soProbe blank) ts) L)
    (hu : applyActs blank L (applyActs blank (soProbe blank) ts) =
      applyActs blank (soProbe blank) u) :
    ∃ T, ExecA Terminal blank endSym mark (SECOND_OUTER_R k) ts T ∧
      applyActs blank T ts = u ∧ T.length = L.length + 4 := by
  refine ⟨soProbe blank ++ (L ++ soRestore (applyActs blank (soProbe blank) u)), ?_, ?_, ?_⟩
  · apply execA_seq (soProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]
    exact soRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hu, soProbe_restore u hq he]
  · simp only [soProbe, soRestore, List.length_append, List.length_cons, List.length_nil]
    omega


/-- info: 'PalPeg.GSPreProg.SO_RUN_R_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SO_RUN_R_cont

end PalPeg.GSPreProg
