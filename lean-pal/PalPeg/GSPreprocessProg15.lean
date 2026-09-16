import PalPeg.GSPreprocessProg14

/-! # Finite outer-loop control for the second phase

The syntax depends only on the fixed exponent `k`. The control lemmas below
separate head restoration and guard correctness from the semantic invariant.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def soProbe (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank .left, Act.Ce blank .left]

def soProbeProg : Prog A9 Cond9 :=
  .seq (.act (tCq, .blk, .left)) (.act (tCe, .blk, .left))

def soRestore (ts : Tapes sc) : List (Act sc) :=
  [Act.Ce ts.Ce.focus .right, Act.Cq ts.Cq.focus .right]

def soRestoreProg : Prog A9 Cond9 :=
  .seq (.act (tCe, .keep, .right)) (.act (tCq, .keep, .right))

theorem soProbeProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark soProbeProg ts (soProbe blank) :=
  execA_seq (execA_ct_put ctCq .left ts) (execA_ct_put ctCe .left _)

theorem soRestoreProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark soRestoreProg ts (soRestore ts) :=
  execA_seq (execA_ct_keep ctCe .right ts) (execA_ct_keep ctCq .right _)

theorem soProbe_restore (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e) :
    applyActs blank (soRestore (applyActs blank (soProbe blank) ts))
      (applyActs blank (soProbe blank) ts) = ts := by
  have eq := counter_probe_restore hq
  have ee := counter_probe_restore he
  change { ts with
    Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) (probe blank ts.Cq) .right
    Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) (probe blank ts.Ce) .right } = ts
  rw [eq, ee]

theorem soReady_iff (ts : Tapes sc) :
    condOf9 endSym mark .soReady
      (fun j => (getT (applyActs blank (soProbe blank) ts) j).focus) = true ↔
      probe blank ts.Ce = mark ∧ soCond blank endSym mark ts := by
  change decide (probe blank ts.Ce = mark ∧
    ¬ (probe blank ts.Cq = mark ∧ Tape.read ts.V2 = endSym)) = true ↔ _
  simp only [decide_eq_true_eq, soCond]

theorem soReady_enc_iff {startSym : Fin sc} {x : List (Fin sc)}
    (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s p q D E F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hfit : s + p + q ≤ x.length)
    (h : EncS blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, R⟩ g ts) :
    condOf9 endSym mark .soReady
      (fun j => (getT (applyActs blank (soProbe blank) ts) j).focus) = true ↔
      E = 0 ∧ p < (x.drop s).length := by
  rw [soReady_iff, probe_iff hmark h.base.ce]
  unfold soCond
  rw [probe_iff hmark h.base.cq, read_pat_end_iff hend h.base.v2, List.length_drop]
  dsimp only
  omega

/-- One complete outer iteration; the abort branch sets the existing flag. -/
def SO_BODY (k : ℕ) : Prog A9 Cond9 :=
  .seq SCAN (SABORT (.act (tCe, .blk, .right))
    (ORC2 k (PERIOD_SIGNED k) (RESET_SIGNED k)))

def SO_RUN (k : ℕ) : Prog A9 Cond9 :=
  .loop .soReady (tCe, .keep, .right)
    (.seq (.act (tCq, .keep, .right)) (.seq (SO_BODY k) soProbeProg))

/-- Candidate assembled second phase, with no input-dependent syntax or fuel. -/
def SECOND_OUTER (k : ℕ) : Prog A9 Cond9 :=
  .seq soProbeProg (.seq (SO_RUN k) soRestoreProg)

theorem SO_RUN_stop (k : ℕ) (ts : Tapes sc)
    (h : ¬ (probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)) :
    ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((soReady_iff ts).1 hh))

def soIter (blank : Fin sc) (ts : Tapes sc) (L : List (Act sc)) : List (Act sc) :=
  soRestore (applyActs blank (soProbe blank) ts) ++ L ++ soProbe blank

theorem soIter_effect (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e) (L : List (Act sc)) :
    applyActs blank (soIter blank ts L) (applyActs blank (soProbe blank) ts) =
      applyActs blank (soProbe blank) (applyActs blank L ts) := by
  simp only [soIter, applyActs_append, soProbe_restore ts hq he]

theorem soIter_length (ts : Tapes sc) (L : List (Act sc)) :
    (soIter blank ts L).length = L.length + 4 := by
  simp only [soIter, soRestore, soProbe, List.length_append,
    List.length_cons, List.length_nil]
  omega

theorem SO_RUN_cont (k : ℕ) (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e)
    (hc : probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)
    {L T : List (Act sc)}
    (hb : ExecA Terminal blank endSym mark (SO_BODY k) ts L)
    (hn : ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank (soProbe blank) (applyActs blank L ts)) T) :
    ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank (soProbe blank) ts) (soIter blank ts L ++ T) := by
  have hr := soProbe_restore ts hq he
  have hbody : ExecA Terminal blank endSym mark
      (.seq (.act (tCq, .keep, .right)) (.seq (SO_BODY k) soProbeProg))
      (applyAct blank (applyActs blank (soProbe blank) ts)
        (Act.Ce (probe blank ts.Ce) .right))
      ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCq .right _)
    have hr' : applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right)) = ts := hr
    change ExecA Terminal blank endSym mark (.seq (SO_BODY k) soProbeProg)
      (applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) (L ++ soProbe blank)
    rw [hr']
    exact execA_seq hb (soProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank))
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) T := by
    have hv := soIter_effect ts hq he L
    change ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank (soIter blank ts L) (applyActs blank (soProbe blank) ts)) T
    rw [hv]
    exact hn
  have hh := execA_loop_cont (w := .keep) rfl rfl rfl
    ((soReady_iff ts).2 hc) hbody hn'
  exact execA_of_eq (by simp only [soIter, soRestore, List.append_assoc]; rfl) hh

/-- Close the finite outer program once its loop has reached a probed final state. -/
theorem SECOND_OUTER_finish (k : ℕ) (ts u : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark u.Cq q)
    (he : Tape.CounterView' blank mark u.Ce e) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (SO_RUN k)
      (applyActs blank (soProbe blank) ts) L)
    (hu : applyActs blank L (applyActs blank (soProbe blank) ts) =
      applyActs blank (soProbe blank) u) :
    ∃ T, ExecA Terminal blank endSym mark (SECOND_OUTER k) ts T ∧
      applyActs blank T ts = u ∧ T.length = L.length + 4 := by
  refine ⟨soProbe blank ++ (L ++ soRestore (applyActs blank (soProbe blank) u)), ?_, ?_, ?_⟩
  · apply execA_seq (soProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]
    exact soRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hu, soProbe_restore u hq he]
  · simp only [soProbe, soRestore, List.length_append, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.SO_RUN_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SO_RUN_cont

/-- info: 'PalPeg.GSPreProg.soReady_enc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms soReady_enc_iff

end PalPeg.GSPreProg
