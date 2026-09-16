import PalPeg.TextFeedPipelineBirthSource

set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBirthRestore
open PegSeparation.RealTimeTM PalPeg.Program
open PalPeg.ProgLang PalPeg.TextFeedInit
open PalPeg.TextFeedPipelineBirthSource
variable {k : ℕ}

/-- Restore only the borrowed history head, preserving all matcher tapes. -/
def machine (blank : Fin k) : StructuredMachine Unit (Fin 3) (Fin k) 40 1 where
  tapeCount_pos := by decide
  blank := blank
  initial := 0
  accepting := fun q => decide (q = 2)
  micro := fun q a σ =>
    let z := (HistoryRewind.machine blank).micro q a (fun _ => σ sourceAddr)
    (z.1, fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
      | .inl _ => z.2 0
      | .inr _ => (σ j, .stay))

def run (blank : Fin k) (n : ℕ) (x : SConfig (Fin 3) (Fin k) 40) :=
  (List.replicate n ()).foldl (machine blank).sRound x

theorem round_pack (blank : Fin k) (q : Fin 3) (S : STape (Fin k))
    (T : Fin 39 → STape (Fin k)) :
    (machine blank).sRound (pack q S T) () =
      pack ((HistoryRewind.machine blank).sRound (HistoryRewind.config q S) ()).state
        (((HistoryRewind.machine blank).sRound (HistoryRewind.config q S) ()).tape 0) T := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, pack, HistoryRewind.config,
    sourceAddr, Equiv.symm_apply_apply]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) <;> rfl

theorem run_pack (blank : Fin k) (n : ℕ) (q : Fin 3) (S : STape (Fin k))
    (T : Fin 39 → STape (Fin k)) :
    run blank n (pack q S T) =
      pack (HistoryRewind.run blank n (HistoryRewind.config q S)).state
        ((HistoryRewind.run blank n (HistoryRewind.config q S)).tape 0) T := by
  induction n generalizing q S with
  | zero => rfl
  | succ n ih =>
    change run blank n ((machine blank).sRound (pack q S T) ()) = _
    rw [round_pack, ih]
    have eta (x : SConfig (Fin 3) (Fin k) 1) :
        HistoryRewind.config x.state (x.tape 0) = x := by
      cases x with
      | mk q t =>
        unfold HistoryRewind.config
        congr 1
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rfl
    rw [eta]
    rfl

/-- The copied matcher seed survives returning the history head to its
readable position. The explicit right blank is observational padding. -/
theorem restored (blank : Fin k) (w : List (Fin k)) (hw : blank ∉ w)
    (T : Fin 39 → STape (Fin k)) :
    run blank (w.length + 2)
      (pack 0 (HistoryConcat.source blank [] (w.reverse ++ [blank])) T) =
      pack 2 (HistoryConcat.source blank (w ++ [blank]) [blank]) T := by
  rw [run_pack]
  change pack (HistoryRewind.run blank (w.length + 2)
    (HistoryRewind.config 0 ⟨w.reverse ++ [blank], blank, []⟩)).state
    ((HistoryRewind.run blank (w.length + 2)
    (HistoryRewind.config 0 ⟨w.reverse ++ [blank], blank, []⟩)).tape 0) T = _
  rw [HistoryRewind.rewind blank w hw]
  rfl

/-- Concrete copy followed by head restoration: the target seed and the
original readable history are both retained. The phase handoff is explicit
here; the global scheduler must implement it. -/
theorem copy_restore (e : TextFeedControl.Env k) (leftSym : Fin k)
    (w : List (Fin k)) (hw : e.blank ∉ w) :
    let copied := TextFeedPipelineBirthSource.run e leftSym (w.length + 2)
      (pack 0 (HistoryConcat.source e.blank w [e.blank]) (blankBundle e.blank 39))
    run e.blank (w.length + 2)
      (pack 0 (copied.tape sourceAddr) (target copied)) =
      pack 2 (HistoryConcat.source e.blank (w ++ [e.blank]) [e.blank])
        (TextFeedPipelineOutputBirth.seed e leftSym w w.length 0) := by
  dsimp only
  rw [seed_from_source e leftSym w [e.blank] hw]
  simp only [pack, sourceAddr, target, targetAddr, Equiv.symm_apply_apply]
  exact restored e.blank w hw _

/-- info: 'PalPeg.TextFeedPipelineBirthRestore.copy_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_restore

end PalPeg.TextFeedPipelineBirthRestore
