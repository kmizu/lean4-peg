import PalPeg.TextFeedPipelinePrefixPhysical

/-! Turn an actual prep endpoint into the prefix rank invariant. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixEndpoint
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPipelinePrefixStart PalPeg.TextFeedPrefixRank

variable {k : ℕ}

theorem ready_to_prefix {e : Env k} {u v Text : List (Fin k)} {rate p r n R : ℕ}
    {leftSym : Fin k} {x : Phys e leftSym R rate} {S : PatternTapes.Tapes k}
    {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (hp : prepView x.2 = TSg S) (hq : ReadyAt e x.2 q₁ q₂ old) (hl : toList q₁ = Text.take n)
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = false)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [liftPrefix TextFeedPrefixAtomic.source, afterPrefix rate])
    (hv : GSVTapes.VEncodes' e.blank e.startSym e.endSym e.mark u v (TextFeed.padW e.blank Text 0)
      rate p r (toGS S, toVExt S) (⟨0, 0⟩, 0)) :
    ∃ z : State k, Link e leftSym R rate z x ∧
      Good e u v Text rate p r n (5 * u.length + 2) (erase z) ∧
      z.2.q₂ = q₂ ∧ Tape.SeqView e.blank z.2.X (TextFeed.padW e.blank Text 0) 0 := by
  obtain ⟨M, U, X, aux, dir, qt₁, m₁, qt₂, m₂, ht, hQ, hm, h₁, h₂, hr, hX⟩ :=
    TextFeedPipelinePrepReady.prepared_rep hp hq hl hv
  let D : TextFeedPrefixMachine.Data k := ⟨TextFeedPrefixFinish.data M U, q₂, X, aux, old, dir⟩
  have hlink : Link e leftSym R rate ([TextFeedPrefixAtomic.source], D) x := by
    exact ⟨qt₁, m₁, qt₂, m₂, ht, hb, hf, h₁, h₂, hs⟩
  exact ⟨(TextFeedPrefixCycle.loopS, D), normalize hlink, initial_rank rfl hr hm, rfl, hX⟩

/-- info: 'PalPeg.TextFeedPipelinePrefixEndpoint.ready_to_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ready_to_prefix

end PalPeg.TextFeedPipelinePrefixEndpoint
