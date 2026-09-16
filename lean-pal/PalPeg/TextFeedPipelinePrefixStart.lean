import PalPeg.TextFeedPipelinePrefixWindow

/-! Normalize the ghost source stack at the prep/prefix boundary without
changing the physical control, tapes, or clock. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixStart
open PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrefixLink
open PalPeg.TextFeedPrefixRank
open PegSeparation.RealTimeTM PalPeg.TextFeed

variable {k : ℕ}

theorem source_step (ev : TaskCond k → Bool) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev ([TextFeedPrefixAtomic.source].map liftPrefix ++ r) =
      stepStack ev (TextFeedPrefixCycle.loopS.map liftPrefix ++ r) := by
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  change stepStack ev (.seq (liftPrefix TextFeedPrefixCycle.loop)
    (liftPrefix TextFeedPrefixCycle.tail) :: r) = _
  rw [stepStack_seq]
  rfl

theorem normalize {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {D : TextFeedPrefixMachine.Data k} {x : Phys e leftSym R rate}
    (h : Link e leftSym R rate ([TextFeedPrefixAtomic.source], D) x) :
    Link e leftSym R rate (TextFeedPrefixCycle.loopS, D) x := by
  obtain ⟨qt₁, m₁, qt₂, m₂, ht, hb, hf, h₁, h₂, hs⟩ := h
  refine ⟨qt₁, m₁, qt₂, m₂, ht, hb, hf, h₁, h₂, ?_⟩
  exact hs.trans (source_step _ _)

theorem initial_rank {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ}
    {D : TextFeedPrefixMachine.Data k} {M : Machine' k} {U : TapeConfiguration k}
    (hD : D.worker = TextFeedPrefixFinish.data M U)
    (h : Rep e u v Text d p r n M U 0 1) (hm : M.m = 0) :
    Good e u v Text d p r n (5 * u.length + 2) (erase (TextFeedPrefixCycle.loopS, D)) := by
  have hg := Good.loop h hm (Nat.zero_le u.length)
  simpa only [erase, hD, Nat.sub_zero, show 4 * u.length + u.length + 2 = 5 * u.length + 2 by omega] using hg

/-- info: 'PalPeg.TextFeedPipelinePrefixStart.normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms normalize

/-- info: 'PalPeg.TextFeedPipelinePrefixStart.initial_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms initial_rank

end PalPeg.TextFeedPipelinePrefixStart
