import PalPeg.TextFeedPipelineFeed1

/-! Dispatch at the actual verifier body, retaining the caller's continuation.
The branch reads a tape cell, not a ghost arrival count. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFeedBody
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed

variable {k : ℕ} {Terminal : Type}

theorem body_step (e : Env k) (σ : Fin 39 → Fin k) (rate : ℕ)
    (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (verifyBody rate :: s) =
      if σ 12 = e.blank then
        (.seq feedHead2 (liftVerify (GSVProgZLoop.stepProg rate)) :: s,
          some (.inr (.inl .supply)))
      else (liftVerify (GSVProgZLoop.stepProg rate) :: s,
        some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) := by
  rw [verifyBody, stepStack_seq]
  split
  · rename_i h
    exact TextFeedPipelineFeedSource.feed_blank e σ h _
  · rename_i h
    rw [TextFeedPipelineFeedSource.feed_present e σ h]
    rw [stepStack_seq, TextFeedPipelineFeed2.feed2_step]

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

/-- One physical call at body entry preserves both queues and the feed
invariant. A present Q1 cell is skipped without consuming Q1; an empty
cell is supplied before the Q2 instruction can be selected. -/
theorem run_body {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (verifyBody rate :: s))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := if (x.2 12).focus = e.blank then vfillIf1' e.blank e.mark n M
      else vfillHead2 e.blank e.mark M
    let s' := if (x.2 12).focus = e.blank then
      .seq feedHead2 (liftVerify (GSVProgZLoop.stepProg rate)) :: s
      else liftVerify (GSVProgZLoop.stepProg rate) :: s
    ∃ qt₁' m₁' qt₂' m₂', y.2 = tapes e qt₁' m₁' qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s' ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M' := by
  dsimp only
  by_cases hcell : (x.2 12).focus = e.blank
  · simp only [if_pos hcell]
    have hstep := hs
    rw [verifyBody, stepStack_seq] at hstep
    obtain ⟨qt₁', m₁', ht, hby, hcy, hr₁, hr₂, hi⟩ :=
      TextFeedPipelineFeed1.run_feed1 (Terminal := Terminal) hc hmb leftSym R rate x hb hz
        (.seq feedHead2 (liftVerify (GSVProgZLoop.stepProg rate)) :: s) hstep hcell
        qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf
    exact ⟨qt₁', m₁', qt₂, m₂, ht, hby, hcy, hr₁, hr₂, hi⟩
  · simp only [if_neg hcell]
    have hstep := hs
    rw [verifyBody, stepStack_seq, TextFeedPipelineFeedSource.feed_present e _ hcell,
      stepStack_seq] at hstep
    obtain ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hi, _⟩ :=
      TextFeedPipelineFeed2.run_feed2 (Terminal := Terminal) hc hmb leftSym R rate x hb hz
        (liftVerify (GSVProgZLoop.stepProg rate) :: s) hstep
        qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf
    exact ⟨qt₁, m₁, qt₂', m₂', ht, hby, hcy, hr₁, hr₂, hi⟩

/-- With two worker slots available, body entry reaches the transformed
GS program in at most two actual calls. Neither the control stack nor
the physical queues are reset between these calls. -/
theorem run_body_ready {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (hz₂ : nextPhase x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (verifyBody rate :: s))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let M' := vfillHead2 e.blank e.mark (vfillIf1' e.blank e.mark n M)
    ∃ N, 1 ≤ N ∧ N ≤ 2 ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x
      ∃ qt₁' m₁' qt₂' m₂', y.2 = tapes e qt₁' m₁' qt₂' m₂' M' aux old dir ∧
        AtBoundary (programs e) y.1.2.2.1 ∧
        y.1.1.2.2.val = liftVerify (GSVProgZLoop.stepProg rate) :: s ∧
        Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
        VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M' ∧
        Ok2 n M' (M'.z.1.pos - u.length + M'.z.2) := by
  have hbdy := run_body (Terminal := Terminal) hc hmb leftSym R rate x hb hz s hs
    qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hblank hmark hn hf
  dsimp only at hbdy ⊢
  by_cases hcell : (x.2 12).focus = e.blank
  · simp only [if_pos hcell] at hbdy
    obtain ⟨qa, ma, qb, mb, ht, hby, hcy, hr₁, hr₂, hi⟩ := hbdy
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    have hyz : y.1.1.1 ≠ 0 := by
      rw [TextFeedPipelineControl.run_counter]
      exact hz₂
    have hstep : stepStack (taskEval e (fun j => (y.2 j).focus)) y.1.1.2.2.val =
        stepStack (taskEval e (fun j => (y.2 j).focus))
          (feedHead2 :: liftVerify (GSVProgZLoop.stepProg rate) :: s) := by
      rw [hcy, stepStack_seq]
    obtain ⟨qb', mb', ht', hb', hc', hr₁', hr₂', hi', hok⟩ :=
      TextFeedPipelineFeed2.run_feed2 (Terminal := Terminal) hc hmb leftSym R rate y hby hyz
        (liftVerify (GSVProgZLoop.stepProg rate) :: s) hstep
        qa ma qb mb (vfillIf1' e.blank e.mark n M) aux old dir ht hr₁ hr₂ hblank hmark hn hi
    refine ⟨2, by omega, by omega, qa, ma, qb', mb', ?_⟩
    exact ⟨ht', hb', hc', hr₁', hr₂', hi', hok⟩
  · simp only [if_neg hcell] at hbdy
    have hmcell : ((prefixModel M).S GSTapes.tT).focus ≠ e.blank := by
      rw [hx] at hcell
      exact hcell
    have hm := TextFeedPipelineFeed1Model.skip_present hblank hn hf hmcell
    rw [hm]
    obtain ⟨qa, ma, qb, mb, ht, hby, hcy, hr₁, hr₂, hi⟩ := hbdy
    have hok := (vfillHead2_feedInv hmb hblank hmark hn hf).2
    exact ⟨1, by omega, by omega, qa, ma, qb, mb, ht, hby, hcy, hr₁, hr₂, hi, hok⟩

/-- info: 'PalPeg.TextFeedPipelineFeedBody.run_body_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_body_ready

/-- info: 'PalPeg.TextFeedPipelineFeedBody.run_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_body

end PalPeg.TextFeedPipelineFeedBody
