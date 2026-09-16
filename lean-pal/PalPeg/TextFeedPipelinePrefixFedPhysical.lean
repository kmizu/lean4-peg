import PalPeg.TextFeedPipelinePrefixFedHit

/-! Physical prefix return with the preserved verifier input reserve. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrefixFedPhysical
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelinePrefixLink PalPeg.TextFeedPrefixRank
open PalPeg.TextFeedPipelinePrefixFrames PalPeg.TextFeedPipelinePrefixPhysical
open PalPeg.TextFeedPipelinePrefixReserve PalPeg.TextFeedPipelinePrefixFedHit
open PalPeg.TextFeedPipelinePrepFinish (phase finishAt)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def Complete (e : Env k) (leftSym : Fin k) (R rate : ℕ) (u v Text : List (Fin k))
    (d p r n : ℕ) (x : Phys e leftSym R rate) : Prop :=
  ∃ z, Link e leftSym R rate z x ∧ Good e u v Text d p r n 0 (erase z) ∧ Reserve e Text n z

def Witness (e : Env k) (enc : Terminal → Fin k) (leftSym : Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (d p r n : ℕ) (word : List Terminal) (x : Phys e leftSym R rate) : Prop :=
  (∃ before rest y, word = before ++ rest ∧
    before.foldl (machine e leftSym enc R rate).sRound (pack x 0) = pack y 0 ∧
    Complete e leftSym R rate u v Text d p r (n + before.length) y) ∨
  (∃ before a rest J y, J ≤ R ∧ word = before ++ a :: rest ∧
    finishAt e leftSym enc R rate before a J (pack x 0) = pack y (phase R J) ∧
    Complete e leftSym R rate u v Text d p r (n + before.length + 1) y)

theorem hit_witness {e : Env k} {enc : Terminal → Fin k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {word : List Terminal} {x : Phys e leftSym R rate}
    (h : FedHit e enc leftSym R rate u v Text d p r n word x) :
    Witness e enc leftSym R rate u v Text d p r n word x := by
  induction h with
  | @now n w x z hl hg hr => exact Or.inl ⟨[], w, x, rfl, rfl, z, hl, hg, hr⟩
  | @within n a w x z J hJ hl hg hr =>
    exact Or.inr ⟨[], a, w, J, _, hJ, rfl, partial_pack e enc leftSym R rate J hJ a x, z, hl, hg, hr⟩
  | @next n a w x h ih =>
    rcases ih with ⟨before, rest, y, hw, hp, hc⟩ | ⟨before, b, rest, J, y, hJ, hw, hp, hc⟩
    · left
      refine ⟨a :: before, rest, y, by simp only [List.cons_append, hw], ?_, ?_⟩
      · simpa only [List.foldl_cons, round_pack] using hp
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
    · right
      refine ⟨a :: before, b, rest, J, y, hJ, by simp only [List.cons_append, hw], ?_, ?_⟩
      · simpa only [finishAt, List.foldl_cons, round_pack] using hp
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem Complete.ready {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {x : Phys e leftSym R rate}
    (h : Complete e leftSym R rate u v Text d p r n x) :
    stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [afterPrefix rate] ∧
    ∃ D : TextFeedPrefixMachine.Data k, ∃ M U qt₁ m₁ qt₂ m₂,
      D.worker = TextFeedPrefixFinish.data M U ∧
      x.2 = TextFeedPrefixMachine.tapes e qt₁ m₁ qt₂ m₂ D ∧
      RTQueueClosed.Ready e.blank e.mark qt₁ m₁ M.Q ∧ RTQueueClosed.Ready e.blank e.mark qt₂ m₂ D.q₂ ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n
        (TextFeedPrefixReady.model M U D.X D.q₂ ⟨qt₂ ∘ m₂.roles, 0⟩) ∧
      M.st.pos = u.length ∧ M.st.q = 0 ∧ M.m = u.length := by
  obtain ⟨z, hl, hg, hr⟩ := h
  obtain ⟨hs, he⟩ := endpoint_ready hl hg hr
  exact ⟨hs, z.2, he⟩

/-- A completed physical prefix enters the verifier on its next worker call.
No canonical-stack assumption is needed at the prefix endpoint. -/
theorem Complete.enter {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {u v Text : List (Fin k)} {d p r n : ℕ} {x : Phys e leftSym R rate}
    (h : Complete e leftSym R rate u v Text d p r n x)
    (hz : x.1.1.1 ≠ 0) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = writeDir e true x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = [verifyLoop rate] ∧ (y.2 38).focus = e.mark ∧
      ∀ j, j ≠ 38 → y.2 j = x.2 j := by
  have hs := h.ready.1
  obtain ⟨z, ⟨qt₁, m₁, qt₂, m₂, ht, hb, hrest⟩, hg, hr⟩ := h
  exact TextFeedPipelineHandoff.run_prefix_return e leftSym R rate x hb hz hs

/-- info: 'PalPeg.TextFeedPipelinePrefixFedPhysical.Complete.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complete.enter

/-- info: 'PalPeg.TextFeedPipelinePrefixFedPhysical.hit_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hit_witness

/-- info: 'PalPeg.TextFeedPipelinePrefixFedPhysical.Complete.ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complete.ready

end PalPeg.TextFeedPipelinePrefixFedPhysical
