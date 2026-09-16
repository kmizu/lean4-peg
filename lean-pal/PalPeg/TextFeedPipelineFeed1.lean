import PalPeg.TextFeedPipelineFeedSource
import PalPeg.TextFeedPipelineFeed1Model

/-! Actual guarded Q1 supply preserves the verifier invariant. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFeed1
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed

variable {k : ℕ} {Terminal : Type}

theorem fill_ext (e : Env k) (n : ℕ) (M : VMachine' k) :
    (vfillIf1' e.blank e.mark n M).vt.2 = M.vt.2 ∧ (vfillIf1' e.blank e.mark n M).Q2 = M.Q2 := by
  unfold vfillIf1'
  split <;> exact ⟨rfl, rfl⟩

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem run_feed1 {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (feedHead :: s))
    (hcell : (x.2 12).focus = e.blank)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {u v Text : List (Fin k)} {d p r n : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := vfillIf1' e.blank e.mark n M
    ∃ qt₁' m₁', y.2 = tapes e qt₁' m₁' qt₂ m₂ M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂ m₂ M'.Q2 ∧
      VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M' := by
  obtain ⟨qt₁', m₁', ht, hby, hr, hcy⟩ := TextFeedPipelineFeedSource.run_feed_blank e hc hmb leftSym R rate x hb hz s hs hcell
    (prefixModel M) qt₁ m₁ qt₂ m₂ M.vt.2.Txt2 aux old dir hx h₁
  have hmodel : ((prefixModel M).S GSTapes.tT).focus = e.blank := by
    rw [hx] at hcell
    exact hcell
  have he := TextFeedPipelineFeed1Model.supply_blank hblank hmark hn hf hmodel
  rw [he] at ht hr
  obtain ⟨hvt, hQ⟩ := fill_ext e n M
  refine ⟨qt₁', m₁', ?_, hby, hcy, hr, ?_, vfillIf1'_feedInv hmb hn hf⟩
  · simpa only [TextFeedPipelineVerifier.tapes, hvt] using ht
  · rwa [hQ]

/-- info: 'PalPeg.TextFeedPipelineFeed1.run_feed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed1

end PalPeg.TextFeedPipelineFeed1
