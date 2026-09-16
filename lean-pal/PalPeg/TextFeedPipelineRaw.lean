import PalPeg.TextFeedPipelineFeed1
import PalPeg.VerifierFeedRawPrimitive

/-! The raw-head feed invariant on the actual 39-tape pipeline.
These calls remain applicable inside GS, before its macro ghost state is updated. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineRaw
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineVerifier PalPeg.VerifierFeed PalPeg.VerifierFeedRaw
open PalPeg.VerifierFeedRawPrimitive

variable {k : ℕ} {Terminal : Type}

theorem supply_model {e : Env k} {M : VMachine' k}
    (hq : Inv M.Q1) (hb : Encodes e.blank e.mark M.R1.qt M.Q1)
    (ht : Tape.read (M.vt.1 GSTapes.tT) = e.blank) :
    TextFeedPrefixAtomic.effect e .supply (prefixModel M) =
      prefixModel (fill1 e.blank e.mark M) := by
  have hpk : TextFeed.peek e.blank M.R1 = (toList M.Q1).head?.getD e.mark := by
    have hh : TextFeed.peek e.blank M.R1 = (head? M.Q1).getD e.mark := headT_read hb
    rwa [head?_eq hq] at hh
  by_cases he : (toList M.Q1).head?.getD e.mark = e.mark
  · simp only [fill1, hpk, he, ne_eq, not_true_eq_false, and_false, if_false,
      TextFeedPrefixAtomic.effect, prefixModel, TextFeedAtomic.supplyEffect, if_true]
  · have hf : Tape.read (M.vt.1 GSTapes.tT) = e.blank ∧ TextFeed.peek e.blank M.R1 ≠ e.mark :=
      ⟨ht, by rwa [hpk]⟩
    rw [fill1, if_pos hf]
    exact TextFeedPrefixFinish.supply_data (toM M) M.vt.2.U hq hb he

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

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
    {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : RawInv e.blank e.mark Text n M i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := fill1 e.blank e.mark M
    ∃ qt₁' m₁', y.2 = tapes e qt₁' m₁' qt₂ m₂ M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂ m₂ M'.Q2 ∧
      RawInv e.blank e.mark Text n M' i₁ i₂ ∧
      (Tape.read (M'.vt.1 GSTapes.tT) = e.blank ↔ i₁ = n) := by
  obtain ⟨qt₁', m₁', ht, hby, hr, hcy⟩ := TextFeedPipelineFeedSource.run_feed_blank e hc hmb leftSym R rate x hb hz s hs hcell
    (prefixModel M) qt₁ m₁ qt₂ m₂ M.vt.2.Txt2 aux old dir hx h₁
  have hmcell : Tape.read (M.vt.1 GSTapes.tT) = e.blank := by
    rw [hx] at hcell
    exact hcell
  rw [supply_model hf.one.qinv hf.one.buf hmcell] at ht hr
  obtain ⟨hvt, _, hq, _, _⟩ := fill1_other e.blank e.mark M
  refine ⟨qt₁', m₁', ?_, hby, hcy, hr, ?_,
    (raw_fill1 hmb hblank hmark hn hf).1, fill1_wait_iff hmb hblank hmark hn hf.one⟩
  · simpa only [TextFeedPipelineVerifier.tapes, hvt] using ht
  · rwa [hq]

theorem run_instruction {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k)) (a : GSVProg.Act10)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      (s, some (.inr (.inr (.inl a)))))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (hf : RawInv e.blank e.mark Text n M i₁ i₂) (hsa : Safe a M i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := VerifierFeedPrimitive.effect e a M
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' M' aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s ∧
      Ready e.blank e.mark qt₁ m₁ M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      RawInv e.blank e.mark Text n M'
        (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  obtain ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, _⟩ :=
    TextFeedPipelineVerifier.run_instruction e hc hmb leftSym R rate x hb hz s a hs
      qt₁ m₁ qt₂ m₂ M aux old dir hx h₁ h₂ hf.two.buf
  exact ⟨qt₂', m₂', ht, hby, hcy, hr₁, hr₂, raw_effect hmb hblank hmark hn hf hsa⟩

theorem run_arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (a : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux a dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    (ham : a ≠ e.mark) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hf : RawInv e.blank e.mark Text n M i₁ i₂) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    let M' := varrive' e.blank e.mark a M
    ∃ qt₁' m₁' qt₂' m₂', y.2 = tapes e qt₁' m₁' qt₂' m₂' M' aux a dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2 = x.1.1.2.2 ∧ y.1.1.2.1 = false ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      RawInv e.blank e.mark Text (n + 1) M' i₁ i₂ := by
  obtain ⟨qt₁', m₁', qt₂', m₂', ht, hby, hcy, hfy, hr₁, hr₂⟩ :=
    TextFeedPipelineArrival.run_enqueue e hc hmb leftSym R rate x hb hz hfirst
      (prefixModel M) M.Q2 qt₁ m₁ qt₂ m₂ M.vt.2.Txt2 aux a dir hx h₁ h₂ ham
  exact ⟨qt₁', m₁', qt₂', m₂', ht, hby, hcy, hfy, hr₁, hr₂, raw_arrive hmb hn ha hf⟩

/-- info: 'PalPeg.TextFeedPipelineRaw.run_feed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed1

/-- info: 'PalPeg.TextFeedPipelineRaw.run_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_instruction

/-- info: 'PalPeg.TextFeedPipelineRaw.run_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_arrival

end PalPeg.TextFeedPipelineRaw
