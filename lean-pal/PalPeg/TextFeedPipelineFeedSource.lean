import PalPeg.TextFeedPipelineHandoff

/-! Source-level Q1 feeding: guarded at an existing cell, inserted after
each text-right action and before the next guard, including loop actions. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFeedSource
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl
open PalPeg.RTQueue
open PalPeg.ProgLangPersist PalPeg.ProgLangBank PalPeg.TextFeedPipelineBank
open PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineHandoff

variable {k : ℕ} {Terminal : Type}

theorem feed_blank (e : Env k) (σ : Fin 39 → Fin k) (h : σ 12 = e.blank)
    (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (feedHead :: r) = (r, some (.inr (.inl .supply))) := by
  have he : taskEval e σ (.inr (.inl .blankText)) = true := by
    change decide (σ 12 = e.blank) = true
    exact decide_eq_true h
  simp only [feedHead, stepStack_ite, he, if_true, stepStack_act]

theorem feed_present (e : Env k) (σ : Fin 39 → Fin k) (h : σ 12 ≠ e.blank)
    (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack (taskEval e σ) (feedHead :: r) = stepStack (taskEval e σ) r := by
  have he : taskEval e σ (.inr (.inl .blankText)) = false := by
    change decide (σ 12 = e.blank) = false
    exact decide_eq_false h
  simp only [feedHead, stepStack_ite, he, Bool.false_eq_true, if_false, stepStack_skip]

theorem text_right_continuation (ev : TaskCond k → Bool) (keep : Bool)
    (hready : ev (.inr (.inl .blankText)) = false)
    (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (liftVerify (.act (.inl (GSVProg.e8 GSTapes.tT, keep, .right))) :: r) =
      (feedHead :: r, some (.inr (.inr (.inl (GSVProg.e8 GSTapes.tT, keep, .right))))) := by
  simp only [liftVerify, verifyAct, beforeVerify, if_true, waitText1, stepStack_seq,
    stepStack_loop, hready, Bool.false_eq_true, if_false, stepStack_act, afterVerify, and_self]

theorem loop_text_right_continuation (ev : TaskCond k → Bool)
    (c : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond) (hc : ev (verifyCond c) = true)
    (hwait : beforeCond (k := k) c = .skip)
    (keep : Bool) (body : GSVProgZLoop.DProg) (r : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (liftVerify (.loop c (.inl (GSVProg.e8 GSTapes.tT, keep, .right)) body) :: r) =
      (.seq (verifyAct (.inl (GSVProg.e8 GSTapes.tT, keep, .right)))
          (.seq (liftVerify body) (beforeCond c)) ::
        .loop (verifyCond c) (.inr (.inl .idle))
          (.seq (verifyAct (.inl (GSVProg.e8 GSTapes.tT, keep, .right)))
            (.seq (liftVerify body) (beforeCond c))) :: r,
        some (.inr (.inl .idle))) := by
  simp only [liftVerify, hwait, stepStack_seq, stepStack_skip, stepStack_loop, hc, if_true]

/-- This is why the unconditional supply primitive must not be selected
at an already populated scanner cell. -/
theorem unguarded_overwrite (e : Env k) (q : Queue (Fin k)) (S : Stage k) (a : Fin k)
    (ha : (toList q).head?.getD e.mark = a) (ham : a ≠ e.mark) :
    ((TextFeedAtomic.supplyEffect e q S).2 GSTapes.tT).focus = a := by
  simp [TextFeedAtomic.supplyEffect, ha, ham, changeStage, STape.applyAction]

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem run_feed_blank (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s : Stack (TaskAct k) (TaskCond k))
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) (feedHead :: s))
    (hblank : (x.2 12).focus = e.blank)
    (D : TextFeedPrefixAtomic.Model k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)
    (hq : Ready e.blank e.mark qt₁ m₁ D.q) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁', y.2 = TextFeedPrefixBank.tapes e qt₁' m₁' qt₂ m₂
        (TextFeedPrefixAtomic.effect e .supply D) X aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧
      Ready e.blank e.mark qt₁' m₁' (TextFeedPrefixAtomic.effect e .supply D).q ∧ y.1.1.2.2.val = s := by
  have hstep := hs.trans (feed_blank e _ hblank s)
  obtain ⟨ticks, qt₁', m₁', hn, ⟨tr, he, ht, hlen⟩, hr⟩ :=
    TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb .supply D qt₁ m₁ qt₂ m₂ X aux old dir hq
  have he' := exec_prefix he
  rw [← hx] at he' ht
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz s (.inr (.inl .supply)) hstep tr he' (by omega)
  exact ⟨qt₁', m₁', hyt.trans ht, hby, hr, hcy⟩

/-- The proved prefix endpoint supplies current-evaluation control
equality, not an artificial syntactic reset of the continuation. -/
theorem run_after_prefix (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      stepStack (taskEval e (fun j => (x.2 j).focus)) [afterPrefix rate]) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    y.2 = writeDir e true x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.2.val = [verifyLoop rate] ∧ (y.2 38).focus = e.mark ∧
      ∀ j, j ≠ 38 → y.2 j = x.2 j := by
  have hstep : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val =
      ([verifyLoop rate], some (.inr (.inr (.inr true)))) :=
    hs.trans (by rw [afterPrefix, stepStack_seq, stepStack_act])
  obtain ⟨tr, he, hn, ht⟩ := dir_exec (Terminal := Terminal) e true x.2
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz _ (.inr (.inr (.inr true))) hstep tr he (by omega)
  have hout := hyt.trans ht
  refine ⟨hout, hby, hcy, ?_, ?_⟩
  · rw [hout]
    simp [writeDir, GSVProgZLoop.dirSymbol, STape.applyAction]
  · intro j hj
    rw [hout]
    exact Function.update_of_ne hj _ _

/-- info: 'PalPeg.TextFeedPipelineFeedSource.run_after_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_after_prefix

/-- info: 'PalPeg.TextFeedPipelineFeedSource.run_feed_blank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_feed_blank

/-- info: 'PalPeg.TextFeedPipelineFeedSource.feed_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms feed_present

end PalPeg.TextFeedPipelineFeedSource
