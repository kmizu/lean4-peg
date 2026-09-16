import PalPeg.TextFeedPrepEndpoint

/-! Connect the actual post-handoff tapes and live finite continuation to
the existing streaming/deadline invariant, with all prep-time arrivals
still queued and the true arrival count retained. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepared
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt

variable {k : ℕ}

theorem scanner_of_prepared {e : Env k} {T : Fin 27 → STape (Fin k)}
    {S : PatternTapes.Tapes k} {qt : QT k} {m : Mode} {F : Stage k} {old : Fin k}
    (hv : prepView T = TSg S) (hf : feedView T = rtapes e qt m F old) : F = GSProg.TS (toGS S) := by
  funext i
  have hi : feedSlot (scanSlot i) = prepSlot (Fin.castAddEmb 7 i) := by
    apply Fin.ext
    change (if h : 11 + i.val < 19 then (⟨11 + i.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val =
      11 + i.val
    rw [dif_pos (show 11 + i.val < 19 by have := i.isLt; omega)]
  have hx : T (feedSlot (scanSlot i)) = F i := by
    simpa only [feedView, scanSlot, rtapes, TextFeedControl.tapes, Fin.castAddEmb_apply,
      Fin.natAddEmb_apply, Fin.append_left, Fin.append_right] using congrFun hf (scanSlot i)
  calc
    F i = T (feedSlot (scanSlot i)) := hx.symm
    _ = prepView T (Fin.castAddEmb 7 i) := congrArg T hi
    _ = TSg S (Fin.castAddEmb 7 i) := congrFun hv _
    _ = GSProg.TS (toGS S) i := rfl

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

/-- A proof-only reference controller, not an assignment to the physical
machine: its worker has executed the same initial idle as the handoff. -/
noncomputable def fillCtrl (e : Env k) (R rate : ℕ) (counter : Fin (R + 1)) (S : Stage k) :
    CallCtrl (TextFeedAtomic.programs e.blank e.mark) (TextFeedSchedule.Outer R rate) :=
  ((counter, stepCtrlS (TextFeedSchedule.worker rate) (TextFeedCycle.eval e S)
    (startCtrlS (TextFeedSchedule.worker rate))), TextFeedSchedule.encode .idle,
    initialBank (TextFeedAtomic.programs e.blank e.mark), false)

theorem fillCtrl_stack (e : Env k) (R rate : ℕ) (counter : Fin (R + 1)) (S : Stage k) :
    (fillCtrl e R rate counter S).1.2.val = TextFeedCycle.beforeFill rate := by
  change (stepStack (TextFeedCycle.eval e S) [TextFeedSchedule.worker rate]).1 = _
  rw [TextFeedCycle.loop_step]

/-- Prepared tape encoding, queue readiness, and the observed live task
continuation produce the exact existing Sim and a physical-machine Link.
The backlog is not reset, and n is not replaced by zero. -/
theorem prepared_link {e : Env k} {leftSym : Fin k} {R rate p₁ rem n : ℕ}
    {x : TextFeedWorkerBridge.Phys e leftSym R rate} {S : PatternTapes.Tapes k}
    {q : Queue (Fin k)} {old : Fin k} {v Text : List (Fin k)}
    (hb : AtBoundary (programs e) x.1.2.2.1) (hfirst : x.1.1.2.1 = false)
    (hstack : x.1.1.2.2.val = (TextFeedCycle.beforeFill rate).map (Prog.map Sum.inr Sum.inr))
    (hv : prepView x.2 = TSg S) (hq : ReadyAt e x.2 q old) (hl : toList q = Text.take n)
    (hscan : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem (toGS S) ⟨0, 0⟩)
    (hdelay : (rate + 1) * n ≤ rate * v.length) :
    ∃ (qt : QT k) (m : Mode) (y : TextFeedRefine.Phys e R rate),
      TextFeedWorkerBridge.Link e leftSym R rate x y ∧
      TextFeedRefine.Sim e v Text R rate p₁ rem n (TextFeedBacklog.model (toGS S) qt m q) .fill y old ∧
      TextFeedRefine.workScale rate * ((rate + 1) * n) ≤
        TextFeedRefine.workCredit v rate (TextFeedBacklog.model (toGS S) qt m q, .fill) := by
  obtain ⟨qt, m, F, hview, hr⟩ := hq
  have hF := scanner_of_prepared hv hview
  rw [hF] at hview
  let y : TextFeedRefine.Phys e R rate :=
    (fillCtrl e R rate x.1.1.1 (GSProg.TS (toGS S)), rtapes e qt m (GSProg.TS (toGS S)) old)
  have hctrl : y.1.1.2.val = TextFeedCycle.beforeFill rate := fillCtrl_stack e R rate _ _
  have hybank : AtBoundary (TextFeedAtomic.programs e.blank e.mark) y.1.2.2.1 := initialBank_boundary _
  refine ⟨qt, m, y, ?_, ?_, ?_⟩
  · refine ⟨⟨hfirst, rfl, ?_⟩, hview, hb, hybank⟩
    rw [hctrl]
    exact hstack
  · exact ⟨TextFeedBacklog.feedInv hscan hr hl, hybank, hctrl, trivial, qt, m, rfl, hr⟩
  · change TextFeedRefine.workScale rate * ((rate + 1) * n) ≤
      TextFeedRefine.workCredit v rate (TextFeedBacklog.model (toGS S) qt m q, .loop)
    exact TextFeedBacklog.credit hdelay

/-- info: 'PalPeg.TextFeedPrepared.prepared_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_link

end PalPeg.TextFeedPrepared
