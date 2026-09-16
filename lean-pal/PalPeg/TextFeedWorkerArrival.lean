import PalPeg.TextFeedWorkerBridge

/-! Actual arrivals and complete fixed-clock frames preserve the link
from the combined startup machine to the established feeder machine. -/
set_option autoImplicit false

namespace PalPeg.TextFeedWorkerBridge
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput
open PalPeg.TextFeedPrepare PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule
open PalPeg.TextFeedStartupSafety

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
noncomputable local instance (R rate : ℕ) : DecidableEq (TextFeedSchedule.Outer R rate) :=
  Classical.decEq _

theorem capture_link {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate}
    (h : Link e leftSym R rate x y) (enc : Terminal → Fin k) (a : Terminal) :
    Link e leftSym R rate
      (x.1, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) x.2)
      (y.1, arriveA e.blank (TextFeedInput.capture enc) (some a) y.2) := by
  refine ⟨h.ctrl, ?_, h.bank, h.oldBank⟩
  rw [TextFeedStartupRun.capture_view, h.tapes]

theorem frame_link {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate}
    (h : Link e leftSym R rate x y) {q : RTQueue.Queue (Fin k)} {old : Fin k}
    (hq : ReadyAt e x.2 q old) (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) :
    let u := (TextFeedStartupSchedule.machine e leftSym enc R rate).sRound
      { state := ((x.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := x.2 } a
    let v := (TextFeedSchedule.machine e enc R rate).sRound
      { state := ((y.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := y.2 } a
    Link e leftSym R rate (u.state.1.1, u.tape) (v.state.1.1, v.tape) ∧
      (∃ q', ReadyAt e u.tape q' (enc a)) ∧
      u.state.1.2 = ⟨0, by omega⟩ ∧ u.state.2 = ⟨0, by omega⟩ ∧
      v.state.1.2 = ⟨0, by omega⟩ ∧ v.state.2 = ⟨0, by omega⟩ := by
  dsimp only
  rw [TextFeedStartupSchedule.machine_round, TextFeedSchedule.machine_round]
  have hr := run_link_iterate (Terminal := Terminal) hc hmb (capture_link h enc a)
    (TextFeedStartupRun.capture_ready enc a hq) ha (R + 1)
  exact ⟨hr.1, hr.2, rfl, rfl, rfl, rfl⟩

/-- info: 'PalPeg.TextFeedWorkerBridge.frame_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_link

end PalPeg.TextFeedWorkerBridge
