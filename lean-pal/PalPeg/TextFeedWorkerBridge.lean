import PalPeg.TextFeedPrepHandoff

/-! The worker phase of the combined startup machine refines the existing
feeder controller and its atomic calls. This transports its streaming
correctness without copying tapes or replacing the live task control. -/
set_option autoImplicit false

namespace PalPeg.TextFeedWorkerBridge
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety

variable {k : ℕ} {Terminal : Type}

def workerLift : Prog TextFeedSchedule.WorkerAct TextFeedSchedule.WorkerCond →
    Prog (TaskAct k) (TaskCond k) := Prog.map Sum.inr Sum.inr

theorem worker_step_map (e : Env k) (σ : Fin 27 → Fin k)
    (s : Stack TextFeedSchedule.WorkerAct TextFeedSchedule.WorkerCond) :
    stepStack (fun c => taskCond e c σ) (s.map workerLift) =
      ((stepStack (fun c => TextFeedSchedule.workerCond e c (fun j => σ (feedSlot j))) s).1.map workerLift,
        (stepStack (fun c => TextFeedSchedule.workerCond e c (fun j => σ (feedSlot j))) s).2.map Sum.inr) := by
  let ev := fun c => TextFeedSchedule.workerCond e c (fun j => σ (feedSlot j))
  have hh := step_sim_map (A₂ := TaskAct k) Sum.inr Sum.inr ev
    (fun c => taskCond e c σ) (fun _ => rfl) s []
  cases ha : (stepStack ev s).2 with
  | some a =>
    have ht := hh.1 a ha
    simpa only [List.append_nil, ha, Option.map_some, ev, workerLift] using ht
  | none =>
    have ht := hh.2 ha
    have hs := stepStack_snd_eq_none ev s ha
    simpa only [List.append_nil, stepStack_nil, hs, List.map_nil, ha, Option.map_none,
      ev, workerLift] using ht

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _

structure CtrlLink (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (d : TextFeedSchedule.Outer R rate) : Prop where
  first : c.2.1 = false
  counter : c.1 = d.1
  stack : c.2.2.val = d.2.val.map workerLift

theorem choose_link {e : Env k} {leftSym : Fin k} {R rate : ℕ}
    {c : Outer e leftSym R rate} {d : TextFeedSchedule.Outer R rate}
    (h : CtrlLink e leftSym R rate c d) (σ : Fin 27 → Fin k) :
    CtrlLink e leftSym R rate (choose e leftSym R rate c σ).1
      (TextFeedSchedule.choose e R rate d (fun j => σ (feedSlot j))).1 ∧
    decode (choose e leftSym R rate c σ).2 =
      .feed (TextFeedAtomic.decode (TextFeedSchedule.choose e R rate d (fun j => σ (feedSlot j))).2) := by
  by_cases hc : c.1 = ⟨0, Nat.zero_lt_succ R⟩
  · have hd : d.1 = ⟨0, Nat.zero_lt_succ R⟩ := h.counter ▸ hc
    rw [TextFeedStartupSchedule.choose, if_pos hc, TextFeedSchedule.choose, if_pos hd]
    simp only [h.first, Bool.false_eq_true, ↓reduceIte, decode_encode, TextFeedSchedule.decode_encode]
    exact ⟨⟨rfl, congrArg nextPhase h.counter, h.stack⟩, rfl⟩
  · have hd : d.1 ≠ ⟨0, Nat.zero_lt_succ R⟩ := by rw [← h.counter]; exact hc
    have hm := worker_step_map e σ d.2.val
    rw [← h.stack] at hm
    rw [TextFeedStartupSchedule.choose, if_neg hc, TextFeedSchedule.choose, if_neg hd]
    simp only [decode_encode, TextFeedSchedule.decode_encode]
    constructor
    · refine ⟨h.first, congrArg nextPhase h.counter, ?_⟩
      simp only [stepCtrlS_val, hm]
    · simp only [hm]
      cases ha : (stepStack (fun c => TextFeedSchedule.workerCond e c (fun j => σ (feedSlot j))) d.2.val).2
        <;> rfl

abbrev Phys (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k))

structure Link (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : Phys e leftSym R rate) (y : TextFeedRefine.Phys e R rate) : Prop where
  ctrl : CtrlLink e leftSym R rate x.1.1 y.1.1
  tapes : feedView x.2 = y.2
  bank : AtBoundary (programs e) x.1.2.2.1
  oldBank : AtBoundary (TextFeedAtomic.programs e.blank e.mark) y.1.2.2.1

attribute [local irreducible] ProgLangBank.runChunk

/-- Both real atomic calls execute the same original low program. Their
queue representation and all twenty feeder tapes therefore agree exactly. -/
theorem run_link {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate}
    (h : Link e leftSym R rate x y) {q : Queue (Fin k)} {old : Fin k}
    (hq : ReadyAt e x.2 q old) (ha : old ≠ e.mark) :
    Link e leftSym R rate (run (Terminal := Terminal) e leftSym R rate x)
      (TextFeedSchedule.run (Terminal := Terminal) e R rate y) ∧
    ReadyAt e (run (Terminal := Terminal) e leftSym R rate x).2
      (queueEffect e (decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) q) old := by
  obtain ⟨qt, m, S, hv, hr⟩ := hq
  have hy : y.2 = rtapes e qt m S old := h.tapes.symm.trans hv
  have hcsel := choose_link h.ctrl (fun j => (x.2 j).focus)
  have hσ : (fun j => (x.2 (feedSlot j)).focus) = (fun j => (y.2 j).focus) := by
    change (fun j => (feedView x.2 j).focus) = _
    rw [h.tapes]
  rw [hσ] at hcsel
  let a := TextFeedAtomic.decode (TextFeedSchedule.choose e R rate y.1.1 (fun j => (y.2 j).focus)).2
  have hal : TextFeedAtomic.allowed e.mark a := TextFeedSchedule.choose_allowed e R rate y.1.1 _
    (by rw [hy, TextFeedSchedule.input_focus]; exact ha)
  obtain ⟨n, qt', m', hn, ⟨tr, he, hlen, hout⟩, hr'⟩ :=
    TextFeedAtomic.low_bounded (Terminal := Terminal) hc hmb hr S old a hal
  have heY : Exec (TextFeedAtomic.interp (Terminal := Terminal) e).toInterp e.blank
      (TextFeedAtomic.programs e.blank e.mark
        (TextFeedSchedule.choose e R rate y.1.1 (fun j => (y.2 j).focus)).2) y.2 tr := by
    simpa only [TextFeedAtomic.interp, TextFeedAtomic.programs, a, hy] using he
  obtain ⟨hyout, hby, _, _⟩ := callRun_exec (TextFeedAtomic.programs e.blank e.mark)
    (fun _ => TextFeedAtomic.interp (Terminal := Terminal) e) (TextFeedSchedule.choose e R rate)
    48 e.blank y h.oldBank tr heY (by omega)
  rw [hy, hout] at hyout
  have heX := exec_feed he x.2
  have hx : extend feedSlot (rtapes e qt m S old) x.2 = x.2 := by
    rw [← hv]
    exact extend_restrict feedSlot x.2
  rw [hx] at heX
  have heX' : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2
      (tr.map (extendVec feedSlot x.2)) := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 _
    rw [hcsel.2]
    exact heX
  obtain ⟨hxout, hbx, _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e) (choose e leftSym R rate)
    48 e.blank x h.bank (tr.map (extendVec feedSlot x.2)) heX' (by simp only [List.length_map, hlen]; omega)
  have ht := applyTrace_extend feedSlot e.blank x.2 tr (rtapes e qt m S old)
  rw [hx, hout] at ht
  have hxout' : (run (Terminal := Terminal) e leftSym R rate x).2 =
      extend feedSlot (rtapes e qt' m' (TextFeedAtomic.effect e a q S).2 old) x.2 := hxout.trans ht
  refine ⟨⟨hcsel.1, ?_, hbx, hby⟩, ?_⟩
  · rw [hxout', feedView_extend]
    exact hyout.symm
  · rw [hxout', hcsel.2]
    rw [queueEffect_feed] at hr'
    exact ready_feed hr' _ old x.2

theorem run_link_iterate {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {R rate : ℕ} {x : Phys e leftSym R rate} {y : TextFeedRefine.Phys e R rate}
    (h : Link e leftSym R rate x y) {q : Queue (Fin k)} {old : Fin k}
    (hq : ReadyAt e x.2 q old) (ha : old ≠ e.mark) (N : ℕ) :
    let x' := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    let y' := (TextFeedSchedule.run (Terminal := Terminal) e R rate)^[N] y
    Link e leftSym R rate x' y' ∧ ∃ q', ReadyAt e x'.2 q' old := by
  induction N with
  | zero => exact ⟨h, q, hq⟩
  | succ N ih =>
    obtain ⟨hh, q', hr⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨hh', hr'⟩ := run_link (Terminal := Terminal) hc hmb hh hr ha
    exact ⟨hh', _, hr'⟩

/-- info: 'PalPeg.TextFeedWorkerBridge.choose_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms choose_link

/-- info: 'PalPeg.TextFeedWorkerBridge.run_link_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_link_iterate

end PalPeg.TextFeedWorkerBridge
