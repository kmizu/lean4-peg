import PalPeg.TextFeedStartupBank

/-! One finite control runs preparation and then the persistent worker.
Enqueue interrupts preserve that control, including partially executed
preparation loops. The first enqueue is the only bootstrap call. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupSchedule
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.PrepInstance
open PalPeg.TextFeedStartupBank

variable {k : ℕ} {Terminal : Type}

abbrev TaskAct (k : ℕ) := PrepAct k ⊕ TextFeedSchedule.WorkerAct
abbrev TaskCond (k : ℕ) := PrepCond k ⊕ TextFeedSchedule.WorkerCond

def task (e : Env k) (leftSym : Fin k) (rate : ℕ) : Prog (TaskAct k) (TaskCond k) :=
  .seq ((finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate).map Sum.inl Sum.inl)
    ((TextFeedSchedule.worker rate).map Sum.inr Sum.inr)

def taskLabel : TaskAct k → Label k
  | .inl a => .prep a
  | .inr a => .feed (TextFeedSchedule.workerLabel a)

noncomputable def taskCond (e : Env k) : TaskCond k → (Fin 27 → Fin k) → Bool
  | .inl c, σ => (prepInterp (Terminal := Unit) e.blank e.endSym e.mark).condOf c
      (fun j => σ (prepSlot j))
  | .inr c, σ => TextFeedSchedule.workerCond e c (fun j => σ (TextFeedPrepare.feedSlot j))

abbrev Index (k : ℕ) := Fin (Fintype.card (Label k))
noncomputable def encode (a : Label k) : Index k := Fintype.equivFin (Label k) a
noncomputable def decode (a : Index k) : Label k := (Fintype.equivFin (Label k)).symm a

@[simp] theorem decode_encode (a : Label k) : decode (encode a) = a :=
  Equiv.symm_apply_apply _ _

noncomputable def programs (e : Env k) (i : Index k) := low e (decode i)

noncomputable def interp (e : Env k) :
    InterpF Terminal (TextFeedStartupBank.Act k) (TextFeedStartupBank.Cond k) (Fin k) 27 where
  toInterp := shared e
  flagOf _ := none

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

abbrev Outer (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  Fin (R + 1) × Bool × CtrlS (task e leftSym rate)

noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def inputSlot : Fin 27 := ⟨26, by omega⟩

noncomputable def choose (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 27 → Fin k) :
    Outer e leftSym R rate × Index k :=
  if c.1 = ⟨0, Nat.zero_lt_succ R⟩ then
    ((nextPhase c.1, false, c.2.2),
      encode (if c.2.1 then .first (σ inputSlot) else .feed (.enqueue (σ inputSlot))))
  else
    ((nextPhase c.1, c.2.1, stepCtrlS (task e leftSym rate) (fun b => taskCond e b σ) c.2.2),
      encode (taskLabel ((stepStack (fun b => taskCond e b σ) c.2.2.val).2.getD (.inr .idle))))

/-- Input interrupts never advance or reset the suspended task. -/
theorem choose_zero (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (first : Bool) (c : CtrlS (task e leftSym rate)) (σ : Fin 27 → Fin k) :
    choose e leftSym R rate (⟨0, Nat.zero_lt_succ R⟩, first, c) σ =
      ((nextPhase ⟨0, Nat.zero_lt_succ R⟩, false, c),
        encode (if first then .first (σ inputSlot) else .feed (.enqueue (σ inputSlot)))) := by
  simp only [choose, ↓reduceIte]

theorem choose_counter (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 27 → Fin k) :
    (choose e leftSym R rate c σ).1.1 = nextPhase c.1 := by
  unfold choose
  split_ifs <;> rfl

def isEnqueue : Label k → Bool
  | .first _ => true
  | .feed (.enqueue _) => true
  | _ => false

theorem task_not_enqueue (a : TaskAct k) : isEnqueue (taskLabel a) = false := by
  rcases a with a | a
  · rfl
  · cases a <;> rfl

theorem choose_enqueues (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 27 → Fin k) :
    isEnqueue (decode (choose e leftSym R rate c σ).2) =
      decide (c.1 = ⟨0, Nat.zero_lt_succ R⟩) := by
  by_cases h : c.1 = ⟨0, Nat.zero_lt_succ R⟩
  · rw [choose, if_pos h]
    cases c.2.1 <;> simp [isEnqueue, h]
  · rw [choose, if_neg h]
    simp only [decode_encode, task_not_enqueue, h, decide_false]

noncomputable def run (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  callRun (programs e) (fun _ => interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank

theorem run_counter (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k))) :
    (run (Terminal := Terminal) e leftSym R rate x).1.1.1 = nextPhase x.1.1.1 :=
  choose_counter e leftSym R rate _ _

theorem run_counter_iterate (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k))) :
    ((run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.1 =
      nextPhase^[N] x.1.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', run_counter, ih,
      Function.iterate_succ_apply']

theorem run_enqueues_once (e : Env k) (leftSym : Fin k) (R rate N : ℕ) (hN : N < R + 1)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    isEnqueue (decode (choose e leftSym R rate y.1.1 (fun j => (y.2 j).focus)).2) =
      decide (N = 0) := by
  dsimp only
  rw [choose_enqueues, run_counter_iterate, hc0,
    nextPhase_iterate (Nat.zero_lt_succ R) N hN]
  simp only [Fin.mk.injEq]

def capture (enc : Terminal → Fin k) : ArriveAct Terminal (Fin k) 27 :=
  fun a σ j => if j = inputSlot then ((a.map enc).getD (σ j), .stay) else (σ j, .stay)

/-- A fixed 27-tape arrival-bearing machine; its control contains neither
the input word, the stage length, nor an externally supplied prep result. -/
noncomputable def machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) :=
  callFrameMachine (programs e) (fun _ => interp e)
    (choose e leftSym R rate) 48 (R + 1) e.blank (by omega : 0 < 27)
    (⟨0, Nat.zero_lt_succ R⟩, true, startCtrlS (task e leftSym rate))
    (encode (.feed .idle)) (capture enc)

theorem machine_round (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (a : Terminal) :
    (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a =
      let y := (run (Terminal := Terminal) e leftSym R rate)^[R + 1]
        (c, arriveA e.blank (capture enc) (some a) T)
      { state := ((y.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := y.2 } :=
  callFrameMachine_round (programs e) (fun _ => interp e)
    (choose e leftSym R rate) 48 (R + 1) e.blank (by omega)
    (⟨0, Nat.zero_lt_succ R⟩, true, startCtrlS (task e leftSym rate))
    (encode (.feed .idle)) (capture enc) a c T

/-- info: 'PalPeg.TextFeedStartupSchedule.run_enqueues_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enqueues_once

/-- info: 'PalPeg.TextFeedStartupSchedule.machine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round

end PalPeg.TextFeedStartupSchedule
