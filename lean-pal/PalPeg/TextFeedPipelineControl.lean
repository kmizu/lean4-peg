import PalPeg.TextFeedPipelineBank

/-! One finite source continuation orders preparation, prefix alignment,
direction initialization, and the streaming zigzag loop. Input calls keep
that continuation suspended; phase handoff is ordinary sequential control. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineControl
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.TextFeedPipelineBank

variable {k : ℕ} {Terminal : Type}

abbrev TaskAct (k : ℕ) := PrepAct k ⊕ (TextFeedPrefixAtomic.Act ⊕ (GSVProg.Act10 ⊕ Bool))
inductive Gate where
  | up | always | scanWait | verifyWait | blankX
  deriving DecidableEq, Fintype

abbrev TaskCond (k : ℕ) := PrepCond k ⊕ (TextFeedPrefixAtomic.Cond ⊕ (GSVProg.Cond10 ⊕ Gate))
abbrev Task (k : ℕ) := Prog (TaskAct k) (TaskCond k)

def liftPrep (p : Prog (PrepAct k) (PrepCond k)) : Task k := p.map Sum.inl Sum.inl
def liftPrefix (p : Prog TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond) : Task k :=
  p.map (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
def feedHead : Task k :=
  .ite (.inr (.inl .blankText)) (.act (.inr (.inl .supply))) .skip

def afterVerify (a : GSVProg.Act10 ⊕ Bool) : Task k :=
  match a with
  | .inl a => if a.1 = GSVProg.e8 GSTapes.tT ∧ a.2.2 = .right then feedHead else .skip
  | .inr _ => .skip

def waitText1 : Task k := .loop (.inr (.inl .blankText)) (.inr (.inl .supply)) .skip
def waitText2 : Task k :=
  .loop (.inr (.inr (.inr .blankX))) (.inr (.inr (.inl (GSVProg.tX, true, .stay)))) .skip

def beforeVerify (a : GSVProg.Act10 ⊕ Bool) : Task k :=
  match a with
  | .inl a =>
    if a.2.2 = .right then
      if a.1 = GSVProg.e8 GSTapes.tT then waitText1
      else if a.1 = GSVProg.tX then waitText2 else .skip
    else .skip
  | .inr _ => .skip

def verifyCond : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond → TaskCond k
  | .inl c => .inr (.inr (.inl c))
  | .inr .up => .inr (.inr (.inr .up))
  | .inr .always => .inr (.inr (.inr .always))

def beforeCond : GSVProg.Cond10 ⊕ GSVProgZLoop.DCond → Task k
  | .inl .matchOk => .loop (.inr (.inr (.inr .scanWait))) (.inr (.inl .supply)) .skip
  | .inl .compOk => .loop (.inr (.inr (.inr .verifyWait)))
      (.inr (.inr (.inl (GSVProg.tX, true, .stay)))) .skip
  | _ => .skip

def verifyAct (a : GSVProg.Act10 ⊕ Bool) : Task k :=
  .seq (beforeVerify a) (.seq (.act (.inr (.inr a))) (afterVerify a))

/-- Feed Q1 after each text-right instruction, including mandatory loop
actions, before any subsequent source guard can read the new cell. -/
def liftVerify : GSVProgZLoop.DProg → Task k
  | .skip => .skip
  | .act a => verifyAct a
  | .seq p q => .seq (liftVerify p) (liftVerify q)
  | .ite c p q => .seq (beforeCond c) (.ite (verifyCond c) (liftVerify p) (liftVerify q))
  | .loop c a b => .seq (beforeCond c)
      (.loop (verifyCond c) (.inr (.inl .idle))
        (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c))))

/-- Fill Txt2 in place before the first comparison (and retry at later
iterations if the input had not yet arrived). -/
def feedHead2 : Task k := .act (.inr (.inr (.inl (GSVProg.tX, true, .stay))))

def verifyBody (rate : ℕ) : Task k :=
  .seq feedHead (.seq feedHead2 (liftVerify (GSVProgZLoop.stepProg rate)))

/-- Check for a blank Q1 cell before a comparison, never overwrite a
previously supplied cell. Txt2 right moves are fed by the verifier bank. -/
def verifyLoop (rate : ℕ) : Task k :=
  .loop (.inr (.inr (.inr .always))) (.inr (.inl .idle)) (verifyBody rate)

def afterPrefix (rate : ℕ) : Task k :=
  .seq (.act (.inr (.inr (.inr true)))) (verifyLoop rate)

def afterPrep (rate : ℕ) : Task k := .seq (liftPrefix TextFeedPrefixAtomic.source) (afterPrefix rate)

def task (e : Env k) (leftSym : Fin k) (rate : ℕ) : Task k :=
  .seq (liftPrep (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate)) (afterPrep rate)

def taskLabel : TaskAct k → Label k
  | .inl a => .prep a
  | .inr (.inl a) => .prefix a
  | .inr (.inr (.inl a)) => .verify a
  | .inr (.inr (.inr up)) => .dir up

noncomputable def taskEval (e : Env k) (σ : Fin 39 → Fin k) : TaskCond k → Bool
  | .inl c => (prepInterp (Terminal := Unit) e.blank e.endSym e.mark).condOf c (fun j => σ (prepSlot j))
  | .inr (.inl c) => TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAdd 19 j)) c
  | .inr (.inr (.inl c)) => GSVProg.condOf10 e.endSym e.mark e.startSym c
      (fun j => σ (verifySlot (VerifierFeedShared.verifierSlot j)))
  | .inr (.inr (.inr .up)) => decide (σ 38 = e.mark)
  | .inr (.inr (.inr .always)) => true
  | .inr (.inr (.inr .scanWait)) => decide (σ 11 ≠ e.endSym ∧ σ 12 = e.blank)
  | .inr (.inr (.inr .verifyWait)) => decide (σ 19 ≠ e.endSym ∧ σ 20 = e.blank)
  | .inr (.inr (.inr .blankX)) => decide (σ 20 = e.blank)

theorem prep_step (e : Env k) (T : Fin 39 → STape (Fin k))
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (a : PrepAct k)
    (h : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView T j).focus)) s).2 = some a) :
    stepStack (taskEval e (fun j => (T j).focus)) (s.map liftPrep ++ r) =
      ((stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView T j).focus)) s).1.map liftPrep ++ r,
        some (.inl a)) :=
  (step_sim_map Sum.inl Sum.inl _ _ (fun _ => rfl) s r).1 a h

theorem prep_return (e : Env k) (T : Fin 39 → STape (Fin k))
    (s : Stack (PrepAct k) (PrepCond k)) (rate : ℕ)
    (h : (stepStack (evalConds (TextFeedPrepResume.source e) (fun j => (prepView T j).focus)) s).2 = none) :
    stepStack (taskEval e (fun j => (T j).focus)) (s.map liftPrep ++ [afterPrep rate]) =
      stepStack (taskEval e (fun j => (T j).focus)) [liftPrefix TextFeedPrefixAtomic.source, afterPrefix rate] := by
  have hh : stepStack (taskEval e (fun j => (T j).focus)) (s.map liftPrep ++ [afterPrep rate]) =
      stepStack (taskEval e (fun j => (T j).focus)) [afterPrep rate] :=
    (step_sim_map Sum.inl Sum.inl
    (evalConds (TextFeedPrepResume.source e) (fun j => (prepView T j).focus))
    (taskEval e (fun j => (T j).focus)) (fun _ => rfl) s [afterPrep rate]).2 h
  rw [hh, afterPrep, stepStack_seq]

theorem prefix_step (e : Env k) (σ : Fin 39 → Fin k)
    (s : Stack TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond) (r : Stack (TaskAct k) (TaskCond k))
    (a : TextFeedPrefixAtomic.Act)
    (h : (stepStack (TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAdd 19 j))) s).2 = some a) :
    stepStack (taskEval e σ) (s.map liftPrefix ++ r) =
      ((stepStack (TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAdd 19 j))) s).1.map liftPrefix ++ r,
        some (.inr (.inl a))) :=
  (step_sim_map (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl) _ _ (fun _ => rfl) s r).1 a h

/-- A completed prefix immediately selects the real direction write;
there is no halt-and-reset or externally assigned controller. -/
theorem prefix_return (e : Env k) (σ : Fin 39 → Fin k)
    (s : Stack TextFeedPrefixAtomic.Act TextFeedPrefixAtomic.Cond) (rate : ℕ)
    (h : (stepStack (TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAdd 19 j))) s).2 = none) :
    stepStack (taskEval e σ) (s.map liftPrefix ++ [afterPrefix rate]) =
      ([verifyLoop rate], some (.inr (.inr (.inr true)))) := by
  have hh : stepStack (taskEval e σ) (s.map liftPrefix ++ [afterPrefix rate]) =
      stepStack (taskEval e σ) [afterPrefix rate] :=
    (step_sim_map (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)
    (TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAdd 19 j))) (taskEval e σ)
    (fun _ => rfl) s [afterPrefix rate]).2 h
  rw [hh, afterPrefix, stepStack_seq, stepStack_act]

theorem verify_start (e : Env k) (σ : Fin 39 → Fin k) (rate : ℕ) :
    stepStack (taskEval e σ) [verifyLoop (k := k) rate] =
      ([verifyBody rate, verifyLoop rate], some (.inr (.inl .idle))) := by
  rw [verifyLoop, stepStack_loop]
  rfl

abbrev Index (k : ℕ) := Fin (Fintype.card (Label k))
noncomputable def encode (a : Label k) : Index k := Fintype.equivFin _ a
noncomputable def decode (i : Index k) : Label k := (Fintype.equivFin _).symm i
@[simp] theorem decode_encode (a : Label k) : decode (encode a) = a := Equiv.symm_apply_apply _ _
noncomputable def programs (e : Env k) (i : Index k) := low e (decode i)

noncomputable def interp (e : Env k) : InterpF Terminal (Act k) (Cond k) (Fin k) 39 where
  toInterp := TextFeedPipelineBank.interp e
  flagOf _ := none

abbrev Outer (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  Fin (R + 1) × Bool × CtrlS (task e leftSym rate)

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

noncomputable def choose (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 39 → Fin k) : Outer e leftSym R rate × Index k :=
  if c.1 = 0 then ((nextPhase c.1, false, c.2.2), encode (.enqueue c.2.1))
  else ((nextPhase c.1, c.2.1, stepCtrlS (task e leftSym rate) (taskEval e σ) c.2.2),
    encode (taskLabel ((stepStack (taskEval e σ) c.2.2.val).2.getD (.inr (.inl .idle)))))

theorem choose_zero (e : Env k) (leftSym : Fin k) (R rate : ℕ) (first : Bool)
    (c : CtrlS (task e leftSym rate)) (σ : Fin 39 → Fin k) :
    choose e leftSym R rate (0, first, c) σ = ((nextPhase 0, false, c), encode (.enqueue first)) := by
  simp only [choose, ↓reduceIte]

theorem choose_counter (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 39 → Fin k) :
    (choose e leftSym R rate c σ).1.1 = nextPhase c.1 := by
  unfold choose
  split <;> rfl

noncomputable def run (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  callRun (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e leftSym R rate) 93 e.blank

def isEnqueue : Label k → Bool
  | .enqueue _ => true
  | _ => false

theorem task_not_enqueue (a : TaskAct k) : isEnqueue (taskLabel a) = false := by
  rcases a with a | a
  · rfl
  rcases a with a | a
  · rfl
  rcases a with a | a <;> rfl

theorem choose_enqueues (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (c : Outer e leftSym R rate) (σ : Fin 39 → Fin k) :
    isEnqueue (decode (choose e leftSym R rate c σ).2) = decide (c.1 = 0) := by
  by_cases h : c.1 = 0
  · rw [choose, if_pos h]
    simp only [decode_encode, isEnqueue, h, decide_true]
  · rw [choose, if_neg h]
    simp only [decode_encode, task_not_enqueue, h, decide_false]

theorem run_counter (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) :
    (run (Terminal := Terminal) e leftSym R rate x).1.1.1 = nextPhase x.1.1.1 := choose_counter e leftSym R rate _ _

theorem run_counter_iterate (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) :
    ((run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.1 = nextPhase^[N] x.1.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', run_counter, ih, Function.iterate_succ_apply']

/-- Exactly one enqueue is selected per input frame, irrespective of
which source phase the other calls execute. -/
theorem run_enqueues_once (e : Env k) (leftSym : Fin k) (R rate N : ℕ) (hN : N < R + 1)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hz : x.1.1.1 = 0) :
    let y := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    isEnqueue (decode (choose e leftSym R rate y.1.1 (fun j => (y.2 j).focus)).2) = decide (N = 0) := by
  dsimp only
  rw [choose_enqueues, run_counter_iterate, hz]
  change decide ((nextPhase^[N] (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1))) = ⟨0, Nat.zero_lt_succ R⟩) = _
  rw [nextPhase_iterate (Nat.zero_lt_succ R) N hN]
  simp only [Fin.mk.injEq]

noncomputable def machine (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) :=
  callFrameMachine (programs e) (fun _ => interp e) (choose e leftSym R rate) 93 (R + 1) e.blank
    (by omega : 0 < 39) (0, true, startCtrlS (task e leftSym rate)) (encode (.prefix .idle))
    (DualQueueShared.capture enc)

theorem machine_round (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k)) (a : Terminal) :
    (machine e leftSym enc R rate).sRound { state := ((c, 0), 0), tape := T } a =
      let y := (run (Terminal := Terminal) e leftSym R rate)^[R + 1]
        (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
      { state := ((y.1, 0), 0), tape := y.2 } :=
  callFrameMachine_round (programs e) (fun _ => interp e) (choose e leftSym R rate) 93 (R + 1) e.blank
    (by omega) (0, true, startCtrlS (task e leftSym rate)) (encode (.prefix .idle)) (DualQueueShared.capture enc) a c T

/-- info: 'PalPeg.TextFeedPipelineControl.prefix_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_return

/-- info: 'PalPeg.TextFeedPipelineControl.machine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms machine_round

/-- info: 'PalPeg.TextFeedPipelineControl.run_enqueues_once' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enqueues_once

end PalPeg.TextFeedPipelineControl
