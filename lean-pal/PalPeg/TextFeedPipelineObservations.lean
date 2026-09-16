import PalPeg.TextFeedPipelineSourceSafety
import PalPeg.ProgLangWait
import PalPeg.TextFeedPipelineActionWait

/-! Extract observations from the genuine 39-tape execution. Enqueue calls
do not step the source. All worker observations come from actual tape focuses. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineObservations
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl
open PalPeg.ProgLangWait
variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

theorem run_source (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) :
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.2.2.val =
      if x.1.1.1 = 0 then x.1.1.2.2.val
      else (stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val).1 := by
  change (TextFeedPipelineControl.choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).1.2.2.val = _
  unfold TextFeedPipelineControl.choose
  split <;> rfl

noncomputable def observations (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    ℕ → (CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) →
      List (TaskCond k → Bool)
  | 0, _ => []
  | N + 1, x =>
    let rest := observations e leftSym R rate N
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x)
    if x.1.1.1 = 0 then rest else taskEval e (fun j => (x.2 j).focus) :: rest

/-- No invented oracle sequence: interpreting the observations extracted
from real execution recovers its exact residual source stack. -/
theorem run_observe (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) :
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.2.val =
      (observe (observations (Terminal := Terminal) e leftSym R rate N x) x.1.1.2.2.val).1 := by
  induction N generalizing x with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih, observations]
    by_cases hz : x.1.1.1 = 0
    · rw [if_pos hz, run_source, if_pos hz]
    · rw [if_neg hz, observe_cons, run_source, if_neg hz]

theorem observations_length (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))) :
    (observations (Terminal := Terminal) e leftSym R rate N x).length ≤ N := by
  induction N generalizing x with
  | zero => exact Nat.le_refl 0
  | succ N ih =>
    rw [observations]
    split
    · exact Nat.le_succ_of_le (ih _)
    · exact Nat.succ_le_succ (ih _)

/-- A real pending command survives any number of enqueue calls and blocked
worker observations. Once its actual observations end in release, its real
source continuation contains exactly the after-feed command and old suffix. -/
theorem run_pending_release (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (a : GSVProg.Act10 ⊕ Bool) (c : TaskCond k) (w : TaskAct k)
    (hbefore : beforeVerify a = .loop c w .skip)
    (s : Stack (TaskAct k) (TaskCond k)) (hs : x.1.1.2.2.val = verifyAct a :: s)
    (xs : List (TaskCond k → Bool)) (last : TaskCond k → Bool)
    (ho : observations (Terminal := Terminal) e leftSym R rate N x = xs ++ [last])
    (hw : ∀ ev ∈ xs, ev c = true) (hl : last c = false) :
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.2.val =
      afterVerify a :: s := by
  rw [run_observe, ho, hs, TextFeedPipelineActionWait.pending_release a c w hbefore s xs last hw hl]

/-- info: 'PalPeg.TextFeedPipelineObservations.run_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_observe

end PalPeg.TextFeedPipelineObservations
