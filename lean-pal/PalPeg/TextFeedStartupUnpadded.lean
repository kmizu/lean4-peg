import PalPeg.TextFeedPrepEndpoint
import PalPeg.TextFeedUnpadded

/-! The arrival-bearing startup machine needs no physical right padding,
including at the partial-frame endpoint used for the worker handoff. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupUnpadded
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2
open PalPeg.TextFeedControl PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule
open PalPeg.TextFeedPrepEndpoint

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem calls_blankEq (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    {x y : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k))}
    (hc : x.1 = y.1) (ht : ∀ j, STape.BlankEq e.blank (x.2 j) (y.2 j)) :
    let u := (run (Terminal := Terminal) e leftSym R rate)^[N] x
    let v := (run (Terminal := Terminal) e leftSym R rate)^[N] y
    u.1 = v.1 ∧ ∀ j, STape.BlankEq e.blank (u.2 j) (v.2 j) := by
  let M := callMachine (programs e) (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank (by omega : 0 < 27) x.1.1 x.1.2.1
  have h : ConfigBlankEq M.blank
      { state := (x.1, (⟨0, by omega⟩ : Fin 49)), tape := x.2 }
      { state := (y.1, (⟨0, by omega⟩ : Fin 49)), tape := y.2 } := ⟨by rw [hc], ht⟩
  have hf := M.microSteps_blankEq (List.replicate (N * 49) none) h
  dsimp only [M] at hf
  rw [callMachine_noneBlocks, callMachine_noneBlocks] at hf
  dsimp only [ConfigBlankEq] at hf
  exact ⟨Prod.mk.inj hf.1 |>.1, hf.2⟩

theorem stateBefore_blankEq (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    {T U : Fin 27 → STape (Fin k)} (h : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (word : List Terminal) :
    ConfigBlankEq e.blank (stateBefore e leftSym enc R rate c T word)
      (stateBefore e leftSym enc R rate c U word) :=
  (machine e leftSym enc R rate).runFrom_blankEq word ⟨rfl, h⟩

theorem prefixRun_blankEq (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    {T U : Fin 27 → STape (Fin k)} (h : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (word : List Terminal) (a : Terminal) (N : ℕ) :
    let x := prefixRun e leftSym enc R rate c T word a N
    let y := prefixRun e leftSym enc R rate c U word a N
    x.1 = y.1 ∧ ∀ j, STape.BlankEq e.blank (x.2 j) (y.2 j) := by
  have hs := stateBefore_blankEq e leftSym enc R rate c h word
  apply calls_blankEq e leftSym R rate N (congrArg (fun q => q.1.1) hs.1)
  have hf : (fun j => ((stateBefore e leftSym enc R rate c T word).tape j).focus) =
      (fun j => ((stateBefore e leftSym enc R rate c U word).tape j).focus) :=
    funext fun j => (hs.2 j).focus
  intro j
  unfold arriveA
  rw [hf]
  exact (hs.2 j).applyAction _

theorem birth_prefixRun_blankEq (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (R rate : ℕ) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (w : List (Fin k)) (L padding : ℕ) (old : Fin k)
    (word : List Terminal) (a : Terminal) (N : ℕ) :
    let T := TextFeedPrepare.before e (StageBirth.birthTapes e.blank e.mark leftSym w L 0) old
    let U := TextFeedPrepare.before e (StageBirth.birthTapes e.blank e.mark leftSym w L padding) old
    let x := prefixRun e leftSym enc R rate c T word a N
    let y := prefixRun e leftSym enc R rate c U word a N
    x.1 = y.1 ∧ ∀ j, STape.BlankEq e.blank (x.2 j) (y.2 j) :=
  prefixRun_blankEq e leftSym enc R rate c
    (TextFeedPrepare.before_blankEq old
      (TextFeedPrepare.birthTapes_blankEq e.blank e.mark leftSym w L padding)) word a N

/-- info: 'PalPeg.TextFeedStartupUnpadded.calls_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calls_blankEq

/-- info: 'PalPeg.TextFeedStartupUnpadded.birth_prefixRun_blankEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms birth_prefixRun_blankEq

end PalPeg.TextFeedStartupUnpadded
