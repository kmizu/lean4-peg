import PalPeg.TextFeedStageStartup
import PalPeg.TextFeedStartupUnpadded

/-! The startup theorem on the physically unpadded stage tapes. The
reference padding is existential proof data, never an initialization input. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStageStartup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedPrepEndpoint
open PalPeg.TextFeedStartupBudget

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def ObservedReady (e : Env k) (leftSym : Fin k) (R rate : ℕ) (v Text : List (Fin k))
    (p₁ rem n : ℕ) (x : TextFeedWorkerBridge.Phys e leftSym R rate) : Prop :=
  ∃ y : TextFeedWorkerBridge.Phys e leftSym R rate,
    x.1 = y.1 ∧ (∀ j, STape.BlankEq e.blank (x.2 j) (y.2 j)) ∧
      StreamReady e leftSym R rate v Text p₁ rem n y

theorem birth_reaches_boundary {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {w : List (Fin k)} {L : ℕ}
    (enc : Terminal → Fin k) (input : List Terminal) (old : Fin k)
    (hL : 4 ≤ L) (hw : L ≤ w.length) (hfresh : leftSym ∉ w)
    (htext : L / 2 ≤ input.length)
    (hstart : e.startSym ∉ PrepInstances.stagePat w L)
    (hend : e.endSym ∉ PrepInstances.stagePat w L) (hne : e.startSym ≠ e.endSym)
    (hblank : e.blank ∉ input.map enc) (hmark : e.mark ∉ input.map enc) :
    let d := PrepInstances.prepRes w L
    let v := (PrepInstances.stagePat w L).drop d.1
    let R := startupRate 8
    let T := before e (StageBirth.birthTapes e.blank e.mark leftSym w L 0) old
    ∃ n, 1 ≤ n ∧ n ≤ L / 2 ∧
      let z := stateBefore e leftSym enc R 8 (callInitial e leftSym R 8) T (input.take n)
      ObservedReady e leftSym R 8 v (input.map enc) d.2.1 d.2.2 n (z.state.1.1, z.tape) ∧
        z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  have hpre := StageBirth.birthTapes_prepPre (blank := e.blank) (mark := e.mark)
    (Text := input.map enc) (by omega : 0 < L) hw hfresh (Nat.le_refl (input.map enc).length)
  obtain ⟨n, hn, hhalf, hready, hlocal, hglobal⟩ := setup_reaches_boundary hc hmb enc input old
    hpre hL htext hstart hend hne hblank hmark
  have ht := before_blankEq old (birthTapes_blankEq e.blank e.mark leftSym w L (input.map enc).length)
  have he := TextFeedStartupUnpadded.stateBefore_blankEq e leftSym enc (startupRate 8) 8
    (callInitial e leftSym (startupRate 8) 8) ht (input.take n)
  refine ⟨n, hn, hhalf, ?_, ?_, ?_⟩
  · exact ⟨_, congrArg (fun s => s.1.1) he.1, he.2, hready⟩
  · exact (congrArg (fun s => s.1.2) he.1).trans hlocal
  · exact (congrArg Prod.snd he.1).trans hglobal

/-- info: 'PalPeg.TextFeedStageStartup.birth_reaches_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms birth_reaches_boundary

end PalPeg.TextFeedStageStartup
