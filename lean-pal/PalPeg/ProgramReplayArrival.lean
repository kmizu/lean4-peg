import PalPeg.ProgramTapeReplay
import PalPeg.ProgramArrivalLog
import PalPeg.ProgramBlankEq

set_option autoImplicit false
namespace PalPeg.Program.ReplayArrival
open PegSeparation.RealTimeTM
variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q]
  [Fintype Γ] [DecidableEq Γ] {t B : ℕ}

def machine (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (enc : Terminal → Γ) (decode : Γ → Terminal) (C : ℕ) :=
  ArrivalLog.machine (TapeReplay.machine M hB decode) enc C

/-- While replaying the old batch, every new real input is captured once
in a disjoint log. Worker execution is exactly the old ordinary-input run. -/
theorem replayed (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (enc : Terminal → Γ) (decode : Γ → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (C : ℕ) (old fresh : List Terminal) (junk out : List Γ) (x : SConfig Q Γ t)
    (T : Fin ((1 + t) + 1) → STape Γ)
    (hwork : (fun j => T (ArrivalLog.addr j)) =
      (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (old.map enc) junk) x).tape)
    (hlog : T ArrivalLog.logAddr = ⟨out, M.blank, []⟩)
    (budget : old.length * B ≤ fresh.length * C) :
    let y := fresh.foldl (machine M hB enc decode C).sRound ⟨((x.state, ⟨0, hB⟩), 0), T⟩
    y.state.2 = 0 ∧
    ArrivalLog.view y = TapeReplay.pack ⟨0, hB⟩
      (TapeReplay.source M.blank [] ((old.map enc).reverse ++ junk))
      (old.foldl M.sRound x) ∧
    y.tape ArrivalLog.logAddr = ⟨(fresh.map enc).reverse ++ out, M.blank, []⟩ := by
  have hh := ArrivalLog.rounds (TapeReplay.machine M hB decode) enc C fresh
    (x.state, ⟨0, hB⟩) T out hlog
  refine ⟨hh.1, hh.2.1.trans ?_, hh.2.2⟩
  change TapeReplay.run M hB decode (fresh.length * C)
    ⟨(x.state, ⟨0, hB⟩), fun j => T (ArrivalLog.addr j)⟩ = _
  rw [hwork]
  exact TapeReplay.encoded_word M hB enc decode hdec henc old junk x _ budget

/-- Replaying a batch from a configuration reached by earlier inputs
extends that very execution, with no reset of the matcher or its queues. -/
theorem replayed_after (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (enc : Terminal → Γ) (decode : Γ → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (C : ℕ) (past old fresh : List Terminal) (junk out : List Γ) (x : SConfig Q Γ t)
    (T : Fin ((1 + t) + 1) → STape Γ)
    (hwork : (fun j => T (ArrivalLog.addr j)) =
      (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (old.map enc) junk)
        (past.foldl M.sRound x)).tape)
    (hlog : T ArrivalLog.logAddr = ⟨out, M.blank, []⟩)
    (budget : old.length * B ≤ fresh.length * C) :
    let y := fresh.foldl (machine M hB enc decode C).sRound
      ⟨(((past.foldl M.sRound x).state, ⟨0, hB⟩), 0), T⟩
    y.state.2 = 0 ∧
    ArrivalLog.view y = TapeReplay.pack ⟨0, hB⟩
      (TapeReplay.source M.blank [] ((old.map enc).reverse ++ junk))
      ((past ++ old).foldl M.sRound x) ∧
    y.tape ArrivalLog.logAddr = ⟨(fresh.map enc).reverse ++ out, M.blank, []⟩ := by
  simpa only [List.foldl_append] using
    replayed M hB enc decode hdec henc C old fresh junk out
      (past.foldl M.sRound x) T hwork hlog budget

theorem replayed_padded (M : StructuredMachine Terminal Q Γ t B) (hB : 0 < B)
    (enc : Terminal → Γ) (decode : Γ → Terminal)
    (hdec : ∀ a, decode (enc a) = a) (henc : ∀ a, enc a ≠ M.blank)
    (C : ℕ) (old fresh : List Terminal) (junk out : List Γ) (x : SConfig Q Γ t)
    (T U : Fin ((1 + t) + 1) → STape Γ)
    (hwork : (fun j => U (ArrivalLog.addr j)) =
      (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank (old.map enc) junk) x).tape)
    (hlog : U ArrivalLog.logAddr = ⟨out, M.blank, []⟩)
    (hpad : ∀ j, STape.BlankEq M.blank (T j) (U j))
    (budget : old.length * B ≤ fresh.length * C) :
    let y := fresh.foldl (machine M hB enc decode C).sRound ⟨((x.state, ⟨0, hB⟩), 0), T⟩
    y.state.2 = 0 ∧
    ConfigBlankEq M.blank (ArrivalLog.view y)
      (TapeReplay.pack ⟨0, hB⟩ (TapeReplay.source M.blank [] ((old.map enc).reverse ++ junk))
        (old.foldl M.sRound x)) ∧
    STape.BlankEq M.blank (y.tape ArrivalLog.logAddr)
      ⟨(fresh.map enc).reverse ++ out, M.blank, []⟩ := by
  have hc := replayed M hB enc decode hdec henc C old fresh junk out x U hwork hlog budget
  have hr := (machine M hB enc decode C).runFrom_blankEq fresh
    (show ConfigBlankEq (machine M hB enc decode C).blank
      ⟨((x.state, ⟨0, hB⟩), 0), T⟩ ⟨((x.state, ⟨0, hB⟩), 0), U⟩ from ⟨rfl, hpad⟩)
  refine ⟨(congrArg Prod.snd hr.1).trans hc.1, ?_, ?_⟩
  · have hv : ConfigBlankEq M.blank
        (ArrivalLog.view (fresh.foldl (machine M hB enc decode C).sRound
          ⟨((x.state, ⟨0, hB⟩), 0), T⟩))
        (ArrivalLog.view (fresh.foldl (machine M hB enc decode C).sRound
          ⟨((x.state, ⟨0, hB⟩), 0), U⟩)) :=
      ⟨congrArg Prod.fst hr.1, fun j => hr.2 (ArrivalLog.addr j)⟩
    rw [hc.2.1] at hv
    exact hv
  · exact (hr.2 ArrivalLog.logAddr).trans (hc.2.2 ▸ STape.BlankEq.refl _ _)

/-- info: 'PalPeg.Program.ReplayArrival.replayed_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replayed_padded

/-- info: 'PalPeg.Program.ReplayArrival.replayed_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replayed_after

end PalPeg.Program.ReplayArrival
