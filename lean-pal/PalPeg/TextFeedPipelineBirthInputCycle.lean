import PalPeg.TextFeedPipelineBirthCycle
import PalPeg.ProgramArrivalLog

set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBirthInputCycle
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.TextFeedControl PalPeg.TextFeedInit
variable {k : ℕ} {Terminal : Type}

/-- 41 tapes: borrowed history, 39 seed tapes, and the real arrival log.
Every actual arrival is captured once, followed by C worker ticks. -/
noncomputable def machine (e : Env k) (leftSym : Fin k)
    (enc : Terminal → Fin k) (C : ℕ) :=
  ArrivalLog.machine (TextFeedPipelineBirthCycle.machine e leftSym) enc C

theorem prepared (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (C : ℕ) (pat : List (Fin k)) (hp : e.blank ∉ pat)
    (input : List Terminal) (out : List (Fin k)) (T : Fin 41 → STape (Fin k))
    (hwork : (fun j => T (ArrivalLog.addr j)) =
      (TextFeedPipelineBirthSource.pack 0
        (HistoryConcat.source e.blank pat [e.blank]) (blankBundle e.blank 39)).tape)
    (hlog : T ArrivalLog.logAddr = ⟨out, e.blank, []⟩)
    (budget : 2 * pat.length + 5 ≤ input.length * C) :
    let y := input.foldl (machine e leftSym enc C).sRound ⟨(.inl 0, 0), T⟩
    y.state.2 = 0 ∧
    ArrivalLog.view y = TextFeedPipelineBirthCycle.restoring
      (TextFeedPipelineBirthSource.pack 2
        (HistoryConcat.source e.blank (pat ++ [e.blank]) [e.blank])
        (TextFeedPipelineOutputBirth.seed e leftSym pat pat.length 0)) ∧
    y.tape ArrivalLog.logAddr = ⟨(input.map enc).reverse ++ out, e.blank, []⟩ := by
  have hh := ArrivalLog.rounds (TextFeedPipelineBirthCycle.machine e leftSym)
    enc C input (.inl 0) T out hlog
  refine ⟨hh.1, hh.2.1.trans ?_, hh.2.2⟩
  change TextFeedPipelineBirthCycle.run e leftSym (input.length * C)
    ⟨.inl 0, fun j => T (ArrivalLog.addr j)⟩ = _
  rw [hwork]
  exact TextFeedPipelineBirthCycle.ready_at e leftSym pat hp _ budget

/-- Physically recycled tapes may have extra right-hand blanks. They need
not be normalized before using the real-input copy/restore machine. -/
theorem prepared_padded (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (C : ℕ) (pat : List (Fin k)) (hp : e.blank ∉ pat)
    (input : List Terminal) (out : List (Fin k))
    (T U : Fin 41 → STape (Fin k))
    (hwork : (fun j => U (ArrivalLog.addr j)) =
      (TextFeedPipelineBirthSource.pack 0
        (HistoryConcat.source e.blank pat [e.blank]) (blankBundle e.blank 39)).tape)
    (hlog : U ArrivalLog.logAddr = ⟨out, e.blank, []⟩)
    (hpad : ∀ j, STape.BlankEq e.blank (T j) (U j))
    (budget : 2 * pat.length + 5 ≤ input.length * C) :
    let y := input.foldl (machine e leftSym enc C).sRound ⟨(.inl 0, 0), T⟩
    y.state = (.inr 2, 0) ∧
    ConfigBlankEq e.blank (ArrivalLog.view y)
      (TextFeedPipelineBirthCycle.restoring
        (TextFeedPipelineBirthSource.pack 2
          (HistoryConcat.source e.blank (pat ++ [e.blank]) [e.blank])
          (TextFeedPipelineOutputBirth.seed e leftSym pat pat.length 0))) ∧
    STape.BlankEq e.blank (y.tape ArrivalLog.logAddr)
      ⟨(input.map enc).reverse ++ out, e.blank, []⟩ := by
  have hc := prepared e leftSym enc C pat hp input out U hwork hlog budget
  have hr := (machine e leftSym enc C).runFrom_blankEq input
    (show ConfigBlankEq (machine e leftSym enc C).blank
      ⟨(.inl 0, 0), T⟩ ⟨(.inl 0, 0), U⟩ from ⟨rfl, hpad⟩)
  have hs := congrArg SConfig.state hc.2.1
  refine ⟨hr.1.trans (Prod.ext hs hc.1), ?_, ?_⟩
  · have hv : ConfigBlankEq e.blank
        (ArrivalLog.view (input.foldl (machine e leftSym enc C).sRound ⟨(.inl 0, 0), T⟩))
        (ArrivalLog.view (input.foldl (machine e leftSym enc C).sRound ⟨(.inl 0, 0), U⟩)) :=
      ⟨congrArg Prod.fst hr.1, fun j => hr.2 (ArrivalLog.addr j)⟩
    rw [hc.2.1] at hv
    exact hv
  · exact (hr.2 ArrivalLog.logAddr).trans (hc.2.2 ▸ STape.BlankEq.refl _ _)

/-- A local copy/restore pass fits in one eighth of an already available
history's length at 32 worker ticks per arrival. This does not include
the time spent constructing that history. -/
theorem eighth_budget (L n : ℕ) (hL : 32 ≤ L) (hn : L / 8 ≤ n) :
    2 * L + 5 ≤ n * 32 := by omega

theorem prepared_by_eighth (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k)
    (pat : List (Fin k)) (hp : e.blank ∉ pat) (hlen : 32 ≤ pat.length)
    (input : List Terminal) (out : List (Fin k)) (T : Fin 41 → STape (Fin k))
    (hwork : (fun j => T (ArrivalLog.addr j)) =
      (TextFeedPipelineBirthSource.pack 0
        (HistoryConcat.source e.blank pat [e.blank]) (blankBundle e.blank 39)).tape)
    (hlog : T ArrivalLog.logAddr = ⟨out, e.blank, []⟩)
    (elapsed : pat.length / 8 ≤ input.length) :
    let y := input.foldl (machine e leftSym enc 32).sRound ⟨(.inl 0, 0), T⟩
    y.state.2 = 0 ∧
    ArrivalLog.view y = TextFeedPipelineBirthCycle.restoring
      (TextFeedPipelineBirthSource.pack 2
        (HistoryConcat.source e.blank (pat ++ [e.blank]) [e.blank])
        (TextFeedPipelineOutputBirth.seed e leftSym pat pat.length 0)) ∧
    y.tape ArrivalLog.logAddr = ⟨(input.map enc).reverse ++ out, e.blank, []⟩ :=
  prepared e leftSym enc 32 pat hp input out T hwork hlog
    (eighth_budget _ _ hlen elapsed)

/-- info: 'PalPeg.TextFeedPipelineBirthInputCycle.prepared_by_eighth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_by_eighth

/-- info: 'PalPeg.TextFeedPipelineBirthInputCycle.prepared_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_padded

end PalPeg.TextFeedPipelineBirthInputCycle
