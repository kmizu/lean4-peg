import PalPeg.HistoryRecover
import PalPeg.ProgramArrivalLog
import PalPeg.ProgramBlankEq

set_option autoImplicit false
namespace PalPeg.ReplayBufferTurn
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

/-- Buffers 0/1 are reclaimed while frozen log 2 is rewound. Incoming
symbols continue to be captured in log 3, disjoint from all three workers. -/
def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) :=
  ArrivalLog.machine (HistoryRecover.machine blank) enc C

theorem prepared (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (old batch : List (Fin k)) (ho : blank ∉ old) (hb : blank ∉ batch)
    (input : List Terminal) (out : List (Fin k)) (T : Fin 4 → STape (Fin k))
    (h0 : T 0 = ⟨old.reverse ++ [blank], blank, []⟩)
    (h1 : T 1 = ⟨[blank], blank, []⟩)
    (h2 : T 2 = ⟨batch.reverse ++ [blank], blank, []⟩)
    (h3 : T 3 = ⟨out, blank, []⟩)
    (budget : max old.length batch.length + 2 ≤ input.length * C) :
    let y := input.foldl (machine blank enc C).sRound ⟨((fun _ => 0), 0), T⟩
    y.state = ((fun _ => 2), 0) ∧
    STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
    STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ ∧
    STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank batch [blank]) ∧
    y.tape 3 = ⟨(input.map enc).reverse ++ out, blank, []⟩ := by
  have hh := ArrivalLog.rounds (HistoryRecover.machine blank) enc C input
    (fun _ => 0) T out h3
  let A : Fin 3 → STape (Fin k) := fun j => T (ArrivalLog.addr j)
  have hA := HistoryRecover.erase_lane blank 0 (by decide) old.reverse (by simpa using ho)
    (input.length * C) (by simp; omega) A h0
  have hB := HistoryRecover.erase_lane blank 1 (by decide) [] (by simp)
    (input.length * C) (by simp; omega) A h1
  have hD := HistoryRecover.rewind_lane blank batch hb (input.length * C) (by omega) A h2
  let z := HistoryRecover.run blank (input.length * C) ⟨fun _ => 0, A⟩
  have hs : z.state = fun _ => 2 := by
    funext i
    fin_cases i
    · exact hA.1
    · exact hB.1
    · exact hD.1
  let y := input.foldl (machine blank enc C).sRound ⟨((fun _ => 0), 0), T⟩
  have hp : ArrivalLog.view y = z := hh.2.1
  have hstate : y.state.1 = z.state := congrArg SConfig.state hp
  have ht (i : Fin 3) : y.tape (ArrivalLog.addr i) = z.tape i :=
    congrArg (fun x => x.tape i) hp
  refine ⟨Prod.ext (hstate.trans hs) hh.1, ?_, ?_, ?_, hh.2.2⟩
  · change STape.BlankEq blank (y.tape (ArrivalLog.addr 0)) _
    rw [ht]
    exact hA.2
  · change STape.BlankEq blank (y.tape (ArrivalLog.addr 1)) _
    rw [ht]
    exact hB.2
  · change STape.BlankEq blank (y.tape (ArrivalLog.addr 2)) _
    rw [ht]
    exact hD.2

theorem prepared_padded (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (old batch : List (Fin k)) (ho : blank ∉ old) (hb : blank ∉ batch)
    (input : List Terminal) (out : List (Fin k)) (T U : Fin 4 → STape (Fin k))
    (h0 : U 0 = ⟨old.reverse ++ [blank], blank, []⟩)
    (h1 : U 1 = ⟨[blank], blank, []⟩)
    (h2 : U 2 = ⟨batch.reverse ++ [blank], blank, []⟩)
    (h3 : U 3 = ⟨out, blank, []⟩)
    (hpad : ∀ i, STape.BlankEq blank (T i) (U i))
    (budget : max old.length batch.length + 2 ≤ input.length * C) :
    let y := input.foldl (machine blank enc C).sRound ⟨((fun _ => 0), 0), T⟩
    y.state = ((fun _ => 2), 0) ∧
    STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
    STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ ∧
    STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank batch [blank]) ∧
    STape.BlankEq blank (y.tape 3) ⟨(input.map enc).reverse ++ out, blank, []⟩ := by
  have hc := prepared blank enc C old batch ho hb input out U h0 h1 h2 h3 budget
  have hr := (machine blank enc C).runFrom_blankEq input
    (show ConfigBlankEq (machine blank enc C).blank
      ⟨((fun _ => 0), 0), T⟩ ⟨((fun _ => 0), 0), U⟩ from ⟨rfl, hpad⟩)
  exact ⟨hr.1.trans hc.1, (hr.2 0).trans hc.2.1, (hr.2 1).trans hc.2.2.1,
    (hr.2 2).trans hc.2.2.2.1, (hr.2 3).trans (hc.2.2.2.2 ▸ STape.BlankEq.refl _ _)⟩

/-- info: 'PalPeg.ReplayBufferTurn.prepared_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_padded

end PalPeg.ReplayBufferTurn
