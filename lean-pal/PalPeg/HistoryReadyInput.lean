import PalPeg.HistoryReady
import PalPeg.ProgramArrivalLog

set_option autoImplicit false
namespace PalPeg.HistoryReadyInput
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

/-- Four tapes, finite control and a fixed C+1 microsteps per real input.
The accepting flag denotes history readiness, not PAL membership. -/
def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) :=
  ArrivalLog.machine (HistoryReady.machine blank) enc C

theorem prepared (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (log : List (Fin k)) (T : Fin 4 → STape (Fin k))
    (h0 : T 0 = HistoryConcat.source blank u [blank])
    (h1 : T 1 = HistoryConcat.source blank v [blank])
    (h2 : T 2 = ⟨[blank], blank, []⟩) (h3 : T 3 = ⟨log, blank, []⟩)
    (budget : 2 * (u.length + v.length) + 5 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C).sRound ⟨(.inl 0, 0), T⟩
    y.state = (.inr (fun _ => 2), 0) ∧ STape.BlankEq blank (y.tape 2)
      (HistoryConcat.source blank (u ++ v) [blank]) ∧
      y.tape 3 = ⟨(w.map enc).reverse ++ log, blank, []⟩ ∧
      STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ := by
  have hh := ArrivalLog.rounds (HistoryReady.machine blank) enc C w (.inl 0) T log h3
  let A : Fin 3 → STape (Fin k) := fun j => T (ArrivalLog.addr j)
  have hc := HistoryReady.ready blank u v hu hv A h0 h1 h2
  let D := 2 * (u.length + v.length) + 5
  let z := HistoryReady.run blank D (HistoryReady.copy ⟨0, A⟩)
  have hz : z.state = .inr (fun _ => 2) := hc.1
  have he : z = ⟨.inr (fun _ => 2), z.tape⟩ := by rw [← hz]
  have hr : HistoryReady.run blank (w.length * C) (HistoryReady.copy ⟨0, A⟩) = z := by
    rw [show w.length * C = D + (w.length * C - D) by dsimp only [D]; omega,
      HistoryReady.run_add]
    change HistoryReady.run blank (w.length * C - D) z = z
    rw [he, HistoryReady.done_run]
  let y := w.foldl (machine blank enc C).sRound ⟨(.inl 0, 0), T⟩
  have hp : ArrivalLog.view y = z := hh.2.1.trans hr
  have hs : y.state.1 = z.state := congrArg SConfig.state hp
  have ht : y.tape 2 = z.tape 2 := congrArg (fun x => x.tape 2) hp
  have hA : y.tape 0 = z.tape 0 := congrArg (fun x => x.tape 0) hp
  have hB : y.tape 1 = z.tape 1 := congrArg (fun x => x.tape 1) hp
  refine ⟨Prod.ext (hs.trans hz) hh.1, ?_, hh.2.2, ?_, ?_⟩
  · change STape.BlankEq blank (y.tape 2) _
    rw [ht]
    exact hc.2.1
  · change STape.BlankEq blank (y.tape 0) _
    rw [hA]
    exact hc.2.2.1
  · change STape.BlankEq blank (y.tape 1) _
    rw [hB]
    exact hc.2.2.2

/-- The reusable-buffer contract allows physical blank padding left by
previous recovery runs. No normalization of real tapes is assumed. -/
theorem prepared_padded (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (w : List Terminal) (u v : List (Fin k)) (hu : blank ∉ u) (hv : blank ∉ v)
    (log : List (Fin k)) (T : Fin 4 → STape (Fin k))
    (h0 : STape.BlankEq blank (T 0) (HistoryConcat.source blank u [blank]))
    (h1 : STape.BlankEq blank (T 1) (HistoryConcat.source blank v [blank]))
    (h2 : STape.BlankEq blank (T 2) ⟨[blank], blank, []⟩)
    (h3 : STape.BlankEq blank (T 3) ⟨log, blank, []⟩)
    (budget : 2 * (u.length + v.length) + 5 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C).sRound ⟨(.inl 0, 0), T⟩
    y.state = (.inr (fun _ => 2), 0) ∧
      STape.BlankEq blank (y.tape 2) (HistoryConcat.source blank (u ++ v) [blank]) ∧
      STape.BlankEq blank (y.tape 3) ⟨(w.map enc).reverse ++ log, blank, []⟩ ∧
      STape.BlankEq blank (y.tape 0) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape 1) ⟨[blank], blank, []⟩ := by
  let A : Fin 4 → STape (Fin k) := Fin.cases (HistoryConcat.source blank u [blank])
    (Fin.cases (HistoryConcat.source blank v [blank])
      (Fin.cases ⟨[blank], blank, []⟩ (fun _ => ⟨log, blank, []⟩)))
  have ha : ∀ i, STape.BlankEq blank (T i) (A i) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hc := prepared blank enc C w u v hu hv log A rfl rfl rfl rfl budget
  have hr := (machine blank enc C).runFrom_blankEq w
    (show ConfigBlankEq (machine blank enc C).blank
      ⟨(.inl 0, 0), T⟩ ⟨(.inl 0, 0), A⟩ from ⟨rfl, ha⟩)
  refine ⟨hr.1.trans hc.1, (hr.2 2).trans hc.2.1, ?_,
    (hr.2 0).trans hc.2.2.2.1, (hr.2 1).trans hc.2.2.2.2⟩
  apply (hr.2 3).trans
  rw [hc.2.2.1]
  exact STape.BlankEq.refl _ _

/-- info: 'PalPeg.HistoryReadyInput.prepared_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_padded

/-- info: 'PalPeg.HistoryReadyInput.prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared

end PalPeg.HistoryReadyInput
