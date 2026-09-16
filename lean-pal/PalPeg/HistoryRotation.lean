import PalPeg.HistoryFreeze
import PalPeg.HistoryNextInput
import PalPeg.ProgramTapeRename

set_option autoImplicit false
namespace PalPeg.HistoryRotation
open PegSeparation.RealTimeTM PalPeg.Program
variable {k : ℕ} {Terminal : Type}

/-- After a completed merge, physical tapes 2 and 3 hold the old prefix
and arrival log. Tape 1 becomes the next destination; tape 0 the new log. -/
def roles : Fin 4 ≃ Fin 4 where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem roles_four (i : Fin 4) : roles (roles (roles (roles i))) = i := by
  fin_cases i <;> rfl

/-- e is the current logical-to-physical assignment. The new wiring uses
the same four physical tapes, and the same fixed microstep budget. -/
def machine (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) (e : Fin 4 ≃ Fin 4) :=
  TapeRename.machine (HistoryFreeze.machine blank enc C) (roles.trans e)

theorem frozen (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (w : List Terminal) (u v : List (Fin k)) (hv : blank ∉ v)
    (T : Fin 4 → STape (Fin k))
    (h0 : STape.BlankEq blank (T (e 0)) ⟨[blank], blank, []⟩)
    (h1 : STape.BlankEq blank (T (e 1)) ⟨[blank], blank, []⟩)
    (h2 : STape.BlankEq blank (T (e 2)) (HistoryConcat.source blank u [blank]))
    (h3 : STape.BlankEq blank (T (e 3)) ⟨v.reverse ++ [blank], blank, []⟩)
    (budget : v.length + 2 ≤ w.length * C) :
    let y := w.foldl (machine blank enc C e).sRound ⟨(0, 0), T⟩
    y.state = (2, 0) ∧
      STape.BlankEq blank (y.tape (e 2)) (HistoryConcat.source blank u [blank]) ∧
      STape.BlankEq blank (y.tape (e 3)) (HistoryConcat.source blank v [blank]) ∧
      STape.BlankEq blank (y.tape (e 1)) ⟨[blank], blank, []⟩ ∧
      STape.BlankEq blank (y.tape (e 0)) ⟨(w.map enc).reverse ++ [blank], blank, []⟩ := by
  let A : Fin 4 → STape (Fin k) := fun j => T ((roles.trans e) j)
  have hh := HistoryFreeze.frozen_padded blank enc C w u v hv A h2 h3 h1 h0 budget
  have hr := TapeRename.run_view (HistoryFreeze.machine blank enc C) (roles.trans e)
    w ⟨(0, 0), T⟩
  change _ = w.foldl (HistoryFreeze.machine blank enc C).sRound ⟨(0, 0), A⟩ at hr
  rw [← hr] at hh
  exact hh

/-- The repeatable data invariant: two reusable buffers, one readable old
prefix, and the arrival suffix accumulated since the last snapshot. -/
def Layout (blank : Fin k) (e : Fin 4 ≃ Fin 4) (u v : List (Fin k))
    (T : Fin 4 → STape (Fin k)) : Prop :=
  STape.BlankEq blank (T (e 0)) ⟨[blank], blank, []⟩ ∧
  STape.BlankEq blank (T (e 1)) ⟨[blank], blank, []⟩ ∧
  STape.BlankEq blank (T (e 2)) (HistoryConcat.source blank u [blank]) ∧
  STape.BlankEq blank (T (e 3)) ⟨v.reverse ++ [blank], blank, []⟩

/-- One autonomous pass in the new tape roles, including new arrivals
through every phase and both internally detected handoffs. -/
def cycle (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ) (e : Fin 4 ≃ Fin 4) :=
  TapeRename.machine (HistoryNextInput.machine blank enc C) (roles.trans e)

theorem cycled (blank : Fin k) (enc : Terminal → Fin k) (C : ℕ)
    (e : Fin 4 ≃ Fin 4) (w : List Terminal) (u v : List (Fin k))
    (hu : blank ∉ u) (hv : blank ∉ v) (T : Fin 4 → STape (Fin k))
    (h : Layout blank e u v T)
    (budget : 2 * (u.length + v.length) + v.length + 8 ≤ w.length * C) :
    let y := w.foldl (cycle blank enc C e).sRound ⟨(.inl 0, 0), T⟩
    y.state = (.inr (.inr (fun _ => 2)), 0) ∧
      Layout blank (roles.trans e) (u ++ v) (w.map enc) y.tape := by
  let A : Fin 4 → STape (Fin k) := fun j => T ((roles.trans e) j)
  have hh := HistoryNextInput.prepared_padded blank enc C w u v hu hv [blank] A
    h.2.2.1 h.2.2.2 h.2.1 h.1 budget
  have hr := TapeRename.run_view (HistoryNextInput.machine blank enc C) (roles.trans e)
    w ⟨(.inl 0, 0), T⟩
  change _ = w.foldl (HistoryNextInput.machine blank enc C).sRound ⟨(.inl 0, 0), A⟩ at hr
  rw [← hr] at hh
  exact ⟨hh.1, hh.2.2.2.1, hh.2.2.2.2, hh.2.1, hh.2.2.1⟩

/-- info: 'PalPeg.HistoryRotation.cycled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cycled

/-- info: 'PalPeg.HistoryRotation.frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frozen

end PalPeg.HistoryRotation
