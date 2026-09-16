import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.Basic

/-!
# Controller modes of the Scala online Galil scaffold

`ScaffoldGalil.scala` keeps a finite controller record beside the VM: the
mode, a countdown clock (always reset to `timing.matchDelay`), and four Boolean
flags. This module transcribes that record, its mode graph (`stepInit` …
`stepReplayStart`), and packages the clock-bounded record as a `Fintype`, so it
can be part of the finite control of a `StructuredMachine`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldController

/-- `ScaffoldGalil.Mode`, in source order. -/
inductive Mode
  | init | scan | shift | copy | home | fpp | markEnd | choose | rewind | replayStart
  deriving DecidableEq, Repr

def Mode.toFin : Mode → Fin 10
  | .init => 0 | .scan => 1 | .shift => 2 | .copy => 3 | .home => 4
  | .fpp => 5 | .markEnd => 6 | .choose => 7 | .rewind => 8 | .replayStart => 9

def Mode.ofFin : Fin 10 → Mode
  | 0 => .init | 1 => .scan | 2 => .shift | 3 => .copy | 4 => .home
  | 5 => .fpp | 6 => .markEnd | 7 => .choose | 8 => .rewind | 9 => .replayStart

theorem Mode.ofFin_toFin : ∀ m : Mode, Mode.ofFin (Mode.toFin m) = m := by
  intro m; cases m <;> rfl

theorem Mode.toFin_ofFin : ∀ k : Fin 10, Mode.toFin (Mode.ofFin k) = k := by
  decide

def Mode.equivFin : Mode ≃ Fin 10 where
  toFun := Mode.toFin
  invFun := Mode.ofFin
  left_inv := Mode.ofFin_toFin
  right_inv := Mode.toFin_ofFin

instance : Fintype Mode := Fintype.ofEquiv _ Mode.equivFin.symm

/-- The Scala `mode = Mode.X` assignments, one edge per assignment site. -/
inductive ModeStep : Mode → Mode → Prop
  | init_scan : ModeStep .init .scan
  | scan_shift : ModeStep .scan .shift
  | scan_copy : ModeStep .scan .copy
  | shift_scan : ModeStep .shift .scan
  | copy_home : ModeStep .copy .home
  | home_fpp : ModeStep .home .fpp
  | fpp_markEnd : ModeStep .fpp .markEnd
  | markEnd_choose : ModeStep .markEnd .choose
  | choose_rewind : ModeStep .choose .rewind
  | rewind_replayStart : ModeStep .rewind .replayStart
  | replayStart_scan : ModeStep .replayStart .scan

/-- Reflexive-transitive closure of the mode graph. -/
inductive Reaches : Mode → Mode → Prop
  | refl (m : Mode) : Reaches m m
  | step {a b c : Mode} (h : ModeStep a b) (hr : Reaches b c) : Reaches a c

theorem reaches_trans {a b c : Mode} (h1 : Reaches a b) (h2 : Reaches b c) : Reaches a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

/-- Every mode returns to `scan`: the fallback cycle
`copy → home → fpp → markEnd → choose → rewind → replayStart → scan` and the
short cycle `shift → scan` are the only exits. -/
theorem reaches_scan (m : Mode) : Reaches m .scan := by
  have h9 : Reaches .replayStart .scan := .step .replayStart_scan (.refl _)
  have h8 : Reaches .rewind .scan := .step .rewind_replayStart h9
  have h7 : Reaches .choose .scan := .step .choose_rewind h8
  have h6 : Reaches .markEnd .scan := .step .markEnd_choose h7
  have h5 : Reaches .fpp .scan := .step .fpp_markEnd h6
  have h4 : Reaches .home .scan := .step .home_fpp h5
  have h3 : Reaches .copy .scan := .step .copy_home h4
  cases m with
  | init => exact .step .init_scan (.refl _)
  | scan => exact .refl _
  | shift => exact .step .shift_scan (.refl _)
  | copy => exact h3
  | home => exact h4
  | fpp => exact h5
  | markEnd => exact h6
  | choose => exact h7
  | rewind => exact h8
  | replayStart => exact h9

/-- `init` is never re-entered. -/
theorem no_step_to_init (m : Mode) : ¬ ModeStep m .init := by
  intro h; cases h

/-- The controller record `Control` of `ScaffoldGalil.scala`
(`mode`, `clock`, `output`, `replaying`, `odd`, `pair`). -/
structure Control where
  mode : Mode
  clock : ℕ
  output : Bool
  replaying : Bool
  odd : Bool
  pair : Bool
  deriving DecidableEq

/-- `Control.initial(timing)`: mode `init`, clock at the match delay, all flags off. -/
def initial (delay : ℕ) : Control := ⟨.init, delay, false, false, false, false⟩

/-- The clock never exceeds the match delay it is reset to. -/
def Bounded (delay : ℕ) (c : Control) : Prop := c.clock ≤ delay

instance (delay : ℕ) (c : Control) : Decidable (Bounded delay c) := by
  unfold Bounded; infer_instance

/-- Clock-bounded controller records, the finite type used as controller
component of the structured machine's control state. -/
def BoundedControl (delay : ℕ) := { c : Control // Bounded delay c }

instance (delay : ℕ) : DecidableEq (BoundedControl delay) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

def toTuple (delay : ℕ) (c : BoundedControl delay) : Mode × Fin (delay+1) × Bool × Bool × Bool × Bool :=
  ⟨c.val.mode, ⟨c.val.clock, Nat.lt_succ_of_le c.property⟩, c.val.output, c.val.replaying,
    c.val.odd, c.val.pair⟩

def ofTuple (delay : ℕ) (t : Mode × Fin (delay+1) × Bool × Bool × Bool × Bool) : BoundedControl delay :=
  ⟨⟨t.1, t.2.1.val, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩, Nat.le_of_lt_succ t.2.1.isLt⟩

theorem ofTuple_toTuple (delay : ℕ) (c : BoundedControl delay) : ofTuple delay (toTuple delay c) = c := by
  apply Subtype.ext
  rfl

theorem toTuple_ofTuple (delay : ℕ) (t : Mode × Fin (delay+1) × Bool × Bool × Bool × Bool) :
    toTuple delay (ofTuple delay t) = t := by
  obtain ⟨m, ⟨k, hk⟩, o, r, d, p⟩ := t
  rfl

def equivTuple (delay : ℕ) : BoundedControl delay ≃ Mode × Fin (delay+1) × Bool × Bool × Bool × Bool where
  toFun := toTuple delay
  invFun := ofTuple delay
  left_inv := ofTuple_toTuple delay
  right_inv := toTuple_ofTuple delay

noncomputable instance (delay : ℕ) : Fintype (BoundedControl delay) :=
  Fintype.ofEquiv _ (equivTuple delay).symm

theorem initial_bounded (delay : ℕ) : Bounded delay (initial delay) := le_refl _

#print axioms reaches_scan
#print axioms ofTuple_toTuple

end PalPeg.GalilScaffoldController
