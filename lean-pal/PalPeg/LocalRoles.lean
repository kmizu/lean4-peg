import PalPeg.LocalCounter

/-!
# K-local refinement, piece 2: role assignment for counter *moves*

`PalPeg.LocalCounter` realizes a single logical counter on one physical
segmented tape, with `push`/`pop`/`resetSeg` all costing one tape action.
That is not yet enough for the Galil scaffold, because the scaffold performs
whole-counter *moves* whose source dies in the same step:

```
work      := span    ; span   := reset     -- GalilScaffoldSearchFinish.finish
replay    := radius  ; radius := reset     -- replayStartVM
lower     := last                          -- restartVM
remaining := ofNat h                       -- beginShiftVM
```

Copying a unary counter cell by cell is linear, so a literal copy is not
`K`-local.  The fix is *indirection*: the finite control does not hardwire
"logical counter `ℓ` lives on physical tape number `i`".  It carries a **role
assignment** `roles : L → Fin P` (injective: distinct logical counters live on
distinct tapes) together with a **polarity** `pol : L → Bool`, and a move is
performed by permuting the assignment instead of moving any tape content:

* `dst` starts pointing at the physical tape that `src` used to own — so `dst`
  inherits `src`'s value *for free*;
* `src` starts pointing at the physical tape that `dst` used to own, and that
  one tape gets a single `resetSeg`.

Since `L` is finite and `roles`/`pol` live in the finite control, the
permutation is a finite-control update, and the only tape work is the one
`resetSeg`.  That is `O(1)`: exactly one physical tape is written
(`moveTapes_apply_of_ne`, `moveTapes_writes_one`).

`swapMove` below is the version without the reset, used when both logical
counters survive (a pure exchange of roles).
-/

set_option autoImplicit false

namespace PalPeg.LocalRoles

open PalPeg.Program
open PalPeg.GalilScaffoldCounter
open PalPeg.LocalCounter

universe u

variable {L : Type u} [Fintype L] [DecidableEq L] {P : ℕ}

/-! ## The abstraction map -/

/-- The abstraction map of a whole *bank*: physical tapes `phys`, a role
assignment `roles`, and the control-held polarities `pol` together determine the
value of every logical counter. -/
def absL (phys : Fin P → STape Seg) (roles : L → Fin P) (pol : L → Bool) :
    L → Counter :=
  fun ℓ => absCtr (phys (roles ℓ)) (pol ℓ)

@[simp] theorem absL_apply (phys : Fin P → STape Seg) (roles : L → Fin P)
    (pol : L → Bool) (ℓ : L) :
    absL phys roles pol ℓ = absCtr (phys (roles ℓ)) (pol ℓ) := rfl

theorem absL_canonical (phys : Fin P → STape Seg) (roles : L → Fin P)
    (pol : L → Bool) (ℓ : L) : Canonical (absL phys roles pol ℓ) :=
  absCtr_canonical _ _

/-! ## The transposition on logical names -/

/-- The transposition of `src` and `dst`, as a self-contained function (no
`Equiv` needed). -/
def swapAt (src dst : L) : L → L :=
  fun ℓ => if ℓ = dst then src else if ℓ = src then dst else ℓ

@[simp] theorem swapAt_dst (src dst : L) : swapAt src dst dst = src := by
  simp [swapAt]

@[simp] theorem swapAt_src {src dst : L} (h : src ≠ dst) :
    swapAt src dst src = dst := by
  simp [swapAt, h]

theorem swapAt_other {src dst ℓ : L} (h1 : ℓ ≠ dst) (h2 : ℓ ≠ src) :
    swapAt src dst ℓ = ℓ := by
  simp [swapAt, h1, h2]

@[simp] theorem swapAt_involutive (src dst ℓ : L) :
    swapAt src dst (swapAt src dst ℓ) = ℓ := by
  unfold swapAt
  by_cases h1 : ℓ = dst
  · subst h1; by_cases h2 : ℓ = src <;> simp [h2]
  · by_cases h2 : ℓ = src
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapAt_injective (src dst : L) : Function.Injective (swapAt src dst) :=
  Function.involutive_iff_iter_2_eq_id.mpr (by
    funext ℓ; simpa using swapAt_involutive src dst ℓ) |>.injective

/-! ## The move -/

/-- The role assignment after `dst := src ; src := reset`: the two names swap
physical tapes. -/
def moveRoles (src dst : L) (roles : L → Fin P) : L → Fin P :=
  fun ℓ => roles (swapAt src dst ℓ)

/-- The polarity bits travel with the names. -/
def movePol (src dst : L) (pol : L → Bool) : L → Bool :=
  fun ℓ => pol (swapAt src dst ℓ)

/-- The only tape work of a move: a single `resetSeg` on physical tape `r`
(which is the tape `src` owns *after* the permutation). -/
def moveTapes (r : Fin P) (phys : Fin P → STape Seg) : Fin P → STape Seg :=
  fun j => if j = r then resetSeg (phys r) else phys j

@[simp] theorem moveTapes_apply_self (r : Fin P) (phys : Fin P → STape Seg) :
    moveTapes r phys r = resetSeg (phys r) := by simp [moveTapes]

theorem moveTapes_apply_of_ne {r j : Fin P} (phys : Fin P → STape Seg)
    (h : j ≠ r) : moveTapes r phys j = phys j := by simp [moveTapes, h]

/-- `O(1)`: every physical tape except `r` is untouched, so a move writes
exactly one tape. -/
theorem moveTapes_writes_one (r : Fin P) (phys : Fin P → STape Seg) :
    ∀ j : Fin P, j ≠ r → moveTapes r phys j = phys j :=
  fun _ h => moveTapes_apply_of_ne phys h

/-- The tape newly owned by `src` satisfies the segment invariant at value `0`. -/
theorem segCtr_moveTapes_self (r : Fin P) (phys : Fin P → STape Seg) :
    SegCtr (moveTapes r phys r) 0 := by
  simpa using segCtr_reset (phys r)

/-- Injectivity of the role assignment is preserved by a move. -/
theorem moveRoles_injective {src dst : L} {roles : L → Fin P}
    (h : Function.Injective roles) :
    Function.Injective (moveRoles src dst roles) :=
  h.comp (swapAt_injective src dst)

/-- **Main lemma.**  Permuting the roles of `src` and `dst` and resetting the
single tape that `src` now owns realizes the simultaneous assignment
`dst := src ; src := reset` on the abstract counters, leaving every other
logical counter untouched. -/
theorem absL_move {src dst : L} {roles : L → Fin P} {pol : L → Bool}
    {phys : Fin P → STape Seg} (hne : src ≠ dst) (hinj : Function.Injective roles) :
    absL (moveTapes (roles dst) phys) (moveRoles src dst roles)
        (movePol src dst pol)
      = fun ℓ =>
          if ℓ = dst then absL phys roles pol src
          else if ℓ = src then reset
          else absL phys roles pol ℓ := by
  funext ℓ
  by_cases h1 : ℓ = dst
  · subst h1
    have hsd : roles src ≠ roles ℓ := fun h => hne (hinj h)
    simp [absL, moveRoles, movePol, moveTapes_apply_of_ne phys hsd]
  · by_cases h2 : ℓ = src
    · subst h2
      simp [absL, moveRoles, movePol, swapAt_src hne, absCtr_reset, h1]
    · have hd : roles ℓ ≠ roles dst := fun h => h1 (hinj h)
      simp [absL, moveRoles, movePol, swapAt_other h1 h2,
        moveTapes_apply_of_ne phys hd, h1, h2]

/-- Pointwise form of `absL_move`. -/
theorem absL_move_apply {src dst : L} {roles : L → Fin P} {pol : L → Bool}
    {phys : Fin P → STape Seg} (hne : src ≠ dst) (hinj : Function.Injective roles)
    (ℓ : L) :
    absL (moveTapes (roles dst) phys) (moveRoles src dst roles)
        (movePol src dst pol) ℓ
      = if ℓ = dst then absL phys roles pol src
        else if ℓ = src then reset
        else absL phys roles pol ℓ := by
  rw [absL_move hne hinj]

/-! ## The pure swap -/

/-- A role exchange with no reset: both logical counters survive. -/
def swapMove (src dst : L) (roles : L → Fin P) (pol : L → Bool) :
    (L → Fin P) × (L → Bool) :=
  (moveRoles src dst roles, movePol src dst pol)

/-- A pure swap writes no tape at all and simply renames the counters. -/
theorem absL_swap (src dst : L) (roles : L → Fin P) (pol : L → Bool)
    (phys : Fin P → STape Seg) :
    absL phys (moveRoles src dst roles) (movePol src dst pol)
      = fun ℓ => absL phys roles pol (swapAt src dst ℓ) := by
  funext ℓ; rfl

theorem absL_swap_apply (src dst : L) (roles : L → Fin P) (pol : L → Bool)
    (phys : Fin P → STape Seg) (ℓ : L) :
    absL phys (moveRoles src dst roles) (movePol src dst pol) ℓ
      = absL phys roles pol (swapAt src dst ℓ) := rfl

theorem absL_swap_dst (src dst : L) (roles : L → Fin P) (pol : L → Bool)
    (phys : Fin P → STape Seg) :
    absL phys (moveRoles src dst roles) (movePol src dst pol) dst
      = absL phys roles pol src := by
  simp [absL, moveRoles, movePol]

theorem absL_swap_src {src dst : L} (h : src ≠ dst) (roles : L → Fin P)
    (pol : L → Bool) (phys : Fin P → STape Seg) :
    absL phys (moveRoles src dst roles) (movePol src dst pol) src
      = absL phys roles pol dst := by
  simp [absL, moveRoles, movePol, swapAt_src h]

theorem absL_swap_other {src dst ℓ : L} (h1 : ℓ ≠ dst) (h2 : ℓ ≠ src)
    (roles : L → Fin P) (pol : L → Bool) (phys : Fin P → STape Seg) :
    absL phys (moveRoles src dst roles) (movePol src dst pol) ℓ
      = absL phys roles pol ℓ := by
  simp [absL, moveRoles, movePol, swapAt_other h1 h2]

#print axioms absL_move
#print axioms absL_move_apply
#print axioms absL_swap
#print axioms moveRoles_injective
#print axioms moveTapes_writes_one
#print axioms segCtr_moveTapes_self
#print axioms swapAt_injective
#print axioms absL_canonical

end PalPeg.LocalRoles
