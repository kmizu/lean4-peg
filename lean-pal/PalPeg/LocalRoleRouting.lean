import PalPeg.MachineStep
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite tape roles for the existing local steps

A role permutation belongs to finite control. Each rule reads windows in
logical order and writes the same physical tapes under the source permutation.
Its output may rotate roles without copying tape contents. The commuting square
below is for `LocalStep.apply`, including the real write sweep.
-/
set_option autoImplicit false

namespace PalPeg.LocalRoleRouting
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12

abbrev Control (Q : Type) (t : ℕ) := Equiv.Perm (Fin t) × Q
abbrev Config (Q Γ : Type) (t : ℕ) := Control Q t × (Fin t → STape Γ)

variable {Terminal Q Γ : Type} {t K : ℕ}

def decode (p : Config Q Γ t) : Q × (Fin t → STape Γ) :=
  (p.1.2, fun j => p.2 (p.1.1 j))

abbrev RoleChange (Terminal Q Γ : Type) (t K : ℕ) :=
  Q → Option Terminal → (Fin t → Window Γ K) → Equiv.Perm (Fin t)

/-- New roles are relative to the source logical order. Tape contents are never
permuted physically; only the finite names change. -/
def route (L : LocalStep Terminal Q Γ t K) (change : RoleChange Terminal Q Γ t K) :
    LocalStep Terminal (Control Q t) Γ t K where
  next := fun q a ws =>
    let logical := fun j => ws (q.1 j)
    let result := L.next q.2 a logical
    (( (change q.2 a logical).trans q.1, result.1),
      fun j => result.2 (q.1.symm j))
  disp_le := fun q a ws j => L.disp_le q.2 a (fun i => ws (q.1 i)) (q.1.symm j)

/-- Physical execution followed by decoding is the old execution followed by
the requested logical role exchange. No tape equality modulo a sweep is assumed. -/
theorem decode_route (L : LocalStep Terminal Q Γ t K)
    (change : RoleChange Terminal Q Γ t K) (blank : Γ) (p : Config Q Γ t)
    (a : Option Terminal) :
    decode ((route L change).apply blank p a) =
      ((L.apply blank (decode p) a).1, fun j =>
        (L.apply blank (decode p) a).2
          (change p.1.2 a (fun i => readWin blank K ((decode p).2 i)) j)) := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [decode, route, LocalStep.apply, Equiv.trans_apply, Equiv.symm_apply_apply]

def hold (L : LocalStep Terminal Q Γ t K) : LocalStep Terminal (Control Q t) Γ t K :=
  route L (fun _ _ _ => Equiv.refl _)

theorem decode_hold (L : LocalStep Terminal Q Γ t K) (blank : Γ)
    (p : Config Q Γ t) (a : Option Terminal) :
    decode ((hold L).apply blank p a) = L.apply blank (decode p) a := by
  rw [hold, decode_route]
  rfl

def routedEnc {X : Type} (Enc : X → Q × (Fin t → STape Γ) → Prop) :
    X → Config Q Γ t → Prop := fun x p => Enc x (decode p)

/-- Already proved transitions transfer for every role assignment, including
assignments created by earlier boundary events. -/
theorem preserve_hold {X : Type} (Enc : X → Q × (Fin t → STape Γ) → Prop)
    (L : LocalStep Terminal Q Γ t K) (blank : Γ) (x y : X) (p : Config Q Γ t)
    (a : Option Terminal)
    (hstep : Enc x (decode p) → Enc y (L.apply blank (decode p) a))
    (henc : routedEnc Enc x p) : routedEnc Enc y ((hold L).apply blank p a) := by
  unfold routedEnc
  rw [decode_hold]
  exact hstep henc

/-- Reindexing also commutes with closure under tape observations. -/
theorem sweepClosure_routed (blank : Γ)
    (Enc : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM →
      Q × (Fin t → STape Γ) → Prop)
    (x : PalPeg.GalilScaffoldTop.State PalPeg.GalilScaffoldChainInputSupply.GalilVM)
    (p : Config Q Γ t) :
    PalPeg.MachineStep.sweepClosure blank (routedEnc Enc) x p ↔
      routedEnc (PalPeg.MachineStep.sweepClosure blank Enc) x p := by
  constructor
  · rintro ⟨T, hT, hteq⟩
    exact ⟨fun j => T (p.1.1 j), hT, fun j => hteq (p.1.1 j)⟩
  · rintro ⟨T, hT, hteq⟩
    refine ⟨fun j => T (p.1.1.symm j), ?_, ?_⟩
    · simpa only [routedEnc, decode, Equiv.symm_apply_apply] using hT
    · intro j
      simpa only [decode, Equiv.apply_symm_apply] using hteq (p.1.1.symm j)

/-- info: 'PalPeg.LocalRoleRouting.decode_route' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decode_route

/-- info: 'PalPeg.LocalRoleRouting.sweepClosure_routed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sweepClosure_routed

end PalPeg.LocalRoleRouting
