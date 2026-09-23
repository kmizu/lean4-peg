import PalPeg.LocalRoleRouting
import PalPeg.LocalStepFusion

/-!
# Fusing action rules across intermediate tape-role changes

A temporary role register lets the second rule read the tapes renamed by the
first. Flattening removes that register from the emitted control: the existing
outer role router installs only the final permutation. Both stages become one
bounded action list and one real sweep, not extra machine ticks.
-/
set_option autoImplicit false
namespace PalPeg.LocalRoleFusion
open PalPeg.LocalRoleRouting PalPeg.LocalStepFusion PalPeg.CloseoutCoreEnc12
open PalPeg.Program PalPeg.Local
variable {Terminal Q Γ : Type} {t K K₁ K₂ : ℕ}

/-- The action-list analogue of the existing local-step role router. -/
def routeRule (R : ActRule Terminal Q Γ t K) (change : RoleChange Terminal Q Γ t K) :
    ActRule Terminal (Control Q t) Γ t K where
  nq := fun q input ws =>
    let logical := fun j => ws (q.1 j)
    ((change q.2 input logical).trans q.1, R.nq q.2 input logical)
  acts := fun q input ws j => R.acts q.2 input (fun k => ws (q.1 k)) (q.1.symm j)
  len_le := fun q input ws j => R.len_le q.2 input (fun k => ws (q.1 k)) (q.1.symm j)

/-- Ideal execution in logical tape order, followed by a finite relabeling. -/
def logicalStep (R : ActRule Terminal Q Γ t K) (change : RoleChange Terminal Q Γ t K)
    (blank : Γ) (p : Q × (Fin t → STape Γ)) (input : Option Terminal) :
    Q × (Fin t → STape Γ) :=
  let result := idealStep R blank p input
  (result.1, fun j => result.2 (change p.1 input (fun k => readWin blank K (p.2 k)) j))

theorem decode_routeRule (R : ActRule Terminal Q Γ t K)
    (change : RoleChange Terminal Q Γ t K) (blank : Γ) (p : Config Q Γ t)
    (input : Option Terminal) :
    decode (idealStep (routeRule R change) blank p input) =
      logicalStep R change blank (decode p) input := by
  apply Prod.ext
  · rfl
  · funext j
    simp only [decode,routeRule,idealStep,logicalStep,Equiv.trans_apply,Equiv.symm_apply_apply]

/-- The second logical rule observes the intermediate relabeling. The same
source window provides both stages, with the existing additive radius bound. -/
theorem decode_seqRule (R₁ : ActRule Terminal Q Γ t K₁) (R₂ : ActRule Terminal Q Γ t K₂)
    (change₁ : RoleChange Terminal Q Γ t K₁) (change₂ : RoleChange Terminal Q Γ t K₂)
    (blank : Γ) (p : Config Q Γ t) (input : Option Terminal)
    (hm : ∀ j, K₁ + K₂ ≤ pos (p.2 j)) :
    decode (idealStep (seqRule (routeRule R₁ change₁) (routeRule R₂ change₂)) blank p input) =
      logicalStep R₂ change₂ blank (logicalStep R₁ change₁ blank (decode p) input) none := by
  rw [seqRule_ideal blank _ _ p input hm,decode_routeRule,decode_routeRule]

/-- The temporary permutation is recomputed from the finite source windows;
only the original finite control is emitted by the flattened rule. -/
def flatten (S : ActRule Terminal (Control Q t) Γ t K) : ActRule Terminal Q Γ t K where
  nq := fun q input ws => (S.nq (Equiv.refl _,q) input ws).2
  acts := fun q input ws => S.acts (Equiv.refl _,q) input ws
  len_le := fun q input ws j => S.len_le (Equiv.refl _,q) input ws j

def finalRoles (S : ActRule Terminal (Control Q t) Γ t K) : RoleChange Terminal Q Γ t K :=
  fun q input ws => (S.nq (Equiv.refl _,q) input ws).1

def compiled (S : ActRule Terminal (Control Q t) Γ t K) :
    LocalStep Terminal (Control Q t) Γ t K := route (compStep (flatten S)) (finalRoles S)

/-- One real routed sweep implements the flattened plan up to the existing
observational equality. This holds for every source role assignment. -/
theorem compiled_apply (S : ActRule Terminal (Control Q t) Γ t K) (blank : Γ)
    (p : Config Q Γ t) (input : Option Terminal)
    (hm : ∀ j, K ≤ pos ((decode p).2 j)) :
    let ideal := decode (idealStep S blank ((Equiv.refl _,(decode p).1),(decode p).2) input)
    let actual := decode ((compiled S).apply blank p input)
    actual.1 = ideal.1 ∧ ∀ j, TEqG blank (ideal.2 j) (actual.2 j) := by
  dsimp only
  rw [compiled,decode_route]
  obtain ⟨hq,ht⟩ := compStep_apply (flatten S) blank (decode p) input hm
  constructor
  · exact hq
  · intro j
    exact ht (finalRoles S (decode p).1 input (fun k => readWin blank K ((decode p).2 k)) j)

/-- The real compiled step performs both relabeling rules within one tick. -/
theorem compiled_seq (R₁ : ActRule Terminal Q Γ t K₁) (R₂ : ActRule Terminal Q Γ t K₂)
    (change₁ : RoleChange Terminal Q Γ t K₁) (change₂ : RoleChange Terminal Q Γ t K₂)
    (blank : Γ) (p : Config Q Γ t) (input : Option Terminal)
    (hm : ∀ j, K₁ + K₂ ≤ pos ((decode p).2 j)) :
    let ideal := logicalStep R₂ change₂ blank (logicalStep R₁ change₁ blank (decode p) input) none
    let actual := decode ((compiled (seqRule (routeRule R₁ change₁) (routeRule R₂ change₂))).apply blank p input)
    actual.1 = ideal.1 ∧ ∀ j, TEqG blank (ideal.2 j) (actual.2 j) := by
  have h := compiled_apply (seqRule (routeRule R₁ change₁) (routeRule R₂ change₂)) blank p input hm
  dsimp only at h ⊢
  rw [decode_seqRule R₁ R₂ change₁ change₂ blank _ input hm] at h
  exact h

/-- info: 'PalPeg.LocalRoleFusion.compiled_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled_seq

end PalPeg.LocalRoleFusion
