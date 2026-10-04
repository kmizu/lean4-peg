import MacroPeg.Properties.Observation
import MacroPeg.PegEmbed
import Shallot.Peg.GrammarExtend

/-!
# The finite-argument fragment of first-order call-by-name Macro PEG (instructions.md §5.1)

The fragment is given as restricted syntax plus an embedding into `MExp` (allowed by §5.1):

* `FGrammar` = an ordinary PEG environment `env : List PExp` (rule `i` is referred to as `env i`; inside `env` and `D`,
  `.nt i` means env rule `i`), a finite argument domain `D : List PExp`, and parameterized rules `rules : List FRule`.
* A rule body (`FExp`) is a PEG expression that may also mention a formal parameter (`param j`), an env rule (`env i`), or
  call a fragment rule with actual arguments that are only a forwarded parameter (`fwd j`) or a constant of `D`
  (`const k`). No `lam`, `callParam`, `invoke` and no constructed arguments exist by construction: the fragment is
  first-order and pure, and every actual argument stays inside `D` during evaluation.

`toMacro` embeds an `FGrammar` into an ordinary `MGrammar`: macro rules `0 … |env|-1` are the env rules (arity 0, via the
existing `embedExp`), followed by the fragment rules (offset `|env|`). The identifier map is the identity on env indices
and `B ↦ |env| + B` on fragment rules, so it is injective and decodable.

This module also has the input-independent enumeration used by the specialization: `vecs n m` (all length-`m` vectors over
`[0, n)`), `specs F` (all valid (rule, argument-vector) pairs) and `code F B w` (the index of a pair in `specs F`), and the
syntactic well-formedness predicate `FGrammar.WF` with an executable checker `wfB` proved sound.
-/

namespace Shallot.MacroPeg

open Shallot (PExp Grammar)

/-- An actual argument of a fragment call: a forwarded formal parameter or a constant `D[k]`. -/
inductive FArg where
  | fwd (j : Nat)
  | const (k : Nat)
  deriving DecidableEq, Repr

/-- Fragment rule bodies. -/
inductive FExp where
  | eps
  | any
  | chr (c : Char)
  | range (lo hi : Char)
  | lit (s : List Char)
  /-- The `j`-th formal parameter of the enclosing rule. -/
  | param (j : Nat)
  /-- A reference to rule `i` of the ordinary environment. -/
  | env (i : Nat)
  /-- A call of fragment rule `B`. -/
  | call (B : Nat) (args : List FArg)
  | seq (e₁ e₂ : FExp)
  | alt (e₁ e₂ : FExp)
  | star (e : FExp)
  | notP (e : FExp)
  deriving Repr

structure FRule where
  arity : Nat
  body : FExp
  deriving Repr

structure FGrammar where
  env : List PExp
  D : List PExp
  rules : List FRule

/-! ## Embedding into Macro PEG -/

/-- The PEG always-fail expression, `!ε`; `embedExp pFail = MExp.failAlways`. -/
def pFail : PExp := .notP .eps

theorem embedExp_pFail : embedExp pFail = MExp.failAlways := rfl

/-- The constant `D[k]` (always-fail when out of range; never used under `WF`). -/
def FGrammar.constP (F : FGrammar) (k : Nat) : PExp := F.D.getD k pFail

def FArg.toM (F : FGrammar) : FArg → MExp
  | .fwd j => .param j
  | .const k => embedExp (F.constP k)

def FExp.toM (F : FGrammar) : FExp → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit s => .lit s
  | .param j => .param j
  | .env i => .call i []
  | .call B as => .call (F.env.length + B) (as.map (FArg.toM F))
  | .seq e₁ e₂ => .seq (FExp.toM F e₁) (FExp.toM F e₂)
  | .alt e₁ e₂ => .alt (FExp.toM F e₁) (FExp.toM F e₂)
  | .star e => .star (FExp.toM F e)
  | .notP e => .notP (FExp.toM F e)

/-- The Macro PEG grammar denoted by a fragment grammar. -/
def FGrammar.toMacro (F : FGrammar) : MGrammar :=
  ⟨F.env.map (fun p => ⟨0, embedExp p⟩) ++ F.rules.map (fun r => ⟨r.arity, r.body.toM F⟩)⟩

/-- The macro expression of a constant argument vector `w` (indices into `D`). -/
def FGrammar.constArgs (F : FGrammar) (w : List Nat) : List MExp := w.map (fun k => embedExp (F.constP k))

/-- The entry call `A(D[ks₀], …)` as a Macro PEG expression. -/
def FGrammar.entry (F : FGrammar) (A : Nat) (ks : List Nat) : MExp :=
  .call (F.env.length + A) (F.constArgs ks)

/-! ## Well-formedness (syntactic) -/

def FArg.WF (F : FGrammar) (a : Nat) : FArg → Prop
  | .fwd j => j < a
  | .const k => k < F.D.length

def FExp.WF (F : FGrammar) (a : Nat) : FExp → Prop
  | .param j => j < a
  | .env i => i < F.env.length
  | .call B as => (∃ r, F.rules[B]? = some r ∧ as.length = r.arity) ∧ ∀ x ∈ as, x.WF F a
  | .seq e₁ e₂ => FExp.WF F a e₁ ∧ FExp.WF F a e₂
  | .alt e₁ e₂ => FExp.WF F a e₁ ∧ FExp.WF F a e₂
  | .star e => FExp.WF F a e
  | .notP e => FExp.WF F a e
  | .eps | .any | .chr _ | .range _ _ | .lit _ => True

/-- Syntactic well-formedness: every env reference (in `env`, `D` and rule bodies) exists, every called fragment rule
exists with matching arity, every parameter and forwarded parameter is in range, every constant index is in `D`. -/
def FGrammar.WF (F : FGrammar) : Prop :=
  (∀ p ∈ F.env, p.NtBounded F.env.length) ∧ (∀ p ∈ F.D, p.NtBounded F.env.length) ∧
    ∀ r ∈ F.rules, r.body.WF F r.arity

/-- `w` is an admissible constant argument vector for rule `B`. -/
def FGrammar.ValidVec (F : FGrammar) (B : Nat) (w : List Nat) : Prop :=
  ∃ r, F.rules[B]? = some r ∧ w.length = r.arity ∧ ∀ k ∈ w, k < F.D.length

/-! ### Executable checker -/

def ntBoundedB (n : Nat) : PExp → Bool
  | .nt i => decide (i < n)
  | .seq e₁ e₂ => ntBoundedB n e₁ && ntBoundedB n e₂
  | .alt e₁ e₂ => ntBoundedB n e₁ && ntBoundedB n e₂
  | .star e => ntBoundedB n e
  | .notP e => ntBoundedB n e
  | .eps | .any | .chr _ | .range _ _ | .lit _ => true

theorem ntBoundedB_sound (n : Nat) : ∀ p : PExp, ntBoundedB n p = true → p.NtBounded n
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .nt i, h => by simpa [ntBoundedB, PExp.NtBounded] using h
  | .seq e₁ e₂, h => by
    simp only [ntBoundedB, Bool.and_eq_true] at h
    exact ⟨ntBoundedB_sound n e₁ h.1, ntBoundedB_sound n e₂ h.2⟩
  | .alt e₁ e₂, h => by
    simp only [ntBoundedB, Bool.and_eq_true] at h
    exact ⟨ntBoundedB_sound n e₁ h.1, ntBoundedB_sound n e₂ h.2⟩
  | .star e, h => ntBoundedB_sound n e h
  | .notP e, h => ntBoundedB_sound n e h

def FArg.wfB (F : FGrammar) (a : Nat) : FArg → Bool
  | .fwd j => decide (j < a)
  | .const k => decide (k < F.D.length)

def FExp.wfB (F : FGrammar) (a : Nat) : FExp → Bool
  | .param j => decide (j < a)
  | .env i => decide (i < F.env.length)
  | .call B as =>
    (match F.rules[B]? with
      | some r => decide (as.length = r.arity)
      | none => false) && as.all (FArg.wfB F a)
  | .seq e₁ e₂ => FExp.wfB F a e₁ && FExp.wfB F a e₂
  | .alt e₁ e₂ => FExp.wfB F a e₁ && FExp.wfB F a e₂
  | .star e => FExp.wfB F a e
  | .notP e => FExp.wfB F a e
  | .eps | .any | .chr _ | .range _ _ | .lit _ => true

theorem FArg.wfB_sound (F : FGrammar) (a : Nat) : ∀ x : FArg, x.wfB F a = true → x.WF F a
  | .fwd j, h => by simpa [FArg.wfB, FArg.WF] using h
  | .const k, h => by simpa [FArg.wfB, FArg.WF] using h

theorem FExp.wfB_sound (F : FGrammar) (a : Nat) : ∀ e : FExp, e.wfB F a = true → e.WF F a
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param j, h => by simpa [FExp.wfB, FExp.WF] using h
  | .env i, h => by simpa [FExp.wfB, FExp.WF] using h
  | .call B as, h => by
    simp only [FExp.wfB, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨?_, fun x hx => FArg.wfB_sound F a x (h₂ x hx)⟩
    cases hr : F.rules[B]? with
    | none => rw [hr] at h₁; simp at h₁
    | some r => rw [hr] at h₁; exact ⟨r, rfl, by simpa using h₁⟩
  | .seq e₁ e₂, h => by
    simp only [FExp.wfB, Bool.and_eq_true] at h
    exact ⟨FExp.wfB_sound F a e₁ h.1, FExp.wfB_sound F a e₂ h.2⟩
  | .alt e₁ e₂, h => by
    simp only [FExp.wfB, Bool.and_eq_true] at h
    exact ⟨FExp.wfB_sound F a e₁ h.1, FExp.wfB_sound F a e₂ h.2⟩
  | .star e, h => FExp.wfB_sound F a e h
  | .notP e, h => FExp.wfB_sound F a e h

def FGrammar.wfB (F : FGrammar) : Bool :=
  F.env.all (ntBoundedB F.env.length) && F.D.all (ntBoundedB F.env.length) &&
    F.rules.all (fun r => r.body.wfB F r.arity)

theorem FGrammar.wfB_sound (F : FGrammar) (h : F.wfB = true) : F.WF := by
  simp only [FGrammar.wfB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  exact ⟨fun p hp => ntBoundedB_sound _ p (h₁ p hp), fun p hp => ntBoundedB_sound _ p (h₂ p hp),
    fun r hr => FExp.wfB_sound F r.arity r.body (h₃ r hr)⟩

def FGrammar.validVecB (F : FGrammar) (B : Nat) (w : List Nat) : Bool :=
  (match F.rules[B]? with
    | some r => decide (w.length = r.arity)
    | none => false) && w.all (fun k => decide (k < F.D.length))

theorem FGrammar.validVecB_sound (F : FGrammar) (B : Nat) (w : List Nat) (h : F.validVecB B w = true) :
    F.ValidVec B w := by
  simp only [FGrammar.validVecB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  cases hr : F.rules[B]? with
  | none => rw [hr] at h₁; simp at h₁
  | some r => rw [hr] at h₁; exact ⟨r, hr, by simpa using h₁, h₂⟩

/-! ## Enumeration of argument vectors and specializations -/

theorem sum_replicate_nat (c : Nat) : ∀ n, (List.replicate n c).sum = n * c
  | 0 => by simp
  | n + 1 => by simp [List.replicate_succ, sum_replicate_nat c n, Nat.succ_mul, Nat.add_comm]

/-- All length-`m` vectors with entries in `[0, n)`. -/
def vecs (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | m + 1 => (List.range n).flatMap (fun k => (vecs n m).map (k :: ·))

theorem length_vecs (n : Nat) : ∀ m, (vecs n m).length = n ^ m
  | 0 => rfl
  | m + 1 => by
    simp only [vecs, List.length_flatMap, List.length_map, length_vecs n m]
    rw [List.map_const', List.length_range, sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]

theorem mem_vecs (n : Nat) : ∀ (m : Nat) (w : List Nat), w ∈ vecs n m ↔ w.length = m ∧ ∀ k ∈ w, k < n
  | 0, w => by
    cases w with
    | nil => simp [vecs]
    | cons _ _ => simp [vecs]
  | m + 1, w => by
    cases w with
    | nil => simp [vecs]
    | cons k w =>
      simp only [vecs, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq, List.length_cons,
        List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨k', hk', w', hw', rfl, rfl⟩
        exact ⟨((mem_vecs n m w').1 hw').1, hk', ((mem_vecs n m w').1 hw').2⟩
      · rintro ⟨hl, hk, hw⟩
        exact ⟨k, hk, w, (mem_vecs n m w).2 ⟨hl, hw⟩, rfl, rfl⟩

/-- `(i + j, w)` for every rule `rs[j]` and every admissible vector `w` of it, rule by rule. -/
def specsFrom (d : Nat) : Nat → List FRule → List (Nat × List Nat)
  | _, [] => []
  | i, r :: rs => (vecs d r.arity).map (fun w => (i, w)) ++ specsFrom d (i + 1) rs

theorem length_specsFrom (d : Nat) : ∀ (i : Nat) (rs : List FRule),
    (specsFrom d i rs).length = (rs.map (fun r => d ^ r.arity)).sum
  | _, [] => rfl
  | i, r :: rs => by
    simp [specsFrom, length_vecs, length_specsFrom d (i + 1) rs]

theorem mem_specsFrom (d : Nat) : ∀ (i : Nat) (rs : List FRule) (B : Nat) (w : List Nat),
    (B, w) ∈ specsFrom d i rs ↔
      i ≤ B ∧ ∃ r, rs[B - i]? = some r ∧ w.length = r.arity ∧ ∀ k ∈ w, k < d
  | i, [], B, w => by simp [specsFrom]
  | i, r :: rs, B, w => by
    simp only [specsFrom, List.mem_append, List.mem_map, Prod.mk.injEq]
    rw [mem_specsFrom d (i + 1) rs B w]
    constructor
    · rintro (⟨w', hw', rfl, rfl⟩ | ⟨hle, r', hr', hl, hk⟩)
      · exact ⟨Nat.le_refl _, r, by simp, ((mem_vecs d _ w').1 hw').1, ((mem_vecs d _ w').1 hw').2⟩
      · refine ⟨by omega, r', ?_, hl, hk⟩
        have : B - i = (B - (i + 1)) + 1 := by omega
        rw [this]; simpa using hr'
    · rintro ⟨hle, r', hr', hl, hk⟩
      by_cases hB : B = i
      · subst hB
        simp at hr'
        subst hr'
        exact Or.inl ⟨w, (mem_vecs d _ w).2 ⟨hl, hk⟩, rfl, rfl⟩
      · refine Or.inr ⟨by omega, r', ?_, hl, hk⟩
        have : B - i = (B - (i + 1)) + 1 := by omega
        rw [this] at hr'; simpa using hr'

/-- Every admissible (rule, constant vector) pair, in rule order. -/
def FGrammar.specs (F : FGrammar) : List (Nat × List Nat) := specsFrom F.D.length 0 F.rules

theorem FGrammar.mem_specs (F : FGrammar) (B : Nat) (w : List Nat) : (B, w) ∈ F.specs ↔ F.ValidVec B w := by
  simp [FGrammar.specs, mem_specsFrom, FGrammar.ValidVec]

/-- The number of specialized rules: `Σ_B |D| ^ arity(B)` (exactly). -/
theorem FGrammar.length_specs (F : FGrammar) : F.specs.length = (F.rules.map (fun r => F.D.length ^ r.arity)).sum :=
  length_specsFrom _ _ _

/-- First index of `a` in a list (the length when absent). -/
def indexIn {α : Type} [DecidableEq α] (a : α) : List α → Nat
  | [] => 0
  | b :: bs => if b = a then 0 else indexIn a bs + 1

theorem getElem?_indexIn {α : Type} [DecidableEq α] (a : α) : ∀ l : List α, a ∈ l → l[indexIn a l]? = some a
  | [], h => by simp at h
  | b :: bs, h => by
    by_cases hb : b = a
    · simp [indexIn, hb]
    · have : a ∈ bs := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hb
        · exact h
      simp [indexIn, hb, getElem?_indexIn a bs this]

/-- The specialized-rule index of `(B, w)`. -/
def FGrammar.code (F : FGrammar) (B : Nat) (w : List Nat) : Nat := indexIn (B, w) F.specs

theorem FGrammar.specs_code (F : FGrammar) {B : Nat} {w : List Nat} (h : F.ValidVec B w) :
    F.specs[F.code B w]? = some (B, w) :=
  getElem?_indexIn _ _ ((F.mem_specs B w).2 h)

end Shallot.MacroPeg
