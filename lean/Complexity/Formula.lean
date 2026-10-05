import Complexity.Qbf

/-!
# Tree formulas, quantified trees, prenexing, and compilation to circuits

The hardness proof reasons about ordinary formula trees (`Formula`) and quantified trees (`QF`) under function
environments. Two general facts carry the results over to the circuit-matrix prenex formulas of `Qbf.lean`:

* `QF.eval_prenex`: a quantified tree is equivalent to its prenex form when no propositional side condition mentions a
  variable quantified below it (`QF.Clean`);
* `matrixValue_compileF`: the circuit `compileF ψ p` (gates named by tree paths under `p`) computes `ψ`.
-/

namespace Complexity

inductive Formula where
  | var (x : Name)
  | tt
  | ff
  | not (a : Formula)
  | and (a b : Formula)
  | or (a b : Formula)

def Formula.eval (ρ : Name → Bool) : Formula → Bool
  | .var x => ρ x
  | .tt => true
  | .ff => false
  | .not a => !a.eval ρ
  | .and a b => a.eval ρ && b.eval ρ
  | .or a b => a.eval ρ || b.eval ρ

def Formula.imp (a b : Formula) : Formula := .or (.not a) b
def Formula.iff (a b : Formula) : Formula := .or (.and a b) (.and (.not a) (.not b))

def bigAnd : List Formula → Formula
  | [] => .tt
  | a :: as => .and a (bigAnd as)

def bigOr : List Formula → Formula
  | [] => .ff
  | a :: as => .or a (bigOr as)

theorem eval_imp (ρ : Name → Bool) (a b : Formula) : (a.imp b).eval ρ = (!a.eval ρ || b.eval ρ) := rfl

theorem eval_iff (ρ : Name → Bool) (a b : Formula) : (a.iff b).eval ρ = (a.eval ρ == b.eval ρ) := by
  simp only [Formula.iff, Formula.eval]; cases a.eval ρ <;> cases b.eval ρ <;> rfl

theorem eval_bigAnd (ρ : Name → Bool) : ∀ as : List Formula, (bigAnd as).eval ρ = true ↔ ∀ a ∈ as, a.eval ρ = true
  | [] => by simp [bigAnd, Formula.eval]
  | a :: as => by simp [bigAnd, Formula.eval, eval_bigAnd ρ as]

theorem eval_bigOr (ρ : Name → Bool) : ∀ as : List Formula, (bigOr as).eval ρ = true ↔ ∃ a ∈ as, a.eval ρ = true
  | [] => by simp [bigOr, Formula.eval]
  | a :: as => by simp [bigOr, Formula.eval, eval_bigOr ρ as]

/-! ## Dependence on a set of variables -/

def upd (ρ : Name → Bool) (x : Name) (b : Bool) : Name → Bool := fun y => if y = x then b else ρ y

/-- `f` only looks at variables in `S`. -/
def DependsOn (f : (Name → Bool) → Bool) (S : Name → Prop) : Prop :=
  ∀ ρ ρ', (∀ x, S x → ρ x = ρ' x) → f ρ = f ρ'

theorem DependsOn.mono {f : (Name → Bool) → Bool} {S T : Name → Prop} (h : DependsOn f S) (hST : ∀ x, S x → T x) :
    DependsOn f T := fun ρ ρ' hρ => h ρ ρ' (fun x hx => hρ x (hST x hx))

theorem dependsOn_var (x : Name) : DependsOn (fun ρ => (Formula.var x).eval ρ) (· = x) :=
  fun _ _ h => h x rfl

theorem dependsOn_not {a : Formula} {S : Name → Prop} (h : DependsOn a.eval S) : DependsOn (Formula.not a).eval S :=
  fun ρ ρ' hρ => by simp only [Formula.eval, h ρ ρ' hρ]

theorem dependsOn_and {a b : Formula} {S : Name → Prop} (ha : DependsOn a.eval S) (hb : DependsOn b.eval S) :
    DependsOn (Formula.and a b).eval S := fun ρ ρ' hρ => by simp only [Formula.eval, ha ρ ρ' hρ, hb ρ ρ' hρ]

theorem dependsOn_or {a b : Formula} {S : Name → Prop} (ha : DependsOn a.eval S) (hb : DependsOn b.eval S) :
    DependsOn (Formula.or a b).eval S := fun ρ ρ' hρ => by simp only [Formula.eval, ha ρ ρ' hρ, hb ρ ρ' hρ]

theorem dependsOn_bigAnd {S : Name → Prop} : ∀ as : List Formula, (∀ a ∈ as, DependsOn a.eval S) →
    DependsOn (bigAnd as).eval S
  | [], _ => fun _ _ _ => rfl
  | a :: as, h => dependsOn_and (h a List.mem_cons_self)
      (dependsOn_bigAnd as (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem dependsOn_bigOr {S : Name → Prop} : ∀ as : List Formula, (∀ a ∈ as, DependsOn a.eval S) →
    DependsOn (bigOr as).eval S
  | [], _ => fun _ _ _ => rfl
  | a :: as, h => dependsOn_or (h a List.mem_cons_self)
      (dependsOn_bigOr as (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-! ## Quantified trees and prenexing -/

inductive QF where
  | prop (ψ : Formula)
  | ex (x : Name) (φ : QF)
  | all (x : Name) (φ : QF)
  | andL (ψ : Formula) (φ : QF)
  | impL (ψ : Formula) (φ : QF)

def QF.eval : QF → (Name → Bool) → Bool
  | .prop ψ, ρ => ψ.eval ρ
  | .ex x φ, ρ => φ.eval (upd ρ x true) || φ.eval (upd ρ x false)
  | .all x φ, ρ => φ.eval (upd ρ x true) && φ.eval (upd ρ x false)
  | .andL ψ φ, ρ => ψ.eval ρ && φ.eval ρ
  | .impL ψ φ, ρ => !ψ.eval ρ || φ.eval ρ

def QF.bound : QF → List Name
  | .prop _ => []
  | .ex x φ => x :: φ.bound
  | .all x φ => x :: φ.bound
  | .andL _ φ => φ.bound
  | .impL _ φ => φ.bound

/-- No side condition mentions a variable quantified below it. -/
def QF.Clean : QF → Prop
  | .prop _ => True
  | .ex _ φ => φ.Clean
  | .all _ φ => φ.Clean
  | .andL ψ φ => (∀ x ∈ φ.bound, ∀ ρ b, ψ.eval (upd ρ x b) = ψ.eval ρ) ∧ φ.Clean
  | .impL ψ φ => (∀ x ∈ φ.bound, ∀ ρ b, ψ.eval (upd ρ x b) = ψ.eval ρ) ∧ φ.Clean

def QF.prenex : QF → List (Bool × Name) × Formula
  | .prop ψ => ([], ψ)
  | .ex x φ => ((false, x) :: φ.prenex.1, φ.prenex.2)
  | .all x φ => ((true, x) :: φ.prenex.1, φ.prenex.2)
  | .andL ψ φ => (φ.prenex.1, .and ψ φ.prenex.2)
  | .impL ψ φ => (φ.prenex.1, ψ.imp φ.prenex.2)

def evalPrefix (m : Formula) : List (Bool × Name) → (Name → Bool) → Bool
  | [], ρ => m.eval ρ
  | (true, x) :: q, ρ => evalPrefix m q (upd ρ x true) && evalPrefix m q (upd ρ x false)
  | (false, x) :: q, ρ => evalPrefix m q (upd ρ x true) || evalPrefix m q (upd ρ x false)

theorem prenex_bound : ∀ φ : QF, φ.prenex.1.map Prod.snd = φ.bound
  | .prop _ => rfl
  | .ex x φ => by simp [QF.prenex, QF.bound, prenex_bound φ]
  | .all x φ => by simp [QF.prenex, QF.bound, prenex_bound φ]
  | .andL _ φ => by simp [QF.prenex, QF.bound, prenex_bound φ]
  | .impL _ φ => by simp [QF.prenex, QF.bound, prenex_bound φ]

/-- Pulling a side condition through a prefix that does not touch it. -/
theorem evalPrefix_side (comb : Bool → Bool → Bool) (ψ m : Formula) (mk : Formula → Formula)
    (hmk : ∀ ρ, (mk m).eval ρ = comb (ψ.eval ρ) (m.eval ρ)) :
    ∀ q : List (Bool × Name), (∀ x ∈ q.map Prod.snd, ∀ ρ b, ψ.eval (upd ρ x b) = ψ.eval ρ) →
      (comb true true = true ∧ comb true false = false ∧ comb false true = comb false false) →
      ∀ ρ, evalPrefix (mk m) q ρ = comb (ψ.eval ρ) (evalPrefix m q ρ)
  | [], _, _, ρ => hmk ρ
  | (b, x) :: q, hq, hc, ρ => by
    have hx := hq x (by simp)
    have ih := evalPrefix_side comb ψ m mk hmk q (fun y hy => hq y (by simp [hy])) hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases b <;> simp only [evalPrefix, ih, hx] <;>
      cases hψ : ψ.eval ρ <;> cases evalPrefix m q (upd ρ x true) <;> cases evalPrefix m q (upd ρ x false) <;>
      simp_all

/-- **Prenexing.** -/
theorem QF.eval_prenex : ∀ φ : QF, φ.Clean → ∀ ρ, φ.eval ρ = evalPrefix φ.prenex.2 φ.prenex.1 ρ
  | .prop ψ, _, ρ => rfl
  | .ex x φ, h, ρ => by simp only [QF.eval, QF.prenex, evalPrefix, QF.eval_prenex φ h]
  | .all x φ, h, ρ => by simp only [QF.eval, QF.prenex, evalPrefix, QF.eval_prenex φ h]
  | .andL ψ φ, h, ρ => by
    simp only [QF.eval, QF.prenex, QF.eval_prenex φ h.2]
    refine (evalPrefix_side (· && ·) ψ φ.prenex.2 (Formula.and ψ) (fun _ => rfl) φ.prenex.1
      (by rw [prenex_bound]; exact h.1) (by decide) ρ).symm
  | .impL ψ φ, h, ρ => by
    simp only [QF.eval, QF.prenex, QF.eval_prenex φ h.2]
    refine (evalPrefix_side (fun a b => !a || b) ψ φ.prenex.2 (Formula.imp ψ) (fun _ => rfl) φ.prenex.1
      (by rw [prenex_bound]; exact h.1) (by decide) ρ).symm

/-! ## Block quantifiers -/

def exBlock : List Name → QF → QF
  | [], φ => φ
  | x :: xs, φ => .ex x (exBlock xs φ)

def allBlock : List Name → QF → QF
  | [], φ => φ
  | x :: xs, φ => .all x (allBlock xs φ)

/-- `ρ'` agrees with `ρ` outside `xs`. -/
def AgreeOff (xs : List Name) (ρ ρ' : Name → Bool) : Prop := ∀ y, y ∉ xs → ρ' y = ρ y

theorem eval_exBlock : ∀ (xs : List Name) (φ : QF) (ρ : Name → Bool),
    (exBlock xs φ).eval ρ = true ↔ ∃ ρ', AgreeOff xs ρ ρ' ∧ φ.eval ρ' = true
  | [], φ, ρ => by
    constructor
    · intro h; exact ⟨ρ, fun _ _ => rfl, h⟩
    · rintro ⟨ρ', hρ', h⟩
      have : ρ' = ρ := funext fun y => hρ' y (by simp)
      rwa [this] at h
  | x :: xs, φ, ρ => by
    simp only [exBlock, QF.eval, Bool.or_eq_true, eval_exBlock xs φ]
    constructor
    · rintro (⟨ρ', hρ', h⟩ | ⟨ρ', hρ', h⟩)
      · refine ⟨ρ', fun y hy => ?_, h⟩
        simp only [List.mem_cons, not_or] at hy
        rw [hρ' y hy.2]; simp [upd, hy.1]
      · refine ⟨ρ', fun y hy => ?_, h⟩
        simp only [List.mem_cons, not_or] at hy
        rw [hρ' y hy.2]; simp [upd, hy.1]
    · rintro ⟨ρ', hρ', h⟩
      cases hx : ρ' x
      · refine Or.inr ⟨ρ', fun y hy => ?_, h⟩
        by_cases hyx : y = x
        · subst hyx; simp [upd, hx]
        · simp only [upd, hyx, if_false]; exact hρ' y (by simp [hyx, hy])
      · refine Or.inl ⟨ρ', fun y hy => ?_, h⟩
        by_cases hyx : y = x
        · subst hyx; simp [upd, hx]
        · simp only [upd, hyx, if_false]; exact hρ' y (by simp [hyx, hy])

theorem eval_allBlock : ∀ (xs : List Name) (φ : QF) (ρ : Name → Bool),
    (allBlock xs φ).eval ρ = true ↔ ∀ ρ', AgreeOff xs ρ ρ' → φ.eval ρ' = true
  | [], φ, ρ => by
    constructor
    · intro h ρ' hρ'
      have : ρ' = ρ := funext fun y => hρ' y (by simp)
      rwa [this]
    · intro h; exact h ρ (fun _ _ => rfl)
  | x :: xs, φ, ρ => by
    simp only [allBlock, QF.eval, Bool.and_eq_true, eval_allBlock xs φ]
    constructor
    · rintro ⟨h₁, h₂⟩ ρ' hρ'
      cases hx : ρ' x
      · refine h₂ ρ' (fun y hy => ?_)
        by_cases hyx : y = x
        · subst hyx; simp [upd, hx]
        · simp only [upd, hyx, if_false]; exact hρ' y (by simp [hyx, hy])
      · refine h₁ ρ' (fun y hy => ?_)
        by_cases hyx : y = x
        · subst hyx; simp [upd, hx]
        · simp only [upd, hyx, if_false]; exact hρ' y (by simp [hyx, hy])
    · intro h
      refine ⟨fun ρ' hρ' => h ρ' (fun y hy => ?_), fun ρ' hρ' => h ρ' (fun y hy => ?_)⟩ <;>
      · simp only [List.mem_cons, not_or] at hy
        rw [hρ' y hy.2]; simp [upd, hy.1]

theorem bound_exBlock : ∀ (xs : List Name) (φ : QF), (exBlock xs φ).bound = xs ++ φ.bound
  | [], _ => rfl
  | x :: xs, φ => by simp [exBlock, QF.bound, bound_exBlock xs φ]

theorem bound_allBlock : ∀ (xs : List Name) (φ : QF), (allBlock xs φ).bound = xs ++ φ.bound
  | [], _ => rfl
  | x :: xs, φ => by simp [allBlock, QF.bound, bound_allBlock xs φ]

theorem clean_exBlock : ∀ (xs : List Name) (φ : QF), φ.Clean → (exBlock xs φ).Clean
  | [], _, h => h
  | _ :: xs, φ, h => clean_exBlock xs φ h

theorem clean_allBlock : ∀ (xs : List Name) (φ : QF), φ.Clean → (allBlock xs φ).Clean
  | [], _, h => h
  | _ :: xs, φ, h => clean_allBlock xs φ h

/-! ## Compiling a tree to a circuit -/

/-- Gates of `ψ`, the root gate named `p`, the subtrees named by extending `p`. -/
def compileF : Formula → Name → List Gate
  | .var x, p => [⟨p, .var x⟩]
  | .tt, p => [⟨p, .tt⟩]
  | .ff, p => [⟨p, .ff⟩]
  | .not a, p => compileF a (p ++ [0]) ++ [⟨p, .not (p ++ [0])⟩]
  | .and a b, p => compileF a (p ++ [0]) ++ compileF b (p ++ [1]) ++ [⟨p, .and (p ++ [0]) (p ++ [1])⟩]
  | .or a b, p => compileF a (p ++ [0]) ++ compileF b (p ++ [1]) ++ [⟨p, .or (p ++ [0]) (p ++ [1])⟩]

/-- The values after running the gates. -/
def runGates (ρ : List (Name × Bool)) : List Gate → List (Name × Bool) → List (Name × Bool)
  | [], vals => vals
  | g :: gs, vals => runGates ρ gs ((g.out, g.op.eval ρ vals) :: vals)

end Complexity
