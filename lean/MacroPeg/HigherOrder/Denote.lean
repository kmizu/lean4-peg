import MacroPeg.HigherOrder.Domain

/-!
# The meaning of typed terms in the finite model

Fix the input `x`; positions are the lengths `q ≤ |x|` of its suffixes `sfx x q`. Given values `T` for the rules and
`ρ` for the variables, `den x t T ρ` is the value of the typed term `t`:

* a PEG operator is computed position by position from the values of its operands (`seqRes`, `altRes`, `notRes`,
  `starRes`); a leaf (`ε`, `.`, a character, a range, a literal) is run directly;
* a lambda is the table of its body's values on all well-formed (monotone) arguments; an application looks it up.

Rule values are computed by iteration (`iter`): start with no results anywhere, then evaluate every rule body with the
current values. `den_mono` — the meaning is well formed and monotone in `T` and `ρ` — makes the iterates an increasing
chain (`iter_le_succ`). By counting defined entries the chain is constant from `maxEnv x.length R` on
(`iter_stable`): a fixpoint, computed in a number of rounds that is a tower of exponentials in `|x|` whose height is
the order of the grammar.
-/

namespace Shallot.MacroPeg.HO

/-! ## Environments -/

/-- One value per type of `Γ`. -/
def Env : List Ty → Type
  | [] => Unit
  | τ :: Γ => Dom τ × Env Γ

def Env.get : {Γ : List Ty} → Env Γ → (i : Nat) → {τ : Ty} → Γ[i]? = some τ → Dom τ
  | [], _, _, _, h => absurd h (by simp)
  | _ :: _, (d, _), 0, _, h => (Option.some.inj h) ▸ d
  | _ :: _, (_, ρ), i + 1, _, h => Env.get ρ i h

def Env.le : {Γ : List Ty} → Env Γ → Env Γ → Prop
  | [], _, _ => True
  | τ :: _, (d, ρ), (d', ρ') => Dom.le τ d d' ∧ Env.le ρ ρ'

/-- Every value is well formed. -/
def Env.Mem (N : Nat) : {Γ : List Ty} → Env Γ → Prop
  | [], _ => True
  | τ :: _, (d, ρ) => d ∈ elems N τ ∧ Env.Mem N ρ

def Env.bot (N : Nat) : (Γ : List Ty) → Env Γ
  | [] => ()
  | τ :: Γ => (HO.bot N τ, Env.bot N Γ)

def Env.count : {Γ : List Ty} → Env Γ → Nat
  | [], _ => 0
  | τ :: _, (d, ρ) => defCount τ d + Env.count ρ

def maxEnv (N : Nat) : List Ty → Nat
  | [] => 0
  | τ :: Γ => maxCount N τ + maxEnv N Γ

section EnvLemmas

variable {N : Nat}

theorem Env.get_mem : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → ∀ (i : Nat) {τ : Ty} (h : Γ[i]? = some τ),
    Env.get ρ i h ∈ elems N τ
  | [], _, _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), hρ, 0, _, h => by cases Option.some.inj h; exact hρ.1
  | _ :: _, (_, _), hρ, i + 1, _, h => Env.get_mem hρ.2 i h

theorem Env.get_le : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → ∀ (i : Nat) {τ : Ty} (h : Γ[i]? = some τ),
    Dom.le τ (Env.get ρ i h) (Env.get ρ' i h)
  | [], _, _, _, _, _, h => absurd h (by simp)
  | _ :: _, (_, _), (_, _), hρ, 0, _, h => by cases Option.some.inj h; exact hρ.1
  | _ :: _, (_, _), (_, _), hρ, i + 1, _, h => Env.get_le hρ.2 i h

theorem Env.le_refl : ∀ {Γ : List Ty} (ρ : Env Γ), Env.le ρ ρ
  | [], _ => trivial
  | τ :: _, (d, ρ) => ⟨Dom.le_refl τ d, Env.le_refl ρ⟩

theorem Env.le_trans : ∀ {Γ : List Ty} {ρ₁ ρ₂ ρ₃ : Env Γ}, Env.le ρ₁ ρ₂ → Env.le ρ₂ ρ₃ → Env.le ρ₁ ρ₃
  | [], _, _, _, _, _ => trivial
  | τ :: _, (_, _), (_, _), (_, _), h₁, h₂ => ⟨Dom.le_trans τ _ _ _ h₁.1 h₂.1, Env.le_trans h₁.2 h₂.2⟩

theorem Env.bot_mem : ∀ Γ : List Ty, Env.Mem N (Env.bot N Γ)
  | [] => trivial
  | τ :: Γ => ⟨HO.bot_mem N τ, Env.bot_mem Γ⟩

theorem Env.bot_le : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → Env.le (Env.bot N Γ) ρ
  | [], _, _ => trivial
  | τ :: _, (d, _), h => ⟨HO.bot_le N τ d h.1, Env.bot_le h.2⟩

theorem Env.count_le : ∀ {Γ : List Ty} {ρ : Env Γ}, Env.Mem N ρ → Env.count ρ ≤ maxEnv N Γ
  | [], _, _ => Nat.le_refl _
  | τ :: _, (d, _), h => by
    have := defCount_le_maxCount N τ d h.1
    have := Env.count_le h.2
    simp only [Env.count, maxEnv]; omega

theorem Env.count_mono : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → Env.count ρ ≤ Env.count ρ'
  | [], _, _, _ => Nat.le_refl _
  | τ :: _, (_, _), (_, _), h => by
    have := defCount_mono τ h.1
    have := Env.count_mono h.2
    simp only [Env.count]; omega

theorem Env.count_lt : ∀ {Γ : List Ty} {ρ ρ' : Env Γ}, Env.le ρ ρ' → ρ ≠ ρ' → Env.count ρ < Env.count ρ'
  | [], _, _, _, hne => absurd rfl hne
  | τ :: _, (d, ρ), (d', ρ'), h, hne => by
    simp only [Env.count]
    have h₁ := defCount_mono τ h.1
    have h₂ := Env.count_mono h.2
    by_cases hd : d = d'
    · subst hd
      have : ρ ≠ ρ' := fun e => hne (by rw [e])
      have := Env.count_lt h.2 this
      omega
    · have := defCount_lt τ h.1 hd
      omega

end EnvLemmas

/-! ## Parsers position by position -/

section Positions

variable (x : List Char)

/-- The suffix of `x` with `q` symbols. -/
def sfx (q : Nat) : List Char := x.drop (x.length - q)

/-- A parser value from its result at each position `0, …, |x|`. -/
def baseVec (f : Nat → Res) : Dom .p := (List.range (x.length + 1)).map f

/-- The result at position `q`. -/
def atq (d : Dom .p) (q : Nat) : Res := (d : List Res).getD q none

/-- A leaf (`ε`, `.`, a character, a range, a literal) run once at position `q`. -/
def leafRes (e : HExp) (q : Nat) : Res := (hrun ⟨[]⟩ 1 e (sfx x q)).map (Option.map List.length)

end Positions

def seqRes (da db : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some j) => atq db j
  | r => r

def altRes (da db : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some none => atq db q
  | r => r

def notRes (da : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some _) => some none
  | some none => some (some q)
  | none => none

/-- `a*` at position `q`: repeat while `a` succeeds and consumes; a zero-width success loops forever (no result). -/
def starRes (da : Dom .p) (q : Nat) : Res :=
  match atq da q with
  | some (some j) => if j < q then starRes da j else none
  | some none => some (some q)
  | none => none
termination_by q

/-! ## The meaning of a term -/

/-- The value of `t` given rule values `T` and variable values `ρ`, on the input `x`. -/
def den (x : List Char) {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → Env R → Env Γ → Dom τ
  | _, _, .eps, _, _ => baseVec x (leafRes x .eps)
  | _, _, .any, _, _ => baseVec x (leafRes x .any)
  | _, _, .chr c, _, _ => baseVec x (leafRes x (.chr c))
  | _, _, .range lo hi, _, _ => baseVec x (leafRes x (.range lo hi))
  | _, _, .lit s, _, _ => baseVec x (leafRes x (.lit s))
  | _, _, .seq a b, T, ρ => baseVec x (seqRes (den x a T ρ) (den x b T ρ))
  | _, _, .alt a b, T, ρ => baseVec x (altRes (den x a T ρ) (den x b T ρ))
  | _, _, .star a, T, ρ => baseVec x (starRes (den x a T ρ))
  | _, _, .notP a, T, ρ => baseVec x (notRes (den x a T ρ))
  | _, _, .var i h, _, ρ => Env.get ρ i h
  | _, _, .rule i h, T, _ => Env.get T i h
  | _, _, @Tm.lam _ _ a _ body, T, ρ => (elems x.length a).map (fun d => den x body T (d, ρ))
  | _, _, .app f y, T, ρ => Dom.app (N := x.length) (den x f T ρ) (den x y T ρ)

/-- The rule bodies evaluated with rule values `T`. -/
def TBodies.den (x : List Char) {R : List Ty} : {S : List Ty} → TBodies R S → Env R → Env S
  | [], _, _ => ()
  | _ :: _, (t, ts), T => (HO.den x t T (), TBodies.den x ts T)

/-- The iterates: no results anywhere, then the bodies evaluated with the previous iterate. -/
def iter (x : List Char) {R : List Ty} (G : TGrammar R) : Nat → Env R
  | 0 => Env.bot x.length R
  | m + 1 => G.bodies.den x (iter x G m)

end Shallot.MacroPeg.HO
