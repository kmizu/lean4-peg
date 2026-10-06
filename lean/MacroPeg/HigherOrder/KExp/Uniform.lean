import MacroPeg.HigherOrder.KExp.Hard

/-!
# The uniform problem: the grammar is part of the input

An instance is a grammar, a start expression and a string, serialized as tokens below `16` (`serIn`) and read from
bits four at a time, as in the TQBF reduction. A token's meaning depends on what is being read (a number, a type, an
expression, a string, a rule list), so the codes of different sorts share tokens; each code is prefix-free
(`serE_prefix` and friends), so the serialization is injective (`serIn_inj`).

`UMPEG j` is the set of instances whose grammar is well typed of order `≤ j`, whose start is a closed parser, and whose
grammar consumes the whole string.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

/-! ## The order of the lambdas -/

/-- One more than the largest order of a lambda's binder type (`0` without lambdas). With rule types of order `≤ j`
and `lamOrd ≤ j`, every subterm of a well-typed expression has a type of order `≤ j`. -/
def lamOrd : HExp → Nat
  | .seq a b | .alt a b | .app a b => max (lamOrd a) (lamOrd b)
  | .star a | .notP a => lamOrd a
  | .lam τ b => max (τ.order + 1) (lamOrd b)
  | _ => 0

/-! ## Serialization -/

/-- `n` in unary: `1ⁿ0`. -/
def serNat : Nat → List Nat
  | 0 => [0]
  | n + 1 => 1 :: serNat n

def serChar (c : Char) : List Nat := serNat c.toNat

/-- A string: `1 c` per character, then `0`. -/
def serStr : List Char → List Nat
  | [] => [0]
  | c :: s => 1 :: (serChar c ++ serStr s)

def serTy : HO.Ty → List Nat
  | .p => [0]
  | .arr a b => 1 :: (serTy a ++ serTy b)

def serE : HExp → List Nat
  | .eps => [0]
  | .any => [1]
  | .chr c => 2 :: serChar c
  | .range lo hi => 3 :: (serChar lo ++ serChar hi)
  | .lit s => 4 :: serStr s
  | .seq a b => 5 :: (serE a ++ serE b)
  | .alt a b => 6 :: (serE a ++ serE b)
  | .star a => 7 :: serE a
  | .notP a => 8 :: serE a
  | .var i => 9 :: serNat i
  | .rule i => 10 :: serNat i
  | .lam τ b => 11 :: (serTy τ ++ serE b)
  | .app f a => 12 :: (serE f ++ serE a)

/-- The rule types: `1 τ` per rule, then `0`. -/
def serTys : List HO.Ty → List Nat
  | [] => [0]
  | τ :: ts => 1 :: (serTy τ ++ serTys ts)

/-- The rule bodies: `1 e` per rule, then `0`. -/
def serBodies : List HExp → List Nat
  | [] => [0]
  | e :: es => 1 :: (serE e ++ serBodies es)

/-- An instance: all rule types (so that a body can be typed in one pass), the rule bodies, the start expression,
the string. -/
def serIn (g : HGrammar) (s : HExp) (x : List Char) : List Nat :=
  serTys (g.rules.map HRule.ty) ++ (serBodies (g.rules.map HRule.body) ++ (serE s ++ serStr x))

/-! ## The codes are prefix-free -/

theorem serNat_prefix : ∀ (a b : Nat) (r r' : List Nat), serNat a ++ r = serNat b ++ r' → a = b ∧ r = r'
  | 0, 0, _, _, h => by simpa [serNat] using h
  | 0, _ + 1, _, _, h => by simp [serNat] at h
  | _ + 1, 0, _, _, h => by simp [serNat] at h
  | a + 1, b + 1, r, r', h => by
    simp only [serNat, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := serNat_prefix a b r r' h
    exact ⟨rfl, rfl⟩

theorem serChar_prefix {a b : Char} {r r' : List Nat} (h : serChar a ++ r = serChar b ++ r') : a = b ∧ r = r' := by
  obtain ⟨h₁, h₂⟩ := serNat_prefix _ _ _ _ h
  exact ⟨Char.toNat_inj.mp h₁, h₂⟩

theorem serStr_prefix : ∀ (a b : List Char) (r r' : List Nat), serStr a ++ r = serStr b ++ r' → a = b ∧ r = r'
  | [], [], _, _, h => by simpa [serStr] using h
  | [], _ :: _, _, _, h => by simp [serStr] at h
  | _ :: _, [], _, _, h => by simp [serStr] at h
  | c :: a, d :: b, r, r', h => by
    simp only [serStr, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h₁⟩ := serChar_prefix h
    obtain ⟨rfl, rfl⟩ := serStr_prefix a b r r' h₁
    exact ⟨rfl, rfl⟩

theorem serTy_prefix : ∀ (a b : HO.Ty) (r r' : List Nat), serTy a ++ r = serTy b ++ r' → a = b ∧ r = r'
  | .p, .p, _, _, h => by simpa [serTy] using h
  | .p, .arr _ _, _, _, h => by simp [serTy] at h
  | .arr _ _, .p, _, _, h => by simp [serTy] at h
  | .arr a₁ a₂, .arr b₁ b₂, r, r', h => by
    simp only [serTy, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h₁⟩ := serTy_prefix a₁ b₁ _ _ h
    obtain ⟨rfl, rfl⟩ := serTy_prefix a₂ b₂ r r' h₁
    exact ⟨rfl, rfl⟩

theorem serE_prefix : ∀ (a b : HExp) (r r' : List Nat), serE a ++ r = serE b ++ r' → a = b ∧ r = r' := by
  intro a
  induction a with
  | eps | any =>
    intro b r r' h
    cases b <;> simp_all [serE]
  | chr c =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, rfl⟩ := serChar_prefix h.2
    exact ⟨rfl, rfl⟩
  | range lo hi =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.append_assoc, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, h₁⟩ := serChar_prefix h.2
    obtain ⟨rfl, rfl⟩ := serChar_prefix h₁
    exact ⟨rfl, rfl⟩
  | lit s =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, rfl⟩ := serStr_prefix _ _ _ _ h.2
    exact ⟨rfl, rfl⟩
  | seq a₁ a₂ ih₁ ih₂ | alt a₁ a₂ ih₁ ih₂ | app a₁ a₂ ih₁ ih₂ =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.append_assoc, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, h₁⟩ := ih₁ _ _ _ h.2
    obtain ⟨rfl, rfl⟩ := ih₂ _ _ _ h₁
    exact ⟨rfl, rfl⟩
  | star a ih | notP a ih =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h.2
    exact ⟨rfl, rfl⟩
  | var i | rule i =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, rfl⟩ := serNat_prefix _ _ _ _ h.2
    exact ⟨rfl, rfl⟩
  | lam τ body ih =>
    intro b r r' h
    cases b <;> simp only [serE, List.cons_append, List.append_assoc, List.cons.injEq] at h <;>
      first | (exact absurd h.1 (by decide)) | skip
    obtain ⟨rfl, h₁⟩ := serTy_prefix _ _ _ _ h.2
    obtain ⟨rfl, rfl⟩ := ih _ _ _ h₁
    exact ⟨rfl, rfl⟩

theorem serTys_prefix : ∀ (a b : List HO.Ty) (r r' : List Nat), serTys a ++ r = serTys b ++ r' → a = b ∧ r = r'
  | [], [], _, _, h => by simpa [serTys] using h
  | [], _ :: _, _, _, h => by simp [serTys] at h
  | _ :: _, [], _, _, h => by simp [serTys] at h
  | τ :: a, σ :: b, r, r', h => by
    simp only [serTys, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h₁⟩ := serTy_prefix _ _ _ _ h
    obtain ⟨rfl, rfl⟩ := serTys_prefix a b r r' h₁
    exact ⟨rfl, rfl⟩

theorem serBodies_prefix : ∀ (a b : List HExp) (r r' : List Nat), serBodies a ++ r = serBodies b ++ r' →
    a = b ∧ r = r'
  | [], [], _, _, h => by simpa [serBodies] using h
  | [], _ :: _, _, _, h => by simp [serBodies] at h
  | _ :: _, [], _, _, h => by simp [serBodies] at h
  | e :: a, e' :: b, r, r', h => by
    simp only [serBodies, List.cons_append, List.append_assoc, List.cons.injEq, true_and] at h
    obtain ⟨rfl, h₁⟩ := serE_prefix _ _ _ _ h
    obtain ⟨rfl, rfl⟩ := serBodies_prefix a b r r' h₁
    exact ⟨rfl, rfl⟩

/-- Rules are determined by their types and their bodies. -/
theorem rules_ext : ∀ {rs rs' : List HRule}, rs.map HRule.ty = rs'.map HRule.ty →
    rs.map HRule.body = rs'.map HRule.body → rs = rs'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | ⟨τ, e⟩ :: rs, ⟨τ', e'⟩ :: rs', h₁, h₂ => by
    simp only [List.map_cons, List.cons.injEq] at h₁ h₂
    rw [h₁.1, h₂.1, rules_ext h₁.2 h₂.2]

/-- **The serialization is injective.** -/
theorem serIn_inj {g g' : HGrammar} {s s' : HExp} {x x' : List Char} (h : serIn g s x = serIn g' s' x') :
    g = g' ∧ s = s' ∧ x = x' := by
  obtain ⟨ht, h₁⟩ := serTys_prefix _ _ _ _ h
  obtain ⟨hb, h₂⟩ := serBodies_prefix _ _ _ _ h₁
  obtain ⟨rfl, h₃⟩ := serE_prefix _ _ _ _ h₂
  obtain ⟨rfl, -⟩ := serStr_prefix x x' [] [] (by simpa using h₃)
  have hr := rules_ext ht hb
  cases g; cases g'
  simp only at hr
  exact ⟨by rw [hr], rfl, rfl⟩

/-! ## Tokens are below 16 -/

theorem serNat_lt : ∀ (n : Nat), ∀ t ∈ serNat n, t < 16
  | 0, t, ht => by simp [serNat] at ht; omega
  | n + 1, t, ht => by
    simp only [serNat, List.mem_cons] at ht
    exact ht.elim (fun h => by omega) (serNat_lt n t)

theorem serStr_lt : ∀ (s : List Char), ∀ t ∈ serStr s, t < 16
  | [], t, ht => by simp [serStr] at ht; omega
  | c :: s, t, ht => by
    simp only [serStr, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serNat_lt _ t h
    · exact serStr_lt s t h

theorem serTy_lt : ∀ (τ : HO.Ty), ∀ t ∈ serTy τ, t < 16
  | .p, t, ht => by simp [serTy] at ht; omega
  | .arr a b, t, ht => by
    simp only [serTy, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serTy_lt a t h
    · exact serTy_lt b t h

theorem serE_lt : ∀ (e : HExp), ∀ t ∈ serE e, t < 16
  | .eps, t, ht | .any, t, ht => by simp [serE] at ht; omega
  | .chr _, t, ht | .lit _, t, ht | .var _, t, ht | .rule _, t, ht => by
    simp only [serE, serChar, List.mem_cons] at ht
    rcases ht with h | h
    · omega
    · first | exact serNat_lt _ t h | exact serStr_lt _ t h
  | .range _ _, t, ht => by
    simp only [serE, serChar, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serNat_lt _ t h
    · exact serNat_lt _ t h
  | .seq a b, t, ht | .alt a b, t, ht | .app a b, t, ht => by
    simp only [serE, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serE_lt a t h
    · exact serE_lt b t h
  | .star a, t, ht | .notP a, t, ht => by
    simp only [serE, List.mem_cons] at ht
    rcases ht with h | h
    · omega
    · exact serE_lt a t h
  | .lam τ b, t, ht => by
    simp only [serE, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serTy_lt τ t h
    · exact serE_lt b t h

theorem serTys_lt : ∀ (ts : List HO.Ty), ∀ t ∈ serTys ts, t < 16
  | [], t, ht => by simp [serTys] at ht; omega
  | τ :: ts, t, ht => by
    simp only [serTys, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serTy_lt _ t h
    · exact serTys_lt ts t h

theorem serBodies_lt : ∀ (es : List HExp), ∀ t ∈ serBodies es, t < 16
  | [], t, ht => by simp [serBodies] at ht; omega
  | e :: es, t, ht => by
    simp only [serBodies, List.mem_cons, List.mem_append] at ht
    rcases ht with h | h | h
    · omega
    · exact serE_lt _ t h
    · exact serBodies_lt es t h

theorem serIn_lt (g : HGrammar) (s : HExp) (x : List Char) : ∀ t ∈ serIn g s x, t < 16 := by
  intro t ht
  simp only [serIn, List.mem_append] at ht
  rcases ht with h | h | h | h
  · exact serTys_lt _ t h
  · exact serBodies_lt _ t h
  · exact serE_lt _ t h
  · exact serStr_lt _ t h

/-! ## The uniform problem -/

/-- Order `≤ j`: the rule types, and the lambdas in the bodies and the start (`lamOrd`). -/
def GOrd (j : Nat) (g : HGrammar) (s : HExp) : Prop :=
  g.order ≤ j ∧ (∀ r ∈ g.rules, lamOrd r.body ≤ j) ∧ lamOrd s ≤ j

/-- **The uniform recognition problem for order `j`**: the bits encode a well-typed grammar of order `≤ j` (its rule
types and its lambdas, `GOrd`), a closed start parser, and a string the grammar consumes. -/
def UMPEG (j : Nat) : Lang := fun bits => ∃ (g : HGrammar) (s : HExp) (x : List Char),
  ofBits bits = serIn g s x ∧ g.WellTyped ∧ GOrd j g s ∧ HasTy g.types [] s .p ∧ HObs g s x (some [])

/-- On an encoded instance, `UMPEG j` asks exactly the question about that instance. -/
theorem umpeg_toBits (j : Nat) (g : HGrammar) (s : HExp) (x : List Char) :
    UMPEG j (toBits (serIn g s x)) ↔
      g.WellTyped ∧ GOrd j g s ∧ HasTy g.types [] s .p ∧ HObs g s x (some []) := by
  unfold UMPEG
  rw [ofBits_toBits _ (serIn_lt g s x)]
  constructor
  · rintro ⟨g', s', x', h, hrest⟩
    obtain ⟨rfl, rfl, rfl⟩ := serIn_inj h
    exact hrest
  · intro h
    exact ⟨g, s, x, rfl, h⟩

end Shallot.MacroPeg.KExp
