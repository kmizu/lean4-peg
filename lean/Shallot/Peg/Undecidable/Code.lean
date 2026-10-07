import Shallot.Peg.Syntax
import Complexity.Univ.Code

/-!
# Grammars as bits

An expression is written in prefix form as numbers (`serE`): a tag, then the characters' code points or the index,
then the subexpressions. A grammar is its start, its number of rules and its rules (`serG`), and its bits are these
numbers in unary (`encG`). The code is prefix-free (`serE_prefix`), so grammars are determined by their bits
(`encG_inj`).
-/

namespace Shallot

/-- A string of characters as numbers, with its length first. -/
def serStrN (s : List Char) : List Nat := s.length :: s.map Char.toNat

/-- An expression in prefix form. -/
def serE : PExp → List Nat
  | .eps => [0]
  | .any => [1]
  | .chr c => [2, c.toNat]
  | .range lo hi => [3, lo.toNat, hi.toNat]
  | .lit s => 4 :: serStrN s
  | .nt i => [5, i]
  | .seq a b => 6 :: (serE a ++ serE b)
  | .alt a b => 7 :: (serE a ++ serE b)
  | .star a => 8 :: serE a
  | .notP a => 9 :: serE a

/-- A grammar: its start, its number of rules, its rules. -/
def serG (g : Grammar) : List Nat := g.start :: g.rules.length :: (g.rules.map serE).flatten

/-- **The bits of a grammar.** -/
def encG (g : Grammar) : List Bool := Complexity.Univ.unary (serG g)

theorem toNat_inj {c d : Char} (h : c.toNat = d.toNat) : c = d := by
  have := congrArg Char.ofNat h; simpa using this

theorem map_toNat_prefix : ∀ {s t : List Char} {r r' : List Nat}, s.length = t.length →
    s.map Char.toNat ++ r = t.map Char.toNat ++ r' → s = t ∧ r = r'
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | c :: s, d :: t, r, r', hl, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    have := map_toNat_prefix (s := s) (t := t) (by simpa using hl) h.2
    exact ⟨by rw [toNat_inj h.1, this.1], this.2⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- **The prefix form is prefix-free.** -/
theorem serE_prefix : ∀ (e e' : PExp) (r r' : List Nat), serE e ++ r = serE e' ++ r' → e = e' ∧ r = r'
  | .eps, e', r, r', h => by cases e' <;> simp_all [serE]
  | .any, e', r, r', h => by cases e' <;> simp_all [serE]
  | .chr c, e', r, r', h => by
    cases e' <;> simp_all [serE]
    exact toNat_inj h.1
  | .range lo hi, e', r, r', h => by
    cases e' <;> simp_all [serE]
    exact ⟨toNat_inj h.1, toNat_inj h.2.1⟩
  | .lit s, e', r, r', h => by
    cases e' with
    | lit t =>
      simp only [serE, serStrN, List.cons_append, List.cons.injEq, true_and] at h
      have := map_toNat_prefix h.1 h.2
      exact ⟨by rw [this.1], this.2⟩
    | _ => simp_all [serE]
  | .nt i, e', r, r', h => by cases e' <;> simp_all [serE]
  | .seq a b, e', r, r', h => by
    cases e' with
    | seq a' b' =>
      simp only [serE, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h₁⟩ := serE_prefix a a' _ _ h
      obtain ⟨rfl, h₂⟩ := serE_prefix b b' _ _ h₁
      exact ⟨rfl, h₂⟩
    | _ => simp_all [serE]
  | .alt a b, e', r, r', h => by
    cases e' with
    | alt a' b' =>
      simp only [serE, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h₁⟩ := serE_prefix a a' _ _ h
      obtain ⟨rfl, h₂⟩ := serE_prefix b b' _ _ h₁
      exact ⟨rfl, h₂⟩
    | _ => simp_all [serE]
  | .star a, e', r, r', h => by
    cases e' with
    | star a' =>
      simp only [serE, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h₁⟩ := serE_prefix a a' _ _ h
      exact ⟨rfl, h₁⟩
    | _ => simp_all [serE]
  | .notP a, e', r, r', h => by
    cases e' with
    | notP a' =>
      simp only [serE, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h₁⟩ := serE_prefix a a' _ _ h
      exact ⟨rfl, h₁⟩
    | _ => simp_all [serE]

theorem serRules_prefix : ∀ (l l' : List PExp), l.length = l'.length →
    (l.map serE).flatten = (l'.map serE).flatten → l = l'
  | [], [], _, _ => rfl
  | e :: l, e' :: l', hl, h => by
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨rfl, h₁⟩ := serE_prefix e e' _ _ h
    rw [serRules_prefix l l' (by simpa using hl) h₁]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **Grammars are determined by their bits.** -/
theorem encG_inj {g g' : Grammar} (h : encG g = encG g') : g = g' := by
  have h₁ : serG g = serG g' := by
    have := congrArg Complexity.Univ.deUnary h
    simpa [encG, Complexity.Univ.deUnary_unary] using this
  simp only [serG, List.cons.injEq] at h₁
  obtain ⟨hs, hl, hr⟩ := h₁
  have := serRules_prefix g.rules g'.rules hl hr
  cases g; cases g'
  simp_all

theorem serRules_prefix' : ∀ (l l' : List PExp) (r r' : List Nat), l.length = l'.length →
    (l.map serE).flatten ++ r = (l'.map serE).flatten ++ r' → l = l' ∧ r = r'
  | [], [], r, r', _, h => ⟨rfl, by simpa using h⟩
  | e :: l, e' :: l', r, r', hl, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h₁⟩ := serE_prefix e e' _ _ h
    obtain ⟨rfl, h₂⟩ := serRules_prefix' l l' r r' (by simpa using hl) h₁
    exact ⟨rfl, h₂⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- **The code of a grammar is prefix-free.** -/
theorem serG_prefix {g g' : Grammar} {r r' : List Nat} (h : serG g ++ r = serG g' ++ r') : g = g' ∧ r = r' := by
  simp only [serG, List.cons_append, List.cons.injEq] at h
  obtain ⟨hs, hl, hr⟩ := h
  obtain ⟨hrules, hrest⟩ := serRules_prefix' g.rules g'.rules r r' hl hr
  cases g; cases g'
  simp_all

theorem unary_append (a b : List Nat) : Complexity.Univ.unary (a ++ b) =
    Complexity.Univ.unary a ++ Complexity.Univ.unary b := by
  simp [Complexity.Univ.unary]

/-- **Pairs of grammars are determined by their bits.** -/
theorem encG_pair_inj {g h g' h' : Grammar} (e : encG g ++ encG h = encG g' ++ encG h') : g = g' ∧ h = h' := by
  have e₁ : serG g ++ serG h = serG g' ++ serG h' := by
    have := congrArg Complexity.Univ.deUnary e
    simpa [encG, ← unary_append, Complexity.Univ.deUnary_unary] using this
  obtain ⟨rfl, e₂⟩ := serG_prefix e₁
  exact ⟨rfl, by
    have := congrArg (fun l => Complexity.Univ.unary l) e₂
    exact encG_inj (by simpa [encG] using this)⟩

end Shallot
