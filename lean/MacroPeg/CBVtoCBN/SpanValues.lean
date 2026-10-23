import MacroPeg.CBVtoCBN.SpanMatch
import MacroPeg.Properties.DecideCBV

namespace Shallot.MacroPeg.CBVtoCBN

/-- A finite, input-independent cover of Lean's character alphabet. Invalid codepoints only add duplicates. -/
def unicodeAlphabet : List Char := (List.range 0x110000).map Char.ofNat

theorem unicodeAlphabet_mem (c : Char) : c ∈ unicodeAlphabet := by
  have hv := c.valid
  change c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) at hv
  exact List.mem_map.mpr ⟨c.toNat, List.mem_range.mpr (by omega), Char.ofNat_toNat c⟩

/-- One fixed first-order grammar implements interval equality over all character inputs. -/
def spanGrammar : MGrammar := ⟨[⟨4, spanEqBody 0 unicodeAlphabet⟩]⟩

theorem spanGrammar_firstOrder : spanGrammar.FirstOrder := by
  intro rule hr
  have he : rule = ⟨4, spanEqBody 0 unicodeAlphabet⟩ := List.mem_singleton.mp hr
  subst rule
  exact spanEqBody_firstOrder 0 unicodeAlphabet

theorem spanGrammar_obs (x : List Char) (p q t u : Nat)
    (hpq : p ≤ q) (hqn : q ≤ x.length) (htu : t ≤ u) (hun : u ≤ x.length) :
    MacroObs spanGrammar (.call 0 [skipN p, skipN (x.length - q), skipN t, skipN (x.length - u)]) x
      (if spanSlice x p q = spanSlice x t u then some x else none) :=
  spanEq_obs rfl x (fun c _ => unicodeAlphabet_mem c) p q t u hpq hqn htu hun

theorem spanGrammar_iff (x : List Char) (p q t u : Nat)
    (hpq : p ≤ q) (hqn : q ≤ x.length) (htu : t ≤ u) (hun : u ≤ x.length) :
    MacroObs spanGrammar (.call 0 [skipN p, skipN (x.length - q), skipN t, skipN (x.length - u)]) x (some x) ↔
      spanSlice x p q = spanSlice x t u := test_success_iff _ (spanGrammar_obs x p q t u hpq hqn htu hun)

/-- The matcher accepts every expression representing the four lengths, independently of syntax shape. -/
theorem spanEq_rep_obs {g : MGrammar} (hg : g.FirstOrder) {self : Nat} {A : List Char}
    (hr : ruleAtM g.rules self = some ⟨4, spanEqBody self A⟩) (x : List Char) (hA : ∀ c ∈ x, c ∈ A)
    (p q t u : Nat) (hpq : p ≤ q) (hqn : q ≤ x.length) (htu : t ≤ u) (hun : u ≤ x.length)
    (a b c d : MExp) (ha : LenRep g a p) (hb : LenRep g b (x.length - q))
    (hc : LenRep g c t) (hd : LenRep g d (x.length - u)) :
    MacroObs g (.call self [a, b, c, d]) x (if spanSlice x p q = spanSlice x t u then some x else none) := by
  have hs : Sim g (.call self [skipN p, skipN (x.length - q), skipN t, skipN (x.length - u)])
      (.call self [a, b, c, d]) :=
    .node (.call self (.cons (.leaf ((skipN_rep g p).equiv ha))
      (.cons (.leaf ((skipN_rep g (x.length - q)).equiv hb))
        (.cons (.leaf ((skipN_rep g t).equiv hc))
          (.cons (.leaf ((skipN_rep g (x.length - u)).equiv hd)) .nil)))))
  exact sim_obs hg hs (spanEq_obs hr x hA p q t u hpq hqn htu hun)

theorem spanSlice_pre (x : List Char) (p j : Nat) (hp : p ≤ x.length) (hj : j ≤ p) :
    spanSlice x (x.length - p) (x.length - j) = pre x p j := by
  unfold spanSlice pre sfx
  congr 1
  omega

/-- Exact prefix matching determines the actual prefix, rather than only the existence of a suffix. -/
theorem stripPrefix_exact : ∀ (w input rest : List Char),
    Shallot.stripPrefix? w input = some rest ↔ input = w ++ rest
  | [], input, rest => by simp [Shallot.stripPrefix?]
  | c :: cs, [], rest => by simp [Shallot.stripPrefix?]
  | c :: cs, d :: ds, rest => by
    by_cases he : c = d
    · subst d
      simpa [Shallot.stripPrefix?, Shallot.beqChar] using stripPrefix_exact cs ds rest
    · simp [Shallot.stripPrefix?, Shallot.beqChar, Char.toNat_inj, he, Ne.symm he]

theorem pre_suffix_split (x : List Char) (q r : Nat) (hq : q ≤ x.length) (hr : r ≤ q) :
    sfx x q = pre x q r ++ sfx x r := by
  have he : (sfx x q).drop (q - r) = sfx x r := by
    unfold sfx
    rw [List.drop_drop]
    congr 1
    omega
  simpa only [pre, he] using (List.take_append_drop (q - r) (sfx x q)).symm

theorem pre_literal_iff (x : List Char) (p j q r : Nat) (hq : q ≤ x.length) (hr : r ≤ q) :
    Shallot.stripPrefix? (pre x p j) (sfx x q) = some (sfx x r) ↔ pre x p j = pre x q r := by
  rw [stripPrefix_exact]
  constructor
  · intro he
    exact List.append_cancel_right (he.symm.trans (pre_suffix_split x q r hq hr))
  · intro he
    rw [he]
    exact pre_suffix_split x q r hq hr

/-- The CBN interval representation implements precisely the literal value captured by CBV.
All positions are remaining-input lengths, as in `evV`; matching takes place at the unchanged original input root. -/
theorem capturedLiteral_iff (x : List Char) (p j q r : Nat)
    (hp : p ≤ x.length) (hj : j ≤ p) (hq : q ≤ x.length) (hr : r ≤ q) :
    MacroObs spanGrammar (.call 0 [skipN (x.length - p), skipN j, skipN (x.length - q), skipN r]) x (some x) ↔
      Shallot.stripPrefix? (pre x p j) (sfx x q) = some (sfx x r) := by
  have h := spanGrammar_iff x (x.length - p) (x.length - j) (x.length - q) (x.length - r)
    (by omega) (by omega) (by omega) (by omega)
  rw [show x.length - (x.length - j) = j by omega,
    show x.length - (x.length - r) = r by omega, spanSlice_pre x p j hp hj, spanSlice_pre x q r hq hr] at h
  exact h.trans (pre_literal_iff x p j q r hq hr).symm

end Shallot.MacroPeg.CBVtoCBN
