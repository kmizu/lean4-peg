import MacroPeg.CBVtoCBN.Control

namespace Shallot.MacroPeg.CBVtoCBN

/-- Grow a closed counter until it denotes the whole input length, then pass it to a fixed rule. -/
def findLengthBody (self next : Nat) : MExp :=
  ifP (exactLengthP (.param 0)) (.call next [.param 0])
    (.call self [.seq (.param 0) .any])

theorem findLengthBody_firstOrder (self next : Nat) : (findLengthBody self next).FirstOrder := by
  exact ifP_firstOrder ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨⟨trivial, trivial⟩, trivial⟩

theorem findLength_step {g : MGrammar} {self next : Nat}
    (hr : ruleAtM g.rules self = some ⟨1, findLengthBody self next⟩)
    (x : List Char) (k : Nat) (r : Option (List Char)) :
    MacroObs g (.call self [skipN k]) x r ↔
      if k = x.length then MacroObs g (.call next [skipN k]) x r
      else MacroObs g (.call self [skipN (k + 1)]) x r := by
  rw [obs_call_iff hr (by rfl)]
  change MacroObs g (ifP (exactLengthP (skipN k)) (.call next [skipN k])
    (.call self [skipN (k + 1)])) x r ↔ _
  have ht := exactLength_obs (skipN_rep g k) x
  by_cases hk : k = x.length
  · rw [if_pos hk] at ht ⊢
    exact ifP_true_iff ht r
  · rw [if_neg hk] at ht ⊢
    exact ifP_false_iff ht r

/-- Length discovery is a finite CBN computation on every input, preserving all observations of the continuation. -/
theorem findLength_iff {g : MGrammar} {self next : Nat}
    (hr : ruleAtM g.rules self = some ⟨1, findLengthBody self next⟩)
    (x : List Char) (k : Nat) (hk : k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call self [skipN k]) x r ↔ MacroObs g (.call next [skipN x.length]) x r := by
  have aux : ∀ d k, k + d = x.length →
      (MacroObs g (.call self [skipN k]) x r ↔ MacroObs g (.call next [skipN x.length]) x r) := by
    intro d
    induction d with
    | zero =>
      intro k h
      have he : k = x.length := by omega
      rw [findLength_step hr, if_pos he, he]
    | succ d ih =>
      intro k h
      have he : k ≠ x.length := by omega
      rw [findLength_step hr, if_neg he]
      exact ih (k + 1) (by omega)
  exact aux (x.length - k) k (by omega)

/-- An already constructed length counter can also enter the discovery rule; no tree-shape assumption is needed. -/
theorem findLength_rep_iff {g : MGrammar} (hg : g.FirstOrder) {self next : Nat}
    (hr : ruleAtM g.rules self = some ⟨1, findLengthBody self next⟩)
    {counter : MExp} {k : Nat} (hc : LenRep g counter k)
    (x : List Char) (hk : k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call self [counter]) x r ↔ MacroObs g (.call next [skipN x.length]) x r :=
  (call_len_equiv hg self hc (skipN_rep g k) x r).trans (findLength_iff hr x k hk r)

/-- Search for a counter complementary to a fixed input position. Both counters are parser-valued arguments. -/
def findComplementBody (self next : Nat) : MExp :=
  ifP (exactLengthP (.seq (.param 0) (.param 1))) (.call next [.param 0, .param 1])
    (.call self [.param 0, .seq (.param 1) .any])

theorem findComplementBody_firstOrder (self next : Nat) : (findComplementBody self next).FirstOrder := by
  exact ifP_firstOrder ⟨⟨trivial, trivial⟩, trivial⟩ ⟨trivial, trivial, trivial⟩
    ⟨trivial, ⟨trivial, trivial⟩, trivial⟩

theorem findComplement_step {g : MGrammar} {self next : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, findComplementBody self next⟩)
    (x : List Char) (p k : Nat) (r : Option (List Char)) :
    MacroObs g (.call self [skipN p, skipN k]) x r ↔
      if p + k = x.length then MacroObs g (.call next [skipN p, skipN k]) x r
      else MacroObs g (.call self [skipN p, skipN (k + 1)]) x r := by
  rw [obs_call_iff hr (by rfl)]
  change MacroObs g (ifP (exactLengthP (.seq (skipN p) (skipN k))) (.call next [skipN p, skipN k])
    (.call self [skipN p, skipN (k + 1)])) x r ↔ _
  have ht := exactLength_obs ((skipN_rep g p).seq (skipN_rep g k)) x
  by_cases hk : p + k = x.length
  · rw [if_pos hk] at ht ⊢
    exact ifP_true_iff ht r
  · rw [if_neg hk] at ht ⊢
    exact ifP_false_iff ht r

/-- Complement search keeps the original input and yields a frozen counter of length `n-p`.
Its guard is total, so continuation failure cannot fall through into another search iteration. -/
theorem findComplement_iff {g : MGrammar} {self next : Nat}
    (hr : ruleAtM g.rules self = some ⟨2, findComplementBody self next⟩)
    (x : List Char) (p k : Nat) (hk : p + k ≤ x.length) (r : Option (List Char)) :
    MacroObs g (.call self [skipN p, skipN k]) x r ↔
      MacroObs g (.call next [skipN p, skipN (x.length - p)]) x r := by
  have aux : ∀ d k, p + k + d = x.length →
      (MacroObs g (.call self [skipN p, skipN k]) x r ↔
        MacroObs g (.call next [skipN p, skipN (x.length - p)]) x r) := by
    intro d
    induction d with
    | zero =>
      intro k h
      have he : p + k = x.length := by omega
      have hk' : k = x.length - p := by omega
      rw [findComplement_step hr, if_pos he, hk']
    | succ d ih =>
      intro k h
      have he : p + k ≠ x.length := by omega
      rw [findComplement_step hr, if_neg he]
      exact ih (k + 1) (by omega)
  exact aux (x.length - (p + k)) k (by omega)

/-- A concrete two-rule wrapper turns length discovery into a first-order CBN grammar. -/
def lengthWrapper (body : MExp) : MGrammar :=
  ⟨[⟨1, findLengthBody 0 1⟩, ⟨1, body⟩]⟩

theorem lengthWrapper_firstOrder {body : MExp} (hb : body.FirstOrder) : (lengthWrapper body).FirstOrder := by
  intro rule hr
  simp only [lengthWrapper, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact findLengthBody_firstOrder 0 1
  · exact hb

theorem lengthWrapper_obs (body : MExp) (x : List Char) (r : Option (List Char)) :
    MacroObs (lengthWrapper body) (.call 0 [.eps]) x r ↔
      MacroObs (lengthWrapper body) (MExp.subst [skipN x.length] body) x r := by
  have h := findLength_iff (g := lengthWrapper body) (self := 0) (next := 1) rfl x 0 (by omega) r
  exact h.trans (obs_call_iff (g := lengthWrapper body) (i := 1)
    (args := [skipN x.length]) (rule := ⟨1, body⟩) rfl rfl x r)

end Shallot.MacroPeg.CBVtoCBN
