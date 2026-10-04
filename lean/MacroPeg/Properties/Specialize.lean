import MacroPeg.Properties.FiniteArgs

/-!
# Finite specialization into an ordinary PEG (instructions.md §5.2, §5.4)

`FGrammar.specialize F A ks` is an ordinary `Grammar`: its rules are the env rules (same indices) followed by one rule per
admissible pair `(B, w) ∈ F.specs`, at index `|env| + code F B w`. The specialized rule of `(B, w)` is `B`'s body with the
constant vector `w` fixed (`FExp.spec`): `param j ↦ D[w[j]]`, `env i ↦ .nt i`, and a call `C(as)` becomes a reference to
the specialized rule of `(C, as resolved against w)`. The construction reads no input; recursion stays recursion (a rule
that calls itself with the same vector becomes a recursive PEG rule, not an unrolling).

Size (§5.4): the number of specialized rules is exactly `Σ_B |D| ^ arity(B)` (`length_specs`); the env rules are counted
separately and the entry adds no rule (its nonterminal is the specialized rule of `(A, ks)`). `|D| = 0` and arity `0` are
covered by `vecs` (`0 ^ 0 = 1`). Reference validity: under `WF`, every `.nt` inside the specialized grammar is in range.
-/

namespace Shallot.MacroPeg

open Shallot (PExp Grammar)

/-- The constant index an actual argument denotes under the constant vector `v`. -/
def FArg.resolve (v : List Nat) : FArg → Nat
  | .fwd j => v.getD j 0
  | .const k => k

/-- A body with the constant vector `v` fixed, as a plain PEG expression; a call `B(as)` becomes the nonterminal
`|env| + c B w` of the specialized rule of `(B, w)`, `w` the resolved argument vector. -/
def FExp.spec (F : FGrammar) (c : Nat → List Nat → Nat) (v : List Nat) : FExp → PExp
  | .eps => .eps
  | .any => .any
  | .chr ch => .chr ch
  | .range lo hi => .range lo hi
  | .lit s => .lit s
  | .param j =>
    match v[j]? with
    | some k => F.constP k
    | none => pFail
  | .env i => .nt i
  | .call B as => .nt (F.env.length + c B (as.map (FArg.resolve v)))
  | .seq e₁ e₂ => .seq (FExp.spec F c v e₁) (FExp.spec F c v e₂)
  | .alt e₁ e₂ => .alt (FExp.spec F c v e₁) (FExp.spec F c v e₂)
  | .star e => .star (FExp.spec F c v e)
  | .notP e => .notP (FExp.spec F c v e)

/-! ## Specialization over a chosen list of pairs

`specializeOn F S` specializes exactly the pairs listed in `S` (the specialized rule of `S[k]` is at index
`|env| + k`). The full specialization takes `S = F.specs`; the reachable one (`Reachable.lean`) takes the pairs reachable
from the entry. Correctness needs `S` to be a `SpecSet`: admissible pairs, closed under the calls of their bodies. -/

/-- The position of `(B, w)` in `S`. -/
def codeOn (S : List (Nat × List Nat)) (B : Nat) (w : List Nat) : Nat := indexIn (B, w) S

theorem FGrammar.code_eq_codeOn (F : FGrammar) : F.code = codeOn F.specs := rfl

def FGrammar.specRuleOn (F : FGrammar) (S : List (Nat × List Nat)) (q : Nat × List Nat) : PExp :=
  match F.rules[q.1]? with
  | some r => r.body.spec F (codeOn S) q.2
  | none => pFail

def FGrammar.specializeOn (F : FGrammar) (S : List (Nat × List Nat)) (A : Nat) (ks : List Nat) : Grammar :=
  ⟨F.env ++ S.map (F.specRuleOn S), F.env.length + codeOn S A ks⟩

/-- Every call of `e`, resolved against `v`, is listed in `S`. -/
def FExp.CallsIn (S : List (Nat × List Nat)) (v : List Nat) : FExp → Prop
  | .call B as => (B, as.map (FArg.resolve v)) ∈ S
  | .seq e₁ e₂ => FExp.CallsIn S v e₁ ∧ FExp.CallsIn S v e₂
  | .alt e₁ e₂ => FExp.CallsIn S v e₁ ∧ FExp.CallsIn S v e₂
  | .star e => FExp.CallsIn S v e
  | .notP e => FExp.CallsIn S v e
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .env _ => True

/-- A list of pairs that can be specialized on its own: admissible pairs, closed under the calls of their bodies. -/
def FGrammar.SpecSet (F : FGrammar) (S : List (Nat × List Nat)) : Prop :=
  (∀ q ∈ S, F.ValidVec q.1 q.2) ∧ ∀ B w r, (B, w) ∈ S → F.rules[B]? = some r → r.body.CallsIn S w

/-! ## The full specialization -/

/-- The specialized rule of a pair. -/
def FGrammar.specRule (F : FGrammar) (q : Nat × List Nat) : PExp := F.specRuleOn F.specs q

/-- The nonterminal of the entry `(A, ks)`. -/
def FGrammar.entryNt (F : FGrammar) (A : Nat) (ks : List Nat) : Nat := F.env.length + F.code A ks

/-- The specialized ordinary PEG (all admissible pairs). -/
def FGrammar.specialize (F : FGrammar) (A : Nat) (ks : List Nat) : Grammar := F.specializeOn F.specs A ks

theorem FGrammar.specialize_start (F : FGrammar) (A : Nat) (ks : List Nat) :
    (F.specialize A ks).start = F.entryNt A ks := rfl

/-! ## Size -/

theorem FGrammar.specializeOn_size (F : FGrammar) (S : List (Nat × List Nat)) (A : Nat) (ks : List Nat) :
    (F.specializeOn S A ks).rules.length = F.env.length + S.length := by
  simp [FGrammar.specializeOn]

/-- Exact size: env rules plus `Σ_B |D| ^ arity(B)` specialized rules. -/
theorem FGrammar.specialize_size (F : FGrammar) (A : Nat) (ks : List Nat) :
    (F.specialize A ks).rules.length = F.env.length + (F.rules.map (fun r => F.D.length ^ r.arity)).sum := by
  rw [FGrammar.specialize, F.specializeOn_size, FGrammar.length_specs]

/-- The bound of §5.4: the specialized (non-env) part has at most `Σ_B |D| ^ arity(B)` rules. -/
theorem FGrammar.specialize_size_le (F : FGrammar) (A : Nat) (ks : List Nat) :
    (F.specialize A ks).rules.length - F.env.length ≤ (F.rules.map (fun r => F.D.length ^ r.arity)).sum := by
  rw [F.specialize_size]; omega

/-! ## Rule lookup -/

theorem ruleAt_eq_getElem? : ∀ (l : List PExp) (i : Nat), Shallot.ruleAt l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, n + 1 => by simp [Shallot.ruleAt, ruleAt_eq_getElem? rs n]

theorem ruleAtM_eq_getElem? : ∀ (l : List MRule) (i : Nat), ruleAtM l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, n + 1 => by simp [ruleAtM, ruleAtM_eq_getElem? rs n]

theorem codeOn_getElem? {S : List (Nat × List Nat)} {B : Nat} {w : List Nat} (h : (B, w) ∈ S) :
    S[codeOn S B w]? = some (B, w) :=
  getElem?_indexIn _ _ h

theorem codeOn_lt {S : List (Nat × List Nat)} {B : Nat} {w : List Nat} (h : (B, w) ∈ S) : codeOn S B w < S.length :=
  (List.getElem?_eq_some_iff.1 (codeOn_getElem? h)).1

/-- Decoding: equal codes of listed pairs are equal pairs (the encoding is injective on `S`). -/
theorem codeOn_inj {S : List (Nat × List Nat)} {B B' : Nat} {w w' : List Nat} (h : (B, w) ∈ S) (h' : (B', w') ∈ S)
    (he : codeOn S B w = codeOn S B' w') : B = B' ∧ w = w' := by
  have := (codeOn_getElem? h).symm.trans (he ▸ codeOn_getElem? h')
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this

theorem FGrammar.ruleAt_specializeOn_env (F : FGrammar) (S : List (Nat × List Nat)) (A : Nat) (ks : List Nat)
    {i : Nat} {q : PExp} (h : F.env[i]? = some q) : Shallot.ruleAt (F.specializeOn S A ks).rules i = some q := by
  have hi : i < F.env.length := (List.getElem?_eq_some_iff.1 h).1
  rw [ruleAt_eq_getElem?, FGrammar.specializeOn, List.getElem?_append_left hi, h]

theorem FGrammar.ruleAt_specializeOn_spec (F : FGrammar) (S : List (Nat × List Nat)) (A : Nat) (ks : List Nat)
    {B : Nat} {w : List Nat} {r : FRule} (hr : F.rules[B]? = some r) (hm : (B, w) ∈ S) :
    Shallot.ruleAt (F.specializeOn S A ks).rules (F.env.length + codeOn S B w) =
      some (r.body.spec F (codeOn S) w) := by
  rw [ruleAt_eq_getElem?, FGrammar.specializeOn, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_map, codeOn_getElem? hm]
  simp [FGrammar.specRuleOn, hr]

/-- Decoding of the specialized grammar's nonterminals: an index is an env rule, or `|env| + k` with `S[k]` a listed
pair whose specialized rule sits there; nothing else is in range. -/
theorem FGrammar.specializeOn_decode (F : FGrammar) (S : List (Nat × List Nat)) (A : Nat) (ks : List Nat) (i : Nat)
    (hi : i < (F.specializeOn S A ks).rules.length) :
    (i < F.env.length ∧ Shallot.ruleAt (F.specializeOn S A ks).rules i = F.env[i]?) ∨
      ∃ k q, i = F.env.length + k ∧ S[k]? = some q ∧
        Shallot.ruleAt (F.specializeOn S A ks).rules i = some (F.specRuleOn S q) := by
  rw [F.specializeOn_size] at hi
  by_cases h : i < F.env.length
  · left; exact ⟨h, by rw [ruleAt_eq_getElem?, FGrammar.specializeOn, List.getElem?_append_left h]⟩
  · right
    have hk : i - F.env.length < S.length := by omega
    refine ⟨i - F.env.length, S[i - F.env.length], by omega, List.getElem?_eq_getElem hk, ?_⟩
    rw [ruleAt_eq_getElem?, FGrammar.specializeOn, List.getElem?_append_right (by omega), List.getElem?_map,
      List.getElem?_eq_getElem hk]
    rfl

theorem FGrammar.code_lt (F : FGrammar) {B : Nat} {w : List Nat} (hv : F.ValidVec B w) :
    F.code B w < F.specs.length :=
  codeOn_lt ((F.mem_specs B w).2 hv)

/-! ## Reference validity -/

theorem ntBounded_mono {n n' : Nat} (hle : n ≤ n') : ∀ (p : PExp), p.NtBounded n → p.NtBounded n'
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .nt _, h => Nat.lt_of_lt_of_le h hle
  | .seq a b, h => ⟨ntBounded_mono hle a h.1, ntBounded_mono hle b h.2⟩
  | .alt a b, h => ⟨ntBounded_mono hle a h.1, ntBounded_mono hle b h.2⟩
  | .star a, h => ntBounded_mono hle a h
  | .notP a, h => ntBounded_mono hle a h

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem getD_of_ge {α : Type} {l : List α} {i : Nat} (d : α) (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem pFail_ntBounded (n : Nat) : pFail.NtBounded n := ⟨⟩

theorem FGrammar.constP_ntBounded (F : FGrammar) (hF : F.WF) (k : Nat) : (F.constP k).NtBounded F.env.length := by
  unfold FGrammar.constP
  by_cases hk : k < F.D.length
  · rw [getD_of_lt _ hk]; exact hF.2.1 _ (List.getElem_mem hk)
  · rw [getD_of_ge _ (by omega)]; exact pFail_ntBounded _

/-- Resolving a well-formed argument against an admissible vector stays inside `D`. -/
theorem FArg.resolve_lt (F : FGrammar) {a : Nat} {v : List Nat} (hl : v.length = a)
    (hv : ∀ k ∈ v, k < F.D.length) : ∀ {x : FArg}, x.WF F a → x.resolve v < F.D.length
  | .fwd j, h => by
    simp only [FArg.resolve]
    rw [getD_of_lt _ (by simp only [FArg.WF] at h; omega)]
    exact hv _ (List.getElem_mem _)
  | .const _, h => h

/-- The call site `C(as)` of a well-formed body, resolved against an admissible vector, is an admissible pair. -/
theorem FGrammar.validVec_call (F : FGrammar) {a C : Nat} {as : List FArg} {v : List Nat} (hl : v.length = a)
    (hv : ∀ k ∈ v, k < F.D.length) (h : FExp.WF F a (.call C as)) : F.ValidVec C (as.map (FArg.resolve v)) := by
  obtain ⟨⟨r, hr, hlen⟩, hargs⟩ := h
  refine ⟨r, hr, by simp [hlen], ?_⟩
  intro k hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
  exact FArg.resolve_lt F hl hv (hargs x hx)

theorem FExp.spec_ntBounded (F : FGrammar) (hF : F.WF) (S : List (Nat × List Nat)) {v : List Nat} :
    ∀ (e : FExp), e.CallsIn S v → FExp.WF F v.length e →
      (e.spec F (codeOn S) v).NtBounded (F.env.length + S.length)
  | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => trivial
  | .param j, _, _ => by
    simp only [FExp.spec]
    split
    · exact ntBounded_mono (by omega) _ (F.constP_ntBounded hF _)
    · exact pFail_ntBounded _
  | .env i, _, h => by simp only [FExp.spec, PExp.NtBounded]; simp only [FExp.WF] at h; omega
  | .call _ _, hc, _ => by
    simp only [FExp.spec, PExp.NtBounded]
    have := codeOn_lt hc
    omega
  | .seq a b, hc, h => ⟨FExp.spec_ntBounded F hF S a hc.1 h.1, FExp.spec_ntBounded F hF S b hc.2 h.2⟩
  | .alt a b, hc, h => ⟨FExp.spec_ntBounded F hF S a hc.1 h.1, FExp.spec_ntBounded F hF S b hc.2 h.2⟩
  | .star a, hc, h => FExp.spec_ntBounded F hF S a hc h
  | .notP a, hc, h => FExp.spec_ntBounded F hF S a hc h

/-- Reference validity for any `SpecSet`: every `.nt` in every rule of the specialized grammar names an existing rule. -/
theorem FGrammar.specializeOn_selfContained (F : FGrammar) (hF : F.WF) {S : List (Nat × List Nat)}
    (hS : F.SpecSet S) (A : Nat) (ks : List Nat) :
    ∀ p ∈ (F.specializeOn S A ks).rules, p.NtBounded (F.specializeOn S A ks).rules.length := by
  rw [F.specializeOn_size]
  intro p hp
  simp only [FGrammar.specializeOn, List.mem_append, List.mem_map] at hp
  rcases hp with hp | ⟨⟨B, w⟩, hq, rfl⟩
  · exact ntBounded_mono (by omega) p (hF.1 p hp)
  · obtain ⟨r, hr, hl, _⟩ := hS.1 _ hq
    simp only [FGrammar.specRuleOn, hr]
    have hwf := hF.2.2 r (List.mem_of_getElem? hr)
    rw [← hl] at hwf
    exact FExp.spec_ntBounded F hF S _ (hS.2 B w r hq hr) hwf

/-- The calls of a well-formed body, resolved against an admissible vector, are admissible, hence listed in `specs`. -/
theorem FExp.callsIn_specs (F : FGrammar) {a : Nat} {v : List Nat} (hl : v.length = a)
    (hv : ∀ k ∈ v, k < F.D.length) : ∀ (e : FExp), e.WF F a → e.CallsIn F.specs v
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ | .env _, _ => trivial
  | .call _ _, h => (F.mem_specs _ _).2 (F.validVec_call hl hv h)
  | .seq a b, h => ⟨FExp.callsIn_specs F hl hv a h.1, FExp.callsIn_specs F hl hv b h.2⟩
  | .alt a b, h => ⟨FExp.callsIn_specs F hl hv a h.1, FExp.callsIn_specs F hl hv b h.2⟩
  | .star a, h => FExp.callsIn_specs F hl hv a h
  | .notP a, h => FExp.callsIn_specs F hl hv a h

/-- All admissible pairs form a `SpecSet` (for a well-formed grammar). -/
theorem FGrammar.specs_specSet (F : FGrammar) (hF : F.WF) : F.SpecSet F.specs := by
  refine ⟨fun q hq => (F.mem_specs q.1 q.2).1 hq, ?_⟩
  intro B w r hm hr
  obtain ⟨r', hr', hl, hk⟩ := (F.mem_specs B w).1 hm
  rw [hr] at hr'; cases hr'
  exact FExp.callsIn_specs F hl hk r.body (hF.2.2 r (List.mem_of_getElem? hr))

/-- Reference validity of the full specialization. -/
theorem FGrammar.specialize_selfContained (F : FGrammar) (hF : F.WF) (A : Nat) (ks : List Nat) :
    ∀ p ∈ (F.specialize A ks).rules, p.NtBounded (F.specialize A ks).rules.length :=
  F.specializeOn_selfContained hF (F.specs_specSet hF) A ks

/-- The entry nonterminal is in range when `(A, ks)` is admissible. -/
theorem FGrammar.entryNt_lt (F : FGrammar) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) :
    F.entryNt A ks < (F.specialize A ks).rules.length := by
  have := F.code_lt hv
  rw [FGrammar.specialize, F.specializeOn_size]
  simp only [FGrammar.entryNt]; omega

end Shallot.MacroPeg
