import Shallot.Peg.Semantics

/-!
# Derivations with a height bound

`DH g n e x o` is `Derives g e x o` with a derivation of height at most `n`: every rule concludes at `n + 1` from
premises at `n`. Heights make "a derivation cannot contain a strictly smaller derivation of the same judgment"
usable as an infinite-descent argument. `DH` is monotone in `n` (`dh_mono_le`) and has exactly the judgments of
`Derives` (`dh_derives`, `derives_dh`).
-/

namespace Shallot

inductive DH (g : Grammar) : Nat → PExp → List Char → Outcome → Prop where
  | eps (n : Nat) (input : List Char) : DH g (n + 1) .eps input (.ok (.leaf []) input)
  | anyOk (n : Nat) (c : Char) (rest : List Char) : DH g (n + 1) .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail (n : Nat) : DH g (n + 1) .any [] .fail
  | chrOk (n : Nat) (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      DH g (n + 1) (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (n : Nat) (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      DH g (n + 1) (.chr c) (d :: rest) .fail
  | chrEmpty (n : Nat) (c : Char) : DH g (n + 1) (.chr c) [] .fail
  | rangeOk (n : Nat) (lo hi d : Char) (rest : List Char) (h : (leChar lo d && leChar d hi) = true) :
      DH g (n + 1) (.range lo hi) (d :: rest) (.ok (.leaf [d]) rest)
  | rangeFail (n : Nat) (lo hi d : Char) (rest : List Char) (h : (leChar lo d && leChar d hi) = false) :
      DH g (n + 1) (.range lo hi) (d :: rest) .fail
  | rangeEmpty (n : Nat) (lo hi : Char) : DH g (n + 1) (.range lo hi) [] .fail
  | litOk (n : Nat) (s input rest : List Char) (h : stripPrefix? s input = some rest) :
      DH g (n + 1) (.lit s) input (.ok (.leaf s) rest)
  | litFail (n : Nat) (s input : List Char) (h : stripPrefix? s input = none) : DH g (n + 1) (.lit s) input .fail
  | ntOk (n : Nat) (i : Nat) (e : PExp) (input rest : List Char) (t : PTree) (hr : ruleAt g.rules i = some e)
      (hd : DH g n e input (.ok t rest)) : DH g (n + 1) (.nt i) input (.ok (.nodeNT i t) rest)
  | ntFail (n : Nat) (i : Nat) (e : PExp) (input : List Char) (hr : ruleAt g.rules i = some e)
      (hd : DH g n e input .fail) : DH g (n + 1) (.nt i) input .fail
  | ntMissing (n : Nat) (i : Nat) (input : List Char) (hr : ruleAt g.rules i = none) :
      DH g (n + 1) (.nt i) input .fail
  | seqOk (n : Nat) (e₁ e₂ : PExp) (input rest₁ rest₂ : List Char) (t₁ t₂ : PTree)
      (h₁ : DH g n e₁ input (.ok t₁ rest₁)) (h₂ : DH g n e₂ rest₁ (.ok t₂ rest₂)) :
      DH g (n + 1) (.seq e₁ e₂) input (.ok (.seq t₁ t₂) rest₂)
  | seqFail₁ (n : Nat) (e₁ e₂ : PExp) (input : List Char) (h₁ : DH g n e₁ input .fail) :
      DH g (n + 1) (.seq e₁ e₂) input .fail
  | seqFail₂ (n : Nat) (e₁ e₂ : PExp) (input rest₁ : List Char) (t₁ : PTree)
      (h₁ : DH g n e₁ input (.ok t₁ rest₁)) (h₂ : DH g n e₂ rest₁ .fail) : DH g (n + 1) (.seq e₁ e₂) input .fail
  | altL (n : Nat) (e₁ e₂ : PExp) (input rest : List Char) (t : PTree) (h : DH g n e₁ input (.ok t rest)) :
      DH g (n + 1) (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (n : Nat) (e₁ e₂ : PExp) (input rest : List Char) (t : PTree) (h₁ : DH g n e₁ input .fail)
      (h₂ : DH g n e₂ input (.ok t rest)) : DH g (n + 1) (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (n : Nat) (e₁ e₂ : PExp) (input : List Char) (h₁ : DH g n e₁ input .fail)
      (h₂ : DH g n e₂ input .fail) : DH g (n + 1) (.alt e₁ e₂) input .fail
  | starNil (n : Nat) (e : PExp) (input : List Char) (h : DH g n e input .fail) :
      DH g (n + 1) (.star e) input (.ok .starNil input)
  | starCons (n : Nat) (e : PExp) (input rest rest' : List Char) (t ts : PTree)
      (h₁ : DH g n e input (.ok t rest)) (h₂ : DH g n (.star e) rest (.ok ts rest')) :
      DH g (n + 1) (.star e) input (.ok (.starCons t ts) rest')
  | notOk (n : Nat) (e : PExp) (input rest : List Char) (t : PTree) (h : DH g n e input (.ok t rest)) :
      DH g (n + 1) (.notP e) input .fail
  | notFail (n : Nat) (e : PExp) (input : List Char) (h : DH g n e input .fail) :
      DH g (n + 1) (.notP e) input (.ok .notT input)

/-- A height-bounded derivation is a derivation. -/
theorem dh_derives {g : Grammar} {n : Nat} {e : PExp} {x : List Char} {o : Outcome} (h : DH g n e x o) :
    Derives g e x o := by
  induction h with
  | eps => exact .eps _
  | anyOk => exact .anyOk _ _
  | anyFail => exact .anyFail
  | chrOk _ _ _ _ h => exact .chrOk _ _ _ h
  | chrFail _ _ _ _ h => exact .chrFail _ _ _ h
  | chrEmpty => exact .chrEmpty _
  | rangeOk _ _ _ _ _ h => exact .rangeOk _ _ _ _ h
  | rangeFail _ _ _ _ _ h => exact .rangeFail _ _ _ _ h
  | rangeEmpty => exact .rangeEmpty _ _
  | litOk _ _ _ _ h => exact .litOk _ _ _ h
  | litFail _ _ _ h => exact .litFail _ _ h
  | ntOk _ _ _ _ _ _ hr _ ih => exact .ntOk _ _ _ _ _ hr ih
  | ntFail _ _ _ _ hr _ ih => exact .ntFail _ _ _ hr ih
  | ntMissing _ _ _ hr => exact .ntMissing _ _ hr
  | seqOk _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqOk _ _ _ _ _ _ _ ih₁ ih₂
  | seqFail₁ _ _ _ _ _ ih => exact .seqFail₁ _ _ _ ih
  | seqFail₂ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqFail₂ _ _ _ _ _ ih₁ ih₂
  | altL _ _ _ _ _ _ _ ih => exact .altL _ _ _ _ _ ih
  | altR _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .altR _ _ _ _ _ ih₁ ih₂
  | altFail _ _ _ _ _ _ ih₁ ih₂ => exact .altFail _ _ _ ih₁ ih₂
  | starNil _ _ _ _ ih => exact .starNil _ _ ih
  | starCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .starCons _ _ _ _ _ _ ih₁ ih₂
  | notOk _ _ _ _ _ _ ih => exact .notOk _ _ _ _ ih
  | notFail _ _ _ _ ih => exact .notFail _ _ ih

/-- Raising the height bound by one. -/
theorem dh_succ {g : Grammar} {n : Nat} {e : PExp} {x : List Char} {o : Outcome} (h : DH g n e x o) :
    DH g (n + 1) e x o := by
  induction h with
  | eps => exact .eps _ _
  | anyOk => exact .anyOk _ _ _
  | anyFail => exact .anyFail _
  | chrOk _ _ _ _ h => exact .chrOk _ _ _ _ h
  | chrFail _ _ _ _ h => exact .chrFail _ _ _ _ h
  | chrEmpty => exact .chrEmpty _ _
  | rangeOk _ _ _ _ _ h => exact .rangeOk _ _ _ _ _ h
  | rangeFail _ _ _ _ _ h => exact .rangeFail _ _ _ _ _ h
  | rangeEmpty => exact .rangeEmpty _ _ _
  | litOk _ _ _ _ h => exact .litOk _ _ _ _ h
  | litFail _ _ _ h => exact .litFail _ _ _ h
  | ntOk _ _ _ _ _ _ hr _ ih => exact .ntOk _ _ _ _ _ _ hr ih
  | ntFail _ _ _ _ hr _ ih => exact .ntFail _ _ _ _ hr ih
  | ntMissing _ _ _ hr => exact .ntMissing _ _ _ hr
  | seqOk _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqOk _ _ _ _ _ _ _ _ ih₁ ih₂
  | seqFail₁ _ _ _ _ _ ih => exact .seqFail₁ _ _ _ _ ih
  | seqFail₂ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqFail₂ _ _ _ _ _ _ ih₁ ih₂
  | altL _ _ _ _ _ _ _ ih => exact .altL _ _ _ _ _ _ ih
  | altR _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .altR _ _ _ _ _ _ ih₁ ih₂
  | altFail _ _ _ _ _ _ ih₁ ih₂ => exact .altFail _ _ _ _ ih₁ ih₂
  | starNil _ _ _ _ ih => exact .starNil _ _ _ ih
  | starCons _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .starCons _ _ _ _ _ _ _ ih₁ ih₂
  | notOk _ _ _ _ _ _ ih => exact .notOk _ _ _ _ _ ih
  | notFail _ _ _ _ ih => exact .notFail _ _ _ ih

/-- Raising the height bound. -/
theorem dh_mono_le {g : Grammar} {n m : Nat} {e : PExp} {x : List Char} {o : Outcome} (h : DH g n e x o)
    (hnm : n ≤ m) : DH g m e x o := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · exact dh_succ (ih (by omega))
    · have : n = m + 1 := by omega
      subst this; exact h

/-- Every derivation has a height bound. -/
theorem derives_dh {g : Grammar} {e : PExp} {x : List Char} {o : Outcome} (h : Derives g e x o) :
    ∃ n, DH g n e x o := by
  induction h with
  | eps => exact ⟨1, .eps 0 _⟩
  | anyOk => exact ⟨1, .anyOk 0 _ _⟩
  | anyFail => exact ⟨1, .anyFail 0⟩
  | chrOk _ _ _ h => exact ⟨1, .chrOk 0 _ _ _ h⟩
  | chrFail _ _ _ h => exact ⟨1, .chrFail 0 _ _ _ h⟩
  | chrEmpty => exact ⟨1, .chrEmpty 0 _⟩
  | rangeOk _ _ _ _ h => exact ⟨1, .rangeOk 0 _ _ _ _ h⟩
  | rangeFail _ _ _ _ h => exact ⟨1, .rangeFail 0 _ _ _ _ h⟩
  | rangeEmpty => exact ⟨1, .rangeEmpty 0 _ _⟩
  | litOk _ _ _ h => exact ⟨1, .litOk 0 _ _ _ h⟩
  | litFail _ _ h => exact ⟨1, .litFail 0 _ _ h⟩
  | ntOk _ _ _ _ _ hr _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .ntOk _ _ _ _ _ _ hr h⟩
  | ntFail _ _ _ hr _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .ntFail _ _ _ _ hr h⟩
  | ntMissing _ _ hr => exact ⟨1, .ntMissing 0 _ _ hr⟩
  | seqOk _ _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, .seqOk _ _ _ _ _ _ _ _ (dh_mono_le h₁ (by omega)) (dh_mono_le h₂ (by omega))⟩
  | seqFail₁ _ _ _ _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .seqFail₁ _ _ _ _ h⟩
  | seqFail₂ _ _ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, .seqFail₂ _ _ _ _ _ _ (dh_mono_le h₁ (by omega)) (dh_mono_le h₂ (by omega))⟩
  | altL _ _ _ _ _ _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .altL _ _ _ _ _ _ h⟩
  | altR _ _ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, .altR _ _ _ _ _ _ (dh_mono_le h₁ (by omega)) (dh_mono_le h₂ (by omega))⟩
  | altFail _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, .altFail _ _ _ _ (dh_mono_le h₁ (by omega)) (dh_mono_le h₂ (by omega))⟩
  | starNil _ _ _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .starNil _ _ _ h⟩
  | starCons _ _ _ _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    exact ⟨max n₁ n₂ + 1, .starCons _ _ _ _ _ _ _ (dh_mono_le h₁ (by omega)) (dh_mono_le h₂ (by omega))⟩
  | notOk _ _ _ _ _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .notOk _ _ _ _ _ h⟩
  | notFail _ _ _ ih =>
    obtain ⟨n, h⟩ := ih; exact ⟨n + 1, .notFail _ _ _ h⟩

end Shallot
