import Shallot.Peg.Determinism
import Shallot.Peg.Props
import Shallot.Peg.Total.Mask
import Shallot.Peg.Total.Height

/-!
# Derivations with the run-time circularity check

`DS g S e x o` is `Derives g e x o` where `S` (a bit mask, `Mask.lean`) is the set of nonterminals open at the
current position `x`: a call of `A ∈ S` has no rule (it is a loop), a call of `A ∉ S` evaluates the body with `A`
added, and once input is consumed the set resets to `∅` (`nx`). A repetition step must consume
(`starCons` has `rest ≠ input`).

* `ds_derives`: a checked derivation is a derivation (forget `S`), hence `ds_det`.
* `derives_ds`: conversely a derivation is a checked one for any `S` whose members are *open callers* (`Inv`):
  every derivation of `A ∈ S` at `x` contains a strictly lower derivation of the current expression at `x`.
  A call of `A ∈ S` then would give an infinitely descending chain of heights (`no_self`).
-/

namespace Shallot

/-- The open set after a step from `x` to `r`: unchanged without consumption, empty otherwise. -/
def nx (S : Nat) (x r : List Char) : Nat := if r = x then S else 0

inductive DS (g : Grammar) : Nat → PExp → List Char → Outcome → Prop where
  | eps (S : Nat) (input : List Char) : DS g S .eps input (.ok (.leaf []) input)
  | anyOk (S : Nat) (c : Char) (rest : List Char) : DS g S .any (c :: rest) (.ok (.leaf [c]) rest)
  | anyFail (S : Nat) : DS g S .any [] .fail
  | chrOk (S : Nat) (c d : Char) (rest : List Char) (h : beqChar c d = true) :
      DS g S (.chr c) (d :: rest) (.ok (.leaf [d]) rest)
  | chrFail (S : Nat) (c d : Char) (rest : List Char) (h : beqChar c d = false) :
      DS g S (.chr c) (d :: rest) .fail
  | chrEmpty (S : Nat) (c : Char) : DS g S (.chr c) [] .fail
  | rangeOk (S : Nat) (lo hi d : Char) (rest : List Char) (h : (leChar lo d && leChar d hi) = true) :
      DS g S (.range lo hi) (d :: rest) (.ok (.leaf [d]) rest)
  | rangeFail (S : Nat) (lo hi d : Char) (rest : List Char) (h : (leChar lo d && leChar d hi) = false) :
      DS g S (.range lo hi) (d :: rest) .fail
  | rangeEmpty (S : Nat) (lo hi : Char) : DS g S (.range lo hi) [] .fail
  | litOk (S : Nat) (s input rest : List Char) (h : stripPrefix? s input = some rest) :
      DS g S (.lit s) input (.ok (.leaf s) rest)
  | litFail (S : Nat) (s input : List Char) (h : stripPrefix? s input = none) : DS g S (.lit s) input .fail
  | ntOk (S : Nat) (i : Nat) (e : PExp) (input rest : List Char) (t : PTree) (hr : ruleAt g.rules i = some e)
      (hm : S.testBit i = false) (hd : DS g (ins S i) e input (.ok t rest)) :
      DS g S (.nt i) input (.ok (.nodeNT i t) rest)
  | ntFail (S : Nat) (i : Nat) (e : PExp) (input : List Char) (hr : ruleAt g.rules i = some e)
      (hm : S.testBit i = false) (hd : DS g (ins S i) e input .fail) : DS g S (.nt i) input .fail
  | ntMissing (S : Nat) (i : Nat) (input : List Char) (hr : ruleAt g.rules i = none) : DS g S (.nt i) input .fail
  | seqOk (S : Nat) (e₁ e₂ : PExp) (input rest₁ rest₂ : List Char) (t₁ t₂ : PTree)
      (h₁ : DS g S e₁ input (.ok t₁ rest₁)) (h₂ : DS g (nx S input rest₁) e₂ rest₁ (.ok t₂ rest₂)) :
      DS g S (.seq e₁ e₂) input (.ok (.seq t₁ t₂) rest₂)
  | seqFail₁ (S : Nat) (e₁ e₂ : PExp) (input : List Char) (h₁ : DS g S e₁ input .fail) :
      DS g S (.seq e₁ e₂) input .fail
  | seqFail₂ (S : Nat) (e₁ e₂ : PExp) (input rest₁ : List Char) (t₁ : PTree)
      (h₁ : DS g S e₁ input (.ok t₁ rest₁)) (h₂ : DS g (nx S input rest₁) e₂ rest₁ .fail) :
      DS g S (.seq e₁ e₂) input .fail
  | altL (S : Nat) (e₁ e₂ : PExp) (input rest : List Char) (t : PTree) (h : DS g S e₁ input (.ok t rest)) :
      DS g S (.alt e₁ e₂) input (.ok (.choiceL t) rest)
  | altR (S : Nat) (e₁ e₂ : PExp) (input rest : List Char) (t : PTree) (h₁ : DS g S e₁ input .fail)
      (h₂ : DS g S e₂ input (.ok t rest)) : DS g S (.alt e₁ e₂) input (.ok (.choiceR t) rest)
  | altFail (S : Nat) (e₁ e₂ : PExp) (input : List Char) (h₁ : DS g S e₁ input .fail)
      (h₂ : DS g S e₂ input .fail) : DS g S (.alt e₁ e₂) input .fail
  | starNil (S : Nat) (e : PExp) (input : List Char) (h : DS g S e input .fail) :
      DS g S (.star e) input (.ok .starNil input)
  | starCons (S : Nat) (e : PExp) (input rest rest' : List Char) (t ts : PTree)
      (h₁ : DS g S e input (.ok t rest)) (hne : rest ≠ input) (h₂ : DS g 0 (.star e) rest (.ok ts rest')) :
      DS g S (.star e) input (.ok (.starCons t ts) rest')
  | notOk (S : Nat) (e : PExp) (input rest : List Char) (t : PTree) (h : DS g S e input (.ok t rest)) :
      DS g S (.notP e) input .fail
  | notFail (S : Nat) (e : PExp) (input : List Char) (h : DS g S e input .fail) :
      DS g S (.notP e) input (.ok .notT input)

/-- A checked derivation is a derivation. -/
theorem ds_derives {g : Grammar} {S : Nat} {e : PExp} {x : List Char} {o : Outcome} (h : DS g S e x o) :
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
  | ntOk _ _ _ _ _ _ hr _ _ ih => exact .ntOk _ _ _ _ _ hr ih
  | ntFail _ _ _ _ hr _ _ ih => exact .ntFail _ _ _ hr ih
  | ntMissing _ _ _ hr => exact .ntMissing _ _ hr
  | seqOk _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqOk _ _ _ _ _ _ _ ih₁ ih₂
  | seqFail₁ _ _ _ _ _ ih => exact .seqFail₁ _ _ _ ih
  | seqFail₂ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .seqFail₂ _ _ _ _ _ ih₁ ih₂
  | altL _ _ _ _ _ _ _ ih => exact .altL _ _ _ _ _ ih
  | altR _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .altR _ _ _ _ _ ih₁ ih₂
  | altFail _ _ _ _ _ _ ih₁ ih₂ => exact .altFail _ _ _ ih₁ ih₂
  | starNil _ _ _ _ ih => exact .starNil _ _ ih
  | starCons _ _ _ _ _ _ _ _ _ _ ih₁ ih₂ => exact .starCons _ _ _ _ _ _ ih₁ ih₂
  | notOk _ _ _ _ _ _ ih => exact .notOk _ _ _ _ ih
  | notFail _ _ _ _ ih => exact .notFail _ _ ih

/-- Checked derivations are deterministic. -/
theorem ds_det {g : Grammar} {S S' : Nat} {e : PExp} {x : List Char} {o₁ o₂ : Outcome} (h₁ : DS g S e x o₁)
    (h₂ : DS g S' e x o₂) : o₁ = o₂ :=
  derives_det (ds_derives h₁) (ds_derives h₂)

/-- A successful checked derivation consumes a prefix. -/
theorem ds_suffix {g : Grammar} {S : Nat} {e : PExp} {x r : List Char} {t : PTree} (h : DS g S e x (.ok t r)) :
    ∃ p, x = p ++ r :=
  derives_suffix (ds_derives h) t r rfl

/-- A proper suffix is shorter. -/
theorem suffix_lt {x r p : List Char} (hx : x = p ++ r) (hne : r ≠ x) : r.length < x.length := by
  subst hx
  cases p with
  | nil => exact absurd rfl hne
  | cons c p => simp; omega

/-- A suffix is no longer. -/
theorem suffix_le {x r p : List Char} (hx : x = p ++ r) : r.length ≤ x.length := by
  subst hx; simp

/-! ## From derivations to checked derivations -/

/-- The members of `S` are open callers of `e` at `x`: each derivation of a member at `x` contains a strictly lower
derivation of `e` at `x`. -/
def Inv (g : Grammar) (S : Nat) (e : PExp) (x : List Char) : Prop :=
  ∀ A, S.testBit A = true → ∀ n o, DH g n (.nt A) x o → ∃ m o', m < n ∧ DH g m e x o'

/-- The empty set is trivially a set of open callers. -/
theorem inv_zero (g : Grammar) (e : PExp) (x : List Char) : Inv g 0 e x := by
  intro A hA; rw [testBit_zero_mask] at hA; cases hA

/-- A nonterminal that is its own open caller has no derivation (infinite descent on heights). -/
theorem no_self {g : Grammar} {A : Nat} {x : List Char}
    (h : ∀ n o, DH g n (.nt A) x o → ∃ m o', m < n ∧ DH g m (.nt A) x o') :
    ∀ N n o, n < N → ¬ DH g n (.nt A) x o := by
  intro N
  induction N with
  | zero => intro n o hn; omega
  | succ N ih =>
    intro n o hn hd
    obtain ⟨m, o', hm, hd'⟩ := h n o hd
    exact ih m o' (by omega) hd'

/-- Open callers of `e` are open callers of anything `e` evaluates first at the same position. -/
theorem inv_step {g : Grammar} {S : Nat} {e e' : PExp} {x : List Char} (hI : Inv g S e x)
    (hstep : ∀ n o, DH g n e x o → ∃ m o', m < n ∧ DH g m e' x o') : Inv g S e' x := by
  intro A hA n o hd
  obtain ⟨m, o', hm, hd'⟩ := hI A hA n o hd
  obtain ⟨k, o'', hk, hd''⟩ := hstep m o' hd'
  exact ⟨k, o'', by omega, hd''⟩

/-- A repetition cannot take a step that consumes nothing. -/
theorem star_no_empty {g : Grammar} {e : PExp} {y : List Char} {o : Outcome} (h : Derives g (.star e) y o) :
    ∀ t, Derives g e y (.ok t y) → False := by
  generalize he : PExp.star e = es at h
  induction h with
  | starNil _ _ hf =>
    cases he; intro t ht; cases derives_det hf ht
  | starCons _ _ _ _ _ _ h₁ _ _ ih₂ =>
    cases he; intro t ht
    cases derives_det h₁ ht
    exact ih₂ rfl _ h₁
  | _ => cases he

/-- `nx` of a step that consumed is the empty set. -/
theorem nx_ne {S : Nat} {x r : List Char} (h : r ≠ x) : nx S x r = 0 := by simp [nx, h]

/-- `nx` of a step that consumed nothing is the set itself. -/
theorem nx_eq {S : Nat} {x : List Char} : nx S x x = S := by simp [nx]

/-- Open callers of `seq a b` at `x` are open callers of `b` at `x` when `a` succeeds at `x` consuming nothing. -/
theorem inv_seq_right {g : Grammar} {S : Nat} {a b : PExp} {x : List Char} {t : PTree} (hI : Inv g S (.seq a b) x)
    (ha : Derives g a x (.ok t x)) : Inv g S b x := by
  refine inv_step hI ?_
  intro n o hd
  cases hd with
  | seqOk n _ _ _ r₁ _ _ _ h₁ h₂ =>
    cases derives_det ha (dh_derives h₁); exact ⟨n, _, by omega, h₂⟩
  | seqFail₁ n _ _ _ h₁ => cases derives_det ha (dh_derives h₁)
  | seqFail₂ n _ _ _ r₁ _ h₁ h₂ =>
    cases derives_det ha (dh_derives h₁); exact ⟨n, _, by omega, h₂⟩

/-- The open set handed to the second part of a sequence satisfies the invariant. -/
theorem inv_seq_nx {g : Grammar} {S : Nat} {a b : PExp} {x r : List Char} {t : PTree} (hI : Inv g S (.seq a b) x)
    (ha : Derives g a x (.ok t r)) : Inv g (nx S x r) b r := by
  by_cases h : r = x
  · subst h; rw [nx_eq]; exact inv_seq_right hI ha
  · rw [nx_ne h]; exact inv_zero g b r

/-- **Derivations are checked derivations**, for a set of open callers. -/
theorem dh_ds {g : Grammar} {n : Nat} {e : PExp} {x : List Char} {o : Outcome} (h : DH g n e x o) :
    ∀ S, Inv g S e x → DS g S e x o := by
  induction h with
  | eps => intro S _; exact .eps _ _
  | anyOk => intro S _; exact .anyOk _ _ _
  | anyFail => intro S _; exact .anyFail _
  | chrOk _ _ _ _ h => intro S _; exact .chrOk _ _ _ _ h
  | chrFail _ _ _ _ h => intro S _; exact .chrFail _ _ _ _ h
  | chrEmpty => intro S _; exact .chrEmpty _ _
  | rangeOk _ _ _ _ _ h => intro S _; exact .rangeOk _ _ _ _ _ h
  | rangeFail _ _ _ _ _ h => intro S _; exact .rangeFail _ _ _ _ _ h
  | rangeEmpty => intro S _; exact .rangeEmpty _ _ _
  | litOk _ _ _ _ h => intro S _; exact .litOk _ _ _ _ h
  | litFail _ _ _ h => intro S _; exact .litFail _ _ _ h
  | ntMissing _ _ _ hr => intro S _; exact .ntMissing _ _ _ hr
  | ntOk k A body x r t hr hd ih =>
    intro S hI
    have hm : S.testBit A = false := by
      cases hb : S.testBit A with
      | false => rfl
      | true =>
        exfalso
        exact no_self (hI A hb) (k + 2) (k + 1) _ (by omega) (.ntOk _ _ _ _ _ _ hr hd)
    exact .ntOk _ _ _ _ _ _ hr hm (ih _ (inv_body hI hr))
  | ntFail k A body x hr hd ih =>
    intro S hI
    have hm : S.testBit A = false := by
      cases hb : S.testBit A with
      | false => rfl
      | true =>
        exfalso
        exact no_self (hI A hb) (k + 2) (k + 1) _ (by omega) (.ntFail _ _ _ _ hr hd)
    exact .ntFail _ _ _ _ hr hm (ih _ (inv_body hI hr))
  | seqOk k a b x r₁ r₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro S hI
    exact .seqOk _ _ _ _ _ _ _ _ (ih₁ _ (inv_first hI)) (ih₂ _ (inv_seq_nx hI (dh_derives h₁)))
  | seqFail₁ k a b x h₁ ih₁ => intro S hI; exact .seqFail₁ _ _ _ _ (ih₁ _ (inv_first hI))
  | seqFail₂ k a b x r₁ t₁ h₁ h₂ ih₁ ih₂ =>
    intro S hI
    exact .seqFail₂ _ _ _ _ _ _ (ih₁ _ (inv_first hI)) (ih₂ _ (inv_seq_nx hI (dh_derives h₁)))
  | altL k a b x r t h ih => intro S hI; exact .altL _ _ _ _ _ _ (ih _ (inv_first hI))
  | altR k a b x r t h₁ h₂ ih₁ ih₂ =>
    intro S hI
    exact .altR _ _ _ _ _ _ (ih₁ _ (inv_first hI)) (ih₂ _ (inv_alt_right hI (dh_derives h₁)))
  | altFail k a b x h₁ h₂ ih₁ ih₂ =>
    intro S hI
    exact .altFail _ _ _ _ (ih₁ _ (inv_first hI)) (ih₂ _ (inv_alt_right hI (dh_derives h₁)))
  | starNil k a x h ih => intro S hI; exact .starNil _ _ _ (ih _ (inv_first hI))
  | starCons k a x r r' t ts h₁ h₂ ih₁ ih₂ =>
    intro S hI
    have hne : r ≠ x := by
      intro hr; subst hr
      exact star_no_empty (dh_derives h₂) t (dh_derives h₁)
    exact .starCons _ _ _ _ _ _ _ (ih₁ _ (inv_first hI)) hne (ih₂ _ (inv_zero g _ r))
  | notOk k a x r t h ih => intro S hI; exact .notOk _ _ _ _ _ (ih _ (inv_first hI))
  | notFail k a x h ih => intro S hI; exact .notFail _ _ _ (ih _ (inv_first hI))
where
  /-- Open callers of a compound expression are open callers of its first part. -/
  inv_first {g : Grammar} {S : Nat} {e a : PExp} {x : List Char} (hI : Inv g S e x)
      (hfirst : ∀ n o, DH g n e x o → ∃ m o', m < n ∧ DH g m a x o' := by
        intro n o hd; cases hd <;> exact ⟨_, _, Nat.lt_succ_self _, by assumption⟩) : Inv g S a x :=
    inv_step hI hfirst
  /-- Open callers of `alt a b` at `x` are open callers of `b` when `a` fails at `x`. -/
  inv_alt_right {g : Grammar} {S : Nat} {a b : PExp} {x : List Char} (hI : Inv g S (.alt a b) x)
      (ha : Derives g a x .fail) : Inv g S b x := by
    refine inv_step hI ?_
    intro n o hd
    cases hd with
    | altL n _ _ _ _ _ h => cases derives_det ha (dh_derives h)
    | altR n _ _ _ _ _ _ h₂ => exact ⟨n, _, by omega, h₂⟩
    | altFail n _ _ _ _ h₂ => exact ⟨n, _, by omega, h₂⟩
  /-- Entering a rule body: the callee joins the open callers. -/
  inv_body {g : Grammar} {S A : Nat} {body : PExp} {x : List Char} (hI : Inv g S (.nt A) x)
      (hr : ruleAt g.rules A = some body) : Inv g (ins S A) body x := by
    have hstep : ∀ n o, DH g n (.nt A) x o → ∃ m o', m < n ∧ DH g m body x o' := by
      intro n o hd
      cases hd with
      | ntOk n _ e' _ _ _ hr' hd' => rw [hr] at hr'; cases hr'; exact ⟨n, _, by omega, hd'⟩
      | ntFail n _ e' _ hr' hd' => rw [hr] at hr'; cases hr'; exact ⟨n, _, by omega, hd'⟩
      | ntMissing n _ _ hr' => rw [hr] at hr'; cases hr'
    intro B hB n o hd
    rw [testBit_ins] at hB
    cases hS : S.testBit B with
    | true => exact inv_step hI hstep B hS n o hd
    | false =>
      rw [hS] at hB
      have hAB : A = B := by simpa using hB
      subst hAB
      exact hstep n o hd

/-- **A derivation is a checked derivation from the empty open set.** -/
theorem derives_ds {g : Grammar} {e : PExp} {x : List Char} {o : Outcome} (h : Derives g e x o) :
    DS g 0 e x o := by
  obtain ⟨n, hn⟩ := derives_dh h
  exact dh_ds hn 0 (inv_zero g e x)

end Shallot
