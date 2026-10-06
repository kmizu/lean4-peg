import MacroPeg.ExpandSemantics
import MacroPeg.Divergence

/-!
# Well-formedness implies termination, for the first-order fragment (M-PEG-7)

The reference `GrammarValidator` (`Ast.isWellFormed` in `kmizu/macro_peg`) accepts a
grammar when (1) no repetition `e*` has a nullable body and (2) no rule is left-recursive
through nullable prefixes. Its stated purpose is to keep the evaluator — and hence the
generated parser — from looping. `Divergence.lean` (CE-002) shows this is FALSE for the
full macro language: `F(x) = x; S = F(S)` passes the checker and diverges.

This module proves that it is TRUE for the **first-order fragment** — which is exactly
what `MExp.expand` produces from a lambda-free macro grammar (T-fix: no calls with
arguments remain), i.e. exactly the language of the parsers `ParserGenerator` emits.
Concretely: if `wfB g = true` then EVERY first-order expression has a derivation on
EVERY input (`wf_total`), so `mpegRun` finishes with some fuel (`wf_total_run`).
Combined with M-PEG-6 (`expand_preserves_cbn`), the generated parser both terminates
and agrees with the macro grammar.

Design:
- `MExp.fo` picks out the fragment: leaves, `.call i []`, `seq`/`alt`/`star`/`notP`/`dbg`.
- Nullability is a table `List Bool` (one entry per rule) computed by the same fixpoint
  iteration as the reference (`iterTbl`). The proofs never need the iteration to have
  CONVERGED — they only use that the table `wfB` checks is a fixpoint (`stepTbl g tbl =
  tbl`, checked by `wfB` itself). The key semantic fact is `nullExp_of_nonconsuming`: a
  derivation that succeeds without consuming input is reported nullable by any fixpoint
  table — proved by induction on the derivation, the `.call` case going through the
  fixpoint equation. Its contrapositive, `consumes_of_not_nullExp`, is what drives the
  input-length induction.
- Left recursion: `headCalls tbl e` lists the rules reachable from `e` BEFORE consuming
  any input (the second half of a `seq` counts only if the first half is nullable —
  mirroring the reference `leadsToSelf`); acyclicity of that graph is decided with
  `CallGraph.lean`'s `rankGo` (generic in the adjacency function), and
  `rankAdj_lt_of_acyclic` gives the strict rank drop across a head edge.
- Totality (`wf_total_aux`): induction on the input length, then on the left rank, then
  on the expression. A `seq` whose first half consumed input recurses on a shorter input;
  one whose first half did not consume is nullable, so the second half is a head position
  and stays within the same rank budget; a `star` body is non-nullable, so each iteration
  strictly shortens the input; a `.call` drops the rank.
-/

namespace Shallot.MacroPeg

/-! ## The first-order fragment -/

def MExp.fo : MExp → Bool
  | .eps => true
  | .any => true
  | .chr _ => true
  | .range _ _ => true
  | .lit _ => true
  | .call _ [] => true
  | .call _ (_ :: _) => false
  | .seq a b => a.fo && b.fo
  | .alt a b => a.fo && b.fo
  | .star e => e.fo
  | .notP e => e.fo
  | .dbg e => e.fo
  | .param _ => false
  | .lam _ _ => false
  | .callParam _ _ => false
  | .invoke _ _ _ => false

/-- Substitution is the identity on the first-order fragment (nothing to substitute). -/
theorem subst_of_fo (args : List MExp) : ∀ e : MExp, e.fo = true → MExp.subst args e = e
  | .eps, _ => by simp [MExp.subst]
  | .any, _ => by simp [MExp.subst]
  | .chr _, _ => by simp [MExp.subst]
  | .range _ _, _ => by simp [MExp.subst]
  | .lit _, _ => by simp [MExp.subst]
  | .call _ [], _ => by simp [MExp.subst, MExp.substArgs]
  | .call _ (_ :: _), h => by simp [MExp.fo] at h
  | .seq a b, h => by
    simp only [MExp.fo, Bool.and_eq_true] at h
    simp [MExp.subst, subst_of_fo args a h.1, subst_of_fo args b h.2]
  | .alt a b, h => by
    simp only [MExp.fo, Bool.and_eq_true] at h
    simp [MExp.subst, subst_of_fo args a h.1, subst_of_fo args b h.2]
  | .star e, h => by simp only [MExp.fo] at h; simp [MExp.subst, subst_of_fo args e h]
  | .notP e, h => by simp only [MExp.fo] at h; simp [MExp.subst, subst_of_fo args e h]
  | .dbg e, h => by simp only [MExp.fo] at h; simp [MExp.subst, subst_of_fo args e h]
  | .param _, h => by simp [MExp.fo] at h
  | .lam _ _, h => by simp [MExp.fo] at h
  | .callParam _ _, h => by simp [MExp.fo] at h
  | .invoke _ _ _, h => by simp [MExp.fo] at h

/-! ## Nullability table -/

/-- Table lookup, `false` out of range (a missing rule fails, hence is not nullable). -/
def tblAt : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, n + 1 => tblAt bs n

/-- "May succeed without consuming input", relative to a table for the rules. Mirrors
the reference `exprNullable`; the higher-order constructors are marked nullable
conservatively (they are outside the fragment anyway). -/
def nullExp (tbl : List Bool) : MExp → Bool
  | .eps => true
  | .any => false
  | .chr _ => false
  | .range _ _ => false
  | .lit s => s.isEmpty
  | .call i _ => tblAt tbl i
  | .seq a b => nullExp tbl a && nullExp tbl b
  | .alt a b => nullExp tbl a || nullExp tbl b
  | .star _ => true
  | .notP _ => true
  | .dbg _ => true
  | .param _ => true
  | .lam _ _ => true
  | .callParam _ _ => true
  | .invoke _ _ _ => true

/-- One round of the reference's fixpoint loop: recompute every rule's entry from the
current table. Only 0-arity rules matter for the fragment; the others get whatever
`nullExp` says about their (parameterized) bodies, harmlessly. -/
def stepTbl (g : MGrammar) (tbl : List Bool) : List Bool :=
  g.rules.map (fun r => nullExp tbl r.body)

def iterTbl (g : MGrammar) : Nat → List Bool
  | 0 => g.rules.map (fun _ => false)
  | n + 1 => stepTbl g (iterTbl g n)

/-- The table `wfB` uses: one round per rule, plus one — enough for the loop to have
converged on any grammar (each non-final round flips at least one entry to `true`), though
the proofs below never rely on that: they only use the fixpoint equation `wfB` checks. -/
def nullTbl (g : MGrammar) : List Bool := iterTbl g (g.rules.length + 1)

theorem tblAt_map {rs : List MRule} (f : MRule → Bool) :
    ∀ (i : Nat) (r : MRule), ruleAtM rs i = some r → tblAt (rs.map f) i = f r := by
  induction rs with
  | nil => intro i r h; simp [ruleAtM] at h
  | cons r' rs ih =>
    intro i r h
    cases i with
    | zero => simp [ruleAtM] at h; simp [tblAt, h]
    | succ i => simp only [ruleAtM] at h; simp [tblAt, ih i r h]

/-- The fixpoint equation, read at one rule. -/
theorem tblAt_of_stable {g : MGrammar} {tbl : List Bool} (hst : stepTbl g tbl = tbl)
    {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r) :
    tblAt tbl i = nullExp tbl r.body := by
  have h1 : tblAt (stepTbl g tbl) i = nullExp tbl r.body := tblAt_map _ i r hr
  rw [hst] at h1
  exact h1

/-! ## Non-consuming success is reported nullable -/

theorem stripPrefix?_eq_self : ∀ {str x : List Char}, stripPrefix? str x = some x → str = [] := by
  intro str x h
  cases str with
  | nil => rfl
  | cons c cs =>
    exfalso
    have hlen : ∀ {s x r : List Char}, stripPrefix? s x = some r → x.length = s.length + r.length := by
      intro s
      induction s with
      | nil => intro x r h; simp [stripPrefix?] at h; simp [h]
      | cons d ds ih =>
        intro x r h
        cases x with
        | nil => simp [stripPrefix?] at h
        | cons e es =>
          simp only [stripPrefix?] at h
          split at h
          · have := ih h; simp [this]; omega
          · simp at h
    have := hlen h
    simp at this

/-- All 0-arity rule bodies lie in the fragment. -/
def bodiesFoB (g : MGrammar) : Bool :=
  g.rules.all (fun r => r.arity != 0 || r.body.fo)

theorem bodyFo_of_bodiesFoB {g : MGrammar} (hb : bodiesFoB g = true) {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) (h0 : r.arity = 0) : r.body.fo = true := by
  simp only [bodiesFoB, List.all_eq_true] at hb
  have := hb r (ruleAtM_mem hr)
  simpa [h0] using this

/-- **Soundness of the nullability table.** If a first-order expression succeeds on `x`
leaving exactly `x` (consumed nothing), any fixpoint table marks it nullable. -/
theorem nullExp_of_nonconsuming {g : MGrammar} {tbl : List Bool} (hst : stepTbl g tbl = tbl)
    (hb : bodiesFoB g = true) {e : MExp} {x : List Char} {o : MOutcome}
    (hd : MDerives g .callByName e x o) :
    e.fo = true → ∀ t, o = .ok t x → nullExp tbl e = true := by
  induction hd using MDerives.rec
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
  case eps input => intro _ _ _; simp [nullExp]
  case anyOk c rest => intro _ t h; simp at h
  case anyFail => intro _ t h; cases h
  case chrOk c d rest hcd => intro _ t h; simp at h
  case chrFail c d rest hcd => intro _ t h; cases h
  case chrEmpty c => intro _ t h; cases h
  case rangeOk lo hi d rest hr => intro _ t h; simp at h
  case rangeFail lo hi d rest hr => intro _ t h; cases h
  case rangeEmpty lo hi => intro _ t h; cases h
  case litOk str input rest hs =>
    intro _ t h
    simp only [MOutcome.ok.injEq] at h
    rw [h.2] at hs
    simp [nullExp, stripPrefix?_eq_self hs]
  case litFail str input hs => intro _ t h; cases h
  case dbg e input => intro _ _ _; simp [nullExp]
  case paramFail k input => intro _ t h; cases h
  case lam ar bod input => intro _ _ _; simp [nullExp]
  case callParamFail k args input => intro _ t h; cases h
  case invokeNameOk ar bod args input rest t hs ha hd ih => intro hfo; simp [MExp.fo] at hfo
  case invokeNameFail ar bod args input hs ha hd ih => intro hfo; simp [MExp.fo] at hfo
  case invokeParOk ar bod args input rest vals t hs ha hargs hd ihargs ih => cases hs
  case invokeParFail ar bod args input vals hs ha hargs hd ihargs ih => cases hs
  case invokeParArgFail ar bod pre badArg post input preVals hs ha hpre hfail ihpre ihfail => cases hs
  case invokeSeqOk ar bod args input mid rest vals t hs ha hargs hd ihargs ih => cases hs
  case invokeSeqFail ar bod args input mid vals hs ha hargs hd ihargs ih => cases hs
  case invokeSeqArgFail ar bod pre badArg post input mid preVals hs ha hpre hfail ihpre ihfail => cases hs
  case invokeArity ar bod args input ha => intro hfo; simp [MExp.fo] at hfo
  case callNameOk i args r input rest t hs hr ha hd ih =>
    intro hfo t' h
    cases args with
    | cons a as => simp [MExp.fo] at hfo
    | nil =>
      simp only [MOutcome.ok.injEq] at h
      have h0 : r.arity = 0 := by simpa using ha
      have hbfo : r.body.fo = true := bodyFo_of_bodiesFoB hb hr h0
      rw [subst_of_fo [] r.body hbfo] at ih
      have := ih hbfo t (by rw [h.2])
      simp only [nullExp]
      rw [tblAt_of_stable hst hr]
      exact this
  case callNameFail i args r input hs hr ha hd ih => intro _ t h; cases h
  case callParOk i args r input rest vals t hs hr ha hargs hd ihargs ih => cases hs
  case callParFail i args r input vals hs hr ha hargs hd ihargs ih => cases hs
  case callParArgFail i pre badArg post r input preVals hs hr ha hpre hfail ihpre ihfail => cases hs
  case callSeqOk i args r input mid rest vals t hs hr ha hargs hd ihargs ih => cases hs
  case callSeqFail i args r input mid vals hs hr ha hargs hd ihargs ih => cases hs
  case callSeqArgFail i pre badArg post r input mid preVals hs hr ha hpre hfail ihpre ihfail => cases hs
  case callMissing i args input hr => intro _ t h; cases h
  case callArity i args r input hr ha => intro _ t h; cases h
  case seqOk e₁ e₂ input rest₁ rest₂ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    intro hfo t h
    simp only [MExp.fo, Bool.and_eq_true] at hfo
    simp only [MOutcome.ok.injEq] at h
    -- input = p₁ ++ rest₁ and rest₁ = p₂ ++ rest₂ = p₂ ++ input force p₁ = p₂ = [].
    obtain ⟨p₁, hp₁⟩ := mderives_suffix h₁ t₁ rest₁ rfl
    obtain ⟨p₂, hp₂⟩ := mderives_suffix h₂ t₂ rest₂ rfl
    rw [h.2] at hp₂
    have hlen₁ := congrArg List.length hp₁
    have hlen₂ := congrArg List.length hp₂
    simp at hlen₁ hlen₂
    have hp₁nil : p₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp₁nil
    simp at hp₁
    have hn₁ := ih₁ hfo.1 t₁ (by rw [hp₁])
    have hn₂ := ih₂ hfo.2 t₂ (by rw [h.2, hp₁])
    simp [nullExp, hn₁, hn₂]
  case seqFail₁ e₁ e₂ input h₁ ih₁ => intro _ t h; cases h
  case seqFail₂ e₁ e₂ input rest₁ t₁ h₁ h₂ ih₁ ih₂ => intro _ t h; cases h
  case altL e₁ e₂ input rest t h ih =>
    intro hfo t' h'
    simp only [MExp.fo, Bool.and_eq_true] at hfo
    simp only [MOutcome.ok.injEq] at h'
    have := ih hfo.1 t (by rw [h'.2])
    simp [nullExp, this]
  case altR e₁ e₂ input rest t h₁ h₂ ih₁ ih₂ =>
    intro hfo t' h'
    simp only [MExp.fo, Bool.and_eq_true] at hfo
    simp only [MOutcome.ok.injEq] at h'
    have := ih₂ hfo.2 t (by rw [h'.2])
    simp [nullExp, this]
  case altFail e₁ e₂ input h₁ h₂ ih₁ ih₂ => intro _ t h; cases h
  case starNil e input h ih => intro _ _ _; simp [nullExp]
  case starCons e input rest rest' t ts h₁ h₂ ih₁ ih₂ => intro _ _ _; simp [nullExp]
  case notOk e input rest t h ih => intro _ t h; cases h
  case notFail e input h ih => intro _ _ _; simp [nullExp]
  all_goals trivial

/-- Contrapositive, in the form the termination argument uses: a non-nullable
first-order expression that succeeds must have consumed at least one character. -/
theorem consumes_of_not_nullExp {g : MGrammar} {tbl : List Bool} (hst : stepTbl g tbl = tbl)
    (hb : bodiesFoB g = true) {e : MExp} (hfo : e.fo = true) (hnull : nullExp tbl e = false)
    {x r : List Char} {t : MTree} (hd : MDerives g .callByName e x (.ok t r)) :
    r.length < x.length := by
  obtain ⟨p, hp⟩ := mderives_suffix hd t r rfl
  cases p with
  | nil =>
    simp at hp
    subst hp
    have := nullExp_of_nonconsuming hst hb hd hfo t rfl
    rw [this] at hnull
    cases hnull
  | cons c cs =>
    rw [hp]
    simp
    omega

/-! ## Left recursion: the head-call graph and its ranks

`CallGraph.lean`'s `rankGo`/`rankSuccs` are generic in the adjacency function; only the
top-level `rank`/`acyclicB`/`rank_lt_of_acyclic` were specialised to `g.calls`. Here are
the generic counterparts, with the same proof. -/

/-- Rank of node `i` in the graph `adj` on `n` nodes, `0` if the DFS fails. -/
def rankAdj (adj : Nat → List Nat) (n i : Nat) : Nat := (rankGo adj [] n i).getD 0

def acyclicAdjB (adj : Nat → List Nat) (n : Nat) : Bool :=
  (List.range n).all (fun i => (rankGo adj [] n i).isSome)

theorem rankGo_top_some_of_acyclicAdj {adj : Nat → List Nat} {n : Nat}
    (hacyc : acyclicAdjB adj n = true) {i : Nat} (hi : i < n) :
    ∃ r, rankGo adj [] n i = some r := by
  simp only [acyclicAdjB, List.all_eq_true] at hacyc
  have := hacyc i (by simpa using hi)
  simpa [Option.isSome_iff_exists] using this

theorem rankAdj_pos_of_acyclic {adj : Nat → List Nat} {n : Nat}
    (hacyc : acyclicAdjB adj n = true) {i : Nat} (hi : i < n) : 0 < rankAdj adj n i := by
  obtain ⟨ri, hrankI⟩ := rankGo_top_some_of_acyclicAdj hacyc hi
  obtain ⟨fuel, rfl⟩ : ∃ fuel, n = fuel + 1 := ⟨n - 1, by omega⟩
  have hrankI' := hrankI
  simp only [rankGo] at hrankI'
  split at hrankI'
  · simp at hrankI'
  · cases hrs : rankSuccs adj [i] fuel (adj i) with
    | none => rw [hrs] at hrankI'; simp at hrankI'
    | some rs =>
      rw [hrs] at hrankI'
      simp only [Option.map_some, Option.some.injEq] at hrankI'
      simp [rankAdj, hrankI, ← hrankI']
      omega

theorem rankAdj_lt_of_acyclic {adj : Nat → List Nat} {n : Nat}
    (hacyc : acyclicAdjB adj n = true) {i j : Nat} (hi : i < n) (hij : j ∈ adj i) :
    rankAdj adj n j < rankAdj adj n i := by
  obtain ⟨ri, hrankI⟩ := rankGo_top_some_of_acyclicAdj hacyc hi
  obtain ⟨fuel, rfl⟩ : ∃ fuel, n = fuel + 1 := ⟨n - 1, by omega⟩
  have hrankI' := hrankI
  simp only [rankGo] at hrankI'
  split at hrankI'
  · simp at hrankI'
  · cases hrs : rankSuccs adj [i] fuel (adj i) with
    | none => rw [hrs] at hrankI'; simp at hrankI'
    | some rs =>
      rw [hrs] at hrankI'
      simp only [Option.map_some, Option.some.injEq] at hrankI'
      obtain ⟨rj', hrj', hrj'le⟩ := rankSuccs_mem hrs hij
      have hstep1 : rankGo adj [i] (fuel + 1) j = some rj' := rankGo_mono hrj'
      have hsub : ∀ x, natElem x ([] : List Nat) = true → natElem x [i] = true := by
        intro x hx; simp [natElem] at hx
      obtain ⟨rj, hrjle, hrankJ⟩ := rankGo_shrink hsub hstep1
      have heqI : rankAdj adj (fuel + 1) i = ri := by simp [rankAdj, hrankI]
      have heqJ : rankAdj adj (fuel + 1) j = rj := by simp [rankAdj, hrankJ]
      rw [heqI, heqJ]
      omega

/-- Rules reachable from `e` BEFORE any input is consumed — the second half of a `seq`
only if the first half is nullable (per the table), mirroring the reference
`leadsToSelf`. `dbg e` does not evaluate `e`. -/
def headCalls (tbl : List Bool) : MExp → List Nat
  | .call i [] => [i]
  | .call _ (_ :: _) => []
  | .seq a b => headCalls tbl a ++ (if nullExp tbl a then headCalls tbl b else [])
  | .alt a b => headCalls tbl a ++ headCalls tbl b
  | .star e => headCalls tbl e
  | .notP e => headCalls tbl e
  | _ => []

/-- Head edges out of rule `i` (only 0-arity rules participate). -/
def headAdj (g : MGrammar) (tbl : List Bool) (i : Nat) : List Nat :=
  match ruleAtM g.rules i with
  | some r => if r.arity == 0 then headCalls tbl r.body else []
  | none => []

def leftAcyclicB (g : MGrammar) (tbl : List Bool) : Bool :=
  acyclicAdjB (headAdj g tbl) g.rules.length

def lrankRule (g : MGrammar) (tbl : List Bool) (i : Nat) : Nat :=
  rankAdj (headAdj g tbl) g.rules.length i

/-- Left rank of an expression: the largest rank among its head calls. -/
def lrank (g : MGrammar) (tbl : List Bool) (e : MExp) : Nat :=
  (headCalls tbl e).foldr (fun j acc => max (lrankRule g tbl j) acc) 0

theorem foldrMax_append (f : Nat → Nat) (l₁ l₂ : List Nat) :
    (l₁ ++ l₂).foldr (fun j acc => max (f j) acc) 0 =
      max (l₁.foldr (fun j acc => max (f j) acc) 0) (l₂.foldr (fun j acc => max (f j) acc) 0) := by
  induction l₁ with
  | nil => simp
  | cons j l₁ ih => simp [List.foldr_cons, ih, Nat.max_assoc]

theorem foldrMax_lt_of_forall_lt (f : Nat → Nat) {bound : Nat} (hpos : 0 < bound) :
    ∀ l : List Nat, (∀ j ∈ l, f j < bound) → l.foldr (fun j acc => max (f j) acc) 0 < bound
  | [], _ => hpos
  | j :: l, h => by
    simp only [List.foldr_cons]
    have hj := h j (List.mem_cons_self ..)
    have hl := foldrMax_lt_of_forall_lt f hpos l (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))
    omega

theorem lrank_seq_left (g : MGrammar) (tbl : List Bool) (a b : MExp) :
    lrank g tbl a ≤ lrank g tbl (.seq a b) := by
  simp only [lrank, headCalls, foldrMax_append]
  exact Nat.le_max_left _ _

theorem lrank_seq_right_of_null (g : MGrammar) (tbl : List Bool) (a b : MExp)
    (hn : nullExp tbl a = true) : lrank g tbl b ≤ lrank g tbl (.seq a b) := by
  simp only [lrank, headCalls, hn, if_true, foldrMax_append]
  exact Nat.le_max_right _ _

theorem lrank_alt_left (g : MGrammar) (tbl : List Bool) (a b : MExp) :
    lrank g tbl a ≤ lrank g tbl (.alt a b) := by
  simp only [lrank, headCalls, foldrMax_append]
  exact Nat.le_max_left _ _

theorem lrank_alt_right (g : MGrammar) (tbl : List Bool) (a b : MExp) :
    lrank g tbl b ≤ lrank g tbl (.alt a b) := by
  simp only [lrank, headCalls, foldrMax_append]
  exact Nat.le_max_right _ _

theorem lrank_star (g : MGrammar) (tbl : List Bool) (e : MExp) :
    lrank g tbl e = lrank g tbl (.star e) := rfl

theorem lrank_notP (g : MGrammar) (tbl : List Bool) (e : MExp) :
    lrank g tbl e = lrank g tbl (.notP e) := rfl

theorem lrank_call (g : MGrammar) (tbl : List Bool) (i : Nat) :
    lrank g tbl (.call i []) = lrankRule g tbl i := by
  simp [lrank, headCalls]

/-- The strict rank drop from a 0-arity rule into its body. -/
theorem lrank_body_lt (g : MGrammar) (tbl : List Bool) (hacyc : leftAcyclicB g tbl = true)
    {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r) (h0 : r.arity = 0) :
    lrank g tbl r.body < lrankRule g tbl i := by
  have hi : i < g.rules.length := ruleAtM_some_lt hr
  have hadj : headAdj g tbl i = headCalls tbl r.body := by simp [headAdj, hr, h0]
  have hpos : 0 < lrankRule g tbl i := rankAdj_pos_of_acyclic hacyc hi
  apply foldrMax_lt_of_forall_lt _ hpos
  intro j hj
  rw [← hadj] at hj
  exact rankAdj_lt_of_acyclic hacyc hi hj

/-! ## The well-formedness checker and the totality theorem -/

/-- No repetition over a nullable body (the reference `checkRepetition`). -/
def repOk (tbl : List Bool) : MExp → Bool
  | .star e => !nullExp tbl e && repOk tbl e
  | .seq a b => repOk tbl a && repOk tbl b
  | .alt a b => repOk tbl a && repOk tbl b
  | .notP e => repOk tbl e
  | .dbg e => repOk tbl e
  | _ => true

def repOkB (g : MGrammar) (tbl : List Bool) : Bool :=
  g.rules.all (fun r => r.arity != 0 || repOk tbl r.body)

theorem repOk_of_repOkB {g : MGrammar} {tbl : List Bool} (h : repOkB g tbl = true) {i : Nat}
    {r : MRule} (hr : ruleAtM g.rules i = some r) (h0 : r.arity = 0) : repOk tbl r.body = true := by
  simp only [repOkB, List.all_eq_true] at h
  have := h r (ruleAtM_mem hr)
  simpa [h0] using this

/-- **The well-formedness check** for the first-order fragment: all 0-arity bodies are
first-order, the nullability table is a fixpoint, no `star` over a nullable body, and
the head-call graph is acyclic. Plain computable `Bool`. -/
def wfB (g : MGrammar) : Bool :=
  bodiesFoB g && (stepTbl g (nullTbl g) == nullTbl g) && repOkB g (nullTbl g) &&
    leftAcyclicB g (nullTbl g)

theorem wfB_parts {g : MGrammar} (h : wfB g = true) :
    bodiesFoB g = true ∧ stepTbl g (nullTbl g) = nullTbl g ∧ repOkB g (nullTbl g) = true ∧
      leftAcyclicB g (nullTbl g) = true := by
  simp only [wfB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, by simpa using h2, h3, h4⟩

/-- One layer of the totality argument: structural recursion on the expression, given
the two outer induction hypotheses (shorter inputs — `ihn`; smaller left rank at the same
input — `ihk`). -/
theorem wf_struct (g : MGrammar) (tbl : List Bool) (hb : bodiesFoB g = true)
    (hst : stepTbl g tbl = tbl) (hrepB : repOkB g tbl = true) (hacyc : leftAcyclicB g tbl = true)
    (x : List Char)
    (ihn : ∀ y : List Char, y.length < x.length → ∀ e : MExp, e.fo = true → repOk tbl e = true →
      ∃ o, MDerives g .callByName e y o)
    (k : Nat)
    (ihk : ∀ e : MExp, lrank g tbl e < k → e.fo = true → repOk tbl e = true →
      ∃ o, MDerives g .callByName e x o) :
    ∀ e : MExp, lrank g tbl e < k + 1 → e.fo = true → repOk tbl e = true →
      ∃ o, MDerives g .callByName e x o
  | .eps, _, _, _ => ⟨_, .eps x⟩
  | .any, _, _, _ => by
    cases x with
    | nil => exact ⟨_, .anyFail⟩
    | cons c rest => exact ⟨_, .anyOk c rest⟩
  | .chr c, _, _, _ => by
    cases x with
    | nil => exact ⟨_, .chrEmpty c⟩
    | cons d rest =>
      cases h : beqChar c d with
      | true => exact ⟨_, .chrOk c d rest h⟩
      | false => exact ⟨_, .chrFail c d rest h⟩
  | .range lo hi, _, _, _ => by
    cases x with
    | nil => exact ⟨_, .rangeEmpty lo hi⟩
    | cons d rest =>
      cases h : (leChar lo d && leChar d hi) with
      | true => exact ⟨_, .rangeOk lo hi d rest h⟩
      | false => exact ⟨_, .rangeFail lo hi d rest h⟩
  | .lit str, _, _, _ => by
    cases h : stripPrefix? str x with
    | some rest => exact ⟨_, .litOk str x rest h⟩
    | none => exact ⟨_, .litFail str x h⟩
  | .dbg e, _, _, _ => ⟨_, .dbg e x⟩
  | .param _, _, hfo, _ => by simp [MExp.fo] at hfo
  | .lam _ _, _, hfo, _ => by simp [MExp.fo] at hfo
  | .callParam _ _, _, hfo, _ => by simp [MExp.fo] at hfo
  | .invoke _ _ _, _, hfo, _ => by simp [MExp.fo] at hfo
  | .call _ (_ :: _), _, hfo, _ => by simp [MExp.fo] at hfo
  | .call i [], hk, _, _ => by
    cases hr : ruleAtM g.rules i with
    | none => exact ⟨_, .callMissing i [] x hr⟩
    | some r =>
      by_cases h0 : r.arity = 0
      · have hbfo := bodyFo_of_bodiesFoB hb hr h0
        have hbrep := repOk_of_repOkB hrepB hr h0
        have hlt : lrank g tbl r.body < k := by
          have h1 := lrank_body_lt g tbl hacyc hr h0
          rw [lrank_call] at hk
          omega
        obtain ⟨o, hd⟩ := ihk r.body hlt hbfo hbrep
        rw [← subst_of_fo [] r.body hbfo] at hd
        have ha : r.arity = ([] : List MExp).length := by simpa using h0
        cases o with
        | fail => exact ⟨_, .callNameFail i [] r x rfl hr ha hd⟩
        | ok t rest => exact ⟨_, .callNameOk i [] r x rest t rfl hr ha hd⟩
      · exact ⟨_, .callArity i [] r x hr (by simpa using h0)⟩
  | .seq a b, hk, hfo, hrep => by
    simp only [MExp.fo, Bool.and_eq_true] at hfo
    simp only [repOk, Bool.and_eq_true] at hrep
    have hka : lrank g tbl a < k + 1 := Nat.lt_of_le_of_lt (lrank_seq_left g tbl a b) hk
    obtain ⟨oa, hda⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk a hka hfo.1 hrep.1
    cases oa with
    | fail => exact ⟨_, .seqFail₁ a b x hda⟩
    | ok t r =>
      obtain ⟨p, hp⟩ := mderives_suffix hda t r rfl
      cases p with
      | cons c cs =>
        -- `a` consumed at least one character: `b` runs on a strictly shorter input.
        have hlt : r.length < x.length := by rw [hp]; simp; omega
        obtain ⟨ob, hdb⟩ := ihn r hlt b hfo.2 hrep.2
        cases ob with
        | fail => exact ⟨_, .seqFail₂ a b x r t hda hdb⟩
        | ok t₂ r₂ => exact ⟨_, .seqOk a b x r r₂ t t₂ hda hdb⟩
      | nil =>
        -- `a` consumed nothing, hence is nullable: `b` is in head position.
        simp at hp
        subst hp
        have hna : nullExp tbl a = true := nullExp_of_nonconsuming hst hb hda hfo.1 t rfl
        have hkb : lrank g tbl b < k + 1 :=
          Nat.lt_of_le_of_lt (lrank_seq_right_of_null g tbl a b hna) hk
        obtain ⟨ob, hdb⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk b hkb hfo.2 hrep.2
        cases ob with
        | fail => exact ⟨_, .seqFail₂ a b x x t hda hdb⟩
        | ok t₂ r₂ => exact ⟨_, .seqOk a b x x r₂ t t₂ hda hdb⟩
  | .alt a b, hk, hfo, hrep => by
    simp only [MExp.fo, Bool.and_eq_true] at hfo
    simp only [repOk, Bool.and_eq_true] at hrep
    have hka : lrank g tbl a < k + 1 := Nat.lt_of_le_of_lt (lrank_alt_left g tbl a b) hk
    obtain ⟨oa, hda⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk a hka hfo.1 hrep.1
    cases oa with
    | ok t r => exact ⟨_, .altL a b x r t hda⟩
    | fail =>
      have hkb : lrank g tbl b < k + 1 := Nat.lt_of_le_of_lt (lrank_alt_right g tbl a b) hk
      obtain ⟨ob, hdb⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk b hkb hfo.2 hrep.2
      cases ob with
      | fail => exact ⟨_, .altFail a b x hda hdb⟩
      | ok t r => exact ⟨_, .altR a b x r t hda hdb⟩
  | .star e, hk, hfo, hrep => by
    simp only [MExp.fo] at hfo
    simp only [repOk, Bool.and_eq_true, Bool.not_eq_true'] at hrep
    have hke : lrank g tbl e < k + 1 := by rw [lrank_star]; exact hk
    obtain ⟨oe, hde⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk e hke hfo hrep.2
    cases oe with
    | fail => exact ⟨_, .starNil e x hde⟩
    | ok t r =>
      have hlt : r.length < x.length := consumes_of_not_nullExp hst hb hfo hrep.1 hde
      obtain ⟨os, hds⟩ := ihn r hlt (.star e) (by simpa [MExp.fo] using hfo)
        (by simp [repOk, hrep.1, hrep.2])
      cases os with
      | fail => exact absurd hds (by intro h; cases h)
      | ok ts r' => exact ⟨_, .starCons e x r r' t ts hde hds⟩
  | .notP e, hk, hfo, hrep => by
    simp only [MExp.fo] at hfo
    simp only [repOk] at hrep
    have hke : lrank g tbl e < k + 1 := by rw [lrank_notP]; exact hk
    obtain ⟨oe, hde⟩ := wf_struct g tbl hb hst hrepB hacyc x ihn k ihk e hke hfo hrep
    cases oe with
    | fail => exact ⟨_, .notFail e x hde⟩
    | ok t r => exact ⟨_, .notOk e x r t hde⟩

/-- Outer induction: on the input length, then on the left rank. -/
theorem wf_total_aux (g : MGrammar) (hwf : wfB g = true) :
    ∀ n : Nat, ∀ x : List Char, x.length < n → ∀ k : Nat, ∀ e : MExp,
      lrank g (nullTbl g) e < k → e.fo = true → repOk (nullTbl g) e = true →
        ∃ o, MDerives g .callByName e x o := by
  obtain ⟨hb, hst, hrepB, hacyc⟩ := wfB_parts hwf
  intro n
  induction n with
  | zero => intro x hx; exact absurd hx (Nat.not_lt_zero _)
  | succ n ihn =>
    intro x hx k
    have ihn' : ∀ y : List Char, y.length < x.length → ∀ e : MExp, e.fo = true →
        repOk (nullTbl g) e = true → ∃ o, MDerives g .callByName e y o := by
      intro y hy e hfo hrep
      exact ihn y (by omega) (lrank g (nullTbl g) e + 1) e (Nat.lt_succ_self _) hfo hrep
    induction k with
    | zero => intro e hk; exact absurd hk (Nat.not_lt_zero _)
    | succ k ihk =>
      exact wf_struct g (nullTbl g) hb hst hrepB hacyc x ihn' k ihk

/-- **T-total (M-PEG-7).** On a well-formed grammar, every first-order expression has a
derivation on every input: the parser cannot loop. -/
theorem wf_total (g : MGrammar) (hwf : wfB g = true) (e : MExp) (hfo : e.fo = true)
    (hrep : repOk (nullTbl g) e = true) (x : List Char) :
    ∃ o, MDerives g .callByName e x o :=
  wf_total_aux g hwf (x.length + 1) x (Nat.lt_succ_self _) (lrank g (nullTbl g) e + 1) e
    (Nat.lt_succ_self _) hfo hrep

/-- Any start rule of a well-formed grammar terminates on every input. -/
theorem wf_total_start (g : MGrammar) (hwf : wfB g = true) (i : Nat) (x : List Char) :
    ∃ o, MDerives g .callByName (.call i []) x o :=
  wf_total g hwf _ (by simp [MExp.fo]) (by simp [repOk]) x

/-- The interpreter reading: some finite fuel always suffices. -/
theorem wf_total_run (g : MGrammar) (hwf : wfB g = true) (e : MExp) (hfo : e.fo = true)
    (hrep : repOk (nullTbl g) e = true) (x : List Char) :
    ∃ f o, mpegRun g .callByName f e x = some o := by
  obtain ⟨o, hd⟩ := wf_total g hwf e hfo hrep x
  obtain ⟨f, hf⟩ := mpegRun_complete hd
  exact ⟨f, o, hf⟩

/-- **The generator's guarantee**: for a macro grammar `g` whose expansion passes the
first-order well-formedness check, the generated (expanded) parser terminates on every
input from every start rule — and, by M-PEG-6, agrees with `g` wherever `g` itself has a
derivation. -/
theorem generated_parser_total {g : MGrammar} (h : acyclicB g = true)
    (hwf : wfB (MGrammar.expandGrammar g h) = true) (i : Nat) (x : List Char) :
    ∃ o, MDerives (MGrammar.expandGrammar g h) .callByName (.call i []) x o :=
  wf_total_start _ hwf i x

/-! ## `wfB` is not vacuous: a passing and a failing grammar

Same `simp`-driven evaluation as the other machine-checked witnesses (`rankGo` is
well-founded recursion, so `decide` cannot reduce it; the equation lemmas can). -/

/-- `S = "a" S / "b"` — right-recursive, terminates on every input. Rule 0 is `S`. -/
def rightRecGrammar : MGrammar :=
  { rules := [ { arity := 0, body := .alt (.seq (.chr 'a') (.call 0 [])) (.chr 'b') } ] }

theorem rightRec_wf : wfB rightRecGrammar = true := by
  simp [wfB, bodiesFoB, repOkB, leftAcyclicB, acyclicAdjB, rightRecGrammar, nullTbl, iterTbl,
    stepTbl, nullExp, tblAt, MExp.fo, repOk, headAdj, headCalls, ruleAtM, rankGo, rankSuccs,
    natElem, List.range, List.range.loop, List.all]

/-- ...so `wf_total` applies: `S` has a derivation on every input. (`"aab"` is accepted
with nothing left; `"aac"` is rejected — both are instances of the theorem, evaluated.) -/
theorem rightRec_total (x : List Char) :
    ∃ o, MDerives rightRecGrammar .callByName (.call 0 []) x o :=
  wf_total_start rightRecGrammar rightRec_wf 0 x

#guard renderMPeg (mpegRun rightRecGrammar .callByName 50 (.call 0 []) "aab".toList) == "ok+0"
#guard renderMPeg (mpegRun rightRecGrammar .callByName 50 (.call 0 []) "aac".toList) == "fail"

/-- `S = S "a" / "b"` — left-recursive: `wfB` rejects it, exactly as the reference
`GrammarValidator` does (`leadsToSelf`). -/
def leftRecGrammar : MGrammar :=
  { rules := [ { arity := 0, body := .alt (.seq (.call 0 []) (.chr 'a')) (.chr 'b') } ] }

theorem leftRec_not_wf : wfB leftRecGrammar = false := by
  simp [wfB, bodiesFoB, repOkB, leftAcyclicB, acyclicAdjB, leftRecGrammar, nullTbl, iterTbl,
    stepTbl, nullExp, tblAt, MExp.fo, repOk, headAdj, headCalls, ruleAtM, rankGo, rankSuccs,
    natElem, List.range, List.range.loop, List.all]

/-- `S = ("a"?)* "b"` — a repetition over a nullable body: rejected (`checkRepetition`). -/
def nullStarGrammar : MGrammar :=
  { rules := [ { arity := 0, body := .seq (.star (.alt (.chr 'a') .eps)) (.chr 'b') } ] }

theorem nullStar_not_wf : wfB nullStarGrammar = false := by
  simp [wfB, bodiesFoB, repOkB, leftAcyclicB, acyclicAdjB, nullStarGrammar, nullTbl, iterTbl,
    stepTbl, nullExp, tblAt, MExp.fo, repOk, headAdj, headCalls, ruleAtM, rankGo, rankSuccs,
    natElem, List.range, List.range.loop, List.all]

/-- CE-002's diverging macro grammar (`F(x) = x; S = F(S)`) is outside the fragment —
`S`'s body is a call WITH an argument — so `wfB` (correctly) does not vouch for it. The
reference checker's blind spot is precisely that it accepts such grammars. -/
theorem ce002_not_wf : wfB selfCallGrammar = false := by
  simp [wfB, bodiesFoB, selfCallGrammar, MExp.fo]

end Shallot.MacroPeg
