import MacroPeg.CBV.PrefixSearch
import MacroPeg.CBV.PrefixSuccessor

namespace Shallot.MacroPeg.CBV.PrefixCounters

open RootObservation
open CBVtoCBN (paramsFrom paramsFrom_firstOrder subst_paramsFrom ruleAtM_append_offset)

/-- All fixed-width tuples of input positions, in the generated loop order. -/
def tupleAny (n : Nat) : Nat → (List Nat → Bool) → Bool
  | 0, P => P []
  | d + 1, P => anyFrom (fun j => tupleAny n d (fun ds => P (ds ++ [j]))) 0 n

theorem tupleAny_true_iff (n d : Nat) (P : List Nat → Bool) :
    tupleAny n d P = true ↔
      ∃ ds, ds.length = d ∧ (∀ k ∈ ds, k ≤ n) ∧ P ds = true := by
  induction d generalizing P with
  | zero =>
    simp only [tupleAny]
    constructor
    · intro hp; exact ⟨[], rfl, by simp, hp⟩
    · rintro ⟨ds, hd, _, hp⟩
      have : ds = [] := List.eq_nil_of_length_eq_zero hd
      simpa [this] using hp
  | succ d ih =>
    rw [tupleAny, anyFrom_true_iff]
    simp only [Nat.zero_add]
    constructor
    · rintro ⟨j, _, hj, hp⟩
      obtain ⟨ds, hd, hv, hp⟩ := (ih _).mp hp
      refine ⟨ds ++ [j], by simp [hd], ?_, hp⟩
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact hv k hk
      · exact (List.mem_singleton.mp hk).symm ▸ hj
    · rintro ⟨ds, hd, hv, hp⟩
      obtain ⟨j, tail, ht⟩ := List.exists_cons_of_length_pos (l := ds.reverse) (by simp [hd])
      have he : ds = tail.reverse ++ [j] := by
        simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse ht
      rw [he] at hd hv hp
      refine ⟨j, by omega, hv j (by simp), (ih _).mpr ?_⟩
      exact ⟨tail.reverse, by simp only [List.length_append, List.length_cons, List.length_nil] at hd; omega,
        fun k hk => hv k (List.mem_append_left _ hk), hp⟩

/-- Zero dimensions call the supplied predicate immediately. -/
def tupleSearch (entry leaf : Nat) : Nat → List MExp → MExp
  | 0, ctx => .call leaf ctx
  | _ + 1, ctx => .call entry (.lit [] :: ctx)

theorem tupleSearch_firstOrder (entry leaf d : Nat) (ctx : List MExp)
    (hc : MExp.FirstOrderArgs ctx) : (tupleSearch entry leaf d ctx).FirstOrder := by
  cases d with
  | zero => exact hc
  | succ d => exact ⟨trivial, hc⟩

theorem tupleSearch_subst (args : List MExp) (entry leaf d : Nat) (ctx : List MExp) :
    MExp.subst args (tupleSearch entry leaf d ctx) =
      tupleSearch entry leaf d (MExp.substArgs args ctx) := by
  cases d <;> rfl

def tupleRules (entry leaf : Nat) : Nat → Nat → List MRule
  | 0, _ => []
  | d + 1, ctxSize =>
    ⟨ctxSize + 1, existsBody entry (entry + 1) ctxSize⟩ ::
      ⟨ctxSize + 1, tupleSearch (entry + 2) leaf d (paramsFrom 0 (ctxSize + 1))⟩ ::
        tupleRules (entry + 2) leaf d (ctxSize + 1)

theorem tupleRules_length (entry leaf d ctxSize : Nat) :
    (tupleRules entry leaf d ctxSize).length = 2 * d := by
  induction d generalizing entry ctxSize with
  | zero => rfl
  | succ d ih => simp only [tupleRules, List.length_cons, ih]; omega

theorem tupleRules_firstOrder (entry leaf d ctxSize : Nat) :
    ∀ r ∈ tupleRules entry leaf d ctxSize, r.body.FirstOrder := by
  induction d generalizing entry ctxSize with
  | zero => intro r hr; cases hr
  | succ d ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact existsBody_firstOrder entry (entry + 1) ctxSize
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact tupleSearch_firstOrder _ _ _ _ (paramsFrom_firstOrder _ _)
      · exact ih _ _ r hr

def TupleRules (g : MGrammar) (entry leaf : Nat) : Nat → Nat → Prop
  | 0, _ => True
  | d + 1, ctxSize =>
    ruleAtM g.rules entry = some ⟨ctxSize + 1, existsBody entry (entry + 1) ctxSize⟩ ∧
      ruleAtM g.rules (entry + 1) =
        some ⟨ctxSize + 1, tupleSearch (entry + 2) leaf d (paramsFrom 0 (ctxSize + 1))⟩ ∧
      TupleRules g (entry + 2) leaf d (ctxSize + 1)

theorem tupleRules_rules (pre tail : List MRule) (leaf d ctxSize : Nat) :
    TupleRules ⟨pre ++ (tupleRules pre.length leaf d ctxSize ++ tail)⟩ pre.length leaf d ctxSize := by
  induction d generalizing pre ctxSize with
  | zero => trivial
  | succ d ih =>
    refine ⟨?_, ?_, ?_⟩
    · rw [show pre.length = pre.length + 0 by omega, ruleAtM_append_offset]
      rfl
    · rw [ruleAtM_append_offset]
      rfl
    · let head : List MRule :=
        [⟨ctxSize + 1, existsBody pre.length (pre.length + 1) ctxSize⟩,
          ⟨ctxSize + 1, tupleSearch (pre.length + 2) leaf d (paramsFrom 0 (ctxSize + 1))⟩]
      have hi := ih (pre ++ head) (ctxSize + 1)
      simpa only [head, tupleRules, List.length_append, List.length_cons, List.length_nil,
        Nat.add_zero, List.append_assoc, List.cons_append, List.nil_append] using hi

/-- Polynomially many candidates are tested on the same original input,
with all enclosing counters preserved. Every candidate test must terminate. -/
theorem tupleSearch_test {g : MGrammar} (entry leaf d : Nat) (ctx : List Nat)
    (hr : TupleRules g entry leaf d ctx.length) (x : List Char) (P : List Nat → Bool)
    (hP : ∀ ds, ds.length = d → (∀ k ∈ ds, k ≤ x.length) →
      Test g .callByValuePar (.call leaf (prefixValues x (ds ++ ctx))) x (P ds)) :
    Test g .callByValuePar (tupleSearch entry leaf d (prefixValues x ctx)) x
      (tupleAny x.length d P) := by
  induction d generalizing entry ctx P with
  | zero => exact hP [] rfl (by simp)
  | succ d ih =>
    obtain ⟨hEntry, hNext, hRest⟩ := hr
    have hEach : ∀ j, j ≤ x.length → Test g .callByValuePar
        (.call (entry + 1) (.lit (x.take j) :: prefixValues x ctx)) x
        (tupleAny x.length d (fun ds => P (ds ++ [j]))) := by
      intro j hj
      have hp : ∀ ds, ds.length = d → (∀ k ∈ ds, k ≤ x.length) →
          Test g .callByValuePar (.call leaf (prefixValues x (ds ++ (j :: ctx)))) x (P (ds ++ [j])) := by
        intro ds hd hv
        have hh := hP (ds ++ [j]) (by simp [hd]) (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hv k hk
          · exact (List.mem_singleton.mp hk).symm ▸ hj)
        simpa only [List.append_assoc, List.singleton_append] using hh
      have hi := ih (entry + 2) (j :: ctx) hRest (fun ds => P (ds ++ [j])) hp
      apply (par_call_iff hNext (by simp) (prefixValues_args g x (j :: ctx)) _).mpr
      rw [show ctx.length + 1 = (prefixValues x (j :: ctx)).length by simp,
        tupleSearch_subst, subst_paramsFrom]
      exact hi
    have hh := exists_obs ctx hEntry x _ hEach 0 (by omega)
    simpa only [tupleSearch, tupleAny, List.take_zero, Nat.sub_zero] using hh

theorem tupleBlock_test (pre tail : List MRule) (leaf d : Nat) (ctx : List Nat)
    (x : List Char) (P : List Nat → Bool)
    (hP : ∀ ds, ds.length = d → (∀ k ∈ ds, k ≤ x.length) →
      Test ⟨pre ++ (tupleRules pre.length leaf d ctx.length ++ tail)⟩ .callByValuePar
        (.call leaf (prefixValues x (ds ++ ctx))) x (P ds)) :
    Test ⟨pre ++ (tupleRules pre.length leaf d ctx.length ++ tail)⟩ .callByValuePar
      (tupleSearch pre.length leaf d (prefixValues x ctx)) x (tupleAny x.length d P) :=
  tupleSearch_test _ _ _ _ (tupleRules_rules pre tail leaf d ctx.length) x P hP

theorem tupleSearch_predicate {g : MGrammar} (entry leaf d : Nat) (ctx : List Nat)
    (hr : TupleRules g entry leaf d ctx.length) (x : List Char) (P : List Nat → Prop)
    [DecidablePred P]
    (hP : ∀ ds, ds.length = d → (∀ k ∈ ds, k ≤ x.length) →
      Predicate g .callByValuePar (.call leaf (prefixValues x (ds ++ ctx))) x (P ds)) :
    Predicate g .callByValuePar (tupleSearch entry leaf d (prefixValues x ctx)) x
      (∃ ds, ds.length = d ∧ (∀ k ∈ ds, k ≤ x.length) ∧ P ds) := by
  let B : List Nat → Bool := fun ds => decide (P ds)
  have ht : ∀ ds, ds.length = d → (∀ k ∈ ds, k ≤ x.length) →
      Test g .callByValuePar (.call leaf (prefixValues x (ds ++ ctx))) x (B ds) := by
    intro ds hd hv
    simpa only [Test, B, decide_eq_true_eq] using (hP ds hd hv).obs
  have hh := tupleSearch_test entry leaf d ctx hr x B ht
  have hp := Predicate.of_obs hh
  apply hp.congr
  rw [tupleAny_true_iff]
  simp only [B, decide_eq_true_eq]

end Shallot.MacroPeg.CBV.PrefixCounters
