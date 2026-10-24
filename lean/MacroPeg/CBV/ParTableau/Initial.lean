import MacroPeg.CBV.ParTableau.Atoms

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue paramsFrom subst_paramsFrom_slice subst_paramsFrom)
open Complexity (TM Cfg)

theorem subst_truth (args : List MExp) (b : Bool) : MExp.subst args (truth b) = truth b := by
  cases b <;> rfl

private def pieces (high low : MExp) (s : Nat) : MExp :=
  if s = 0 then .alt (.notP high) (atEnd low)
  else if s = 1 then .seq high (atPosition low (.seq (.notP (.chr 'b')) .any))
  else if s = 2 then .seq high (atPosition low (.chr 'b'))
  else MExp.failAlways

private theorem scalar_tests (g : MGrammar) (x : List Char) (p : Nat) (hp : p ≤ x.length) :
    Test g .callByValuePar (atEnd (.lit (x.take p))) x (inputSymbol x p == 0) ∧
    Test g .callByValuePar (atPosition (.lit (x.take p)) (.seq (.notP (.chr 'b')) .any)) x
      (inputSymbol x p == 1) ∧
    Test g .callByValuePar (atPosition (.lit (x.take p)) (.chr 'b')) x (inputSymbol x p == 2) := by
  have he := end_obs g x p hp
  have hf := falseChar_test g x p
  have ht := charAt_test g x p 'b'
  cases hx : x[p]? with
  | none =>
    have hn : p = x.length := by have := List.getElem?_eq_none_iff.mp hx; omega
    simpa [Test, inputSymbol, charAt, hx, hn] using And.intro he (And.intro hf ht)
  | some c =>
    have hn : p ≠ x.length := by have := (List.getElem?_eq_some_iff.mp hx).1; omega
    cases hb : Shallot.beqChar 'b' c <;>
      simpa [Test, inputSymbol, charAt, hx, hn, hb] using And.intro he (And.intro hf ht)

private theorem pieces_test {g : MGrammar} (x : List Char) (high : MExp) (b : Bool)
    (hh : Test g .callByValuePar high x b) (p : Nat) (hp : p ≤ x.length) (s : Nat) :
    Test g .callByValuePar (pieces high (.lit (x.take p)) s) x
      (if b then inputSymbol x p == s else 0 == s) := by
  obtain ⟨h0, h1, h2⟩ := scalar_tests g x p hp
  by_cases hs0 : s = 0
  · subst s
    have ht := test_alt (test_not hh) h0
    cases b <;> simpa [pieces, Test] using ht
  · by_cases hs1 : s = 1
    · subst s
      have ht := test_seq hh h1
      cases b <;> simpa [pieces, Test] using ht
    · by_cases hs2 : s = 2
      · subst s
        have ht := test_seq hh h2
        cases b <;> simpa [pieces, Test] using ht
      · have hv : inputSymbol x p ≤ 2 := by
          cases hx : x[p]? with
          | none => simp [inputSymbol, hx]
          | some c => simp only [inputSymbol, hx]; split <;> omega
        have hfalse : (inputSymbol x p == s) = false := Bool.eq_false_iff.mpr (by
          intro he; have := eq_of_beq he; omega)
        have hz : (0 == s) = false := Bool.eq_false_iff.mpr (fun he => hs0 (eq_of_beq he).symm)
        cases b <;> simpa [pieces, hs0, hs1, hs2, hfalse, hz, truth] using truth_test g x false

private theorem initialCell_subst (x : List Char) (ds : List Nat) (s : Nat) :
    MExp.subst (prefixValues x ds) (initialCell ds.length s) =
      pieces (zeroDigits (prefixValues x ds.tail)) (.lit (x.take (ds.headD 0))) s := by
  cases ds with
  | nil =>
    by_cases h0 : s = 0 <;> by_cases h1 : s = 1 <;> by_cases h2 : s = 2 <;>
      simp [initialCell, pieces, lowDigit, zeroDigits, conjunction, prefixValues, paramsFrom,
        MExp.subst, atEnd, atPosition, MExp.andP, MExp.failAlways, h0, h1, h2]
  | cons a ds =>
    have hh := subst_paramsFrom_slice [.lit (x.take a)] (prefixValues x ds) []
    simp only [List.length_cons, List.length_nil, List.singleton_append, List.append_nil,
      prefixValues_length] at hh
    by_cases h0 : s = 0 <;> by_cases h1 : s = 1 <;> by_cases h2 : s = 2 <;>
      simp [initialCell, pieces, lowDigit, List.length_cons, prefixValues, MExp.subst,
        zeroDigits_subst, hh, argAt, atEnd, atPosition, MExp.andP, MExp.failAlways, h0, h1, h2]

theorem initialCell_test {g : MGrammar} (he : ruleAtM g.rules 0 = some ⟨2, equalBody 0⟩)
    (x : List Char) (ds : List Nat) (hv : ∀ a ∈ ds, a ≤ x.length) (s : Nat) :
    Test g .callByValuePar (MExp.subst (prefixValues x ds) (initialCell ds.length s)) x
      (inputSymbol x (clockValue x.length ds) == s) := by
  rw [initialCell_subst]
  have htail : ∀ a ∈ ds.tail, a ≤ x.length := fun a ha => hv a (List.mem_of_mem_tail ha)
  have hlow : ds.headD 0 ≤ x.length := by
    cases ds with
    | nil => simp
    | cons a ds => exact hv a (by simp)
  have hh := pieces_test x _ _ (zeroDigits_test he x ds.tail htail) (ds.headD 0) hlow s
  have hb : (if clockValue x.length ds.tail == 0 then inputSymbol x (ds.headD 0) == s else 0 == s) =
      (inputSymbol x (clockValue x.length ds) == s) := by
    cases ds with
    | nil => simp [clockValue]
    | cons a ds =>
      simp only [List.tail_cons, List.headD_cons, clockValue]
      by_cases hz : clockValue x.length ds = 0
      · simp [hz]
      · have hn : x.length ≤ a + (x.length + 1) * clockValue x.length ds := by
          have hh := Nat.le_mul_of_pos_right (x.length + 1) (Nat.pos_of_ne_zero hz)
          omega
        have hfalse : (clockValue x.length ds == 0) = false := Bool.eq_false_iff.mpr (fun he => hz (eq_of_beq he))
        simp only [hfalse, Bool.false_eq_true, if_false, inputSymbol_outside x _ hn]
  rw [hb] at hh
  exact hh

def queryBit {k : Nat} (c : Cfg k) (p : Nat) : Node k → Bool
  | .state q => c.state == q
  | .head i => c.pos i == p
  | .cell i s => c.cells i p == s
  | _ => false

theorem zeroBody_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) (position : List Nat)
    (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length) (node : Node k) (ht : Timed node) :
    Test (compile M d) .callByValuePar (MExp.subst (prefixValues x position) (zeroBody d node)) x
      (queryBit (Complexity.initCfg k (inputBits x)) (clockValue x.length position) node) := by
  cases node with
  | state q =>
    simpa only [zeroBody, subst_truth, queryBit, Complexity.initCfg, Bool.beq_comm] using
      truth_test (compile M d) x (q == 2)
  | head i =>
    have hs : MExp.substArgs (prefixValues x position) (paramsFrom 0 d) = prefixValues x position := by
      simpa only [prefixValues_length, hp] using subst_paramsFrom (prefixValues x position)
    rw [zeroBody, zeroDigits_subst, hs]
    simpa only [queryBit, Complexity.initCfg, Bool.beq_comm] using zeroDigits_test (equal_rule M d) x position hv
  | cell i s =>
    simp only [zeroBody, queryBit, init_cells]
    by_cases hi : i.val = 0
    · simp only [if_pos hi]
      simpa only [hp] using initialCell_test (equal_rule M d) x position hv s
    · simp only [if_neg hi]
      simpa only [subst_truth, Bool.beq_comm] using truth_test (compile M d) x (s == 0)
  | read _ _ | incHead _ | decHead _ => cases ht

end Shallot.MacroPeg.CBV.ParTableau
