import MacroPeg.CBV.ParTableau.Read

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue)
open Complexity (TM Cfg)

theorem truth_test (g : MGrammar) (x : List Char) (b : Bool) :
    Test g .callByValuePar (truth b) x b := by
  cases b with
  | true => exact ⟨_, .eps x, rfl⟩
  | false => exact ⟨_, .notOk _ _ _ _ (.eps x), rfl⟩

theorem clockValue_zero (n : Nat) (ds : List Nat) :
    clockValue n ds = 0 ↔ ∀ a ∈ ds, a = 0 := by
  induction ds with
  | nil => simp [clockValue]
  | cons a ds ih => simp [clockValue, Nat.mul_eq_zero, ih]

theorem prefixValues_map (x : List Char) (ds : List Nat) :
    prefixValues x ds = ds.map (fun a => MExp.lit (x.take a)) := by
  induction ds with
  | nil => rfl
  | cons a ds ih => simp only [prefixValues, List.map_cons, ih]

theorem zeroDigits_subst (args ds : List MExp) :
    MExp.subst args (zeroDigits ds) = zeroDigits (MExp.substArgs args ds) := by
  have hm : MExp.substArgs args ds = ds.map (MExp.subst args) := by
    induction ds with
    | nil => rfl
    | cons a ds ih => simp only [MExp.substArgs, List.map_cons, ih]
  simp only [zeroDigits, conjunction_subst, List.map_map, Function.comp_def, MExp.subst,
    MExp.substArgs, hm]

theorem zeroDigits_test {g : MGrammar} (he : ruleAtM g.rules 0 = some ⟨2, equalBody 0⟩)
    (x : List Char) (ds : List Nat) (hv : ∀ a ∈ ds, a ≤ x.length) :
    Test g .callByValuePar (zeroDigits (prefixValues x ds)) x (clockValue x.length ds == 0) := by
  have hh := conjunction_test ds (fun a => MExp.call 0 [.lit (x.take a), .lit []]) (fun a => a == 0) (by
    intro a ha
    simpa only [Test, equalCall, List.take_zero, beq_iff_eq] using equal_obs he x a 0 (hv a ha) (by omega))
  have hb : ds.all (fun a => a == 0) = (clockValue x.length ds == 0) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, beq_iff_eq]
    exact (clockValue_zero x.length ds).symm
  rw [hb] at hh
  simpa only [zeroDigits, prefixValues_map, List.map_map, Function.comp_def] using hh

def inputBits (x : List Char) : List Bool := x.map (Shallot.beqChar 'b')

def inputSymbol (x : List Char) (p : Nat) : Nat :=
  match x[p]? with
  | none => 0
  | some c => if Shallot.beqChar 'b' c then 2 else 1

theorem inputSymbol_outside (x : List Char) (p : Nat) (hp : x.length ≤ p) : inputSymbol x p = 0 := by
  simp [inputSymbol, List.getElem?_eq_none hp]

theorem init_cells (k : Nat) (x : List Char) (i : Fin k) (p : Nat) :
    (Complexity.initCfg k (inputBits x)).cells i p = if i.val = 0 then inputSymbol x p else 0 := by
  simp only [Complexity.initCfg, inputBits, List.getElem?_map, inputSymbol]
  cases x[p]? <;> simp [Complexity.bitSym]

theorem falseChar_test (g : MGrammar) (x : List Char) (p : Nat) :
    Test g .callByValuePar
      (atPosition (.lit (x.take p)) (.seq (.notP (.chr 'b')) .any)) x
      (match x[p]? with | none => false | some c => !Shallot.beqChar 'b' c) := by
  have hl : SObs g .callByValuePar (.lit (x.take p)) x (some (x.drop p)) :=
    ⟨_, literal_take g .callByValuePar x p, rfl⟩
  rw [← List.head?_drop]
  cases hd : x.drop p with
  | nil =>
    have hn : SObs g .callByValuePar (.chr 'b') (x.drop p) none :=
      ⟨_, by rw [hd]; exact .chrEmpty 'b', rfl⟩
    have ha : SObs g .callByValuePar .any (x.drop p) none := ⟨_, by rw [hd]; exact .anyFail, rfl⟩
    exact peek_failure (seq_ok hl (seq_ok (not_fail hn) ha))
  | cons c cs =>
    cases hb : Shallot.beqChar 'b' c with
    | true =>
      have hc : SObs g .callByValuePar (.chr 'b') (x.drop p) (some cs) :=
        ⟨_, by rw [hd]; exact .chrOk 'b' c cs hb, rfl⟩
      simpa only [atPosition, List.head?_cons, hb, Bool.not_true] using
        peek_failure (seq_ok hl (seq_fail (not_ok hc)))
    | false =>
      have hc : SObs g .callByValuePar (.chr 'b') (x.drop p) none :=
        ⟨_, by rw [hd]; exact .chrFail 'b' c cs hb, rfl⟩
      have ha : SObs g .callByValuePar .any (x.drop p) (some cs) :=
        ⟨_, by rw [hd]; exact .anyOk c cs, rfl⟩
      simpa only [atPosition, List.head?_cons, hb, Bool.not_false] using
        peek_success (seq_ok hl (seq_ok (not_fail hc) ha))

end Shallot.MacroPeg.CBV.ParTableau
