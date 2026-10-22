import Shallot.Peg.Packrat.Machine.Test

/-!
# Input symbols and fixed lexical tests

A character is encoded as its codepoint plus one; zero is the end marker.
The fixed tables for character and range tests can be compiled by `dispatch`.
-/

namespace Shallot.Packrat.Machine

/-- Character codes are positive, leaving zero for end of input. -/
def symbolCode (c : Char) : Nat := c.toNat + 1

/-- The input, in position order, followed by its end marker. -/
def inputRow (x : List Char) : List Nat := x.map symbolCode ++ [0]

/-- The symbol at a position, or the end marker. -/
def symbolAt (x : List Char) (i : Nat) : Nat := (x[i]?.map symbolCode).getD 0

@[simp] theorem inputRow_length (x : List Char) : (inputRow x).length = x.length + 1 := by
  simp [inputRow]

theorem inputRow_lookup (x : List Char) (i : Nat) (hi : i ≤ x.length) :
    (inputRow x)[i]? = some (symbolAt x i) := by
  unfold inputRow
  by_cases hlt : i < x.length
  · rw [List.getElem?_append_left (l₁ := x.map symbolCode) (l₂ := [0]) (by simpa using hlt)]
    simp [symbolAt, List.getElem?_eq_getElem hlt]
  · have he : i = x.length := by omega
    subst i
    rw [List.getElem?_append_right (l₁ := x.map symbolCode) (l₂ := [0]) (by simp)]
    simp [symbolAt]

theorem inputRow_get (x : List Char) (i : Nat) (hi : i ≤ x.length) :
    (inputRow x)[i]'(by simp; omega) = symbolAt x i := by
  have h := inputRow_lookup x i hi
  simpa only [List.getElem?_eq_getElem (l := inputRow x) (i := i) (by simp; omega), Option.some.injEq] using h

structure SymbolTest where
  flags : List Bool
  fallback : Bool

def SymbolTest.eval (t : SymbolTest) (v : Nat) : Bool := (t.flags[v]?).getD t.fallback

/-- Compile a test below a fixed cutoff, rejecting all larger numbers. -/
def finiteTest (cutoff : Nat) (test : Nat → Bool) : SymbolTest :=
  ⟨(List.range cutoff).map test, false⟩

theorem finiteTest_eval (cutoff : Nat) (test : Nat → Bool) (v : Nat) :
    (finiteTest cutoff test).eval v = if v < cutoff then test v else false := by
  simp only [finiteTest, SymbolTest.eval, List.getElem?_map]
  by_cases hv : v < cutoff
  · simp [hv]
  · simp [hv]

def anyTest : SymbolTest := ⟨[false], true⟩

def chrTest (c : Char) : SymbolTest :=
  finiteTest (c.toNat + 2) (fun v => decide (v = c.toNat + 1))

def rangeTest (lo hi : Char) : SymbolTest :=
  finiteTest (hi.toNat + 2) (fun v => decide (0 < v ∧ lo.toNat + 1 ≤ v))

@[simp] theorem anyTest_end : anyTest.eval 0 = false := rfl
@[simp] theorem anyTest_char (c : Char) : anyTest.eval (symbolCode c) = true := by
  simp [anyTest, SymbolTest.eval, symbolCode]

@[simp] theorem chrTest_end (c : Char) : (chrTest c).eval 0 = false := by
  simp [chrTest, finiteTest_eval]

@[simp] theorem chrTest_char (c d : Char) : (chrTest c).eval (symbolCode d) = beqChar c d := by
  unfold chrTest
  rw [finiteTest_eval]
  by_cases he : c.toNat = d.toNat
  · simp [symbolCode, he, beqChar]
  · by_cases hl : d.toNat + 1 < c.toNat + 2
    · simp [symbolCode, hl, beqChar, he, Ne.symm he]
    · simp [symbolCode, hl, beqChar, he]

@[simp] theorem rangeTest_end (lo hi : Char) : (rangeTest lo hi).eval 0 = false := by
  simp [rangeTest, finiteTest_eval]

@[simp] theorem rangeTest_char (lo hi d : Char) :
    (rangeTest lo hi).eval (symbolCode d) = (leChar lo d && leChar d hi) := by
  apply Bool.eq_iff_iff.mpr
  simp only [rangeTest, finiteTest_eval, symbolCode, Bool.and_eq_true, leChar, Nat.ble_eq]
  by_cases hl : d.toNat + 1 < hi.toNat + 2
  · simp only [hl, if_true, decide_eq_true_eq]
    omega
  · have hn : ¬ d.toNat ≤ hi.toNat := by omega
    simp [hl, hn]

end Shallot.Packrat.Machine
