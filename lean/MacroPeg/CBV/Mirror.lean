import MacroPeg.CBV.Spans
import Shallot.Peg.Packrat.Machine.Symbol

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine
open Shallot (stripPrefix? beqChar)

/-- Remaining-length positions index the input in reverse, with EOF at index zero. -/
def mirrorRow (x : List Char) : List Nat := (inputRow x).reverse

@[simp] theorem mirrorRow_length (x : List Char) : (mirrorRow x).length = x.length + 1 := by simp [mirrorRow]

theorem mirrorRow_get {x : List Char} {p : Nat} (hp : p ≤ x.length) :
    (mirrorRow x).getD p 0 = symbolAt x (x.length - p) := by
  have hi : p < (mirrorRow x).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [Option.getD_some, mirrorRow, List.getElem_reverse, inputRow_length, Nat.add_sub_cancel]
  exact inputRow_get x (x.length - p) (by omega)

theorem sfx_length {x : List Char} {p : Nat} (hp : p ≤ x.length) : (sfx x p).length = p := by
  simp only [sfx, List.length_drop]
  omega

theorem sfx_tail {x : List Char} {p : Nat} {c : Char} {cs : List Char}
    (hp : p ≤ x.length) (hs : sfx x p = c :: cs) : sfx x (p - 1) = cs := by
  have hl := sfx_length hp
  rw [hs] at hl
  have he : x.length - (p - 1) = x.length - p + 1 := by simp at hl; omega
  simp only [sfx, he, List.drop_add_one_eq_tail_drop]
  rw [show x.drop (x.length - p) = c :: cs from hs]
  rfl

theorem mirrorRow_cons {x : List Char} {p : Nat} {c : Char} {cs : List Char}
    (hp : p ≤ x.length) (hs : sfx x p = c :: cs) : (mirrorRow x).getD p 0 = symbolCode c := by
  rw [mirrorRow_get hp]
  have hh : x[x.length - p]? = some c := by
    rw [← List.head?_drop, show x.drop (x.length - p) = c :: cs from hs]
    rfl
  simp [symbolAt, hh]

theorem mirrorRow_nil {x : List Char} {p : Nat} (hp : p ≤ x.length) (hs : sfx x p = []) :
    (mirrorRow x).getD p 0 = 0 := by
  rw [mirrorRow_get hp]
  have hh : x[x.length - p]? = none := by
    rw [← List.head?_drop, show x.drop (x.length - p) = [] from hs]
    rfl
  simp [symbolAt, hh]

def literalCode (s input : List Char) : Nat :=
  match stripPrefix? s input with
  | none => 1
  | some rest => rest.length + 2

/-- The loop specification for a dynamic interval literal; the source interval is known valid. -/
def mirrorScan (row : List Nat) : Nat → Nat → Nat → Nat
  | 0, _, q => q + 2
  | k + 1, p, q =>
    if row.getD p 0 == row.getD q 0 && !(row.getD p 0 == 0) then
      mirrorScan row k (p - 1) (q - 1)
    else 1

/-- Dynamic span comparison is exactly ordinary literal matching, including EOF and failure. -/
theorem mirrorScan_literal (x : List Char) (k p q : Nat)
    (hk : k ≤ p) (hp : p ≤ x.length) (hq : q ≤ x.length) :
    mirrorScan (mirrorRow x) k p q = literalCode ((sfx x p).take k) (sfx x q) := by
  induction k generalizing p q with
  | zero => simp [mirrorScan, literalCode, stripPrefix?, sfx_length hq]
  | succ k ih =>
    cases hs : sfx x p with
    | nil => have hl := sfx_length hp; rw [hs] at hl; simp at hl; omega
    | cons c cs =>
      have hsrc := mirrorRow_cons hp hs
      cases ht : sfx x q with
      | nil =>
        have hdst := mirrorRow_nil hq ht
        simp only [mirrorScan, hsrc, hdst]
        simp [symbolCode, literalCode, hs, ht, stripPrefix?]
      | cons d ds =>
        have hdst := mirrorRow_cons hq ht
        have heq : (symbolCode c == symbolCode d) = beqChar c d := by simp [symbolCode, beqChar]
        have hs' := sfx_tail hp hs
        have ht' := sfx_tail hq ht
        have hn := ih (p - 1) (q - 1) (by omega) (by omega) (by omega)
        rw [hs', ht'] at hn
        simp only [mirrorScan, hsrc, hdst, heq]
        have hpos : (symbolCode c == 0) = false := by simp [symbolCode]
        simp only [hpos, Bool.not_false, Bool.and_true]
        cases h : beqChar c d with
        | false => simp [h, literalCode, hs, ht, stripPrefix?]
        | true => simpa [h, literalCode, hs, ht, stripPrefix?] using hn

/-- The dynamic matcher implements exactly the literal stored at a span identifier. -/
theorem mirrorScan_span {x : List Char} {p j q : Nat} (hp : p ≤ x.length) (hq : q ≤ x.length) :
    mirrorScan (mirrorRow x) (p - j) p q = literalCode (literalAt x (spanId x.length p j)) (sfx x q) := by
  rw [literalAt_spanId hp]
  exact mirrorScan_literal x (p - j) p q (by omega) hp hq

theorem mirrorRow_positive {x : List Char} {p : Nat} (hp : p ≤ x.length) (hpos : 0 < p) :
    0 < (mirrorRow x).getD p 0 := by
  cases hs : sfx x p with
  | nil => have hl := sfx_length hp; rw [hs] at hl; simp at hl; omega
  | cons c cs => rw [mirrorRow_cons hp hs]; unfold symbolCode; omega

/-- Final local cursors and the success flag of the bounded span comparison. -/
structure ScanEnd where
  src : Nat
  dst : Nat
  ok : Bool

def scanEnd (row : List Nat) : Nat → Nat → Nat → ScanEnd
  | 0, p, q => ⟨p, q, true⟩
  | k + 1, p, q =>
    if row.getD p 0 == row.getD q 0 && !(row.getD p 0 == 0) then
      scanEnd row k (p - 1) (q - 1)
    else ⟨p, q, false⟩

theorem scanEnd_value (row : List Nat) (k p q : Nat) :
    (if (scanEnd row k p q).ok then (scanEnd row k p q).dst + 2 else 1) = mirrorScan row k p q := by
  induction k generalizing p q with
  | zero => rfl
  | succ k ih =>
    simp only [scanEnd, mirrorScan]
    split
    · exact ih _ _
    · rfl

/-- Unicode character codes have a fixed machine-independent bound. -/
theorem symbolCode_bound (c : Char) : symbolCode c ≤ UInt32.size := by
  have hc := UInt32.toNat_lt_size c.val
  change c.val.toNat + 1 ≤ UInt32.size
  omega

theorem mirrorRow_bound (x : List Char) : ∀ v ∈ mirrorRow x, v ≤ UInt32.size := by
  intro v hv
  have hm : v ∈ x.map symbolCode ++ [0] := List.mem_reverse.mp hv
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hm
    exact symbolCode_bound c
  · have he : v = 0 := List.mem_singleton.mp hm
    subst v
    exact Nat.zero_le _

end Shallot.MacroPeg.CBV
