import MacroPeg.CBV.FixedLiteral
import MacroPeg.CBV.Eval

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.KExp

/-- A one-character match returns the code of one fewer remaining character. -/
def remainingSuccessP {K : Nat} (r : LiteralRegs K) : NProg K :=
  .seq (.prim (.dup (r.get 15) (r.get 16) (r.ne (by decide)))) (.prim (.inc (r.get 16)))

theorem remainingSuccess_runs {K : Nat} (r : LiteralRegs K) (S : Lists K) {lp : List Nat} {q : Nat}
    (hp : S (r.get 15) = lp ++ [q]) :
    NRuns (remainingSuccessP r) S (S.set (r.get 16) (S (r.get 16) ++ [q + 1])) 2 := by
  have xd := nruns_dup (r.get 15) (r.get 16) (r.ne (by decide)) S hp
  have xi := nruns_inc (r.get 16) (S.set (r.get 16) (S (r.get 16) ++ [q]))
    (l := S (r.get 16)) (v := q) (by simp)
  simp only [Lists.set_set_u] at xi
  exact xd.seq xi

def remainingLexP {K : Nat} (r : LiteralRegs K) (t : SymbolTest) : NProg K :=
  readTest (r.get 0) (r.get 1) (r.get 2) (r.get 15) (r.get 5)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) t.flags t.fallback
    (remainingSuccessP r) (npushC (r.get 16) 1)

def remainingLexValue (t : SymbolTest) (x : List Char) (q : Nat) : Nat :=
  if t.eval ((mirrorRow x).getD q 0) then q + 1 else 1

def remainingLexCost (t : SymbolTest) (n : Nat) : Nat := 10 * n + 2 * t.flags.length + 18

theorem remainingLex_runs {K : Nat} (r : LiteralRegs K) (t : SymbolTest) (S : Lists K)
    (x : List Char) (hrow : S (r.get 0) = mirrorRow x) (ht : S (r.get 1) = [])
    {lp : List Nat} {q : Nat} (hp : S (r.get 15) = lp ++ [q]) (hq : q ≤ x.length) :
    NRuns (remainingLexP r t) S (S.set (r.get 16) (S (r.get 16) ++ [remainingLexValue t x q]))
      (remainingLexCost t x.length) := by
  have hri : q < (S (r.get 0)).length := by rw [hrow, mirrorRow_length]; omega
  have hv : (S (r.get 0))[q] = (mirrorRow x).getD q 0 := by
    exact (List.getElem_eq_getD 0).trans (congrArg (fun row : List Nat => row.getD q 0) hrow)
  have hb : NRuns (if t.eval ((S (r.get 0))[q]) then remainingSuccessP r else npushC (r.get 16) 1) S
      (S.set (r.get 16) (S (r.get 16) ++ [remainingLexValue t x q])) 2 := by
    rw [hv]
    cases he : t.eval ((mirrorRow x).getD q 0) with
    | false => simpa only [remainingLexValue, he, Bool.false_eq_true, if_false] using nruns_pushC (r.get 16) S 1
    | true => simpa only [remainingLexValue, he, if_true] using remainingSuccess_runs r S hp
  have hd : [r.get 0, r.get 1, r.get 2, r.get 15, r.get 5].Nodup := by simp [List.nodup_cons]
  have hx := nruns_readTest (r.get 0) (r.get 1) (r.get 2) (r.get 15) (r.get 5)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) hd t.flags t.fallback _ _ S _ ht hp hri hb
  exact hx.mono (by rw [hrow, mirrorRow_length]; unfold remainingLexCost; omega)

theorem remainingLexCost_poly (t : SymbolTest) : IsPoly (remainingLexCost t) :=
  isPoly_add (isPoly_add (isPoly_mul (isPoly_const 10) isPoly_id) (isPoly_const _)) (isPoly_const 18)

/-- The lexical cell agrees with the CBV numerical evaluator on `any`. -/
theorem remainingLex_any (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (q : Nat) (hq : q ≤ x.length) :
    remainingLexValue anyTest x q = resultCode (eval g x s row E .any q) := by
  cases hs : sfx x q with
  | nil => simp only [remainingLexValue, mirrorRow_nil hq hs, anyTest_end]; simp [eval, hs, resultCode]
  | cons c cs =>
    have hl := sfx_length hq
    rw [hs] at hl
    simp only [List.length_cons] at hl
    simp only [remainingLexValue, mirrorRow_cons hq hs, anyTest_char, if_true]
    simp only [eval, hs, resultCode]
    omega

theorem remainingLex_chr (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (c : Char) (q : Nat) (hq : q ≤ x.length) :
    remainingLexValue (chrTest c) x q = resultCode (eval g x s row E (.chr c) q) := by
  cases hs : sfx x q with
  | nil => simp only [remainingLexValue, mirrorRow_nil hq hs, chrTest_end]; simp [eval, hs, resultCode]
  | cons d ds =>
    have hl := sfx_length hq
    rw [hs] at hl
    simp only [List.length_cons] at hl
    simp only [remainingLexValue, mirrorRow_cons hq hs, chrTest_char]
    cases he : Shallot.beqChar c d <;> simp only [eval, hs, he, Bool.false_eq_true, if_false, if_true, resultCode] <;> omega

theorem remainingLex_range (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (lo hi : Char) (q : Nat) (hq : q ≤ x.length) :
    remainingLexValue (rangeTest lo hi) x q = resultCode (eval g x s row E (.range lo hi) q) := by
  cases hs : sfx x q with
  | nil => simp only [remainingLexValue, mirrorRow_nil hq hs, rangeTest_end]; simp [eval, hs, resultCode]
  | cons d ds =>
    have hl := sfx_length hq
    rw [hs] at hl
    simp only [List.length_cons] at hl
    simp only [remainingLexValue, mirrorRow_cons hq hs, rangeTest_char]
    cases he : (Shallot.leChar lo d && Shallot.leChar d hi) <;> simp only [eval, hs, he, Bool.false_eq_true, if_false, if_true, resultCode] <;> omega

theorem literalCode_eval (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (w : List Char) (q : Nat) :
    literalCode w (sfx x q) = resultCode (eval g x s row E (.lit w) q) := by
  simp only [literalCode, eval]
  cases Shallot.stripPrefix? w (sfx x q) <;> rfl

end Shallot.MacroPeg.CBV
