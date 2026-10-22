import Shallot.Peg.Packrat.Machine.Lex

/-!
# Literal strings on the stack machine

A literal is compiled into a fixed sequence of character tests. A private
cursor advances only after a matched character and is removed at the end.
The caller's position and all input/table rows are preserved.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Matching a character requires a real input character, never the end marker. -/
theorem chrTest_in_bounds {x : List Char} {i : Nat} {c : Char}
    (h : (chrTest c).eval (symbolAt x i) = true) : i < x.length := by
  apply Classical.byContradiction
  intro hi
  have hn : x[i]? = none := List.getElem?_eq_none (by omega)
  simp [symbolAt, hn] at h

/-- The numerical result and the final private cursor of a literal scan. -/
def literalScan : List Char → List Char → Nat → Nat × Nat
  | [], _, i => (i + 2, i)
  | c :: cs, x, i =>
    if (chrTest c).eval (symbolAt x i) then literalScan cs x (i + 1) else (1, i)

/-- The scan computes the same entry as the original literal rule. -/
theorem literalScan_value (g : Grammar) (x : List Char) (T : Tbl) (s : List Char) (i : Nat) :
    (literalScan s x i).1 = code i (F g x T (.lit s) i) := by
  induction s generalizing i with
  | nil => rfl
  | cons c cs ih =>
    have hx : x[i]? = (x.drop i).head? := List.head?_drop.symm
    cases hd : x.drop i with
    | nil =>
      simp [literalScan, symbolAt, hx, hd, F, stripPrefix?, code]
    | cons d rest =>
      have hdrop : x.drop (i + 1) = rest := by rw [← List.drop_drop, hd]; rfl
      have hs : (chrTest c).eval (symbolAt x i) = beqChar c d := by simp [symbolAt, hx, hd]
      simp only [literalScan, hs]
      cases hc : beqChar c d with
      | false => simp [F, hd, stripPrefix?, hc, code]
      | true =>
        simp only [if_true]
        rw [ih]
        simp only [F, hd, stripPrefix?, hc, if_true, hdrop]
        cases stripPrefix? cs rest <;> simp [code, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Each scan stays within the input when started at a valid position. -/
theorem literalScan_bound (s : List Char) (x : List Char) (i : Nat) (hi : i ≤ x.length) :
    (literalScan s x i).2 ≤ x.length := by
  induction s generalizing i with
  | nil => exact hi
  | cons c cs ih =>
    simp only [literalScan]
    split
    · rename_i h
      exact ih (i + 1) (by have := chrTest_in_bounds h; omega)
    · exact hi

/-- A stack-step budget for the literal body. -/
def literalCost : List Char → Nat → Nat
  | [], _ => 3
  | c :: cs, n => 10 * n + 2 * (chrTest c).flags.length + 21 + literalCost cs n

theorem literalCost_pos (s : List Char) (n : Nat) : 3 ≤ literalCost s n := by
  cases s <;> simp only [literalCost] <;> omega

/-- For a fixed literal, the budget is linear in input length. -/
theorem literalCost_eq (s : List Char) (n : Nat) :
    literalCost s n = 10 * s.length * n + literalCost s 0 := by
  induction s with
  | nil => simp [literalCost]
  | cons c cs ih =>
    simp only [literalCost, List.length_cons, Nat.mul_succ, Nat.add_mul, Nat.mul_zero, ih]
    omega

theorem literalCost_le (s : List Char) (n : Nat) :
    literalCost s n + 2 ≤ (10 * s.length + literalCost s 0 + 2) * (n + 1) := by
  rw [literalCost_eq s n, Nat.mul_succ]
  have hm := Nat.mul_le_mul_right n (show 10 * s.length ≤ 10 * s.length + literalCost s 0 + 2 by omega)
  omega

/-- Scan using the top of `cur` as the private cursor. -/
def literalBody (r tmp idx cur work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hci : cur ≠ idx) (hco : cur ≠ out) : List Char → NProg K
  | [] => emptySuccess cur out hco
  | c :: cs => readTest r tmp idx cur work hrT hTw hci (chrTest c).flags (chrTest c).fallback
      (.seq (.prim (.inc cur)) (literalBody r tmp idx cur work out hrT hTw hci hco cs))
      (npushC out 1)

/-- The literal body realizes the scan with a concrete bounded execution. -/
theorem nruns_literalBody (x : List Char) (r tmp idx cur work out : Fin K)
    (hrT : r ≠ tmp) (hTw : tmp ≠ work) (hci : cur ≠ idx) (hco : cur ≠ out)
    (hd : [r, tmp, idx, cur, work].Nodup) (s : List Char) (S : Lists K)
    (hT : S tmp = []) (hr : S r = inputRow x) {lc : List Nat} {i : Nat}
    (hc : S cur = lc ++ [i]) (hi : i ≤ x.length) :
    NRuns (literalBody r tmp idx cur work out hrT hTw hci hco s) S
      ((S.set cur (lc ++ [(literalScan s x i).2])).set out (S out ++ [(literalScan s x i).1]))
      (literalCost s x.length) := by
  have hrc : r ≠ cur := by simp_all [List.nodup_cons]
  have hTc : tmp ≠ cur := by simp_all [List.nodup_cons]
  have hoc : out ≠ cur := Ne.symm hco
  induction s generalizing S i with
  | nil =>
    simpa only [literalBody, literalScan, ← hc, Lists.set_get_self, literalCost] using
      nruns_emptySuccess cur out hco S hc
  | cons c cs ih =>
    have hri : i < (S r).length := by simp only [hr, inputRow_length]; omega
    have hv : (S r)[i] = symbolAt x i := by simp only [hr, inputRow_get x i hi]
    have hb : NRuns
        (if (chrTest c).eval ((S r)[i]) then
          .seq (.prim (.inc cur)) (literalBody r tmp idx cur work out hrT hTw hci hco cs)
        else npushC out 1) S
        ((S.set cur (lc ++ [(literalScan (c :: cs) x i).2])).set out
          (S out ++ [(literalScan (c :: cs) x i).1])) (1 + literalCost cs x.length) := by
      rw [hv]
      cases ht : (chrTest c).eval (symbolAt x i) with
      | false =>
        simp only [ht, Bool.false_eq_true, if_false, literalScan]
        simp only [← hc, Lists.set_get_self]
        exact (nruns_pushC out S 1).mono (by have := literalCost_pos cs x.length; omega)
      | true =>
        simp only [ht, if_true, literalScan]
        have hlt := chrTest_in_bounds ht
        have ic := nruns_inc cur S hc
        let S₁ := S.set cur (lc ++ [i + 1])
        have bx := ih S₁ (i := i + 1) (by simp only [S₁, Lists.set_ne _ _ hTc]; exact hT)
          (by simp only [S₁, Lists.set_ne _ _ hrc]; exact hr) (by simp [S₁]) (by omega)
        have he : (S₁.set cur (lc ++ [(literalScan cs x (i + 1)).2])).set out
            (S₁ out ++ [(literalScan cs x (i + 1)).1]) =
            (S.set cur (lc ++ [(literalScan cs x (i + 1)).2])).set out
            (S out ++ [(literalScan cs x (i + 1)).1]) := by
          simp only [S₁, Lists.set_ne _ _ hoc, Lists.set_set_u]
        rw [he] at bx
        exact ic.seq bx
    have rd := nruns_readTest r tmp idx cur work hrT hTw hci hd (chrTest c).flags
      (chrTest c).fallback _ _ S _ hT hc hri hb
    apply rd.mono
    have hl : (S r).length = x.length + 1 := by simp [hr]
    simp only [literalCost]
    omega

/-- Copy the caller's position, scan, and remove the private cursor. -/
def literalCell (r tmp idx p cur work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hci : cur ≠ idx) (hco : cur ≠ out) (hpc : p ≠ cur) (s : List Char) : NProg K :=
  .seq (.prim (.dup p cur hpc))
    (.seq (literalBody r tmp idx cur work out hrT hTw hci hco s) (.prim (.pop cur)))

/-- A literal cell preserves all stacks except its output. -/
theorem nruns_literalCell (g : Grammar) (x : List Char) (n : Nat) (s : List Char)
    (r tmp idx p cur work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hci : cur ≠ idx) (hco : cur ≠ out) (hpc : p ≠ cur)
    (hd : [r, tmp, idx, cur, work].Nodup) (S : Lists K) (hT : S tmp = [])
    (hr : S r = inputRow x) {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (literalCell r tmp idx p cur work out hrT hTw hci hco hpc s) S
      (S.set out (S out ++ [code i (iter g x (n + 1) (.lit s) i)]))
      (literalCost s x.length + 2) := by
  have hrc : r ≠ cur := by simp_all [List.nodup_cons]
  have hTc : tmp ≠ cur := by simp_all [List.nodup_cons]
  have hoc : out ≠ cur := Ne.symm hco
  have cp := nruns_dup p cur hpc S hp
  let S₁ := S.set cur (S cur ++ [i])
  have bx := nruns_literalBody x r tmp idx cur work out hrT hTw hci hco hd s S₁
    (by simp only [S₁, Lists.set_ne _ _ hTc]; exact hT) (by simp only [S₁, Lists.set_ne _ _ hrc]; exact hr)
    (lc := S cur) (i := i) (by simp [S₁]) hi
  let S₂ := (S₁.set cur (S cur ++ [(literalScan s x i).2])).set out (S₁ out ++ [(literalScan s x i).1])
  have pp := nruns_pop cur S₂ (l := S cur) (v := (literalScan s x i).2)
    (by simp only [S₂, Lists.set_ne _ _ hco, Lists.set_same])
  have he : S₂.set cur (S cur) = S.set out (S out ++ [(literalScan s x i).1]) := by
    simp only [S₂, S₁]; lists_eq
  rw [he, literalScan_value g x (iter g x n) s i] at pp
  exact (cp.seq (bx.seq pp)).mono (by omega)

end Shallot.Packrat.Machine
