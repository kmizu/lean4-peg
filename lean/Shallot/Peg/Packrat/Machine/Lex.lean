import Shallot.Peg.Packrat.Machine.Symbol

/-!
# One-character lexical cells

The input row is read by the same verified lookup as expression rows.
Successful lexical tests consume one character; failed tests return the
numeric failure code. EOF is tested explicitly and never consumed.
-/

namespace Shallot.Packrat.Machine

open Complexity

variable {K : Nat}

/-- Append a success consuming one character from the current position. -/
def oneSuccess (p out : Fin K) (hpo : p ≠ out) : NProg K :=
  .seq (emptySuccess p out hpo) (.prim (.inc out))

theorem nruns_oneSuccess (p out : Fin K) (hpo : p ≠ out) (S : Lists K)
    {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) :
    NRuns (oneSuccess p out hpo) S (S.set out (S out ++ [i + 3])) 4 := by
  have es := nruns_emptySuccess p out hpo S hp
  have ic := nruns_inc out (S.set out (S out ++ [i + 2])) (l := S out) (v := i + 2) (by simp)
  simp only [Lists.set_set_u] at ic
  exact es.seq ic

/-- A fixed lexical test compiled into an input-row lookup and branch. -/
def lexCell (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hpo : p ≠ out) (t : SymbolTest) : NProg K :=
  readTest r tmp idx p work hrT hTw hpi t.flags t.fallback (oneSuccess p out hpo) (npushC out 1)

theorem nruns_lexCell (r tmp idx p work out : Fin K) (hrT : r ≠ tmp) (hTw : tmp ≠ work)
    (hpi : p ≠ idx) (hpo : p ≠ out) (hd : [r, tmp, idx, p, work].Nodup)
    (t : SymbolTest) (S : Lists K) (hT : S tmp = []) {lp : List Nat} {i : Nat}
    (hp : S p = lp ++ [i]) (hi : i < (S r).length) :
    NRuns (lexCell r tmp idx p work out hrT hTw hpi hpo t) S
      (S.set out (S out ++ [if t.eval ((S r)[i]) then i + 3 else 1]))
      (6 * (S r).length + 4 * i + 2 * t.flags.length + 14) := by
  apply nruns_readTest r tmp idx p work hrT hTw hpi hd t.flags t.fallback _ _ S _ hT hp hi
  change NRuns (if t.eval ((S r)[i]) then _ else _) _ _ _
  cases hb : t.eval ((S r)[i]) with
  | false => simpa [hb] using (nruns_pushC out S 1).mono (show 1 + 1 ≤ 4 by omega)
  | true => simpa [hb] using nruns_oneSuccess p out hpo S hp

/-- The numerical value of a one-character test on the input. -/
def lexValue (t : SymbolTest) (x : List Char) (i : Nat) : Nat :=
  if t.eval (symbolAt x i) then i + 3 else 1

/-- A lexical cell's stack-step bound is linear in input length. -/
theorem nruns_lexCell_input (x : List Char) (r tmp idx p work out : Fin K)
    (hrT : r ≠ tmp) (hTw : tmp ≠ work) (hpi : p ≠ idx) (hpo : p ≠ out)
    (hd : [r, tmp, idx, p, work].Nodup) (t : SymbolTest) (S : Lists K) (hT : S tmp = [])
    (hr : S r = inputRow x) {lp : List Nat} {i : Nat} (hp : S p = lp ++ [i]) (hi : i ≤ x.length) :
    NRuns (lexCell r tmp idx p work out hrT hTw hpi hpo t) S
      (S.set out (S out ++ [lexValue t x i])) (10 * x.length + 2 * t.flags.length + 20) := by
  have hri : i < (S r).length := by simp only [hr, inputRow_length]; omega
  have hx := nruns_lexCell r tmp idx p work out hrT hTw hpi hpo hd t S hT hp hri
  have hv : (S r)[i] = symbolAt x i := by simp only [hr, inputRow_get x i hi]
  rw [hv] at hx
  apply hx.mono
  have hl : (S r).length = x.length + 1 := by simp [hr]
  omega

theorem anyValue (g : Grammar) (x : List Char) (T : Tbl) (i : Nat) :
    lexValue anyTest x i = code i (F g x T .any i) := by
  unfold lexValue symbolAt
  by_cases hi : i < x.length
  · simp [F, code, hi, Nat.add_assoc]
  · simp [F, code, hi]

theorem chrValue (g : Grammar) (x : List Char) (T : Tbl) (c : Char) (i : Nat) :
    lexValue (chrTest c) x i = code i (F g x T (.chr c) i) := by
  unfold lexValue symbolAt
  simp only [F]
  cases hs : x[i]? with
  | none => simp [code]
  | some d => cases hc : beqChar c d <;> simp [code, hc, Nat.add_assoc]

theorem rangeValue (g : Grammar) (x : List Char) (T : Tbl) (lo hi : Char) (i : Nat) :
    lexValue (rangeTest lo hi) x i = code i (F g x T (.range lo hi) i) := by
  unfold lexValue symbolAt
  simp only [F]
  cases hs : x[i]? with
  | none => simp [code]
  | some d => cases hc : (leChar lo d && leChar d hi) <;> simp [code, hc, Nat.add_assoc]

end Shallot.Packrat.Machine
