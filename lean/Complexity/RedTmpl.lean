import Complexity.Tmpl
import Complexity.TopFormula

/-!
# The reduction's output as a template

`redTmpl M` describes the token list of `redQbf M S w` (`redTmpl_denote`, proved in `RedTmplSpec.lean`) in the
environment `⟨w, S, blockSize M S, _⟩`. Loops over constant ranges (states, symbols, tapes, transition combinations)
are unrolled when the template is built; only the cell loops (`S`) and the level loop (`T`) are template loops.
Counters: `0` the level (`ℓ = T - ctr 0`), `1` a cell, `2` a second cell, `3` the cell of a read.
-/

namespace Complexity

/-! ## RPN token lists of formulas -/

def rpnEnc (φ : Formula) : List Nat := (toRPN φ).flatMap RTok.enc

theorem rpnEnc_var (x : Name) : rpnEnc (.var x) = Tok.var :: encName x := by simp [rpnEnc, toRPN, RTok.enc]
theorem rpnEnc_tt : rpnEnc .tt = [Tok.tt] := rfl
theorem rpnEnc_ff : rpnEnc .ff = [Tok.ff] := rfl
theorem rpnEnc_not (a : Formula) : rpnEnc (.not a) = rpnEnc a ++ [Tok.neg] := by
  simp [rpnEnc, toRPN, RTok.enc]
theorem rpnEnc_and (a b : Formula) : rpnEnc (.and a b) = rpnEnc a ++ rpnEnc b ++ [Tok.conj] := by
  simp [rpnEnc, toRPN, RTok.enc]
theorem rpnEnc_or (a b : Formula) : rpnEnc (.or a b) = rpnEnc a ++ rpnEnc b ++ [Tok.disj] := by
  simp [rpnEnc, toRPN, RTok.enc]

theorem rpnEnc_bigAnd : ∀ l : List Formula,
    rpnEnc (bigAnd l) = l.flatMap rpnEnc ++ [Tok.tt] ++ List.replicate l.length Tok.conj
  | [] => rfl
  | a :: as => by
    rw [bigAnd, rpnEnc_and, rpnEnc_bigAnd as]
    simp [List.replicate_succ']

theorem rpnEnc_bigOr : ∀ l : List Formula,
    rpnEnc (bigOr l) = l.flatMap rpnEnc ++ [Tok.ff] ++ List.replicate l.length Tok.disj
  | [] => rfl
  | a :: as => by
    rw [bigOr, rpnEnc_or, rpnEnc_bigOr as]
    simp [List.replicate_succ']

/-! ## Template combinators -/

namespace T

def var (ps : List Part) : Tmpl := .seq (.tok Tok.var) (.name ps)
def not (a : Tmpl) : Tmpl := .seq a (.tok Tok.neg)
def and (a b : Tmpl) : Tmpl := Tmpl.seqs [a, b, .tok Tok.conj]
def or (a b : Tmpl) : Tmpl := Tmpl.seqs [a, b, .tok Tok.disj]
def iff (a b : Tmpl) : Tmpl := or (and a b) (and (not a) (not b))

/-- `bigAnd` of a list unrolled at construction. -/
def bigAndL (ts : List Tmpl) : Tmpl := Tmpl.seqs (ts ++ [.tok Tok.tt] ++ ts.map (fun _ => .tok Tok.conj))
def bigOrL (ts : List Tmpl) : Tmpl := Tmpl.seqs (ts ++ [.tok Tok.ff] ++ ts.map (fun _ => .tok Tok.disj))

/-- `bigAnd` over `ctr i ∈ [0, b)` restricted to `c`. -/
def bigAndF (i : Nat) (b : Bound) (c : Cond) (body : Tmpl) : Tmpl :=
  Tmpl.seqs [.forR i b (.ite c body .nil), .tok Tok.tt, .forR i b (.ite c (.tok Tok.conj) .nil)]
def bigOrF (i : Nat) (b : Bound) (c : Cond) (body : Tmpl) : Tmpl :=
  Tmpl.seqs [.forR i b (.ite c body .nil), .tok Tok.ff, .forR i b (.ite c (.tok Tok.disj) .nil)]

/-- One template per suffix pattern of a block (`blockSuf` order); cells use counter `1`. -/
def block {k : Nat} (M : TM k) (body : List Part → Tmpl) : List Tmpl :=
  (List.range M.nq).map (fun q => body [.const 0, .const q]) ++
  (List.range k).map (fun i => .forR 1 .S (body [.const 1, .const i, .ctr 1])) ++
  (List.range k).map (fun i => .forR 1 .S (Tmpl.seqs ((List.range M.na).map (fun s =>
    body [.const 2, .const i, .ctr 1, .const s]))))

/-- `bigAnd` over the suffix patterns of a block. -/
def bigAndBlock {k : Nat} (M : TM k) (body : List Part → Tmpl) : Tmpl :=
  Tmpl.seqs (block M body ++ [.tok Tok.tt] ++ block M (fun _ => .tok Tok.conj))

end T

section Red

variable {k : Nat} (M : TM k)

/-- The initial configuration's value of pattern `[2, i, j, s]` (`j` = counter `1`). -/
def initCellCond (i s : Nat) : Cond :=
  if i = 0 then
    (if s = 2 then .inBit 1 true else if s = 1 then .inBit 1 false
     else if s = 0 then .and (.not (.inBit 1 true)) (.not (.inBit 1 false)) else .not .tt)
  else (if s = 0 then .tt else .not .tt)

/-- `initF` for block `tag`. -/
def initT (tag : List Part) : Tmpl :=
  Tmpl.seqs (
    (List.range M.nq).map (fun q => if q = 2 then T.var (tag ++ [.const 0, .const q])
      else T.not (T.var (tag ++ [.const 0, .const q]))) ++
    (List.range k).map (fun i => .forR 1 .S
      (.ite (.eqc 1 0) (T.var (tag ++ [.const 1, .const i, .ctr 1]))
        (T.not (T.var (tag ++ [.const 1, .const i, .ctr 1]))))) ++
    (List.range k).map (fun i => .forR 1 .S (Tmpl.seqs ((List.range M.na).map (fun s =>
      .ite (initCellCond i s) (T.var (tag ++ [.const 2, .const i, .ctr 1, .const s]))
        (T.not (T.var (tag ++ [.const 2, .const i, .ctr 1, .const s]))))))) ++
    [.tok Tok.tt] ++ T.block M (fun _ => .tok Tok.conj))

def eqT (b b' : List Part) : Tmpl := T.bigAndBlock M (fun v => T.iff (T.var (b ++ v)) (T.var (b' ++ v)))

def accT (b : List Part) : Tmpl := T.var (b ++ [.const 0, .const 0])

/-- `exOneF` of an unrolled list of names. -/
def exOneL (vs : List (List Part)) : Tmpl :=
  T.and (T.bigOrL (vs.map T.var)) (T.bigAndL ((pairsOf vs).map (fun p => T.not (T.and (T.var p.1) (T.var p.2)))))

/-- `exOneF` of the head variables of tape `i` (cells `j` = counter `1`, `j'` = counter `2`). -/
def exOneHead (b : List Part) (i : Nat) : Tmpl :=
  T.and (T.bigOrF 1 .S .tt (T.var (b ++ [.const 1, .const i, .ctr 1])))
    (Tmpl.seqs [.forR 1 .S (.forR 2 .S (.ite (.lt 1 2)
        (T.not (T.and (T.var (b ++ [.const 1, .const i, .ctr 1])) (T.var (b ++ [.const 1, .const i, .ctr 2]))))
        .nil)),
      .tok Tok.tt,
      .forR 1 .S (.forR 2 .S (.ite (.lt 1 2) (.tok Tok.conj) .nil))])

/-- `wfF b`: the conjunction of `1 + k + k * S` exactly-one constraints. -/
def wfT (b : List Part) : Tmpl :=
  Tmpl.seqs (
    [exOneL ((List.range M.nq).map (fun q => b ++ [.const 0, .const q]))] ++
    (List.range k).map (fun i => exOneHead b i) ++
    (List.range k).map (fun i => .forR 1 .S (exOneL ((List.range M.na).map (fun s =>
      b ++ [.const 2, .const i, .ctr 1, .const s])))) ++
    [.tok Tok.tt, .tok Tok.conj] ++
    (List.range k).map (fun _ => .tok Tok.conj) ++
    (List.range k).map (fun _ => .forR 1 .S (.tok Tok.conj)))

/-- `readF S b i s` (cells = counter `3`). -/
def readT (b : List Part) (i s : Nat) : Tmpl :=
  T.bigOrF 3 .S .tt (T.and (T.var (b ++ [.const 1, .const i, .ctr 3])) (T.var (b ++ [.const 2, .const i, .ctr 3, .const s])))

def combT (b : List Part) (q : Nat) (r : Fin k → Nat) : Tmpl :=
  T.and (T.var (b ++ [.const 0, .const q])) (T.bigAndL ((List.finRange k).map (fun i => readT b i.val (r i))))

def stateBitsT (b b' : List Part) : List Tmpl :=
  (List.range M.nq).map (fun q' => T.iff (T.var (b' ++ [.const 0, .const q']))
    (T.bigOrL (((combos M).filter (fun p => nextState M p.1 p.2 = q')).map (fun p => combT b p.1 p.2))))

/-- `(m.apply j' = j)` for `j'` = counter `2`, `j` = counter `1`. -/
def moveCond : Move → Cond
  | .L => .or (.succ 2 1) (.and (.eqc 2 0) (.eqc 1 0))
  | .S => .eq 2 1
  | .R => .succ 1 2

/-- `headBitF b b' i j` with `j` = counter `1`. -/
def headBitT (b b' : List Part) (i : Fin k) : Tmpl :=
  T.iff (T.var (b' ++ [.const 1, .const i.val, .ctr 1]))
    (T.bigOrL ((combos M).map (fun p => T.and (combT b p.1 p.2)
      (T.bigOrF 2 .S (moveCond (moveOf M p.1 p.2 i)) (T.var (b ++ [.const 1, .const i.val, .ctr 2]))))))

/-- `cellBitF b b' i j s` with `j` = counter `1`. -/
def cellBitT (b b' : List Part) (i : Fin k) (s : Nat) : Tmpl :=
  T.iff (T.var (b' ++ [.const 2, .const i.val, .ctr 1, .const s]))
    (T.or (T.and (T.not (T.var (b ++ [.const 1, .const i.val, .ctr 1]))) (T.var (b ++ [.const 2, .const i.val, .ctr 1, .const s])))
      (T.and (T.var (b ++ [.const 1, .const i.val, .ctr 1]))
        (T.bigOrL (((combos M).filter (fun p => writeSym M p.1 p.2 i = s)).map (fun p => combT b p.1 p.2)))))

def stepT (b b' : List Part) : Tmpl :=
  Tmpl.seqs (stateBitsT M b b' ++
    (List.finRange k).map (fun i => .forR 1 .S (headBitT M b b' i)) ++
    (List.finRange k).map (fun i => .forR 1 .S (Tmpl.seqs ((List.range M.na).map (fun s => cellBitT M b b' i s)))) ++
    [.tok Tok.tt] ++
    (List.range M.nq).map (fun _ => .tok Tok.conj) ++
    (List.finRange k).map (fun _ => .forR 1 .S (.tok Tok.conj)) ++
    (List.finRange k).map (fun _ => .forR 1 .S (Tmpl.seqs ((List.range M.na).map (fun _ => .tok Tok.conj)))))

def guardT (X Y Mi A B : List Part) : Tmpl :=
  T.or (T.and (eqT M A X) (eqT M B Mi)) (T.and (eqT M A Mi) (eqT M B Y))

/-- Tags. Level `ℓ = T - ctr 0`. -/
def tagX : List Part := [.const 0, .const 0]
def tagY : List Part := [.const 0, .const 1]
def tagL (i : Nat) : List Part := [.rev 0 0, .const i]
/-- The parent level's `A`/`B` (level `ℓ + 1`). -/
def tagP (i : Nat) : List Part := [.rev 0 1, .const i]

def levelT : Tmpl :=
  Tmpl.seqs [wfT M (tagL 0),
    .ite (.eqc 0 0) (guardT M tagX tagY (tagL 0) (tagL 1) (tagL 2))
      (guardT M (tagP 1) (tagP 2) (tagL 0) (tagL 1) (tagL 2)),
    .tok Tok.neg]

def baseT : Tmpl :=
  T.or (eqT M [.const 1, .const 1] [.const 1, .const 2]) (stepT M [.const 1, .const 1] [.const 1, .const 2])

def sideT : Tmpl :=
  T.and (initT M tagX) (T.and (wfT M tagY) (accT tagY))

def matrixT : Tmpl :=
  Tmpl.seqs [sideT M, .forR 0 .T (levelT M), baseT M, .forR 0 .T (Tmpl.seqs [.tok Tok.disj, .tok Tok.conj]),
    .tok Tok.conj]

def quantBlockT (kind : Nat) (tag : List Part) : Tmpl :=
  Tmpl.seqs (T.block M (fun v => .seq (.tok kind) (.name (tag ++ v))))

def prefixT : Tmpl :=
  Tmpl.seqs [quantBlockT M Tok.ex tagX, quantBlockT M Tok.ex tagY,
    .forR 0 .T (Tmpl.seqs [quantBlockT M Tok.ex (tagL 0), quantBlockT M Tok.all (tagL 1),
      quantBlockT M Tok.all (tagL 2)])]

def redTmpl : Tmpl := .seq (prefixT M) (matrixT M)

end Red

end Complexity
