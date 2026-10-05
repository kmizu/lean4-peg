import Complexity.Tmpl
import Complexity.TqbfFrames

/-!
# Running templates on a list machine

Tapes (`TT`): `out` (output bits, `0`/`1`), `inr` (input bits, first bit on top), `sb`/`tb` (`S`/`T` in unary), `bc`
(a constant bound in unary), counters `ct i` and their save tapes `sv i` (unary), scratch `ta`, `tb'`, `tc`, and the
condition flag `fl` (`[0]` = true, `[]` = false). Unary numbers are lists of `1`s.

`compileT tt t` emits the bits of `t.denote e` (each token as its 4 bits `tokBits`), leaving every other tape as it
was. `forR i` saves counter `i` on `sv i`, counts from `0` while `ctr i < bound`, and restores it.
-/

namespace Complexity

variable {k : Nat}

structure TT (k : Nat) where
  out : Fin k
  inr : Fin k
  sb : Fin k
  tb : Fin k
  bc : Fin k
  ta : Fin k
  tb' : Fin k
  tc : Fin k
  fl : Fin k
  ct : Nat → Fin k
  sv : Nat → Fin k

section
variable (tt : TT k)

/-- Sequence of list programs. -/
def seqL : List (LProg k) → LProg k
  | [] => skipP tt.out
  | [p] => p
  | p :: ps => .seq p (seqL ps)

def emitTokP (t : Nat) : LProg k := seqL tt ((tokBits t).map (fun b => .push tt.out (if b then 1 else 0)))

/-- Emit one `Tok.one` token per element of unary tape `c` (restored through `ta`). -/
def emitOnesP (c : Fin k) : LProg k :=
  .seq (.loop c nonEmpty (.seq (moveTop c tt.ta) (emitTokP tt Tok.one))) (moveAll tt.ta c)

/-- Fill `bc` with `n` ones. -/
def fillP (n : Nat) : LProg k := seqL tt (List.replicate n (.push tt.bc 1))

/-- Flag `fl` := `|a| < |b|` (unary, nondestructive). -/
def ltP (a b : Fin k) : LProg k :=
  seqL tt [.loop a nonEmpty (.seq (moveTop a tt.ta) (.ite b nonEmpty (moveTop b tt.tb') (skipP b))),
    .ite b nonEmpty (.push tt.fl 0) (skipP b),
    moveAll tt.ta a, moveAll tt.tb' b]

/-- Negate the flag. -/
def notFlP : LProg k := .ite tt.fl nonEmpty (.pop tt.fl) (.push tt.fl 0)

/-- Flag := `|a| = |b|`. -/
def eqP (a b : Fin k) : LProg k :=
  seqL tt [ltP tt a b, .ite tt.fl nonEmpty (.pop tt.fl) (.seq (ltP tt b a) (notFlP tt))]

/-- Flag := the input has bit `b` at position `|c|`. -/
def inBitP (c : Fin k) (b : Bool) : LProg k :=
  seqL tt [.loop c nonEmpty (.seq (moveTop c tt.ta) (.ite tt.inr nonEmpty (moveTop tt.inr tt.tb') (skipP tt.inr))),
    .ite tt.inr (symIs (if b then 1 else 0)) (.push tt.fl 0) (skipP tt.inr),
    moveAll tt.ta c, moveAll tt.tb' tt.inr]

def clearP' (c : Fin k) : LProg k := .loop c nonEmpty (.pop c)

/-- Flag := the condition. -/
def condP : Cond → LProg k
  | .tt => .push tt.fl 0
  | .lt i j => ltP tt (tt.ct i) (tt.ct j)
  | .eq i j => eqP tt (tt.ct i) (tt.ct j)
  | .eqc i n => seqL tt [fillP tt n, eqP tt (tt.ct i) tt.bc, clearP' tt.bc]
  | .succ i j => seqL tt [.push (tt.ct j) 1, eqP tt (tt.ct i) (tt.ct j), .pop (tt.ct j)]
  | .inBit i b => inBitP tt (tt.ct i) b
  | .not c => .seq (condP c) (notFlP tt)
  | .and c d => .seq (condP c) (.ite tt.fl nonEmpty (.seq (.pop tt.fl) (condP d)) (skipP tt.fl))
  | .or c d => .seq (condP c) (.ite tt.fl nonEmpty (skipP tt.fl) (condP d))

/-- Emit the ones of a name part. -/
def partP : Part → LProg k
  | .const n => seqL tt (List.replicate n (emitTokP tt Tok.one))
  | .ctr i => emitOnesP tt (tt.ct i)
  | .rev i c =>
    seqL tt [
      -- move `min (ctr i) T` ones from `tb` to `tc`, the counter to `ta`
      .loop (tt.ct i) nonEmpty (.seq (moveTop (tt.ct i) tt.ta) (.ite tt.tb nonEmpty (moveTop tt.tb tt.tc) (skipP tt.tb))),
      -- `tb` now holds `T - ctr i` ones
      .loop tt.tb nonEmpty (.seq (moveTop tt.tb tt.tb') (emitTokP tt Tok.one)),
      moveAll tt.tb' tt.tb, moveAll tt.tc tt.tb, moveAll tt.ta (tt.ct i),
      seqL tt (List.replicate c (emitTokP tt Tok.one))]

def nameP (ps : List Part) : LProg k :=
  seqL tt ((ps.map (fun p => LProg.seq (partP tt p) (emitTokP tt Tok.sep))) ++ [emitTokP tt Tok.fin])

def boundTape : Bound → Fin k
  | .const _ => tt.bc
  | .S => tt.sb
  | .T => tt.tb

def compileT : Tmpl → LProg k
  | .nil => skipP tt.out
  | .tok t => emitTokP tt t
  | .name ps => nameP tt ps
  | .seq a b => .seq (compileT a) (compileT b)
  | .forR i b body =>
    let fillB : LProg k := match b with
      | .const n => fillP tt n
      | _ => skipP tt.out
    let clearB : LProg k := match b with
      | .const _ => clearP' tt.bc
      | _ => skipP tt.out
    seqL tt [moveAll (tt.ct i) (tt.sv i), fillB,
      ltP tt (tt.ct i) (boundTape tt b),
      .loop tt.fl nonEmpty (seqL tt [.pop tt.fl, clearB, compileT body, fillB, .push (tt.ct i) 1,
        ltP tt (tt.ct i) (boundTape tt b)]),
      clearB, clearP' (tt.ct i), moveAll (tt.sv i) (tt.ct i)]
  | .ite c a b => .seq (condP tt c) (.ite tt.fl nonEmpty (.seq (.pop tt.fl) (compileT a)) (compileT b))

end

/-! ## Specification -/

def bit01 (b : Bool) : Nat := if b then 1 else 0

/-- Counters looped over by a template. -/
def Tmpl.loops : Tmpl → List Nat
  | .nil => []
  | .tok _ => []
  | .name _ => []
  | .seq a b => a.loops ++ b.loops
  | .forR i _ body => i :: body.loops
  | .ite _ a b => a.loops ++ b.loops

def Cond.WF (nc : Nat) : Cond → Prop
  | .tt => True
  | .lt i j => i < nc ∧ j < nc
  | .eq i j => i < nc ∧ j < nc
  | .eqc i _ => i < nc
  | .succ i j => i < nc ∧ j < nc ∧ i ≠ j
  | .inBit i _ => i < nc
  | .not c => c.WF nc
  | .and c d => c.WF nc ∧ d.WF nc
  | .or c d => c.WF nc ∧ d.WF nc

def Part.WF (nc : Nat) : Part → Prop
  | .const _ => True
  | .ctr i => i < nc
  | .rev i _ => i < nc

/-- Counters are below `nc`, and a loop never nests a loop over the same counter. -/
def Tmpl.WF (nc : Nat) : Tmpl → Prop
  | .nil => True
  | .tok _ => True
  | .name ps => ∀ p ∈ ps, p.WF nc
  | .seq a b => a.WF nc ∧ b.WF nc
  | .forR i _ body => i < nc ∧ i ∉ body.loops ∧ body.WF nc
  | .ite c a b => c.WF nc ∧ a.WF nc ∧ b.WF nc

/-- Constants are at most `Z`. -/
def Cond.Small (Z : Nat) : Cond → Prop
  | .eqc _ n => n ≤ Z
  | .not c => c.Small Z
  | .and c d => c.Small Z ∧ d.Small Z
  | .or c d => c.Small Z ∧ d.Small Z
  | _ => True

def Part.Small (Z : Nat) : Part → Prop
  | .const n => n ≤ Z
  | .ctr _ => True
  | .rev _ c => c ≤ Z

def Tmpl.Small (Z : Nat) : Tmpl → Prop
  | .nil => True
  | .tok t => t < 16
  | .name ps => ∀ p ∈ ps, p.Small Z
  | .seq a b => a.Small Z ∧ b.Small Z
  | .forR _ b body => (match b with | .const n => n ≤ Z | _ => True) ∧ body.Small Z
  | .ite c a b => c.Small Z ∧ a.Small Z ∧ b.Small Z

/-- The tape layout for environment `e` with output so far `acc`. -/
def TRep (tt : TT k) (nc : Nat) (e : TEnv) (acc : List Nat) (L : Lists k) : Prop :=
  L tt.out = acc ∧ L tt.inr = (e.w.map bit01).reverse ∧ L tt.sb = List.replicate e.S 1 ∧
  L tt.tb = List.replicate e.T 1 ∧ L tt.bc = [] ∧ L tt.ta = [] ∧ L tt.tb' = [] ∧ L tt.tc = [] ∧ L tt.fl = [] ∧
  ∀ i, i < nc → L (tt.ct i) = List.replicate (e.ctr i) 1

/-- The tapes of the layout are distinct. -/
def TT.Distinct (tt : TT k) (nc : Nat) : Prop :=
  ([tt.out, tt.inr, tt.sb, tt.tb, tt.bc, tt.ta, tt.tb', tt.tc, tt.fl] ++ (List.range nc).map tt.ct ++
    (List.range nc).map tt.sv).Nodup

/-- The cost unit: one primitive on unary numbers at most `Z`. -/
def tunit (Z : Nat) : Nat := 100 * (Z + 3)

def Cond.cost (Z : Nat) : Cond → Nat
  | .not c => c.cost Z + tunit Z
  | .and c d => c.cost Z + d.cost Z + tunit Z
  | .or c d => c.cost Z + d.cost Z + tunit Z
  | _ => tunit Z

/-- A step bound for running a template when every number involved is at most `Z`. -/
def Tmpl.ucost (Z : Nat) : Tmpl → Nat
  | .nil => 1
  | .tok _ => tunit Z
  | .name ps => (ps.length + 1) * tunit Z
  | .seq a b => a.ucost Z + b.ucost Z
  | .forR _ _ body => 4 * tunit Z + (Z + 1) * (body.ucost Z + 4 * tunit Z)
  | .ite c a b => c.cost Z + 2 + a.ucost Z + b.ucost Z

end Complexity
