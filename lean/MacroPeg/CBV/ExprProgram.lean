import MacroPeg.CBV.StarMachine
import MacroPeg.CBV.SpanRegister

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.Mach

/-- Shared evaluator layout. Slots 19–24 hold dictionary count, length, rank, old table,
repetition flag and the current rule's parameter row; slots 25–31 are reserved for saturation. -/
structure EvalRegs (K : Nat) where
  get : Fin 32 → Fin K
  inj : ∀ i j, get i = get j → i = j

@[simp] theorem EvalRegs.eq {K : Nat} (r : EvalRegs K) (i j : Fin 32) :
    r.get i = r.get j ↔ i = j := ⟨r.inj i j, congrArg r.get⟩

theorem EvalRegs.ne {K : Nat} (r : EvalRegs K) {i j : Fin 32} (h : i ≠ j) : r.get i ≠ r.get j :=
  fun he => h (r.inj i j he)

def EvalRegs.param {K : Nat} (r : EvalRegs K) : ParamRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 32 => k.val) he)

def EvalRegs.register {K : Nat} (r : EvalRegs K) : RegisterRegs K where
  get i := r.get ⟨i.val, by have := i.isLt; omega⟩
  inj i j h := by
    have he := r.inj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ h
    exact Fin.ext (congrArg (fun k : Fin 32 => k.val) he)

def starSlot (i : Fin 18) : Fin 32 :=
  if h : i.val < 17 then ⟨i.val, by omega⟩ else 23

def EvalRegs.star {K : Nat} (r : EvalRegs K) : StarRegs K where
  get i := r.get (starSlot i)
  inj i j h := by
    have he := congrArg (fun k : Fin 32 => k.val) (r.inj _ _ h)
    have hi := i.isLt
    have hj := j.isLt
    simp only [starSlot] at he
    split at he <;> split at he <;> simp only at he <;> apply Fin.ext <;> omega

def addrSlot (i : Fin 5) : Fin 32 :=
  if i.val = 0 then 19 else if i.val = 1 then 20 else if i.val = 2 then 21 else if i.val = 3 then 15 else 18

def EvalRegs.address {K : Nat} (r : EvalRegs K) : AddrExpr.Regs K 5 where
  out := r.get 2
  a := r.get 5
  b := r.get 6
  tmp := r.get 1
  vars i := r.get (addrSlot i)
  ab := r.ne (by decide)
  atmp := r.ne (by decide)
  ao := r.ne (by decide)
  btmp := r.ne (by decide)
  bo := r.ne (by decide)
  to := r.ne (by decide)
  vo i := by
    by_cases h0 : i.val = 0
    · simp [addrSlot, h0]
    by_cases h1 : i.val = 1
    · simp [addrSlot, h0, h1]
    by_cases h2 : i.val = 2
    · simp [addrSlot, h0, h1, h2]
    by_cases h3 : i.val = 3
    · simp [addrSlot, h0, h1, h2, h3]
    simp [addrSlot, h0, h1, h2, h3]

/-- Read an identifier from the immutable parameter row, match it, and pop the identifier frame. -/
def paramEvalP {K : Nat} (r : EvalRegs K) (m k : Nat) : NProg K :=
  if k < m then
    .seq (tableReadP r.address (r.get 24) (r.get 7) (r.get 18)
      (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (.num k))
      (.seq (paramLiteralP r.param) (.prim (.pop (r.get 18))))
  else npushC (r.get 16) 1

/-- Accumulate a mixed-radix rank without storing an argument vector in work registers. -/
def rankUpdateExpr (tailArity : Nat) : AddrExpr 5 :=
  .add (.var 2) (.mul (.var 4) (AddrExpr.power (.var 0) tailArity))

def rankUpdateP {K : Nat} (r : EvalRegs K) (tailArity : Nat) : NProg K :=
  .seq (AddrExpr.compile r.address (rankUpdateExpr tailArity))
    (.seq (.prim (.pop (r.get 21))) (nmv (r.get 2) (r.get 21) (r.ne (by decide))))

def rankAddressExpr (g : MGrammar) (i : Nat) : AddrExpr 5 :=
  let positions := AddrExpr.add (.var 1) (.num 1)
  .add (.add (AddrExpr.sumExpr ((List.range i).map (fun j => AddrExpr.widthExpr g j (.var 0) positions)))
    (.mul (.var 2) positions)) (.var 3)

def ruleReadP {K : Nat} (r : EvalRegs K) (g : MGrammar) (i : Nat) : NProg K :=
  tableReadP r.address (r.get 22) (r.get 7) (r.get 16)
    (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)) (rankAddressExpr g i)

/-- Both strategies use private rank and position frames, including on an early failure. -/
def callPrepareP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pushZ (r.get 21)))
    (.seq (.prim (.dup (r.get 15) (r.get 3) (r.ne (by decide))))
      (nmv (r.get 3) (r.get 15) (r.ne (by decide))))

def callCleanupP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (.prim (.pop (r.get 15))) (.prim (.pop (r.get 21)))

/-- Only Seq advances the private position frame after registering an argument. -/
def argPositionP {K : Nat} (r : EvalRegs K) (s : Strategy) : NProg K :=
  match s with
  | .callByValueSeq =>
    .seq (.prim (.dec (r.get 16))) (.seq (.prim (.dec (r.get 16)))
      (.seq (.prim (.pop (r.get 15))) (nmv (r.get 16) (r.get 15) (r.ne (by decide)))))
  | _ => .prim (.pop (r.get 16))

def argSuccessP {K : Nat} (r : EvalRegs K) (s : Strategy) (tailArity : Nat) (cont : NProg K) : NProg K :=
  .seq (.prim (.inc (r.get 16)))
    (.seq (registerSpanP r.register) (.seq (rankUpdateP r tailArity)
      (.seq (.prim (.pop (r.get 18))) (.seq (argPositionP r s) cont))))

/-- Distinguish unknown, failure and success without retrying or evaluating later arguments on an error. -/
def argAfterP {K : Nat} (r : EvalRegs K) (s : Strategy) (tailArity : Nat) (cont : NProg K) : NProg K :=
  .ite (r.get 16) .zero (nskip (r.get 16))
    (.seq (.prim (.dec (r.get 16))) (.ite (r.get 16) .zero (.prim (.inc (r.get 16)))
      (argSuccessP r s tailArity cont)))

mutual
  /-- A concrete program for every fixed expression. Correctness is established separately from this definition. -/
  def exprProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) : MExp → NProg K
    | .eps => emptySuccess (r.get 15) (r.get 16) (r.ne (by decide))
    | .any => remainingLexP r.param.literal anyTest
    | .chr c => remainingLexP r.param.literal (chrTest c)
    | .range lo hi => remainingLexP r.param.literal (rangeTest lo hi)
    | .lit w => fixedLiteralP r.param.literal w
    | .param k => paramEvalP r m k
    | .call i args =>
      match ruleAtM g.rules i with
      | none => npushC (r.get 16) 1
      | some rule =>
        if rule.arity = args.length then
          .seq (callPrepareP r) (.seq (argsProgram r g s m args (ruleReadP r g i)) (callCleanupP r))
        else npushC (r.get 16) 1
    | .seq a b => .seq (exprProgram r g s m a) (seqAfterP r.param.literal (exprProgram r g s m b))
    | .alt a b => altEvalP (r.get 16) (exprProgram r g s m a) (exprProgram r g s m b)
    | .star a => starEvalP r.star (exprProgram r g s m a)
    | .notP a => .seq (exprProgram r g s m a) (notAfterP r.param.literal)
    | .dbg _ | .lam _ _ => emptySuccess (r.get 15) (r.get 16) (r.ne (by decide))
    | .callParam _ _ => npushC (r.get 16) 1
    | .invoke _ _ _ => npushC (r.get 16) 0

  /-- Arguments are compiled with a continuation for the final saved-table access. -/
  def argsProgram {K : Nat} (r : EvalRegs K) (g : MGrammar) (s : Strategy) (m : Nat) :
      List MExp → NProg K → NProg K
    | [], cont => cont
    | a :: args, cont => .seq (exprProgram r g s m a)
        (argAfterP r s args.length (argsProgram r g s m args cont))
end

end Shallot.MacroPeg.CBV
