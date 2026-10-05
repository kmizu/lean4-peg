import Complexity.Formula

/-!
# From quantified trees to prenex QBFs

`toRPN` writes a formula tree in reverse Polish notation; `QF.toQbf` takes the prenex form of a clean quantified tree
and writes its matrix in RPN. `QF.toQbf_value`: the QBF has the value of the tree.
-/

namespace Complexity

def toRPN : Formula → List RTok
  | .var x => [.var x]
  | .tt => [.tt]
  | .ff => [.ff]
  | .not a => toRPN a ++ [.neg]
  | .and a b => toRPN a ++ toRPN b ++ [.conj]
  | .or a b => toRPN a ++ toRPN b ++ [.disj]

theorem evalRPN_append (σ : List (Name × Bool)) : ∀ (ts us : List RTok) (st : List Bool),
    evalRPN σ (ts ++ us) st = evalRPN σ us (evalRPN σ ts st)
  | [], _, _ => rfl
  | .var _ :: ts, us, _ => evalRPN_append σ ts us _
  | .tt :: ts, us, _ => evalRPN_append σ ts us _
  | .ff :: ts, us, _ => evalRPN_append σ ts us _
  | .neg :: ts, us, _ => evalRPN_append σ ts us _
  | .conj :: ts, us, _ => evalRPN_append σ ts us _
  | .disj :: ts, us, _ => evalRPN_append σ ts us _

theorem evalRPN_toRPN (σ : List (Name × Bool)) : ∀ (ψ : Formula) (st : List Bool),
    evalRPN σ (toRPN ψ) st = ψ.eval (lookup σ) :: st
  | .var _, _ => rfl
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .not a, st => by
    simp only [toRPN, evalRPN_append, evalRPN_toRPN σ a]; rfl
  | .and a b, st => by
    simp only [toRPN, evalRPN_append, evalRPN_toRPN σ a, evalRPN_toRPN σ b]; rfl
  | .or a b, st => by
    simp only [toRPN, evalRPN_append, evalRPN_toRPN σ a, evalRPN_toRPN σ b]; rfl

theorem lookup_cons (σ : List (Name × Bool)) (x : Name) (b : Bool) :
    lookup ((x, b) :: σ) = upd (lookup σ) x b := by
  funext y
  by_cases h : y = x
  · subst h; simp [lookup, upd]
  · have : (x == y) = false := by simp; exact fun e => h e.symm
    simp [lookup, upd, h, List.find?, this]

theorem lookup_nil : lookup [] = fun _ => false := by
  funext y; rfl

theorem qEval_toRPN (ψ : Formula) : ∀ (q : List (Bool × Name)) (σ : List (Name × Bool)),
    qEval (toRPN ψ) q σ = evalPrefix ψ q (lookup σ)
  | [], σ => by simp [qEval, matrixValue, evalRPN_toRPN, evalPrefix]
  | (true, x) :: q, σ => by
    simp only [qEval, evalPrefix, qEval_toRPN ψ q, lookup_cons]
  | (false, x) :: q, σ => by
    simp only [qEval, evalPrefix, qEval_toRPN ψ q, lookup_cons]

def QF.toQbf (φ : QF) : Qbf := ⟨φ.prenex.1, toRPN φ.prenex.2⟩

theorem QF.toQbf_value (φ : QF) (h : φ.Clean) : φ.toQbf.value = φ.eval (fun _ => false) := by
  simp only [QF.toQbf, Qbf.value]
  rw [qEval_toRPN, lookup_nil, QF.eval_prenex φ h]

end Complexity
