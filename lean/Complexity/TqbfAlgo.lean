import Complexity.Circuit

/-!
# A name-free evaluation of QBFs

The matrix is evaluated only once every quantified variable is bound, so each variable occurrence can be resolved in
advance to the distance (`ref r`, newest binding first) of the newest quantifier with that name; an unbound variable
reads `false`. `value_eq_qEvalV`: the value of a QBF equals the evaluation of its resolved matrix over the bit
vectors of the quantifier kinds.
-/

namespace Complexity

/-- Resolved matrix tokens. -/
inductive VTok where
  | ref (r : Nat)
  | tt
  | ff
  | neg
  | conj
  | disj
  deriving DecidableEq, Repr

def resolveTok (N : List Name) : RTok → VTok
  | .var x => match N.findIdx? (· == x) with
    | some r => .ref r
    | none => .ff
  | .tt => .tt
  | .ff => .ff
  | .neg => .neg
  | .conj => .conj
  | .disj => .disj

def evalV (bits : List Bool) : List VTok → List Bool → List Bool
  | [], st => st
  | .ref r :: ts, st => evalV bits ts (bits.getD r false :: st)
  | .tt :: ts, st => evalV bits ts (true :: st)
  | .ff :: ts, st => evalV bits ts (false :: st)
  | .neg :: ts, st => evalV bits ts ((!st.headD false) :: st.tail)
  | .conj :: ts, st => evalV bits ts ((st.tail.headD false && st.headD false) :: st.tail.tail)
  | .disj :: ts, st => evalV bits ts ((st.tail.headD false || st.headD false) :: st.tail.tail)

def comb (κ a b : Bool) : Bool := if κ then a && b else a || b

/-- `kinds` outermost first (`true` = ∀), `bits` newest first. -/
def qEvalV (mv : List VTok) : List Bool → List Bool → Bool
  | [], bits => (evalV bits mv []).headD false
  | κ :: ks, bits => comb κ (qEvalV mv ks (true :: bits)) (qEvalV mv ks (false :: bits))

theorem lookup_zip : ∀ (N : List Name) (bits : List Bool), N.length = bits.length → ∀ x,
    lookup (N.zip bits) x = match N.findIdx? (· == x) with
      | some r => bits.getD r false
      | none => false
  | [], [], _, x => rfl
  | y :: N, b :: bits, h, x => by
    have ih := lookup_zip N bits (by simpa using h) x
    by_cases hy : y = x
    · subst hy; simp [lookup, List.findIdx?_cons]
    · have hyx : (y == x) = false := by simp [hy]
      simp only [List.zip_cons_cons, List.findIdx?_cons, hyx]
      simp only [lookup, List.find?_cons, hyx] at ih ⊢
      rw [ih]
      cases N.findIdx? (· == x) <;> rfl

theorem evalRPN_resolve (N : List Name) (bits : List Bool) (hl : N.length = bits.length) :
    ∀ (m : List RTok) (st : List Bool), evalRPN (N.zip bits) m st = evalV bits (m.map (resolveTok N)) st
  | [], _ => rfl
  | .var x :: m, st => by
    simp only [evalRPN, List.map_cons, resolveTok, lookup_zip N bits hl x]
    rw [evalRPN_resolve N bits hl m]
    cases N.findIdx? (· == x) <;> rfl
  | .tt :: m, st => evalRPN_resolve N bits hl m _
  | .ff :: m, st => evalRPN_resolve N bits hl m _
  | .neg :: m, st => evalRPN_resolve N bits hl m _
  | .conj :: m, st => evalRPN_resolve N bits hl m _
  | .disj :: m, st => evalRPN_resolve N bits hl m _

theorem qEval_resolve (m : List RTok) : ∀ (qs : List (Bool × Name)) (pN : List Name) (pb : List Bool),
    pN.length = pb.length →
    qEval m qs (pN.zip pb) = qEvalV (m.map (resolveTok ((qs.map Prod.snd).reverse ++ pN))) (qs.map Prod.fst) pb
  | [], pN, pb, hl => by
    simp only [qEval, matrixValue, List.map_nil, List.reverse_nil, List.nil_append, qEvalV]
    rw [evalRPN_resolve pN pb hl]
  | (κ, x) :: qs, pN, pb, hl => by
    have h1 := qEval_resolve m qs (x :: pN) (true :: pb) (by simp [hl])
    have h2 := qEval_resolve m qs (x :: pN) (false :: pb) (by simp [hl])
    simp only [List.zip_cons_cons] at h1 h2
    have hN : (qs.map Prod.snd).reverse ++ x :: pN = (((κ, x) :: qs).map Prod.snd).reverse ++ pN := by simp
    rw [hN] at h1 h2
    cases κ <;> simp only [qEval, List.map_cons, qEvalV, comb, h1, h2] <;> rfl

theorem value_eq_qEvalV (φ : Qbf) :
    φ.value = qEvalV (φ.matrix.map (resolveTok (φ.quants.map Prod.snd).reverse)) (φ.quants.map Prod.fst) [] := by
  have := qEval_resolve φ.matrix φ.quants [] [] rfl
  simpa [Qbf.value] using this

end Complexity
