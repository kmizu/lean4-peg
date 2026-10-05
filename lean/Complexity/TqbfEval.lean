import Complexity.LProgs
import Complexity.TqbfAlgo

/-!
# Evaluating a resolved matrix on a list machine

Elements: matrix tokens `6` (ref, followed by `r` ones and `3`), `7` tt, `8` ff, `9` neg, `10` conj, `11` disj;
Boolean values `0`/`1`; frames `20` (first branch, bit `true`), `21`/`22` (second branch, bit `false`, first result
`false`/`true`).

`evalLeafP`: with the resolved matrix on tape `mr` (first token on top), the frames on `fr` (newest on top) and a value
stack on `vs` (top on top), run the matrix in RPN; the matrix is moved to `mr2` while it is read and moved back at the
end; `ft` is scratch for reading a frame below the top.
-/

namespace Complexity

variable {k : Nat}

def encV : VTok → List Nat
  | .ref r => 6 :: (List.replicate r 1 ++ [3])
  | .tt => [7]
  | .ff => [8]
  | .neg => [9]
  | .conj => [10]
  | .disj => [11]

def toksV (mv : List VTok) : List Nat := mv.flatMap encV

inductive Frame where
  | fresh
  | second (a : Bool)
  deriving DecidableEq

def Frame.elem : Frame → Nat
  | .fresh => 20
  | .second false => 21
  | .second true => 22

def Frame.bit : Frame → Bool
  | .fresh => true
  | .second _ => false

/-- A tape holding a stack whose head is on top. -/
def stackL {α : Type} (enc : α → Nat) (st : List α) : List Nat := (st.map enc).reverse

def symIs (e : Nat) : Nat → Bool := fun s => s == e + 4

def nonEmpty : Nat → Bool := fun s => s != 3

section
variable (mr mr2 fr ft vs : Fin k)

def pushBitP : LProg k := .ite fr (symIs 20) (.push vs 1) (.push vs 0)

def refP : LProg k :=
  .seq (moveTop mr mr2)
  (.seq (.loop mr (symIs 1) (.seq (moveTop mr mr2) (.ite fr nonEmpty (moveTop fr ft) (skipP fr))))
  (.seq (moveTop mr mr2)
  (.seq (pushBitP fr vs) (moveAll ft fr))))

def negP : LProg k :=
  .ite vs nonEmpty (.ite vs (symIs 1) (.seq (.pop vs) (.push vs 0)) (.seq (.pop vs) (.push vs 1))) (.push vs 1)

def conjP : LProg k :=
  .ite vs nonEmpty
    (.ite vs (symIs 1)
      (.seq (.pop vs) (.ite vs nonEmpty (skipP vs) (.push vs 0)))
      (.seq (.pop vs) (.seq (.ite vs nonEmpty (.pop vs) (skipP vs)) (.push vs 0))))
    (.push vs 0)

def disjP : LProg k :=
  .ite vs nonEmpty
    (.ite vs (symIs 1)
      (.seq (.pop vs) (.seq (.ite vs nonEmpty (.pop vs) (skipP vs)) (.push vs 1)))
      (.seq (.pop vs) (.ite vs nonEmpty (skipP vs) (.push vs 0))))
    (.push vs 0)

def tokP : LProg k :=
  .ite mr (symIs 6) (refP mr mr2 fr ft vs)
  (.ite mr (symIs 7) (.seq (moveTop mr mr2) (.push vs 1))
  (.ite mr (symIs 8) (.seq (moveTop mr mr2) (.push vs 0))
  (.ite mr (symIs 9) (.seq (moveTop mr mr2) (negP vs))
  (.ite mr (symIs 10) (.seq (moveTop mr mr2) (conjP vs))
  (.seq (moveTop mr mr2) (disjP vs))))))

def evalLeafP : LProg k := .seq (.loop mr nonEmpty (tokP mr mr2 fr ft vs)) (moveAll mr2 mr)

end

end Complexity
