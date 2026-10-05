import Complexity.TqbfEval
import Complexity.Qbf

/-!
# Decoding on a list machine

* `tokenizeP a tk`: list `a` holds bits (`0`/`1`), first bit on top; the 4-bit groups are pushed onto `tk` as tokens
  (`ofBits`), a final incomplete group is dropped.
* `parseNameP tk buf d`: read a name from `tk` (first token on top) as `parseName` does and append its normalized
  encoding `encName x` to `d`; `buf` is scratch for a run of ones.
* `decodeP tk qn mt buf`: process the whole token list as `decodeToks` does: quantifiers go to `qn` as
  `kind :: encName x` (kind `4` = ∀, `5` = ∃), matrix tokens go to `mt` as `RTok.enc`.
-/

namespace Complexity

variable {k : Nat}

def bitsTokL : List Bool → Nat
  | [b₃, b₂, b₁, b₀] => bitsTok b₃ b₂ b₁ b₀
  | _ => 0

section
variable (a tk : Fin k)

def readBitsP : Nat → List Bool → LProg k
  | 0, bs => .push tk (bitsTokL bs)
  | n + 1, bs =>
    .ite a nonEmpty
      (.ite a (symIs 1) (.seq (.pop a) (readBitsP n (bs ++ [true]))) (.seq (.pop a) (readBitsP n (bs ++ [false]))))
      (skipP a)

def tokenizeP : LProg k := .loop a nonEmpty (readBitsP a tk 4 [])

end

section
variable (tk buf d : Fin k)

/-- One component or the end of a name. The flag tape `fl` is nonempty while the name continues. -/
def nameStepP (fl : Fin k) : LProg k :=
  .seq (.loop tk (symIs Tok.one) (moveTop tk buf))
  (.ite tk (symIs Tok.sep)
    -- a component: its ones, then sep
    (.seq (moveAll buf d) (.seq (.pop tk) (.push d Tok.sep)))
    (.ite tk (symIs Tok.fin)
      -- end of the name, consuming `fin`
      (.seq (.pop tk) (.seq (.push d Tok.fin) (.pop fl)))
      -- anything else: drop the ones, end without consuming
      (.seq (clearAll buf) (.seq (.push d Tok.fin) (.pop fl)))))
where
  clearAll (i : Fin k) : LProg k := .loop i nonEmpty (.pop i)

def parseNameP (fl : Fin k) : LProg k := .seq (.push fl 0) (.loop fl nonEmpty (nameStepP tk buf d fl))

end

section
variable (tk qn mt buf fl : Fin k)

/-- Process one token at the top of `tk`. -/
def decStepP : LProg k :=
  .ite tk (symIs Tok.all) (.seq (moveTop tk qn) (parseNameP tk buf qn fl))
  (.ite tk (symIs Tok.ex) (.seq (moveTop tk qn) (parseNameP tk buf qn fl))
  (.ite tk (symIs Tok.var) (.seq (moveTop tk mt) (parseNameP tk buf mt fl))
  (.ite tk (fun s => s == Tok.tt + 4 || s == Tok.ff + 4 || s == Tok.neg + 4 || s == Tok.conj + 4 ||
      s == Tok.disj + 4) (moveTop tk mt)
  (.pop tk))))

def decodeP : LProg k := .loop tk nonEmpty (decStepP tk qn mt buf fl)

end

/-! ## Functional descriptions -/

def qnList (qs : List (Bool × Name)) : List Nat :=
  qs.flatMap (fun p => (if p.1 then Tok.all else Tok.ex) :: encName p.2)

def mtList (m : List RTok) : List Nat := m.flatMap RTok.enc

end Complexity
