import Complexity.TqbfDecode
import Complexity.TqbfFrames

/-!
# Resolving names on a list machine

Input: `qn` holds `qnList qs` (first quantifier at the bottom, so the newest is on top), `mt` holds the matrix tokens
with the first token on top. `resolveP` pushes onto `out` the resolved tokens `toksV (m.map (resolveTok N))`
(first token at the bottom) where `N` lists the quantifier names newest first; for a variable it reads the name into `x`
and scans the quantifier entries from the top, comparing names and counting skipped entries on `r` (as ones), moving
scanned entries to `qn2` and back afterwards.

`kindsP qn ks`: extract the kinds from `qn` onto `ks` (outermost on top, `1` = ∀, `0` = ∃).
-/

namespace Complexity

variable {k : Nat}

def isKind : Nat → Bool := fun s => s == Tok.all + 4 || s == Tok.ex + 4

section
variable (mt out x x2 qn qn2 r fl cf : Fin k)

/-- Copy the name at the top of `mt` (up to and including `fin`) onto `x`. -/
def readNameP : LProg k :=
  .seq (.loop mt (fun s => s == Tok.one + 4 || s == Tok.sep + 4) (moveTop mt x)) (moveTop mt x)

/-- Move the rest of the current entry (down to and including its kind) from `qn` to `qn2`. -/
def skipEntryP : LProg k :=
  .seq (.loop qn (fun s => !(isKind s) && s != 3) (moveTop qn qn2)) (moveTop qn qn2)

/-- Compare the entry on top of `qn` with `x`; flag `cf` is popped when the comparison ends.
On a match `fl` (the search flag) is popped as well; on a mismatch the entry is skipped and `r` counts it. -/
def cmpStepP : LProg k :=
  .ite x nonEmpty
    (.ite x (symIs Tok.one)
      (.ite qn (symIs Tok.one) (.seq (moveTop qn qn2) (moveTop x x2)) (mismatch))
    (.ite x (symIs Tok.sep)
      (.ite qn (symIs Tok.sep) (.seq (moveTop qn qn2) (moveTop x x2)) (mismatch))
      (.ite qn (symIs Tok.fin) (.seq (moveTop qn qn2) (moveTop x x2)) (mismatch))))
    -- `x` exhausted: a match iff the entry's name is exhausted too
    (.ite qn isKind (.seq (.pop cf) (.pop fl)) (mismatch))
where
  mismatch : LProg k := .seq (skipEntryP qn qn2) (.seq (.push r Tok.one) (.pop cf))

/-- One entry of the search: compare, then restore `x`. -/
def searchStepP : LProg k :=
  .seq (.push cf 0) (.seq (.loop cf nonEmpty (cmpStepP x x2 qn qn2 r fl cf)) (moveAll x2 x))

/-- Resolve the variable whose name is on `x`; emit `ref r` or `ff` on `out`. -/
def lookupP : LProg k :=
  .seq (.push fl 0)
  (.seq (.loop qn nonEmpty (.ite fl nonEmpty (searchStepP x x2 qn qn2 r fl cf) (skipEntryP qn qn2)))
  (.seq (moveAll qn2 qn)
  (.seq (.ite fl nonEmpty
      -- not found
      (.seq (.pop fl) (.seq (clearP r) (.push out Tok.ff)))
      -- found
      (.seq (.push out Tok.var) (.seq (moveAll r out) (.push out Tok.fin))))
    (clearP x))))

/-- Process one matrix token. -/
def resStepP : LProg k :=
  .ite mt (symIs Tok.var) (.seq (.pop mt) (.seq (readNameP mt x) (lookupP out x x2 qn qn2 r fl cf)))
    (moveTop mt out)

def resolveP : LProg k := .loop mt nonEmpty (resStepP mt out x x2 qn qn2 r fl cf)

end

def kindsP (qn ks : Fin k) : LProg k :=
  .loop qn nonEmpty
    (.ite qn (symIs Tok.all) (.seq (.pop qn) (.push ks 1))
      (.ite qn (symIs Tok.ex) (.seq (.pop qn) (.push ks 0)) (.pop qn)))

end Complexity
