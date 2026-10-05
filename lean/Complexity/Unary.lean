import Complexity.TqbfFrames

/-!
# Unary arithmetic on list machines

Numbers are lists of `1`s. `copyLenP src dst tmp` appends one `1` to `dst` per element of `src` (restoring `src`);
`mulP a b dst ta tb` appends `|a| * |b|` ones to `dst`; `powStepP pw n p2 ta tb` replaces `pw` by `pw * n`.
-/

namespace Complexity

variable {k : Nat}

def copyLenP (src dst tmp : Fin k) : LProg k :=
  .seq (.loop src nonEmpty (.seq (moveTop src tmp) (.push dst 1))) (moveAll tmp src)

def mulP (a b dst ta tb : Fin k) : LProg k :=
  .seq (.loop a nonEmpty (.seq (moveTop a ta) (copyLenP b dst tb))) (moveAll ta a)

def powStepP (pw n p2 ta tb : Fin k) : LProg k :=
  .seq (mulP pw n p2 ta tb) (.seq (clearP pw) (moveAll p2 pw))

/-- Repeat a program `m` times. -/
def repeatP (i : Fin k) (p : LProg k) : Nat → LProg k
  | 0 => skipP i
  | m + 1 => .seq p (repeatP i p m)

end Complexity
