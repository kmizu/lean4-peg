import Shallot.Peg.Dpda.AccSpec
import Shallot.Peg.Total.Main

/-!
# Deterministic context-free languages are PEG languages

Birman–Ullman (1973, Theorem 2.2): every language accepted by a deterministic pushdown automaton (by final state) is
the language of a PEG; Ford (POPL 2004, §5) quotes it without proof. The grammar (`DPDA.grammar`) has, for states
`q, r` and a stack symbol `Z`, a nonterminal `P q Z r` (Birman–Ullman's `[qZr]`: pop `Z`, ending in state `r`) and a
nonterminal `A q Z` (accept while `Z` is on the stack). Reading and ε-moves are ordered choices; the state in which a
pushed symbol is popped is found by an ordered choice over all states, and determinism leaves at most one candidate.

* `DPDA.sound`: a successful derivation gives a run of the automaton (`Sound.lean`).
* `DPDA.complete`: an accepted word has a successful derivation (`PopSpec.lean`, `AccSpec.lean`).

No normalization of the automaton is assumed (Birman–Ullman use one that always reads its whole input): the grammar
may loop where the automaton does. The language is then a PEG language in the sense of `IsPEL` (inputs on which the
grammar loops are not accepted), and `isPEL_iff_isTotalPEL` turns it into the language of a complete PEG.
-/

namespace Shallot.Dpda

open Shallot

/-- **DCFL ⊆ PEL**: the language of a DPDA is a PEG language. -/
theorem dpda_isPEL (M : DPDA) : Shallot.Cfg.IsPEL M.language :=
  ⟨M.grammar, fun w => ⟨M.complete, fun ⟨_, h⟩ => M.sound h⟩⟩

/-- **DCFL ⊆ PEL, with a complete PEG**: the language of a DPDA is the language of a PEG whose start rule succeeds
or fails on every input. -/
theorem dpda_isTotalPEL (M : DPDA) : IsTotalPEL M.language :=
  (isPEL_iff_isTotalPEL M.language).mp (dpda_isPEL M)

end Shallot.Dpda
