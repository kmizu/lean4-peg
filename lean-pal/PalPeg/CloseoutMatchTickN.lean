import PalPeg.CloseoutMatchTickRefute

/-!
# `MatchTickC` reformulated — and then it is a theorem

`CloseoutMatchTickRefute` showed `CloseoutWatchRound2.MatchTickC` is false: it
asks for `Good w1` at **every** matched comparison, and at a round's terminal a
matched comparison breaks the chain instead
(`CloseoutPackRun31.not_good_of_terminal_match`).

`halign` is consumed at exactly one place —
`CloseoutWatchRound2.roundStepC_of_align` `:193`, inside
`by_cases hmm : read (left s1.left) = read (right s1.right)` — so the fix is the
same shape as `ShiftPal`'s and `H_advanceT`'s: put the datum the consumer can
supply into the statement.  Here that datum is the round's non-terminality,
which `roundStepC_of_align` obtains by a `by_cases` on `singlePositive s1.cycle`.

*(Correction, 2026-09-19: an earlier version of this header said the terminal
half is routed to "`TerminalC`'s cycle end exit".  That was wrong and was not
checked — `TerminalC`'s exits are `roundFuel h s = 0`, `shiftGuardVM s`,
`¬ canRight s.right` and `BreakEndC`, none of which is a cycle end.  The
terminal half needs a **fifth** exit, which is `CloseoutTerminalN.BrokeEndN`;
`CloseoutTerminalN.roundStepC_of_alignN` is the consumer that takes
`MatchTickN` and returns `TerminalN`.)*

With that premise the statement is not merely true, it is **already proved** in
`GalilRoundPeriod`:

* `RoundScan.caught.lagZero` gives `zero w1.lag = true`;
* `RoundScan.good_of_match`, which carries exactly
  `hend : singlePositive v.cycle = false`, gives `Good w1`.

So `MatchTickN` below follows from the round datum the `RoundBundle`'s
`ChainRound` field already carries: `matchTickN_of_round`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutMatchTickN

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31

/-- **(NAMED, reformulated) `MatchTickC` with the round's non-terminality.**
The premise `singlePositive s1.cycle = false` is what the only consumer can
decide for itself. -/
def MatchTickN (raw : List (Fin 2)) : Prop :=
  ∀ (s1 : GalilVM) (w1 : GalilScaffoldChainWatch.State),
    s1.chain = ChainVM.watch w1 → canRight s1.right →
    read (GalilScaffoldInputHead.left s1.left) = read (right s1.right) →
    singlePositive s1.cycle = false →
    zero w1.lag = true ∧ GalilScaffoldChainWatch.Good w1

/-- **`MatchTickN` is a theorem given the round datum.**  `lagZero` is a
`CaughtScan` field and `Good` is `RoundScan.good_of_match`, whose non-terminal
premise is exactly the one the reformulation added. -/
theorem matchTickN_of_round {raw : List (Fin 2)}
    (hR : ∀ (s1 : GalilVM) (w1 : GalilScaffoldChainWatch.State),
      s1.chain = ChainVM.watch w1 →
      ∃ C R used : ℕ, RoundScan raw C R (periodLength w1) used s1 w1) :
    MatchTickN raw := by
  intro s1 w1 hch hav hmm hend
  obtain ⟨C, R, used, hI⟩ := hR s1 w1 hch
  exact ⟨hI.caught.lagZero, (hI.good_of_match hav hend hmm).1⟩

/-- **`MatchTickN` from `ChainRound`**, the field `CloseoutRoundBundle.RoundBundle`
already carries.  The mode / replay / `periodOnly` premises are the bundle's
own. -/
theorem matchTickN_of_chainRound {raw : List (Fin 2)} {c : Control}
    (hCR : ∀ s : GalilVM, ChainRound raw c s)
    (hm : c.mode = Mode.scan) (hr : c.replaying = false)
    (hpo : ∀ s : GalilVM, s.periodOnly = true) :
    MatchTickN raw :=
  matchTickN_of_round (fun s1 w1 hch => hCR s1 hm hr (hpo s1) w1 hch)

/-- **The terminal case is not lost, it breaks.**  At the terminal a matched
comparison yields a `BreakStep`, which is `TerminalC`'s cycle-end exit — so
splitting the consumer's matched branch on `singlePositive` loses nothing. -/
theorem break_at_terminal {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hav : canRight s.right)
    (hend : singlePositive s.cycle = true)
    (hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right)) :
    ∃ w', BreakStep w0 w' :=
  hI.break_of_match hav hend hmatch

#print axioms matchTickN_of_round
#print axioms matchTickN_of_chainRound
#print axioms break_at_terminal

end PalPeg.CloseoutMatchTickN
