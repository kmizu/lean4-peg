import PalPeg.CloseoutConsumeAvail

/-!
# The verifier head's `Represents`, carried by the chain

`CloseoutConsumeAvail.consumeAvail_of_bound` reduced `ConsumeAvail` to one
remaining input: the chain's verifier head represents the word
(`Represents wch.machine.verifier.head w ∧ focus ≠ none`).  The same pair is
`CloseoutPackRun49.MatchRest`'s `repV` / `repVmid`.  (That file is **not**
registered in `PalPeg.lean` and does not currently build — 5 errors on its own —
so nothing here depends on it; the shape is quoted from its source only.)

It travels.  `CloseoutPackRun41.ChainPositionLedger` already carries `canRight ver` at
every live chain shape, and `GalilScaffoldChainInputSupply.right_word` /
`CloseoutScanMargin4.right_present` push `Represents` and presence through one
`right`.  So the pair is preserved by exactly the step that moves the verifier.

`VerRep` below is that pair as a chain predicate, and `verRep_next` is the
one-step transport, which is what `repVmid` asks for.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutVerRep

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun41 PalPeg.CloseoutScanMargin4

/-- **The verifier head represents the word, at every live chain shape.** -/
def VerRep (w : List (Fin 2)) (z : ChainVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
    GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
      wch.machine.verifier.head.focus ≠ none

/-- `VerRep` is vacuous at an idle chain. -/
theorem verRep_idle (w : List (Fin 2)) : VerRep w ChainVM.idle := fun _ h => by cases h

/-- **One `right` on the verifier preserves the pair.**  This is what
`MatchRest.repVmid` asks for at a `take`/`immediate` consume: the moved head
still represents the word, because `ChainPositionLedger` gives `canRight` of the head
before the move. -/
theorem verRep_next {w : List (Fin 2)} {wch : GalilScaffoldChainWatch.State}
    (hv : GalilScaffoldInputTrace.Represents wch.machine.verifier.head w)
    (hf : wch.machine.verifier.head.focus ≠ none)
    (hc : canRight wch.machine.verifier) :
    GalilScaffoldInputTrace.Represents (right wch.machine.verifier).head w ∧
      (right wch.machine.verifier).head.focus ≠ none :=
  ⟨right_word _ w hv hc, right_present _ w hv hf hc⟩

/-- **`VerRep` plus `ChainPositionLedger` transports across a verifier move.** -/
theorem verRep_of_chainPos {w : List (Fin 2)} {z : ChainVM} {R : ℕ}
    (hV : VerRep w z) (hP : ChainPositionLedger z R)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch) :
    GalilScaffoldInputTrace.Represents (right wch.machine.verifier).head w ∧
      (right wch.machine.verifier).head.focus ≠ none := by
  obtain ⟨hv, hf⟩ := hV wch hz
  obtain ⟨hc, -, -⟩ := hP.watch wch hz
  exact verRep_next hv hf hc

#print axioms verRep_idle
#print axioms verRep_next
#print axioms verRep_of_chainPos

/-! ## `ConsumeAvail` from `VerRep` plus the position budget

`CloseoutConsumeAvail.consumeAvail_of_bound` takes the verifier pair as an
input; `VerRep` is exactly that input as a chain predicate.  Composing the two
leaves only the run's own position budget.
-/

open PalPeg.CloseoutConsumeAvail PalPeg.CloseoutPackRun26

/-- **`ConsumeAvail` at a scan state from `VerRep` and the bound.** -/
theorem consumeAvail_of_verRep
    {w : List (Fin 2)} {c : Control} {s : GalilVM} {m : ℕ}
    (hx : ChainPositionInvariantWithShiftPhase w c s) (hs : ScanNR ⟨c, s⟩) (hni : s.chain ≠ ChainVM.idle)
    (hV : VerRep w s.chain)
    (hrepN : GalilScaffoldInputTrace.Represents (right s.right).head w)
    (hfocN : (right s.right).head.focus ≠ none)
    (hstep : position (right s.right) = position s.right + 1)
    (hlag : PalPeg.CloseoutPackRun47.LagNonneg s.chain)
    (hlv : 0 < s.right.head.left.length)
    (hm1 : 1 ≤ m) (hmlt : m < w.length) (hpos : position s.right ≤ 2 * m - 1) :
    PalPeg.CloseoutPackRun41.ConsumeAvail s.chain :=
  consumeAvail_of_bound hx hs hni hV hrepN hfocN hstep hlag hlv hm1 hmlt hpos

#print axioms consumeAvail_of_verRep

end PalPeg.CloseoutVerRep
