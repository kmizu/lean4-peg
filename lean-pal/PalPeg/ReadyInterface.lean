import PalPeg.CloseoutReadyStage

/-!
# `ReadyInterface`: what the readiness consumers actually need

Measured on `CloseoutReadyStage` (2026-09-19, n195).  **Every** use of
`ReadyPacedS` in that file — the segment construction `watchSegE_constructS`,
its entry `segment_of_invLPCS`, the report comparison `readyPacedS_watchSegE`,
the crossing case `reachAtC3_of_crossS`, and `reachAtC3_of_target_matchS` — goes
through exactly four lemmas:

* `readyPacedS_ready`        — extract `SearchReady`;
* `readyPacedS_mono`         — weaken the two indices;
* `readyPacedS_effect_false` — carry across **one background quantum**;
* `readyPacedS_effect_true`  — carry across **one comparison quantum**.

**No consumer instantiates the `∀ as : List Bool` at an arbitrary list.**
`readyPacedS_ready` uses the single witness `List.replicate n false`, and the
two `effect` lemmas only prepend one element.  So the `∀ as` of

    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as

is **over-quantified relative to its consumers** — the eighth-plus instance of
the pattern CLAUDE.md lists.  That matters because `ReadyPacedS` is the `fuel`
field of `CloseoutContracts.StageEntryC`, and the run-based readiness line
(`CloseoutPreload28` / `35` / `36`) **cannot** produce a statement quantified
over lists the machine does not take (`CloseoutPreload36`, "What this is and is
not").

This file names the interface.  Anything satisfying it closes every consumer, so
`StageEntryC.fuel` can be re-cut to *some* `Φ` with `ReadyIface P Φ`, and the run
line then only has to supply a run-indexed `Φ` — no `PostRun`, no `NoReturn`.

**Not done here:** re-proving `watchSegE_constructS` and its four consumers
against an abstract `Φ`.  That is mechanical (replace the four lemma calls by
the four fields) but long, and until it is done this file removes nothing.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace PalPeg.ReadyInterface

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop
open PalPeg.GalilBranchInvariants2 (SearchReady)
open PalPeg.CloseoutReadyStage (ReadyPacedS readyPacedS_ready readyPacedS_mono
  readyPacedS_effect_false readyPacedS_effect_true)

/-- **NAMED — the readiness interface.**  The four properties every consumer of
`CloseoutReadyStage.ReadyPacedS` uses, and nothing else.  `Φ v n k` reads
"`v` can still serve `n` more events at clock slack `k`". -/
structure ReadyIface (P : Shared) (Φ : SearchVM → ℕ → ℕ → Prop) : Prop where
  /-- The search is ready right now. -/
  ready : ∀ {v : SearchVM} {n k : ℕ}, Φ v n k → SearchReady v
  /-- Fewer events and less slack is weaker. -/
  mono : ∀ {v : SearchVM} {n n' k k' : ℕ}, n ≤ n' → k' ≤ k → Φ v n k → Φ v n' k'
  /-- A background quantum spends one event and buys one unit of slack. -/
  background : ∀ {s : GalilVM} {v : SearchVM} {n k k' : ℕ}, k' ≤ k + 1 →
    s.chain = ChainVM.idle → Φ (searchLens.get s) (n + 1) k →
    searchEffect P false s v → Φ v n k'
  /-- A comparison may fire only on a full clock, and it resets the slack. -/
  comparison : ∀ {s : GalilVM} {v : SearchVM} {n k : ℕ}, 2048 ≤ k + 1 →
    s.chain = ChainVM.idle → Φ (searchLens.get s) (n + 1) k →
    searchEffect P true s v → Φ v n 0

/-- **`ReadyPacedS` is an instance.**  The four fields are the four existing
lemmas verbatim, which is the measurement: the interface is not weaker than what
`CloseoutReadyStage` proves, and by the file header it is not stronger than what
`CloseoutReadyStage` uses. -/
theorem readyIface_readyPacedS (P : Shared) : ReadyIface P ReadyPacedS where
  ready := readyPacedS_ready
  mono := fun hn hk h => readyPacedS_mono hn hk h
  background := fun hk hidle h he => readyPacedS_effect_false P hk hidle h he
  comparison := fun hk hidle h he => readyPacedS_effect_true P hk hidle h he

#print axioms readyIface_readyPacedS

end PalPeg.ReadyInterface
