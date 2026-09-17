import PalPeg.CloseoutOracle5

/-!
# `CloseoutPreload41`: the replay half of `hpres`, and the run-predicate bridge

Three findings, in the order the task posed them.

**(1) `ReadyFieldP4` is not needed: `ReadyFieldP3` already covers the replay.**
The premise of the plan was that `GalilReplaySpan`'s uses of the universal
`hpres` sit at `Mode.replay` states while `CloseoutPreload39.ReadyFieldP3`'s
`paced` / `paced0` are conditioned on `Mode.scan`.  That is **false**: the
fallback replay runs at `c.mode = .scan` with the *flag* `c.replaying = true`
(`GalilReplaySpan.idle_countdown3` takes `hm : c.mode = .scan`,
`hr : c.replaying = true`, `GalilReplaySpan:1484–1487`; `idle_compare3`'s use of
`hpres` at `GalilReplaySpan:1737` is likewise under `c.mode = .scan`,
`c.replaying = true`, `c.clock = 1`, `s.chain = ChainVM.idle`).  `ReadyFieldP3`
never mentions `replaying`, so its clauses apply verbatim there, and the two
polarities the replay consumes are exactly `HpresAt`'s two cases:
`a = false` at any clock (the countdown quantum) and `a = true` at `clock = 1`
(the comparison quantum).  `hpresAt_replaying` below records this; `ReadyFieldP4`
is therefore `ReadyFieldP3` itself, and `readyField4_tick` /
`readyField4_along_run` are `CloseoutPreload39.readyField3_tick` /
`readyField3_along_run` unchanged.

**(2) `hpresRep` is genuinely universal, hence refuted.**  As it appears in
`CloseoutOracle5.cycleOracleMC2C_of_piecesP` it is `∀ s a v, …`, with no run,
no clock and no chain condition, so `GalilLeafPres.hpres_false_at` refutes it
just as it refutes the original `hpres`.  Its reachability-restricted form is
`HpresRepAt` below (`HpresAt` at every state of a `SoundScanNR` run from an
`InvLPC` origin).  Making the three `GalilReplaySpan` consumers accept it is an
**edit to `GalilReplaySpan`**, not a wrapper: `idle_countdown3` (`:1474`),
`idle_compare3` (`:1582`) and `replay_construct3` (`:1765`) thread `hpres` as a
plain hypothesis through an induction that already carries
`StepsAll … (SoundScanNR raw)` witnesses from the entry, so the primed variants
would pass `HpresRepAt` plus the accumulated run and apply it at each use site
— mechanical, but it must be repeated for all **three** copies of the block
(`…3`, `…3S`, and the third at `:3197–3500`), i.e. roughly 9 lemma signatures
and 6 use sites.

**(3) The run-predicate bridge, proved here.**  The oracle's runs carry
`SoundScanNR w`; the readiness field propagates along `BigPack2M''` runs.  The
direction needed is `SoundScanNR → BigPack2M''`, which is not a weakening: it is
`CloseoutPackRun18.packRunR_M''`'s inner induction, re-run so that it returns
the *upgraded run* rather than `IPackM` pointwise.  That is
`stepsAll_bigPack2M''_of_soundScanNR`, and `hpresAt_along_soundScanNR` is the
readiness leaf delivered along an oracle-shaped run.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload41

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun10 (IPackM)
open PalPeg.CloseoutPackRun18 (BigPack2M'' bigPack2M''_tick Extra3 H_extraEntry3 H_extraTick3)
open PalPeg.CloseoutPackRun16 (H_marksEntry')
open PalPeg.CloseoutPackRun11 (BigResid6)
open PalPeg.GalilOracleLeaves2 (hlive_of_invLPC)
open PalPeg.GalilInvPlus2 (InvLPC)
open PalPeg.CloseoutPreload39 (ReadyFieldP3 readyField3_along_run)
open PalPeg.CloseoutPreload40 (HpresAt searchReadyB_of_readyField3)
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. `ReadyFieldP4 = ReadyFieldP3`: the replay clause is already there -/

/-- **`ReadyFieldP4`.**  No new clause: the fallback replay is a `scan` mode
with the `replaying` flag set, and `ReadyFieldP3` is silent about the flag. -/
abbrev ReadyFieldP4 : ℕ → State GalilVM → Prop := ReadyFieldP3

/-- **The replay half of the leaf.**  `ReadyFieldP3` at a `scan` state supplies
`HpresAt` whatever the `replaying` flag says — which is exactly the situation of
`GalilReplaySpan.idle_countdown3` / `idle_compare3`. -/
theorem hpresAt_replaying (P : Shared) {n : ℕ} {c : Control} {s : GalilVM}
    (hf : ReadyFieldP4 (n + 1) ⟨c, s⟩) (hm0 : c.mode = Mode.scan)
    (_hrep : c.replaying = true) :
    HpresAt P c s :=
  searchReadyB_of_readyField3 P hf hm0

#print axioms hpresAt_replaying

/-- The two polarities the replay actually consumes, read off `HpresAt`:
the countdown quantum (`a = false`, any clock) and the comparison quantum
(`a = true`, `clock = 1`). -/
theorem hpresAt_countdown {P : Shared} {c : Control} {s : GalilVM} {v : SearchVM}
    (h : HpresAt P c s) (hidle : s.chain = ChainVM.idle)
    (hv : searchEffect P false s v) :
    PalPeg.GalilBranchInvariants2.SearchReady v :=
  h false v hidle (by intro hx; exact absurd hx (by decide)) hv

theorem hpresAt_compare {P : Shared} {c : Control} {s : GalilVM} {v : SearchVM}
    (h : HpresAt P c s) (hidle : s.chain = ChainVM.idle) (hc : c.clock = 1)
    (hv : searchEffect P true s v) :
    PalPeg.GalilBranchInvariants2.SearchReady v :=
  h true v hidle (fun _ => by omega) hv

#print axioms hpresAt_compare

/-! ## 2. The run-predicate bridge -/

section BridgeT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(KEY) `SoundScanNR` runs upgrade to `BigPack2M''` runs.**  The inner
induction of `CloseoutPackRun18.packRunR_M''`, returning the whole run over the
enlarged pack instead of `IPackM` state by state.  This is the bridge between
the oracle's run predicate (`SoundScanNR`) and the readiness field's
(`BigPack2M''`). -/
theorem stepsAll_bigPack2M''_of_soundScanNR {w : List (Fin 2)}
    (hr : BigResid6 centre place entry q first w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r) :
    ∀ (k j : ℕ) (x y : State GalilVM),
      Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x →
      BigPack2M'' centre place entry q first w x →
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
      StepsAll (galilFrameS (PofC centre place entry w) q first) 2048
        (BigPack2M'' centre place entry q first w) k x y := by
  intro k
  induction k with
  | zero =>
    intro j x y _ hbx h
    cases h with
    | zero _ _ => exact .zero _ hbx
  | succ n ih =>
    intro j x y hjx hbx h
    cases h with
    | succ hq ht hrest =>
      have hstep : Steps (galilFrameS (PofC centre place entry w) q first) 2048 (j + 1) ⟨c, r⟩ _ :=
        steps_trans hjx (.succ ht (.zero _))
      exact .succ hbx ht
        (ih (j + 1) _ y hstep
          (bigPack2M''_tick centre place entry q first hr het hme hbx ht
            (stepsAll_head hrest)
            (hlive_of_invLPC centre place entry q first hIC (j + 1) _ hstep))
          hrest)

#print axioms stepsAll_bigPack2M''_of_soundScanNR

/-! ## 3. The readiness leaf along an oracle-shaped run -/

/-- **`HpresRepAt`: the reachability-restricted replacement for the refuted
universal `hpresRep`.**  `HpresAt` at every `scan` state of a `SoundScanNR` run
out of `x`. -/
def HpresRepAt (w : List (Fin 2)) (x : State GalilVM) : Prop :=
  ∀ (k : ℕ) (y : State GalilVM),
    StepsAll (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) k x y →
    y.ctl.mode = Mode.scan → HpresAt (PofC centre place entry w) y.ctl y.vm

/-- **`hpresAt_along_soundScanNR`.**  `CloseoutPreload40.hpresAt_along_run` with
the oracle's own run predicate, via the bridge.  Covers replay states too
(§1): the conclusion asks only for `Mode.scan`, not for `replaying = false`. -/
theorem hpresAt_along_soundScanNR {w : List (Fin 2)} {n : ℕ}
    (hr : BigResid6 centre place entry q first w)
    (het : H_extraTick3 centre place entry q first w)
    (hme : H_marksEntry' (PofC centre place entry w) q first)
    {c : Control} {r : GalilVM} (hIC : InvLPC w c r)
    {j : ℕ} {x : State GalilVM}
    (hjx : Steps (galilFrameS (PofC centre place entry w) q first) 2048 j ⟨c, r⟩ x)
    (hbx : BigPack2M'' centre place entry q first w x)
    (hf : ReadyFieldP4 (n + 1) x)
    (hentry : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.scan → restartVM entry z.vm z'.vm → ReadyFieldP3 (n + 1) z')
    (hentry' : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.replayStart → ReadyFieldP3 (n + 1) z') :
    HpresRepAt centre place entry q first w x := by
  intro k y hst hm
  have hbig := stepsAll_bigPack2M''_of_soundScanNR centre place entry q first hr het hme hIC
    k j x y hjx hbx hst
  have hy : ReadyFieldP3 (n + 1) y :=
    readyField3_along_run centre place entry q first hbig hf hentry hentry'
  obtain ⟨cy, sy⟩ := y
  exact searchReadyB_of_readyField3 _ hy hm

#print axioms hpresAt_along_soundScanNR

end BridgeT

end PalPeg.CloseoutPreload41
