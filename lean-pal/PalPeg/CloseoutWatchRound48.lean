import PalPeg.CloseoutWatchRound46

/-!
# Closeout watch round 48 — the copy/back → watch reach that CROSSES clock windows

Round 43 built the reach `ChainWatchReachC` as a run of **background** ticks
only, and Round 46 had to pay for that with `ChainWatchPhaseC` /
`PhaseWindowC`: the whole copy/back phase had to fit inside **one** clock
window, `n + 1 ≤ 2048`.  That premise is **false in general**.  The chain
period `h` of a replay-born chain is unbounded — `found_radius_le_two_period`
(`GalilReplayBudgetProof.lean:19–22`, `GalilReplaySpan.lean:116–118`) bounds
the *radius* by the period, never the period by a constant — so
`2 * xs.length + 4 + (R - C)` is not `≤ 2047`, and `chainWatchPhaseC_of_window`
(`CloseoutWatchRound46.lean:189`) correctly bottoms out at needing `h ≤ 681`.

The machine is fine.  In Scala each `step()` performs one `stepCopy` /
`stepBack` per tick (`ScaffoldChain.scala:178–187`) **whatever the clock is**;
the copy/back phase simply *spans* several comparison periods.  At `clock = 1`
the tick is not a `scan_count` but a comparison:

* on a **match** (`Tick.scan_match`) the clock is reset to `delay = 2048`, the
  right head advances, and the chain takes `ChainTick true` = one `ChainStep`
  followed by `ChainMatched` (`inc lag`, `inc margin`).  So the chain still
  makes exactly one step of progress, and the bundle is transported to the
  **next radius** `R + 1` (this is why the conclusion below quantifies `R'`);
* on a **mismatch** the round leaves the phase through its own
  `scan_shift` / `scan_fallback` exit — which is *not* a `.watch` landing at
  all, and therefore appears as a **second disjunct** of the conclusion.

So the correct statement is a general `WatchSegE`-style segment, not Round 43's
pure `count`-phase run, and its conclusion is a disjunction.

## The hypotheses, one per branch

* `WindowEndC` (§2) — the frame fact `position sT.right + R < (encoded raw).length`
  that `GalilReplaySpan.chainW_step` needs to read the input at the window end.
  This is all that survives of `PhaseWindowC`: **the `≤ 2047` conjunct is gone.**
* `ClockOneC` (§3), the `clock = 1` branch.  *Match*: the comparison tick
  exists, and the landing bundle is transported to radius `R + 1` with the
  chain's remaining work shortened by one.  Its real content is (a)
  `BlockOn raw cc b xs (C+1) (E+1)` — the newly matched place must still be
  predicted by the block — and (b) the commutation of `ChainMatched` past the
  remaining `ChainStep`s (`inc lag` / `inc margin` are read by no later step,
  `copyBit`/`copyEnd`/`backStep`/`backDone` pass them through), which turns
  `ChainWRun (n+1)` at `R` into `ChainWRun n` at `R + 1`.  *Mismatch*: the exit
  `X`, an abstract predicate standing for the round's own shift/fallback route.

## The consumer

`CloseoutWatchRound42.liveChainRoundC_of_life` cannot consume this verbatim:
it feeds the reached landing to `ReplayBornRoundC` at the **same** `R`, which
is pinned by `ReplayLanding raw cT sT R`.  §5 states the adapted
`ReplayBornRoundC'` (radius grown to any `R' `) and `MismatchRoundC` (the exit
route), and §6 derives `LiveChainRoundC` from them.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWatchRound48

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC
open PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilInvPlus3 (InvLPS)
open PalPeg.CloseoutContracts

open PalPeg.CloseoutWatchRun (LiveScanWatch)
open PalPeg.CloseoutWatchRound40 (LiveScanChain chainW_shape LiveChainRoundC)
open PalPeg.CloseoutWatchRound42 (LandingData liveScanWatch_of_liveScanChain)
open PalPeg.CloseoutWatchRound43 (ChainWRun landing_step)
open PalPeg.CloseoutWatchRound46 (chainW_true_of_window reach_watch)
open PalPeg.GalilReplaySpan (ChainW budOf)

/-! ## 1. The landing is a live scan landing -/

/-- **Closed.**  The chain shape of `LandingData` plus the control facts give
`LiveScanChain`. -/
theorem liveScanChain_of_landing {raw : List (Fin 2)} {R : ℕ} {sT : GalilVM}
    {cc b : Fin 3} {xs : List (Fin 3)} {c' : Control} {t : GalilVM}
    (hm : c'.mode = Mode.scan) (hr : c'.replaying = false) (hcl : 1 ≤ c'.clock)
    (hd : LandingData raw R sT cc b xs c' t) : LiveScanChain c' t :=
  ⟨hm, hr, hcl, chainW_shape hd.2.1⟩

/-! ## 1b. Destructors of `ChainWRun` (free indices) -/

/-- **Closed.** -/
theorem run_zero {raw : List (Fin 2)} {C E R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {x z : ChainVM} (h : ChainWRun raw C E R cc b xs 0 x z) : x = z := by
  cases h; rfl

/-- **Closed.** -/
theorem run_succ {raw : List (Fin 2)} {C E R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {n : ℕ} {x z : ChainVM} (h : ChainWRun raw C E R cc b xs (n+1) x z) :
    ∃ y, ChainStep x y ∧ (∀ bud, ChainW raw C E R bud false cc b xs y) ∧
      ChainWRun raw C E R cc b xs n y z := by
  cases h with
  | succ hs hw hr => exact ⟨_, hs, hw, hr⟩

/-! ## 2. The surviving frame fact -/

/-- **NAMED (open) — the window end is a place of the input.**  All that is
left of `CloseoutWatchRound46.PhaseWindowC`: the `≤ 2047` conjunct, which the
unbounded period makes false, is **not** here. -/
def WindowEndC (raw : List (Fin 2)) (sT : GalilVM) : Prop :=
  ∀ (R : ℕ) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
    LandingData raw R sT cc b xs c' t → position sT.right + R < (encoded raw).length

/-- **Closed.**  The remaining chain work of a landing is a finite
`ChainWRun` into `.watch` — no clock enters this at all (Round 46 §2–§3 with
the window budget, *not* with `2047`). -/
theorem landing_run {raw : List (Fin 2)} {R : ℕ} {sT : GalilVM} {cc b : Fin 3}
    {xs : List (Fin 3)} {c' : Control} {t : GalilVM}
    (hlen : position sT.right + R < (encoded raw).length)
    (hd : LandingData raw R sT cc b xs c' t) :
    ∃ (n : ℕ) (w : GalilScaffoldChainWatch.State),
      ChainWRun raw (position t.center) (position sT.right + R) (position t.right) cc b xs n
        t.chain (ChainVM.watch w) := by
  obtain ⟨-, hW, hright, -⟩ := hd
  rcases chainW_true_of_window (bud := 2 * xs.length + 4 +
      (position t.right - position t.center)) hW (le_refl _) with ⟨w, hw⟩ | hT
  · exact ⟨0, w, by rw [hw]; exact .zero _⟩
  · obtain ⟨n, w, -, hrun⟩ := reach_watch hlen (le_of_eq hright) _ _ hT
    exact ⟨n, w, hrun⟩

/-! ## 3. The `clock = 1` branch -/

/-- **NAMED (open) — the comparison tick at `clock = 1`.**  The `landing_step`
of Round 43 (`CloseoutWatchRound43.lean:133`) covers only `1 < c'.clock`
(`scan_count` / `scan_wait`).  At `clock = 1` the controller must compare:

* **match** — `Tick.scan_match` resets the clock to `2048`, moves the right
  head (`compareFound` … `afterCompare`), leaves `replaying = false` and hence
  `matchedPlace false s' s'' : s'' = s'` (so `t.replay` is untouched), and puts
  `chainAt true` = `ChainTick true` on the chain: one `ChainStep` and then
  `ChainMatched` (`inc lag`, `inc margin`).  The bundle therefore survives at
  the **next radius** `R + 1`: `LagAt` and the margin identity both move by
  one, `Leftmost`/`ScanInvariant`/`Frontier` in their matched-head versions
  (`matched_invariant'`), and `MInv` by `minv_match`.  The genuinely open part
  is `BlockOn raw cc b xs (C+1) (E+1)` and the `ChainMatched`-commutation that
  turns `ChainWRun (n+1)` into `ChainWRun n`;
* **mismatch** — the round exits through its own `scan_shift` /
  `scan_fallback`; that is the abstract `X`. -/
def ClockOneC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (sT : GalilVM)
    (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop) : Prop :=
  ∀ (R n : ℕ) (c' : Control) (t : GalilVM) (w : GalilScaffoldChainWatch.State),
    LiveScanChain c' t → c'.clock = 1 → LandingData raw R sT cc b xs c' t →
    ChainWRun raw (position t.center) (position sT.right + R) (position t.right) cc b xs (n+1)
      t.chain (ChainVM.watch w) →
    (∃ (c'' : Control) (t'' : GalilVM) (w' : GalilScaffoldChainWatch.State),
        Tick (galilFrameS P q first) 2048 ⟨c', t⟩ ⟨c'', t''⟩ ∧
        c''.mode = Mode.scan ∧ c''.replaying = false ∧ 1 ≤ c''.clock ∧
        LandingData raw (R+1) sT cc b xs c'' t'' ∧
        ChainWRun raw (position t''.center) (position sT.right + (R+1)) (position t''.right)
          cc b xs n t''.chain (ChainVM.watch w'))
    ∨ X c' t

/-! ## 4. The crossing reach -/

/-- **`ChainWatchReachM` — the crossing reach.**  From a live `.copy`/`.back`
`ChainW` landing at *any* positive clock the chain reaches `.watch`, possibly
crossing several clock windows, each crossing advancing the radius; or the
round leaves through the clock-`1` mismatch exit `X`. -/
def ChainWatchReachM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (sT : GalilVM)
    (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop) : Prop :=
  ∀ (R : ℕ) (c' : Control) (t : GalilVM),
    LiveScanChain c' t → LandingData raw R sT cc b xs c' t →
    ∃ (k : ℕ) (c'' : Control) (t'' : GalilVM),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨c'', t''⟩ ∧
      ((∃ R', LiveScanWatch c'' t'' ∧ LandingData raw R' sT cc b xs c'' t'') ∨ X c'' t'')

/-- **Closed modulo §2/§3 — the induction on the chain's remaining work.**
The measure is the length of the `ChainWRun`, which decreases on *every* tick:
at `1 < clock` by Round 43's `landing_step` (a background `ChainStep`), at
`clock = 1` by `ClockOneC` (a `ChainTick true`, i.e. still one `ChainStep`),
with the bundle transported — at the same radius in the first case, at `R + 1`
in the second.  Nothing bounds the number of crossings, which is exactly the
point. -/
theorem reachM_run (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (sT : GalilVM)
    (cc b : Fin 3) (xs : List (Fin 3)) (X : Control → GalilVM → Prop)
    (hone : ClockOneC P q first raw sT cc b xs X) :
    ∀ (n : ℕ) (R : ℕ) (c' : Control) (t : GalilVM) (w : GalilScaffoldChainWatch.State),
      LiveScanChain c' t → LandingData raw R sT cc b xs c' t →
      ChainWRun raw (position t.center) (position sT.right + R) (position t.right) cc b xs n
        t.chain (ChainVM.watch w) →
      ∃ (k : ℕ) (c'' : Control) (t'' : GalilVM),
        StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c', t⟩ ⟨c'', t''⟩ ∧
        ((∃ R', LiveScanWatch c'' t'' ∧ LandingData raw R' sT cc b xs c'' t'') ∨ X c'' t'') := by
  intro n
  induction n with
  | zero =>
    intro R c' t w hlive hd hrun
    refine ⟨0, c', t, .zero _ (fun _ _ => hd.2.2.2.2.2.2.2.2.2.2), Or.inl ⟨R, ?_, hd⟩⟩
    exact liveScanWatch_of_liveScanChain hlive (run_zero hrun)
  | succ n ih =>
    intro R c' t w hlive hd hrun
    have hsound : SoundScanNR raw ⟨c', t⟩ := fun _ _ => hd.2.2.2.2.2.2.2.2.2.2
    by_cases hc1 : c'.clock = 1
    · rcases hone R n c' t w hlive hc1 hd hrun with
        ⟨c1, t1, w', htick, hm1, hr1, hcl1, hd1, hrun1⟩ | hx
      · obtain ⟨k, c2, t2, hsteps, hres⟩ :=
          ih (R+1) c1 t1 w' (liveScanChain_of_landing hm1 hr1 hcl1 hd1) hd1 hrun1
        exact ⟨k+1, c2, t2, .succ hsound htick hsteps, hres⟩
      · exact ⟨0, c', t, .zero _ hsound, Or.inr hx⟩
    · have hgt : 1 < c'.clock := by have := hlive.2.2.1; omega
      obtain ⟨y, hstep, hw, hr⟩ := run_succ hrun
      have hne : t.chain ≠ ChainVM.idle := by
        intro e
        rw [e] at hstep
        cases hstep
        exact (hw 0).elim
      obtain ⟨c1, t1, htick, hm1, hr1, hlo, hch1, hC1, hR1, hd1⟩ :=
        landing_step P q first raw R sT cc b xs hlive.1 hlive.2.1 hgt hne hstep hw hd
      have hcl1 : 1 ≤ c1.clock := by omega
      have hrun1 : ChainWRun raw (position t1.center) (position sT.right + R)
          (position t1.right) cc b xs n t1.chain (ChainVM.watch w) := by
        rw [hC1, hR1, hch1]; exact hr
      obtain ⟨k, c2, t2, hsteps, hres⟩ :=
        ih R c1 t1 w (liveScanChain_of_landing hm1 hr1 hcl1 hd1) hd1 hrun1
      exact ⟨k+1, c2, t2, .succ hsound htick hsteps, hres⟩

/-- **`ChainWatchReachM` from the two hypotheses.** -/
theorem chainWatchReachM_of_background (P : Shared) (q : ℕ) (first : Fin 9)
    (raw : List (Fin 2)) (sT : GalilVM) (cc b : Fin 3) (xs : List (Fin 3))
    (X : Control → GalilVM → Prop) (hwin : WindowEndC raw sT)
    (hone : ClockOneC P q first raw sT cc b xs X) :
    ChainWatchReachM P q first raw sT cc b xs X := by
  intro R c' t hlive hd
  obtain ⟨n, w, hrun⟩ := landing_run (hwin R c' t cc b xs hd) hd
  exact reachM_run P q first raw sT cc b xs X hone n R c' t w hlive hd hrun

/-! ## 5. The consumer: Round 42's `liveChainRoundC_of_life`, adapted -/

/-- The common conclusion of a round started at `⟨c, t⟩` after `j` ticks. -/
def RoundGoal (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (sT : GalilVM) (j : ℕ) (c : Control) (t : GalilVM) : Prop :=
  ∃ (cT' : Control) (sT' : GalilVM) (k : ℕ) (L : List Piece),
    StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, t⟩ ⟨cT', sT'⟩ ∧
    CostedRun sT sT' (j + k) L ∧ InvLPS P q first raw cT' sT' ∧
    position sT'.right ≤ 2 * m - 1

/-- The clock-`1` **mismatch** exit, as an instance of `ChainWatchReachM`'s
abstract `X`: the round is finished from there by its own shift/fallback
route.  (This is the second disjunct `liveChainRoundC_of_life` must route.) -/
def ExitX (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (cT : Control) (sT : GalilVM) : Control → GalilVM → Prop :=
  fun c t => ∀ j, StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) j ⟨cT, sT⟩ ⟨c, t⟩ →
    RoundGoal P q first raw m sT j c t

/-- **NAMED (open) — the crossing reach, at every landing.**  `ChainWatchReachM`
of §4 with the mismatch exit instantiated; supplied by §4 from `WindowEndC` and
`ClockOneC`. -/
def ReachAllC (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (R : ℕ) (cT : Control) (sT : GalilVM), 0 < R → ReplayLanding raw cT sT R → SpanRep sT →
    ∀ (cc b : Fin 3) (xs : List (Fin 3)),
      ChainWatchReachM P q first raw sT cc b xs (ExitX P q first raw m cT sT)

/-- **NAMED (open) — `CloseoutWatchRound42.ReplayBornRoundC` with the radius
grown.**  Round 42's version pins the landing at the **same** `R` as
`ReplayLanding raw cT sT R`; after a crossing the radius is `R' > R`, so the
round hypothesis must be stated at an arbitrary `R'`.  This is the only change
Round 42's consumer needs. -/
def ReplayBornRoundC' (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ) : Prop :=
  ∀ (R : ℕ) (cT : Control) (sT : GalilVM), 0 < R →
    ReplayLanding raw cT sT R → SpanRep sT →
    ∀ (R' k0 : ℕ) (c' : Control) (t : GalilVM) (cc b : Fin 3) (xs : List (Fin 3)),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k0 ⟨cT, sT⟩ ⟨c', t⟩ →
      LiveScanWatch c' t → LandingData raw R' sT cc b xs c' t →
      RoundGoal P q first raw m sT k0 c' t

/-! ## 6. The target -/

/-- **`LiveChainRoundC` from the crossing reach.**  Both disjuncts of
`ChainWatchReachM` land in `RoundGoal` — the `.watch` one through
`ReplayBornRoundC'`, the mismatch one through `ExitX` itself — and the runs
and the cost record compose exactly as in
`CloseoutWatchRound42.liveChainRoundC_of_life`. -/
theorem liveChainRoundC_of_reachM (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (m : ℕ) (hreach : ReachAllC P q first raw m) (hround : ReplayBornRoundC' P q first raw m) :
    LiveChainRoundC P q first raw m := by
  intro R cT sT hR hRL hSR k0 c' t cc b xs hst hlive hc hrep hW hB hM hlm hi hcen hfr hrest
    hrem hout
  have hdata : LandingData raw R sT cc b xs c' t :=
    ⟨hrep, hW, hB, hM, hlm, hi, hcen, hfr, hrest, hrem, hout⟩
  obtain ⟨k1, c'', t'', hst1, hres⟩ :=
    hreach R cT sT hR hRL hSR cc b xs R c' t hlive hdata
  have hgoal : RoundGoal P q first raw m sT (k0 + k1) c'' t'' := by
    rcases hres with ⟨R', hliveW, hd''⟩ | hx
    · exact hround R cT sT hR hRL hSR R' (k0 + k1) c'' t'' cc b xs
        (stepsAll_trans hst hst1) hliveW hd''
    · exact hx (k0 + k1) (stepsAll_trans hst hst1)
  obtain ⟨cT', sT', k, L, hk, hcost, hS, hbound⟩ := hgoal
  refine ⟨cT', sT', k1 + k, L, stepsAll_trans hst1 hk, ?_, hS, hbound⟩
  have e : k0 + (k1 + k) = k0 + k1 + k := by omega
  rw [e]
  exact hcost

end PalPeg.CloseoutWatchRound48

#print axioms PalPeg.CloseoutWatchRound48.liveScanChain_of_landing
#print axioms PalPeg.CloseoutWatchRound48.landing_run
#print axioms PalPeg.CloseoutWatchRound48.reachM_run
#print axioms PalPeg.CloseoutWatchRound48.chainWatchReachM_of_background
#print axioms PalPeg.CloseoutWatchRound48.liveChainRoundC_of_reachM
