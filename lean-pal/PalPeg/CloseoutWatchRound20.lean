import PalPeg.CloseoutWatchRound19
import PalPeg.GalilTickFair

/-!
# Closeout watch round 20 — `WatchPrefixC` discharged

`CloseoutWatchRound19.WatchPrefixC` (any two `WatchSeg` runs out of the
preparation landing are prefix-comparable) is a consequence of step
determinism of `WatchSeg` alone: the three stepping constructors are pairwise
exclusive by their guards (`wait`: `¬ canRight`; `count`: `canRight ∧ 1 < clock`;
`match`: `canRight ∧ clock = 1`), and each successor is a function of the
source (`backgroundS_unique`, `chainTick_unique`, `searchEffect_unique`,
`refresh_unique`).  **No `WatchDetGuard` is needed**, and no liveness of the
landing either.

* `refresh_unique` — the output refresh is a function.
* `watchSeg_step_unique` — one step of `WatchSeg` is a function of its source.
* `watchSeg_prefix` — two runs from one source are prefix-comparable.
* `watchPrefixC_of_unique` — the producer for `WatchPrefixC`, no hypothesis.
* `foundExit_compare_final11` — `foundExit_compare_final10` without `hpre`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

namespace PalPeg.CloseoutWatchRound20

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier GalilScaffoldChainInputSupply
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilFoundStage PalPeg.GalilTraceCost
open PalPeg.CloseoutContracts
open PalPeg.CloseoutWatchRun (LiveScanWatch roundFuel)
open PalPeg.CloseoutWatchPhase2 (LandingRestartReach)
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound3 (DistanceNonnegC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC ShiftReachC ShiftRoundAtC BreakTermData)
open PalPeg.CloseoutWatchRound10 (FoundDpAtC)
open PalPeg.CloseoutWatchRound6 (RightCanC RightSaneC StartLeC LedgerOriginC PeriodMatchC)
open PalPeg.CloseoutWatchRound4 (ZeroLagAtMatchC)
open PalPeg.CloseoutPrepInputs2 (MismatchExitG)
open PalPeg.CloseoutPrepInputs3 (PrepInputsG3)
open PalPeg.CloseoutWatchRound17 (FallbackRouteW)
open PalPeg.CloseoutWatchRound19 (WatchPrefixC)
open PalPeg.GalilTickFair (backgroundS_unique searchEffect_unique)


/-! ## 1. The output refresh is a function -/

theorem refresh_unique {σ : Type} (F : Frame σ) (s : σ) (old : Bool) {o₁ o₂ : Bool}
    (h1 : refresh F s old o₁) (h2 : refresh F s old o₂) : o₁ = o₂ := by
  classical
  obtain ⟨ha₁, hb₁⟩ := h1
  obtain ⟨ha₂, hb₂⟩ := h2
  by_cases hon : F.onLetter s
  · have e₁ := ha₁ hon
    have e₂ := ha₂ hon
    cases o₁ <;> cases o₂ <;> simp_all
  · rw [hb₁ hon, hb₂ hon]

/-! ## 2. One `WatchSeg` step is a function of its source -/

/-- The scan projection chosen by a matched comparison is determined by `s`. -/
theorem compare_scan_unique {P : Shared} {q : ℕ} {first : Fin 9} {s : GalilVM} {vs₁ vs₂ : ScanVM}
    (h1 : (galilFrame P q first).compare s (scanLens.set s vs₁))
    (h2 : (galilFrame P q first).compare s (scanLens.set s vs₂)) : vs₁ = vs₂ := by
  obtain ⟨⟨hl₁, hr₁, ht₁⟩, -⟩ := h1
  obtain ⟨⟨hl₂, hr₂, ht₂⟩, -⟩ := h2
  rw [scanLens.get_set] at hl₁ hr₁ ht₁ hl₂ hr₂ ht₂
  have hl : vs₁.left = vs₂.left := hl₁.trans hl₂.symm
  have hr : vs₁.right = vs₂.right := hr₁.trans hr₂.symm
  have hc : vs₁.chain = vs₂.chain := PalPeg.GalilTickDet.chainTick_unique ht₁ ht₂
  exact PalPeg.GalilTickFair.scanVM_ext hl hr hc

/-- **One step of `WatchSeg` is a function of its source.**  Statement: if a
run from `(c, s)` is not `stop`, its first successor is unique — packaged as:
for any two runs `h1 h2` from `(c, s)` that both take a step, the states after
the first step coincide, and the tails are runs from that state. -/
theorem watchSeg_step_unique {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c₁ c₂ : Control} {s s₁ s₂ : GalilVM}
    (h1 : WatchSeg P q first delay c s c₁ s₁) (h2 : WatchSeg P q first delay c s c₂ s₂) :
    (c₁ = c ∧ s₁ = s) ∨ (c₂ = c ∧ s₂ = s) ∨
      ∃ (c' : Control) (s' : GalilVM),
        WatchSeg P q first delay c' s' c₁ s₁ ∧ WatchSeg P q first delay c' s' c₂ s₂ := by
  cases h1 with
  | stop c s => exact Or.inl ⟨rfl, rfl⟩
  | wait c s s' hm hr hn hb rest =>
    cases h2 with
    | stop c s => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | wait c s s'' hm' hr' hn' hb' rest' =>
      have := backgroundS_unique hb hb'
      subst this
      exact Or.inr (Or.inr ⟨c, s', rest, rest'⟩)
    | count c s s'' hm' hr' ha' hc' hb' rest' => exact absurd ha' hn
    | «match» c s vs vq o hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' => exact absurd ha' hn
  | count c s s' hm hr ha hc hb rest =>
    cases h2 with
    | stop c s => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | wait c s s'' hm' hr' hn' hb' rest' => exact absurd ha hn'
    | count c s s'' hm' hr' ha' hc' hb' rest' =>
      have := backgroundS_unique hb hb'
      subst this
      exact Or.inr (Or.inr ⟨_, s', rest, rest'⟩)
    | «match» c s vs vq o hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' => omega
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest =>
    cases h2 with
    | stop c s => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | wait c s s'' hm' hr' hn' hb' rest' => exact absurd ha hn'
    | count c s s'' hm' hr' ha' hc' hb' rest' => omega
    | «match» c s vs' vq' o' hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' =>
      have hvs : vs = vs' := compare_scan_unique hcmp hcmp'
      subst hvs
      have hvq : vq = vq' := searchEffect_unique hq hq'
      subst hvq
      have hoo : o = o' := refresh_unique _ _ _ ho ho'
      subst hoo
      exact Or.inr (Or.inr ⟨_, _, rest, rest'⟩)

/-! ## 3. Prefix comparability -/

/-- **Two runs from one source are prefix-comparable.**  Induction on the
first run; `watchSeg_step_unique` aligns the first steps. -/
theorem watchSeg_prefix {P : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c₁ : Control} {s s₁ : GalilVM}
    (h1 : WatchSeg P q first delay c s c₁ s₁) :
    ∀ {c₂ : Control} {s₂ : GalilVM}, WatchSeg P q first delay c s c₂ s₂ →
      WatchSeg P q first delay c₁ s₁ c₂ s₂ ∨ WatchSeg P q first delay c₂ s₂ c₁ s₁ := by
  induction h1 with
  | stop c s => intro c₂ s₂ h2; exact Or.inl h2
  | wait c s s' hm hr hn hb rest ih =>
    intro c₂ s₂ h2
    cases h2 with
    | stop c s => exact Or.inr (.wait c s s' hm hr hn hb rest)
    | wait c s s'' hm' hr' hn' hb' rest' =>
      have := backgroundS_unique hb hb'
      subst this
      exact ih rest'
    | count c s s'' hm' hr' ha' hc' hb' rest' => exact absurd ha' hn
    | «match» c s vs vq o hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' => exact absurd ha' hn
  | count c s s' hm hr ha hc hb rest ih =>
    intro c₂ s₂ h2
    cases h2 with
    | stop c s => exact Or.inr (.count c s s' hm hr ha hc hb rest)
    | wait c s s'' hm' hr' hn' hb' rest' => exact absurd ha hn'
    | count c s s'' hm' hr' ha' hc' hb' rest' =>
      have := backgroundS_unique hb hb'
      subst this
      exact ih rest'
    | «match» c s vs vq o hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' => omega
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
    intro c₂ s₂ h2
    cases h2 with
    | stop c s => exact Or.inr (.match c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest)
    | wait c s s'' hm' hr' hn' hb' rest' => exact absurd ha hn'
    | count c s s'' hm' hr' ha' hc' hb' rest' => omega
    | «match» c s vs' vq' o' hm' hr' ha' hc' hne' hcmp' hmt' hq' ho' rest' =>
      have hvs : vs = vs' := compare_scan_unique hcmp hcmp'
      subst hvs
      have hvq : vq = vq' := searchEffect_unique hq hq'
      subst hvq
      have hoo : o = o' := refresh_unique _ _ _ ho ho'
      subst hoo
      exact ih rest'

/-- **The producer for `WatchPrefixC` — no hypothesis.** -/
theorem watchPrefixC_of_unique (P : Shared) (q : ℕ) (first : Fin 9) (cP : Control) (sP : GalilVM) :
    WatchPrefixC P q first cP sP :=
  fun _ _ _ _ h2 h3 => watchSeg_prefix h2 h3

/-! ## 4. The consumer -/

/-- **Derived — `CloseoutWatchRound19.foundExit_compare_final10` with
`WatchPrefixC` discharged.** -/
theorem foundExit_compare_final11 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (m h lower span : ℕ)
    (hP : Decodes (PofC centre place entry w))
    (hex : ∀ s, (PofC centre place entry w).replayExhausted s = zero s.replay)
    (hready : PalPeg.GalilReplayChainSeg.ChainTickable)
    (hcan : RightCanC) (hsane : RightSaneC) (hstart : StartLeC)
    (hor : LedgerOriginC centre place entry q first 2048 w)
    (hzl : ZeroLagAtMatchC) (hnn : DistanceNonnegC) (hpm : PeriodMatchC)
    {c c' cP : Control} {r t sP : GalilVM}
    (hE : StageEntryC (PofC centre place entry w) q first w c r)
    (hsW : SegReachedW centre place entry q first w c r c' t)
    (a : Fin 2) (ls rs qw : List (Fin 2)) (gap : Bool)
    (hprep : PrepInputsG3 (PofC centre place entry w) q first ⟨a :: ls, gap⟩ lower span cP sP)
    (hmis : MismatchExitG (PofC centre place entry w) q first w m c r cP sP)
    (hctx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hfb : FallbackRouteW (PofC centre place entry w) q first w m c r cP sP)
    (hLR : LandingRestartReach (PofC centre place entry w) q first w c r)
    (hstage : ReplayStage w (PofC centre place entry w) q first c r)
    (hmP : cP.mode = .scan) (hrP : cP.replaying = false) (hcP : 1 ≤ cP.clock)
    (hreachWatch : ∃ (es : List Bool) (c2 : Control) (s2 : GalilVM),
      WatchSegE (PofC centre place entry w) q first 2048 es cP sP c2 s2 ∧
        PalPeg.CloseoutWatchRun.LiveScanWatch c2 s2)
    (hat : FoundDpAtC centre place entry q first w lower span h c r)
    (hreach : ShiftReachC centre place entry q first w h)
    (hround : ShiftRoundAtC centre place entry q first w m h lower)
    (hland : ∀ sF : GalilVM,
      PalPeg.CloseoutWatchRound5.BreakLandingC centre place entry q first w h sF cP sP)
    (hstepBreak : ∀ (c0 : Control) (s0 : GalilVM), LiveScanWatch c0 s0 →
      PalPeg.CloseoutWatchRun.RoundStepC (PofC centre place entry w) q first (roundFuel h)
        (BreakTermData centre place entry q first w m h) c0 s0) :
    FoundExit (PofC centre place entry w) q first w m c r :=
  PalPeg.CloseoutWatchRound19.foundExit_compare_final10 centre place entry q first w m h
    lower span hP hex hready hcan hsane hstart hor hzl hnn hpm hE hsW a ls rs qw gap hprep hmis
    hctx (watchPrefixC_of_unique _ _ _ _ _) hfb hLR hstage hmP hrP hcP hreachWatch hat hreach hround
    hland hstepBreak

end PalPeg.CloseoutWatchRound20

#print axioms PalPeg.CloseoutWatchRound20.refresh_unique
#print axioms PalPeg.CloseoutWatchRound20.compare_scan_unique
#print axioms PalPeg.CloseoutWatchRound20.watchSeg_step_unique
#print axioms PalPeg.CloseoutWatchRound20.watchSeg_prefix
#print axioms PalPeg.CloseoutWatchRound20.watchPrefixC_of_unique
#print axioms PalPeg.CloseoutWatchRound20.foundExit_compare_final11
