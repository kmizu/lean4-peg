import PalPeg.CloseoutPackRun40

/-!
# `CloseoutPackRun41`: a chain-local positional payload (`ScanPositionPayloadWithChainLedger`)

`CloseoutPackRun40.chainPosInv'_tick` still carries the three Run34/38 payload
residues (`BgRes`, `MatchRes`, `posPayload_shiftDone`).  Run38's analysis names
their content: the source payload says nothing about a `copy`/`back` chain,
does not know the live verifier `Sane`, and its `verNext` is a *one-tick
lookahead*, which needs two ticks to preserve.

This file re-cuts the payload so that the chain half is **closed under
`ChainStep` and `ChainMatched`** on its own:

* §1 `ChainPositionLedger z R`: one clause per live chain shape (`watch`/`back`/`copy`),
  each asserting `canRight ver ∧ Sane ver ∧ position ver + lag = R`.  This
  replaces Run38's `SrcPos` (its `saneVer`/`backPos` are two of the clauses)
  *and* the lookahead: `chainPos_step` / `chainPos_matched` push `ChainPositionLedger`
  through a chain tick, so the verifier facts at the **target** come from the
  verifier facts at the **source**, not from a lookahead.
* §2 `ConsumeAvail`: the one genuinely non-local residue that survives — a
  `take`/`immediate` consume moves the verifier, and `canRight` of the *moved*
  verifier is an input-supply fact (`Extra3.scanAvail`'s family), not a
  consequence of the source.  `right_sane` supplies the moved `Sane`, so this
  is all that is left of Run38's `verNext`.
* §3 `ScanPositionPayloadWithChainLedger` (`canR`, `radLe`, `chainPos`), the shift-mode clause
  `ShiftPhaseChainLedger` (the chain half alone — `radLe` is meaningless while the centre
  is moving), and `ChainPositionInvariantWithShiftPhase`.
* §4 `chainPosInv2_tick`.  `shift_one` **closes outright** (`shiftTick` moves
  only centre/left, `chainShiftOne` fixes verifier and lag, and `t.right =
  s.right` because `right` is not a component of `shiftLens`), as do all
  `idle`-chain and off-mode branches.  Named: `H_BackgroundLandingChainLedger`, `H_MatchLandingChainLedger`,
  `H_ShiftEntryChainLedger`, `H_ShiftExitRadiusLedger`.
* §5 `watchShiftS_of_chainPosInv2`: `WatchShiftS` with **no** `H_FourSemiperiodsLeDistance`
  (Run40) and **no** lookahead — the target's verifier pair comes from
  `chainPos_step`, since an unmatched comparison's chain effect is a plain
  `ChainStep`.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun41

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilChainCoupling
open PalPeg.CloseoutLPack5 PalPeg.CloseoutPackRun6 PalPeg.CloseoutPackRun10
open PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack4
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun30 PalPeg.CloseoutPackRun32
open PalPeg.CloseoutPackRun34 PalPeg.CloseoutPackRun38 PalPeg.CloseoutPackRun40
open PalPeg.GalilBranchInvariants

/-! ## 1. The chain-local ledger -/

/-- **`ChainPositionLedger z R`**: every live shape of the chain `z` carries a verifier
that can move, is `Sane`, and sits `lag` cells behind the position `R`.
`idle` and `broken` carry nothing. -/
structure ChainPositionLedger (z : ChainVM) (R : ℕ) : Prop where
  watch : ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
    GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
      Sane wch.machine.verifier ∧
      (position wch.machine.verifier : ℤ) + value wch.lag = R
  back : ∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    z = .back v h lag margin ver →
      GalilScaffoldChainVerifier.canRight ver ∧ Sane ver ∧
        (position ver : ℤ) + value lag = R
  copy : ∀ (t : GalilScaffoldTape.Tape) (h : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
    z = .copy t h p v lag margin ver →
      GalilScaffoldChainVerifier.canRight ver ∧ Sane ver ∧
        (position ver : ℤ) + value lag = R

theorem chainPos_idle (R : ℕ) : ChainPositionLedger .idle R :=
  ⟨(fun _ h => by cases h), (fun _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ h => by cases h)⟩

theorem chainPos_broken (wch : GalilScaffoldChainWatch.State) (R : ℕ) :
    ChainPositionLedger (.broken wch) R :=
  ⟨(fun _ h => by cases h), (fun _ _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ _ h => by cases h)⟩

/-! ## 2. `ConsumeAvail`: the one non-local residue -/

/-- **(NAMED residue.)**  The verifier of a watching chain can still move
*after* one consume.  A `take` (`Internal.take`) and an `immediate`
(`Outer.immediate`) both replace the verifier by `right verifier`, and
`canRight` of that moved head is an input-supply fact — the verifier's
analogue of `Extra3.scanAvail`.  `Sane` of the moved head is **not** part of
this: it comes from `GalilFrontMono.right_sane`. -/
def ConsumeAvail (z : ChainVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
    GalilScaffoldChainVerifier.canRight
      (GalilScaffoldChainVerifier.right wch.machine.verifier)

/-- **One background chain step keeps `ChainPositionLedger`.**  `take` moves the verifier
one cell right and pays one unit of lag; `copyBit`/`backStep` keep both;
`copyEnd` carries the `copy` clause into the `back` clause; `backDone` carries
the `back` clause into the new watch. -/
theorem chainPos_step {x z : ChainVM} {R : ℕ} (hP : ChainPositionLedger x R) (hav : ConsumeAvail x)
    (hst : ChainStep x z) : ChainPositionLedger z R := by
  cases hst with
  | idle => exact hP
  | brokenIdle w => exact chainPos_broken w R
  | copyBit t h p v lag margin ver a _ _ _ =>
    obtain ⟨hc, hs, hp⟩ := hP.copy t h p v lag margin ver rfl
    exact ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hb => by cases hb),
      (fun _ _ _ _ _ _ _ hcp => by cases hcp; exact ⟨hc, hs, hp⟩)⟩
  | copyEnd t h p v lag margin ver b _ _ _ =>
    obtain ⟨hc, hs, hp⟩ := hP.copy t h p v lag margin ver rfl
    exact ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hb => by cases hb; exact ⟨hc, hs, hp⟩),
      (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
  | backStep v h lag margin ver _ =>
    obtain ⟨hc, hs, hp⟩ := hP.back v h lag margin ver rfl
    exact ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hb => by cases hb; exact ⟨hc, hs, hp⟩),
      (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
  | backDone v h lag margin ver _ =>
    obtain ⟨hc, hs, hp⟩ := hP.back v h lag margin ver rfl
    exact ⟨(fun _ hw => by cases hw; exact ⟨hc, hs, hp⟩), (fun _ _ _ _ _ hb => by cases hb),
      (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
  | watchStep w w' hi =>
    obtain ⟨hc, hs, hp⟩ := hP.watch w rfl
    cases hi with
    | idle _ =>
      exact ⟨(fun _ hw => by cases hw; exact ⟨hc, hs, hp⟩), (fun _ _ _ _ _ hb => by cases hb),
        (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
    | take _ hg =>
      have hr := right_sane hc hs
      have hcn : GalilScaffoldChainVerifier.canRight
          (GalilScaffoldChainVerifier.right w.machine.verifier) := hav w rfl
      refine ⟨fun wch hw => ?_, (fun _ _ _ _ _ hb => by cases hb),
        (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
      cases hw
      refine ⟨hcn, hr.2, ?_⟩
      show (position (GalilScaffoldChainVerifier.right w.machine.verifier) : ℤ) +
        value (dec w.lag) = R
      rw [hr.1, dec_value]
      push_cast
      omega

/-- **One match credit raises the ledger by one.**  `queued` pays into the lag,
`immediate` moves the verifier, `copy`/`back` pay into the lag, `breaks` lands
in `broken`. -/
theorem chainPos_matched {y z : ChainVM} {R : ℕ} (hP : ChainPositionLedger y R) (hav : ConsumeAvail y)
    (hm : ChainMatched y z) : ChainPositionLedger z (R + 1) := by
  cases hm with
  | idle => exact chainPos_idle _
  | copy t h p v lag margin ver =>
    obtain ⟨hc, hs, hp⟩ := hP.copy t h p v lag margin ver rfl
    refine ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hb => by cases hb),
      fun _ _ _ _ _ _ _ hcp => ?_⟩
    cases hcp
    refine ⟨hc, hs, ?_⟩
    show (position ver : ℤ) + value (inc lag) = R + 1
    rw [inc_value]; omega
  | back v h lag margin ver =>
    obtain ⟨hc, hs, hp⟩ := hP.back v h lag margin ver rfl
    refine ⟨(fun _ hw => by cases hw), fun _ _ _ _ _ hb => ?_,
      (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
    cases hb
    refine ⟨hc, hs, ?_⟩
    show (position ver : ℤ) + value (inc lag) = R + 1
    rw [inc_value]; omega
  | breaks w w' hb => exact chainPos_broken w' _
  | watch w w' ho =>
    obtain ⟨hc, hs, hp⟩ := hP.watch w rfl
    cases ho with
    | queued _ =>
      refine ⟨fun wch hw => ?_, (fun _ _ _ _ _ hb => by cases hb),
        (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
      cases hw
      refine ⟨hc, hs, ?_⟩
      show (position w.machine.verifier : ℤ) + value (inc w.lag) = R + 1
      rw [inc_value]; omega
    | immediate _ hg =>
      have hr := right_sane hc hs
      have hcn : GalilScaffoldChainVerifier.canRight
          (GalilScaffoldChainVerifier.right w.machine.verifier) := hav w rfl
      refine ⟨fun wch hw => ?_, (fun _ _ _ _ _ hb => by cases hb),
        (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
      cases hw
      refine ⟨hcn, hr.2, ?_⟩
      show (position (GalilScaffoldChainVerifier.right w.machine.verifier) : ℤ) +
        value w.lag = R + 1
      rw [hr.1]
      push_cast
      omega

#print axioms chainPos_step
#print axioms chainPos_matched

/-! ## 3. `ScanPositionPayloadWithChainLedger`, `ShiftPhaseChainLedger`, `ChainPositionInvariantWithShiftPhase` -/

section Pos
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`ScanPositionPayloadWithChainLedger`**: `CloseoutPackRun34.ScanPositionPayload` with the one-tick
lookahead `verNext` replaced by the *state-local* chain ledger `ChainPositionLedger`
(which also absorbs Run38's `SrcPos`). -/
structure ScanPositionPayloadWithChainLedger (w : List (Fin 2)) (s : GalilVM) : Prop where
  canR : GalilScaffoldChainVerifier.canRight s.right
  radLe : ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
    value s.radius ≤ (rad : ℤ)
  chainPos : ChainPositionLedger s.chain (position s.right)

/-- **The shift-mode clause.**  While the centre moves, `radLe` is meaningless
(the scan geometry is `ShiftGeom`, not `ScanInvariant`), so only the chain
ledger is carried.  `shift_one` preserves exactly this. -/
def ShiftPhaseChainLedger (s : GalilVM) : Prop := ChainPositionLedger s.chain (position s.right)

/-- **`ChainPositionInvariantWithShiftPhase`**: `Coupled'` (Run40, so `H_FourSemiperiodsLeDistance` is a theorem), the
scan payload, and the shift-mode chain ledger. -/
structure ChainPositionInvariantWithShiftPhase (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  coupled : Coupled' c s
  payload : ScanNR ⟨c, s⟩ → s.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w s
  shiftPay : c.mode = Mode.shift → ShiftPhaseChainLedger s

theorem chainPosInv2_of_idle {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hi : s.chain = ChainVM.idle) : ChainPositionInvariantWithShiftPhase w c s :=
  ⟨coupled'_of_idle hi, fun _ hni => absurd hi hni, fun _ => by
    show ChainPositionLedger s.chain _
    rw [hi]; exact chainPos_idle _⟩

/-! ## 4. One tick -/

/-- **(NAMED) `H_BackgroundLandingChainLedger`.**  The `scan_wait`/`scan_count` landing.  Everything
chain-side now follows from `chainPos_step`; what is left at the source is the
chain-start shape (`s.chain = idle`, where the payload is empty and the new
`copy` chain's verifier is the centre head) together with `ConsumeAvail`. -/
def H_BackgroundLandingChainLedger (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s t : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t

/-- **(NAMED) `H_MatchLandingChainLedger`.**  The `scan_match` landing: `canRight` and the
radius ledger at the *moved* heads (`Extra3.scanAvail` / `ScanInvariant` at
`right s.right`), the replaying source payload, and `ConsumeAvail`. -/
def H_MatchLandingChainLedger (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → GalilScaffoldChainVerifier.canRight t.right →
    ScanPositionPayloadWithChainLedger w t

/-- **(NAMED) `H_ShiftEntryChainLedger`.**  The `scan_shift` landing establishes the
shift-mode ledger at the entry state (`beginShiftVM'` applies
`GalilScaffoldChainWatch.immediate`, i.e. one consume, at the moved right
head). -/
def H_ShiftEntryChainLedger (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s s' t : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t →
    GalilScaffoldChainVerifier.canRight t.right → ShiftPhaseChainLedger t

/-- **(NAMED) `H_ShiftExitRadiusLedger`.**  At the `shift_done` exit only the *radius
ledger* is missing: the chain half is `ChainPositionInvariantWithShiftPhase.shiftPay`, and `canRight R`
is the scan-mode supply.  (`LPackM2.shiftGeom` + `shiftGeom_exit` produce the
`ScanInvariant` this is measured against.) -/
def H_ShiftExitRadiusLedger (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s : GalilVM), c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ChainPositionInvariantWithShiftPhase w c s → s.chain ≠ ChainVM.idle →
    GalilScaffoldChainVerifier.canRight s.right ∧
      ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
        value s.radius ≤ (rad : ℤ)

/-- **(NAMED, state-local) the four branch obligations at one source state.**

`H_BackgroundLandingChainLedger` / `H_MatchLandingChainLedger` / `H_ShiftEntryChainLedger` / `H_ShiftExitRadiusLedger` are each
`∀ (c : Control) (s : GalilVM), …` over the **source** state of the landing, and
`chainPosInv2_tick` applies all four at its own `(c, s)` and nowhere else.
Bundling them per state is what lets a run carry them: the facts that discharge
them (`LPackM2.shiftGeom`, the chain-side ledger `ChainPositionLedger`, the input supply)
exist **along the run**, not at an arbitrary state, so an obligation written
`∀ c s, …` cannot be met. Compare `CloseoutVerSide.VerRun` and
`CloseoutMarksFree.MarksRun`, and the refutation
`ConsumeAvailRefute.hav_false` of the same mistake made with `∀ st`. -/
structure LandingObligationsAt (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  bg : ∀ t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → ScanPositionPayloadWithChainLedger w t
  matchLand : ∀ (s' t : GalilVM) (o b : Bool), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    (galilFrameS (PofC centre place entry w) q first).matched s' →
    (galilFrameS (PofC centre place entry w) q first).matchedPlace c.replaying s' t →
    ScanNR ⟨{c with clock := 2048, output := o, replaying := c.replaying && b}, t⟩ →
    t.chain ≠ ChainVM.idle → GalilScaffoldChainVerifier.canRight t.right →
    ScanPositionPayloadWithChainLedger w t
  entryLand : ∀ s' t : GalilVM, c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
    shiftGuardVM s' → beginShiftVM' s' t →
    GalilScaffoldChainVerifier.canRight t.right → ShiftPhaseChainLedger t
  shiftDone : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ChainPositionInvariantWithShiftPhase w c s → s.chain ≠ ChainVM.idle →
    GalilScaffoldChainVerifier.canRight s.right ∧
      ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
        value s.radius ≤ (rad : ℤ)

/-- The global hypotheses restrict to any state. -/
theorem landingObligationsAt_of_globalHypotheses {w : List (Fin 2)}
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w) (c : Control) (s : GalilVM) :
    LandingObligationsAt centre place entry q first w c s :=
  ⟨fun t => hbg c s t, fun s' t o b => hmatch c s s' t o b,
    fun s' t => hentry c s s' t, hsd c s⟩

/-- **One tick of `ChainPositionInvariantWithShiftPhase`, from the state-local bundle.**  `shift_one`
closes outright; `LandingObligationsAt` covers the three scan landings and the shift entry. -/
theorem chainPosInv2_tick_of_landingObligationsAt {w : List (Fin 2)}
    {x y : State GalilVM} (hB : LandingObligationsAt centre place entry q first w x.ctl x.vm)
    (hCanRightAtTarget : y.ctl.mode = Mode.scan ∨ y.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight y.vm.right)
    (hx : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    ChainPositionInvariantWithShiftPhase w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  have hcoup : Coupled' c' t :=
    coupled'_tick (onLetterVM w) leftFirstVM centre place entry q first 2048 hx.coupled h
  refine ⟨hcoup, ?_, ?_⟩
  · -- the scan payload
    cases h
    case init =>
      rename_i hm hi
      obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
      exact fun _ hni => absurd hch hni
    case scan_wait =>
      rename_i hm hav hb
      exact fun hs hni => hB.bg t hm hx hb hs hni
    case scan_count =>
      rename_i hm hc hav hb
      exact fun hs hni => hB.bg t hm hx hb ⟨hm, hs.2⟩ hni
    case scan_match =>
      rename_i s' o hmt hm hc hcmp hav hpl ho
      exact fun hs hni =>
        hB.matchLand s' t o _ hm hx hcmp hmt hpl hs hni (hCanRightAtTarget (Or.inl hs.1))
    case shift_done =>
      rename_i o hm hp ho
      exact fun _ hni =>
        ⟨(hB.shiftDone hm hp hx hni).1, (hB.shiftDone hm hp hx hni).2, hx.shiftPay hm⟩
    case replayStart =>
      rename_i o hm ho ho' hi
      obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hi
      exact fun _ hni => absurd hch hni
    case restart =>
      rename_i hm hb
      obtain ⟨w', -, -, -, -, ht⟩ : restartVM entry s t := hb
      subst ht
      exact fun _ hni => absurd rfl hni
    all_goals
      exact fun h1 _ => by
        obtain ⟨h2, -⟩ := h1
        simp_all
  · -- the shift-mode ledger
    cases h
    case scan_shift =>
      rename_i s' hmt hg hm hc hr hcmp hav hb
      exact fun hModeShift =>
        hB.entryLand s' t hm hx hcmp hmt hg hb (hCanRightAtTarget (Or.inr hModeShift))
    case shift_one =>
      rename_i hm hp hi
      obtain ⟨-, -, -, wv, hw, hv⟩ := hi.1
      have ht := hi.2
      rw [hv] at ht
      subst ht
      intro _
      show ChainPositionLedger _ (position _)
      -- `right` is not a component of `shiftLens`, so the right head is fixed
      have hrr : (shiftLens.set s
          ⟨shiftTick (shiftLens.get s).shift, ChainVM.watch (chainShiftOne wv),
            inc (inc (shiftLens.get s).cycle)⟩).right = s.right := rfl
      have hcc : (shiftLens.set s
          ⟨shiftTick (shiftLens.get s).shift, ChainVM.watch (chainShiftOne wv),
            inc (inc (shiftLens.get s).cycle)⟩).chain = ChainVM.watch (chainShiftOne wv) := rfl
      rw [hrr, hcc]
      have hP : ChainPositionLedger s.chain (position s.right) := hx.shiftPay hm
      obtain ⟨hcn, hsn, hpn⟩ := hP.watch wv hw
      refine ⟨fun wch hw' => ?_, (fun _ _ _ _ _ hb => by cases hb),
        (fun _ _ _ _ _ _ _ hcp => by cases hcp)⟩
      cases hw'
      -- `chainShiftOne` touches only `distance`/`boundary`/`last`/`margin`
      exact ⟨hcn, hsn, hpn⟩
    all_goals
      exact fun h1 => by simp_all

/-- **One tick of `ChainPositionInvariantWithShiftPhase`** (the global form, unchanged).  Kept so that
every existing caller works; new code should use `chainPosInv2_tick_of_landingObligationsAt`. -/
theorem chainPosInv2_tick {w : List (Fin 2)}
    (hbg : H_BackgroundLandingChainLedger centre place entry q first w) (hmatch : H_MatchLandingChainLedger centre place entry q first w)
    (hentry : H_ShiftEntryChainLedger centre place entry q first w)
    (hsd : H_ShiftExitRadiusLedger centre place entry q first w)
    {x y : State GalilVM}
    (hCanRightAtTarget : y.ctl.mode = Mode.scan ∨ y.ctl.mode = Mode.shift →
      GalilScaffoldChainVerifier.canRight y.vm.right)
    (hx : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    ChainPositionInvariantWithShiftPhase w y.ctl y.vm :=
  chainPosInv2_tick_of_landingObligationsAt centre place entry q first
    (landingObligationsAt_of_globalHypotheses centre place entry q first hbg hmatch hentry hsd _ _)
    hCanRightAtTarget hx h

#print axioms landingObligationsAt_of_globalHypotheses
#print axioms chainPosInv2_tick_of_landingObligationsAt
#print axioms chainPosInv2_tick

/-! ## 5. `WatchShiftS` with neither `H_FourSemiperiodsLeDistance` nor a lookahead -/

/-- **`WatchShiftS` from `ChainPositionInvariantWithShiftPhase`.**  `4h ≤ distance` is Run40's
`four_of_freshC` / `four_of_other'`; `distance ≤ 2·rad` is the guard's zero lag
plus `Coupled'.sum` plus `radLe`; and the **verifier pair at the target** is
`chainPos_step` applied to the source ledger — an unmatched comparison's chain
effect is a plain `ChainStep`, so no lookahead is needed.  The only input is
`ConsumeAvail` at the source chain. -/
theorem watchShiftS_of_chainPosInv2 {w : List (Fin 2)} {x : State GalilVM}
    (h : ChainPositionInvariantWithShiftPhase w x.ctl x.vm) (hav : ConsumeAvail x.vm.chain) :
    WatchShiftS centre place entry q first w x := by
  intro hs hni s'' hcmp hmt hg wch hch
  have hs' : ScanNR ⟨x.ctl, x.vm⟩ := hs
  have P := h.payload hs' hni
  -- the chain of the (unmatched) target is one plain `ChainStep` away
  have hstep : ChainStep x.vm.chain s''.chain := by
    obtain ⟨vs, vq, a, -, -, hiff, -, hchn, hteq⟩ :
      compareFound (PofC centre place entry w) q first x.vm s'' := hcmp
    have ha : a = false := by
      cases a with
      | false => rfl
      | true =>
        rw [if_pos rfl] at hteq
        subst hteq
        refine absurd ?_ hmt
        show GalilScaffoldInputHead.read (afterBirth _ (afterCompare x.vm vs vq)).left
          = GalilScaffoldInputHead.read (afterBirth _ (afterCompare x.vm vs vq)).right
        rw [afterBirth_left, afterBirth_right]
        exact hiff.1 rfl
    subst ha
    have hcn : s''.chain = vs.chain := by rw [hteq, afterBirth_chain]; rfl
    rw [hcn]
    rcases hchn with ⟨-, ht⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
    · obtain ⟨y, hst, ho⟩ := ht
      simp only [Bool.false_eq_true, ↓reduceIte] at ho
      rw [ho]
      exact hst
    · exact absurd hi hni
    · exact absurd hi hni
  have hver := (chainPos_step P.chainPos hav hstep).watch wch hch
  -- the two numeric halves, exactly as in Run40
  obtain ⟨-, -, -, -, hmis⟩ :=
    compare'_inv (onLetterVM w) leftFirstVM centre place entry q first h.coupled hs.1 hcmp
  obtain ⟨-, -, hsum, hwk⟩ := hmis hmt
  have hg' := hg
  obtain ⟨w1, hw1, hz, hph, hbr, -, -⟩ := hg'
  have hch' := hch
  rw [hw1] at hch'
  injection hch' with hwe
  rw [hwe] at hw1 hz hph hbr
  rw [hw1] at hsum hwk
  have hd : value wch.machine.control.distance + value wch.lag = value x.vm.radius := hsum hbr
  rw [value_zero_of_zero hz] at hd
  refine ⟨P.canR, ?_, ?_, hver.1, hver.2.1⟩
  · rcases hwk wch rfl hbr with ⟨-, hf⟩ | hO
    · exact four_of_freshC hph hf
    · exact four_of_other' centre place entry q first h.coupled hs hcmp hmt hg hch hO
  · intro rad hsc
    have := P.radLe rad hsc
    omega

end Pos

#print axioms chainPos_idle
#print axioms chainPosInv2_of_idle
#print axioms watchShiftS_of_chainPosInv2

end PalPeg.CloseoutPackRun41
