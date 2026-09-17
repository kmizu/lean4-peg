import PalPeg.PackedRun
import PalPeg.CloseoutLPack4
import PalPeg.GalilFinalAssembly4

/-!
# `CloseoutLPack5`: the pack travels with the run, not with the tick

`CloseoutLPack4` reduced `CloseoutLPack.H_lpack` to `LTickLeaves4` and left three
fields that provably do **not** fall out of one tick: `scanMargin` (the origin
corner is the machine's stopping rule), `mismatchMinv` (which of
`Leftmost … (position R + 1)` and `minv_after_fallback` applies is decided by the
entry guard, i.e. by the round) and `shiftDoneScan` (the new centre's palindrome
radius, a statement about the shift round).

This file changes the *carrier* instead of pushing on the tick.  The trace the
final theorem actually uses is not an arbitrary `PreTrace`: it is the one
`GalilFinalAssembly4.checkpoints_cost2_upto1` builds out of the oracle, segment
by segment.  Along that construction the pack is a **run**-level datum, and the
three stubborn fields are exactly the run-level facts that already exist:

* the landings are `InvLPS` states (`GalilInvPlus3.invLPS_of_landed`,
  `invLPS_of_inv`, `invLPS_of_boot`), whose `Inv` half is `MInv` together with
  `ScanInvariant`;
* a scan interval keeps the centre invariant (`GalilLiveCentreReplay.minv_watchSegE`,
  replays included);
* a fallback lands through `GalilLiveCentreFallback.minv_after_fallback` out of
  `fallback_replayStart_All`;
* a found route lands restarted (`FoundExit.landed`), where `L = C = R`, so the
  origin corner is `MInv` plus `Live` and nothing else;
* a shift exit is `GalilLiveCentreShift.leftmost_shift` /
  `live_shift_of_palAt` at the landing of `FoundRouteMC3.landed`.

So this file:

* defines `IPack` — `CloseoutLPack.LPack` **plus** the four shift-entry
  side-conditions of `CloseoutLPack4` (`H_shiftMode`, `H_shiftMove`,
  `H_shiftGuardPlaces`, `H_shiftCoupled`) and `CloseoutLPack.H_shiftCanRight`,
  all of which are *state*-local once the trace is fixed;
* defines `StepsI`, a run that carries `IPack` at **every** tick, with the
  concatenation calculus it needs (`pack_concat`, `stepsI_trans`);
* re-runs the checkpoint recursion over `StepsI` (`ReachAtI`, `CycleOutI`,
  `CycleOracleI`, `reachI_from_invLPC`, `checkpoints_costI_upto1`) — the proof is
  `GalilFinalAssembly4.checkpoints_cost2_upto1` with `StepsAll`/`stepsAll_fn`
  replaced by `StepsI`, so the pack is threaded through the two concatenations;
* defines `PreTraceI` (`PreTraceB` plus `IPack` at every tick) and proves
  `preTraceI_exists`;
* proves `needI'_le` and `pal_in_peg_final5`: the final theorem with
  `H_needLB'` **gone** — the need bound is now supplied by the trace the
  construction produces.

## What is still NAMED, and why

* `H_bootI` — the boot prefix as a `StepsI`: the one `init` tick of
  `GalilFinalAssembly4.invLPC_init` with `IPack` at its two states.  `LPack`
  at the boot state is `CloseoutLPack.lpack_boot` (vacuous, `init` mode) and at
  the landing it is `MInv` from `minv_of_leftmost` plus the radius-`0`
  `ScanInvariant`; what is *not* free is the shift-entry half at those two
  states, which is why this is named rather than proved.
* `H_oracleI` — `GalilOracleMC2.CycleOracleMC2C` with `StepsAll` replaced by
  `StepsI`: each exit run carries the pack at every tick.  This is the real
  content moved here from the tick layer, and it is where the five run-level
  routes above have to be discharged.
* `H_trailI` — the **pointwise** form of the chain
  `CloseoutLPack4.h_trailF_lpack4 → … → GalilTrailProof.H_trailF`: from the pack
  at every state of *one* trace, the trailing invariant at every state of that
  trace.  Every link of the existing chain is stated `∀ st Tc, PreTrace → …`,
  so it cannot be instantiated at a single chosen trace; re-deriving it
  pointwise is the one remaining bridge, and it is the reason `pal_in_peg_final5`
  has three hypotheses rather than two.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLPack5

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilTrailProof PalPeg.GalilFinalAssembly
open PalPeg.CloseoutRadPack PalPeg.CloseoutRadPack2 PalPeg.CloseoutRadPack3
open PalPeg.CloseoutRadPack4 PalPeg.CloseoutLPack PalPeg.CloseoutLPack2
open PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4
open PalPeg.GalilRunSkeleton PalPeg.GalilCheckpoints PalPeg.GalilTraceCost
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleLocal PalPeg.GalilLexMeasure
open PalPeg.GalilInvPlus PalPeg.GalilInvPlus2 PalPeg.GalilOracleMC PalPeg.GalilOracleMC2
open PalPeg.GalilLookRefined PalPeg.GalilFinalBaseNeed PalPeg.GalilFinalAssembly2
open PalPeg.GalilLedgerQ64 PalPeg.GalilLedgerAssembly PalPeg.GalilIntervalCost
open PalPeg.GalilLatchTracking PalPeg.GalilArriveChain PalPeg.GalilTickArrive
open PalPeg.GalilTruncTick
open PalPeg.GalilFinalAssembly4
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 0. The guarded centre invariant and the guarded left-head pack

`CloseoutPackRun4.minv_false_at_mismatch` refutes the unguarded third field of
`CloseoutLPack.LPack` (`c.mode ≠ Mode.init → MInv w c s`) along a real run: a
mismatching comparison kills the current centre, and the whole fallback phase
runs with no live centre at all.  `MInvG` demands the centre invariant **only in
scan mode**, and `LPackG` is `LPack` with that weakened field.  The run payload
`IPack` below carries `LPackG`; §2 of `CloseoutPackRun5` shows the weakening is
free, because the only consumer of the payload in the whole chain is
`H_trailI`, which reads `lrep` and `scanInv` and never `minv`.
-/

/-- **The guarded centre invariant.** -/
def MInvG (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → MInv w c s

theorem minvG_of_minv {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : MInv w c s) : MInvG w c s := fun _ => h

/-- **The guarded left-head pack**: `CloseoutLPack.LPack` with its third field
guarded by `scan`. -/
structure LPackG (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  lrep : c.mode ≠ Mode.init →
    GalilScaffoldInputTrace.Represents s.left.head w ∧ s.left.head.focus ≠ none
  scanInv : c.mode = Mode.scan → c.replaying = false →
    ∃ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right
  minvG : MInvG w c s

/-- **`LPackG` is a weakening of `LPack`.** -/
theorem lpackG_of_lpack {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPack w c s) : LPackG w c s :=
  ⟨h.lrep, h.scanInv, fun hm => h.minv (by rw [hm]; decide)⟩

/-- **`LeftLive` is read off the weakened pack**: it only ever used `lrep`. -/
theorem leftLive_of_lpackG {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : LPackG w c s) : PalPeg.GalilTrailSane.LeftLive c s := by
  refine ⟨fun hm _ => ?_, fun hm => ?_⟩
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp
  · obtain ⟨hh, hp⟩ := h.lrep (by rw [hm]; decide)
    exact pos_of_rep hh hp

/-- The boot state, where every field is vacuous. -/
theorem lpackG_boot (w : List (Fin 2)) : LPackG w (boot w).ctl (boot w).vm :=
  lpackG_of_lpack (lpack_boot w)

#print axioms lpackG_of_lpack
#print axioms leftLive_of_lpackG
#print axioms lpackG_boot

/-! ## 1. The state-local shift-entry conditions -/

section Pack
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The four shift-entry residuals of `CloseoutLPack4`, at one state.**  Once
the trace is fixed, `H_shiftMode`, `H_shiftMove`, `H_shiftGuardPlaces`,
`H_shiftCoupled` and `CloseoutLPack.H_shiftCanRight` are all conditions on the
single state `x` and the comparison/entry pair out of it. -/
structure ShiftLocal (w : List (Fin 2)) (x : State GalilVM) : Prop where
  /-- `H_shiftMode`: the controller is in a non-replaying scan. -/
  mode : ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' → x.ctl.mode = Mode.scan ∧ x.ctl.replaying = false
  /-- `H_shiftMove`: the right head can move. -/
  move : ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' → GalilScaffoldChainVerifier.canRight x.vm.right
  /-- `H_shiftGuardPlaces`: the guard's place count `4h ≤ distance`. -/
  guard : ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
  /-- `H_shiftCoupled`: the chain/scan coupling `distance ≤ 2·rad`. -/
  coupled : ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      ∀ rad : ℕ, ScanInvariant w (position x.vm.center) rad x.vm.left x.vm.right →
        value wch.machine.control.distance ≤ 2 * (rad : ℤ)
  /-- `H_shiftCanRight`: the watching chain's own verifier can move and is sane. -/
  ver : ∀ s'' t'' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare x.vm s'' →
    beginShiftVM' s'' t'' →
    ∀ wch : GalilScaffoldChainWatch.State, s''.chain = .watch wch →
      GalilScaffoldChainVerifier.canRight wch.machine.verifier ∧
        GalilFrontMono.Sane wch.machine.verifier

/-- **The run-level pack.**  `CloseoutLPack.LPack` together with the
shift-entry conditions at the same state. -/
structure IPack (w : List (Fin 2)) (x : State GalilVM) : Prop where
  pack : LPackG w x.ctl x.vm
  shift : ShiftLocal centre place entry q first w x

end Pack

/-! ## 2. Runs that carry the pack -/

section Runs
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **A packed run**: a concrete `Trace` from `x` to `y` of length `k`, every
state of which satisfies `IPack`.  This is `StepsAll` in function form with the
pack added; `GalilCheckpoints.stepsAll_fn` is the reason the function form costs
nothing. -/
def StepsI (w : List (Fin 2)) (k : ℕ) (x y : State GalilVM) : Prop :=
  PackedRun (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w)
    (IPack centre place entry q first w) k x y

end Runs

/-- **The pack transports across a concatenation.** -/
theorem pack_concat {Pk : State GalilVM → Prop} {f g : ℕ → State GalilVM} {e k : ℕ}
    (hfg : f e = g 0) (hf : ∀ i, i ≤ e → Pk (f i)) (hg : ∀ i, i ≤ k → Pk (g i)) :
    ∀ i, i ≤ e + k → Pk (concat f g e i) := by
  intro i hi
  by_cases hie : i ≤ e
  · rw [concat_le f g hie]; exact hf i hie
  · have hsplit : i = e + (i - e) := by omega
    rw [hsplit, concat_end f g hfg]
    exact hg (i - e) (by omega)

section Trans
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- Packed runs compose. -/
theorem stepsI_trans {w : List (Fin 2)} {k1 k2 : ℕ} {x y z : State GalilVM}
    (h1 : StepsI centre place entry q first w k1 x y)
    (h2 : StepsI centre place entry q first w k2 y z) :
    StepsI centre place entry q first w (k1 + k2) x z :=
  PalPeg.PackedRun.trans h1 h2

end Trans

#print axioms pack_concat
#print axioms stepsI_trans

/-! ## 3. The checkpoint recursion over packed runs -/

section Recursion
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- `GalilOracleMC2.ReachAtC2` over packed runs. -/
def ReachAtI (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ∃ (y : State GalilVM) (k : ℕ) (L : List Piece),
    StepsI centre place entry q first w k ⟨c, r⟩ y ∧
    CostedRun r y.vm k L ∧
    PalPeg.GalilReportPrefix.ReportPointAt w m y ∧
    Refreshed (PofC centre place entry w) q first y ∧
    (m < w.length → ∃ (c' : Control) (r' : GalilVM) (k' : ℕ) (L' : List Piece),
      StepsI centre place entry q first w k' y ⟨c', r'⟩ ∧
      CostedRun y.vm r' k' L' ∧
      InvLPC w c' r' ∧ position r'.right ≤ 2 * (m+1) - 1)

/-- `GalilOracleMC2.CycleOutMC2C` over packed runs. -/
def CycleOutI (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) : Prop :=
  ReachAtI centre place entry q first w m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsI centre place entry q first w k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLPC w cT sT ∧ mu w sT < mu w r ∧
      position sT.right ≤ 2 * m - 1

/-- `GalilOracleMC2.CycleOracleMC2C` over packed runs. -/
def CycleOracleI (w : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ w.length → InvLPC w c r →
    position r.right ≤ 2 * m - 1 → CycleOutI centre place entry q first w m c r

/-- `GalilOracleMC2.reachC2_fuel` over packed runs. -/
theorem reachI_fuel (w : List (Fin 2)) (hor : CycleOracleI centre place entry q first w)
    (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ w.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu w r ≤ n → InvLPC w c r →
      position r.right ≤ 2 * m - 1 → ReachAtI centre place entry q first w m c r := by
  intro n
  induction n with
  | zero =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, _, _, _, hlt, _⟩
    · exact hdone
    · omega
  | succ n ih =>
    intro c r hn hI hp
    rcases hor m c r hm1 hmle hI hp with hdone | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hpT⟩
    · exact hdone
    · obtain ⟨y, k', L', hst', hcr', hrp, hfr, hcont⟩ := ih cT sT (by omega) hIT hpT
      exact ⟨y, k + k', L ++ L',
        stepsI_trans centre place entry q first hst hst',
        costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachI_from_invLPC (w : List (Fin 2)) (hor : CycleOracleI centre place entry q first w)
    {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ w.length) {c : Control} {r : GalilVM}
    (hI : InvLPC w c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtI centre place entry q first w m c r :=
  reachI_fuel centre place entry q first w hor m hm1 hmle _ c r le_rfl hI hp

end Recursion

#print axioms reachI_fuel
#print axioms reachI_from_invLPC

/-! ## 4. The construction, with the pack threaded through -/

section Construct
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`GalilFinalAssembly4.checkpoints_cost2_upto1` over packed runs.**  Verbatim,
with `StepsAll`/`stepsAll_fn` replaced by `StepsI`, and one extra conclusion:
the pack holds at *every* tick of the constructed trace.  The two places where
the trace grows are the two concatenations, and `pack_concat` carries the pack
across both. -/
theorem checkpoints_costI_upto1 (w : List (Fin 2))
    (hor : CycleOracleI centre place entry q first w)
    {x0 : State GalilVM} {k0 : ℕ} {c : Control} {r : GalilVM}
    (hpre : StepsI centre place entry q first w k0 x0 ⟨c, r⟩)
    (hI : InvLPC w c r) (hpos : position r.right = 1) :
    ∀ M, M ≤ w.length →
    ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) (e : ℕ),
      st 0 = x0 ∧ Tc 0 = 0 ∧
      Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st e ∧
      (∀ m, m < M → Tc m ≤ Tc (m+1)) ∧ Tc M ≤ e ∧
      (∀ m, 1 ≤ m → m ≤ M →
        PalPeg.GalilReportPrefix.ReportPointAt w m (st (Tc m)) ∧
        Refreshed (PofC centre place entry w) q first (st (Tc m))) ∧
      (∀ m, 1 ≤ m → m < M →
        Tc (m+1) - Tc m ≤ alpha' 2048 * (Cw w (m+1) - Cw w m) + beta' 2048) ∧
      (M < w.length → ∃ (c' : Control) (r' : GalilVM),
        st e = ⟨c', r'⟩ ∧ InvLPC w c' r' ∧ position r'.right ≤ 2 * (M+1) - 1 ∧
        (1 ≤ M → ∃ L : List Piece, CostedRun (st (Tc M)).vm r' (e - Tc M) L)) ∧
      (M = 0 → e = k0 ∧ st e = ⟨c, r⟩) ∧
      (1 ≤ M → Tc 1 = k0) ∧
      (∀ i, i ≤ e → IPack centre place entry q first w (st i)) := by
  intro M
  induction M with
  | zero =>
    intro _
    obtain ⟨g, hg0, hgn, htr, hgp⟩ := hpre
    refine ⟨g, fun _ => 0, k0, hg0, rfl, htr, fun m hm => absurd hm (Nat.not_lt_zero _),
      Nat.zero_le _, fun m h1 h2 => absurd h1 (by omega), fun m h1 h2 => absurd h2 (by omega),
      fun _ => ⟨c, r, hgn, hI, by omega, fun h => absurd h (by omega)⟩,
      fun _ => ⟨rfl, hgn⟩, fun h => absurd h (by omega), hgp⟩
  | succ M ih =>
    intro hM
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, hres, hzero, hone, hpk⟩ :=
      ih (by omega)
    obtain ⟨c', r', hste, hI', hp', hpend⟩ := hres (by omega)
    obtain ⟨y, k, L2, hrun, hcr, hrp, hfr, hcont⟩ :=
      reachI_from_invLPC centre place entry q first w hor (m := M+1) (by omega) hM hI' hp'
    have hk0 : M = 0 → k = 0 ∧ e = k0 := by
      intro hM0
      subst hM0
      obtain ⟨he, hse⟩ := hzero rfl
      have hrr : r' = r := by
        have := hste.symm.trans hse
        exact (GalilScaffoldTop.State.mk.injEq _ _ _ _ ▸ this).2
      subst hrr
      have hyp := hrp.atPlace
      exact ⟨costedRun_zero hcr (by rw [hyp, hpos]), he⟩
    obtain ⟨g1, hg10, hg1k, htr1, hpg1⟩ := hrun
    have hj1 : st e = g1 0 := by rw [hste, hg10]
    set st1 := concat st g1 e with hst1
    have htr1' : Trace (galilFrameS (PofC centre place entry w) q first) 2048
        (SoundScanNR w) st1 (e + k) :=
      trace_concat htr htr1 hj1
    have hst1y : st1 (e + k) = y := by rw [hst1, concat_end st g1 hj1, hg1k]
    have hpk1 : ∀ i, i ≤ e + k → IPack centre place entry q first w (st1 i) :=
      pack_concat hj1 hpk hpg1
    obtain ⟨st2, e2, htr2, hagree, hle2, hres2, hpk2⟩ :
        ∃ (st2 : ℕ → State GalilVM) (e2 : ℕ),
          Trace (galilFrameS (PofC centre place entry w) q first) 2048 (SoundScanNR w) st2 e2 ∧
          (∀ i, i ≤ e + k → st2 i = st1 i) ∧ e + k ≤ e2 ∧
          (M + 1 < w.length → ∃ (c'' : Control) (r'' : GalilVM),
            st2 e2 = ⟨c'', r''⟩ ∧ InvLPC w c'' r'' ∧
            position r''.right ≤ 2 * (M+1+1) - 1 ∧
            ∃ L : List Piece, CostedRun y.vm r'' (e2 - (e + k)) L) ∧
          (∀ i, i ≤ e2 → IPack centre place entry q first w (st2 i)) := by
      by_cases hlt : M + 1 < w.length
      · obtain ⟨c'', r'', k', L', hrun2, hcr2, hI2, hp2⟩ := hcont hlt
        obtain ⟨g2, hg20, hg2k, htr2, hpg2⟩ := hrun2
        have hj2 : st1 (e + k) = g2 0 := by rw [hst1y, hg20]
        refine ⟨concat st1 g2 (e + k), e + k + k', trace_concat htr1' htr2 hj2,
          fun i hi => concat_le st1 g2 hi, by omega, fun _ => ⟨c'', r'', ?_, hI2, hp2, L', ?_⟩,
          pack_concat hj2 hpk1 hpg2⟩
        · rw [concat_end st1 g2 hj2, hg2k]
        · rw [show e + k + k' - (e + k) = k' by omega]; exact hcr2
      · exact ⟨st1, e + k, htr1', fun _ _ => rfl, le_rfl, fun h => absurd h hlt, hpk1⟩
    have hTcle : ∀ m, m ≤ M → Tc m ≤ e := fun m hm =>
      le_trans (mono_of_step Tc M hmono m M hm le_rfl) hTcM
    have hst2old : ∀ m, m ≤ M → st2 (Tc m) = st (Tc m) := by
      intro m hm
      rw [hagree _ (by have := hTcle m hm; omega), hst1, concat_le st g1 (hTcle m hm)]
    have hst2y : st2 (e + k) = y := by rw [hagree _ le_rfl, hst1y]
    refine ⟨st2, fun m => if m ≤ M then Tc m else e + k, e2, ?_, ?_, htr2, ?_, ?_, ?_, ?_, ?_,
      fun h => absurd h (by omega), ?_, hpk2⟩
    · rw [hagree 0 (by omega), hst1, concat_le st g1 (Nat.zero_le _), hst0]
    · simp [hTc0]
    · intro m hm
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]; exact hmono m (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        exact le_trans hTcM (Nat.le_add_right _ _)
    · simp only [show ¬ M + 1 ≤ M by omega, if_false]; exact hle2
    · intro m h1 h2
      by_cases hm' : m ≤ M
      · simp only [hm', if_true]
        rw [hst2old m hm']
        exact hchk m h1 hm'
      · have hmM : m = M + 1 := by omega
        subst hmM
        simp only [hm', if_false]
        rw [hst2y]
        exact ⟨hrp, hfr⟩
    · intro m h1 h2
      by_cases hm' : m + 1 ≤ M
      · simp only [hm', show m ≤ M by omega, if_true]
        exact hcost m h1 (by omega)
      · have hmM : m = M := by omega
        subst hmM
        simp only [le_refl, if_true, hm', if_false]
        obtain ⟨L1, hcr1⟩ := hpend h1
        have hall := costedRun_trans hcr1 hcr
        have hTm := hTcle m le_rfl
        obtain ⟨hrp0, hfr0⟩ := hchk m h1 le_rfl
        have hc' : CostedRun (st (Tc m)).vm y.vm (e + k - Tc m) (L1 ++ L2) := by
          rw [show e + k - Tc m = e - Tc m + k by omega]; exact hall
        exact interval_cost_of_costedRun h1 hrp0 hfr0 hrp hfr hc'
    · intro hlt
      obtain ⟨c'', r'', h1, h2, h3, L, h4⟩ := hres2 hlt
      refine ⟨c'', r'', h1, h2, h3, fun _ => ⟨L, ?_⟩⟩
      simp only [show ¬ M + 1 ≤ M by omega, if_false]
      rw [hst2y]
      exact h4
    · intro _
      by_cases hM0 : M = 0
      · subst hM0
        obtain ⟨hk, he⟩ := hk0 rfl
        simp only [show ¬ (1 ≤ 0) by omega, if_false]
        omega
      · simp only [show 1 ≤ M by omega, if_true]
        exact hone (by omega)

end Construct

#print axioms checkpoints_costI_upto1

/-! ## 5. `PreTraceI` -/

section Pre
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The pre-loaded trace with the pack.**  `GalilFinalBaseNeed.PreTraceB`
together with `IPack` at every one of its ticks. -/
structure PreTraceI (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop where
  base : PreTraceB centre place entry q first w st Tc
  packs : ∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)

/-- **(NAMED) the boot prefix as a packed run.**  `GalilFinalAssembly4.invLPC_init`
delivers the `init` tick with `InvLPC` and the right head on place `1`; what has
to be added is `IPack` at the boot state (where `LPack` is
`CloseoutLPack.lpack_boot`, vacuous in `init` mode) and at the landing (where
`MInv` is `minv_of_leftmost` and the scan invariant has radius `0`).  The
shift-entry half at those two states is not free, which is why this is named. -/
def H_bootI : Prop :=
  ∀ (a : Fin 2) (rest : List (Fin 2)),
    ∃ (c1 : Control) (t : GalilVM),
      StepsI centre place entry q first (a :: rest) 1
        ⟨GalilScaffoldController.initial 2048, GalilBootVM.initVM0 (a :: rest)⟩ ⟨c1, t⟩ ∧
      InvLPC (a :: rest) c1 t ∧ position t.right = 1

/-- **(NAMED) the packed cycle oracle.**  `GalilFinalAssembly4.H_oracle2` with
every exit run carrying `IPack` at every tick.  The five run-level routes that
`CloseoutLPack4` could not reach tick-locally (`invLPS_of_landed` at the
landings, `minv_watchSegE` along a scan interval, `minv_after_fallback` out of
`fallback_replayStart_All`, `FoundExit.landed` on a found route, `leftmost_shift`
at a shift exit) are exactly what has to be discharged here. -/
def H_oracleI : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → CycleOracleI centre place entry q first w

/-- **`GalilFinalAssembly4.preTraceB2_exists` with the pack.** -/
theorem preTraceI_exists (hboot : H_bootI centre place entry q first)
    (hor : H_oracleI centre place entry q first) (w : List (Fin 2)) (hw : 0 < w.length) :
    ∃ st Tc, PreTraceI centre place entry q first w st Tc := by
  rcases w with _ | ⟨a, rest⟩
  · simp at hw
  · obtain ⟨c1, t, hst, hI, hpos⟩ := hboot a rest
    obtain ⟨st, Tc, e, hst0, hTc0, htr, hmono, hTcM, hchk, hcost, -, -, hone, hpk⟩ :=
      checkpoints_costI_upto1 centre place entry q first (a :: rest) (hor (a :: rest) hw)
        hst hI hpos (a :: rest).length le_rfl
    refine ⟨st, Tc, ⟨⟨⟨hst0, hTc0, trace_le htr hTcM, mono_of_step Tc _ hmono, ?_, hcost⟩,
      hone (by simp)⟩, fun i hi => hpk i (le_trans hi hTcM)⟩⟩
    intro m h1 h2
    exact ledgerAt_of_prefix (hchk m h1 h2).1 (hchk m h1 h2).2

end Pre

#print axioms preTraceI_exists

/-! ## 6. The need bound on the constructed trace -/

section Need
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the pointwise trailing invariant from the pack.**  This is the
chain `CloseoutLPack4.h_trailF_lpack4 → CloseoutLPack.h_trailF_final → … →
GalilTrailProof.H_trailF`, restated for *one* trace.  Every link of that chain is
of the shape `∀ st Tc, PreTrace → …`, so it cannot be instantiated at a chosen
trace; this is the pointwise counterpart. -/
def H_trailI : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i, i ≤ Tc w.length → IPack centre place entry q first w (st i)) →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i)

/-- **The trailing invariant on a `PreTraceI`.** -/
theorem trailF_of_preTraceI (h : H_trailI centre place entry q first) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceI centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → TrailF w m (st i) :=
  h w hw st Tc hP.base.pre hP.packs

/-- **The refined need bound on a `PreTraceI`**, via
`GalilTrailProof.needL'_le_of_trailF`. -/
theorem needI'_le (h : H_trailI centre place entry q first) {w : List (Fin 2)}
    (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTraceI centre place entry q first w st Tc) :
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → needL' w st i ≤ m + 1 :=
  fun m hm i hi =>
    needL'_le_of_trailF w st m i (trailF_of_preTraceI centre place entry q first h hw hP m hm i hi)

end Need

#print axioms trailF_of_preTraceI
#print axioms needI'_le

/-! ## 7. The final theorem: `H_needLB'` gone -/

/-- (C) Realization over the refined throttled run of a `PreTraceI`. -/
def H_realizeLI' (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∃ (Q' Γ' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (_ : Fintype Γ') (_ : DecidableEq Γ')
    (t K : ℕ) (L : PalPeg.Local.LocalStep (Fin 2) Q' Γ' t K) (blank : Γ') (initQ : Q')
    (outQ : Q' → Bool) (n : ℕ) (htape : 0 < t) (hn : 0 < n),
    ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTraceI centre place entry q first w st Tc →
      ((L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn).SAccepts w ↔
        LatchTrue (PofC centre place entry w) q first w (stLG' τF w st (Tc w.length))
          ((w.length + 1) * τF))

/-- **`PAL ∈ PEG` with the need bound supplied by the construction.**
`GalilLookRefined.pal_in_peg_final2'_gen` over `PreTraceI` instead of
`PreTrace`: the trace is the one `preTraceI_exists` builds, so `H_needLB'` (and
`H_base`, via `base_of_preTraceB`) are discharged rather than assumed.  What is
left is the packed oracle, the packed boot prefix, the pointwise trail bridge,
and (C). -/
theorem pal_in_peg_final5 (entry q : ℕ) (first : Fin 9)
    (hboot : H_bootI centreC placeC entry q first)
    (hA : H_oracleI centreC placeC entry q first)
    (hT : H_trailI centreC placeC entry q first)
    (hC : H_realizeLI' centreC placeC entry q first) :
    RecognizedByTotalPEG PAL := by
  classical
  obtain ⟨Q', Γ', iQ, dQ, iΓ, dΓ, t, K, L, blank, initQ, outQ, n, htape, hn, hreal⟩ := hC
  have key : ∀ w : List (Fin 2), ∃ (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      0 < w.length → PreTraceI centreC placeC entry q first w st Tc := by
    intro w
    by_cases hw : 0 < w.length
    · obtain ⟨st, Tc, h⟩ := preTraceI_exists centreC placeC entry q first hboot hA w hw
      exact ⟨st, Tc, fun _ => h⟩
    · exact ⟨fun _ => boot w, fun _ => 0, fun h => absurd h hw⟩
  choose stP TcP hP using key
  let M := L.realize blank initQ (GalilEmptyWord.accept' initQ outQ) n htape hn
  have hpre : ∀ w : List (Fin 2), 0 < w.length → PreloadL' w (stP w) (TcP w) := by
    intro w hw
    have h := hP w hw
    exact ⟨h.base.pre.tc0, fun m hm => h.base.pre.mono m (m+1) (by omega) hm,
      needL'_boot w (stP w) h.base.pre.start,
      needLe_of_pointwise' w (stP w) (TcP w) (needI'_le centreC placeC entry q first hT hw h)⟩
  refine pal_in_peg_of_latch' (Nat.mul_pos hn (PalPeg.Local.cnt_pos K)) M
    (PofC centreC placeC entry) (fun _ => q) (fun _ => first) 2048
    (fun w => PofC_onLetter centreC placeC entry w)
    (fun w => PofC_leftFirst centreC placeC entry w)
    (fun w => stLG' τF w (stP w) (TcP w w.length))
    (fun w => arrLG' τF w (stP w) (TcP w w.length))
    (fun w => (w.length + 1) * τF) ?_ ?_ ?_ ?_
  · intro w hw
    have h := hP w hw
    exact abstractRun_throttledL'_2p18 w (stP w) (TcP w w.length)
      (PofC centreC placeC entry w) q first 2048
      (fun j => sharedC_trunc_vm w j centreC placeC entry (fun s => (centrePlaceC w j s).1)
        (fun s => (centrePlaceC w j s).2))
      (sharedC_suf w _ _ centreC placeC entry)
      (by rw [h.base.pre.start]; rfl) (needL'_boot w (stP w) h.base.pre.start)
      (by rw [h.base.pre.start]; exact sufVM_boot w) h.base.pre.trace.tick
  · intro w hw
    exact hreal w hw _ _ (hP w hw)
  · exact ledger_throttledL'_2p18 (PofC centreC placeC entry) (fun _ => q) (fun _ => first)
      stP TcP hpre (fun w hw => (hP w hw).base.pre.report w.length (by omega) le_rfl)
      (fun w hw => base_of_preTraceB (hP w hw).base)
      (fun w hw => (hP w hw).base.pre.cost)
  · exact GalilEmptyWord.realize_accept'_nil L blank initQ outQ n htape hn

#print axioms pal_in_peg_final5

/-! ## 3. `LPackG` along one tick -/

/-- A VM step that leaves the three heads and the replay counter alone
transports the weakened pack.  `hscm` replaces `CloseoutLPack3.lpack_of_same`'s
use of `hni` for the `minv` field: the landing only has to be in `scan` mode
when the source is. -/
theorem lpackG_of_same {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackG w c s) (hni : c.mode ≠ Mode.init)
    (hL : t.left = s.left) (hC : t.center = s.center) (hR : t.right = s.right)
    (hrep : t.replay = s.replay) (hr : c'.replaying = c.replaying)
    (hsc : c'.mode = Mode.scan → c'.replaying = false → c.mode = Mode.scan ∧ c.replaying = false)
    (hscm : c'.mode = Mode.scan → c.mode = Mode.scan) :
    LPackG w c' t := by
  refine ⟨fun _ => by rw [hL]; exact hP.lrep hni, ?_,
    fun hm' => minv_same hr hR hC hrep (hP.minvG (hscm hm'))⟩
  intro hm hrr
  obtain ⟨hm0, hr0⟩ := hsc hm hrr
  obtain ⟨r, hi⟩ := hP.scanInv hm0 hr0
  exact ⟨r, by rw [hL, hR, hC]; exact hi⟩

#print axioms lpackG_of_same

section LeavesG
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the leaves of one tick, re-cut.**  `CloseoutLPack3.LTickLeaves`
with the four fallback-phase `MInv` corners dropped (their landing mode is not
`scan`, so `MInvG` is vacuous there) and one new corner added at the
`shift → scan` exit. -/
structure LTickLeavesG (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop where
  /-- The `init` landing. -/
  initPackG : c.mode = Mode.init → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).init s t →
    LPackG w {c with mode := Mode.scan, output := true} t
  /-- **The origin corner** (unchanged). -/
  scanLeft : c.mode = Mode.scan → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- The scan invariant in `scan` mode including a replay (unchanged). -/
  scanInvR : c.mode = Mode.scan →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- The right head can move in `scan` mode (unchanged). -/
  scanCanR : c.mode = Mode.scan → GalilScaffoldChainVerifier.canRight s.right
  /-- **The shift exit, scan half** (unchanged): the new centre's radius. -/
  shiftDoneScan : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    ∃ r, ScanInvariant w (position s.center) r s.left s.right
  /-- **NEW — the shift exit, centre half.**  `shift_done` moves no head, so
  this is `MInv` at the shifted state; the intended proof is
  `GalilLiveCentreShift.leftmost_shift` at the candidate period carried by
  `CloseoutPackRun3.Extra.cand`.  This is the *only* corner the re-cut adds,
  and it replaces `shiftMinv` + `shiftOneMinv`, which had to hold at every
  intermediate shift unit. -/
  shiftDoneMinv : c.mode = Mode.shift →
    ¬ (galilFrameS (PofC centre place entry w) q first).remainingPos s →
    MInv w c s
  /-- `choose` re-centres on the right head — **head half only**; the landing
  mode is `rewind`, so the old `MInv` half is vacuous. -/
  choosePackL : c.mode = Mode.choose → c.odd = true → ∀ t : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).choose s t →
    GalilScaffoldInputTrace.Represents t.left.head w ∧ t.left.head.focus ≠ none
  /-- A rewind unit walks `L` one place left (unchanged). -/
  rewindLeft : c.mode = Mode.rewind → 0 < position (GalilScaffoldInputHead.left s.left)
  /-- **The fallback landing.**  `replayStart` lands in `scan`, so this is where
  the centre invariant comes back: `GalilLiveCentreFallback.leftmost_after_fallback`
  together with `GalilLiveCentreReplay.minv_after_fallback`. -/
  replayPackG : c.mode = Mode.replayStart → ∀ (t : GalilVM) (o : Bool),
    (galilFrameS (PofC centre place entry w) q first).replayStart s t →
    LPackG w {c with mode := Mode.scan, clock := 2048, output := o, replaying := (galilFrameS (PofC centre place entry w) q first).replayPos t} t

/-- **`LPackG` survives one tick, given the re-cut leaves.**  The five
fallback-phase branches (`scan_shift`, `scan_fallback`, `shift_one`,
`rewind_pair`, `choose_select`) now discharge their centre obligation by
`Mode.noConfusion`: their landing mode is `shift`, `copy`, `shift`, `rewind`,
`rewind`. -/
theorem lpackG_tick {w : List (Fin 2)} {c c' : Control} {s t : GalilVM}
    (hP : LPackG w c s) (hL : LTickLeavesG centre place entry q first w c s)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 ⟨c, s⟩ ⟨c', t⟩) :
    LPackG w c' t := by
  cases h
  case init =>
    rename_i hm hi
    exact hL.initPackG hm _ hi
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackG_of_same hP (by rw [hm]; decide) hl hC hr hrep rfl
      (fun hm' hr' => ⟨hm', hr'⟩) (fun hm' => hm')
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hC, -, -, -, -, -, hrep, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    exact lpackG_of_same hP (by rw [hm]; decide) hl hC hr hrep rfl
      (fun hm' hr' => ⟨hm', hr'⟩) (fun hm' => hm')
  case restart =>
    rename_i hm hb
    obtain ⟨wch, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    exact lpackG_of_same hP (by rw [hm]; decide) rfl rfl rfl rfl rfl
      (fun hm' hr' => ⟨hm', hr'⟩) (fun hm' => hm')
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨vs, vq, hvl, hvr, hmatch, rfl⟩ :=
      compare_matched_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have hpl' : t = (if c.replaying then
        {afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq) with replay := dec (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).replay}
      else afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) := hpl
    have htl : t.left = (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).left := by
      rw [hpl']; cases c.replaying <;> rfl
    have htr : t.right = (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)).right := by
      rw [hpl']; cases c.replaying <;> rfl
    have htc : t.center = s.center := by
      rw [hpl']
      cases c.replaying <;> simp [afterBirth_center, afterCompare_center]
    have hcan := hL.scanCanR hm
    obtain ⟨r, hi⟩ := hL.scanInvR hm
    have hi' := matched_invariant' w vq hvl hvr hmatch hcan hi
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun _ _ => ⟨r + 1, ?_⟩, fun _ => ?_⟩
    · rw [htl, afterBirth_left, afterCompare_left, hvl]
      exact lrep_left hrepr hpres (hL.scanLeft hm)
    · rw [htc, htl, htr, afterBirth_left, afterBirth_right]; exact hi'
    · cases hcr : c.replaying with
      | false =>
        have ht : t = afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq) := by rw [hpl', hcr]; rfl
        have hm0 := minv_match (raw := w) (c := c) (vq := vq) o 2048 hcr hvl hvr hcan hmatch hi
          (hP.minvG hm)
        exact minv_same (by simp) (by rw [ht, afterBirth_right])
          (by rw [ht, afterBirth_center]) (by rw [ht, afterBirth_replay]) hm0
      | true =>
        have ht : t = replayDec true (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterCompare s vs vq)) := by rw [hpl', hcr]; rfl
        have hm0 := minv_matchR (raw := w) (c := c) (vs := vs) (vq := vq)
          (PofC centre place entry w) (fun _ => rfl) o 2048 hcr hvr hcan hi (hP.minvG hm)
        have hm1 := minv_afterBirth (raw := w) (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) hm0
        refine minv_same ?_ ?_ ?_ ?_ hm1
        · show (true && !GalilScaffoldCounter.zero t.replay)
            = !GalilScaffoldCounter.zero (replayDec true (afterCompare s vs vq)).replay
          rw [ht, replayDec_true_replay, afterBirth_replay, replayDec_true_replay]
          simp
        · rw [ht, replayDec_right, afterBirth_right, afterBirth_right, replayDec_right]
        · rw [ht, replayDec_center, afterBirth_center, afterBirth_center, replayDec_center]
        · rw [ht, replayDec_true_replay, afterBirth_replay, afterBirth_replay,
            replayDec_true_replay]
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨wch, hchain, ht⟩ :
      beginShiftVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm',
      fun hm' => Mode.noConfusion hm'⟩
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht, afterBirth_left, afterMismatch_left]; exact hvl
    rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
      compare_mismatch_form centre place entry q first hcmp hmt
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨pl, ht⟩ :
      beginFallbackVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion hm',
      fun hm' => Mode.noConfusion hm'⟩
    have htl : t.left = GalilScaffoldInputHead.left s.left := by
      rw [ht, afterBirth_left, afterMismatch_left]; exact hvl
    rw [htl]; exact lrep_left hrepr hpres (hL.scanLeft hm)
  case shift_one =>
    rename_i hm hp hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨hcC, hcL, hcL2, wch, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
    have htl : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    rw [htl]
    obtain ⟨h1, h2⟩ := lrep_right hrepr hpres hcL
    exact lrep_right h1 h2 hcL2
  case shift_done =>
    rename_i o hm hp ho
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    exact ⟨fun _ => hP.lrep hni, fun _ _ => hL.shiftDoneScan hm hp,
      fun _ => minv_same rfl rfl rfl rfl (hL.shiftDoneMinv hm hp)⟩
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
      (fun hm' => Mode.noConfusion (hm.symm.trans hm'))
  case copy_done =>
    rename_i hm hp hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
      (fun hm' => Mode.noConfusion hm')
  case home_start =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
      (fun hm' => Mode.noConfusion hm')
  case home_step =>
    rename_i hm hl hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
      (fun hm' => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_slice =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
      (fun hm' => Mode.noConfusion (hm.symm.trans hm'))
  case fpp_done =>
    rename_i hm hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
      (fun hm' => Mode.noConfusion hm')
  case markEnd_step =>
    rename_i hm he hi
    obtain ⟨-, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide) (by rw [hset]; rfl) (by rw [hset]; rfl)
      (by rw [hset]; rfl) (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
      (fun hm' => Mode.noConfusion (hm.symm.trans hm'))
  case markEnd_found =>
    rename_i hm he hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
      (fun hm' => Mode.noConfusion hm')
  case choose_step =>
    rename_i hm hs hi
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (by rw [hset]; rfl) rfl
      (fun hm' _ => Mode.noConfusion (hm.symm.trans hm'))
      (fun hm' => Mode.noConfusion (hm.symm.trans hm'))
  case rewind_done =>
    rename_i hm hfi hi
    obtain ⟨heq, hset⟩ := hi
    exact lpackG_of_same hP (by rw [hm]; decide)
      (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl) (by rw [hset, heq]; rfl)
      (by rw [hset]; rfl) rfl (fun hm' _ => Mode.noConfusion hm')
      (fun hm' => Mode.noConfusion hm')
  case choose_select =>
    rename_i hm hodd hs hi
    obtain ⟨hrepr, hpres⟩ := hL.choosePackL hm hodd _ hi
    exact ⟨fun _ => ⟨hrepr, hpres⟩, fun hm' _ => Mode.noConfusion hm',
      fun hm' => Mode.noConfusion hm'⟩
  case rewind_one =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    obtain ⟨⟨-, heq⟩, hset⟩ := hi
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
  case rewind_pair =>
    rename_i hm hfi hpr hi
    have hni : c.mode ≠ Mode.init := by rw [hm]; decide
    have heq := hi.1.2
    have hset := hi.2
    have htl : t.left = GalilScaffoldInputHead.left s.left := by rw [hset, heq]; rfl
    obtain ⟨hrepr, hpres⟩ := hP.lrep hni
    refine ⟨fun _ => ?_, fun hm' _ => Mode.noConfusion (hm.symm.trans hm'),
      fun hm' => Mode.noConfusion (hm.symm.trans hm')⟩
    rw [htl]; exact lrep_left hrepr hpres (hL.rewindLeft hm)
  case replayStart =>
    rename_i o hm ho ho' hi
    exact hL.replayPackG hm _ o hi

/-- `lpackG_tick` in state form. -/
theorem lpackG_tick' {w : List (Fin 2)} {x y : State GalilVM}
    (hP : LPackG w x.ctl x.vm) (hL : LTickLeavesG centre place entry q first w x.ctl x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y) :
    LPackG w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  exact lpackG_tick centre place entry q first hP hL h

/-- **The tick induction**: `LPackG` at every state of a pre-loaded trace. -/
theorem lpackG_steps {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length → LTickLeavesG centre place entry q first w (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc w.length → LPackG w (st i).ctl (st i).vm :=
  hP.trace.carried (Pk := fun z => LPackG w z.ctl z.vm)
    (by rw [hP.start]; exact lpackG_boot w)
    (fun n hn ht hp => lpackG_tick' centre place entry q first hp (hLv n (by omega)) ht)

end LeavesG

#print axioms lpackG_tick
#print axioms lpackG_steps

end PalPeg.CloseoutLPack5
