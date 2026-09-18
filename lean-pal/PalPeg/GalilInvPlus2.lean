import PalPeg.GalilFoundLandingL
import PalPeg.GalilInvPlus
import PalPeg.GalilChainCoupling
import PalPeg.GalilNoShiftStage
import PalPeg.GalilReplaySpan
import PalPeg.GalilLexMeasure

/-!
# `InvLP2` and `InvScanC`: the landing invariant with the copy pack and the centre head

Two gaps of `PalPeg.GalilInvPlus` are closed by strengthening the landing
invariant with facts that travel for free along the runs the cycle exits are
made of.

**(a) `hcopy`.**  `GalilChainCoupling.hfloor_final` needs `CopyIdle r`, which
`InvLP` does not carry.  `CopyPack c s := c.mode ≠ .copy → CopyIdle s` holds at
the boot state (`copyPack_boot`) and is preserved by every tick
(`copyPack_tick`, `copyPack_steps`), and an `InvLP` state is in `scan` mode, so
`InvLP2 := InvLP ∧ CopyPack` gives `hfloor` with **no** hypothesis
(`hfloor_of_invLP2`), and `InvLP2` is re-established at every landing of a run
out of an `InvLP2` state (`invLP2_of_stepsAll`) and out of the boot state
(`invLP2_of_boot`).

**(b) `hcenR`.**  `GalilNoShiftStage.foundRouteMC_noshift'` still asks for the
centre-head representation on the `InvScan` branch of `InvS` (`Inv` carries it,
`InvScan` does not).  But every producer of an `InvScan` state is a replay out
of a `Restarted` state and returns the landing with `t'.center = t.center`:
`GalilReplaySegment.replay_after_fallback` (the fallback replay) and all three
branches of `GalilReplaySpan.replay_after_fallback_general''` (quiet, chain
end, broke-and-restarted).  So `InvScanC := InvScan ∧ CentreRep` is available
wherever `InvScan` is (`invScanC_of_restart`, `invScanC_of_replay_after_fallback`,
`invScanC_of_replay_general`), and with `InvLPC := InvLP2 ∧ CentreRep` the
no-shift break loses its `hcenS` hypothesis (`foundRouteMC_noshift''`) and
returns an `InvLP2` landing.

**(c)** `CycleOutMC2` / `CycleOracleMC2` are `GalilLexMeasure.CycleOutMC'` /
`CycleOracleMC'` over `InvLP2`, with the bridge `cycleOracleMC_of_MC2` back to
`GalilTraceCost.CycleOracleMC`.  The bridge needs `hstr`, the strengthening of
an admissible `InvL` state to `InvLP2`; its `CopyPack` half is free from the
boot (`invLP2_of_boot`), its `SpanRep` half is the residue.
-/

set_option autoImplicit false

namespace PalPeg.GalilInvPlus2

open PalPeg PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleLocal PalPeg.GalilInvPlus PalPeg.GalilChainCoupling
open PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-! ## (a) The landing invariant with the copy pack -/

/-- The local recursion state, the entering counters, and the copy pack. -/
def InvLP2 (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  InvLP raw c s ∧ CopyPack c s

theorem invLP2_invLP {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLP2 raw c s) :
    InvLP raw c s := h.1

theorem invLP2_invL {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLP2 raw c s) :
    InvL raw c s := h.1.1

/-- An `InvLP2` state is in `scan` mode, so its copy pack is the copy walker
being idle outright. -/
theorem invLP2_copyIdle {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLP2 raw c s) :
    CopyIdle s := h.2 (by rw [(invS_mode h.1.1.1).1]; decide)

/-- **`hfloor` with no hypothesis.**  `GalilChainCoupling.hfloor_final` from
`InvLP2` alone: the length counter never goes negative at any scan state
reachable from an `InvLP2` state. -/
theorem hfloor_of_invLP2 (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hI : InvLP2 raw c r) :
    ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 m ⟨c, r⟩ z →
      z.ctl.mode = Mode.scan → 0 ≤ value z.vm.length :=
  hfloor_final centre place entry q first hI.1 (invLP2_copyIdle hI)

/-- The copy pack travels along every sound run. -/
theorem copyPack_of_stepsAll (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {n : ℕ} {x y : State GalilVM} (hx : CopyPack x.ctl x.vm)
    (h : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      n x y) : CopyPack y.ctl y.vm :=
  copyPack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048 (stepsAll_steps h) hx

/-- An `InvLP` landing of a run out of a copy-packed state is `InvLP2`. -/
theorem invLP2_of_stepsAll (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {n : ℕ} {x : State GalilVM} {c : Control} {r : GalilVM}
    (hx : CopyPack x.ctl x.vm)
    (h : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw)
      n x ⟨c, r⟩) (hI : InvLP raw c r) : InvLP2 raw c r :=
  ⟨hI, copyPack_of_stepsAll centre place entry q first hx h⟩

/-- **The copy pack is free from the boot.**  Every `InvLP` state reached from
the boot state is `InvLP2`. -/
theorem invLP2_of_boot (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (d : ℕ)
    {raw : List (Fin 2)} {n : ℕ} {c : Control} {r : GalilVM}
    (h : Steps (galilFrameS (PofC centre place entry raw) q first) 2048 n
      ⟨GalilScaffoldController.initial d, GalilBootVM.initVM0 raw⟩ ⟨c, r⟩)
    (hI : InvLP raw c r) : InvLP2 raw c r :=
  ⟨hI, copyPack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048 h
    (copyPack_boot d raw)⟩

#print axioms invLP2_copyIdle
#print axioms hfloor_of_invLP2
#print axioms invLP2_of_stepsAll
#print axioms invLP2_of_boot

/-! ## (b) The centre head on the `InvScan` branch -/

/-- The centre head represents the input and is present. -/
def CentreRep (raw : List (Fin 2)) (s : GalilVM) : Prop :=
  GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none

theorem centreRep_congr {raw : List (Fin 2)} {s t : GalilVM} (h : t.center = s.center)
    (hc : CentreRep raw s) : CentreRep raw t := by
  unfold CentreRep at hc ⊢; rw [h]; exact hc

/-- A restart state carries the centre head. -/
theorem centreRep_of_restarted {raw : List (Fin 2)} {t : GalilVM} {Rad : ℕ} {last : Counter}
    (h : Restarted raw t Rad last) : CentreRep raw t := ⟨h.2.1, h.2.2.1⟩

/-- `Inv` carries the centre head (`GalilNoShiftStage.centreRep_of_inv`). -/
theorem centreRep_of_inv {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : Inv raw c r) :
    CentreRep raw r := GalilNoShiftStage.centreRep_of_inv h

/-- `InvScan` together with the centre head the replay came from. -/
def InvScanC (delay : ℕ) (raw : List (Fin 2)) (c : Control) (s : GalilVM) (k : ℕ) : Prop :=
  PalPeg.GalilReplaySegment.InvScan delay raw c s k ∧ CentreRep raw s

/-- **Centre-head transport.**  Scan and chain ticks move the centre only on a
restart or a shift, so every replay landing out of a `Restarted` state — the
only way an `InvScan` state is ever produced — keeps its centre head. -/
theorem invScanC_of_restart {delay : ℕ} {raw : List (Fin 2)} {c' : Control} {t t' : GalilVM}
    {k Rad : ℕ} {last : Counter} (hR : Restarted raw t Rad last) (hC : t'.center = t.center)
    (hIS : PalPeg.GalilReplaySegment.InvScan delay raw c' t' k) : InvScanC delay raw c' t' k :=
  ⟨hIS, centreRep_congr hC (centreRep_of_restarted hR)⟩

/-- **The fallback replay lands in `InvScanC`.**
`GalilReplaySegment.replay_after_fallback` with its `InvScan` strengthened. -/
theorem invScanC_of_replay_after_fallback (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) → searchEffect P a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    ∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanC delay raw c' t' r := by
  obtain ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw P q first delay hex hd hsearch hpres
      hquiet r hr0 c t hm hc hrpl hR hrep hM hfr hsi
  exact ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, invScanC_of_restart hR hC hIS⟩

/-- **The general replay lands in `InvScanC`** too:
`GalilReplaySpan.replay_after_fallback_general''` with the `InvScan` of both of
its `InvScan`-producing branches strengthened. -/
theorem invScanC_of_replay_general (raw : List (Fin 2)) (P : Shared)
    (hP : P.onLetter = onLetterVM raw) (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9)
    (delay : ℕ) (hex : ∀ s, P.replayExhausted s = zero s.replay) (hd : 1 ≤ delay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect P a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) → searchEffect P a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hshape : PalPeg.GalilWatchOkInst.StartShape P)
    (hbudget : PalPeg.GalilReplaySpan.ReplayBudget raw P delay)
    (hrs : PalPeg.GalilReplaySpan.RestartShape P)
    (r : ℕ) (hr0 : 0 < r) (c : Control) (t : GalilVM)
    (hm : c.mode = Mode.scan) (hc : c.clock = delay) (hrpl : c.replaying = true)
    (hR : Restarted raw t 0 reset) (hrep : t.replay = ofNat r)
    (hM : MInv raw c t) (hfr : Frontier t) (hsi : ShiftIdle t) :
    (∃ (es : List Bool) (c' : Control) (t' : GalilVM),
      WatchSegE P q first delay es c t c' t' ∧
      (SoundScanNR raw ⟨c', t'⟩ →
        StepsAll (galilFrameS P q first) delay (SoundScanNR raw) es.length ⟨c, t⟩ ⟨c', t'⟩) ∧
      es.length = r * delay ∧ es.count true = r ∧
      position t'.right = position t.right + r ∧ t'.center = t.center ∧
      InvScanC delay raw c' t' r) ∨
    PalPeg.GalilReplaySpan.ChainEnd raw P q first delay (position t.right + r) c t 0 r ∨
    (PalPeg.GalilReplaySpan.BrokeAndRestarted raw P q first delay c t ∧
      ∃ (n : ℕ) (c' : Control) (t' : GalilVM),
        (SoundScanNR raw ⟨c', t'⟩ →
          StepsAll (galilFrameS P q first) delay (SoundScanNR raw) n ⟨c, t⟩ ⟨c', t'⟩) ∧
        position t'.right = position t.right + r ∧ t'.center = t.center ∧
        InvScanC delay raw c' t' r) := by
  rcases PalPeg.GalilReplaySpan.replay_after_fallback_general'' raw P hP hP' q first delay hex hd
      hsearch hpres hshape hbudget hrs r hr0 c t hm hc hrpl hR hrep hM hfr hsi with
    ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, hIS⟩ | hEnd | ⟨hw, n, c', t', hst, hpos, hC, hIS⟩
  · exact Or.inl ⟨es, c', t', hseg, hst, hlen, hcnt, hpos, hC, invScanC_of_restart hR hC hIS⟩
  · exact Or.inr (Or.inl hEnd)
  · exact Or.inr (Or.inr ⟨hw, n, c', t', hst, hpos, hC, invScanC_of_restart hR hC hIS⟩)

#print axioms invScanC_of_restart
#print axioms invScanC_of_replay_after_fallback
#print axioms invScanC_of_replay_general

/-! ## (b, cont.) The landing invariant with the centre head -/

/-- The full landing invariant: `InvLP`, the copy pack, the centre head. -/
def InvLPC (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  InvLP2 raw c s ∧ CentreRep raw s

theorem invLPC_invLP2 {raw : List (Fin 2)} {c : Control} {s : GalilVM} (h : InvLPC raw c s) :
    InvLP2 raw c s := h.1

/-- The radius-`0` fallback landing and every found landing are `Inv` states,
so they carry the centre head outright. -/
theorem invLPC_of_landed (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {k : ℕ} {x : State GalilVM} {cT : Control} {sT : GalilVM}
    (hx : CopyPack x.ctl x.vm)
    (hst : StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
      x ⟨cT, sT⟩)
    (hI : Inv raw cT sT) (hS : SpanRep sT) : InvLPC raw cT sT :=
  ⟨invLP2_of_stepsAll centre place entry q first hx hst (invLP_of_landed hst hI hS),
    centreRep_of_inv hI⟩

/-- **The replayed landing carries the centre head.**  `invLP_after_replayLanding`
with `CentreRep`: the replay lands with `t'.center = sT.center` and `sT` is the
restart the fallback made. -/
theorem invLPC_after_replayLanding (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (cT : Control) (sT : GalilVM) (R : ℕ)
    (hst : ∃ k, StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048
      (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hL : ReplayLanding raw cT sT R) (hS : SpanRep sT)
    (hprog : position r.center < position sT.center) :
    ∃ (c' : Control) (t' : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨c', t'⟩ ∧
      InvLP raw c' t' ∧ CentreRep raw t' ∧ position r.center < position t'.center := by
  obtain ⟨es, c', t', hseg, hrun, _hlen, hcnt, _hrpos, hcen, hIS⟩ :=
    PalPeg.GalilReplaySegment.replay_after_fallback raw (PofC centre place entry raw) q first 2048
      hex (by norm_num) hsearch hpres hquiet R hL.pos cT sT hL.mode hL.clock hL.replaying
      hL.rest hL.replay hL.minv hL.frontier hL.shiftIdle
  obtain ⟨k, hst1⟩ := hst
  have hall := stepsAll_trans hst1 (hrun (hout c' t' R hIS))
  have hRR : RadiusRep t'.radius R := by
    have h0 := radiusRep_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.1
    rw [hcnt, Nat.zero_add] at h0
    exact h0
  have hE : EntryCounters raw t' :=
    entryCounters_of_invScan hIS hRR (spanRep_watchSegE _ q first 2048 hseg hS)
      (canonical_length_watchSegE _ q first 2048 hseg hL.rest.2.2.2.2.2.1)
  refine ⟨c', t', k + es.length, hall, ⟨invL_of_run hall (Or.inr ⟨R, hIS⟩), hE⟩,
    (invScanC_of_restart hL.rest hcen hIS).2, ?_⟩
  rw [hcen]
  exact hprog

#print axioms invLPC_of_landed
#print axioms invLPC_after_replayLanding

/-! ## (b, cont.) The routes out of an `InvLPC` state -/

/-- Every non-report fallback route re-enters the recursion at an `InvLPC`
state. -/
theorem invLPC_of_fallbackRouteP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    (hsearch : ∀ s : GalilVM, PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centre place entry raw) a s v)
    (hpres : ∀ (s : GalilVM) (a : Bool) (v : SearchVM),
      PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get s) →
      searchEffect (PofC centre place entry raw) a s v →
      PalPeg.GalilBranchInvariants2.SearchReady v)
    (hquiet : PalPeg.GalilReplaySegment.SearchQuiet (PofC centre place entry raw))
    (hout : ∀ (c' : Control) (t' : GalilVM) (k : ℕ),
      PalPeg.GalilReplaySegment.InvScan 2048 raw c' t' k → SoundScanNR raw ⟨c', t'⟩)
    (c : Control) (r : GalilVM) (hcp : CopyPack c r)
    (h : FallbackRouteP centre place entry q first raw c r) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
      StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
        ⟨c, r⟩ ⟨cT, sT⟩ ∧
      InvLPC raw cT sT ∧ position r.center < position sT.center := by
  cases h with
  | landed cT sT hst hI hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact ⟨cT, sT, k, hst, invLPC_of_landed centre place entry q first hcp hst hI hS, hprog⟩
  | replaying cT sT R hst hL hS hprog =>
    obtain ⟨c', t', k, hall, hIL, hcen, hprog'⟩ :=
      invLPC_after_replayLanding centre place entry q first raw hex hsearch hpres hquiet hout
        c r cT sT R hst hL hS hprog
    exact ⟨c', t', k, hall,
      ⟨invLP2_of_stepsAll centre place entry q first hcp hall hIL, hcen⟩, hprog'⟩

/-- Every non-report found route re-enters the recursion at an `InvLPC` state:
a found landing is a restart, so `Inv` supplies the centre head. -/
theorem invLPC_of_foundRouteLP (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {raw : List (Fin 2)} {c : Control} {r : GalilVM} (hcp : CopyPack c r)
    (h : FoundRouteLP (PofC centre place entry raw) q first raw c r) :
    LocalReport (PofC centre place entry raw) q first raw c r ∨
      ∃ (cT : Control) (sT : GalilVM) (k : ℕ),
        StepsAll (galilFrameS (PofC centre place entry raw) q first) 2048 (SoundScanNR raw) k
          ⟨c, r⟩ ⟨cT, sT⟩ ∧
        InvLPC raw cT sT ∧ position r.center < position sT.center := by
  cases h with
  | report h => exact Or.inl h
  | shift cT sT hst hM hR hres hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact Or.inr ⟨cT, sT, k, hst,
      invLPC_of_landed centre place entry q first hcp hst (inv_of_residual hM hR hres) hS, hprog⟩
  | noShift cT sT hst hM hR hres hS hprog =>
    obtain ⟨k, hst⟩ := hst
    exact Or.inr ⟨cT, sT, k, hst,
      invLPC_of_landed centre place entry q first hcp hst (inv_of_residual hM hR hres) hS, hprog⟩

/-- **`foundRouteMC_noshift''`.**  `GalilNoShiftStage.foundRouteMC_noshift'`
with `hcenS` discharged by the landing invariant, and with the landing
strengthened to `InvLP2` (the copy pack travels along the exit's own run). -/
theorem foundRouteMC_noshift'' (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLPC raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (hwatch2 : s2.chain = .watch (GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius))
    (hes0 : es.count true = 0)
    (hpal1 : PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1))
    (hpal2 : PalAt (encoded raw) (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)))
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    -- **`M-watchBreak` 修正で現れた義務**（`GalilNoShiftStage.foundRouteMC_noshift'` から素通し）。
    -- 比較 tick は「背景 step → matched」の順なので、背景 step が `ChainStep.watchBreak`
    -- （正 lag ＋ 不一致）で chain を壊しうる。その分岐が起きないことを要求する。
    (hnobg : ∀ v, ¬ BreakStepPos w3 v)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right := by
  obtain ⟨cT, sT, k, L, hrun, hcr, hIT, h1, h2, h3⟩ :=
    GalilNoShiftStage.foundRouteMC_noshift' centre place entry qq first raw hex hI.1.1 hlive
      (fun _ _ => hI.2) hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg
      cen ys b hwatch2 hes0 hpal1 hpal2 hseg hm3 hr3 hc3 w3 hs3 hav3 hnobg vs3 vq3 hcmp3 hmt3 hq3
      o3 ho3 w3' hbroken hmargin
  exact ⟨cT, sT, k, L, hrun, hcr,
    invLP2_of_stepsAll centre place entry qq first hI.1.2 hrun hIT, h1, h2, h3⟩

#print axioms invLPC_of_fallbackRouteP
#print axioms invLPC_of_foundRouteLP
#print axioms foundRouteMC_noshift''

/-! ## (c) The costed cycle oracle over `InvLP2` -/

/-- **`GalilLexMeasure.CycleOutMC'` over `InvLP2`.**  Same two exits — the
target is reached, or the cycle returns to the recursion with `mu` down — but
the landing carries the copy pack as well. -/
def CycleOutMC2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) (m : ℕ)
    (c : Control) (r : GalilVM) : Prop :=
  ReachAtC P q first raw m c r ∨
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧
      InvLP2 raw cT sT ∧ mu raw sT < mu raw r ∧
      position sT.right ≤ 2 * m - 1

/-- **The costed per-target cycle oracle over `InvLP2`.** -/
def CycleOracleMC2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2)) : Prop :=
  ∀ (m : ℕ) (c : Control) (r : GalilVM), 1 ≤ m → m ≤ raw.length → InvLP2 raw c r →
    position r.right ≤ 2 * m - 1 → CycleOutMC2 P q first raw m c r

/-- The centre-progress exit (fallback and found routes). -/
theorem cycleOutMC2_of_centre {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hI : InvLP2 raw c r)
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT)
    (hlt : position r.center < position sT.center) (hp : position sT.right ≤ 2 * m - 1) :
    CycleOutMC2 P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT,
    mu_lt_of_centre (invS_center_le hI.1.1.1) hIT.1.1 hlt, hp⟩

/-- The no-shift exit (centre kept, right head strictly up). -/
theorem cycleOutMC2_of_noshift {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} {cT : Control} {sT : GalilVM} {k : ℕ} {L : List Piece}
    (hst : StepsAll (galilFrameS P q first) 2048 (SoundScanNR raw) k ⟨c, r⟩ ⟨cT, sT⟩)
    (hcr : CostedRun r sT k L) (hIT : InvLP2 raw cT sT)
    (hc : position sT.center = position r.center) (hlt : position r.right < position sT.right)
    (hp : position sT.right ≤ 2 * m - 1) : CycleOutMC2 P q first raw m c r :=
  Or.inr ⟨cT, sT, k, L, hst, hcr, hIT, mu_lt_of_right hIT.1.1 hc hlt, hp⟩

/-- Forgetting the copy pack and the entering counters. -/
theorem cycleOutMC'_of_MC2 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)} {m : ℕ}
    {c : Control} {r : GalilVM} (h : CycleOutMC2 P q first raw m c r) :
    CycleOutMC' P q first raw m c r := by
  rcases h with h | ⟨cT, sT, k, L, hst, hcr, hIT, hlt, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨cT, sT, k, L, hst, hcr, hIT.1.1, hlt, hp⟩

/-- **The recursion over `InvLP2`.**  The strengthened class is closed under
the oracle's own exits, so an `InvLP2` state reaches its target on its own. -/
theorem reachC_fuel2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2 P q first raw) (m : ℕ) (hm1 : 1 ≤ m) (hmle : m ≤ raw.length) :
    ∀ (n : ℕ) (c : Control) (r : GalilVM), mu raw r ≤ n → InvLP2 raw c r →
      position r.right ≤ 2 * m - 1 → ReachAtC P q first raw m c r := by
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
      exact ⟨y, k + k', L ++ L', stepsAll_trans hst hst', costedRun_trans hcr hcr', hrp, hfr, hcont⟩

theorem reachC_from_invLP2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2 P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvLP2 raw c r) (hp : position r.right ≤ 2 * m - 1) :
    ReachAtC P q first raw m c r :=
  reachC_fuel2 P q first raw hor m hm1 hmle _ c r le_rfl hI hp

/-- **The original oracle at every `InvLP2` state**, unconditionally. -/
theorem cycleOutMC_of_invLP2 (P : Shared) (q : ℕ) (first : Fin 9) (raw : List (Fin 2))
    (hor : CycleOracleMC2 P q first raw) {m : ℕ} (hm1 : 1 ≤ m) (hmle : m ≤ raw.length)
    {c : Control} {r : GalilVM} (hI : InvLP2 raw c r) (hp : position r.right ≤ 2 * m - 1) :
    CycleOutMC P q first raw m c r :=
  Or.inl (reachC_from_invLP2 P q first raw hor hm1 hmle hI hp)

/-- **The bridge back to `GalilTraceCost.CycleOracleMC`.**  `hstr` is the one
residue: every admissible `InvL` state of the recursion carries `SpanRep` (the
entering counters) and the copy pack.  The copy-pack half is free from the boot
(`invLP2_of_boot`). -/
theorem cycleOracleMC_of_MC2 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleMC2 P q first raw)
    (hstr : ∀ (c : Control) (r : GalilVM), InvL raw c r → InvLP2 raw c r) :
    CycleOracleMC P q first raw :=
  fun _ c r hm1 hmle hI hp => cycleOutMC_of_invLP2 P q first raw hor hm1 hmle (hstr c r hI) hp

/-- The same bridge at the `CycleOracleMC'` level. -/
theorem cycleOracleMC'_of_MC2 {P : Shared} {q : ℕ} {first : Fin 9} {raw : List (Fin 2)}
    (hor : CycleOracleMC2 P q first raw)
    (hstr : ∀ (c : Control) (r : GalilVM), InvL raw c r → InvLP2 raw c r) :
    CycleOracleMC' P q first raw :=
  fun m c r hm1 hmle hI hp => cycleOutMC'_of_MC2 (hor m c r hm1 hmle (hstr c r hI) hp)

#print axioms cycleOutMC2_of_centre
#print axioms cycleOutMC2_of_noshift
#print axioms cycleOutMC'_of_MC2
#print axioms reachC_from_invLP2
#print axioms cycleOutMC_of_invLP2
#print axioms cycleOracleMC_of_MC2
#print axioms cycleOracleMC'_of_MC2

/-! ## (d) The no-shift route with the landing invariant exported

`CloseoutWatchPhase2.landingRestart_of_inv` turns a landing's full `Inv` pack
into `LandingRestart`, but the no-shift route chain
(`GalilFoundLandingL.foundRouteMC_noshift` →
`GalilNoShiftStage.foundRouteMC_noshift'` → `foundRouteMC_noshift''`) throws the
pack away at its first link.  The two theorems below re-run that chain on
`GalilFoundLandingL.foundRouteMC_noshift_Inv`, which keeps it.  Only the
conclusion changes; the hypotheses and the proof scripts are those of the
originals. -/

section NoShiftInv

open PalPeg.GalilCostedFound PalPeg.GalilFoundLandingL PalPeg.GalilNoShiftStage

theorem foundRouteMC_noshift'_Inv (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLP raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    (hcenS : ∀ k : ℕ, PalPeg.GalilReplaySegment.InvScan 2048 raw c0 r k →
      GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (hwatch2 : s2.chain = .watch (freshWatch sF.center cen ys b sF.radius))
    (hes0 : es.count true = 0)
    (hpal1 : PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1))
    (hpal2 : PalAt (encoded raw) (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)))
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    -- **`M-watchBreak` 修正で現れた義務**（`GalilNoShiftStage.foundRouteMC_noshift'` から素通し）。
    -- 比較 tick は「背景 step → matched」の順なので、背景 step が `ChainStep.watchBreak`
    -- （正 lag ＋ 不一致）で chain を壊しうる。その分岐が起きないことを要求する。
    (hnobg : ∀ v, ¬ BreakStepPos w3 v)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right ∧ Inv raw cT sT := by
  set P := PofC centre place entry raw with hPdef
  -- (3) the centre representation
  have hcenR : GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none :=
    hI.1.1.elim centreRep_of_inv (fun ⟨k, h⟩ => hcenS k h)
  -- the entering counters
  obtain ⟨R, hi0, hRR0, -, -⟩ := hI.2
  obtain ⟨hsc0, _, hrad0, hrc0, _⟩ := watchSegE_heads P qq first 2048 hseg0
  have hcen : sF.center = r.center := watchSegE_center P qq first 2048 hseg0
  have hrcF : Canonical sF.radius := hrc0 hRR0.1
  have hradF : value sF.radius = (R : ℤ) + es0.count true := by rw [hrad0, hRR0.2]
  -- the scan invariant at the breaking comparison
  have hinvF : ScanInvariant raw (position sF.center) (R + es0.count true) sF.left sF.right := by
    rw [hcen]; exact scan_events_invariant (hsc0 raw (position r.center) R) hi0
  have hinv1 := matched_invariant' raw vq (s := sF) (vs := ⟨left sF.left, right sF.right, ch⟩)
    rfl rfl hmt havF hinvF
  obtain ⟨hsc1, _, hrad1, _, _⟩ := watchSegE_heads P qq first 2048 hprepSeg
  have hcen2 : s2.center = sF.center := by
    have h0 := watchSegE_center P qq first 2048 hprepSeg
    rw [afterBirth_center, afterCompare_center] at h0; exact h0
  have hinv2 := scan_events_invariant (hsc1 raw (position sF.center) _) hinv1
  have hne2 : s2.chain ≠ .idle := by rw [hwatch2]; intro h0; cases h0
  obtain ⟨es2, hticks, hsc2, hcen21, _, hrad2, _, _⟩ := watchSeg_events P qq first 2048 hseg hne2
  have hi3 : ScanInvariant raw (position s3.center)
      (R + es0.count true + 1 + es.count true + es2.count true) s3.left s3.right := by
    rw [hcen21, hcen2]
    exact scan_events_invariant (hsc2 raw (position sF.center) _) hinv2
  have hinv3 := matched_invariant raw P qq first vq3 hcmp3 hmt3 hav3 hi3
  -- the chain: a watch run out of `freshWatch`, then the break
  rw [hwatch2, hs3] at hticks
  have hrun3 := chainTicks_watch_run es2 hticks
  have hmatch3 : read (left s3.left) = read (right s3.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp3
    rw [scanLens.get_set] at hl0 hr0
    have hp0 := matched_parts P qq first hmt3
    rw [hl0, hr0] at hp0; exact hp0
  obtain ⟨-, -, htick⟩ := compare_parts P qq first hcmp3 hmatch3
  have hvs3 : vs3.chain = .broken w3' := by rw [← afterCompare_chain s3 vs3 vq3]; exact hbroken
  rw [hs3, hvs3] at htick
  obtain ⟨y, hy, hym⟩ := htick
  cases hy with
  | watchBreak _ v hbp => exact absurd hbp (hnobg v)
  | watchStep _ m hint =>
  have hym' : ChainMatched (.watch m) (.broken w3') := by simpa using hym
  cases hym' with
  | breaks _ _ hbr =>
  have hrunM := run_snoc hrun3 (.step hint (.idle m))
  obtain ⟨-, -, -, -, -, hdR, -, -⟩ := fresh_break_ledger _ cen ys b _ hrcF hrunM hbr
  have hc2 : (es2 ++ [false]).count true = es2.count true := by simp
  rw [hc2] at hdR
  -- the places
  have hplaces := fresh_break_places raw sF.center cen ys b sF.radius hrcF
    (by rw [hcen]; exact hcenR.1) (by rw [hcen]; exact hcenR.2)
    (by rw [hcen]; exact hpal1) (by rw [hcen]; exact hpal2) hrunM hbr hmargin
    (fun R' hR' => by
      have hp := hinv3.palindrome
      have e : R' = R + es0.count true + 1 + es.count true + es2.count true + 1 := by
        have : (R' : ℤ) = (R : ℤ) + es0.count true + 1 + es2.count true + 1 := by
          rw [hR', hdR, hradF]
        rw [hes0]; omega
      rw [e, ← hcen2, ← hcen21]; exact hp)
  obtain ⟨hcanon, hlast, hlag, hst⟩ := fresh_break_stage _ cen ys b _ hrcF hrunM hbr hplaces
  refine foundRouteMC_noshift_Inv centre place entry qq first raw hex hI hlive hcenR hseg0 hmF hrF hcF
    havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3
    hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag hcanon (fun R' hR' => hst R' ?_)
  have hv := hR'.2
  rw [afterCompare_radius, inc_value, hrad2, hrad1, afterBirth_radius,
    afterCompare_radius, inc_value, hes0] at hv
  rw [hdR]
  push_cast at hv ⊢
  linarith

#print axioms freshWatch_eq
#print axioms centreRep_of_inv

/-- **`foundRouteMC_noshift''` with the landing invariant exported.**  Same
hypotheses as `foundRouteMC_noshift''`; the conclusion adds `Inv raw cT sT`,
taken from `foundRouteMC_noshift'_Inv`. -/
theorem foundRouteMC_noshift''_Inv (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry qq : ℕ) (first : Fin 9)
    (raw : List (Fin 2))
    (hex : ∀ s, (PofC centre place entry raw).replayExhausted s = zero s.replay)
    {c0 : Control} {r : GalilVM} (hI : InvLPC raw c0 r)
    (hlive : ∀ (m : ℕ) (z : State GalilVM),
      Steps (galilFrameS (PofC centre place entry raw) qq first) 2048 m ⟨c0, r⟩ z →
      CentreLive z.ctl z.vm)
    {es0 : List Bool} {cF : Control} {sF : GalilVM}
    (hseg0 : WatchSegE (PofC centre place entry raw) qq first 2048 es0 c0 r cF sF)
    (hmF : cF.mode = .scan) (hrF : cF.replaying = false)
    (hcF : cF.clock = 1) (havF : canRight sF.right) (hidle : sF.chain = .idle)
    (vq : SearchVM) (hq : searchEffect (PofC centre place entry raw) true sF vq)
    (hfound : vq.search.mode = .found)
    (hmt : read (left sF.left) = read (right sF.right))
    (ch : ChainVM)
    (hch : ChainMatched (chainStart (vq.dp.config.tapes 11) ((PofC centre place entry raw).centre sF)
      ((PofC centre place entry raw).place sF) sF.center sF.radius) ch)
    (hchne : ch ≠ .idle) (oF : Bool)
    (hoF : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) cF.output oF)
    {es : List Bool} {c2 : Control} {s2 : GalilVM}
    (hprepSeg : WatchSegE (PofC centre place entry raw) qq first 2048 es
      {cF with clock := 2048, output := oF, replaying := false}
      (afterBirth true (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq)) c2 s2)
    (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (hwatch2 : s2.chain = .watch (GalilNoShiftStage.freshWatch sF.center cen ys b sF.radius))
    (hes0 : es.count true = 0)
    (hpal1 : PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1))
    (hpal2 : PalAt (encoded raw) (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)))
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
    -- **`M-watchBreak` 修正で現れた義務**（`GalilNoShiftStage.foundRouteMC_noshift'` から素通し）。
    -- 比較 tick は「背景 step → matched」の順なので、背景 step が `ChainStep.watchBreak`
    -- （正 lag ＋ 不一致）で chain を壊しうる。その分岐が起きないことを要求する。
    (hnobg : ∀ v, ¬ BreakStepPos w3 v)
    (vs3 : ScanVM) (vq3 : SearchVM)
    (hcmp3 : (galilFrame (PofC centre place entry raw) qq first).compare s3 (scanLens.set s3 vs3))
    (hmt3 : (galilFrame (PofC centre place entry raw) qq first).matched (scanLens.set s3 vs3))
    (hq3 : searchEffect (PofC centre place entry raw) true s3 vq3)
    (o3 : Bool) (ho3 : refresh (galilFrame (PofC centre place entry raw) qq first)
      (afterCompare s3 vs3 vq3) c3.output o3)
    (w3' : GalilScaffoldChainWatch.State) (hbroken : (afterCompare s3 vs3 vq3).chain = .broken w3')
    (hmargin : negative w3'.margin = false) :
    ∃ (cT : Control) (sT : GalilVM) (k : ℕ) (L : List Piece),
      StepsAll (galilFrameS (PofC centre place entry raw) qq first) 2048 (SoundScanNR raw) k
        ⟨c0, r⟩ ⟨cT, sT⟩ ∧
      CostedRun r sT k L ∧ InvLP2 raw cT sT ∧
      position sT.center = position r.center ∧ position r.right < position sT.right ∧
      sT.right = (afterCompare s3 vs3 vq3).right ∧ Inv raw cT sT := by
  obtain ⟨cT, sT, k, L, hrun, hcr, hIT, h1, h2, h3, hInv⟩ :=
    foundRouteMC_noshift'_Inv centre place entry qq first raw hex hI.1.1 hlive
      (fun _ _ => hI.2) hseg0 hmF hrF hcF havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg
      cen ys b hwatch2 hes0 hpal1 hpal2 hseg hm3 hr3 hc3 w3 hs3 hav3 hnobg vs3 vq3 hcmp3 hmt3 hq3
      o3 ho3 w3' hbroken hmargin
  exact ⟨cT, sT, k, L, hrun, hcr,
    invLP2_of_stepsAll centre place entry qq first hI.1.2 hrun hIT, h1, h2, h3, hInv⟩

end NoShiftInv

#print axioms foundRouteMC_noshift'_Inv
#print axioms foundRouteMC_noshift''_Inv

end PalPeg.GalilInvPlus2
