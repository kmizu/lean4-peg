import PalPeg.GalilFoundLandingL
import PalPeg.GalilCatchUpDistance
import PalPeg.GalilLastLowerBreak
import PalPeg.GalilLastRadius
import PalPeg.GalilRadiusConsumed
import PalPeg.GalilGlueBLeaves

/-!
# The no-shift break: stage budget, canonical `last`, centre representation

Discharges `hstage`, `hcanon` (and `hlast`, `hlag`) of
`GalilFoundLandingL.foundRouteMC_noshift`.  Ledger out of the fresh watch
(`fresh_break_ledger`): at the pre-break state `m`, `distance = 4h + margin`,
`distance = radius + 1 + #matched(watch)` (the restart radius minus one), and
the control is a successful sweep from `ready`.  A nonnegative break margin
gives only `4h - 1 ≤ distance`; the corner `distance = 4h - 1` (break at place
`4h`, `last = 2h`, budget false) is excluded by the input (`fresh_break_places`):
prediction `x[C+2h]`, read `x[C+4h]`, equal by the scan palindrome at `C` and
the candidate palindromes `PalAt (C-h) h`, `PalAt (C-2h) (2h)`.  With
`4h ≤ distance`, `sweep_last_lower_sharp` (q = 3) and `sweep_gap` give
`StageEntry` (`fresh_break_stage`).
-/

set_option autoImplicit false

namespace PalPeg.GalilNoShiftStage

open PalPeg GalilScaffoldCounter PalPeg.GalilScaffoldChainInputSupply

/-! ## 1. The fresh watch start and its ledger -/

theorem decFour_iter_value (c : Counter) :
    ∀ n : ℕ, value (GalilScaffoldChainCredits.decFour^[n] c) = value c - 4 * n
  | 0 => by simp
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    simp only [GalilScaffoldChainCredits.decFour, dec_value, decFour_iter_value c n]
    push_cast; ring

theorem decFour_iter_canonical (c : Counter) (hc : Canonical c) :
    ∀ n : ℕ, Canonical (GalilScaffoldChainCredits.decFour^[n] c)
  | 0 => by simpa using hc
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact dec_canonical _ (dec_canonical _ (dec_canonical _ (dec_canonical _
      (decFour_iter_canonical c hc n))))

/-- The watch state `prep_segment_construct` lands on. -/
def freshWatch (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) : GalilScaffoldChainWatch.State :=
  ⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, inc radius,
    GalilScaffoldChainCredits.decFour^[ys.length + 1] (inc radius)⟩

theorem run_snoc {s t u : GalilScaffoldChainWatch.State} {bs : List Bool} {b : Bool}
    (hr : GalilScaffoldChainWatch.Run s bs t) (ht : GalilScaffoldChainWatch.Tick t b u) :
    GalilScaffoldChainWatch.Run s (bs ++ [b]) u := by
  induction hr with
  | stop s => exact .next ht (.stop _)
  | next ht' _ ih => exact .next ht' (ih ht)

/-- **The ledger at the break of a fresh watch.**  Along a watch run out of
`freshWatch`, at the state `m` right before a breaking consume:
the consumed word, the distance as scan places, and the balance. -/
theorem fresh_break_ledger (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    {es : List Bool} {m w' : GalilScaffoldChainWatch.State}
    (hrun : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es m)
    (hbr : BreakStep m w') :
    ∃ xs : List (Fin 3),
      GalilScaffoldChainWatchTrace.Trace (freshWatch ver cen ys b radius).machine xs m.machine ∧
      m.machine.control = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) xs ∧
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) xs).broken = false ∧
      value m.machine.control.distance = (xs.length : ℤ) ∧
      value m.machine.control.distance = value radius + 1 + (es.count true : ℤ) ∧
      value m.machine.control.distance = 4 * ((ys.length : ℤ) + 1) + value m.margin ∧
      GalilScaffoldChainWatch.CanonicalState m := by
  have hc0 : GalilScaffoldChainWatch.CanonicalState (freshWatch ver cen ys b radius) :=
    ⟨inc_canonical _ hrc, decFour_iter_canonical _ (inc_canonical _ hrc) _⟩
  have hcm := GalilScaffoldChainWatch.run_canonical hrun hc0
  have hl0 : value m.lag = 0 := (zero_iff _ hcm.1).mp hbr.1
  obtain ⟨xs, htr, -⟩ := GalilScaffoldChainWatchTrace.run_trace hrun
  have hb := GalilScaffoldChainWatch.run_balance hrun
  have hprog := GalilScaffoldChainInputSupply.watch_progress hrun
  have hd0 : value (freshWatch ver cen ys b radius).machine.control.distance = 0 := rfl
  have hlag0 : value (freshWatch ver cen ys b radius).lag = value radius + 1 := inc_value _
  have hmar0 : value (freshWatch ver cen ys b radius).margin =
      value radius + 1 - 4 * ((ys.length + 1 : ℕ) : ℤ) := by
    show value (GalilScaffoldChainCredits.decFour^[ys.length + 1] (inc radius)) = _
    rw [decFour_iter_value, inc_value]
  have hctl : m.machine.control =
      GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) xs := htr.control
  have hbrk : (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cen ys b) xs).broken
      = false := by rw [← hctl, htr.broken]; rfl
  have hdist := htr.distance
  rw [hd0] at hdist
  unfold GalilScaffoldChainWatch.balance at hb
  rw [hd0, hlag0, hmar0, hl0] at hb
  rw [hd0, hlag0, hl0] at hprog
  refine ⟨xs, htr, hctl, hbrk, by linarith, by linarith, ?_, hcm⟩
  push_cast at hb
  linarith

#print axioms fresh_break_ledger

/-! ## 2. The stage budget at the break, from four semiperiods of places -/

theorem break_control {m w' : GalilScaffoldChainWatch.State} (hbr : BreakStep m w') :
    w'.machine.control = {m.machine.control with broken := true} ∧ w'.lag = m.lag ∧
      value w'.margin = value m.margin + 1 := by
  obtain ⟨-, -, a, hsym, hne, hw⟩ := hbr
  subst hw
  refine ⟨?_, rfl, inc_value _⟩
  exact GalilScaffoldChainConsume.mismatch _ a _ hsym hne

/-- **`fresh_break_stage`.**  At a no-shift break with at least `4*h` consumed
places, the lower bound installed by the restart is canonical and positive,
the lag is zero, and the stage budget holds at the restart radius
`distance + 1`. -/
theorem fresh_break_stage (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    {es : List Bool} {m w' : GalilScaffoldChainWatch.State}
    (hrun : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es m)
    (hbr : BreakStep m w')
    (hplaces : 4 * ((ys.length : ℤ) + 1) ≤ value m.machine.control.distance) :
    Canonical w'.machine.control.last ∧ positive w'.machine.control.last = true ∧
      zero w'.lag = true ∧
      ∀ Rad : ℕ, (Rad : ℤ) = value m.machine.control.distance + 1 →
        StageEntry Rad w'.machine.control.last := by
  obtain ⟨xs, -, hctl, hbrk, hdx, -, -, -⟩ := fresh_break_ledger ver cen ys b radius hrc hrun hbr
  obtain ⟨hc', hlag', -⟩ := break_control hbr
  have hlast : w'.machine.control.last = m.machine.control.last := by rw [hc']
  have hcan : Canonical w'.machine.control.last := by
    rw [hlast, hctl]
    exact (GalilScaffoldChainRestart.run_canonical _ xs (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)).1
  have hlen : (3 + 1) * (ys.length + 1) ≤ xs.length := by
    have : ((4 * (ys.length + 1) : ℕ) : ℤ) ≤ (xs.length : ℤ) := by push_cast; linarith
    have := Int.ofNat_le.mp this
    linarith
  have hlow := PalPeg.GalilLastLowerBreak.sweep_last_lower_sharp cen b ys xs 3 hbrk hlen
  have hup := GalilLastRadius.sweep_gap cen b ys xs hbrk
  rw [← hctl, ← hlast] at hlow hup
  have hpos : positive w'.machine.control.last = true := by
    rw [positive_iff _ hcan]; push_cast at hlow; linarith
  refine ⟨hcan, hpos, by rw [hlag']; exact hbr.1, fun Rad hRad => ?_⟩
  refine GalilLastRadius.stageEntry_of_gap Rad (ys.length + 1) _ (by push_cast at hlow ⊢; linarith) ?_
  rw [hRad]; push_cast at hup ⊢; linarith

#print axioms break_control
#print axioms fresh_break_stage

/-! ## 3. The early-break corner is impossible -/

open GalilScaffoldInputHead GalilScaffoldChainVerifier in
/-- **`fresh_break_places`.**  At a no-shift break the ledger gives
`4*h - 1 ≤ distance` from the nonnegative margin; the corner
`distance = 4*h - 1` (break at place `4*h`, where `last = 2*h` and the budget
`3*Rad ≤ 5*last` would fail) is excluded by the input: the prediction there is
the symbol at `C + 2*h`, the verifier reads `C + 4*h`, and the scan palindrome
at `C` (radius `4*h`) with the candidate's palindromes `PalAt (C-h) h` and
`PalAt (C-2h) (2h)` make them equal. -/
theorem fresh_break_places (raw : List (Fin 2)) (ver : PlaceHead) (cen : Fin 3)
    (ys : List (Fin 3)) (b : Fin 3) (radius : Counter) (hrc : Canonical radius)
    (hvrep : GalilScaffoldInputTrace.Represents ver.head raw) (hvp : ver.head.focus ≠ none)
    (hpal1 : Manacher.PalAt (encoded raw) (position ver - (ys.length + 1)) (ys.length + 1))
    (hpal2 : Manacher.PalAt (encoded raw) (position ver - 2 * (ys.length + 1))
      (2 * (ys.length + 1)))
    {es : List Bool} {m w' : GalilScaffoldChainWatch.State}
    (hrun : GalilScaffoldChainWatch.Run (freshWatch ver cen ys b radius) es m)
    (hbr : BreakStep m w') (hmargin : negative w'.margin = false)
    (hscan : ∀ R : ℕ, (R : ℤ) = value m.machine.control.distance + 1 →
      Manacher.PalAt (encoded raw) (position ver) R) :
    4 * ((ys.length : ℤ) + 1) ≤ value m.machine.control.distance := by
  obtain ⟨xs, htr, -, -, hdx, -, hbal, hcm⟩ := fresh_break_ledger ver cen ys b radius hrc hrun hbr
  obtain ⟨-, -, hmar'⟩ := break_control hbr
  have hcw' : Canonical w'.margin := by
    obtain ⟨-, -, -, -, -, hw⟩ := hbr
    rw [hw]; exact inc_canonical _ hcm.2
  have hnn : 0 ≤ value w'.margin := by
    by_contra hlt
    have : negative w'.margin = true := (negative_iff _ hcw').mpr (by omega)
    rw [hmargin] at this; exact absurd this (by simp)
  by_contra hcorner
  -- the corner: `distance = 4*h - 1`
  set h := ys.length + 1 with hh
  have hd : value m.machine.control.distance = 4 * (h : ℤ) - 1 := by
    push_cast [hh] at hcorner hbal ⊢; linarith
  have hxs : xs.length = 4 * h - 1 := by
    have : (xs.length : ℤ) = 4 * (h : ℤ) - 1 := by rw [← hdx, hd]
    omega
  have hh1 : 1 ≤ h := by omega
  obtain ⟨hdisp, hmrep⟩ := watch_displacement hrun raw hvrep hvp
  have hd0 : value (freshWatch ver cen ys b radius).machine.control.distance = 0 := rfl
  have hposm : position m.machine.verifier = position ver + (4 * h - 1) := by
    have e : ((position m.machine.verifier : ℕ) : ℤ) - (position ver : ℤ) = 4 * (h : ℤ) - 1 := by
      have := hdisp; rw [hd0, hd] at this; exact this.trans (by ring)
    omega
  have hmp : m.machine.verifier.head.focus ≠ none := reads_present htr.reads hvp
  have hpred := watch_prediction_window hrun raw hvrep hvp cen b ys rfl (4 * h - 1) hposm
    (by omega)
  obtain ⟨-, hcanR, a, hsym, hne, -⟩ := hbr
  rw [hsym, hposm] at hpred
  have hmpos := (represented_position m.machine.verifier.head raw hmrep hmp).1
  have hrread : read (right m.machine.verifier) = (encoded raw)[position ver + 4 * h]? := by
    rw [represented_read _ raw (right_word _ raw hmrep hcanR) (right_present _ raw hmrep hmp hcanR),
      right_position _ hcanR hmpos, hposm,
      show position ver + (4 * h - 1) + 1 = position ver + 4 * h by omega]
  have hC := hscan (4 * h) (by push_cast; linarith)
  have hC4 := hC.2.2 (4 * h) le_rfl
  have hC2 := hC.2.2 (2 * h) (by omega)
  have hb1 := hpal1.1
  have hb2 := hpal2.1
  have hp1 := hpal1.2.2 h le_rfl
  have hp2 := hpal2.2.2 (2 * h) le_rfl
  rw [show position ver - h - h = position ver - 2 * h by omega,
    show position ver - h + h = position ver by omega] at hp1
  rw [show position ver - 2 * h - 2 * h = position ver - 4 * h by omega,
    show position ver - 2 * h + 2 * h = position ver by omega] at hp2
  apply hne
  rw [hrread, ← hC4, hp2, ← hp1, hC2, hpred]
  congr 1; omega

#print axioms fresh_break_places

/-! ## 4. The controller-level discharge -/

/-- `freshWatch` is literally the watch `GalilPrepConstruct.prep_segment_construct`
lands on (`s2.chain = .watch ⟨⟨ver, ready cen ys b⟩, inc radius, decFour^[h] (inc radius)⟩`). -/
theorem freshWatch_eq (ver : GalilScaffoldInputHead.PlaceHead) (cen : Fin 3) (ys : List (Fin 3))
    (b : Fin 3) (radius : Counter) (h : ℕ) (hh : ys.length + 1 = h) :
    (⟨⟨ver, GalilScaffoldChainConsume.ready cen ys b⟩, inc radius,
      GalilScaffoldChainCredits.decFour^[h] (inc radius)⟩ : GalilScaffoldChainWatch.State) =
      freshWatch ver cen ys b radius := by
  subst hh; rfl

open PalPeg.Program PalPeg.GalilStructuredSkeleton
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleLocal PalPeg.GalilInvPlus
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead
  GalilScaffoldChainVerifier
open PalPeg.GalilTraceCost PalPeg.GalilCostedFound PalPeg.GalilFoundLandingL

/-- The centre head of an `Inv` state represents the input. -/
theorem centreRep_of_inv {raw : List (Fin 2)} {c : Control} {r : GalilVM} (h : Inv raw c r) :
    GalilScaffoldInputTrace.Represents r.center.head raw ∧ r.center.head.focus ≠ none := by
  obtain ⟨Rad, last, hR⟩ := h.rest
  exact ⟨hR.2.1, hR.2.2.1⟩

/-- **`foundRouteMC_noshift'`.**  `foundRouteMC_noshift` with `hstage`,
`hcanon`, `hlast` and `hlag` discharged, and `hcenR` reduced to the
`InvScan` branch of `InvLP`.

New hypotheses, all produced by the found-cycle construction:
* `hwatch2` / `hes0` — the preparation lands on `freshWatch` with no matched
  comparison during it (`prep_segment_construct`: `bs`, `cs`, `dm` all
  `false`, verifier `sF.center` from `hch`);
* `hpal1` / `hpal2` — the candidate's palindromes about the found centre
  (`GalilCandidatePeriod.candidate_palAt`, with `h = ys.length + 1`);
* `hcenS` — the centre representation on the `InvScan` branch (`InvScan`
  carries no centre field). -/
theorem foundRouteMC_noshift' (centre : GalilVM → Fin 3)
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
      (afterCompare sF ⟨left sF.left, right sF.right, ch⟩ vq) c2 s2)
    (cen : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (hwatch2 : s2.chain = .watch (freshWatch sF.center cen ys b sF.radius))
    (hes0 : es.count true = 0)
    (hpal1 : PalAt (encoded raw) (position r.center - (ys.length + 1)) (ys.length + 1))
    (hpal2 : PalAt (encoded raw) (position r.center - 2 * (ys.length + 1)) (2 * (ys.length + 1)))
    {c3 : Control} {s3 : GalilVM}
    (hseg : WatchSeg (PofC centre place entry raw) qq first 2048 c2 s2 c3 s3)
    (hm3 : c3.mode = .scan) (hr3 : c3.replaying = false) (hc3 : c3.clock = 1)
    (w3 : GalilScaffoldChainWatch.State) (hs3 : s3.chain = .watch w3) (hav3 : canRight s3.right)
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
      sT.right = (afterCompare s3 vs3 vq3).right := by
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
    rw [afterCompare_center] at h0; exact h0
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
  refine foundRouteMC_noshift centre place entry qq first raw hex hI hlive hcenR hseg0 hmF hrF hcF
    havF hidle vq hq hfound hmt ch hch hchne oF hoF hprepSeg hseg hm3 hr3 hc3 w3 hs3 hav3 vs3 vq3
    hcmp3 hmt3 hq3 o3 ho3 w3' hbroken hmargin hlast hlag hcanon (fun R' hR' => hst R' ?_)
  have hv := hR'.2
  rw [afterCompare_radius, inc_value, hrad2, hrad1, afterCompare_radius, inc_value, hes0] at hv
  rw [hdR]
  push_cast at hv ⊢
  linarith

#print axioms freshWatch_eq
#print axioms centreRep_of_inv
#print axioms foundRouteMC_noshift'

end PalPeg.GalilNoShiftStage
