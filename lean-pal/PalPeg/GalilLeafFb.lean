import PalPeg.GalilLeafMismatch
import PalPeg.GalilFallbackCost

/-!
# Discharging the `hfb` residue of `GalilLeafMismatch.hmismatch_of_residues`

`GalilLeafMismatch.fallbackRouteMC2_of_mismatch` takes the tick bound of the
fallback phase as a residue `hfb`, quantified over *every* run of length
`1 + (n+1)` out of the mismatching state.  In that shape the residue is false:
`t` and `c'` are unconstrained there, so a scan state with `value t.length = 1`
and a long input tail carries `SoundScanNR`-runs of arbitrarily many ticks.

The fix is not to restate the residue but to **carry the bound along the chain
that creates `n`**.  `GalilFallbackCost.fallback_ticks_le` already bounds the
`copy → replayStart` chain, but only for `Steps`; `fallback_landing_len` runs
the `StepsAll` chain (`copy_home_start_All`, `fpp_then_markEnd_All`,
`choose_then_rewind_All`) whose `n` is existential and unbounded.  Both chains
have the *same* phase lengths, the only non-constant one being the number of
FPP quanta, which `GalilFallbackCost.fpp_phase_vm_le` bounds.  So this module
re-runs the `All` chain with the bound attached:

  `fpp_then_markEnd_All_le` → `fallback_chain_All_le` → `fallback_to_scan_All_le`
  → `scan_fallback_cycle_All_le` → `fallback_landing_len_le`

and then re-proves the mismatch leaf without `hfb`:
`fallbackRouteMC2_of_mismatch'`, `hmismatch_of_residues'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.GalilLeafFb

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.GalilStructuredSkeleton PalPeg.GalilRunSkeleton
open PalPeg.GalilOracleDischarge PalPeg.GalilOracleGlueB PalPeg.GalilGlueBLeaves
open PalPeg.GalilOracleLocal PalPeg.GalilInvPlus PalPeg.GalilInvPlus2
open PalPeg.GalilCheckpoints PalPeg.GalilTraceCost PalPeg.GalilLexMeasure
open PalPeg.GalilOracleMC PalPeg.GalilBranchInvariants2 PalPeg.GalilSegmentConstruct
open PalPeg.GalilOracleM PalPeg.GalilOracleMC2 PalPeg.GalilFinalAssembly2
open PalPeg.GalilLeafMismatch
open Manacher GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- `fpp_phase_scheduled_le` with the sharper bound `1584·|w|+830` on the number
of quanta: a quantum runs at least one instruction (`0 < q`), so the instruction
count is itself a bound on the quantum count.  The `⌈·/q⌉+1` of
`fpp_phase_scheduled_le` loses one tick at `q = 1`, which is exactly the tick
the `hfb` constant does not have. -/
theorem fpp_phase_scheduled_le' (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ) (c : Control) (hm : c.mode = .fpp)
    (x : FppControl.State) (hx : x.mode = .run) (w : List (Fin 3))
    (hp : x.program = ⟨fppInitial w, false⟩) :
    FppOutcomeLe q first onLetter leftFirst delay c x (1584*w.length+830) := by
  obtain ⟨v, _, _, _, _, hrun⟩ := fpp_scheduled w
  apply fpp_phase_lift_le q first onLetter leftFirst delay c hm x hx (1584*w.length+830) v
  rw [hp]
  apply hrun
  rw [count_true_replicate]
  exact Nat.le_mul_of_pos_right _ hq

/-- `fpp_phase_vm_le` with the sharper bound. -/
theorem fpp_phase_vm_le' (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : GalilScaffoldController.Control) (hm : c.mode = .fpp) (s : GalilVM)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (p : GalilScaffoldControl.Machine 9) (y : FppControl.State),
      n ≤ 1584*w.length+830 ∧
      Steps (Frame.pull fppLens (fppFrame q first onLetter leftFirst)) delay (n+1) ⟨c, s⟩
        ⟨{c with mode := .markEnd}, {s with fpp := y}⟩ ∧
      y.program = markNew p first ∧ y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧
      y.finalStage = s.fpp.finalStage ∧ p.done = true ∧
      GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate ((n+1)*q) true) p := by
  obtain ⟨n, p, y, hb, hs, hprog, hmode, hw, hk, hf, hd, hrun⟩ :=
    fpp_phase_scheduled_le' q hq first onLetter leftFirst delay c hm s.fpp hx w hp
  exact ⟨n, p, y, hb, steps_pull fppLens _ delay (n+1) c _ s y hs, hprog, hmode, hw, hk, hf, hd, hrun⟩

/-- `fpp_then_markEnd_All` with the number of FPP quanta bounded, i.e.
`fpp_then_markEnd_le` transferred with `stepsAll_transfer_*` instead of
`steps_transfer_*`. -/
theorem fpp_then_markEnd_All_le (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .fpp) (s : GalilVM) (hi : ShiftIdle s)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hw : 1 ≤ w.length)
    (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (y : FppControl.State), n ≤ 1584*w.length+830 ∧
      StepsAll (galilFrameS P q first) delay NoScan (n+1 + (w.length-1+1)) ⟨c, s⟩
        ⟨{c with mode := .choose, odd := false}, {s with fpp := y}⟩ ∧
      GalilScaffoldTape.denote (marksTape y) = Function.update (GalilFppMarkedLayout.marks w) 1 first ∧
      GalilScaffoldTape.head (marksTape y) = w.length ∧
      y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧ y.finalStage = s.fpp.finalStage ∧
      ShiftIdle {s with fpp := y} := by
  obtain ⟨v, hpc, hpos, ht7, ht8, hsched⟩ := fpp_scheduled w
  obtain ⟨n, p, y1, hb, hs1, hprog, hmode, hwk, hwork, hfin, hd, hrun⟩ :=
    fpp_phase_vm_le' q hq first (fun _ => True) (fun _ => True) delay c hm s hx w hp
  obtain ⟨hg1, hi1⟩ := stepsAll_transfer_fpp_S P q first delay (n+1) hm hi hs1 (fun h0 => by cases h0)
  have hpv : p = ⟨v, true⟩ := fpp_outcome_program q w s.fpp hp v hsched n p hd hrun
  subst hpv
  obtain ⟨hden, hhead⟩ := marks_after_fpp first w v hpos ht8
  have hden1 : GalilScaffoldTape.denote (marksTape y1) = Function.update (GalilFppMarkedLayout.marks w) 1 first := by
    show GalilScaffoldTape.denote (y1.program.config.tapes 8) = _
    rw [hprog]; exact hden
  have hhead1 : GalilScaffoldTape.head (marksTape y1) = 2 := by
    show GalilScaffoldTape.head (y1.program.config.tapes 8) = 2
    rw [hprog]; exact hhead
  have hm1 : ({c with mode := .markEnd} : Control).mode = .markEnd := rfl
  have hne : ∀ j, j < w.length - 1 →
      GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
        (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + j) ≠ 5 := by
    intro j hj
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + j) ≠ 5
    rw [hden1, hhead1, Function.update_of_ne (by omega)]
    exact marks_no_end w (2+j) (by omega) (by omega)
  have hend : GalilScaffoldTape.denote (marksTape ({s with fpp := y1} : GalilVM).fpp)
      (GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1)) = 5 := by
    show GalilScaffoldTape.denote (marksTape y1) (GalilScaffoldTape.head (marksTape y1) + (w.length - 1)) = 5
    rw [hden1, hhead1, Function.update_of_ne (by omega), show 2 + (w.length - 1) = w.length + 1 by omega]
    exact marks_end w
  have hpos' : 0 < GalilScaffoldTape.head (marksTape ({s with fpp := y1} : GalilVM).fpp) + (w.length - 1) := by
    show 0 < GalilScaffoldTape.head (marksTape y1) + (w.length - 1)
    rw [hhead1]; omega
  obtain ⟨y2, hs2, hsame, hhead2⟩ := markEnd_phase_vm first (fun _ => True) (fun _ => True) delay
    {c with mode := .markEnd} hm1 {s with fpp := y1} (w.length - 1) hne hend hpos'
  obtain ⟨hg2, hi2⟩ :=
    stepsAll_transfer_markEnd_S P q first delay (w.length - 1 + 1) hm1 hi1 hs2 (fun h0 => by cases h0)
  refine ⟨n, y2, hb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hi2⟩
  · exact stepsAll_trans hg1 hg2
  · rw [hsame.denote]; exact hden1
  · rw [hhead2]
    show GalilScaffoldTape.head (marksTape y1) + (w.length - 1) - 1 = w.length
    rw [hhead1]; omega
  · rw [hsame.mode]; exact hmode
  · rw [hsame.walker]; exact hwk
  · rw [hsame.work]; exact hwork
  · rw [hsame.finalStage]; exact hfin

#print axioms fpp_phase_scheduled_le'
#print axioms fpp_then_markEnd_All_le

/-- `fallback_chain_All` with its tick count bounded, i.e. `fallback_ticks_le`
in the `StepsAll`/`NoScan` world.  Every phase length is the same as in
`fallback_ticks_le`, so the arithmetic is unchanged. -/
theorem fallback_chain_All_le (P : Shared) (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM) (hi : ShiftIdle s)
    (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let w := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius w
    ∃ (n : ℕ) (y : RewindVM),
      StepsAll (galilFrameS P q first) delay NoScan n ⟨c, s⟩
        ⟨{c with mode := .replayStart, odd := oddAt false (w.length - (2*r+1)), pair := pairAt (2*r)},
          rewindLens.set s y⟩ ∧
      n ≤ 1588*(ℓ+1) + 835 ∧
      y.left = GalilScaffoldInputHead.left^[2*r] s.right ∧
      y.center = GalilScaffoldInputHead.left^[r] s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat (2*r+1) ∧ y.radius = GalilScaffoldCounter.ofNat r ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program ∧ ShiftIdle (rewindLens.set s y) := by
  intro w r
  have hwl : w.length ≤ ℓ+1 := by
    show ((GalilScaffoldPlace.stream p).take (ℓ+1)).length ≤ ℓ+1
    rw [List.length_take]; omega
  have hw : 1 ≤ w.length := by
    show 1 ≤ ((GalilScaffoldPlace.stream p).take (ℓ+1)).length
    rw [List.length_take]
    have : 0 < (GalilScaffoldPlace.stream p).length := List.length_pos_iff.mpr hne
    omega
  have hwne : w ≠ [] := by
    intro h
    rw [h] at hw
    simp at hw
  have hr1 : 2*r+1 ≤ w.length := (chosen_spec w hwne).1
  obtain ⟨t, hg1, hmode, hprog, _, hi1⟩ :=
    copy_home_start_All P q first delay c hm s hi old p length hc ℓ hv hs
  have hm1 : ({c with mode := .fpp} : Control).mode = .fpp := rfl
  obtain ⟨n2, y2, hb2, hg2, hden2, hhead2, _, _, _, _, hi2⟩ :=
    fpp_then_markEnd_All_le P q hq first delay {c with mode := .fpp} hm1 {s with fpp := t} hi1 hmode w hw hprog
  have hm2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).mode = .choose := rfl
  have ho2 : ({({c with mode := .fpp} : Control) with mode := .choose, odd := false} : Control).odd = false := rfl
  obtain ⟨y3, hg3, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩ :=
    choose_then_rewind_All P q first h7 h8 delay _ hm2 ho2 {({s with fpp := t} : GalilVM) with fpp := y2} hi2
      w hw heven r rfl hden2 hhead2
  have hlink : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length = w.length := rfl
  refine ⟨_, y3, stepsAll_trans hg1 (stepsAll_trans hg2 hg3), ?_, hl, hc3, hr3, hlen, hrad, hprog3, hi3⟩
  omega

#print axioms fallback_chain_All_le

/-- `fallback_to_scan_All` with the tick bound of `fallback_chain_All_le`. -/
theorem fallback_to_scan_All_le (onLetter leftFirst guard : GalilVM → Prop)
    (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM)
    (hi : ShiftIdle s) (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let win := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius win
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      (∀ Q : State GalilVM → Prop, (∀ st : State GalilVM, st.ctl.mode ≠ .scan → Q st) →
        Q ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < r), odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)}, t⟩ →
        StepsAll (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay Q (n+1) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < r), odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)}, t⟩) ∧
      n + 1 ≤ 1588*(ℓ+1) + 836 ∧
      t.left = GalilScaffoldInputHead.left^[r] s.right ∧ t.right = GalilScaffoldInputHead.left^[r] s.right ∧
      t.center = GalilScaffoldInputHead.left^[r] s.right ∧
      t.replay = GalilScaffoldCounter.ofNat r ∧ t.radius = GalilScaffoldCounter.reset ∧
      t.length = GalilScaffoldCounter.ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < r → o = c.output) ∧
      (r = 0 → (onLetter t → (o = true ↔ leftFirst t)) ∧ (¬ onLetter t → o = c.output)) ∧
      t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset ∧
      t.lower = GalilScaffoldCounter.reset ∧ t.chain = .idle := by
  intro win r
  obtain ⟨n, y, hg, hb, hl, hc', hr, hlen, hrad, hprog, hi'⟩ :=
    fallback_chain_All_le (galilShared onLetter leftFirst guard bs bf rs centre place entry) q hq first h7 h8 delay c hm s hi old p length hc ℓ hv hs hne heven
  have hm' : ({c with mode := .replayStart, odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)} : Control).mode = .replayStart := rfl
  obtain ⟨o, t, ht, hrep, hR, hL, hC, hrad', hlen', hrem, hcyc, hfpp, hw, ho, ho0, hsearch, hlower, _⟩ :=
    replayStart_tick onLetter leftFirst guard bs bf rs centre place entry q first delay _ hm' (rewindLens.set s y)
  have hrad'' : (rewindLens.set s y).radius = GalilScaffoldCounter.ofNat r := hrad
  have hcen : (rewindLens.set s y).center = GalilScaffoldInputHead.left^[r] s.right := hc'
  rw [hrad'', positive_ofNat] at ht ho
  have htS := tick_S_of_tick _ q first delay ht (by rw [hm']; decide)
  refine ⟨n, o, t, fun Q hQ hQend => stepsAll_trans (stepsAll_mono (fun st h0 => hQ st h0) hg)
      (.succ (hQ _ (fun h0 => by cases h0)) htS (.zero _ hQend)), by omega, ?_, ?_, ?_, ?_, hrad', hlen', hw, ?_, ?_, ?_,
    (fun hr0 => ho0 (by rw [hrad'', positive_ofNat]; simp [hr0])), hsearch, hlower, hw⟩
  · rw [hL, hcen]
  · rw [hR, hcen]
  · rw [hC, hcen]
  · rw [hrep, hrad'']
  · rw [hfpp]; exact hprog
  · rw [shiftIdle_iff, hrem]
    show GalilScaffoldCounter.positive s.remaining = false
    exact (shiftIdle_iff s).1 hi
  · intro hr0
    exact ho (by simpa using hr0)

#print axioms fallback_to_scan_All_le

/-- `scan_fallback_cycle_All` with the tick bound carried. -/
theorem scan_fallback_cycle_All_le (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s) (place s)
      s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    (p : GalilScaffoldPlace.Place)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      (∀ Q : State GalilVM → Prop, (∀ st : State GalilVM, st.ctl.mode ≠ .scan → Q st) → Q ⟨c, s⟩ →
        Q ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream p).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)))}, t⟩ →
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay Q (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream p).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)))}, t⟩) ∧
      n + 1 ≤ 1588*(ℓ+1) + 836 ∧
      t.left = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.center = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))] (right s.right) ∧
      t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1))) ∧ t.radius = reset ∧
      t.length = ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)) → o = c.output) ∧
      (chosenRadius ((GalilScaffoldPlace.stream p).take (ℓ+1)) = 0 → (onLetter t → (o = true ↔ leftFirst t)) ∧ (¬ onLetter t → o = c.output)) ∧
      t.search = GalilScaffoldSearchFinish.begin reset reset ∧ t.lower = reset := by
  -- the mismatch tick
  have hmis' : ¬ (galilFrame (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).matched
      (scanLens.set s vs) := by
    intro h0
    apply hmis
    have h1 : read (scanLens.get (scanLens.set s vs)).left = read (scanLens.get (scanLens.set s vs)).right := h0
    rw [scanLens.get_set] at h1
    have h2 : read vs.left = read vs.right := h1
    rw [hl, hrr] at h2
    exact h2
  have hcmpS : (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).compare
      s (afterMismatchB s vs vq) :=
    ⟨vs, vq, false, hl, hrr, Iff.intro (fun h0 => by cases h0) (fun h0 => absurd h0 hmis'), hq, hch, rfl⟩
  have hmisS : ¬ (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).matched
      (afterMismatchB s vs vq) := by
    intro h0
    apply hmis
    have h1 : read (afterMismatchB s vs vq).left = read (afterMismatchB s vs vq).right := h0
    rw [afterMismatchB_left, afterMismatchB_right, afterMismatch_left, afterMismatch_right, hl, hrr] at h1
    exact h1
  have hav' : (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first).available s := hav
  have ht1 : Tick (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay ⟨c, s⟩
      ⟨{c with clock := delay, mode := .copy},
        {afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}}⟩ :=
    .scan_fallback c s _ _ hm (Or.inr hav') hc hcmpS hmisS (Or.inr (not_shiftGuard_afterMismatchB _ _ _ _ _ hch hg)) hr ⟨p, rfl⟩
  have hm2 : ({c with clock := delay, mode := .copy} : Control).mode = .copy := rfl
  have hi2 : ShiftIdle {afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}} := by
    rw [shiftIdle_iff] at hi ⊢
    show positive (afterMismatchB s vs vq).remaining = false
    rw [afterMismatchB_remaining]
    exact hi
  have hcan' : Canonical (afterMismatchB s vs vq).length := by rw [afterMismatchB_length, afterMismatch_length]; exact hcan
  have hv' : value (afterMismatchB s vs vq).length = ℓ := by rw [afterMismatchB_length, afterMismatch_length]; exact hv
  obtain ⟨n, o, t, hst, hb, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower, _⟩ :=
    fallback_to_scan_All_le onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry q hq0 first
      h7 h8 delay _ hm2 _ hi2 (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length hcan' ℓ hv'
      rfl hne heven
  have hright : ({afterMismatchB s vs vq with fpp := FppControl.beginFallback (afterMismatchB s vs vq).fpp.program p (afterMismatchB s vs vq).length, chain := .idle, search := {(afterMismatchB s vs vq).search with mode := .idle}} : GalilVM).right = right s.right := by
    show (afterMismatchB s vs vq).right = _
    rw [afterMismatchB_right, afterMismatch_right, hrr]
  rw [hright] at hl' hR hC
  exact ⟨n, o, t, fun Q hQ hQs hQend => stepsAll_trans (.succ hQs ht1 (.zero _ (hQ _ (fun h0 => by cases h0)))) (hst Q hQ hQend),
    hb, hl', hR, hC, hrep, hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower⟩

#print axioms scan_fallback_cycle_All_le

/-- `fallback_landing_len` with the tick bound carried. -/
theorem fallback_landing_len_le (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop)
    (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (hq0 : 0 < q) (first : Fin 9) (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hi : ShiftIdle s) (hav : canRight s.right)
    (vs : ScanVM) (vq : SearchVM) (hl : vs.left = left s.left) (hrr : vs.right = right s.right)
    (hmis : read (left s.left) ≠ read (right s.right))
    (hq : searchEffect (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry)
      false s vq)
    (hch : chainAt false (decide (vq.search.mode = .found)) (vq.dp.config.tapes 11) (centre s) (place s)
      s.center s.radius s.chain vs.chain)
    (hg : ¬ shiftGuardVM (afterMismatch s vs vq))
    {raw : List (Fin 2)} (hrep : GalilScaffoldInputTrace.Represents (right s.right).head raw)
    (hfoc : (right s.right).head.focus ≠ none)
    (hcan : Canonical s.length) (ℓ : ℕ) (hv : value s.length = ℓ)
    (heven : ∀ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' →
      ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length % 2 = 0)
    (honL : onLetter = onLetterVM raw) (hlF : leftFirst = leftFirstVM) (hout : OutputRel raw c s) :
    ∃ (a : Fin 2) (xs rs' q' : List (Fin 2)),
      right s.right = represent ⟨a :: xs,(right s.right).gap⟩ (rs'.map some) q' ∧
      raw = (a :: xs).reverse ++ rs' ++ q' ∧
      ∃ (n : ℕ) (o : Bool) (t : GalilVM),
        StepsAll (galilFrameS (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first) delay (SoundScanNR raw) (1 + (n+1)) ⟨c, s⟩
          ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))), odd := oddAt false (((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length - (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))+1)), pair := pairAt (2*chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))}, t⟩ ∧
        n + 1 ≤ 1588*(ℓ+1) + 836 ∧
        Restarted raw t 0 reset ∧
        position t.center = position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) ∧
        Manacher.PalAt (encoded raw) (position (right s.right) - chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)))
          (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        (∀ r', 2*r'+1 ≤ ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)).length →
          Manacher.PalAt (encoded raw) (position (right s.right) - r') r' →
          r' ≤ chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        t.replay = ofNat (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))) ∧
        ShiftIdle t ∧ t.chain = .idle ∧
        t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) ∧
        t.center = t.right ∧ t.length = ofNat 1 := by
  let w0 : GalilScaffoldChainWatch.State :=
    ⟨⟨right s.right, GalilScaffoldChainConsume.ready 0 [] 0⟩, reset, reset⟩
  obtain ⟨a, xs, rs', q', hdec, hraw, hpal, hmax, h, hmoves, hhrep, hhfoc, hhpos, _⟩ :=
    fallback_replay (⟨s.center, s.left, right s.right, w0, s.cycle, s.radius⟩ : OnlyCompareState)
      hrep hfoc s.length hcan ℓ hv
  refine ⟨a, xs, rs', q', hdec, hraw, ?_⟩
  obtain ⟨n, o, t, hst, hb, hl', hR, hC, hrep', hrad, hlen, hw, hprog, hi', ho, ho0, hsearch, hlower⟩ :=
    scan_fallback_cycle_All_le onLetter leftFirst rs centre place entry q hq0 first h7 h8 delay c hm hr hc s hi hav
      vs vq hl hrr hmis hq hch hg ⟨a :: xs,(right s.right).gap⟩ hcan ℓ hv (stream_ne_nil _ _ _)
      (heven a xs rs' q' hdec)
  have hh : GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))]
      (right s.right) = h := (leftMoves_eq hmoves).symm
  have hRit : t.right = GalilScaffoldInputHead.left^[chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1))] (right s.right) := hR
  have hCR : t.center = t.right := hC.trans hR.symm
  rw [hh] at hl' hR hC
  have hRst : Restarted raw t 0 reset := by
    refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_, hlower, ofNat_canonical 0, by rw [reset_eq_ofNat, ofNat_value]; simp⟩
    · rw [hC]; exact hhrep
    · rw [hC]; exact hhfoc
    · rw [hC, hl', hR]; exact scan_initial raw h hhrep hhfoc
    · rw [hrad, reset_eq_ofNat]; exact ⟨ofNat_canonical 0, ofNat_value 0⟩
    · rw [hlen]; exact ofNat_canonical 1
    · rw [hsearch, hrad]
  refine ⟨n, o, t, ?_, hb, hRst, by rw [hC]; exact hhpos, hpal, hmax, hrep', hi', hw, hRit, hCR, hlen⟩
  refine hst (SoundScanNR raw) (fun st hns hsc => absurd hsc hns) (fun _ _ => hout) ?_
  intro _ hrepl
  have hr0 : chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).take (ℓ+1)) = 0 := by
    simp at hrepl; omega
  obtain ⟨_, _, _, hscan, _⟩ := hRst
  intro hout' k hk hk2 hrk
  refine output_sound raw t c.output o hscan k hk hk2 hrk ?_ hout'
  have := ho0 hr0
  rw [honL, hlF] at this
  exact this

#print axioms fallback_landing_len_le

/-! ## The mismatch leaf without the `hfb` residue -/

/-- `GalilLeafMismatch.fallbackRouteMC2_of_mismatch` with residue 2 discharged. -/
theorem fallbackRouteMC2_of_mismatch' (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM)
    (hIC : InvLPC w c r)
    (hs : SegReachedW centreC placeC entry q first w c r c' t)
    (hnr : c'.replaying = false) (hc1 : c'.clock = 1) (hav : canRight t.right)
    (hmis : read (left t.left) ≠ read (right t.right))
    -- residue 1: the DP/period pack at the mismatch
    (hdp : ∀ Rad : ℕ, ScanInvariant w (position t.center) Rad t.left t.right → DpPack w t Rad)
    -- residue 3: the mismatch place is still inside the target
    (hpos : position (right t.right) ≤ 2 * m - 1) :
    FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t := by
  obtain ⟨es, hw⟩ := hs.2
  have hK : FallbackCounters w t :=
    fallbackCounters_of_seg _ q first 2048 hw hs.1.center hIC.1.1.2 hav
  have hT : FallbackTick centreC placeC entry w t :=
    fallbackTick_of_mismatch centreC placeC entry w (hsearch w) t hs.1.idle hs.1.search
  obtain ⟨k0, hrun⟩ := hs.1.run
  have hout : OutputRel w c' t := stepsAll_last hrun hs.1.mode hnr
  obtain ⟨⟨Rad, hscan, hRR, hS⟩, hcan, ℓ, hv, heven⟩ := hK
  obtain ⟨vs, vq, hl, hrr, hqe, hch, hg⟩ := hT.data
  have hrep : GalilScaffoldInputTrace.Represents (right t.right).head w :=
    right_word t.right w hscan.rightRep hav
  have hfoc : (right t.right).head.focus ≠ none :=
    right_present t.right w hscan.rightRep hscan.rightPresent hav
  obtain ⟨a, xs, rs', q', hdec, hraw, n, o, sT, hstA, hfbB, hRst, hposT, hpal, hmax, hrepT, hsiT, hchT,
      hRit, hCR, hlenT⟩ :=
    fallback_landing_len_le (onLetterVM w) leftFirstVM (restartVM entry) centreC placeC entry q hq0
      first h7 h8 2048 c' hs.1.mode hnr hc1 t hs.1.shiftIdle hav vs vq hl hrr hmis hqe hch hg
      hrep hfoc hcan ℓ hv heven rfl rfl hout
  obtain ⟨a₀, ls₀, rs₀, q₀, gap₀, lower, span, y, hraw₀, hC₀, hspan, hres, hidle, hlow⟩ :=
    hdp Rad hscan
  have hkC : Rad < position t.center := radius_lt_centre hscan
  have hrpos : position (right t.right) = position t.right + 1 :=
    right_position t.right hav (represented_position _ w hscan.rightRep hscan.rightPresent).1
  have mkD : ∀ RR : ℕ,
      RR = chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right t.right).gap⟩).take (ℓ+1)) →
      FppData w t (n+1) RR := by
    intro RR hRR'
    exact ⟨Rad, ℓ, a, xs, rs', q', a₀, ls₀, rs₀, q₀, gap₀, lower, span, y,
      hscan, hRR, hS, hv, hkC, hdec, hraw, hraw₀, hC₀, hspan, hres, hidle, hlow, hRR', hfbB⟩
  have hprog : position t.center < position sT.center :=
    PalPeg.GalilCycleProgress.fallback_progress w hs.1.minv hnr hscan hRR hS hav hmis a xs rs' q'
      hdec ℓ hv hpal hmax hposT
  have hL := leftmost_after_fallback_landing w hs.1.minv hnr hscan hRR hS hav hmis a xs rs' q'
    hdec ℓ hv hpal hmax hposT
  have hSpan : SpanRep sT := spanRep_of_restarted_one hRst hlenT
  rcases Nat.eq_zero_or_pos
      (chosenRadius ((GalilScaffoldPlace.stream ⟨a :: xs,(right t.right).gap⟩).take (ℓ+1)))
    with hz | hz
  · refine FallbackRouteMC2.landed (n+1) _ sT hstA (mkD 0 hz.symm) ?_ hCR ?_ hSpan hprog hpos
    · rw [hposT, hz]
    · have htrp : sT.replay = reset := by rw [hrepT, hz]; rfl
      refine inv_of_parts hRst ?_ ⟨rfl, by simp [hz], rfl⟩ (frontier_of_reset htrp)
        (replayRest_of_reset htrp) hsiT
      exact minv_after_fallback hRst hrepT (by rw [hposT, hrpos]) (by rw [← hrpos]; exact hL) rfl
  · refine FallbackRouteMC2.replaying (n+1) _ _ sT hstA (mkD _ rfl) ?_ hSpan hposT hCR hprog hpos
    exact
      { pos := hz
        rest := hRst
        mode := rfl
        clock := rfl
        replaying := by simp [hz]
        replay := hrepT
        minv := minv_after_fallback hRst hrepT (by rw [hposT, hrpos])
          (by rw [← hrpos]; exact hL) rfl
        frontier := frontier_after_fallback' hRit hrepT hpal
        shiftIdle := hsiT }

/-- `GalilLeafMismatch.hmismatch_of_residues` with residue 2 discharged. -/
theorem hmismatch_of_residues' (entry q : ℕ) (hq0 : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8)
    (hsearch : ∀ (w : List (Fin 2)) (s : GalilVM), SearchReady (searchLens.get s) →
      ∀ a : Bool, ∃ v, searchEffect (PofC centreC placeC entry w) a s v)
    (hdp : ∀ (w : List (Fin 2)) (t : GalilVM) (Rad : ℕ),
      ScanInvariant w (position t.center) Rad t.left t.right → DpPack w t Rad)
    (hpos : ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t → canRight t.right →
      position (right t.right) ≤ 2 * m - 1) :
    ∀ (w : List (Fin 2)) (m : ℕ) (c : Control) (r : GalilVM) (c' : Control) (t : GalilVM),
      1 ≤ m → m ≤ w.length → InvLPC w c r → position r.right ≤ 2 * m - 1 →
      SegReachedW centreC placeC entry q first w c r c' t →
      c'.replaying = false → c'.clock = 1 → canRight t.right →
      read (left t.left) ≠ read (right t.right) →
      FallbackRouteMC2 (PofC centreC placeC entry w) q first w m c r c' t := by
  intro w m c r c' t hm1 hmle hIC hrt hs hnr hc1 hav hmis
  exact fallbackRouteMC2_of_mismatch' entry q hq0 first h7 h8 hsearch w m c r c' t hIC hs hnr hc1
    hav hmis (fun Rad hi => hdp w t Rad hi)
    (hpos w m c r c' t hm1 hmle hIC hrt hs hav)

#print axioms fallbackRouteMC2_of_mismatch'
#print axioms hmismatch_of_residues'

end PalPeg.GalilLeafFb
