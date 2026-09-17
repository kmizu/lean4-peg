import PalPeg.CloseoutPackRun37

/-!
# `H_advance` is a carried datum, not an obligation

`CloseoutPackRun31.chainRound_tick` takes

```
hA : H_advance w x.vm
```

— "after the immediate consume the chain predicts the next encoded symbol one
period behind" — and `CloseoutPackRun37` already proves that from a **carried**
datum:

| name | file | content |
|---|---|---|
| `ReadsInv raw C R h used w0` | `CloseoutPackRun37:476` | `w0.machine.control = run o.shifted.machine.control extra` for the round's origin `o`, with `extra.length = used` |
| `h_advance_of_readsInv` | `CloseoutPackRun37:483` | `H_advance`'s conclusion, by `GalilGoodLag.origin_prediction_index` at the one-longer continuation |
| `readsInv_immediate` | `CloseoutPackRun37:517` | `ReadsInv` steps with the immediate consume of a `Good` chain |

So the mathematics is done; what was missing is that `ReadsInv` mentions the
round's `(C, R, used)`, which `H_advance` quantifies over.  `ReadsRun` below is
the state-local closure of `ReadsInv` over all rounds at a state, and
`h_advance_of_readsRun` is then one line.

`chainRound_tick_R` is `chainRound_tick` with `H_advance` replaced by
`ReadsRun` — a single-state datum in the same family as `ChainRound` itself,
so it belongs in the run-carried bundle rather than beside it.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRoundReads

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutLPack3 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.GalilRoundPeriod PalPeg.GalilChainCoupling PalPeg.CloseoutPackRun31
open PalPeg.CloseoutPackRun37

/-- **(NAMED) the `Reads`-trace datum, closed over the rounds at one state.**
Every round the state is in carries its origin's sweep witness. -/
def ReadsRun (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch →
    ∀ C R used : ℕ, RoundScan w C R (periodLength wch) used s wch →
      ReadsInv w C R (periodLength wch) used wch

/-- **`H_advance` from `ReadsRun`.**  `h_advance_of_readsInv` at the round the
state is already in. -/
theorem h_advance_of_readsRun {w : List (Fin 2)} {s : GalilVM} (hRR : ReadsRun w s) :
    H_advance w s := by
  intro C R used w0 hI hg hend
  exact h_advance_of_readsInv hI (hRR w0 hI.chain C R used hI) hg hend

/-- **(NAMED) `ReadsRun` premised exactly like `ChainRound`.**  This is the
shape the tick lemma consumes: the sweep witness is only ever read inside the
`scan_match` branch, where `scan` / not-replaying / `periodOnly` are all in
scope. -/
def ReadsRound (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.scan → c.replaying = false → s.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch →
    ∀ C R used : ℕ, RoundScan w C R (periodLength wch) used s wch →
      ReadsInv w C R (periodLength wch) used wch

/-- `ReadsRun` is the unconditional form. -/
theorem readsRound_of_readsRun {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (h : ReadsRun w s) : ReadsRound w c s := fun _ _ _ => h

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`chainRound_tick` with `H_advance` replaced by the carried `ReadsRun`.** -/
theorem chainRound_tick_R {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hRR : ReadsRun w x.vm)
    (hS : H_shiftDone centre place entry q first w x.ctl x.vm)
    (hB : H_birth w x.ctl x.vm y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ChainRound w y.ctl y.vm :=
  chainRound_tick centre place entry q first hCR (h_advance_of_readsRun hRR) hS hB hblk h

/-- **`chainRound_tick` with `H_advance` replaced by the carried `ReadsRound`.**
The 200-line case analysis is `CloseoutPackRun31.chainRound_tick` verbatim; the
only change is the single line that consumed `hA`, which now reads the round's
sweep witness off `ReadsRound` and applies
`CloseoutPackRun37.h_advance_of_readsInv`. -/
theorem chainRound_tick_RR {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hRR : ReadsRound w x.ctl x.vm)
    (hS : H_shiftDone centre place entry q first w x.ctl x.vm)
    (hB : H_birth w x.ctl x.vm y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ChainRound w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h with
  | init c s t hm hi =>
    intro _ _ _ wch hchain
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    rw [hch] at hchain
    cases hchain
  | scan_wait c s t hm hav hb =>
    intro hm' hr' hpo' wch hchain
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · have hne : s.chain ≠ ChainVM.idle := by rw [hw0]; intro h0; cases h0
      have hb0 : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
        unfold chainBorn
        cases h0 : s.chain <;> simp_all [ChainVM.isIdle]
      rw [hb0, if_neg (by decide)] at hpo hcyc
      obtain ⟨C, R, used, hI⟩ := hCR hm' hr' (hpo ▸ hpo') w0 hw0
      have hwe := internal_of_zero hI.caught.lagZero hint
      subst hwe
      exact ⟨C, R, used, roundScan_transport hI hchain hl hr hcyc⟩
    · exact hB (Or.inr hnot) hpo' wch hchain
  | scan_count c s t hm hav hc hb =>
    intro hm' hr' hpo' wch hchain
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · have hne : s.chain ≠ ChainVM.idle := by rw [hw0]; intro h0; cases h0
      have hb0 : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
        unfold chainBorn
        cases h0 : s.chain <;> simp_all [ChainVM.isIdle]
      rw [hb0, if_neg (by decide)] at hpo hcyc
      obtain ⟨C, R, used, hI⟩ := hCR hm' hr' (hpo ▸ hpo') w0 hw0
      have hwe := internal_of_zero hI.caught.lagZero hint
      subst hwe
      exact ⟨C, R, used, roundScan_transport hI hchain hl hr hcyc⟩
    · exact hB (Or.inr hnot) hpo' wch hchain
  | restart c s t hm hb =>
    intro _ _ _ wch hchain
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    cases hchain
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    intro hm' hr' hpo' wch hchain
    cases hrep : c.replaying with
    | true => exact hB (Or.inl hrep) hpo' wch hchain
    | false =>
    have hav' : canRight s.right := by
      rcases hav with hav | hav
      · rw [hrep] at hav; cases hav
      · exact hav
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    rw [hrep, if_neg (by simp)] at hpl'
    clear hpl
    subst t
    have hcf : compareFound (PofC centre place entry w) q first s s' := hcmp
    obtain ⟨vs, vq, a, hvl, hvr, hiff, -, hch, hteq⟩ := hcf
    cases a with
    | false =>
      rw [if_neg (by simp)] at hteq
      refine absurd (hiff.2 ?_) (by simp)
      rw [hteq] at hmt
      have h0 : GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).left
        = GalilScaffoldInputHead.read (afterBirth _ (afterMismatch s vs vq)).right := hmt
      rw [afterBirth_left, afterBirth_right] at h0
      exact h0
    | true =>
      rw [if_pos rfl] at hteq
      have hchain' : vs.chain = .watch wch := by
        rw [hteq, afterBirth_chain] at hchain; exact hchain
      rcases chainAt_true_watch hch hchain' with ⟨w0, w1, hw0, hint, hout⟩ | hnot
      · have hne : s.chain ≠ ChainVM.idle := by rw [hw0]; intro h0; cases h0
        rw [afterBirth_of_ne_idle hne] at hteq
        have hpo : s.periodOnly = true := by rw [hteq] at hpo'; exact hpo'
        subst hteq
        obtain ⟨C, R, used, hI⟩ := hCR hm hrep hpo w0 hw0
        have hz := hI.caught.lagZero
        have hwe := internal_of_zero hz hint
        subst w1
        obtain ⟨hg, hwch⟩ := outer_of_zero hz hout
        subst hwch
        have hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right) := by
          have hm2 : read vs.left = read vs.right := hmt
          rw [hvl, hvr] at hm2
          exact hm2
        cases hend : singlePositive s.cycle with
        | true => exact absurd hg (not_good_of_terminal_match hI hav' hend hmatch)
        | false =>
          have hadv := h_advance_of_readsInv hI (hRR hm hrep hpo w0 hw0 C R used hI) hg hend
          have hcyc : (afterCompare s vs vq).cycle = dec s.cycle := by
            show cycleAfter s = dec s.cycle
            unfold cycleAfter
            rw [hpo, if_pos rfl]
          have hstep := roundScan_step hI hav' hend hmatch hchain
            (show (afterCompare s vs vq).left = GalilScaffoldInputHead.left s.left from hvl)
            (show (afterCompare s vs vq).right = right s.right from hvr) hcyc hadv
          have hblk' : GalilBranchInvariants.OnBlock w0.machine.control.period := by
            have hb0 : GalilBranchInvariants.BlockInv s.chain := hblk
            rw [hw0] at hb0
            exact hb0
          have hper : periodLength (GalilScaffoldChainWatch.immediate w0) = periodLength w0 :=
            periodLength_consume w0.machine w0.lag w0.margin w0.lag (inc w0.margin) hblk'
          refine ⟨C, R, used + 1, ?_⟩
          rw [hper]
          exact hstep
      · exact hB (Or.inr hnot) hpo' wch hchain
  | scan_shift c s s' t hm h hc hcmp hmt hr hg hb =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | scan_fallback c s s' t hm h hc hcmp hmt hg hr hb =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | shift_one c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | shift_done c s o hm hp ho =>
    intro _ hr' hpo' wch hchain
    exact hS hm hr' hpo' hp wch hchain
  | copy_one c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | copy_done c s t hm hp hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | home_start c s t hm hl hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | home_step c s t hm hl hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_slice c s t hm hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_done c s t hm hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_found c s t hm he hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_step c s t hm he hs =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | choose_select c s t hm ho hs h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | choose_step c s t hm hs h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_done c s t hm hf h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp)
  | rewind_one c s t hm hf hp h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_pair c s t hm hf hp h =>
    intro hm' _ _ _ _
    exact absurd hm' (by simp [hm])
  | replayStart c s t o hm hrs ho ho' =>
    intro _ _ _ wch hchain
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hrs
    rw [hch] at hchain
    cases hchain


end

#print axioms h_advance_of_readsRun
#print axioms chainRound_tick_R
#print axioms chainRound_tick_RR

end PalPeg.CloseoutRoundReads
