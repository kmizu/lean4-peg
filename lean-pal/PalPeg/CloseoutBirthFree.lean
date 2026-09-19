import PalPeg.CloseoutPeriodShape
import PalPeg.CloseoutRoundReads

/-!
# `H_birth` reduced to its replaying half

`CloseoutPackRun31.H_birth` covers two situations:

```
(c.replaying = true ∨ ∀ w0, s.chain ≠ .watch w0) → t.periodOnly = true → …
```

The second disjunct — a watch appears at the target although the source had
none — can only come from `ChainStep.backDone` (`chainAt_false_watch` /
`chainAt_true_watch` leave exactly that constructor in their `hnot` case), so
the source chain is a `.back`.  `CloseoutPeriodShape.PeriodShape` says a
`.back` chain is unreachable while `periodOnly = true`, and the tick carries
`t.periodOnly = true` back to `s.periodOnly = true` because a birth would have
cleared the flag.

`chainAt_false_back` / `chainAt_true_back` expose the source shape, and
`chainRound_tick_B` is `chainRound_tick_RR` with the three "born" uses of `hB`
replaced by that contradiction, so only `H_birthR` (the replaying half) is
left.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutBirthFree

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutLPack3 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.GalilRoundPeriod PalPeg.GalilChainCoupling PalPeg.CloseoutPackRun31
open PalPeg.CloseoutPackRun37 PalPeg.CloseoutPackRun40 PalPeg.CloseoutPackRun41
open PalPeg.CloseoutRoundReads PalPeg.CloseoutPeriodShape

/-- **The source of a newborn watch after `chainAt false` is a `.back` chain**,
hence not `WatchLike`.  Same case split as
`CloseoutPackRun31.chainAt_false_born`. -/
theorem chainAt_false_back {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt false found ans cc walker ver radius x z)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch)
    (hnot : ∀ w0, x ≠ .watch w0) : ¬ WatchLike x := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hzc⟩
  · rw [if_neg (by simp)] at hzy
    subst hzy
    subst hz
    cases hstep with
    | watchStep w w' ht => exact absurd rfl (hnot w)
    | backDone v h lag margin ver hf => exact fun hx => hx
  · cases hz
  · rw [if_neg (by simp)] at hzc
    subst hzc
    unfold chainStart at hz
    cases hz

/-- The `chainAt true` version. -/
theorem chainAt_true_back {found : Bool} {ans : GalilScaffoldTape.Tape} {cc : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : PlaceHead} {radius : Counter} {x z : ChainVM}
    (h : chainAt true found ans cc walker ver radius x z)
    {wch : GalilScaffoldChainWatch.State} (hz : z = .watch wch)
    (hnot : ∀ w0, x ≠ .watch w0) : ¬ WatchLike x := by
  rcases h with ⟨-, y, hstep, hzy⟩ | ⟨-, -, rfl⟩ | ⟨-, -, hzc⟩
  · rw [if_pos rfl] at hzy
    subst hz
    cases hzy with
    | watch w w' ho =>
      cases hstep with
      | watchStep w0 w1 ht => exact absurd rfl (hnot w0)
      | backDone v h lag margin ver hf => exact fun hx => hx
  · cases hz
  · rw [if_pos rfl] at hzc
    unfold chainStart at hzc
    cases hzc
    cases hz

/-- **(NAMED) `H_birth`'s replaying half.** -/
def H_birthR (w : List (Fin 2)) (c : Control) (s t : GalilVM) : Prop :=
  c.replaying = true → t.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, t.chain = ChainVM.watch wch →
    ∃ C R used : ℕ, RoundScan w C R (periodLength wch) used t wch

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`chainRound_tick` with `H_birth` reduced to its replaying half.**
The case analysis is `chainRound_tick_RR` verbatim; the only changes are the
four lines that consumed `hB`.  Three of them are the "chain born during the
tick" branch, which `PeriodShape` refutes: a newborn watch comes from
`ChainStep.backDone`, i.e. from a `.back` chain, which `periodOnly = true`
excludes. -/
theorem chainRound_tick_B {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hRR : ReadsRound w x.ctl x.vm)
    (hps : PeriodShape x.vm)
    (hS : H_shiftDone centre place entry q first w x.ctl x.vm)
    (hB : H_birthR w x.ctl x.vm y.vm)
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
    · exfalso
      have hsp : s.periodOnly = true := by
        cases hbq : chainBorn (decide ((searchLens.get t).search.mode
            = GalilScaffoldSearchFinish.Mode.found)) s.chain with
        | true => rw [hbq, if_pos rfl] at hpo; rw [hpo] at hpo'; cases hpo'
        | false => rw [hbq, if_neg (by decide)] at hpo; rw [← hpo]; exact hpo'
      exact absurd (hps hsp) (chainAt_false_back hch hchain hnot)
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
    · exfalso
      have hsp : s.periodOnly = true := by
        cases hbq : chainBorn (decide ((searchLens.get t).search.mode
            = GalilScaffoldSearchFinish.Mode.found)) s.chain with
        | true => rw [hbq, if_pos rfl] at hpo; rw [hpo] at hpo'; cases hpo'
        | false => rw [hbq, if_neg (by decide)] at hpo; rw [← hpo]; exact hpo'
      exact absurd (hps hsp) (chainAt_false_back hch hchain hnot)
  | restart c s t hm hb =>
    intro _ _ _ wch hchain
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    cases hchain
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    intro hm' hr' hpo' wch hchain
    cases hrep : c.replaying with
    | true => exact hB hrep hpo' wch hchain
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
      · exfalso
        have hsp : s.periodOnly = true := by
          rw [hteq, afterBirth_periodOnly] at hpo'
          cases hbq : chainBorn (decide (vq.search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain with
          | true => rw [hbq, if_pos rfl] at hpo'; cases hpo'
          | false => rw [hbq, if_neg (by decide)] at hpo'; exact hpo'
        exact absurd (hps hsp) (chainAt_true_back hch hchain' hnot)
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



/-- **`ChainRound` along a tick with only `H_shiftDone` and `H_birthR` left.**
`H_advance` comes from `ReadsRound`, `BlockInv` from `ChainPositionInvariantWithShiftPhase`, and the
"born" half of `H_birth` from `PeriodShape`. -/
theorem chainRound_tick_BF {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hRR : ReadsRound w x.ctl x.vm)
    (hps : PeriodShape x.vm)
    (hinv : ChainPositionInvariantWithShiftPhase w x.ctl x.vm)
    (hS : H_shiftDone centre place entry q first w x.ctl x.vm)
    (hB : H_birthR w x.ctl x.vm y.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ChainRound w y.ctl y.vm :=
  chainRound_tick_B centre place entry q first hCR hRR hps hS hB
    (blockInv_of_chainPosInv2 hinv) h

end

#print axioms chainAt_false_back
#print axioms chainAt_true_back
#print axioms chainRound_tick_B
#print axioms chainRound_tick_BF

end PalPeg.CloseoutBirthFree
