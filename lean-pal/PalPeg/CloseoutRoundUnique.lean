import PalPeg.CloseoutBirthFree

/-!
# The round is determined by the state, and `ReadsRound` travels

`CloseoutRoundReads.ReadsRound` quantifies over the round `(C, R, used)` a state
is in, so transporting it along a tick needs to know that the round is
**determined** by the state and its watch.  It is:

| field | equation |
|---|---|
| `count` | `value v.cycle = 2h − used` |
| `rightPos` | `position v.right = C + R + 1 + used` |
| `leftPos` | `position v.left = C + 2h − R − 1 − used` |

The first pins `used`, and then the other two pin `C + R` and `C − R`, hence
`C` and `R` (the subtractions are safe by `size : 2h ≤ R` and `room : R+2 ≤ C`).
`roundScan_unique` is that `omega`.

With it, `ReadsRound` transports along the three ticks that can land a watching
chain in `scan` mode with the flag set:

* `scan_wait` / `scan_count` — the chain steps `Internal` at lag zero, so the
  watch state is *unchanged* (`internal_of_zero`) and the heads and cycle are
  too (`backgroundS_fields`); the round is literally the same one, and
  `roundScan_transport` moves it back to the source.
* `scan_match` — the watch becomes `immediate w0` and the round advances to
  `used + 1`; `CloseoutPackRun37.readsInv_immediate` is exactly that step.
* `shift_done` — the VM is unchanged but the *source* is in `shift` mode, where
  `ReadsRound` is vacuous.  The witness has to come through the shift phase, so
  this one is named `H_readsShift`, the `ReadsRound` companion of
  `CloseoutPackRun31.H_shiftDone`.

Every other shape is vacuous: `init` / `restart` / `replayStart` /
`scan_fallback` land with an idle chain, and every remaining shape lands in a
mode other than `scan`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutRoundUnique

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutLPack3 PalPeg.CloseoutPackRun24 PalPeg.CloseoutPackRun29
open PalPeg.GalilRoundPeriod PalPeg.GalilChainCoupling PalPeg.CloseoutPackRun31
open PalPeg.CloseoutPackRun37 PalPeg.CloseoutPackRun40 PalPeg.CloseoutPackRun41
open PalPeg.CloseoutRoundReads PalPeg.CloseoutPeriodShape PalPeg.CloseoutBirthFree

/-- **The round of a state is unique.** -/
theorem roundScan_unique {raw : List (Fin 2)} {C R h used C' R' used' : ℕ} {v : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used v w) (hI' : RoundScan raw C' R' h used' v w) :
    C = C' ∧ R = R' ∧ used = used' := by
  have hc := hI.count
  have hc' := hI'.count
  have hf := hI.fresh
  have hf' := hI'.fresh
  have hu : used = used' := by omega
  subst hu
  have hr := hI.rightPos
  have hr' := hI'.rightPos
  have hl := hI.leftPos
  have hl' := hI'.leftPos
  have hs := hI.size
  have hs' := hI'.size
  have hm := hI.room
  have hm' := hI'.room
  have hp := hI.posH
  omega

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) the `ReadsRound` companion of `H_shiftDone`.**  At the
`shift_done` exit the VM is unchanged but the source is in `shift` mode, where
`ReadsRound` says nothing; the sweep witness of the next round has to be
carried through the shift phase (`CloseoutPackRun37.ShiftInv`). -/
def H_readsShift (w : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.mode = Mode.shift → c.replaying = false → s.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, s.chain = ChainVM.watch wch →
    ∀ C R used : ℕ, RoundScan w C R (periodLength wch) used s wch →
      ReadsInv w C R (periodLength wch) used wch

/-- **(NAMED) the `ReadsRound` companion of `H_birthR`.** -/
def H_readsBirth (w : List (Fin 2)) (c : Control) (t : GalilVM) : Prop :=
  c.replaying = true → t.periodOnly = true →
  ∀ wch : GalilScaffoldChainWatch.State, t.chain = ChainVM.watch wch →
    ∀ C R used : ℕ, RoundScan w C R (periodLength wch) used t wch →
      ReadsInv w C R (periodLength wch) used wch

/-- **`ReadsRound` along one `galilFrameS` tick.**  Only three shapes can land a
watching chain in `scan` mode with `periodOnly` set; every other shape is
vacuous. -/
theorem readsRound_tick {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hRR : ReadsRound w x.ctl x.vm)
    (hps : PeriodShape x.vm)
    (hSh : H_readsShift w x.ctl x.vm)
    (hBR : H_readsBirth w x.ctl y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ReadsRound w y.ctl y.vm := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h with
  | init c s t hm hi =>
    intro _ _ _ wch hchain _ _ _ _
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s t := hi
    rw [hch] at hchain
    cases hchain
  | restart c s t hm hb =>
    intro _ _ _ wch hchain _ _ _ _
    obtain ⟨w0, -, -, -, -, ht⟩ : restartVM entry s t := hb
    subst ht
    cases hchain
  | replayStart c s t o hm hrs ho ho' =>
    intro _ _ _ wch hchain _ _ _ _
    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : replayStartVM entry s t := hrs
    rw [hch] at hchain
    cases hchain
  | scan_wait c s t hm hav hb =>
    intro hm' hr' hpo' wch hchain C R used hI
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hpo; rw [hpo] at hpo'; cases hpo'
      | false => rfl
    rw [hb0, if_neg (by decide)] at hpo hcyc
    have hsp : s.periodOnly = true := by rw [← hpo]; exact hpo'
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · obtain ⟨C0, R0, used0, hI0⟩ := hCR hm' hr' hsp w0 hw0
      have hwe := internal_of_zero hI0.caught.lagZero hint
      rw [hwe] at hchain hI ⊢
      have hIt : RoundScan w C0 R0 (periodLength w0) used0 t w0 :=
        roundScan_transport hI0 hchain hl hr hcyc
      obtain ⟨hC, hR, hU⟩ := roundScan_unique hIt hI
      subst hC; subst hR; subst hU
      exact hRR hm' hr' hsp w0 hw0 C0 R0 used0 hI0
    · exact absurd (hps hsp) (chainAt_false_back hch hchain hnot)
  | scan_count c s t hm hav hc hb =>
    intro hm' hr' hpo' wch hchain C R used hI
    obtain ⟨hl, hr, hch, -, hpo, -, -, hcyc, -, -, -, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hb0 : chainBorn (decide ((searchLens.get t).search.mode
        = GalilScaffoldSearchFinish.Mode.found)) s.chain = false := by
      cases hbq : chainBorn (decide ((searchLens.get t).search.mode
          = GalilScaffoldSearchFinish.Mode.found)) s.chain with
      | true => rw [hbq, if_pos rfl] at hpo; rw [hpo] at hpo'; cases hpo'
      | false => rfl
    rw [hb0, if_neg (by decide)] at hpo hcyc
    have hsp : s.periodOnly = true := by rw [← hpo]; exact hpo'
    rcases chainAt_false_watch hch hchain with ⟨w0, hw0, hint⟩ | hnot
    · obtain ⟨C0, R0, used0, hI0⟩ := hCR hm' hr' hsp w0 hw0
      have hwe := internal_of_zero hI0.caught.lagZero hint
      rw [hwe] at hchain hI ⊢
      have hIt : RoundScan w C0 R0 (periodLength w0) used0 t w0 :=
        roundScan_transport hI0 hchain hl hr hcyc
      obtain ⟨hC, hR, hU⟩ := roundScan_unique hIt hI
      subst hC; subst hR; subst hU
      exact hRR hm' hr' hsp w0 hw0 C0 R0 used0 hI0
    · exact absurd (hps hsp) (chainAt_false_back hch hchain hnot)
  | scan_match c s s' t o hm hav hc hcmp hmt hpl ho =>
    intro hm' hr' hpo' wch hchain C R used hI
    cases hrep : c.replaying with
    | true => exact hBR hrep hpo' wch hchain C R used hI
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
        obtain ⟨C0, R0, used0, hI0⟩ := hCR hm hrep hpo w0 hw0
        have hz := hI0.caught.lagZero
        have hwe := internal_of_zero hz hint
        subst w1
        obtain ⟨hg, hwch⟩ := outer_of_zero hz hout
        subst hwch
        have hmatch : read (GalilScaffoldInputHead.left s.left) = read (right s.right) := by
          have hm2 : read vs.left = read vs.right := hmt
          rw [hvl, hvr] at hm2
          exact hm2
        have hblk' : GalilBranchInvariants.OnBlock w0.machine.control.period := by
          have hb0 : GalilBranchInvariants.BlockInv s.chain := hblk
          rw [hw0] at hb0
          exact hb0
        have hper : periodLength (GalilScaffoldChainWatch.immediate w0) = periodLength w0 :=
          periodLength_consume w0.machine w0.lag w0.margin w0.lag (inc w0.margin) hblk'
        rw [hper] at hI ⊢
        cases hend : singlePositive s.cycle with
        | true => exact absurd hg (not_good_of_terminal_match hI0 hav' hend hmatch)
        | false =>
          have hRI : ReadsInv w C0 R0 (periodLength w0) used0 w0 :=
            hRR hm hrep hpo w0 hw0 C0 R0 used0 hI0
          have hadv := h_advance_of_readsInv hI0 hRI hg hend
          have hcyc : (afterCompare s vs vq).cycle = dec s.cycle := by
            show cycleAfter s = dec s.cycle
            unfold cycleAfter
            rw [hpo, if_pos rfl]
          have hstep := roundScan_step hI0 hav' hend hmatch hchain
            (show (afterCompare s vs vq).left = GalilScaffoldInputHead.left s.left from hvl)
            (show (afterCompare s vs vq).right = right s.right from hvr) hcyc hadv
          obtain ⟨hC, hR, hU⟩ := roundScan_unique hstep hI
          subst hC; subst hR; subst hU
          exact readsInv_immediate hRI hg
      · exfalso
        have hsp : s.periodOnly = true := by
          rw [hteq, afterBirth_periodOnly] at hpo'
          cases hbq : chainBorn (decide (vq.search.mode
              = GalilScaffoldSearchFinish.Mode.found)) s.chain with
          | true => rw [hbq, if_pos rfl] at hpo'; cases hpo'
          | false => rw [hbq, if_neg (by decide)] at hpo'; exact hpo'
        exact absurd (hps hsp) (chainAt_true_back hch hchain' hnot)
  | scan_shift c s s' t hm h hc hcmp hmt hr hg hb =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | scan_fallback c s s' t hm h hc hcmp hmt hg hr hb =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | shift_one c s t hm hp hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | shift_done c s o hm hp ho =>
    intro _ hr' hpo' wch hchain C R used hI
    exact hSh hm hr' hpo' wch hchain C R used hI
  | copy_one c s t hm hp hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | copy_done c s t hm hp hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | home_start c s t hm hl hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | home_step c s t hm hl hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_slice c s t hm hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | fpp_done c s t hm hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_found c s t hm he hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | markEnd_step c s t hm he hs =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | choose_select c s t hm ho hs h =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | choose_step c s t hm hs h =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_done c s t hm hf h =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp)
  | rewind_one c s t hm hf hp h =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])
  | rewind_pair c s t hm hf hp h =>
    intro hm' _ _ _ _ _ _ _ _
    exact absurd hm' (by simp [hm])

end

#print axioms roundScan_unique
#print axioms readsRound_tick

end PalPeg.CloseoutRoundUnique
