import PalPeg.CloseoutNoReplayWatch

/-!
# `H_advanceT`: the prediction after the terminal consume

`CloseoutPackRun37.shiftRound_tick` names `H_advanceT`: after the *terminal*
consume of a round the chain predicts `x[C+R+2]`.  `H_advance`'s proof
(`h_advance_of_readsInv`) uses `origin_prediction_index` (`GalilGoodLag`), which
needs the continuation strictly shorter than `2h` — and at the terminal it is
exactly `2h`, so the period tape has wrapped.

The wrap is not a problem, it is the point.  Two observations close it.

## 1. The tape's prediction is `2h`-periodic in the consumed count

`GalilScaffoldChainPrediction.continued_prediction` gives the prediction as
`bounce[(pre.length + extra.length) % (2*(xs.length+1))]?` with **no** bound on
`extra.length`, and `ReadOrigin` supplies the `SamePrediction` it needs through
`Offset.shift org.shiftRun org.offset`.  So at `extra.length = 2h` the
prediction equals the one at `extra.length = 0`, which
`origin_prediction_index` does convert: `x[C+R+2-2h]`.

## 2. `x[C+R+2-2h] = x[C+R+2]`

At the terminal the round carries two palindromes: `PalAt x (C+h) (R+h)` (its
caught scan) and `PalAt x (C+2h) (R+1)`
(`CloseoutPackRun31.terminal_palindrome`).  Mirroring `C+R+2` about `C+2h` and
then about `C+h` lands on `C+R+2-2h`:

```
C+R+2  ↦  2(C+2h) − (C+R+2) = C+4h−R−2  ↦  2(C+h) − (C+4h−R−2) = C+R+2−2h
```

Both mirrors are inside their radii because `2h ≤ R`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutAdvanceT

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37

/-! ## 1. The tape's prediction, unbounded -/

/-- **The prediction as a `bounce` index, with no length bound.**
`continued_prediction` fed with the `SamePrediction` that `ReadOrigin` carries
through `Offset.shift`. -/
theorem origin_prediction_bounce {raw : List (Fin 2)} (org : ReadOrigin raw)
    (extra : List (Fin 3))
    (hsucc : (GalilScaffoldChainSweep.run org.shifted.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainSweep.run org.shifted.machine.control extra).period.focus =
      (GalilScaffoldChainSweep.bounce org.token org.boundary org.interior)[
        (org.pre.length + extra.length) % (2 * (org.interior.length + 1))]? := by
  have hoff' := Offset.shift org.shiftRun org.offset
  exact GalilScaffoldChainPrediction.continued_prediction org.token org.boundary
    org.interior org.pre extra org.shifted.machine.control hoff'.prediction hoff'.broken hsucc

/-- **The prediction after a full period sweep.**  At `extra.length = 2h` the
`bounce` index is the same as at `extra.length = 0`, where
`origin_prediction_index` (`GalilGoodLag`) converts it to an index of the encoded
word. -/
theorem origin_prediction_wrap {raw : List (Fin 2)} (org : ReadOrigin raw) (h : ℕ)
    (hh : org.interior.length + 1 = h) (extra : List (Fin 3)) (hlen : extra.length = 2 * h)
    (hsucc : (GalilScaffoldChainSweep.run org.shifted.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainSweep.run org.shifted.machine.control extra).period.focus =
      (encoded raw)[org.center + org.radius + 2 - 2 * h]? := by
  have h0 : org.shifted.machine.control.broken = false :=
    GalilScaffoldChainPrediction.unbroken_start _ extra hsucc
  have h0succ : (GalilScaffoldChainSweep.run org.shifted.machine.control
      ([] : List (Fin 3))).broken = false := h0
  have h1 := origin_prediction_bounce org extra hsucc
  have h2 := origin_prediction_bounce org ([] : List (Fin 3)) h0succ
  have hidx : (org.pre.length + extra.length) % (2 * (org.interior.length + 1))
      = (org.pre.length + ([] : List (Fin 3)).length) % (2 * (org.interior.length + 1)) := by
    simp only [List.length_nil, Nat.add_zero, hlen, hh]
    exact Nat.add_mod_right _ _
  rw [hidx] at h1
  have h3 := origin_prediction_index org h hh ([] : List (Fin 3))
    (by simp only [List.length_nil]; omega) h0succ
  simp only [List.length_nil, Nat.add_zero] at h3
  exact h1.trans (h2.symm.trans h3)

/-! ## 2. The two mirrors -/

/-- **`x[C+R+2−2h] = x[C+R+2]`** from the round's two palindromes. -/
theorem period_at_next {raw : List (Fin 2)} {C R h : ℕ}
    (hpal : Manacher.PalAt (encoded raw) (C + h) (R + h))
    (hnext : Manacher.PalAt (encoded raw) (C + 2 * h) (R + 1))
    (hs : 2 * h ≤ R) (hp : 0 < h) (hroom : R + 2 ≤ C) :
    (encoded raw)[C + R + 2 - 2 * h]? = (encoded raw)[C + R + 2]? := by
  have e1 : (encoded raw)[C + R + 2]? = (encoded raw)[2 * (C + 2 * h) - (C + R + 2)]? :=
    Manacher.mirror_getElem? hnext (by omega) (by omega)
  have hmid : 2 * (C + 2 * h) - (C + R + 2) = C + 4 * h - R - 2 := by omega
  rw [hmid] at e1
  have e2 : (encoded raw)[C + 4 * h - R - 2]?
      = (encoded raw)[2 * (C + h) - (C + 4 * h - R - 2)]? :=
    Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hmid2 : 2 * (C + h) - (C + 4 * h - R - 2) = C + R + 2 - 2 * h := by omega
  rw [hmid2] at e2
  exact (e1.trans e2).symm

/-! ## 3. `H_advanceT`'s content -/

/-- **The prediction after the terminal consume, from the carried sweep
witness and the two palindromes.**  This is `H_advanceT`'s conclusion.  Only
`Good`'s second component is used, so it is taken directly. -/
theorem advanceT_of_readsInv {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hRI : ReadsInv raw C R h used w0)
    (hsym : ∃ a, GalilScaffoldChainConsume.symbol w0.machine.control.period.focus = some a ∧
      read (right w0.machine.verifier) = some a)
    (hend : singlePositive s.cycle = true)
    (hnext : Manacher.PalAt (encoded raw) (C + 2 * h) (R + 1)) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded raw)[C + R + 2]? := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hctl⟩ := hRI
  obtain ⟨a, ha, hra⟩ := hsym
  have hterm : used + 1 = 2 * h := hI.terminal_iff.mp hend
  have hrun : (GalilScaffoldChainWatch.immediate w0).machine.control =
      GalilScaffoldChainSweep.run o.shifted.machine.control (extra ++ [a]) := by
    show GalilScaffoldChainConsume.consume w0.machine.control
      (read (right w0.machine.verifier)) = _
    rw [GalilScaffoldChainSweep.run_append, ← hctl, hra]
    rfl
  have hunb : (GalilScaffoldChainSweep.run o.shifted.machine.control
      (extra ++ [a])).broken = false := by
    rw [← hrun]
    show (GalilScaffoldChainConsume.consume w0.machine.control
      (read (right w0.machine.verifier))).broken = false
    rw [hra]
    exact consume_keeps_unbroken _ a ha hI.caught.unbroken
  have hlen2 : (extra ++ [a]).length = 2 * h := by
    simp only [List.length_append, List.length_singleton, hlen]
    omega
  rw [hrun, origin_prediction_wrap o h hh (extra ++ [a]) hlen2 hunb, hC, hRR]
  have hpal : Manacher.PalAt (encoded raw) (C + h) (R + h) := by
    have hp := hI.caught.scan.palindrome
    rw [show R + 1 - h + used = R + h from by
      have := hI.size; have := hI.posH; omega] at hp
    exact hp
  exact period_at_next hpal hnext hI.size hI.posH hI.room

/-! ## 4. The guard supplies what is left -/

/-- **The consume at a guarded terminal succeeds.**  `Good`'s second component,
from the round and the guard's prediction.  The derivation is
`GalilRoundPeriod.RoundScan.break_of_match`'s: `canRight v.right` bounds the
scan's right head, `CaughtScan.aligned` carries the bound to the verifier
(`canRight_of_bound`), and the two representations then read the same
symbol. -/
theorem sym_of_guard {raw : List (Fin 2)} {C R h used : ℕ} {v : GalilVM}
    {w : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used v w) (hav : canRight v.right)
    (hend : singlePositive v.cycle = true)
    (hpred : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
      = read (right v.right)) :
    ∃ a, GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a ∧
      read (right w.machine.verifier) = some a := by
  have hc := hI.caught
  have hs := hc.scan
  have hrrep := right_word v.right raw hs.rightRep hav
  have hrpres := right_present v.right raw hs.rightRep hs.rightPresent hav
  have hrpos := right_position v.right hav
    (represented_position v.right.head raw hs.rightRep hs.rightPresent).1
  have hbound := position_bound (right v.right) raw hrrep hrpres
  have hvc : canRight w.machine.verifier :=
    canRight_of_bound w.machine.verifier raw hc.verifierRep hc.verifierPresent
      (by rw [hc.aligned]; omega)
  have hvrep := right_word _ raw hc.verifierRep hvc
  have hvpres := right_present _ raw hc.verifierRep hc.verifierPresent hvc
  have hvpos := right_position w.machine.verifier hvc
    (represented_position w.machine.verifier.head raw hc.verifierRep hc.verifierPresent).1
  have hread : read (right w.machine.verifier) = read (right v.right) := by
    rw [represented_read _ raw hvrep hvpres, represented_read _ raw hrrep hrpres,
      hvpos, hrpos, hc.aligned]
  have he := hI.terminal_iff.mp hend
  have hsz := hI.size
  have hph := hI.posH
  have hrm := hI.room
  have hidx : C + R + 2 + used - 2 * h = C + R + 1 := by omega
  have hlt : C + R + 1 < (encoded raw).length := by
    have := hs.palindrome.2.1
    have := hs.rightPos
    omega
  obtain ⟨a, ha⟩ : ∃ a, (encoded raw)[C + R + 1]? = some a :=
    ⟨(encoded raw)[C + R + 1], List.getElem?_eq_getElem hlt⟩
  have hp2 : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a := by
    rw [hI.pred, hidx]; exact ha
  exact ⟨a, hp2, by rw [hread, ← hpred]; exact hp2⟩

/-- **`H_advanceT`'s conclusion from the round, the sweep witness and the
guard.**  `terminal_palindrome` supplies `palNext` and `sym_of_guard` the
consume. -/
theorem advanceT_of_guard {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hRI : ReadsInv raw C R h used w0)
    (hav : canRight s.right) (hend : singlePositive s.cycle = true)
    (hpred : GalilScaffoldChainConsume.symbol w0.machine.control.period.focus
      = read (right s.right)) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded raw)[C + R + 2]? :=
  advanceT_of_readsInv hI hRI (sym_of_guard hI hav hend hpred) hend
    (terminal_palindrome hI hend hav hpred)

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`H_advanceT` is a theorem given the carried `ReadsRound`.**  The two are
now the same shape: both are premised on `scan` / not-replaying / `periodOnly`
and quantify over the rounds of the state. -/
theorem h_advanceT_of_readsRound {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hRR : PalPeg.CloseoutRoundReads.ReadsRound w c s) :
    H_advanceT w c s := fun hm hr hpo C R used w0 hI hend hav hpred =>
  advanceT_of_guard hI (hRR hm hr hpo w0 hI.chain C R used hI) hav hend hpred

/-- **`ShiftRound` along a tick with `H_advanceT` gone.** -/
theorem shiftRound_tick_A {w : List (Fin 2)} {delay : ℕ} {x y : State GalilVM}
    (hCR : ChainRound w x.ctl x.vm)
    (hSR : ShiftRound w x.ctl x.vm)
    (hRR : PalPeg.CloseoutRoundReads.ReadsRound w x.ctl x.vm)
    (hF : PalPeg.CloseoutPackRun37.H_freshShiftAtShiftEntry centre place entry q first w x.ctl x.vm y.vm)
    (hblk : GalilBranchInvariants.BlockInv x.vm.chain)
    (hci : x.ctl.mode = Mode.shift → CopyIdle x.vm)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) delay x y) :
    ShiftRound w y.ctl y.vm :=
  shiftRound_tick centre place entry q first hCR hSR (h_advanceT_of_readsRound hRR) hF hblk hci h

end

#print axioms origin_prediction_bounce
#print axioms origin_prediction_wrap
#print axioms period_at_next
#print axioms advanceT_of_readsInv
#print axioms sym_of_guard
#print axioms advanceT_of_guard
#print axioms h_advanceT_of_readsRound
#print axioms shiftRound_tick_A

end PalPeg.CloseoutAdvanceT
