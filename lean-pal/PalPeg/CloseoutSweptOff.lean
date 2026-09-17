import PalPeg.CloseoutOriginAt

/-!
# `SweptOff`: the sweep witness as an `Offset`, which survives the shift

`CloseoutOriginAt` measured why `H_readsShift` is there:
`CloseoutPackRun37.ReadsInv` states the witness as an **equality**

```
w.machine.control = GalilScaffoldChainSweep.run o.shifted.machine.control extra
```

and `chainShiftOne` decrements `distance`, `boundary` and `last`, so the shift
phase destroys it.  But the development's own relation for "same period tape,
same `broken`, counters off by a constant" is `ReadOrigin.Offset`, and it has
the full algebra already:

| lemma | `GalilScaffoldChainReadOrigin` | content |
|---|---|---|
| `Offset.of_eq` | `:28` | an equality is an `Offset 0` |
| `Offset.consume` | `:32` | one consume on both sides keeps `k` |
| `Offset.run` | `:46` | a whole continuation keeps `k` |
| `Offset.trans` | `:53` | offsets add |
| `Offset.shift` | `:60` | a `ChainShiftRun` of `n` steps shifts `k` by `n` |

So restating the witness with `Offset` makes it survive **both** the consume
(`sweptOff_consume`) and the shift (`sweptOff_shift`), and the prediction is
still readable off the reference run because `Offset.prediction` is literally
`period` equality (`SamePrediction`).

That is what removes `H_readsShift`: the witness no longer has to be rebuilt at
the round boundary, it is transported.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutSweptOff

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.GalilRoundPeriod PalPeg.CloseoutPackRun31 PalPeg.CloseoutPackRun37

/-- **(NAMED) the sweep witness, as an `Offset`.**  `n` is the number of
symbols consumed since the origin's own prefix. -/
def SweptOff (raw : List (Fin 2)) (C R h n : ℕ) (w : GalilScaffoldChainWatch.State) : Prop :=
  ∃ (o : ReadOrigin raw) (extra : List (Fin 3)) (k : ℤ),
    o.center = C ∧ o.radius = R ∧ o.interior.length + 1 = h ∧ extra.length = n ∧
    Offset k w.machine.control
      (GalilScaffoldChainSweep.run
        (GalilScaffoldChainConsume.ready o.token o.interior o.boundary) (o.pre ++ extra))

/-- **`ReadsInv` implies it.**  The equality is an `Offset 0`, and the origin's
own `offset` / `shiftRun` carry the reference back to `ready`. -/
theorem sweptOff_of_readsInv {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hRI : ReadsInv raw C R h n w) :
    SweptOff raw C R h n w := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hctl⟩ := hRI
  have h1 : Offset 0 w.machine.control
      (GalilScaffoldChainSweep.run o.shifted.machine.control extra) := Offset.of_eq hctl
  have h2 := (Offset.shift o.shiftRun o.offset).run extra
  have h3 := h1.trans h2
  rw [← GalilScaffoldChainSweep.run_append] at h3
  exact ⟨o, extra, _, hC, hRR, hh, hlen, h3⟩

/-- **The consume transports it.**  `Offset.consume` on both sides; the
continuation grows by the symbol the verifier read. -/
theorem sweptOff_consume {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hS : SweptOff raw C R h n w) {a : Fin 3}
    (hra : read (right w.machine.verifier) = some a) :
    SweptOff raw C R h (n + 1) (GalilScaffoldChainWatch.immediate w) := by
  obtain ⟨o, extra, k, hC, hRR, hh, hlen, hoff⟩ := hS
  refine ⟨o, extra ++ [a], k, hC, hRR, hh, by simp [hlen], ?_⟩
  have h1 := hoff.consume (some a)
  show Offset k (GalilScaffoldChainConsume.consume w.machine.control
      (read (right w.machine.verifier))) _
  rw [hra]
  rw [show o.pre ++ (extra ++ [a]) = (o.pre ++ extra) ++ [a] from by
    simp only [List.append_assoc]]
  rw [GalilScaffoldChainSweep.run_append]
  exact h1

/-- **The shift phase transports it.**  `Offset.shift`: `k` moves by the number
of shift steps, the reference run does not move at all. -/
theorem sweptOff_shift {raw : List (Fin 2)} {C R h n : ℕ}
    {w v : GalilScaffoldChainWatch.State} {s t : ShiftState}
    {cycle finish : Counter} {m : ℕ}
    (hS : SweptOff raw C R h n w) (hr : ChainShiftRun s w cycle m t v finish) :
    SweptOff raw C R h n v := by
  obtain ⟨o, extra, k, hC, hRR, hh, hlen, hoff⟩ := hS
  exact ⟨o, extra, k + m, hC, hRR, hh, hlen, Offset.shift hr hoff⟩

/-- **One shift unit transports it.**  `chainShiftOne` keeps `period`,
`forward` and `broken` and decrements the three counters, which is exactly an
`Offset` step of one.  (`Offset.shift` does the whole `ChainShiftRun` at once;
this is the single-unit form the `shift_one` tick needs.) -/
theorem sweptOff_shiftOne {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hS : SweptOff raw C R h n w) :
    SweptOff raw C R h n (chainShiftOne w) := by
  obtain ⟨o, extra, k, hC, hRR, hh, hlen, hoff⟩ := hS
  refine ⟨o, extra, k + 1, hC, hRR, hh, hlen, ?_⟩
  obtain ⟨⟨hp, hf⟩, hb, hd, hbd, hl⟩ := hoff
  refine ⟨⟨hp, hf⟩, hb, ?_, ?_, ?_⟩
  · show value (dec w.machine.control.distance) = _
    rw [dec_value, hd]; ring
  · show value (dec w.machine.control.boundary) = _
    rw [dec_value, hbd]; ring
  · show value (dec w.machine.control.last) = _
    rw [dec_value, hl]; ring

/-- **The prediction is readable off the reference run.**  `Offset.prediction`
is `period` equality, so the two focuses are the same token. -/
theorem symbol_of_sweptOff {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hS : SweptOff raw C R h n w) :
    ∃ (o : ReadOrigin raw) (extra : List (Fin 3)),
      o.center = C ∧ o.radius = R ∧ o.interior.length + 1 = h ∧ extra.length = n ∧
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus =
        GalilScaffoldChainConsume.symbol
          (GalilScaffoldChainSweep.run
            (GalilScaffoldChainConsume.ready o.token o.interior o.boundary)
            (o.pre ++ extra)).period.focus ∧
      (w.machine.control.broken =
        (GalilScaffoldChainSweep.run
          (GalilScaffoldChainConsume.ready o.token o.interior o.boundary)
          (o.pre ++ extra)).broken) := by
  obtain ⟨o, extra, k, hC, hRR, hh, hlen, hoff⟩ := hS
  exact ⟨o, extra, hC, hRR, hh, hlen,
    congrArg (fun t => GalilScaffoldChainConsume.symbol t.focus) hoff.prediction.1,
    hoff.broken⟩

/-- **The `bounce` index of the prediction, with no length bound.**
`GalilScaffoldChainPrediction.successful_prediction` applied to the reference
run, which the `Offset` says has the same period tape. -/
theorem bounce_of_sweptOff {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hS : SweptOff raw C R h n w)
    (hb : w.machine.control.broken = false) :
    ∃ o : ReadOrigin raw, o.center = C ∧ o.radius = R ∧ o.interior.length + 1 = h ∧
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus =
        (GalilScaffoldChainSweep.bounce o.token o.boundary o.interior)[
          (o.pre.length + n) % (2 * h)]? := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hsym, hbr⟩ := symbol_of_sweptOff hS
  have hb' : (GalilScaffoldChainSweep.run
      (GalilScaffoldChainConsume.ready o.token o.interior o.boundary)
      (o.pre ++ extra)).broken = false := by rw [← hbr]; exact hb
  have hp := GalilScaffoldChainPrediction.successful_prediction o.token o.boundary o.interior
    (o.pre ++ extra) hb'
  refine ⟨o, hC, hRR, hh, ?_⟩
  rw [hsym, hp]
  simp only [List.length_append, hlen, hh]

/-! ## The encoded index, inside a round

Within one round the witness's `n` **is** the round's `used`, so
`GalilGoodLag.origin_prediction_index` applies directly (`used < 2h` by
`RoundScan.fresh`) and no periodicity is needed.  `H_advance`'s conclusion
follows from `SweptOff` alone.
-/

/-- **The prediction as an index of the encoded word, inside a round.** -/
theorem encoded_of_sweptOff {raw : List (Fin 2)} {C R h n : ℕ}
    {w : GalilScaffoldChainWatch.State} (hS : SweptOff raw C R h n w)
    (hn : n < 2 * h) (hb : w.machine.control.broken = false) :
    GalilScaffoldChainConsume.symbol w.machine.control.period.focus =
      (encoded raw)[C + R + 2 - 2 * h + n]? := by
  obtain ⟨o, extra, hC, hRR, hh, hlen, hsym, hbr⟩ := symbol_of_sweptOff hS
  have hb' : (GalilScaffoldChainSweep.run o.shifted.machine.control extra).broken = false := by
    -- the reference run and the origin's shifted control have the same `broken`
    have h2 := (Offset.shift o.shiftRun o.offset).run extra
    rw [← GalilScaffoldChainSweep.run_append] at h2
    rw [h2.broken, ← hbr]
    exact hb
  have h3 := origin_prediction_index o h hh extra (by rw [hlen]; exact hn) hb'
  have h4 : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
      = GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainSweep.run o.shifted.machine.control extra).period.focus := by
    have h2 := (Offset.shift o.shiftRun o.offset).run extra
    rw [← GalilScaffoldChainSweep.run_append] at h2
    rw [hsym, h2.prediction.1]
  rw [h4, h3, hC, hRR, hlen]

/-- **`H_advance`'s conclusion from `SweptOff`.**  The consume grows the
continuation by one, and the round is not yet terminal. -/
theorem advance_of_sweptOff {raw : List (Fin 2)} {C R h used : ℕ} {s : GalilVM}
    {w0 : GalilScaffoldChainWatch.State}
    (hI : RoundScan raw C R h used s w0) (hS : SweptOff raw C R h used w0)
    (hg : GalilScaffoldChainWatch.Good w0) (hend : singlePositive s.cycle = false) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainWatch.immediate w0).machine.control.period.focus =
      (encoded raw)[C + R + 2 + (used + 1) - 2 * h]? := by
  obtain ⟨-, a, ha, hra⟩ := hg
  have hne : used + 1 ≠ 2 * h := by
    intro heq
    rw [hI.terminal_iff.mpr heq] at hend
    cases hend
  have hlt : used + 1 < 2 * h := by have := hI.fresh; omega
  have hunb : (GalilScaffoldChainWatch.immediate w0).machine.control.broken = false := by
    show (GalilScaffoldChainConsume.consume w0.machine.control
      (read (right w0.machine.verifier))).broken = false
    rw [hra]
    exact consume_keeps_unbroken _ a ha hI.caught.unbroken
  have h := encoded_of_sweptOff (sweptOff_consume hS hra) hlt hunb
  rw [h]
  congr 1
  have := hI.size
  have := hI.posH
  omega

/-! ## The local period on the overlap of the two palindromes -/

/-- **`x[j − 2h] = x[j]` for every `j` in the overlap.**  `CloseoutAdvanceT`'s
`period_at_next` at a general index: mirror `j` about `C + 2h`, then about
`C + h`. -/
theorem period_window {raw : List (Fin 2)} {C R h j : ℕ}
    (hpal : Manacher.PalAt (encoded raw) (C + h) (R + h))
    (hnext : Manacher.PalAt (encoded raw) (C + 2 * h) (R + 1))
    (hs : 2 * h ≤ R) (hp : 0 < h) (hroom : R + 2 ≤ C)
    (hj1 : C + 2 * h - R ≤ j) (hj2 : j ≤ C + R + 2 * h) :
    (encoded raw)[j - 2 * h]? = (encoded raw)[j]? := by
  have hm : 2 * (C + 2 * h) - j = 2 * C + 4 * h - j := by omega
  have e1 : (encoded raw)[j]? = (encoded raw)[2 * (C + 2 * h) - j]? :=
    Manacher.mirror_getElem? hnext (by omega) (by omega)
  rw [hm] at e1
  have e2 : (encoded raw)[2 * C + 4 * h - j]?
      = (encoded raw)[2 * (C + h) - (2 * C + 4 * h - j)]? :=
    Manacher.mirror_getElem? hpal (by omega) (by omega)
  have hmid : 2 * (C + h) - (2 * C + 4 * h - j) = j - 2 * h := by omega
  rw [hmid] at e2
  exact (e1.trans e2).symm

#print axioms sweptOff_of_readsInv
#print axioms sweptOff_consume
#print axioms sweptOff_shift
#print axioms sweptOff_shiftOne
#print axioms symbol_of_sweptOff
#print axioms bounce_of_sweptOff
#print axioms encoded_of_sweptOff
#print axioms advance_of_sweptOff
#print axioms period_window

end PalPeg.CloseoutSweptOff
