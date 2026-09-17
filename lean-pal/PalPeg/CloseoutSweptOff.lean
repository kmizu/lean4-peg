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

#print axioms sweptOff_of_readsInv
#print axioms sweptOff_consume
#print axioms sweptOff_shift
#print axioms symbol_of_sweptOff
#print axioms bounce_of_sweptOff

end PalPeg.CloseoutSweptOff
