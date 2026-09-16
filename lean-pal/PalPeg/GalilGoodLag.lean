import PalPeg.GalilPeriodUnion
import PalPeg.GalilScaffoldTopOnly
import PalPeg.GalilRoundsLeftmost

/-!
# `Good` at positive lag from the periodicity of the current span

`GalilScaffoldChainWatch.Internal.take` needs `Good s` — the chain's period
prediction agrees with the actual input read — at every lag-positive
background step. `found_window_safe` / `found_watch_run` supply that for the
*first* watch, out of `PalAt (encoded raw) center radius`. This file is the
re-shift counterpart: after a shift the chain no longer runs the fresh sweep,
so the agreement has to come from the `2h`-periodicity of the span that
`rounds_leftmost` carries along, not from the mirror of a palindrome.

The mathematics is one line of `PeriodOn`: the chain reading position `j`
predicts the symbol at `j - 2h` (`read_prediction_window`), and
`PeriodOn (encoded raw) (2*h) a b` says `(encoded raw)[j-2h]? =
(encoded raw)[j]?` as long as `a + 2*h ≤ j ≤ b`. Everything else is
bookkeeping: `Entry` pins the verifier at `org.center + org.radius + 1`, so
the read index is `org.center + org.radius + 2 + m` after `m` background
consumes.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldTop GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier GalilScaffoldChainVerifyRun

/-- An agreeing consume never breaks. -/
theorem consume_keeps_unbroken (c : GalilScaffoldChainConsume.State) (a : Fin 3)
    (ht : GalilScaffoldChainConsume.symbol c.period.focus = some a)
    (hb : c.broken = false) :
    (GalilScaffoldChainConsume.consume c (some a)).broken = false := by
  simp [GalilScaffoldChainConsume.consume, ht, hb]

variable {raw : List (Fin 2)}

/-- The chain's prediction after `extra` further background consumes, read
off the input at the position one half-period pair behind the verifier.
This is `read_prediction_window` specialised to a `ReadOrigin` and rewritten
through `org.endPosition`. -/
theorem origin_prediction_index (org : ReadOrigin raw) (h : ℕ)
    (hh : org.interior.length + 1 = h) (extra : List (Fin 3))
    (hextra : extra.length < 2 * h)
    (hsucc : (GalilScaffoldChainSweep.run org.shifted.machine.control extra).broken = false) :
    GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainSweep.run org.shifted.machine.control extra).period.focus =
      (encoded raw)[org.center + org.radius + 2 - 2 * h + extra.length]? := by
  have hsize : 2 * h ≤ org.radius := by have := org.size; omega
  have hw := read_prediction_window (raw := raw) org.token org.boundary org.interior extra
    org.reads org.offset org.unbroken org.shiftRun org.represents org.present org.full
    (by omega) hsucc
  rw [org.endPosition] at hw
  rw [hw]
  congr 1
  omega

/-! ## The single step -/

/-- **`Good` from periodicity.** In a re-shift round with origin `org` and
half period `h`, the watch state `w` of the round's `Entry` predicts exactly
the symbol the verifier is about to read, provided the read index
`org.center + org.radius + 2` lies in a span `[a, b]` on which `2*h` is a
period of `encoded raw`.

`Entry` pins the verifier: `CaughtScan.aligned` plus `ScanInvariant.rightPos`
give `position w.machine.verifier = org.center + org.radius + 1`, so
`reads_position` is not needed here. The lemma that comes closest to a
*lag-positive* verifier position is `reads_position`, which measures the
displacement along a `Reads` trace; the span containment is therefore left as
the single named hypothesis `hidx`. -/
theorem good_of_periodOn {vm : GalilVM} {w : GalilScaffoldChainWatch.State}
    (org : ReadOrigin raw) (h a b : ℕ)
    (hh : org.interior.length + 1 = h)
    (he : Entry raw org (toOnly vm w))
    (hper : PeriodOn (encoded raw) (2 * h) a b)
    (hcan : canRight w.machine.verifier)
    (hidx : a + 2 * h ≤ org.center + org.radius + 2 ∧
      org.center + org.radius + 2 ≤ b) :
    GalilScaffoldChainWatch.Good w := by
  have hsize : 2 * h ≤ org.radius := by have := org.size; omega
  have hcaught := he.scan.caught
  have hrep : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw :=
    hcaught.verifierRep
  have hpres : w.machine.verifier.head.focus ≠ none := hcaught.verifierPresent
  have hmach : w.machine = org.shifted.machine := he.machine
  -- the verifier sits one place past the current right endpoint
  have hpos : position w.machine.verifier = org.center + org.radius + 1 := by
    have h1 : position w.machine.verifier = position vm.right := hcaught.aligned
    have h2 : position vm.right = org.center + h + (org.radius + 1 - h) := by
      rw [← hh]; exact hcaught.scan.rightPos
    omega
  have hleftlen : 0 < w.machine.verifier.head.left.length :=
    (represented_position w.machine.verifier.head raw hrep hpres).1
  have hnext : position (right w.machine.verifier) = org.center + org.radius + 2 := by
    rw [right_position _ hcan hleftlen, hpos]
  -- the actual read
  have hrrep := right_word w.machine.verifier raw hrep hcan
  have hrpres := right_present w.machine.verifier raw hrep hpres hcan
  have hread : GalilScaffoldInputHead.read (right w.machine.verifier) =
      (encoded raw)[org.center + org.radius + 2]? := by
    rw [represented_read _ raw hrrep hrpres, hnext]
  -- the prediction
  have hb0 : (GalilScaffoldChainSweep.run org.shifted.machine.control []).broken = false := by
    show org.shifted.machine.control.broken = false
    rw [← hmach]; exact hcaught.unbroken
  have hpred := origin_prediction_index org h hh [] (by simp only [List.length_nil]; omega) hb0
  simp only [List.length_nil, Nat.add_zero] at hpred
  rw [← hmach] at hpred
  -- periodicity closes the gap
  have hcycle := hper (org.center + org.radius + 2 - 2 * h) (by omega) (by omega)
  rw [show org.center + org.radius + 2 - 2 * h + 2 * h = org.center + org.radius + 2 from
    by omega] at hcycle
  have hne : GalilScaffoldInputHead.read (right w.machine.verifier) ≠ none := by
    rcases hz : (right w.machine.verifier).head.focus with _ | z
    · exact absurd hz hrpres
    · simp [GalilScaffoldInputHead.read, hz]
  obtain ⟨c, hf⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨hcan, c, ?_, hf⟩
  show GalilScaffoldChainConsume.symbol
    (GalilScaffoldChainSweep.run w.machine.control []).period.focus = some c
  rw [hpred, hcycle, ← hread]
  exact hf

#print axioms good_of_periodOn

/-! ## The iterated step -/

/-- An agreeing consume advances the distance counter by one. -/
theorem consume_distance_succ (c : GalilScaffoldChainConsume.State) (a : Fin 3)
    (ht : GalilScaffoldChainConsume.symbol c.period.focus = some a) :
    value (GalilScaffoldChainConsume.consume c (some a)).distance = value c.distance + 1 := by
  simp [GalilScaffoldChainConsume.consume, ht, inc_value]

/-- **Every prefix of the round's reads is safe.** As long as the verifier's
read indices `org.center + org.radius + 2 + m` stay inside a span `[a, b]`
carrying the period `2*h`, the chain predicts each of them correctly, so no
prefix of `actual` breaks the sweep and the distance counter just counts. -/
theorem sweep_prefix_of_periodOn {vm : GalilVM} {w : GalilScaffoldChainWatch.State}
    (org : ReadOrigin raw) (h a b : ℕ)
    (hh : org.interior.length + 1 = h)
    (he : Entry raw org (toOnly vm w))
    (hper : PeriodOn (encoded raw) (2 * h) a b)
    {actual : List (Fin 3)} {q : PlaceHead}
    (hreads : Reads w.machine.verifier actual q)
    (hsmall : actual.length ≤ 2 * h)
    (hidx : a + 2 * h ≤ org.center + org.radius + 2 ∧
      org.center + org.radius + 1 + actual.length ≤ b) :
    ∀ m, m ≤ actual.length →
      (GalilScaffoldChainSweep.run w.machine.control (actual.take m)).broken = false ∧
        value (GalilScaffoldChainSweep.run w.machine.control (actual.take m)).distance =
          value w.machine.control.distance + m := by
  have hsize : 2 * h ≤ org.radius := by have := org.size; omega
  have hcaught := he.scan.caught
  have hrep : GalilScaffoldInputTrace.Represents w.machine.verifier.head raw :=
    hcaught.verifierRep
  have hpres : w.machine.verifier.head.focus ≠ none := hcaught.verifierPresent
  have hmach : w.machine = org.shifted.machine := he.machine
  have hpos : position w.machine.verifier = org.center + org.radius + 1 := by
    have h1 : position w.machine.verifier = position vm.right := hcaught.aligned
    have h2 : position vm.right = org.center + h + (org.radius + 1 - h) := by
      rw [← hh]; exact hcaught.scan.rightPos
    omega
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨hcaught.unbroken, by simp [GalilScaffoldChainSweep.run]⟩
  | succ m ih =>
    intro hm
    obtain ⟨hb, hd⟩ := ih (by omega)
    have hmlen : m < actual.length := by omega
    have hmtake : (actual.take m).length = m := by
      rw [List.length_take]; omega
    -- the chain's prediction at the read index
    have hsucc : (GalilScaffoldChainSweep.run org.shifted.machine.control
        (actual.take m)).broken = false := by rw [← hmach]; exact hb
    have hpred := origin_prediction_index org h hh (actual.take m)
      (by rw [hmtake]; omega) hsucc
    rw [hmtake, ← hmach] at hpred
    -- the actual input symbol at that read
    have hin := reads_index hreads raw hrep hpres m hmlen
    rw [hpos] at hin
    -- periodicity identifies the two
    have hcycle := hper (org.center + org.radius + 2 - 2 * h + m) (by omega) (by omega)
    rw [show org.center + org.radius + 2 - 2 * h + m + 2 * h =
      org.center + org.radius + 1 + (m + 1) from by omega] at hcycle
    obtain ⟨c, hc⟩ : ∃ c, actual[m]? = some c := ⟨actual[m], List.getElem?_eq_getElem hmlen⟩
    have hsym : GalilScaffoldChainConsume.symbol
        (GalilScaffoldChainSweep.run w.machine.control (actual.take m)).period.focus =
        some c := by rw [hpred, hcycle, ← hin]; exact hc
    have hstep : actual.take (m + 1) = actual.take m ++ [c] := by
      rw [List.take_add_one, hc]; rfl
    rw [hstep, GalilScaffoldChainSweep.run_append]
    have hrun : GalilScaffoldChainSweep.run
        (GalilScaffoldChainSweep.run w.machine.control (actual.take m)) [c] =
        GalilScaffoldChainConsume.consume
          (GalilScaffoldChainSweep.run w.machine.control (actual.take m)) (some c) := rfl
    rw [hrun]
    exact ⟨consume_keeps_unbroken _ c hsym hb,
      by rw [consume_distance_succ _ c hsym, hd]; push_cast; ring⟩

/-- **The lag-positive catch-up run.** Mirroring `found_watch_run`, but for a
re-shift round: with the read indices inside a `2*h`-periodic span, the
verifier's `actual` reads are all `Good` steps of the watch controller, so a
watch state carrying the round's machine and lag `v` performs
`actual.length` background `Internal.take` ticks unbroken, lowering the lag
by one per read and leaving the margin alone. -/
theorem good_run_of_periodOn {vm : GalilVM} {w : GalilScaffoldChainWatch.State}
    (org : ReadOrigin raw) (h a b : ℕ)
    (hh : org.interior.length + 1 = h)
    (he : Entry raw org (toOnly vm w))
    (hper : PeriodOn (encoded raw) (2 * h) a b)
    {actual : List (Fin 3)} {q : PlaceHead}
    (hreads : Reads w.machine.verifier actual q)
    (hsmall : actual.length ≤ 2 * h)
    (hidx : a + 2 * h ≤ org.center + org.radius + 2 ∧
      org.center + org.radius + 1 + actual.length ≤ b)
    (v : ℕ) (hv : actual.length ≤ v) (margin : Counter) :
    ∃ z, GalilScaffoldChainWatch.Run ⟨w.machine, ofNat v, margin⟩
        (List.replicate actual.length false)
        ⟨z, ofNat (v - actual.length), margin⟩ ∧
      z.control.broken = false ∧
      GalilScaffoldInputTrace.Represents z.verifier.head raw ∧
      value z.control.distance = value w.machine.control.distance + actual.length := by
  have hcaught := he.scan.caught
  obtain ⟨hb, hd⟩ := sweep_prefix_of_periodOn org h a b hh he hper hreads hsmall hidx
    actual.length (le_refl _)
  rw [List.take_length] at hb hd
  have hrun := GalilScaffoldChainVerifyRun.realize hreads w.machine.control
  have hwatch := verify_watch_run hrun hb (v - actual.length) margin
  rw [show actual.length + (v - actual.length) = v from by omega] at hwatch
  exact ⟨⟨q, GalilScaffoldChainSweep.run w.machine.control actual⟩, hwatch, hb,
    reads_word hreads raw hcaught.verifierRep, hd⟩

#print axioms consume_keeps_unbroken
#print axioms consume_distance_succ
#print axioms origin_prediction_index
#print axioms sweep_prefix_of_periodOn
#print axioms good_run_of_periodOn

end PalPeg.GalilScaffoldChainInputSupply
