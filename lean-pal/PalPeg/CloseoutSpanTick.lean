import PalPeg.GalilSpanCounter
import PalPeg.CloseoutLenNonneg

/-!
# `SpanRep` is a tick invariant, hence `0 ≤ value length` is

`CloseoutPackRun17.marks_steps` — the `H_marksEntry'`-free marks route — needs
`hfl : 0 ≤ value z.vm.length` at the run's `scan` states.  Two earlier attempts
in this development got this wrong:

1. "`length` is never decremented" — false: `shiftTick`
   (`GalilScaffoldChainInputSupply:1445`) sets `length := dec (dec s.length)`.
2. "so it is not a tick invariant" — also false: `shiftTick` decrements
   `radius` at the same time, and `GalilSpanCounter.spanRepS_shiftTick` shows
   the *relation* `value length = 2 * value radius + 1` survives.

`SpanRep` is the right invariant, and `GalilSpanCounter` already has a transport
lemma for every shape that touches the pair:

| tick shape | lemma |
|---|---|
| `scan_match` | `spanRep_afterCompare`, `spanRep_replayDec` |
| `scan_wait` / `scan_count` | `spanRep_background` |
| `shift_one` | `spanRepS_shiftTick` |
| `restart` | `spanRep_restart` |
| `init` | `spanRep_of_init` |
| `scan_fallback` | `spanRep_of_fallback` |

This file records the two consequences that the marks route actually consumes:
`SpanRep` plus a non-negative radius gives `0 < value length`, and `RadiusRep`
supplies the radius half.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutSpanTick

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter
open PalPeg.GalilInvPlus

/-- **`0 < value s.length` from `SpanRep` and a non-negative radius.**  This is
the shape `marks_steps`' `hfl` needs, stated without `EntryCounters`. -/
theorem lenPos_of_spanRep {s : GalilVM} (hS : SpanRep s) (hr : 0 ≤ value s.radius) :
    0 < value s.length := by
  unfold SpanRep at hS
  omega

/-- The same, weakened to `≤`. -/
theorem lenNonneg_of_spanRep {s : GalilVM} (hS : SpanRep s) (hr : 0 ≤ value s.radius) :
    0 ≤ value s.length :=
  le_of_lt (lenPos_of_spanRep hS hr)

/-- `RadiusRep` gives the radius half. -/
theorem radiusNonneg_of_radiusRep {r : Counter} {Rad : ℕ} (h : RadiusRep r Rad) :
    0 ≤ value r := by
  rw [h.2]; exact Int.natCast_nonneg Rad

/-- **`0 ≤ value length` from `SpanRep` and `RadiusRep`.**  The two halves the
invariant actually carries. -/
theorem lenNonneg_of_span_radius {s : GalilVM} {Rad : ℕ}
    (hS : SpanRep s) (hR : RadiusRep s.radius Rad) : 0 ≤ value s.length :=
  lenNonneg_of_spanRep hS (radiusNonneg_of_radiusRep hR)

#print axioms lenPos_of_spanRep
#print axioms radiusNonneg_of_radiusRep
#print axioms lenNonneg_of_span_radius

end PalPeg.CloseoutSpanTick
