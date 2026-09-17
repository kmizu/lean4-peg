import PalPeg.CloseoutPackRun41

/-!
# `CloseoutPackRun44`: discharging `ConsumeAvail`, and the background landing

`CloseoutPackRun41` cut the chain-local positional ledger `ChainPosInv2` and
left five input-supply–shaped leaves.  This file attacks the first two.

* §1 `position_le_of_represents`: a represented head never sits past the last
  cell `2·|w|` of `encoded w`.  (`GalilEndOfInput.not_canRight_iff` gives the
  *equality* case; this is the missing inequality.)
* §2 `consumeAvail_of_supply` **closes `ConsumeAvail`** from the pack's supply
  facts: `Extra3.scanAvail` (`canRight s.right`), the `lrep` pair for the right
  head and for the chain's verifier, the Run41 ledger
  `position ver + lag = position right`, and a **positive lag**.  The verifier
  trails the right head, so `canRight (right ver)` reduces to
  `position ver + 1 ≠ 2·|w|`, which follows from
  `position ver + 1 ≤ position right < 2·|w|`.
  The positive-lag side condition is named `LagPos` — at `lag = 0` the verifier
  *is* the right head and `canRight (right ver)` is supply **one cell ahead**,
  which no fact at the source state can give.
* §3 `h_bgP2_of_start` **reduces `H_bgP2` to the chain-start shape alone**
  (`BgStartP2`): when the source chain is live the background tick keeps
  `left`/`right`/`center`/`radius` (`backgroundS_fields`) and moves the chain by
  a plain `ChainStep` (`backgroundS_chainTick`), so `canR`/`radLe` transport by
  rewriting and `chainPos` is `chainPos_step`.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun44

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun41

/-! ## 1. A represented head never passes the final cell -/

/-- **The missing half of `GalilEndOfInput.not_canRight_iff`.**  `position p`
indexes `encoded w`, whose last index is `2·|w|`; the left stack of a
represented head is a prefix of `w`. -/
theorem position_le_of_represents {w : List (Fin 2)} {p : PlaceHead}
    (hh : GalilScaffoldInputTrace.Represents p.head w) : position p ≤ 2 * w.length := by
  obtain ⟨xs, rs, q, hlay, hw⟩ := hh
  have hl : p.head.left.length = xs.length := by
    rw [hlay]; exact PalPeg.GalilEndOfInput.layout_left_length xs (rs.map some) q
  have hle : xs.length ≤ w.length := by
    rw [hw]; simp only [List.length_append, List.length_reverse]; omega
  unfold position
  split <;> omega

#print axioms position_le_of_represents

/-! ## 2. `ConsumeAvail` from the supply facts -/

/-- **(NAMED) `LagPos`.**  A watching chain owes at least one unit of lag.
This is the *only* residue of `ConsumeAvail`: at `lag = 0` the verifier sits on
the right head itself, so `canRight (right ver)` is availability one cell past
the scan front — supply at the *next* state, which no fact at the source can
give.  The natural home is the `watch` clause of `ChainPos`, strengthened to
carry `0 < value wch.lag`. -/
def LagPos (z : ChainVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch → 0 < value wch.lag

/-- **`ConsumeAvail` is discharged by the input supply.**  `hcR` is
`Extra3.scanAvail`, `hrepR`/`hfocR` the right head's `lrep` pair, `hrepV` the
verifier's (`CloseoutPackRun37.verifierRep` / `GalilReplaySpan`), `hP` the
Run41 ledger, and `hlag` the named `LagPos`. -/
theorem consumeAvail_of_supply {w : List (Fin 2)} {z : ChainVM} {R : PlaceHead}
    (hrepR : GalilScaffoldInputTrace.Represents R.head w) (hfocR : R.head.focus ≠ none)
    (hcR : canRight R)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hlag : LagPos z) (hP : ChainPos z (position R)) : ConsumeAvail z := by
  intro wch hw
  obtain ⟨hcv, hsv, hpv⟩ := hP.watch wch hw
  obtain ⟨hrv, hfv⟩ := hrepV wch hw
  have hlv : 0 < wch.machine.verifier.head.left.length :=
    (PalPeg.CloseoutLPack3.present_iff_left hrv).1 hfv
  have hposv : position (right wch.machine.verifier) = position wch.machine.verifier + 1 :=
    right_position wch.machine.verifier hcv hlv
  obtain ⟨hrr, hfr⟩ := PalPeg.CloseoutLPack3.lrep_right hrv hfv hcv
  -- the right head is strictly inside the encoded word
  have hRne : position R ≠ 2 * w.length := fun h =>
    ((PalPeg.GalilEndOfInput.not_canRight_iff R w hrepR hfocR).2 h) hcR
  have hRle : position R ≤ 2 * w.length := position_le_of_represents hrepR
  have hlag' : 0 < value wch.lag := hlag wch hw
  by_contra hnc
  have heq : position (right wch.machine.verifier) = 2 * w.length :=
    (PalPeg.GalilEndOfInput.not_canRight_iff _ w hrr hfr).1 hnc
  rw [hposv] at heq
  omega

#print axioms consumeAvail_of_supply

/-! ## 3. `H_bgP2` reduced to the chain-start shape -/

section Bg
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `BgStartP2`.**  `H_bgP2` restricted to the one shape Run41 could
not reach: the source chain is *idle*, so there is no source payload and the
target chain is `chainStart` — whose verifier is the centre head and whose lag
is `s.radius`, i.e. the obligation is the scan geometry
`position center + radius = position right` (plus `canRight center`,
`Sane center`) together with the scan-mode supply and the radius ledger.  The
natural home is an `LPackM2.scanGeomR`-shaped pack field. -/
def BgStartP2 (w : List (Fin 2)) : Prop :=
  ∀ (c : Control) (s t : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
    s.chain = ChainVM.idle →
    (galilFrameS (PofC centre place entry w) q first).background s t →
    ScanNR ⟨c, t⟩ → t.chain ≠ ChainVM.idle → PosPayload2 w t

/-- **`H_bgP2` from the chain-start shape plus `ConsumeAvail`.**  With a live
source chain every component transports: `backgroundS_fields` keeps
`left`/`right`/`center`/`radius`, so `canR` and `radLe` are literally the
source's, and `backgroundS_chainTick` makes the chain effect a plain
`ChainStep`, which `chainPos_step` pushes through. -/
theorem h_bgP2_of_start {w : List (Fin 2)}
    (hav : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPosInv2 w c s →
      ConsumeAvail s.chain)
    (hstart : BgStartP2 centre place entry q first w) :
    H_bgP2 centre place entry q first w := by
  intro c s t hm hx hb hs hni
  by_cases hi : s.chain = ChainVM.idle
  · exact hstart c s t hm hx hi hb hs hni
  · have P : PosPayload2 w s := hx.payload hs hi
    obtain ⟨hl, hr, -, hcen, -, hrad, -⟩ :=
      backgroundS_fields (PofC centre place entry w) q first hb
    have hstep : ChainStep s.chain t.chain := by
      obtain ⟨y, hst, hy⟩ :=
        backgroundS_chainTick (PofC centre place entry w) q first hb hi
      simp only [Bool.false_eq_true, ↓reduceIte] at hy
      rw [hy]; exact hst
    refine ⟨?_, ?_, ?_⟩
    · rw [hr]; exact P.canR
    · rw [hcen, hl, hr, hrad]; exact P.radLe
    · rw [hr]
      exact chainPos_step P.chainPos (hav c s hm hx) hstep

end Bg

#print axioms h_bgP2_of_start

end PalPeg.CloseoutPackRun44
