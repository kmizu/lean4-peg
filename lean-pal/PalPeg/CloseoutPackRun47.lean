import PalPeg.CloseoutPackRun44

/-!
# `CloseoutPackRun47`: `LagPos` is *refuted*, and `ConsumeAvail` re-based on the
  target's supply

`CloseoutPackRun44` closed `ConsumeAvail` modulo the named side condition
`LagPos` (`0 < value wch.lag` for a watching chain) and proposed to *home* it by
strengthening the `watch` clause of `CloseoutPackRun41.ChainPositionLedger`.  **That fix
cannot work.**  This file shows why, with two structural obstructions, and then
gives the repair.

* §1 **Obstruction A (`ChainStep`/`Internal.take`).**  `take`'s guard is only
  `positive s.lag = true`, i.e. `0 < value lag`, and the target lag is
  `dec s.lag`.  At `value lag = 1` the target lag is **`0`**, and the target is
  still a `.watch` state (`caught s`).  So a `0 < value lag` watch clause is not
  preserved by `chainPos_step`.
* §2 **Obstruction B (`ChainMatched`/`Outer.immediate`).**  Far worse: the
  `immediate` consume — the *other* place `ConsumeAvail` is used — is guarded by
  `zero s.lag = true`, i.e. `value lag = 0`.  So a strengthened `ChainPos'` is
  outright **false** at exactly the states where the machine performs an
  immediate consume; `chainPos'_matched` would close that case vacuously and
  `ChainPos'` could never be established there.
* §3 **The repair.**  `LagPos` is replaced by the *true* fact
  `LagNonneg` (`0 ≤ value lag`) plus supply **one cell ahead of the scan
  front** — which is not a fact of the source state but *is* available at the
  landing: `H_MatchLandingChainLedger`'s target is measured at `right s.right`, whose
  `canR` field is exactly `position (right s.right) ≠ 2·|w|`.
  `consumeAvail_of_next_supply` proves `ConsumeAvail` from it.
* §4 `bgStartP2_of_centre` reduces `CloseoutPackRun44.BgStartP2` to a single
  *centre-head* obligation `CentreLedger` (`canRight center`, `Sane center`,
  `position center + value radius = position right`) plus the scan supply
  `canRight right` and the radius ledger.  Note `LPackM2.scanGeomR`'s
  `ScanInvariant` alone is **not** enough: it gives `position right =
  position center + rad` for *some* `rad` with only `value radius ≤ rad`, and
  says nothing about `canRight`/`Sane` of the centre head.

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun47

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono
open PalPeg.CloseoutPackRun26 PalPeg.CloseoutPackRun41 PalPeg.CloseoutPackRun44

/-! ## 1. Obstruction A: a `take` can drive the lag to zero -/

/-- The lag after a `take` is one less. -/
theorem caught_lag (w : GalilScaffoldChainWatch.State) :
    value (GalilScaffoldChainWatch.caught w).lag = value w.lag - 1 :=
  dec_value w.lag

/-- **Obstruction A.**  A `take` is enabled at `value lag = 1` (its guard is
`positive lag`), it produces a `.watch` target, and that target's lag is `0`.
So no `0 < value lag` strengthening of `ChainPositionLedger`'s `watch` clause survives
`chainPos_step`. -/
theorem take_lag_vanishes {w : GalilScaffoldChainWatch.State}
    (hcan : Canonical w.lag) (h1 : value w.lag = 1) (hg : GalilScaffoldChainWatch.Good w) :
    GalilScaffoldChainWatch.Internal w (GalilScaffoldChainWatch.caught w) ∧
      ChainStep (.watch w) (.watch (GalilScaffoldChainWatch.caught w)) ∧
      ¬ (0 < value (GalilScaffoldChainWatch.caught w).lag) := by
  have hp : positive w.lag = true := (positive_iff w.lag hcan).2 (by omega)
  refine ⟨.take w hp hg, .watchStep _ _ (.take w hp hg), ?_⟩
  rw [caught_lag]; omega

#print axioms take_lag_vanishes

/-! ## 2. Obstruction B: an `immediate` consume *requires* a zero lag -/

/-- **Obstruction B.**  The only `ChainMatched` transition that moves the
verifier (and hence the only other user of `ConsumeAvail`) is
`Outer.immediate`, whose guard is `zero lag = true`.  Hence at every state
where it fires the lag is `0`, and `0 < value lag` is *false* there. -/
theorem immediate_needs_zero_lag {w w' : GalilScaffoldChainWatch.State}
    (ho : GalilScaffoldChainWatch.Outer w true w')
    (hne : w' ≠ GalilScaffoldChainWatch.queued w)
    (hcan : Canonical w.lag) : value w.lag = 0 := by
  cases ho with
  | queued hz => exact absurd rfl hne
  | immediate hz hg => exact (zero_iff w.lag hcan).1 hz

/-- The contrapositive form actually used: a strengthened `ChainPositionLedger` (one
carrying `0 < value lag` in its `watch` clause) is inconsistent with the
enabledness of an `immediate` consume. -/
theorem lagPos_contradicts_immediate {w w' : GalilScaffoldChainWatch.State}
    (ho : GalilScaffoldChainWatch.Outer w true w')
    (hne : w' ≠ GalilScaffoldChainWatch.queued w)
    (hcan : Canonical w.lag) (hpos : 0 < value w.lag) : False := by
  have := immediate_needs_zero_lag ho hne hcan; omega

#print axioms immediate_needs_zero_lag
#print axioms lagPos_contradicts_immediate

/-! ## 3. The repair: `LagNonneg` plus one-cell-ahead supply -/

/-- **(NAMED) `LagNonneg`.**  The *true* replacement for `LagPos`: the lag of a
watching chain is never negative.  (The chain never owes the scan front cells
it has not seen; `Canonical`-plus-`positive`-guard discipline keeps it so.) -/
def LagNonneg (z : ChainVM) : Prop :=
  ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch → 0 ≤ value wch.lag

/-- **`ConsumeAvail` from supply one cell past the scan front.**  `R` is the
source right head, `R'` any represented, present head with
`position R' = position R + 1` and `canRight R'` — at a matched landing this is
the *target's* right head and its `ScanPositionPayloadWithChainLedger.canR`.  With the Run41 ledger
`position ver + lag = position R` and `0 ≤ lag`, the moved verifier sits at
`position ver + 1 ≤ position R + 1 = position R' < 2·|w|`. -/
theorem consumeAvail_of_next_supply {w : List (Fin 2)} {z : ChainVM} {R R' : PlaceHead}
    (hrepR' : GalilScaffoldInputTrace.Represents R'.head w) (hfocR' : R'.head.focus ≠ none)
    (hcR' : canRight R') (hstep : position R' = position R + 1)
    (hrepV : ∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
      GalilScaffoldInputTrace.Represents wch.machine.verifier.head w ∧
        wch.machine.verifier.head.focus ≠ none)
    (hlag : LagNonneg z) (hP : ChainPositionLedger z (position R)) : ConsumeAvail z := by
  intro wch hw
  obtain ⟨hcv, hsv, hpv⟩ := hP.watch wch hw
  obtain ⟨hrv, hfv⟩ := hrepV wch hw
  have hlv : 0 < wch.machine.verifier.head.left.length :=
    (PalPeg.CloseoutLPack3.present_iff_left hrv).1 hfv
  have hposv : position (right wch.machine.verifier) = position wch.machine.verifier + 1 :=
    right_position wch.machine.verifier hcv hlv
  obtain ⟨hrr, hfr⟩ := PalPeg.CloseoutLPack3.lrep_right hrv hfv hcv
  have hR'ne : position R' ≠ 2 * w.length := fun h =>
    ((PalPeg.GalilEndOfInput.not_canRight_iff R' w hrepR' hfocR').2 h) hcR'
  have hR'le : position R' ≤ 2 * w.length := position_le_of_represents hrepR'
  have hlag' : 0 ≤ value wch.lag := hlag wch hw
  by_contra hnc
  have heq : position (right wch.machine.verifier) = 2 * w.length :=
    (PalPeg.GalilEndOfInput.not_canRight_iff _ w hrr hfr).1 hnc
  rw [hposv] at heq
  omega

#print axioms consumeAvail_of_next_supply

/-! ## 4. `BgStartP2` from a centre-head ledger -/

section Bg
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **(NAMED) `CentreLedger`.**  The chain-start shape puts the *centre* head in
the verifier slot and `radius` in the lag slot, so `ChainPositionLedger` at the new `copy`
chain is exactly this.  `LPackM2.scanGeomR` does **not** supply it: its
`ScanInvariant` knows `position right = position center + rad` for some `rad`
with only `value radius ≤ rad`, and nothing at all about `canRight`/`Sane` of
the centre head. -/
def CentreLedger (s : GalilVM) : Prop :=
  canRight s.center ∧ Sane s.center ∧
    (position s.center : ℤ) + value s.radius = position s.right

/-- **`BgStartP2` from the centre ledger plus the scan supply and the radius
ledger.**  Background keeps the heads, the centre and the radius
(`backgroundS_fields`), and with an idle source chain `backgroundS_idle` says
the target chain is either idle (excluded by `hni`) or
`chainStart answer (P.centre s) (P.place s) s.center s.radius`, a `copy` chain
whose verifier is `s.center` and whose lag is `s.radius`. -/
theorem bgStartP2_of_centre {w : List (Fin 2)}
    (hav : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      canRight s.right)
    (hrad : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      ∀ rad : ℕ, ScanInvariant w (position s.center) rad s.left s.right →
        value s.radius ≤ (rad : ℤ))
    (hcen : ∀ (c : Control) (s : GalilVM), c.mode = Mode.scan → ChainPositionInvariantWithShiftPhase w c s →
      CentreLedger s) :
    BgStartP2 centre place entry q first w := by
  intro c s t hm hx hi hb hs hni
  obtain ⟨hl, hr, -, hcenf, -, hradf, -⟩ :=
    backgroundS_fields (PofC centre place entry w) q first hb
  obtain ⟨hc1, hc2, hc3⟩ := hcen c s hm hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hr]; exact hav c s hm hx
  · rw [hcenf, hl, hr, hradf]; exact hrad c s hm hx
  · rcases backgroundS_idle (PofC centre place entry w) q first hb hi with ⟨-, hz⟩ | ⟨-, hz⟩
    · exact absurd hz hni
    · rw [hz, hr]
      refine ⟨(fun _ hw => by cases hw), (fun _ _ _ _ _ hbk => by cases hbk),
        fun _ _ _ _ _ _ _ hcp => ?_⟩
      unfold chainStart at hcp
      injection hcp with _ _ _ _ h5 _ h7
      subst h5; subst h7
      exact ⟨hc1, hc2, hc3⟩

end Bg

#print axioms bgStartP2_of_centre

end PalPeg.CloseoutPackRun47
