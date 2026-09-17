import PalPeg.CloseoutPackRun23
import PalPeg.CloseoutPackRun19
import PalPeg.CloseoutPackRun20
import PalPeg.CloseoutPackRun21
import PalPeg.CloseoutPackRun24

/-!
# `CloseoutPackRun29`: the shift entry of `LPackM2`, and `BigResid6` from it

## §1 `shiftEntry_of_guard`

`CloseoutPackRun23.LTickLeaves2.shiftEntry` asks for `ShiftGeom w t` at the
`beginShift` landing of a `scan_shift` tick.  Everything positional is in the
pack: the scan invariant at the source (`LPackM.scanGeom`), `canRight R`
(`LTickLeavesN.scanCanR`), and the landing's heads (`t.left = left L`,
`t.center = C`, `t.right = right R`, `t.remaining = ofNat (periodLength wch)`
by `beginShiftVM`).  What is **not** in the pack is the palindrome at the
destination centre `position C + periodLength wch` of radius
`r₀ + 1 − periodLength wch` — the whole-round content of
`GalilScaffoldChainReadOrigin.reshift_palindrome`, which needs a `ReadOrigin`
(the chain's read history since its start), an `OnlyScan` state and a
`Trace` of the watching machine; none of these is a one-state fact.  That is
the single named hypothesis `ShiftPal` (§1), together with the two side
bounds `1 ≤ periodLength wch` (the period tape is non-empty) and
`periodLength wch ≤ r₀ + 1` (which `CloseoutPackRun24.WatchShift` implies
via `4·h ≤ distance ≤ 2·r₀`).

## §2 `bigResid6_of_lpackM2`

`BigResid6` from `LPackM2` at every pack state and `WatchShift` at every
state, by `CloseoutPackRun19.bigResid6_of_leaves` with the four `LPackM2`
contracts of `CloseoutPackRun23`, `rInitPackM_of_pack` (unconditional),
`rReplayPackM_of_pack`, `rChoosePackL_of_pack`, `rShiftNext_of_pack`.

## §3 `lpackM2_on_pack_of_run`

`LPackM2` at every pack state from `lpackM2_steps`, provided every
`BigPack2M` state *is* a state of the pre-loaded trace (`H_packOnRun`).

Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRun29

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFrontMono PalPeg.GalilFinalAssembly
open PalPeg.CloseoutLPack PalPeg.CloseoutLPack3 PalPeg.CloseoutLPack4 PalPeg.CloseoutLPack5
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun10 PalPeg.CloseoutPackRun11
open PalPeg.CloseoutPackRun19 PalPeg.CloseoutPackRun20 PalPeg.CloseoutPackRun21
open PalPeg.CloseoutPackRun23 PalPeg.CloseoutPackRun24

/-! ## 0. Small facts -/

/-- A head off the clipped origin is `Sane`. -/
theorem sane_of_pos' {p : PlaceHead} (h : 0 < position p) : Sane p := by
  rcases p with ⟨hd, g⟩
  cases g with
  | true => exact Or.inl rfl
  | false =>
    right
    simp only [position, Bool.false_eq_true, if_false] at h
    show 0 < hd.left.length
    omega

section Entry
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## 1. The one named hypothesis and the shift entry -/

/-- **(NAMED) the whole-round palindrome at a shift entry.**  At a scan state
`s` whose comparison target `s'` watches `wch` and passes the shift guard, for
the scan radius `r₀` at `s`: the period is non-empty, at most `r₀ + 1`, and
the palindrome of radius `r₀ + 1 − periodLength wch` is known at the
destination centre `position C + periodLength wch`.  Content:
`GalilScaffoldChainReadOrigin.reshift_palindrome`. -/
def ShiftPal (w : List (Fin 2)) (s : GalilVM) : Prop :=
  ∀ s' : GalilVM,
    (galilFrameS (PofC centre place entry w) q first).compare s s' →
    ∀ wch : GalilScaffoldChainWatch.State, s'.chain = .watch wch →
    shiftGuardVM s' →
    ∀ r₀ : ℕ, ScanInvariant w (position s.center) r₀ s.left s.right →
      1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
      Manacher.PalAt (encoded w) (position s.center + periodLength wch)
        (r₀ + 1 - periodLength wch)

/-- **`ShiftGeom` at the `beginShift` landing** from the scan invariant at the
source, `canRight R`, and `ShiftPal`. -/
theorem shiftEntry_of_guard {w : List (Fin 2)} {s s' t : GalilVM} {r₀ : ℕ}
    (hi : ScanInvariant w (position s.center) r₀ s.left s.right)
    (hcan : canRight s.right)
    (hSP : ShiftPal centre place entry q first w s)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s')
    (hmt : ¬ (galilFrameS (PofC centre place entry w) q first).matched s')
    (hg : (galilFrameS (PofC centre place entry w) q first).shiftGuard s')
    (hb : (galilFrameS (PofC centre place entry w) q first).beginShift s' t) :
    ShiftGeom w t := by
  obtain ⟨vs, vq, hvl, hvr, rfl⟩ :=
    compare_mismatch_form centre place entry q first hcmp hmt
  obtain ⟨wch, hchain, ht⟩ :
    beginShiftVM' (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) t := hb
  have hg' : shiftGuardVM (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found)) s.chain) (afterMismatch s vs vq)) := hg
  obtain ⟨h1, hle, hpal⟩ := hSP _ hcmp wch hchain hg' r₀ hi
  have htl : t.left = GalilScaffoldInputHead.left s.left := by
    rw [ht, afterBirth_left, afterMismatch_left]; exact hvl
  have htr : t.right = GalilScaffoldChainVerifier.right s.right := by
    rw [ht, afterBirth_right, afterMismatch_right]; exact hvr
  have htc : t.center = s.center := by rw [ht, afterBirth_center, afterMismatch_center]
  have htm : t.remaining = ofNat (periodLength wch) := by rw [ht]
  have hLpos : 1 ≤ position s.left := scanInv_pos hi
  have hLp := hi.leftPos
  have hRp := hi.rightPos
  have hCpos : 0 < position s.center := by omega
  have hRs := right_sane hcan (sane_of_rep hi.rightRep hi.rightPresent)
  have hlpos := CloseoutPackRun13.position_left s.left
  refine ⟨periodLength wch, r₀ + 1 - periodLength wch, htm, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [htl]; exact represents_left hi.leftRep hi.leftPresent
  · rw [htr]; exact right_word _ w hi.rightRep hcan
  · rw [htr]; exact right_present _ w hi.rightRep hi.rightPresent hcan
  · rw [htl]; exact left_sane (by omega)
  · rw [htc]; exact sane_of_pos' hCpos
  · rw [htl, htc]; omega
  · rw [htr, htc, hRs.1]; omega
  · rw [htl]; omega
  · rw [htc]; exact hpal

/-- **`LTickLeaves2` from `LPackM2`, `LTickLeavesN` and `ShiftPal`.** -/
theorem lTickLeaves2_of_shiftPal {w : List (Fin 2)} {c : Control} {s : GalilVM}
    (hP : LPackM2 w c s) (hL : LTickLeavesN centre place entry q first w c s)
    (hSP : ShiftPal centre place entry q first w s) :
    LTickLeaves2 centre place entry q first w c s where
  shiftEntry := fun hm hr s' t hcmp hmt hg hb => by
    obtain ⟨r₀, hi⟩ := hP.packM.scanGeom hm hr
    exact shiftEntry_of_guard centre place entry q first hi (hL.scanCanR hm) hSP hcmp hmt hg hb

/-! ## 2. `BigResid6` from `LPackM2` on the pack and `WatchShift` -/

/-- **`BigResid6` from `LPackM2` at every pack state and `WatchShift`.** -/
theorem bigResid6_of_lpackM2 {w : List (Fin 2)}
    (hall : ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm)
    (hws : ∀ y : State GalilVM, WatchShift centre place entry q first w y) :
    BigResid6 centre place entry q first w :=
  bigResid6_of_leaves centre place entry q first
    (scanGeomReplay_of_lpackM2 centre place entry q first hall)
    (shiftDoneGeom_of_lpackM2 centre place entry q first hall)
    (rInitPackM_of_pack centre place entry q first)
    (rChoosePackL_of_pack centre place entry q first
      (rrepChoose_of_lpackM2 centre place entry q first hall))
    (rReplayPackM_of_pack centre place entry q first
      (centreReplay_of_lpackM2 centre place entry q first hall))
    (rShiftNext_of_pack centre place entry q first hws)

/-! ## 3. `LPackM2` on the pack along a run -/

/-- **(NAMED) every pack state is a state of the pre-loaded trace.**  This is
what links the predicate `BigPack2M` to the run `st`; `lpackM2_steps` speaks
only about `st i`. -/
def H_packOnRun (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ) : Prop :=
  ∀ x : State GalilVM, BigPack2M centre place entry q first w x →
    ∃ i, i ≤ Tc w.length ∧ x = st i

/-- **`LPackM2` at every pack state** from the tick induction, given the
leaves along the trace and `H_packOnRun`. -/
theorem lpackM2_on_pack_of_run {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesN centre place entry q first w (st i).ctl (st i).vm ∧
      AuxPack (st i).ctl (st i).vm ∧
      LTickLeaves2 centre place entry q first w (st i).ctl (st i).vm)
    (hon : H_packOnRun centre place entry q first w st Tc) :
    ∀ x : State GalilVM, BigPack2M centre place entry q first w x → LPackM2 w x.ctl x.vm := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := hon x hx
  exact lpackM2_steps centre place entry q first hP hLv i hi

/-- `BigResid6` along a run: `LPackM2` leaves on the trace, `H_packOnRun`,
and `WatchShift`. -/
theorem bigResid6_of_run {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc)
    (hLv : ∀ i, i ≤ Tc w.length →
      LTickLeavesN centre place entry q first w (st i).ctl (st i).vm ∧
      AuxPack (st i).ctl (st i).vm ∧
      LTickLeaves2 centre place entry q first w (st i).ctl (st i).vm)
    (hon : H_packOnRun centre place entry q first w st Tc)
    (hws : ∀ y : State GalilVM, WatchShift centre place entry q first w y) :
    BigResid6 centre place entry q first w :=
  bigResid6_of_lpackM2 centre place entry q first
    (lpackM2_on_pack_of_run centre place entry q first hP hLv hon) hws

end Entry

#print axioms sane_of_pos'
#print axioms shiftEntry_of_guard
#print axioms lTickLeaves2_of_shiftPal
#print axioms bigResid6_of_lpackM2
#print axioms lpackM2_on_pack_of_run
#print axioms bigResid6_of_run

end PalPeg.CloseoutPackRun29
