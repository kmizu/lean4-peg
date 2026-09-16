import PalPeg.GalilRoundConstruct
import PalPeg.GalilSharedFunctional
import PalPeg.GalilFrontier
import PalPeg.GalilShiftH

/-!
# L7c(ii) — the shift block `ShiftPack` at a mismatching terminal

`GalilRoundConstruct.round_scan_construct` leaves the shift half of a round as
the named hypothesis `hpack : … → ShiftPack P h s1 w`.  This module discharges
it for the concrete shareds `sharedC` / `sharedFun`, whose `shiftGuard` is
`shiftGuardVM` and whose `beginShift` is `beginShiftVM'`.

`ShiftPack P h s1 w` has three components:

* the prediction `read (right s1.right) = symbol w…period.focus`;
* `Canonical s1.length`;
* for every comparison result `vs`/`vq` that passes the shift guard, a shift
  entry `s2` with `beginShiftVM h w`, `CopyIdle s2`, and a `ShiftRun` of `h`
  unit head moves.

The entry is *constructed*, not obtained from the guard: `beginShiftVM h w` is
an equation once `h = periodLength w` (which is what `beginShiftVM'` pins,
`GalilShiftH.beginShiftVM_periodLength`) and once the compared chain is the
round's own watch `w`.  The `h` unit moves come from the scan invariant:
`bounded_right_moves` for the centre, `shifted_left_moves` for the left head,
`reads_shift_heads` to synchronise them and `shift_heads_counters` to attach
the counters.

The one hypothesis that is *not* discharged is `hlock` — see its docstring.
-/

set_option autoImplicit false
namespace PalPeg.GalilShiftPack

open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRoundConstruct
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
open GalilScaffoldChainVerifier

/-! ## The centre head of a scan state -/

/-- `ScanInv`'s `centre` field is a concrete layout, so the centre head
represents the input and its focus is present. -/
theorem centre_rep {raw : List (Fin 2)} {s : GalilVM} {r : ℕ} (hi : ScanInv raw s r) :
    GalilScaffoldInputTrace.Represents s.center.head raw ∧ s.center.head.focus ≠ none := by
  obtain ⟨a, ls, rs, q, gap, hc, hraw⟩ := hi.centre
  refine ⟨⟨a :: ls, rs, q, ?_, hraw⟩, ?_⟩
  · rw [hc]; rfl
  · rw [hc]; simp [represent, layout]

/-! ## The `h` unit head moves -/

/-- **The head side condition.**  A scan state whose radius is at least the
semiperiod `h ≥ 1` has room for `h` centre moves and `2*h` left-head moves:
the centre ends at `position center + h ≤ position center + radius`, the left
head at `position left + 2*h - 1 ≤ position center + radius - 1`, and
`position center + radius < |encoded raw|` is the `PalAt` bound carried by
`ScanInvariant`. -/
theorem shiftHeads_of_scan (raw : List (Fin 2)) (cen l r : PlaceHead) (radius h : ℕ)
    (hcrep : GalilScaffoldInputTrace.Represents cen.head raw)
    (hcpres : cen.head.focus ≠ none)
    (hinv : ScanInvariant raw (position cen) radius l r)
    (hpos : 0 < h) (hle : h ≤ radius) :
    ∃ ce le, ShiftHeads cen (left l) h ce le := by
  have hrad : radius ≤ position cen := hinv.palindrome.1
  have hbnd : position cen + radius < (encoded raw).length := hinv.palindrome.2.1
  have hlpos : position l = position cen - radius := hinv.leftPos
  obtain ⟨cw, ce, hcr, hcl, -, -, -⟩ :=
    bounded_right_moves cen raw hcrep hcpres h (by omega)
  obtain ⟨lw, le, hlr, hll, -, -, -⟩ :=
    shifted_left_moves l raw hinv.leftRep hinv.leftPresent (2 * h - 1) (by omega)
  refine ⟨ce, le, ?_⟩
  have hsync : ShiftHeads cen (left l) cw.length ce le :=
    reads_shift_heads hcr hlr (by omega)
  rwa [hcl] at hsync

/-- The `ShiftRun` of `h` unit steps that `ShiftPack` asks for, with the
counters the round's terminal leaves (`remaining := ofNat h`, the compared
radius `inc s1.radius` and `inc (inc s1.length)`). -/
theorem shiftRun_of_scan (raw : List (Fin 2)) (s1 : GalilVM) (radius h : ℕ)
    (hi : ScanInv raw s1 radius) (hpos : 0 < h) (hle : h ≤ radius) :
    ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t' := by
  obtain ⟨hcrep, hcpres⟩ := centre_rep hi
  obtain ⟨ce, le, hs⟩ :=
    shiftHeads_of_scan raw s1.center s1.left s1.right radius h hcrep hcpres hi.scan hpos hle
  obtain ⟨t, ht, -, -, -, -, -⟩ := shift_heads_counters hs (inc s1.radius) (inc (inc s1.length))
  exact ⟨t, ht⟩

/-! ## The shift entry -/

/-- The shift block for one comparison result whose chain is the round's own
watch `w`.  The guard is not used: with `h = periodLength w` the entry is an
equation, so `beginShiftVM h w` and `beginShiftVM'` hold outright, and
`CopyIdle` transfers because neither `afterMismatch` nor the entry touches
`fpp`. -/
theorem shiftBlock (P : Shared) (h : ℕ) (s1 : GalilVM) (w : GalilScaffoldChainWatch.State)
    (hbegin : ∀ u v : GalilVM, beginShiftVM' u v → P.beginShift u v)
    (hh : h = periodLength w) (hcopy : CopyIdle s1)
    (hrun : ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t')
    (vs : ScanVM) (vq : SearchVM) (hvs : vs.chain = ChainVM.watch w) :
    ∃ (s2 : GalilVM) (t' : ShiftState), P.beginShift (afterMismatch s1 vs vq) s2 ∧
      beginShiftVM h w (afterMismatch s1 vs vq) s2 ∧ CopyIdle s2 ∧
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t' := by
  obtain ⟨t', hrun'⟩ := hrun
  have hchain : (afterMismatch s1 vs vq).chain = ChainVM.watch w := by
    rw [afterMismatch_chain]; exact hvs
  refine ⟨_, t', ?_, ⟨hchain, rfl⟩, ?_, hrun'⟩
  · refine hbegin _ _ ⟨w, ?_⟩
    rw [← hh]; exact ⟨hchain, rfl⟩
  · rw [copyIdle_iff] at hcopy ⊢
    exact hcopy

/-! ## `ShiftPack` -/

/-- **The shift block of a round, for a shared with the concrete entries.**

`hlock` is the one hypothesis that is *not* discharged here.  `ShiftPack`
quantifies over *every* comparison result `vs`, while `beginShiftVM h w`
requires the compared chain to be the round's own watch `w` (it is an equation
in `w`).  At the only place `ShiftPack` is consumed —
`round_scan_construct`'s mismatching terminal — `vs` is
`⟨left s1.left, right s1.right, .watch w⟩`, so `hlock` is trivially true
there; as a statement about all `vs` it is a genuine gap, and it is named
rather than hidden. -/
theorem shiftPack_of_lock (P : Shared) (h : ℕ) (s1 : GalilVM)
    (w : GalilScaffoldChainWatch.State)
    (hbegin : ∀ u v : GalilVM, beginShiftVM' u v → P.beginShift u v)
    (hh : h = periodLength w) (hcopy : CopyIdle s1)
    (hpred : read (right s1.right) =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlen : Canonical s1.length)
    (hrun : ∃ t' : ShiftState,
      ShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ h t')
    (hlock : ∀ (vs : ScanVM) (vq : SearchVM), P.shiftGuard (afterMismatch s1 vs vq) →
      vs.chain = ChainVM.watch w) :
    ShiftPack P h s1 w :=
  ⟨hpred, hlen, fun vs vq hg => shiftBlock P h s1 w hbegin hh hcopy hrun vs vq (hlock vs vq hg)⟩

/-- **`hpack` for `sharedC`.**  The scan data (`ScanInv`) supplies the head
moves and the canonical length; `h = periodLength w`, the prediction, the
copy idleness and `hlock` travel as hypotheses. -/
theorem shiftPack_concrete (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (raw : List (Fin 2)) (radius h : ℕ) (s1 : GalilVM)
    (w : GalilScaffoldChainWatch.State)
    (hi : ScanInv raw s1 radius) (hpos : 0 < h) (hle : h ≤ radius)
    (hh : h = periodLength w) (hcopy : CopyIdle s1)
    (hpred : read (right s1.right) =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlock : ∀ (vs : ScanVM) (vq : SearchVM), shiftGuardVM (afterMismatch s1 vs vq) →
      vs.chain = ChainVM.watch w) :
    ShiftPack (sharedC onLetter leftFirst centre place entry) h s1 w :=
  shiftPack_of_lock _ h s1 w (fun _ _ hb => hb) hh hcopy hpred hi.lengthCanon
    (shiftRun_of_scan raw s1 radius h hi hpos hle) hlock

/-- **`hpack` for `sharedFun`** (the shared of `cycle_fallback_stepsAll`, whose
fallback entry is determinized by `place`).  Same proof: only `shiftGuard` and
`beginShift` are touched, and both agree with `sharedC`'s. -/
theorem shiftPack_concreteFun (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (raw : List (Fin 2)) (radius h : ℕ) (s1 : GalilVM)
    (w : GalilScaffoldChainWatch.State)
    (hi : ScanInv raw s1 radius) (hpos : 0 < h) (hle : h ≤ radius)
    (hh : h = periodLength w) (hcopy : CopyIdle s1)
    (hpred : read (right s1.right) =
      GalilScaffoldChainConsume.symbol w.machine.control.period.focus)
    (hlock : ∀ (vs : ScanVM) (vq : SearchVM), shiftGuardVM (afterMismatch s1 vs vq) →
      vs.chain = ChainVM.watch w) :
    ShiftPack (PalPeg.GalilTickFun.sharedFun onLetter leftFirst centre place entry) h s1 w :=
  shiftPack_of_lock _ h s1 w (fun _ _ hb => hb) hh hcopy hpred hi.lengthCanon
    (shiftRun_of_scan raw s1 radius h hi hpos hle) hlock

#print axioms centre_rep
#print axioms shiftHeads_of_scan
#print axioms shiftRun_of_scan
#print axioms shiftBlock
#print axioms shiftPack_of_lock
#print axioms shiftPack_concrete
#print axioms shiftPack_concreteFun

end PalPeg.GalilShiftPack
