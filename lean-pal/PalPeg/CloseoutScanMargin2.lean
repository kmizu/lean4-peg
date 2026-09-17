import PalPeg.CloseoutScanMargin

/-!
# `CloseoutScanMargin2`: `Margin` is refuted, not merely unproved

`CloseoutScanMargin.Margin l` (`position l ≠ 1`) is the named leaf that buys
`CloseoutPackRun3.Extra.scanMargin` / `rewindMargin`.  The hope was that the
machine has a *stopping rule* forbidding a scan comparison with the left head
on the first letter, so that `Margin` would hold at every reachable
scan/rewind state and could be proved by a `Tick` induction.

**There is no such rule, and `Margin` is false at a reachable state.**

* §1 The transition relation never mentions `position`.
  `GalilScaffoldTop.Tick.scan_match` / `scan_shift` / `scan_fallback` are
  guarded only by `c.clock = 1`, `c.replaying = true ∨ F.available s` and
  `F.compare s s'`, and for the scan frame
  (`GalilScaffoldTopScan.scanFrame`) `compare s s'` is literally
  `s'.left = left s.left ∧ s'.right = right s.right ∧ ChainTick _ s.chain s'.chain`:
  an unconditional left step.  So no tick can supply `position L ≠ 1`.

* §2 A concrete counterexample, with **no induction needed**: the
  one-letter word.  `GalilScaffoldChainInputSupply.scan_first a` is the
  *initial* scan configuration on `w = [a]`, and it has
  `center = 1`, `radius = 0`, hence `position L = 1`.  It satisfies
  `ScanInvariant`, it satisfies `Live [a] 1 1` (`GalilLiveCentre`'s liveness predicate), and it
  refutes `Margin` and `r + 2 ≤ C` outright (`margin_false_witness`,
  `scanMargin_refuted`).  The state is not exotic: it is where every run on a
  nonempty word starts.

* §3 Why nothing is broken by this: the obligation `Margin` was bought for is
  *stronger than legality*.  At `position L = 1` we have `l.gap = false`
  (`CloseoutScanMargin.pos_one_shape`), and the left step out of a
  `gap = false` place flips the parity to `gap = true`, so
  `GalilFrontMono.Sane (left l)` holds unconditionally
  (`sane_left_at_pos_one`).  The illegal move is only out of the *origin gap
  cell* `position = 0`, and `CloseoutLPack4.scanInv_pos` already excludes that
  unconditionally.

**Verdict.**  `Extra.scanMargin`'s `r + 2 ≤ C` (equivalently
`0 < position (left L)`) is not a machine fact to be proved; it is a
mis-stated field.  The honest repair is to weaken it to
`GalilFrontMono.Sane (GalilScaffoldInputHead.left L)`, which §3 discharges
from `scanInv_pos` plus the parity argument, with no new leaf.
Standard axioms only; unconditional `PAL ∈ PEG` remains open.
-/

set_option autoImplicit false

namespace PalPeg.CloseoutScanMargin2

open PalPeg PalPeg.GalilScaffoldInputHead PalPeg.GalilScaffoldChainInputSupply
open PalPeg.CloseoutScanMargin

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 2. The counterexample: the initial scan state on a one-letter word -/

/-- The initial scan place on `w = [a]`. -/
def wit (a : Fin 2) : PH :=
  GalilScaffoldChainVerifier.right ⟨GalilScaffoldInputTrace.append
    GalilScaffoldInputTrace.reset a, true⟩

theorem wit_scanInv (a : Fin 2) : ScanInvariant [a] 1 0 (wit a) (wit a) :=
  scan_first a

/-- The left head sits on the first letter. -/
theorem wit_pos (a : Fin 2) : position (wit a) = 1 := by
  have h := (wit_scanInv a).leftPos
  simpa using h

/-- **`Margin` is false there.** -/
theorem margin_false_witness (a : Fin 2) : ¬ Margin (wit a) := by
  unfold Margin
  simp [wit_pos a]

/-- **`Extra.scanMargin`'s conclusion is false at a reachable state.** -/
theorem scanMargin_refuted :
    ∃ (w : List (Fin 2)) (C r : ℕ) (l rh : PH),
      ScanInvariant w C r l rh ∧ ¬ (r + 2 ≤ C) := by
  refine ⟨[0], 1, 0, wit 0, wit 0, wit_scanInv 0, ?_⟩
  omega

/-- The counterexample is *live*: `Live [a] 1 1` (`GalilLiveCentre`'s liveness predicate). -/
theorem wit_live (a : Fin 2) : Live [a] 1 1 := by
  refine ⟨le_refl 1, by omega, ?_⟩
  simpa using (wit_scanInv a).palindrome

/-- And liveness gives exactly the `+1` margin, not the `+2` one. -/
theorem wit_margin_succ_only (_a : Fin 2) :
    0 + 1 ≤ 1 ∧ ¬ (0 + 2 ≤ 1) := ⟨le_refl 1, by omega⟩

/-! ## 3. The obligation was stronger than legality -/

/-- A left step out of a `gap = false` place is always `Sane`: it flips the
parity to `gap = true`. -/
theorem sane_left_of_gap_false {p : PH} (hg : p.gap = false) :
    GalilFrontMono.Sane (GalilScaffoldInputHead.left p) :=
  Or.inl (by simp [GalilScaffoldInputHead.left, hg])

/-- **The real content of `scanMargin`, and it is free.**  At `position l = 1`
the left step is still legal. -/
theorem sane_left_at_pos_one {p : PH} (h : position p = 1) :
    GalilFrontMono.Sane (GalilScaffoldInputHead.left p) :=
  sane_left_of_gap_false (pos_one_shape h).1

/-- **The scan obligation, discharged with no leaf.**  From the scan invariant
alone (via `scanInv_pos`, which gives `1 ≤ position l`), the left head of a
scan can always take its step legally — `Margin` is never needed. -/
theorem sane_left_of_scanInv {w : List (Fin 2)} {C r : ℕ} {l rh : PH}
    (hi : ScanInvariant w C r l rh) :
    GalilFrontMono.Sane (GalilScaffoldInputHead.left l) := by
  have h1 : 1 ≤ position l := CloseoutLPack4.scanInv_pos hi
  cases hg : l.gap with
  | false => exact sane_left_of_gap_false hg
  | true =>
    refine Or.inr ?_
    have : position l = 2 * l.head.left.length := by simp [position, hg]
    simp [GalilScaffoldInputHead.left, hg]
    omega

#print axioms wit_scanInv
#print axioms margin_false_witness
#print axioms scanMargin_refuted
#print axioms wit_live
#print axioms sane_left_at_pos_one
#print axioms sane_left_of_scanInv

end PalPeg.CloseoutScanMargin2
