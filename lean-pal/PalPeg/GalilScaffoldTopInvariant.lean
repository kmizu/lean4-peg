import PalPeg.GalilScaffoldTopGuards

/-!
# The scan-mode invariant of the controller

What the lower layer's supply lemmas (`found_supplied_restart`,
`scan_prediction_shift`) assume at a comparison tick, stated on the unified
VM: the heads represent the input (`ScanInvariant` around the centre), the
radius counter is the scan radius and canonical, the length counter is
canonical, and the centre head is a decoded place of the input. Also the
arithmetic of the shift run: `h` unit shifts from `remaining = h` exhaust
`remaining`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead

/-- The scan-mode invariant on the unified VM for the input `raw` with the
current scan radius `r`. -/
structure ScanInv (raw : List (Fin 2)) (s : GalilVM) (r : ℕ) : Prop where
  scan : ScanInvariant raw (position s.center) r s.left s.right
  radius : value s.radius = r
  radiusCanon : Canonical s.radius
  lengthCanon : Canonical s.length
  centre : ∃ (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool),
    s.center = represent ⟨a :: ls, gap⟩ (rs.map some) q ∧ raw = (a :: ls).reverse ++ rs ++ q

/-- `h` unit shifts from `remaining = h` exhaust the counter. -/
theorem shift_run_remaining (h : ℕ) : ∀ {s t : ShiftState}, s.remaining = ofNat h →
    ShiftRun s h t → t.remaining = ofNat 0 := by
  induction h with
  | zero => intro s t hs hr; cases hr; exact hs
  | succ h ih =>
    intro s t hs hr
    cases hr with
    | next _ _ _ _ _ rest =>
      apply ih _ rest
      show dec s.remaining = ofNat h
      rw [hs, dec_ofNat_succ]

theorem positive_ofNat_zero : positive (ofNat 0) = false := rfl

/-- The chain shift run of `found_supplied_restart` ends with `remaining`
exhausted, as `scan_shift_cycle` needs. -/
theorem chain_shift_exhausts (h : ℕ) {s t : ShiftState} {w v : GalilScaffoldChainWatch.State}
    {cycle finish : Counter} (hs : s.remaining = ofNat h)
    (hr : ChainShiftRun s w cycle h t v finish) : positive t.remaining = false := by
  have hsr : ShiftRun s h t := by
    clear hs
    induction hr with
    | stop => exact .stop _
    | next _ _ _ enabled hc hl hl' _ ih => exact .next _ enabled hc hl hl' ih
  rw [shift_run_remaining h hs hsr]
  rfl

#print axioms chain_shift_exhausts

end PalPeg.GalilScaffoldChainInputSupply
