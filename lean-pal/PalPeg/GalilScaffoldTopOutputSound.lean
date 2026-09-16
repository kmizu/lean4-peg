import PalPeg.GalilScaffoldTopInitRestart

/-!
# Soundness of the output along scan segments

`OutputRel raw c s`: the controller's output is sound at the state — if it
is `true`, the prefix up to the right head's letter is a palindrome. The
output changes only at comparisons (through `refresh` under the scan
invariant), so the relation propagates along every scan segment; at a
report point (scan mode, not replaying, the right head waiting on a letter)
a `true` output certifies the palindromic prefix.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The output is sound at the state. -/
def OutputRel (raw : List (Fin 2)) (c : Control) (s : GalilVM) : Prop :=
  c.output = true → ∀ k, 0 < k → k ≤ raw.length → position s.right = 2*k-1 → IsPal (raw.take k)

/-- A refreshed output under the scan invariant is sound at its state. -/
theorem outputRel_of_refresh (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM) (o : Bool)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right)
    (ho : refresh (galilFrame P q first) s c.output o) :
    OutputRel raw {c with clock := c.clock, output := o} s := by
  intro hout k hk hk2 hr
  exact refresh_sound raw P hP hP' q first s c.output o hi k hk hk2 hr ho hout

theorem scanInvariant_matched {raw : List (Fin 2)} {cen r : ℕ} {l rr : PlaceHead}
    (hi : ScanInvariant raw cen r l rr) (hav : canRight rr) (hm : read (left l) = read (right rr)) :
    ScanInvariant raw cen (r+1) (left l) (right rr) := by
  have he : ScanEvents raw cen r l rr [true] (left l) (right rr) := .matched _ _ _ hav hm (.stop _ _ _)
  simpa using scan_events_invariant he hi

/-- The output relation propagates along an event-indexed segment. -/
theorem watchSegE_output (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s → OutputRel raw c' t := by
  induction h with
  | stop c s => intro r _ ho; exact ho
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | countR c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho')
  | matchIdle c s vs vq o _ _ ha _ _ hl hr _ hmt _ _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho')
  | matchIdleR c s vs vq o _ _ _ ha _ hl hr _ hmt _ _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho')

/-- The output relation propagates along a matched scan segment. -/
theorem scanSeg_output (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s → OutputRel raw c' t := by
  induction h with
  | stop c s => intro r _ ho; exact ho
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho')

/-- The output relation propagates along a general segment. -/
theorem watchSeg_output (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s → OutputRel raw c' t := by
  induction h with
  | stop c s => intro r _ ho; exact ho
  | wait c s s' _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | count c s s' _ _ _ _ hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr, _, _⟩ := background_frame P q first hb
    refine ih r (by rw [hl, hr]; exact hi) ?_
    intro hout k hk hk2 hrk
    rw [hr] at hrk
    exact ho hout k hk hk2 hrk
  | «match» c s vs vq o _ _ ha _ _ hcmp hmt _ ho' _ ih =>
    intro r hi _
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
    have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
      rw [afterCompare_left, afterCompare_right, hl, hr]
      exact scanInvariant_matched hi ha hmatch
    exact ih (r+1) hi' (outputRel_of_refresh raw P hP hP' q first _ _ o hi' ho')

/-- At a report point — the right head waiting on a letter — a `true`
output certifies the palindromic prefix read so far. -/
theorem report_sound (raw : List (Fin 2)) (c : Control) (s : GalilVM) (hrel : OutputRel raw c s)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) (hgap : s.right.gap = false)
    (hout : c.output = true) :
    IsPal (raw.take s.right.head.left.length) := by
  have hpos := represented_position _ raw hi.rightRep hi.rightPresent
  apply hrel hout s.right.head.left.length hpos.1 hpos.2
  simp [position, hgap]

#print axioms watchSegE_output
#print axioms report_sound

end PalPeg.GalilScaffoldChainInputSupply
