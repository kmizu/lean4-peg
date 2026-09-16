import PalPeg.GalilScaffoldTopOutputSound

/-!
# Output soundness across the refresh points of a chain's life

The output is refreshed at comparisons and at the end of each shift. Along
a segment `watchSegE_output` carries the relation; at a matched comparison
the invariant grows by one; at a shift end the read origin's `Entry` gives
the scan invariant of the resumed heads, so the refreshed output there is
sound too. `rounds_output` carries the relation over the re-shift rounds.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem outputRel_congr (raw : List (Fin 2)) {c c' : Control} (s : GalilVM) (h : c'.output = c.output)
    (ho : OutputRel raw c s) : OutputRel raw c' s := by
  intro hout; rw [h] at hout; exact ho hout

theorem refreshS_iff (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) (old o : Bool) :
    refresh (galilFrameS P q first) s old o ↔ refresh (galilFrame P q first) s old o := Iff.rfl

/-- A refreshed output under the scan invariant is sound, for any controller
carrying it. -/
theorem outputRel_of_refresh' (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (s : GalilVM) (old o : Bool)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right)
    (ho : refresh (galilFrame P q first) s old o) (c' : Control) (hc' : c'.output = o) :
    OutputRel raw c' s := by
  intro hout k hk hk2 hr
  rw [hc'] at hout
  exact refresh_sound raw P hP hP' q first s old o hi k hk hk2 hr ho hout

theorem outputRel_of_refreshS' (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (s : GalilVM) (old o : Bool)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right)
    (ho : refresh (galilFrameS P q first) s old o) (c' : Control) (hc' : c'.output = o) :
    OutputRel raw c' s :=
  outputRel_of_refresh' raw P hP hP' q first s old o hi ((refreshS_iff P q first s old o).1 ho) c' hc'

/-- The scan invariant at a read origin's entry state. -/
theorem entry_scanInvariant {raw : List (Fin 2)} {org : ReadOrigin raw} {s : OnlyCompareState}
    (he : Entry raw org s) :
    ScanInvariant raw (org.center+(org.interior.length+1)) (org.radius+1-(org.interior.length+1))
      s.left s.right :=
  he.scan.caught.scan

/-- A matched comparison with a refreshed output: the invariant grows and
the output is sound. -/
theorem outputRel_matched_refresh' (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM} (vq : SearchVM)
    (hl : vs.left = left s.left) (hr : vs.right = right s.right)
    (hmatch : read (left s.left) = read (right s.right)) (hav : canRight s.right)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) (old o : Bool)
    (ho : refresh (galilFrame P q first) (afterCompare s vs vq) old o) (c' : Control) (hc' : c'.output = o) :
    ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right ∧
      OutputRel raw c' (afterCompare s vs vq) := by
  have hi' : ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
    rw [afterCompare_left, afterCompare_right, hl, hr]
    exact scanInvariant_matched hi hav hmatch
  exact ⟨hi', outputRel_of_refresh' raw P hP hP' q first _ old o hi' ho c' hc'⟩

theorem outputRel_matched_refresh (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) {s : GalilVM} {vs : ScanVM} (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs)) (hav : canRight s.right)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) (old o : Bool)
    (ho : refresh (galilFrame P q first) (afterCompare s vs vq) old o) (c' : Control) (hc' : c'.output = o) :
    ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right ∧
      OutputRel raw c' (afterCompare s vs vq) := by
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P q first hmt
    rw [hl0, hr0] at this; exact this
  obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
  exact outputRel_matched_refresh' raw P hP hP' q first vq hl hr hmatch hav hi old o ho c' hc'

/-- Along an event-indexed segment: the output relation and the invariant
at the end. -/
theorem watchSegE_output_inv (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (cen r : ℕ)
    (hi : ScanInvariant raw cen r s.left s.right) (ho : OutputRel raw c s) :
    OutputRel raw c' t ∧ ScanInvariant raw cen (r + es.count true) t.left t.right :=
  ⟨watchSegE_output raw P hP hP' q first delay h cen r hi ho,
    scan_events_invariant ((watchSegE_heads P q first delay h).1 raw cen r) hi⟩

/-- Along a general segment with the chain active. -/
theorem watchSeg_output_inv (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (hne : s.chain ≠ .idle)
    (cen r : ℕ) (hi : ScanInvariant raw cen r s.left s.right) (ho : OutputRel raw c s) :
    OutputRel raw c' t ∧ ∃ es : List Bool, ScanInvariant raw cen (r + es.count true) t.left t.right := by
  obtain ⟨es, _, hsc, _⟩ := watchSeg_events P q first delay h hne
  exact ⟨watchSeg_output raw P hP hP' q first delay h cen r hi ho, es, scan_events_invariant (hsc raw cen r) hi⟩

/-- The output relation across the re-shift rounds, from a read origin's
entry: each round scans under the invariant, and the shift end refreshes
the output under the next origin's invariant. -/
theorem rounds_output (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    ∀ w0 : GalilScaffoldChainWatch.State, s.periodOnly = true → s.chain = .watch w0 →
      zero w0.lag = true → ∀ org : ReadOrigin raw, org.interior.length+1 = h →
      Entry raw org (toOnly s w0) → OutputRel raw c s → OutputRel raw c' s' := by
  induction hr with
  | stop c s => intro w0 _ _ _ org _ _ ho; exact ho
  | next c s hseg hm1 hr1 hc1 w hs1 hav vs vq hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho rest ih =>
    intro w0 hp hs hz org hint he hout
    have hi : ScanInvariant raw _ _ s.left s.right := entry_scanInvariant he
    have hout1 := scanSeg_output raw P hP hP' q first delay hseg _ _ hi hout
    obtain ⟨_, hcr1⟩ := round_next P q first delay h hseg w0 hp hs hz hm1 hr1 hc1 w hs1 hav vs vq
      hcmp hmis hq hend hpred hlen hg s2 hb hs2 hi2 hchain o ho
    obtain ⟨org', he', _, hinterior, _, _, _, _, _⟩ := rounds_origin hcr1 org hint he
    have hi2' := entry_scanInvariant he'
    obtain ⟨w1, hw1, hz1, _, _⟩ := scanSeg_only P q first delay hseg w0 hp hs hz
    have hww : w1 = w := by rw [hs1] at hw1; injection hw1 with e; exact e.symm
    subst hww
    exact ih _ (by show s2.periodOnly = true; rw [hs2.2]) rfl (by rw [chain_shift_lag hchain]; exact hz1)
      org' (by rw [hinterior]; exact hint) he'
      (outputRel_of_refreshS' raw P hP hP' q first _ _ o hi2' ho _ rfl)

#print axioms rounds_output
#print axioms outputRel_matched_refresh

end PalPeg.GalilScaffoldChainInputSupply
