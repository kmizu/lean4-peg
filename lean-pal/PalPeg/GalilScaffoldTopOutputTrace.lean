import PalPeg.GalilScaffoldTopOutputLife

/-!
# Output soundness at every state of a segment

`StepsAll F delay Q k x y`: a run of `k` ticks all of whose states satisfy
`Q`. Along a scan segment every state's output is sound with respect to its
right head (`SoundOut`), since the output changes only through `refresh`
under the scan invariant and the heads move only at comparisons.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- A run all of whose states satisfy `Q`. -/
inductive StepsAll {σ : Type} (F : Frame σ) (delay : ℕ) (Q : State σ → Prop) :
    ℕ → State σ → State σ → Prop
  | zero (x : State σ) (hx : Q x) : StepsAll F delay Q 0 x x
  | succ {n : ℕ} {x y z : State σ} (hx : Q x) (h : Tick F delay x y) (hr : StepsAll F delay Q n y z) :
      StepsAll F delay Q (n+1) x z

theorem stepsAll_steps {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) : Steps F delay n x y := by
  induction h with
  | zero x _ => exact .zero x
  | succ _ h _ ih => exact .succ h ih

theorem stepsAll_head {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) : Q x := by
  cases h with
  | zero _ hx => exact hx
  | succ hx _ _ => exact hx

theorem stepsAll_last {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) : Q y := by
  induction h with
  | zero _ hx => exact hx
  | succ _ _ _ ih => exact ih

theorem stepsAll_trans {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {m n : ℕ}
    {x y z : State σ} (h1 : StepsAll F delay Q m x y) (h2 : StepsAll F delay Q n y z) :
    StepsAll F delay Q (m+n) x z := by
  induction h1 with
  | zero x _ => simpa using h2
  | succ hx h _ ih =>
    rw [Nat.add_right_comm]
    exact .succ hx h (ih h2)

theorem stepsAll_mono {σ : Type} {F : Frame σ} {delay : ℕ} {Q Q' : State σ → Prop}
    (hQ : ∀ st, Q st → Q' st) {n : ℕ} {x y : State σ} (h : StepsAll F delay Q n x y) :
    StepsAll F delay Q' n x y := by
  induction h with
  | zero x hx => exact .zero x (hQ x hx)
  | succ hx h _ ih => exact .succ (hQ _ hx) h ih

/-- A run whose states all satisfy `Q`, from a run and a proof that `Q`
holds at every state reached by a tick from a `Q` state. -/
theorem stepsAll_of_steps {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    (hstep : ∀ x y, Q x → Tick F delay x y → Q y) {n : ℕ} {x y : State σ}
    (h : Steps F delay n x y) (hx : Q x) : StepsAll F delay Q n x y := by
  induction h with
  | zero x => exact .zero x hx
  | succ h _ ih => exact .succ hx h (ih (hstep _ _ hx h))

/-- Output sound with respect to the right head. -/
def SoundOut (raw : List (Fin 2)) (st : State GalilVM) : Prop := OutputRel raw st.ctl st.vm

theorem outputRel_background (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s s' : GalilVM} (hb : (galilFrameS P q first).background s s') {c c' : Control}
    (hc : c'.output = c.output) (ho : OutputRel raw c s) : OutputRel raw c' s' := by
  obtain ⟨_, hr, _, _⟩ := background_frame P q first hb
  intro hout k hk hk2 hrk
  rw [hr] at hrk; rw [hc] at hout
  exact ho hout k hk hk2 hrk

/-- The invariant after a matched comparison. -/
theorem matched_invariant (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9) {s : GalilVM}
    {vs : ScanVM} (vq : SearchVM) (hcmp : (galilFrame P q first).compare s (scanLens.set s vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s vs)) (hav : canRight s.right)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) :
    ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
  have hmatch : read (left s.left) = read (right s.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P q first hmt
    rw [hl0, hr0] at this; exact this
  obtain ⟨hl, hr, _⟩ := compare_parts P q first hcmp hmatch
  rw [afterCompare_left, afterCompare_right, hl, hr]
  exact scanInvariant_matched hi hav hmatch

theorem matched_invariant' (raw : List (Fin 2)) {s : GalilVM} {vs : ScanVM} (vq : SearchVM)
    (hl : vs.left = left s.left) (hr : vs.right = right s.right)
    (hmatch : read (left s.left) = read (right s.right)) (hav : canRight s.right)
    {cen r : ℕ} (hi : ScanInvariant raw cen r s.left s.right) :
    ScanInvariant raw cen (r+1) (afterCompare s vs vq).left (afterCompare s vs vq).right := by
  rw [afterCompare_left, afterCompare_right, hl, hr]
  exact scanInvariant_matched hi hav hmatch

/-- Every state of an event-indexed segment has a sound output. -/
theorem watchSegE_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundOut raw) k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ ho; exact ⟨0, .zero _ ho⟩
  | wait c s s' hm hr hn hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | countR c s s' hm hr hc hidle hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_count c s s' hm (Or.inl hr) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho' _ ih =>
    intro r hi ho
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    exact ⟨k+1, .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho') hs⟩
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' := matched_invariant' raw vq hl hrr hmatch ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    exact ⟨k+1, .succ ho (scan_match_idle_S P q first delay c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho') hs⟩
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho' _ ih =>
    intro r hi ho
    have hmatch : read (left s.left) = read (right s.right) := by
      have := matched_parts P q first hmt
      rw [hl, hrr] at this; exact this
    have hi' : ScanInvariant raw cen (r+1) (replayDec true (afterCompare s vs vq)).left
        (replayDec true (afterCompare s vs vq)).right := by
      rw [replayDec_left, replayDec_right, afterCompare_left, afterCompare_right, hl, hrr]
      exact scanInvariant_matched hi ha hmatch
    obtain ⟨k, hs⟩ := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    have ht := scan_match_idle_S' P q first delay c s vs vq o hm (Or.inl hr) hc hidle hl hrr hvs hmt hq hnf
      (by rw [hr]; exact ho')
    rw [hr] at ht
    exact ⟨k+1, .succ ho (by simpa using ht) hs⟩

/-- Every state of a matched scan segment has a sound output. -/
theorem scanSeg_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundOut raw) k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ ho; exact ⟨0, .zero _ ho⟩
  | wait c s s' hm hr hn hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho' _ ih =>
    intro r hi ho
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨w', hw'⟩ := hwatch
    have hne : s.chain ≠ .idle :=
      chainTick_source_ne_idle (compare_parts P q first hcmp hmatch).2.2 (by rw [hw']; intro h0; cases h0)
    exact ⟨k+1, .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho') hs⟩

/-- Every state of a general segment has a sound output. -/
theorem watchSeg_stepsAll (raw : List (Fin 2)) (P : Shared) (hP : P.onLetter = onLetterVM raw)
    (hP' : P.leftFirst = leftFirstVM) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) (cen : ℕ) :
    ∀ r : ℕ, ScanInvariant raw cen r s.left s.right → OutputRel raw c s →
      ∃ k, StepsAll (galilFrameS P q first) delay (SoundOut raw) k ⟨c, s⟩ ⟨c', t⟩ := by
  induction h with
  | stop c s => intro r _ ho; exact ⟨0, .zero _ ho⟩
  | wait c s s' hm hr hn hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_wait c s s' hm ⟨hr, hn⟩ hb) hs⟩
  | count c s s' hm hr ha hc hb _ ih =>
    intro r hi ho
    obtain ⟨hl, hr', _, _⟩ := background_frame P q first hb
    obtain ⟨k, hs⟩ := ih r (by rw [hl, hr']; exact hi) (outputRel_background raw P q first hb rfl ho)
    exact ⟨k+1, .succ ho (.scan_count c s s' hm (Or.inr ha) hc hb) hs⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho' _ ih =>
    intro r hi ho
    have hi' := matched_invariant raw P q first vq hcmp hmt ha hi
    obtain ⟨k, hs⟩ := ih (r+1) hi' (outputRel_of_refresh' raw P hP hP' q first _ c.output o hi' ho' _ rfl)
    exact ⟨k+1, .succ ho (scan_match_S P q first delay c s vs vq o hm hr ha hc hne hcmp hmt hq ho') hs⟩

#print axioms watchSegE_stepsAll
#print axioms scanSeg_stepsAll
#print axioms watchSeg_stepsAll

end PalPeg.GalilScaffoldChainInputSupply
