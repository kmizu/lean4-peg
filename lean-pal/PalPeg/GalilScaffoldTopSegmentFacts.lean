import PalPeg.GalilScaffoldTopFirstStagePrefix

/-!
# Facts about chain-idle segments

The centre is kept along a segment; the controller's clock after a segment
is the match clock's; the search's inactive modes are inert (padding a run);
and along a segment that ends with the chain idle the search never lands in
`found` (that would have started the chain).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem watchSegE_center (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    t.center = s.center := by
  induction h with
  | stop c s => rfl
  | wait c s s' _ _ _ hb _ ih =>
    obtain ⟨_, _, hcen, _⟩ := background_frame P q first hb
    rw [ih, hcen]
  | count c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, hcen, _⟩ := background_frame P q first hb
    rw [ih, hcen]
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih, afterCompare_center]
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih, afterCompare_center]
  | countR c s s' _ _ _ _ hb _ ih =>
    obtain ⟨_, _, hcen, _⟩ := background_frame P q first hb
    rw [ih, hcen]
  | matchIdleR c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    rw [ih, replayDec_center, afterCompare_center]

/-- The controller's clock after a segment is the match clock's, and the
control stays in scan mode without replay. -/
theorem watchSegE_clock (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    ∃ av : List Bool, av.length = es.length ∧
      es = GalilScaffoldAdvanceClock.advances delay c.clock (av.map (fun b => (b, true))) ∧
      c'.clock = (GalilScaffoldMatchClock.run delay c.clock av).1 ∧
      c'.mode = c.mode := by
  induction h with
  | stop c s => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | wait c s s' hm hr _ _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    refine ⟨false :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, he]
    · rw [hcl]; rfl
  | count c s s' hm hr _ hc _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    have hne : c.clock ≠ 1 := by omega
    refine ⟨true :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, hne, he]
    · rw [hcl]; simp [GalilScaffoldMatchClock.run, hne]
  | «match» c s vs vq o hm hr _ hc _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, hc, he]
    · rw [hcl]; simp [GalilScaffoldMatchClock.run, hc]
  | matchIdle c s vs vq o hm hr _ hc _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, hc, he]
    · rw [hcl]; simp [GalilScaffoldMatchClock.run, hc]
  | countR c s s' hm hr hc _ _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    have hne : c.clock ≠ 1 := by omega
    refine ⟨true :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, hne, he]
    · rw [hcl]; simp [GalilScaffoldMatchClock.run, hne]
  | matchIdleR c s vs vq o hm hr hc _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he, hcl, hmo⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_, ?_, hmo⟩
    · simp [GalilScaffoldAdvanceClock.advances, hc, he]
    · rw [hcl]; simp [GalilScaffoldMatchClock.run, hc]

/-- An inactive search is inert: any events pad the run. -/
theorem searchRun_pad (center : GalilScaffoldPlace.Place) (m : ℕ) (v : SearchVM)
    (hm : v.search.mode = .found ∨ v.search.mode = .missed ∨ v.search.mode = .idle) :
    SearchRun center (List.replicate m false) v v := by
  induction m with
  | zero => exact .nil _
  | succ m ih =>
    refine .cons ?_ ih
    unfold searchStep
    rcases hm with h | h | h <;> rw [h]

/-- Along a segment ending with the chain idle, the search never lands in
`found` (that would have started the chain). -/
theorem watchSegE_search_not_found (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    {es : List Bool} {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    (ht : t.chain = .idle) :
    ∀ (es1 es2 : List Bool) (u : SearchVM), es = es1 ++ es2 → es1 ≠ [] →
      SearchRun (P.place s) es1 (searchLens.get s) u → u.search.mode ≠ .found := by
  induction h with
  | stop c s =>
    intro es1 es2 u he hne _
    cases es1 with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at he
  | wait c s s' _ _ _ hb rest ih =>
    intro es1 es2 u he hne hu
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    have hs' : s'.chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hs : s.chain = .idle := by
      by_contra hne'
      exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne') hne' hs'
    have hnf : (searchLens.get s').search.mode ≠ .found := by
      rcases backgroundS_idle P q first hb hs with ⟨hnf, _⟩ | ⟨_, hz⟩
      · exact hnf
      · exfalso; rw [hz] at hs'; cases hs'
    rcases hse with ⟨_, hstep⟩ | ⟨hne', _⟩
    · cases es1 with
      | nil => exact absurd rfl hne
      | cons a es1' =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he'⟩ := he
        cases hu with
        | cons hstep' hrest' =>
          have := searchStep_unique hstep hstep'
          subst this
          cases es1' with
          | nil => cases hrest'; exact hnf
          | cons b es1'' =>
            rw [hplace s' s hcen] at ih
            exact ih ht (b :: es1'') es2 u he' (by simp) hrest'
    · exact absurd hs hne'
  | count c s s' _ _ _ _ hb rest ih =>
    intro es1 es2 u he hne hu
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    have hs' : s'.chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hs : s.chain = .idle := by
      by_contra hne'
      exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne') hne' hs'
    have hnf : (searchLens.get s').search.mode ≠ .found := by
      rcases backgroundS_idle P q first hb hs with ⟨hnf, _⟩ | ⟨_, hz⟩
      · exact hnf
      · exfalso; rw [hz] at hs'; cases hs'
    rcases hse with ⟨_, hstep⟩ | ⟨hne', _⟩
    · cases es1 with
      | nil => exact absurd rfl hne
      | cons a es1' =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he'⟩ := he
        cases hu with
        | cons hstep' hrest' =>
          have := searchStep_unique hstep hstep'
          subst this
          cases es1' with
          | nil => cases hrest'; exact hnf
          | cons b es1'' =>
            rw [hplace s' s hcen] at ih
            exact ih ht (b :: es1'') es2 u he' (by simp) hrest'
    · exact absurd hs hne'
  | «match» c s vs vq o _ _ _ _ hne' hcmp hmt hq _ rest ih =>
    intro es1 es2 u he hne hu
    exfalso
    have hs' : (afterCompare s vs vq).chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨_, _, htk⟩ := compare_parts P q first hcmp hmatch
    rw [afterCompare_chain] at hs'
    exact chainTick_ne_idle htk hne' hs'
  | matchIdle c s vs vq o _ _ _ _ hidle _ _ _ _ hq hnf _ rest ih =>
    intro es1 es2 u he hne hu
    rcases hq with ⟨_, hstep⟩ | ⟨hne', _⟩
    · cases es1 with
      | nil => exact absurd rfl hne
      | cons a es1' =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he'⟩ := he
        cases hu with
        | cons hstep' hrest' =>
          have := searchStep_unique hstep hstep'
          subst this
          cases es1' with
          | nil => cases hrest'; exact hnf
          | cons b es1'' =>
            rw [hplace (afterCompare s vs vq) s (afterCompare_center s vs vq)] at ih
            have hget : searchLens.get (afterCompare s vs vq) = vq := rfl
            rw [hget] at ih
            exact ih ht (b :: es1'') es2 u he' (by simp) hrest'
    · exact absurd hidle hne'
  | countR c s s' _ _ _ hidle hb rest ih =>
    intro es1 es2 u he hne hu
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    have hs' : s'.chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hnf : (searchLens.get s').search.mode ≠ .found := by
      rcases backgroundS_idle P q first hb hidle with ⟨hnf, _⟩ | ⟨_, hz⟩
      · exact hnf
      · exfalso; rw [hz] at hs'; cases hs'
    rcases hse with ⟨_, hstep⟩ | ⟨hne', _⟩
    · cases es1 with
      | nil => exact absurd rfl hne
      | cons a es1' =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he'⟩ := he
        cases hu with
        | cons hstep' hrest' =>
          have := searchStep_unique hstep hstep'
          subst this
          cases es1' with
          | nil => cases hrest'; exact hnf
          | cons b es1'' =>
            rw [hplace s' s hcen] at ih
            exact ih ht (b :: es1'') es2 u he' (by simp) hrest'
    · exact absurd hidle hne'
  | matchIdleR c s vs vq o _ _ _ _ hidle _ _ _ _ hq hnf _ rest ih =>
    intro es1 es2 u he hne hu
    rcases hq with ⟨_, hstep⟩ | ⟨hne', _⟩
    · cases es1 with
      | nil => exact absurd rfl hne
      | cons a es1' =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he'⟩ := he
        cases hu with
        | cons hstep' hrest' =>
          have := searchStep_unique hstep hstep'
          subst this
          cases es1' with
          | nil => cases hrest'; exact hnf
          | cons b es1'' =>
            rw [hplace (replayDec true (afterCompare s vs vq)) s (by rw [replayDec_center, afterCompare_center])] at ih
            have hget : searchLens.get (replayDec true (afterCompare s vs vq)) = vq := rfl
            rw [hget] at ih
            exact ih ht (b :: es1'') es2 u he' (by simp) hrest'
    · exact absurd hidle hne'

#print axioms watchSegE_clock
#print axioms watchSegE_search_not_found

end PalPeg.GalilScaffoldChainInputSupply
