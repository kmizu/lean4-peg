import PalPeg.GalilScaffoldTopFoundLife

/-!
# The search's run over a chain-idle segment

While the chain is idle every scan tick steps the search (`searchStep`),
with the advance at each comparison. A segment ending with the chain still
idle never started the chain, so its whole event list drives the search:
`SearchRun`. The events of such a segment are the advances of the match
clock over the availability list (`GalilScaffoldAdvanceClock.advances`),
which is the event form the staged search lemmas consume.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

inductive SearchRun (center : GalilScaffoldPlace.Place) : List Bool → SearchVM → SearchVM → Prop
  | nil (v : SearchVM) : SearchRun center [] v v
  | cons {a : Bool} {as : List Bool} {v v' v'' : SearchVM}
      (h : searchStep center a v v') (hr : SearchRun center as v' v'') : SearchRun center (a :: as) v v''

theorem searchRun_append {center : GalilScaffoldPlace.Place} {as : List Bool} {v v' : SearchVM}
    (h1 : SearchRun center as v v') : ∀ {bs : List Bool} {v'' : SearchVM},
      SearchRun center bs v' v'' → SearchRun center (as ++ bs) v v'' := by
  induction h1 with
  | nil v => intro bs v'' h2; simpa using h2
  | cons h _ ih => intro bs v'' h2; exact .cons h (ih h2)

/-- A chain tick never returns to `idle`. -/
theorem chainTick_ne_idle {a : Bool} {x z : ChainVM} (h : ChainTick a x z) (hx : x ≠ .idle) :
    z ≠ .idle := by
  obtain ⟨y, hs, hm⟩ := h
  have hy : y ≠ .idle := by
    intro hy; subst hy
    cases hs; exact hx rfl
  cases a
  · simp at hm; subst hm; exact hy
  · simp at hm
    intro hz; subst hz
    cases hm; exact hy rfl

/-- Along a segment the chain never returns to `idle`. -/
theorem watchSegE_ne_idle (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    s.chain ≠ .idle → t.chain ≠ .idle := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ _ _ hb _ ih =>
    intro hs
    exact ih (chainTick_ne_idle (backgroundS_chainTick P q first hb hs) hs)
  | count c s s' _ _ _ _ hb _ ih =>
    intro hs
    exact ih (chainTick_ne_idle (backgroundS_chainTick P q first hb hs) hs)
  | «match» c s vs vq o _ _ _ _ _ hcmp hmt _ _ _ ih =>
    intro hs
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨_, _, ht⟩ := compare_parts P q first hcmp hmatch
    apply ih
    rw [afterCompare_chain]
    exact chainTick_ne_idle ht hs
  | matchIdle c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => intro hs; exact absurd hidle hs
  | countR c s _ _ _ _ hidle _ _ _ => intro hs; exact absurd hidle hs
  | matchIdleR c s _ _ _ _ _ _ _ hidle _ _ _ _ _ _ _ _ _ => intro hs; exact absurd hidle hs

theorem watchSegE_idle_start (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    (ht : t.chain = .idle) : s.chain = .idle := by
  by_contra hs
  exact watchSegE_ne_idle P q first delay h hs ht

/-- A segment that ends with the chain idle drives the search by its events. -/
theorem watchSegE_searchRun (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hplace : ∀ u v : GalilVM, u.center = v.center → P.place u = P.place v)
    {es : List Bool} {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t)
    (ht : t.chain = .idle) :
    SearchRun (P.place s) es (searchLens.get s) (searchLens.get t) := by
  induction h with
  | stop c s => exact .nil _
  | wait c s s' _ _ _ hb rest ih =>
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    have hs' : s'.chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hs : s.chain = .idle := by
      by_contra hne
      exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
    rcases hse with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace s' s hcen] at this
      exact .cons hstep this
    · exact absurd hs hne
  | count c s s' _ _ _ _ hb rest ih =>
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    have hs' : s'.chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hs : s.chain = .idle := by
      by_contra hne
      exact chainTick_ne_idle (backgroundS_chainTick P q first hb hne) hne hs'
    rcases hse with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace s' s hcen] at this
      exact .cons hstep this
    · exact absurd hs hne
  | «match» c s vs vq o _ _ _ _ _ hcmp hmt hq _ rest ih =>
    have hs' : (afterCompare s vs vq).chain = .idle := watchSegE_idle_start P q first delay rest ht
    have hmatch : read (left s.left) = read (right s.right) := by
      obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
      rw [scanLens.get_set] at hl0 hr0
      have := matched_parts P q first hmt
      rw [hl0, hr0] at this; exact this
    obtain ⟨_, _, htk⟩ := compare_parts P q first hcmp hmatch
    have hs : s.chain = .idle := by
      by_contra hne
      rw [afterCompare_chain] at hs'
      exact chainTick_ne_idle htk hne hs'
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace (afterCompare s vs vq) s (afterCompare_center s vs vq)] at this
      have hget : searchLens.get (afterCompare s vs vq) = vq := rfl
      rw [hget] at this
      exact .cons hstep this
    · exact absurd hs hne
  | matchIdle c s vs vq o _ _ _ _ hidle _ _ _ _ hq _ _ rest ih =>
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace (afterCompare s vs vq) s (afterCompare_center s vs vq)] at this
      have hget : searchLens.get (afterCompare s vs vq) = vq := rfl
      rw [hget] at this
      exact .cons hstep this
    · exact absurd hidle hne
  | countR c s s' _ _ _ hidle hb rest ih =>
    obtain ⟨_, _, _, hcen, _, _, _, _, _, _, _, hse⟩ := backgroundS_fields P q first hb
    rcases hse with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace s' s hcen] at this
      exact .cons hstep this
    · exact absurd hidle hne
  | matchIdleR c s vs vq o _ _ _ _ hidle _ _ _ _ hq _ _ rest ih =>
    rcases hq with ⟨_, hstep⟩ | ⟨hne, _⟩
    · have := ih ht
      rw [hplace (replayDec true (afterCompare s vs vq)) s (by rw [replayDec_center, afterCompare_center])] at this
      have hget : searchLens.get (replayDec true (afterCompare s vs vq)) = vq := rfl
      rw [hget] at this
      exact .cons hstep this
    · exact absurd hidle hne

/-- The events of a segment are the match clock's advances over its
availability list, from the controller's clock. -/
theorem watchSegE_advances (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    ∃ av : List Bool, av.length = es.length ∧
      es = GalilScaffoldAdvanceClock.advances delay c.clock (av.map (fun b => (b, true))) := by
  induction h with
  | stop c s => exact ⟨[], rfl, rfl⟩
  | wait c s s' _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨false :: av, by simp [hlen], ?_⟩
    simp [GalilScaffoldAdvanceClock.advances, he]
  | count c s s' _ _ _ hc _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_⟩
    have hne : c.clock ≠ 1 := by omega
    simp [GalilScaffoldAdvanceClock.advances, hne, he]
  | «match» c s vs vq o _ _ _ hc _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_⟩
    simp [GalilScaffoldAdvanceClock.advances, hc, he]
  | matchIdle c s vs vq o _ _ _ hc _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_⟩
    simp [GalilScaffoldAdvanceClock.advances, hc, he]
  | countR c s s' _ _ hc _ _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_⟩
    have hne : c.clock ≠ 1 := by omega
    simp [GalilScaffoldAdvanceClock.advances, hne, he]
  | matchIdleR c s vs vq o _ _ hc _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨av, hlen, he⟩ := ih
    refine ⟨true :: av, by simp [hlen], ?_⟩
    simp [GalilScaffoldAdvanceClock.advances, hc, he]

#print axioms watchSegE_searchRun
#print axioms watchSegE_advances

end PalPeg.GalilScaffoldChainInputSupply
