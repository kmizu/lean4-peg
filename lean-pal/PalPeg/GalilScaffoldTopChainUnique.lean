import PalPeg.GalilScaffoldTopGeneralEvents

/-!
# Determinism of the chain ticks

Every chain step and every credit is determined by the state (and the
input under the verifier): copy reads the answer cell (`"1"` or LEFT), back
tests FIRST, the watch consumes by `lag`/`Good`, the credit queues or
consumes by `lag`, and a break is exactly the failed immediate consume. So
chain tick runs over the same events from the same state coincide, and the
outcome of `found_to_watchStart` is *the* chain state after the preparation.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

theorem internal_unique {w m m' : GalilScaffoldChainWatch.State}
    (h1 : GalilScaffoldChainWatch.Internal w m) (h2 : GalilScaffoldChainWatch.Internal w m') : m = m' := by
  cases h1 <;> cases h2 <;> first | rfl | (exfalso; simp_all)

theorem outer_unique {w m m' : GalilScaffoldChainWatch.State} {b : Bool}
    (h1 : GalilScaffoldChainWatch.Outer w b m) (h2 : GalilScaffoldChainWatch.Outer w b m') : m = m' := by
  cases h1 <;> cases h2 <;> first | rfl | (exfalso; simp_all)

theorem outer_true_cases {w m : GalilScaffoldChainWatch.State} (h : GalilScaffoldChainWatch.Outer w true m) :
    zero w.lag = false ∨ GalilScaffoldChainWatch.Good w := by
  cases h with
  | queued hz => exact Or.inl hz
  | immediate hz hg => exact Or.inr hg

theorem break_not_good {w w' : GalilScaffoldChainWatch.State} (hb : BreakStep w w')
    (hg : GalilScaffoldChainWatch.Good w) : False := by
  obtain ⟨_, _, a, ha, hne, _⟩ := hb
  obtain ⟨_, a', ha', hr⟩ := hg
  rw [ha] at ha'
  cases ha'
  exact hne hr

theorem break_outer_absurd {w w' w'' : GalilScaffoldChainWatch.State} (hb : BreakStep w w')
    (ho : GalilScaffoldChainWatch.Outer w true w'') : False := by
  rcases outer_true_cases ho with hz | hg
  · have := hb.1; rw [hz] at this; cases this
  · exact break_not_good hb hg

theorem chainStep_unique {x y y' : ChainVM} (h1 : ChainStep x y) (h2 : ChainStep x y') : y = y' := by
  cases h1 <;> cases h2
  case copyBit.copyBit =>
    rename_i present₁ _ _ _ present₂
    rw [present₁] at present₂
    cases present₂
    rfl
  case watchStep.watchStep =>
    rename_i hi₁ _ hi₂
    rw [internal_unique hi₁ hi₂]
  all_goals first
    | rfl
    | (rename_i h₁ _ h₂; rw [breakStepPos_unique h₁ h₂])
    | (rename_i hi _ hbr; exact (internal_breakStepPos_false hi hbr).elim)
    | (rename_i hbr _ hi; exact (internal_breakStepPos_false hi hbr).elim)
    | (exfalso; simp_all; done)
    | (simp_all; done)

theorem chainMatched_unique {x y y' : ChainVM} (h1 : ChainMatched x y) (h2 : ChainMatched x y') : y = y' := by
  cases h1 <;> cases h2
  case watch.watch =>
    rename_i ho₁ _ ho₂
    rw [outer_unique ho₁ ho₂]
  case watch.breaks =>
    rename_i ho _ hb
    exact (break_outer_absurd hb ho).elim
  case breaks.watch =>
    rename_i hb _ ho
    exact (break_outer_absurd hb ho).elim
  case breaks.breaks =>
    rename_i hb₁ _ hb₂
    obtain ⟨_, _, _, _, _, e₁⟩ := hb₁
    obtain ⟨_, _, _, _, _, e₂⟩ := hb₂
    rw [e₁, e₂]
  all_goals rfl

theorem chainTick_unique {a : Bool} {x y y' : ChainVM} (h1 : ChainTick a x y) (h2 : ChainTick a x y') : y = y' := by
  obtain ⟨m, hs, hm⟩ := h1
  obtain ⟨m', hs', hm'⟩ := h2
  have := chainStep_unique hs hs'
  subst this
  cases a
  · simp at hm hm'
    rw [hm, hm']
  · simp at hm hm'
    exact chainMatched_unique hm hm'

theorem chainTicks_unique {es : List Bool} : ∀ {x y y' : ChainVM},
    ChainTicks es x y → ChainTicks es x y' → y = y' := by
  induction es with
  | nil => intro x y y' h1 h2; cases h1; cases h2; rfl
  | cons a es ih =>
    intro x y y' h1 h2
    cases h1 with
    | cons ht hr =>
      cases h2 with
      | cons ht' hr' =>
        have := chainTick_unique ht ht'
        subst this
        exact ih hr hr'

#print axioms chainTicks_unique

end PalPeg.GalilScaffoldChainInputSupply
