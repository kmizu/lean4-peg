import PalPeg.GalilScaffoldTopPrep

/-!
# Watch-phase chain ticks as verifier runs

A chain tick run on a watching chain that never breaks is a `Watch.Run`,
and a `Watch.Run` with a unary lag consumes exactly `watchConsumes bs lag`
places of the verifier (`VerifyRun.Run`), leaving lag `watchLag bs lag`:
`Internal.take` consumes when the lag is positive, `Outer.immediate`
consumes when it is zero, `Outer.queued` increments it — the arithmetic of
the lower layer's `watchTick`. This is the converse of
`verify_watch_run_events`, in the direction the controller needs.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

/-- **壊れた chain は壊れたままである。**  以前は `z = .broken w`（状態まで同一）と
書いていたが、`ChainMatched.brokenMatched`（Scala の `matched()` は mode に関係なく
`margin.inc()` と `lag.inc()` をする）を入れた結果それは偽になった。カウンタは動く。 -/
theorem broken_stays (es : List Bool) : ∀ {w : GalilScaffoldChainWatch.State} {z : ChainVM},
    ChainTicks es (.broken w) z → ∃ w' : GalilScaffoldChainWatch.State, z = .broken w' := by
  induction es with
  | nil => intro w z h; cases h; exact ⟨w, rfl⟩
  | cons a es ih =>
    intro w z h
    cases h with
    | cons ht hr =>
      obtain ⟨m, hs, hm⟩ := ht
      cases hs with
      | brokenIdle =>
        cases a
        · simp at hm; subst hm; exact ih hr
        · simp only [if_true] at hm
          cases hm with
          | brokenMatched _ => exact ih hr

/-- Chain ticks on a watching chain that stays watching are a watch run. -/
theorem chainTicks_watch_run (es : List Bool) : ∀ {w w' : GalilScaffoldChainWatch.State},
    ChainTicks es (.watch w) (.watch w') → GalilScaffoldChainWatch.Run w es w' := by
  induction es with
  | nil =>
    intro w w' h
    cases h
    exact .stop _
  | cons a es ih =>
    intro w w' h
    cases h with
    | cons ht hr =>
      obtain ⟨m, hs, hm⟩ := ht
      cases hs with
      | watchStep _ m' hi =>
        cases a
        · simp at hm
          subst hm
          exact .next (.step hi (.idle _)) (ih hr)
        · simp at hm
          cases hm with
          | watch _ w'' ho => exact .next (.step hi ho) (ih hr)
          | breaks _ _ _ =>
            obtain ⟨v, hv⟩ := broken_stays es hr
            cases hv
      | watchBreak _ v hbr =>
        cases a
        · simp at hm
          subst hm
          obtain ⟨v', hv'⟩ := broken_stays es hr
          cases hv'
        · simp only [if_true] at hm
          cases hm with
          | brokenMatched _ =>
            obtain ⟨v', hv'⟩ := broken_stays es hr
            cases hv'

theorem verify_run_append {s u t : GalilScaffoldChainVerifier.State} {m n : ℕ}
    (h1 : GalilScaffoldChainVerifyRun.Run s m u) (h2 : GalilScaffoldChainVerifyRun.Run u n t) :
    GalilScaffoldChainVerifyRun.Run s (m+n) t := by
  induction h1 with
  | stop => simpa using h2
  | next _ hp _ ih => rw [Nat.add_right_comm]; exact .next _ hp (ih h2)

theorem positive_ofNat_iff (k : ℕ) : positive (ofNat k) = true ↔ 0 < k := by
  cases k <;> simp [positive, ofNat, List.replicate_succ]

theorem zero_ofNat_iff (k : ℕ) : zero (ofNat k) = true ↔ k = 0 := by
  cases k <;> simp [zero, ofNat, List.replicate_succ]

/-- A watch run with unary lag `lag` consumes `watchConsumes bs lag` places
and leaves lag `watchLag bs lag`. -/
theorem watch_run_verify (bs : List Bool) : ∀ (lag : ℕ) {w w' : GalilScaffoldChainWatch.State},
    w.lag = ofNat lag → GalilScaffoldChainWatch.Run w bs w' →
    GalilScaffoldChainVerifyRun.Run w.machine (watchConsumes bs lag) w'.machine ∧
      w'.lag = ofNat (watchLag bs lag) := by
  induction bs with
  | nil =>
    intro lag w w' hl h
    cases h
    exact ⟨.stop _, hl⟩
  | cons b bs ih =>
    intro lag w w' hl h
    cases h with
    | next ht hr =>
      rename_i m
      cases ht with
      | step hi ho =>
        rename_i m0
        cases hi with
        | idle hp =>
          -- lag is zero
          have hl0 : lag = 0 := by
            rw [hl] at hp
            by_contra hne
            have : positive (ofNat lag) = true := (positive_ofNat_iff lag).2 (by omega)
            rw [this] at hp; cases hp
          subst hl0
          cases ho with
          | idle =>
            obtain ⟨hv, hl'⟩ := ih 0 hl hr
            refine ⟨?_, ?_⟩
            · simpa [watchConsumes, watchTick] using hv
            · simpa [watchLag, watchTick] using hl'
          | queued hz =>
            rw [hl] at hz
            have := (zero_ofNat_iff 0).2 rfl
            rw [this] at hz; cases hz
          | immediate hz hg =>
            obtain ⟨hv, hl'⟩ := ih 0 (by simp [GalilScaffoldChainWatch.immediate, hl]) hr
            refine ⟨?_, ?_⟩
            · have h1 : GalilScaffoldChainVerifyRun.Run w.machine 1 (GalilScaffoldChainWatch.immediate w).machine :=
                .next _ hg.1 (.stop _)
              have := verify_run_append h1 hv
              simpa [watchConsumes, watchTick] using this
            · simpa [watchLag, watchTick] using hl'
        | take hp hg =>
          -- lag is positive: `k+1`
          obtain ⟨k, hk⟩ : ∃ k, lag = k+1 := by
            rw [hl] at hp
            have := (positive_ofNat_iff lag).1 hp
            exact ⟨lag - 1, by omega⟩
          subst hk
          have hcl : (GalilScaffoldChainWatch.caught w).lag = ofNat k := by
            simp [GalilScaffoldChainWatch.caught, hl, dec_ofNat_succ]
          have h1 : GalilScaffoldChainVerifyRun.Run w.machine 1 (GalilScaffoldChainWatch.caught w).machine :=
            .next _ hg.1 (.stop _)
          cases ho with
          | idle =>
            obtain ⟨hv, hl'⟩ := ih k hcl hr
            refine ⟨?_, ?_⟩
            · have := verify_run_append h1 hv
              simpa [watchConsumes, watchTick] using this
            · simpa [watchLag, watchTick] using hl'
          | queued hz =>
            have hk0 : k ≠ 0 := by
              intro hk0; subst hk0
              rw [hcl] at hz
              have := (zero_ofNat_iff 0).2 rfl
              rw [this] at hz; cases hz
            have hql : (GalilScaffoldChainWatch.queued (GalilScaffoldChainWatch.caught w)).lag = ofNat (k+1) := by
              simp [GalilScaffoldChainWatch.queued, hcl, inc_ofNat]
            obtain ⟨hv, hl'⟩ := ih (k+1) hql hr
            refine ⟨?_, ?_⟩
            · have := verify_run_append h1 hv
              simpa [watchConsumes, watchTick, hk0] using this
            · simpa [watchLag, watchTick, hk0] using hl'
          | immediate hz hg2 =>
            have hk0 : k = 0 := by
              rw [hcl] at hz
              exact (zero_ofNat_iff k).1 hz
            subst hk0
            have hil : (GalilScaffoldChainWatch.immediate (GalilScaffoldChainWatch.caught w)).lag = ofNat 0 := by
              simp [GalilScaffoldChainWatch.immediate, hcl]
            obtain ⟨hv, hl'⟩ := ih 0 hil hr
            refine ⟨?_, ?_⟩
            · have h2 : GalilScaffoldChainVerifyRun.Run (GalilScaffoldChainWatch.caught w).machine 1
                  (GalilScaffoldChainWatch.immediate (GalilScaffoldChainWatch.caught w)).machine :=
                .next _ hg2.1 (.stop _)
              have := verify_run_append h1 (verify_run_append h2 hv)
              show GalilScaffoldChainVerifyRun.Run w.machine
                ((watchTick true (0+1)).1 + watchConsumes bs (watchTick true (0+1)).2) w'.machine
              have e1 : (watchTick true (0+1)).1 = 2 := by decide
              have e2 : (watchTick true (0+1)).2 = 0 := by decide
              rw [e1, e2]
              have e : 2 + watchConsumes bs 0 = 1 + (1 + watchConsumes bs 0) := by omega
              rw [e]
              exact this
            · simpa [watchLag, watchTick] using hl'

#print axioms chainTicks_watch_run
#print axioms watch_run_verify

end PalPeg.GalilScaffoldChainInputSupply
