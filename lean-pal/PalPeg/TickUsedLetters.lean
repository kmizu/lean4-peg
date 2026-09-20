import PalPeg.GalilLookRefined

/-!
# The letters used by the target of a tick

A truncated tick is legitimate when the letters used by its source and by its target, and the
lookahead of its source, have arrived (`GalilLookRefined.tick_trunc'`).  The starvation test of
the local layer reads the source only, so the letters used by the target have to be bounded by
the source.  Here: a background tick keeps the three heads, and its chain either ticks (within
its refined lookahead, `chainTick_used'`), stays idle, or is born on the centre head.
-/

set_option autoImplicit false

namespace PalPeg.TickUsedLetters

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilThrottledRun (usedPH usedChain usedVM)
open PalPeg.GalilTruncTick (usedVM_left usedVM_center usedVM_right)
open PalPeg.GalilLookRefined (lookChain' chainTick_used')

/-- **The letters used after a background tick**: those used before, or the refined lookahead of
the chain. -/
theorem usedVM_background_le (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s s' : GalilVM} (hbackground : (galilFrameS P q first).background s s') :
    usedVM raw s' ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
  obtain ⟨hleft, hright, hchain, hcenter, -⟩ := backgroundS_fields P q first hbackground
  have hchainBound : usedChain raw.length s'.chain
      ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
    rcases hchain with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
    · exact le_trans (chainTick_used' raw.length htick) (le_max_right _ _)
    · rw [hidle]
      exact Nat.zero_le _
    · simp only [Bool.false_eq_true, if_false] at hborn
      rw [hborn]
      exact le_trans (usedVM_center raw s) (le_max_left _ _)
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  show max (max (usedPH raw.length s'.left) (usedPH raw.length s'.center))
      (max (usedPH raw.length s'.right) (usedChain raw.length s'.chain)) ≤ _
  rw [hleft, hcenter, hright]
  omega

#print axioms usedVM_background_le

/-- **The letters used after the `init` effect**: the three heads stand on the place right of the
right head and the chain is idle, so they are the letters used by that move. -/
theorem usedVM_init_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hinit : initVM entry s t) :
    usedVM raw t ≤ usedPH raw.length (GalilScaffoldChainVerifier.right s.right) := by
  obtain ⟨hright, hleft, hcenter, -, -, -, -, -, -, hchain, -⟩ := hinit
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [hleft, hcenter, hright, hchain]
  simp [usedChain, PalPeg.GalilThrottledRun.verOf]

/-- **The letters used after the `replayStart` effect**: the three heads stand on the centre head
and the chain is idle, so no new letter is used. -/
theorem usedVM_replayStart_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hreplayStart : replayStartVM entry s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨-, hright, hleft, hcenter, -, -, -, -, -, hchain, -⟩ := hreplayStart
  have hcenterUsed := usedVM_center raw s
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [hleft, hcenter, hright, hchain]
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

#print axioms usedVM_replayStart_le

/-- **The letters used after a comparison**: the left head moves left (no letter), the right head
moves right, the centre stays, and the chain ticks within its refined lookahead, stays idle, or
is born on the centre head (a matched step does not move the verifier of a copying chain). -/
theorem usedVM_compare_le (raw : List (Fin 2)) (P : Shared) (q : ℕ) (first : Fin 9)
    {s t : GalilVM} (hcompare : compareFound P q first s t) :
    usedVM raw t ≤ max (max (usedVM raw s)
      (usedPH raw.length (GalilScaffoldChainVerifier.right s.right)))
      (lookChain' raw.length s.chain) := by
  obtain ⟨vs, vq, a, hleft, hright, -, -, hchain, ht⟩ := hcompare
  have hfields : t.left = vs.left ∧ t.center = s.center ∧ t.right = vs.right ∧
      t.chain = vs.chain := by
    subst ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [afterBirth_left]; cases a <;> rfl
    · rw [afterBirth_center]; cases a <;> rfl
    · rw [afterBirth_right]; cases a <;> rfl
    · rw [afterBirth_chain]; cases a <;> rfl
  obtain ⟨htl, htc, htr, htchain⟩ := hfields
  have hcenterUsed := usedVM_center raw s
  have hleftUsed := usedVM_left raw s
  have hchainBound : usedChain raw.length vs.chain
      ≤ max (usedVM raw s) (lookChain' raw.length s.chain) := by
    rcases hchain with ⟨_, htick⟩ | ⟨_, _, hidle⟩ | ⟨_, _, hborn⟩
    · exact le_trans (chainTick_used' raw.length htick) (le_max_right _ _)
    · rw [hidle]
      exact Nat.zero_le _
    · have hverifier : usedChain raw.length vs.chain = usedPH raw.length s.center := by
        cases a
        · simp only [Bool.false_eq_true, if_false] at hborn
          rw [hborn]
          rfl
        · simp only [if_true] at hborn
          generalize vs.chain = born at hborn ⊢
          unfold chainStart at hborn
          cases hborn
          rfl
      rw [hverifier]
      exact le_trans hcenterUsed (le_max_left _ _)
  show max (max (usedPH raw.length t.left) (usedPH raw.length t.center))
      (max (usedPH raw.length t.right) (usedChain raw.length t.chain)) ≤ _
  rw [htl, htc, htr, htchain, hleft, hright, PalPeg.GalilTruncTick.usedPH_left]
  omega

#print axioms usedVM_compare_le

/-- **The letters used after the fallback entry**: the heads stay and the chain becomes idle. -/
theorem usedVM_beginFallback_le (raw : List (Fin 2)) {s t : GalilVM}
    (hfallback : beginFallbackVM' s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨place, hplace, -⟩ := hfallback
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  rw [hplace]
  show max (max (usedPH raw.length s.left) (usedPH raw.length s.center))
      (max (usedPH raw.length s.right) (usedChain raw.length ChainVM.idle)) ≤ _
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

/-- **The letters used after a restart**: the heads stay and the chain becomes idle. -/
theorem usedVM_restart_le (raw : List (Fin 2)) {entry : ℕ} {s t : GalilVM}
    (hrestart : restartVM entry s t) : usedVM raw t ≤ usedVM raw s := by
  obtain ⟨broken, -, -, -, -, ht⟩ := hrestart
  have hl := usedVM_left raw s
  have hc := usedVM_center raw s
  have hr := usedVM_right raw s
  rw [ht]
  show max (max (usedPH raw.length s.left) (usedPH raw.length s.center))
      (max (usedPH raw.length s.right) (usedChain raw.length ChainVM.idle)) ≤ _
  simp only [usedChain, PalPeg.GalilThrottledRun.verOf]
  omega

#print axioms usedVM_restart_le

end PalPeg.TickUsedLetters
