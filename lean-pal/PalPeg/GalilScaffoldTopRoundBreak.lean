import PalPeg.GalilScaffoldTopRounds

/-!
# The breaking terminal comparison after chained rounds

After `m` chained rounds and a further segment of `n` matched comparisons,
the terminal comparison at the last continuation cell may match on the outer
symbols while the chain's prediction fails: the watch breaks
(`ChainTick true (.watch w) (.broken w')`). On the projection this is the
`rounds_restart` situation of the lower layer, so the restart entry
conditions (scan invariant with the accumulated centre/radius, broken watch
with non-negative margin, positive `last`, lag zero, canonical counters)
hold at the actual controller state `afterCompare s1 vs vq` — exactly the
premises of `restartVM`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- At lag zero a breaking matched tick records the consumed watch. -/
theorem chainTick_true_broken {w w' : GalilScaffoldChainWatch.State} (hz : zero w.lag = true)
    (h : ChainTick true (.watch w) (.broken w')) :
    w' = GalilScaffoldChainWatch.immediate w ∧ BreakStep w w' := by
  obtain ⟨m, hs, hm⟩ := h
  cases hs with
  | watchStep _ m' hi =>
    cases hi with
    | idle _ =>
      simp at hm
      cases hm
      have hb : BreakStep w w' := ‹_›
      obtain ⟨a, _, _, he⟩ := hb.2.2
      exact ⟨he, hb⟩
    | take hp _ =>
      rw [positive_of_zero hz] at hp; cases hp

/-- The projection of a matched comparison, for any recorded watch equal to
the consumed one (watching or broken). -/
theorem afterCompare_only' (s : GalilVM) (w w' : GalilScaffoldChainWatch.State) (vs : ScanVM)
    (vq : SearchVM) (hp : s.periodOnly = true) (hw : w' = GalilScaffoldChainWatch.immediate w)
    (hl : vs.left = left s.left) (hr : vs.right = right s.right) :
    toOnly (afterCompare s vs vq) w' = onlyCompareNext (toOnly s w) := by
  subst hw
  simp only [toOnly, afterCompare, onlyCompareNext, cycleAfter, radiusAfter, hp, ite_true]
  simp [searchLens, scanLens, hl, hr]

theorem afterCompare_chain (s : GalilVM) (vs : ScanVM) (vq : SearchVM) :
    (afterCompare s vs vq).chain = vs.chain := by
  show (searchLens.set (scanLens.set s vs) vq).chain = _
  simp [searchLens, scanLens]

/-- Chained rounds, a matched segment, and a breaking terminal comparison:
controller steps to the broken state, and the restart entry conditions there. -/
theorem rounds_break (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ)
    {m : ℕ} {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s')
    (w0 : GalilScaffoldChainWatch.State) (hp0 : s.periodOnly = true) (hs0 : s.chain = .watch w0)
    (hz0 : zero w0.lag = true)
    {n : ℕ} {c1 : Control} {s1 : GalilVM} (hseg : ScanSeg P q first delay n c' s' c1 s1)
    (hm1 : c1.mode = .scan) (hr1 : c1.replaying = false) (hc1 : c1.clock = 1)
    (w : GalilScaffoldChainWatch.State) (hs1 : s1.chain = .watch w) (hav : canRight s1.right)
    (vs : ScanVM) (vq : SearchVM)
    (hcmp : (galilFrame P q first).compare s1 (scanLens.set s1 vs))
    (hmt : (galilFrame P q first).matched (scanLens.set s1 vs))
    (hq : searchEffect P true s1 vq)
    (hend : singlePositive s1.cycle = true)
    (w' : GalilScaffoldChainWatch.State) (hbr : vs.chain = .broken w')
    (o : Bool) (ho : refresh (galilFrame P q first) (afterCompare s1 vs vq) c1.output o) :
    (∃ k : ℕ, Steps (galilFrameS P q first) delay k ⟨c, s⟩
        ⟨{c1 with clock := delay, output := o, replaying := false}, afterCompare s1 vs vq⟩) ∧
      w' = GalilScaffoldChainWatch.immediate w ∧ (afterCompare s1 vs vq).chain = .broken w' ∧
      ∀ (raw : List (Fin 2)) (org : ReadOrigin raw), org.interior.length+1 = h →
        Entry raw org (toOnly s w0) → read s'.center ≠ none →
        let e := afterCompare s1 vs vq
        let center := org.center+(m+1)*h
        let radius := org.radius+1+m*h-h
        ScanInvariant raw center (radius+n+1) e.left e.right ∧
          w'.machine.control.broken = true ∧
          negative w'.margin = false ∧
          positive w'.machine.control.last = true ∧
          zero w'.lag = true ∧
          read e.center ≠ none ∧
          RadiusRep e.radius (radius+n+1) ∧
          negative e.radius = false ∧
          (GalilScaffoldSearchFinish.begin w'.machine.control.last e.radius).work =
            w'.machine.control.last ∧
          Canonical w'.machine.control.last := by
  obtain ⟨⟨k1, hst1⟩, w1, hw1, hz1, hp1, hcr⟩ := rounds_lift P q first delay h hr w0 hp0 hs0 hz0
  obtain ⟨k2, hst2⟩ := scanSeg_steps P q first delay hseg
  obtain ⟨w2, hw2, hz2, hp2, hrun⟩ := scanSeg_only P q first delay hseg w1 hp1 hw1 hz1
  have hww : w2 = w := by rw [hs1] at hw2; injection hw2 with e; exact e.symm
  subst w2
  have hmatch : read (left s1.left) = read (right s1.right) := by
    obtain ⟨⟨hl0, hr0, _⟩, _⟩ := hcmp
    rw [scanLens.get_set] at hl0 hr0
    have := matched_parts P q first hmt
    rw [hl0, hr0] at this; exact this
  obtain ⟨hl, hr', ht⟩ := compare_parts P q first hcmp hmatch
  have ht' := ht
  rw [hs1, hbr] at ht'
  obtain ⟨hw', _⟩ := chainTick_true_broken hz2 ht'
  have hav' : (galilFrame P q first).available s1 := hav
  have htick := scan_match_S P q first delay c1 s1 vs vq o hm1 hr1 hav' hc1 (by rw [hs1]; intro h0; cases h0) hcmp hmt hq ho
  refine ⟨⟨_, steps_trans (steps_trans hst1 hst2) (.succ htick (.zero _))⟩, hw', ?_, ?_⟩
  · rw [afterCompare_chain]; exact hbr
  · intro raw org hh he hcenter
    have hres := rounds_restart hcr org hh he hrun hcenter hend hav hmatch
    have heq := afterCompare_only' s1 w w' vs vq hp2 hw' hl hr'
    rw [← heq] at hres
    exact hres

#print axioms chainTick_true_broken
#print axioms rounds_break

end PalPeg.GalilScaffoldChainInputSupply
