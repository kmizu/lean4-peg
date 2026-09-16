import PalPeg.GalilScaffoldTopWatch

/-!
# Progress at a comparison

At clock one in scan mode with R available, after moving L and R the
controller always has a tick: the outer symbols agree (`scan_match`, with
the chain either ticking or breaking), or they differ and the chain guard
selects a shift (`scan_shift`), or a fallback (`scan_fallback`). The chain
tick-or-break and the entry effects are the only hypotheses.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead GalilScaffoldChainVerifier

theorem compare_progress (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hav : canRight s.right)
    (hw : ∀ a : Bool, ∃ ch', ChainTick a s.chain ch')
    (hbs : ∀ s1, P.shiftGuard s1 → ∃ s2, P.beginShift s1 s2)
    (hbf : ∀ s1, ∃ s2, P.beginFallback s1 s2) :
    ∃ (c' : Control) (t : GalilVM), Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨c', t⟩ ∧
      (c'.mode = .scan ∨ c'.mode = .shift ∨ c'.mode = .copy) := by
  classical
  -- the chain step (tick or break)
  obtain ⟨w', hw'⟩ := hw (decide (read (left s.left) = read (right s.right)))
  let v1 : ScanVM := ⟨left s.left, right s.right, w'⟩
  let s1 : GalilVM := scanLens.set s v1
  have hav' : (galilFrame P q first).available s := hav
  have hcmp : (galilFrame P q first).compare s s1 := by
    refine ⟨?_, ?_⟩
    · rw [scanLens.get_set]
      exact ⟨rfl, rfl, hw'⟩
    · rw [scanLens.get_set]
  by_cases hmt : (galilFrame P q first).matched s1
  · -- matched
    have hpl : (galilFrame P q first).matchedPlace c.replaying s1 s1 := by
      show s1 = (if c.replaying then _ else s1)
      rw [hr]; simp
    let o : Bool := if P.onLetter s1 then decide (P.leftFirst s1) else c.output
    have ho : refresh (galilFrame P q first) s1 c.output o := by
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : P.onLetter s1 := hl
        show (if P.onLetter s1 then decide (P.leftFirst s1) else c.output) = true ↔ P.leftFirst s1
        rw [if_pos hl']; exact decide_eq_true_iff
      · have hl' : ¬ P.onLetter s1 := hl
        show (if P.onLetter s1 then decide (P.leftFirst s1) else c.output) = c.output
        rw [if_neg hl']
    exact ⟨_, s1, .scan_match c s s1 s1 o hm (Or.inr hav') hc hcmp hmt hpl ho, Or.inl hm⟩
  · by_cases hg : P.shiftGuard s1
    · obtain ⟨s2, hb⟩ := hbs s1 hg
      exact ⟨_, s2, .scan_shift c s s1 s2 hm (Or.inr hav') hc hcmp hmt hr hg hb, Or.inr (Or.inl rfl)⟩
    · obtain ⟨s2, hb⟩ := hbf s1
      exact ⟨_, s2, .scan_fallback c s s1 s2 hm (Or.inr hav') hc hcmp hmt (Or.inr hg) hr hb, Or.inr (Or.inr rfl)⟩

#print axioms compare_progress

end PalPeg.GalilScaffoldChainInputSupply
