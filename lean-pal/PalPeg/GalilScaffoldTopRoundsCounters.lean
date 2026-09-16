import PalPeg.GalilScaffoldTopSegmentHeads

/-!
# Counters across the rounds

The rounds keep the radius and length counters canonical: the matched
segments increment them, the shift entry increments the length, and the
shift runs decrement canonical counters.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

theorem rounds_counters (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    Canonical s.radius → Canonical s.length → Canonical s'.radius ∧ Canonical s'.length := by
  induction hr with
  | stop c s => intro hrc hlc; exact ⟨hrc, hlc⟩
  | next c s hseg _ _ _ w _ _ vs vq _ _ _ _ _ _ _ s2 _ hs2 _ hchain _ _ _ ih =>
    intro hrc hlc
    obtain ⟨hrc1, hlc1⟩ := scanSeg_counters P q first delay hseg
    obtain ⟨_, hrt, hlt⟩ := shift_run_canonical (shiftRun_of_chain hchain)
      ⟨ofNat_canonical h, inc_canonical _ (hrc1 hrc), inc_canonical _ (inc_canonical _ (hlc1 hlc))⟩
    exact ih hrt hlt

#print axioms rounds_counters

end PalPeg.GalilScaffoldChainInputSupply
