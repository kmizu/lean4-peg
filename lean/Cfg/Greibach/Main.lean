import Cfg.Greibach.CFL
import Cfg.Greibach.Std
import Cfg.Greibach.GNF
import Cfg.Greibach.PelHom
import Cfg.OpenProblems

/-!
# The open problem is about one language

Aho–Ullman's and Ford's question — is there a context-free language without a PEG? — is equivalent to whether
Greibach's hardest language has no PEG (`cfl_pel_iff`): every context-free language has a PEG iff `L0` has one.

- (→) `L0` is context-free (`l0_cfl`).
- (←) Every context-free language, without `ε`, is the inverse image of `L0` under a homomorphism with finitely many
  distinct blocks (`stdForm_exists`, `greibach_std`); PEG languages are closed under such inverse images
  (`isPEL_invHom`), and under removing and adding `ε` (`isPEL_nonempty`, `isPEL_addEps`).
-/

namespace Shallot.Cfg

/-- **Every context-free language has a PEG iff Greibach's hardest language has one.** -/
theorem cfl_pel_iff : CFLSubsetPELConjecture ↔ IsPEL L0 := by
  constructor
  · intro h; exact h L0 l0_cfl
  · intro hL0 L ⟨g, hg⟩
    obtain ⟨g', hstd, heq⟩ := stdForm_exists g
    obtain ⟨h, S, hne, hS, hh⟩ := greibach_std g' hstd
    have hinv : IsPEL (invHom h L0) := isPEL_invHom hL0 h S ['c', 'd'] hne hS
    -- `L` without `ε` is the inverse image
    have hne' : IsPEL (fun w => w ≠ [] ∧ invHom h L0 w) := isPEL_nonempty hinv
    have hcore : ∀ w, (w ≠ [] ∧ L w) ↔ (w ≠ [] ∧ invHom h L0 w) := fun w => by
      constructor
      · rintro ⟨hw, hl⟩; exact ⟨hw, (hh w hw).1 ((heq w hw).1 ((hg w).1 hl))⟩
      · rintro ⟨hw, hl⟩; exact ⟨hw, (hg w).2 ((heq w hw).2 ((hh w hw).2 hl))⟩
    have hnoeps : IsPEL (fun w => w ≠ [] ∧ L w) := by
      obtain ⟨p, hp⟩ := hne'
      exact ⟨p, fun w => (hcore w).trans (hp w)⟩
    -- put `ε` back if `L` has it
    by_cases he : L []
    · obtain ⟨p, hp⟩ := isPEL_addEps hnoeps
      refine ⟨p, fun w => ?_⟩
      rw [← hp w]
      constructor
      · intro hl
        by_cases hw : w = []
        · exact .inl hw
        · exact .inr ⟨hw, hl⟩
      · rintro (rfl | ⟨_, hl⟩)
        · exact he
        · exact hl
    · obtain ⟨p, hp⟩ := hnoeps
      refine ⟨p, fun w => ?_⟩
      rw [← hp w]
      constructor
      · intro hl
        refine ⟨fun hw => ?_, hl⟩
        subst hw; exact he hl
      · exact fun h => h.2

end Shallot.Cfg
