import Cfg.Greibach.PelHomSound
import Cfg.Greibach.PelHomPad
import Cfg.Greibach.Defs

/-!
# Closure properties of PEG languages

- `isPEL_invHom`: inverse images under nonerasing homomorphisms with finitely many distinct blocks
  (`h a = h₀` outside a finite list `S`). The simulating grammar reads a source letter while simulating `g` on
  its whole block, keeping the offset inside the current block in the rule index (`PhSim.grammar`); it is
  complete (`PhSim.complete`) and terminates only where `g` does (`PhSim.sound`).
- `isPEL_nonempty`, `isPEL_addEps` (in `PelHomPad`): removing or adding the empty word.

Why the finiteness of the blocks: a grammar has finitely many rules, and the simulation needs a rule for each
offset inside each block. (Since `Char` is itself finite this is not a restriction in principle, but it is the
form Greibach's construction delivers, and it keeps the state list explicit.)
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome pegRun_complete derives_det)

namespace PhSim

variable (M : PhSim)

/-- The image is exhausted only at a boundary with the source exhausted. -/
theorem img_eq_nil (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {q : St} {u : List Char}
    (hq : q ∈ M.stList) (h : M.img q u = []) : q = none ∧ u = [] := by
  rcases M.img_cases hne hS (u := u) hq with hn | ⟨_, _, _, _, _, _, himg, _⟩
  · exact hn
  · rw [himg] at h; cases h

/-- The simulating grammar accepts a source word iff `g` accepts its image. -/
theorem grammar_iff (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) (w : List Char) :
    (∃ t, Derives M.grammar (.nt M.grammar.start) w (.ok t [])) ↔
      ∃ t, Derives M.g (.nt M.g.start) (M.hflat w) (.ok t []) := by
  constructor
  · rintro ⟨t, hd⟩
    obtain ⟨n, hn⟩ := pegRun_complete hd
    obtain ⟨o, hdo⟩ := M.sound hne hS n _ none none w _ M.elist_start M.none_mem_stList M.none_mem_stList hn
    rcases M.outcome_cases hne hS M.none_mem_stList M.elist_start hdo with ⟨rfl, Hm⟩ | ⟨t', q₁, u₁, rfl, H⟩
    · cases derives_det hd (Hm none M.none_mem_stList)
    · rcases Classical.em (q₁ = none) with rfl | hq
      · obtain ⟨t'', h''⟩ := H.ok
        have he := derives_det hd h''
        injection he with _ hu
        subst hu
        exact ⟨t', hdo⟩
      · cases derives_det hd (H.fail M.none_mem_stList (fun h => hq h.symm))
  · rintro ⟨t, hd⟩
    obtain ⟨q₁, u₁, hr, H⟩ := M.complete hne hS hd none w M.none_mem_stList rfl M.elist_start
    obtain ⟨rfl, rfl⟩ := M.img_eq_nil hne hS H.1 hr.symm
    exact H.ok

end PhSim

/-- **Inverse homomorphisms.** If `L` has a PEG, so has `h⁻¹(L)` for a nonerasing `h` that is constant (`h₀`)
outside a finite list `S` of letters. -/
theorem isPEL_invHom {L : Language} (hL : IsPEL L) (h : Char → List Char) (S : List Char) (h₀ : List Char)
    (hne : ∀ a, h a ≠ []) (hS : ∀ a, a ∉ S → h a = h₀) : IsPEL (invHom h L) := by
  obtain ⟨g, hg⟩ := hL
  refine ⟨(PhSim.mk g h S h₀).grammar, fun w => ?_⟩
  rw [(PhSim.mk g h S h₀).grammar_iff hne hS w]
  exact hg _

end Shallot.Cfg
