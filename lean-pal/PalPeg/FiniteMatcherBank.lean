import PalPeg.GSVerifierProgZLoop
import PalPeg.ProgLangBankTapes

/-! Fixed zigzag loops retain their continuation and direction under slot switching. -/

set_option autoImplicit false

namespace PalPeg.GSVProgZLoop

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.GSVProg PalPeg.GSVTapes PalPeg.GSVTapesZ

variable {sc n : ℕ} {Terminal : Type}

noncomputable def bankInterp (blank endSym mark startSym : Fin sc) :
    InterpF Terminal (Act10 ⊕ Bool) (Cond10 ⊕ DCond) (Fin sc) 11 where
  toInterp := interp blank endSym mark startSym
  flagOf _ := none

theorem loopProg_interleaved {blank endSym mark startSym : Fin sc}
    {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc}
    {z : PalPeg.GSVerifierZ.VStateZ}
    (hk : 0 < k) (hp : 0 < p₁) (hmb : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v)
    (hendu : endSym ∉ u) (hstartu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hwf : PalPeg.GSVerifierZ.ZWf u.length z.2) (hq : z.1.q ≤ v.length)
    (hpos : u.length ≤ z.1.pos)
    (hfit : (PalPeg.scanStep v k p₁ r Text z.1).pos +
      (PalPeg.scanStep v k p₁ r Text z.1).q < Text.length)
    (i : Fin n)
    (x : (Bank (fun _ : Fin n => loopProg k) × Bool) × (Fin (n * 11) → STape (Fin sc)))
    (hx : tapeSlice i x.2 = tapes blank mark vt z.2.up)
    (hs : SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
      (tapes blank mark vt z.2.up) (x.1.1 i).val [loopProg k]) :
    let z' := PalPeg.GSVerifierZ.vStepZ u v k p₁ r Text z
    ∃ cost s' vt',
      VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt' z' ∧
      SEqAt (interp (Terminal := Terminal) blank endSym mark startSym)
        (tapes blank mark vt' z'.2.up) s' [loopProg k] ∧
      0 < cost ∧ cost ≤ zA k * (PalPeg.Phi k z'.1 - PalPeg.Phi k z.1) + 18 ∧
      ∀ l : List (Fin n × Option Terminal), localInputs i l = List.replicate cost none →
        localState (fun _ : Fin n => loopProg k) i
          (runInterleaved (fun _ : Fin n => loopProg k)
            (fun _ => bankInterp blank endSym mark startSym) blank l x) =
          (s', tapes blank mark vt' z'.2.up) := by
  obtain ⟨cost, s', vt', hr, hseq, he, hposc, hcost⟩ :=
    loopProg_chunk_spec (Terminal := Terminal) hk hp hmb hstart hend hendu hstartu hse
      hE hwf hq hpos hfit (x.1.1 i).val hs
  refine ⟨cost, s', vt', he, hseq, hposc, hcost, ?_⟩
  intro l hl
  have h := runInterleaved_local (fun _ : Fin n => loopProg k)
    (fun _ => bankInterp blank endSym mark startSym) blank i l x
  rw [hl] at h
  conv_rhs at h => arg 4; unfold localState; rw [hx]
  exact h.trans hr

/-- info: 'PalPeg.GSVProgZLoop.loopProg_interleaved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loopProg_interleaved

end PalPeg.GSVProgZLoop
