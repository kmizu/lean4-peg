import PalPeg.GSPreprocessProg28

/-! # The finite scan realizes the reference inner search -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem SCAN_R_second_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s p q D E first S : ℕ) (g : Ctr3) (ts : Tapes sc) (hs : s ≤ x.length)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, first, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, first, S, r⟩ g)
    (hfit : s + p + q ≤ x.length) :
    ∃ L D' g' j, ExecA Terminal blank endSym mark SCAN_R ts L ∧
      EncR blank startSym endSym mark x (s + (q + j)) (s + p + (q + j))
        ⟨D', q + j, E, p, first, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r p (q + j) ⟨D', q + j, E, p, first, S, r⟩ g' ∧
      s + p + (q + j) ≤ x.length ∧
      j ≤ secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q ∧
      secondInner (x.drop s) k p r ((x.drop s).length + 1) q =
        (if sAbort endSym (orcAB blank mark) (applyActs blank L ts)
          then none else some (q + j)) ∧
      L.length ≤ 17 * j + 4 := by
  let fuel := (x.drop s).length + 1
  have hbound : x.length ≤ s + p + q + fuel := by
    dsimp only [fuel]; rw [List.length_drop]; omega
  obtain ⟨L, D', g', hx, he', hok', hc⟩ :=
    SCAN_R_spec (Terminal := Terminal) hend hmark k r s p fuel q D E first S g ts he hok hbound
  let j := sSteps x k p r s fuel q
  have he1 : EncR blank startSym endSym mark x (s + (q + j)) (s + p + (q + j))
      ⟨D', q + j, E, p, first, S, r⟩ g' (applyActs blank L ts) := by
    simpa only [Nat.add_assoc] using he'
  have hfit1 : s + p + (q + j) ≤ x.length := by
    have hh := sSteps_fit x k p r s fuel q hfit
    omega
  have hnone := sInner_none_iff (x := x) (k := k) (p := p) (r := r) hs
    fuel q hfit (by dsimp only [fuel]; rw [List.length_drop]; omega)
  have hab := sAbort_iffR hend hmark he1 hok'
  have hsi : secondInner (x.drop s) k p r fuel q =
      (if sAbort endSym (orcAB blank mark) (applyActs blank L ts) then none else some (q + j)) := by
    by_cases ha : sAbort endSym (orcAB blank mark) (applyActs blank L ts)
    · rw [if_pos ha]
      exact hnone.mpr (hab.mp ha)
    · rw [if_neg ha]
      cases hh : secondInner (x.drop s) k p r fuel q with
      | none => exact False.elim (ha (hab.mpr (hnone.mp hh)))
      | some q' =>
        have hh' := (sSteps_secondInner (x := x) (k := k) (r := r) (p := p)
          hs fuel q hfit).1 q' hh
        rw [hh']
  refine ⟨L, D', g', j, hx, he1, hok', hfit1, ?_, hsi, hc⟩
  have hW := (sSteps_secondInner (x := x) (k := k) (r := r) (p := p)
    hs fuel q hfit).2
  have hj := sSteps_le_sWork x k p r s fuel q
  rw [hW] at hj
  exact hj

/-- info: 'PalPeg.GSPreProg.SCAN_R_second_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SCAN_R_second_spec

end PalPeg.GSPreProg
