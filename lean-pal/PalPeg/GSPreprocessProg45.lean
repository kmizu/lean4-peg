import PalPeg.GSPreprocessProg44

/-! # Complete finite first search with restored tape heads -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem FIRST_OUTER_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s F S R A B fuel p : ℕ)
    (hk : 2 ≤ k) (hs : s ≤ x.length) (hp : 0 < p) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩
      ⟨foBound bounded bound p, A, B⟩ ts)
    (hbound : (x.drop s).length ≤ p + fuel) :
    ∃ L P Q, ExecA Terminal blank endSym mark (FIRST_OUTER bounded k) ts L ∧
      EncS blank startSym endSym mark x (s + Q) (s + P + Q)
        ⟨(k - 1) * P - Q, Q, 0, P, F, S, R⟩ ⟨foBound bounded bound P, A, B⟩
        (applyActs blank L ts) ∧
      0 < P ∧
      P ≤ p + firstOuterWork (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p ∧
      Q = (if (firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p).isSome
        then (k - 1) * P else 0) ∧
      (∀ p' m, firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel p = some (p', m) →
        P = p' ∧ P + Q = m) ∧
      ¬ foGuard blank endSym mark bounded (applyActs blank L ts) ∧
      L.length ≤ foRate k * firstOuterWork (x.drop s) k
        (foLimit bounded bound (x.drop s).length) fuel p + 4 := by
  obtain ⟨L1, u, P, Q, hx1, hu, he1, hp1, hsize, hflag, hanswer, hstop, hc1⟩ :=
    FO_RUN_spec (Terminal := Terminal) hend hmark bounded bound k s F S R A B hk hs
      fuel p ts hp he hbound
  obtain ⟨L, hx, hfin, hc⟩ := FIRST_OUTER_finish bounded k ts u he1.ca he1.base.cd L1 hx1 hu
  refine ⟨L, P, Q, hx, ?_, hp1, hsize, hflag, hanswer, ?_, ?_⟩
  · rw [hfin]; exact he1
  · rw [hfin]; exact hstop
  · omega

/-- Both entry modes have a concrete linear bound. The successful-output
    bound below is sharper when the first period is much shorter than the input. -/
theorem FIRST_OUTER_linear_cost (k n p W L : ℕ) (hp : 0 < p)
    (hw : W ≤ (k + 2) * (n + 1 - p)) (hc : L ≤ foRate k * W + 4) :
    L ≤ foRate k * (k + 2) * n + 4 := by
  have hn : n + 1 - p ≤ n := by omega
  have hw' := Nat.mul_le_mul_left (k + 2) hn
  have hmul := Nat.mul_le_mul_left (foRate k) (hw.trans hw')
  nlinarith

theorem FIRST_OUTER_success_cost (k p p1 W L : ℕ)
    (hw : W + (k + 2) * p ≤ (2 * k + 1) * p1 + 2)
    (hc : L ≤ foRate k * W + 4) :
    L ≤ foRate k * ((2 * k + 1) * p1 + 2) + 4 := by
  have hmul := Nat.mul_le_mul_left (foRate k)
    (show W ≤ (2 * k + 1) * p1 + 2 by omega)
  omega

/-- info: 'PalPeg.GSPreProg.FIRST_OUTER_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_OUTER_spec

end PalPeg.GSPreProg
