import PalPeg.GSPreprocessProg52
import PalPeg.GSPreprocessProg35

/-! # Reposition, seed, run the second search, and clear its scratch space -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def SECOND_PHASE (k : ℕ) : Prog A9 Cond9 :=
  .seq REPO (.seq (SEED_SIGNED k) (.seq (SECOND_SEARCH k) CLEAR_SIGNED))

theorem SECOND_PHASE_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k fuel : ℕ) (hk : 3 ≤ k) {s first S r : ℕ} {ts : Tapes sc}
    (hf : 0 < first) (hfr : first ≤ r)
    (he : EncS blank startSym endSym mark x (s + (r - first)) (s + r)
      ⟨0, 0, 0, first, 0, S, r⟩ ⟨0, 0, 0⟩ ts)
    (hbound : (x.drop s).length ≤ 1 + fuel) :
    ∃ L E P, ExecA Terminal blank endSym mark (SECOND_PHASE k) ts L ∧
      EncS blank startSym endSym mark x s (s + P)
        ⟨0, 0, E, P, first, S, r⟩ ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      s + P ≤ x.length ∧
      P ≤ 1 + secondOuterWork (x.drop s) k first r fuel 1 0 ∧
      (∀ p2, secondOuter (x.drop s) k first r fuel 1 0 = some p2 → P = p2) ∧
      E = (if (secondOuter (x.drop s) k first r fuel 1 0).isSome then 1 else 0) ∧
      L.length ≤ (soRRate k + 2 * k) * secondOuterWork (x.drop s) k first r fuel 1 0 +
        17 * r + 17 * first + 3 * k + 52 := by
  obtain ⟨L1, hx1, h1, hl1⟩ := REPO_spec (Terminal := Terminal) hmark hf hfr he
  obtain ⟨L2, hx2, h2, hok2, hl2⟩ := SEED_SIGNED_spec (Terminal := Terminal)
    hmark k hk (by omega) h1
  have hfit := pat_le h1.base.v2
  obtain ⟨L3, D3, E3, P3, g3, hx3, h3, hok3, hfit3, hsize3, hans3, hflag3, hl3⟩ :=
    SECOND_SEARCH_spec (Terminal := Terminal) hend hmark k r s first S fuel 1 0 (k - 2)
      (by omega) hf (by omega) _ _ (by simpa using h2) hok2 (by omega) hbound
  obtain ⟨L4, hx4, h4, hl4⟩ := CLEAR_SIGNED_spec (Terminal := Terminal) hmark h3
  have hc := CLEAR_SIGNED_bound blank (by omega : 1 ≤ k) hok3
  have hp := Nat.mul_le_mul_left (2 * k) hsize3
  refine ⟨_, E3, P3, execA_seq hx1 (execA_seq hx2 (execA_seq hx3 hx4)), ?_,
    hfit3, by simpa using hsize3, hans3, hflag3, ?_⟩
  · simpa only [applyActs_append] using h4
  · simp only [List.length_append, hl2, hl4]
    simp only [Nat.mul_zero, Nat.add_zero] at hl3 hc hp
    have hk2 : k - 2 ≤ k := Nat.sub_le k 2
    nlinarith only [hl1, hl3, hc, hp, hk2]

/-- info: 'PalPeg.GSPreProg.SECOND_PHASE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SECOND_PHASE_spec
end PalPeg.GSPreProg
