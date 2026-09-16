import PalPeg.GSPreprocessProg47

/-! # Finite initialization for the first search -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def FIRST_INIT (k : ℕ) : Prog A9 Cond9 :=
  .seq (.seq (CD_UP (k - 1))
    (.seq (.act (tCp, .blk, .right)) (.act (tV2, .keep, .right)))) (SAT_DEC tCa)

def firstInitL (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  initActs blank k ++ satDecRawL ctCa blank mark (applyActs blank (initActs blank k) ts)

theorem FIRST_INIT_exec (k : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (FIRST_INIT k) ts (firstInitL blank mark k ts) := by
  exact execA_seq (execA_seq (CD_UP_exec (k - 1) ts)
    (execA_seq (execA_ct_put ctCp .right _) (execA_v2 .right _))) (satDecRaw_exec ctCa _)

theorem FIRST_INIT_spec (hmark : mark ≠ blank) (k s F S R : ℕ) (g : Ctr3)
    (ts : Tapes sc) (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark (FIRST_INIT k) ts L ∧
      EncS blank startSym endSym mark x s (s + 1) ⟨k - 1, 0, 0, 1, F, S, R⟩
        ⟨g.ap - 1, g.an, g.bn⟩ (applyActs blank L ts) ∧ L.length = (k - 1) + 4 := by
  have he₁ := he.frame (acts := initActs blank k)
    (by simp [initActs, Act.noSigned]) (initActs_enc hs he.base)
  refine ⟨firstInitL blank mark k ts, FIRST_INIT_exec k ts, ?_, ?_⟩
  · rw [firstInitL, applyActs_append]
    simpa using satDecCa_enc hmark he₁
  · simp [firstInitL, initActs, satDecRaw_length]

def FIRST_SEARCH (bounded : Bool) (k : ℕ) : Prog A9 Cond9 :=
  .seq (FIRST_INIT k) (FIRST_OUTER bounded k)

theorem FIRST_SEARCH_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s F S R A B fuel : ℕ)
    (hk : 2 ≤ k) (hs : s < x.length) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩
      ⟨foBound bounded bound 0, A, B⟩ ts)
    (hbound : (x.drop s).length ≤ 1 + fuel) :
    ∃ L P Q, ExecA Terminal blank endSym mark (FIRST_SEARCH bounded k) ts L ∧
      EncS blank startSym endSym mark x (s + Q) (s + P + Q)
        ⟨(k - 1) * P - Q, Q, 0, P, F, S, R⟩ ⟨foBound bounded bound P, A, B⟩
        (applyActs blank L ts) ∧
      0 < P ∧
      P ≤ 1 + firstOuterWork (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1 ∧
      Q = (if (firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1).isSome
        then (k - 1) * P else 0) ∧
      (∀ p' m, firstOuter (x.drop s) k (foLimit bounded bound (x.drop s).length) fuel 1 = some (p', m) →
        P = p' ∧ P + Q = m) ∧
      ¬ foGuard blank endSym mark bounded (applyActs blank L ts) ∧
      L.length ≤ (k - 1) + 8 + foRate k * firstOuterWork (x.drop s) k
        (foLimit bounded bound (x.drop s).length) fuel 1 := by
  obtain ⟨L₁, hx₁, he₁, hl₁⟩ := FIRST_INIT_spec (Terminal := Terminal)
    hmark k s F S R _ ts hs he
  have hb : foBound bounded bound 0 - 1 = foBound bounded bound 1 := by
    cases bounded <;> simp [foBound]
  simp only [hb] at he₁
  obtain ⟨L₂, P, Q, hx₂, he₂, hp, hsize, hflag, hans, hstop, hl₂⟩ :=
    FIRST_OUTER_spec (Terminal := Terminal) hend hmark bounded bound k s F S R A B fuel 1
      hk (by omega) (by omega) _ (by simpa using he₁) hbound
  refine ⟨L₁ ++ L₂, P, Q, execA_seq hx₁ hx₂, ?_, hp, hsize, hflag, hans, ?_, ?_⟩
  · simpa only [applyActs_append] using he₂
  · simpa only [applyActs_append] using hstop
  · rw [List.length_append, hl₁]
    omega

/-- info: 'PalPeg.GSPreProg.FIRST_SEARCH_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_SEARCH_spec

/-- info: 'PalPeg.GSPreProg.FIRST_INIT_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FIRST_INIT_spec

end PalPeg.GSPreProg
