import PalPeg.GSPreprocessProg18

/-! # Scan steps with an incrementally maintained reach difference -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem getT_applyActs_other (j : Fin 12) (L : List (Act sc))
    (h : ∀ a ∈ L, actTape a ≠ j) (ts : Tapes sc) :
    getT (applyActs blank L ts) j = getT ts j := by
  induction L generalizing ts with
  | nil => rfl
  | cons a L ih =>
    change getT (applyActs blank L (applyAct blank ts a)) j = _
    rw [ih (fun b hb => h b (List.mem_cons_of_mem a hb)), getT_applyAct]
    exact if_neg (Ne.symm (h a (List.mem_cons_self ..)))

theorem shadowR_eq_of_frame (R : ℕ) (ts u : Tapes sc)
    (h : ∀ j, j ≠ tCr → getT ts j = getT u j) :
    shadowR blank mark R ts = shadowR blank mark R u := by
  apply tapes_ext
  intro j
  by_cases hj : j = tCr
  · subst j; rfl
  · rw [shadowR_get R ts j hj, shadowR_get R u j hj]
    exact h j hj

theorem shadowR_oneDec (R M N : ℕ) (ts : Tapes sc) :
    shadowR blank mark R (applyActs blank (oneDecL ctCr blank mark M N) ts) =
      shadowR blank mark R ts :=
  shadowR_eq_of_frame R _ ts (fun j hj => oneDec_other ctCr j hj M N ts)

theorem shadowR_oneInc (R M N : ℕ) (ts : Tapes sc) :
    shadowR blank mark R (applyActs blank (oneIncL ctCr blank mark M N) ts) =
      shadowR blank mark R ts :=
  shadowR_eq_of_frame R _ ts (fun j hj => oneInc_other ctCr j hj M N ts)

theorem sCond_shadowR (R : ℕ) (ts : Tapes sc) :
    sCond endSym (orcAB blank mark) (shadowR blank mark R ts) ↔
      sCond endSym (orcAB blank mark) ts := Iff.rfl

theorem sBodyL_shadowR (R : ℕ) (ts : Tapes sc) :
    sBodyL blank mark (shadowR blank mark R ts) = sBodyL blank mark ts := rfl

theorem sBodyL_noCr (ts : Tapes sc) :
    ∀ a ∈ sBodyL blank mark ts, actTape a ≠ tCr := by
  unfold sBodyL sBase sDecA sDecB
  split <;> split <;> simp [actTape, tCr] <;> decide

theorem sBodyL_Cr (ts : Tapes sc) :
    (applyActs blank (sBodyL blank mark ts) ts).Cr = ts.Cr :=
  getT_applyActs_other tCr _ (sBodyL_noCr ts) ts

def sBodyRProg : Prog A9 Cond9 := .seq sBodyProg (SIGNED1_DEC tCr)

def sBodyRL (blank mark : Fin sc) (R Q : ℕ) (ts : Tapes sc) : List (Act sc) :=
  sBodyL blank mark ts ++ oneDecL ctCr blank mark R Q

theorem sBodyRL_length (R Q : ℕ) (ts : Tapes sc) :
    (sBodyRL blank mark R Q ts).length ≤ 13 := by
  have ha := sDecA_length_le blank mark ts
  have hb := sDecB_length_le blank mark ts
  have hc := oneDec_length (blank := blank) (mark := mark) ctCr R Q
  simp only [sBodyRL, sBodyL, List.length_append, sBase_length]
  omega

theorem sBodyR_exec (hmark : mark ≠ blank) (R Q : ℕ) (ts : Tapes sc)
    (h : OneSgn blank mark R Q ts.Cr) :
    ExecA Terminal blank endSym mark sBodyRProg ts (sBodyRL blank mark R Q ts) := by
  apply execA_seq (sBodyProg_exec ts)
  apply oneDec_exec ctCr hmark
  change OneSgn blank mark R Q (applyActs blank (sBodyL blank mark ts) ts).Cr
  rw [sBodyL_Cr]
  exact h

theorem encR_s_step (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (h : EncR blank startSym endSym mark x a b c g ts) (hab : a ≤ b)
    (hc : sCond endSym (orcAB blank mark) ts) :
    EncR blank startSym endSym mark x (a + 1) (b + 1)
      ⟨c.d - 1, c.q + 1, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn + (if c.d = 0 then 1 else 0)⟩
      (applyActs blank (sBodyRL blank mark c.r c.q ts) ts) := by
  have hcs := (sCond_shadowR c.r ts).mpr hc
  have hs := encS_s_step hend hmark h.enc hab hcs
  rw [sActs, if_pos hcs] at hs
  change EncS blank startSym endSym mark x (a + 1) (b + 1) _ _
    (applyActs blank (sBodyL blank mark (shadowR blank mark c.r ts))
      (shadowR blank mark c.r ts)) at hs
  rw [sBodyL_shadowR] at hs
  refine ⟨?_, ?_⟩
  · change EncS blank startSym endSym mark x (a + 1) (b + 1) _ _
      (shadowR blank mark c.r (applyActs blank (sBodyRL blank mark c.r c.q ts) ts))
    rw [sBodyRL, applyActs_append, shadowR_oneDec,
      shadowR_applyActs c.r _ (sBodyL_noCr ts)]
    exact hs
  · change OneSgn blank mark c.r (c.q + 1)
      (applyActs blank (sBodyRL blank mark c.r c.q ts) ts).Cr
    rw [sBodyRL, applyActs_append]
    apply oneDec_spec ctCr hmark
    change OneSgn blank mark c.r c.q (applyActs blank (sBodyL blank mark ts) ts).Cr
    rw [sBodyL_Cr]
    exact h.diff

/-- info: 'PalPeg.GSPreProg.encR_s_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms encR_s_step

end PalPeg.GSPreProg
