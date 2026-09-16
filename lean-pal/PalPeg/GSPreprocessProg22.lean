import PalPeg.GSPreprocessProg21

/-! # Rewind bodies maintaining the reach difference -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def rewindRRest : Prog A9 Cond9 :=
  .seq rewindSignedRest (SIGNED1_INC tCr)

def rewindRRestL (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  rewindSignedRestL blank mark ts ++
    oneIncTrace ctCr blank mark (applyActs blank (rewindSignedRestL blank mark ts) ts)

theorem rewindRRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark rewindRRest ts (rewindRRestL blank mark ts) :=
  execA_seq (rewindSignedRest_exec ts) (oneIncTrace_exec ctCr _)

theorem rewindRRest_cq (ts : Tapes sc) :
    (applyActs blank (rewindRRestL blank mark ts) ts).Cq = ts.Cq := by
  unfold rewindRRestL
  rw [applyActs_append]
  have h := oneIncTrace_other (blank := blank) (mark := mark) ctCr tCq
    (by change (3 : Fin 12) ≠ 8; decide) (applyActs blank (rewindSignedRestL blank mark ts) ts)
  change (applyActs blank (oneIncTrace ctCr blank mark _) _).Cq = _ at h
  exact h.trans (rewindSignedRest_cq ts)

theorem rewindRRest_length (ts : Tapes sc) :
    (rewindRRestL blank mark ts).length ≤ 12 := by
  have ha := rewindSignedRest_length (blank := blank) (mark := mark) ts
  have hb := oneIncTrace_length (blank := blank) (mark := mark) ctCr
    (applyActs blank (rewindSignedRestL blank mark ts) ts)
  simp only [rewindRRestL, List.length_append]
  omega

theorem rewindSignedRestL_noCr (ts : Tapes sc) :
    ∀ a ∈ rewindSignedRestL blank mark ts, actTape a ≠ tCr := by
  unfold rewindSignedRestL rewindSignedBase sIncATrace sIncBTrace
  dsimp only
  split <;> split <;> simp [actTape, tCr] <;> decide

theorem rewindSignedRestL_Cr (ts : Tapes sc) :
    (applyActs blank (rewindSignedRestL blank mark ts) ts).Cr = ts.Cr :=
  getT_applyActs_other tCr _ (rewindSignedRestL_noCr ts) ts

theorem rewindRRest_diff (hmark : mark ≠ blank) {R Q : ℕ} {ts : Tapes sc}
    (h : OneSgn blank mark R Q ts.Cr) :
    OneSgn blank mark (R + 1) Q
      (applyActs blank (rewindRRestL blank mark ts) ts).Cr := by
  unfold rewindRRestL
  rw [applyActs_append]
  apply oneIncTrace_spec ctCr hmark
  change OneSgn blank mark R Q (applyActs blank (rewindSignedRestL blank mark ts) ts).Cr
  rw [rewindSignedRestL_Cr]
  exact h

theorem rewindSignedRestL_shadowR (R : ℕ) (ts : Tapes sc) :
    rewindSignedRestL blank mark (shadowR blank mark R ts) =
      rewindSignedRestL blank mark ts := by
  unfold rewindSignedRestL sIncATrace
  dsimp only
  have hh : (applyActs blank rewindSignedBase (shadowR blank mark R ts)).Cb =
      (applyActs blank rewindSignedBase ts).Cb := rfl
  rw [hh]
  split <;> rfl

theorem shadowR_oneIncTrace (R : ℕ) (ts : Tapes sc) :
    shadowR blank mark R (applyActs blank (oneIncTrace ctCr blank mark ts) ts) =
      shadowR blank mark R ts :=
  shadowR_eq_of_frame R _ ts (fun j hj => oneIncTrace_other ctCr j hj ts)

theorem rewindRUnit_enc {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) {a b D Q E P F S R M N M' N' : ℕ}
    {g : Ctr3} {ts : Tapes sc}
    (he : EncR blank startSym endSym mark x (a + 1) (b + 1)
      ⟨D, Q + 1, E, P, F, S, R⟩ g ts)
    (ha : SgnA M (N + 1) g)
    (hb : SgnB M' (N' + 1) ⟨D, Q + 1, E, P, F, S, R⟩ g) :
    ∃ D' g', EncR blank startSym endSym mark x a b ⟨D', Q, E, P, F, S, R⟩ g'
      (applyActs blank (rewindRRestL blank mark (dStep ctCq blank ts))
        (dStep ctCq blank ts)) ∧
      SgnA M N g' ∧ SgnB M' N' ⟨D', Q, E, P, F, S, R⟩ g' := by
  obtain ⟨D', ap, an, bn, he1, ha1, hb1⟩ := rewindUnit2S_enc hmark he.enc ha hb
  have hu := rewindSignedUnit_effect hmark he.enc
  rw [← hu] at he1
  have hd : dStep ctCq blank (shadowR blank mark R ts) =
      shadowR blank mark R (dStep ctCq blank ts) := rfl
  rw [hd, rewindSignedRestL_shadowR] at he1
  refine ⟨D', ⟨ap, an, bn⟩, ⟨?_, ?_⟩, ha1, hb1⟩
  · change EncS blank startSym endSym mark x a b _ _
      (shadowR blank mark R (applyActs blank (rewindRRestL blank mark _) _))
    rw [rewindRRestL, applyActs_append, shadowR_oneIncTrace,
      shadowR_applyActs R _ (rewindSignedRestL_noCr _)]
    exact he1
  · apply (OneSgn_add_cancel R Q 1 _).mp
    apply rewindRRest_diff hmark
    exact he.diff

theorem rewindRPow_enc {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (n : ℕ) :
    ∀ (a b D Q E P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncR blank startSym endSym mark x (a + n) (b + n)
      ⟨D, Q + n, E, P, F, S, R⟩ g ts →
    SgnA M (N + n) g → SgnB M' (N' + n) ⟨D, Q + n, E, P, F, S, R⟩ g →
    ∃ D' g', EncR blank startSym endSym mark x a b ⟨D', Q, E, P, F, S, R⟩ g'
      (applyActs blank (dPowS ctCq blank (rewindRRestL blank mark) n ts) ts) ∧
      SgnA M N g' ∧ SgnB M' N' ⟨D', Q, E, P, F, S, R⟩ g' := by
  induction n with
  | zero => intro a b D Q E P F S R M N M' N' g ts he ha hb; exact ⟨D, g, he, ha, hb⟩
  | succ n ih =>
    intro a b D Q E P F S R M N M' N' g ts he ha hb
    have he0 : EncR blank startSym endSym mark x ((a + n) + 1) ((b + n) + 1)
        ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g ts := by simpa [Nat.add_assoc] using he
    have ha0 : SgnA M ((N + n) + 1) g := by simpa only [Nat.add_assoc] using ha
    have hb0 : SgnB M' ((N' + n) + 1) ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g := by
      simpa only [Nat.add_assoc] using hb
    obtain ⟨D1, g1, he1, ha1, hb1⟩ := rewindRUnit_enc hmark he0 ha0 hb0
    obtain ⟨D2, g2, he2, ha2, hb2⟩ := ih a b D1 Q E P F S R M N M' N'
      g1 _ he1 ha1 hb1
    refine ⟨D2, g2, ?_, ha2, hb2⟩
    simp only [dPowS, applyActs, List.foldl_append, List.foldl_cons]
    exact he2

/-- info: 'PalPeg.GSPreProg.rewindRPow_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rewindRPow_enc

/-- info: 'PalPeg.GSPreProg.rewindRRest_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rewindRRest_exec

end PalPeg.GSPreProg
