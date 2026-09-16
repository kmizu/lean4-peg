import PalPeg.GSPreprocessProg4

/-! # Tape-driven signed displacement

This module compiles the displacement part of the second-phase reset.
The remaining displacement is stored on `Ce`; only the fixed exponent `k`
is unrolled into finite control.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def shiftSignedBase (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .right, Act.V2 .right]

def shiftSignedRest (k : ℕ) : Prog A9 Cond9 :=
  .seq (.seq (.act (tCp, .blk, .right)) (.act (tV2, .keep, .right)))
    (.seq sDecAProg (repeatProg sIncBProg (k - 1)))

def shiftSignedRestL (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  let t := applyActs blank (shiftSignedBase blank) ts
  shiftSignedBase blank ++ (sDecA blank mark t ++
    sIncBRepeated blank mark (k - 1) (applyActs blank (sDecA blank mark t) t))

theorem shiftSignedRest_exec (k : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (shiftSignedRest k) ts
      (shiftSignedRestL blank mark k ts) :=
  execA_seq (execA_seq (execA_ct_put ctCp .right ts) (execA_v2 .right _))
    (execA_seq (sDecAProg_exec _) (sIncBRepeated_exec (k - 1) _))

theorem sIncBRepeated_ce (n : ℕ) (ts : Tapes sc) :
    (applyActs blank (sIncBRepeated blank mark n ts) ts).Ce = ts.Ce := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    simp only [sIncBRepeated, applyActs_append, ih]
    unfold sIncBTrace
    split <;> rfl

theorem shiftSignedRest_ce (k : ℕ) (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (shiftSignedRestL blank mark k ts) ts) =
      (ctCe : CT sc).get ts := by
  change (applyActs blank (shiftSignedRestL blank mark k ts) ts).Ce = ts.Ce
  simp only [shiftSignedRestL, applyActs_append, sIncBRepeated_ce]
  unfold sDecA
  split <;> rfl

def SHIFT_SIGNED (k : ℕ) : Prog A9 Cond9 := DLOOP tCe (shiftSignedRest k)

theorem shiftSigned_exec (hmark : mark ≠ blank) (k n : ℕ) (ts : Tapes sc)
    (he : Tape.CounterView' blank mark ts.Ce n) :
    ExecA Terminal blank endSym mark (SHIFT_SIGNED k) ts
      (dPowS ctCe blank (shiftSignedRestL blank mark k) n ts ++ dTest ctCe blank mark) :=
  dLoopS_exec ctCe (shiftSignedRest k) (shiftSignedRestL blank mark k) hmark
    (shiftSignedRest_exec k) (shiftSignedRest_ce k) n ts he

theorem shiftSigned_length (k n : ℕ) (ts : Tapes sc) :
    (dPowS ctCe blank (shiftSignedRestL blank mark k) n ts ++ dTest ctCe blank mark).length
      ≤ n * (3 * k + 7) + 2 := by
  have hl : ∀ t : Tapes sc, (shiftSignedRestL blank mark k t).length ≤ 3 * k + 5 := by
    intro t
    have ha := sDecA_length_le blank mark (applyActs blank (shiftSignedBase blank) t)
    have hb := sIncBRepeated_length (blank := blank) (mark := mark) (k - 1)
      (applyActs blank (sDecA blank mark (applyActs blank (shiftSignedBase blank) t))
        (applyActs blank (shiftSignedBase blank) t))
    have hbase : (shiftSignedBase (sc := sc) blank).length = 2 := rfl
    simp only [shiftSignedRestL, List.length_append, hbase]
    omega
  have h := dPowS_length_le ctCe blank (shiftSignedRestL blank mark k) (3 * k + 5) hl n ts
  simpa [List.length_append, dTest, Nat.add_assoc] using Nat.add_le_add_right h 2

theorem shiftSignedUnit_effect {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k : ℕ) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩ g ts)
    (hb : b < x.length) :
    applyActs blank (shiftSignedRestL blank mark k (dStep ctCe blank ts))
      (dStep ctCe blank ts) = applyActs blank (shiftUnitS blank mark k ts) ts := by
  have hhead : EncS blank startSym endSym mark x a (b + 1)
      ⟨D, Q, E, P + 1, F, S, R⟩ g (applyActs blank (shiftHead blank) ts) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [applyActs_shiftHead]
    · exact ⟨hE.base.v1, pat_right hE.base.v2 hb, hE.base.cd, hE.base.cq,
        by simpa using Tape.counter'_dec (n := E) hE.base.ce,
        Tape.counter'_inc hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩
    · exact hE.ca
    · exact hE.cb
    · exact hE.cc
  have hbase : applyActs blank (shiftSignedBase blank) (dStep ctCe blank ts) =
      applyActs blank (shiftHead blank) ts := rfl
  have ha : sDecA blank mark ts =
      sDecA blank mark (applyActs blank (shiftHead blank) ts) :=
    sDecA_congr blank mark (by rw [applyActs_shiftHead])
  simp only [shiftSignedRestL, shiftUnitS, applyActs_append, hbase, ha]
  exact sIncBRepeated_effect hmark (k - 1) (sDecA_enc hmark hhead)

theorem shiftSignedPow_effect {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n : ℕ) :
    ∀ (a b D Q E P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ g ts →
    b + n ≤ x.length → SgnA M N g → SgnB M' N' ⟨D, Q, E + n, P, F, S, R⟩ g →
    applyActs blank (dPowS ctCe blank (shiftSignedRestL blank mark k) n ts) ts =
      applyActs blank (shiftLoopS blank mark k n ts) ts := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro a b D Q E P F S R M N M' N' g ts hE hfit hA hB
    have he : EncS blank startSym endSym mark x a b
        ⟨D, Q, (E + n) + 1, P, F, S, R⟩ g ts := by simpa [Nat.add_assoc] using hE
    have hunit := shiftSignedUnit_effect hmark k he (by omega)
    obtain ⟨D1, ap1, an1, bn1, he1, ha1, hb1⟩ :=
      shiftUnitS_enc hmark k he (by omega) hA hB
    have hnext := ih a (b + 1) D1 Q E (P + 1) F S R M (N + 1) (M' + (k - 1)) N'
      ⟨ap1, an1, bn1⟩ _ he1 (by omega) ha1 hb1
    simp only [dPowS, shiftLoopS, applyActs, List.foldl_append, List.foldl_cons]
    change applyActs blank (dPowS ctCe blank (shiftSignedRestL blank mark k) n
        (applyActs blank (shiftSignedRestL blank mark k (dStep ctCe blank ts))
          (dStep ctCe blank ts)))
        (applyActs blank (shiftSignedRestL blank mark k (dStep ctCe blank ts))
          (dStep ctCe blank ts)) =
      applyActs blank (shiftLoopS blank mark k n (applyActs blank (shiftUnitS blank mark k ts) ts))
        (applyActs blank (shiftUnitS blank mark k ts) ts)
    rw [hunit]
    exact hnext

/-- The entire displacement consumes `Ce`, leaving the same tapes as the
reference loop, including the final counter probe. -/
theorem SHIFT_SIGNED_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D Q P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc)
    (hE : EncS blank startSym endSym mark x a b ⟨D, Q, n, P, F, S, R⟩ g ts)
    (hfit : b + n ≤ x.length) (hA : SgnA M N g)
    (hB : SgnB M' N' ⟨D, Q, n, P, F, S, R⟩ g) :
    ∃ L : List (Act sc),
      ExecA Terminal blank endSym mark (SHIFT_SIGNED k) ts L ∧
      applyActs blank L ts = applyActs blank (shiftLoopS blank mark k n ts) ts ∧
      L.length ≤ n * (3 * k + 7) + 2 := by
  have heffect := shiftSignedPow_effect hmark k n a b D Q 0 P F S R M N M' N' g ts
    (by simpa using hE) hfit hA hB
  obtain ⟨D', ap', an', bn', he', _, _⟩ := shiftLoopS_enc hmark k n a b D Q 0 P F S R
    M N M' N' g ts (by simpa using hE) hfit hA hB
  refine ⟨_, shiftSigned_exec hmark k n ts hE.base.ce, ?_, shiftSigned_length k n ts⟩
  rw [applyActs_append, heffect]
  exact dTest_ce_effect hmark _ he'.base.ce

/-- info: 'PalPeg.GSPreProg.SHIFT_SIGNED_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SHIFT_SIGNED_spec

def MAX_ONE : Prog A9 Cond9 :=
  .seq (.act (tCe, .blk, .left))
    (.ite (.notMark tCe) (.act (tCe, .blk, .right))
      (.seq (.act (tCe, .mrk, .right)) (.act (tCe, .blk, .right))))

theorem MAX_ONE_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark MAX_ONE ts (maxOneActs blank mark ts) := by
  have hp : (getT (applyActs blank [ctCe.act blank .left] ts) tCe).focus =
      probe blank ts.Ce := rfl
  unfold MAX_ONE maxOneActs
  by_cases h : probe blank ts.Ce = mark
  · rw [if_pos h]
    apply execA_seq (execA_ct_put ctCe .left ts)
    apply execA_ite_neg
    · simp only [condOf9, hp, h, ne_eq, not_true_eq_false, decide_false]
    · exact execA_seq (execA_ct_mark ctCe .right _) (execA_ct_put ctCe .right _)
  · rw [if_neg h]
    apply execA_seq (execA_ct_put ctCe .left ts)
    apply execA_ite_pos
    · simp only [condOf9, hp, decide_eq_true_eq]; exact h
    · exact execA_ct_put ctCe .right _

end PalPeg.GSPreProg
