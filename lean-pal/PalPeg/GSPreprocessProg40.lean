import PalPeg.GSPreprocessProg39

/-! # Finite first-phase displacement maintaining a saturated candidate bound -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

theorem satDecCa_enc (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b c ⟨g.ap - 1, g.an, g.bn⟩
      (applyActs blank (satDecRawL ctCa blank mark ts) ts) := by
  have ha := satDecRaw_counter ctCa hmark g.ap ts he.ca
  by_cases hc : probe blank ts.Ca = mark
  · simp only [satDecRawL, ctCa, hc, if_true] at ha ⊢
    exact ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, he.base.ce, he.base.cp,
      he.base.cf, he.base.cs, he.base.cr⟩, ha, he.cb, he.cc⟩
  · simp only [satDecRawL, ctCa, hc, if_false] at ha ⊢
    exact ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, he.base.ce, he.base.cp,
      he.base.cf, he.base.cs, he.base.cr⟩, ha, he.cb, he.cc⟩

def firstShiftBase (blank : Fin sc) (k : ℕ) : List (Act sc) :=
  shiftSignedBase blank ++ cdIncs blank (k - 1)

def firstShiftRest (k : ℕ) : Prog A9 Cond9 :=
  .seq (.seq (.seq (.act (tCp, .blk, .right)) (.act (tV2, .keep, .right))) (CD_UP (k - 1)))
    (SAT_DEC tCa)

def firstShiftRestL (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  firstShiftBase blank k ++ satDecRawL ctCa blank mark (applyActs blank (firstShiftBase blank k) ts)

theorem firstShiftRest_exec (k : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (firstShiftRest k) ts (firstShiftRestL blank mark k ts) :=
  execA_seq (execA_seq (execA_seq (execA_ct_put ctCp .right ts) (execA_v2 .right _))
    (CD_UP_exec (k - 1) _)) (satDecRaw_exec ctCa _)

theorem firstShiftRest_ce (k : ℕ) (ts : Tapes sc) :
    (ctCe : CT sc).get (applyActs blank (firstShiftRestL blank mark k ts) ts) = ctCe.get ts := by
  have ha := satDecRaw_other (blank := blank) (mark := mark) ctCa tCe
    (by change (4 : Fin 12) ≠ 9; decide)
    (applyActs blank (firstShiftBase blank k) ts)
  have hb := cdIncs_other (blank := blank) (k - 1) tCe (by decide)
    (applyActs blank (shiftSignedBase blank) ts)
  change (applyActs blank (firstShiftRestL blank mark k ts) ts).Ce = ts.Ce
  rw [firstShiftRestL, applyActs_append]
  change (applyActs blank (satDecRawL ctCa blank mark _) _).Ce =
    (applyActs blank (firstShiftBase blank k) ts).Ce at ha
  rw [ha]
  change (applyActs blank (cdIncs blank (k - 1)) _).Ce =
    (applyActs blank (shiftSignedBase blank) ts).Ce at hb
  rw [firstShiftBase, applyActs_append, hb]
  rfl

theorem firstShiftRest_length (k : ℕ) (ts : Tapes sc) :
    (firstShiftRestL blank mark k ts).length ≤ k + 4 := by
  simp only [firstShiftRestL, firstShiftBase, List.length_append, satDecRaw_length, cdIncs_length]
  change 2 + (k - 1) + 2 ≤ k + 4
  omega

theorem firstShiftUnit_enc (hmark : mark ≠ blank) (k : ℕ)
    {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩ g ts)
    (hb : b < x.length) :
    EncS blank startSym endSym mark x a (b + 1) ⟨D + (k - 1), Q, E, P + 1, F, S, R⟩
      ⟨g.ap - 1, g.an, g.bn⟩
      (applyActs blank (firstShiftRestL blank mark k (dStep ctCe blank ts)) (dStep ctCe blank ts)) := by
  have he1 := he.frame (acts := shiftUnit blank k)
    (by simp [shiftUnit, shiftHead, Act.noSigned]) (shift_unit_enc he.base hb)
  have heff : applyActs blank (firstShiftBase blank k) (dStep ctCe blank ts) =
      applyActs blank (shiftUnit blank k) ts := by
    simp only [firstShiftBase, shiftUnit, applyActs_append]
    rfl
  rw [firstShiftRestL, applyActs_append, heff]
  exact satDecCa_enc hmark he1

theorem firstShiftPow_enc (hmark : mark ≠ blank) (k n : ℕ) :
    ∀ (a b D Q E P F S R : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ g ts → b + n ≤ x.length →
    EncS blank startSym endSym mark x a (b + n) ⟨D + (k - 1) * n, Q, E, P + n, F, S, R⟩
      ⟨g.ap - n, g.an, g.bn⟩
      (applyActs blank (dPowS ctCe blank (firstShiftRestL blank mark k) n ts) ts) := by
  induction n with
  | zero => intro a b D Q E P F S R g ts he hb; simpa [dPowS] using he
  | succ n ih =>
    intro a b D Q E P F S R g ts he hb
    have he1 := firstShiftUnit_enc hmark k (E := E + n)
      (by simpa only [Nat.add_assoc] using he) (by omega)
    have hi := ih a (b + 1) (D + (k - 1)) Q E (P + 1) F S R
      ⟨g.ap - 1, g.an, g.bn⟩ _ he1 (by omega)
    simpa only [dPowS, applyActs, List.foldl_append, List.foldl_cons, List.foldl_nil,
      dStep, Nat.mul_succ, Nat.sub_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

def FIRST_SHIFT (k : ℕ) : Prog A9 Cond9 := DLOOP tCe (firstShiftRest k)

theorem FIRST_SHIFT_spec (hmark : mark ≠ blank) (k n a b D Q P F S R : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x a b ⟨D, Q, n, P, F, S, R⟩ g ts)
    (hb : b + n ≤ x.length) :
    ∃ L, ExecA Terminal blank endSym mark (FIRST_SHIFT k) ts L ∧
      EncS blank startSym endSym mark x a (b + n) ⟨D + (k - 1) * n, Q, 0, P + n, F, S, R⟩
        ⟨g.ap - n, g.an, g.bn⟩ (applyActs blank L ts) ∧ L.length ≤ n * (k + 6) + 2 := by
  let L := dPowS ctCe blank (firstShiftRestL blank mark k) n ts
  have hx := dLoopS_exec (Terminal := Terminal) (endSym := endSym) ctCe (firstShiftRest k)
    (firstShiftRestL blank mark k) hmark (firstShiftRest_exec k) (firstShiftRest_ce k)
    n ts he.base.ce
  have hout := firstShiftPow_enc hmark k n a b D Q 0 P F S R g ts
    (by simpa only [Nat.zero_add] using he) hb
  have hr := ct_dTest_restore ctCe hmark (applyActs blank L ts) hout.base.ce
  refine ⟨L ++ dTest ctCe blank mark, hx, ?_, ?_⟩
  · rw [applyActs_append, hr]; exact hout
  · have hc := dPowS_length_le ctCe blank (firstShiftRestL blank mark k) (k + 4)
      (firstShiftRest_length k) n ts
    simp only [List.length_append]
    change L.length + 2 ≤ n * (k + 6) + 2
    exact Nat.add_le_add_right hc 2

end PalPeg.GSPreProg
