import PalPeg.GSPreprocessProg7

/-! # Signed rewind groups -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def sIncAProg : Prog A9 Cond9 := SIGNED_DEC tCb tCa

def sIncATrace (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Cb = mark then
    [Act.Cb blank .left, Act.Cb mark .right, Act.Ca blank .right]
  else [Act.Cb blank .left, Act.Cb blank .stay]

theorem sIncAProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sIncAProg ts (sIncATrace blank mark ts) :=
  signed_dec_exec ctCb ctCa ts

theorem sIncATrace_effect (ts : Tapes sc) {n : ℕ}
    (hn : Tape.CounterView' blank mark ts.Cb n) :
    applyActs blank (sIncATrace blank mark ts) ts =
      applyActs blank (sIncA blank mark ts) ts := by
  unfold sIncATrace sIncA
  by_cases h : probe blank ts.Cb = mark
  · rw [if_pos h, if_pos h]
    have he := counter_probe_restore hn
    rw [h] at he
    change { ts with
      Cb := Tape.step blank (Tape.step blank ts.Cb blank .left) mark .right
      Ca := Tape.step blank ts.Ca blank .right } =
      { ts with Ca := Tape.step blank ts.Ca blank .right }
    rw [he]
  · rw [if_neg h, if_neg h]

theorem sIncATrace_length (ts : Tapes sc) :
    (sIncATrace blank mark ts).length ≤ 3 := by
  unfold sIncATrace
  split <;> simp

def rewindSignedBase : List (Act sc) := [Act.V1 .left, Act.V2 .left]

def rewindSignedRest : Prog A9 Cond9 :=
  .seq (.seq (.act (tV1, .keep, .left)) (.act (tV2, .keep, .left)))
    (.seq sIncAProg sIncBProg)

def rewindSignedRestL (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  let t := applyActs blank rewindSignedBase ts
  rewindSignedBase ++ (sIncATrace blank mark t ++
    sIncBTrace blank mark (applyActs blank (sIncATrace blank mark t) t))

theorem rewindSignedRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark rewindSignedRest ts (rewindSignedRestL blank mark ts) :=
  execA_seq (execA_seq (execA_v1 .left ts) (execA_v2 .left _))
    (execA_seq (sIncAProg_exec _) (sIncBProg_exec _))

theorem rewindSignedRest_cq (ts : Tapes sc) :
    (applyActs blank (rewindSignedRestL blank mark ts) ts).Cq = ts.Cq := by
  unfold rewindSignedRestL
  simp only [applyActs_append]
  unfold sIncBTrace
  split <;> (unfold sIncATrace; split <;> rfl)

theorem rewindSignedRest_length (ts : Tapes sc) :
    (rewindSignedRestL blank mark ts).length ≤ 8 := by
  have ha := sIncATrace_length (blank := blank) (mark := mark)
    (applyActs blank rewindSignedBase ts)
  have hb := sIncBTrace_length (blank := blank) (mark := mark)
    (applyActs blank (sIncATrace blank mark (applyActs blank rewindSignedBase ts))
      (applyActs blank rewindSignedBase ts))
  simp only [rewindSignedRestL, List.length_append]
  change 2 + (_ + _) ≤ 8
  omega

theorem rewindSignedUnit_effect {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (a + 1) (b + 1)
      ⟨D, Q + 1, E, P, F, S, R⟩ g ts) :
    applyActs blank (rewindSignedRestL blank mark (dStep ctCq blank ts))
      (dStep ctCq blank ts) = applyActs blank (rewindUnit2S blank mark ts) ts := by
  have hbase : applyActs blank rewindSignedBase (dStep ctCq blank ts) =
      applyActs blank (rewindUnit2 blank) ts := rfl
  have h0 : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g
      (applyActs blank (rewindUnit2 blank) ts) := by
    refine ⟨rewind2_unit_enc hE.base, ?_, ?_, ?_⟩ <;> rw [applyActs_rewindUnit2]
    · exact hE.ca
    · exact hE.cb
    · exact hE.cc
  have ha : sIncA blank mark ts = sIncA blank mark (applyActs blank (rewindUnit2 blank) ts) :=
    sIncA_congr blank mark (by rw [applyActs_rewindUnit2])
  have hb : sIncB blank mark ts = sIncB blank mark
      (applyActs blank (sIncA blank mark (applyActs blank (rewindUnit2 blank) ts))
        (applyActs blank (rewindUnit2 blank) ts)) := by
    apply sIncB_congr
    unfold sIncA
    split <;> rfl
  simp only [rewindSignedRestL, applyActs_append, hbase, sIncATrace_effect _ h0.cb]
  rw [sIncBTrace_effect _ (sIncA_enc hmark h0).cc]
  simp only [rewindUnit2S, applyActs_append, ha, hb]

theorem rewindSignedPow_enc {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (n : ℕ) :
    ∀ (a b D Q E P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x (a + n) (b + n)
      ⟨D, Q + n, E, P, F, S, R⟩ g ts →
    SgnA M (N + n) g → SgnB M' (N' + n) ⟨D, Q + n, E, P, F, S, R⟩ g →
    ∃ D' g', EncS blank startSym endSym mark x a b ⟨D', Q, E, P, F, S, R⟩ g'
      (applyActs blank (dPowS ctCq blank (rewindSignedRestL blank mark) n ts) ts) ∧
      SgnA M N g' ∧ SgnB M' N' ⟨D', Q, E, P, F, S, R⟩ g' := by
  induction n with
  | zero => intro a b D Q E P F S R M N M' N' g ts he ha hb; exact ⟨D, g, he, ha, hb⟩
  | succ n ih =>
    intro a b D Q E P F S R M N M' N' g ts he ha hb
    have he0 : EncS blank startSym endSym mark x ((a + n) + 1) ((b + n) + 1)
        ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g ts := by simpa [Nat.add_assoc] using he
    have hu := rewindSignedUnit_effect hmark he0
    have ha0 : SgnA M ((N + n) + 1) g := by simpa only [Nat.add_assoc] using ha
    have hb0 : SgnB M' ((N' + n) + 1) ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g := by
      simpa only [Nat.add_assoc] using hb
    obtain ⟨D1, ap1, an1, bn1, he1, ha1, hb1⟩ := rewindUnit2S_enc hmark he0
      ha0 hb0
    obtain ⟨D2, g2, he2, ha2, hb2⟩ := ih a b D1 Q E P F S R M N M' N'
      ⟨ap1, an1, bn1⟩ _ he1 ha1 hb1
    refine ⟨D2, g2, ?_, ha2, hb2⟩
    simp only [dPowS, applyActs, List.foldl_append, List.foldl_cons]
    change EncS blank startSym endSym mark x a b ⟨D2, Q, E, P, F, S, R⟩ g2
      (applyActs blank (dPowS ctCq blank (rewindSignedRestL blank mark) n
        (applyActs blank (rewindSignedRestL blank mark (dStep ctCq blank ts))
          (dStep ctCq blank ts)))
        (applyActs blank (rewindSignedRestL blank mark (dStep ctCq blank ts))
          (dStep ctCq blank ts)))
    rw [hu]
    exact he2

def rewindSignedGroup (k : ℕ) : Prog A9 Cond9 :=
  .seq (.act (tCe, .blk, .right)) (QBLOCK rewindSignedRest k)

def REWIND_SIGNED (k : ℕ) : Prog A9 Cond9 := QGROUP (rewindSignedGroup k)

theorem rewindSignedGroup_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D E P F S R M N M' N' : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E, P, F, S, R⟩ g ts)
    (ha : SgnA M (N + n) g) (hb : SgnB M' (N' + n) ⟨D, n, E, P, F, S, R⟩ g) :
    ∃ B D' g', ExecA Terminal blank endSym mark (rewindSignedGroup k) ts B ∧
      EncS blank startSym endSym mark x (a + (n - min k n)) (b + (n - min k n))
        ⟨D', n - min k n, E + 1, P, F, S, R⟩ g' (applyActs blank B ts) ∧
      SgnA M (N + (n - min k n)) g' ∧
      SgnB M' (N' + (n - min k n)) ⟨D', n - min k n, E + 1, P, F, S, R⟩ g' ∧
      B.length ≤ min k n * 10 + 3 := by
  let t := applyAct blank ts (Act.Ce blank .right)
  have he1 : EncS blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E + 1, P, F, S, R⟩ g t :=
    ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, Tape.counter'_inc he.base.ce,
      he.base.cp, he.base.cf, he.base.cs, he.base.cr⟩, he.ca, he.cb, he.cc⟩
  let B := qBlockL blank mark (rewindSignedRestL blank mark) k n t
  have hex := qBlock_exec (Terminal := Terminal) (endSym := endSym)
    rewindSignedRest (rewindSignedRestL blank mark) hmark
    rewindSignedRest_exec rewindSignedRest_cq k n t he1.base.cq
  have heff := qBlock_effect (rewindSignedRestL blank mark) hmark rewindSignedRest_cq
    k n t he1.base.cq
  have hn : n - min k n + min k n = n := by omega
  obtain ⟨D', g', he2, ha2, hb2⟩ := rewindSignedPow_enc hmark (min k n)
    (a + (n - min k n)) (b + (n - min k n)) D (n - min k n) (E + 1) P F S R
    M (N + (n - min k n)) M' (N' + (n - min k n)) g t
    (by simpa only [Nat.add_assoc, hn] using he1)
    (by simpa only [Nat.add_assoc, hn] using ha)
    (by simpa only [Nat.add_assoc, hn, SgnB] using hb)
  refine ⟨[Act.Ce blank .right] ++ B, D', g',
    execA_seq (execA_ct_put ctCe .right ts) hex, ?_, ha2, hb2, ?_⟩
  · change EncS blank startSym endSym mark x _ _ _ _ (applyActs blank B t)
    rw [heff]
    exact he2
  · have hl := qBlock_length (blank := blank) (mark := mark) (rewindSignedRestL blank mark) 8
      rewindSignedRest_length k n t
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [B]
    omega

/-- A fixed finite program rewinds both pattern heads, updates the signed
differences, and counts the groups in `Ce`, in linear tape work. -/
theorem REWIND_SIGNED_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D E P F S R M N M' N' : ℕ) (hk : 0 < k)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E, P, F, S, R⟩ g ts)
    (ha : SgnA M (N + n) g) (hb : SgnB M' (N' + n) ⟨D, n, E, P, F, S, R⟩ g) :
    ∃ L D' g', ExecA Terminal blank endSym mark (REWIND_SIGNED k) ts L ∧
      EncS blank startSym endSym mark x a b ⟨D', 0, E + stays k n 0, P, F, S, R⟩ g'
        (applyActs blank L ts) ∧
      SgnA M N g' ∧ SgnB M' N' ⟨D', 0, E + stays k n 0, P, F, S, R⟩ g' ∧
      L.length ≤ 15 * n + 2 := by
  let Inv : ℕ → Tapes sc → Prop := fun m t => ∃ d e g',
    EncS blank startSym endSym mark x (a + m) (b + m) ⟨d, m, e, P, F, S, R⟩ g' t ∧
    SgnA M (N + m) g' ∧ SgnB M' (N' + m) ⟨d, m, e, P, F, S, R⟩ g' ∧
    e + stays k m 0 = E + stays k n 0
  have hq : ∀ m t, Inv m t → Tape.CounterView' blank mark t.Cq m := by
    rintro m t ⟨d, e, g', he', _⟩
    exact he'.base.cq
  have hbody : ∀ m t, Inv m t → 0 < m →
      ∃ B, ExecA Terminal blank endSym mark (rewindSignedGroup k) t B ∧
        Inv (m - min k m) (applyActs blank B t) ∧ B.length ≤ min k m * 10 + 3 := by
    rintro m t ⟨d, e, g', he', ha', hb', hsum⟩ hm
    obtain ⟨B, d', g'', hx, he'', ha'', hb'', hc⟩ :=
      rewindSignedGroup_spec hmark k m a b d e P F S R M N M' N' g' t he' ha' hb'
    refine ⟨B, hx, ⟨d', e + 1, g'', he'', ha'', hb'', ?_⟩, hc⟩
    have hs := stays_block k m hk hm
    omega
  obtain ⟨L, hx, hf, hc⟩ := QGROUP_spec (rewindSignedGroup k) Inv k 10 hk hmark hq hbody
    n ts ⟨D, E, g, he, ha, hb, rfl⟩
  obtain ⟨d, e, g', he', ha', hb', hsum⟩ := hf
  have hes : e = E + stays k n 0 := by simpa only [stays, Nat.add_zero] using hsum
  subst e
  refine ⟨L, d, g', hx, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using he'
  · simpa only [Nat.add_zero] using ha'
  · simpa only [Nat.add_zero] using hb'
  · have hs := stays_le k n 0
    omega

/-- info: 'PalPeg.GSPreProg.REWIND_SIGNED_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms REWIND_SIGNED_spec

end PalPeg.GSPreProg
