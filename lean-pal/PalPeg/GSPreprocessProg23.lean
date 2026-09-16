import PalPeg.GSPreprocessProg22

/-! # Linear rewind with a maintained reach difference -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def rewindRGroup (k : ℕ) : Prog A9 Cond9 :=
  .seq (.act (tCe, .blk, .right)) (QBLOCK rewindRRest k)

def REWIND_R (k : ℕ) : Prog A9 Cond9 := QGROUP (rewindRGroup k)

theorem rewindRGroup_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D E P F S R M N M' N' : ℕ)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E, P, F, S, R⟩ g ts)
    (ha : SgnA M (N + n) g) (hb : SgnB M' (N' + n) ⟨D, n, E, P, F, S, R⟩ g) :
    ∃ B D' g', ExecA Terminal blank endSym mark (rewindRGroup k) ts B ∧
      EncR blank startSym endSym mark x (a + (n - min k n)) (b + (n - min k n))
        ⟨D', n - min k n, E + 1, P, F, S, R⟩ g' (applyActs blank B ts) ∧
      SgnA M (N + (n - min k n)) g' ∧
      SgnB M' (N' + (n - min k n)) ⟨D', n - min k n, E + 1, P, F, S, R⟩ g' ∧
      B.length ≤ min k n * 14 + 3 := by
  let t := applyAct blank ts (Act.Ce blank .right)
  have he1 : EncR blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E + 1, P, F, S, R⟩ g t :=
    ⟨⟨⟨he.enc.base.v1, he.enc.base.v2, he.enc.base.cd, he.enc.base.cq,
      Tape.counter'_inc he.enc.base.ce, he.enc.base.cp, he.enc.base.cf,
      he.enc.base.cs, he.enc.base.cr⟩, he.enc.ca, he.enc.cb, he.enc.cc⟩, he.diff⟩
  let B := qBlockL blank mark (rewindRRestL blank mark) k n t
  have hex := qBlock_exec (Terminal := Terminal) (endSym := endSym)
    rewindRRest (rewindRRestL blank mark) hmark
    rewindRRest_exec rewindRRest_cq k n t he1.enc.base.cq
  have heff := qBlock_effect (rewindRRestL blank mark) hmark rewindRRest_cq
    k n t he1.enc.base.cq
  have hn : n - min k n + min k n = n := by omega
  obtain ⟨D', g', he2, ha2, hb2⟩ := rewindRPow_enc hmark (min k n)
    (a + (n - min k n)) (b + (n - min k n)) D (n - min k n) (E + 1) P F S R
    M (N + (n - min k n)) M' (N' + (n - min k n)) g t
    (by simpa only [Nat.add_assoc, hn] using he1)
    (by simpa only [Nat.add_assoc, hn] using ha)
    (by simpa only [Nat.add_assoc, hn, SgnB] using hb)
  refine ⟨[Act.Ce blank .right] ++ B, D', g',
    execA_seq (execA_ct_put ctCe .right ts) hex, ?_, ha2, hb2, ?_⟩
  · change EncR blank startSym endSym mark x _ _ _ _ (applyActs blank B t)
    rw [heff]
    exact he2
  · have hl := qBlock_length (blank := blank) (mark := mark) (rewindRRestL blank mark) 12
      rewindRRest_length k n t
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [B]
    omega

/-- The reach tape is restored to the ordinary encoding when the rewind ends. -/
theorem REWIND_R_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D E P F S R M N M' N' : ℕ) (hk : 0 < k)
    (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E, P, F, S, R⟩ g ts)
    (ha : SgnA M (N + n) g) (hb : SgnB M' (N' + n) ⟨D, n, E, P, F, S, R⟩ g) :
    ∃ L D' g', ExecA Terminal blank endSym mark (REWIND_R k) ts L ∧
      EncS blank startSym endSym mark x a b ⟨D', 0, E + stays k n 0, P, F, S, R⟩ g'
        (applyActs blank L ts) ∧
      SgnA M N g' ∧ SgnB M' N' ⟨D', 0, E + stays k n 0, P, F, S, R⟩ g' ∧
      L.length ≤ 19 * n + 2 := by
  let Inv : ℕ → Tapes sc → Prop := fun m t => ∃ d e g',
    EncR blank startSym endSym mark x (a + m) (b + m) ⟨d, m, e, P, F, S, R⟩ g' t ∧
    SgnA M (N + m) g' ∧ SgnB M' (N' + m) ⟨d, m, e, P, F, S, R⟩ g' ∧
    e + stays k m 0 = E + stays k n 0
  have hq : ∀ m t, Inv m t → Tape.CounterView' blank mark t.Cq m := by
    rintro m t ⟨d, e, g', he', _⟩
    exact he'.enc.base.cq
  have hbody : ∀ m t, Inv m t → 0 < m →
      ∃ B, ExecA Terminal blank endSym mark (rewindRGroup k) t B ∧
        Inv (m - min k m) (applyActs blank B t) ∧ B.length ≤ min k m * 14 + 3 := by
    rintro m t ⟨d, e, g', he', ha', hb', hsum⟩ hm
    obtain ⟨B, d', g'', hx, he'', ha'', hb'', hc⟩ :=
      rewindRGroup_spec hmark k m a b d e P F S R M N M' N' g' t he' ha' hb'
    refine ⟨B, hx, ⟨d', e + 1, g'', he'', ha'', hb'', ?_⟩, hc⟩
    have hs := stays_block k m hk hm
    omega
  obtain ⟨L, hx, hf, hc⟩ := QGROUP_spec (rewindRGroup k) Inv k 14 hk hmark hq hbody
    n ts ⟨D, E, g, he, ha, hb, rfl⟩
  obtain ⟨d, e, g', he', ha', hb', hsum⟩ := hf
  have hes : e = E + stays k n 0 := by simpa only [stays, Nat.add_zero] using hsum
  subst e
  refine ⟨L, d, g', hx, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using EncR_to_EncS he' rfl
  · simpa only [Nat.add_zero] using ha'
  · simpa only [Nat.add_zero] using hb'
  · have hs := stays_le k n 0
    omega

/-- info: 'PalPeg.GSPreProg.REWIND_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms REWIND_R_spec

end PalPeg.GSPreProg
