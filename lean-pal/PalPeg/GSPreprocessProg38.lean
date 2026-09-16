import PalPeg.GSPreprocessProg37

/-! # Finite unsigned rewind for the first search -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def firstRewindRest : Prog A9 Cond9 :=
  .seq (.act (tV1, .keep, .left))
    (.seq (.act (tV2, .keep, .left)) (.act (tCd, .blk, .right)))

def firstRewindRestL (blank : Fin sc) (_ : Tapes sc) : List (Act sc) :=
  [.V1 .left, .V2 .left, .Cd blank .right]

theorem firstRewindRest_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark firstRewindRest ts (firstRewindRestL blank ts) :=
  execA_seq (execA_v1 .left ts) (execA_seq (execA_v2 .left _) (execA_ct_put ctCd .right _))

theorem firstRewindRest_cq (ts : Tapes sc) :
    (applyActs blank (firstRewindRestL blank ts) ts).Cq = ts.Cq := rfl

theorem firstRewindUnit_enc {a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x (a + 1) (b + 1)
      ⟨D, Q + 1, E, P, F, S, R⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D + 1, Q, E, P, F, S, R⟩ g
      (applyActs blank (firstRewindRestL blank (dStep ctCq blank ts)) (dStep ctCq blank ts)) := by
  change EncS blank startSym endSym mark x a b _ g (applyActs blank (rewindUnit blank) ts)
  exact he.frame (by simp [NoSigned, rewindUnit, Act.noSigned]) (rewind_unit_enc he.base)

theorem firstRewindPow_enc (n : ℕ) :
    ∀ (a b D Q E P F S R : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ g ts →
    EncS blank startSym endSym mark x a b ⟨D + n, Q, E, P, F, S, R⟩ g
      (applyActs blank (dPowS ctCq blank (firstRewindRestL blank) n ts) ts) := by
  induction n with
  | zero => intro a b D Q E P F S R g ts he; simpa [dPowS] using he
  | succ n ih =>
    intro a b D Q E P F S R g ts he
    have he1 := firstRewindUnit_enc (a := a + n) (b := b + n) (Q := Q + n)
      (by simpa only [Nat.add_assoc] using he)
    have hi := ih a b (D + 1) Q E P F S R g _ he1
    simpa only [dPowS, applyActs, List.foldl_append, List.foldl_cons, List.foldl_nil,
      dStep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hi

def firstRewindGroup (k : ℕ) : Prog A9 Cond9 :=
  .seq (.act (tCe, .blk, .right)) (QBLOCK firstRewindRest k)

def FIRST_REWIND (k : ℕ) : Prog A9 Cond9 := QGROUP (firstRewindGroup k)

theorem firstRewindGroup_spec (hmark : mark ≠ blank)
    (k n a b D E P F S R : ℕ) (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x (a + n) (b + n) ⟨D, n, E, P, F, S, R⟩ g ts) :
    ∃ B, ExecA Terminal blank endSym mark (firstRewindGroup k) ts B ∧
      EncS blank startSym endSym mark x (a + (n - min k n)) (b + (n - min k n))
        ⟨D + min k n, n - min k n, E + 1, P, F, S, R⟩ g (applyActs blank B ts) ∧
      B.length ≤ min k n * 5 + 3 := by
  let t := applyAct blank ts (.Ce blank .right)
  have he1 : EncS blank startSym endSym mark x (a + n) (b + n)
      ⟨D, n, E + 1, P, F, S, R⟩ g t :=
    ⟨⟨he.base.v1, he.base.v2, he.base.cd, he.base.cq, Tape.counter'_inc he.base.ce,
      he.base.cp, he.base.cf, he.base.cs, he.base.cr⟩, he.ca, he.cb, he.cc⟩
  let B := qBlockL blank mark (firstRewindRestL blank) k n t
  have hx := qBlock_exec (Terminal := Terminal) (endSym := endSym)
    firstRewindRest (firstRewindRestL blank) hmark firstRewindRest_exec firstRewindRest_cq
    k n t he1.base.cq
  have heff := qBlock_effect (firstRewindRestL blank) hmark firstRewindRest_cq k n t he1.base.cq
  have hn : n - min k n + min k n = n := by omega
  have he2 := firstRewindPow_enc (min k n) (a + (n - min k n)) (b + (n - min k n))
    D (n - min k n) (E + 1) P F S R g t (by simpa only [Nat.add_assoc, hn] using he1)
  refine ⟨[Act.Ce blank .right] ++ B, execA_seq (execA_ct_put ctCe .right ts) hx, ?_, ?_⟩
  · change EncS blank startSym endSym mark x _ _ _ _ (applyActs blank B t)
    rw [heff]; exact he2
  · have hl := qBlock_length (blank := blank) (mark := mark) (firstRewindRestL blank) 3
      (fun _ => by simp [firstRewindRestL]) k n t
    simp only [List.length_append, List.length_cons, List.length_nil]
    dsimp only [B]
    omega

theorem FIRST_REWIND_spec (hmark : mark ≠ blank)
    (k n a b D E P F S R : ℕ) (hk : 0 < k) (g : Ctr3) (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x (a + n) (b + n) ⟨D, n, E, P, F, S, R⟩ g ts) :
    ∃ L, ExecA Terminal blank endSym mark (FIRST_REWIND k) ts L ∧
      EncS blank startSym endSym mark x a b ⟨D + n, 0, E + stays k n 0, P, F, S, R⟩ g
        (applyActs blank L ts) ∧ L.length ≤ 10 * n + 2 := by
  let Inv : ℕ → Tapes sc → Prop := fun m t => ∃ d e,
    EncS blank startSym endSym mark x (a + m) (b + m) ⟨d, m, e, P, F, S, R⟩ g t ∧
    d + m = D + n ∧ e + stays k m 0 = E + stays k n 0
  have hq : ∀ m t, Inv m t → Tape.CounterView' blank mark t.Cq m := by
    rintro m t ⟨d, e, he', _⟩; exact he'.base.cq
  have hbody : ∀ m t, Inv m t → 0 < m →
      ∃ B, ExecA Terminal blank endSym mark (firstRewindGroup k) t B ∧
        Inv (m - min k m) (applyActs blank B t) ∧ B.length ≤ min k m * 5 + 3 := by
    rintro m t ⟨d, e, he', hd, heq⟩ hm
    obtain ⟨B, hx, he'', hc⟩ := firstRewindGroup_spec hmark k m a b d e P F S R g t he'
    refine ⟨B, hx, ⟨d + min k m, e + 1, he'', by omega, ?_⟩, hc⟩
    have := stays_block k m hk hm
    omega
  obtain ⟨L, hx, hf, hc⟩ := QGROUP_spec (firstRewindGroup k) Inv k 5 hk hmark hq hbody
    n ts ⟨D, E, he, rfl, rfl⟩
  obtain ⟨d, e, he', hd, heq⟩ := hf
  have hd' : d = D + n := by omega
  have heq' : e = E + stays k n 0 := by simpa only [stays, Nat.add_zero] using heq
  subst d; subst e
  refine ⟨L, hx, by simpa only [Nat.add_zero] using he', ?_⟩
  have := stays_le k n 0
  omega

end PalPeg.GSPreProg
