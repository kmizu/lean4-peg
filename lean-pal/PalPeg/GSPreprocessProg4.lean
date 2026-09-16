import PalPeg.GSPreprocessProg3

/-! # Signed-counter finite control

The decrement program reads the positive counter by moving its head left.
It implements the existing action list exactly, without inspecting list lengths.
-/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

/-- Decrement the difference of two unary counters. -/
def SIGNED_DEC (pos neg : Fin 12) : Prog A9 Cond9 :=
  .seq (.act (pos, .blk, .left))
    (.ite (.notMark pos) (.act (pos, .blk, .stay))
      (.seq (.act (pos, .mrk, .right)) (.act (neg, .blk, .right))))

theorem signed_dec_exec (p n : CT sc) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (SIGNED_DEC p.idx n.idx) ts
      (if probe blank (p.get ts) = mark then
        [p.act blank .left, p.act mark .right, n.act blank .right]
       else [p.act blank .left, p.act blank .stay]) := by
  have hprobe :
      (getT (applyActs blank [p.act blank .left] ts) p.idx).focus =
        probe blank (p.get ts) := by
    simp only [applyActs, List.foldl_cons, List.foldl_nil, p.get_eq, p.step_eq]
    rfl
  unfold SIGNED_DEC
  by_cases h : probe blank (p.get ts) = mark
  · rw [if_pos h]
    apply execA_seq (execA_ct_put p .left ts)
    apply execA_ite_neg
    · simp only [condOf9, hprobe, h, ne_eq, not_true_eq_false, decide_false]
    · exact execA_seq (execA_ct_mark p .right _) (execA_ct_put n .right _)
  · rw [if_neg h]
    apply execA_seq (execA_ct_put p .left ts)
    apply execA_ite_pos
    · simp only [condOf9, hprobe, ne_eq, h, not_false_eq_true, decide_true]
    · exact execA_ct_put p .stay _

def sDecAProg : Prog A9 Cond9 := SIGNED_DEC tCa tCb
def sDecBProg : Prog A9 Cond9 := SIGNED_DEC tCd tCc

theorem sDecAProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sDecAProg ts (sDecA blank mark ts) :=
  signed_dec_exec ctCa ctCb ts

theorem sDecBProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sDecBProg ts (sDecB blank mark ts) :=
  signed_dec_exec ctCd ctCc ts

/-- The continuing scan body has nine or fewer tape actions. -/
def sBodyProg : Prog A9 Cond9 :=
  .seq (.seq (.act (tV1, .keep, .right))
    (.seq (.act (tV2, .keep, .right)) (.act (tCq, .blk, .right))))
    (.seq sDecAProg sDecBProg)

theorem sBodyProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sBodyProg ts
      (sBase blank ++ (sDecA blank mark ts ++ sDecB blank mark ts)) := by
  have hbase : ExecA Terminal blank endSym mark
      (.seq (.act (tV1, .keep, .right))
        (.seq (.act (tV2, .keep, .right)) (.act (tCq, .blk, .right))))
      ts (sBase blank) :=
    execA_seq (execA_v1 .right ts)
      (execA_seq (execA_v2 .right _) (execA_ct_put ctCq .right _))
  have ha : sDecA blank mark ts = sDecA blank mark (applyActs blank (sBase blank) ts) :=
    sDecA_congr blank mark (by rw [applyActs_sBase])
  have hb : sDecB blank mark ts = sDecB blank mark
      (applyActs blank (sDecA blank mark (applyActs blank (sBase blank) ts))
        (applyActs blank (sBase blank) ts)) :=
    sDecB_congr blank mark (by rw [sDecA_Cd, applyActs_sBase])
  rw [ha, hb]
  exact execA_seq hbase (execA_seq (sDecAProg_exec _) (sDecBProg_exec _))

theorem sBodyProg_exec_of_sCond (ts : Tapes sc) (orc : Tapes sc → Bool)
    (h : sCond endSym orc ts) :
    ExecA Terminal blank endSym mark sBodyProg ts (sActs blank endSym mark orc ts) := by
  rw [sActs, if_pos h]
  exact sBodyProg_exec ts

def sProbe (blank : Fin sc) : List (Act sc) :=
  [Act.Ca blank .left, Act.Cd blank .left]

def sProbeProg : Prog A9 Cond9 :=
  .seq (.act (tCa, .blk, .left)) (.act (tCd, .blk, .left))

theorem sProbeProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sProbeProg ts (sProbe blank) :=
  execA_seq (execA_ct_put ctCa .left ts) (execA_ct_put ctCd .left _)

theorem sReady_iff (ts : Tapes sc) :
    condOf9 endSym mark .sReady
        (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) = true ↔
      sCond endSym (orcAB blank mark) ts := by
  simp [condOf9, getT, tV1, tV2, tCa, tCd, sProbe, applyActs, applyAct,
    sCond, orcAB, probe, Tape.read]
  tauto

theorem execA_ct_keep (c : CT sc) (m : Move) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (.act (c.idx, .keep, m)) ts
      [c.act (c.get ts).focus m] := by
  have h := execA_act_gen (Terminal := Terminal) (blank := blank)
    (endSym := endSym) (mark := mark) (c.act (c.get ts).focus m) W9.keep ts
    (by rw [c.tape_eq, c.get_eq, c.write_eq])
  rw [c.tape_eq, c.move_eq] at h
  exact h

def sRestore (ts : Tapes sc) : List (Act sc) :=
  [Act.Cd ts.Cd.focus .right, Act.Ca ts.Ca.focus .right]

def sRestoreProg : Prog A9 Cond9 :=
  .seq (.act (tCd, .keep, .right)) (.act (tCa, .keep, .right))

theorem sRestoreProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sRestoreProg ts (sRestore ts) :=
  execA_seq (execA_ct_keep ctCd .right ts) (execA_ct_keep ctCa .right _)

theorem counter_probe_restore {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) :
    Tape.step blank (Tape.step blank tp blank .left) (probe blank tp) .right = tp := by
  obtain ⟨l, f, r⟩ := tp
  have hf := h.focus_blank
  have hl := h.left_eq
  cases l with
  | nil => simp at hl
  | cons a l =>
    simp only at hf
    subst f
    rfl

theorem sProbe_restore (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    applyActs blank (sRestore (applyActs blank (sProbe blank) ts))
      (applyActs blank (sProbe blank) ts) = ts := by
  have ea := counter_probe_restore ha
  have ed := counter_probe_restore hd
  change { ts with
    Ca := Tape.step blank (Tape.step blank ts.Ca blank .left) (probe blank ts.Ca) .right
    Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) (probe blank ts.Cd) .right } = ts
  rw [ea, ed]

def sBodyL (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  sBase blank ++ (sDecA blank mark ts ++ sDecB blank mark ts)

def sRunBody : Prog A9 Cond9 :=
  .seq (.act (tCa, .keep, .right)) (.seq sBodyProg sProbeProg)

def sRunProg : Prog A9 Cond9 := .loop .sReady (tCd, .keep, .right) sRunBody

def SCAN : Prog A9 Cond9 := .seq sProbeProg (.seq sRunProg sRestoreProg)

def sIter (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  sRestore (applyActs blank (sProbe blank) ts) ++ sBodyL blank mark ts ++ sProbe blank

theorem sIter_effect (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    applyActs blank (sIter blank mark ts) (applyActs blank (sProbe blank) ts) =
      applyActs blank (sProbe blank) (applyActs blank (sBodyL blank mark ts) ts) := by
  simp only [sIter, applyActs_append, sProbe_restore ts ha hd]

theorem sRun_cont (ts : Tapes sc) {a d : ℕ} {L : List (Act sc)}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d)
    (hc : sCond endSym (orcAB blank mark) ts)
    (hnext : ExecA Terminal blank endSym mark sRunProg
      (applyActs blank (sProbe blank) (applyActs blank (sBodyL blank mark ts) ts)) L) :
    ExecA Terminal blank endSym mark sRunProg (applyActs blank (sProbe blank) ts)
      (sIter blank mark ts ++ L) := by
  let tp := applyActs blank (sProbe blank) ts
  have hr : applyActs blank [Act.Ca tp.Ca.focus .right]
      (applyAct blank tp (Act.Cd tp.Cd.focus .right)) = ts :=
    sProbe_restore ts ha hd
  have hbody : ExecA Terminal blank endSym mark sRunBody
      (applyAct blank tp (Act.Cd tp.Cd.focus .right))
      ([Act.Ca tp.Ca.focus .right] ++ (sBodyL blank mark ts ++ sProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCa .right _)
    change ExecA Terminal blank endSym mark (.seq sBodyProg sProbeProg)
      (applyActs blank [Act.Ca tp.Ca.focus .right]
        (applyAct blank tp (Act.Cd tp.Cd.focus .right))) _
    rw [hr]
    exact execA_seq (sBodyProg_exec ts) (sProbeProg_exec _)
  have hnext' : ExecA Terminal blank endSym mark sRunProg
      (applyActs blank ([Act.Ca tp.Ca.focus .right] ++ (sBodyL blank mark ts ++ sProbe blank))
        (applyAct blank tp (Act.Cd tp.Cd.focus .right))) L := by
    simpa only [applyActs_append, hr] using hnext
  exact execA_loop_cont rfl rfl rfl ((sReady_iff ts).2 hc) hbody hnext'

theorem sRun_stop (ts : Tapes sc) (h : ¬ sCond endSym (orcAB blank mark) ts) :
    ExecA Terminal blank endSym mark sRunProg (applyActs blank (sProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.2 (fun hh => h ((sReady_iff ts).1 hh))

def sInnerTrace (blank endSym mark : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
    if sCond endSym (orcAB blank mark) ts then
      sIter blank mark ts ++
        sInnerTrace blank endSym mark fuel (applyActs blank (sBodyL blank mark ts) ts)
    else []

theorem sRun_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel a b : ℕ) (c : Ctr) (g : Ctr3) (ts : Tapes sc),
      EncS blank startSym endSym mark x a b c g ts → a ≤ b → x.length ≤ b + fuel →
      ExecA Terminal blank endSym mark sRunProg (applyActs blank (sProbe blank) ts)
          (sInnerTrace blank endSym mark fuel ts) ∧
      applyActs blank (sInnerTrace blank endSym mark fuel ts) (applyActs blank (sProbe blank) ts) =
        applyActs blank (sProbe blank)
          (applyActs blank (sProg blank endSym mark (orcAB blank mark) fuel ts) ts) ∧
      (sInnerTrace blank endSym mark fuel ts).length ≤
        3 * (sProg blank endSym mark (orcAB blank mark) fuel ts).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b c g ts hE hab hbound
    have hstop : ¬ sCond endSym (orcAB blank mark) ts := by
      intro h
      have hb := ((sCond_iff hend hE.base hab).1 h).1
      omega
    exact ⟨sRun_stop ts hstop, rfl, by simp [sInnerTrace, sProg]⟩
  | succ fuel ih =>
    intro a b c g ts hE hab hbound
    by_cases h : sCond endSym (orcAB blank mark) ts
    · let next := applyActs blank (sBodyL blank mark ts) ts
      have hstep := encS_s_step hend hmark hE hab h
      rw [sActs, if_pos h] at hstep
      obtain ⟨he, hf, hl⟩ := ih (a + 1) (b + 1) _ _ next hstep (by omega) (by omega)
      have hp : sProg blank endSym mark (orcAB blank mark) (fuel + 1) ts =
          sBodyL blank mark ts ++ sProg blank endSym mark (orcAB blank mark) fuel next := by
        rw [sProg, if_pos h, sActs, if_pos h]
        rfl
      rw [sInnerTrace, if_pos h]
      refine ⟨sRun_cont ts hE.ca hE.base.cd h he, ?_, ?_⟩
      · rw [applyActs_append, sIter_effect ts hE.ca hE.base.cd, hf, hp, applyActs_append]
      · have hm : 3 ≤ (sBodyL blank mark ts).length := by
          simp [sBodyL, List.length_append, sBase_length]
        have hi : (sIter blank mark ts).length = (sBodyL blank mark ts).length + 4 := by
          simp [sIter, sRestore, sProbe, List.length_append]
        rw [List.length_append, hi, hp, List.length_append]
        dsimp only [next] at hl ⊢
        omega
    · simp only [sInnerTrace, if_neg h, sProg, applyActs, List.foldl_nil, List.length_nil,
        Nat.mul_zero, le_refl, and_true]
      exact sRun_stop ts h

/-- A single, input-independent finite program implements the whole inner scan.
The extra probe/restore actions are included in the work bound. -/
theorem SCAN_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s fuel q D E p F S : ℕ) (g : Ctr3) (ts : Tapes sc)
    (hE : EncS blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g)
    (hbound : x.length ≤ s + p + q + fuel) :
    ∃ L : List (Act sc), ExecA Terminal blank endSym mark SCAN ts L ∧
      applyActs blank L ts = applyActs blank (sProg blank endSym mark (orcAB blank mark) fuel ts) ts ∧
      L.length ≤ 27 * sWork x k p r s fuel q + 4 := by
  obtain ⟨he, hf, hl⟩ := sRun_spec (Terminal := Terminal) hend hmark
    fuel (s + q) (s + p + q) _ _ ts hE (by omega) hbound
  obtain ⟨⟨D', g', hE', _⟩, hcost⟩ := sProg_spec hend hmark
    (fun _ _ _ _ _ _ _ _ hEE hOK => orcAB_spec hmark hEE hOK)
    fuel q D E p F S g ts hE hok
  let fin := applyActs blank (sProg blank endSym mark (orcAB blank mark) fuel ts) ts
  let tail := sRestore (applyActs blank (sProbe blank) fin)
  refine ⟨sProbe blank ++ (sInnerTrace blank endSym mark fuel ts ++ tail), ?_, ?_, ?_⟩
  · apply execA_seq (sProbeProg_exec ts)
    apply execA_seq he
    rw [hf]
    exact sRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hf]
    exact sProbe_restore fin hE'.ca hE'.base.cd
  · have ht : tail.length = 2 := rfl
    have hp : (sProbe blank).length = 2 := rfl
    change (sProg blank endSym mark (orcAB blank mark) fuel ts).length ≤
      9 * sWork x k p r s fuel q at hcost
    simp only [List.length_append, ht, hp]
    omega

/-- info: 'PalPeg.GSPreProg.SCAN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SCAN_spec
#print axioms signed_dec_exec
#print axioms sBodyProg_exec

/-- Incrementing a signed counter uses the same finite control with swapped poles.
The zero branch includes a probe/restore pair absent from the specification trace. -/
def sIncBProg : Prog A9 Cond9 := SIGNED_DEC tCc tCd

def sIncBTrace (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Cc = mark then
    [Act.Cc blank .left, Act.Cc mark .right, Act.Cd blank .right]
  else [Act.Cc blank .left, Act.Cc blank .stay]

theorem sIncBProg_exec (ts : Tapes sc) :
    ExecA Terminal blank endSym mark sIncBProg ts (sIncBTrace blank mark ts) :=
  signed_dec_exec ctCc ctCd ts

theorem sIncBTrace_effect (ts : Tapes sc) {n : ℕ}
    (hn : Tape.CounterView' blank mark ts.Cc n) :
    applyActs blank (sIncBTrace blank mark ts) ts =
      applyActs blank (sIncB blank mark ts) ts := by
  unfold sIncBTrace sIncB
  by_cases h : probe blank ts.Cc = mark
  · rw [if_pos h, if_pos h]
    have he := counter_probe_restore hn
    rw [h] at he
    change { ts with
      Cc := Tape.step blank (Tape.step blank ts.Cc blank .left) mark .right
      Cd := Tape.step blank ts.Cd blank .right } =
      { ts with Cd := Tape.step blank ts.Cd blank .right }
    rw [he]
  · rw [if_neg h, if_neg h]

theorem sIncBTrace_length (ts : Tapes sc) :
    (sIncBTrace blank mark ts).length ≤ 3 := by
  unfold sIncBTrace
  split <;> simp

/-- Statically repeat an instruction. The parameter is a grammar constant,
not an input length or a run-time counter value. -/
def repeatProg (p : Prog A9 Cond9) : ℕ → Prog A9 Cond9
  | 0 => .skip
  | n + 1 => .seq p (repeatProg p n)

def sIncBRepeated (blank mark : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts => sIncBTrace blank mark ts ++
      sIncBRepeated blank mark n (applyActs blank (sIncBTrace blank mark ts) ts)

theorem sIncBRepeated_exec (n : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (repeatProg sIncBProg n) ts
      (sIncBRepeated blank mark n ts) := by
  induction n generalizing ts with
  | zero => exact execA_skip
  | succ n ih => exact execA_seq (sIncBProg_exec ts) (ih _)

theorem sIncBRepeated_length (n : ℕ) (ts : Tapes sc) :
    (sIncBRepeated blank mark n ts).length ≤ 3 * n := by
  induction n generalizing ts with
  | zero => simp [sIncBRepeated]
  | succ n ih =>
    have h := sIncBTrace_length (blank := blank) (mark := mark) ts
    have hi := ih (applyActs blank (sIncBTrace blank mark ts) ts)
    simp only [sIncBRepeated, List.length_append]
    omega

theorem sIncBRepeated_effect {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (n : ℕ) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    applyActs blank (sIncBRepeated blank mark n ts) ts =
      applyActs blank (sIncBLoop blank mark n ts) ts := by
  induction n generalizing c g ts with
  | zero => rfl
  | succ n ih =>
    have he := sIncBTrace_effect ts hE.cc
    simp only [sIncBRepeated, sIncBLoop, applyActs_append, he]
    exact ih (sIncB_enc hmark hE)

/-- The period counter `Cf`, not an external length, drives the shift. -/
def perSignedBase (blank : Fin sc) : List (Act sc) :=
  [Act.V1 .left, Act.Cq blank .left, Act.Cq blank .stay,
    Act.Cp blank .right, Act.Ce blank .right]

def perSignedRest (k : ℕ) : Prog A9 Cond9 :=
  .seq (.seq (.act (tV1, .keep, .left))
    (.seq (.act (tCq, .blk, .left))
      (.seq (.act (tCq, .blk, .stay))
        (.seq (.act (tCp, .blk, .right)) (.act (tCe, .blk, .right))))))
    (repeatProg sIncBProg k)

def perSignedRestL (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  perSignedBase blank ++
    sIncBRepeated blank mark k (applyActs blank (perSignedBase blank) ts)

theorem perSignedRest_exec (k : ℕ) (ts : Tapes sc) :
    ExecA Terminal blank endSym mark (perSignedRest k) ts
      (perSignedRestL blank mark k ts) := by
  apply execA_seq
    (execA_seq (execA_v1 .left ts)
      (execA_seq (execA_ct_put ctCq .left _)
        (execA_seq (execA_ct_put ctCq .stay _)
          (execA_seq (execA_ct_put ctCp .right _) (execA_ct_put ctCe .right _)))))
  exact sIncBRepeated_exec k _

theorem sIncBRepeated_cf (n : ℕ) (ts : Tapes sc) :
    (applyActs blank (sIncBRepeated blank mark n ts) ts).Cf = ts.Cf := by
  induction n generalizing ts with
  | zero => rfl
  | succ n ih =>
    simp only [sIncBRepeated, applyActs_append, ih]
    unfold sIncBTrace
    split <;> rfl

theorem perSignedRest_cf (k : ℕ) (ts : Tapes sc) :
    (ctCf : CT sc).get (applyActs blank (perSignedRestL blank mark k ts) ts) =
      (ctCf : CT sc).get ts := by
  change (applyActs blank (perSignedRestL blank mark k ts) ts).Cf = ts.Cf
  rw [perSignedRestL, applyActs_append, sIncBRepeated_cf]
  rfl

def PERIOD_SIGNED (k : ℕ) : Prog A9 Cond9 :=
  .seq (DLOOP tCf (perSignedRest k)) cfProg

theorem perSignedLoop_exec (hmark : mark ≠ blank) (k n : ℕ) (ts : Tapes sc)
    (hf : Tape.CounterView' blank mark ts.Cf n) :
    ExecA Terminal blank endSym mark (DLOOP tCf (perSignedRest k)) ts
      (dPowS ctCf blank (perSignedRestL blank mark k) n ts ++ dTest ctCf blank mark) :=
  dLoopS_exec ctCf (perSignedRest k) (perSignedRestL blank mark k) hmark
    (perSignedRest_exec k) (perSignedRest_cf k) n ts hf

theorem perSignedLoop_length (k n : ℕ) (ts : Tapes sc) :
    (dPowS ctCf blank (perSignedRestL blank mark k) n ts ++ dTest ctCf blank mark).length
      ≤ n * (3 * k + 7) + 2 := by
  have hl : ∀ t : Tapes sc, (perSignedRestL blank mark k t).length ≤ 3 * k + 5 := by
    intro t
    have h := sIncBRepeated_length (blank := blank) (mark := mark) k
      (applyActs blank (perSignedBase blank) t)
    simpa only [perSignedRestL, List.length_append, perSignedBase, List.length_cons,
      List.length_nil] using (by omega : 5 +
        (sIncBRepeated blank mark k (applyActs blank (perSignedBase blank) t)).length ≤ 3 * k + 5)
  have h := dPowS_length_le ctCf blank (perSignedRestL blank mark k) (3 * k + 5) hl n ts
  simpa [List.length_append, dTest, Nat.add_assoc] using Nat.add_le_add_right h 2

theorem perSignedPow_enc {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n : ℕ) :
    ∀ (a b D Q E P F S R M N : ℕ) (g : Ctr3) (ts : Tapes sc),
    EncS blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ g ts →
    SgnB M N ⟨D, Q + n, E, P, F + n, S, R⟩ g →
    ∃ D' bn',
      EncS blank startSym endSym mark x a b ⟨D', Q, E + n, P + n, F, S, R⟩
        ⟨g.ap, g.an, bn'⟩
        (applyActs blank (dPowS ctCf blank (perSignedRestL blank mark k) n ts) ts) ∧
      SgnB (M + k * n) N ⟨D', Q, E + n, P + n, F, S, R⟩ ⟨g.ap, g.an, bn'⟩ := by
  induction n with
  | zero =>
    intro a b D Q E P F S R M N g ts hE hB
    exact ⟨D, g.bn, by simpa [dPowS] using hE, by simpa using hB⟩
  | succ n ih =>
    intro a b D Q E P F S R M N g ts hE hB
    have hp : EncS blank startSym endSym mark x (a + n) b
        ⟨D, Q + n, E + 1, P + 1, F + n, S, R⟩ g
        (applyActs blank (perUnit blank) ts) := by
      have hb := perLoop1_enc (blank := blank) (startSym := startSym)
        (endSym := endSym) (mark := mark) (x := x)
        1 (a + n) b D (Q + n) E P (F + n) S R ts
        (by simpa [Nat.add_assoc] using hE.base)
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [perLoop1, applyActs_append] using hb
      · rw [applyActs_perUnit]; exact hE.ca
      · rw [applyActs_perUnit]; exact hE.cb
      · rw [applyActs_perUnit]; exact hE.cc
    obtain ⟨D1, bn1, he1, hb1⟩ := sIncBLoop_enc (blank := blank)
      (startSym := startSym) (endSym := endSym) (mark := mark) (x := x)
      hmark k M N (a + n) b ⟨D, Q + n, E + 1, P + 1, F + n, S, R⟩ g _ hp hB
    have heq : applyActs blank (perSignedRestL blank mark k (dStep ctCf blank ts))
        (dStep ctCf blank ts) =
        applyActs blank (sIncBLoop blank mark k (applyActs blank (perUnit blank) ts))
          (applyActs blank (perUnit blank) ts) := by
      have hbase : applyActs blank (perSignedBase blank) (dStep ctCf blank ts) =
          applyActs blank (perUnit blank) ts := rfl
      rw [perSignedRestL, applyActs_append, hbase]
      exact sIncBRepeated_effect hmark k hp
    obtain ⟨D2, bn2, he2, hb2⟩ := ih a b D1 Q (E + 1) (P + 1) F S R (M + k) N
      ⟨g.ap, g.an, bn1⟩ _ he1 hb1
    refine ⟨D2, bn2, ?_, ?_⟩
    · simp only [dPowS, applyActs, List.foldl_append, List.foldl_cons] at ⊢
      change EncS _ _ _ _ _ _ _ _ _
        (applyActs blank (dPowS ctCf blank (perSignedRestL blank mark k) n
          (applyActs blank (perSignedRestL blank mark k (dStep ctCf blank ts))
            (dStep ctCf blank ts)))
          (applyActs blank (perSignedRestL blank mark k (dStep ctCf blank ts))
            (dStep ctCf blank ts)))
      rw [heq]
      convert he2 using 1 <;> congr 1 <;> omega
    · convert hb2 using 1 <;> simp [SgnB, Nat.mul_succ] at * <;> omega

theorem dTest_cf_effect (hmark : mark ≠ blank) (ts : Tapes sc)
    (hf : Tape.CounterView' blank mark ts.Cf 0) :
    applyActs blank (dTest ctCf blank mark) ts = ts := by
  have hp := (probe_iff hmark hf).2 rfl
  have he := counter_probe_restore hf
  rw [hp] at he
  change { ts with Cf := Tape.step blank (Tape.step blank ts.Cf blank .left) mark .right } = ts
  rw [he]

theorem dTest_ce_effect (hmark : mark ≠ blank) (ts : Tapes sc)
    (he : Tape.CounterView' blank mark ts.Ce 0) :
    applyActs blank (dTest ctCe blank mark) ts = ts := by
  have hp := (probe_iff hmark he).2 rfl
  have ht := counter_probe_restore he
  rw [hp] at ht
  change { ts with Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) mark .right } = ts
  rw [ht]

/-- A finite, tape-driven signed period shift, including restoration and
the two terminating probes. No run-time length occurs in `PERIOD_SIGNED k`. -/
theorem PERIOD_SIGNED_spec {startSym : Fin sc} {x : List (Fin sc)}
    (hmark : mark ≠ blank) (k n a b D Q P S R M N : ℕ) (g : Ctr3) (ts : Tapes sc)
    (hE : EncS blank startSym endSym mark x (a + n) b ⟨D, Q + n, 0, P, n, S, R⟩ g ts)
    (hB : SgnB M N ⟨D, Q + n, 0, P, n, S, R⟩ g) :
    ∃ (L : List (Act sc)) (D' bn' : ℕ),
      ExecA Terminal blank endSym mark (PERIOD_SIGNED k) ts L ∧
      EncS blank startSym endSym mark x a b ⟨D', Q, 0, P + n, n, S, R⟩
        ⟨g.ap, g.an, bn'⟩ (applyActs blank L ts) ∧
      SgnB (M + k * n) N ⟨D', Q, 0, P + n, n, S, R⟩ ⟨g.ap, g.an, bn'⟩ ∧
      L.length ≤ n * (3 * k + 10) + 4 := by
  let L1 := dPowS ctCf blank (perSignedRestL blank mark k) n ts
  let t1 := applyActs blank L1 ts
  obtain ⟨D', bn', he1, hb1⟩ := perSignedPow_enc hmark k n a b D Q 0 P 0 S R M N g ts
    (by simpa using hE) hB
  have he1' : EncS blank startSym endSym mark x a b ⟨D', Q, n, P + n, 0, S, R⟩
      ⟨g.ap, g.an, bn'⟩ t1 := by simpa [t1, L1] using he1
  have ht1 : applyActs blank (L1 ++ dTest ctCf blank mark) ts = t1 := by
    rw [applyActs_append]
    exact dTest_cf_effect hmark t1 he1'.base.cf
  let t2 := applyActs blank (cfLoop blank n) t1
  have he2 : EncS blank startSym endSym mark x a b ⟨D', Q, 0, P + n, n, S, R⟩
      ⟨g.ap, g.an, bn'⟩ t2 := by
    have hb := cfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) n a b D' Q 0 (P + n) 0 S R t1 (by simpa using he1'.base)
    obtain ⟨ha, hb', hc⟩ := cfLoop_ctr3 blank n t1
    refine ⟨by simpa [t2] using hb, ?_, ?_, ?_⟩
    · change Tape.CounterView' _ _ (applyActs blank (cfLoop blank n) t1).Ca _
      rw [ha]; exact he1'.ca
    · change Tape.CounterView' _ _ (applyActs blank (cfLoop blank n) t1).Cb _
      rw [hb']; exact he1'.cb
    · change Tape.CounterView' _ _ (applyActs blank (cfLoop blank n) t1).Cc _
      rw [hc]; exact he1'.cc
  let L2 := cfLoop blank n ++ dTest ctCe blank mark
  have ht2 : applyActs blank L2 t1 = t2 := by
    dsimp only [L2]
    rw [applyActs_append]
    exact dTest_ce_effect hmark t2 he2.base.ce
  refine ⟨L1 ++ dTest ctCf blank mark ++ L2, D', bn', ?_, ?_, hb1, ?_⟩
  · apply execA_seq (perSignedLoop_exec hmark k n ts hE.base.cf)
    rw [ht1]
    exact cfProg_exec hmark n t1 he1'.base.ce
  · rw [applyActs_append, ht1, ht2]
    exact he2
  · have hlen := perSignedLoop_length (blank := blank) (mark := mark) k n ts
    have hrest : L2.length = 3 * n + 2 := by simp [L2]
    change (L1 ++ dTest ctCf blank mark).length ≤ n * (3 * k + 7) + 2 at hlen
    rw [List.length_append, hrest]
    calc
      _ ≤ (n * (3 * k + 7) + 2) + (3 * n + 2) := Nat.add_le_add_right hlen _
      _ = n * (3 * k + 10) + 4 := by ring

/-- info: 'PalPeg.GSPreProg.PERIOD_SIGNED_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PERIOD_SIGNED_spec

end PalPeg.GSPreProg
