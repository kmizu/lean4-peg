import PalPeg.GSPreprocessProg19

/-! # A finite scan that also maintains `r-q` -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def sRunRProg : Prog A9 Cond9 :=
  .loop .sReady (tCd, .keep, .right)
    (.seq (.act (tCa, .keep, .right)) (.seq sBodyRProg sProbeProg))

def SCAN_R : Prog A9 Cond9 := .seq sProbeProg (.seq sRunRProg sRestoreProg)

def sIterR (blank mark : Fin sc) (R Q : ℕ) (ts : Tapes sc) : List (Act sc) :=
  sRestore (applyActs blank (sProbe blank) ts) ++ sBodyRL blank mark R Q ts ++ sProbe blank

theorem sIterR_effect (R Q : ℕ) (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d) :
    applyActs blank (sIterR blank mark R Q ts) (applyActs blank (sProbe blank) ts) =
      applyActs blank (sProbe blank) (applyActs blank (sBodyRL blank mark R Q ts) ts) := by
  simp only [sIterR, applyActs_append, sProbe_restore ts ha hd]

theorem sIterR_length (R Q : ℕ) (ts : Tapes sc) :
    (sIterR blank mark R Q ts).length ≤ 17 := by
  have hb := sBodyRL_length (blank := blank) (mark := mark) R Q ts
  simp only [sIterR, List.length_append, sRestore, sProbe, List.length_cons, List.length_nil]
  omega

theorem sRunR_stop (ts : Tapes sc) (h : ¬ sCond endSym (orcAB blank mark) ts) :
    ExecA Terminal blank endSym mark sRunRProg (applyActs blank (sProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((sReady_iff ts).mp hh))

theorem sRunR_cont (hmark : mark ≠ blank) (R Q : ℕ) (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a)
    (hd : Tape.CounterView' blank mark ts.Cd d)
    (hr : OneSgn blank mark R Q ts.Cr)
    (hc : sCond endSym (orcAB blank mark) ts) {L : List (Act sc)}
    (hn : ExecA Terminal blank endSym mark sRunRProg
      (applyActs blank (sProbe blank) (applyActs blank (sBodyRL blank mark R Q ts) ts)) L) :
    ExecA Terminal blank endSym mark sRunRProg (applyActs blank (sProbe blank) ts)
      (sIterR blank mark R Q ts ++ L) := by
  let tp := applyActs blank (sProbe blank) ts
  have hres : applyActs blank [Act.Ca tp.Ca.focus .right]
      (applyAct blank tp (Act.Cd tp.Cd.focus .right)) = ts := sProbe_restore ts ha hd
  have hb : ExecA Terminal blank endSym mark
      (.seq (.act (tCa, .keep, .right)) (.seq sBodyRProg sProbeProg))
      (applyAct blank tp (Act.Cd tp.Cd.focus .right))
      ([Act.Ca tp.Ca.focus .right] ++ (sBodyRL blank mark R Q ts ++ sProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCa .right _)
    change ExecA Terminal blank endSym mark (.seq sBodyRProg sProbeProg)
      (applyActs blank [Act.Ca tp.Ca.focus .right]
        (applyAct blank tp (Act.Cd tp.Cd.focus .right))) _
    rw [hres]
    exact execA_seq (sBodyR_exec hmark R Q ts hr) (sProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark sRunRProg
      (applyActs blank ([Act.Ca tp.Ca.focus .right] ++ (sBodyRL blank mark R Q ts ++ sProbe blank))
        (applyAct blank tp (Act.Cd tp.Cd.focus .right))) L := by
    simpa only [applyActs_append, hres] using hn
  have hh := execA_loop_cont rfl rfl rfl ((sReady_iff ts).mpr hc) hb hn'
  exact execA_of_eq (by simp only [sIterR, sRestore, List.append_assoc]; rfl) hh

theorem sCond_iffR (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {k r s p q D E F S : ℕ} {g : Ctr3} {ts : Tapes sc}
    (h : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g) :
    sCond endSym (orcAB blank mark) ts ↔
      s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
        ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
  rw [← sCond_shadowR r ts,
    sCond_iff hend h.enc.base (by omega), orcAB_spec hmark h.enc hok]
  simp only [decide_eq_false_iff_not, Nat.add_assoc]

theorem sRunR_spec (hend : endSym ∉ x) (hmark : mark ≠ blank) (k r s p : ℕ) :
    ∀ (fuel q D E F S : ℕ) (g : Ctr3) (ts : Tapes sc),
      EncR blank startSym endSym mark x (s + q) (s + p + q)
        ⟨D, q, E, p, F, S, r⟩ g ts →
      SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g →
      x.length ≤ s + p + q + fuel →
      ∃ (L : List (Act sc)) (u : Tapes sc) (D' : ℕ) (g' : Ctr3),
        ExecA Terminal blank endSym mark sRunRProg (applyActs blank (sProbe blank) ts) L ∧
        applyActs blank L (applyActs blank (sProbe blank) ts) = applyActs blank (sProbe blank) u ∧
        EncR blank startSym endSym mark x
          (s + q + sSteps x k p r s fuel q) (s + p + q + sSteps x k p r s fuel q)
          ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g' u ∧
        SignedOK k r p (q + sSteps x k p r s fuel q)
          ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g' ∧
        L.length ≤ 17 * sSteps x k p r s fuel q := by
  intro fuel
  induction fuel with
  | zero =>
    intro q D E F S g ts he hok hbound
    have hc : ¬ sCond endSym (orcAB blank mark) ts := by
      intro hh
      have := ((sCond_iffR hend hmark he hok).mp hh).1
      omega
    refine ⟨[], ts, D, g, sRunR_stop ts hc, rfl, ?_, ?_, by simp [sSteps]⟩
    · simpa only [sSteps, Nat.add_zero] using he
    · simpa only [sSteps, Nat.add_zero] using hok
  | succ fuel ih =>
    intro q D E F S g ts he hok hbound
    have hguard := sCond_iffR hend hmark he hok
    by_cases hc : sCond endSym (orcAB blank mark) ts
    · have hm := hguard.mp hc
      let u1 := applyActs blank (sBodyRL blank mark r q ts) ts
      let g1 : Ctr3 := ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0),
        g.bn + (if D = 0 then 1 else 0)⟩
      have he1 : EncR blank startSym endSym mark x (s + (q + 1)) (s + p + (q + 1))
          ⟨D - 1, q + 1, E, p, F, S, r⟩ g1 u1 := by
        simpa only [Nat.add_assoc] using encR_s_step hend hmark he (by omega) hc
      have hok1 : SignedOK k r p (q + 1) ⟨D - 1, q + 1, E, p, F, S, r⟩ g1 :=
        signedOK_step hok
      obtain ⟨L, u, D', g', hx, hu, he', hok', hlen⟩ :=
        ih (q + 1) (D - 1) E F S g1 u1 he1 hok1 (by omega)
      refine ⟨sIterR blank mark r q ts ++ L, u, D', g',
        sRunR_cont hmark r q ts he.enc.ca he.enc.base.cd he.diff hc hx, ?_, ?_, ?_, ?_⟩
      · rw [applyActs_append, sIterR_effect r q ts he.enc.ca he.enc.base.cd]
        exact hu
      · rw [sSteps, if_pos hm]
        simpa only [Nat.add_assoc] using he'
      · rw [sSteps, if_pos hm]
        simpa only [Nat.add_assoc] using hok'
      · have hi := sIterR_length (blank := blank) (mark := mark) r q ts
        rw [List.length_append, sSteps, if_pos hm]
        omega
    · have hm := mt hguard.mpr hc
      refine ⟨[], ts, D, g, sRunR_stop ts hc, rfl, ?_, ?_, ?_⟩
      · simpa only [sSteps, if_neg hm, Nat.add_zero] using he
      · simpa only [sSteps, if_neg hm, Nat.add_zero] using hok
      · simp only [sSteps, if_neg hm, List.length_nil, Nat.mul_zero, le_refl]

theorem SCAN_R_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k r s p fuel q D E F S : ℕ) (g : Ctr3) (ts : Tapes sc)
    (he : EncR blank startSym endSym mark x (s + q) (s + p + q)
      ⟨D, q, E, p, F, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g)
    (hbound : x.length ≤ s + p + q + fuel) :
    ∃ (L : List (Act sc)) (D' : ℕ) (g' : Ctr3),
      ExecA Terminal blank endSym mark SCAN_R ts L ∧
      EncR blank startSym endSym mark x
        (s + q + sSteps x k p r s fuel q) (s + p + q + sSteps x k p r s fuel q)
        ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g' (applyActs blank L ts) ∧
      SignedOK k r p (q + sSteps x k p r s fuel q)
        ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g' ∧
      L.length ≤ 17 * sSteps x k p r s fuel q + 4 := by
  obtain ⟨L, u, D', g', hx, hu, he', hok', hlen⟩ :=
    sRunR_spec hend hmark k r s p fuel q D E F S g ts he hok hbound
  let T := sProbe blank ++ (L ++ sRestore (applyActs blank (sProbe blank) u))
  have ht : applyActs blank T ts = u := by
    rw [applyActs_append, applyActs_append, hu, sProbe_restore u he'.enc.ca he'.enc.base.cd]
  refine ⟨T, D', g', ?_, by rw [ht]; exact he', hok', ?_⟩
  · apply execA_seq (sProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]
    exact sRestoreProg_exec _
  · have hh : T.length = L.length + 4 := by
      simp only [T, sProbe, sRestore, List.length_append, List.length_cons, List.length_nil]
      omega
    omega

/-- info: 'PalPeg.GSPreProg.SCAN_R_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SCAN_R_spec

end PalPeg.GSPreProg
