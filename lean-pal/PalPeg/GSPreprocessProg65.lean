import PalPeg.GSPreprocessProg64

/-! # Finite decomposition-loop control -/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def DECOMP_RUN (k : ℕ) : Prog A9 Cond9 :=
  .loop .soReady (tCe, .keep, .right)
    (.seq (.act (tCq, .keep, .right)) (.seq (DECOMP_BODY k) soProbeProg))

def DECOMP_CORE (k : ℕ) : Prog A9 Cond9 :=
  .seq soProbeProg (.seq (DECOMP_RUN k) soRestoreProg)

theorem DECOMP_RUN_stop (k : ℕ) (ts : Tapes sc)
    (h : ¬ (probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)) :
    ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((soReady_iff ts).1 hh))

theorem DECOMP_RUN_cont (k : ℕ) (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e)
    (hc : probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)
    {L T : List (Act sc)}
    (hb : ExecA Terminal blank endSym mark (DECOMP_BODY k) ts L)
    (hn : ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soProbe blank) (applyActs blank L ts)) T) :
    ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soProbe blank) ts) (soIter blank ts L ++ T) := by
  have hr := soProbe_restore ts hq he
  have hbody : ExecA Terminal blank endSym mark
      (.seq (.act (tCq, .keep, .right)) (.seq (DECOMP_BODY k) soProbeProg))
      (applyAct blank (applyActs blank (soProbe blank) ts)
        (Act.Ce (probe blank ts.Ce) .right))
      ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCq .right _)
    have hr' : applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right)) = ts := hr
    change ExecA Terminal blank endSym mark (.seq (DECOMP_BODY k) soProbeProg)
      (applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) (L ++ soProbe blank)
    rw [hr']
    exact execA_seq hb (soProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank))
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) T := by
    have hv := soIter_effect ts hq he L
    change ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soIter blank ts L) (applyActs blank (soProbe blank) ts)) T
    rw [hv]
    exact hn
  have hh := execA_loop_cont (w := .keep) rfl rfl rfl
    ((soReady_iff ts).2 hc) hbody hn'
  exact execA_of_eq (by simp only [soIter, soRestore, List.append_assoc]; rfl) hh

/-- Close the finite outer program once its loop has reached a probed final state. -/
theorem DECOMP_CORE_finish (k : ℕ) (ts u : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark u.Cq q)
    (he : Tape.CounterView' blank mark u.Ce e) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soProbe blank) ts) L)
    (hu : applyActs blank L (applyActs blank (soProbe blank) ts) =
      applyActs blank (soProbe blank) u) :
    ∃ T, ExecA Terminal blank endSym mark (DECOMP_CORE k) ts T ∧
      applyActs blank T ts = u ∧ T.length = L.length + 4 := by
  refine ⟨soProbe blank ++ (L ++ soRestore (applyActs blank (soProbe blank) u)), ?_, ?_, ?_⟩
  · apply execA_seq (soProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]
    exact soRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hu, soProbe_restore u hq he]
  · simp only [soProbe, soRestore, List.length_append, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.DECOMP_RUN_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMP_RUN_cont


theorem DECOMP_RUN_stop_enc (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) {s P E R : ℕ} {ts : Tapes sc}
    (_hs : s ≤ x.length)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, E, P, 0, s, R⟩ ⟨0, 0, 0⟩ ts)
    (hstop : E ≠ 0 ∨ s = x.length) :
    ExecA Terminal blank endSym mark (DECOMP_RUN k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply DECOMP_RUN_stop
  intro hh
  have hE := (probe_iff hmark he.base.ce).mp hh.1
  have hread := (read_pat_end_iff hend he.base.v2).mpr
  rcases hstop with hne | hseq
  · exact hne hE
  · have hq := (probe_iff hmark he.base.cq).mpr rfl
    exact hh.2 ⟨hq, hread hseq⟩

theorem decomposeLoop2_at_end {α : Type} [DecidableEq α] (x : List α)
    (k fuel : ℕ) : decomposeLoop2 x k fuel x.length = (x.length, 0, 0) := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [decomposeLoop2, firstPeriod, firstOuter]

theorem decomposeLoop2Work_at_end {α : Type} [DecidableEq α] (x : List α)
    (k fuel : ℕ) : decomposeLoop2Work x k fuel x.length = 0 := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [decomposeLoop2Work, decomposeStepWork, firstPeriod, firstOuter, firstOuterWork]

def decompRate (k : ℕ) : ℕ := decompBodyRate k + 9 * k + 204


theorem DECOMP_RUN_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) (fuel : ℕ) {s : ℕ} {ts : Tapes sc}
    (hs : s ≤ x.length) (hf : x.length ≤ s + fuel)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts) :
    let out := decomposeLoop2 x k fuel s
    ∃ L u E, ExecA Terminal blank endSym mark (DECOMP_RUN k)
        (applyActs blank (soProbe blank) ts) L ∧
      applyActs blank L (applyActs blank (soProbe blank) ts) = applyActs blank (soProbe blank) u ∧
      EncS blank startSym endSym mark x out.1 out.1
        ⟨0, 0, E, out.2.1, 0, out.1, out.2.2⟩ ⟨0, 0, 0⟩ u ∧
      out.1 ≤ x.length ∧ E ≤ 1 ∧ (E ≠ 0 ∨ out.1 = x.length) ∧
      L.length ≤ decompRate k * (decomposeLoop2Work x k fuel s + fuel) := by
  induction fuel generalizing s ts with
  | zero =>
    have hseq : s = x.length := by omega
    subst s
    refine ⟨[], ts, 0, ?_, rfl, he, by simp [decomposeLoop2], by omega, ?_, ?_⟩
    · exact DECOMP_RUN_stop_enc hend hmark k (by omega) he (Or.inr rfl)
    · exact Or.inr rfl
    · simp [decomposeLoop2Work]
  | succ fuel ih =>
    by_cases hseq : s = x.length
    · subst s
      refine ⟨[], ts, 0, ?_, rfl, ?_, ?_, by omega, ?_, ?_⟩
      · exact DECOMP_RUN_stop_enc hend hmark k (by omega) he (Or.inr rfl)
      · simpa only [decomposeLoop2_at_end] using he
      · simp only [decomposeLoop2_at_end, le_refl]
      · exact Or.inr (by simp only [decomposeLoop2_at_end])
      · exact Nat.zero_le _
    · have hslt : s < x.length := by omega
      have hc := STRIP_RUN_ready_enc hend hmark hslt he
      cases hfp : firstPeriod (x.drop s) k with
      | none =>
        obtain ⟨L, hx, h, hl⟩ := DECOMP_BODY_no_first (Terminal := Terminal) hend hmark k hk hslt he hfp
        have hn := DECOMP_RUN_stop_enc (Terminal := Terminal) hend hmark k hs h (Or.inl (by omega))
        have hx' := DECOMP_RUN_cont k ts he.base.cq he.base.ce hc hx hn
        refine ⟨soIter blank ts L, applyActs blank L ts, 1, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
        · simpa only [List.append_nil] using hx'
        · exact soIter_effect ts he.base.cq he.base.ce L
        · simpa only [decomposeLoop2, hfp] using h
        · simpa only [decomposeLoop2, hfp] using hs
        · exact Or.inl (by omega)
        · rw [soIter_length]
          simp only [decomposeLoop2Work, hfp, Nat.add_zero]
          unfold decompRate
          nlinarith only [hl, Nat.zero_le (decompBodyRate k)]
      | some pm =>
        rcases pm with ⟨p, m⟩
        cases hsp : secondPeriod (x.drop s) k p (extendReach (x.drop s) p (x.length + 1) m) with
        | none =>
          obtain ⟨L, hx, h, hl⟩ := DECOMP_BODY_no_second (Terminal := Terminal) hend hmark k hk hslt he hfp hsp
          have hn := DECOMP_RUN_stop_enc (Terminal := Terminal) hend hmark k hs h (Or.inl (by omega))
          have hx' := DECOMP_RUN_cont k ts he.base.cq he.base.ce hc hx hn
          refine ⟨soIter blank ts L, applyActs blank L ts, 1, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
          · simpa only [List.append_nil] using hx'
          · exact soIter_effect ts he.base.cq he.base.ce L
          · simpa only [decomposeLoop2, hfp, hsp] using h
          · simpa only [decomposeLoop2, hfp, hsp] using hs
          · exact Or.inl (by omega)
          · rw [soIter_length]
            simp only [decomposeLoop2Work, hfp, hsp, Nat.add_zero]
            unfold decompRate
            nlinarith only [hl, Nat.zero_le (decompBodyRate k)]
        | some p2 =>
          obtain ⟨L, hx, h, hlt, hle, hl⟩ := DECOMP_BODY_continue (Terminal := Terminal) hend hmark k hk hslt he hfp hsp
          obtain ⟨T, u, E, ht, heff, henc, hfit, hE, hstop, hlen⟩ := ih hle (by omega) h
          have hx' := DECOMP_RUN_cont k ts he.base.cq he.base.ce hc hx ht
          refine ⟨soIter blank ts L ++ T, u, E, hx', ?_, ?_, ?_, hE, ?_, ?_⟩
          · rw [applyActs_append, soIter_effect ts he.base.cq he.base.ce L]
            exact heff
          · simpa only [decomposeLoop2, hfp, hsp] using henc
          · simpa only [decomposeLoop2, hfp, hsp] using hfit
          · simpa only [decomposeLoop2, hfp, hsp] using hstop
          · rw [List.length_append, soIter_length]
            simp only [decomposeLoop2Work, hfp, hsp]
            unfold decompRate at hlen ⊢
            nlinarith only [hl, hlen, Nat.zero_le (decompBodyRate k)]

/-- info: 'PalPeg.GSPreProg.DECOMP_RUN_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMP_RUN_spec

def DECOMPOSE (k : ℕ) : Prog A9 Cond9 := .seq (DECOMP_CORE k) ezProg

theorem DECOMPOSE_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) (fuel : ℕ) {s : ℕ} {ts : Tapes sc}
    (hs : s ≤ x.length) (hf : x.length ≤ s + fuel)
    (he : EncS blank startSym endSym mark x s s
      ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts) :
    let out := decomposeLoop2 x k fuel s
    ∃ L, ExecA Terminal blank endSym mark (DECOMPOSE k) ts L ∧
      EncS blank startSym endSym mark x out.1 out.1
        ⟨0, 0, 0, out.2.1, 0, out.1, out.2.2⟩ ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ decompRate k * (decomposeLoop2Work x k fuel s + fuel) + 8 := by
  obtain ⟨L, u, E, hx, hu, henc, _, hE, _, hlen⟩ :=
    DECOMP_RUN_spec (Terminal := Terminal) hend hmark k hk fuel hs hf he
  obtain ⟨T, ht, heff, hcost⟩ := DECOMP_CORE_finish k ts u henc.base.cq henc.base.ce L hx hu
  have hT := heff ▸ henc
  obtain ⟨U, hU, hfin, hcl⟩ := EZ_spec (Terminal := Terminal) hmark hT
  refine ⟨_, execA_seq ht hU, ?_, ?_⟩
  · simpa only [applyActs_append] using hfin
  · rw [List.length_append]
    omega

theorem DECOMPOSE_initial (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x 0 0
      ⟨0, 0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0⟩ ts) :
    ∃ L, ExecA Terminal blank endSym mark (DECOMPOSE k) ts L ∧
      EncS blank startSym endSym mark x (decompose2 x k).1 (decompose2 x k).1
        ⟨0, 0, 0, (decompose2 x k).2.1, 0, (decompose2 x k).1, (decompose2 x k).2.2⟩
        ⟨0, 0, 0⟩ (applyActs blank L ts) ∧
      L.length ≤ decompRate k * (decompose2Work x k + x.length + 1) + 8 := by
  simpa only [decompose2, decompose2Work, Nat.add_assoc] using
    DECOMPOSE_spec (Terminal := Terminal) hend hmark k hk (x.length + 1) (Nat.zero_le _) (by omega) he

/-- info: 'PalPeg.GSPreProg.DECOMPOSE_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DECOMPOSE_initial
end PalPeg.GSPreProg
