import PalPeg.GSPreprocessProg60

/-! # Finite stripping-loop control

The failure flag lives in Ce; syntax depends on k only, not input or fuel.
-/
set_option autoImplicit false
namespace PalPeg.GSPreProg
open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang
variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def STRIP_FLAG_STEP (k : ℕ) : Prog A9 Cond9 :=
  .seq (STRIP_STEP k) (CD_CASE (.act (tCe, .blk, .right)) .skip)

def STRIP_RUN (k : ℕ) : Prog A9 Cond9 :=
  .loop .soReady (tCe, .keep, .right)
    (.seq (.act (tCq, .keep, .right)) (.seq (STRIP_FLAG_STEP k) soProbeProg))

def STRIP_CORE (k : ℕ) : Prog A9 Cond9 :=
  .seq soProbeProg (.seq (STRIP_RUN k) soRestoreProg)

theorem STRIP_RUN_stop (k : ℕ) (ts : Tapes sc)
    (h : ¬ (probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)) :
    ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((soReady_iff ts).1 hh))

theorem STRIP_RUN_cont (k : ℕ) (ts : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark ts.Cq q)
    (he : Tape.CounterView' blank mark ts.Ce e)
    (hc : probe blank ts.Ce = mark ∧ soCond blank endSym mark ts)
    {L T : List (Act sc)}
    (hb : ExecA Terminal blank endSym mark (STRIP_FLAG_STEP k) ts L)
    (hn : ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soProbe blank) (applyActs blank L ts)) T) :
    ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soProbe blank) ts) (soIter blank ts L ++ T) := by
  have hr := soProbe_restore ts hq he
  have hbody : ExecA Terminal blank endSym mark
      (.seq (.act (tCq, .keep, .right)) (.seq (STRIP_FLAG_STEP k) soProbeProg))
      (applyAct blank (applyActs blank (soProbe blank) ts)
        (Act.Ce (probe blank ts.Ce) .right))
      ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCq .right _)
    have hr' : applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right)) = ts := hr
    change ExecA Terminal blank endSym mark (.seq (STRIP_FLAG_STEP k) soProbeProg)
      (applyActs blank [Act.Cq (probe blank ts.Cq) .right]
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) (L ++ soProbe blank)
    rw [hr']
    exact execA_seq hb (soProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank ([Act.Cq (probe blank ts.Cq) .right] ++ (L ++ soProbe blank))
        (applyAct blank (applyActs blank (soProbe blank) ts)
          (Act.Ce (probe blank ts.Ce) .right))) T := by
    have hv := soIter_effect ts hq he L
    change ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soIter blank ts L) (applyActs blank (soProbe blank) ts)) T
    rw [hv]
    exact hn
  have hh := execA_loop_cont (w := .keep) rfl rfl rfl
    ((soReady_iff ts).2 hc) hbody hn'
  exact execA_of_eq (by simp only [soIter, soRestore, List.append_assoc]; rfl) hh

/-- Close the finite outer program once its loop has reached a probed final state. -/
theorem STRIP_CORE_finish (k : ℕ) (ts u : Tapes sc) {q e : ℕ}
    (hq : Tape.CounterView' blank mark u.Cq q)
    (he : Tape.CounterView' blank mark u.Ce e) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soProbe blank) ts) L)
    (hu : applyActs blank L (applyActs blank (soProbe blank) ts) =
      applyActs blank (soProbe blank) u) :
    ∃ T, ExecA Terminal blank endSym mark (STRIP_CORE k) ts T ∧
      applyActs blank T ts = u ∧ T.length = L.length + 4 := by
  refine ⟨soProbe blank ++ (L ++ soRestore (applyActs blank (soProbe blank) u)), ?_, ?_, ?_⟩
  · apply execA_seq (soProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]
    exact soRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hu, soProbe_restore u hq he]
  · simp only [soProbe, soRestore, List.length_append, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.STRIP_RUN_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_RUN_cont

variable {startSym : Fin sc} {x : List (Fin sc)}

theorem STRIP_FLAG_STEP_success (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s F p m : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts)
    (hfp : firstOuter (x.drop s) k F (x.length + 1) 1 = some (p, m)) :
    let r := extendReach (x.drop s) p (x.length + 1) (k * p)
    let s' := s + (r - k * p + 1)
    ∃ L, ExecA Terminal blank endSym mark (STRIP_FLAG_STEP k) ts L ∧
      EncS blank startSym endSym mark x s' s' ⟨0, 0, 0, 0, F, s', 0⟩
        ⟨F, 0, 0⟩ (applyActs blank L ts) ∧ s < s' ∧ s' ≤ x.length ∧
      L.length ≤ stripRate k * (firstOuterWork (x.drop s) k F (x.length + 1) 1 +
        extendReachWork (x.drop s) p (x.length + 1) (k * p)) + 2 := by
  dsimp only
  obtain ⟨L, hx, h, hlt, hle, hl⟩ := STRIP_STEP_success
    (Terminal := Terminal) hend hmark k hk hs he hfp
  let u := applyActs blank L ts
  have hc := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark u h.base.cd
    (.act (tCe, .blk, .right)) .skip [] (by exact execA_skip)
  refine ⟨_, execA_seq hx hc, ?_, hlt, hle, ?_⟩
  · simp only [List.append_nil, applyActs_append]
    rw [cdCaseTest_restore u h.base.cd]
    exact h
  · simp only [List.length_append, cdCaseTest, List.length_cons, List.length_nil]
    omega

theorem STRIP_FLAG_STEP_failure (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) (hk : 3 ≤ k) {s F : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (he : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ⟨F, 0, 0⟩ ts)
    (hfp : firstOuter (x.drop s) k F (x.length + 1) 1 = none) :
    ∃ L P, ExecA Terminal blank endSym mark (STRIP_FLAG_STEP k) ts L ∧
      EncS blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 1, P, F, s, 0⟩
        ⟨F - P, 0, 0⟩ (applyActs blank L ts) ∧ 0 < P ∧ s + P ≤ x.length ∧
      P ≤ 1 + firstOuterWork (x.drop s) k F (x.length + 1) 1 ∧
      L.length ≤ foRate k * firstOuterWork (x.drop s) k F (x.length + 1) 1 + k + 15 := by
  obtain ⟨L, P, hx, h, hp, hfit, hsize, hl⟩ := STRIP_STEP_failure
    (Terminal := Terminal) hend hmark k hk hs he hfp
  let u := applyActs blank L ts
  have hd : (k - 1) * P ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by omega) hp)
  have hc := CD_CASE_exec (Terminal := Terminal) (endSym := endSym) hmark u h.base.cd
    (.act (tCe, .blk, .right)) .skip (ceFlag blank)
    (by rw [if_neg hd]; exact execA_ct_put ctCe .right u)
  refine ⟨_, P, execA_seq hx hc, ?_, hp, hfit, hsize, ?_⟩
  · rw [applyActs_append, applyActs_append, cdCaseTest_restore u h.base.cd]
    exact ceFlagS_enc h
  · simp only [List.length_append, cdCaseTest, ceFlag, List.length_cons, List.length_nil]
    omega

/-- info: 'PalPeg.GSPreProg.STRIP_FLAG_STEP_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_FLAG_STEP_success
/-- info: 'PalPeg.GSPreProg.STRIP_FLAG_STEP_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms STRIP_FLAG_STEP_failure

theorem STRIP_RUN_stop_enc (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (k : ℕ) {s P D E F : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hfit : s + P ≤ x.length)
    (he : EncS blank startSym endSym mark x s (s + P)
      ⟨D, 0, E, P, F, s, 0⟩ g ts)
    (hstop : E ≠ 0 ∨ s + P = x.length) :
    ExecA Terminal blank endSym mark (STRIP_RUN k)
      (applyActs blank (soProbe blank) ts) [] := by
  apply execA_loop_stop
  apply Bool.eq_false_iff.mpr
  intro hh
  have hz := (soReady_enc_iff hend hmark (q := 0) (by simpa using hfit)
    (by simpa using he)).mp hh
  simp only [List.length_drop] at hz
  omega

end PalPeg.GSPreProg
