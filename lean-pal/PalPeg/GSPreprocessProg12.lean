import PalPeg.GSPreprocessProg11

/-! # Execution of the one-scratch scaled comparison loop -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank endSym mark : Fin sc}

def cmulSuccessP (left : Fin 12) : Prog A9 Cond9 :=
  .seq (.act (left, .blk, .left))
    (.seq (.act (left, .blk, .stay))
      (.seq (.act (tCe, .blk, .right)) (.act (left, .blk, .left))))

def cmulFailureP (left : Fin 12) : Prog A9 Cond9 :=
  .seq (.act (tCe, .mrk, .stay))
    (.seq (.act (left, .blk, .left)) (.act (left, .mrk, .stay)))

def cmulLoopP (left right : Fin 12) (k : ℕ) : Prog A9 Cond9 :=
  .loop (.notMark left) (left, .keep, .right)
    (TRY_DEC right k (cmulSuccessP left) (cmulFailureP left))

def cmulSuccessL (left : CT sc) (blank : Fin sc) : List (Act sc) :=
  [left.act blank .left, left.act blank .stay, Act.Ce blank .right,
    left.act blank .left]

def cmulFailureL (left : CT sc) (blank mark : Fin sc) : List (Act sc) :=
  [Act.Ce mark .stay, left.act blank .left, left.act mark .stay]

def cmulNext (left right : CT sc) (blank mark : Fin sc) (k b : ℕ)
    (t : Tapes sc) : Tapes sc :=
  applyAct blank (dStep left blank (applyActs blank (tryDecL right blank mark k b t) t))
    (Act.Ce blank .right)

def cmulExitState (left : CT sc) (blank mark : Fin sc) (ok : Bool)
    (t : Tapes sc) : Tapes sc :=
  if ok then applyAct blank t (left.act blank .left)
  else applyActs blank (cmulFailureL left blank mark) t

theorem cmulSuccess_exec (left : CT sc) (t : Tapes sc) :
    ExecA Terminal blank endSym mark (cmulSuccessP left.idx) t (cmulSuccessL left blank) :=
  execA_seq (execA_ct_put left .left t)
    (execA_seq (execA_ct_put left .stay _)
      (execA_seq (execA_ct_put ctCe .right _) (execA_ct_put left .left _)))

theorem cmulFailure_exec (left : CT sc) (t : Tapes sc) :
    ExecA Terminal blank endSym mark (cmulFailureP left.idx) t
      (cmulFailureL left blank mark) :=
  execA_seq (execA_ct_mark ctCe .stay t)
    (execA_seq (execA_ct_put left .left _) (execA_ct_mark left .stay _))

theorem cmulNext_counter (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (hmark : mark ≠ blank) (k a b e : ℕ) (t : Tapes sc) (hk : k ≤ b)
    (ha : Tape.CounterView' blank mark (left.get t) (a + 1))
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce e) :
    let u := cmulNext left right blank mark k b t
    Tape.CounterView' blank mark (left.get u) a ∧
    Tape.CounterView' blank mark (right.get u) (b - k) ∧
    Tape.CounterView' blank mark u.Ce (e + 1) := by
  have hleft : left.get (applyActs blank (tryDecL right blank mark k b t) t) =
      left.get t := by
    rw [← left.get_eq, tryDec_other right left.idx hlr, left.get_eq]
  have hce : (applyActs blank (tryDecL right blank mark k b t) t).Ce = t.Ce :=
    tryDec_other right tCe hr k b t
  have hright := tryDec_counter right hmark k b t hb
  rw [if_pos hk] at hright
  dsimp only [cmulNext]
  constructor
  · change Tape.CounterView' blank mark
      (left.get (applyAct blank (dStep left blank
        (applyActs blank (tryDecL right blank mark k b t) t)) (ctCe.act blank .right))) a
    rw [ct_other_step left ctCe (Ne.symm hl), dStep, left.step_eq, left.step_eq]
    apply Tape.counter'_dec
    rw [hleft]
    exact ha
  constructor
  · change Tape.CounterView' blank mark
      (right.get (applyAct blank (dStep left blank
        (applyActs blank (tryDecL right blank mark k b t) t)) (ctCe.act blank .right))) (b - k)
    rw [ct_other_step right ctCe (Ne.symm hr)]
    simpa only [dStep, ct_other_step right left (Ne.symm hlr)] using hright
  · apply Tape.counter'_inc
    change Tape.CounterView' blank mark (ctCe.get
      (dStep left blank (applyActs blank (tryDecL right blank mark k b t) t))) e
    simp only [dStep, ct_other_step ctCe left hl]
    change Tape.CounterView' blank mark
      (applyActs blank (tryDecL right blank mark k b t) t).Ce e
    rw [hce]
    exact he

theorem getT_ct_other (c : CT sc) (j : Fin 12) (h : j ≠ c.idx)
    (t : Tapes sc) (a : Fin sc) (m : Move) :
    getT (applyAct blank t (c.act a m)) j = getT t j := by
  simp only [getT_applyAct, c.tape_eq, if_neg h]

theorem cmulNext_other (left right : CT sc) (j : Fin 12)
    (hl : j ≠ left.idx) (hr : j ≠ right.idx) (he : j ≠ tCe)
    (k b : ℕ) (t : Tapes sc) :
    getT (cmulNext left right blank mark k b t) j = getT t j := by
  change getT (applyAct blank (dStep left blank
    (applyActs blank (tryDecL right blank mark k b t) t)) (ctCe.act blank .right)) j = _
  rw [getT_ct_other ctCe j he]
  simp only [dStep, getT_ct_other left j hl]
  exact tryDec_other right j hr k b t

theorem cmulLoop_spec (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (hmark : mark ≠ blank) (k a b e : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce e) :
    ∃ (L : List (Act sc)) (u : Tapes sc),
      ExecA Terminal blank endSym mark (cmulLoopP left.idx right.idx k)
        (applyAct blank t (left.act blank .left)) L ∧
      applyActs blank L (applyAct blank t (left.act blank .left)) =
        cmulExitState left blank mark (decide (scaledGroups k a b = a)) u ∧
      Tape.CounterView' blank mark (left.get u) (a - scaledGroups k a b) ∧
      Tape.CounterView' blank mark (right.get u) (b - k * scaledGroups k a b) ∧
      Tape.CounterView' blank mark u.Ce (e + scaledGroups k a b) ∧
      (∀ j, j ≠ left.idx → j ≠ right.idx → j ≠ tCe → getT u j = getT t j) ∧
      L.length ≤ scaledGroups k a b * (3 * k + 7) +
        3 * min k (b - k * scaledGroups k a b) + 6 := by
  induction a generalizing b e t with
  | zero =>
    refine ⟨[], t, ?_, ?_, ?_⟩
    · apply execA_loop_stop
      have hp : (getT (applyAct blank t (left.act blank .left)) left.idx).focus = mark := by
        rw [left.get_eq, left.step_eq]
        exact (Tape.counter'_read_after_probe ha).trans (by simp)
      simp [condOf9, hp]
    · rfl
    · simpa [scaledGroups] using And.intro ha (And.intro hb (And.intro he
        (show ∀ j, j ≠ left.idx → j ≠ right.idx → j ≠ tCe → getT t j = getT t j by
          intros; rfl)))
  | succ a ih =>
    have hp : (getT (applyAct blank t (left.act blank .left)) left.idx).focus = blank := by
      rw [left.get_eq, left.step_eq]
      exact (Tape.counter'_read_after_probe ha).trans (by simp)
    have hrestore : applyAct blank (applyAct blank t (left.act blank .left))
        (left.act blank .right) = t := by
      have h := ct_probe_restore left t ha
      have hp' : probe blank (left.get t) = blank := (probe_eq ha).trans (by simp)
      simpa only [hp'] using h
    have hc : condOf9 endSym mark (.notMark left.idx)
        (fun j => (getT (applyAct blank t (left.act blank .left)) j).focus) = true := by
      simp [condOf9, hp, Ne.symm hmark]
    by_cases hk : k ≤ b
    · let v := cmulNext left right blank mark k b t
      have hv := cmulNext_counter left right hlr hl hr hmark k a b e t hk ha hb he
      obtain ⟨L, u, hx, hu, hua, hub, hue, huo, hcost⟩ := ih (b - k) (e + 1) v hv.1 hv.2.1 hv.2.2
      let LB := tryDecL right blank mark k b t ++ cmulSuccessL left blank
      have hB : ExecA Terminal blank endSym mark
          (TRY_DEC right.idx k (cmulSuccessP left.idx) (cmulFailureP left.idx)) t LB := by
        apply TRY_DEC_exec right hmark k b _ _ t _ hb
        rw [if_pos hk]
        exact cmulSuccess_exec left _
      have hprefix : applyActs blank LB t = applyAct blank v (left.act blank .left) := by
        rw [show LB = tryDecL right blank mark k b t ++ cmulSuccessL left blank from rfl,
          applyActs_append]
        rfl
      refine ⟨left.act blank .right :: (LB ++ L), u, ?_, ?_, ?_⟩
      · apply execA_loop_cont (w := .keep) (left.tape_eq blank .right)
          (left.move_eq blank .right)
        · rw [left.tape_eq, hp, left.write_eq]
        · exact hc
        · rw [hrestore]
          exact hB
        · rw [hrestore, hprefix]
          exact hx
      · rw [applyActs_cons, hrestore, applyActs_append, hprefix, hu]
        simp only [scaledGroups, if_pos hk, Nat.add_right_cancel_iff]
      · have hsub : b - k * (scaledGroups k a (b - k) + 1) =
            b - k - k * scaledGroups k a (b - k) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        have hother : ∀ j, j ≠ left.idx → j ≠ right.idx → j ≠ tCe → getT u j = getT t j := by
          intro j hjl hjr hjce
          exact (huo j hjl hjr hjce).trans (cmulNext_other left right j hjl hjr hjce k b t)
        have hcost' : (left.act blank .right :: (LB ++ L)).length ≤
            (scaledGroups k a (b - k) + 1) * (3 * k + 7) +
              3 * min k (b - k - k * scaledGroups k a (b - k)) + 6 := by
          have hd := tryDec_length (blank := blank) (mark := mark) right k b t
          rw [Nat.min_eq_left hk] at hd
          dsimp only [LB]
          simp only [List.length_cons, List.length_append, cmulSuccessL, List.length_nil,
            Nat.add_mul, Nat.one_mul]
          omega
        simpa only [scaledGroups, if_pos hk, Nat.succ_sub_succ, hsub,
          Nat.add_assoc, Nat.add_comm 1 (scaledGroups k a (b - k))] using
          And.intro hua (And.intro hub (And.intro hue (And.intro hother hcost')))
    · have hfail := tryDec_failure right hmark k b t hb (by omega)
      let LB := tryDecL right blank mark k b t ++ cmulFailureL left blank mark
      have hB : ExecA Terminal blank endSym mark
          (TRY_DEC right.idx k (cmulSuccessP left.idx) (cmulFailureP left.idx)) t LB := by
        apply TRY_DEC_exec right hmark k b _ _ t _ hb
        rw [if_neg hk]
        exact cmulFailure_exec left _
      have hprefix : applyActs blank LB t = cmulExitState left blank mark false t := by
        rw [show LB = tryDecL right blank mark k b t ++ cmulFailureL left blank mark from rfl,
          applyActs_append, hfail]
        rfl
      have hstop : condOf9 endSym mark (.notMark left.idx)
          (fun j => (getT (cmulExitState left blank mark false t) j).focus) = false := by
        change decide ((getT (applyActs blank (cmulFailureL left blank mark) t) left.idx).focus ≠ mark) = false
        simp only [cmulFailureL, applyActs, List.foldl_cons, List.foldl_nil,
          left.get_eq, left.step_eq]
        simp [Tape.step, TapeConfiguration.applyAction]
      refine ⟨left.act blank .right :: (LB ++ []), t, ?_, ?_, ?_⟩
      · apply execA_loop_cont (w := .keep) (left.tape_eq blank .right)
          (left.move_eq blank .right)
        · rw [left.tape_eq, hp, left.write_eq]
        · exact hc
        · rw [hrestore]
          exact hB
        · rw [hrestore, hprefix]
          exact execA_loop_stop hstop
      · rw [applyActs_cons, hrestore, applyActs_append, hprefix]
        simp [scaledGroups, hk]
      · have hcost' : (left.act blank .right :: (LB ++ [])).length ≤ 3 * min k b + 6 := by
          have hd := tryDec_length (blank := blank) (mark := mark) right k b t
          dsimp only [LB]
          simp only [List.length_cons, List.length_append, cmulFailureL, List.length_nil]
          omega
        simpa [scaledGroups, hk] using And.intro ha (And.intro hb (And.intro he
          (And.intro
            (show ∀ j, j ≠ left.idx → j ≠ right.idx → j ≠ tCe → getT t j = getT t j by
              intros; rfl) hcost')))

def cmulClearL (left : CT sc) (blank : Fin sc) (ok : Bool) (t : Tapes sc) : List (Act sc) :=
  if ok then [left.act (probe blank (left.get t)) .right]
  else [left.act blank .right, Act.Ce blank .stay]

def cmulExitP (left : Fin 12) (yes no : Prog A9 Cond9) : Prog A9 Cond9 :=
  .ite (.notMark tCe)
    (.seq (.act (left, .keep, .right)) yes)
    (.seq (.act (left, .blk, .right)) (.seq (.act (tCe, .blk, .stay)) no))

theorem cmulClear_restore (left : CT sc) (hl : tCe ≠ left.idx)
    (ok : Bool) (a e : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (he : Tape.CounterView' blank mark t.Ce e)
    (hpos : ok = false → 0 < a) :
    applyActs blank (cmulClearL left blank ok t) (cmulExitState left blank mark ok t) = t := by
  cases ok with
  | false =>
    obtain ⟨a, rfl⟩ : ∃ n, a = n + 1 := ⟨a - 1, by have := hpos rfl; omega⟩
    exact cmul_failure_flags_restore left ctCe (Ne.symm hl) t ha he
  | true => exact ct_probe_restore left t ha

theorem cmulExit_exec (left : CT sc) (hl : tCe ≠ left.idx)
    (hmark : mark ≠ blank) (ok : Bool) (a e : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (he : Tape.CounterView' blank mark t.Ce e)
    (hpos : ok = false → 0 < a)
    (yes no : Prog A9 Cond9) (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (if ok then yes else no) t L) :
    ExecA Terminal blank endSym mark (cmulExitP left.idx yes no)
      (cmulExitState left blank mark ok t) (cmulClearL left blank ok t ++ L) := by
  have hrestore := cmulClear_restore left hl ok a e t ha he hpos
  cases ok with
  | false =>
    apply execA_ite_neg
    · change decide ((ctCe.get (applyActs blank (cmulFailureL left blank mark) t)).focus ≠ mark) = false
      simp only [cmulFailureL, applyActs, List.foldl_cons, List.foldl_nil,
        ct_other_step ctCe left hl]
      simp [ctCe, Tape.step, TapeConfiguration.applyAction, applyAct]
    · apply execA_seq (execA_ct_put left .right _)
      apply execA_seq (execA_ct_put ctCe .stay _)
      change ExecA Terminal blank endSym mark no
        (applyActs blank (cmulClearL left blank false t) (cmulExitState left blank mark false t)) L
      rw [hrestore]
      exact hx
  | true =>
    apply execA_ite_pos
    · change decide ((ctCe.get (applyAct blank t (left.act blank .left))).focus ≠ mark) = true
      rw [ct_other_step ctCe left hl]
      change decide (t.Ce.focus ≠ mark) = true
      simp [he.focus_blank, Ne.symm hmark]
    · have hp : (getT (cmulExitState left blank mark true t) left.idx).focus =
          probe blank (left.get t) := by
        change (getT (applyAct blank t (left.act blank .left)) left.idx).focus = _
        rw [left.get_eq, left.step_eq]
        rfl
      have hx' : ExecA Terminal blank endSym mark yes
          (applyActs blank (cmulClearL left blank true t) (cmulExitState left blank mark true t)) L := by
        rw [hrestore]
        exact hx
      have hact := execA_ct_keep (Terminal := Terminal) (blank := blank) (endSym := endSym)
        (mark := mark) left .right (cmulExitState left blank mark true t)
      rw [left.get_eq] at hp
      rw [hp] at hact
      exact execA_seq hact hx'

theorem getT_repeat_other (c : CT sc) (j : Fin 12) (h : j ≠ c.idx)
    (a : Fin sc) (m : Move) (k : ℕ) (t : Tapes sc) :
    getT (applyActs blank (List.replicate k (c.act a m)) t) j = getT t j := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, applyActs_cons, ih, getT_ct_other c j h]

theorem cmulRestore_other (left right : CT sc) (j : Fin 12)
    (hl : j ≠ left.idx) (hr : j ≠ right.idx) (he : j ≠ tCe)
    (k e : ℕ) (t : Tapes sc) :
    getT (applyActs blank (cmulRestoreL left right blank mark k e) t) j = getT t j := by
  have hd (n : ℕ) (u : Tapes sc) :
      getT (applyActs blank (dPow ctCe blank (cmulRestoreUnit left right blank k) n) u) j = getT u j := by
    induction n generalizing u with
    | zero => rfl
    | succ n ih =>
      rw [dPow, applyActs_append, ih]
      simp only [dUnit, cmulRestoreUnit, applyActs_cons,
        getT_repeat_other right j hr, getT_ct_other left j hl, getT_ct_other ctCe j he]
  rw [cmulRestoreL, applyActs_append]
  simp only [dTest, applyActs_cons, applyActs_nil, getT_ct_other ctCe j he]
  exact hd e t

/-- The finite comparator chooses the right continuation and restores both
operand values. The scratch counter starts and finishes at zero. The trace
prefix and returned state do not depend on either continuation. -/
theorem CMUL_LE_spec (left right : CT sc)
    (hlr : left.idx ≠ right.idx) (hl : tCe ≠ left.idx) (hr : tCe ≠ right.idx)
    (hmark : mark ≠ blank) (k a b : ℕ) (t : Tapes sc)
    (ha : Tape.CounterView' blank mark (left.get t) a)
    (hb : Tape.CounterView' blank mark (right.get t) b)
    (he : Tape.CounterView' blank mark t.Ce 0) :
    ∃ (L : List (Act sc)) (u : Tapes sc),
      applyActs blank L t = u ∧
      Tape.CounterView' blank mark (left.get u) a ∧
      Tape.CounterView' blank mark (right.get u) b ∧
      Tape.CounterView' blank mark u.Ce 0 ∧
      (∀ j, j ≠ left.idx → j ≠ right.idx → j ≠ tCe → getT u j = getT t j) ∧
      L.length ≤ scaledGroups k a b * (4 * k + 10) +
        3 * min k (b - k * scaledGroups k a b) + 11 ∧
      ∀ (yes no : Prog A9 Cond9) (LT : List (Act sc)),
        ExecA Terminal blank endSym mark (if k * a ≤ b then yes else no) u LT →
        ExecA Terminal blank endSym mark (CMUL_LE left.idx right.idx k yes no) t (L ++ LT) := by
  obtain ⟨L0, v, hx, hv, hva, hvb, hve, hvo, hcost⟩ :=
    cmulLoop_spec (Terminal := Terminal) (endSym := endSym) left right hlr hl hr hmark k a b 0 t ha hb he
  simp only [Nat.zero_add] at hve
  let g := scaledGroups k a b
  let R := cmulRestoreL left right blank mark k g
  let u := applyActs blank R v
  have hR := CMUL_RESTORE_exec (Terminal := Terminal) (endSym := endSym)
    left right hl hr hmark k g v hve
  have huc := CMUL_RESTORE_counter left right hlr hl hr hmark k g (a - g) (b - k * g)
    v hva hvb hve
  have hnum := scaledGroups_restore k a b
  change a - g + g = a ∧ b - k * g + k * g = b at hnum
  have hua : Tape.CounterView' blank mark (left.get u) a := by
    simpa only [hnum.1] using huc.1
  have hub : Tape.CounterView' blank mark (right.get u) b := by
    simpa only [hnum.2] using huc.2.1
  have hpos : decide (g = a) = false → 0 < a - g := by
    intro hn
    have hg := (scaledGroups_spec k a b).1
    have hne : g ≠ a := of_decide_eq_false hn
    omega
  let C := cmulClearL left blank (decide (g = a)) v
  refine ⟨[left.act blank .left] ++ (L0 ++ (C ++ R)), u, ?_, hua, hub, huc.2.2, ?_, ?_, ?_⟩
  · rw [applyActs_append, applyActs_append, applyActs_append]
    change applyActs blank R (applyActs blank C
      (applyActs blank L0 (applyAct blank t (left.act blank .left)))) = u
    rw [hv, cmulClear_restore left hl (decide (g = a)) (a - g) g v hva hve hpos]
  · intro j hjl hjr hjce
    exact (cmulRestore_other left right j hjl hjr hjce k g v).trans (hvo j hjl hjr hjce)
  · have hclen : C.length ≤ 2 := by
      dsimp only [C, cmulClearL]
      split <;> simp
    have hrlen : R.length = g * (k + 3) + 2 := cmulRestoreL_length left right k g
    change L0.length ≤ g * (3 * k + 7) + 3 * min k (b - k * g) + 6 at hcost
    change ([left.act blank .left] ++ (L0 ++ (C ++ R))).length ≤
      g * (4 * k + 10) + 3 * min k (b - k * g) + 11
    simp only [List.length_append, List.length_cons, List.length_nil]
    nlinarith
  intro yes no LT hLT
  have hchoice : (if decide (g = a) then Prog.seq (CMUL_RESTORE left.idx right.idx k) yes
      else Prog.seq (CMUL_RESTORE left.idx right.idx k) no) =
      Prog.seq (CMUL_RESTORE left.idx right.idx k) (if k * a ≤ b then yes else no) := by
    simp only [decide_eq_true_eq, g, scaledGroups_complete_iff]
    split <;> rfl
  have hRL : ExecA Terminal blank endSym mark
      (if decide (g = a) then .seq (CMUL_RESTORE left.idx right.idx k) yes
        else .seq (CMUL_RESTORE left.idx right.idx k) no) v (R ++ LT) := by
    rw [hchoice]
    exact execA_seq hR hLT
  have hExit := cmulExit_exec left hl hmark (decide (g = a)) (a - g) g v hva hve hpos
    (.seq (CMUL_RESTORE left.idx right.idx k) yes)
    (.seq (CMUL_RESTORE left.idx right.idx k) no) (R ++ LT) hRL
  rw [← hv] at hExit
  have hMain := execA_seq (execA_ct_put (Terminal := Terminal) (endSym := endSym)
    (mark := mark) left .left t) (execA_seq hx hExit)
  simpa only [CMUL_LE, cmulLoopP, cmulExitP, cmulSuccessP, cmulFailureP,
    C, List.append_assoc] using hMain

/-- With positive scale, comparison cost is linear in the right operand,
even when the left operand is much larger. -/
theorem cmul_cost_le_right {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    scaledGroups k a b * (4 * k + 10) +
      3 * min k (b - k * scaledGroups k a b) + 11 ≤ 14 * b + 11 := by
  have hw := scaledGroups_work_bound k a b
  have hg : scaledGroups k a b ≤ k * scaledGroups k a b := by
    have := Nat.mul_le_mul_right (scaledGroups k a b) (show 1 ≤ k by omega)
    simpa only [Nat.one_mul] using this
  generalize scaledGroups k a b = g at *
  generalize min k (b - k * g) = m at *
  nlinarith [Nat.zero_le m]

/-- At unit scale, cost is also linear in the left operand. This is the
bound needed when `Cq` is compared against a possibly very large `Cr`. -/
theorem cmul_cost_one_le_left (a b : ℕ) :
    scaledGroups 1 a b * (4 * 1 + 10) +
      3 * min 1 (b - 1 * scaledGroups 1 a b) + 11 ≤ 14 * a + 14 := by
  have hg := (scaledGroups_spec 1 a b).1
  have hm := Nat.min_le_left 1 (b - 1 * scaledGroups 1 a b)
  omega

/-- info: 'PalPeg.GSPreProg.cmulLoop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cmulLoop_spec

/-- info: 'PalPeg.GSPreProg.CMUL_LE_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CMUL_LE_spec

end PalPeg.GSPreProg
