import PalPeg.GSPreprocessProg73
import PalPeg.ProgLangSum

/-! # Embedding the finite decomposition into the shared fifteen tapes -/
set_option autoImplicit false
namespace PalPeg.PrepInstance
open PegSeparation.RealTimeTM PalPeg.PatternTapes PalPeg.PatternProg PalPeg.ProgLang PalPeg.Program
variable {sc : ℕ} {Terminal : Type}

def coreSlot : Fin 12 ↪ Fin 15 where
  toFun i := ![sV1, sV2, sCd, sCq, sCe, sC1, sCf, sCs, sRp, sCa, sCb, sCc] i
  inj' := by decide

theorem getT_prj_slot (S : Tapes sc) (i : Fin 12) :
    GSPreProg.getT (prj S) i = S (coreSlot i) := by
  fin_cases i <;> rfl

theorem TS_prj_slot (S : Tapes sc) (i : Fin 12) :
    GSPreProg.TS (prj S) i = TSg S (coreSlot i) := by
  change GSPreProg.toS (GSPreProg.getT (prj S) i) = _
  rw [getT_prj_slot]
  rfl

theorem extend_prj (S : Tapes sc) :
    extend coreSlot (GSPreProg.TS (prj S)) (TSg S) = TSg S := by
  funext j
  cases h : proj coreSlot j with
  | none => exact extend_of_proj_none h _ _
  | some i =>
    have e := eq_ι_of_proj_eq_some h
    subst j
    rw [extend_ι, TS_prj_slot]

theorem core_exec_transport {blank endSym mark : Fin sc}
    {p : Prog GSPreProg.A9 GSPreProg.Cond9} {S : Tapes sc}
    {trace : List (Fin 12 → Fin sc × Move)}
    (h : Exec (GSPreProg.I9 (Terminal := Terminal) blank endSym mark) blank p
      (GSPreProg.TS (prj S)) trace) :
    Exec ((GSPreProg.I9 (Terminal := Terminal) blank endSym mark).transport coreSlot)
      blank p (TSg S) (trace.map (extendVec coreSlot (TSg S))) := by
  simpa only [extend_prj] using exec_transport h coreSlot (TSg S)

theorem extend_core_result (blank : Fin sc) (L : List (GSPre.Act sc)) (S : Tapes sc) :
    extend coreSlot (GSPreProg.TS (GSPre.applyActs blank L (prj S))) (TSg S) =
      TSg (run blank (L.map liftAct) S) := by
  rw [← prj_run]
  funext j
  cases h : proj coreSlot j with
  | some i =>
    have e := eq_ι_of_proj_eq_some h
    subst j
    rw [extend_ι, TS_prj_slot]
  | none =>
    rw [extend_of_proj_none h]
    have hn (i : Fin 12) : j ≠ coreSlot i := by
      intro e
      subst j
      simp at h
    have he := run_liftActs_other blank L S j (hn 0) (hn 1) (hn 2) (hn 3)
      (hn 4) (hn 5) (hn 6) (hn 7) (hn 8) (hn 9) (hn 10) (hn 11)
    exact congrArg PatternProg.toS he.symm

theorem applyTrace_core (blank : Fin sc) (L : List (GSPre.Act sc)) (S : Tapes sc) :
    applyTrace blank (TSg S)
      ((GSPreProg.avecs blank L (prj S)).map (extendVec coreSlot (TSg S))) =
        TSg (run blank (L.map liftAct) S) := by
  have h := applyTrace_extend coreSlot blank (TSg S)
    (GSPreProg.avecs blank L (prj S)) (GSPreProg.TS (prj S))
  simpa only [extend_prj, GSPreProg.applyTrace_avecs, extend_core_result] using h

abbrev PrepAct (sc : ℕ) := Sum GSPreProg.A9 (ActG 15 sc)
abbrev PrepCond (sc : ℕ) := Sum GSPreProg.Cond9 (CondG 15 sc)

/-- Both branches act on the same tapes, not on a disjoint sum of tape bundles. -/
noncomputable def prepInterp (blank endSym mark : Fin sc) :
    Interp Terminal (PrepAct sc) (PrepCond sc) (Fin sc) 15 where
  actOf a := match a with
    | .inl a => ((GSPreProg.I9 blank endSym mark).transport coreSlot).actOf a
    | .inr a => (IG Terminal 15 sc).actOf a
  condOf c := match c with
    | .inl c => ((GSPreProg.I9 (Terminal := Terminal) blank endSym mark).transport coreSlot).condOf c
    | .inr c => (IG Terminal 15 sc).condOf c

theorem prepInterp_inputFree (blank endSym mark : Fin sc) :
    InputFree (prepInterp (Terminal := Terminal) blank endSym mark) := by
  intro a x σ
  cases a with
  | inl a =>
    funext j
    simp only [prepInterp, Interp.transport]
    cases proj coreSlot j <;> rfl
  | inr a => rfl

theorem core_exec_shared {blank endSym mark : Fin sc}
    {p : Prog GSPreProg.A9 GSPreProg.Cond9} {S : Tapes sc}
    {trace : List (Fin 12 → Fin sc × Move)}
    (h : Exec (GSPreProg.I9 (Terminal := Terminal) blank endSym mark) blank p
      (GSPreProg.TS (prj S)) trace) :
    Exec (prepInterp (Terminal := Terminal) blank endSym mark) blank
      (p.map Sum.inl Sum.inl) (TSg S) (trace.map (extendVec coreSlot (TSg S))) :=
  exec_map (I₂ := prepInterp blank endSym mark) (fa := Sum.inl) (fc := Sum.inl)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (core_exec_transport h)

theorem aux_exec_shared {blank endSym mark : Fin sc}
    {p : Prog (ActG 15 sc) (CondG 15 sc)} {S : Fin 15 → STape (Fin sc)}
    {trace : List (Fin 15 → Fin sc × Move)}
    (h : Exec (IG Terminal 15 sc) blank p S trace) :
    Exec (prepInterp (Terminal := Terminal) blank endSym mark) blank
      (p.map Sum.inr Sum.inr) S trace :=
  exec_map (I₂ := prepInterp blank endSym mark) (fa := Sum.inr) (fc := Sum.inr)
    (fun _ _ => rfl) (fun _ _ _ => rfl) h

def finitePrep (blank startSym endSym leftSym mark : Fin sc) (k : ℕ) :
    Prog (PrepAct sc) (PrepCond sc) :=
  .seq ((finitePrologue blank startSym endSym leftSym).map Sum.inr Sum.inr)
    (.seq ((GSPreProg.DECOMPOSE k).map Sum.inl Sum.inl)
      ((finiteEpilogue (blank := blank) (mark := mark) startSym endSym).map Sum.inr Sum.inr))

theorem exec_shared_seq {blank endSym mark : Fin sc}
    {a c : Prog (ActG 15 sc) (CondG 15 sc)} {b : Prog GSPreProg.A9 GSPreProg.Cond9}
    {S : Tapes sc} {la lc : List (TAct 15 sc)} {lb : List (GSPre.Act sc)}
    (ha : ExecG Terminal blank a S la)
    (hb : GSPreProg.ExecA Terminal blank endSym mark b (prj (runG blank la S)) lb)
    (hc : ExecG Terminal blank c (run blank (lb.map liftAct) (runG blank la S)) lc) :
    Exec (prepInterp (Terminal := Terminal) blank endSym mark) blank
      (.seq (a.map Sum.inr Sum.inr) (.seq (b.map Sum.inl Sum.inl) (c.map Sum.inr Sum.inr)))
      (TSg S) (gavecs blank la S ++
        ((GSPreProg.avecs blank lb (prj (runG blank la S))).map
          (extendVec coreSlot (TSg (runG blank la S))) ++
          gavecs blank lc (run blank (lb.map liftAct) (runG blank la S)))) := by
  apply exec_seq (aux_exec_shared ha)
  rw [applyTrace_gavecs]
  apply exec_seq (core_exec_shared hb)
  rw [applyTrace_core]
  exact aux_exec_shared hc

/-- The shared execution has exactly the sequential concrete tape endpoint. -/
theorem applyTrace_shared_seq (blank : Fin sc) (S : Tapes sc)
    (la lc : List (TAct 15 sc)) (lb : List (GSPre.Act sc)) :
    applyTrace blank (TSg S) (gavecs blank la S ++
      ((GSPreProg.avecs blank lb (prj (runG blank la S))).map
        (extendVec coreSlot (TSg (runG blank la S))) ++
        gavecs blank lc (run blank (lb.map liftAct) (runG blank la S)))) =
      TSg (runG blank lc (run blank (lb.map liftAct) (runG blank la S))) := by
  simp only [applyTrace_append, applyTrace_gavecs, applyTrace_core]

theorem shared_trace_length (blank : Fin sc) (S : Tapes sc)
    (la lc : List (TAct 15 sc)) (lb : List (GSPre.Act sc)) :
    (gavecs blank la S ++
      ((GSPreProg.avecs blank lb (prj (runG blank la S))).map
        (extendVec coreSlot (TSg (runG blank la S))) ++
        gavecs blank lc (run blank (lb.map liftAct) (runG blank la S)))).length =
      la.length + (lb.length + lc.length) := by
  simp only [List.length_append, List.length_map, gavecs_length, GSPreProg.avecs_length]

/-- info: 'PalPeg.PrepInstance.exec_shared_seq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exec_shared_seq

end PalPeg.PrepInstance
