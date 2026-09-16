import PalPeg.TextFeedPipelineArrival

/-! Verifier source instructions execute in the same physical bundle as
preparation and alignment. Q1 and the auxiliary/input/direction tapes are
preserved by a verifier instruction, while Txt2 receives bounded feeding. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineVerifier
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineHandoff

variable {k : ℕ} {Terminal : Type}

def prefixModel (M : VerifierFeed.VMachine' k) : TextFeedPrefixAtomic.Model k :=
  ⟨M.Q1, GSProg.TS M.vt.1, M.vt.2.U⟩

def tapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (M : VerifierFeed.VMachine' k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :=
  TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ (prefixModel M) M.vt.2.Txt2 aux old dir

def Reserved (j : Fin 39) : Prop := j.val < 11 ∨ (21 ≤ j.val ∧ j.val < 27) ∨ j.val = 38

theorem reserved_omitted {j : Fin 39} (hj : Reserved j) : proj verifySlot j = none := by
  apply proj_eq_none
  intro i hi
  have hh := congrArg Fin.val hi
  have hn := i.isLt
  change (if h : i.val < 11 then (⟨i.val + 27, by omega⟩ : Fin 39) else ⟨i.val, by omega⟩).val = j.val at hh
  split_ifs at hh <;> dsimp at hh <;> rcases hj with hj | hj | hj <;> omega

theorem verify_view (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (M : VerifierFeed.VMachine' k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    (fun j => tapes e qt₁ m₁ qt₂ m₂ M aux old dir (verifySlot j)) = VerifierFeedShared.bundle e qt₂ m₂ M := by
  funext j
  fin_cases j <;> rfl

theorem replace_verify (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ qt₂' : QT k) (m₂ m₂' : Mode)
    (M M' : VerifierFeed.VMachine' k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    extend verifySlot (VerifierFeedShared.bundle e qt₂' m₂' M') (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) =
      tapes e qt₁ m₁ qt₂' m₂' M' aux old dir := by
  funext j
  have hcover : ∀ j : Fin 39, Reserved j ∨ ∃ i, verifySlot i = j := by
    unfold Reserved verifySlot
    decide
  rcases hcover j with hj | ⟨i, rfl⟩
  · rw [extend_of_proj_none (reserved_omitted hj)]
    fin_cases j <;> first | rfl | (simp [Reserved] at hj)
  · rw [extend_ι]
    exact (congrFun (verify_view e qt₁ m₁ qt₂' m₂' M' aux old dir) i).symm

theorem effect_Q1 (e : Env k) (a : GSVProg.Act10) (M : VerifierFeed.VMachine' k) :
    (VerifierFeedPrimitive.effect e a M).Q1 = M.Q1 := by
  unfold VerifierFeedPrimitive.effect
  split
  · exact VerifierFeed.vstepXR_Q1 e.blank e.mark M
  · split
    · exact VerifierFeed.vfillHead2_Q1 e.blank e.mark M
    · rfl

theorem instruction_exec {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VerifierFeed.VMachine' k)
    (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2) (hb : Encodes e.blank e.mark M.R2.qt M.Q2)
    (a : GSVProg.Act10) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    ∃ tr qt₂' m₂', Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank (low e (.verify a))
      (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) tr ∧ tr.length ≤ 48 ∧
      applyTrace e.blank (tapes e qt₁ m₁ qt₂ m₂ M aux old dir) tr =
        tapes e qt₁ m₁ qt₂' m₂' (VerifierFeedPrimitive.effect e a M) aux old dir ∧
      Ready e.blank e.mark qt₂' m₂' (VerifierFeedPrimitive.effect e a M).Q2 ∧
      Encodes e.blank e.mark (VerifierFeedPrimitive.effect e a M).R2.qt (VerifierFeedPrimitive.effect e a M).Q2 := by
  obtain ⟨tr, qt₂', m₂', he, hn, ht, hr, hb'⟩ := verify_exec (Terminal := Terminal) hc hmb h₂ hb a
    (tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
  rw [replace_verify] at he ht
  rw [replace_verify] at ht
  exact ⟨tr, qt₂', m₂', he, hn, ht, hr, hb'⟩

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- An instruction selected by the real source controller updates the
verifier and its FIFO on the original 39 tapes, then returns to its suffix. -/
theorem run_instruction (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s' : Stack (TaskAct k) (TaskCond k)) (a : GSVProg.Act10)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val = (s', some (.inr (.inr (.inl a)))))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (M : VerifierFeed.VMachine' k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ M aux old dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    (henc : Encodes e.blank e.mark M.R2.qt M.Q2) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₂' m₂', y.2 = tapes e qt₁ m₁ qt₂' m₂' (VerifierFeedPrimitive.effect e a M) aux old dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s' ∧
      Ready e.blank e.mark qt₁ m₁ (VerifierFeedPrimitive.effect e a M).Q1 ∧
      Ready e.blank e.mark qt₂' m₂' (VerifierFeedPrimitive.effect e a M).Q2 ∧
      Encodes e.blank e.mark (VerifierFeedPrimitive.effect e a M).R2.qt (VerifierFeedPrimitive.effect e a M).Q2 := by
  obtain ⟨tr, qt₂', m₂', he, hn, ht, hr, he'⟩ := instruction_exec (Terminal := Terminal) hc hmb qt₁ m₁ qt₂ m₂ M h₂ henc a aux old dir
  rw [← hx] at he ht
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz s' (.inr (.inr (.inl a))) hs tr he (by omega)
  refine ⟨qt₂', m₂', hyt.trans ht, hby, hcy, ?_, hr, he'⟩
  rwa [effect_Q1]

/-- Direction changes inside the zigzag loop use the same real write as
initialization, preserving every scanner and FIFO tape. -/
theorem run_direction (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 ≠ 0)
    (s' : Stack (TaskAct k) (TaskCond k)) (up : Bool)
    (hs : stepStack (taskEval e (fun j => (x.2 j).focus)) x.1.1.2.2.val = (s', some (.inr (.inr (.inr up))))) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    y.2 = writeDir e up x.2 ∧ AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2.val = s' ∧
      (y.2 38).focus = GSVProgZLoop.dirSymbol e.blank e.mark up ∧ ∀ j, j ≠ 38 → y.2 j = x.2 j := by
  obtain ⟨tr, he, hn, ht⟩ := dir_exec (Terminal := Terminal) e up x.2
  obtain ⟨hyt, hby, hcy⟩ := run_selected e leftSym R rate x hb hz s' (.inr (.inr (.inr up))) hs tr he (by omega)
  have hout := hyt.trans ht
  refine ⟨hout, hby, hcy, ?_, ?_⟩
  · rw [hout]
    simp [writeDir, STape.applyAction]
  · intro j hj
    rw [hout]
    exact Function.update_of_ne hj _ _

/-- info: 'PalPeg.TextFeedPipelineVerifier.run_instruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_instruction

/-- info: 'PalPeg.TextFeedPipelineVerifier.run_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_direction

end PalPeg.TextFeedPipelineVerifier
