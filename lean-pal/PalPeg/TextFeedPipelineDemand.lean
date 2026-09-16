import PalPeg.ProgLangDemand
import PalPeg.TextFeedPipelineSupplyCost
import PalPeg.TextFeedPipelineMacroFit

/-! Transfer source-level input-demand certificates to the actual framed
verifier. An optional post-move feed is not a demand for another input. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineDemand
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.ProgLangDemand PalPeg.ProgLangControlSteps
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineBranch
open PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineIdealEngine
open PalPeg.TextFeedPipelineGuardAgreement PalPeg.TextFeedPipelineSupplyCost
open PalPeg.TextFeedPipelineFrameCost PalPeg.VerifierFeedRefinement
variable {k : ℕ}

def idx (j : Fin 10) : Fin 11 := Fin.castAdd 1 j

def actReady (n : ℕ) (T : Fin 11 → STape (Fin k)) : A → Prop
  | .inr _ => True
  | .inl a => a.2.2 = .right →
      (a.1 = GSVProg.e8 GSTapes.tT → (T (idx (GSVProg.e8 GSTapes.tT))).left.length < n) ∧
      (a.1 = GSVProg.tX → (T (idx GSVProg.tX)).left.length < n)

def condReady (endSym : Fin k) (n : ℕ) (T : Fin 11 → STape (Fin k)) : C → Prop
  | .inl .matchOk => (T (idx (GSVProg.e8 GSTapes.tP))).focus = endSym ∨
      (T (idx (GSVProg.e8 GSTapes.tT))).left.length < n
  | .inl .compOk => (T (idx GSVProg.tU)).focus = endSym ∨ (T (idx GSVProg.tX)).left.length < n
  | _ => True

abbrev Certified (e : Env k) (n : ℕ) :=
  Checked (engine e) e.blank (actReady n) (condReady e.endSym n)

theorem Certified.frontier_mono {e : Env k} {m n : ℕ} (hmn : m ≤ n)
    {s : Stack A C} {T U : Fin 11 → STape (Fin k)} (h : Certified e m s T U) :
    Certified e n s T U := by
  apply h.mono
  · intro T a ha
    cases a with
    | inr => trivial
    | inl a =>
      intro hr
      exact ⟨fun ht => (ha hr).1 ht |>.trans_le hmn, fun ht => (ha hr).2 ht |>.trans_le hmn⟩
  · intro T c hc
    cases c with
    | inr c => cases c <;> trivial
    | inl c => cases c <;> first | trivial | exact hc.imp_right (fun h => h.trans_le hmn)

/-- The certificate follows every real instruction and every pure-control
transition. Arrival and FIFO service do not alter its ideal source state. -/
theorem follows_certified {e : Env k} {n : ℕ} {u v : Snapshot k} {ws : List Event}
    {U : Fin 11 → STape (Fin k)}
    (hu : Certified e n (erase u.frames) (bundle u.ideal u.dir) U) (h : Follows e u ws v) :
    Certified e n (erase v.frames) (bundle v.ideal v.dir) U := by
  induction h with
  | nil => exact hu
  | stutter hf hi hd _ ih => apply ih; simpa only [hf, hi, hd] using hu
  | @step u v z w ws had ht ih =>
    apply ih
    have hc := hu.controls (by rw [eval_bundle]; exact had.control)
    cases w with
    | instruction a =>
      have hh := hc.action_ready.2
      rw [had.ideal, had.direction]
      exact (bundle_action e u.ideal u.dir a) ▸ hh
    | feed1 | feed2 | idle | halt =>
      simpa only [destination, had.ideal, had.direction, idealNext, dirNext] using hc

/-- At a blocked pre-instruction supply, source readiness would require
the same text head to be strictly before the input frontier. -/
theorem pre_ready_not_blocked {n : ℕ} {u : Snapshot k}
    {T : Fin 11 → STape (Fin k)} (ev : TaskCond k → Bool)
    (h₁ : (T (idx (GSVProg.e8 GSTapes.tT))).left.length = u.i1)
    (h₂ : (T (idx GSVProg.tX)).left.length = u.i2)
    {a : A} {w : Event} (hr : actReady n T a) (hw : preWait ev a = some w) :
    ¬ Blocked n u w := by
  cases a with
  | inr up => simp [preWait] at hw
  | inl a =>
    simp only [preWait] at hw
    split_ifs at hw with hm ht hb hx hb <;> try cases hw
    · have hn := (hr hm).1 ht
      rw [h₁] at hn
      rintro (⟨_, hi⟩ | ⟨he, _⟩)
      · omega
      · cases he
    · have hn := (hr hm).2 hx
      rw [h₂] at hn
      rintro (⟨he, _⟩ | ⟨_, hi⟩)
      · cases he
      · omega

/-- Only a debt-discharging postlude can emit an unavailable supply from
a certified source state. This theorem uses the real residual frames. -/
theorem next_blocked_decreases {e : Env k} {n : ℕ} {u : Snapshot k}
    (ev : TaskCond k → Bool) (T U : Fin 11 → STape (Fin k))
    (hcompat : ∀ c, Waiting ev c = false → ev (verifyCond c) = evalConds (engine e) (fun j => (T j).focus) c)
    (ha : ∀ a w, actReady n T a → preWait ev a = some w → ¬ Blocked n u w)
    (hc : ∀ c, condReady e.endSym n T c → Waiting ev c = true → ¬ Blocked n u (condEvent c))
    (fs : List Frame) (h : Certified e n (erase fs) T U)
    (hb : Blocked n u (next ev fs).2) : afterDebt (next ev fs).1 < afterDebt fs := by
  induction fs using next.induct (ev := ev) with
  | case1 => simp [next, Blocked] at hb
  | case2 fs ih =>
    simpa only [next, afterDebt] using
      ih (by simpa [erase, eraseFrame] using h) (by simpa [next] using hb)
  | case3 fs ih =>
    simpa only [next, afterDebt] using ih (h.control (.skip _)) (by simpa [next] using hb)
  | case4 a fs ih => simpa only [next, afterDebt] using ih h (by simpa [next] using hb)
  | case5 p q fs ih =>
    simpa only [next, afterDebt] using ih (h.control (.seq _ _ _)) (by simpa [next] using hb)
  | case6 c p q fs ih => simpa only [next, afterDebt] using ih h (by simpa [next] using hb)
  | case7 c a b fs ih => simpa only [next, afterDebt] using ih h (by simpa [next] using hb)
  | case8 a fs w hw =>
    exact False.elim (ha a w h.action_ready.1 hw (by simpa only [next, hw] using hb))
  | case9 a fs hw => simp [next, hw, Blocked] at hb
  | case10 a fs hw => simp [next, hw, afterDebt]
  | case11 a fs hw ih =>
    have hh := ih h (by simpa [next, hw] using hb)
    simp only [next, if_neg hw, afterDebt]
    omega
  | case12 c p q fs hw =>
    exact False.elim (hc c h.branch_ready hw (by simpa only [next, hw, if_true] using hb))
  | case13 c p q fs hw ih =>
    have he := hcompat c (Bool.eq_false_iff.mpr hw)
    have hh := h.control (.branch c p q (erase fs))
    rw [← he] at hh
    have hh' := ih hh (by simpa [next, hw] using hb)
    by_cases hv : ev (verifyCond c) = true <;> simpa [next, hw, hv, afterDebt] using hh'
  | case14 c a b fs hw =>
    exact False.elim (hc c h.loop_ready hw (by simpa only [next, hw, if_true] using hb))
  | case15 c a b fs hw he => simp [next, hw, he, Blocked] at hb
  | case16 c a b fs hw he ih =>
    have hi : evalConds (engine e) (fun j => (T j).focus) c = false :=
      (hcompat c (Bool.eq_false_iff.mpr hw)).symm.trans (Bool.eq_false_iff.mpr he)
    simpa only [next, if_neg hw, if_neg he, afterDebt] using
      ih (h.control (.loop_no c a b (erase fs) hi)) (by simpa [next, hw, he] using hb)
  | case17 c a b fs ih => simpa only [next, afterDebt] using ih h (by simpa [next] using hb)
  | case18 c a b fs ih => simpa only [next, afterDebt] using ih h (by simpa [next] using hb)

/-- Pattern endpoints in the certificate are the actual stored endpoints;
the ideal witness is used only to identify text-head indices. -/
theorem cond_ready_not_blocked {e : Env k} {n : ℕ} {u : Snapshot k}
    {Text : List (Fin k)}
    (hu : Refines e Text n u.model u.ideal u.i1 u.i2)
    {c : C} (hc : condReady e.endSym n (bundle u.ideal u.dir) c)
    (hw : Waiting (taskEval e (fun j =>
      (TextFeedPipelineVerifier.tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir j).focus)) c = true) :
    ¬ Blocked n u (condEvent c) := by
  have h₁ := TextFeedPipelineMacroFit.seq_left_length hu.one
  have h₂ := TextFeedPipelineMacroFit.seq_left_length hu.two
  cases c with
  | inr c => cases c <;> simp [Waiting] at hw
  | inl c =>
    cases c with
    | notMark | notStart | notStartU => simp [Waiting] at hw
    | matchOk =>
      have hp := hu.other (GSVProg.e8 GSTapes.tP) (by decide) (by decide)
      change u.model.vt.1 GSTapes.tP = u.ideal.1 GSTapes.tP at hp
      have hw' : Tape.read (u.model.vt.1 GSTapes.tP) ≠ e.endSym := (of_decide_eq_true hw).1
      change Tape.read (u.ideal.1 GSTapes.tP) = e.endSym ∨
        (u.ideal.1 GSTapes.tT).left.length < n at hc
      rcases hc with hc | hc
      · exact False.elim (hw' (hp ▸ hc))
      · rw [h₁] at hc
        rintro (⟨_, hi⟩ | ⟨he, _⟩)
        · omega
        · cases he
    | compOk =>
      have hp := hu.other GSVProg.tU (by decide) (by decide)
      change u.model.vt.2.U = u.ideal.2.U at hp
      have hw' : Tape.read u.model.vt.2.U ≠ e.endSym := (of_decide_eq_true hw).1
      change Tape.read u.ideal.2.U = e.endSym ∨ u.ideal.2.Txt2.left.length < n at hc
      rcases hc with hc | hc
      · exact False.elim (hw' (hp ▸ hc))
      · rw [h₂] at hc
        rintro (⟨he, _⟩ | ⟨_, hi⟩)
        · cases he
        · omega

/-- A source demand certificate rules out every genuine barrier in the
current physical configuration, without assuming a macro return. -/
theorem certified_not_barrier {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text : List (Fin k)} {n : ℕ} (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    {U : Fin 11 → STape (Fin k)}
    (h : Certified e n (erase u.frames) (bundle u.ideal u.dir) U) :
    ¬ Barrier n u (next (taskEval e (fun j => (x.2 j).focus)) u.frames).1
      (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 := by
  rw [hu.physical]
  let ev := taskEval e (fun j =>
    (TextFeedPipelineVerifier.tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir j).focus)
  intro hf
  have hc : ∀ c, Waiting ev c = false →
      ev (verifyCond c) = evalConds (engine e) (fun j => (bundle u.ideal u.dir j).focus) c := by
    rw [eval_bundle]
    exact guard_agreement u.qt1 u.mode1 u.qt2 u.mode2 u.aux u.old u.dir hu.refines hmb hb hm hn
  have hd := next_blocked_decreases ev (bundle u.ideal u.dir) U hc
    (fun a w ha hw => pre_ready_not_blocked ev
      (TextFeedPipelineMacroFit.seq_left_length hu.refines.one)
      (TextFeedPipelineMacroFit.seq_left_length hu.refines.two) ha hw)
    (fun c hc hw => cond_ready_not_blocked hu.refines hc hw) u.frames h hf.1
  exact (Nat.not_lt_of_ge hf.2) hd

/-- info: 'PalPeg.TextFeedPipelineDemand.certified_not_barrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certified_not_barrier

end PalPeg.TextFeedPipelineDemand
