import PalPeg.GSPreprocessProg42

/-! # Finite outer control for bounded and unbounded first searches -/

set_option autoImplicit false

namespace PalPeg.GSPreProg

open PegSeparation.RealTimeTM PalPeg.GSPre PalPeg.Program PalPeg.ProgLang

variable {sc : ℕ} {Terminal : Type} {blank startSym endSym mark : Fin sc}
  {x : List (Fin sc)}

def foGuard (blank endSym mark : Fin sc) (bounded : Bool) (ts : Tapes sc) : Prop :=
  probe blank ts.Cd ≠ mark ∧ Tape.read ts.V2 ≠ endSym ∧
    (bounded = true → probe blank ts.Ca ≠ mark)

theorem foReady_iff (bounded : Bool) (ts : Tapes sc) :
    condOf9 endSym mark (.foReady bounded)
      (fun j => (getT (applyActs blank (sProbe blank) ts) j).focus) = true ↔
      foGuard blank endSym mark bounded ts := by
  simp only [condOf9, decide_eq_true_eq]
  rfl

theorem foGuard_enc_iff (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (he : EncS blank startSym endSym mark x a b c g ts) :
    foGuard blank endSym mark bounded ts ↔
      c.d ≠ 0 ∧ b < x.length ∧ (bounded = true → g.ap ≠ 0) := by
  have hb := pat_le he.base.v2
  have hd := probe_iff hmark he.base.cd
  have ha := probe_iff hmark he.ca
  have hv := read_pat_end_iff hend he.base.v2
  constructor
  · rintro ⟨hcd, hv2, hca⟩
    refine ⟨fun hz => hcd (hd.mpr hz), ?_, fun hbo hz => hca hbo (ha.mpr hz)⟩
    have hh : b ≠ x.length := fun hz => hv2 (hv.mpr hz)
    omega
  · rintro ⟨hcd, hlt, hca⟩
    refine ⟨fun hz => hcd (hd.mp hz), ?_, fun hbo hz => hca hbo (ha.mp hz)⟩
    intro hz
    have := hv.mp hz
    omega

def foBound (bounded : Bool) (bound p : ℕ) : ℕ := if bounded then bound - p else 0

theorem foBound_shift (bounded : Bool) (bound p δ : ℕ) :
    foBound bounded bound p - δ = foBound bounded bound (p + δ) := by
  cases bounded <;> simp [foBound, Nat.sub_sub]

theorem foGuard_normal_iff (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (bounded : Bool) (bound k s p F S R A B : ℕ) (hk : 2 ≤ k) (hp : 0 < p)
    (ts : Tapes sc)
    (he : EncS blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩
      ⟨foBound bounded bound p, A, B⟩ ts) :
    foGuard blank endSym mark bounded ts ↔
      p < (x.drop s).length ∧ (bounded = true → p < bound) := by
  rw [foGuard_enc_iff hend hmark bounded he, List.length_drop]
  have hpos : 0 < (k - 1) * p := Nat.mul_pos (by omega) hp
  have hs := pat_le he.base.v1
  cases bounded <;> simp only [foBound, Bool.false_eq_true, if_false, if_true, false_implies,
    true_implies, and_true] <;> omega

def foIter (blank : Fin sc) (ts : Tapes sc) (L : List (Act sc)) : List (Act sc) :=
  sRestore (applyActs blank (sProbe blank) ts) ++ L ++ sProbe blank

theorem foIter_effect (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a) (hd : Tape.CounterView' blank mark ts.Cd d)
    (L : List (Act sc)) :
    applyActs blank (foIter blank ts L) (applyActs blank (sProbe blank) ts) =
      applyActs blank (sProbe blank) (applyActs blank L ts) := by
  simp only [foIter, applyActs_append, sProbe_restore ts ha hd]

theorem foIter_length (ts : Tapes sc) (L : List (Act sc)) :
    (foIter blank ts L).length = L.length + 4 := by
  simp only [foIter, sRestore, sProbe, List.length_append, List.length_cons, List.length_nil]
  omega

def FO_RUN (bounded : Bool) (k : ℕ) : Prog A9 Cond9 :=
  .loop (.foReady bounded) (tCd, .keep, .right)
    (.seq (.act (tCa, .keep, .right)) (.seq (FIRST_BODY k) sProbeProg))

def FIRST_OUTER (bounded : Bool) (k : ℕ) : Prog A9 Cond9 :=
  .seq sProbeProg (.seq (FO_RUN bounded k) sRestoreProg)

theorem FO_RUN_stop (bounded : Bool) (k : ℕ) (ts : Tapes sc)
    (h : ¬ foGuard blank endSym mark bounded ts) :
    ExecA Terminal blank endSym mark (FO_RUN bounded k) (applyActs blank (sProbe blank) ts) [] := by
  apply execA_loop_stop
  exact Bool.eq_false_iff.mpr (fun hh => h ((foReady_iff bounded ts).mp hh))

theorem FO_RUN_cont (bounded : Bool) (k : ℕ) (ts : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark ts.Ca a) (hd : Tape.CounterView' blank mark ts.Cd d)
    (hc : foGuard blank endSym mark bounded ts) {L T : List (Act sc)}
    (hb : ExecA Terminal blank endSym mark (FIRST_BODY k) ts L)
    (hn : ExecA Terminal blank endSym mark (FO_RUN bounded k)
      (applyActs blank (sProbe blank) (applyActs blank L ts)) T) :
    ExecA Terminal blank endSym mark (FO_RUN bounded k)
      (applyActs blank (sProbe blank) ts) (foIter blank ts L ++ T) := by
  let tp := applyActs blank (sProbe blank) ts
  have hr : applyActs blank [Act.Ca tp.Ca.focus .right]
      (applyAct blank tp (Act.Cd tp.Cd.focus .right)) = ts := sProbe_restore ts ha hd
  have hbody : ExecA Terminal blank endSym mark
      (.seq (.act (tCa, .keep, .right)) (.seq (FIRST_BODY k) sProbeProg))
      (applyAct blank tp (Act.Cd tp.Cd.focus .right))
      ([Act.Ca tp.Ca.focus .right] ++ (L ++ sProbe blank)) := by
    apply execA_seq (execA_ct_keep ctCa .right _)
    change ExecA Terminal blank endSym mark (.seq (FIRST_BODY k) sProbeProg)
      (applyActs blank [Act.Ca tp.Ca.focus .right] (applyAct blank tp (Act.Cd tp.Cd.focus .right))) _
    rw [hr]
    exact execA_seq hb (sProbeProg_exec _)
  have hn' : ExecA Terminal blank endSym mark (FO_RUN bounded k)
      (applyActs blank ([Act.Ca tp.Ca.focus .right] ++ (L ++ sProbe blank))
        (applyAct blank tp (Act.Cd tp.Cd.focus .right))) T := by
    simpa only [applyActs_append, hr] using hn
  have hh := execA_loop_cont rfl rfl rfl ((foReady_iff bounded ts).mpr hc) hbody hn'
  exact execA_of_eq (by simp only [foIter, sRestore, List.append_assoc]; rfl) hh

theorem FIRST_OUTER_finish (bounded : Bool) (k : ℕ) (ts u : Tapes sc) {a d : ℕ}
    (ha : Tape.CounterView' blank mark u.Ca a) (hd : Tape.CounterView' blank mark u.Cd d)
    (L : List (Act sc))
    (hx : ExecA Terminal blank endSym mark (FO_RUN bounded k) (applyActs blank (sProbe blank) ts) L)
    (hu : applyActs blank L (applyActs blank (sProbe blank) ts) = applyActs blank (sProbe blank) u) :
    ∃ T, ExecA Terminal blank endSym mark (FIRST_OUTER bounded k) ts T ∧
      applyActs blank T ts = u ∧ T.length = L.length + 4 := by
  refine ⟨sProbe blank ++ (L ++ sRestore (applyActs blank (sProbe blank) u)), ?_, ?_, ?_⟩
  · apply execA_seq (sProbeProg_exec ts)
    apply execA_seq hx
    rw [hu]; exact sRestoreProg_exec _
  · rw [applyActs_append, applyActs_append, hu, sProbe_restore u ha hd]
  · simp only [sProbe, sRestore, List.length_append, List.length_cons, List.length_nil]
    omega

end PalPeg.GSPreProg
