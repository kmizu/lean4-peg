import PalPeg.TextFeedPipelineDemand
import PalPeg.GSVerifierHeadMoves

/-! Exact input-demand certificates for the concrete GS verifier.
Right-move budgets account for resets that also move text heads left. -/
set_option autoImplicit false

namespace PalPeg.GSVerifierDemand
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.ProgLangDemand PalPeg.ProgLangHeadMoves PalPeg.GSVerifierHeadMoves
open PalPeg.TextFeedPipelineDemand PalPeg.TextFeedPipelineIdealEngine
open PalPeg.TextFeedPipelineFrames PalPeg.GSVTapes
variable {k : ℕ}

theorem move_inl (e : Env k) (T : Fin 11 → STape (Fin k)) (a : GSVProg.Act10) (j : Fin 10) :
    (actVec (engine e) (.inl a) T (idx j)).2 = if j = a.1 then a.2.2 else .stay := by
  have hp : PalPeg.ProgLang.proj (Fin.castAddEmb 1) (Fin.castAdd 1 j) = some j := by
    rw [← Fin.castAddEmb_apply]
    exact PalPeg.ProgLang.proj_ι _ j
  simp only [actVec, engine, GSVProgZLoop.interp, Interp.sum, Interp.transport,
    idx, GSVProg.I10, hp, GSVProg.actOf10, touchVec]
  split <;> rfl

def reserve (n : ℕ) (T : Fin 11 → STape (Fin k)) (as : List (Fin 11 → Fin k × Move)) : Prop :=
  (T txt1).left.length + count txt1 as ≤ n ∧ (T txt2).left.length + count txt2 as ≤ n

theorem reserve_step (e : Env k) (n : ℕ) (T : Fin 11 → STape (Fin k)) (a : A)
    (as : List (Fin 11 → Fin k × Move)) (hb : reserve n T (actVec (engine e) a T :: as)) :
    actReady n T a ∧ reserve n (action (engine e) e.blank T a) as := by
  obtain ⟨h₁, h₂⟩ := hb
  simp only [count_cons] at h₁ h₂
  have hm₁ := apply_head e.blank (T txt1) (actVec (engine e) a T txt1)
  have hm₂ := apply_head e.blank (T txt2) (actVec (engine e) a T txt2)
  constructor
  · cases a with
    | inr => trivial
    | inl a =>
      intro hr
      constructor
      · intro ht
        have hm := move_inl e T a (GSVProg.e8 GSTapes.tT)
        rw [if_pos ht.symm, hr] at hm
        change (actVec (engine e) (.inl a) T txt1).2 = .right at hm
        rw [hm] at h₁
        norm_num [right] at h₁
        change (T txt1).left.length < n
        omega
      · intro ht
        have hm := move_inl e T a GSVProg.tX
        rw [if_pos ht.symm, hr] at hm
        change (actVec (engine e) (.inl a) T txt2).2 = .right at hm
        rw [hm] at h₂
        norm_num [right] at h₂
        change (T txt2).left.length < n
        omega
  · unfold reserve action
    constructor <;> omega

def noTextGuard : C → Prop
  | .inl .matchOk | .inl .compOk => False
  | _ => True

theorem counts_certified {e : Env k} {n : ℕ} {p : GSVProgZLoop.DProg}
    {T : Fin 11 → STape (Fin k)} {as : List (Fin 11 → Fin k × Move)}
    (he : Exec (engine e) e.blank p T as)
    (hp : Allowed (fun _ : A => True) noTextGuard p) (hb : reserve n T as) :
    Certified e n [p] T (applyTrace e.blank T as) := by
  apply checked_of_exec_budget (pa := fun _ : A => True) (pc := noTextGuard)
    (budget := reserve n) (fun T a as _ h => reserve_step e n T a as h) ?_ he hp hb
  intro T c hc
  cases c with
  | inr c => cases c <;> trivial
  | inl c => cases c <;> trivial

private theorem resChain_allowed (rate : ℕ) :
    Allowed (fun _ : A => True) noTextGuard (GSVProgZLoop.lift (GSVProg.pmap (GSProg.resChain rate))) := by
  induction rate with
  | zero => simp [GSProg.resChain, GSProg.KEEP, GSVProgZLoop.lift, GSVProg.pmap, Prog.map, Allowed]
  | succ rate ih =>
    simpa [GSProg.resChain, GSVProgZLoop.lift, GSVProg.pmap, Prog.map, Allowed, noTextGuard,
      GSProg.KEEP, GSProg.PUT, GSProg.qDecProg, GSProg.sUpProg, GSProg.sUpTail, GSVProg.fc] using ih

theorem shift_allowed (rate : ℕ) :
    Allowed (fun _ : A => True) noTextGuard (GSVProgZLoop.lift (GSVProg.shiftCore rate)) := by
  have h := resChain_allowed (rate - 1)
  simpa [GSVProg.shiftCore, GSVProg.resProgX, GSVProg.resLoopProgX, GSVProg.perProgX,
    GSVProg.perDownLoopX, GSVProg.perBodyX, GSVProg.perBodyPre, GSVProg.KEEP10,
    GSProg.perUpLoop, GSProg.perUpBody, GSProg.qDecTail, GSProg.qDecProg,
    GSProg.sUpProg, GSProg.sUpTail, GSProg.KEEP, GSProg.PUT, GSVProg.fc,
    GSVProgZLoop.lift, GSVProg.pmap, Prog.map, Allowed, noTextGuard] using h

/-- The shift is enabled at the frontier even when a complete nonempty
right pattern has just ended there. No extra input symbol is required. -/
theorem shift_certified {e : Env k} {pattern Word : List (Fin k)} {rate p r n : ℕ}
    {T : VTapes' k} {st : PalPeg.ScanState}
    (hrate : 0 < rate) (hmb : e.mark ≠ e.blank) (hstart : e.startSym ∉ pattern)
    (hpat : 0 < pattern.length)
    (hE : PalPeg.GSTapes.Encodes' e.blank e.startSym e.endSym e.mark pattern Word rate p r T.1 st)
    (hq : st.q ≤ pattern.length) (hfront : st.pos + st.q ≤ n)
    (hX : T.2.Txt2.left.length ≤ st.pos) (hen : PalPeg.Enabled pattern n st) (up : Bool) :
    Certified e n [GSVProgZLoop.lift (GSVProg.shiftCore rate)]
      (GSVProgZLoop.tapes e.blank e.mark T up)
      (GSVProgZLoop.tapes e.blank e.mark (vApplyActs' e.blank (GSVProg.shiftCoreActs e.blank e.mark rate T) T) up) := by
  obtain ⟨as, he, ht, hc₁, hc₂⟩ := lift_bounded
    (GSVProg.shiftCore_exec (Terminal := Unit) (z := (st, 0)) hrate hmb hstart hE hq) up
  obtain ⟨h₁, h₂⟩ := shift_counts hrate hmb hE
  have hpos : st.q = 0 → st.pos < n := by
    intro hq0
    rcases hen with hen | hen <;> omega
  have hi := PalPeg.TextFeedPipelineMacroFit.seq_left_length hE.txt
  have hb : reserve n (GSVProgZLoop.tapes e.blank e.mark T up) as := by
    change (T.1 PalPeg.GSTapes.tT).left.length + count txt1 as ≤ n ∧
      T.2.Txt2.left.length + count txt2 as ≤ n
    rw [hi]
    by_cases hq0 : st.q = 0
    · simp only [if_pos hq0] at h₁
      have hh := hpos hq0
      omega
    · simp only [if_neg hq0] at h₁
      omega
  have h := counts_certified he (shift_allowed rate) hb
  simpa only [ht] using h

/-- info: 'PalPeg.GSVerifierDemand.shift_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shift_certified

end PalPeg.GSVerifierDemand
