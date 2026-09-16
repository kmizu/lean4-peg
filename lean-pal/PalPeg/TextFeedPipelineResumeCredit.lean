import PalPeg.TextFeedPipelineInputCredit
import PalPeg.TextFeedPipelinePrefixResume

/-! Preserve work already performed in a partial frame, then continue
with actual input rounds without restarting the macro or its accounting. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineResumeCredit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInputRun PalPeg.TextFeedPipelineSupplyCost PalPeg.TextFeedPipelineInputCredit
open PalPeg.TextFeedPipelineInstructionCost PalPeg.VerifierFeedSupplyProgress
open PalPeg.TextFeedPipelineFrameCost
variable {k : ℕ} {Terminal : Type}

def remaining {e : Env k} {leftSym : Fin k} {R rate : ℕ} (x : Config e leftSym R rate) : ℕ :=
  if x.1.1.1 = 0 then 0 else R + 1 - x.1.1.1.val

noncomputable def resume (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : Config e leftSym R rate) : Config e leftSym R rate :=
  (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[remaining x] x

theorem phase_before {B : ℕ} (N : ℕ) (p : Fin B) (h : p.val + N < B) :
    (nextPhase^[N] p).val = p.val + N := by
  induction N generalizing p with
  | zero => simp
  | succ N ih =>
    have hp : p.val + 1 < B := by omega
    rw [Function.iterate_succ_apply]
    have hh : (nextPhase p).val + N < B := by simp only [nextPhase, dif_pos hp]; omega
    rw [ih _ hh]
    simp only [nextPhase, dif_pos hp]
    omega

theorem resume_clock (e : Env k) (leftSym : Fin k) (R rate : ℕ) (x : Config e leftSym R rate) :
    (resume (Terminal := Terminal) e leftSym R rate x).1.1.1 = 0 := by
  unfold resume
  rw [run_counter_iterate]
  by_cases hz : x.1.1.1 = 0
  · simp [remaining, hz]
  · apply TextFeedPipelinePrefixResume.nextPhase_finish
    have hp := x.1.1.1.isLt
    simp only [remaining, if_neg hz]
    omega

theorem before_clock (e : Env k) (leftSym : Fin k) (R rate : ℕ) (x : Config e leftSym R rate)
    (j : ℕ) (hj : j < remaining x) :
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0 := by
  by_cases hz : x.1.1.1 = 0
  · simp only [remaining, if_pos hz] at hj
    omega
  · have hp : x.1.1.1.val ≠ 0 := fun he => hz (Fin.ext he)
    have hlt := x.1.1.1.isLt
    have hroom : x.1.1.1.val + j < R + 1 := by simp only [remaining, if_neg hz] at hj; omega
    rw [run_counter_iterate]
    intro he
    have hv := congrArg Fin.val he
    rw [phase_before j x.1.1.1 hroom] at hv
    change x.1.1.1.val + j = 0 at hv
    omega

theorem iterate_not_first (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : Config e leftSym R rate) (hf : x.1.1.2.1 = false) :
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.1 = false := by
  induction N generalizing x with
  | zero => exact hf
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (run_not_first leftSym R rate x hf)

theorem resume_or_stop {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (hu : Valid e leftSym R rate Text n x u caller) :
    (∃ v ws, Valid e leftSym R rate Text n (resume (Terminal := Terminal) e leftSym R rate x) v caller ∧
      Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      ws.length = remaining x) ∨
    (∃ m v ws, m ≤ remaining x ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      Stopped e leftSym R rate n y v) := by
  classical
  obtain ⟨m, v, ws, hmN, hlen, hv, ht, hcredit, hstop⟩ :=
    barrier_prefix (Terminal := Terminal) hc hmb leftSym R rate hb hm hn (remaining x) x u caller hu
  by_cases hs : Stopped e leftSym R rate n
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x) v
  · exact Or.inr ⟨m, v, ws, hmN, hlen, hv, ht, hcredit, hs⟩
  · have hmfull : m = remaining x := by
      rcases hstop with hmfull | hclock | hhalt | hblock
      · exact hmfull
      · by_contra hmne
        exact before_clock e leftSym R rate x m (by omega) hclock
      · exact False.elim (hs (Or.inl hhalt))
      · exact False.elim (hs (Or.inr hblock))
    rw [hmfull] at hv hlen
    exact Or.inl ⟨v, ws, hv, ht, hcredit, hlen⟩

def ContinuedStop (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (Text : List (Fin k)) (n B : ℕ) (as : List Terminal)
    (x : Config e leftSym R rate) (u₀ : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k)) : Prop :=
  ∃ pre a post m v ws, as = pre ++ a :: post ∧ m ≤ R ∧ ws.length = B + R * pre.length + m ∧
    let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
      (captured e leftSym R rate enc a (frames e leftSym R rate enc pre x))
    Valid e leftSym R rate Text (n + pre.length + 1) y v caller ∧ Follows e u₀ ws v ∧
    (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u₀.model ≤
      2 * (ws.map instructions).sum + afterDebt u₀.frames + readyCredit e.blank v.model ∧
    Stopped e leftSym R rate (n + pre.length + 1) y v

/-- A partially executed macro retains its original GS cost certificate;
the input-frame boundary need not be the beginning of its source code. -/
theorem frames_budget_from {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n cost : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u₀ u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) {xs : List Event} (hprefix : Follows e u₀ xs u)
    (hcredit : (xs.map feeds).sum + afterDebt u.frames + readyCredit e.blank u₀.model ≤
      2 * (xs.map instructions).sum + afterDebt u₀.frames + readyCredit e.blank u.model)
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)}
    (hcode : erase u₀.frames = [p])
    (hr : GSVProgZLoop.RunsTo (TextFeedPipelineIdealEngine.engine e) e.blank p
      (TextFeedPipelineIdealEngine.bundle u₀.ideal u₀.dir) U cost)
    (hbudget : 4 * cost + 3 + afterDebt u₀.frames < xs.length + R * as.length + readyCredit e.blank u₀.model) :
    ContinuedStop e leftSym R rate enc Text n xs.length as x u₀ caller := by
  rcases frames_credit hc hmb leftSym R rate enc hb hm as hn ha x u caller hu hz hfirst with hfull | hstop
  · obtain ⟨v, ws, hv, ht, hcredit', hlen⟩ := hfull
    have hwork := worker_bound (hprefix.trans ht) hcode hr
    have hins := follows_bound (hprefix.trans ht) hcode hr
    rw [← semantic_count] at hins
    simp only [List.map_append, List.sum_append] at hins
    simp only [List.length_append, List.map_append, List.sum_append] at hwork
    have hready := readyCredit_le e.blank v.model
    omega
  · obtain ⟨pre, a, post, m, v, ws, hsplit, hmR, hlen, hv, ht, hcredit', hstop⟩ := hstop
    refine ⟨pre, a, post, m, v, xs ++ ws, hsplit, hmR, ?_, hv, hprefix.trans ht, ?_, hstop⟩
    · simp only [List.length_append, hlen]; omega
    · simp only [List.map_append, List.sum_append]; omega

/-- info: 'PalPeg.TextFeedPipelineResumeCredit.frames_budget_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_budget_from

theorem resume_budget {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n cost : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hfirst : x.1.1.2.1 = false)
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)}
    (hcode : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (TextFeedPipelineIdealEngine.engine e) e.blank p
      (TextFeedPipelineIdealEngine.bundle u.ideal u.dir) U cost)
    (hbudget : 4 * cost + 3 + afterDebt u.frames < remaining x + R * as.length + readyCredit e.blank u.model) :
    (∃ m v ws, m ≤ remaining x ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      Stopped e leftSym R rate n y v) ∨
    ContinuedStop e leftSym R rate enc Text n (remaining x) as
      (resume (Terminal := Terminal) e leftSym R rate x) u caller := by
  rcases resume_or_stop (Terminal := Terminal) hc hmb leftSym R rate hb hm (by omega)
      x u caller hu with hfull | hstop
  · obtain ⟨v, xs, hv, ht, hcredit, hlen⟩ := hfull
    have H := frames_budget_from hc hmb leftSym R rate enc hb hm as hn ha
      (resume (Terminal := Terminal) e leftSym R rate x) u v caller hv
      (resume_clock e leftSym R rate x)
      (iterate_not_first e leftSym R rate (remaining x) x hfirst) ht hcredit hcode hr
      (by simpa only [hlen] using hbudget)
    exact Or.inr (by simpa only [hlen] using H)
  · exact Or.inl hstop

/-- Service within the current input frame keeps the original macro's
trace and credit. At an enabled frontier it either uses the whole window
or restores the successor; no new input or restart is involved. -/
theorem macro_window {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate N : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n₀ n : ℕ} {z : GSVerifierZ.VStateZ}
    (x₀ x : Config e leftSym R rate) (u₀ u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) {xs : List Event}
    (hu₀ : Valid e leftSym R rate Text n₀ x₀ u₀ caller)
    (hs : TextFeedPipelineInputMacro.Start e Text leftPat rightPat rate p r n₀ u₀ z)
    (hc : TextFeedPipelineInputMacro.Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (hn₀ : n₀ ≤ n) (hn : n ≤ Text.length)
    (hen : Enabled rightPat n z.1) (hu : Valid e leftSym R rate Text n x u caller)
    (hprefix : Follows e u₀ xs u)
    (hcredit : (xs.map feeds).sum + afterDebt u.frames + readyCredit e.blank u₀.model ≤
      2 * (xs.map instructions).sum + afterDebt u₀.frames + readyCredit e.blank u.model)
    (hN : N ≤ remaining x) :
    ∃ m v ws, m ≤ N ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u₀ (xs ++ ws) v ∧
      ((xs ++ ws).map feeds).sum + afterDebt v.frames + readyCredit e.blank u₀.model ≤
        2 * ((xs ++ ws).map instructions).sum + afterDebt u₀.frames + readyCredit e.blank v.model ∧
      (m = N ∨ TextFeedPipelineInputMacro.Restored e leftSym R rate Text leftPat rightPat p r n y v caller
        (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z)) := by
  obtain ⟨m, v, ws, hmN, hlen, hv, ht, hcredit', hstop⟩ :=
    barrier_prefix (Terminal := Terminal) hcode hc.mark_blank leftSym R rate
      hc.blank_text hc.mark_text hn N x u caller hu
  refine ⟨m, v, ws, hmN, hlen, hv, hprefix.trans ht, ?_, ?_⟩
  · simp only [List.map_append, List.sum_append]
    omega
  · by_cases he : m = N
    · exact Or.inl he
    · apply Or.inr
      apply stopped_restored leftSym R rate x₀ _ u₀ v caller hu₀ hs hc hpat hn₀ hn hen
        (hprefix.trans ht) hv
      rcases hstop with hfull | hclock | hhalt | hblock
      · exact False.elim (he hfull)
      · exact False.elim ((before_clock e leftSym R rate x m (by omega)) hclock)
      · exact Or.inl hhalt
      · exact Or.inr hblock

/-- info: 'PalPeg.TextFeedPipelineResumeCredit.macro_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_window

/-- info: 'PalPeg.TextFeedPipelineResumeCredit.resume_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms resume_budget

end PalPeg.TextFeedPipelineResumeCredit
