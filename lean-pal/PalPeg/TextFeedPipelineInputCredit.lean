import PalPeg.TextFeedPipelineSupplyCost
import PalPeg.TextFeedPipelineInputRun
import PalPeg.TextFeedPipelineInputMacro
import PalPeg.TextFeedPipelineMacroDemand

/-! Productive-work accounting through real input frames. Arrivals
preserve the two ready-cell credits and pending instruction postludes. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineInputCredit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInputRun PalPeg.TextFeedPipelineSupplyCost
open PalPeg.TextFeedPipelineInstructionCost PalPeg.VerifierFeedSupplyProgress
open PalPeg.TextFeedPipelineFrameCost
variable {k : ℕ} {Terminal : Type}

def Stopped (e : Env k) (leftSym : Fin k) (R rate n : ℕ)
    (x : Config e leftSym R rate) (u : Snapshot k) : Prop :=
  (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt ∨
    Barrier n u (next (taskEval e (fun j => (x.2 j).focus)) u.frames).1
      (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2

theorem arrival_credit {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    ∃ m v ws, m ≤ R ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a x)
      Valid e leftSym R rate Text (n + 1) y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      (m = R ∨ Stopped e leftSym R rate (n + 1) y v) := by
  obtain ⟨v, hv, had, _, _, hf, hvt⟩ := capture_enqueue hc hmb leftSym R rate enc a hm hn x u caller hu hz hfirst ha
  have hready : readyCredit e.blank v.model = readyCredit e.blank u.model := by
    simp only [readyCredit, hvt]
  obtain ⟨m, z, ws, hmR, hlen, hzv, hfollow, hcredit, hstop⟩ := barrier_prefix (Terminal := Terminal)
    hc hmb leftSym R rate hb hm (Nat.succ_le_of_lt hn) R
    (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
      (captured e leftSym R rate enc a x)) v caller hv
  refine ⟨m, z, ws, hmR, hlen, ?_, had.trans hfollow, ?_, ?_⟩
  · simpa only [Function.iterate_succ_apply] using hzv
  · simpa only [hready, hf] using hcredit
  · rcases hstop with hfull | hclock | hhalt | hblock
    · exact Or.inl hfull
    · by_cases hfull : m = R
      · exact Or.inl hfull
      · have hm1 : m + 1 < R + 1 := by omega
        have he := run_enqueues_once (Terminal := Terminal) e leftSym R rate (m + 1) hm1
          (captured e leftSym R rate enc a x) hz
        simp only [Function.iterate_succ_apply, choose_enqueues, hclock] at he
        simp at he
    · exact Or.inr (Or.inl (by simpa only [Function.iterate_succ_apply] using hhalt))
    · exact Or.inr (Or.inr (by simpa only [Function.iterate_succ_apply] using hblock))

/-- Returns at the last worker call of a frame are exposed too; no extra
input is needed merely to notice that boundary. -/
theorem frame_credit {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (a : Terminal)
    {Text : List (Fin k)} {n : ℕ} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some (enc a)) :
    (∃ v ws, Valid e leftSym R rate Text (n + 1) (frame e leftSym R rate enc a x) v caller ∧
      Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧ ws.length = R) ∨
    (∃ m v ws, m ≤ R ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a x)
      Valid e leftSym R rate Text (n + 1) y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      Stopped e leftSym R rate (n + 1) y v) := by
  classical
  obtain ⟨m, v, ws, hmR, hlen, hv, hfollow, hcredit, hstop⟩ :=
    arrival_credit hc hmb leftSym R rate enc a hb hm hn x u caller hu hz hfirst ha
  by_cases hs : Stopped e leftSym R rate (n + 1)
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a x)) v
  · exact Or.inr ⟨m, v, ws, hmR, hlen, hv, hfollow, hcredit, hs⟩
  · have hfull := hstop.resolve_right hs
    rw [hfull] at hv hlen
    exact Or.inl ⟨v, ws, hv, hfollow, hcredit, hlen⟩

def Interrupted (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (Text : List (Fin k)) (n : ℕ) (as : List Terminal)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k)) : Prop :=
  ∃ pre a post m v ws, as = pre ++ a :: post ∧ m ≤ R ∧ ws.length = R * pre.length + m ∧
    let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
      (captured e leftSym R rate enc a (frames e leftSym R rate enc pre x))
    Valid e leftSym R rate Text (n + pre.length + 1) y v caller ∧ Follows e u ws v ∧
    (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
      2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
    Stopped e leftSym R rate (n + pre.length + 1) y v

/-- Accounting telescopes across arbitrarily many actual input rounds. -/
theorem frames_credit {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) :
    (∃ v ws, Valid e leftSym R rate Text (n + as.length) (frames e leftSym R rate enc as x) v caller ∧
      Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      ws.length = R * as.length) ∨
    Interrupted e leftSym R rate enc Text n as x u caller := by
  induction as generalizing n x u with
  | nil => exact Or.inl ⟨u, [], hu, .nil u, by simp, by simp⟩
  | cons a as ih =>
    have hn' : n < Text.length := by simp only [List.length_cons] at hn; omega
    have ha0 : Text[n]? = some (enc a) := by simpa using ha 0 a rfl
    rcases frame_credit hc hmb leftSym R rate enc a hb hm hn' x u caller hu hz hfirst ha0 with hfull | hret
    · obtain ⟨v, ws, hv, hfollow, hcredit, hlen⟩ := hfull
      have hnt : n + 1 + as.length ≤ Text.length := by simp only [List.length_cons] at hn; omega
      have hat : ∀ j b, as[j]? = some b → Text[n + 1 + j]? = some (enc b) := by
        intro j b hj
        have he := ha (j + 1) b (by simpa using hj)
        simpa only [Nat.add_assoc, Nat.add_comm 1 j] using he
      rcases ih hnt hat (frame e leftSym R rate enc a x) v hv
        (frame_clock leftSym R rate enc a x hz) (frame_not_first leftSym R rate enc a x hfirst) with hall | hret
      · obtain ⟨z, ts, hzv, ht, hcredit', hts⟩ := hall
        refine Or.inl ⟨z, ws ++ ts, ?_, hfollow.trans ht, ?_, ?_⟩
        · simpa only [frames, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 as.length] using hzv
        · simp only [List.map_append, List.sum_append]
          omega
        · simp only [List.length_append, hlen, hts, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
      · obtain ⟨pre, b, post, m, z, ts, hsplit, hmR, hts, hzv, ht, hcredit', hstop⟩ := hret
        refine Or.inr ⟨a :: pre, b, post, m, z, ws ++ ts, ?_, hmR, ?_, ?_, hfollow.trans ht, ?_, ?_⟩
        · simp only [List.cons_append, hsplit]
        · simp only [List.length_append, hlen, hts, List.length_cons, Nat.mul_add, Nat.mul_one]
          omega
        · simpa only [frames, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 pre.length] using hzv
        · simp only [List.map_append, List.sum_append]
          omega
        · simpa only [frames, List.foldl_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 pre.length] using hstop
    · obtain ⟨m, v, ws, hmR, hlen, hv, hfollow, hcredit, hstop⟩ := hret
      exact Or.inr ⟨[], a, as, m, v, ws, rfl, hmR, by simpa using hlen, hv, hfollow, hcredit, hstop⟩

/-- info: 'PalPeg.TextFeedPipelineInputCredit.frames_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_credit

/-- Sufficient real input-frame budget forces a return or a genuine
frontier barrier. The bound is independent of the arrival index. -/
theorem frames_budget {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n cost : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false)
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)}
    (hcode : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (TextFeedPipelineIdealEngine.engine e) e.blank p
      (TextFeedPipelineIdealEngine.bundle u.ideal u.dir) U cost)
    (hbudget : 4 * cost + 3 + afterDebt u.frames < R * as.length + readyCredit e.blank u.model) :
    Interrupted e leftSym R rate enc Text n as x u caller := by
  rcases frames_credit hc hmb leftSym R rate enc hb hm as hn ha x u caller hu hz hfirst with hfull | hstop
  · obtain ⟨v, ws, hv, hfollow, hcredit, hlen⟩ := hfull
    have hwork := worker_bound hfollow hcode hr
    have hins := follows_bound hfollow hcode hr
    rw [semantic_count] at hcredit
    have hready := readyCredit_le e.blank v.model
    omega
  · exact hstop

theorem bounded_frames {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text : List (Fin k)} (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (as : List Terminal) {n cost : ℕ} (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false)
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)}
    (hcode : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (TextFeedPipelineIdealEngine.engine e) e.blank p
      (TextFeedPipelineIdealEngine.bundle u.ideal u.dir) U cost)
    (hR : 1 ≤ R) (hlen : as.length = 4 * cost + afterDebt u.frames + 4) :
    Interrupted e leftSym R rate enc Text n as x u caller := by
  apply frames_budget hc hmb leftSym R rate enc hb hm as hn ha x u caller hu hz hfirst hcode hr
  have hmR := Nat.mul_le_mul_right as.length hR
  omega

/-- info: 'PalPeg.TextFeedPipelineInputCredit.frames_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frames_budget

/-- A stopped residual macro at an enabled frontier is a real return,
even when it started before intervening input arrivals. -/
theorem stopped_restored {e : Env k} (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n₀ n : ℕ} {z : GSVerifierZ.VStateZ}
    (x₀ x : Config e leftSym R rate) (u v : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) {ws : List Event}
    (hu : Valid e leftSym R rate Text n₀ x₀ u caller)
    (hs : TextFeedPipelineInputMacro.Start e Text leftPat rightPat rate p r n₀ u z)
    (hc : TextFeedPipelineInputMacro.Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (hn₀ : n₀ ≤ n) (hn : n ≤ Text.length)
    (hen : Enabled rightPat n z.1) (ht : Follows e u ws v)
    (hv : Valid e leftSym R rate Text n x v caller)
    (hstop : Stopped e leftSym R rate n x v) :
    TextFeedPipelineInputMacro.Restored e leftSym R rate Text leftPat rightPat p r n x v caller
      (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z) := by
  rcases hstop with hhalt | hblock
  · exact ⟨hhalt, TextFeedPipelineMacroBoundary.compiled_boundary leftSym R rate x₀ x u v caller
      hu hv hs.feed hs.ghost hc.mark_blank hc.blank_text hc.mark_text hn ht hhalt
      hc.positive_rate hc.positive_p hc.start_right hc.end_right hc.end_left hc.start_left hc.start_end
      hs.wf hs.direction hs.code⟩
  · exact False.elim ((TextFeedPipelineMacroDemand.macro_not_barrier leftSym R rate hu.refines hs hc hpat
      hn₀ hen ht x caller hv hn) hblock)

/-- Concrete GS macro completion through actual inputs. The work budget
forces a restored successor; exact demand safety eliminates the former
input-barrier alternative without requiring an extra backlog. -/
theorem macro_budget {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {z : GSVerifierZ.VStateZ} (as : List Terminal)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller)
    (hs : TextFeedPipelineInputMacro.Start e Text leftPat rightPat rate p r n u z)
    (hc : TextFeedPipelineInputMacro.Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length)
    (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hbudget : 4 * (GSVTapesZ.zA rate *
      (Phi rate (scanStep rightPat rate p r (TextFeed.padW e.blank Text Text.length) z.1) - Phi rate z.1) +
      GSVTapesZ.zB + 1) + 3 < R * as.length + readyCredit e.blank u.model) :
    ∃ pre a post m v ws, as = pre ++ a :: post ∧ m ≤ R ∧ ws.length = R * pre.length + m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m + 1]
        (captured e leftSym R rate enc a (frames e leftSym R rate enc pre x))
      Valid e leftSym R rate Text (n + pre.length + 1) y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      TextFeedPipelineInputMacro.Restored e leftSym R rate Text leftPat rightPat p r
        (n + pre.length + 1) y v caller
        (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z) := by
  obtain ⟨he, hq, _, _⟩ := TextFeedPipelineMacroResult.initial_encoding hu.refines hs.feed hs.ghost
  have hr := GSVProgZLoop.stepProg_runsTo (Terminal := Unit) hc.positive_rate hc.mark_blank
    hc.start_right he.scan hq z.2.up
  have hinit : GSVProgZLoop.tapes e.blank e.mark u.ideal z.2.up =
      TextFeedPipelineIdealEngine.bundle u.ideal u.dir := by rw [hs.direction]; rfl
  rw [hinit] at hr
  have hprog : erase u.frames = [GSVProgZLoop.stepProg rate] := by
    simp only [hs.code, erase, eraseFrame, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hcost := GSVTapesZ.vprogramZ'_cost hc.positive_rate hc.mark_blank hc.end_right he hq
  have hdebt : afterDebt u.frames = 0 := by simp [hs.code, afterDebt]
  have hret := frames_budget hcode hc.mark_blank leftSym R rate enc hc.blank_text hc.mark_text as hn ha
    x u caller hu hz hfirst hprog hr (by omega)
  obtain ⟨pre, a, post, m, v, ws, hsplit, hmR, hlen, hv, ht, hcredit, hstop⟩ := hret
  refine ⟨pre, a, post, m, v, ws, hsplit, hmR, hlen, hv, ht, hcredit, ?_⟩
  have hfront : n + pre.length + 1 ≤ Text.length := by
    rw [hsplit, List.length_append, List.length_cons] at hn
    omega
  have hhead : z.1.pos + z.1.q ≤ n := by
    simpa only [hs.ghost] using hs.feed.hd1.trans hs.feed.m1le
  exact stopped_restored leftSym R rate x _ u v caller hu hs hc hpat (by omega) hfront
    (Or.inr (by omega)) ht hv hstop

/-- info: 'PalPeg.TextFeedPipelineInputCredit.macro_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms macro_budget

end PalPeg.TextFeedPipelineInputCredit
