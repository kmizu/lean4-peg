import PalPeg.TextFeedPipelineOutputClock
import PalPeg.TextFeedStartupBudget

/-! A fixed implementation rate pays for concrete prep, prefix alignment
and startup. The rate does not inspect the input or the pattern length. -/
set_option autoImplicit false
namespace PalPeg.TextFeedPipelineOutputBudget

def workerRate (rate : ℕ) : ℕ :=
  max (TextFeedPipelineFrontier.progressRate rate * (rate + 1))
    (16 * (TextFeedStartupBudget.slope rate + TextFeedStartupBudget.offset rate + 8))

theorem service_rate (rate : ℕ) :
    TextFeedPipelineFrontier.progressRate rate * (rate + 1) ≤ workerRate rate := Nat.le_max_left _ _

theorem prep_rate (rate : ℕ) :
    16 * (TextFeedStartupBudget.slope rate + TextFeedStartupBudget.offset rate + 8) ≤ workerRate rate :=
  Nat.le_max_right _ _

theorem workerRate_pos (rate : ℕ) : 0 < workerRate rate := by
  have := prep_rate rate
  omega

def windows (R cost : ℕ) : ℕ := cost / R + 1
def waiting (R cost cut n : ℕ) : ℕ := cut - (n + windows R cost)
def finishInput (R cost cut n : ℕ) : ℕ :=
  n + windows R cost + waiting R cost cut n + windows R (5 * cut + 2)

theorem windows_pay {R cost : ℕ} (hR : 0 < R) : cost ≤ windows R cost * R := by
  have := Nat.mod_lt cost hR
  have := Nat.mod_add_div cost R
  unfold windows
  nlinarith

private theorem windows_eighth {A D R L cost : ℕ} (hL : 8 ≤ L)
    (hR : 16 * (A + D + 1) ≤ R) (hc : cost ≤ A * L + D) :
    windows R cost ≤ L / 8 := by
  have hq : 1 ≤ L / 8 := by omega
  have hlength : L ≤ 16 * (L / 8) := by omega
  have hA := Nat.mul_le_mul_left A hlength
  have hD := Nat.mul_le_mul_left D hq
  have hbig := Nat.mul_le_mul_right (L / 8) hR
  have hpos : 0 < R := by omega
  have hfit : cost < (L / 8) * R := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul hpos).mpr hfit
  unfold windows
  omega

theorem prep_windows {rate L cost : ℕ} (hL : 8 ≤ L)
    (hc : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate) :
    windows (workerRate rate) cost ≤ L / 8 :=
  windows_eighth hL (by have := prep_rate rate; omega) hc

theorem prefix_windows {rate L cut : ℕ} (hL : 8 ≤ L) (hcut : cut ≤ L) :
    windows (workerRate rate) (5 * cut + 2) ≤ L / 8 := by
  apply windows_eighth (A := 5) (D := 2) hL
  · have := prep_rate rate
    omega
  · omega

theorem waiting_room (R cost cut n : ℕ) :
    cut ≤ n + windows R cost + waiting R cost cut n := by unfold waiting; omega

/-- Large stages spend at most half their pattern length, including the
four possible startup arrivals. Small stages remain a separate case. -/
theorem finish_half {rate L cost cut n : ℕ} (hL : 32 ≤ L)
    (hc : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate)
    (hcut : 7 * cut < L) (hn : n ≤ L / 8) :
    finishInput (workerRate rate) cost cut n + 4 ≤ L / 2 := by
  have hp := prep_windows (by omega : 8 ≤ L) hc
  have hw := prefix_windows (rate := rate) (by omega : 8 ≤ L) (by omega : cut ≤ L)
  have hcut' : cut ≤ 2 * (L / 8) := by omega
  unfold finishInput waiting
  omega

theorem finish_credit {rate L cost cut n done : ℕ} (hrate : 2 ≤ rate) (hL : 32 ≤ L)
    (hc : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate)
    (hcut : 7 * cut < L) (hn : n ≤ L / 8)
    (hdone : done ≤ finishInput (workerRate rate) cost cut n) :
    (rate + 1) * (done + 4) ≤ rate * (L - cut) := by
  apply TextFeedStartupBudget.half_credit hrate hcut
  have := finish_half hL hc hcut hn
  omega

theorem stage_credit {k rate L cost n done : ℕ} (w : List (Fin k))
    (hrate : 2 ≤ rate) (hL : 32 ≤ L) (hw : L ≤ w.length)
    (hc : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate)
    (hn : n ≤ L / 8)
    (hdone : done ≤ finishInput (workerRate rate) cost (PrepInstances.prepRes w L).1 n) :
    let cut := (PrepInstances.prepRes w L).1
    (rate + 1) * (done + 4) ≤
      (rate + 1) * ((w.take L).reverse.take cut).length +
        rate * ((w.take L).reverse.drop cut).length := by
  have hcut : 7 * (PrepInstances.prepRes w L).1 < L := PrepInstances.prep_cut_bound (by omega) hw
  have hh := finish_credit hrate hL hc hcut hn hdone
  simp only [List.length_drop, List.length_reverse, List.length_take, Nat.min_eq_left hw]
  omega

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineOutputPrepFinish (Config finishAt)
open PalPeg.TextFeedPipelinePrefixFedPhysical (Complete)
open PalPeg.TextFeedPipelineOutputPrefixFrames (Reached)

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

def ReadyToBoot (e : Env k) (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (u v Text : List (Fin k)) (p r n : ℕ) (word : List Terminal) (x : Config e leftSym R rate) : Prop :=
  ∃ before a after J, word = before ++ a :: after ∧ J ≤ R ∧
    let y := finishAt e leftSym enc R rate before a J x
    Complete e leftSym R rate u v Text rate p r (n + before.length + 1) (y.state.1.1.1, y.tape) ∧
      (rate + 1) * (n + before.length + 1 + 4) ≤ (rate + 1) * u.length + rate * v.length

theorem credit_of_reached {e : Env k} {leftSym : Fin k} {rate L cost n : ℕ}
    (enc : Terminal → Fin k) (w Text : List (Fin k)) (word : List Terminal)
    (x : Config e leftSym (workerRate rate) rate)
    (hrate : 2 ≤ rate) (hL : 32 ≤ L) (hw : L ≤ w.length)
    (hc : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate)
    (hn : n ≤ L / 8)
    (hsize : n + word.length ≤ finishInput (workerRate rate) cost (PrepInstances.prepRes w L).1 n)
    (h : let d := PrepInstances.prepRes w L
      Reached e leftSym enc (workerRate rate) rate
        ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1) Text rate d.2.1 d.2.2 n word x) :
    let d := PrepInstances.prepRes w L
    ReadyToBoot e leftSym enc (workerRate rate) rate
      ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1) Text d.2.1 d.2.2 n word x := by
  obtain ⟨before, a, after, J, he, hJ, hcomplete⟩ := h
  refine ⟨before, a, after, J, he, hJ, hcomplete, ?_⟩
  apply stage_credit w hrate hL hw hc hn
  rw [he, List.length_append, List.length_cons] at hsize
  omega

open PalPeg.ProgLangBank PalPeg.ProgLangPersist
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelinePrepInput

/-- Instantiate the actual prep/prefix execution with a fixed worker
rate. Caller-supplied prefix-work and startup-credit inequalities disappear;
only the chosen input-slice lengths and actual input correspondence remain. -/
theorem setup_timed {e : Env k} (leftSym : Fin k) (enc : Terminal → Fin k) (rate : ℕ)
    (c : TextFeedPipelineOutput.Core e leftSym (workerRate rate) rate)
    (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hz : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (hq : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (hs : c.1.2.2.val = [task e leftSym rate]) {S : PatternTapes.Tapes k}
    (hv : prepView T = TSg S) {w Text : List (Fin k)} {L n : ℕ}
    (hpre : StageTapes.PrepPre e.blank e.mark leftSym L w Text S)
    (h : TextFeedPipelinePrefixWindow.Safe e (PrepInstances.stagePat w L) Text)
    (hi₁ : Inv q₁) (hl₁ : toList q₁ = Text.take n)
    (hi₂ : Inv q₂) (hl₂ : toList q₂ = Text.take n) (ρ : Role) (bit : Bool)
    (hrate : 2 ≤ rate) (hL : 32 ≤ L) (hw : L ≤ w.length) (hn : n ≤ L / 8) :
    let d := PrepInstances.prepRes w L
    ∃ cost, cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate ∧
      ∀ (before : List Terminal) (a : Terminal), before.length = cost / workerRate rate →
        TextFeedPrefixDeadline.Valid Text n ((before ++ [a]).map enc) →
        ∀ (waitWord runWord : List Terminal),
          waitWord.length = waiting (workerRate rate) cost d.1 n →
          runWord.length = windows (workerRate rate) (5 * d.1 + 2) →
          n + before.length + 1 + waitWord.length + runWord.length ≤ Text.length →
          (∀ j b, waitWord[j]? = some b → Text[n + before.length + 1 + j]? = some (enc b)) →
          (∀ j b, runWord[j]? = some b →
            Text[n + before.length + 1 + waitWord.length + j]? = some (enc b)) →
          ReadyToBoot e leftSym enc (workerRate rate) rate
            ((w.take L).reverse.take d.1) ((w.take L).reverse.drop d.1) Text d.2.1 d.2.2 n
            (before ++ a :: (waitWord ++ runWord)) ⟨(((c, ρ, bit), 0), 0), T⟩ := by
  dsimp only
  obtain ⟨cost, hcost, hreach⟩ := TextFeedPipelineOutputPrefixSetup.setup_reaches leftSym enc
    (workerRate rate) rate c T hb hz hq hs hv hpre h hi₁ hl₁ hi₂ hl₂ ρ bit (workerRate_pos rate)
  have hbound : cost ≤ TextFeedStartupBudget.slope rate * L + TextFeedStartupBudget.offset rate := by
    simpa only [TextFeedStartupBudget.slope, TextFeedStartupBudget.offset, Nat.add_assoc] using hcost
  refine ⟨cost, hbound, ?_⟩
  intro before a hbefore hvalid waitWord runWord hwait hrun htext hwa hra
  have hJ : cost % workerRate rate ≤ workerRate rate := Nat.le_of_lt (Nat.mod_lt _ (workerRate_pos rate))
  have hsplit : cost = before.length * workerRate rate + cost % workerRate rate := by
    rw [hbefore]
    simpa only [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div cost (workerRate rate)).symm
  have hcut : (PrepInstances.prepRes w L).1 < L := PrepInstances.prep_cut_lt (by omega) hw
  have hu : ((w.take L).reverse.take (PrepInstances.prepRes w L).1).length =
      (PrepInstances.prepRes w L).1 := by
    simp only [List.length_take, List.length_reverse, Nat.min_eq_left hw]
    exact Nat.min_eq_left (Nat.le_of_lt hcut)
  have hroom : ((w.take L).reverse.take (PrepInstances.prepRes w L).1).length ≤
      n + before.length + 1 + waitWord.length + 1 := by
    have hh := waiting_room (workerRate rate) cost (PrepInstances.prepRes w L).1 n
    rw [hu, hbefore, hwait]
    unfold windows at hh
    omega
  have hwork : 5 * ((w.take L).reverse.take (PrepInstances.prepRes w L).1).length + 2 ≤
      runWord.length * workerRate rate := by
    rw [hu, hrun]
    exact windows_pay (workerRate_pos rate)
  have hready := hreach before a (cost % workerRate rate) hJ hsplit hvalid
    waitWord runWord htext hwa hra hroom hwork
  apply credit_of_reached enc w Text (before ++ a :: (waitWord ++ runWord)) _
    hrate hL hw hbound hn _ hready
  simp only [List.length_append, List.length_cons, hbefore, hwait, hrun, finishInput, windows]
  omega

/-- info: 'PalPeg.TextFeedPipelineOutputBudget.setup_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms setup_timed
/-- info: 'PalPeg.TextFeedPipelineOutputBudget.credit_of_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms credit_of_reached
/-- info: 'PalPeg.TextFeedPipelineOutputBudget.finish_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finish_credit
/-- info: 'PalPeg.TextFeedPipelineOutputBudget.windows_pay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms windows_pay
end PalPeg.TextFeedPipelineOutputBudget
