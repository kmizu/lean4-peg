import PalPeg.TextFeedPipelineInputCredit
import PalPeg.TextFeedPipelineReentryInput

/-! GS progress pays for actual worker calls and outer-loop reentry.
Input-demand safety and macro completion are proved by the imported pipeline. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrontier
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled PalPeg.TextFeedPipelineIdealEngine
open PalPeg.VerifierFeedRefinement
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineMacroResult
open PalPeg.TextFeedPipelineSupplyCost
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineInputRun
variable {k : ℕ}

/-- One unit of GS progress also pays for the outer-loop reentry. -/
def progressRate (rate : ℕ) : ℕ := 4 * GSVTapesZ.zA rate + 4 * GSVTapesZ.zB + 15

/-- Macro work, six reentry calls and two observer slots are paid by GS
progress alone. The at-most-two ready cells eliminate all input-history
credit from the conclusion. -/
theorem macro_credit {e : Env k} {Text leftPat rightPat : List (Fin k)}
    {rate p r n : ℕ} {z : GSVerifierZ.VStateZ} {u v : Snapshot k} {ws : List Event}
    (waits : ℕ)
    (hu : Refines e Text n u.model u.ideal u.i1 u.i2)
    (hs : Start e Text leftPat rightPat rate p r n u z)
    (hc : Conditions e Text leftPat rightPat rate p r z)
    (ht : Follows e u ws v)
    (hcredit : (ws.map TextFeedPipelineInstructionCost.feeds).sum +
      TextFeedPipelineFrameCost.afterDebt v.frames + VerifierFeedSupplyProgress.readyCredit e.blank u.model ≤
      2 * (ws.map TextFeedPipelineFrameCost.instructions).sum +
        TextFeedPipelineFrameCost.afterDebt u.frames + VerifierFeedSupplyProgress.readyCredit e.blank v.model + waits) :
    ws.length + 8 + progressRate rate * Phi rate z.1 ≤
      progressRate rate * Phi rate
        (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z).1 + waits := by
  obtain ⟨he, hq, _, _⟩ := initial_encoding hu hs.feed hs.ghost
  have hw := TextFeedPipelineInstructionCost.amortized_worker ht hc.positive_rate hc.mark_blank
    hc.start_right hc.end_right he hq hs.direction hs.code
  have hi := TextFeedPipelineInstructionCost.step_bound ht hc.positive_rate hc.mark_blank
    hc.start_right he.scan hq z.2.up hs.direction hs.code
  have hv := GSVTapesZ.vprogramZ'_cost hc.positive_rate hc.mark_blank hc.end_right he hq
  rw [TextFeedPipelineInstructionCost.semantic_count] at hcredit
  simp only [hs.code, TextFeedPipelineFrameCost.afterDebt] at hcredit
  have hready := VerifierFeedSupplyProgress.readyCredit_le e.blank v.model
  have hp := phi_step_lt (v := rightPat) (T := TextFeed.padW e.blank Text Text.length)
    (r := r) hc.positive_rate hc.positive_p z.1
  have hd : 1 ≤ Phi rate (scanStep rightPat rate p r
      (TextFeed.padW e.blank Text Text.length) z.1) - Phi rate z.1 := by omega
  have heq := Nat.sub_add_cancel (Nat.le_of_lt hp)
  have hpay := Nat.mul_le_mul_left (4 * GSVTapesZ.zB + 15) hd
  simp only [GSVerifierZ.vStepZ_fst, progressRate]
  nlinarith

/-- A suspended macro cannot claim an occurrence deadline merely by
accumulating physical work. Safe shifts bound its successor, and the
reserved return work keeps the current prefix strictly below that bound. -/
theorem prefix_before_deadline {e : Env k} {Text leftPat rightPat : List (Fin k)}
    {rate p r n i : ℕ} {z : GSVerifierZ.VStateZ} {u v : Snapshot k} {ws : List Event}
    (waits : ℕ)
    (hu : Refines e Text n u.model u.ideal u.i1 u.i2)
    (hs : Start e Text leftPat rightPat rate p r n u z)
    (hc : Conditions e Text leftPat rightPat rate p r z)
    (ht : Follows e u ws v)
    (hcredit : (ws.map TextFeedPipelineInstructionCost.feeds).sum +
      TextFeedPipelineFrameCost.afterDebt v.frames + VerifierFeedSupplyProgress.readyCredit e.blank u.model ≤
      2 * (ws.map TextFeedPipelineFrameCost.instructions).sum +
        TextFeedPipelineFrameCost.afterDebt u.frames + VerifierFeedSupplyProgress.readyCredit e.blank v.model + waits)
    (hK : KSimple rightPat rate p r)
    (hi : ScanInv rightPat (TextFeed.padW e.blank Text Text.length) z.1)
    (hocc : OccAt rightPat (TextFeed.padW e.blank Text Text.length) i)
    (hpos : z.1.pos ≤ i) (hno : ¬ (z.1.pos = i ∧ z.1.q = rightPat.length)) :
    ws.length + progressRate rate * (Phi rate z.1 + rate * rightPat.length) <
      progressRate rate * ((rate + 1) * (i + rightPat.length)) + waits := by
  have hw := macro_credit waits hu hs hc ht hcredit
  have hp := scanStep_pos_le_of_occ hK hc.positive_rate hi hocc hpos
    (fun hq he => hno ⟨he, hq⟩)
  have hq := scanStep_q_le (T := TextFeed.padW e.blank Text Text.length)
    (k := rate) (p₁ := p) (r := r) hi.2
  have hm := Nat.mul_le_mul_left (rate + 1) hp
  have hb : Phi rate (scanStep rightPat rate p r (TextFeed.padW e.blank Text Text.length) z.1) +
      rate * rightPat.length ≤ (rate + 1) * (i + rightPat.length) := by
    simp only [Phi]
    nlinarith
  have hb' := Nat.mul_le_mul_left (progressRate rate) hb
  simp only [GSVerifierZ.vStepZ_fst, Nat.mul_add] at hw hb' ⊢
  omega

/-- info: 'PalPeg.TextFeedPipelineFrontier.prefix_before_deadline' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prefix_before_deadline

/-- The same credit survives the actual return and interrupted reentry.
The output is the next physical macro start, with its existing phase. -/
theorem reenter_credit {Terminal : Type} {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (hR : 0 < R) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {n₀ n p r : ℕ} {z : GSVerifierZ.VStateZ}
    (x y : Config e leftSym R rate) (u v : Snapshot k) {ws : List Event}
    (hu : Valid e leftSym R rate Text n₀ x u [verifyLoop rate])
    (hs : Start e Text leftPat rightPat rate p r n₀ u z)
    (hc : Conditions e Text leftPat rightPat rate p r z)
    (ht : Follows e u ws v)
    (hcredit : (ws.map TextFeedPipelineInstructionCost.feeds).sum +
      TextFeedPipelineFrameCost.afterDebt v.frames + VerifierFeedSupplyProgress.readyCredit e.blank u.model ≤
      2 * (ws.map TextFeedPipelineFrameCost.instructions).sum +
        TextFeedPipelineFrameCost.afterDebt u.frames + VerifierFeedSupplyProgress.readyCredit e.blank v.model)
    (hr : Restored e leftSym R rate Text leftPat rightPat p r n y v [verifyLoop rate]
      (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z))
    (as : List Terminal) (hlen : 3 ≤ as.length) (hn : n + as.length ≤ Text.length)
    (ha : ∀ j a, as[j]? = some a → Text[n + j]? = some (enc a))
    (hfirst : y.1.1.2.1 = false) :
    ∃ m pre post y' v', m ≤ 6 ∧ pre.length ≤ 3 ∧ as = pre ++ post ∧
      (TextFeedPipelineReentryInput.tick e leftSym R rate enc)^[m] (as, y) = (post, y') ∧
      Valid e leftSym R rate Text (n + pre.length) y' v' [verifyLoop rate] ∧
      Start e Text leftPat rightPat rate p r (n + pre.length) v'
        (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z) ∧
      y'.1.1.2.1 = false ∧
      ws.length + m + 2 + progressRate rate * Phi rate z.1 ≤
        progressRate rate * Phi rate
          (GSVerifierZ.vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) z).1 := by
  have hw := macro_credit 0 hu.refines hs hc ht hcredit
  obtain ⟨m, pre, post, y', v', hm, hp, ha', hrun, hv, hs', hf, _⟩ :=
    TextFeedPipelineReentryInput.restored_reenter hcode hc.mark_blank leftSym R rate hR enc
      hc.blank_text hc.mark_text as hlen hn ha y v hr hfirst
  exact ⟨m, pre, post, y', v', hm, hp, ha', hrun, hv, hs', hf, by omega⟩

/-- info: 'PalPeg.TextFeedPipelineFrontier.reenter_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reenter_credit

end PalPeg.TextFeedPipelineFrontier
