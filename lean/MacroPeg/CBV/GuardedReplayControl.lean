import MacroPeg.CBV.LiteralPrefixObservation
import MacroPeg.CBV.ScannerFrontierCertificate
import MacroPeg.CBV.GuardedReplayAlignment
import MacroPeg.CBV.GuardedReplayRotation
import MacroPeg.CBV.ScannerReplayResidual
import MacroPeg.CBV.DependentCaptureFilter

namespace Shallot.MacroPeg.CBV.GuardedReplayControl
open ClockFreezing (Table)
open StatefulScanner (Machine)

/-- Each atom preserves the same retained value at its new origin.
PEG control may choose different atoms on different iterations. -/
inductive Expr (n : Nat) where
  | replayQuery
  | shift (q : Fin n) (R : ScannerReplayResidual.Labels n)
  | literalQuery (alphabet : List Char) (alphabetState literalState : Fin n) (labels : LiteralPrefixObservation.Labels n)
  | seq (a b : Expr n)
  | alt (a b : Expr n)
  | notP (a : Expr n)
  | star (a : Expr n)

def render {n : Nat} : Expr n → MExp
  | .replayQuery => .andP (.param 0)
  | .shift q R => GuardedReplayIteration.step ((R q).getD [])
  | .literalQuery _ _ q L => .andP (.lit ((L q).getD []))
  | .seq a b => .seq (render a) (render b)
  | .alt a b => .alt (render a) (render b)
  | .notP a => .notP (render a)
  | .star a => .star (render a)

def header {n : Nat} (e : Expr n) : MExp := .seq (render e) (.param 0)

def check {n : Nat} (M : Machine n) : Expr n → Bool
  | .replayQuery => true
  | .shift q R => ScannerReplayResidual.entryCheck M R q && ScannerReplayResidual.completeCheck M R
  | .literalQuery alphabet a q L => (L q).isSome && (LiteralPrefixObservation.check M alphabet L && LiteralPrefixObservation.alphabetCheck M alphabet a)
  | .seq a b | .alt a b => check M a && check M b
  | .notP a | .star a => check M a

def residual {n : Nat} (P : List Nat) : Expr n → DependentCaptureFilter.Expr
  | .replayQuery => .lit []
  | .shift q R => match DynamicScannerBinding.resume P q with
    | none => .notP (.lit [])
    | some r => .lit ((R r).getD [])
  | .literalQuery _ _ q L => match DynamicScannerBinding.resume P q with
    | none => .notP (.lit [])
    | some r => .notP (.notP (.lit ((L r).getD [])))
  | .seq a b => .seq (residual P a) (residual P b)
  | .alt a b => .alt (residual P a) (residual P b)
  | .notP a => .notP (residual P a)
  | .star a => .star (residual P a)

/-- Some observations require a finite frontier certificate for this
particular captured profile, rather than every arbitrary environment. -/
def captureCheck {n : Nat} (P : List Nat) : Expr n → Bool
  | .replayQuery | .shift _ _ => true
  | .literalQuery _ a _ _ => ScannerFrontierCertificate.check P a
  | .seq a b | .alt a b => captureCheck P a && captureCheck P b
  | .star a | .notP a => captureCheck P a

def inputSafe {n : Nat} : Expr n → Bool
  | .replayQuery | .shift _ _ => false
  | .literalQuery _ _ _ _ => true
  | .seq a b | .alt a b => inputSafe a || inputSafe b
  | .star a | .notP a => inputSafe a

/-- The old universal frontend keeps precisely its observation-free family;
alphabet-derived profiles can certify the additional observations. -/
def universalCheck {n : Nat} : Expr n → Bool
  | .replayQuery | .shift _ _ => true
  | .literalQuery _ _ _ _ => false
  | .seq a b | .alt a b => universalCheck a && universalCheck b
  | .star a | .notP a => universalCheck a

theorem capture_universal {n : Nat} (P : List Nat) : ∀ e : Expr n,
    universalCheck e=true → captureCheck P e=true
  | .replayQuery,_ | .shift _ _,_ => rfl
  | .literalQuery _ _ _ _,h => by cases h
  | .seq a b,h | .alt a b,h => Bool.and_eq_true_iff.mpr
      ⟨capture_universal P a (Bool.and_eq_true_iff.mp h).1,capture_universal P b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a,h | .notP a,h => capture_universal P a h

theorem capture_safe {n : Nat} (M : Machine n) (w : List Char) : ∀ e : Expr n,
    (inputSafe e=true → TotalCaptureSafety.Total M w) →
    captureCheck (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e=true
  | .replayQuery,_ | .shift _ _,_ => rfl
  | .literalQuery _ a _ _,h => (ScannerFrontierCertificate.check_actual M w a).mpr (h rfl a)
  | .seq a b,h | .alt a b,h => Bool.and_eq_true_iff.mpr
      ⟨capture_safe M w a (fun ha => h (Bool.or_eq_true_iff.mpr (Or.inl ha))),
       capture_safe M w b (fun hb => h (Bool.or_eq_true_iff.mpr (Or.inr hb)))⟩
  | .star a,h | .notP a,h => capture_safe M w a h

theorem literal_results {n : Nat} (M : Machine n) (alphabet : List Char) (a q : Fin n)
    (L : LiteralPrefixObservation.Labels n) (hc : check M (.literalQuery alphabet a q L)=true)
    (w : List Char) (hCap : captureCheck (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) (.literalQuery alphabet a q L)=true)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (p j : Nat) (h : Aligned x w p j) :
    Results (Aligned x w) (evV g x s T [w] (render (.literalQuery alphabet a q L)) p)
      (evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) (.literalQuery alphabet a q L))) j) := by
  obtain ⟨hq,hc⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hL,ha⟩ := Bool.and_eq_true_iff.mp hc
  have hw := LiteralPrefixObservation.alphabet_of_readable M alphabet a ha w
    ((ScannerFrontierCertificate.check_actual M w a).mp hCap)
  cases hl : L q with
  | none => simp [hl] at hq
  | some u =>
    have he := LiteralPrefixObservation.peek_transfer M alphabet L hL q u hl g g x w s s T T p j hw h
    cases hr : DynamicScannerBinding.resume (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) q <;>
      simpa [render,hl,residual,LiteralPrefixObservation.query,DependentCaptureFilter.render,hr,MExp.failAlways,MExp.andP,evV,Shallot.stripPrefix?] using he

theorem atom_results {n : Nat} (M : Machine n) (q : Fin n)
    (R : ScannerReplayResidual.Labels n) (hc : check M (.shift q R)=true)
    (g : MGrammar) (x w : List Char) (s : Strategy) (T : Table) (p j : Nat)
    (h : Aligned x w p j) :
    Results (Aligned x w) (evV g x s T [w] (render (.shift q R)) p)
      (evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) (.shift q R))) j) := by
  obtain ⟨he,hc⟩ := Bool.and_eq_true_iff.mp hc
  have ha := aligned_replay g x w s T p j h
  cases hs : StatefulScanner.advance M q w with
  | none =>
    have hf := ScannerReplayResidual.replay_unreadable M R q he hc w hs g x s T p j h.2.2
    have hg : evV g x s T [w] (GuardedReplayIteration.step ((R q).getD [])) p=some none := by
      simp only [GuardedReplayIteration.step,evV] at hf ⊢
      split at hf <;> simp_all [MExp.andP,evV]
    simp [render,residual,DynamicScannerBinding.resume_actual,hs,DependentCaptureFilter.render,hg,Results,evV,Shallot.stripPrefix?]
  | some r =>
    have ht := BlockCapture.prefix_rotate g x s T w _ _ (ScannerReplayResidual.actual_rotation M R q he w r hs) p
    rw [evV_seq_ok ha] at ht
    simp only [render,residual,DynamicScannerBinding.resume_actual,hs,DependentCaptureFilter.render]
    cases hb : evV g x s T [w] (.lit ((R q).getD [])) p with
    | none =>
      have hc := ht.symm.trans (evV_seq_none hb)
      rw [hc,GuardedReplayIteration.step,evV_seq_none hb]; trivial
    | some a => cases a with
      | none =>
        have hc := ht.symm.trans (evV_seq_fail hb)
        rw [hc,GuardedReplayIteration.step,evV_seq_fail hb]; trivial
      | some p' =>
        have hp' := (GuardedReplayIteration.literal_length g x s T [w] _ p p' h.1 hb).1
        rw [evV_seq_ok hb] at ht
        cases hw : evV g x s T [w] (.param 0) p' with
        | none =>
          rw [hw] at ht
          simp only [GuardedReplayIteration.step,evV_seq_ok hb,CallLookahead.evV_peek,hw,ht.symm,CallLookahead.peek]
          trivial
        | some a => cases a with
          | none =>
            rw [hw] at ht
            simp only [GuardedReplayIteration.step,evV_seq_ok hb,CallLookahead.evV_peek,hw,ht.symm,CallLookahead.peek]
            trivial
          | some j' =>
            rw [hw] at ht
            simp only [GuardedReplayIteration.step,evV_seq_ok hb,CallLookahead.evV_peek,hw,ht.symm,CallLookahead.peek,Results]
            exact aligned_of_replay g x w s T p' j' hp' hw

/-- A syntax induction transports all control, not just a fixed operand
repeated a predetermined number of times. -/
theorem control_results {n : Nat} (M : Machine n) (g : MGrammar) (x w : List Char)
    (s : Strategy) (T : Table) : ∀ e : Expr n, check M e=true →
    captureCheck (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e=true →
    ∀ p j, Aligned x w p j →
    Results (Aligned x w) (evV g x s T [w] (render e) p)
      (evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j)
  | .replayQuery,_,_,p,j,h => by
    have ha := aligned_replay g x w s T p j h
    simp only [render,CallLookahead.evV_peek,ha,CallLookahead.peek,residual,DependentCaptureFilter.render]
    simpa [evV,Shallot.stripPrefix?,length_sfx x h.2.1,Results] using h
  | .shift q R,hc,_,p,j,h => atom_results M q R hc g x w s T p j h
  | .literalQuery alphabet a q L,hc,hCap,p,j,h => literal_results M alphabet a q L hc w hCap g x s T p j h
  | .seq a b,hc,hCap,p,j,h => by
    exact bind_results (control_results M g x w s T a (Bool.and_eq_true_iff.mp hc).1 (Bool.and_eq_true_iff.mp hCap).1 p j h) _ _
      (fun p j h => control_results M g x w s T b (Bool.and_eq_true_iff.mp hc).2 (Bool.and_eq_true_iff.mp hCap).2 p j h)
  | .alt a b,hc,hCap,p,j,h => by
    exact alt_results (control_results M g x w s T a (Bool.and_eq_true_iff.mp hc).1 (Bool.and_eq_true_iff.mp hCap).1 p j h)
      (control_results M g x w s T b (Bool.and_eq_true_iff.mp hc).2 (Bool.and_eq_true_iff.mp hCap).2 p j h)
  | .notP a,hc,hCap,p,j,h => by
    exact not_results (control_results M g x w s T a hc hCap p j h) p j h
  | .star a,hc,hCap,p,j,h => by
    exact star_results x w _ _ (fun p j h => control_results M g x w s T a hc hCap p j h) p j h

theorem render_independent {n : Nat} (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Table) (E : List (List Char)) : ∀ e : Expr n, ∀ p,
    evV g x s T E (render e) p=evV h x t U E (render e) p
  | .replayQuery,_ | .shift _ _,_ | .literalQuery _ _ _ _,_ => rfl
  | .seq a b,p | .alt a b,p => by
    simp only [render,evV,render_independent g h x s t T U E a p]
    split <;> first | rfl | exact render_independent g h x s t T U E b _
  | .notP a,p => by simp only [render,evV,render_independent g h x s t T U E a p]
  | .star a,p => by
    rw [render,evV_star,evV_star]
    exact evStar_congr p (fun q _ => render_independent g h x s t T U E a q)

theorem header_independent {n : Nat} (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Table) (E : List (List Char)) (e : Expr n) (p : Nat) :
    evV g x s T E (header e) p=evV h x t U E (header e) p := by
  simp only [header,evV,render_independent g h x s t T U E e p]

theorem render_firstOrder {n : Nat} : ∀ e : Expr n, (render e).FirstOrder
  | .shift _ _ => ⟨True.intro,True.intro⟩
  | .replayQuery | .literalQuery _ _ _ _ => True.intro
  | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
  | .star a | .notP a => render_firstOrder a

theorem residual_noHelpers {n : Nat} (P : List Nat) : ∀ e : Expr n,
    DependentCaptureFilter.Valid [] (residual P e)
  | .replayQuery => True.intro
  | .shift q R | .literalQuery _ _ q R => by simp only [residual]; split <;> trivial
  | .seq a b | .alt a b => ⟨residual_noHelpers P a,residual_noHelpers P b⟩
  | .star a | .notP a => residual_noHelpers P a

theorem residual_pure {n : Nat} (P : List Nat) : ∀ e : Expr n,
    ParserPrefixFusion.Pure (DependentCaptureFilter.render (residual P e))
  | .replayQuery => True.intro
  | .shift q R | .literalQuery _ _ q R => by simp only [residual]; split <;> trivial
  | .seq a b | .alt a b => ⟨residual_pure P a,residual_pure P b⟩
  | .star a | .notP a => residual_pure P a

/-- Actual capture alignment is derived from the real argument evaluation
by callers; the only additional input here is a finite syntax check. -/
theorem header_eq {n : Nat} (M : Machine n) (e : Expr n) (hc : check M e=true)
    (g h : MGrammar) (x w : List Char) (s t : Strategy) (T U : Table)
    (p j : Nat) (hpj : Aligned x w p j)
    (hCap : captureCheck (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e=true) :
    evV g x s T [w] (header e) p=
      evV h x t U [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j := by
  have hr := control_results M g x w s T e hc hCap p j hpj
  have he : evV g x s T [w] (header e) p=
      evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j := by
    rcases ha : evV g x s T [w] (render e) p with _ | (_ | p') <;>
      rcases hb : evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j with _ | (_ | j') <;>
      simp only [ha,hb,Results] at hr
    all_goals first | contradiction | skip
    · exact evV_seq_none ha
    · exact evV_seq_fail ha
    · exact (evV_seq_ok ha).trans (aligned_replay g x w s T p' j' hr)
  exact he.trans (ParserPrefixFusion.pure_eval g h x s t T U [w] [w] _ (residual_pure _ e) j)

end Shallot.MacroPeg.CBV.GuardedReplayControl
