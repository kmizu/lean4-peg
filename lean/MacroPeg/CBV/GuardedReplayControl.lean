import MacroPeg.CBV.GuardedReplayRotation
import MacroPeg.CBV.ScannerReplayResidual
import MacroPeg.CBV.DependentCaptureFilter

namespace Shallot.MacroPeg.CBV.GuardedReplayControl
open ClockFreezing (Table)
open StatefulScanner (Machine)

/-- Each atom preserves the same retained value at its new origin.
PEG control may choose different atoms on different iterations. -/
inductive Expr (n : Nat) where
  | shift (q : Fin n) (R : ScannerReplayResidual.Labels n)
  | seq (a b : Expr n)
  | alt (a b : Expr n)
  | notP (a : Expr n)
  | star (a : Expr n)

def render {n : Nat} : Expr n → MExp
  | .shift q R => GuardedReplayIteration.step ((R q).getD [])
  | .seq a b => .seq (render a) (render b)
  | .alt a b => .alt (render a) (render b)
  | .notP a => .notP (render a)
  | .star a => .star (render a)

def header {n : Nat} (e : Expr n) : MExp := .seq (render e) (.param 0)

def check {n : Nat} (M : Machine n) : Expr n → Bool
  | .shift q R => ScannerReplayResidual.entryCheck M R q && ScannerReplayResidual.completeCheck M R
  | .seq a b | .alt a b => check M a && check M b
  | .notP a | .star a => check M a

def residual {n : Nat} (P : List Nat) : Expr n → DependentCaptureFilter.Expr
  | .shift q R => match DynamicScannerBinding.resume P q with
    | none => .notP (.lit [])
    | some r => .lit ((R r).getD [])
  | .seq a b => .seq (residual P a) (residual P b)
  | .alt a b => .alt (residual P a) (residual P b)
  | .notP a => .notP (residual P a)
  | .star a => .star (residual P a)

def Aligned (x w : List Char) (p q : Nat) : Prop :=
  p≤x.length ∧ q≤x.length ∧ sfx x p=w++sfx x q

def Results (R : Nat → Nat → Prop) : Option (Option Nat) → Option (Option Nat) → Prop
  | none,none | some none,some none => True
  | some (some p),some (some q) => R p q
  | _,_ => False

def bindValue (a : Option (Option Nat)) (f : Nat → Option (Option Nat)) :=
  match a with | some (some p) => f p | other => other

def altValue (a b : Option (Option Nat)) :=
  match a with | some none => b | other => other

def notValue (p : Nat) (a : Option (Option Nat)) :=
  match a with | some (some _) => some none | some none => some (some p) | none => none

theorem bind_results {R : Nat → Nat → Prop} {a b : Option (Option Nat)}
    (h : Results R a b) (F G : Nat → Option (Option Nat))
    (hF : ∀ p q, R p q → Results R (F p) (G q)) :
    Results R (bindValue a F) (bindValue b G) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,bindValue]

theorem alt_results {R : Nat → Nat → Prop} {a b c d : Option (Option Nat)}
    (h : Results R a b) (k : Results R c d) : Results R (altValue a c) (altValue b d) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,altValue]

theorem not_results {R : Nat → Nat → Prop} {a b : Option (Option Nat)}
    (h : Results R a b) (p q : Nat) (hpq : R p q) : Results R (notValue p a) (notValue q b) := by
  rcases a with _ | (_ | a) <;> rcases b with _ | (_ | b) <;> simp_all [Results,notValue]

theorem aligned_length {x w : List Char} {p q : Nat} (h : Aligned x w p q) : p=w.length+q := by
  have hl := congrArg List.length h.2.2
  rw [List.length_append,length_sfx x h.1,length_sfx x h.2.1] at hl
  exact hl

theorem aligned_replay (g : MGrammar) (x w : List Char) (s : Strategy) (T : Table)
    (p q : Nat) (h : Aligned x w p q) : evV g x s T [w] (.param 0) p=some (some q) := by
  simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr h.2.2,length_sfx x h.2.1]

theorem aligned_of_replay (g : MGrammar) (x w : List Char) (s : Strategy) (T : Table)
    (p q : Nat) (hp : p≤x.length) (hv : evV g x s T [w] (.param 0) p=some (some q)) :
    Aligned x w p q := by
  obtain ⟨hq,he⟩ := SequenceArguments.success_prefix g x s T [w] (.param 0) True.intro p q hp hv
  have hw : w=pre x p q := by
    simpa [WordArguments.value] using WordArguments.value_of_success g x s T [w] (.param 0) True.intro p q hp hv
  exact ⟨hp,hq,hw ▸ he⟩

/-- Lifting a step relation to greedy partial repetition uses the actual
capture alignment to preserve strict decrease, including nullable divergence. -/
theorem star_results (x w : List Char) (F G : Nat → Option (Option Nat))
    (hStep : ∀ p q, Aligned x w p q → Results (Aligned x w) (F p) (G q)) :
    ∀ p q, Aligned x w p q → Results (Aligned x w) (evStar F p) (evStar G q) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro q h
    have hr := hStep p q h
    cases hf : F p with
    | none =>
      cases hg : G q <;> simp [hf,hg,Results] at hr
      rw [evStar_none hf,evStar_none hg]; trivial
    | some a => cases a with
      | none =>
        cases hg : G q with
        | none => simp [hf,hg,Results] at hr
        | some b => cases b with
          | some z => simp [hf,hg,Results] at hr
          | none => rw [evStar_fail hf,evStar_fail hg]; exact h
      | some p' =>
        cases hg : G q with
        | none => simp [hf,hg,Results] at hr
        | some b => cases b with
          | none => simp [hf,hg,Results] at hr
          | some q' =>
            have hr : Aligned x w p' q' := by simpa [hf,hg,Results] using hr
            have hlen := aligned_length h
            have hlen' := aligned_length hr
            by_cases hd : p'<p
            · rw [evStar_ok hf hd,evStar_ok hg (by omega)]
              exact ih p' hd q' hr
            · rw [evStar_stuck hf hd,evStar_stuck hg (by omega)]
              trivial

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
    (s : Strategy) (T : Table) : ∀ e : Expr n, check M e=true → ∀ p j, Aligned x w p j →
    Results (Aligned x w) (evV g x s T [w] (render e) p)
      (evV g x s T [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j)
  | .shift q R,hc,p,j,h => atom_results M q R hc g x w s T p j h
  | .seq a b,hc,p,j,h => by
    exact bind_results (control_results M g x w s T a (Bool.and_eq_true_iff.mp hc).1 p j h) _ _
      (fun p j h => control_results M g x w s T b (Bool.and_eq_true_iff.mp hc).2 p j h)
  | .alt a b,hc,p,j,h => by
    exact alt_results (control_results M g x w s T a (Bool.and_eq_true_iff.mp hc).1 p j h)
      (control_results M g x w s T b (Bool.and_eq_true_iff.mp hc).2 p j h)
  | .notP a,hc,p,j,h => by
    exact not_results (control_results M g x w s T a hc p j h) p j h
  | .star a,hc,p,j,h => by
    exact star_results x w _ _ (fun p j h => control_results M g x w s T a hc p j h) p j h

theorem render_independent {n : Nat} (g h : MGrammar) (x : List Char) (s t : Strategy)
    (T U : Table) (E : List (List Char)) : ∀ e : Expr n, ∀ p,
    evV g x s T E (render e) p=evV h x t U E (render e) p
  | .shift _ _,_ => rfl
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
  | .seq a b | .alt a b => ⟨render_firstOrder a,render_firstOrder b⟩
  | .star a | .notP a => render_firstOrder a

theorem residual_noHelpers {n : Nat} (P : List Nat) : ∀ e : Expr n,
    DependentCaptureFilter.Valid [] (residual P e)
  | .shift q R => by simp only [residual]; split <;> trivial
  | .seq a b | .alt a b => ⟨residual_noHelpers P a,residual_noHelpers P b⟩
  | .star a | .notP a => residual_noHelpers P a

theorem residual_pure {n : Nat} (P : List Nat) : ∀ e : Expr n,
    ParserPrefixFusion.Pure (DependentCaptureFilter.render (residual P e))
  | .shift q R => by simp only [residual]; split <;> trivial
  | .seq a b | .alt a b => ⟨residual_pure P a,residual_pure P b⟩
  | .star a | .notP a => residual_pure P a

/-- Actual capture alignment is derived from the real argument evaluation
by callers; the only additional input here is a finite syntax check. -/
theorem header_eq {n : Nat} (M : Machine n) (e : Expr n) (hc : check M e=true)
    (g h : MGrammar) (x w : List Char) (s t : Strategy) (T U : Table)
    (p j : Nat) (hpj : Aligned x w p j) :
    evV g x s T [w] (header e) p=
      evV h x t U [w] (DependentCaptureFilter.render (residual (CaptureTransitionProfile.profile (DynamicScannerCapture.observer M) w) e)) j := by
  have hr := control_results M g x w s T e hc p j hpj
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
