import MacroPeg.CBV.EndpointSupport
import MacroPeg.CBV.ExpressionContext

namespace Shallot.MacroPeg.CBV.ProducerArgumentRewrite
open ClockFreezing (Table)

def guarded (i : Nat) (d a : MExp) := MExp.seq (.andP a) (.call i [d])

theorem call_ok (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (har : r.arity=1)
    (a : MExp) (p j : Nat) (ha : evV g x .callByValuePar T E a p=some (some j)) :
    evV g x .callByValuePar T E (.call i [a]) p=valAt (T i [pre x p j]) p := by
  rw [evV_call_par hr (by simpa using har) (by decide)]
  simp only [evParArgs,ha]

theorem argument (g : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (htu : TLeV T U) (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) (har : r.arity=1)
    (a b : MExp) (p : Nat)
    (hab : RLe (evV g x .callByValuePar T E a p) (evV g x .callByValuePar U E b p)) :
    RLe (evV g x .callByValuePar T E (.call i [a]) p) (evV g x .callByValuePar U E (.call i [b]) p) := by
  rw [evV_call_par hr (by simpa using har) (by decide),evV_call_par hr (by simpa using har) (by decide)]
  simp only [evParArgs]
  cases ha : evV g x .callByValuePar T E a p with
  | none => exact Or.inl rfl
  | some v =>
    have hb := hab.eq_of_some ha
    cases v with
    | none => simp only [hb]; exact RLe.refl _
    | some j => simp only [hb]; exact htu i [pre x p j] p

/-- Replacing a producer argument retains its original evaluation order.
The prefix itself is still evaluated by the actual original callee. -/
theorem forward (g : MGrammar) (hg : g.FirstOrder) (i : Nat) (d b c a : MExp)
    (hr : ruleAtM g.rules i=some ⟨1,.seq d b⟩) (hd : ReplayFallbackFusion.Closed d)
    (hc : ReplayFallbackFusion.Closed c) (ha : a.FirstOrder)
    (hA : EndpointSupport.check g a c=true) (hD : EndpointSupport.check g d c=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call i [a]) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar k) E (guarded i d a) p) := by
  have hdFO := ReplayFallbackFusion.closed_firstOrder d hd
  cases ea : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
  | none =>
    rw [evV_call_par hr rfl (by decide),evPar_cons_none ea]
    exact Or.inl rfl
  | some v => cases v with
    | none =>
      have hguard : evV g x .callByValuePar (tblV g x .callByValuePar k) E (.andP a) p=some none := by
        rw [CallLookahead.evV_peek,ea]; rfl
      simp only [guarded,evV_seq_fail hguard]
      rw [evV_call_par hr rfl (by decide),evPar_cons_fail ea]
      exact RLe.refl _
    | some j =>
      have hguard : evV g x .callByValuePar (tblV g x .callByValuePar k) E (.andP a) p=some (some p) := by
        rw [CallLookahead.evV_peek,ea]; rfl
      simp only [guarded,evV_seq_ok hguard]
      rw [call_ok g x _ E i _ hr rfl a p j ea]
      cases k with
      | zero => exact Or.inl rfl
      | succ k =>
        rw [valAt_tblV_succ hr [pre x p j] hp]
        cases ed : evV g x .callByValuePar (tblV g x .callByValuePar k) [pre x p j] d p with
        | none => rw [evV_seq_none ed]; exact Or.inl rfl
        | some v =>
          have high := evV_lift (g := g) (s := .callByValuePar) (E := [pre x p j]) (by omega : k≤k+1) ed
          rw [ReplayFallbackFusion.closed_env _ _ _ _ d hd [pre x p j] p] at high
          have heD : evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E d p=some v := by
            rw [ReplayFallbackFusion.closed_env _ _ _ _ d hd E p]; exact high
          cases v with
          | none =>
            rw [evV_seq_fail ed,evV_call_par hr rfl (by decide),evPar_cons_fail heD]
            exact RLe.refl _
          | some q =>
            have hq := EndpointSupport.agree g hg a d c ha hdFO hc hA hD x (k+1) k E [pre x p j] p j q hp ea ed
            subst q
            rw [call_ok g x _ E i _ hr rfl d p j heD,valAt_tblV_succ hr [pre x p j] hp]
            exact RLe.refl _

/-- A failed canonical argument may expose the original prefix's failure
one call round earlier. Spending one original round is sufficient. -/
theorem backward (g : MGrammar) (hg : g.FirstOrder) (i : Nat) (d b c a : MExp)
    (hr : ruleAtM g.rules i=some ⟨1,.seq d b⟩) (hd : ReplayFallbackFusion.Closed d)
    (hc : ReplayFallbackFusion.Closed c) (ha : a.FirstOrder)
    (hA : EndpointSupport.check g a c=true) (hD : EndpointSupport.check g d c=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (tblV g x .callByValuePar k) E (guarded i d a) p)
      (evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E (.call i [a]) p) := by
  have hdFO := ReplayFallbackFusion.closed_firstOrder d hd
  simp only [guarded]
  change RLe (match evV g x .callByValuePar (tblV g x .callByValuePar k) E (.andP a) p with
    | some (some j) => evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call i [d]) j
    | r => r) _
  rw [CallLookahead.evV_peek]
  cases ea : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
  | none => exact Or.inl rfl
  | some v =>
    have high := evV_lift (g := g) (s := .callByValuePar) (E := E) (by omega : k≤k+1) ea
    cases v with
    | none =>
      simp only [CallLookahead.peek]
      rw [evV_call_par hr rfl (by decide),evPar_cons_fail high]
      exact RLe.refl _
    | some j =>
      simp only [CallLookahead.peek]
      cases ed : evV g x .callByValuePar (tblV g x .callByValuePar k) E d p with
      | none => rw [evV_call_par hr rfl (by decide),evPar_cons_none ed]; exact Or.inl rfl
      | some v => cases v with
        | none =>
          have dbody : evV g x .callByValuePar (tblV g x .callByValuePar k) [pre x p j] d p=some none := by
            rw [ReplayFallbackFusion.closed_env _ _ _ _ d hd [pre x p j] p]
            rwa [ReplayFallbackFusion.closed_env _ _ _ _ d hd E p] at ed
          rw [evV_call_par hr rfl (by decide),evPar_cons_fail ed,
            call_ok g x _ E i _ hr rfl a p j high,valAt_tblV_succ hr [pre x p j] hp,evV_seq_fail dbody]
          exact RLe.refl _
        | some q =>
          have hq := EndpointSupport.agree g hg a d c ha hdFO hc hA hD x k k E E p j q hp ea ed
          subst q
          rw [call_ok g x _ E i _ hr rfl d p j ed,call_ok g x _ E i _ hr rfl a p j high]
          exact tblV_step g x .callByValuePar k i [pre x p j] p

end Shallot.MacroPeg.CBV.ProducerArgumentRewrite
