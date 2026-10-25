import MacroPeg.CBV.ParReturnEffects
import MacroPeg.CBV.StablePar

namespace Shallot.MacroPeg.CBV.EndpointSupport

abbrev zero (g : MGrammar) (e : MExp) := decide (ParReturnEffects.emptyEffect g e ≠ .any)

/-- Successful runs must have the same endpoint as a common core. Queries
are retained in the program; this certificate does not assert equal failure
or termination behavior, and must not be used to erase their execution. -/
def check (g : MGrammar) : MExp → MExp → Bool
  | e,c => if MExp.beqE e c then true else
    match e with
    | .seq a b => (zero g a && check g b c) || (check g a c && zero g b) ||
        (match c with | .seq u v => check g a u && check g b v | _ => false)
    | .alt a b => check g a c && check g b c
    | .chr _ | .range _ _ => MExp.beqE c .any
    | _ => MExp.beqE c .eps && zero g e

/-- The successful core run uses the same actual source table and input.
No equivalence or successful evaluation of the removed queries is assumed. -/
theorem success (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (k : Nat)
    (E : List (List Char)) : ∀ e c, e.FirstOrder → check g e c=true → ∀ p q, p≤x.length →
      evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=some (some q) →
      evV g x .callByValuePar (tblV g x .callByValuePar k) E c p=some (some q) := by
  intro e c he hc p q hp hs
  unfold check at hc
  split at hc
  · rename_i hsame
    have hsame := (MExp.beqE_iff e c).mp hsame
    simpa only [←hsame] using hs
  · cases e with
    | seq a b =>
      cases ha : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
      | none => rw [evV_seq_none ha] at hs; cases hs
      | some v => cases v with
        | none => rw [evV_seq_fail ha] at hs; cases hs
        | some j =>
          rw [evV_seq_ok ha] at hs
          have hj := evV_ok (tblV_ok g x .callByValuePar k) a p hp j ha
          rcases Bool.or_eq_true_iff.mp hc with hab|hseq
          · rcases Bool.or_eq_true_iff.mp hab with hbefore|hafter
            · obtain ⟨hz,hb⟩ := Bool.and_eq_true_iff.mp hbefore
              have hzero := ParReturnEffects.zero_of_not_any _ (of_decide_eq_true hz) p j
                (ParReturnEffects.empty_success g hg a he.1 x k E p j hp ha)
              subst j
              exact success g hg x k E b c he.2 hb p q hp hs
            · obtain ⟨hc,hz⟩ := Bool.and_eq_true_iff.mp hafter
              have hzero := ParReturnEffects.zero_of_not_any _ (of_decide_eq_true hz) j q
                (ParReturnEffects.empty_success g hg b he.2 x k E j q hj hs)
              subst q
              exact success g hg x k E a c he.1 hc p j hp ha
          · cases c with
            | seq u v =>
              obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp hseq
              rw [evV_seq_ok (success g hg x k E a u he.1 hu p j hp ha)]
              exact success g hg x k E b v he.2 hv j q hj hs
            | _ => cases hseq
    | alt a b =>
      obtain ⟨hcA,hcB⟩ := Bool.and_eq_true_iff.mp hc
      cases ha : evV g x .callByValuePar (tblV g x .callByValuePar k) E a p with
      | none => rw [evV_alt_none ha] at hs; cases hs
      | some v => cases v with
        | none =>
          rw [evV_alt_fail ha] at hs
          exact success g hg x k E b c he.2 hcB p q hp hs
        | some j =>
          rw [evV_alt_ok ha] at hs
          have hq : j=q := by simpa only [Option.some.injEq] using hs
          subst j
          exact success g hg x k E a c he.1 hcA p q hp ha
    | chr ch =>
      have hcore := (MExp.beqE_iff c .any).mp hc
      subst c
      cases hx : sfx x p with
      | nil => simp [evV,hx] at hs
      | cons d rest =>
        by_cases hcd : Shallot.beqChar ch d=true
        · simpa [evV,hx,hcd] using hs
        · simp [evV,hx,hcd] at hs
    | range lo hi =>
      have hcore := (MExp.beqE_iff c .any).mp hc
      subst c
      cases hx : sfx x p with
      | nil => simp [evV,hx] at hs
      | cons d rest =>
        by_cases hcd : (Shallot.leChar lo d && Shallot.leChar d hi)=true
        · simpa [evV,hx,hcd] using hs
        · simp [evV,hx,hcd] at hs
    | _ =>
      obtain ⟨hc,hz⟩ := Bool.and_eq_true_iff.mp hc
      have hcore := (MExp.beqE_iff c .eps).mp hc
      subst c
      have hq := ParReturnEffects.zero_of_not_any _ (of_decide_eq_true hz) p q
        (ParReturnEffects.empty_success g hg _ he x k E p q hp hs)
      subst q
      rfl
termination_by e _ _ _ _ _ _ _ => sizeOf e

theorem agree (g : MGrammar) (hg : g.FirstOrder) (a d c : MExp) (ha : a.FirstOrder) (hd : d.FirstOrder)
    (hc : ReplayFallbackFusion.Closed c) (hA : check g a c=true) (hD : check g d c=true)
    (x : List Char) (ka kd : Nat) (E F : List (List Char)) (p qa qd : Nat) (hp : p≤x.length)
    (ea : evV g x .callByValuePar (tblV g x .callByValuePar ka) E a p=some (some qa))
    (ed : evV g x .callByValuePar (tblV g x .callByValuePar kd) F d p=some (some qd)) : qa=qd := by
  have ca := success g hg x ka E a c ha hA p qa hp ea
  have cd := success g hg x kd F d c hd hD p qd hp ed
  have sa := (StablePar.eval_le g x ka E c p hp).eq_of_some ca
  have sd := (StablePar.eval_le g x kd F c p hp).eq_of_some cd
  rw [ReplayFallbackFusion.closed_env _ _ _ _ c hc E p] at sa
  rw [ReplayFallbackFusion.closed_env _ _ _ _ c hc F p,sa] at sd
  simpa only [Option.some.injEq] using sd

end Shallot.MacroPeg.CBV.EndpointSupport
