import MacroPeg.CBV.SemanticBodyRewrite
import MacroPeg.CBV.DependentCaptureFilter

/-! Body rewrites need only hold on values a real Par call can capture.
This origin invariant is derived from actual argument evaluation, including
recursive arguments, rather than supplied as a successful-row certificate. -/
namespace Shallot.MacroPeg.CBV.CaptureOriginRewrite
open ClockFreezing (Table)

def Captured (x : List Char) (E : List (List Char)) (p : Nat) : Prop :=
  ∀ w∈E, w.IsPrefix (sfx x p)

def Rows (x : List Char) (T U : Table) : Prop :=
  ∀ i E p, p≤x.length → Captured x E p → valAt (T i E) p=valAt (U i E) p

mutual
  theorem evaluator (g h : MGrammar) (ha : SemanticBodyRewrite.ArityEq g h) (x : List Char)
      (T U : Table) (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T) (hRows : Rows x T U) :
      ∀ (e : MExp), e.FirstOrder → ∀ E p, p≤x.length →
        evV g x .callByValuePar T E e p=evV h x .callByValuePar U E e p
    | .call i args,he,E,p,hp => by
      have hi := ha i
      cases hg : ruleAtM g.rules i with
      | none =>
        cases hh : ruleAtM h.rules i with
        | none => simp only [evV,hg,hh]
        | some r => simp [hg,hh] at hi
      | some r =>
        cases hh : ruleAtM h.rules i with
        | none => simp [hg,hh] at hi
        | some r' =>
          have harity : r.arity=r'.arity := by simpa [hg,hh] using hi
          by_cases hn : r.arity=args.length
          · rw [evV_call_par hg hn (by decide),evV_call_par hh (harity.symm.trans hn) (by decide)]
            have hm := arguments g h ha x T U hT hOk hRows args he E p hp
            rw [←hm.1]
            cases hv : evParArgs g x .callByValuePar T E args p with
            | none => rfl
            | some v => cases v with
              | none => rfl
              | some W => exact hRows i W p hp (hm.2 W hv)
          · have hn' : r'.arity≠args.length := by omega
            simp only [evV,hg,hh,if_neg hn,if_neg hn']
    | .seq a b,he,E,p,hp => by
      have hh := evaluator g h ha x T U hT hOk hRows a he.1 E p hp
      cases hv : evV g x .callByValuePar T E a p with
      | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
      | some v => cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
          exact evaluator g h ha x T U hT hOk hRows b he.2 E q (evV_ok hOk a p hp q hv)
    | .alt a b,he,E,p,hp => by
      have hh := evaluator g h ha x T U hT hOk hRows a he.1 E p hp
      cases hv : evV g x .callByValuePar T E a p with
      | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
      | some v => cases v with
        | none =>
          rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]
          exact evaluator g h ha x T U hT hOk hRows b he.2 E p hp
        | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
    | .star a,he,E,p,hp => by
      rw [evV_star,evV_star]
      exact evStar_congr p (fun q hq => evaluator g h ha x T U hT hOk hRows a he E q (by omega))
    | .notP a,he,E,p,hp => by
      simp only [evV,evaluator g h ha x T U hT hOk hRows a he E p hp]
    | .eps,_,_,_,_ | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_
    | .lit _,_,_,_,_ | .param _,_,_,_,_ => rfl
    | .dbg _,he,_,_,_ | .lam _ _,he,_,_,_ | .callParam _ _,he,_,_,_
    | .invoke _ _ _,he,_,_,_ => False.elim he
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega

  theorem arguments (g h : MGrammar) (ha : SemanticBodyRewrite.ArityEq g h) (x : List Char)
      (T U : Table) (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T) (hRows : Rows x T U) :
      ∀ args, MExp.FirstOrderArgs args → ∀ E p, p≤x.length →
      evParArgs g x .callByValuePar T E args p=evParArgs h x .callByValuePar U E args p ∧
      ∀ W, evParArgs g x .callByValuePar T E args p=some (some W) → Captured x W p
    | [],_,E,p,_ => ⟨rfl,by intro W hw; cases hw; simp [Captured]⟩
    | a::args,he,E,p,hp => by
      have hh := evaluator g h ha x T U hT hOk hRows a he.1 E p hp
      have ht := arguments g h ha x T U hT hOk hRows args he.2 E p hp
      constructor
      · simp only [evParArgs,hh,ht.1]
      · intro W hw
        cases hv : evV g x .callByValuePar T E a p with
        | none => simp [evParArgs,hv] at hw
        | some v => cases v with
          | none => simp [evParArgs,hv] at hw
          | some q =>
            cases hs : evParArgs g x .callByValuePar T E args p with
            | none => simp [evParArgs,hv,hs] at hw
            | some v => cases v with
              | none => simp [evParArgs,hv,hs] at hw
              | some ws =>
                have heq : W=pre x p q::ws := by simpa [evParArgs,hv,hs] using hw.symm
                subst W
                have hpref := (ReplayFusion.success_prefix hT E a he.1 p q hp hv).2
                intro w hm
                rcases List.mem_cons.mp hm with rfl | hm
                · exact ⟨sfx x q,hpref.symm⟩
                · exact ht.2 ws hs w hm
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

/-- This relation restricts the local rewrite to actual common-origin
prefix values. The physical table theorem below discharges reachability. -/
def Related (g h : MGrammar) : Prop := ∀ i,
  match ruleAtM g.rules i,ruleAtM h.rules i with
  | none,none => True
  | some a,some b => a.arity=b.arity ∧ ∀ x T E p, p≤x.length → Captured x E p →
      evV g x .callByValuePar T E a.body p=evV g x .callByValuePar T E b.body p
  | _,_ => False

theorem arities {g h : MGrammar} (hr : Related g h) : SemanticBodyRewrite.ArityEq g h := by
  intro i
  have hi := hr i
  cases hg : ruleAtM g.rules i with
  | none => cases hh : ruleAtM h.rules i with
    | none => rfl
    | some b => simp [hg,hh] at hi
  | some a => cases hh : ruleAtM h.rules i with
    | none => simp [hg,hh] at hi
    | some b =>
      simp only [hg,hh] at hi
      exact congrArg some hi.1

theorem tables_rows {g h : MGrammar} (hr : Related g h) (hg : g.FirstOrder) (hh : h.FirstOrder)
    (x : List Char) (k : Nat) : Rows x (tblV g x .callByValuePar k) (tblV h x .callByValuePar k) := by
  induction k with
  | zero => intro i E p hp hE; rfl
  | succ k ih =>
    intro i E p hp hE
    have hi := hr i
    cases hs : ruleAtM g.rules i with
    | none =>
      cases ht : ruleAtM h.rules i with
      | none => simp [tblV,hs,ht,valAt]
      | some b => simp [hs,ht] at hi
    | some a =>
      cases ht : ruleAtM h.rules i with
      | none => simp [hs,ht] at hi
      | some b =>
        have hbody := (show a.arity=b.arity ∧ _ from by simpa [hs,ht] using hi).2
        rw [valAt_tblV_succ hs E hp,valAt_tblV_succ ht E hp]
        exact (hbody x (tblV g x .callByValuePar k) E p hp hE).trans
          (evaluator g h (arities hr) x _ _ (tblV_sound hg (by decide) k) (tblV_ok g x .callByValuePar k) ih
            b.body (hh b (ruleAtM_mem ht)) E p hp)

theorem physical {g h : MGrammar} (hr : Related g h) (hg : g.FirstOrder) (hh : h.FirstOrder)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E e p=
      evV h x .callByValuePar (tblV h x .callByValuePar k) E e p :=
  evaluator g h (arities hr) x _ _ (tblV_sound hg (by decide) k) (tblV_ok g x .callByValuePar k)
    (tables_rows hr hg hh x k) e he E p hp

theorem observations {g h : MGrammar} (hr : Related g h) (hg : g.FirstOrder) (hh : h.FirstOrder)
    (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs h .callByValuePar e x rest := by
  rw [←decideObsV_iff hg (by decide) he,←decideObsV_iff hh (by decide) he]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq g h x .callByValuePar .callByValuePar e e
    (fun k => physical hr hg hh x k [] e he x.length (Nat.le_refl _))]

end Shallot.MacroPeg.CBV.CaptureOriginRewrite
