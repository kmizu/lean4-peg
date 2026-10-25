import MacroPeg.CBV.ProducedPrefixCompiler

namespace Shallot.MacroPeg.CBV.ProducedPrefixEvaluation
open ProducedPrefixCompiler
open ReplayControlFusion (Part Plan)
open GuardedReplayControl (Aligned)

abbrev sourceTable (ps : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (source ps es) x .callByValuePar k
abbrev normalizedTable (ps : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (normalized ps es) x .callByValuePar k

def lexical (D : MExp) (x : List Char) (p : Nat) := evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [] D p

def Captured (D : MExp) (x w : List Char) (p j : Nat) := Aligned x w p j ∧ lexical D x p=some (some j)

def Rows (ps : List Part) (es : List Entry) (x : List Char) (k : Nat) : Prop :=
  ∀ (i : Nat) (e : Entry), es[i]?=some e → match e with
    | .produced D _ => ∀ w p j, Captured D x w p j →
        valAt (sourceTable ps es x k i [w]) p=valAt (normalizedTable ps es x k i [w]) p
    | _ => ∀ W p, p≤x.length → valAt (sourceTable ps es x k i W) p=valAt (normalizedTable ps es x k i W) p

theorem producer_eval (ps : List Part) (es : List Entry) (x : List Char) (k : Nat)
    (E : List (List Char)) (D : MExp) (hD : ParserPrefixFusion.Pure D) (p : Nat) :
    evV (source ps es) x .callByValuePar (sourceTable ps es x k) E D p=lexical D x p :=
  ParserPrefixFusion.pure_eval _ _ _ _ _ _ _ _ _ D hD p

theorem evaluator (parts : List Part) (es : List Entry) (hg : (source parts es).FirstOrder) (hv : check parts es=true)
    (x : List Char) (k : Nat) (hRows : Rows parts es x k) (E : List (List Char)) : ∀ e, e.FirstOrder → conforms es e=true → ∀ p, p≤x.length →
    evV (source parts es) x .callByValuePar (sourceTable parts es x k) E e p=
      evV (normalized parts es) x .callByValuePar (normalizedTable parts es x k) E e p
  | .call i [a],h,hc,p,hp => by
    have hca := (Bool.and_eq_true_iff.mp hc).1
    have hci := (Bool.and_eq_true_iff.mp hc).2
    cases hr : es[i]? with
    | none => simp [evV,source_rule,normalized_rule parts es hv,hr]
    | some e =>
      have hs : ruleAtM (source parts es).rules i=some ⟨1,body parts e⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (normalized parts es).rules i=some ⟨1,normalizedBody parts e⟩ := by rw [normalized_rule _ _ hv,hr]; rfl
      rw [evV_call_par hs rfl (by decide),evV_call_par ht rfl (by decide)]
      have heq := evaluator parts es hg hv x k hRows E a h.1 hca p hp
      simp only [evParArgs,←heq]
      cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some j =>
          obtain ⟨hj,hprefix⟩ := ReplayFusion.success_prefix (tblV_sound hg (by decide) k) E a h.1 p j hp ha
          cases e with
          | growth r => exact hRows i (.growth r) hr [pre x p j] p hp
          | origin P => exact hRows i (.origin P) hr [pre x p j] p hp
          | produced D B =>
            have had : a=D := (MExp.beqE_iff _ _).mp (by simpa only [callCheck,hr] using hci)
            have hD := (checked parts es hv).2.1 (.produced D B) (List.mem_of_getElem? hr)
            have hlex : lexical D x p=some (some j) := by
              rw [←producer_eval parts es x k E D hD p]
              simpa only [had] using ha
            exact hRows i (.produced D B) hr (pre x p j) p j ⟨⟨hp,hj,hprefix⟩,hlex⟩
  | .call i [],_,_,p,_ | .call i (_::_::_),_,_,p,_ => by
    cases hr : es[i]? <;> simp [evV,source_rule,normalized_rule parts es hv,hr]
  | .seq a b,h,hc,p,hp => by
    have he := evaluator parts es hg hv x k hRows E a h.1 (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
    | none => simp only [evV_seq_none ha,evV_seq_none (he.symm.trans ha)]
    | some v => cases v with
      | none => simp only [evV_seq_fail ha,evV_seq_fail (he.symm.trans ha)]
      | some j =>
        simp only [evV_seq_ok ha,evV_seq_ok (he.symm.trans ha)]
        exact evaluator parts es hg hv x k hRows E b h.2 (Bool.and_eq_true_iff.mp hc).2 j (evV_ok (tblV_ok (source parts es) x .callByValuePar k) a p hp j ha)
  | .alt a b,h,hc,p,hp => by
    have he := evaluator parts es hg hv x k hRows E a h.1 (Bool.and_eq_true_iff.mp hc).1 p hp
    cases ha : evV (source parts es) x .callByValuePar (sourceTable parts es x k) E a p with
    | none => simp only [evV_alt_none ha,evV_alt_none (he.symm.trans ha)]
    | some v => cases v with
      | none =>
        simp only [evV_alt_fail ha,evV_alt_fail (he.symm.trans ha)]
        exact evaluator parts es hg hv x k hRows E b h.2 (Bool.and_eq_true_iff.mp hc).2 p hp
      | some j => simp only [evV_alt_ok ha,evV_alt_ok (he.symm.trans ha)]
  | .notP a,h,hc,p,hp => by
    simp only [evV,evaluator parts es hg hv x k hRows E a h hc p hp]
  | .star a,h,hc,p,hp => by
    simp only [evV_star]
    exact evStar_congr p (fun q hq => evaluator parts es hg hv x k hRows E a h hc q (Nat.le_trans hq hp))
  | .eps,_,_,_,_ | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_ | .lit _,_,_,_,_ | .param _,_,_,_,_ => rfl
  | .dbg _,h,_,_,_ | .lam _ _,h,_,_,_ | .callParam _ _,h,_,_,_ | .invoke _ _ _,h,_,_,_ => False.elim h


end Shallot.MacroPeg.CBV.ProducedPrefixEvaluation
