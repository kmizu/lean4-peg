import MacroPeg.CBV.GuardedPairSyntax
import MacroPeg.CBV.ExpressionContext

namespace Shallot.MacroPeg.CBV.GuardedPairSimulation
open GuardedPairSyntax
open MixedScannerPairFusion (Entry arity)
open ScannerFrontier
open ClockFreezing (Table)

def values (r : Entry) (x : List Char) (p : Nat) : List (List Char) := match r.pairing with
  | none => []
  | some (A,B) => restore (firstStops A B (sfx x p)) (pre x p (commonPos A B x p))
      (pre x (commonPos A B x p) (finalPos A B x p))

theorem source_call (es : List Entry) (qs : List MExp) (x : List Char) (T : Table) (E : List (List Char))
    (i : Nat) (r : Entry) (hr : es[i]?=some r) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar es qs) x .callByValuePar T E (render es true (.call i [])) p=valAt (T i (values r x p)) p := by
  have hs : ruleAtM (parGrammar es qs).rules i=some (sourceRule es qs i r) := by rw [par_rule,hr]; rfl
  cases hc : r.pairing with
  | none => simp [render,hr,hc,evV,hs,sourceRule,arity,evParArgs,values]
  | some pair =>
    obtain ⟨A,B⟩ := pair
    simp only [render,hr,hc,if_true]
    rw [evV_call_par hs (by simp [sourceRule,arity,hc]) (by decide),parallel_arguments _ x .callByValuePar T E A B p hp]
    simp only [values,hc]

theorem target_call (es : List Entry) (qs : List MExp) (x : List Char) (U : Table) (E : List (List Char))
    (i : Nat) (r : Entry) (hr : es[i]?=some r) (p : Nat) :
    evV (seqGrammar es qs) x .callByValueSeq U E (render es false (.call i [])) p=valAt (U (3*i) []) p := by
  have ht : ruleAtM (seqGrammar es qs).rules (3*i)=some (header es qs i r) := by
    simpa only [Nat.add_zero,hr,Option.map_some,slot,if_true] using seq_rule es qs i 0 (by omega)
  simp only [render,hr,Bool.false_eq_true,if_false]
  rw [evV_call_seq ht rfl]
  rfl

/-- Structural refinement works in either direction between the two
renderings, independently of how call rows will be established. -/
theorem evaluator (es : List Entry) (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (a b : Bool) (hok : OkTV x.length T)
    (calls : ∀ i E p, p≤x.length → RLe (evV g x s T E (render es a (.call i [])) p)
      (evV h x t U E (render es b (.call i [])) p)) :
    ∀ e E p, p≤x.length → RLe (evV g x s T E (render es a e) p) (evV h x t U E (render es b e) p)
  | .call i [],E,p,hp => calls i E p hp
  | .seq c d,E,p,hp => by
    have hh := evaluator es g h x s t T U a b hok calls c E p hp
    cases hc : evV g x s T E (render es a c) p with
    | none => rw [render,evV_seq_none hc]; exact Or.inl rfl
    | some v =>
      have hd := hh.eq_of_some hc
      cases v with
      | none => simp only [render,evV_seq_fail hc,evV_seq_fail hd]; exact RLe.refl _
      | some j =>
        simp only [render,evV_seq_ok hc,evV_seq_ok hd]
        exact evaluator es g h x s t T U a b hok calls d E j (evV_ok hok _ p hp j hc)
  | .alt c d,E,p,hp => by
    have hh := evaluator es g h x s t T U a b hok calls c E p hp
    cases hc : evV g x s T E (render es a c) p with
    | none => rw [render,evV_alt_none hc]; exact Or.inl rfl
    | some v =>
      have hd := hh.eq_of_some hc
      cases v with
      | none =>
        simp only [render,evV_alt_fail hc,evV_alt_fail hd]
        exact evaluator es g h x s t T U a b hok calls d E p hp
      | some j => simp only [render,evV_alt_ok hc,evV_alt_ok hd]; exact RLe.refl _
  | .notP c,E,p,hp => by
    have hh := evaluator es g h x s t T U a b hok calls c E p hp
    cases hc : evV g x s T E (render es a c) p with
    | none => rw [render,evV_not_none hc]; exact Or.inl rfl
    | some v =>
      have hd := hh.eq_of_some hc
      cases v with
      | none => simp only [render,evV_not_fail hc,evV_not_fail hd]; exact RLe.refl _
      | some j => simp only [render,evV_not_ok hc,evV_not_ok hd]; exact RLe.refl _
  | .star c,E,p,hp => by
    simp only [render,evV_star]
    exact evStar_mono p (fun q hq => evaluator es g h x s t T U a b hok calls c E q (by omega))
  | .call _ (_::_),_,_,_ | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_
  | .lit _,_,_,_ | .param _,_,_,_ | .dbg _,_,_,_ | .lam _ _,_,_,_ | .invoke _ _ _,_,_,_ | .callParam _ _,_,_,_ => RLe.refl _

def Rows (forward : Bool) (es : List Entry) (x : List Char) (T U : Table) : Prop :=
  ∀ (i : Nat) (r : Entry), es[i]?=some r → ∀ p, p≤x.length →
    if forward then RLe (valAt (T i (values r x p)) p) (valAt (U (3*i) []) p)
    else RLe (valAt (U (3*i) []) p) (valAt (T i (values r x p)) p)

theorem forward_evaluator (es : List Entry) (qs : List MExp) (x : List Char) (T U : Table)
    (hok : OkTV x.length T) (rows : Rows true es x T U) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (parGrammar es qs) x .callByValuePar T E (render es true e) p)
      (evV (seqGrammar es qs) x .callByValueSeq U E (render es false e) p) := by
  apply evaluator es _ _ x _ _ T U true false hok _ e E p hp
  intro i E p hp
  cases hr : es[i]? with
  | none => simp only [render,hr,evV,MExp.failAlways]; exact RLe.refl _
  | some r => rw [source_call es qs x T E i r hr p hp,target_call es qs x U E i r hr p]; exact rows i r hr p hp

theorem backward_evaluator (es : List Entry) (qs : List MExp) (x : List Char) (T U : Table)
    (hok : OkTV x.length U) (rows : Rows false es x T U) (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    RLe (evV (seqGrammar es qs) x .callByValueSeq U E (render es false e) p)
      (evV (parGrammar es qs) x .callByValuePar T E (render es true e) p) := by
  apply evaluator es _ _ x _ _ U T false true hok _ e E p hp
  intro i E p hp
  cases hr : es[i]? with
  | none => simp only [render,hr,evV,MExp.failAlways]; exact RLe.refl _
  | some r => rw [source_call es qs x T E i r hr p hp,target_call es qs x U E i r hr p]; exact rows i r hr p hp

end Shallot.MacroPeg.CBV.GuardedPairSimulation
