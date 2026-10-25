import MacroPeg.CBV.CopyFieldCapture
import MacroPeg.CBV.RecursiveParserStability

/-! Ordinary first-order control may use each retained parameter separately.
Only calls inside this control are restricted to an installed independent
nullary recursive library. The word-view theorem itself has no call restriction. -/
namespace Shallot.MacroPeg.CBV.TupleFieldControl

def check (helpers arity : Nat) : MExp → Bool
  | .eps | .any | .chr _ | .range _ _ | .lit _ => true
  | .param i => decide (i<arity)
  | .call i [] => decide (i<helpers)
  | .seq a b | .alt a b => check helpers arity a && check helpers arity b
  | .notP a | .star a => check helpers arity a
  | _ => false

theorem firstOrder (helpers arity : Nat) : ∀ e, check helpers arity e=true → e.FirstOrder
  | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
  | .call _ [],_ => trivial
  | .call _ (_::_),hc | .dbg _,hc | .lam _ _,hc | .callParam _ _,hc | .invoke _ _ _,hc => by simp [check] at hc
  | .seq a b,hc | .alt a b,hc =>
    ⟨firstOrder helpers arity a (Bool.and_eq_true_iff.mp hc).1,
      firstOrder helpers arity b (Bool.and_eq_true_iff.mp hc).2⟩
  | .notP a,hc | .star a,hc => firstOrder helpers arity a hc

/-- All control and independent recursive helpers preserve the physical clock
when switching argument conventions. Each original parameter remains available. -/
theorem physical (bodies : List MExp) (g h : MGrammar)
    (hb : RecursiveParserStability.Valid bodies)
    (hg : RecursiveParserStability.Installed bodies g)
    (hh : RecursiveParserStability.Installed bodies h)
    (x : List Char) (k : Nat) (W : List (List Char)) (arity : Nat) :
    ∀ e, check bodies.length arity e=true → ∀ p, p≤x.length →
    evV g x .callByValuePar (tblV g x .callByValuePar k) W e p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) W e p
  | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ | .param _,_,_,_ => rfl
  | .call i [],hc,p,hp => by
    have hi : i<bodies.length := of_decide_eq_true hc
    have hr := List.getElem?_eq_getElem hi
    rw [evV_call_par (hg i bodies[i] hr) rfl (by decide),evPar_nil,
      evV_call_seq (hh i bodies[i] hr) rfl,evSeq_nil]
    exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hb hg hh x _ _ k i hi [] [])
  | .call _ (_::_),hc,_,_ | .dbg _,hc,_,_ | .lam _ _,hc,_,_ | .callParam _ _,hc,_,_ | .invoke _ _ _,hc,_,_ => by simp [check] at hc
  | .seq a b,hc,p,hp => by
    have ha := physical bodies g h hb hg hh x k W arity a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) W a p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact physical bodies g h hb hg hh x k W arity b (Bool.and_eq_true_iff.mp hc).2 q
          (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b,hc,p,hp => by
    have ha := physical bodies g h hb hg hh x k W arity a (Bool.and_eq_true_iff.mp hc).1 p hp
    cases hv : evV g x .callByValuePar (tblV g x .callByValuePar k) W a p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact physical bodies g h hb hg hh x k W arity b (Bool.and_eq_true_iff.mp hc).2 p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .notP a,hc,p,hp => by
    simp only [evV,physical bodies g h hb hg hh x k W arity a hc p hp]
  | .star a,hc,p,hp => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun q hq => physical bodies g h hb hg hh x k W arity a hc q (by omega))

/-- Actual Seq capture of a verified anchor followed by raw component-aware
Par control. All results, including failure and partiality, are preserved. -/
theorem entry (bodies : List MExp) (g h : MGrammar)
    (hb : RecursiveParserStability.Valid bodies)
    (hg : RecursiveParserStability.Installed bodies g)
    (hh : RecursiveParserStability.Installed bodies h)
    (address arity : Nat) (d : Char) (js : List Nat) (e : MExp)
    (hc : check bodies.length arity e=true)
    (hrow : ruleAtM h.rules address=some ⟨2*js.length,MExp.subst (CopyFieldCapture.views arity js) e⟩)
    (x : List Char) (E W : List (List Char)) (hl : W.length=arity)
    (cover : ∀ i, i<arity → i∈js) (hs : ∀ i∈js, i<W.length)
    (hf : ∀ i, (hi : i<W.length) → DelimitedCopyProjection.Free d W[i])
    (k p : Nat) (hp : p≤x.length) (rest : List Char)
    (hfirst : DelimiterTemplate.run d W (DelimitedWordPattern.sourceParts d js) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (.call address (CopyFieldCapture.scanArgs d js)) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) W e rest.length := by
  rw [CopyFieldCapture.entry h address arity d js e (firstOrder _ _ e hc)
    hrow x E W hl cover hs hf k p hp rest hfirst]
  have hx : sfx x p=DelimitedWordPattern.encode d W js++rest :=
    (CBVtoCBN.stripPrefix_exact _ _ _).mp ((RecapturedCopyBlock.source_run d W js hs _).symm.trans hfirst)
  have hq : rest.length≤x.length := by
    have := congrArg List.length hx
    simp only [length_sfx x hp,List.length_append] at this
    omega
  exact (physical bodies g h hb hg hh x k W arity e hc rest.length hq).symm

end Shallot.MacroPeg.CBV.TupleFieldControl
