import MacroPeg.CBV.CopyFieldCapture

/-! A delimiter anchor only needs to recapture parameters used by the
continuation. Missing values are never replaced by empty successes. All
source actuals must still be evaluated by the caller's preflight. -/
namespace Shallot.MacroPeg.CBV.UsedFieldCapture
open CopyFieldCapture DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection

abbrev Allowed (arity : Nat) (js : List Nat) (i : Nat) : Prop := i<arity → i∈js
def check (arity : Nat) (js : List Nat) (e : MExp) : Bool :=
  ParameterSupport.check (fun i => decide (Allowed arity js i)) e

theorem checked (arity : Nat) (js : List Nat) (e : MExp) (hc : check arity js e=true) :
    ParameterSupport.Supports (Allowed arity js) e :=
  ParameterSupport.mono (fun _ hi => of_decide_eq_true hi) e
    ((ParameterSupport.check_iff _ e).mp hc)

theorem check_complete (arity : Nat) (js : List Nat) (e : MExp)
    (he : ParameterSupport.Supports (Allowed arity js) e) : check arity js e=true :=
  (ParameterSupport.check_iff _ e).mpr (ParameterSupport.mono (fun _ hi => decide_eq_true hi) e he)

theorem of_cover (arity : Nat) (js : List Nat) (e : MExp) (he : e.FirstOrder)
    (cover : ∀ i, i<arity → i∈js) : ParameterSupport.Supports (Allowed arity js) e :=
  ParameterSupport.mono (fun i _ => cover i) e (ParameterSupport.all_of_firstOrder e he)

private theorem argAt_map {α : Type} (f : α → MExp) : ∀ (xs : List α) k,
    argAt (xs.map f) k=(xs[k]?).map f
  | [],_ => rfl
  | _::_,0 => rfl
  | _::xs,k+1 => by simpa only [List.map_cons,argAt,List.getElem?_cons_succ] using argAt_map f xs k

theorem parameter_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (W : List (List Char)) (arity : Nat)
    (hl : W.length=arity) (d : Char) (js : List Nat) (i : Nat) (cover : Allowed arity js i) (p : Nat) :
    evV g x s T (fields d W js) (MExp.subst (views arity js) (.param i)) p=
      evV g x s T W (.param i) p := by
  by_cases hi : i<arity
  · have hw : i<W.length := by omega
    have hr : (List.range arity)[i]?=some i := by simp [hi]
    simp only [MExp.subst,views,argAt_map,hr,Option.map_some,evV,
      field_lookup d W i hw js (cover hi),List.getElem?_eq_getElem hw]
  · have hr : (List.range arity)[i]?=none := by simp [hi]
    have hw : W[i]?=none := List.getElem?_eq_none (by omega)
    simp [MExp.subst,views,argAt_map,hr,evV,hw,MExp.failAlways]

theorem expression_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (W : List (List Char)) (arity : Nat)
    (hl : W.length=arity) (d : Char) (js : List Nat) (e : MExp)
    (used : ParameterSupport.Supports (Allowed arity js) e) (p : Nat) :
    evV g x s T (fields d W js) (MExp.subst (views arity js) e) p=
      evV g x s T W e p :=
  ParameterSupport.evV_rebind (Allowed arity js) _ W
    (fun i hi q => parameter_view g x s T W arity hl d js i hi q) e used p

theorem entry (h : MGrammar) (address arity : Nat) (d : Char) (js : List Nat)
    (e : MExp) (used : ParameterSupport.Supports (Allowed arity js) e)
    (hrow : ruleAtM h.rules address=some ⟨2*js.length,MExp.subst (views arity js) e⟩)
    (x : List Char) (E W : List (List Char)) (hl : W.length=arity)
    (hs : ∀ i∈js, i<W.length) (hf : ∀ i, (hi : i<W.length) → Free d W[i])
    (k p : Nat) (hp : p≤x.length) (rest : List Char)
    (hfirst : run d W (sourceParts d js) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.call address (scanArgs d js)) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) W e rest.length := by
  have hx : sfx x p=encode d W js++rest :=
    (CBVtoCBN.stripPrefix_exact _ _ _).mp ((RecapturedCopyBlock.source_run d W js hs _).symm.trans hfirst)
  have hq : rest.length≤x.length := by
    have hh := congrArg List.length hx
    rw [length_sfx x hp,List.length_append] at hh
    omega
  rw [evV_call_seq hrow (scanArgs_length d js).symm,
    scan_encoded h x .callByValueSeq _ E W d hf js hs rest p hp hx]
  change valAt (tblV h x .callByValueSeq (k+1) address (fields d W js)) rest.length=_
  rw [valAt_tblV_succ hrow (fields d W js) hq]
  exact expression_view h x .callByValueSeq _ W arity hl d js e used rest.length

end Shallot.MacroPeg.CBV.UsedFieldCapture
