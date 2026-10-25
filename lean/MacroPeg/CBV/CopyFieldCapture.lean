import MacroPeg.CBV.RecapturedCopyBlock
import MacroPeg.CBV.CaptureViews

/-! Recapture the individual words of a verified delimited anchor as real
Seq arguments. Delimiters occupy separate arguments, so every original word
can subsequently be replayed without its delimiter, at any input position.
The values may overlap in the original Par capture; their copies in the
anchor are disjoint. -/
namespace Shallot.MacroPeg.CBV.CopyFieldCapture
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection

def scanArgs (d : Char) : List Nat → List MExp
  | [] => []
  | _::js => gap d :: .chr d :: scanArgs d js

def fields (d : Char) (W : List (List Char)) : List Nat → List (List Char)
  | [] => []
  | j::js => W[j]! :: [d] :: fields d W js

def fieldIndex (i : Nat) : List Nat → Nat
  | [] => 0
  | j::js => if i=j then 0 else 2+fieldIndex i js

def views (arity : Nat) (js : List Nat) : List MExp :=
  (List.range arity).map (fun i => .param (fieldIndex i js))

theorem scanArgs_firstOrder (d : Char) : ∀ js, MExp.FirstOrderArgs (scanArgs d js)
  | [] => trivial
  | _::js => ⟨⟨True.intro,True.intro⟩,True.intro,scanArgs_firstOrder d js⟩

theorem views_firstOrder (arity : Nat) (js : List Nat) : MExp.FirstOrderArgs (views arity js) := by
  have hm : ∀ is : List Nat, MExp.FirstOrderArgs (is.map (fun i => .param (fieldIndex i js))) := by
    intro is
    induction is with
    | nil => trivial
    | cons i is ih => exact ⟨True.intro,ih⟩
  exact hm _

theorem scanArgs_length (d : Char) (js : List Nat) :
    (scanArgs d js).length=2*js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [scanArgs,List.length_cons,ih]; omega

theorem fields_length (d : Char) (W : List (List Char)) (js : List Nat) :
    (fields d W js).length=2*js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [fields,List.length_cons,ih]; omega

theorem field_lookup (d : Char) (W : List (List Char)) (i : Nat)
    (hi : i<W.length) : ∀ js, i∈js →
    (fields d W js)[fieldIndex i js]?=some W[i]
  | [],hm => by simp at hm
  | j::js,hm => by
    by_cases he : i=j
    · subst j; simp [fieldIndex,fields,getElem!_pos W i hi]
    · have ht : i∈js := by simpa [he] using hm
      simpa only [fieldIndex,if_neg he,fields,show 2+fieldIndex i js=(fieldIndex i js+1)+1 by omega,
        List.getElem?_cons_succ]
        using field_lookup d W i hi js ht

private theorem argAt_map {α : Type} (f : α → MExp) : ∀ (xs : List α) k,
    argAt (xs.map f) k=(xs[k]?).map f
  | [],_ => rfl
  | _::_,0 => rfl
  | _::xs,k+1 => by simpa only [List.map_cons,argAt,List.getElem?_cons_succ] using argAt_map f xs k

/-- Full value representation, including malformed out-of-range parameters.
No body restriction or bound on the observation position is needed. -/
theorem parameter_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (W : List (List Char)) (arity : Nat)
    (hl : W.length=arity) (d : Char) (js : List Nat)
    (cover : ∀ i, i<arity → i∈js) (i p : Nat) :
    evV g x s T (fields d W js) (MExp.subst (views arity js) (.param i)) p=
      evV g x s T W (.param i) p := by
  by_cases hi : i<arity
  · have hw : i<W.length := by omega
    have hr : (List.range arity)[i]?=some i := by simp [hi]
    simp only [MExp.subst,views,argAt_map,hr,Option.map_some,evV,
      field_lookup d W i hw js (cover i hi),List.getElem?_eq_getElem hw]
  · have hr : (List.range arity)[i]?=none := by simp [hi]
    have hw : W[i]?=none := List.getElem?_eq_none (by omega)
    simp [MExp.subst,views,argAt_map,hr,evV,hw,MExp.failAlways]

/-- Arbitrary first-order control and calls can use every recovered word
separately. The strategy and recursive table remain arbitrary and unchanged. -/
theorem expression_view (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (W : List (List Char)) (arity : Nat)
    (hl : W.length=arity) (d : Char) (js : List Nat)
    (cover : ∀ i, i<arity → i∈js) (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV g x s T (fields d W js) (MExp.subst (views arity js) e) p=
      evV g x s T W e p :=
  CaptureViews.evV_rebind _ _ (parameter_view g x s T W arity hl d js cover) e he p

/-- The scanner captures each word and separator as distinct real Seq
arguments; it does not embed runtime words in generated syntax. -/
theorem scan_encoded (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E W : List (List Char)) (d : Char)
    (hf : ∀ i, (hi : i<W.length) → Free d W[i]) :
    ∀ js, (∀ i∈js, i<W.length) → ∀ rest p, p≤x.length →
    sfx x p=encode d W js++rest →
    evSeqArgs g x s T E (scanArgs d js) p=some (some (fields d W js,rest.length))
  | [],_,rest,p,hp,hx => by
    have hl : p=rest.length := by simpa only [encode,List.flatMap_nil,List.nil_append,length_sfx x hp] using congrArg List.length hx
    simp only [scanArgs,fields,evSeq_nil,hl]
  | j::js,hs,rest,p,hp,hx => by
    have hj := hs j (by simp)
    let next := encode d W js++rest
    have he : sfx x p=W[j]++d::next := by
      simpa only [next,encode,List.flatMap_cons,getElem!_pos W j hj,List.append_assoc,
        List.cons_append,List.nil_append] using hx
    have hsuffix := suffix_trans (sfx_is_suffix x p) ⟨W[j],he⟩
    have hq : (d::next).length≤x.length := by
      obtain ⟨front,hprefix⟩ := hsuffix
      have := congrArg List.length hprefix
      simp only [List.length_append] at this
      omega
    have hnext : sfx x (d::next).length=d::next := sfx_suffix hsuffix.choose_spec
    have hgap : evV g x s T E (gap d) p=some (some (d::next).length) := by
      rw [gap_eval g x s T E d p hp,he,DelimitedCopyTemplates.drop_free d W[j] (hf j hj)]
    have hchr : evV g x s T E (.chr d) (d::next).length=some (some next.length) := by
      simp only [evV,hnext]
      simp [Shallot.beqChar]
    have hpre : pre x p (d::next).length=W[j] := by
      simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) he
    have hpsep : pre x (d::next).length next.length=[d] := by
      exact pre_eq hsuffix (show d::next=[d]++next from rfl)
    have htail : sfx x next.length=next := by
      exact sfx_suffix (suffix_trans hsuffix ⟨[d],rfl⟩).choose_spec
    have hn : next.length≤x.length := by simp only [List.length_cons] at hq; omega
    rw [scanArgs,evSeq_cons_ok hgap,evSeq_cons_ok hchr,
      scan_encoded g x s T E W d hf js (fun i hi => hs i (by simp [hi])) rest next.length hn htail]
    simp only [hpre,hpsep,fields,getElem!_pos W j hj]

/-- Enter a real generated row after a verified anchor. Every original
parameter is available to its arbitrary first-order body, independently of
how little input remains. This theorem preserves the target strategy; the
separate control theorem handles changing Par to Seq. -/
theorem entry (h : MGrammar) (address arity : Nat) (d : Char) (js : List Nat)
    (e : MExp) (he : e.FirstOrder)
    (hrow : ruleAtM h.rules address=some ⟨2*js.length,MExp.subst (views arity js) e⟩)
    (x : List Char) (E W : List (List Char)) (hl : W.length=arity)
    (cover : ∀ i, i<arity → i∈js)
    (hs : ∀ i∈js, i<W.length)
    (hf : ∀ i, (hi : i<W.length) → Free d W[i])
    (k p : Nat) (hp : p≤x.length) (rest : List Char)
    (hfirst : run d W (sourceParts d js) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (.call address (scanArgs d js)) p=
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
  exact expression_view h x .callByValueSeq _ W arity hl d js cover e he rest.length

end Shallot.MacroPeg.CBV.CopyFieldCapture
