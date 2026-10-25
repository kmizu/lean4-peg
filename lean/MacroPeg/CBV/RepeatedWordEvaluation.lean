import MacroPeg.CBV.DelimitedRepeatEvaluation

namespace Shallot.MacroPeg.CBV.RepeatedWordEvaluation
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open RepeatedWordPattern ClockFreezing Classical

theorem viewParts_append (d : Char) (i : Nat) : ∀ a b,
    viewParts d i (a++b)=viewParts d i a++viewParts d i b
  | [],_ => rfl
  | j::js,b => by simp [viewParts,viewParts_append d i js b]

theorem source_copies (d : Char) (js : List Nat) : ∀ n,
    sourceParts d (RepeatedWordPattern.copies js n)=
      DelimitedRepeatEvaluation.copies (sourceParts d js) n
  | 0 => rfl
  | n+1 => by simp [RepeatedWordPattern.copies,DelimitedRepeatEvaluation.copies,CopyBodyEvaluation.sourceParts_append,source_copies d js n]

theorem view_copies (d : Char) (i : Nat) (js : List Nat) : ∀ n,
    viewParts d i (RepeatedWordPattern.copies js n)=
      DelimitedRepeatEvaluation.copies (viewParts d i js) n
  | 0 => rfl
  | n+1 => by simp [RepeatedWordPattern.copies,DelimitedRepeatEvaluation.copies,viewParts_append,view_copies d i js n]

theorem matches_suffix (d : Char) (w : List Char) (i : Nat) : ∀ js x rest,
    Matches d w i js x rest → ∃ prefixPart, x=prefixPart++rest
  | [],x,rest,h => ⟨[],h⟩
  | j::js,x,rest,h => by
    obtain ⟨a,t,_,hx,_,ht⟩ := h
    exact suffix_trans ⟨a++[d],by simpa [List.append_assoc] using hx⟩
      (matches_suffix d w i js t rest ht)

theorem source_progress (d : Char) (E : List (List Char)) (j : Nat) (js : List Nat)
    (x rest : List Char) (hr : run d E (sourceParts d (j::js)) x=some rest) :
    rest.length<x.length := by
  obtain ⟨w,t,_,hx,ht⟩ := (source_cons d E j js x rest).mp hr
  obtain ⟨a,ha⟩ := DelimitedRepeatEvaluation.run_suffix d E (sourceParts d js) t rest ht
  rw [hx,ha]
  simp only [List.length_append,List.length_cons]
  omega

theorem view_progress (d : Char) (w : List Char) (hw : Free d w) (i j : Nat) (js : List Nat)
    (x rest : List Char) (hr : run d [w] (viewParts d i (j::js)) x=some rest) :
    rest.length<x.length := by
  obtain ⟨a,t,_,hx,_,ht⟩ := (view_iff d w hw i (j::js) x rest).mp hr
  obtain ⟨b,hb⟩ := matches_suffix d w i js t rest ht
  rw [hx,hb]
  simp only [List.length_append,List.length_cons]
  omega

theorem source_empty (d : Char) (E : List (List Char)) (j : Nat) (js : List Nat) :
    run d E (sourceParts d (j::js)) []=none := by
  cases hr : run d E (sourceParts d (j::js)) [] with
  | none => rfl
  | some rest => have := source_progress d E j js [] rest hr; simp at this

theorem view_empty (d : Char) (w : List Char) (hw : Free d w) (i j : Nat) (js : List Nat) :
    run d [w] (viewParts d i (j::js)) []=none := by
  cases hr : run d [w] (viewParts d i (j::js)) [] with
  | none => rfl
  | some rest => have := view_progress d w hw i j js [] rest hr; simp at this

def sourceBody (d : Char) (js : List Nat) := DelimitedRepeatEvaluation.fullStar d (sourceParts d js)
def viewBody (d : Char) (i : Nat) (js : List Nat) := DelimitedRepeatEvaluation.fullStar d (viewParts d i js)
def afterBody (d : Char) (i : Nat) (js : List Nat) :=
  MExp.seq (compile d (afterParts d i js)) (viewBody d i js)

theorem source_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (E : List (List Char)) (d : Char) (j : Nat) (js : List Nat)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (sourceBody d (j::js)) p=
      some (if SourceAccept d E (j::js) (sfx x p) then some 0 else none) := by
  have he : DelimitedRepeatEvaluation.Accept d E (sourceParts d (j::js)) (sfx x p) ↔
      SourceAccept d E (j::js) (sfx x p) := by
    unfold DelimitedRepeatEvaluation.Accept SourceAccept
    simp only [source_copies]
  simpa only [sourceBody,he] using
    DelimitedRepeatEvaluation.physical g x s T hT E d (sourceParts d (j::js))
      (source_progress d E j js) (source_empty d E j js) p hp

theorem view_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (w : List Char) (d : Char) (hw : Free d w) (i j : Nat) (js : List Nat)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T [w] (viewBody d i (j::js)) p=
      some (if ViewAccept d w i (j::js) (sfx x p) then some 0 else none) := by
  have he : DelimitedRepeatEvaluation.Accept d [w] (viewParts d i (j::js)) (sfx x p) ↔
      ViewAccept d w i (j::js) (sfx x p) := by
    unfold DelimitedRepeatEvaluation.Accept ViewAccept
    simp only [←view_copies,view_iff d w hw]
  simpa only [viewBody,he] using
    DelimitedRepeatEvaluation.physical g x s T hT [w] d (viewParts d i (j::js))
      (view_progress d w hw i j js) (view_empty d w hw i j js) p hp

theorem after_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (hT : OkTV x.length T) (w : List Char) (d : Char) (hw : Free d w) (i j : Nat) (js : List Nat)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T [w] (afterBody d i (j::js)) p=
      some (if AfterAccept d w i (j::js) (sfx x p) then some 0 else none) := by
  rw [afterBody]
  cases hr : run d [w] (afterParts d i (j::js)) (sfx x p) with
  | none =>
    have hv : evV g x s T [w] (compile d (afterParts d i (j::js))) p=some none := by
      simpa [hr] using compile_eval g x s T [w] d (afterParts d i (j::js)) p hp
    rw [evV_seq_fail hv]
    simp [AfterAccept,hr]
  | some rest =>
    have hv : evV g x s T [w] (compile d (afterParts d i (j::js))) p=some (some rest.length) := by
      simpa [hr] using compile_eval g x s T [w] d (afterParts d i (j::js)) p hp
    have hq := evV_ok hT _ p hp _ hv
    have hs : sfx x rest.length=rest := sfx_suffix
      (suffix_trans (sfx_is_suffix x p)
        (DelimitedRepeatEvaluation.run_suffix d [w] _ _ rest hr)).choose_spec
    rw [evV_seq_ok hv,view_physical g x s T hT w d hw i j js rest.length hq,hs]
    have he : AfterAccept d w i (j::js) (sfx x p) ↔ ViewAccept d w i (j::js) rest := by
      simp only [AfterAccept,ViewAccept,hr,Option.some.injEq]
      constructor
      · rintro ⟨n,mid,hm,ht⟩; subst mid; exact ⟨n,ht⟩
      · rintro ⟨n,ht⟩; exact ⟨n,rest,rfl,ht⟩
    simp only [he]

end Shallot.MacroPeg.CBV.RepeatedWordEvaluation
