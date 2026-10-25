import MacroPeg.CBV.RepeatedWordArguments
import MacroPeg.CBV.RepeatedWordEvaluation

/-! Once a first delimited copy block has been checked, its entire actual
input span can be recaptured as one word. Replaying that word preserves
the stopping frontier of arbitrarily many subsequent full blocks. -/
namespace Shallot.MacroPeg.CBV.RecapturedCopyBlock
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection ClockFreezing

def skeleton (d : Char) : List Nat → List Part
  | [] => []
  | _::js => .gap::.lit [d]::skeleton d js

theorem source_run (d : Char) (E : List (List Char)) : ∀ js,
    (∀ i∈js, i<E.length) → ∀ x,
    run d E (sourceParts d js) x=Shallot.stripPrefix? (encode d E js) x
  | [],_,_ => rfl
  | j::js,hs,x => by
    have hj := hs j (by simp)
    have ht : ∀ i∈js, i<E.length := fun i hi => hs i (by simp [hi])
    simp only [sourceParts,run,action,List.getElem?_eq_getElem hj,Option.bind_some,
      encode,List.flatMap_cons,getElem!_pos E j hj,
      RepeatedWordArguments.strip_concat,Option.bind_assoc]
    have he : run d E (sourceParts d js)=Shallot.stripPrefix? (encode d E js) := funext (source_run d E js ht)
    rw [he]
    rfl

theorem block_nonempty (d : Char) (E : List (List Char)) (j : Nat) (js : List Nat) :
    encode d E (j::js)≠[] := by
  simp [encode]

theorem skeleton_run (d : Char) (E : List (List Char))
    (hf : ∀ i, (hi : i<E.length) → Free d E[i]) :
    ∀ js, (∀ i∈js, i<E.length) → ∀ rest,
    run d [] (skeleton d js) (encode d E js++rest)=some rest
  | [],_,_ => rfl
  | j::js,hs,rest => by
    have hj := hs j (by simp)
    apply (DelimitedCopyTemplates.run_gap_sep_iff d [] (skeleton d js) _ rest).mpr
    refine ⟨E[j],encode d E js++rest,hf j hj,?_,?_⟩
    · simp [encode,List.getElem?_eq_getElem hj,List.append_assoc]
    · exact skeleton_run d E hf js (fun i hi => hs i (by simp [hi])) rest

theorem step_literal (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (d : Char) (js : List Nat) (hs : ∀ i∈js, i<E.length)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (compile d (sourceParts d js)) p=
      evV g x s T [] (.lit (encode d E js)) p := by
  rw [compile_eval g x s T E d _ p hp,source_run d E js hs]
  simp only [evV]
  cases Shallot.stripPrefix? (encode d E js) (sfx x p) <;> rfl

theorem star_literal (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (d : Char) (js : List Nat) (hs : ∀ i∈js, i<E.length)
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (compile d (sourceParts d js))) p=
      evV g x s T [] (.star (.lit (encode d E js))) p := by
  rw [evV_star,evV_star]
  exact evStar_congr p (fun q hq => step_literal g x s T E d js hs q (by omega))

theorem recapture_call (g h : MGrammar) (loop : Nat) (d : Char) (j : Nat) (js : List Nat)
    (hrow : ruleAtM h.rules loop=some ⟨1,.star (.param 0)⟩)
    (x : List Char) (E W : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (hs : ∀ i∈j::js, i<W.length)
    (hf : ∀ i, (hi : i<W.length) → Free d W[i])
    (rest : List Char) (hfirst : run d W (sourceParts d (j::js)) (sfx x p)=some rest) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (.call loop [compile d (skeleton d (j::js))]) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (.star (compile d (sourceParts d (j::js)))) p := by
  let B := encode d W (j::js)
  have hx : sfx x p=B++rest :=
    (CBVtoCBN.stripPrefix_exact _ _ _).mp ((source_run d W (j::js) hs (sfx x p)).symm.trans hfirst)
  have hscan : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (compile d (skeleton d (j::js))) p=some (some rest.length) := by
    rw [compile_eval]
    have he : run d E (skeleton d (j::js)) (sfx x p)=some rest := by
      -- Skeleton parts contain no parameter accesses.
      have henv : ∀ is y, run d E (skeleton d is) y=run d [] (skeleton d is) y := by
        intro is
        induction is with
        | nil => intro y; rfl
        | cons i is ih =>
          intro y
          simp only [skeleton,run,action]
          exact congrArg (fun f => (Shallot.stripPrefix? [d] (y.dropWhile (pred d))).bind f) (funext ih)
      rw [henv,hx]
      exact skeleton_run d W hf (j::js) hs rest
    simp only [he,Option.map_some]
    exact hp
  have hq := evV_ok (tblV_ok h x .callByValueSeq (k+1)) _ p hp _ hscan
  have hpre : pre x p rest.length=B := by
    simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hx
  have hlen : rest.length<p := by
    have hh := congrArg List.length hx
    rw [length_sfx x hp,List.length_append] at hh
    have hb := List.length_pos_iff.mpr (block_nonempty d W j js)
    change 0<B.length at hb
    omega
  rw [evV_call_seq hrow rfl,evSeq_cons_ok hscan,evSeq_nil]
  change valAt (tblV h x .callByValueSeq (k+1) loop [pre x p rest.length]) rest.length=_
  rw [hpre,valAt_tblV_succ hrow [B] hq,star_literal g x .callByValuePar _ W d (j::js) hs p hp,evV_star]
  have hhead : evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.lit B) p=some (some rest.length) := by
    simp only [evV,(CBVtoCBN.stripPrefix_exact B (sfx x p) rest).mpr hx]
  change evStar (fun q => evV h x .callByValueSeq (tblV h x .callByValueSeq k) [B] (.param 0) q) rest.length=
    evStar (fun q => evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.lit B) q) p
  rw [evStar_ok hhead hlen]
  rfl

theorem literal_copies (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (B : List Char) (hne : B≠[]) (rest : List Char)
    (hstop : Shallot.stripPrefix? B rest=none) :
    ∀ n p, p≤x.length → sfx x p=RepeatedWordArguments.copies B n++rest →
      evV g x s T E (.star (.lit B)) p=some (some rest.length)
  | 0,p,hp,hs => by
    have hs : sfx x p=rest := hs
    have hl : p=rest.length := by simpa only [length_sfx x hp] using congrArg List.length hs
    rw [evV_star,evStar_fail (by simp only [evV,hs,hstop])]
    rw [hl]
  | n+1,p,hp,hs => by
    let next := RepeatedWordArguments.copies B n++rest
    have hx : sfx x p=B++next := by simpa only [RepeatedWordArguments.copies,List.append_assoc] using hs
    have hv : evV g x s T E (.lit B) p=some (some next.length) := by
      simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hx]
    have hl := congrArg List.length hx
    rw [length_sfx x hp,List.length_append] at hl
    have hb := List.length_pos_iff.mpr hne
    have hlt : next.length<p := by omega
    have hnext : sfx x next.length=next :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨B,hx⟩).choose_spec
    rw [evV_star,evStar_ok hv hlt]
    exact literal_copies g x s T E B hne rest hstop n next.length (by omega) hnext

end Shallot.MacroPeg.CBV.RecapturedCopyBlock
