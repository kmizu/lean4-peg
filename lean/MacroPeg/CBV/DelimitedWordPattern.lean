import MacroPeg.CBV.DelimitedCopyTemplates

namespace Shallot.MacroPeg.CBV.DelimitedWordPattern
open DelimiterTemplate DelimitedCopyTemplates DelimitedCopyProjection

/-- Any finite order and multiplicity of retained-word occurrences. -/
def sourceParts (d : Char) : List Nat → List Part
  | [] => []
  | j::js => .param j::.lit [d]::sourceParts d js

def viewParts (d : Char) (i : Nat) : List Nat → List Part
  | [] => []
  | j::js => (if j=i then Part.param 0 else .gap)::.lit [d]::viewParts d i js

/-- The Seq argument already consumed w at the original origin. Its
first segment is therefore checked only from that actual endpoint. -/
def afterParts (d : Char) (i : Nat) : List Nat → List Part
  | [] => []
  | j::js => if j=i then .lit [d]::viewParts d i js
      else .gap::.lit [d]::viewParts d i js

def Matches (d : Char) (w : List Char) (i : Nat) : List Nat → List Char → List Char → Prop
  | [],x,rest => x=rest
  | j::js,x,rest => ∃ h t, Free d h ∧ x=h++d::t ∧ (j=i → h=w) ∧ Matches d w i js t rest

theorem source_cons (d : Char) (E : List (List Char)) (j : Nat) (js : List Nat) (x rest : List Char) :
    run d E (sourceParts d (j::js)) x=some rest ↔
      ∃ w t, E[j]?=some w ∧ x=w++d::t ∧ run d E (sourceParts d js) t=some rest := by
  cases hw : E[j]? with
  | none => simp [sourceParts,run,action,hw]
  | some w =>
    have hh : run d E (sourceParts d (j::js)) x=run d E (.lit w::.lit [d]::sourceParts d js) x := by simp [sourceParts,run,action,hw]
    rw [hh]
    simp only [run_lit_iff]
    constructor
    · rintro ⟨y,hx,t,hy,ht⟩
      exact ⟨w,t,rfl,by rw [hx,hy]; rfl,ht⟩
    · rintro ⟨v,t,hv,hx,ht⟩
      have he : v=w := (Option.some.inj hv).symm
      subst v
      exact ⟨d::t,hx,t,rfl,ht⟩

def encode (d : Char) (E : List (List Char)) (js : List Nat) : List Char :=
  js.flatMap (fun i => E[i]!++[d])

theorem run_encode (d : Char) (E : List (List Char)) : ∀ js,
    (∀ i∈js, i<E.length) → ∀ rest,
    run d E (sourceParts d js) (encode d E js++rest)=some rest
  | [],_,rest => rfl
  | j::js,hscope,rest => by
    have hj := hscope j (by simp)
    apply (source_cons d E j js _ rest).mpr
    refine ⟨E[j],encode d E js++rest,List.getElem?_eq_getElem hj,?_,?_⟩
    · simp [encode,List.getElem?_eq_getElem hj,List.append_assoc]
    · exact run_encode d E js (fun i hi => hscope i (by simp [hi])) rest

theorem view_iff (d : Char) (w : List Char) (hw : Free d w) (i : Nat) :
    ∀ js x rest, run d [w] (viewParts d i js) x=some rest ↔ Matches d w i js x rest
  | [],x,rest => by simp [viewParts,run,Matches]
  | j::js,x,rest => by
    by_cases hj : j=i
    · simp only [viewParts,if_pos hj]
      change run d [w] (.lit w::.lit [d]::viewParts d i js) x=some rest ↔ _
      simp only [run_lit_iff,view_iff d w hw i js]
      constructor
      · rintro ⟨y,hx,t,hy,ht⟩
        exact ⟨w,t,hw,by rw [hx,hy]; rfl,fun _ => rfl,ht⟩
      · rintro ⟨v,t,hv,hx,he,ht⟩
        rw [he hj] at hx
        exact ⟨d::t,hx,t,rfl,ht⟩
    · simp only [viewParts,if_neg hj,run_gap_sep_iff,view_iff d w hw i js]
      constructor
      · rintro ⟨v,t,hv,hx,ht⟩
        exact ⟨v,t,hv,hx,fun he => False.elim (hj he),ht⟩
      · rintro ⟨v,t,hv,hx,_,ht⟩
        exact ⟨v,t,hv,hx,ht⟩

/-- The projections synchronize their actual delimiter boundaries, even
when capture lengths overlap and occurrences repeat in arbitrary order. -/
theorem source_iff_views (d : Char) (E : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i]) :
    ∀ js, (∀ j∈js, j<E.length) → ∀ x rest,
      run d E (sourceParts d js) x=some rest ↔
        ∀ i, (hi : i<E.length) → Matches d E[i] i js x rest
  | [],_,x,rest => by
    constructor
    · intro h i hi; simpa [sourceParts,run,Matches] using h
    · intro h; simpa [sourceParts,run,Matches] using h 0 hn
  | j::js,hscope,x,rest => by
    have hj := hscope j (by simp)
    have htail : ∀ k∈js, k<E.length := fun k hk => hscope k (by simp [hk])
    rw [source_cons]
    constructor
    · rintro ⟨w,t,hw,hx,ht⟩
      have he : w=E[j] := Option.some.inj (hw.symm.trans (List.getElem?_eq_getElem hj))
      subst w
      have ih := (source_iff_views d E hn hfree js htail t rest).mp ht
      intro i hi
      exact ⟨E[j],t,hfree j hj,hx,fun he => by subst i; rfl,ih i hi⟩
    · intro h
      obtain ⟨w,t,hw,hx,he,ht⟩ := h j hj
      have he := he rfl
      subst w
      refine ⟨E[j],t,List.getElem?_eq_getElem hj,hx,?_⟩
      apply (source_iff_views d E hn hfree js htail t rest).mpr
      intro i hi
      obtain ⟨v,s,hv,hx',_,hs⟩ := h i hi
      obtain ⟨_,rfl⟩ := split_unique d E[j] v t s (hfree j hj) hv (hx.symm.trans hx')
      exact hs

/-- Separate passes cannot silently return different suffixes. -/
theorem matches_endpoint_unique (d : Char) (w v : List Char) (i k : Nat) :
    ∀ js x a b, Matches d w i js x a → Matches d v k js x b → a=b
  | [],x,a,b,ha,hb => ha.symm.trans hb
  | j::js,x,a,b,ha,hb => by
    obtain ⟨u,t,hu,hx,_,ht⟩ := ha
    obtain ⟨z,s,hz,hx',_,hs⟩ := hb
    obtain ⟨_,rfl⟩ := split_unique d u z t s hu hz (hx.symm.trans hx')
    exact matches_endpoint_unique d w v i k js t a b ht hs

theorem drop_free_prefix (d : Char) : ∀ w, Free d w → ∀ x,
    (w++x).dropWhile (pred d)=x.dropWhile (pred d)
  | [],_,_ => rfl
  | c::w,hw,x => by
    have hc : c≠d := fun he => hw (by simp [he])
    have ht : Free d w := fun hm => hw (by simp [hm])
    simpa [pred,hc] using drop_free_prefix d w ht x

theorem after_eq_view (d : Char) (w : List Char) (hw : Free d w) (i j : Nat) (js : List Nat) (a : List Char) :
    run d [w] (afterParts d i (j::js)) a=run d [w] (viewParts d i (j::js)) (w++a) := by
  by_cases hj : j=i
  · have hs := (CBVtoCBN.stripPrefix_exact w (w++a) a).mpr rfl
    simp [afterParts,viewParts,hj,run,action,hs]
  · simp [afterParts,viewParts,hj,run,action,drop_free_prefix d w hw a]

/-- All actual capture endpoints may be different. Each generated unary
projection starts at its own Seq argument endpoint and yields the same
original suffix after the entire word pattern. -/
theorem source_iff_after (d : Char) (E tails : List (List Char)) (hn : 0<E.length)
    (hfree : ∀ i, (hi : i<E.length) → Free d E[i])
    (htails : tails.length=E.length) (x : List Char)
    (hprefix : ∀ i, (hi : i<E.length) → x=E[i]++(tails[i]'(by omega)))
    (j : Nat) (js : List Nat) (hscope : ∀ k∈j::js, k<E.length) (rest : List Char) :
    run d E (sourceParts d (j::js)) x=some rest ↔
      ∀ i, (hi : i<E.length) → run d [E[i]] (afterParts d i (j::js)) (tails[i]'(by omega))=some rest := by
  rw [source_iff_views d E hn hfree (j::js) hscope]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [after_eq_view d E[i] (hfree i hi) i j js,←hprefix i hi,view_iff d E[i] (hfree i hi) i]

end Shallot.MacroPeg.CBV.DelimitedWordPattern
