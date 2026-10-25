import MacroPeg.CBV.FiniteSuffixObservedSyntax

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedDeclarations
open FiniteSuffixObservedSyntax
open RegularCaptureProduct (run choice)
open FiniteSuffixReplay (palette views)

theorem mode_mem (R : List (List Char)) (u : List Char) (q r : Nat) :
    some (u,q,r)∈modes R ↔ u∈palette R ∧ q<u.length+2 ∧ r<u.length+2 := by
  simp only [modes,List.mem_cons,Option.some.injEq,reduceCtorEq,false_or,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,he,hbe,hce⟩
    subst a; subst b; subst c
    exact ⟨ha,hb,hc⟩
  · rintro ⟨hu,hq,hr⟩
    exact ⟨u,hu,q,hq,r,hr,rfl,rfl,rfl⟩

theorem key_mem (R : List (List Char)) (rs : List Spec) (i : Nat) (r : Spec) (hr : rs[i]?=some r)
    (E : List (List Char)) (he : E.length=r.arity) (m : Mode) (hm : m∈modes R) :
    (⟨i,views R E,m⟩ : Key)∈keys R rs := by
  apply List.mem_flatMap.mpr
  refine ⟨(r,i),List.mem_of_getElem? (show rs.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hr]),?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨views R E,by simpa only [he] using FiniteSuffixRecursiveSyntax.views_mem R E,List.mem_map.mpr ⟨m,hm,rfl⟩⟩

theorem target_rule (R : List (List Char)) (rs : List Spec) (i : Nat) (r : Spec) (hr : rs[i]?=some r)
    (E : List (List Char)) (he : E.length=r.arity) (m : Mode) (hm : m∈modes R) :
    ruleAtM (target R rs).rules (address R rs i (views R E) m)=some ⟨0,emit R rs (views R E) m r.body⟩ := by
  have hk := DependentProfileCall.index_correct (⟨i,views R E,m⟩ : Key) (keys R rs) (key_mem R rs i r hr E he m hm)
  simp [target,ruleAtM_eq_getElem?,address,List.getElem?_map,hk,targetRule,hr]

theorem atom_firstOrder (m : Mode) (e : MExp) (w : List Char) (he : e.FirstOrder) : (atom m e w).FirstOrder := by
  cases m with
  | none => exact he
  | some v => rcases v with ⟨u,q,r⟩; simp only [atom]; split <;> exact ⟨he,True.intro⟩

theorem charFilter_firstOrder (u : List Char) (q r : Nat) : (charFilter u q r).FirstOrder := by
  simp only [charFilter]; split
  · split <;> split <;> trivial
  · split <;> trivial

theorem character_firstOrder (m : Mode) (e : MExp) (he : e.FirstOrder) : (character m e).FirstOrder := by
  cases m with
  | none => exact he
  | some v => exact ⟨he,charFilter_firstOrder _ _ _⟩

theorem choose_firstOrder (F : List Char → Nat → Nat → MExp) (hF : ∀ u q r, (F u q r).FirstOrder)
    (K : Option (List Char) → MExp) (hK : ∀ v, (K v).FirstOrder) : ∀ ws, (choose ws F K).FirstOrder
  | [] => hK none
  | u::ws => ⟨⟨hF u 0 u.length,hK (some u)⟩,hF u 0 u.length,choose_firstOrder F hF K hK ws⟩

theorem gather_firstOrder (R : List (List Char)) (rs : List Spec) (V : View) (args : List Term)
    (h : ∀ a∈args, ∀ m, (emit R rs V m a).FirstOrder) (K : View → MExp) (hK : ∀ W, (K W).FirstOrder) :
    (gather R rs V args K).FirstOrder := by
  induction args generalizing K with
  | nil => exact hK []
  | cons a args ih =>
    refine ⟨h a (by simp) none,choose_firstOrder _ (fun u q r => h a (by simp) _) _ ?_ _⟩
    intro v
    exact ih (by intro a ha; exact h a (by simp [ha])) _ (fun W => hK (v::W))

theorem emit_firstOrder (R : List (List Char)) (rs : List Spec) (V : View) (m : Mode) (e : Term) :
    (emit R rs V m e).FirstOrder := by
  cases e with
  | eps | lit _ => exact atom_firstOrder _ _ _ True.intro
  | any | chr _ | range _ _ => exact character_firstOrder _ _ True.intro
  | replay i => exact atom_firstOrder _ _ _ ⟨FiniteSuffixReplay.guard_firstOrder R,FiniteSuffixReplay.literal_firstOrder V i⟩
  | call i args =>
    simp only [emit]; split
    · trivial
    · split
      · apply gather_firstOrder
        · intro a ha m; exact emit_firstOrder R rs V m a
        · intro _; trivial
      · trivial
  | seq a b =>
    cases m with
    | none => exact ⟨emit_firstOrder R rs V none a,emit_firstOrder R rs V none b⟩
    | some v =>
      rcases v with ⟨u,q,r⟩
      apply RegularCaptureProduct.choice_firstOrder
      intro e he
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
      exact ⟨emit_firstOrder R rs V _ a,emit_firstOrder R rs V _ b⟩
  | alt a b =>
    cases m with
    | none => exact ⟨emit_firstOrder R rs V none a,emit_firstOrder R rs V none b⟩
    | some v => exact ⟨⟨emit_firstOrder R rs V none a,emit_firstOrder R rs V _ a⟩,emit_firstOrder R rs V none a,emit_firstOrder R rs V _ b⟩
  | notP a => exact atom_firstOrder _ _ _ (emit_firstOrder R rs V none a)
  | star a =>
    cases m with
    | none => exact emit_firstOrder R rs V none a
    | some v => exact GeneralStarFilter.filter_firstOrder _ _ (emit_firstOrder R rs V none a) _ (fun q r => emit_firstOrder R rs V _ a) _ _
termination_by sizeOf e

mutual
  theorem render_firstOrder (R : List (List Char)) : ∀ e, (original R e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ => True.intro
    | .replay _ => ⟨FiniteSuffixReplay.guard_firstOrder R,True.intro⟩
    | .call _ args => renderArgs_firstOrder R args
    | .seq a b | .alt a b => ⟨render_firstOrder R a,render_firstOrder R b⟩
    | .notP a | .star a => render_firstOrder R a
  theorem renderArgs_firstOrder (R : List (List Char)) : ∀ args,
      MExp.FirstOrderArgs (FiniteSuffixDependentView.renderArgs R none args)
    | [] => True.intro
    | a::args => ⟨render_firstOrder R a,renderArgs_firstOrder R args⟩
end

theorem source_firstOrder (R : List (List Char)) (rs : List Spec) : (source R rs).FirstOrder := by
  intro r hr
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  exact render_firstOrder _ _

 theorem target_firstOrder (R : List (List Char)) (rs : List Spec) : (target R rs).FirstOrder := by
  intro r hr
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
  exact emit_firstOrder _ _ _ _ _

theorem target_nullary (R : List (List Char)) (rs : List Spec) : ∀ r∈(target R rs).rules, r.arity=0 := by
  intro r hr
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
  rfl

end Shallot.MacroPeg.CBV.FiniteSuffixObservedDeclarations
