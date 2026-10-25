import MacroPeg.CBV.EmptyObservedSyntax

namespace Shallot.MacroPeg.CBV.EmptyObservedFirstOrder
open EmptyObservedSyntax
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule

theorem preflight_firstOrder (pairs : List (MExp × MExp))
    (h : ∀ pair∈pairs, pair.1.FirstOrder) : (preflight pairs).FirstOrder := by
  induction pairs with
  | nil => trivial
  | cons pair pairs ih =>
    exact ⟨h pair (by simp),ih (by intro a ha; exact h a (by simp [ha]))⟩

theorem decision_firstOrder (pairs : List (MExp × MExp)) (f : List Bool → MExp)
    (h : ∀ pair∈pairs, pair.2.FirstOrder) (hf : ∀ bits, (f bits).FirstOrder) :
    (decision pairs f).FirstOrder := by
  induction pairs generalizing f with
  | nil => exact hf []
  | cons pair pairs ih =>
    have hz := h pair (by simp)
    have ht := ih (fun bits => f (true::bits)) (by intro a ha; exact h a (by simp [ha])) (by intro bits; exact hf _)
    have hn := ih (fun bits => f (false::bits)) (by intro a ha; exact h a (by simp [ha])) (by intro bits; exact hf _)
    exact ⟨⟨hz,ht⟩,⟨hz,hn⟩⟩

theorem emit_firstOrder (rs : List Spec) (bits : List Bool) (zero : Bool) (e : Term) :
    (emit rs bits zero e).FirstOrder := by
  cases e with
  | eps | any | chr _ | range _ _ => cases zero <;> simp [emit,MExp.FirstOrder,MExp.failAlways]
  | lit w =>
    cases zero with
    | false => simp [emit,MExp.FirstOrder]
    | true => simp only [emit]; split <;> trivial
  | atEnd i => simp only [emit]; split <;> trivial
  | call i args =>
    cases hr : rs[i]? with
    | none => simp [emit,hr,MExp.failAlways,MExp.FirstOrder]
    | some r =>
      by_cases ha : r.arity=args.length
      · simp only [emit,hr,if_pos ha,emitArgs_eq_map]
        constructor
        · apply preflight_firstOrder
          intro pair hm
          obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
          exact emit_firstOrder rs bits false a
        · apply decision_firstOrder
          · intro pair hm
            obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
            exact emit_firstOrder rs bits true a
          · intro _; trivial
      · simp [emit,hr,ha,MExp.failAlways,MExp.FirstOrder]
  | seq a b =>
    cases zero with
    | false => simpa only [emit,MExp.FirstOrder] using And.intro (emit_firstOrder rs bits false a) (emit_firstOrder rs bits false b)
    | true =>
      rw [emit]
      exact ⟨emit_firstOrder rs bits false (.seq a b),emit_firstOrder rs bits true a,emit_firstOrder rs bits true b⟩
  | alt a b =>
    cases zero with
    | false => simpa only [emit,MExp.FirstOrder] using And.intro (emit_firstOrder rs bits false a) (emit_firstOrder rs bits false b)
    | true =>
      rw [emit]
      exact ⟨emit_firstOrder rs bits false (.alt a b),emit_firstOrder rs bits true a,emit_firstOrder rs bits false a,emit_firstOrder rs bits true b⟩
  | notP a => simpa only [emit,MExp.FirstOrder] using emit_firstOrder rs bits false a
  | star a =>
    cases zero with
    | false => simpa only [emit,MExp.FirstOrder] using emit_firstOrder rs bits false a
    | true =>
      rw [emit]
      exact ⟨emit_firstOrder rs bits false (.star a),emit_firstOrder rs bits false a⟩
termination_by (sizeOf e,if zero then 1 else 0)
decreasing_by all_goals simp_wf; all_goals first | omega | (apply Prod.Lex.left; exact Nat.lt_trans (List.sizeOf_lt_of_mem ha) (by omega))

theorem target_firstOrder (rs : List Spec) : (target rs).FirstOrder := by
  intro r hr
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
  exact emit_firstOrder _ _ _ _

theorem target_nullary (rs : List Spec) : ∀ r∈(target rs).rules, r.arity=0 := by
  intro r hr
  obtain ⟨key,_,rfl⟩ := List.mem_map.mp hr
  rfl

end Shallot.MacroPeg.CBV.EmptyObservedFirstOrder
