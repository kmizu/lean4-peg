import MacroPeg.CBV.SequentialTotalSyntax

namespace Shallot.MacroPeg.CBV.SequentialTotalSyntax

def Forms.FirstOrder (f : Forms) : Prop :=
  f.zero.FirstOrder ∧ f.positive.FirstOrder ∧ f.failure.FirstOrder
def EntryOrder (as : List (Forms × Forms)) : Prop :=
  ∀ a∈as, a.1.FirstOrder ∧ a.2.FirstOrder

theorem Forms.success_firstOrder (f : Forms) (h : f.FirstOrder) : f.success.FirstOrder := ⟨h.2.1,h.1⟩
theorem Forms.get_firstOrder (f : Forms) (h : f.FirstOrder) (m : Mode) : (f.get m).FirstOrder := by
  cases m
  · exact f.success_firstOrder h
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem args_order_of_mem (as : List MExp) (h : ∀ a∈as, a.FirstOrder) : MExp.FirstOrderArgs as := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))⟩

theorem choices_firstOrder (as : List MExp) (h : ∀ a∈as, a.FirstOrder) : (choices as).FirstOrder := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨h a (by simp),ih (by intro b hb; exact h b (by simp [hb]))⟩

theorem positiveRoutes_firstOrder (as : List (Forms × Forms)) (h : EntryOrder as)
    (bs : List MExp) (hb : bs∈positiveRoutes as) : MExp.FirstOrderArgs bs := by
  induction as generalizing bs with
  | nil => simp [positiveRoutes] at hb
  | cons a as ih =>
    have ha := h a (by simp)
    have hs : EntryOrder as := by intro b hb; exact h b (by simp [hb])
    simp only [positiveRoutes,List.mem_cons,List.mem_map] at hb
    rcases hb with rfl|⟨cs,hcs,rfl⟩
    · exact ⟨ha.1.2.1,args_order_of_mem _ (by
        intro e he
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
        exact b.2.success_firstOrder (hs b hb).2)⟩
    · exact ⟨ha.1.1,ih hs _ hcs⟩

theorem zeroArgs_firstOrder (as : List (Forms × Forms)) (h : EntryOrder as) :
    (zeroArgs as).FirstOrder := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨(h a (by simp)).1.1,ih (by intro b hb; exact h b (by simp [hb]))⟩

theorem failureArgs_firstOrder (as : List (Forms × Forms)) (h : EntryOrder as) :
    (failureArgs as).FirstOrder := by
  match as with
  | [] => rw [failureArgs]; trivial
  | a::as =>
    rw [failureArgs]
    have ha := (h a (by simp)).1
    have hs : EntryOrder as := by intro b hb; exact h b (by simp [hb])
    have hn : EntryOrder (as.map (fun b => (b.2,b.2))) := by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      exact ⟨(hs c hc).2,(hs c hc).2⟩
    exact ⟨ha.2.2,⟨ha.1,failureArgs_firstOrder as hs⟩,
      ha.2.1,failureArgs_firstOrder _ hn⟩
termination_by as.length

theorem callForms_firstOrder (g : MGrammar) (fuel i : Nat) (as : List (Forms × Forms))
    (h : EntryOrder as) : (callForms g fuel i as).FirstOrder := by
  unfold callForms
  split
  · exact ⟨True.intro,True.intro,True.intro⟩
  · split
    · have hz := zeroArgs_firstOrder as h
      have hc : ∀ m, (choices ((positiveRoutes as).map
          (fun bs => MExp.call (ordinaryIndex g i m) bs))).FirstOrder := by
        intro m
        apply choices_firstOrder
        intro e he
        obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp he
        exact positiveRoutes_firstOrder as h bs hbs
      have hf : (choices ((positiveRoutes as).map
          (fun bs => MExp.andP (.call (ordinaryIndex g i .failure) bs)))).FirstOrder := by
        apply choices_firstOrder
        intro e he
        obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp he
        exact positiveRoutes_firstOrder as h bs hbs
      exact ⟨⟨hz,True.intro⟩,⟨hc _,hz,True.intro⟩,
        failureArgs_firstOrder as h,hf,hz,True.intro⟩
    · exact ⟨True.intro,True.intro,True.intro⟩

mutual
  theorem compile_firstOrder (g : MGrammar) (fuel : Nat) : ∀ e, (compile g fuel e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ => ⟨True.intro,True.intro,True.intro⟩
    | .lit w => by unfold compile; split <;> exact ⟨True.intro,True.intro,True.intro⟩
    | .param _ => ⟨⟨True.intro,True.intro⟩,⟨⟨True.intro,True.intro⟩,True.intro⟩,True.intro⟩
    | .call i as => callForms_firstOrder g fuel i _ (compileArgs_firstOrder g fuel as)
    | .seq a b => by
      have ha := compile_firstOrder g fuel a
      have hb := compile_firstOrder g fuel b
      have hn := compile_firstOrder g g.rules.length b
      exact ⟨⟨ha.1,hb.1⟩,⟨⟨ha.2.1,Forms.success_firstOrder _ hn⟩,ha.1,hb.2.1⟩,
        ha.2.2,⟨ha.2.1,hn.2.2⟩,ha.1,hb.2.2⟩
    | .alt a b => by
      have ha := compile_firstOrder g fuel a
      have hb := compile_firstOrder g fuel b
      exact ⟨⟨ha.1,ha.2.2,hb.1⟩,⟨ha.2.1,ha.2.2,hb.2.1⟩,ha.2.2,hb.2.2⟩
    | .notP a => by
      have ha := compile_firstOrder g fuel a
      exact ⟨ha.2.2,True.intro,Forms.success_firstOrder _ ha⟩
    | .star a => by
      have ha := compile_firstOrder g fuel a
      have hn := compile_firstOrder g g.rules.length a
      exact ⟨ha.2.2,⟨ha.2.1,hn.2.1,hn.2.2⟩,True.intro⟩
    | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => ⟨True.intro,True.intro,True.intro⟩
  theorem compileArgs_firstOrder (g : MGrammar) (fuel : Nat) : ∀ as, EntryOrder (compileArgs g fuel as)
    | [] => by intro a ha; cases ha
    | a::as => by
      intro b hb
      simp only [compileArgs,List.mem_cons] at hb
      rcases hb with rfl|hb
      · exact ⟨compile_firstOrder g fuel a,compile_firstOrder g g.rules.length a⟩
      · exact compileArgs_firstOrder g fuel as b hb
end

theorem target_firstOrder (g : MGrammar) : (target g).FirstOrder := by
  intro r hr
  obtain ⟨b,hb,hr⟩ := List.mem_flatMap.mp hr
  simp only [ruleBlock,List.mem_append] at hr
  rcases hr with hr|hr
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
    exact Forms.get_firstOrder _ (compile_firstOrder g _ _) m
  · obtain ⟨j,hj,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
    cases j with
    | zero => trivial
    | succ j => exact Forms.get_firstOrder _ (compile_firstOrder g _ _) m

theorem start_firstOrder (g : MGrammar) (e : MExp) : (start g e).FirstOrder :=
  Forms.success_firstOrder _ (compile_firstOrder g _ e)

end Shallot.MacroPeg.CBV.SequentialTotalSyntax
