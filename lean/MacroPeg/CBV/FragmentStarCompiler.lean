import MacroPeg.CBV.FragmentStarForm

namespace Shallot.MacroPeg.CBV.FragmentStarCompiler
open ReplayControlFusion (Plan)
open FragmentStarForm (Body Form normalize raw lookup)
open FragmentStuckRecursive (render)

/-- Missing local captures are divergence, and use the single global
capture-independent leaf rather than an A;param0 wrapper. -/
def address (total offset : Nat) (ls : List (Option MExp)) (i : Nat) : Nat :=
  match ls[i]? with | some (some _) => offset+i | _ => total

def relocate (f : Nat → Nat) : Plan → Plan
  | .leaf i => .leaf (f i)
  | .alt a b => .alt (relocate f a) (relocate f b)
  | .guard a b => .guard (relocate f a) (relocate f b)
  | .notP a => .notP (relocate f a)

theorem relocate_bounded (n total offset : Nat) (ls : List (Option MExp))
    (hl : ls.length=n) (ho : offset+n≤total) : ∀ P,
    P.All (fun i => i<n) → (relocate (address total offset ls) P).All (fun i => i≤total)
  | .leaf i, hi => by
    change i<n at hi
    change address total offset ls i≤total
    unfold address
    split <;> omega
  | .alt a b, h | .guard a b, h =>
    ⟨relocate_bounded n total offset ls hl ho a h.1,relocate_bounded n total offset ls hl ho b h.2⟩
  | .notP a, h => relocate_bounded n total offset ls hl ho a h

theorem relocate_exp (f : Nat → Nat) (L : Nat → MExp) : ∀ P,
    (relocate f P).exp L=P.exp (fun i => L (f i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [relocate,Plan.exp,relocate_exp f L a,relocate_exp f L b]
  | .notP a => by simp only [relocate,Plan.exp,relocate_exp f L a]

def tails (users : List Body) : List MExp :=
  (users.flatMap (fun u => (normalize u).leaves)).map (fun b => b.getD .eps)
def emit (total offset : Nat) : List Body → List Plan
  | [] => []
  | u::us => relocate (address total offset (normalize u).leaves) (normalize u).plan::
      emit total (offset+(normalize u).leaves.length) us
def plans (users : List Body) := emit (tails users).length 0 users
abbrev core (users : List Body) := FragmentStuckRecursive.source (plans users) (tails users)
abbrev target (users : List Body) := FragmentStuckRecursive.target (plans users) (tails users)
abbrev sourceRender (users : List Body) := render (tails users).length (plans users) true false
abbrev targetRender (users : List Body) := render (tails users).length (plans users) false false

def source (users : List Body) : MGrammar :=
  ⟨users.map (fun u => ⟨1,sourceRender users u.syntax⟩)++(core users).rules.drop users.length⟩

theorem emit_length (total offset : Nat) : ∀ users : List Body, (emit total offset users).length=users.length
  | [] => rfl
  | u::us => by simp only [emit,List.length_cons,emit_length total (offset+(normalize u).leaves.length) us]

theorem emit_bounded (total offset : Nat) (users : List Body) (h : offset+(tails users).length≤total) :
    ∀ P∈emit total offset users, P.All (fun i => i≤total) := by
  induction users generalizing offset with
  | nil => simp [emit]
  | cons u us ih =>
    intro P hp
    have hl : (tails (u::us)).length=(normalize u).leaves.length+(tails us).length := by
      simp [tails]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact relocate_bounded _ _ _ _ rfl (by omega) _ (normalize u).bounded
    · exact ih (offset+(normalize u).leaves.length) (by omega) P hp

theorem valid (users : List Body) : FragmentStuckRecursive.Valid (plans users) (tails users) :=
  emit_bounded (tails users).length 0 users (by omega)

theorem placed_leaf (ps : List Plan) (ambient pre post : List MExp) (group : List (Option MExp))
    (ha : ambient=pre++group.map (fun b => b.getD .eps)++post) (i : Nat) (hi : i<group.length) :
    FragmentStuckRecursive.leaf ps ambient (address ambient.length pre.length group i)=
      render ambient.length ps true false (lookup group i) := by
  have hg := List.getElem?_eq_getElem hi
  cases he : group[i] with
  | none =>
    simp only [address,hg,he,lookup,raw]
    simp [FragmentStuckRecursive.leaf,FragmentStuckRecursive.stuck,render]
  | some b =>
    have hb : ambient[pre.length+i]?=some b := by
      rw [ha,List.getElem?_append_left (by simp; omega : pre.length+i<(pre++group.map (fun b => b.getD .eps)).length),
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left,List.getElem?_map,hg,he,Option.map_some,Option.getD_some]
    simp only [address,hg,he,lookup,FragmentStuckRecursive.leaf,hb]
    exact (FragmentStarForm.render_raw ambient.length ps true b).symm

private theorem exp_congr (L R : Nat → MExp) : ∀ (P : Plan), P.All (fun i => L i=R i) → P.exp L=P.exp R
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => by simp only [Plan.exp,exp_congr L R a h.1,exp_congr L R b h.2]
  | .notP a, h => by simp only [Plan.exp,exp_congr L R a h]

theorem normalized_bodies (ambient : List MExp) (ps : List Plan) (users : List Body) (pre post : List MExp)
    (ha : ambient=pre++tails users++post) (g : MGrammar) (x : List Char) (s : Strategy)
    (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    (emit ambient.length pre.length users).map (fun P => evV g x s T E (P.exp (FragmentStuckRecursive.leaf ps ambient)) p)=
      users.map (fun u => evV g x s T E (render ambient.length ps true false u.syntax) p) := by
  induction users generalizing pre with
  | nil => rfl
  | cons u us ih =>
    simp only [emit,List.map_cons]
    congr 1
    · calc
        _ = evV g x s T E (render ambient.length ps true false (normalize u).syntax) p := by
          rw [relocate_exp,FragmentStarForm.Form.syntax,FragmentStarForm.render_plan]
          apply congrArg (fun e => evV g x s T E e p)
          apply exp_congr
          apply Plan.all_imp _ _ (normalize u).bounded
          intro i hi
          exact placed_leaf ps ambient pre (tails us++post) (normalize u).leaves
            (by simpa only [tails,List.flatMap_cons,List.map_append,List.append_assoc] using ha) i hi
        _ = _ := FragmentStarForm.evaluator_eq ambient.length ps true g x s hs T hT E u p hp
    · have h := ih (pre++(normalize u).leaves.map (fun b => b.getD .eps))
        (by simpa only [tails,List.flatMap_cons,List.map_append,List.append_assoc] using ha)
      simpa only [List.length_append,List.length_map] using h

private theorem rules (users : List Body) : (core users).rules=
    (plans users).map (fun P => ⟨1,P.exp (FragmentStuckRecursive.leaf (plans users) (tails users))⟩)++
      (core users).rules.drop users.length := by
  have hl : (plans users).length=users.length := emit_length _ _ users
  simp only [core,FragmentStuckRecursive.source]
  rw [←hl]
  simp only [List.drop_append,List.length_map,←List.map_drop,List.drop_length,Nat.sub_self,Nat.zero_sub,
    List.drop_zero,List.nil_append,List.map_nil]

theorem headers (users : List Body) (i : Nat) :
    (ruleAtM (source users).rules i).map MRule.arity=(ruleAtM (core users).rules i).map MRule.arity := by
  have h : (source users).rules.map MRule.arity=(core users).rules.map MRule.arity := by
    rw [source]
    conv => rhs; rw [rules]
    simp only [List.map_append,List.map_map,Function.comp_def,List.map_const',plans,emit_length]
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using congrArg (fun l => l[i]?) h

theorem body_results (users : List Body) (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    (source users).rules.map (fun r => evV g x s T E r.body p)=
      (core users).rules.map (fun r => evV g x s T E r.body p) := by
  rw [source]
  conv => rhs; rw [rules]
  simp only [List.map_append,List.map_map,Function.comp_def]
  have h := normalized_bodies (tails users) (plans users) users [] [] (by simp) g x s hs T hT E p hp
  simpa only [plans,List.length_nil,List.nil_append,List.append_nil,sourceRender] using
    congrArg (fun l => l++((core users).rules.drop users.length).map (fun r => evV g x s T E r.body p)) h.symm


theorem tables_eq (users : List Body) (x : List Char) (s : Strategy) (hs : s≠.callByName) : ∀ k,
    tblV (source users) x s k=tblV (core users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers users i
    simp only [tblV]
    cases hrow : ruleAtM (source users).rules i with
    | none =>
      cases ht : ruleAtM (core users).rules i with
      | none => rfl
      | some r => simp [hrow,ht] at hh
    | some r =>
      cases ht : ruleAtM (core users).rules i with
      | none => simp [hrow,ht] at hh
      | some t =>
        apply List.map_congr_left
        intro p hp
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results users (core users) x s hs (tblV (core users) x s k) (tblV_sound (FragmentStuckRecursive.source_firstOrder _ _) hs k) E p (by have := List.mem_range.mp hp; omega))
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hrow,ht,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (source users) (core users)
          (headers users) x s _ E r.body p).trans hb

theorem evaluator_eq (users : List Body) (x : List Char) (s : Strategy) (hs : s≠.callByName) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source users) x s (tblV (source users) x s k) E e p=
      evV (core users) x s (tblV (core users) x s k) E e p := by
  rw [tables_eq users x s hs k]
  exact ContinuationGrammar.eval_headers (source users) (core users) (headers users) x s _ E e p

theorem source_firstOrder (users : List Body) : (source users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact FragmentStuckRecursive.render_firstOrder _ _ true false u.syntax
  · exact FragmentStuckRecursive.source_firstOrder _ _ r (List.mem_of_mem_drop hr)

/-- Close normalization and recursive capture transfer on all unchanged
inputs. No body equivalence, table-row relation, or layout certificate is
provided by a caller: the plan bounds are generated from source syntax. -/
theorem observations_iff (users : List Body) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source users) .callByValuePar (sourceRender users e) x r ↔
      SObs (target users) .callByValueSeq (targetRender users e) x r := by
  have hnorm : SObs (source users) .callByValuePar (sourceRender users e) x r ↔
      SObs (core users) .callByValuePar (sourceRender users e) x r := by
    rw [←decideObsV_iff (source_firstOrder users) (by decide) (FragmentStuckRecursive.render_firstOrder _ _ true false e),
      ←decideObsV_iff (FragmentStuckRecursive.source_firstOrder _ _) (by decide)
        (FragmentStuckRecursive.render_firstOrder _ _ true false e)]
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (source users) (core users) x .callByValuePar .callByValuePar
      (sourceRender users e) (sourceRender users e) (fun k => evaluator_eq users x .callByValuePar (by decide) k [] _ x.length)]
  exact hnorm.trans (FragmentStuckRecursive.observations_iff _ _ (valid users) e x r)

theorem language_translation (users : List Body) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source users) .callByValuePar (sourceRender users e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target users,targetRender users e,FragmentStuckRecursive.target_firstOrder _ _,
    FragmentStuckRecursive.render_firstOrder _ _ false false e,fun x => observations_iff users e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentStarCompiler
