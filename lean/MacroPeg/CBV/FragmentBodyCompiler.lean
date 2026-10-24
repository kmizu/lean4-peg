import MacroPeg.CBV.FragmentBodyForm

namespace Shallot.MacroPeg.CBV.FragmentBodyCompiler
open ReplayControlFusion (Plan)
open FragmentBodyForm (Body Form normalize raw lookup)
open ContinuationFamily (shift)
open FragmentOriginRecursive (render)

/-- All leaf copies and plans are computed from nested source bodies. -/
def tails (users : List Body) : List MExp := users.flatMap (fun u => (normalize u).leaves)
def emit (offset : Nat) : List Body → List Plan
  | [] => []
  | u::us => shift offset (normalize u).plan::emit (offset+(normalize u).leaves.length) us
def plans (users : List Body) := emit 0 users

def source (users : List Body) : MGrammar :=
  ⟨users.map (fun u => ⟨1,render (plans users) true false u.syntax⟩)++
    (tails users).map (fun b => ⟨1,render (plans users) true false (raw b)⟩)⟩
abbrev normalized (users : List Body) := FragmentOriginRecursive.source (plans users) (tails users)
abbrev target (users : List Body) := FragmentOriginRecursive.target (plans users) (tails users)
abbrev sourceRender (users : List Body) := render (plans users) true false
abbrev targetRender (users : List Body) := render (plans users) false false

theorem emit_length (offset : Nat) : ∀ users : List Body, (emit offset users).length=users.length
  | [] => rfl
  | u::us => by simp only [emit,List.length_cons,emit_length (offset+(normalize u).leaves.length) us]

theorem emit_bounded (offset total : Nat) (users : List Body)
    (h : offset+(tails users).length≤total) : ∀ P∈emit offset users, P.All (fun i => i<total) := by
  induction users generalizing offset with
  | nil => simp [emit]
  | cons u us ih =>
    intro P hp
    rcases List.mem_cons.mp hp with rfl | hp
    · apply ContinuationFamily.shift_all offset (normalize u).leaves.length total _ _ (normalize u).bounded
      have hl : offset+(normalize u).leaves.length≤total := by
        simp only [tails,List.flatMap_cons,List.length_append] at h; omega
      exact hl
    · apply ih (offset+(normalize u).leaves.length) _ P hp
      simpa only [tails,List.flatMap_cons,List.length_append,Nat.add_assoc] using h

theorem valid (users : List Body) : FragmentOriginRecursive.Valid (plans users) (tails users) :=
  emit_bounded 0 (tails users).length users (by omega)

theorem placed_leaf (ps : List Plan) (ambient pre group post : List MExp)
    (ha : ambient=pre++group++post) (i : Nat) (hi : i<group.length) :
    FragmentOriginRecursive.leaf ps ambient (pre.length+i)=render ps true false (lookup group i) := by
  unfold FragmentOriginRecursive.leaf lookup
  have hg := List.getElem?_eq_getElem hi
  rw [ha,List.getElem?_append_left (by simp only [List.length_append]; omega : pre.length+i<(pre++group).length),
    List.getElem?_append_right (by omega : pre.length≤pre.length+i)]
  simp only [Nat.add_sub_cancel_left,hg]
  exact (FragmentBodyForm.render_raw ps true group[i]).symm

/-- Normalize the actual body expressions, independently of any grammar
rows or caller values. Both sides use the same retained environment. -/
theorem normalized_bodies (ambient : List MExp) (ps : List Plan)
    (users : List Body) (pre post : List MExp) (ha : ambient=pre++tails users++post)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    (emit pre.length users).map (fun P => evV g x s T E (P.exp (FragmentOriginRecursive.leaf ps ambient)) p)=
      users.map (fun u => evV g x s T E (render ps true false u.syntax) p) := by
  induction users generalizing pre with
  | nil => rfl
  | cons u us ih =>
    simp only [emit,List.map_cons]
    congr 1
    · calc
        _ = evV g x s T E (render ps true false (normalize u).syntax) p := by
          rw [Plan.exp_eval,ContinuationFamily.shift_eval,FragmentBodyForm.Form.syntax,
            FragmentBodyForm.render_plan,Plan.exp_eval]
          apply Plan.eval_congr
          apply Plan.all_imp _ _ (normalize u).bounded
          intro i hi
          exact congrArg (fun e => evV g x s T E e p)
            (placed_leaf ps ambient pre (normalize u).leaves (tails us++post)
              (by simpa only [tails,List.flatMap_cons,List.append_assoc] using ha) i hi)
        _ = _ := FragmentBodyForm.evaluator_eq ps true g x s T E u p
    · have h := ih (pre++(normalize u).leaves)
        (by simpa only [tails,List.flatMap_cons,List.append_assoc] using ha)
      simpa only [List.length_append] using h

theorem headers (users : List Body) (i : Nat) :
    (ruleAtM (source users).rules i).map MRule.arity=(ruleAtM (normalized users).rules i).map MRule.arity := by
  have h : (source users).rules.map MRule.arity=(normalized users).rules.map MRule.arity := by
    simp only [source,normalized,FragmentOriginRecursive.source,List.map_append,List.map_map]
    simp only [Function.comp_def,List.map_const',plans,emit_length]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (users : List Body) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    (source users).rules.map (fun r => evV g x s T E r.body p)=
      (normalized users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [source,normalized,FragmentOriginRecursive.source,List.map_append,List.map_map,Function.comp_def]
  have h := normalized_bodies (tails users) (plans users) users [] [] (by simp) g x s T E p
  have ht : (fun b => evV g x s T E (render (plans users) true false (raw b)) p)=
      (fun b => evV g x s T E (RuntimeShiftFilter.scanner.seq (.seq (.param 0) (render (plans users) true false b))) p) := by
    funext b; rw [FragmentBodyForm.render_raw]
  rw [ht]
  exact congrArg (fun a => a++(tails users).map (fun b => evV g x s T E
    (.seq RuntimeShiftFilter.scanner (.seq (.param 0) (render (plans users) true false b))) p)) h.symm

theorem tables_eq (users : List Body) (x : List Char) (s : Strategy) : ∀ k,
    tblV (source users) x s k=tblV (normalized users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers users i
    simp only [tblV]
    cases hs : ruleAtM (source users).rules i with
    | none =>
      cases ht : ruleAtM (normalized users).rules i with
      | none => rfl
      | some r => simp [hs,ht] at hh
    | some r =>
      cases ht : ruleAtM (normalized users).rules i with
      | none => simp [hs,ht] at hh
      | some t =>
        apply List.map_congr_left
        intro p _
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results users (normalized users) x s (tblV (normalized users) x s k) E p)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hs,ht,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (source users) (normalized users)
          (headers users) x s _ E r.body p).trans hb

theorem evaluator_eq (users : List Body) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (source users) x s (tblV (source users) x s k) E e p=
      evV (normalized users) x s (tblV (normalized users) x s k) E e p := by
  rw [tables_eq users x s k]
  exact ContinuationGrammar.eval_headers (source users) (normalized users) (headers users) x s _ E e p

theorem source_firstOrder (users : List Body) : (source users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact FragmentOriginRecursive.render_firstOrder _ true false u.syntax
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact FragmentOriginRecursive.render_firstOrder _ true false (raw b)

/-- Close normalization and recursive capture transfer on all unchanged
inputs. No body equivalence, table-row relation, or layout certificate is
provided by a caller: the plan bounds are generated from source syntax. -/
theorem observations_iff (users : List Body) (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source users) .callByValuePar (sourceRender users e) x r ↔
      SObs (target users) .callByValueSeq (targetRender users e) x r := by
  have hnorm : SObs (source users) .callByValuePar (sourceRender users e) x r ↔
      SObs (normalized users) .callByValuePar (sourceRender users e) x r := by
    rw [←decideObsV_iff (source_firstOrder users) (by decide) (FragmentOriginRecursive.render_firstOrder _ true false e),
      ←decideObsV_iff (FragmentOriginRecursive.source_firstOrder _ _) (by decide)
        (FragmentOriginRecursive.render_firstOrder _ true false e)]
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (source users) (normalized users) x .callByValuePar .callByValuePar
      (sourceRender users e) (sourceRender users e) (fun k => evaluator_eq users x .callByValuePar k [] _ x.length)]
  exact hnorm.trans (FragmentOriginRecursive.observations_iff _ _ (valid users) e x r)

theorem language_translation (users : List Body) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source users) .callByValuePar (sourceRender users e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target users,targetRender users e,FragmentOriginRecursive.target_firstOrder _ _,
    FragmentOriginRecursive.render_firstOrder _ false false e,fun x => observations_iff users e x (some [])⟩

end Shallot.MacroPeg.CBV.FragmentBodyCompiler
