import MacroPeg.CBV.LeafContinuation
import MacroPeg.CBV.ContinuationGrammar

/-! Assemble distinct consuming control bodies into one fixed origin-control
family. Each user has its own leaves and continuation. -/
namespace Shallot.MacroPeg.CBV.ContinuationFamily
open ReplayControlFusion (Plan)
open OriginControlNormalization
open LeafContinuation
abbrev Arg := RecursiveArgumentCompiler.Expr
open RegularCaptureProduct (Node)

def shift (offset : Nat) : Plan → Plan
  | .leaf i => .leaf (offset+i)
  | .alt a b => .alt (shift offset a) (shift offset b)
  | .guard a b => .guard (shift offset a) (shift offset b)
  | .notP a => .notP (shift offset a)

theorem shift_eval (offset : Nat) (L : Nat → Res) (p : Nat) :
    ∀ P, (shift offset P).eval L p=P.eval (fun i => L (offset+i)) p
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [shift,Plan.eval,shift_eval offset L p a,shift_eval offset L p b]
  | .notP a => by simp only [shift,Plan.eval,shift_eval offset L p a]

theorem shift_all (offset n total : Nat) (h : offset+n≤total) :
    ∀ P, P.All (fun i => i<n) → (shift offset P).All (fun i => i<total)
  | .leaf i, hi => by change i<n at hi; change offset+i<total; omega
  | .alt a b, hp | .guard a b, hp => ⟨shift_all offset n total h a hp.1,shift_all offset n total h b hp.2⟩
  | .notP a, hp => shift_all offset n total h a hp

structure User where
  leaves : List Leaf
  control : Plan
  tail : Option Arg

def User.group (u : User) : List Leaf :=
  match u.tail with | none => u.leaves | some tail => continued u.leaves tail
def User.plan (u : User) : Plan :=
  match u.tail with | none => u.control | some _ => chain u.leaves.length u.control
def leaves (users : List User) : List Leaf := users.flatMap User.group

def emit (offset : Nat) : List User → List Plan
  | [] => []
  | u::us => shift offset u.plan :: emit (offset+u.group.length) us

def specs (users : List User) : List Plan := emit 0 users

theorem emit_length (offset : Nat) : ∀ users, (emit offset users).length=users.length
  | [] => rfl
  | u::us => by simp only [emit,List.length_cons,emit_length (offset+u.group.length) us]

def User.Shape (u : User) : Prop := u.control.All (fun i => i<u.leaves.length) ∧
  ∀ tail, u.tail=some tail → Consumer u.control
def Shapes (users : List User) : Prop := ∀ u∈users, u.Shape

def Valid (nodes : List Node) (users : List User) : Prop := Shapes users ∧ ∀ u∈users,
  LeavesValid nodes u.leaves (specs users) ∧ ∀ tail, u.tail=some tail →
  OriginControlNormalization.Valid nodes (specs users) tail ∧
  ∀ r∈u.leaves, r.shift=none → OriginControlNormalization.Closed tail

theorem local_bounded (u : User) (hv : u.Shape) : u.plan.All (fun i => i<u.group.length) := by
  cases ht : u.tail with
  | none => simpa only [User.plan,User.group,ht] using hv.1
  | some tail =>
    simpa only [User.plan,User.group,ht,continued_length] using
      chain_bounded u.leaves.length u.control (hv.2 tail ht) hv.1

theorem emit_bounded (users : List User) (hv : Shapes users) (offset total : Nat)
    (ht : offset+(leaves users).length≤total) :
    ∀ P∈emit offset users, P.All (fun i => i<total) := by
  induction users generalizing offset with
  | nil => simp [emit]
  | cons u us ih =>
    have hu := hv u (by simp)
    have hus : Shapes us := fun v hm => hv v (by simp [hm])
    intro P hp
    simp only [emit,List.mem_cons] at hp
    rcases hp with rfl|hp
    · exact shift_all offset u.group.length total (by
        change offset+(u.group++leaves us).length≤total at ht
        simp only [List.length_append] at ht
        omega) _ (local_bounded u hu)
    · apply ih hus (offset+u.group.length) _ P hp
      change offset+(u.group++leaves us).length≤total at ht
      simpa only [List.length_append,Nat.add_assoc] using ht

theorem plans_valid (_nodes : List Node) (users : List User) (hv : Shapes users) :
    PlansValid (leaves users) (specs users) :=
  emit_bounded users hv 0 (leaves users).length (by omega)

theorem leaves_valid (nodes : List Node) (users : List User) (hv : Valid nodes users) :
    LeavesValid nodes (leaves users) (specs users) := by
  intro r hr
  obtain ⟨u,hu,hr⟩ := List.mem_flatMap.mp hr
  cases ht : u.tail with
  | none =>
    have hm : r∈u.leaves := by simpa only [User.group,ht] using hr
    exact (hv.2 u hu).1 r hm
  | some tail =>
    have hm : r∈continued u.leaves tail := by simpa only [User.group,ht] using hr
    exact continued_valid nodes u.leaves (specs users) (hv.2 u hu).1 tail
      ((hv.2 u hu).2 tail ht).1 ((hv.2 u hu).2 tail ht).2 r hm

/-- Lookup of a local leaf in the actual combined source syntax. -/
theorem placed_leaf (nodes : List Node) (ambient : List Leaf) (ps : List Plan)
    (pre group post : List Leaf) (ha : ambient=pre++group++post) (i : Nat) (hi : i<group.length) :
    sourceLeaf nodes ambient ps (pre.length+i)=render nodes ambient ps (lookup group i) := by
  rw [←lookup_render nodes ambient ps (pre.length+i) (by rw [ha]; simp only [List.length_append]; omega)]
  apply congrArg
  unfold lookup
  rw [ha]
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega : pre.length+i<(pre++group).length)]
  rw [List.getElem?_append_right (by omega : pre.length≤pre.length+i)]
  simp only [Nat.add_sub_cancel_left]

def body (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (u : User) : MExp :=
  match u.tail with
  | none => u.control.exp (fun i => render nodes ambient ps (lookup u.leaves i))
  | some tail => .seq (u.control.exp (fun i => render nodes ambient ps (lookup u.leaves i))) (render nodes ambient ps tail)

theorem user_body_eq (nodes : List Node) (ambient : List Leaf) (ps : List Plan)
    (u : User) (hv : u.Shape) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (u.plan.exp (fun i => render nodes ambient ps (lookup u.group i))) p=
    evV g x s T E (body nodes ambient ps u) p := by
  cases ht : u.tail with
  | none => simp only [User.plan,User.group,body,ht]
  | some tail =>
    simpa only [User.plan,User.group,body,ht] using
      body_eq nodes ambient u.leaves ps u.control (hv.2 tail ht) hv.1 tail g x s T E p

theorem bodies_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan)
    (users : List User) (hv : Shapes users) (pre post : List Leaf)
    (ha : ambient=pre++leaves users++post)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    (emit pre.length users).map (fun P => evV g x s T E (P.exp (sourceLeaf nodes ambient ps)) p)=
    users.map (fun u => evV g x s T E (body nodes ambient ps u) p) := by
  induction users generalizing pre with
  | nil => rfl
  | cons u us ih =>
    have hu := hv u (by simp)
    have hus : Shapes us := fun v hm => hv v (by simp [hm])
    simp only [emit,List.map_cons]
    congr 1
    · calc
        _ = evV g x s T E (u.plan.exp
              (fun i => render nodes ambient ps (lookup u.group i))) p := by
          rw [Plan.exp_eval,shift_eval,Plan.exp_eval]
          apply Plan.eval_congr
          apply Plan.all_imp _ _ (local_bounded u hu)
          intro i hi
          have hg : i<u.group.length := hi
          exact congrArg (fun e => evV g x s T E e p)
            (placed_leaf nodes ambient ps pre u.group (leaves us++post)
              (by simpa only [leaves,List.flatMap_cons,List.append_assoc] using ha) i hg)
        _ = _ := user_body_eq nodes ambient ps u hu g x s T E p
    · have h := ih hus (pre++u.group) (by simpa only [leaves,List.flatMap_cons,List.append_assoc] using ha)
      simpa only [List.length_append] using h


def sourceRules (nodes : List Node) (users : List User) : List MRule :=
  users.map (fun u => ⟨1,body nodes (leaves users) (specs users) u⟩)
def sourceGrammar (nodes : List Node) (users : List User) : MGrammar :=
  FilteredOverlapCaller.extend nodes (machine (leaves users) (specs users)) (sourceRules nodes users)
abbrev normalizedGrammar (nodes : List Node) (users : List User) :=
  OriginControlNormalization.sourceGrammar nodes (leaves users) (specs users)
abbrev sourceRender (nodes : List Node) (users : List User) := render nodes (leaves users) (specs users)
abbrev targetGrammar (nodes : List Node) (users : List User) :=
  OriginControlNormalization.targetGrammar nodes (leaves users) (specs users)
abbrev targetRender (nodes : List Node) (users : List User) :=
  OriginControlNormalization.targetRender nodes (leaves users) (specs users)

theorem headers (nodes : List Node) (users : List User) (i : Nat) :
    (ruleAtM (sourceGrammar nodes users).rules i).map MRule.arity=
    (ruleAtM (normalizedGrammar nodes users).rules i).map MRule.arity := by
  have h : (sourceGrammar nodes users).rules.map MRule.arity=
      (normalizedGrammar nodes users).rules.map MRule.arity := by
    simp only [sourceGrammar,normalizedGrammar,OriginControlNormalization.sourceGrammar,
      FilteredOverlapCaller.extend,sourceRules,OriginControlNormalization.sourceRules,List.map_append,List.map_map]
    congr 1
    simp only [Function.comp_def,List.map_const',specs,emit_length]
  have hi := congrArg (fun l => l[i]?) h
  simpa only [List.getElem?_map,ruleAtM_eq_getElem?] using hi

theorem body_results (nodes : List Node) (users : List User) (hv : Shapes users)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    (sourceGrammar nodes users).rules.map (fun r => evV g x s T E r.body p)=
    (normalizedGrammar nodes users).rules.map (fun r => evV g x s T E r.body p) := by
  simp only [sourceGrammar,normalizedGrammar,OriginControlNormalization.sourceGrammar,
    FilteredOverlapCaller.extend,sourceRules,OriginControlNormalization.sourceRules,List.map_append,List.map_map,
    Function.comp_def]
  congr 1
  exact (bodies_eval nodes (leaves users) (specs users) users hv [] [] (by simp) g x s T E p).symm

theorem tables_eq (nodes : List Node) (users : List User) (hv : Shapes users)
    (x : List Char) (s : Strategy) : ∀ k,
    tblV (sourceGrammar nodes users) x s k=tblV (normalizedGrammar nodes users) x s k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i E
    have hh := headers nodes users i
    simp only [tblV]
    cases hs : ruleAtM (sourceGrammar nodes users).rules i with
    | none =>
      cases ht : ruleAtM (normalizedGrammar nodes users).rules i with
      | none => rfl
      | some r => simp [hs,ht] at hh
    | some r =>
      cases ht : ruleAtM (normalizedGrammar nodes users).rules i with
      | none => simp [hs,ht] at hh
      | some t =>
        apply List.map_congr_left
        intro p _
        rw [ih]
        have hb := congrArg (fun l => l[i]?)
          (body_results nodes users hv (normalizedGrammar nodes users) x s (tblV (normalizedGrammar nodes users) x s k) E p)
        simp only [List.getElem?_map,←ruleAtM_eq_getElem?,hs,ht,Option.map_some,Option.some.injEq] at hb
        exact (ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users)
          (headers nodes users) x s _ E r.body p).trans hb

theorem evaluator_eq (nodes : List Node) (users : List User) (hv : Shapes users)
    (x : List Char) (s : Strategy) (k : Nat) (E : List (List Char)) (e : MExp) (p : Nat) :
    evV (sourceGrammar nodes users) x s (tblV (sourceGrammar nodes users) x s k) E e p=
    evV (normalizedGrammar nodes users) x s (tblV (normalizedGrammar nodes users) x s k) E e p := by
  rw [tables_eq nodes users hv x s k]
  exact ContinuationGrammar.eval_headers (sourceGrammar nodes users) (normalizedGrammar nodes users)
    (headers nodes users) x s _ E e p

theorem source_firstOrder (nodes : List Node) (users : List User) : (sourceGrammar nodes users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact RegularCaptureProduct.grammar_firstOrder nodes (machine (leaves users) (specs users)) r hr
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    change (body nodes (leaves users) (specs users) u).FirstOrder
    unfold body
    cases u.tail with
    | none => exact Plan.exp_firstOrder (fun i => render_firstOrder nodes (leaves users) (specs users) (lookup u.leaves i)) u.control
    | some tail => exact ⟨Plan.exp_firstOrder (fun i => render_firstOrder nodes (leaves users) (specs users) (lookup u.leaves i)) u.control,
        render_firstOrder nodes (leaves users) (specs users) tail⟩

theorem normalized_observations_iff (nodes : List Node) (users : List User) (hv : Shapes users)
    (e : Arg) (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (normalizedGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest := by
  have hd : decideObsV .callByValuePar (sourceGrammar nodes users) x (sourceRender nodes users e)=
      decideObsV .callByValuePar (normalizedGrammar nodes users) x (sourceRender nodes users e) := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes users) (normalizedGrammar nodes users) x
      .callByValuePar .callByValuePar (sourceRender nodes users e) (sourceRender nodes users e)
      (fun k => evaluator_eq nodes users hv x .callByValuePar k [] _ x.length)]
  rw [←decideObsV_iff (source_firstOrder nodes users) (by decide) (render_firstOrder nodes (leaves users) (specs users) e),
    ←decideObsV_iff (OriginControlNormalization.source_firstOrder nodes (leaves users) (specs users)) (by decide)
      (render_firstOrder nodes (leaves users) (specs users) e),hd]

/-- Actual consuming source bodies, rather than a replacement-source premise,
translate to one fixed first-order Seq grammar on the original strings. -/
theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hv : Valid nodes users) (e : Arg)
    (he : OriginControlNormalization.Valid nodes (specs users) e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x rest ↔
    SObs (targetGrammar nodes users) .callByValueSeq (targetRender nodes users e) x rest :=
  (normalized_observations_iff nodes users hv.1 e x rest).trans
    (OriginControlNormalization.observations_iff nodes hNodes (leaves users) (specs users)
      (plans_valid nodes users hv.1) (leaves_valid nodes users hv) e he x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hv : Valid nodes users) (e : Arg)
    (he : OriginControlNormalization.Valid nodes (specs users) e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (sourceGrammar nodes users) .callByValuePar (sourceRender nodes users e) x (some []) ↔
    SObs g .callByValueSeq start x (some []) :=
  ⟨targetGrammar nodes users,targetRender nodes users e,
    RecursiveArgumentCompiler.seq_firstOrder nodes (coreUsers (leaves users) (specs users)),
    RecursiveArgumentCompiler.plain_firstOrder nodes (coreUsers (leaves users) (specs users)) []
      (normalize (leaves users) (specs users) e),
    fun x => observations_iff nodes hNodes users hv e he x (some [])⟩

end Shallot.MacroPeg.CBV.ContinuationFamily
