import MacroPeg.CBV.ProfileControl

/-! A fixed unary compiler with explicit, structurally nested user arguments.
Plain rows and finite-state product rows are generated together. Semantic
correspondence of all recursive rows is established separately. -/
namespace Shallot.MacroPeg.CBV.RecursiveArgumentCompiler
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)

inductive Expr where
  | lit (w : List Char)
  | param (k : Nat)
  | helper (i : Nat)
  | user (i : Nat) (arg : Expr)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | star (a : Expr)
  | notP (a : Expr)

structure User where
  shift : List Char
  body : Expr

def shifts (users : List User) : List (List Char) := users.map User.shift
abbrev machine (users : List User) := CaptureMachineFamily.machine (shifts users)
abbrev Mode := Option (Nat × Nat)

def modes (D : Machine) : List Mode :=
  none::(List.range D.width).flatMap (fun q => (List.range D.width).map (fun r => some (q,r)))

def keys (users : List User) : List (Nat × List Nat × Mode) :=
  (List.range users.length).flatMap (fun i => (profiles (machine users)).flatMap (fun P =>
    (modes (machine users)).map (fun m => (i,P,m))))

def address (nodes : List Node) (users : List User) (i : Nat) (P : List Nat) (m : Mode) : Nat :=
  (grammar nodes (machine users)).rules.length+(keys users).idxOf (i,P,m)

def parRender (nodes : List Node) (users : List User) : Expr → MExp
  | .lit w => .lit w
  | .param k => .param k
  | .helper i => .call i []
  | .user i a => if i<users.length then
      .call ((grammar nodes (machine users)).rules.length+i) [parRender nodes users a]
    else MExp.failAlways
  | .seq a b => .seq (parRender nodes users a) (parRender nodes users b)
  | .alt a b => .alt (parRender nodes users a) (parRender nodes users b)
  | .star a => .star (parRender nodes users a)
  | .notP a => .notP (parRender nodes users a)

mutual
  def plain (nodes : List Node) (users : List User) (S : List (List Nat)) : Expr → MExp
    | .lit w => .lit w
    | .param k => .param k
    | .helper i => .call i []
    | .user i a => if i<users.length then
        ProfileControl.select (machine users) (plain nodes users S a) (fun q r => filter nodes users S a q r)
          (fun P => .call (address nodes users i P none) [plain nodes users S a])
      else MExp.failAlways
    | .seq a b => .seq (plain nodes users S a) (plain nodes users S b)
    | .alt a b => .alt (plain nodes users S a) (plain nodes users S b)
    | .star a => .star (plain nodes users S a)
    | .notP a => .notP (plain nodes users S a)

  def filter (nodes : List Node) (users : List User) (S : List (List Nat)) : Expr → Nat → Nat → MExp
    | .lit w, q, r => .seq (.lit w) (if some (run (machine users) q w)=some r then .eps else MExp.failAlways)
    | .param k, q, r => .seq (.param k) (if DependentCaptureFilter.nextState S k q=some r then .eps else MExp.failAlways)
    | .helper i, q, r => call nodes (machine users) i q r
    | .user i a, q, r => if i<users.length then
        ProfileControl.select (machine users) (plain nodes users S a) (fun q r => filter nodes users S a q r)
          (fun P => .call (address nodes users i P (some (q,r))) [plain nodes users S a])
      else MExp.failAlways
    | .seq a b, q, r => choice ((List.range (machine users).width).map (fun t =>
        .seq (filter nodes users S a q t) (filter nodes users S b t r)))
    | .alt a b, q, r => RootObservation.branch (.andP (plain nodes users S a))
        (filter nodes users S a q r) (filter nodes users S b q r)
    | .star a, q, r => GeneralStarFilter.filter (machine users).width (plain nodes users S a)
        (fun q r => filter nodes users S a q r) q r
    | .notP a, q, r => .seq (.notP (plain nodes users S a)) (if some q=some r then .eps else MExp.failAlways)
end

def phase (users : List User) (i : Nat) (P : List Nat) : Nat :=
  P[CaptureMachineFamily.start (shifts users) i]?.getD 0-CaptureMachineFamily.start (shifts users) i

def tailPrefix (users : List User) (i : Nat) (P : List Nat) (r : User) : MExp :=
  if r.shift=[] then .lit [] else if phase users i P<r.shift.length then .lit (PeriodicCaptureMachine.phase r.shift (phase users i P)) else MExp.failAlways

def targetBody (nodes : List Node) (users : List User) (i : Nat) (P : List Nat) (m : Mode) (r : User) : MExp :=
  .seq (tailPrefix users i P r) (match m with
    | none => plain nodes users [P] r.body
    | some (q,t) => filter nodes users [P] r.body
        (run (machine users) (P[q]?.getD 0) (PeriodicCaptureMachine.phase r.shift (phase users i P))) t)

def sourceRules (nodes : List Node) (users : List User) : List MRule :=
  users.map (fun r => ⟨1,.seq (.seq (.lit r.shift) (.param 0)) (parRender nodes users r.body)⟩)
def targetRules (nodes : List Node) (users : List User) : List MRule :=
  (keys users).map (fun (i,P,m) => ⟨1,match users[i]? with
    | some r => targetBody nodes users i P m r | none => MExp.failAlways⟩)
abbrev parGrammar (nodes : List Node) (users : List User) :=
  FilteredOverlapCaller.extend nodes (machine users) (sourceRules nodes users)
abbrev seqGrammar (nodes : List Node) (users : List User) :=
  FilteredOverlapCaller.extend nodes (machine users) (targetRules nodes users)
abbrev helpers (nodes : List Node) (users : List User) := component nodes (machine users)
abbrev parTable (nodes : List Node) (users : List User) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes users) (parGrammar nodes users) x .callByValuePar k
abbrev seqTable (nodes : List Node) (users : List User) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes users) (seqGrammar nodes users) x .callByValueSeq k

def Valid (nodes : List Node) (users : List User) : Expr → Prop
  | .helper i => i<nodes.length
  | .user i a => i<users.length ∧ Valid nodes users a
  | .seq a b | .alt a b => Valid nodes users a ∧ Valid nodes users b
  | .star a | .notP a => Valid nodes users a
  | .lit _ | .param _ => True

def UsersValid (nodes : List Node) (users : List User) : Prop :=
  ∀ r∈users, Valid nodes users r.body

theorem parRender_firstOrder (nodes : List Node) (users : List User) :
    ∀ e, (parRender nodes users e).FirstOrder
  | .lit _ | .param _ | .helper _ => True.intro
  | .user i a => by simp only [parRender]; split; exact ⟨parRender_firstOrder nodes users a,True.intro⟩; trivial
  | .seq a b | .alt a b => ⟨parRender_firstOrder nodes users a,parRender_firstOrder nodes users b⟩
  | .star a | .notP a => parRender_firstOrder nodes users a

mutual
  theorem plain_firstOrder (nodes : List Node) (users : List User) (S : List (List Nat)) :
      ∀ e, (plain nodes users S e).FirstOrder
    | .lit _ | .param _ | .helper _ => True.intro
    | .user i a => by
      simp only [plain]
      split
      · exact ProfileControl.select_firstOrder _ _ _ (plain_firstOrder nodes users S a)
          (fun q r => filter_firstOrder nodes users S a q r) _
          (fun _ _ => ⟨plain_firstOrder nodes users S a,True.intro⟩)
      · trivial
    | .seq a b | .alt a b => ⟨plain_firstOrder nodes users S a,plain_firstOrder nodes users S b⟩
    | .star a | .notP a => plain_firstOrder nodes users S a

  theorem filter_firstOrder (nodes : List Node) (users : List User) (S : List (List Nat)) :
      ∀ e q r, (filter nodes users S e q r).FirstOrder
    | .lit _, _, _ | .param _, _, _ => by simp only [filter]; split <;> trivial
    | .helper _, _, _ => True.intro
    | .user i a, q, r => by
      simp only [filter]
      split
      · exact ProfileControl.select_firstOrder _ _ _ (plain_firstOrder nodes users S a)
          (fun q r => filter_firstOrder nodes users S a q r) _
          (fun _ _ => ⟨plain_firstOrder nodes users S a,True.intro⟩)
      · trivial
    | .seq a b, q, r => by
      apply choice_firstOrder
      intro e he
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
      exact ⟨filter_firstOrder nodes users S a q t,filter_firstOrder nodes users S b t r⟩
    | .alt a b, q, r => ⟨⟨plain_firstOrder nodes users S a,filter_firstOrder nodes users S a q r⟩,
        plain_firstOrder nodes users S a,filter_firstOrder nodes users S b q r⟩
    | .star a, q, r => GeneralStarFilter.filter_firstOrder _ _ (plain_firstOrder nodes users S a) _
        (fun q r => filter_firstOrder nodes users S a q r) q r
    | .notP a, q, r => by
      simp only [filter]
      split <;> exact ⟨plain_firstOrder nodes users S a,True.intro⟩
end

theorem mode_plain_mem (D : Machine) : none∈modes D := by simp [modes]
theorem mode_filter_mem (D : Machine) (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    some (q,r)∈modes D := by
  simp only [modes,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_range]
  exact Or.inr ⟨q,hq,r,hr,rfl⟩

theorem key_mem (users : List User) (i : Nat) (hi : i<users.length)
    (P : List Nat) (hP : P∈profiles (machine users)) (m : Mode) (hm : m∈modes (machine users)) :
    (i,P,m)∈keys users := by
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_range.mpr hi,List.mem_flatMap.mpr ?_⟩
  exact ⟨P,hP,List.mem_map.mpr ⟨m,hm,rfl⟩⟩

theorem source_rule (nodes : List Node) (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r) :
    ruleAtM (parGrammar nodes users).rules ((grammar nodes (machine users)).rules.length+i)=
      some ⟨1,.seq (.seq (.lit r.shift) (.param 0)) (parRender nodes users r.body)⟩ := by
  rw [ruleAtM_eq_getElem?]
  change ((grammar nodes (machine users)).rules++sourceRules nodes users)[(grammar nodes (machine users)).rules.length+i]?=_
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,sourceRules,List.getElem?_map,hr,Option.map_some]

theorem target_rule (nodes : List Node) (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r)
    (P : List Nat) (hP : P∈profiles (machine users)) (m : Mode) (hm : m∈modes (machine users)) :
    ruleAtM (seqGrammar nodes users).rules (address nodes users i P m)=some ⟨1,targetBody nodes users i P m r⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [ruleAtM_eq_getElem?]
  change ((grammar nodes (machine users)).rules++targetRules nodes users)[address nodes users i P m]?=_
  rw [address,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,targetRules,List.getElem?_map,
    DependentProfileCall.index_correct (i,P,m) _ (key_mem users i hi P hP m hm),Option.map_some,hr]

theorem targetBody_firstOrder (nodes : List Node) (users : List User) (i : Nat) (P : List Nat) (m : Mode) (r : User) :
    (targetBody nodes users i P m r).FirstOrder := by
  refine ⟨?_,?_⟩
  · unfold tailPrefix
    split
    · trivial
    · split <;> trivial
  · cases m with
    | none => exact plain_firstOrder nodes users [P] r.body
    | some pair => exact filter_firstOrder nodes users [P] r.body _ pair.2

theorem par_firstOrder (nodes : List Node) (users : List User) : (parGrammar nodes users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact grammar_firstOrder nodes (machine users) r hr
  · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨True.intro,True.intro⟩,parRender_firstOrder nodes users u.body⟩

theorem seq_firstOrder (nodes : List Node) (users : List User) : (seqGrammar nodes users).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact grammar_firstOrder nodes (machine users) r hr
  · obtain ⟨⟨i,P,m⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only []
    cases users[i]? with
    | none => trivial
    | some u => exact targetBody_firstOrder nodes users i P m u

theorem par_installed (nodes : List Node) (users : List User) :
    RecursiveParserStability.Installed (helpers nodes users) (parGrammar nodes users) := component_installed _ _ _
theorem seq_installed (nodes : List Node) (users : List User) :
    RecursiveParserStability.Installed (helpers nodes users) (seqGrammar nodes users) := component_installed _ _ _

end Shallot.MacroPeg.CBV.RecursiveArgumentCompiler
