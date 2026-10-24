import MacroPeg.CBV.ProfiledDependentRecursion

/-! A finite family of distinct unary bodies and retained-value-dependent
arguments can mutually recurse through the same shifted-replay compiler. -/
namespace Shallot.MacroPeg.CBV.MutualProfiledRecursion
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)
open PeriodicCaptureMachine (machine)
abbrev Arg := DependentCaptureFilter.Expr

structure User where
  arg : Arg
  body : MExp

def Valid (nodes : List Node) (users : List User) : Prop :=
  ∀ r∈users, DependentCaptureFilter.Valid nodes r.arg

def keys (u : List Char) (users : List User) : List (Nat × List Nat) :=
  (List.range users.length).flatMap (fun i => (profiles (machine u)).map (fun P => (i,P)))

def address (nodes : List Node) (u : List Char) (users : List User) (i : Nat) (P : List Nat) : Nat :=
  (grammar nodes (machine u)).rules.length + (keys u users).idxOf (i,P)

def parRender (nodes : List Node) (u : List Char) (users : List User) : MExp → MExp
  | .call i [] => match users[i]? with
    | some r => .call ((grammar nodes (machine u)).rules.length+i) [DependentCaptureFilter.render r.arg]
    | none => if i-users.length<(grammar nodes (machine u)).rules.length then .call (i-users.length) [] else MExp.failAlways
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (parRender nodes u users a) (parRender nodes u users b)
  | .alt a b => .alt (parRender nodes u users a) (parRender nodes u users b)
  | .star a => .star (parRender nodes u users a)
  | .notP a => .notP (parRender nodes u users a)
  | .eps => .eps | .any => .any | .chr c => .chr c | .range lo hi => .range lo hi
  | .lit w => .lit w | .param k => .param k
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def seqRender (nodes : List Node) (u : List Char) (users : List User) (S : List (List Nat)) : MExp → MExp
  | .call i [] => match users[i]? with
    | some r => DependentProfileCall.select nodes (machine u) S r.arg
      (fun P => .call (address nodes u users i P) [DependentCaptureFilter.render r.arg])
    | none => if i-users.length<(grammar nodes (machine u)).rules.length then .call (i-users.length) [] else MExp.failAlways
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (seqRender nodes u users S a) (seqRender nodes u users S b)
  | .alt a b => .alt (seqRender nodes u users S a) (seqRender nodes u users S b)
  | .star a => .star (seqRender nodes u users S a)
  | .notP a => .notP (seqRender nodes u users S a)
  | .eps => .eps | .any => .any | .chr c => .chr c | .range lo hi => .range lo hi
  | .lit w => .lit w | .param k => .param k
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def sourceRules (nodes : List Node) (u : List Char) (users : List User) : List MRule :=
  users.map (fun r => ⟨1,.seq (.seq (.lit u) (.param 0)) (parRender nodes u users r.body)⟩)
def targetBody (nodes : List Node) (u : List Char) (users : List User) (P : List Nat) (r : User) : MExp :=
  .seq (ProfiledDependentRecursion.tailPrefix u P) (seqRender nodes u users [P] r.body)
def targetRules (nodes : List Node) (u : List Char) (users : List User) : List MRule :=
  (keys u users).map (fun (i,P) => ⟨1,match users[i]? with | some r => targetBody nodes u users P r | none => MExp.failAlways⟩)
abbrev parGrammar (nodes : List Node) (u : List Char) (users : List User) :=
  FilteredOverlapCaller.extend nodes (machine u) (sourceRules nodes u users)
abbrev seqGrammar (nodes : List Node) (u : List Char) (users : List User) :=
  FilteredOverlapCaller.extend nodes (machine u) (targetRules nodes u users)
abbrev helpers (nodes : List Node) (u : List Char) := component nodes (machine u)
abbrev parTable (nodes : List Node) (u : List Char) (users : List User) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (parGrammar nodes u users) x .callByValuePar k
abbrev seqTable (nodes : List Node) (u : List Char) (users : List User) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (seqGrammar nodes u users) x .callByValueSeq k

theorem parRender_firstOrder (nodes : List Node) (u : List Char) (users : List User) :
    ∀ e, (parRender nodes u users e).FirstOrder
  | .call i [] => by
    simp only [parRender]
    cases users[i]? with
    | some r => exact ⟨DependentCaptureFilter.render_firstOrder r.arg,True.intro⟩
    | none => dsimp only []; split <;> trivial
  | .call _ (_::_) => True.intro
  | .seq a b | .alt a b => ⟨parRender_firstOrder nodes u users a,parRender_firstOrder nodes u users b⟩
  | .star a | .notP a => parRender_firstOrder nodes u users a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True.intro
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => True.intro

theorem seqRender_firstOrder (nodes : List Node) (u : List Char) (users : List User) (S : List (List Nat)) :
    ∀ e, (seqRender nodes u users S e).FirstOrder
  | .call i [] => by
    simp only [seqRender]
    cases users[i]? with
    | some r =>
      exact DependentProfileCall.select_firstOrder nodes (machine u) S r.arg _
        (fun _ _ => ⟨DependentCaptureFilter.render_firstOrder r.arg,True.intro⟩)
    | none => dsimp only []; split <;> trivial
  | .call _ (_::_) => True.intro
  | .seq a b | .alt a b => ⟨seqRender_firstOrder nodes u users S a,seqRender_firstOrder nodes u users S b⟩
  | .star a | .notP a => seqRender_firstOrder nodes u users S a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True.intro
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => True.intro

theorem source_rule (nodes : List Node) (u : List Char) (users : List User) (i : Nat) (r : User)
    (hr : users[i]?=some r) :
    ruleAtM (parGrammar nodes u users).rules ((grammar nodes (machine u)).rules.length+i)=
      some ⟨1,.seq (.seq (.lit u) (.param 0)) (parRender nodes u users r.body)⟩ := by
  rw [ruleAtM_eq_getElem?]
  change ((grammar nodes (machine u)).rules++sourceRules nodes u users)[(grammar nodes (machine u)).rules.length+i]?=_
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,sourceRules,List.getElem?_map,hr,Option.map_some]

theorem key_mem (u : List Char) (users : List User) (i : Nat) (hi : i<users.length)
    (P : List Nat) (hP : P∈profiles (machine u)) : (i,P)∈keys u users := by
  apply List.mem_flatMap.mpr
  exact ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨P,hP,rfl⟩⟩

theorem target_rule (nodes : List Node) (u : List Char) (users : List User) (i : Nat) (r : User)
    (hr : users[i]?=some r) (P : List Nat) (hP : P∈profiles (machine u)) :
    ruleAtM (seqGrammar nodes u users).rules (address nodes u users i P)=
      some ⟨1,targetBody nodes u users P r⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [ruleAtM_eq_getElem?]
  change ((grammar nodes (machine u)).rules++targetRules nodes u users)[address nodes u users i P]?=_
  rw [address,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,targetRules,List.getElem?_map,
    DependentProfileCall.index_correct (i,P) _ (key_mem u users i hi P hP),Option.map_some,hr]

theorem par_firstOrder (nodes : List Node) (u : List Char) (users : List User) :
    (parGrammar nodes u users).FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact grammar_firstOrder nodes (machine u) rule hr
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨True.intro,True.intro⟩,parRender_firstOrder nodes u users r.body⟩

theorem seq_firstOrder (nodes : List Node) (u : List Char) (users : List User) :
    (seqGrammar nodes u users).FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact grammar_firstOrder nodes (machine u) rule hr
  · obtain ⟨⟨i,P⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only []
    cases users[i]? with
    | none => trivial
    | some r =>
      refine ⟨?_,seqRender_firstOrder nodes u users [P] r.body⟩
      unfold ProfiledDependentRecursion.tailPrefix
      split <;> trivial

theorem par_installed (nodes : List Node) (u : List Char) (users : List User) :
    RecursiveParserStability.Installed (helpers nodes u) (parGrammar nodes u users) := component_installed _ _ _
theorem seq_installed (nodes : List Node) (u : List Char) (users : List User) :
    RecursiveParserStability.Installed (helpers nodes u) (seqGrammar nodes u users) := component_installed _ _ _

def Shifted (nodes : List Node) (u : List Char) (users : List User) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, users[i]?=some r → ∀ E p j, p≤x.length → j≤x.length →
    evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (DependentCaptureFilter.render r.arg) p=some (some j) →
      valAt (parTable nodes u users x k ((grammar nodes (machine u)).rules.length+i) [pre x p j]) p =
        valAt (seqTable nodes u users x k (address nodes u users i (profile (machine u) (pre x p j))) [pre x p j]) j

theorem selected_call (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (u : List Char) (hu : u≠[]) (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r)
    (ha : DependentCaptureFilter.Valid nodes r.arg) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate (machine u) S E)
    (p : Nat) (hp : p≤x.length) :
    evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k) E
        (seqRender nodes u users S (.call i [])) p =
      match evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E
          (DependentCaptureFilter.render r.arg) p with
      | some (some j) => valAt (seqTable nodes u users x k (address nodes u users i (profile (machine u) (pre x p j))) [pre x p j]) j
      | other => other := by
  have hD := PeriodicCaptureMachine.valid u hu
  have he : evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k) E (DependentCaptureFilter.render r.arg) p =
      evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (DependentCaptureFilter.render r.arg) p := by
    rw [ParametricHelperControl.rounds_base nodes hNodes (machine u) hD.1 (targetRules nodes u users) x .callByValueSeq k E _
        (ParametricHelperControl.render_safe nodes (machine u) r.arg ha) p hp,
      ParametricHelperControl.rounds_base nodes hNodes (machine u) hD.1 (sourceRules nodes u users) x .callByValuePar k E _
        (ParametricHelperControl.render_safe nodes (machine u) r.arg ha) p hp]
  simp only [seqRender,hr]
  rw [DependentProfileCall.select_correct nodes hNodes (machine u) hD (targetRules nodes u users) x k S E hS r.arg ha p hp,he]
  cases hv : evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (DependentCaptureFilter.render r.arg) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      rw [evV_call_seq (target_rule nodes u users i r hr (profile (machine u) (pre x p j)) (CaptureTransitionProfile.profile_mem (machine u) hD (pre x p j))) rfl]
      simp only [evSeqArgs,he,hv]

theorem entry_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (u : List Char) (hu : u≠[]) (users : List User) (hUsers : Valid nodes users)
    (x : List Char) (k : Nat) (hRows : Shifted nodes u users x k)
    (i : Nat) (r : User) (hr : users[i]?=some r) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (machine u) S E) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (parRender nodes u users (.call i [])) p =
      evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k) E (seqRender nodes u users S (.call i [])) p := by
  rw [selected_call nodes hNodes u hu users i r hr (hUsers r (List.mem_of_getElem? hr)) x k S E hS p hp]
  simp only [parRender,hr]
  rw [evV_call_par (source_rule nodes u users i r hr) rfl (by decide)]
  simp only [evParArgs]
  cases hv : evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (DependentCaptureFilter.render r.arg) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      exact hRows i r hr E p j hp (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp j hv) hv

theorem evaluator_of_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (users : List User) (hUsers : Valid nodes users) (x : List Char) (k : Nat)
    (hRows : Shifted nodes u users x k) :
    ∀ e S E, DependentCaptureFilter.Accurate (machine u) S E → ∀ p, p≤x.length →
      evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (parRender nodes u users e) p =
        evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k) E (seqRender nodes u users S e) p
  | .call i [], S, E, hS, p, hp => by
    cases hr : users[i]? with
    | some r => exact entry_eq nodes hNodes u hu users hUsers x k hRows i r hr S E hS p hp
    | none =>
      simp only [parRender,seqRender,hr]
      split
      · rename_i hj
        exact (RecursiveFilteredOverlap.query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1
          (sourceRules nodes u users) x .callByValuePar k (i-users.length) p hj hp E).trans
          (RecursiveFilteredOverlap.query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1
            (targetRules nodes u users) x .callByValueSeq k (i-users.length) p hj hp E).symm
      · rfl
  | .call j (_::_), _, _, _, _, _ => by cases j <;> rfl
  | .seq a b, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu users hUsers x k hRows a S E hS p hp
    simp only [parRender,seqRender]
    cases hv : evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (parRender nodes u users a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu users hUsers x k hRows b S E hS z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp z hv)
  | .alt a b, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu users hUsers x k hRows a S E hS p hp
    simp only [parRender,seqRender]
    cases hv : evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (parRender nodes u users a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu users hUsers x k hRows b S E hS p hp
      | some z => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .star a, S, E, hS, p, hp => by
    simp only [parRender,seqRender,evV_star]
    exact evStar_congr p (fun z hz => evaluator_of_rows nodes hNodes u hu users hUsers x k hRows a S E hS z (by omega))
  | .notP a, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu users hUsers x k hRows a S E hS p hp
    change (match evV _ _ _ _ E (parRender nodes u users a) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [heq]
    rfl
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _ | .range _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl

/-- All transition profiles, including a sink profile, are threaded through
actual recursive user rows. -/
theorem tables_shifted (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (users : List User) (hUsers : Valid nodes users) (x : List Char) :
    ∀ k, Shifted nodes u users x k := by
  have hD := PeriodicCaptureMachine.valid u hu
  have huser (i : Nat) : RecursiveParserStability.pick (helpers nodes u) ((grammar nodes (machine u)).rules.length+i)=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser (i : Nat) (P : List Nat) : RecursiveParserStability.pick (helpers nodes u) (address nodes u users i P)=false := by
    simp [RecursiveParserStability.pick,helpers,component,address]
  intro k
  induction k with
  | zero =>
    intro i r hr E p j hp hj hv
    have hpar := source_rule nodes u users i r hr
    have hseq := target_rule nodes u users i r hr (profile (machine u) (pre x p j)) (CaptureTransitionProfile.profile_mem (machine u) hD (pre x p j))
    have hrot := ProfiledDependentRecursion.prefix_eq (parGrammar nodes u users) (seqGrammar nodes u users) x
      (parTable nodes u users x 0)
      (ClockFreezing.frozen (parGrammar nodes u users) x .callByValuePar (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      (ClockFreezing.frozen (seqGrammar nodes u users) x .callByValueSeq (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      (SeededClock.rounds_sound (par_firstOrder nodes u users) (helpers nodes u) x .callByValuePar (by decide) 0)
      E (DependentCaptureFilter.render r.arg) (DependentCaptureFilter.render_firstOrder r.arg) u hu p j hp hv
    change valAt (SeededClock.prefixSeed _ x .callByValuePar _ _ _ [pre x p j]) p =
      valAt (SeededClock.prefixSeed _ x .callByValueSeq _ _ _ [pre x p j]) j
    rw [SeededClock.prefixSeed_query _ x .callByValuePar _ _ _ (huser i) 1 _ _ hpar _ p hp,
      SeededClock.prefixSeed_query _ x .callByValueSeq _ _ _ (htuser i _) 1 _ _
        hseq _ j hj,hrot]
  | succ k ih =>
    intro i r hr E p j hp hj hv
    have hpar := source_rule nodes u users i r hr
    have hseq := target_rule nodes u users i r hr (profile (machine u) (pre x p j)) (CaptureTransitionProfile.profile_mem (machine u) hD (pre x p j))
    have hrot := ProfiledDependentRecursion.prefix_eq (parGrammar nodes u users) (seqGrammar nodes u users) x
      (parTable nodes u users x (k+1)) (parTable nodes u users x k) (seqTable nodes u users x k)
      (SeededClock.rounds_sound (par_firstOrder nodes u users) (helpers nodes u) x .callByValuePar (by decide) (k+1))
      E (DependentCaptureFilter.render r.arg) (DependentCaptureFilter.render_firstOrder r.arg) u hu p j hp hv
    rw [SeededClock.user_step _ x .callByValuePar _ _ _ k _ (huser i) _ hpar _ p hp,
      SeededClock.user_step _ x .callByValueSeq _ _ _ k _ (htuser i _) _
        hseq _ j hj]
    change (match evV _ _ _ _ [pre x p j] (.seq (.lit u) (.param 0)) p with
      | some (some z) => evV _ _ _ _ [pre x p j] (parRender nodes u users r.body) z
      | other => other)=_
    rw [hrot]
    dsimp only [targetBody]
    cases hz : evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k)
        [pre x p j] (ProfiledDependentRecursion.tailPrefix u (profile (machine u) (pre x p j))) j with
    | none => rw [evV_seq_none hz]
    | some result => cases result with
      | none => rw [evV_seq_fail hz]
      | some z =>
        dsimp only []
        rw [evV_seq_ok hz]
        exact evaluator_of_rows nodes hNodes u hu users hUsers x k ih r.body [profile (machine u) (pre x p j)] [pre x p j]
          (DependentCaptureFilter.environment_accurate (machine u) [pre x p j]) z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ j hj z hz)

theorem evaluator_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (users : List User) (hUsers : Valid nodes users) (x : List Char) (k : Nat)
    (e : MExp) (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate (machine u) S E) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u users) x .callByValuePar (parTable nodes u users x k) E (parRender nodes u users e) p =
      evV (seqGrammar nodes u users) x .callByValueSeq (seqTable nodes u users x k) E (seqRender nodes u users S e) p :=
  evaluator_of_rows nodes hNodes u hu users hUsers x k (tables_shifted nodes hNodes u hu users hUsers x k) e S E hS p hp

/-- Prefix seeds are removed: these are finite observations of the actual
first-order grammars on the same original character strings. -/
theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (users : List User) (hUsers : Valid nodes users) (e : MExp) (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar nodes u users) .callByValuePar (parRender nodes u users e) x rest ↔
      SObs (seqGrammar nodes u users) .callByValueSeq (seqRender nodes u users [] e) x rest := by
  have hb := component_valid nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1
  rw [SeededClock.observations_iff hb (par_installed nodes u users) (par_firstOrder nodes u users)
      x .callByValuePar (by decide) _ (parRender_firstOrder nodes u users e) rest,
    SeededClock.observations_iff hb (seq_installed nodes u users) (seq_firstOrder nodes u users)
      x .callByValueSeq (by decide) _ (seqRender_firstOrder nodes u users [] e) rest]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu users hUsers x k e [] [] (DependentCaptureFilter.environment_accurate (machine u) []) x.length (Nat.le_refl _)).symm.trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu users hUsers x k e [] [] (DependentCaptureFilter.environment_accurate (machine u) []) x.length (Nat.le_refl _)).trans hv,hr⟩

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (users : List User) (hUsers : Valid nodes users) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (parGrammar nodes u users) .callByValuePar (parRender nodes u users e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar nodes u users,seqRender nodes u users [] e,seq_firstOrder nodes u users,
    seqRender_firstOrder nodes u users [] e,fun x => observations_iff nodes hNodes u hu users hUsers e x (some [])⟩

/-- Two distinct user rules call each other. The second extends the first
capture, while the first recaptures independently. Both retained values
survive the return through the other user rule. -/
theorem mutual_capture_execution :
    let nodes : List Node := [.lit "aa".toList,.lit ['a']]
    let u := ['a']
    let B0 := MExp.seq (.lit ['#']) (.seq (.param 0)
      (.alt (.seq (.lit ['!']) (.seq (.call 1 []) (.seq (.lit ['?']) (.param 0)))) .eps))
    let B1 := MExp.seq (.lit ['@']) (.seq (.param 0)
      (.alt (.seq (.lit ['%']) (.seq (.call 0 []) (.seq (.lit ['$']) (.param 0)))) .eps))
    let users : List User := [⟨.helper 0,B0⟩,⟨.seq (.param 0) (.helper 1),B1⟩]
    let gp := parGrammar nodes u users
    let gs := seqGrammar nodes u users
    let e := MExp.seq (.call 0 []) (.notP .any)
    let x := "aaa#aa!aaaa@aaa%aaa#aa$aaa?aa".toList
    let bad := "aaa#aa!aaaa@aaa%aaa#aa$aa?aa".toList
    evV gp x .callByValuePar (tblV gp x .callByValuePar 18) [] (parRender nodes u users e) x.length=some (some 0) ∧
      evV gs x .callByValueSeq (tblV gs x .callByValueSeq 18) [] (seqRender nodes u users [] e) x.length=some (some 0) ∧
    evV gp bad .callByValuePar (tblV gp bad .callByValuePar 18) [] (parRender nodes u users e) bad.length=some none ∧
      evV gs bad .callByValueSeq (tblV gs bad .callByValueSeq 18) [] (seqRender nodes u users [] e) bad.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.MutualProfiledRecursion
