import MacroPeg.CBV.RecursiveArgumentCorrespondence
import MacroPeg.CBV.ReplayControlFusion

/-! Normalize capture-dependent origin control into shifted recursive leaves.
The resulting Seq grammar is fixed and keeps the original input strings. -/
namespace Shallot.MacroPeg.CBV.OriginControlNormalization
open RegularCaptureProduct
open ReplayControlFusion (Plan)
abbrev Arg := RecursiveArgumentCompiler.Expr
abbrev Leaf := RecursiveArgumentCompiler.User

def expand (L : Nat → Arg) : Plan → Arg
  | .leaf i => L i
  | .alt a b => .alt (expand L a) (expand L b)
  | .notP a => .notP (expand L a)
  | .guard a b => .seq (.notP (.notP (expand L a))) (expand L b)

def normalize (specs : List Plan) : Arg → Arg
  | .user i a => match specs[i]? with
    | some P => .seq (.notP (.notP (normalize specs a))) (expand (fun j => .user j (normalize specs a)) P)
    | none => .notP (.lit [])
  | .lit w => .lit w
  | .param k => .param k
  | .helper i => .helper i
  | .seq a b => .seq (normalize specs a) (normalize specs b)
  | .alt a b => .alt (normalize specs a) (normalize specs b)
  | .star a => .star (normalize specs a)
  | .notP a => .notP (normalize specs a)

def coreUsers (leaves : List Leaf) (specs : List Plan) : List Leaf :=
  leaves.map (fun r => ⟨r.shift,normalize specs r.body⟩)
abbrev machine (leaves : List Leaf) (specs : List Plan) := RecursiveArgumentCompiler.machine (coreUsers leaves specs)
abbrev base (nodes : List Node) (leaves : List Leaf) (specs : List Plan) := (grammar nodes (machine leaves specs)).rules.length

def render (nodes : List Node) (leaves : List Leaf) (specs : List Plan) : Arg → MExp
  | .user i a => if i<specs.length then .call (base nodes leaves specs+i) [render nodes leaves specs a] else MExp.failAlways
  | .lit w => .lit w
  | .param k => .param k
  | .helper i => .call i []
  | .seq a b => .seq (render nodes leaves specs a) (render nodes leaves specs b)
  | .alt a b => .alt (render nodes leaves specs a) (render nodes leaves specs b)
  | .star a => .star (render nodes leaves specs a)
  | .notP a => .notP (render nodes leaves specs a)

def sourceLeaf (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (i : Nat) : MExp :=
  match leaves[i]? with
  | some r => .seq (.seq (.lit r.shift) (.param 0)) (render nodes leaves specs r.body)
  | none => MExp.failAlways

def sourceRules (nodes : List Node) (leaves : List Leaf) (specs : List Plan) : List MRule :=
  specs.map (fun P => ⟨1,P.exp (sourceLeaf nodes leaves specs)⟩)
abbrev sourceGrammar (nodes : List Node) (leaves : List Leaf) (specs : List Plan) :=
  FilteredOverlapCaller.extend nodes (machine leaves specs) (sourceRules nodes leaves specs)
abbrev coreGrammar (nodes : List Node) (leaves : List Leaf) (specs : List Plan) :=
  RecursiveArgumentCompiler.parGrammar nodes (coreUsers leaves specs)
abbrev targetGrammar (nodes : List Node) (leaves : List Leaf) (specs : List Plan) :=
  RecursiveArgumentCompiler.seqGrammar nodes (coreUsers leaves specs)
abbrev coreRender (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (e : Arg) :=
  RecursiveArgumentCompiler.parRender nodes (coreUsers leaves specs) (normalize specs e)
abbrev targetRender (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (e : Arg) :=
  RecursiveArgumentCompiler.plain nodes (coreUsers leaves specs) [] (normalize specs e)

def Valid (nodes : List Node) (specs : List Plan) : Arg → Prop
  | .helper i => i<nodes.length
  | .user i a => i<specs.length ∧ Valid nodes specs a
  | .seq a b | .alt a b => Valid nodes specs a ∧ Valid nodes specs b
  | .star a | .notP a => Valid nodes specs a
  | .lit _ | .param _ => True

def PlansValid (leaves : List Leaf) (specs : List Plan) : Prop :=
  ∀ P∈specs, P.All (fun i => i<leaves.length)
def LeavesValid (nodes : List Node) (leaves : List Leaf) (specs : List Plan) : Prop :=
  ∀ r∈leaves, r.shift≠[] ∧ Valid nodes specs r.body

theorem expand_valid (nodes : List Node) (users : List Leaf) (L : Nat → Arg) :
    ∀ P, P.All (fun i => RecursiveArgumentCompiler.Valid nodes users (L i)) →
      RecursiveArgumentCompiler.Valid nodes users (expand L P)
  | .leaf _, h => h
  | .alt a b, h | .guard a b, h => ⟨expand_valid nodes users L a h.1,expand_valid nodes users L b h.2⟩
  | .notP a, h => expand_valid nodes users L a h

theorem normalize_valid (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs) :
    ∀ e, Valid nodes specs e → RecursiveArgumentCompiler.Valid nodes (coreUsers leaves specs) (normalize specs e)
  | .lit _, _ | .param _, _ => True.intro
  | .helper _, hi => hi
  | .seq a b, h | .alt a b, h => ⟨normalize_valid nodes leaves specs hPlans a h.1,normalize_valid nodes leaves specs hPlans b h.2⟩
  | .star a, h | .notP a, h => normalize_valid nodes leaves specs hPlans a h
  | .user i a, h => by
    have hi : i<specs.length := h.1
    have hr := List.getElem?_eq_getElem hi
    simp only [normalize,hr]
    refine ⟨normalize_valid nodes leaves specs hPlans a h.2,expand_valid nodes _ _ _ ?_⟩
    apply Plan.all_imp (t := specs[i]) _ (hPlans specs[i] (List.getElem_mem hi))
    intro j hj
    exact ⟨by simpa [coreUsers] using hj,normalize_valid nodes leaves specs hPlans a h.2⟩

theorem core_valid (nodes : List Node) (leaves : List Leaf) (specs : List Plan)
    (hPlans : PlansValid leaves specs) (hLeaves : LeavesValid nodes leaves specs) :
    RecursiveArgumentCompiler.UsersValid nodes (coreUsers leaves specs) := by
  intro r hr
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
  exact ⟨(hLeaves u hu).1,normalize_valid nodes leaves specs hPlans u.body (hLeaves u hu).2⟩

theorem render_firstOrder (nodes : List Node) (leaves : List Leaf) (specs : List Plan) :
    ∀ e, (render nodes leaves specs e).FirstOrder
  | .lit _ | .param _ | .helper _ => True.intro
  | .user i a => by simp only [render]; split; exact ⟨render_firstOrder nodes leaves specs a,True.intro⟩; trivial
  | .seq a b | .alt a b => ⟨render_firstOrder nodes leaves specs a,render_firstOrder nodes leaves specs b⟩
  | .star a | .notP a => render_firstOrder nodes leaves specs a

theorem source_firstOrder (nodes : List Node) (leaves : List Leaf) (specs : List Plan) :
    (sourceGrammar nodes leaves specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr|hr
  · exact grammar_firstOrder nodes (machine leaves specs) r hr
  · obtain ⟨P,_,rfl⟩ := List.mem_map.mp hr
    apply Plan.exp_firstOrder
    intro i
    unfold sourceLeaf
    cases leaves[i]? with
    | none => trivial
    | some r => exact ⟨⟨True.intro,True.intro⟩,render_firstOrder nodes leaves specs r.body⟩

theorem source_rule (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (i : Nat) (P : Plan)
    (hr : specs[i]?=some P) :
    ruleAtM (sourceGrammar nodes leaves specs).rules (base nodes leaves specs+i)=
      some ⟨1,P.exp (sourceLeaf nodes leaves specs)⟩ := by
  rw [ruleAtM_eq_getElem?]
  change ((grammar nodes (machine leaves specs)).rules++sourceRules nodes leaves specs)[base nodes leaves specs+i]?=_
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left,sourceRules,List.getElem?_map,hr,Option.map_some]

theorem core_rule (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (i : Nat) (r : Leaf)
    (hr : leaves[i]?=some r) :
    ruleAtM (coreGrammar nodes leaves specs).rules (base nodes leaves specs+i)=
      some ⟨1,.seq (.seq (.lit r.shift) (.param 0)) (coreRender nodes leaves specs r.body)⟩ := by
  have hi : (coreUsers leaves specs)[i]?=some ⟨r.shift,normalize specs r.body⟩ := by simp [coreUsers,hr]
  exact RecursiveArgumentCompiler.source_rule nodes (coreUsers leaves specs) i _ hi

theorem parRender_expand (nodes : List Node) (users : List Leaf) (L : Nat → Arg) :
    ∀ P, RecursiveArgumentCompiler.parRender nodes users (expand L P)=
      P.exp (fun i => RecursiveArgumentCompiler.parRender nodes users (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [expand,RecursiveArgumentCompiler.parRender,Plan.exp,parRender_expand nodes users L a,parRender_expand nodes users L b,MExp.andP]
  | .notP a => by simp only [expand,RecursiveArgumentCompiler.parRender,Plan.exp,parRender_expand nodes users L a]

abbrev table (g : MGrammar) (x : List Char) (k : Nat) := tblV g x .callByValuePar k

def leafRows (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (x : List Char) (k : Nat)
    (w : List Char) (p i : Nat) : Res :=
  if i<leaves.length then valAt (table (coreGrammar nodes leaves specs) x k (base nodes leaves specs+i) [w]) p else some none

def Rows (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (x : List Char) (k : Nat) : Prop :=
  ∀ i P, specs[i]?=some P → ∀ w p, p≤x.length →
    valAt (table (sourceGrammar nodes leaves specs) x k (base nodes leaves specs+i) [w]) p =
      P.eval (leafRows nodes leaves specs x k w p) p

theorem callLeaf_eval (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (x : List Char) (k : Nat)
    (E : List (List Char)) (a : Arg) (p j : Nat)
    (ha : evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k)
      E (coreRender nodes leaves specs a) p=some (some j)) (i : Nat) :
    evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k) E
      (RecursiveArgumentCompiler.parRender nodes (coreUsers leaves specs) (.user i (normalize specs a))) p =
        leafRows nodes leaves specs x k (pre x p j) p i := by
  by_cases hi : i<leaves.length
  · have hib : i<(coreUsers leaves specs).length := by simpa [coreUsers] using hi
    simp only [RecursiveArgumentCompiler.parRender,if_pos hib,leafRows,if_pos hi]
    rw [evV_call_par (core_rule nodes leaves specs i leaves[i] (List.getElem?_eq_getElem hi)) rfl (by decide)]
    simp only [evParArgs,ha]
  · have hib : ¬i<(coreUsers leaves specs).length := by simpa [coreUsers] using hi
    simp only [RecursiveArgumentCompiler.parRender,if_neg hib,leafRows,if_neg hi]
    simp [MExp.failAlways,evV]

theorem coreRender_user (nodes : List Node) (leaves : List Leaf) (specs : List Plan) (i : Nat) (P : Plan)
    (hr : specs[i]?=some P) (a : Arg) :
    coreRender nodes leaves specs (.user i a)=.seq (.andP (coreRender nodes leaves specs a))
      (P.exp (fun j => RecursiveArgumentCompiler.parRender nodes (coreUsers leaves specs) (.user j (normalize specs a)))) := by
  unfold coreRender
  rw [normalize,hr]
  change MExp.seq _ (RecursiveArgumentCompiler.parRender nodes (coreUsers leaves specs)
    (expand (fun j => .user j (normalize specs a)) P))=_
  rw [parRender_expand]
  rfl

theorem evaluator_of_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (x : List Char) (k : Nat) (hRows : Rows nodes leaves specs x k) :
    ∀ e, Valid nodes specs e → ∀ E p, p≤x.length →
      evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs e) p =
        evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k) E (coreRender nodes leaves specs e) p
  | .lit _, _, _, _, _ | .param _, _, _, _, _ => rfl
  | .helper i, hi, E, p, hp => by
    have hg := component_installed nodes (machine leaves specs) (sourceRules nodes leaves specs)
    have hh := RecursiveArgumentCompiler.par_installed nodes (coreUsers leaves specs)
    have hlen : i<(component nodes (machine leaves specs)).length :=
      Nat.lt_of_lt_of_le hi (by simp [component,grammar])
    have he := RecursiveParserStability.helper_rows_eq
      (component_valid nodes hNodes (machine leaves specs) (CaptureMachineFamily.valid _).1) hg hh x .callByValuePar .callByValuePar k i hlen [] []
    have hg' : ruleAtM (sourceGrammar nodes leaves specs).rules i=some ⟨0,(component nodes (machine leaves specs))[i]⟩ :=
      hg i (component nodes (machine leaves specs))[i] (List.getElem?_eq_getElem hlen)
    have hh' : ruleAtM (coreGrammar nodes leaves specs).rules i=some ⟨0,(component nodes (machine leaves specs))[i]⟩ :=
      hh i (component nodes (machine leaves specs))[i] (List.getElem?_eq_getElem hlen)
    change evV _ _ _ _ E (.call i []) p=evV _ _ _ _ E (.call i []) p
    rw [evV_call_par hg' rfl (by decide),evV_call_par hh' rfl (by decide)]
    exact congrArg (fun row => valAt row p) he
  | .user i a, ha, E, p, hp => by
    have hi : i<specs.length := ha.1
    have hr := List.getElem?_eq_getElem hi
    have harg := evaluator_of_rows nodes hNodes leaves specs x k hRows a ha.2 E p hp
    rw [coreRender_user nodes leaves specs i specs[i] hr a]
    rw [show render nodes leaves specs (.user i a)=.call (base nodes leaves specs+i) [render nodes leaves specs a] by simp only [render,if_pos hi]]
    rw [evV_call_par (source_rule nodes leaves specs i specs[i] hr) rfl (by decide)]
    have hguard : evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k) E
        (.andP (coreRender nodes leaves specs a)) p =
      CallLookahead.peek p (evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs a) p) := by
      rw [CallLookahead.evV_peek,←harg]
    cases hv : evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs a) p with
    | none => rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
    | some result => cases result with
      | none => rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
      | some j =>
        rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl))]
        change valAt (table (sourceGrammar nodes leaves specs) x k (base nodes leaves specs+i) [pre x p j]) p = _
        rw [Plan.exp_eval]
        have hl : (fun n => evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k) E
            (RecursiveArgumentCompiler.parRender nodes (coreUsers leaves specs) (.user n (normalize specs a))) p)=
            leafRows nodes leaves specs x k (pre x p j) p := by
          funext n
          exact callLeaf_eval nodes leaves specs x k E a p j (harg.symm.trans hv) n
        rw [hl]
        exact hRows i specs[i] hr _ p hp
  | .seq a b, h, E, p, hp => by
    have heq := evaluator_of_rows nodes hNodes leaves specs x k hRows a h.1 E p hp
    cases hv : evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs a) p with
    | none => rw [show render nodes leaves specs (.seq a b)=.seq (render nodes leaves specs a) (render nodes leaves specs b) from rfl,
        evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [show render nodes leaves specs (.seq a b)=.seq (render nodes leaves specs a) (render nodes leaves specs b) from rfl,
          evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some j =>
        simp only [render,coreRender,normalize,RecursiveArgumentCompiler.parRender,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes leaves specs x k hRows b h.2 E j (evV_ok (tblV_ok _ _ _ k) _ p hp j hv)
  | .alt a b, h, E, p, hp => by
    have heq := evaluator_of_rows nodes hNodes leaves specs x k hRows a h.1 E p hp
    cases hv : evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs a) p with
    | none => simp only [render,coreRender,normalize,RecursiveArgumentCompiler.parRender,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        simp only [render,coreRender,normalize,RecursiveArgumentCompiler.parRender,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes leaves specs x k hRows b h.2 E p hp
      | some j => simp only [render,coreRender,normalize,RecursiveArgumentCompiler.parRender,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .star a, h, E, p, hp =>
    evStar_congr p (fun j hj => evaluator_of_rows nodes hNodes leaves specs x k hRows a h E j (by omega))
  | .notP a, h, E, p, hp => by
    simp only [render,coreRender,normalize,RecursiveArgumentCompiler.parRender,evV]
    rw [evaluator_of_rows nodes hNodes leaves specs x k hRows a h E p hp]

/-- Ordinary physical Par rounds already agree under normalization. The
control tree's negative branches need no extra semantic seed. -/
theorem tables_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (x : List Char) :
    ∀ k, Rows nodes leaves specs x k := by
  intro k
  induction k with
  | zero =>
    intro i P hr w p hp
    change none=P.eval (leafRows nodes leaves specs x 0 w p) p
    symm
    apply Plan.eval_none
    apply Plan.all_imp (t := P) _ (hPlans P (List.mem_of_getElem? hr))
    intro j hj
    simp only [leafRows,if_pos hj,table,tblV,valAt_nil]
  | succ k ih =>
    intro i P hr w p hp
    rw [valAt_tblV_succ (source_rule nodes leaves specs i P hr) [w] hp,Plan.exp_eval]
    apply Plan.eval_congr
    apply Plan.all_imp (t := P) _ (hPlans P (List.mem_of_getElem? hr))
    intro j hj
    have hrj := List.getElem?_eq_getElem hj
    have hvalid := hLeaves leaves[j] (List.getElem_mem hj)
    simp only [sourceLeaf,hrj,leafRows,if_pos hj]
    rw [valAt_tblV_succ (core_rule nodes leaves specs j leaves[j] hrj) [w] hp]
    have heq := SeededClock.word_eval_eq (sourceGrammar nodes leaves specs) (coreGrammar nodes leaves specs)
      x .callByValuePar .callByValuePar (table (sourceGrammar nodes leaves specs) x k)
      (table (coreGrammar nodes leaves specs) x k) [w] (.seq (.lit leaves[j].shift) (.param 0)) ⟨True.intro,True.intro⟩ p
    cases hv : evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k)
        [w] (.seq (.lit leaves[j].shift) (.param 0)) p with
    | none => rw [evV_seq_none hv]; exact (evV_seq_none (heq.symm.trans hv)).symm
    | some result => cases result with
      | none => rw [evV_seq_fail hv]; exact (evV_seq_fail (heq.symm.trans hv)).symm
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes leaves specs x k ih leaves[j].body hvalid.2 [w] z
          (evV_ok (tblV_ok _ _ _ k) _ p hp z hv)

theorem evaluator_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (x : List Char) (k : Nat)
    (e : Arg) (he : Valid nodes specs e) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (sourceGrammar nodes leaves specs) x .callByValuePar (table (sourceGrammar nodes leaves specs) x k) E (render nodes leaves specs e) p =
      evV (coreGrammar nodes leaves specs) x .callByValuePar (table (coreGrammar nodes leaves specs) x k) E (coreRender nodes leaves specs e) p :=
  evaluator_of_rows nodes hNodes leaves specs x k (tables_rows nodes hNodes leaves specs hPlans hLeaves x k) e he E p hp

theorem decide_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (e : Arg) (he : Valid nodes specs e) (x : List Char) :
    decideObsV .callByValuePar (sourceGrammar nodes leaves specs) x (render nodes leaves specs e) =
      decideObsV .callByValuePar (coreGrammar nodes leaves specs) x (coreRender nodes leaves specs e) := by
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (sourceGrammar nodes leaves specs) (coreGrammar nodes leaves specs)
    x .callByValuePar .callByValuePar (render nodes leaves specs e) (coreRender nodes leaves specs e)
    (fun k => evaluator_eq nodes hNodes leaves specs hPlans hLeaves x k e he [] x.length (Nat.le_refl _))]

theorem normalized_observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (e : Arg) (he : Valid nodes specs e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes leaves specs) .callByValuePar (render nodes leaves specs e) x rest ↔
      SObs (coreGrammar nodes leaves specs) .callByValuePar (coreRender nodes leaves specs e) x rest := by
  rw [←decideObsV_iff (source_firstOrder nodes leaves specs) (by decide) (render_firstOrder nodes leaves specs e),
    ←decideObsV_iff (RecursiveArgumentCompiler.par_firstOrder nodes (coreUsers leaves specs)) (by decide)
      (RecursiveArgumentCompiler.parRender_firstOrder nodes (coreUsers leaves specs) (normalize specs e)),
    decide_eq nodes hNodes leaves specs hPlans hLeaves e he x]

/-- Source bodies may use capture-dependent choice, negation, and guards
before committing to any replay leaf, and may return before capture ended. -/
theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (e : Arg) (he : Valid nodes specs e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (sourceGrammar nodes leaves specs) .callByValuePar (render nodes leaves specs e) x rest ↔
      SObs (targetGrammar nodes leaves specs) .callByValueSeq (targetRender nodes leaves specs e) x rest :=
  (normalized_observations_iff nodes hNodes leaves specs hPlans hLeaves e he x rest).trans
    (RecursiveArgumentCorrespondence.observations_iff nodes hNodes (coreUsers leaves specs)
      (core_valid nodes leaves specs hPlans hLeaves) (normalize specs e)
      (normalize_valid nodes leaves specs hPlans e he) x rest)

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (leaves : List Leaf) (specs : List Plan) (hPlans : PlansValid leaves specs)
    (hLeaves : LeavesValid nodes leaves specs) (e : Arg) (he : Valid nodes specs e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (sourceGrammar nodes leaves specs) .callByValuePar (render nodes leaves specs e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨targetGrammar nodes leaves specs,targetRender nodes leaves specs e,
    RecursiveArgumentCompiler.seq_firstOrder nodes (coreUsers leaves specs),
    RecursiveArgumentCompiler.plain_firstOrder nodes (coreUsers leaves specs) [] (normalize specs e),
    fun x => observations_iff nodes hNodes leaves specs hPlans hLeaves e he x (some [])⟩

end Shallot.MacroPeg.CBV.OriginControlNormalization
