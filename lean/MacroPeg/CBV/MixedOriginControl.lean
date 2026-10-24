import MacroPeg.CBV.MixedAdjacentRecursive
import MacroPeg.CBV.ReplayControlFusion

/-! Normalize origin control over ordinary and shifted replay leaves before
applying the mixed recursive Seq compiler. -/
namespace Shallot.MacroPeg.CBV.MixedOriginControl
open AdjacentCallsiteRecursive (Header Argument argument argument_syntax)
open MixedAdjacentRecursive (Body sourcePrefix)
open ReplayControlFusion (Plan)
structure Part (H : Header) where
  split : Bool
  body : Body H
  /-- A compiler-generated empty-progress loop, independent of capture. -/
  stuck : Bool := false
structure Spec where
  split : Bool
  plan : Plan

theorem stuck_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) : evV g x s T E (.star .eps) p=none := by
  change evStar (fun q => some (some q)) p=none
  exact evStar_stuck rfl (by omega)

def embed (H : Header) : MExp → Body H
  | .seq a b => .seq (embed H a) (embed H b)
  | .alt a b => .alt (embed H a) (embed H b)
  | .star a => .star (embed H a)
  | .notP a => .notP (embed H a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | _ => .notP .eps

theorem embed_exact (H : Header) (parts : List (MixedAdjacentRecursive.Spec H)) (mode : Bool) :
    ∀ e, HelperArgument.Syntax 0 e → MixedAdjacentRecursive.render H parts true mode (embed H e)=e
  | .seq a b, h | .alt a b, h => by simp only [embed,MixedAdjacentRecursive.render,embed_exact H parts mode a h.1,embed_exact H parts mode b h.2]
  | .star a, h | .notP a, h => by simp only [embed,MixedAdjacentRecursive.render,embed_exact H parts mode a h]
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl
  | .call i [], h => by simp [HelperArgument.Syntax] at h
  | .call _ (_::_), h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

def expand {H : Header} (L : Nat → Body H) : Plan → Body H
  | .leaf i => L i
  | .alt a b => .alt (expand L a) (expand L b)
  | .notP a => .notP (expand L a)
  | .guard a b => .seq (.notP (.notP (expand L a))) (expand L b)

theorem expand_render (H : Header) (parts : List (MixedAdjacentRecursive.Spec H)) (par mode : Bool) (L : Nat → Body H) :
    ∀ P, MixedAdjacentRecursive.render H parts par mode (expand L P)=
      P.exp (fun i => MixedAdjacentRecursive.render H parts par mode (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [expand,MixedAdjacentRecursive.render,Plan.exp,MExp.andP,expand_render H parts par mode L a,expand_render H parts par mode L b]
  | .notP a => by simp only [expand,MixedAdjacentRecursive.render,Plan.exp,expand_render H parts par mode L a]

/-- A codeword capture may feed either kind of leaf. -/
def codeCall (H : Header) (parts : List (Part H)) (a : Argument H) (j : Nat) : Body H :=
  match parts[j]? with
  | none => .notP .eps
  | some r => if r.stuck then .star .eps else if r.split then .call j a else .replay j (embed H (argument H a))

def replayCall (H : Header) (parts : List (Part H)) (a : Body H) (j : Nat) : Body H :=
  match parts[j]? with
  | none => .notP .eps
  | some r => if r.stuck then .star .eps else .replay j a

def normalize (H : Header) (parts : List (Part H)) (specs : List Spec) : Body H → Body H
  | .call i a => match specs[i]? with
    | none => .notP .eps
    | some s => if s.split then
        .seq (.notP (.notP (embed H (argument H a)))) (expand (codeCall H parts a) s.plan)
      else .notP .eps
  | .replay i a => match specs[i]? with
    | none => .notP .eps
    | some s => if s.split then .notP .eps else
        .seq (.notP (.notP (normalize H parts specs a)))
          (expand (replayCall H parts (normalize H parts specs a)) s.plan)
  | .seq a b => .seq (normalize H parts specs a) (normalize H parts specs b)
  | .alt a b => .alt (normalize H parts specs a) (normalize H parts specs b)
  | .star a => .star (normalize H parts specs a)
  | .notP a => .notP (normalize H parts specs a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w

def render (H : Header) (specs : List Spec) : Body H → MExp
  | .call i a => match specs[i]? with
    | none => MExp.failAlways
    | some s => if s.split then .call (i+1) [argument H a] else MExp.failAlways
  | .replay i a => match specs[i]? with
    | none => MExp.failAlways
    | some s => if s.split then MExp.failAlways else .call (i+1) [render H specs a]
  | .seq a b => .seq (render H specs a) (render H specs b)
  | .alt a b => .alt (render H specs a) (render H specs b)
  | .star a => .star (render H specs a)
  | .notP a => .notP (render H specs a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w

def sourceLeaf (H : Header) (parts : List (Part H)) (specs : List Spec) (i : Nat) : MExp :=
  match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.stuck then .star .eps else .seq (sourcePrefix H r.split) (render H specs r.body)
def source (H : Header) (parts : List (Part H)) (specs : List Spec) : MGrammar :=
  ⟨⟨1,.param 0⟩::specs.map (fun s => ⟨1,s.plan.exp (sourceLeaf H parts specs)⟩)⟩
def coreUsers (H : Header) (parts : List (Part H)) (specs : List Spec) : List (MixedAdjacentRecursive.Spec H) :=
  parts.map (fun r => ⟨r.split,normalize H parts specs r.body⟩)
abbrev core (H : Header) (parts : List (Part H)) (specs : List Spec) :=
  MixedAdjacentRecursive.source H (coreUsers H parts specs)
abbrev target (H : Header) (parts : List (Part H)) (specs : List Spec) :=
  MixedAdjacentRecursive.target H (coreUsers H parts specs)
abbrev coreRender (H : Header) (parts : List (Part H)) (specs : List Spec) (mode : Bool) (e : Body H) :=
  MixedAdjacentRecursive.render H (coreUsers H parts specs) true mode (normalize H parts specs e)
abbrev targetRender (H : Header) (parts : List (Part H)) (specs : List Spec) (e : Body H) :=
  MixedAdjacentRecursive.render H (coreUsers H parts specs) false false (normalize H parts specs e)

/-- General captures enter ordinary leaves; codeword captures may enter both. -/
def Valid (H : Header) (parts : List (Part H)) (specs : List Spec) : Prop :=
  ∀ s∈specs, s.plan.All (fun j => ∃ r, parts[j]?=some r ∧ (s.split=false → r.split=false ∨ r.stuck=true))

theorem render_firstOrder (H : Header) (specs : List Spec) : ∀ e, (render H specs e).FirstOrder
  | .call i a => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some s =>
      cases hs : s.split <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true]
      · trivial
      · exact ⟨AdjacentCallsiteRecursive.argument_firstOrder H a,True.intro⟩
  | .replay i a => by
    simp only [render]
    cases specs[i]? with
    | none => trivial
    | some s =>
      cases hs : s.split <;> simp only [hs,Bool.false_eq_true,ite_false,ite_true]
      · exact ⟨render_firstOrder H specs a,True.intro⟩
      · trivial
  | .seq a b | .alt a b => ⟨render_firstOrder H specs a,render_firstOrder H specs b⟩
  | .star a | .notP a => render_firstOrder H specs a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial

theorem prefix_syntax (H : Header) (mode : Bool) : HelperArgument.Syntax 0 (sourcePrefix H mode) := by
  cases mode
  · trivial
  · exact ⟨LastCodewordGrammar.pure_syntax _ H.pure,True.intro⟩
theorem source_firstOrder (H : Header) (parts : List (Part H)) (specs : List Spec) :
    (source H parts specs).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨s,_,rfl⟩ := List.mem_map.mp hr
    apply Plan.exp_firstOrder
    intro j
    unfold sourceLeaf
    cases parts[j]? with
    | none => trivial
    | some r =>
      cases hr : r.stuck <;> simp only [hr,Bool.false_eq_true,ite_false,ite_true]
      · exact ⟨HelperArgument.firstOrder 0 _ (prefix_syntax H r.split),render_firstOrder H specs r.body⟩
      · trivial

theorem source_rule (H : Header) (parts : List (Part H)) (specs : List Spec) (i : Nat) (s : Spec)
    (hr : specs[i]?=some s) : ruleAtM (source H parts specs).rules (i+1)=some ⟨1,s.plan.exp (sourceLeaf H parts specs)⟩ := by
  simp [source,ruleAtM_eq_getElem?,hr]
theorem core_lookup (H : Header) (parts : List (Part H)) (specs : List Spec) (i : Nat) :
    (coreUsers H parts specs)[i]?=(parts[i]?).map (fun r => ⟨r.split,normalize H parts specs r.body⟩) := by
  simp [coreUsers]
theorem core_rule (H : Header) (parts : List (Part H)) (specs : List Spec) (i : Nat) (r : Part H)
    (hr : parts[i]?=some r) : ruleAtM (core H parts specs).rules (i+1)=some
      ⟨1,.seq (sourcePrefix H r.split) (coreRender H parts specs r.split r.body)⟩ := by
  simp only [MixedAdjacentRecursive.source_rule,core_lookup,hr,Option.map_some]

abbrev table (g : MGrammar) (x : List Char) (k : Nat) := tblV g x .callByValuePar k
def leafRows (H : Header) (parts : List (Part H)) (specs : List Spec) (x : List Char) (k : Nat)
    (w : List Char) (p j : Nat) : Res :=
  if (parts[j]?.map Part.stuck)=some true then none else valAt (table (core H parts specs) x k (j+1) [w]) p
def Rows (H : Header) (parts : List (Part H)) (specs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ i s, specs[i]?=some s → ∀ w p, p≤x.length →
    valAt (table (source H parts specs) x k (i+1) [w]) p = s.plan.eval (leafRows H parts specs x k w p) p

theorem codeCall_eval (H : Header) (parts : List (Part H)) (specs : List Spec) (x : List Char) (k : Nat)
    (E : List (List Char)) (a : Argument H) (mode : Bool) (p q j : Nat) (r : Part H)
    (hr : parts[j]?=some r) (ha : evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k)
      E (argument H a) p=some (some q)) :
    evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k) E
      (MixedAdjacentRecursive.render H (coreUsers H parts specs) true mode (codeCall H parts a j)) p=
      leafRows H parts specs x k (pre x p q) p j := by
  simp only [codeCall,hr,leafRows,Option.map_some]
  cases hd : r.stuck <;> simp only [Bool.false_eq_true,ite_false,ite_true,Option.some.injEq]
  case true => exact stuck_eval _ _ _ _ _ _
  case false =>
    cases hs : r.split <;> simp only [Bool.false_eq_true,ite_false,ite_true,MixedAdjacentRecursive.render,
      core_lookup,hr,Option.map_some,hs,ite_false,ite_true]
    · rw [embed_exact H _ mode _ (argument_syntax H a),evV_call_par (core_rule H parts specs j r hr) rfl (by decide)]
      simp only [evParArgs,ha]
    · rw [evV_call_par (core_rule H parts specs j r hr) rfl (by decide)]
      simp only [evParArgs,ha]

theorem replayCall_eval (H : Header) (parts : List (Part H)) (specs : List Spec) (x : List Char) (k : Nat)
    (E : List (List Char)) (a : Body H) (mode : Bool) (p q j : Nat) (r : Part H)
    (hr : parts[j]?=some r) (hs : r.split=false ∨ r.stuck=true)
    (ha : evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k)
      E (coreRender H parts specs mode a) p=some (some q)) :
    evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k) E
      (MixedAdjacentRecursive.render H (coreUsers H parts specs) true mode (replayCall H parts (normalize H parts specs a) j)) p=
      leafRows H parts specs x k (pre x p q) p j := by
  simp only [replayCall,hr,leafRows,Option.map_some]
  cases hd : r.stuck
  · have hk : r.split=false := hs.resolve_right (by simp [hd])
    simp only [Bool.false_eq_true,ite_false,Option.some.injEq,
      MixedAdjacentRecursive.render,core_lookup,hr,Option.map_some,hk,ite_false]
    rw [evV_call_par (core_rule H parts specs j r hr) rfl (by decide)]
    simp only [evParArgs,ha]
  · simp only [ite_true,MixedAdjacentRecursive.render]
    exact stuck_eval _ _ _ _ _ _

/-- Evaluate the argument before control expansion, including when every
leaf of the plan is negative. Failed or undefined arguments cannot be
turned into successful predicates by normalization. -/
theorem call_plan_eq (g h : MGrammar) (x : List Char) (T U : ClockFreezing.Table)
    (i : Nat) (P : Plan) (L : Nat → MExp) (R : List Char → Nat → Res) (E : List (List Char)) (a b : MExp) (p : Nat)
    (hr : ∃ body, ruleAtM g.rules i=some ⟨1,body⟩)
    (harg : evV g x .callByValuePar T E a p=evV h x .callByValuePar U E b p)
    (hRows : ∀ w, valAt (T i [w]) p=P.eval (R w) p)
    (hLeaf : ∀ q, evV h x .callByValuePar U E b p=some (some q) →
      P.All (fun j => evV h x .callByValuePar U E (L j) p=R (pre x p q) j)) :
    evV g x .callByValuePar T E (.call i [a]) p=
      evV h x .callByValuePar U E (.seq (.andP b) (P.exp L)) p := by
  obtain ⟨body,hr⟩ := hr
  rw [evV_call_par hr rfl (by decide)]
  have hguard := CallLookahead.evV_peek h x .callByValuePar U E b p
  rw [←harg] at hguard
  cases hv : evV g x .callByValuePar T E a p with
  | none => rw [evPar_cons_none hv,evV_seq_none (hguard.trans (by rw [hv]; rfl))]
  | some v => cases v with
    | none => rw [evPar_cons_fail hv,evV_seq_fail (hguard.trans (by rw [hv]; rfl))]
    | some q =>
      rw [evPar_cons_ok hv,evV_seq_ok (hguard.trans (by rw [hv]; rfl)),Plan.exp_eval]
      exact (hRows _).trans (Plan.eval_congr P (Plan.all_imp (fun j hj => hj.symm) P (hLeaf q (harg.symm.trans hv))))

theorem coreRender_call (H : Header) (parts : List (Part H)) (specs : List Spec)
    (mode : Bool) (i : Nat) (s : Spec) (hr : specs[i]?=some s) (hs : s.split=true) (a : Argument H) :
    coreRender H parts specs mode (.call i a)=
      .seq (.andP (argument H a)) (s.plan.exp (fun j =>
        MixedAdjacentRecursive.render H (coreUsers H parts specs) true mode (codeCall H parts a j))) := by
  simp only [coreRender,normalize,hr,hs,ite_true,MixedAdjacentRecursive.render]
  rw [embed_exact H _ mode _ (argument_syntax H a),expand_render]
  rfl

theorem coreRender_replay (H : Header) (parts : List (Part H)) (specs : List Spec)
    (mode : Bool) (i : Nat) (s : Spec) (hr : specs[i]?=some s) (hs : s.split=false) (a : Body H) :
    coreRender H parts specs mode (.replay i a)=
      .seq (.andP (coreRender H parts specs mode a)) (s.plan.exp (fun j =>
        MixedAdjacentRecursive.render H (coreUsers H parts specs) true mode (replayCall H parts (normalize H parts specs a) j))) := by
  simp only [coreRender,normalize,hr,hs,Bool.false_eq_true,ite_false,MixedAdjacentRecursive.render]
  rw [expand_render]
  rfl

theorem evaluator_of_rows (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (x : List Char) (k : Nat) (hRows : Rows H parts specs x k) :
    ∀ e mode E p, p≤x.length →
      evV (source H parts specs) x .callByValuePar (table (source H parts specs) x k) E (render H specs e) p=
      evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k) E (coreRender H parts specs mode e) p
  | .call i a, mode, E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,normalize,coreRender,hr,MixedAdjacentRecursive.render,MExp.failAlways,evV]
    | some s =>
      cases hs : s.split
      · simp only [render,normalize,coreRender,hr,hs,Bool.false_eq_true,ite_false,MixedAdjacentRecursive.render,MExp.failAlways,evV]
      · rw [coreRender_call H parts specs mode i s hr hs a]
        simp only [render,hr,hs,ite_true]
        apply call_plan_eq
        · exact ⟨_,source_rule H parts specs i s hr⟩
        · exact LastCodewordGrammar.syntax_eval _ _ x .callByValuePar .callByValuePar _ _
            (tblV_ok _ _ _ k) E _ (argument_syntax H a) p hp
        · intro w; exact hRows i s hr w p hp
        · intro q harg
          apply Plan.all_imp (t:=s.plan) _ (hValid s (List.mem_of_getElem? hr))
          intro j hj
          obtain ⟨r,hrj,_⟩ := hj
          exact codeCall_eval H parts specs x k E a mode p q j r hrj harg
  | .replay i a, mode, E, p, hp => by
    cases hr : specs[i]? with
    | none => simp only [render,normalize,coreRender,hr,MixedAdjacentRecursive.render,MExp.failAlways,evV]
    | some s =>
      cases hs : s.split
      · rw [coreRender_replay H parts specs mode i s hr hs a]
        simp only [render,hr,hs,Bool.false_eq_true,ite_false]
        apply call_plan_eq
        · exact ⟨_,source_rule H parts specs i s hr⟩
        · exact evaluator_of_rows H parts specs hValid x k hRows a mode E p hp
        · intro w; exact hRows i s hr w p hp
        · intro q harg
          apply Plan.all_imp (t:=s.plan) _ (hValid s (List.mem_of_getElem? hr))
          intro j hj
          obtain ⟨r,hrj,hkind⟩ := hj
          exact replayCall_eval H parts specs x k E a mode p q j r hrj (hkind hs) harg
      · simp only [render,normalize,coreRender,hr,hs,ite_true,MixedAdjacentRecursive.render,MExp.failAlways,evV]
  | .param _, _, _, _, _ | .eps, _, _, _, _ | .any, _, _, _, _ | .chr _, _, _, _, _
  | .range _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .seq a b, mode, E, p, hp => by
    have heq := evaluator_of_rows H parts specs hValid x k hRows a mode E p hp
    cases hv : evV (source H parts specs) x .callByValuePar (table (source H parts specs) x k) E (render H specs a) p with
    | none =>
      simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some v => cases v with
      | none => simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some q =>
        simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_rows H parts specs hValid x k hRows b mode E q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
  | .alt a b, mode, E, p, hp => by
    have heq := evaluator_of_rows H parts specs hValid x k hRows a mode E p hp
    cases hv : evV (source H parts specs) x .callByValuePar (table (source H parts specs) x k) E (render H specs a) p with
    | none => simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some v => cases v with
      | none =>
        simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_rows H parts specs hValid x k hRows b mode E p hp
      | some q => simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .star a, mode, E, p, hp =>
    evStar_congr p (fun q hq => evaluator_of_rows H parts specs hValid x k hRows a mode E q (by omega))
  | .notP a, mode, E, p, hp => by
    simp only [render,coreRender,normalize,MixedAdjacentRecursive.render,evV]
    rw [evaluator_of_rows H parts specs hValid x k hRows a mode E p hp]

/-- Normalization preserves complete partial results at every ordinary Par
round; its extra predicates do not require a semantic row assumption. -/
theorem tables_rows (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (x : List Char) : ∀ k, Rows H parts specs x k := by
  intro k
  induction k with
  | zero =>
    intro i s hr w p hp
    change none=s.plan.eval (leafRows H parts specs x 0 w p) p
    symm
    exact Plan.eval_none s.plan (Plan.all_of_forall (fun j => by simp [leafRows,table,tblV,valAt_nil]) s.plan)
  | succ k ih =>
    intro i s hr w p hp
    rw [valAt_tblV_succ (source_rule H parts specs i s hr) [w] hp,Plan.exp_eval]
    apply Plan.eval_congr
    apply Plan.all_imp (t:=s.plan) _ (hValid s (List.mem_of_getElem? hr))
    intro j hj
    obtain ⟨r,hrj,_⟩ := hj
    cases hd : r.stuck
    · simp only [sourceLeaf,hrj,hd,Bool.false_eq_true,ite_false,leafRows,Option.map_some,
        Bool.false_eq_true,Option.some.injEq,ite_false]
      rw [valAt_tblV_succ (core_rule H parts specs j r hrj) [w] hp]
      have heq := LastCodewordGrammar.syntax_eval (source H parts specs) (core H parts specs)
        x .callByValuePar .callByValuePar (table (source H parts specs) x k) (table (core H parts specs) x k)
        (tblV_ok _ _ _ k) [w] _ (prefix_syntax H r.split) p hp
      cases hv : evV (source H parts specs) x .callByValuePar (table (source H parts specs) x k)
          [w] (sourcePrefix H r.split) p with
      | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
      | some v => cases v with
        | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
          exact evaluator_of_rows H parts specs hValid x k ih r.body r.split [w] q
            (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
    · simp only [sourceLeaf,hrj,hd,ite_true,leafRows,Option.map_some,stuck_eval]

theorem evaluator_eq (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (x : List Char) (k : Nat) (e : Body H) (mode : Bool)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source H parts specs) x .callByValuePar (table (source H parts specs) x k) E (render H specs e) p=
    evV (core H parts specs) x .callByValuePar (table (core H parts specs) x k) E (coreRender H parts specs mode e) p :=
  evaluator_of_rows H parts specs hValid x k (tables_rows H parts specs hValid x k) e mode E p hp

theorem normalized_observations_iff (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (e : Body H) (x : List Char) (r : Option (List Char)) :
    SObs (source H parts specs) .callByValuePar (render H specs e) x r ↔
    SObs (core H parts specs) .callByValuePar (coreRender H parts specs false e) x r := by
  rw [←decideObsV_iff (source_firstOrder H parts specs) (by decide) (render_firstOrder H specs e),
    ←decideObsV_iff (MixedAdjacentRecursive.source_firstOrder H _) (by decide)
      (MixedAdjacentRecursive.render_firstOrder H _ true false _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq (source H parts specs) (core H parts specs)
    x .callByValuePar .callByValuePar (render H specs e) (coreRender H parts specs false e)
    (fun k => evaluator_eq H parts specs hValid x k e false [] x.length (Nat.le_refl _))]

/-- One fixed Seq grammar preserves all finite observations on unchanged
strings, including origin-returning negative control over shifted leaves. -/
theorem observations_iff (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (e : Body H) (x : List Char) (r : Option (List Char)) :
    SObs (source H parts specs) .callByValuePar (render H specs e) x r ↔
    SObs (target H parts specs) .callByValueSeq (targetRender H parts specs e) x r :=
  (normalized_observations_iff H parts specs hValid e x r).trans
    (MixedAdjacentRecursive.observations_iff H (coreUsers H parts specs) (normalize H parts specs e) x r)

theorem language_translation (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (e : Body H) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source H parts specs) .callByValuePar (render H specs e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨target H parts specs,targetRender H parts specs e,
    MixedAdjacentRecursive.target_firstOrder H _,MixedAdjacentRecursive.render_firstOrder H _ false false _,
    fun x => observations_iff H parts specs hValid e x (some [])⟩

end Shallot.MacroPeg.CBV.MixedOriginControl
