import MacroPeg.CBV.TypedFieldCompiler
import MacroPeg.CBV.MixedGrowthChecks

/-! Distribute origin-preserving control over separate typed field entries.
The original header has an arbitrary finite alt/not/guard tree, with no
common leading replay. Its strict actuals are evaluated before dispatch.
Consuming sequence/repetition is confined to leaf tails; redispatching their
original actuals after advancing the cursor would be incorrect. -/
namespace Shallot.MacroPeg.CBV.FieldPlanSyntax
open ReplayControlFusion (Plan)
open TypedFieldSyntax (Header)
open MixedGrowthChecks (firstOrderCheck firstOrder_checked)

structure Spec where
  arity : Nat
  plan : Plan

def sourceLeaf (parts : List Header) (j : Nat) : MExp := match parts[j]? with
  | none => MExp.failAlways
  | some r => TupleFieldTransfer.sourceBody r.delimiter r.pattern r.body
def source (parts : List Header) (specs : List Spec) : MGrammar :=
  ⟨specs.map (fun s => ⟨s.arity,s.plan.exp (sourceLeaf parts)⟩)⟩

mutual
  def render (parts : List Header) (specs : List Spec) : MExp → MExp
    | .call i args => match specs[i]? with
      | none => MExp.failAlways
      | some s => if s.arity=args.length then
          .seq (DelimitedPatternEvaluation.preflight (renderArgs parts specs args))
            (s.plan.exp (fun j => .call j (renderArgs parts specs args)))
        else MExp.failAlways
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .param i => .param i
    | .seq a b => .seq (render parts specs a) (render parts specs b)
    | .alt a b => .alt (render parts specs a) (render parts specs b)
    | .notP a => .notP (render parts specs a)
    | .star a => .star (render parts specs a)
    | _ => MExp.failAlways
  def renderArgs (parts : List Header) (specs : List Spec) : List MExp → List MExp
    | [] => []
    | a::args => render parts specs a::renderArgs parts specs args
end

def expandedHeaders (parts : List Header) (specs : List Spec) : List Header :=
  parts.map (fun r => {r with body:=render parts specs r.body})
def expanded (parts : List Header) (specs : List Spec) : MGrammar :=
  TypedFieldSyntax.source (expandedHeaders parts specs)

def planCheck (parts : List Header) (arity : Nat) : Plan → Bool
  | .leaf j => match parts[j]? with
    | none => false
    | some r => decide (r.parameters.length=arity)
  | .alt a b | .guard a b => planCheck parts arity a && planCheck parts arity b
  | .notP a => planCheck parts arity a
def check (parts : List Header) (specs : List Spec) : Bool :=
  parts.all (fun r => firstOrderCheck r.body) && specs.all (fun s => planCheck parts s.arity s.plan)

def ValidPlan (parts : List Header) (s : Spec) : Prop :=
  s.plan.All (fun j => ∃ r, parts[j]?=some r ∧ r.parameters.length=s.arity)
structure Valid (ps : List Header) (ss : List Spec) : Prop where
  parts : ∀ r∈ps, r.body.FirstOrder
  specs : ∀ s∈ss, ValidPlan ps s

theorem plan_checked (parts : List Header) (arity : Nat) : ∀ P,
    planCheck parts arity P=true → P.All (fun j => ∃ r, parts[j]?=some r ∧ r.parameters.length=arity)
  | .leaf j,h => by
    cases hr : parts[j]? with
    | none => simp [planCheck,hr] at h
    | some r => exact ⟨r,hr,of_decide_eq_true (show decide (r.parameters.length=arity)=true by simpa only [planCheck,hr] using h)⟩
  | .alt a b,h | .guard a b,h => ⟨plan_checked parts arity a (Bool.and_eq_true_iff.mp h).1,
      plan_checked parts arity b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a,h => plan_checked parts arity a h

theorem checked (parts : List Header) (specs : List Spec) (hc : check parts specs=true) : Valid parts specs := by
  obtain ⟨hp,hs⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨(by intro r hr; exact firstOrder_checked r.body (List.all_eq_true.mp hp r hr)),
    (by intro s hs'; exact plan_checked parts s.arity s.plan (List.all_eq_true.mp hs s hs'))⟩

theorem renderArgs_length (parts : List Header) (specs : List Spec) : ∀ args,
    (renderArgs parts specs args).length=args.length
  | [] => rfl
  | a::args => congrArg Nat.succ (renderArgs_length parts specs args)

mutual
  theorem render_firstOrder (parts : List Header) (specs : List Spec) : ∀ e, (render parts specs e).FirstOrder
    | .call i args => by
      simp only [render]
      split
      · trivial
      · split
        · exact ⟨DelimitedPatternCompiler.preflight_firstOrder _ (renderArgs_firstOrder parts specs args),
            Plan.exp_firstOrder (L:=fun j => .call j (renderArgs parts specs args))
              (fun _ => renderArgs_firstOrder parts specs args) _⟩
        · trivial
    | .seq a b | .alt a b => ⟨render_firstOrder parts specs a,render_firstOrder parts specs b⟩
    | .notP a | .star a => render_firstOrder parts specs a
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
  theorem renderArgs_firstOrder (parts : List Header) (specs : List Spec) : ∀ args,
      MExp.FirstOrderArgs (renderArgs parts specs args)
    | [] => True.intro
    | a::args => ⟨render_firstOrder parts specs a,renderArgs_firstOrder parts specs args⟩
end

theorem sourceLeaf_firstOrder (parts : List Header) (specs : List Spec) (hv : Valid parts specs) (j : Nat) :
    (sourceLeaf parts j).FirstOrder := by
  unfold sourceLeaf
  cases hr : parts[j]? with
  | none => trivial
  | some r => exact ⟨DelimiterTemplate.compile_firstOrder _ _,hv.parts r (List.mem_of_getElem? hr)⟩
theorem source_firstOrder (parts : List Header) (specs : List Spec) (hv : Valid parts specs) :
    (source parts specs).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact Plan.exp_firstOrder (sourceLeaf_firstOrder parts specs hv) s.plan
theorem expanded_firstOrder (parts : List Header) (specs : List Spec) : (expanded parts specs).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
  exact ⟨DelimiterTemplate.compile_firstOrder _ _,render_firstOrder parts specs a.body⟩

theorem source_row (parts : List Header) (specs : List Spec) (i : Nat) (s : Spec) (hs : specs[i]?=some s) :
    ruleAtM (source parts specs).rules i=some ⟨s.arity,s.plan.exp (sourceLeaf parts)⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hs]
theorem expanded_row (parts : List Header) (specs : List Spec) (j : Nat) (r : Header) (hr : parts[j]?=some r) :
    ruleAtM (expanded parts specs).rules j=some ⟨r.parameters.length,
      TupleFieldTransfer.sourceBody r.delimiter r.pattern (render parts specs r.body)⟩ := by
  simp [expanded,expandedHeaders,TypedFieldSyntax.source,ruleAtM_eq_getElem?,List.getElem?_map,hr]

end Shallot.MacroPeg.CBV.FieldPlanSyntax
