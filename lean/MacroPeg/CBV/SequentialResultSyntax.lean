import MacroPeg.CBV.EmptyResultObservation
import MacroPeg.CBV.SequentialClock

/-! Ordinary and zero-result observers for arbitrary first-order Seq rules.
Every zero-result call has only empty captures, so its observer row is nullary.
The full-call gates preserve undefined computations skipped by zero-only paths. -/
namespace Shallot.MacroPeg.CBV.SequentialResultSyntax
open EmptyResultObservation (project gate)

mutual
  def normal : MExp → MExp
    | .call i args => .call (2*i) (normalArgs args)
    | .seq a b => .seq (normal a) (normal b)
    | .alt a b => .alt (normal a) (normal b)
    | .notP a => .notP (normal a)
    | .star a => .star (normal a)
    | e => e
  def normalArgs : List MExp → List MExp
    | [] => []
    | a::args => normal a::normalArgs args
end

def emptyParameter (i : Nat) : MExp := .andP (.seq (.star .any) (.param i))

mutual
  def zero : MExp → MExp
    | .eps => .eps
    | .any | .chr _ | .range _ _ => MExp.failAlways
    | .lit w => if w=[] then .eps else MExp.failAlways
    | .param i => emptyParameter i
    | .call i args => gate (normal (.call i args)) (.seq (zeroArgs args) (.call (2*i+1) []))
    | .seq a b => gate (normal (.seq a b)) (.seq (zero a) (zero b))
    | .alt a b => gate (normal (.alt a b)) (.alt (zero a) (.seq (.notP (normal a)) (zero b)))
    | .notP a => normal (.notP a)
    | .star a => gate (normal (.star a)) (.notP (normal a))
    | _ => MExp.failAlways
  def zeroArgs : List MExp → MExp
    | [] => .eps
    | a::args => .seq (zero a) (zeroArgs args)
end

def emptyBody (r : MRule) : MExp := MExp.subst (List.replicate r.arity (.lit [])) r.body
def target (g : MGrammar) : MGrammar :=
  ⟨g.rules.flatMap (fun r => [⟨r.arity,normal r.body⟩,⟨0,zero (emptyBody r)⟩])⟩

theorem normalArgs_length (args : List MExp) : (normalArgs args).length=args.length := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [normalArgs,List.length_cons,ih]

mutual
  theorem normal_firstOrder : ∀ e, e.FirstOrder → (normal e).FirstOrder
    | .call _ args,h => normalArgs_firstOrder args h
    | .seq a b,h | .alt a b,h => ⟨normal_firstOrder a h.1,normal_firstOrder b h.2⟩
    | .notP a,h | .star a,h => normal_firstOrder a h
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => False.elim h
  theorem normalArgs_firstOrder : ∀ args, MExp.FirstOrderArgs args → MExp.FirstOrderArgs (normalArgs args)
    | [],_ => trivial
    | a::args,h => ⟨normal_firstOrder a h.1,normalArgs_firstOrder args h.2⟩
end

mutual
  theorem zero_firstOrder : ∀ e, e.FirstOrder → (zero e).FirstOrder
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ => trivial
    | .lit w,_ => by simp only [zero]; split <;> trivial
    | .param _,_ => ⟨True.intro,True.intro⟩
    | .call i args,h => ⟨normalArgs_firstOrder args h,zeroArgs_firstOrder args h,True.intro⟩
    | .seq a b,h => ⟨normal_firstOrder _ h,zero_firstOrder a h.1,zero_firstOrder b h.2⟩
    | .alt a b,h => ⟨normal_firstOrder _ h,zero_firstOrder a h.1,normal_firstOrder a h.1,zero_firstOrder b h.2⟩
    | .notP a,h => normal_firstOrder _ h
    | .star a,h => ⟨normal_firstOrder _ h,normal_firstOrder a h⟩
    | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => False.elim h
  theorem zeroArgs_firstOrder : ∀ args, MExp.FirstOrderArgs args → (zeroArgs args).FirstOrder
    | [],_ => trivial
    | a::args,h => ⟨zero_firstOrder a h.1,zeroArgs_firstOrder args h.2⟩
end

theorem emptyBody_firstOrder (r : MRule) (h : r.body.FirstOrder) : (emptyBody r).FirstOrder := by
  have he : MExp.FirstOrderArgs (List.replicate r.arity (.lit [])) := by
    induction r.arity with
    | zero => trivial
    | succ n ih => exact ⟨True.intro,ih⟩
  exact firstOrder_subst he r.body h

theorem target_firstOrder (g : MGrammar) (hg : g.FirstOrder) : (target g).FirstOrder := by
  intro r hr
  obtain ⟨b,hb,hr⟩ := List.mem_flatMap.mp hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact normal_firstOrder _ (hg _ hb)
  · exact zero_firstOrder _ (emptyBody_firstOrder b (hg _ hb))

theorem target_rule (g : MGrammar) (i : Nat) (odd : Bool) :
    ruleAtM (target g).rules (2*i+(if odd then 1 else 0))=
      (ruleAtM g.rules i).map (fun r => if odd then ⟨0,zero (emptyBody r)⟩ else ⟨r.arity,normal r.body⟩) := by
  cases g with
  | mk rules =>
    induction rules generalizing i with
    | nil => cases odd <;> rfl
    | cons r rules ih =>
      cases i with
      | zero => cases odd <;> rfl
      | succ i =>
        rw [show 2*(i+1)+(if odd then 1 else 0)=(2*i+(if odd then 1 else 0))+2 by omega]
        simpa only [target,ruleAtM_eq_getElem?,List.flatMap_cons,List.cons_append,List.nil_append,List.getElem?_cons_succ,
          Nat.add_succ,Nat.add_zero] using ih i

theorem rule_count (g : MGrammar) : (target g).rules.length=2*g.rules.length := by
  cases g with
  | mk rules =>
    induction rules with
    | nil => rfl
    | cons r rules ih => simp [target,List.flatMap_cons] at *; omega

end Shallot.MacroPeg.CBV.SequentialResultSyntax
