import MacroPeg.CBV.EmptyCaptureDecision

/-! Finite-control elimination of retained words whose only direct replay is
explicitly guarded by EOF. Calls and actual arguments may mutually recurse
and actuals may inspect the current parameters through the same operation. -/
namespace Shallot.MacroPeg.CBV.EmptyObservedSyntax
open EmptyResultObservation (gate)

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | atEnd (i : Nat)
  | call (i : Nat) (args : List Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

structure Rule where
  arity : Nat
  body : Expr
  deriving Repr

structure Key where
  rule : Nat
  bits : List Bool
  zero : Bool
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).flatMap (fun bits => [false::bits,true::bits])

theorem mem_masks (n : Nat) (bits : List Bool) : bits∈masks n ↔ bits.length=n := by
  induction n generalizing bits with
  | zero => cases bits <;> simp [masks]
  | succ n ih =>
    cases bits with
    | nil => simp [masks]
    | cons b bits =>
      simp only [masks,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,List.length_cons,Nat.add_right_cancel_iff]
      cases b <;> simp [ih]

def keys (rs : List Rule) : List Key := rs.zipIdx.flatMap (fun (r,i) =>
  (masks r.arity).flatMap (fun bits => [⟨i,bits,false⟩,⟨i,bits,true⟩]))
def address (rs : List Rule) (i : Nat) (bits : List Bool) (zero : Bool) := (keys rs).idxOf ⟨i,bits,zero⟩

theorem key_mem (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r)
    (bits : List Bool) (hb : bits.length=r.arity) (zero : Bool) : (⟨i,bits,zero⟩ : Key)∈keys rs := by
  apply List.mem_flatMap.mpr
  refine ⟨(r,i),?_,?_⟩
  · exact List.mem_of_getElem? (show rs.zipIdx[i]?=some (r,i) from by simp [List.getElem?_zipIdx,hr])
  · apply List.mem_flatMap.mpr
    refine ⟨bits,(mem_masks r.arity bits).mpr hb,?_⟩
    cases zero <;> simp

mutual
  def original : Expr → MExp
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | .atEnd i => .seq (.notP .any) (.param i)
  | .call i args => .call i (originalArgs args)
  | .seq a b => .seq (original a) (original b)
  | .alt a b => .alt (original a) (original b)
  | .notP a => .notP (original a)
  | .star a => .star (original a)

  def originalArgs : List Expr → List MExp
    | [] => []
    | a::args => original a::originalArgs args
end

@[simp] theorem originalArgs_eq_map (args : List Expr) : originalArgs args=args.map original := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [originalArgs,List.map_cons,ih]

/-- Normal and empty-result versions of each actual are paired. -/
def preflight : List (MExp × MExp) → MExp
  | [] => .eps
  | (a,_)::args => .seq (.andP a) (preflight args)
def decision : List (MExp × MExp) → (List Bool → MExp) → MExp
  | [],f => f []
  | (_,z)::args,f => RootObservation.branch z
      (decision args (fun bits => f (true::bits)))
      (decision args (fun bits => f (false::bits)))
def dispatch (pairs : List (MExp × MExp)) (f : List Bool → MExp) : MExp :=
  .seq (preflight pairs) (decision pairs f)

mutual
  def emit (rs : List Rule) (bits : List Bool) (zero : Bool) (e : Expr) : MExp :=
  match e,zero with
  | .eps,_ => .eps
  | .any,false => .any
  | .chr c,false => .chr c
  | .range a b,false => .range a b
  | .lit w,false => .lit w
  | .any,true | .chr _,true | .range _ _,true => MExp.failAlways
  | .lit w,true => if w=[] then .eps else MExp.failAlways
  | .atEnd i,_ => if bits[i]?.getD false then .notP .any else MExp.failAlways
  | .call i args,_ => match rs[i]? with
    | none => MExp.failAlways
    | some r => if r.arity=args.length then
        dispatch (emitArgs rs bits args)
          (fun next => .call (address rs i next zero) [])
      else MExp.failAlways
  | .seq a b,false => .seq (emit rs bits false a) (emit rs bits false b)
  | .alt a b,false => .alt (emit rs bits false a) (emit rs bits false b)
  | .notP a,_ => .notP (emit rs bits false a)
  | .star a,false => .star (emit rs bits false a)
  | .seq a b,true => gate (.seq (emit rs bits false a) (emit rs bits false b)) (.seq (emit rs bits true a) (emit rs bits true b))
  | .alt a b,true => gate (.alt (emit rs bits false a) (emit rs bits false b))
      (.alt (emit rs bits true a) (.seq (.notP (emit rs bits false a)) (emit rs bits true b)))
  | .star a,true => gate (.star (emit rs bits false a)) (.notP (emit rs bits false a))
  def emitArgs (rs : List Rule) (bits : List Bool) : List Expr → List (MExp × MExp)
    | [] => []
    | a::args => (emit rs bits false a,emit rs bits true a)::emitArgs rs bits args
end

@[simp] theorem emitArgs_eq_map (rs : List Rule) (bits : List Bool) (args : List Expr) :
    emitArgs rs bits args=args.map (fun a => (emit rs bits false a,emit rs bits true a)) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [emitArgs,List.map_cons,ih]

def source (rs : List Rule) : MGrammar := ⟨rs.map (fun r => ⟨r.arity,original r.body⟩)⟩
def targetRule (rs : List Rule) (key : Key) : MRule := ⟨0,emit rs key.bits key.zero ((rs[key.rule]?).map Rule.body |>.getD .eps)⟩
def target (rs : List Rule) : MGrammar := ⟨(keys rs).map (targetRule rs)⟩

theorem source_rule (rs : List Rule) (i : Nat) :
    ruleAtM (source rs).rules i=(rs[i]?).map (fun r => ⟨r.arity,original r.body⟩) := by
  simp [source,ruleAtM_eq_getElem?]

private theorem key_lookup (xs : List Key) (key : Key) (hm : key∈xs) :
    xs[xs.idxOf key]?=some key := by
  induction xs with
  | nil => cases hm
  | cons a xs ih =>
    by_cases he : a=key
    · subst a; simp
    · have ht : key∈xs := by
        rcases List.mem_cons.mp hm with hh|ht
        · exact False.elim (he hh.symm)
        · exact ht
      simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,he,ih ht]

theorem target_rule (rs : List Rule) (i : Nat) (r : Rule) (hr : rs[i]?=some r)
    (bits : List Bool) (hb : bits.length=r.arity) (zero : Bool) :
    ruleAtM (target rs).rules (address rs i bits zero)=some ⟨0,emit rs bits zero r.body⟩ := by
  have hm := key_mem rs i r hr bits hb zero
  have hh := key_lookup (keys rs) ⟨i,bits,zero⟩ hm
  simpa [target,ruleAtM_eq_getElem?,address,List.getElem?_map,hh,targetRule,hr] using
    congrArg (Option.map (targetRule rs)) hh


mutual
  theorem original_firstOrder : ∀ (e : Expr), (original e).FirstOrder
    | .seq a b | .alt a b => by simpa only [original,originalArgs_eq_map,MExp.FirstOrder] using And.intro (original_firstOrder a) (original_firstOrder b)
    | .notP a | .star a => by simpa only [original,originalArgs_eq_map,MExp.FirstOrder] using original_firstOrder a
    | .call i args => by simpa only [original,originalArgs_eq_map,MExp.FirstOrder] using original_args_firstOrder args
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .atEnd _ => by simp [original,originalArgs_eq_map,MExp.FirstOrder]
  termination_by e => sizeOf e
  decreasing_by all_goals simp_wf; all_goals omega
  theorem original_args_firstOrder : ∀ (args : List Expr), MExp.FirstOrderArgs (args.map original)
    | [] => True.intro
    | a::args => ⟨original_firstOrder a,original_args_firstOrder args⟩
  termination_by args => sizeOf args
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem source_firstOrder (rs : List Rule) : (source rs).FirstOrder := by
  intro r hr
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
  exact original_firstOrder _

end Shallot.MacroPeg.CBV.EmptyObservedSyntax
