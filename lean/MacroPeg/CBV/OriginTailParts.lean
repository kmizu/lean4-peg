import MacroPeg.CBV.OriginTailPlan
import MacroPeg.CBV.EmptyArgumentSpecialization

namespace Shallot.MacroPeg.CBV.OriginTailParts
open ReplayControlFusion (Part Plan sourceLeaf)
open MultiplyingPrefixCompiler (Spec)
export OriginHeadParts (power rebased attached partAt)

def tailSupported (B : MExp) : Bool := if ZeroResetOrigin.closedCheck B then true else
  match B with | .seq (.param 0) _ => true | _ => false

def tailPart (B : MExp) : Part := if ZeroResetOrigin.closedCheck B then ⟨false,B⟩ else
  match B with | .seq (.param 0) C => ⟨true,C⟩ | _ => ⟨false,MExp.failAlways⟩

def donePart (m : Nat) (B : MExp) (a : Part) : Part :=
  if a.replay || ZeroResetOrigin.closedCheck B then attached B (rebased m a) else ⟨false,MExp.failAlways⟩

def doneCheck (B : MExp) (a : Part) : Bool :=
  a.replay || ZeroResetOrigin.closedCheck B || (EmptyArgumentSpecialization.zeroCheck a.body && tailSupported B)

def donePlan (parts : List Part) (r : Spec) (i : Nat) : Plan :=
  if (partAt parts i).replay || ZeroResetOrigin.closedCheck r.tail then .leaf (2*parts.length+i)
  else .guard (.leaf (parts.length+i)) (.leaf (3*parts.length))

def flowCheck (parts : List Part) (B : MExp) : Plan → Bool
  | .leaf i => match parts[i]? with | none => false | some a => doneCheck B a
  | .alt a b => flowCheck parts B a && flowCheck parts B b
  | .guard _ b => flowCheck parts B b
  | .notP _ => tailSupported B

def item (parts : List Part) (r : Spec) (i : Nat) : Part :=
  if i<parts.length then partAt parts i else
  if i<2*parts.length then rebased r.factor (partAt parts (i-parts.length)) else
  if i<3*parts.length then donePart r.factor r.tail (partAt parts (i-2*parts.length)) else
  if i=3*parts.length then tailPart r.tail else
  if i=3*parts.length+1 then ⟨true,.andP (power (r.factor-1))⟩ else ⟨true,r.fallback⟩
def extended (parts : List Part) (r : Spec) : List Part :=
  (List.range (3*parts.length+3)).map (item parts r)
def plan (parts : List Part) (r : Spec) (P : Plan) : Plan :=
  .alt (.guard (.leaf (3*parts.length+1)) (OriginTailPlan.append parts.length (3*parts.length) (donePlan parts r) P))
    (.leaf (3*parts.length+2))

theorem lookup (parts : List Part) (r : Spec) (i : Nat) (hi : i<3*parts.length+3) :
    (extended parts r)[i]?=some (item parts r i) := by
  simp only [extended,List.getElem?_map,List.getElem?_range hi,Option.map_some]

theorem old_lookup (parts : List Part) (r : Spec) (i : Nat) (p : Part) (hr : parts[i]?=some p) :
    (extended parts r)[i]?=some p := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [lookup parts r i (by omega)]
  simp only [item,if_pos hi,partAt,hr,Option.getD_some]

theorem base_lookup (parts : List Part) (r : Spec) (i : Nat) (p : Part) (hr : parts[i]?=some p) :
    (extended parts r)[parts.length+i]?=some (rebased r.factor p) := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬parts.length+i<parts.length by omega,show parts.length+i<2*parts.length by omega,
    show parts.length+i-parts.length=i by omega,partAt,hr]

theorem done_lookup (parts : List Part) (r : Spec) (i : Nat) (p : Part) (hr : parts[i]?=some p) :
    (extended parts r)[2*parts.length+i]?=some (donePart r.factor r.tail p) := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬2*parts.length+i<parts.length by omega,show ¬2*parts.length+i<2*parts.length by omega,
    show 2*parts.length+i<3*parts.length by omega,show 2*parts.length+i-2*parts.length=i by omega,partAt,hr]

theorem tail_lookup (parts : List Part) (r : Spec) :
    (extended parts r)[3*parts.length]?=some (tailPart r.tail) := by
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬3*parts.length<parts.length by omega,show ¬3*parts.length<2*parts.length by omega]

theorem gate_lookup (parts : List Part) (r : Spec) :
    (extended parts r)[3*parts.length+1]?=some ⟨true,.andP (power (r.factor-1))⟩ := by
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬3*parts.length+1<parts.length by omega,show ¬3*parts.length+1<2*parts.length by omega,
    show ¬3*parts.length+1<3*parts.length by omega]

theorem fallback_lookup (parts : List Part) (r : Spec) :
    (extended parts r)[3*parts.length+2]?=some ⟨true,r.fallback⟩ := by
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬3*parts.length+2<parts.length by omega,show ¬3*parts.length+2<2*parts.length by omega,
    show ¬3*parts.length+2<3*parts.length by omega]

theorem old_plan_eq (parts : List Part) (r : Spec) : ∀ P,
    ReplayControlFusion.ValidPlan parts P → P.exp (sourceLeaf (extended parts r))=P.exp (sourceLeaf parts)
  | .leaf i,h => by
    obtain ⟨a,ha⟩ := h
    simp only [Plan.exp,sourceLeaf,ha,old_lookup parts r i a ha]
  | .alt a b,h | .guard a b,h => by simp only [Plan.exp,old_plan_eq parts r a h.1,old_plan_eq parts r b h.2]
  | .notP a,h => by simp only [Plan.exp,old_plan_eq parts r a h]

theorem flow_checked (parts : List Part) (B : MExp) : ∀ P, flowCheck parts B P=true →
    OriginTailPlan.Exits (fun i => ∃ a, parts[i]?=some a ∧ doneCheck B a=true) (tailSupported B=true) P
  | .leaf i,h => by
    cases hi : parts[i]? with
    | none => simp [flowCheck,hi] at h
    | some a => exact ⟨a,hi,by simpa only [flowCheck,hi] using h⟩
  | .alt a b,h => ⟨flow_checked parts B a (Bool.and_eq_true_iff.mp h).1,flow_checked parts B b (Bool.and_eq_true_iff.mp h).2⟩
  | .guard _ b,h => flow_checked parts B b h
  | .notP _,h => h

theorem tail_expression (B : MExp) (h : tailSupported B=true) : sourceLeaf [tailPart B] 0=B := by
  by_cases hc : ZeroResetOrigin.closedCheck B=true
  · simp only [tailPart,hc,if_true,sourceLeaf,List.getElem?_cons_zero,Bool.false_eq_true,if_false]
  · have hf : ZeroResetOrigin.closedCheck B=false := Bool.eq_false_iff.mpr hc
    simp only [tailSupported,hf,Bool.false_eq_true,if_false] at h
    cases B <;> simp_all [tailPart,sourceLeaf]
    rename_i a b
    cases a <;> try simp_all [tailPart,sourceLeaf]
    rename_i k
    cases k <;> simp_all [tailPart,sourceLeaf]

theorem closed_parts (parts : List Part) (r : Spec) (hc : ZeroResetOrigin.closedCheck r.tail=true) :
    extended parts r=OriginHeadParts.extended parts r := by
  apply congrArg (fun f => (List.range (3*parts.length+3)).map f)
  funext i
  simp only [item,OriginHeadParts.item,donePart,tailPart,hc,Bool.or_true,if_true]

theorem closed_plan (parts : List Part) (r : Spec) (hc : ZeroResetOrigin.closedCheck r.tail=true) (P : Plan) :
    plan parts r P=OriginHeadParts.plan parts r P := by
  have hd (i : Nat) : donePlan parts r i=.leaf (2*parts.length+i) := by simp [donePlan,hc]
  have hh : ∀ Q, OriginTailPlan.append parts.length (3*parts.length) (donePlan parts r) Q=
      OriginHeadPlan.after parts.length (2*parts.length) (3*parts.length) Q := by
    intro Q
    induction Q with
    | leaf i => exact hd i
    | alt a b ia ib | guard a b ia ib => simp only [OriginTailPlan.append,OriginHeadPlan.after,ia,ib]
    | notP a ia => rfl
  simp only [plan,OriginHeadParts.plan,hh]

theorem closed_flow (parts : List Part) (B : MExp) (hc : ZeroResetOrigin.closedCheck B=true) :
    ∀ P, ReplayControlFusion.ValidPlan parts P → flowCheck parts B P=true
  | .leaf i,h => by obtain ⟨a,ha⟩ := h; simp [flowCheck,ha,doneCheck,hc]
  | .alt a b,h => by simp only [flowCheck,closed_flow parts B hc a h.1,closed_flow parts B hc b h.2,Bool.and_self]
  | .guard a b,h => closed_flow parts B hc b h.2
  | .notP a,h => by simp [flowCheck,tailSupported,hc]

end Shallot.MacroPeg.CBV.OriginTailParts
