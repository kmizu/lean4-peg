import MacroPeg.CBV.OriginHeadPlan

namespace Shallot.MacroPeg.CBV.OriginHeadParts
open OriginHeadPlan
open ReplayControlFusion (Part Plan sourceLeaf)
open MultiplyingPrefixCompiler (Spec)
open RepeatedWordArguments (expression)

def power (m : Nat) := expression (.param 0) m
def rebased (m : Nat) (r : Part) : Part :=
  if r.replay then ⟨true,.seq (power (m-1)) (MExp.subst [power m] r.body)⟩ else r

def attached (B : MExp) (r : Part) : Part := ⟨r.replay,.seq r.body B⟩
def partAt (parts : List Part) (i : Nat) := (parts[i]?).getD ⟨false,MExp.failAlways⟩
def item (parts : List Part) (r : Spec) (i : Nat) : Part :=
  if i<parts.length then partAt parts i else
  if i<2*parts.length then rebased r.factor (partAt parts (i-parts.length)) else
  if i<3*parts.length then attached r.tail (rebased r.factor (partAt parts (i-2*parts.length))) else
  if i=3*parts.length then ⟨false,r.tail⟩ else
  if i=3*parts.length+1 then ⟨true,.andP (power (r.factor-1))⟩ else ⟨true,r.fallback⟩
def extended (parts : List Part) (r : Spec) : List Part :=
  (List.range (3*parts.length+3)).map (item parts r)
def plan (parts : List Part) (r : Spec) (P : Plan) : Plan :=
  .alt (.guard (.leaf (3*parts.length+1)) (after parts.length (2*parts.length) (3*parts.length) P))
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
    (extended parts r)[2*parts.length+i]?=some (attached r.tail (rebased r.factor p)) := by
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  rw [lookup parts r _ (by omega)]
  simp [item,show ¬2*parts.length+i<parts.length by omega,show ¬2*parts.length+i<2*parts.length by omega,
    show 2*parts.length+i<3*parts.length by omega,show 2*parts.length+i-2*parts.length=i by omega,partAt,hr]

theorem tail_lookup (parts : List Part) (r : Spec) :
    (extended parts r)[3*parts.length]?=some ⟨false,r.tail⟩ := by
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

theorem subst_plan (args : List MExp) (L : Nat → MExp) : ∀ (P : Plan),
    MExp.subst args (P.exp L)=P.exp (fun i => MExp.subst args (L i))
  | .leaf _ => rfl
  | .alt a b | .guard a b => by simp only [Plan.exp,MExp.subst,subst_plan args L a,subst_plan args L b,MExp.andP]
  | .notP a => by simp only [Plan.exp,MExp.subst,subst_plan args L a]

private theorem assoc (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (a b c : MExp) (p : Nat) :
    evV g x s T E (.seq a (.seq b c)) p=evV g x s T E (.seq (.seq a b) c) p := by
  simp only [evV]
  cases evV g x s T E a p with
  | none => rfl
  | some r => cases r <;> rfl

theorem rebased_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (m : Nat) (hm : 1≤m) (r : Part) (hv : ReplayControlFusion.ValidPart r) (p : Nat) :
    evV g x s T E (sourceLeaf [rebased m r] 0) p=
      evV g x s T E (MExp.subst [power m] (sourceLeaf [r] 0)) p := by
  have hsucc : m=(m-1)+1 := by omega
  cases hb : r.replay
  · simp only [rebased,hb,Bool.false_eq_true,if_false,sourceLeaf,List.getElem?_cons_zero]
    rw [ReplayFallbackFusion.subst_closed _ _ (hv.2 hb)]
  · simp only [rebased,hb,if_true,sourceLeaf,List.getElem?_cons_zero,MExp.subst,argAt]
    have he : power m=.seq (.param 0) (power (m-1)) := by exact congrArg (expression (.param 0)) hsucc
    rw [he]
    exact assoc g x s T E _ _ _ p

theorem attached_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (B : MExp) (r : Part) (p : Nat) :
    evV g x s T E (sourceLeaf [attached B r] 0) p=
      follow (evV g x s T E (sourceLeaf [r] 0) p) (fun q => evV g x s T E B q) := by
  cases hb : r.replay <;>
    simp only [sourceLeaf,List.getElem?_cons_zero,attached,hb,Bool.false_eq_true,if_false,if_true]
  · rfl
  · exact assoc g x s T E _ _ _ p

theorem gate_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (m : Nat) (hm : 1≤m) (p : Nat) :
    evV g x s T E (.andP (sourceLeaf [⟨true,.andP (power (m-1))⟩] 0)) p=
      evV g x s T E (.andP (power m)) p := by
  have he : power m=.seq (.param 0) (power (m-1)) := by
    have hh : m=(m-1)+1 := by omega
    exact congrArg (expression (.param 0)) hh
  rw [he,CallLookahead.evV_peek,CallLookahead.evV_peek]
  change CallLookahead.peek p (follow (evV g x s T E (.param 0) p)
    (fun q => evV g x s T E (.andP (power (m-1))) q))=
    CallLookahead.peek p (follow (evV g x s T E (.param 0) p) (fun q => evV g x s T E (power (m-1)) q))
  cases ha : evV g x s T E (.param 0) p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q =>
      simp only [follow,CallLookahead.evV_peek]
      cases evV g x s T E (power (m-1)) q with
      | none => rfl
      | some r => cases r <;> rfl

end Shallot.MacroPeg.CBV.OriginHeadParts
