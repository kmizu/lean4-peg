import MacroPeg.CBV.DynamicScannerBinding
import MacroPeg.CBV.TotalCaptureSafety
import MacroPeg.CBV.IndependentCaptureControl
import MacroPeg.CBV.ProfileControl

namespace Shallot.MacroPeg.CBV.DynamicScannerCompiler
open ClockFreezing (Table)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
abbrev Arg := DependentCaptureFilter.Expr

inductive Expr where
  | eps
  | lit (w : List Char)
  | param (i : Nat)
  | any
  | chr (c : Char)
  | range (a b : Char)
  | user (i : Nat) (arg : Arg)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | notP (a : Expr)
  | star (a : Expr)

def Valid {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) : Expr → Prop
  | .user i a => i<bodies.length ∧ IndependentCaptureControl.NoHelpers a ∧
      TotalCaptureSafety.Safe M (DependentCaptureFilter.render a)
  | .seq a b | .alt a b => Valid M bodies a ∧ Valid M bodies b
  | .notP a | .star a => Valid M bodies a
  | _ => True

def check {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) : Expr → Bool
  | .user i a => decide (i<bodies.length) && (IndependentCaptureControl.check a &&
      TotalCaptureSafety.check M (DependentCaptureFilter.render a))
  | .seq a b | .alt a b => check M bodies a && check M bodies b
  | .notP a | .star a => check M bodies a
  | _ => true

theorem check_sound {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) :
    ∀ e, check M bodies e=true → Valid M bodies e
  | .user _i a, h =>
    ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      IndependentCaptureControl.check_sound a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1,
      TotalCaptureSafety.check_sound M _ (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2⟩
  | .seq a b, h | .alt a b, h =>
    ⟨check_sound M bodies a (Bool.and_eq_true_iff.mp h).1,check_sound M bodies b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a, h | .star a, h => check_sound M bodies a h
  | .eps, _ | .lit _, _ | .param _, _ | .any, _ | .chr _, _ | .range _ _, _ => True.intro

theorem bodies_check_sound {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr)
    (h : bodies.all (check M bodies)=true) : ∀ b∈bodies, Valid M bodies b := by
  intro b hb
  exact check_sound M bodies b ((List.all_eq_true.mp h) b hb)

def keys {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) : List (Nat × List Nat) :=
  (List.range bodies.length).flatMap (fun i => (profiles (observer M)).map (fun P => (i,P)))
def address {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) (i : Nat) (P : List Nat) : Nat :=
  n+(keys M bodies).idxOf (i,P)

def sourceExpr {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) : Expr → MExp
  | .eps => .eps | .lit w => .lit w | .param i => .param i
  | .any => .any | .chr c => .chr c | .range a b => .range a b
  | .user i a => .call (n+i) [DependentCaptureFilter.render a]
  | .seq a b => .seq (sourceExpr M bodies a) (sourceExpr M bodies b)
  | .alt a b => .alt (sourceExpr M bodies a) (sourceExpr M bodies b)
  | .notP a => .notP (sourceExpr M bodies a)
  | .star a => .star (sourceExpr M bodies a)

def targetExpr {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr)
    (S : List (List Nat)) : Expr → MExp
  | .eps => .eps | .lit w => .lit w | .param i => .param i
  | .any => .any | .chr c => .chr c | .range a b => .range a b
  | .user i a => ProfileControl.select (observer M) (DependentCaptureFilter.render a)
      (fun q r => DependentCaptureFilter.filter [] (observer M) S a q r)
      (fun P => .call (address M bodies i P) [DependentCaptureFilter.render a])
  | .seq a b => .seq (targetExpr M bodies S a) (targetExpr M bodies S b)
  | .alt a b => .alt (targetExpr M bodies S a) (targetExpr M bodies S b)
  | .notP a => .notP (targetExpr M bodies S a)
  | .star a => .star (targetExpr M bodies S a)

def source {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr) : MGrammar :=
  ⟨StatefulScanner.block M (fun _ => true) 0 ++
    bodies.map (fun b => ⟨1,.seq (.call q.val []) (sourceExpr M bodies b)⟩)⟩
def targetBody {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr)
    (i : Nat) (P : List Nat) : MExp :=
  match bodies[i]? with
  | none => MExp.failAlways
  | some b => .seq (DynamicScannerBinding.scanner 0 (DynamicScannerBinding.resume P q))
      (targetExpr M bodies [P] b)
def target {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr) : MGrammar :=
  ⟨StatefulScanner.block M (fun _ => true) 0 ++
    (keys M bodies).map (fun (i,P) => ⟨1,targetBody M q bodies i P⟩)⟩

theorem sourceExpr_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr) :
    ∀ e, (sourceExpr M bodies e).FirstOrder
  | .eps | .lit _ | .param _ | .any | .chr _ | .range _ _ => True.intro
  | .user _ a => ⟨DependentCaptureFilter.render_firstOrder a,True.intro⟩
  | .seq a b | .alt a b => ⟨sourceExpr_firstOrder M bodies a,sourceExpr_firstOrder M bodies b⟩
  | .notP a | .star a => sourceExpr_firstOrder M bodies a
theorem targetExpr_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr)
    (S : List (List Nat)) : ∀ e, (targetExpr M bodies S e).FirstOrder
  | .eps | .lit _ | .param _ | .any | .chr _ | .range _ _ => True.intro
  | .user _ a => ProfileControl.select_firstOrder _ _ _ (DependentCaptureFilter.render_firstOrder a)
      (fun q r => DependentCaptureFilter.filter_firstOrder [] (observer M) S a q r) _
      (fun _ _ => ⟨DependentCaptureFilter.render_firstOrder a,True.intro⟩)
  | .seq a b | .alt a b => ⟨targetExpr_firstOrder M bodies S a,targetExpr_firstOrder M bodies S b⟩
  | .notP a | .star a => targetExpr_firstOrder M bodies S a

theorem source_rule {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr)
    (i : Nat) (b : Expr) (hb : bodies[i]?=some b) :
    ruleAtM (source M q bodies).rules (n+i)=some ⟨1,.seq (.call q.val []) (sourceExpr M bodies b)⟩ := by
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp [StatefulScanner.block_length]),StatefulScanner.block_length]
  simp only [Nat.add_sub_cancel_left,List.getElem?_map,hb,Option.map_some]

theorem key_mem {n : Nat} (M : StatefulScanner.Machine n) (bodies : List Expr)
    (i : Nat) (hi : i<bodies.length) (P : List Nat) (hP : P∈profiles (observer M)) :
    (i,P)∈keys M bodies :=
  List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨P,hP,rfl⟩⟩

theorem target_rule {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr)
    (i : Nat) (b : Expr) (hb : bodies[i]?=some b) (P : List Nat) (hP : P∈profiles (observer M)) :
    ruleAtM (target M q bodies).rules (address M bodies i P)=
      some ⟨1,.seq (DynamicScannerBinding.scanner 0 (DynamicScannerBinding.resume P q))
        (targetExpr M bodies [P] b)⟩ := by
  have hk := DependentProfileCall.index_correct (i,P) (keys M bodies)
    (key_mem M bodies i (List.getElem?_eq_some_iff.mp hb).1 P hP)
  simp only [target,address,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp [StatefulScanner.block_length]),StatefulScanner.block_length]
  simp only [Nat.add_sub_cancel_left,List.getElem?_map,hk,Option.map_some,targetBody,hb]

theorem source_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr) :
    (source M q bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact StatefulScanner.block_firstOrder M (fun _ => true) 0 r hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,sourceExpr_firstOrder M bodies b⟩
theorem target_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (q : Fin n) (bodies : List Expr) :
    (target M q bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact StatefulScanner.block_firstOrder M (fun _ => true) 0 r hr
  · obtain ⟨⟨i,P⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only [targetBody]
    cases bodies[i]? with
    | none => trivial
    | some b =>
      refine ⟨?_,targetExpr_firstOrder M bodies [P] b⟩
      unfold DynamicScannerBinding.scanner
      split <;> trivial

def helpers (n i : Nat) : Bool := decide (i<n)
abbrev frozen (g : MGrammar) (n : Nat) (x : List Char) (s : Strategy) (k : Nat) : Table :=
  ClockFreezing.frozen g x s (helpers n) (x.length+1) k

theorem helper_rule {n : Nat} (M : StatefulScanner.Machine n) (extra : List MRule) (r : Fin n) :
    ruleAtM (StatefulScanner.block M (fun _ => true) 0 ++ extra) r.val=
      some ⟨0,StatefulScanner.branches 0 (StatefulScanner.terminal true) (M.arcs r)⟩ := by
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left (by simpa only [StatefulScanner.block_length] using r.isLt)]
  simpa only [ruleAtM_eq_getElem?] using StatefulScanner.block_rule M (fun _ => true) 0 r

theorem helpers_stable {n : Nat} (M : StatefulScanner.Machine n) (extra : List MRule)
    (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ x s (helpers n) (x.length+1) := by
  intro k i hi E
  have hb : i<n := by simpa only [helpers,decide_eq_true_eq] using hi
  simpa only [Nat.zero_add] using StatefulScannerStability.rows_stable M (fun _ => true)
    ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ 0
    (fun r => by simpa only [Nat.zero_add] using helper_rule M extra r)
    x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) ⟨i,hb⟩ E

theorem scanner_eval {n : Nat} (M : StatefulScanner.Machine n) (extra : List MRule)
    (r : Fin n) (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    let g : MGrammar := ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩
    evV g x s (frozen g n x s k) E (.call r.val []) p=
      some (some (StatefulScanner.run M r (sfx x p)).2.length) := by
  dsimp only []
  have hr := helper_rule M extra r
  have hc : evV ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ x s
      (frozen ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ n x s k) E (.call r.val []) p=
      valAt (frozen ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ n x s k r.val []) p := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  rw [hc]
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ k _ (by simp [helpers,r.isLt]) []]
  simpa only [Nat.zero_add,if_true] using StatefulScanner.query_eval M (fun _ => true)
    ⟨StatefulScanner.block M (fun _ => true) 0 ++ extra⟩ 0
    (fun r => by simpa only [Nat.zero_add] using helper_rule M extra r)
    x s p hp (x.length+1) (by omega) r

end Shallot.MacroPeg.CBV.DynamicScannerCompiler
