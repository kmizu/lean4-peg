import MacroPeg.CBV.DynamicScannerCompiler
import MacroPeg.CBV.RecursiveScannerArguments

namespace Shallot.MacroPeg.CBV.RecursiveScannerCompiler
open ClockFreezing (Table)
open RegularCaptureProduct (Node)
open RecursiveScannerHelpers (base)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
abbrev Arg := DependentCaptureFilter.Expr

abbrev Expr := DynamicScannerCompiler.Expr

def offset {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) : Nat :=
  base M nodes+n


def nodeCheck (size : Nat) : Node → Bool
  | .lit _ => true
  | .seq a b | .alt a b => decide (a<size) && decide (b<size)
  | .notP a | .star a => decide (a<size)
def nodesCheck (nodes : List Node) : Bool := nodes.all (nodeCheck nodes.length)

theorem nodesCheck_sound (nodes : List Node) (h : nodesCheck nodes=true) : RegularCaptureProduct.Valid nodes := by
  intro v hv
  have hc := (List.all_eq_true.mp h) v hv
  cases v with
  | lit w => trivial
  | seq a b | alt a b =>
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2⟩
  | notP a | star a => exact of_decide_eq_true hc

def argCheck (nodes : List Node) : Arg → Bool
  | .helper i => decide (i<nodes.length)
  | .seq a b | .alt a b => argCheck nodes a && argCheck nodes b
  | .notP a | .star a => argCheck nodes a
  | .lit _ | .param _ => true

theorem argCheck_sound (nodes : List Node) : ∀ a, argCheck nodes a=true → DependentCaptureFilter.Valid nodes a
  | .helper i, h => by
    change i<nodes.length
    exact of_decide_eq_true (show decide (i<nodes.length)=true from h)
  | .lit _, _ | .param _, _ => True.intro
  | .seq a b, h | .alt a b, h =>
    ⟨argCheck_sound nodes a (Bool.and_eq_true_iff.mp h).1,argCheck_sound nodes b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a, h | .star a, h => argCheck_sound nodes a h


def Valid {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) : Expr → Prop
  | .user i a => i<bodies.length ∧ DependentCaptureFilter.Valid nodes a ∧
      RecursiveCaptureSafety.check M nodes.length (DependentCaptureFilter.render a)=true
  | .seq a b | .alt a b => Valid M nodes bodies a ∧ Valid M nodes bodies b
  | .notP a | .star a => Valid M nodes bodies a
  | _ => True

def check {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) : Expr → Bool
  | .user i a => decide (i<bodies.length) && (argCheck nodes a &&
      RecursiveCaptureSafety.check M nodes.length (DependentCaptureFilter.render a))
  | .seq a b | .alt a b => check M nodes bodies a && check M nodes bodies b
  | .notP a | .star a => check M nodes bodies a
  | _ => true

theorem check_sound {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) :
    ∀ e, check M nodes bodies e=true → Valid M nodes bodies e
  | .user _i a, h =>
    ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      argCheck_sound nodes a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1,
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2⟩
  | .seq a b, h | .alt a b, h =>
    ⟨check_sound M nodes bodies a (Bool.and_eq_true_iff.mp h).1,check_sound M nodes bodies b (Bool.and_eq_true_iff.mp h).2⟩
  | .notP a, h | .star a, h => check_sound M nodes bodies a h
  | .eps, _ | .lit _, _ | .param _, _ | .any, _ | .chr _, _ | .range _ _, _ => True.intro

theorem bodies_check_sound {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr)
    (h : bodies.all (check M nodes bodies)=true) : ∀ b∈bodies, Valid M nodes bodies b := by
  intro b hb
  exact check_sound M nodes bodies b ((List.all_eq_true.mp h) b hb)

def keys {n : Nat} (M : StatefulScanner.Machine n) (_nodes : List Node) (bodies : List Expr) : List (Nat × List Nat) :=
  (List.range bodies.length).flatMap (fun i => (profiles (observer M)).map (fun P => (i,P)))
def address {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) (i : Nat) (P : List Nat) : Nat :=
  offset M nodes+(keys M nodes bodies).idxOf (i,P)

def sourceExpr {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) : Expr → MExp
  | .eps => .eps | .lit w => .lit w | .param i => .param i
  | .any => .any | .chr c => .chr c | .range a b => .range a b
  | .user i a => .call (offset M nodes+i) [DependentCaptureFilter.render a]
  | .seq a b => .seq (sourceExpr M nodes bodies a) (sourceExpr M nodes bodies b)
  | .alt a b => .alt (sourceExpr M nodes bodies a) (sourceExpr M nodes bodies b)
  | .notP a => .notP (sourceExpr M nodes bodies a)
  | .star a => .star (sourceExpr M nodes bodies a)

def targetExpr {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr)
    (S : List (List Nat)) : Expr → MExp
  | .eps => .eps | .lit w => .lit w | .param i => .param i
  | .any => .any | .chr c => .chr c | .range a b => .range a b
  | .user i a => ProfileControl.select (observer M) (DependentCaptureFilter.render a)
      (fun q r => DependentCaptureFilter.filter nodes (observer M) S a q r)
      (fun P => .call (address M nodes bodies i P) [DependentCaptureFilter.render a])
  | .seq a b => .seq (targetExpr M nodes bodies S a) (targetExpr M nodes bodies S b)
  | .alt a b => .alt (targetExpr M nodes bodies S a) (targetExpr M nodes bodies S b)
  | .notP a => .notP (targetExpr M nodes bodies S a)
  | .star a => .star (targetExpr M nodes bodies S a)

def source {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr) : MGrammar :=
  ⟨RecursiveScannerHelpers.rules M nodes ++
    bodies.map (fun b => ⟨1,.seq (.call (base M nodes+q.val) []) (sourceExpr M nodes bodies b)⟩)⟩
def targetBody {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr)
    (i : Nat) (P : List Nat) : MExp :=
  match bodies[i]? with
  | none => MExp.failAlways
  | some b => .seq (DynamicScannerBinding.scanner (base M nodes) (DynamicScannerBinding.resume P q))
      (targetExpr M nodes bodies [P] b)
def target {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr) : MGrammar :=
  ⟨RecursiveScannerHelpers.rules M nodes ++
    (keys M nodes bodies).map (fun (i,P) => ⟨1,targetBody M nodes q bodies i P⟩)⟩

theorem sourceExpr_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr) :
    ∀ e, (sourceExpr M nodes bodies e).FirstOrder
  | .eps | .lit _ | .param _ | .any | .chr _ | .range _ _ => True.intro
  | .user _ a => ⟨DependentCaptureFilter.render_firstOrder a,True.intro⟩
  | .seq a b | .alt a b => ⟨sourceExpr_firstOrder M nodes bodies a,sourceExpr_firstOrder M nodes bodies b⟩
  | .notP a | .star a => sourceExpr_firstOrder M nodes bodies a
theorem targetExpr_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr)
    (S : List (List Nat)) : ∀ e, (targetExpr M nodes bodies S e).FirstOrder
  | .eps | .lit _ | .param _ | .any | .chr _ | .range _ _ => True.intro
  | .user _ a => ProfileControl.select_firstOrder _ _ _ (DependentCaptureFilter.render_firstOrder a)
      (fun q r => DependentCaptureFilter.filter_firstOrder nodes (observer M) S a q r) _
      (fun _ _ => ⟨DependentCaptureFilter.render_firstOrder a,True.intro⟩)
  | .seq a b | .alt a b => ⟨targetExpr_firstOrder M nodes bodies S a,targetExpr_firstOrder M nodes bodies S b⟩
  | .notP a | .star a => targetExpr_firstOrder M nodes bodies S a

theorem source_rule {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr)
    (i : Nat) (b : Expr) (hb : bodies[i]?=some b) :
    ruleAtM (source M nodes q bodies).rules (offset M nodes+i)=some ⟨1,.seq (.call (base M nodes+q.val) []) (sourceExpr M nodes bodies b)⟩ := by
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp [RecursiveScannerHelpers.rules,StatefulScanner.block_length,offset,base]),
    show (RecursiveScannerHelpers.rules M nodes).length=offset M nodes from by simp [RecursiveScannerHelpers.rules,StatefulScanner.block_length,offset,base]]
  simp only [Nat.add_sub_cancel_left,List.getElem?_map,hb,Option.map_some]

theorem key_mem {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (bodies : List Expr)
    (i : Nat) (hi : i<bodies.length) (P : List Nat) (hP : P∈profiles (observer M)) :
    (i,P)∈keys M nodes bodies :=
  List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨P,hP,rfl⟩⟩

theorem target_rule {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr)
    (i : Nat) (b : Expr) (hb : bodies[i]?=some b) (P : List Nat) (hP : P∈profiles (observer M)) :
    ruleAtM (target M nodes q bodies).rules (address M nodes bodies i P)=
      some ⟨1,.seq (DynamicScannerBinding.scanner (base M nodes) (DynamicScannerBinding.resume P q))
        (targetExpr M nodes bodies [P] b)⟩ := by
  have hk := DependentProfileCall.index_correct (i,P) (keys M nodes bodies)
    (key_mem M nodes bodies i (List.getElem?_eq_some_iff.mp hb).1 P hP)
  simp only [target,address,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp [RecursiveScannerHelpers.rules,StatefulScanner.block_length,offset,base]),
    show (RecursiveScannerHelpers.rules M nodes).length=offset M nodes from by simp [RecursiveScannerHelpers.rules,StatefulScanner.block_length,offset,base]]
  simp only [Nat.add_sub_cancel_left,List.getElem?_map,hk,Option.map_some,targetBody,hb]

theorem source_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr) :
    (source M nodes q bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact RegularCaptureProduct.grammar_firstOrder nodes (observer M) r hr
    · exact StatefulScanner.block_firstOrder M (fun _ => true) (base M nodes) r hr
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,sourceExpr_firstOrder M nodes bodies b⟩
theorem target_firstOrder {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) (q : Fin n) (bodies : List Expr) :
    (target M nodes q bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact RegularCaptureProduct.grammar_firstOrder nodes (observer M) r hr
    · exact StatefulScanner.block_firstOrder M (fun _ => true) (base M nodes) r hr
  · obtain ⟨⟨i,P⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only [targetBody]
    cases bodies[i]? with
    | none => trivial
    | some b =>
      refine ⟨?_,targetExpr_firstOrder M nodes bodies [P] b⟩
      unfold DynamicScannerBinding.scanner
      split <;> trivial

abbrev helperBodies {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) :=
  RecursiveScannerHelpers.bodies M nodes
abbrev helpers {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node) :=
  RecursiveParserStability.pick (helperBodies M nodes)
abbrev frozen {n : Nat} (g : MGrammar) (M : StatefulScanner.Machine n) (nodes : List Node)
    (x : List Char) (s : Strategy) (k : Nat) : Table :=
  RecursiveParserStability.frozen (helperBodies M nodes) g x s k

theorem helpers_stable {n : Nat} (M : StatefulScanner.Machine n) (nodes : List Node)
    (hNodes : RegularCaptureProduct.Valid nodes) (extra : List MRule) (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows (RecursiveScannerHelpers.grammar M nodes extra) x s (helpers M nodes)
      (RecursiveParserStability.floor (helperBodies M nodes) x) :=
  RecursiveParserStability.helpers_stable (RecursiveScannerHelpers.valid M nodes hNodes)
    (RecursiveScannerHelpers.installed M nodes extra) x s

end Shallot.MacroPeg.CBV.RecursiveScannerCompiler
