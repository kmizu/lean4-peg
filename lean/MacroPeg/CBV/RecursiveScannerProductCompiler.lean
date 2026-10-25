import MacroPeg.CBV.ScannerLanguageSafety
import MacroPeg.CBV.SelectedCaptureSafety
import MacroPeg.CBV.SequentialRecursiveScanner
import MacroPeg.CBV.RecursiveScannerHelpers

namespace Shallot.MacroPeg.CBV.RecursiveScannerProductCompiler
open StatefulScanner (Machine)
open DynamicScannerCapture (observer)
open CaptureTransitionProfile (profile profiles)
open SequentialRecursiveScanner (state)
open StatefulScannerProduct (right)
abbrev Arg := SequentialRecursiveObserver.Expr
/-- Each user either scans from its own state or replays its retained value. -/
abbrev Entries (n : Nat) := Nat → Option (Fin n)

def sourceHeader {n : Nat} : Option (Fin n) → MExp
  | none => .param 0
  | some q => .call q.val []

abbrev Mode := Option (Nat × Nat)
abbrev valid {n : Nat} (M : Machine n) := DynamicScannerCapture.observer_valid M

def helpers {n : Nat} (M : Machine n) : List MRule :=
  StatefulScanner.block M (fun _ => true) 0 ++
    ObservedScannerDispatch.rules M (observer M) (valid M) n

def helperBodies {n : Nat} (M : Machine n) := (helpers M).map MRule.body

def offset {n : Nat} (M : Machine n) : Nat := (helpers M).length

def modes {n : Nat} (M : Machine n) : List Mode :=
  none::(List.range (observer M).width).flatMap (fun q =>
    (List.range (observer M).width).map (fun r => some (q,r)))

def keys {n : Nat} (M : Machine n) (bodies : List Arg) : List (Nat × List Nat × Mode) :=
  (List.range bodies.length).flatMap (fun i => (profiles (observer M)).flatMap (fun P =>
    (modes M).map (fun mode => (i,P,mode))))

def address {n : Nat} (M : Machine n) (bodies : List Arg) (i : Nat) (P : List Nat) (mode : Mode) :=
  offset M+(keys M bodies).idxOf (i,P,mode)

def sourceExpr {n : Nat} (M : Machine n) : Arg → MExp
  | .lit w => .lit w
  | .param k => .param k
  | .user i a => .call (offset M+i) [sourceExpr M a]
  | .seq a b => .seq (sourceExpr M a) (sourceExpr M b)
  | .alt a b => .alt (sourceExpr M a) (sourceExpr M b)
  | .notP a => .notP (sourceExpr M a)
  | .star a => .star (sourceExpr M a)

mutual
  def plain {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) : Arg → MExp
    | .lit w => .lit w
    | .param k => .param k
    | .user i a => ProfileControl.select (observer M) (plain M bodies S a)
        (fun q r => filter M bodies S a q r)
        (fun P => .call (address M bodies i P none) [plain M bodies S a])
    | .seq a b => .seq (plain M bodies S a) (plain M bodies S b)
    | .alt a b => .alt (plain M bodies S a) (plain M bodies S b)
    | .notP a => .notP (plain M bodies S a)
    | .star a => .star (plain M bodies S a)

  def filter {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) : Arg → Nat → Nat → MExp
    | .lit w, q, r => .seq (.lit w) (if some (RegularCaptureProduct.run (observer M) q w)=some r then .eps else MExp.failAlways)
    | .param k, q, r => .seq (.param k) (if DependentCaptureFilter.nextState S k q=some r then .eps else MExp.failAlways)
    | .user i a, q, r => ProfileControl.select (observer M) (plain M bodies S a)
        (fun q r => filter M bodies S a q r)
        (fun P => .call (address M bodies i P (some (q,r))) [plain M bodies S a])
    | .seq a b, q, r => RegularCaptureProduct.choice ((List.range (observer M).width).map (fun t =>
        .seq (filter M bodies S a q t) (filter M bodies S b t r)))
    | .alt a b, q, r => RootObservation.branch (.andP (plain M bodies S a))
        (filter M bodies S a q r) (filter M bodies S b q r)
    | .star a, q, r => GeneralStarFilter.filter (observer M).width (plain M bodies S a)
        (fun q r => filter M bodies S a q r) q r
    | .notP a, q, r => .seq (.notP (plain M bodies S a)) (if some q=some r then .eps else MExp.failAlways)
end

def sourceRules {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) : List MRule :=
  bodies.zipIdx.map (fun (b,i) => ⟨1,.seq (sourceHeader (entries i)) (sourceExpr M b)⟩)

def source {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) : MGrammar :=
  ⟨helpers M++sourceRules M entries bodies⟩

/-- A product row describes the source row from its original entry, even
though the generated Seq row begins at the actual argument endpoint. -/
def scannerBody {n : Nat} (M : Machine n) (q : Fin n) (bodies : List Arg)
    (P : List Nat) (mode : Mode) (b : Arg) : MExp :=
  match DynamicScannerBinding.resume P q with
  | none => MExp.failAlways
  | some r => match mode with
    | none => .seq (.call r.val []) (plain M bodies [P] b)
    | some (a,z) => if ha : a<(observer M).width then
        ObservedScannerDispatch.dispatch n r (state M P ⟨a,ha⟩)
          (fun t => filter M bodies [P] b (right (valid M).1 t).val z)
      else MExp.failAlways

/-- A replay row removes exactly the captured prefix; a scanner row
resumes from the state determined by that same complete capture. -/
def targetBody {n : Nat} (M : Machine n) (entry : Option (Fin n)) (bodies : List Arg)
    (P : List Nat) (mode : Mode) (b : Arg) : MExp :=
  match entry with
  | some q => scannerBody M q bodies P mode b
  | none => match mode with
    | none => plain M bodies [P] b
    | some (a,z) => if ha : a<(observer M).width then
        filter M bodies [P] b (state M P ⟨a,ha⟩).val z
      else MExp.failAlways

def targetRules {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) : List MRule :=
  (keys M bodies).map (fun (i,P,mode) => ⟨1,match bodies[i]? with
    | none => MExp.failAlways | some b => targetBody M (entries i) bodies P mode b⟩)

def target {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) : MGrammar :=
  ⟨helpers M++targetRules M entries bodies⟩

/-- Closed helper rows are certified only when their consumed words are
safe from every scanner state. Otherwise they remain available to ordinary
users and queries but are excluded from consuming argument paths. -/
def helperSafe {n : Nat} (M : Machine n) : Bool :=
  (helpers M).all (fun r => ParameterizedCaptureSafety.check M (offset M) r.body)

/-- Only plain scanner states with a checked language-inclusion certificate
are primitive safe rows. Product helpers keep their original checks. -/
def primitive {n : Nat} (M : Machine n) (i : Nat) : Bool :=
  if hi : i<n then ScannerLanguageSafety.safe M ⟨i,hi⟩ else false

def selected {n : Nat} (M : Machine n) (safeUsers : Nat) (i : Nat) : Bool :=
  if i<offset M then helperSafe M || primitive M i else decide (i<offset M+safeUsers)

def argumentCheck {n : Nat} (M : Machine n) (safeUsers : Nat) : Arg → Bool :=
  fun a => SelectedCaptureSafety.check M (selected M safeUsers) (sourceExpr M a)

/-- Only positive calls on a consuming argument path require a certified
source component. Calls inside queries retain their ordinary semantics. -/
def check {n : Nat} (M : Machine n) (bodies : List Arg) (safeUsers : Nat) : Arg → Bool
  | .user i a => decide (i<bodies.length) && (argumentCheck M safeUsers a && check M bodies safeUsers a)
  | .seq a b | .alt a b => check M bodies safeUsers a && check M bodies safeUsers b
  | .star a | .notP a => check M bodies safeUsers a
  | _ => true

def sourceSafe {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (safeUsers : Nat) : Bool :=
  decide (safeUsers≤bodies.length) &&
    SelectedCaptureSafety.certifiedCheck M (source M entries bodies) (selected M safeUsers) (primitive M)

def Valid {n : Nat} (M : Machine n) (bodies : List Arg) (safeUsers : Nat) : Arg → Prop
  | .user i a => i<bodies.length ∧ argumentCheck M safeUsers a=true ∧ Valid M bodies safeUsers a
  | .seq a b | .alt a b => Valid M bodies safeUsers a ∧ Valid M bodies safeUsers b
  | .star a | .notP a => Valid M bodies safeUsers a
  | _ => True

theorem check_sound {n : Nat} (M : Machine n) (bodies : List Arg) (safeUsers : Nat) :
    ∀ e, check M bodies safeUsers e=true → Valid M bodies safeUsers e
  | .user _ a, h => ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp h).1,
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1,
      check_sound M bodies safeUsers a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2⟩
  | .seq a b, h | .alt a b, h =>
      ⟨check_sound M bodies safeUsers a (Bool.and_eq_true_iff.mp h).1,check_sound M bodies safeUsers b (Bool.and_eq_true_iff.mp h).2⟩
  | .star a, h | .notP a, h => check_sound M bodies safeUsers a h
  | .lit _, _ | .param _, _ => True.intro

abbrev sourceTable {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (x : List Char) (k : Nat) :=
  RecursiveParserStability.frozen (helperBodies M) (source M entries bodies) x .callByValuePar k
abbrev targetTable {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (x : List Char) (k : Nat) :=
  RecursiveParserStability.frozen (helperBodies M) (target M entries bodies) x .callByValueSeq k

theorem helpers_length {n : Nat} (M : Machine n) : offset M=n+(n*(observer M).width)*(n*(observer M).width) := by
  simp [offset,helpers,StatefulScanner.block_length,ObservedScannerDispatch.length]

theorem sourceExpr_firstOrder {n : Nat} (M : Machine n) : ∀ e, (sourceExpr M e).FirstOrder
  | .lit _ | .param _ => True.intro
  | .user _ a => ⟨sourceExpr_firstOrder M a,True.intro⟩
  | .seq a b | .alt a b => ⟨sourceExpr_firstOrder M a,sourceExpr_firstOrder M b⟩
  | .star a | .notP a => sourceExpr_firstOrder M a

mutual
  theorem plain_firstOrder {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) :
      ∀ e, (plain M bodies S e).FirstOrder
    | .lit _ | .param _ => True.intro
    | .user i a => ProfileControl.select_firstOrder _ _ _ (plain_firstOrder M bodies S a)
        (fun q r => filter_firstOrder M bodies S a q r) _
        (fun _ _ => ⟨plain_firstOrder M bodies S a,True.intro⟩)
    | .seq a b | .alt a b => ⟨plain_firstOrder M bodies S a,plain_firstOrder M bodies S b⟩
    | .star a | .notP a => plain_firstOrder M bodies S a
  theorem filter_firstOrder {n : Nat} (M : Machine n) (bodies : List Arg) (S : List (List Nat)) :
      ∀ e q r, (filter M bodies S e q r).FirstOrder
    | .lit _, _, _ | .param _, _, _ => by simp only [filter]; split <;> trivial
    | .user i a, q, r => ProfileControl.select_firstOrder _ _ _ (plain_firstOrder M bodies S a)
        (fun q r => filter_firstOrder M bodies S a q r) _
        (fun _ _ => ⟨plain_firstOrder M bodies S a,True.intro⟩)
    | .seq a b, q, r => by
      apply RegularCaptureProduct.choice_firstOrder
      intro e he
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
      exact ⟨filter_firstOrder M bodies S a q t,filter_firstOrder M bodies S b t r⟩
    | .alt a b, q, r => ⟨⟨plain_firstOrder M bodies S a,filter_firstOrder M bodies S a q r⟩,
        plain_firstOrder M bodies S a,filter_firstOrder M bodies S b q r⟩
    | .star a, q, r => GeneralStarFilter.filter_firstOrder _ _ (plain_firstOrder M bodies S a) _
        (fun q r => filter_firstOrder M bodies S a q r) q r
    | .notP a, q, r => by simp only [filter]; split <;> exact ⟨plain_firstOrder M bodies S a,True.intro⟩
end

theorem scannerBody_firstOrder {n : Nat} (M : Machine n) (q : Fin n) (bodies : List Arg)
    (P : List Nat) (mode : Mode) (b : Arg) : (scannerBody M q bodies P mode b).FirstOrder := by
  unfold scannerBody
  cases DynamicScannerBinding.resume P q with
  | none => trivial
  | some r => cases mode with
    | none => exact ⟨True.intro,plain_firstOrder M bodies [P] b⟩
    | some pair =>
      obtain ⟨a,z⟩ := pair
      dsimp only []
      split
      · exact ObservedScannerDispatch.dispatch_firstOrder _ _ _ _ (fun t => filter_firstOrder M bodies [P] b _ _)
      · trivial

theorem sourceHeader_firstOrder {n : Nat} (entry : Option (Fin n)) :
    (sourceHeader entry).FirstOrder := by cases entry <;> trivial

theorem targetBody_firstOrder {n : Nat} (M : Machine n) (entry : Option (Fin n)) (bodies : List Arg)
    (P : List Nat) (mode : Mode) (b : Arg) : (targetBody M entry bodies P mode b).FirstOrder := by
  cases entry with
  | some q => exact scannerBody_firstOrder M q bodies P mode b
  | none =>
    cases mode with
    | none => exact plain_firstOrder M bodies [P] b
    | some pair =>
      obtain ⟨a,z⟩ := pair
      simp only [targetBody]
      split
      · exact filter_firstOrder M bodies [P] b _ _
      · trivial

theorem helpers_firstOrder {n : Nat} (M : Machine n) : ∀ r∈helpers M, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact StatefulScanner.block_firstOrder M (fun _ => true) 0 r hr
  · exact ObservedScannerDispatch.firstOrder M (observer M) (valid M) n r hr

theorem source_firstOrder {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) :
    (source M entries bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact helpers_firstOrder M r hr
  · obtain ⟨⟨b,i⟩,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨sourceHeader_firstOrder (entries i),sourceExpr_firstOrder M b⟩

theorem target_firstOrder {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) :
    (target M entries bodies).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact helpers_firstOrder M r hr
  · obtain ⟨⟨i,P,mode⟩,_,rfl⟩ := List.mem_map.mp hr
    dsimp only []
    cases bodies[i]? with
    | none => trivial
    | some b => exact targetBody_firstOrder M (entries i) bodies P mode b

theorem mode_plain_mem {n : Nat} (M : Machine n) : none∈modes M := by simp [modes]
theorem mode_filter_mem {n : Nat} (M : Machine n) (q r : Nat)
    (hq : q<(observer M).width) (hr : r<(observer M).width) : some (q,r)∈modes M := by
  simp only [modes,List.mem_cons,List.mem_flatMap,List.mem_map,List.mem_range]
  exact Or.inr ⟨q,hq,r,hr,rfl⟩

theorem key_mem {n : Nat} (M : Machine n) (bodies : List Arg) (i : Nat) (hi : i<bodies.length)
    (P : List Nat) (hP : P∈profiles (observer M)) (mode : Mode) (hm : mode∈modes M) : (i,P,mode)∈keys M bodies :=
  List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_flatMap.mpr ⟨P,hP,List.mem_map.mpr ⟨mode,hm,rfl⟩⟩⟩

theorem source_rule {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (i : Nat) (b : Arg)
    (hi : bodies[i]?=some b) : ruleAtM (source M entries bodies).rules (offset M+i)=some ⟨1,.seq (sourceHeader (entries i)) (sourceExpr M b)⟩ := by
  simp only [source,offset,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,sourceRules,List.getElem?_map,List.getElem?_zipIdx,hi,Option.map_some,Nat.zero_add]

theorem target_rule {n : Nat} (M : Machine n) (entries : Entries n) (bodies : List Arg) (i : Nat) (b : Arg)
    (hi : bodies[i]?=some b) (P : List Nat) (hP : P∈profiles (observer M)) (mode : Mode) (hm : mode∈modes M) :
    ruleAtM (target M entries bodies).rules (address M bodies i P mode)=some ⟨1,targetBody M (entries i) bodies P mode b⟩ := by
  have hk := DependentProfileCall.index_correct (i,P,mode) (keys M bodies)
    (key_mem M bodies i (List.getElem?_eq_some_iff.mp hi).1 P hP mode hm)
  simp only [target,address,offset,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,targetRules,List.getElem?_map,hk,Option.map_some,hi]

end Shallot.MacroPeg.CBV.RecursiveScannerProductCompiler
