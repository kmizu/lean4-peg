import MacroPeg.CBV.StatefulScannerProduct

/-! One actual grammar contains synchronized selectors, both residual
scanners, and an arbitrary suffix of user rules. -/
namespace Shallot.MacroPeg.CBV.StatefulPairArguments
open StatefulScanner StatefulScannerProduct

def commonSize (n m : Nat) : Nat := (n*m)*(n*m)
def leftBase (n m : Nat) : Nat := commonSize n m
def rightBase (n m : Nat) : Nat := commonSize n m+n

def grammar {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule) : MGrammar :=
  ⟨(StatefulScannerFamily.grammar (product A B hm)).rules ++
    (block A (fun _ => true) (leftBase n m) ++
      (block B (fun _ => true) (rightBase n m) ++ tail))⟩

theorem grammar_length {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule) :
    (grammar A B hm tail).rules.length = commonSize n m+n+m+tail.length := by
  simp [grammar,StatefulScannerFamily.grammar_length,block_length,commonSize,Nat.add_assoc]

private theorem append_lookup_left (as bs : List MRule) (i : Nat) (r : MRule)
    (h : ruleAtM as i = some r) : ruleAtM (as++bs) i = some r := by
  rw [ruleAtM_eq_getElem?] at h ⊢
  have hi := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hi]
  exact h

private theorem append_lookup_middle (as bs cs : List MRule) (i : Nat) (r : MRule)
    (h : ruleAtM bs i = some r) : ruleAtM (as++(bs++cs)) (as.length+i) = some r := by
  have hh := append_lookup_left bs cs i r h
  rw [ruleAtM_eq_getElem?] at hh ⊢
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact hh

theorem common_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (q target : Fin (n*m)) :
    ruleAtM (grammar A B hm tail).rules (target.val*(n*m)+q.val) = some
      ⟨0,branches (target.val*(n*m)) (terminal (decide (q=target))) ((product A B hm).arcs q)⟩ :=
  append_lookup_left _ _ _ _ (StatefulScannerFamily.grammar_rule (product A B hm) q target)

theorem left_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (q : Fin n) : ruleAtM (grammar A B hm tail).rules (leftBase n m+q.val) =
      some ⟨0,branches (leftBase n m) (terminal true) (A.arcs q)⟩ := by
  have hh := append_lookup_middle (StatefulScannerFamily.grammar (product A B hm)).rules
    (block A (fun _ => true) (leftBase n m))
    (block B (fun _ => true) (rightBase n m) ++ tail) q.val _ (block_rule A _ _ q)
  simpa only [StatefulScannerFamily.grammar_length,commonSize,leftBase,grammar] using hh

theorem right_rule {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (q : Fin m) : ruleAtM (grammar A B hm tail).rules (rightBase n m+q.val) =
      some ⟨0,branches (rightBase n m) (terminal true) (B.arcs q)⟩ := by
  have hh := append_lookup_middle
    ((StatefulScannerFamily.grammar (product A B hm)).rules ++ block A (fun _ => true) (leftBase n m))
    (block B (fun _ => true) (rightBase n m)) tail q.val _ (block_rule B _ _ q)
  simpa only [List.length_append,StatefulScannerFamily.grammar_length,block_length,
    commonSize,rightBase,grammar,List.append_assoc] using hh

theorem grammar_firstOrder {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m)
    (tail : List MRule) (ht : ∀ r ∈ tail, r.body.FirstOrder) : (grammar A B hm tail).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hc | hr
  · exact StatefulScannerFamily.grammar_firstOrder (product A B hm) r hc
  · rcases List.mem_append.mp hr with ha | hr
    · exact block_firstOrder A _ _ r ha
    · rcases List.mem_append.mp hr with hb | hr
      · exact block_firstOrder B _ _ r hb
      · exact ht r hr

def leftEntry {n m : Nat} (a : Fin n) : MExp := .call (leftBase n m+a.val) []
def rightEntry {n m : Nat} (b : Fin m) : MExp := .call (rightBase n m+b.val) []

def commonEntry {n m : Nat} (a c : Fin n) (b d : Fin m) : MExp :=
  StatefulScannerFamily.entry (pack a b) (pack c d)

theorem left_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a : Fin n) (p clock : Nat)
    (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E (leftEntry (m := m) a) p =
      some (some (run A a (sfx x p)).2.length) := by
  simpa only [leftEntry,if_true] using entry_of_layout A (fun _ => true)
    (grammar A B hm tail) (leftBase n m) (left_rule A B hm tail) x s a E p clock hp hc

theorem right_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (b : Fin m) (p clock : Nat)
    (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E (rightEntry (n := n) b) p =
      some (some (run B b (sfx x p)).2.length) := by
  simpa only [rightEntry,if_true] using entry_of_layout B (fun _ => true)
    (grammar A B hm tail) (rightBase n m) (right_rule A B hm tail) x s b E p clock hp hc

theorem common_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E (commonEntry a c b d) p =
      some (if (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d
        then some (common A B a b (sfx x p)).2.length else none) := by
  have hh := entry_of_layout (product A B hm) (fun q => decide (q=pack c d))
    (grammar A B hm tail) ((pack c d).val*(n*m))
    (fun q => common_rule A B hm tail q (pack c d)) x s (pack a b) E p clock hp hc
  simpa only [commonEntry,StatefulScannerFamily.entry,run_product,pack_eq_iff hm,decide_eq_true_eq] using hh

def firstStops {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m) (x : List Char) : Bool :=
  match (common A B a b x).2 with
  | [] => true
  | c::_ => (next (A.arcs (common A B a b x).1.1) c).isNone

theorem first_remainder {n m : Nat} (A : Machine n) (B : Machine m)
    (a : Fin n) (b : Fin m) (x : List Char) :
    if firstStops A B a b x then (run A a x).2 = (common A B a b x).2
    else (run B b x).2 = (common A B a b x).2 := by
  obtain ⟨ha,hb⟩ := residual_runs A B a b x
  cases hz : (common A B a b x).2 with
  | nil => simp only [firstStops,hz,if_true]; rw [ha,hz]; rfl
  | cons c rest =>
    have hstop := frontier_stops A B a b x c rest hz
    cases ht : next (A.arcs (common A B a b x).1.1) c with
    | none => simp only [firstStops,hz,ht,Option.isNone_none,if_true]; rw [ha,hz,run,ht]
    | some q =>
      have hr : next (B.arcs (common A B a b x).1.2) c = none := by
        rcases hstop with h | h
        · rw [ht] at h; cases h
        · exact h
      simp only [firstStops,hz,ht,Option.isNone_some,Bool.false_eq_true,if_false]
      rw [hb,hz,run,hr]

def commonPos {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (x : List Char) (p : Nat) : Nat := (common A B a b (sfx x p)).2.length

def finalPos {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (first : Bool) (x : List Char) (p : Nat) : Nat :=
  if first then (run B b (sfx x p)).2.length else (run A a (sfx x p)).2.length

def arguments {n m : Nat} (a c : Fin n) (b d : Fin m) (first : Bool) : List MExp :=
  [commonEntry a c b d,if first then rightEntry (n := n) d else leftEntry (m := m) c]

theorem common_bound {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (x : List Char) (p : Nat) (hp : p ≤ x.length) : commonPos A B a b x p ≤ p := by
  obtain ⟨word,hw,_,_⟩ := common_prefix A B a b (sfx x p)
  have hl := congrArg List.length hw
  simp only [List.length_append,length_sfx x hp] at hl
  change (common A B a b (sfx x p)).2.length ≤ p
  omega

/-- Both residual entries execute in the same grammar as the common-state
selector. A correct candidate gives the actual two disjoint Seq captures. -/
theorem arguments_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock)
    (hstate : (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d) :
    evSeqArgs (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock)
      E (arguments a c b d first) p = some (some
        ([pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b first x p)],finalPos A B a b first x p)) := by
  have hcommon : evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
      (commonEntry a c b d) p = some (some (commonPos A B a b x p)) := by
    simpa [hstate,commonPos] using common_eval A B hm tail x s E a c b d p clock hp hc
  have hbound := common_bound A B a b x p hp
  have hcp : commonPos A B a b x p ≤ x.length := Nat.le_trans hbound hp
  have hclock : commonPos A B a b x p+1 ≤ clock := by omega
  have hs : sfx x (commonPos A B a b x p) = (common A B a b (sfx x p)).2 :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p)
      ⟨_,(common_prefix A B a b (sfx x p)).choose_spec.1⟩).choose_spec
  obtain ⟨hA,hB⟩ := residual_runs A B a b (sfx x p)
  rw [hstate.1] at hA
  rw [hstate.2] at hB
  have hres : evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
      (if first then rightEntry (n := n) d else leftEntry (m := m) c) (commonPos A B a b x p) =
      some (some (finalPos A B a b first x p)) := by
    cases first
    · simp only [Bool.false_eq_true,if_false,finalPos]
      rw [left_eval A B hm tail x s E c _ clock hcp hclock,hs,← hA]
    · simp only [if_true,finalPos]
      rw [right_eval A B hm tail x s E d _ clock hcp hclock,hs,← hB]
  rw [arguments,evSeq_cons_ok hcommon,evSeq_cons_ok hres]
  rfl


def enabled {Q : Type} (arcs : List (Char × Q)) : List Char := arcs.map Prod.fst

theorem next_enabled {Q : Type} (arcs : List (Char × Q)) (c : Char) :
    NestedScannerArguments.accepts (enabled arcs) c = (next arcs c).isSome := by
  induction arcs with
  | nil => rfl
  | cons arc arcs ih =>
    obtain ⟨a,q⟩ := arc
    simp only [enabled] at ih
    by_cases ha : Shallot.beqChar a c = true <;>
      simp [enabled,next,NestedScannerArguments.accepts,ha,ih]

def stopped {Q : Type} (arcs : List (Char × Q)) : List Char → Bool
  | [] => true
  | c::_ => (next arcs c).isNone

def stopTest {Q : Type} (arcs : List (Char × Q)) (first : Bool) : MExp :=
  if first then .notP (NestedScannerArguments.choice (enabled arcs))
  else .andP (NestedScannerArguments.choice (enabled arcs))

theorem stopTest_eval {Q : Type} (arcs : List (Char × Q)) (first : Bool)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Nat → List (List Char) → Val)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (stopTest arcs first) p =
      if stopped arcs (sfx x p) = first then some (some p) else some none := by
  cases first with
  | false =>
    change evV g x s T E (.andP (NestedScannerArguments.choice (enabled arcs))) p = _
    rw [CallLookahead.evV_peek,NestedScannerArguments.choice_eval]
    cases hx : sfx x p with
    | nil => rfl
    | cons c rest =>
      dsimp only [stopped]
      rw [next_enabled]
      have hh : ∀ o : Option Q, CallLookahead.peek p
          (if o.isSome then some (some rest.length) else some none) =
          (if o.isNone=false then some (some p) else some none) := by
        intro o
        cases o <;> rfl
      exact hh (next arcs c)
  | true =>
    change (match evV g x s T E (NestedScannerArguments.choice (enabled arcs)) p with
      | some (some _) => some none | some none => some (some p) | none => none) = _
    rw [NestedScannerArguments.choice_eval]
    cases hx : sfx x p with
    | nil => rfl
    | cons c rest =>
      dsimp only [stopped]
      rw [next_enabled]
      have hh : ∀ o : Option Q,
          (match (if o.isSome then some (some rest.length) else some none) with
          | some (some _) => some none | some none => some (some p) | none => none) =
          (if o.isNone=true then some (some p) else some none) := by
        intro o
        cases o <;> rfl
      exact hh (next arcs c)

abbrev GoodCase {n m : Nat} (A : Machine n) (B : Machine m) (a c : Fin n) (b d : Fin m)
    (first : Bool) (x : List Char) : Prop :=
  ((common A B a b x).1.1=c ∧ (common A B a b x).1.2=d) ∧ firstStops A B a b x = first

def caseGuard {n m : Nat} (A : Machine n) (a c : Fin n) (b d : Fin m) (first : Bool) : MExp :=
  .andP (.seq (commonEntry a c b d) (stopTest (A.arcs c) first))

theorem common_suffix {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (x : List Char) (p : Nat) :
    sfx x (commonPos A B a b x p) = (common A B a b (sfx x p)).2 :=
  sfx_suffix (suffix_trans (sfx_is_suffix x p)
    ⟨_,(common_prefix A B a b (sfx x p)).choose_spec.1⟩).choose_spec

/-- The real input test accepts exactly one candidate state pair and stop
order. Successful testing restores the caller's original position. -/
theorem caseGuard_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E (caseGuard A a c b d first) p =
      if GoodCase A B a c b d first (sfx x p) then some (some p) else some none := by
  rw [caseGuard,CallLookahead.evV_peek]
  by_cases hstate : (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d
  · have he : evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
        (commonEntry a c b d) p = some (some (commonPos A B a b x p)) := by
      simpa [hstate,commonPos] using common_eval A B hm tail x s E a c b d p clock hp hc
    rw [evV_seq_ok he,stopTest_eval,common_suffix]
    have hs : stopped (A.arcs c) (common A B a b (sfx x p)).2 = firstStops A B a b (sfx x p) := by
      rw [← hstate.1]
      rfl
    rw [hs]
    by_cases hf : firstStops A B a b (sfx x p) = first <;>
      simp only [GoodCase,hstate,hf,and_self,if_true,if_false,CallLookahead.peek,and_false]
  · have he : evV (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
        (commonEntry a c b d) p = some none := by
      simpa only [if_neg hstate] using common_eval A B hm tail x s E a c b d p clock hp hc
    rw [evV_seq_fail he]
    simp [GoodCase,hstate,CallLookahead.peek]

/-- The original independent argument parsers still execute from the same
caller position in the combined grammar. -/
theorem independent_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evParArgs (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
      [leftEntry (m := m) a,rightEntry (n := n) b] p =
      some (some [pre x p (run A a (sfx x p)).2.length,pre x p (run B b (sfx x p)).2.length]) := by
  rw [evPar_cons_ok (left_eval A B hm tail x s E a p clock hp hc),
    evPar_cons_ok (right_eval A B hm tail x s E b p clock hp hc)]
  rfl

theorem final_bound {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m)
    (first : Bool) (x : List Char) (p : Nat) : finalPos A B a b first x p ≤ commonPos A B a b x p := by
  obtain ⟨hA,hB⟩ := residual_runs A B a b (sfx x p)
  cases first
  · simpa only [finalPos,Bool.false_eq_true,if_false,commonPos,← hA] using
      run_length A (common A B a b (sfx x p)).1.1 (common A B a b (sfx x p)).2
  · simpa only [finalPos,if_true,commonPos,← hB] using
      run_length B (common A B a b (sfx x p)).1.2 (common A B a b (sfx x p)).2

/-- After the runtime guard has selected a control, the actual independent
Par argument values equal the original-order views of the Seq chunks. -/
theorem capture_reconstruction {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock)
    (hgood : GoodCase A B a c b d first (sfx x p)) :
    evParArgs (grammar A B hm tail) x s (tblV (grammar A B hm tail) x s clock) E
      [leftEntry (m := m) a,rightEntry (n := n) b] p = some (some
        (ScannerFrontier.restore first (pre x p (commonPos A B a b x p))
          (pre x (commonPos A B a b x p) (finalPos A B a b first x p)))) := by
  rw [independent_eval A B hm tail x s E a b p clock hp hc]
  have he := first_remainder A B a b (sfx x p)
  rw [hgood.2] at he
  have hpre := ScannerFrontier.pre_concat x p (commonPos A B a b x p) (finalPos A B a b first x p)
    hp (common_bound A B a b x p hp) (final_bound A B a b first x p)
  cases first with
  | true =>
    simp only [if_true] at he
    have hh : (run A a (sfx x p)).2.length = commonPos A B a b x p := congrArg List.length he
    change some (some [pre x p (run A a (sfx x p)).2.length,pre x p (run B b (sfx x p)).2.length]) = _
    have hl : finalPos A B a b true x p = (run B b (sfx x p)).2.length := rfl
    rw [hh,← hl,hpre]
    rfl
  | false =>
    simp only [Bool.false_eq_true,if_false] at he
    have hh : (run B b (sfx x p)).2.length = commonPos A B a b x p := congrArg List.length he
    have hl : finalPos A B a b false x p = (run A a (sfx x p)).2.length := rfl
    rw [hh,← hl,hpre]
    rfl


abbrev Control (n m : Nat) := Fin n × Fin m × Bool

def actual {n m : Nat} (A : Machine n) (B : Machine m) (a : Fin n) (b : Fin m) (x : List Char) : Control n m :=
  ((common A B a b x).1.1,(common A B a b x).1.2,firstStops A B a b x)

def controls (n m : Nat) : List (Control n m) :=
  (List.ofFn (fun c : Fin n => (List.ofFn (fun d : Fin m => [(c,d,true),(c,d,false)])).flatten)).flatten

theorem controls_mem {n m : Nat} (c : Fin n) (d : Fin m) (first : Bool) : (c,d,first) ∈ controls n m := by
  apply List.mem_flatten.mpr
  refine ⟨_,List.mem_ofFn.mpr ⟨c,rfl⟩,?_⟩
  apply List.mem_flatten.mpr
  refine ⟨_,List.mem_ofFn.mpr ⟨d,rfl⟩,?_⟩
  cases first <;> simp

theorem goodCase_iff_eq {n m : Nat} (A : Machine n) (B : Machine m)
    (a c : Fin n) (b d : Fin m) (first : Bool) (x : List Char) :
    GoodCase A B a c b d first x ↔ (c,d,first) = actual A B a b x := by
  simp only [actual,GoodCase,Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hc,hd⟩,hf⟩; exact ⟨hc.symm,hd.symm,hf.symm⟩
  · rintro ⟨hc,hd,hf⟩; exact ⟨⟨hc.symm,hd.symm⟩,hf.symm⟩

def dispatch {n m : Nat} (A : Machine n) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat) : List (Control n m) → MExp
  | [] => MExp.failAlways
  | (c,d,first)::rest => RootObservation.branch (caseGuard A a c b d first)
    (.call (dest (c,d,first)) (arguments a c b d first)) (dispatch A a b dest rest)

theorem caseGuard_firstOrder {n m : Nat} (A : Machine n) (a c : Fin n) (b d : Fin m) (first : Bool) :
    (caseGuard A a c b d first).FirstOrder := by
  change True ∧ (stopTest (A.arcs c) first).FirstOrder
  constructor
  · trivial
  · cases first <;> exact NestedScannerArguments.choice_firstOrder _

theorem arguments_firstOrder {n m : Nat} (a c : Fin n) (b d : Fin m) (first : Bool) :
    MExp.FirstOrderArgs (arguments a c b d first) := by cases first <;> trivial

theorem dispatch_firstOrder {n m : Nat} (A : Machine n) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat) (cases : List (Control n m)) : (dispatch A a b dest cases).FirstOrder := by
  induction cases with
  | nil => trivial
  | cons control rest ih =>
    obtain ⟨c,d,first⟩ := control
    exact ⟨⟨caseGuard_firstOrder _ _ _ _ _ _,arguments_firstOrder _ _ _ _ _⟩,
      ⟨caseGuard_firstOrder _ _ _ _ _ _,ih⟩⟩

/-- The finite dispatcher uses only actual tests and capture parsers.
Unknown, failed, or undefined chosen user-body results are returned intact. -/
theorem dispatch_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat) (cases : List (Control n m))
    (valid : ∀ control ∈ cases, ∃ r, ruleAtM (grammar A B hm tail).rules (dest control) = some r ∧ r.arity=2)
    (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock)
    (hmem : actual A B a b (sfx x p) ∈ cases) :
    evV (grammar A B hm tail) x .callByValueSeq (tblV (grammar A B hm tail) x .callByValueSeq clock)
      E (dispatch A a b dest cases) p =
      valAt (tblV (grammar A B hm tail) x .callByValueSeq clock
        (dest (actual A B a b (sfx x p)))
        [pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p)])
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) := by
  induction cases with
  | nil => cases hmem
  | cons control rest ih =>
    obtain ⟨c,d,first⟩ := control
    rw [dispatch,ScannerFrontier.branch_eval _ _ _ p (decide (GoodCase A B a c b d first (sfx x p)))
      (by simpa only [decide_eq_true_eq] using
        caseGuard_eval A B hm tail x .callByValueSeq E a c b d first p clock hp hc)]
    simp only [decide_eq_true_eq]
    by_cases hg : GoodCase A B a c b d first (sfx x p)
    · rw [if_pos hg]
      obtain ⟨r,hr,hr2⟩ := valid (c,d,first) (by simp)
      rw [evV_call_seq (args := arguments a c b d first) hr (by
        cases first <;> simpa only [arguments,List.length_cons,List.length_nil] using hr2),
        arguments_eval A B hm tail x .callByValueSeq E a c b d first p clock hp hc hg.1]
      dsimp only []
      have heq := (goodCase_iff_eq A B a c b d first (sfx x p)).mp hg
      rw [← heq,hg.2]
    · rw [if_neg hg]
      apply ih (fun control h => valid control (by simp [h]))
      rcases List.mem_cons.mp hmem with h | h
      · exact False.elim (hg ((goodCase_iff_eq A B a c b d first (sfx x p)).mpr h.symm))
      · exact h

theorem complete_dispatch_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat)
    (valid : ∀ control, ∃ r, ruleAtM (grammar A B hm tail).rules (dest control) = some r ∧ r.arity=2)
    (p clock : Nat) (hp : p ≤ x.length) (hc : p+1 ≤ clock) :
    evV (grammar A B hm tail) x .callByValueSeq (tblV (grammar A B hm tail) x .callByValueSeq clock)
      E (dispatch A a b dest (controls n m)) p =
      valAt (tblV (grammar A B hm tail) x .callByValueSeq clock
        (dest (actual A B a b (sfx x p)))
        [pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p)])
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) :=
  dispatch_eval A B hm tail x E a b dest (controls n m) (fun control _ => valid control)
    p clock hp hc (controls_mem _ _ _)


/-- Only two user-body variants are needed: residual states select the
argument parsers, while the body retains just the original capture order. -/
theorem complete_dispatch_body_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (left right : Nat) (e : MExp) (he : e.FirstOrder)
    (hl : ruleAtM (grammar A B hm tail).rules left = some ⟨2,ScannerFrontier.body true e⟩)
    (hr : ruleAtM (grammar A B hm tail).rules right = some ⟨2,ScannerFrontier.body false e⟩)
    (p clock : Nat) (hp : p ≤ x.length) (hc : p ≤ clock) :
    evV (grammar A B hm tail) x .callByValueSeq (tblV (grammar A B hm tail) x .callByValueSeq (clock+1)) E
      (dispatch A a b (fun control => if control.2.2 then left else right) (controls n m)) p =
      evV (grammar A B hm tail) x .callByValueSeq (tblV (grammar A B hm tail) x .callByValueSeq clock)
        (ScannerFrontier.restore (firstStops A B a b (sfx x p)) (pre x p (commonPos A B a b x p))
          (pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p))) e
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) := by
  have valid : ∀ control : Control n m, ∃ r,
      ruleAtM (grammar A B hm tail).rules (if control.2.2 then left else right) = some r ∧ r.arity=2 := by
    intro control
    cases hf : control.2.2
    · exact ⟨_,hr,rfl⟩
    · exact ⟨_,hl,rfl⟩
  rw [complete_dispatch_eval A B hm tail x E a b _ valid p (clock+1) hp (by omega)]
  have hq : finalPos A B a b (firstStops A B a b (sfx x p)) x p ≤ x.length :=
    Nat.le_trans (final_bound A B a b _ x p) (Nat.le_trans (common_bound A B a b x p hp) hp)
  simp only [actual]
  by_cases hf : firstStops A B a b (sfx x p) = true
  · simp only [hf,if_true] at hq ⊢
    rw [valAt_tblV_succ hl _ hq]
    exact ScannerFrontier.body_eval _ _ _ _ true _ _ e he _
  · have hfalse : firstStops A B a b (sfx x p) = false := Bool.eq_false_iff.mpr hf
    simp only [hfalse,Bool.false_eq_true,if_false] at hq ⊢
    rw [valAt_tblV_succ hr _ hq]
    exact ScannerFrontier.body_eval _ _ _ _ false _ _ e he _

end Shallot.MacroPeg.CBV.StatefulPairArguments
