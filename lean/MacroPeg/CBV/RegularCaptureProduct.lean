import MacroPeg.CBV.OverlapNecessity

/-! Generate real arity-zero PEG rules for a consumed-word finite-state
filter. Original parse queries guard the product, including prioritized
choice and undefined recursion. Global product correctness is separate. -/
namespace Shallot.MacroPeg.CBV.RegularCaptureProduct
open ClockFreezing (Table)

structure Machine where
  width : Nat
  step : Nat → Char → Nat

def run (D : Machine) (q : Nat) (w : List Char) : Nat := w.foldl D.step q

def Machine.Valid (D : Machine) : Prop :=
  0<D.width ∧ ∀ q, q<D.width → ∀ c, D.step q c<D.width

theorem run_append (D : Machine) (q : Nat) (u v : List Char) :
    run D q (u++v) = run D (run D q u) v := by simp [run,List.foldl_append]

theorem run_bound {D : Machine} (h : D.Valid) (q : Nat) (hq : q<D.width) (w : List Char) :
    run D q w<D.width := by
  induction w generalizing q with
  | nil => exact hq
  | cons c w ih => exact ih (D.step q c) (h.2 q hq c)

inductive Node where
  | lit (w : List Char)
  | seq (a b : Nat)
  | alt (a b : Nat)
  | star (a : Nat)
  | notP (a : Nat)

def body : Node → MExp
  | .lit w => .lit w
  | .seq a b => .seq (.call a []) (.call b [])
  | .alt a b => .alt (.call a []) (.call b [])
  | .star a => .star (.call a [])
  | .notP a => .notP (.call a [])

def Valid (nodes : List Node) : Prop := ∀ n ∈ nodes, match n with
  | .lit _ => True
  | .seq a b | .alt a b => a<nodes.length ∧ b<nodes.length
  | .star a | .notP a => a<nodes.length

def key (nodes : List Node) (D : Machine) (i q r : Nat) : Nat :=
  nodes.length + ((i*D.width+q)*D.width+r)

def choice : List MExp → MExp
  | [] => MExp.failAlways
  | e::es => .alt e (choice es)

def call (nodes : List Node) (D : Machine) (i q r : Nat) : MExp := .call (key nodes D i q r) []

def select (nodes : List Node) (D : Machine) (a b q r : Nat) : MExp :=
  choice ((List.range D.width).map (fun t => .seq (call nodes D a q t) (call nodes D b t r)))

def core (nodes : List Node) (D : Machine) (i : Nat) : Node → Nat → Nat → MExp
  | .lit w, q, r => .seq (.lit w) (if run D q w = r then .eps else MExp.failAlways)
  | .seq a b, q, r => select nodes D a b q r
  | .alt a b, q, r => RootObservation.branch (.andP (.call a [])) (call nodes D a q r) (call nodes D b q r)
  | .star a, q, r => RootObservation.branch (.andP (.call a [])) (select nodes D a i q r)
      (if q=r then .eps else MExp.failAlways)
  | .notP _, q, r => if q=r then .eps else MExp.failAlways

def filterBody (nodes : List Node) (D : Machine) (i : Nat) (n : Node) (q r : Nat) : MExp :=
  .seq (.andP (.call i [])) (core nodes D i n q r)

def grammar (nodes : List Node) (D : Machine) : MGrammar :=
  ⟨nodes.map (fun n => ⟨0,body n⟩) ++ List.ofFn (n := nodes.length*D.width*D.width) (fun k =>
    let i := (k.val/D.width)/D.width
    let q := (k.val/D.width)%D.width
    let r := k.val%D.width
    ⟨0,filterBody nodes D i (nodes[i]?.getD (.lit [])) q r⟩)⟩

theorem choice_firstOrder : ∀ es, (∀ e ∈ es, e.FirstOrder) → (choice es).FirstOrder
  | [], _ => True.intro
  | e::es, h => ⟨h e (by simp),choice_firstOrder es (fun e he => h e (by simp [he]))⟩

theorem core_firstOrder (nodes : List Node) (D : Machine) (i q r : Nat) (n : Node) :
    (core nodes D i n q r).FirstOrder := by
  have hc (i q r : Nat) : (call nodes D i q r).FirstOrder := True.intro
  have hs (a b : Nat) : (select nodes D a b q r).FirstOrder := by
    apply choice_firstOrder
    intro e he
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
    exact ⟨hc _ _ _,hc _ _ _⟩
  cases n with
  | lit w => simp only [core]; split <;> trivial
  | seq a b => exact hs a b
  | alt a b => exact ⟨⟨True.intro,hc _ _ _⟩,True.intro,hc _ _ _⟩
  | star a => simp only [core]; split <;> exact ⟨⟨True.intro,hs a i⟩,True.intro,True.intro⟩
  | notP a => simp only [core]; split <;> trivial

theorem grammar_firstOrder (nodes : List Node) (D : Machine) : (grammar nodes D).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨n,_,rfl⟩ := List.mem_map.mp hr
    cases n <;> trivial
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨True.intro,core_firstOrder _ _ _ _ _ _⟩

theorem original_rule (nodes : List Node) (D : Machine) (i : Nat) (n : Node) (hi : nodes[i]?=some n) :
    ruleAtM (grammar nodes D).rules i = some ⟨0,body n⟩ := by
  have hlen := List.getElem?_eq_some_iff.mp hi |>.1
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hlen)]
  simp [hi]

theorem decode (N i q r : Nat) (hN : 0<N) (hq : q<N) (hr : r<N) :
    (((i*N+q)*N+r)/N)/N=i ∧ (((i*N+q)*N+r)/N)%N=q ∧ ((i*N+q)*N+r)%N=r := by
  have hd (a b : Nat) (hb : b<N) : (a*N+b)/N=a := by
    rw [Nat.mul_comm a N,Nat.mul_add_div hN,Nat.div_eq_of_lt hb,Nat.add_zero]
  rw [hd _ _ hr,hd _ _ hq,Nat.mul_add_mod_of_lt hq,Nat.mul_add_mod_of_lt hr]
  exact ⟨rfl,rfl,rfl⟩

theorem filter_rule (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (i q r : Nat) (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) :
    ruleAtM (grammar nodes D).rules (key nodes D i q r) =
      some ⟨0,filterBody nodes D i nodes[i] q r⟩ := by
  have hk : (i*D.width+q)*D.width+r < nodes.length*D.width*D.width := by
    have h1 := Nat.mul_le_mul_right D.width (show i+1≤nodes.length by omega)
    have h2 := Nat.mul_le_mul_right D.width (show i*D.width+q+1≤nodes.length*D.width by
      rw [Nat.add_mul] at h1; omega)
    rw [Nat.add_mul] at h2
    omega
  obtain ⟨hI,hQ,hR⟩ := decode D.width i q r hD hq hr
  simp only [grammar,key,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map,Nat.add_sub_cancel_left,List.getElem?_ofFn]
  simp [hk,hI,hQ,hR,List.getElem?_eq_getElem hi]

/-- The original node query is an actual installed grammar row. -/
theorem filter_body_eval (nodes : List Node) (D : Machine) (x : List Char) (s : Strategy) (T : Table)
    (i : Nat) (n : Node) (hi : nodes[i]?=some n) (q r p : Nat) (E : List (List Char)) :
    evV (grammar nodes D) x s T E (filterBody nodes D i n q r) p =
      match valAt (T i []) p with
      | some (some _) => evV (grammar nodes D) x s T E (core nodes D i n q r) p
      | other => other := by
  have hh : evV (grammar nodes D) x s T E (.call i []) p = valAt (T i []) p := by
    cases s <;> simp [evV,original_rule nodes D i n hi,evParArgs,evSeqArgs]
  change (match evV (grammar nodes D) x s T E (.andP (.call i [])) p with
    | some (some z) => evV (grammar nodes D) x s T E (core nodes D i n q r) z
    | other => other) = _
  rw [CallLookahead.evV_peek,hh]
  cases valAt (T i []) p with
  | none => rfl
  | some result => cases result <;> rfl

theorem original_call_eval (nodes : List Node) (D : Machine) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (i : Nat) (n : Node) (hi : nodes[i]?=some n) (p : Nat) :
    evV (grammar nodes D) x s T E (.call i []) p = valAt (T i []) p := by
  cases s <;> simp [evV,original_rule nodes D i n hi,evParArgs,evSeqArgs]

theorem product_call_eval (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) (i q r : Nat)
    (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) (p : Nat) :
    evV (grammar nodes D) x s T E (call nodes D i q r) p = valAt (T (key nodes D i q r) []) p := by
  cases s <;> simp [call,evV,filter_rule nodes D hD i q r hi hq hr,evParArgs,evSeqArgs]

theorem helper_valid {nodes : List Node} (h : Valid nodes) :
    RecursiveParserStability.Valid (nodes.map body) := by
  intro e he
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
  have hh := h n hn
  cases n <;> simp_all [body,RecursiveParserStability.Lexical]

theorem original_installed (nodes : List Node) (D : Machine) :
    RecursiveParserStability.Installed (nodes.map body) (grammar nodes D) := by
  intro i e hi
  have hlen : i<nodes.length := by
    have hh := List.getElem?_eq_some_iff.mp hi |>.1
    simpa using hh
  have hn := List.getElem?_eq_getElem hlen
  have he : body nodes[i]=e := by simpa only [List.getElem?_map,hn,Option.map_some,Option.some.injEq] using hi
  subst e
  exact original_rule nodes D i nodes[i] hn

/-- An actual product round cannot invent a result from an unknown or failed
original query. This theorem is about physical tables, not supplied advice. -/
theorem filter_step (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (x : List Char) (s : Strategy) (k i q r p : Nat)
    (hi : i<nodes.length) (hq : q<D.width) (hr : r<D.width) (hp : p≤x.length) :
    valAt (tblV (grammar nodes D) x s (k+1) (key nodes D i q r) []) p =
      match valAt (tblV (grammar nodes D) x s k i []) p with
      | some (some _) => evV (grammar nodes D) x s (tblV (grammar nodes D) x s k) [] (core nodes D i nodes[i] q r) p
      | other => other := by
  rw [valAt_tblV_succ (filter_rule nodes D hD i q r hi hq hr) [] hp]
  exact filter_body_eval nodes D x s _ i nodes[i] (List.getElem?_eq_getElem hi) q r p []

/-- A source alternative that succeeds stays chosen even when the requested
end state makes its filtered continuation fail. No second source parse is used. -/
theorem choice_commit (nodes : List Node) (D : Machine) (hD : 0<D.width)
    (x : List Char) (s : Strategy) (T : Table) (i a b q r p z t : Nat)
    (hi : nodes[i]?=some (.alt a b)) (ha : a<nodes.length) (_hb : b<nodes.length)
    (hq : q<D.width) (hr : r<D.width)
    (hparent : valAt (T i []) p=some (some z))
    (hchosen : valAt (T a []) p=some (some t))
    (hfail : valAt (T (key nodes D a q r) []) p=some none) :
    evV (grammar nodes D) x s T [] (filterBody nodes D i (.alt a b) q r) p = some none := by
  rw [filter_body_eval nodes D x s T i (.alt a b) hi q r p [],hparent]
  simp only [core]
  rw [ChoiceArguments.branch_eval,original_call_eval nodes D x s T [] a nodes[a] (List.getElem?_eq_getElem ha) p,hchosen]
  exact (product_call_eval nodes D hD x s T [] a q r ha hq hr p).trans hfail

/-- A left-recursive original query remains undefined in every generated
filter, on every input and at every physical round. -/
theorem left_cycle_undefined (D : Machine) (hD : 0<D.width) (x : List Char) (s : Strategy)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) (k p : Nat) (hp : p≤x.length) :
    let nodes : List Node := [.seq 0 1,.lit []]
    valAt (tblV (grammar nodes D) x s k 0 []) p = none ∧
      valAt (tblV (grammar nodes D) x s k (key nodes D 0 q r) []) p = none := by
  let nodes : List Node := [.seq 0 1,.lit []]
  have hc : ∀ k, valAt (tblV (grammar nodes D) x s k 0 []) p=none := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [valAt_tblV_succ (original_rule nodes D 0 (.seq 0 1) rfl) [] hp]
      change evV (grammar nodes D) x s (tblV (grammar nodes D) x s k) [] (.seq (.call 0 []) (.call 1 [])) p=none
      rw [evV_seq_none ((original_call_eval nodes D x s _ [] 0 (.seq 0 1) rfl p).trans ih)]
  refine ⟨hc k,?_⟩
  cases k with
  | zero => rfl
  | succ k => rw [filter_step nodes D hD x s k 0 q r p (by decide) hq hr hp,hc k]

/-- Empty-success repetition is likewise undefined; no final-state test
turns its nontermination into finite rejection. -/
theorem nullable_star_undefined (D : Machine) (hD : 0<D.width) (x : List Char) (s : Strategy)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) (k p : Nat) (hp : p≤x.length) :
    let nodes : List Node := [.star 1,.lit []]
    valAt (tblV (grammar nodes D) x s k 0 []) p = none ∧
      valAt (tblV (grammar nodes D) x s k (key nodes D 0 q r) []) p = none := by
  let nodes : List Node := [.star 1,.lit []]
  have hc : ∀ k, valAt (tblV (grammar nodes D) x s k 0 []) p=none := by
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      rw [valAt_tblV_succ (original_rule nodes D 0 (.star 1) rfl) [] hp]
      change evV (grammar nodes D) x s (tblV (grammar nodes D) x s k) [] (.star (.call 1 [])) p=none
      rw [evV_star]
      cases k with
      | zero => exact evStar_none (by rw [original_call_eval nodes D x s _ [] 1 (.lit []) rfl p]; rfl)
      | succ k =>
        have ha : evV (grammar nodes D) x s (tblV (grammar nodes D) x s (k+1)) [] (.call 1 []) p=some (some p) := by
          rw [original_call_eval nodes D x s _ [] 1 (.lit []) rfl p,
            valAt_tblV_succ (original_rule nodes D 1 (.lit []) rfl) [] hp]
          simp [body,evV,Shallot.stripPrefix?,length_sfx x hp]
        exact evStar_stuck ha (by omega)
  refine ⟨hc k,?_⟩
  cases k with
  | zero => rfl
  | succ k => rw [filter_step nodes D hD x s k 0 q r p (by decide) hq hr hp,hc k]

def alternating : Machine := ⟨3,fun q c =>
  if q=0 then if c='a' then 1 else 2
  else if q=1 then if c='b' then 0 else 2 else 2⟩

theorem alternating_valid : alternating.Valid := by
  constructor
  · decide
  · intro q hq c
    simp only [alternating] at hq ⊢
    split <;> (repeat' split) <;> omega

/-- This source accepts arbitrary a/b/c words, not just periodic ones. -/
def scannerNodes : List Node := [.alt 1 2,.seq 3 0,.lit [],.alt 4 5,.lit ['a'],.alt 6 7,.lit ['b'],.lit ['c']]

theorem scanner_valid : Valid scannerNodes := by
  intro n hn
  simp only [scannerNodes,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Actual finite-state filtering of a recursive scanner: it keeps ababa,
rejects abac, and does not change the original scanner's selected endpoint. -/
theorem scanner_filter_execution :
    let g := grammar scannerNodes alternating
    let good := "ababa#".toList
    let bad := "abac#".toList
    let f := call scannerNodes alternating 0 0 1
    (evV g good .callByValueSeq (tblV g good .callByValueSeq 50) [] (.call 0 []) good.length=some (some 1)) ∧
    (evV g good .callByValueSeq (tblV g good .callByValueSeq 50) [] f good.length=some (some 1)) ∧
    (evV g bad .callByValueSeq (tblV g bad .callByValueSeq 50) [] (.call 0 []) bad.length=some (some 1)) ∧
    (evV g bad .callByValueSeq (tblV g bad .callByValueSeq 50) [] f bad.length=some none) := by
  decide +kernel

/-- Filtering an ordered choice cannot replace the winning ab parse with a,
even though only the shorter parse ends in the requested automaton state. -/
theorem prioritized_filter_execution :
    let nodes : List Node := [.alt 1 2,.lit ['a','b'],.lit ['a']]
    let g := grammar nodes alternating
    let x := "ab#".toList
    evV g x .callByValueSeq (tblV g x .callByValueSeq 8) [] (call nodes alternating 0 0 1) x.length=some none ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq 8) []
        (.alt (call nodes alternating 1 0 1) (call nodes alternating 2 0 1)) x.length=some (some 2) := by
  decide +kernel

/-- The intended specification distinguishes unknown, finite failure, and a
successful parse with the wrong final automaton state. -/
def filtered (D : Machine) (x : List Char) (q r p : Nat) : Res → Res
  | some (some j) => if run D q (pre x p j)=r then some (some j) else some none
  | other => other

/-- Intermediate-state enumeration cannot retry a different successful
state when the selected continuation fails or is undefined. -/
theorem choice_eval_unique (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p chosen : Nat) (v : Res) (R : Nat → MExp) :
    ∀ (states : List Nat), (∀ t ∈ states, evV g x s T E (R t) p = if t=chosen then v else some none) →
      evV g x s T E (choice (states.map R)) p = if chosen ∈ states then v else some none
  | [], h => by simp [choice,MExp.failAlways,evV]
  | t::states, h => by
    have ht := h t (by simp)
    have ih := choice_eval_unique g x s T E p chosen v R states (fun t ht => h t (by simp [ht]))
    simp only [List.map_cons,choice]
    by_cases hc : t=chosen
    · rw [if_pos hc] at ht
      cases v with
      | none => rw [evV_alt_none ht]; simp [hc]
      | some result => cases result with
        | none => rw [evV_alt_fail ht,ih]; simp [hc]
        | some j => rw [evV_alt_ok ht]; simp [hc]
    · rw [if_neg hc] at ht
      rw [evV_alt_fail ht,ih]
      simp only [List.mem_cons,eq_comm (a := chosen) (b := t),hc,false_or]

/-- Literal product rules implement the full filtered result specification,
including a successful original parse whose requested end state is wrong. -/
theorem literal_correct (nodes : List Node) (D : Machine) (x : List Char) (s : Strategy) (T : Table)
    (i q r p : Nat) (w : List Char) (hi : nodes[i]?=some (.lit w)) (hp : p≤x.length)
    (hOriginal : valAt (T i []) p = evV (grammar nodes D) x s T [] (.lit w) p) :
    evV (grammar nodes D) x s T [] (filterBody nodes D i (.lit w) q r) p =
      filtered D x q r p (evV (grammar nodes D) x s T [] (.lit w) p) := by
  rw [filter_body_eval nodes D x s T i (.lit w) hi q r p [],hOriginal]
  cases hv : evV (grammar nodes D) x s T [] (.lit w) p with
  | none =>
    have hn : evV (grammar nodes D) x s T [] (.lit w) p ≠ none := by
      simp only [evV]
      cases Shallot.stripPrefix? w (sfx x p) <;> simp
    exact False.elim (hn hv)
  | some result => cases result with
    | none => rfl
    | some j =>
      have hw := WordArguments.value_of_success (grammar nodes D) x s T [] (.lit w) True.intro p j hp hv
      have he : pre x p j=w := by simpa only [WordArguments.value,Option.some.injEq] using hw.symm
      simp only [core,filtered,he]
      rw [evV_seq_ok hv]
      split <;> rfl

/-- Greedy repetition may not stop early to satisfy the requested state. -/
theorem star_filter_execution :
    let nodes : List Node := [.star 1,.lit ['a']]
    let g := grammar nodes alternating
    let x := "aaa#".toList
    evV g x .callByValueSeq (tblV g x .callByValueSeq 16) [] (call nodes alternating 0 0 1) x.length=some none ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq 16) [] (call nodes alternating 0 0 2) x.length=some (some 1) := by
  decide +kernel

/-- Negative predicates preserve the starting state when they succeed. -/
theorem predicate_filter_execution :
    let nodes : List Node := [.notP 1,.lit ['a']]
    let g := grammar nodes alternating
    let x := "b#".toList
    evV g x .callByValueSeq (tblV g x .callByValueSeq 4) [] (call nodes alternating 0 0 0) x.length=some (some x.length) ∧
      evV g x .callByValueSeq (tblV g x .callByValueSeq 4) [] (call nodes alternating 0 0 1) x.length=some none := by
  decide +kernel

/-- Prototype caller wiring for shift ab. State 0 selects residual ab;
state 1 selects ba. The full capture remains the actual unary argument. -/
def shiftedSource (nodes : List Node) : MGrammar :=
  ⟨(grammar nodes alternating).rules ++
    [⟨1,.seq (.seq (.lit ['a','b']) (.param 0)) (.notP .any)⟩]⟩

def shiftedTarget (nodes : List Node) : MGrammar :=
  ⟨(grammar nodes alternating).rules ++
    [⟨1,.seq (.lit ['a','b']) (.notP .any)⟩,
     ⟨1,.seq (.lit ['b','a']) (.notP .any)⟩]⟩

def shiftedStart (nodes : List Node) (i : Nat) : MExp :=
  let base := (grammar nodes alternating).rules.length
  RootObservation.branch (.andP (call nodes alternating i 0 0))
    (.call base [.call i []])
    (RootObservation.branch (.andP (call nodes alternating i 0 1))
      (.call (base+1) [.call i []]) MExp.failAlways)

/-- Generated filters repair the previous abacab false positive, while a
successful aba capture selects the rotated ba residual. The nonperiodic
winning alternative must never be replaced with the shorter periodic one. -/
theorem guarded_rotation_execution :
    let nodes : List Node := [.alt 1 2,.lit ['a','b','a','c'],.lit ['a','b','a']]
    let gp := shiftedSource nodes
    let gs := shiftedTarget nodes
    let ep := MExp.call (grammar nodes alternating).rules.length [.call 0 []]
    let es := shiftedStart nodes 0
    let good := "ababa".toList
    let bad := "abacab".toList
    (evV gp good .callByValuePar (tblV gp good .callByValuePar 10) [] ep good.length=some (some 0)) ∧
    (evV gs good .callByValueSeq (tblV gs good .callByValueSeq 10) [] es good.length=some (some 0)) ∧
    (evV gp bad .callByValuePar (tblV gp bad .callByValuePar 10) [] ep bad.length=some none) ∧
    (evV gs bad .callByValueSeq (tblV gs bad .callByValueSeq 10) [] es bad.length=some none) := by
  decide +kernel

end Shallot.MacroPeg.CBV.RegularCaptureProduct
