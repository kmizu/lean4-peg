import MacroPeg.CBV.ScannerFrontier

/-! Compile finite-state prefix scanners and stopping-state selectors to
actual first-order PEG rules. A transition consumes exactly one character;
the first missing transition, or EOF, stops the scan. -/
namespace Shallot.MacroPeg.CBV.StatefulScanner
open Shallot (beqChar)

def next {Q : Type} : List (Char × Q) → Char → Option Q
  | [], _ => none
  | (a,q)::arcs, c => if beqChar a c then some q else next arcs c

structure Machine (n : Nat) where
  arcs : Fin n → List (Char × Fin n)

def run {n : Nat} (M : Machine n) : Fin n → List Char → Fin n × List Char
  | q, [] => (q,[])
  | q, c::x => match next (M.arcs q) c with
    | none => (q,c::x)
    | some r => run M r x

def advance {n : Nat} (M : Machine n) : Fin n → List Char → Option (Fin n)
  | q, [] => some q
  | q, c::x => (next (M.arcs q) c).bind (fun r => advance M r x)

/-- The residual scanner starts in the state actually reached after the
consumed prefix, rather than resetting to its original state. -/
theorem run_after_prefix {n : Nat} (M : Machine n) (word suffix : List Char)
    (q r : Fin n) (h : advance M q word = some r) :
    run M q (word++suffix) = run M r suffix := by
  induction word generalizing q with
  | nil => cases h; rfl
  | cons c word ih =>
    cases ht : next (M.arcs q) c with
    | none => simp [advance,ht] at h
    | some t =>
      simp only [advance,ht,Option.bind_some] at h
      simpa only [List.cons_append,run,ht] using ih t h

theorem run_suffix {n : Nat} (M : Machine n) (q : Fin n) (x : List Char) :
    ∃ word, x = word ++ (run M q x).2 := by
  induction x generalizing q with
  | nil => exact ⟨[],rfl⟩
  | cons c x ih =>
    cases ht : next (M.arcs q) c with
    | none => exact ⟨[],by simp [run,ht]⟩
    | some r =>
      obtain ⟨word,hw⟩ := ih r
      exact ⟨c::word,by simpa only [run,ht,List.cons_append] using congrArg (List.cons c) hw⟩

theorem run_length {n : Nat} (M : Machine n) (q : Fin n) (x : List Char) :
    (run M q x).2.length ≤ x.length := by
  obtain ⟨word,hw⟩ := run_suffix M q x
  have hl := congrArg List.length hw
  simp only [List.length_append] at hl
  omega

def terminal (yes : Bool) : MExp := if yes then .eps else MExp.failAlways

/-- The negative guard prevents a failed final-state test in a recursive
successor from falling back to an earlier stopping point. -/
def branches {n : Nat} (base : Nat) (stop : MExp) : List (Char × Fin n) → MExp
  | [] => stop
  | (c,q)::arcs => RootObservation.branch (.andP (.chr c))
    (.seq (.chr c) (.call (base+q.val) [])) (branches base stop arcs)

def block {n : Nat} (M : Machine n) (finish : Fin n → Bool) (base : Nat) : List MRule :=
  List.ofFn (fun q : Fin n => ⟨0,branches base (terminal (finish q)) (M.arcs q)⟩)

def grammar {n : Nat} (M : Machine n) (finish : Fin n → Bool) : MGrammar :=
  ⟨block M finish 0⟩

theorem block_length {n : Nat} (M : Machine n) (finish : Fin n → Bool) (base : Nat) :
    (block M finish base).length = n := List.length_ofFn

theorem grammar_rule {n : Nat} (M : Machine n) (finish : Fin n → Bool) (q : Fin n) :
    ruleAtM (grammar M finish).rules q.val =
      some ⟨0,branches 0 (terminal (finish q)) (M.arcs q)⟩ := by
  simp [grammar,block,ruleAtM_eq_getElem?,q.isLt]

theorem branches_firstOrder {n : Nat} (base : Nat) (stop : MExp) (h : stop.FirstOrder)
    (arcs : List (Char × Fin n)) : (branches base stop arcs).FirstOrder := by
  induction arcs with
  | nil => exact h
  | cons arc arcs ih => exact ⟨⟨trivial,⟨trivial,trivial⟩⟩,⟨trivial,ih⟩⟩

theorem grammar_firstOrder {n : Nat} (M : Machine n) (finish : Fin n → Bool) :
    (grammar M finish).FirstOrder := by
  intro r hr
  change r ∈ List.ofFn (fun q : Fin n => ⟨0,branches 0 (terminal (finish q)) (M.arcs q)⟩) at hr
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
  apply branches_firstOrder
  cases finish q <;> trivial

private theorem call_nil {g : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} {E : List (List Char)} (i p : Nat) (r : MRule)
    (hr : ruleAtM g.rules i = some r) (ha : r.arity = 0) :
    evV g x s T E (.call i []) p = valAt (T i []) p := by
  cases s <;> simp [evV,hr,ha,evParArgs,evSeqArgs]

private theorem chr_guard (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (a : Char) (p : Nat) :
    evV g x s T E (.andP (.chr a)) p =
      if (match sfx x p with | [] => false | c::_ => beqChar a c)
      then some (some p) else some none := by
  rw [CallLookahead.evV_peek]
  simp only [evV]
  cases sfx x p with
  | nil => rfl
  | cons c rest => cases ha : beqChar a c <;> simp [ha,CallLookahead.peek]

theorem branches_eval {n : Nat} {g : MGrammar} {x : List Char} {s : Strategy}
    (T : Nat → List (List Char) → Val) (E : List (List Char)) (base : Nat)
    (layout : ∀ q : Fin n, ∃ r, ruleAtM g.rules (base+q.val) = some r ∧ r.arity = 0)
    (stop : MExp) (arcs : List (Char × Fin n)) (p : Nat) :
    evV g x s T E (branches base stop arcs) p =
      match sfx x p with
      | [] => evV g x s T E stop p
      | c::rest => match next arcs c with
        | none => evV g x s T E stop p
        | some q => valAt (T (base+q.val) []) rest.length := by
  induction arcs with
  | nil => cases sfx x p <;> rfl
  | cons arc arcs ih =>
    obtain ⟨a,q⟩ := arc
    rw [branches,ScannerFrontier.branch_eval _ _ _ p _ (chr_guard g x s T E a p)]
    cases hs : sfx x p with
    | nil => simpa only [hs,Bool.false_eq_true,if_false] using ih
    | cons c rest =>
      by_cases ha : beqChar a c = true
      · simp only [next,ha,if_true]
        have hc : evV g x s T E (.chr a) p = some (some rest.length) := by simp [evV,hs,ha]
        rw [evV_seq_ok hc]
        obtain ⟨r,hr,hr0⟩ := layout q
        exact call_nil _ _ r hr hr0
      · simpa only [next,ha,if_false,hs,Bool.false_eq_true] using ih

/-- Correctness inside any actual grammar containing this fixed scanner
block. The clock bound charges every consuming transition and final query. -/
theorem query_eval {n : Nat} (M : Machine n) (finish : Fin n → Bool)
    (g : MGrammar) (base : Nat)
    (layout : ∀ q : Fin n, ruleAtM g.rules (base+q.val) =
      some ⟨0,branches base (terminal (finish q)) (M.arcs q)⟩)
    (x : List Char) (s : Strategy) : ∀ p, p ≤ x.length → ∀ m, p+1 ≤ m →
      ∀ q : Fin n, valAt (tblV g x s m (base+q.val) []) p =
        some (if finish (run M q (sfx x p)).1 then some (run M q (sfx x p)).2.length else none) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp m hm q
    cases m with
    | zero => omega
    | succ m =>
      rw [valAt_tblV_succ (layout q) [] hp]
      rw [branches_eval _ [] base (fun q => ⟨_,layout q,rfl⟩)]
      cases hs : sfx x p with
      | nil =>
        have hl := length_sfx x hp
        rw [hs] at hl
        have hzero : p=0 := by simpa using hl.symm
        subst p
        cases hf : finish q <;> simp [terminal,hf,evV,MExp.failAlways,run]
      | cons c rest =>
        have hlen : rest.length+1=p := by simpa only [hs,List.length_cons] using length_sfx x hp
        have hrest : sfx x rest.length = rest :=
          sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨[c],hs⟩).choose_spec
        cases ht : next (M.arcs q) c with
        | none => cases hf : finish q <;> simp [terminal,hf,evV,MExp.failAlways,run,ht,hlen]
        | some r =>
          have he := ih rest.length (by omega) (by omega) m (by omega) r
          simpa only [hrest,run,ht] using he

theorem entry_eval {n : Nat} (M : Machine n) (finish : Fin n → Bool) (x : List Char)
    (s : Strategy) (q : Fin n) (p m : Nat) (hp : p ≤ x.length) (hm : p+1 ≤ m)
    (E : List (List Char)) :
    evV (grammar M finish) x s (tblV (grammar M finish) x s m) E (.call q.val []) p =
      some (if finish (run M q (sfx x p)).1 then some (run M q (sfx x p)).2.length else none) := by
  rw [call_nil _ _ _ (grammar_rule M finish q) rfl]
  simpa only [Nat.zero_add] using query_eval M finish (grammar M finish) 0 (fun q => by simpa using grammar_rule M finish q)
    x s p hp m hm q

end Shallot.MacroPeg.CBV.StatefulScanner
