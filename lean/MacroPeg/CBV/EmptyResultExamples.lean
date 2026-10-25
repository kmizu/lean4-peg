import MacroPeg.CBV.EmptyCaptureDecision

namespace Shallot.MacroPeg.CBV.EmptyResultExamples
open EmptyResultObservation
abbrev Parser := EmptyResultObservation.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def loop : List Parser := [.call 0]
def blocked : Parser := .seq (.chr 'a') (.call 0)

theorem source_loop (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV (source loop) x .callByValuePar (tblV (source loop) x .callByValuePar k) [] (plain (.call 0)) p=none := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change valAt (tblV (source loop) x .callByValuePar (k+1) 0 []) p=none
    rw [valAt_tblV_succ (show ruleAtM (source loop).rules 0=some ⟨0,plain (.call 0)⟩ from rfl) [] hp]
    exact ih

/-- The consumer succeeds, then the actual recursive continuation diverges.
A naive empty-only sequence would stop before reaching that continuation. -/
theorem source_blocked_all_clocks (k : Nat) :
    evV (source loop) ['a'] .callByValuePar (tblV (source loop) ['a'] .callByValuePar k) [] (plain blocked) 1=none := by
  rw [show plain blocked=.seq (.chr 'a') (plain (.call 0)) from rfl,
    evV_seq_ok (j := 0) (show evV (source loop) ['a'] .callByValuePar (tblV (source loop) ['a'] .callByValuePar k) [] (.chr 'a') 1=some (some 0) from rfl)]
  exact source_loop ['a'] 0 k (by decide)

theorem observer_blocked_all_clocks (k : Nat) :
    evV (target loop) ['a'] .callByValueSeq (tblV (target loop) ['a'] .callByValueSeq k) [] (empty blocked) 1=none := by
  rw [(physical loop ['a'] blocked 1 k (by decide)).2,source_blocked_all_clocks]; rfl

theorem removing_sequence_gate_is_wrong :
    evV (target loop) ['a'] .callByValueSeq (tblV (target loop) ['a'] .callByValueSeq 4) []
      (.seq (empty (.chr 'a')) (empty (.call 0))) 1=some none := by decide +kernel

def priority : Parser := .alt (.chr 'a') .eps

theorem consuming_priority :
    evV (target []) ['a'] .callByValueSeq (tblV (target []) ['a'] .callByValueSeq 0) [] (empty priority) 1=some none ∧
    evV (target []) ['b'] .callByValueSeq (tblV (target []) ['b'] .callByValueSeq 0) [] (empty priority) 1=some (some 1) := by decide +kernel

theorem naive_nullable_choice_is_wrong :
    evV (target []) ['a'] .callByValueSeq (tblV (target []) ['a'] .callByValueSeq 0) []
      (.alt (empty (.chr 'a')) (empty .eps)) 1=some (some 1) := by decide +kernel

def nullable : Parser := .star .eps

theorem nullable_all_inputs_all_clocks (bs : List Parser) (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV (target bs) x .callByValueSeq (tblV (target bs) x .callByValueSeq k) [] (empty nullable) p=none := by
  rw [(physical bs x nullable p k hp).2]
  change project p (evV (source bs) x .callByValuePar (tblV (source bs) x .callByValuePar k) [] (.star .eps) p)=none
  rw [evV_star,evStar_stuck (j := p) rfl (by omega)]; rfl

theorem removing_star_gate_is_wrong :
    evV (target []) [] .callByValueSeq (tblV (target []) [] .callByValueSeq 0) [] (.notP (normal .eps)) 0=some none := by decide +kernel

def balanced : Parser := .alt (.seq (.chr 'a') (.seq (.call 0) (.chr 'b'))) .eps
def helpers : List Parser := [balanced]
def args : List Parser := [.call 0,.star (.chr 'a'),.eps]
def sample (n : Nat) := List.replicate n 'a'++List.replicate n 'b'++['!']
def body (bits : List Bool) : MExp := if bits=[false,false,true]
  then normal (.seq (.star .any) (.notP .any)) else MExp.failAlways

theorem actual_independent_captures : ∀ n∈[1,2,4],
    evParArgs (source helpers) (sample n) .callByValuePar (tblV (source helpers) (sample n) .callByValuePar 20) []
      (args.map plain) (sample n).length=some (some [List.replicate n 'a'++List.replicate n 'b',List.replicate n 'a',[]]) := by decide +kernel

/-- The selected leaf consumes input. Argument evaluation has stayed at the
original entry position despite using the actual sequential strategy. -/
theorem target_consuming_leaf : ∀ n∈[1,2,4],
    evV (target helpers) (sample n) .callByValueSeq (tblV (target helpers) (sample n) .callByValueSeq 20) []
      (EmptyCaptureDecision.compile args body) (sample n).length=some (some 0) := by decide +kernel

theorem all_empty_tuple :
    evV (target helpers) ['!'] .callByValueSeq (tblV (target helpers) ['!'] .callByValueSeq 4) []
      (EmptyCaptureDecision.compile args (fun bits => if bits=[true,true,true] then .chr '!' else MExp.failAlways)) 1=some (some 0) := by decide +kernel

def failing : Parser := .notP .eps

theorem failure_before_divergence :
    evV (target loop) ['a'] .callByValueSeq (tblV (target loop) ['a'] .callByValueSeq 4) []
      (EmptyCaptureDecision.compile [failing,.call 0] (fun _ => .eps)) 1=some none := by decide +kernel

theorem divergence_before_failure_all_clocks (x : List Char) (p k : Nat) (hp : p≤x.length) :
    evV (target loop) x .callByValueSeq (tblV (target loop) x .callByValueSeq k) []
      (EmptyCaptureDecision.compile [.call 0,failing] (fun _ => .eps)) p=none := by
  rw [EmptyCaptureDecision.physical loop x _ _ p k hp]
  simp only [List.map_cons,evParArgs,source_loop x p k hp]

theorem missing_preflight_is_wrong :
    evV (target []) [] .callByValueSeq (tblV (target []) [] .callByValueSeq 0) []
      (EmptyCaptureDecision.decision [failing] (fun _ => .eps)) 0=some (some 0) ∧
    evV (target []) [] .callByValueSeq (tblV (target []) [] .callByValueSeq 0) []
      (EmptyCaptureDecision.compile [failing] (fun _ => .eps)) 0=some none := by decide +kernel

theorem out_of_range_is_finite_failure :
    evV (target helpers) ['a'] .callByValueSeq (tblV (target helpers) ['a'] .callByValueSeq 0) []
      (empty (.call 100)) 1=some none := by decide +kernel

/-- Incomplete recursion must not be reported as a consuming success. -/
theorem before_and_after_recursion_finishes :
    evV (target helpers) ['a','b'] .callByValueSeq (tblV (target helpers) ['a','b'] .callByValueSeq 1) []
      (empty (.call 0)) 2=none ∧
    evV (target helpers) ['a','b'] .callByValueSeq (tblV (target helpers) ['a','b'] .callByValueSeq 2) []
      (empty (.call 0)) 2=some none := by decide +kernel

end Shallot.MacroPeg.CBV.EmptyResultExamples
