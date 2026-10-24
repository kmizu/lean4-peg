import MacroPeg.CBV.StatefulScannerFamily

/-! The stateful construction includes the existing greedy scanner, while
resuming a general scanner in its initial state can change its result. -/
namespace Shallot.MacroPeg.CBV.StatefulScannerBridge
open StatefulScanner NestedScannerArguments

def stateless (A : List Char) : Machine 1 :=
  ⟨fun _ => A.map (fun c => (c,0))⟩

theorem next_stateless (A : List Char) (c : Char) :
    next (A.map (fun c => (c,(0 : Fin 1)))) c = if accepts A c then some 0 else none := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    by_cases h : Shallot.beqChar a c = true <;> simp [next,accepts,h,ih]

theorem run_stateless (A : List Char) (x : List Char) :
    run (stateless A) 0 x = (0,x.dropWhile (accepts A)) := by
  induction x with
  | nil => rfl
  | cons c x ih =>
    rw [run]
    have hstep : next ((stateless A).arcs 0) c =
        (if accepts A c then some (0 : Fin 1) else none) := next_stateless A c
    rw [hstep]
    by_cases h : accepts A c = true <;> simp [h,ih]

/-- The actual compiled one-state grammar reads the same original prefix
as the previous character-set scanner under either CBV strategy. -/
theorem stateless_observation (A : List Char) (x : List Char) (s : Strategy)
    (hs : s ≠ .callByName) :
    SObs (StatefulScannerFamily.grammar (stateless A)) s
      (StatefulScannerFamily.entry (0 : Fin 1) 0) x (some (x.dropWhile (accepts A))) := by
  simpa only [run_stateless,if_true] using
    StatefulScannerFamily.entry_observation (stateless A) x s hs 0 0

def changedState : Machine 2 := ⟨fun q =>
  if q.val=0 then [('a',1)] else [('b',1)]⟩

theorem resumed_run (n : Nat) : run changedState 1 (List.replicate n 'b') = (1,[]) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,run,changedState,next,Shallot.beqChar] using ih

/-- An arbitrarily long residual scan distinguishes the reached state from
the original state. Resetting after capture is not a valid general factor. -/
theorem resetting_changes_result (n : Nat) :
    run changedState 0 ('a'::List.replicate (n+1) 'b') = (1,[]) ∧
    run changedState 0 (List.replicate (n+1) 'b') = (0,List.replicate (n+1) 'b') := by
  constructor
  · simpa [run,changedState,next,Shallot.beqChar] using resumed_run (n+1)
  · simp [List.replicate_succ,run,changedState,next,Shallot.beqChar]

end Shallot.MacroPeg.CBV.StatefulScannerBridge
