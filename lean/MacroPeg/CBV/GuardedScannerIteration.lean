import MacroPeg.CBV.GuardedReplayAlignment
import MacroPeg.CBV.DynamicScannerBinding
import MacroPeg.CBV.GeneralStarFilter
import MacroPeg.CBV.ObservedScannerDispatch
import MacroPeg.CBV.DependentCaptureFilter

namespace Shallot.MacroPeg.CBV.GuardedScannerIteration
open GuardedReplayControl (Aligned Results)
open StatefulScanner (Machine run advance)
open ClockFreezing (Table)

def step {n : Nat} (q : Fin n) : MExp := .seq (.call q.val []) (.andP (.param 0))
def header {n : Nat} (q : Fin n) : MExp := .seq (.star (step q)) (.param 0)
def residualStep {n : Nat} (r : Fin n) : MExp := .seq (.call r.val []) (.param 0)
def residual {n : Nat} (P : List Nat) (q : Fin n) : MExp :=
  match DynamicScannerBinding.resume P q with
  | none => MExp.failAlways
  | some r => .star (residualStep r)

def ScannerRows {n : Nat} (M : Machine n) (g : MGrammar) (x : List Char)
    (s : Strategy) (T : Table) (E : List (List Char)) : Prop :=
  ∀ q p, p≤x.length → evV g x s T E (.call q.val []) p=some (some (run M q (sfx x p)).2.length)

/-- The resumed scan ends at the same absolute position as the source
scan. Replaying w there corresponds to the source's zero-width query. -/
theorem step_results {n : Nat} (M : Machine n) (q r : Fin n) (w : List Char)
    (hw : advance M q w=some r) (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : ScannerRows M g x s T [w]) (hU : ScannerRows M h x t U [w])
    (p j : Nat) (hpj : Aligned x w p j) :
    Results (Aligned x w) (evV g x s T [w] (step q) p) (evV h x t U [w] (residualStep r) j) := by
  have he := StatefulScanner.run_after_prefix M w (sfx x j) q r hw
  rw [←hpj.2.2] at he
  let z := (run M q (sfx x p)).2.length
  have hz : z≤x.length := by
    have hh := StatefulScanner.run_length M q (sfx x p)
    rw [length_sfx x hpj.1] at hh
    exact Nat.le_trans hh hpj.1
  have hs := hT q p hpj.1
  have ht := hU r j hpj.2.1
  rw [←he] at ht
  rw [step,residualStep,evV_seq_ok hs,evV_seq_ok ht,CallLookahead.evV_peek]
  change Results (Aligned x w) (CallLookahead.peek z (evV g x s T [w] (.param 0) z))
    (evV h x t U [w] (.param 0) z)
  have hp : evV g x s T [w] (.param 0) z=evV h x t U [w] (.param 0) z := rfl
  rw [hp]
  cases hv : evV h x t U [w] (.param 0) z with
  | none => trivial
  | some v => cases v with
    | none => trivial
    | some y => exact GuardedReplayControl.aligned_of_replay h x w t U z y hz hv

theorem step_position {n : Nat} (M : Machine n) (q : Fin n) (g : MGrammar) (x w : List Char)
    (s : Strategy) (T : Table) (hT : ScannerRows M g x s T [w])
    (p j : Nat) (hp : p≤x.length) (h : evV g x s T [w] (step q) p=some (some j)) :
    j=(run M q (sfx x p)).2.length := by
  rw [step,evV_seq_ok (hT q p hp),CallLookahead.evV_peek] at h
  cases hv : evV g x s T [w] (.param 0) (run M q (sfx x p)).2.length with
  | none => simp [hv,CallLookahead.peek] at h
  | some v => cases v with
    | none => simp [hv,CallLookahead.peek] at h
    | some z => simpa only [hv,CallLookahead.peek,Option.some.injEq] using h.symm

theorem header_eq {n : Nat} (M : Machine n) (q r : Fin n) (w : List Char)
    (hw : advance M q w=some r) (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : ScannerRows M g x s T [w]) (hU : ScannerRows M h x t U [w])
    (p j : Nat) (hpj : Aligned x w p j) :
    evV g x s T [w] (header q) p=evV h x t U [w] (.star (residualStep r)) j := by
  have hr := GuardedReplayControl.star_results x w
    (fun p => evV g x s T [w] (step q) p) (fun j => evV h x t U [w] (residualStep r) j)
    (fun p j hpj => step_results M q r w hw g h x s t T U hT hU p j hpj) p j hpj
  change Results (Aligned x w) (evV g x s T [w] (.star (step q)) p)
    (evV h x t U [w] (.star (residualStep r)) j) at hr
  rcases hs : evV g x s T [w] (.star (step q)) p with _ | (_ | p') <;>
    rcases ht : evV h x t U [w] (.star (residualStep r)) j with _ | (_ | j') <;>
    simp only [hs,ht,Results] at hr
  all_goals first | contradiction | skip
  · exact evV_seq_none hs
  · exact evV_seq_fail hs
  · exact (evV_seq_ok hs).trans (GuardedReplayControl.aligned_replay g x w s T p' j' hr)

theorem residual_transfer {n : Nat} (M : Machine n) (r : Fin n) (w : List Char)
    (g h : MGrammar) (x : List Char) (s t : Strategy) (T U : Table)
    (hT : ScannerRows M g x s T [w]) (hU : ScannerRows M h x t U [w])
    (p : Nat) (hp : p≤x.length) :
    evV g x s T [w] (.star (residualStep r)) p=evV h x t U [w] (.star (residualStep r)) p := by
  apply evStar_congr p
  intro z hz
  rw [residualStep,evV_seq_ok (hT r z (Nat.le_trans hz hp)),evV_seq_ok (hU r z (Nat.le_trans hz hp))]
  rfl

theorem residual_firstOrder {n : Nat} (P : List Nat) (q : Fin n) : (residual P q).FirstOrder := by
  unfold residual
  split <;> trivial


open DynamicScannerCapture (observer)

def scanFilter {n : Nat} (M : Machine n) (r : Fin n) (a z : Nat) : MExp :=
  if ha : a<(observer M).width then
    ObservedScannerDispatch.dispatch n r ⟨a,ha⟩ (fun v =>
      if (StatefulScannerProduct.right (DynamicScannerCapture.observer_valid M).1 v).val=z then .eps else MExp.failAlways)
  else MExp.failAlways

def paramFilter {n : Nat} (M : Machine n) (P : List Nat) (a z : Nat) : MExp :=
  DependentCaptureFilter.filter [] (observer M) [P] (.param 0) a z

def stepFilter {n : Nat} (M : Machine n) (r : Fin n) (P : List Nat) (a z : Nat) : MExp :=
  RegularCaptureProduct.choice ((List.range (observer M).width).map (fun t =>
    .seq (scanFilter M r a t) (paramFilter M P t z)))

def residualFilter {n : Nat} (M : Machine n) (P : List Nat) (q : Fin n) (a z : Nat) : MExp :=
  match DynamicScannerBinding.resume P q with
  | none => MExp.failAlways
  | some r => GeneralStarFilter.filter (observer M).width (residualStep r) (stepFilter M r P) a z

theorem scanFilter_firstOrder {n : Nat} (M : Machine n) (r : Fin n) (a z : Nat) :
    (scanFilter M r a z).FirstOrder := by
  unfold scanFilter
  split
  · apply ObservedScannerDispatch.dispatch_firstOrder
    intro v
    split <;> trivial
  · trivial

theorem paramFilter_firstOrder {n : Nat} (M : Machine n) (P : List Nat) (a z : Nat) :
    (paramFilter M P a z).FirstOrder := DependentCaptureFilter.filter_firstOrder [] (observer M) [P] (.param 0) a z

theorem stepFilter_firstOrder {n : Nat} (M : Machine n) (r : Fin n) (P : List Nat) (a z : Nat) :
    (stepFilter M r P a z).FirstOrder := by
  apply RegularCaptureProduct.choice_firstOrder
  intro e he
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
  exact ⟨scanFilter_firstOrder M r a t,paramFilter_firstOrder M P t z⟩

theorem residualFilter_firstOrder {n : Nat} (M : Machine n) (P : List Nat) (q : Fin n) (a z : Nat) :
    (residualFilter M P q a z).FirstOrder := by
  unfold residualFilter
  split
  · trivial
  · apply GeneralStarFilter.filter_firstOrder
    · exact ⟨True.intro,True.intro⟩
    · exact stepFilter_firstOrder M _ P

end Shallot.MacroPeg.CBV.GuardedScannerIteration
