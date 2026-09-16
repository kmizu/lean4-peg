import PalPeg.GalilScaffoldChainFallback
import PalPeg.GalilScaffoldTop
import PalPeg.GalilScaffoldTopChainVM

/-!
# Scan-mode instantiation of the controller frame

The joint scan/chain tick `JointTick` (input heads L/R, the chain watch,
the match clock) is the VM-side content of the Scala `stepScan` matched
branch. This module instantiates the scan-side predicates of
`GalilScaffoldTop.Frame` with it — the chain component being a `ChainVM`
whose watching case is the joint tick — and lifts `JointTick.count` /
`JointTick.compare` / `JointBreak` to `GalilScaffoldTop.Tick.scan_count` /
`Tick.scan_match`. The output refresh uses `!right.gap` and `left.isFirst`
through the parameters `onLetter`/`leftFirst`, which the scan invariant
supplies elsewhere (`scan_output`, `scan_output_complete`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier
open GalilScaffoldTop GalilScaffoldController

/-- The VM state seen by the scan mode: heads L/R and the chain. The clock
lives in the controller record. -/
structure ScanVM where
  left : PlaceHead
  right : PlaceHead
  chain : ChainVM

def ScanVM.toJoint (s : ScanVM) (w : GalilScaffoldChainWatch.State) (clock : ℕ) : JointState :=
  ⟨s.left, s.right, w, clock⟩

/-- Scan-side frame: only the predicates used by `Tick.scan_*` are
meaningful; the fallback/shift predicates are left empty here. -/
def scanFrame (onLetter leftFirst : ScanVM → Prop) : Frame ScanVM where
  init := fun _ _ => False
  available := fun s => canRight s.right
  background := fun s s' => s'.left = s.left ∧ s'.right = s.right ∧ ChainTick false s.chain s'.chain
  compare := fun s s' => s'.left = left s.left ∧ s'.right = right s.right ∧
    ChainTick (decide (read (left s.left) = read (right s.right))) s.chain s'.chain
  matched := fun s => read s.left = read s.right
  shiftGuard := fun _ => False
  matchedPlace := fun _ s s' => s' = s
  replayExhausted := fun _ => false
  onLetter := onLetter
  leftFirst := leftFirst
  beginShift := fun _ _ => False
  beginFallback := fun _ _ => False
  remainingPos := fun _ => False
  shiftOne := fun _ _ => False
  copyOne := fun _ _ => False
  copyEnd := fun _ _ => False
  atLeft := fun _ => False
  fppStart := fun _ _ => False
  homeStep := fun _ _ => False
  fppSlice := fun _ _ => False
  fppDone := fun _ _ => False
  atEnd := fun _ => False
  markBack := fun _ _ => False
  markForward := fun _ _ => False
  markSet := fun _ => False
  choose := fun _ _ => False
  atFirst := fun _ => False
  fppReset := fun _ _ => False
  rewindOne := fun _ _ => False
  rewindPair := fun _ _ => False
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  restart := fun _ _ => False

def ScanVM.ofJoint (t : JointState) : ScanVM := ⟨t.left, t.right, .watch t.watch⟩

/-- A counting tick of the joint machine (available, clock above one) is the
controller's `scan_count`. -/
theorem count_lift (onLetter leftFirst : ScanVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .scan) (hc : 1 < c.clock)
    (s : ScanVM) (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w)
    (t : JointState) (ha : canRight s.right)
    (ht : JointTick delay true (s.toJoint w c.clock) t) (hcl : t.clock = c.clock - 1) :
    GalilScaffoldTop.Tick (scanFrame onLetter leftFirst) delay ⟨c, s⟩
      ⟨{c with clock := c.clock - 1}, ScanVM.ofJoint t⟩ := by
  cases ht with
  | count _ w' _ ht' =>
    have ha' : (scanFrame onLetter leftFirst).available s := ha
    exact .scan_count c s (ScanVM.ofJoint ⟨s.left, s.right, w', c.clock - 1⟩) hm (Or.inr ha') hc
      ⟨rfl, rfl, by rw [hs]; exact chainTick_of_watch_false ht'⟩
  | compare _ _ hc' =>
    simp only [ScanVM.toJoint] at hc'
    omega

/-- A matched comparison of the joint machine (clock one, R available, L and
R agree after the move, chain watch ticks) is the controller's `scan_match`
with the output refreshed from `onLetter`/`leftFirst`. -/
theorem compare_lift (onLetter leftFirst : ScanVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : ScanVM) (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w) (t : JointState)
    (ht : JointTick delay true (s.toJoint w c.clock) t) (hcl : t.clock = delay) :
    ∃ o : Bool, GalilScaffoldTop.Tick (scanFrame onLetter leftFirst) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false}, ScanVM.ofJoint t⟩ := by
  classical
  cases ht with
  | count _ _ hc' =>
    simp only [ScanVM.toJoint] at hc'
    exact absurd hc hc'
  | compare _ w' _ hr' hm' ht' =>
    let s'' : ScanVM := ScanVM.ofJoint ⟨left s.left, right s.right, w', delay⟩
    refine ⟨if onLetter s'' then decide (leftFirst s'') else c.output, ?_⟩
    have hr'' : (scanFrame onLetter leftFirst).available s := hr'
    have hm'' : read (left s.left) = read (right s.right) := hm'
    have h := GalilScaffoldTop.Tick.scan_match (F := scanFrame onLetter leftFirst) (delay := delay)
      c s s'' s'' (if onLetter s'' then decide (leftFirst s'') else c.output) hm (Or.inr hr'') hc
      ⟨rfl, rfl, by rw [hs, decide_eq_true hm'']; exact chainTick_of_watch_true ht'⟩ hm' rfl ?_
    · rw [hr] at h
      exact h
    · refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = true ↔ leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = c.output
        rw [if_neg hl']

/-- A chain break at a matched comparison is also the controller's
`scan_match`: the outer symbols agree, the chain records the break. -/
theorem break_lift (onLetter leftFirst : ScanVM → Prop) (delay : ℕ) (c : Control)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : ScanVM) (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w) (t : JointState)
    (ht : JointBreak delay (s.toJoint w c.clock) t) :
    ∃ o : Bool, GalilScaffoldTop.Tick (scanFrame onLetter leftFirst) delay ⟨c, s⟩
      ⟨{c with clock := delay, output := o, replaying := false},
        ⟨left s.left, right s.right, .broken ⟨consume w.machine, w.lag, GalilScaffoldCounter.inc w.margin⟩⟩⟩ := by
  classical
  cases ht with
  | intro hc' hr' hm' hz hv a ha hne =>
    let s'' : ScanVM := ⟨left s.left, right s.right,
      .broken ⟨consume w.machine, w.lag, GalilScaffoldCounter.inc w.margin⟩⟩
    refine ⟨if onLetter s'' then decide (leftFirst s'') else c.output, ?_⟩
    have hr'' : (scanFrame onLetter leftFirst).available s := hr'
    have hm'' : read (left s.left) = read (right s.right) := hm'
    have hcmp : (scanFrame onLetter leftFirst).compare s s'' :=
      ⟨rfl, rfl, by rw [hs, decide_eq_true hm'']; exact chainTick_of_break ⟨hz, hv, a, ha, hne, rfl⟩⟩
    have h := GalilScaffoldTop.Tick.scan_match (F := scanFrame onLetter leftFirst) (delay := delay)
      c s s'' s'' (if onLetter s'' then decide (leftFirst s'') else c.output) hm (Or.inr hr'') hc
      hcmp hm' rfl ?_
    · rw [hr] at h
      exact h
    · refine ⟨fun hl => ?_, fun hl => ?_⟩
      · have hl' : onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = true ↔ leftFirst s''
        rw [if_pos hl']
        exact decide_eq_true_iff
      · have hl' : ¬ onLetter s'' := hl
        show (if onLetter s'' then decide (leftFirst s'') else c.output) = c.output
        rw [if_neg hl']

#print axioms count_lift
#print axioms compare_lift
#print axioms break_lift

end PalPeg.GalilScaffoldChainInputSupply
