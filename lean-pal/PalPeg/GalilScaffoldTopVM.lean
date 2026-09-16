import PalPeg.GalilScaffoldTopLens
import PalPeg.GalilScaffoldTopScan
import PalPeg.GalilScaffoldTopRewind

/-!
# The unified VM of the online Galil scaffold and its lenses

`ScaffoldGalil.scala` keeps, beside the finite controller record, the heads
R/L/C/W/V, the counters `length`/`radius`/`remaining`/`replay`, the search
and chain views and the FPP program view. `GalilVM` collects the components
used by the per-mode frames; each per-mode VM is a lens projection of it, so
`Frame.pull` and `steps_pull` place the per-mode phase theorems on one state.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldInputHead

structure GalilVM where
  left : PlaceHead
  center : PlaceHead
  right : PlaceHead
  chain : ChainVM
  cycle : GalilScaffoldCounter.Counter
  remaining : GalilScaffoldCounter.Counter
  radius : GalilScaffoldCounter.Counter
  length : GalilScaffoldCounter.Counter
  replay : GalilScaffoldCounter.Counter
  fpp : FppControl.State
  /-- The search view: scheduling state, DP program, lower bound. -/
  search : GalilScaffoldSearchFinish.State
  dp : GalilScaffoldControl.Machine 12
  lower : GalilScaffoldCounter.Counter
  /-- Scala's `periodOnly`: the two-semiperiod continuation after a shift decision. -/
  periodOnly : Bool
  /-- The search's walker place (`prepareWindow`'s copy cursor). -/
  walker : GalilScaffoldPlace.Place

def scanLens : Lens GalilVM ScanVM where
  get := fun s => ⟨s.left, s.right, s.chain⟩
  set := fun s v => {s with left := v.left, right := v.right, chain := v.chain}
  get_set := by intro s v; rfl
  set_get := by intro s; rfl
  set_set := by intro s v w; rfl

def shiftLens : Lens GalilVM ShiftVM where
  get := fun s => ⟨⟨s.center, s.left, s.remaining, s.radius, s.length⟩, s.chain, s.cycle⟩
  set := fun s v => {s with center := v.shift.center, left := v.shift.left, remaining := v.shift.remaining, radius := v.shift.radius, length := v.shift.length, chain := v.chain, cycle := v.cycle}
  get_set := by intro s v; rfl
  set_get := by intro s; rfl
  set_set := by intro s v w; rfl

def fppLens : Lens GalilVM FppControl.State where
  get := fun s => s.fpp
  set := fun s v => {s with fpp := v}
  get_set := by intro s v; rfl
  set_get := by intro s; rfl
  set_set := by intro s v w; rfl

structure SearchVM where
  search : GalilScaffoldSearchFinish.State
  dp : GalilScaffoldControl.Machine 12
  lower : GalilScaffoldCounter.Counter
  walker : GalilScaffoldPlace.Place

def searchLens : Lens GalilVM SearchVM where
  get := fun s => ⟨s.search, s.dp, s.lower, s.walker⟩
  set := fun s v => {s with search := v.search, dp := v.dp, lower := v.lower, walker := v.walker}
  get_set := by intro s v; rfl
  set_get := by intro s; rfl
  set_set := by intro s v w; rfl

def rewindLens : Lens GalilVM RewindVM where
  get := fun s => ⟨s.fpp, s.left, s.center, s.right, s.length, s.radius⟩
  set := fun s v => {s with fpp := v.fpp, left := v.left, center := v.center, right := v.right, length := v.length, radius := v.radius}
  get_set := by intro s v; rfl
  set_get := by intro s; rfl
  set_set := by intro s v w; rfl

/-- The shift phase on the unified VM. -/
theorem shift_phase_vm (onLetter leftFirst : ShiftVM → Prop) (delay : ℕ) (c : GalilScaffoldController.Control)
    (hm : c.mode = .shift) (s : GalilVM) (w : GalilScaffoldChainWatch.State) (hs : s.chain = .watch w)
    {n : ℕ} {t : ShiftState} {v : GalilScaffoldChainWatch.State}
    {finish : GalilScaffoldCounter.Counter}
    (hr : ChainShiftRun ⟨s.center, s.left, s.remaining, s.radius, s.length⟩ w s.cycle n t v finish)
    (hz : GalilScaffoldCounter.positive t.remaining = false) :
    ∃ o : Bool, Steps (Frame.pull shiftLens (shiftFrame onLetter leftFirst)) delay (n+1) ⟨c, s⟩
      ⟨{c with mode := .scan, output := o}, shiftLens.set s ⟨t, .watch v, finish⟩⟩ := by
  obtain ⟨o, h⟩ := shift_phase_lift onLetter leftFirst delay c hm hr hz
  rw [← hs] at h
  exact ⟨o, steps_pull shiftLens _ delay (n+1) c _ s _ h⟩

/-- The fpp phase on the unified VM. -/
theorem fpp_phase_vm (q : ℕ) (hq : 0 < q) (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop)
    (delay : ℕ) (c : GalilScaffoldController.Control) (hm : c.mode = .fpp) (s : GalilVM)
    (hx : s.fpp.mode = .run) (w : List (Fin 3)) (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    ∃ (n : ℕ) (p : GalilScaffoldControl.Machine 9) (y : FppControl.State),
      Steps (Frame.pull fppLens (fppFrame q first onLetter leftFirst)) delay (n+1) ⟨c, s⟩
        ⟨{c with mode := .markEnd}, {s with fpp := y}⟩ ∧
      y.program = markNew p first ∧ y.mode = .run ∧ y.walker = s.fpp.walker ∧ y.work = s.fpp.work ∧
      y.finalStage = s.fpp.finalStage ∧ p.done = true ∧
      GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program (List.replicate ((n+1)*q) true) p := by
  obtain ⟨n, p, y, hs, hprog, hmode, hw, hk, hf, hd, hrun⟩ :=
    fpp_phase_scheduled q hq first onLetter leftFirst delay c hm s.fpp hx w hp
  exact ⟨n, p, y, steps_pull fppLens _ delay (n+1) c _ s y hs, hprog, hmode, hw, hk, hf, hd, hrun⟩

/-- The markEnd phase on the unified VM. -/
theorem markEnd_phase_vm (first : Fin 9) (onLetter leftFirst : FppControl.State → Prop) (delay : ℕ)
    (c : GalilScaffoldController.Control) (hm : c.mode = .markEnd) (s : GalilVM) (k : ℕ)
    (hne : ∀ j, j < k → GalilScaffoldTape.denote (marksTape s.fpp) (GalilScaffoldTape.head (marksTape s.fpp) + j) ≠ 5)
    (hend : GalilScaffoldTape.denote (marksTape s.fpp) (GalilScaffoldTape.head (marksTape s.fpp) + k) = 5)
    (hpos : 0 < GalilScaffoldTape.head (marksTape s.fpp) + k) :
    ∃ y, Steps (Frame.pull fppLens (marksFrame first onLetter leftFirst)) delay (k+1) ⟨c, s⟩
        ⟨{c with mode := .choose, odd := false}, {s with fpp := y}⟩ ∧ MarksSame s.fpp y ∧
      GalilScaffoldTape.head (marksTape y) = GalilScaffoldTape.head (marksTape s.fpp) + k - 1 := by
  obtain ⟨y, hs, hsame, hhead⟩ := markEnd_phase first onLetter leftFirst delay c hm s.fpp k hne hend hpos
  exact ⟨y, steps_pull fppLens _ delay (k+1) c _ s y hs, hsame, hhead⟩

/-- The choose phase on the unified VM. -/
theorem choose_phase_vm (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : GalilScaffoldController.Control) (hm : c.mode = .choose) (s : GalilVM) (k : ℕ)
    (hk : k ≤ GalilScaffoldTape.head (rewindLens.get s).marks)
    (hno : ∀ j, j < k → ¬ (oddAt c.odd j = true ∧ SetAt first (rewindLens.get s) j))
    (hodd : oddAt c.odd k = true) (hset : SetAt first (rewindLens.get s) k) :
    ∃ y : RewindVM, Steps (Frame.pull rewindLens (rewindFrame first onLetter leftFirst)) delay (k+1) ⟨c, s⟩
        ⟨{c with odd := oddAt c.odd k, mode := .rewind, pair := false}, rewindLens.set s y⟩ ∧
      MarksSame s.fpp y.fpp ∧ y.left = s.right ∧ y.center = s.right ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.ofNat 1 ∧ y.radius = GalilScaffoldCounter.reset ∧
      GalilScaffoldTape.head y.marks = GalilScaffoldTape.head (rewindLens.get s).marks - k := by
  obtain ⟨y, hs, hsame, hl, hc, hr, hlen, hrad, hhead⟩ :=
    choose_phase first onLetter leftFirst delay c hm (rewindLens.get s) k hk hno hodd hset
  exact ⟨y, steps_pull rewindLens _ delay (k+1) c _ s y hs, hsame, hl, hc, hr, hlen, hrad, hhead⟩

/-- The rewind phase on the unified VM. -/
theorem rewind_phase_vm (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : GalilScaffoldController.Control) (hm : c.mode = .rewind) (hp : c.pair = false) (s : GalilVM) (m : ℕ)
    (hk : m ≤ GalilScaffoldTape.head (rewindLens.get s).marks)
    (hno : ∀ j, j < m → GalilScaffoldTape.denote (rewindLens.get s).marks
      (GalilScaffoldTape.head (rewindLens.get s).marks - j) ≠ first)
    (hfirst : GalilScaffoldTape.denote (rewindLens.get s).marks
      (GalilScaffoldTape.head (rewindLens.get s).marks - m) = first) :
    ∃ y : RewindVM, Steps (Frame.pull rewindLens (rewindFrame first onLetter leftFirst)) delay (m+1) ⟨c, s⟩
        ⟨{c with pair := pairAt m, mode := .replayStart}, rewindLens.set s y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[m] s.left ∧
      y.center = GalilScaffoldInputHead.left^[m/2] s.center ∧ y.right = s.right ∧
      y.length = GalilScaffoldCounter.inc^[m] s.length ∧
      y.radius = GalilScaffoldCounter.inc^[m/2] s.radius ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program := by
  obtain ⟨y, hs, hl, hc, hr, hlen, hrad, hprog⟩ :=
    rewind_phase first onLetter leftFirst delay c hm hp (rewindLens.get s) m hk hno hfirst
  exact ⟨y, steps_pull rewindLens _ delay (m+1) c _ s y hs, hl, hc, hr, hlen, hrad, hprog⟩

#print axioms choose_phase_vm
#print axioms rewind_phase_vm

#print axioms shift_phase_vm
#print axioms fpp_phase_vm
#print axioms markEnd_phase_vm

end PalPeg.GalilScaffoldChainInputSupply
