import PalPeg.GalilScaffoldTopMarks

/-!
# Choose- and Rewind-mode instantiation of the controller frame

`stepChoose` walks the MARKS tape to the left from the cell before END,
toggling `odd` at every step, and selects the first cell read with
`odd && (marks == "1" || marks == FIRST)`; then L and C are copied from R,
`length := 1`, `radius := 0`, `pair := 0`. `stepRewind` walks left to the
FIRST cell moving L one place per step and C every second step (`radius++`),
`length++` per step; at FIRST it resets the FPP program and enters
`ReplayStart`. This module instantiates those predicates on a VM with the
FPP state, the three heads and the two counters, and proves both walks.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

structure RewindVM where
  fpp : FppControl.State
  left : PlaceHead
  center : PlaceHead
  right : PlaceHead
  length : GalilScaffoldCounter.Counter
  radius : GalilScaffoldCounter.Counter

def RewindVM.marks (x : RewindVM) : GalilScaffoldTape.Tape := marksTape x.fpp

def rewindFrame (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) : Frame RewindVM where
  init := fun _ _ => False
  available := fun _ => False
  background := fun _ _ => False
  compare := fun _ _ => False
  matched := fun _ => False
  shiftGuard := fun _ => False
  matchedPlace := fun _ _ _ => False
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
  atEnd := fun x => x.marks.focus = 5
  markBack := fun x y => x.marks.left ≠ [] ∧ y = {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft}
  markForward := fun x y => y = {x with fpp := markStep x.fpp GalilScaffoldTape.moveRight}
  markSet := fun x => x.marks.focus = 8 ∨ x.marks.focus = first
  choose := fun x y => y = {x with left := x.right, center := x.right, length := GalilScaffoldCounter.ofNat 1, radius := GalilScaffoldCounter.reset}
  atFirst := fun x => x.marks.focus = first
  fppReset := fun x y => y = {x with fpp := {x.fpp with program := GalilScaffoldControl.reset 320 x.fpp.program}}
  rewindOne := fun x y => x.marks.left ≠ [] ∧
    y = {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left x.left, length := GalilScaffoldCounter.inc x.length}
  rewindPair := fun x y => x.marks.left ≠ [] ∧
    y = {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left x.left, length := GalilScaffoldCounter.inc x.length, center := GalilScaffoldInputHead.left x.center, radius := GalilScaffoldCounter.inc x.radius}
  replayStart := fun _ _ => False
  replayPos := fun _ => false
  restart := fun _ _ => False

/-- The cell `j` places left of the head is a selectable mark. -/
def SetAt (first : Fin 9) (x : RewindVM) (j : ℕ) : Prop :=
  GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - j) = 8 ∨
  GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - j) = first

/-- The `odd` flag after `k` toggles. -/
def oddAt (o : Bool) (k : ℕ) : Bool := if k % 2 = 0 then o else !o

theorem oddAt_succ (o : Bool) (k : ℕ) : oddAt o (k+1) = !oddAt o k := by
  unfold oddAt
  by_cases h : k % 2 = 0
  · have h' : (k+1) % 2 ≠ 0 := by omega
    simp [h, h']
  · have h' : (k+1) % 2 = 0 := by omega
    simp [h, h']

/-- Preservation of the VM apart from the MARKS head during the choose walk. -/
structure ChooseSame (x y : RewindVM) : Prop where
  fpp : MarksSame x.fpp y.fpp
  left : y.left = x.left
  center : y.center = x.center
  right : y.right = x.right
  length : y.length = x.length
  radius : y.radius = x.radius

theorem ChooseSame.refl (x : RewindVM) : ChooseSame x x := ⟨MarksSame.refl _, rfl, rfl, rfl, rfl, rfl⟩

theorem ChooseSame.trans {x y z : RewindVM} (h1 : ChooseSame x y) (h2 : ChooseSame y z) : ChooseSame x z :=
  ⟨h1.fpp.trans h2.fpp, h2.left.trans h1.left, h2.center.trans h1.center, h2.right.trans h1.right,
    h2.length.trans h1.length, h2.radius.trans h1.radius⟩

theorem back_same (x : RewindVM) :
    ChooseSame x {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft} :=
  ⟨markStep_same x.fpp _ (GalilScaffoldTape.left_denote _), rfl, rfl, rfl, rfl, rfl⟩

theorem focus_of_same {x y : RewindVM} (h : ChooseSame x y) (k : ℕ)
    (hh : GalilScaffoldTape.head y.marks = GalilScaffoldTape.head x.marks - k) :
    y.marks.focus = GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - k) := by
  rw [← GalilScaffoldTape.focus_eq]
  show GalilScaffoldTape.denote (marksTape y.fpp) (GalilScaffoldTape.head (marksTape y.fpp)) = _
  rw [h.fpp.denote]
  show GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head y.marks) = _
  rw [hh]

/-- Walking left over `k` cells none of which is selected: `k` `choose_step`
ticks, `odd` toggled `k` times, head moved left by `k`. -/
theorem choose_walk (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .choose) (x : RewindVM) :
    ∀ k, k ≤ GalilScaffoldTape.head x.marks →
      (∀ j, j < k → ¬ (oddAt c.odd j = true ∧ SetAt first x j)) →
      ∃ y : RewindVM, Steps (rewindFrame first onLetter leftFirst) delay k ⟨c, x⟩
          ⟨{c with odd := oddAt c.odd k}, y⟩ ∧ ChooseSame x y ∧
        GalilScaffoldTape.head y.marks = GalilScaffoldTape.head x.marks - k := by
  intro k
  induction k with
  | zero =>
    intro _ _
    refine ⟨x, ?_, ChooseSame.refl _, rfl⟩
    have : ({c with odd := oddAt c.odd 0} : Control) = c := by simp [oddAt]
    rw [this]; exact .zero _
  | succ k ih =>
    intro hk hno
    obtain ⟨y, hs, hsame, hhead⟩ := ih (by omega) (fun j hj => hno j (by omega))
    have hfocus := focus_of_same hsame k hhead
    have hleft : y.marks.left ≠ [] := by
      rw [GalilScaffoldTape.left_legal, hhead]; omega
    have hsel : ({c with odd := oddAt c.odd k} : Control).odd = false ∨
        ¬ (rewindFrame first onLetter leftFirst).markSet y := by
      have h := hno k (by omega)
      cases ho : oddAt c.odd k
      · exact Or.inl rfl
      · right
        intro hset
        apply h
        refine ⟨ho, ?_⟩
        show GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - k) = 8 ∨
          GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - k) = first
        rw [← hfocus]
        exact hset
    refine ⟨{y with fpp := markStep y.fpp GalilScaffoldTape.moveLeft}, ?_, hsame.trans (back_same y), ?_⟩
    · have ht := GalilScaffoldTop.Tick.choose_step (F := rewindFrame first onLetter leftFirst) (delay := delay)
        {c with odd := oddAt c.odd k} y _ hm hsel ⟨hleft, rfl⟩
      have he : ({({c with odd := oddAt c.odd k} : Control) with odd := !oddAt c.odd k} : Control) =
          {c with odd := oddAt c.odd (k+1)} := by
        rw [oddAt_succ]
      rw [he] at ht
      exact steps_trans hs (.succ ht (.zero _))
    · show GalilScaffoldTape.head (marksTape (markStep y.fpp GalilScaffoldTape.moveLeft)) = _
      rw [markStep_tape, GalilScaffoldTape.left_head _ (by show 0 < GalilScaffoldTape.head y.marks; rw [hhead]; omega)]
      show GalilScaffoldTape.head y.marks - 1 = _
      rw [hhead]; omega

/-- The Choose phase: the first selectable odd cell is `k` places left of
the head. `k+1` ticks later the controller is in `rewind` mode with
`pair = false`, L and C copied from R, `length = 1`, `radius = 0`, and the
MARKS head on the selected cell. -/
theorem choose_phase (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .choose) (x : RewindVM) (k : ℕ)
    (hk : k ≤ GalilScaffoldTape.head x.marks)
    (hno : ∀ j, j < k → ¬ (oddAt c.odd j = true ∧ SetAt first x j))
    (hodd : oddAt c.odd k = true) (hset : SetAt first x k) :
    ∃ y : RewindVM, Steps (rewindFrame first onLetter leftFirst) delay (k+1) ⟨c, x⟩
        ⟨{c with odd := oddAt c.odd k, mode := .rewind, pair := false}, y⟩ ∧
      MarksSame x.fpp y.fpp ∧ y.left = x.right ∧ y.center = x.right ∧ y.right = x.right ∧
      y.length = GalilScaffoldCounter.ofNat 1 ∧ y.radius = GalilScaffoldCounter.reset ∧
      GalilScaffoldTape.head y.marks = GalilScaffoldTape.head x.marks - k := by
  obtain ⟨y, hs, hsame, hhead⟩ := choose_walk first onLetter leftFirst delay c hm x k hk hno
  have hfocus := focus_of_same hsame k hhead
  have hset' : (rewindFrame first onLetter leftFirst).markSet y := by
    show y.marks.focus = 8 ∨ y.marks.focus = first
    rw [hfocus]; exact hset
  refine ⟨{y with left := y.right, center := y.right, length := GalilScaffoldCounter.ofNat 1, radius := GalilScaffoldCounter.reset},
    ?_, hsame.fpp, hsame.right, hsame.right, hsame.right, rfl, rfl, hhead⟩
  exact steps_trans hs (.succ (GalilScaffoldTop.Tick.choose_select {c with odd := oddAt c.odd k} y _ hm hodd hset' rfl) (.zero _))

#print axioms choose_phase

/-- The `pair` flag after `m` rewind steps. -/
def pairAt (m : ℕ) : Bool := decide (m % 2 = 1)

/-- Walking left over `m` non-FIRST cells in rewind mode: L moves `m` places,
C every second step, `length += m`, `radius += m/2`. -/
theorem rewind_walk (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .rewind) (hp : c.pair = false) (x : RewindVM) :
    ∀ m, m ≤ GalilScaffoldTape.head x.marks →
      (∀ j, j < m → GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - j) ≠ first) →
      ∃ y : RewindVM, Steps (rewindFrame first onLetter leftFirst) delay m ⟨c, x⟩
          ⟨{c with pair := pairAt m}, y⟩ ∧ MarksSame x.fpp y.fpp ∧
        y.left = GalilScaffoldInputHead.left^[m] x.left ∧
        y.center = GalilScaffoldInputHead.left^[m/2] x.center ∧ y.right = x.right ∧
        y.length = GalilScaffoldCounter.inc^[m] x.length ∧
        y.radius = GalilScaffoldCounter.inc^[m/2] x.radius ∧
        GalilScaffoldTape.head y.marks = GalilScaffoldTape.head x.marks - m := by
  intro m
  induction m with
  | zero =>
    intro _ _
    refine ⟨x, ?_, MarksSame.refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have : ({c with pair := pairAt 0} : Control) = c := by
      cases c; simp [pairAt, hp] at *; assumption
    rw [this]; exact .zero _
  | succ m ih =>
    intro hk hno
    obtain ⟨y, hs, hsame, hl, hc, hr, hlen, hrad, hhead⟩ := ih (by omega) (fun j hj => hno j (by omega))
    have hfocus : y.marks.focus ≠ first := by
      rw [← GalilScaffoldTape.focus_eq]
      show GalilScaffoldTape.denote (marksTape y.fpp) (GalilScaffoldTape.head (marksTape y.fpp)) ≠ _
      rw [hsame.denote]
      show GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head y.marks) ≠ _
      rw [hhead]; exact hno m (by omega)
    have hleft : y.marks.left ≠ [] := by
      rw [GalilScaffoldTape.left_legal, hhead]; omega
    have hheadstep : GalilScaffoldTape.head (marksTape (markStep y.fpp GalilScaffoldTape.moveLeft)) =
        GalilScaffoldTape.head x.marks - (m+1) := by
      rw [markStep_tape, GalilScaffoldTape.left_head _ (by show 0 < GalilScaffoldTape.head y.marks; rw [hhead]; omega)]
      show GalilScaffoldTape.head y.marks - 1 = _
      rw [hhead]; omega
    have hfsame := hsame.trans (markStep_same y.fpp _ (GalilScaffoldTape.left_denote _))
    by_cases he : m % 2 = 0
    · -- pair = false: L only
      have hpa : pairAt m = false := by simp [pairAt]; omega
      have hpa' : pairAt (m+1) = true := by simp [pairAt]; omega
      refine ⟨{y with fpp := markStep y.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left y.left, length := GalilScaffoldCounter.inc y.length},
        ?_, hfsame, ?_, ?_, hr, ?_, ?_, hheadstep⟩
      · have ht := GalilScaffoldTop.Tick.rewind_one (F := rewindFrame first onLetter leftFirst) (delay := delay)
          {c with pair := pairAt m} y _ hm hfocus hpa ⟨hleft, rfl⟩
        rw [← hpa'] at ht
        exact steps_trans hs (.succ ht (.zero _))
      · rw [hl, Function.iterate_succ_apply']
      · rw [hc]; congr 1; omega
      · rw [hlen, Function.iterate_succ_apply']
      · rw [hrad]; congr 1; omega
    · -- pair = true: L and C
      have hpa : pairAt m = true := by simp [pairAt]; omega
      have hpa' : pairAt (m+1) = false := by simp [pairAt]; omega
      refine ⟨{y with fpp := markStep y.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left y.left, length := GalilScaffoldCounter.inc y.length, center := GalilScaffoldInputHead.left y.center, radius := GalilScaffoldCounter.inc y.radius},
        ?_, hfsame, ?_, ?_, hr, ?_, ?_, hheadstep⟩
      · have ht := GalilScaffoldTop.Tick.rewind_pair (F := rewindFrame first onLetter leftFirst) (delay := delay)
          {c with pair := pairAt m} y _ hm hfocus hpa ⟨hleft, rfl⟩
        rw [← hpa'] at ht
        exact steps_trans hs (.succ ht (.zero _))
      · rw [hl, Function.iterate_succ_apply']
      · rw [hc, show (m+1)/2 = m/2 + 1 by omega, Function.iterate_succ_apply']
      · rw [hlen, Function.iterate_succ_apply']
      · rw [hrad, show (m+1)/2 = m/2 + 1 by omega, Function.iterate_succ_apply']

/-- The Rewind phase: FIRST is `m` cells left of the head. `m+1` ticks later
the controller is in `replayStart` mode with the FPP program reset. -/
theorem rewind_phase (first : Fin 9) (onLetter leftFirst : RewindVM → Prop) (delay : ℕ)
    (c : Control) (hm : c.mode = .rewind) (hp : c.pair = false) (x : RewindVM) (m : ℕ)
    (hk : m ≤ GalilScaffoldTape.head x.marks)
    (hno : ∀ j, j < m → GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - j) ≠ first)
    (hfirst : GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head x.marks - m) = first) :
    ∃ y : RewindVM, Steps (rewindFrame first onLetter leftFirst) delay (m+1) ⟨c, x⟩
        ⟨{c with pair := pairAt m, mode := .replayStart}, y⟩ ∧
      y.left = GalilScaffoldInputHead.left^[m] x.left ∧
      y.center = GalilScaffoldInputHead.left^[m/2] x.center ∧ y.right = x.right ∧
      y.length = GalilScaffoldCounter.inc^[m] x.length ∧
      y.radius = GalilScaffoldCounter.inc^[m/2] x.radius ∧
      y.fpp.program = GalilScaffoldControl.reset 320 y.fpp.program := by
  obtain ⟨y, hs, hsame, hl, hc, hr, hlen, hrad, hhead⟩ :=
    rewind_walk first onLetter leftFirst delay c hm hp x m hk hno
  have hfocus : y.marks.focus = first := by
    rw [← GalilScaffoldTape.focus_eq]
    show GalilScaffoldTape.denote (marksTape y.fpp) (GalilScaffoldTape.head (marksTape y.fpp)) = _
    rw [hsame.denote]
    show GalilScaffoldTape.denote x.marks (GalilScaffoldTape.head y.marks) = _
    rw [hhead]; exact hfirst
  refine ⟨{y with fpp := {y.fpp with program := GalilScaffoldControl.reset 320 y.fpp.program}},
    ?_, hl, hc, hr, hlen, hrad, rfl⟩
  exact steps_trans hs (.succ (GalilScaffoldTop.Tick.rewind_done {c with pair := pairAt m} y _ hm hfocus rfl) (.zero _))

#print axioms rewind_phase

end PalPeg.GalilScaffoldChainInputSupply
