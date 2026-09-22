import PalPeg.ReplayStartGhost

/-!
# A section of the abstraction of the local layer

`LocalReplayParked.absState''` forgets the queues, the idle buffers, the mirrors and the physical
tapes behind the counters.  Here it is given a section on the states that can be abstractions:
`ghostOf roles background c t parked` is a local state with `absState'' = ⟨c, t⟩`
(`absState''_ghostOf`), when the counters of `t` are canonical and its right head stands
`replay` places to the left of `parked`.  The physical pack and the mirror of the centre hold of
it (`physWF_ghostOf`), and a canonical counter that is not negative gets the positive polarity
(`polOf_of_nonneg`).

The abstract local layer is a ghost of the proof, so a successor of a scan state need not be
computed from its source: it is the section of the next state of the trace.

The sections of `absCtr` (`ctrOf`) and of `absPlace` (`viewOfPlace`) were first written for the
tape encoder (`CloseoutCoreEnc2`), which re-exports them.
-/

set_option autoImplicit false
namespace PalPeg.GhostSection

open PalPeg PalPeg.LocalState PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply GalilScaffoldInputHead
open PalPeg.GalilScaffoldCounter (Counter Canonical ofNat)
open PalPeg.GalilScaffoldPlace (Place)
open PalPeg.LocalCounter (Seg SegCtr)
open PalPeg.Program (STape)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (absHead' abs')
open PalPeg.LocalReplayParked (Mirrored1 MirInv1 abs'' absState'' absR rval physHead ParkedOK)
open PalPeg.LocalSysConcrete (PhysWF)

/-! ## 1. A section of the counter abstraction

`LocalCounter.absCtr` lands in the canonical counters only, so it can only be sectioned there —
but on those it can be, explicitly. -/

/-- The counter tape holding the unary value `n`: `n` marks above a separator. -/
def ctrTapeSeg (n : ℕ) : STape Seg :=
  ⟨List.replicate n LocalCounter.mark ++ [LocalCounter.sep], LocalCounter.blank, []⟩

@[simp] theorem val_ctrTapeSeg (n : ℕ) : LocalCounter.val (ctrTapeSeg n) = n :=
  LocalCounter.markRun_replicate_sep n []

theorem segCtr_ctrTapeSeg (n : ℕ) : LocalCounter.SegCtr (ctrTapeSeg n) n := ⟨[], rfl⟩

/-- Every list of units is a replicate of its own length. -/
theorem list_unit_eq (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a t ih => cases a; simpa [List.replicate_succ] using congrArg (fun x => () :: x) ih

/-- The tape/sign pair representing a canonical counter. -/
def ctrOf (c : Counter) : STape Seg × Bool :=
  (ctrTapeSeg (if c.neg.isEmpty then c.pos.length else c.neg.length), c.neg.isEmpty)

/-- **A section of `absCtr` on the canonical counters.** -/
theorem absCtr_ctrOf {c : Counter} (hc : Canonical c) :
    LocalCounter.absCtr (ctrOf c).1 (ctrOf c).2 = c := by
  rcases c with ⟨ps, ns⟩
  cases ns with
  | cons b ns' =>
      have hp : ps = [] := by
        rcases hc with h | h
        · exact h
        · exact absurd h (by simp)
      subst hp
      simp only [ctrOf, LocalCounter.absCtr, List.isEmpty_cons, Bool.false_eq_true,
        if_false, val_ctrTapeSeg, LocalCounter.negOfNat]
      exact congrArg (fun l => (⟨[], l⟩ : Counter)) (list_unit_eq (b :: ns')).symm
  | nil =>
      simp only [ctrOf, LocalCounter.absCtr, List.isEmpty_nil, if_true,
        val_ctrTapeSeg, ofNat]
      exact congrArg (fun l => (⟨l, []⟩ : Counter)) (list_unit_eq ps).symm

/-! ## 2. A section of `absPlace` -/

/-- The cursor representing a `Place`: the letters to the left of the head, with
the `none` sentinel closing the run. -/
def viewOfPlace (p : Place) : InputView :=
  match p.letters with
  | [] => ⟨[], none, [], RTQueue.empty, p.gap⟩
  | a :: t => ⟨t.map some ++ [none], some a, [], RTQueue.empty, p.gap⟩

theorem placeLetters_map (t : List (Fin 2)) :
    LocalState.placeLetters (t.map some ++ [none]) = t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
      show a :: LocalState.placeLetters (t.map some ++ [none]) = a :: t
      rw [ih]

/-- **A section of `absPlace`.** -/
theorem absPlace_viewOfPlace (p : Place) : LocalState.absPlace (viewOfPlace p) = p := by
  rcases p with ⟨letters, g⟩
  cases letters with
  | nil => rfl
  | cons a t =>
      show (⟨LocalState.placeLetters (some a :: (t.map some ++ [none])), g⟩ : Place)
        = ⟨a :: t, g⟩
      rw [show LocalState.placeLetters (some a :: (t.map some ++ [none]))
            = a :: LocalState.placeLetters (t.map some ++ [none]) from rfl,
        placeLetters_map]

variable {P : ℕ}

/-! ### heads -/

def queueOfList {α : Type} (l : List α) : RTQueue.Queue α := l.foldl RTQueue.snoc RTQueue.empty

theorem queueOfList_spec {α : Type} (l : List α) :
    RTQueue.Inv (queueOfList l) ∧ RTQueue.toList (queueOfList l) = l := by
  suffices hfold : ∀ (q : RTQueue.Queue α), RTQueue.Inv q →
      RTQueue.Inv (l.foldl RTQueue.snoc q) ∧
        RTQueue.toList (l.foldl RTQueue.snoc q) = RTQueue.toList q ++ l by
    have h := hfold RTQueue.empty RTQueue.inv_empty
    rw [RTQueue.toList_empty, List.nil_append] at h
    exact h
  induction l with
  | nil => intro q hq; exact ⟨hq, (List.append_nil _).symm⟩
  | cons a l ih =>
    intro q hq
    have h := ih (RTQueue.snoc q a) (RTQueue.inv_snoc hq a)
    rw [RTQueue.toList_snoc hq a, List.append_assoc] at h
    exact h

def viewOfHead (p : PlaceHead) : InputView :=
  ⟨p.head.left, p.head.focus, p.head.right, queueOfList p.head.incoming, p.gap⟩

theorem absHead'_viewOfHead (p : PlaceHead) : absHead' (viewOfHead p) [] = p := by
  rcases p with ⟨⟨f, l, r, q⟩, g⟩
  show (⟨⟨f, l, r, RTQueue.toList (queueOfList q) ++ []⟩, g⟩ : PlaceHead) = _
  rw [List.append_nil, (queueOfList_spec q).2]

theorem wf_viewOfHead (p : PlaceHead) : PalPeg.LocalInputView.WF (viewOfHead p) :=
  (queueOfList_spec p.head.incoming).1

/-! ### the counter bank -/

/-- The ten counters of an abstract state, by role. -/
def countersOf (s : GalilVM) : Ctr → Counter
  | .cycle => s.cycle
  | .remaining => s.remaining
  | .radius => s.radius
  | .length => s.length
  | .replay => s.replay
  | .lower => s.lower
  | .span => s.search.span
  | .work => s.search.work
  | .debt => s.search.debt
  | .fppWork => s.fpp.work

noncomputable def bankOf (roles : Ctr → Fin P) (background : Fin P → STape Seg)
    (counters : Ctr → Counter) : Fin P → STape Seg :=
  Function.extend roles (fun c => (ctrOf (counters c)).1) background

def polOf (counters : Ctr → Counter) : Ctr → Bool := fun c => (ctrOf (counters c)).2

theorem bankOf_role {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (counters : Ctr → Counter) (c : Ctr) :
    bankOf roles background counters (roles c) = (ctrOf (counters c)).1 :=
  hinj.extend_apply _ _ c

/-! ### the ghost -/

def bufferOf {n : ℕ} (tapes : Fin n → GalilScaffoldTape.Tape) : LocalBuffers.Buffered n :=
  ⟨tapes, tapes, true, none⟩

/-- A local state whose abstraction is `⟨c, t⟩`: the right view stands on `parked`. -/
noncomputable def ghostOf (roles : Ctr → Fin P) (background : Fin P → STape Seg) (c : Control)
    (t : GalilVM) (parked : PlaceHead) : Mirrored1 P :=
  ⟨{ left := viewOfHead t.left
     center := viewOfHead t.center
     right := viewOfHead parked
     pending := []
     walkerView := viewOfPlace t.walker
     fppWalker := viewOfPlace t.fpp.walker
     phys := bankOf roles background (countersOf t)
     roles := roles
     pol := polOf (countersOf t)
     radiusMir := PalPeg.ReplayStartGhost.mirrorOfTape
       (bankOf roles background (countersOf t) (roles .radius))
     lowerMir := PalPeg.ReplayStartGhost.mirrorOfTape
       (bankOf roles background (countersOf t) (roles .lower))
     lengthMir := PalPeg.ReplayStartGhost.mirrorOfTape
       (bankOf roles background (countersOf t) (roles .length))
     dpBuf := bufferOf t.dp.config.tapes
     dpPc := t.dp.config.pc
     dpDone := t.dp.done
     fppBuf := bufferOf t.fpp.program.config.tapes
     fppPc := t.fpp.program.config.pc
     fppDone := t.fpp.program.done
     chain := t.chain
     ctl := c
     searchMode := t.search.mode
     searchFinalStage := t.search.finalStage
     searchQuarter := t.search.quarter
     fppMode := t.fpp.mode
     fppFinalStage := t.fpp.finalStage
     periodOnly := t.periodOnly }, viewOfHead t.center⟩

theorem absCtrs_ghostOf {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (c : Control) {t : GalilVM} (parked : PlaceHead)
    (hcanonical : ∀ role, Canonical (countersOf t role)) (role : Ctr) :
    absCtrs (ghostOf roles background c t parked).vm role = countersOf t role := by
  show LocalCounter.absCtr (bankOf roles background (countersOf t) (roles role))
    (polOf (countersOf t) role) = _
  rw [bankOf_role hinj]
  exact absCtr_ctrOf (hcanonical role)

/-- The abstraction with the right head read off the view (`abs'`). -/
theorem abs'_ghostOf {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (c : Control) {t : GalilVM} (parked : PlaceHead)
    (hcanonical : ∀ role, Canonical (countersOf t role)) :
    abs' (ghostOf roles background c t parked).vm = { t with right := parked } := by
  have hctr := absCtrs_ghostOf hinj background c parked hcanonical
  rcases t with ⟨tl, tc, tr, tchain, tcycle, tremaining, tradius, tlength, treplay,
    ⟨fmode, fprogram, fwork, fwalker, ffinal⟩, ⟨smode, sfinal, sspan, swork, sdebt, squarter⟩,
    tdp, tlower, tperiodOnly, twalker⟩
  have h1 := hctr .cycle
  have h2 := hctr .remaining
  have h3 := hctr .radius
  have h4 := hctr .length
  have h5 := hctr .replay
  have h6 := hctr .lower
  have h7 := hctr .span
  have h8 := hctr .work
  have h9 := hctr .debt
  have h10 := hctr .fppWork
  show GalilVM.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = GalilVM.mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  congr 1
  · exact absHead'_viewOfHead _
  · exact absHead'_viewOfHead _
  · exact absHead'_viewOfHead _
  · show FppControl.State.mk _ _ _ _ _ = FppControl.State.mk _ _ _ _ _
    congr 1
    exact absPlace_viewOfPlace _
  · show GalilScaffoldSearchFinish.State.mk _ _ _ _ _ _ = GalilScaffoldSearchFinish.State.mk _ _ _ _ _ _
    congr 1
  · exact absPlace_viewOfPlace _

/-- The replay tape of the ghost holds the replay counter. -/
theorem rval_ghostOf {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (c : Control) {t : GalilVM} (parked : PlaceHead) {r : ℕ}
    (hreplay : t.replay = ofNat r) : rval (ghostOf roles background c t parked).vm = r := by
  show LocalCounter.val (bankOf roles background (countersOf t) (roles .replay)) = r
  rw [bankOf_role hinj]
  show LocalCounter.val (ctrOf t.replay).1 = r
  rw [hreplay]
  simp [ctrOf, ofNat]

/-- **The section.**  The abstraction of the ghost is the given state, when its counters are
canonical and its right head stands `replay` places to the left of `parked`. -/
theorem absState''_ghostOf {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (c : Control) {t : GalilVM} {parked : PlaceHead} {r : ℕ}
    (hcanonical : ∀ role, Canonical (countersOf t role))
    (hreplay : t.replay = ofNat r)
    (hright : t.right = GalilScaffoldInputHead.left^[r] parked)
    (hrest : c.replaying = false → r = 0) :
    absState'' (ghostOf roles background c t parked).vm = ⟨c, t⟩ := by
  have hhead : physHead (ghostOf roles background c t parked).vm = parked :=
    absHead'_viewOfHead parked
  have habsR : absR (ghostOf roles background c t parked).vm = t.right := by
    unfold absR
    rw [hhead, rval_ghostOf hinj background c parked hreplay, hright]
    show (if c.replaying = true then _ else _) = _
    cases hreplaying : c.replaying with
    | true => rw [if_pos rfl]
    | false =>
      rw [if_neg (by simp), hrest hreplaying]
      rfl
  show State.mk c (abs'' (ghostOf roles background c t parked).vm) = ⟨c, t⟩
  congr 1
  unfold abs''
  rw [abs'_ghostOf hinj background c parked hcanonical, habsR]

/-- The sentinel of the place cursors. -/
theorem anchored_map_some (a : Fin 2) (l : List (Fin 2)) :
    PalPeg.LocalChain.Anchored (some a) (l.map some ++ [none]) := by
  induction l generalizing a with
  | nil => show PalPeg.LocalChain.Anchored none []; rfl
  | cons b l ih => exact ih b

theorem properView_viewOfPlace (p : GalilScaffoldPlace.Place) :
    PalPeg.LocalChain.ProperView (viewOfPlace p) := by
  rcases p with ⟨letters, g⟩
  cases letters with
  | nil => show PalPeg.LocalChain.Anchored none []; rfl
  | cons a l => exact anchored_map_some a l

theorem wf_viewOfPlace (p : GalilScaffoldPlace.Place) :
    PalPeg.LocalInputView.WF (viewOfPlace p) := by
  rcases p with ⟨letters, g⟩
  cases letters <;> exact RTQueue.inv_empty

/-- The physical pack and the mirror of the centre hold of the ghost. -/
theorem physWF_ghostOf {roles : Ctr → Fin P} (hinj : Function.Injective roles)
    (background : Fin P → STape Seg) (c : Control) {t : GalilVM} {parked : PlaceHead} {r : ℕ}
    (hreplay : t.replay = ofNat r) (hparkedLe : r ≤ position parked) :
    PhysWF (ghostOf roles background c t parked).vm ∧
      MirInv1 (ghostOf roles background c t parked) := by
  have hshaped : ∀ role, ∃ v, SegCtr (bankOf roles background (countersOf t) (roles role)) v := by
    intro role
    rw [bankOf_role hinj]
    exact ⟨_, segCtr_ctrTapeSeg _⟩
  refine ⟨⟨⟨hinj, ⟨rfl, rfl, rfl⟩,
      ⟨wf_viewOfHead _, wf_viewOfHead _, wf_viewOfHead _, wf_viewOfPlace _, wf_viewOfPlace _⟩,
      ?_, ?_, ?_, hshaped⟩, ?_, rfl, properView_viewOfPlace _⟩,
    PalPeg.LocalReplaySwap.Twin.refl _, wf_viewOfHead _⟩
  · obtain ⟨v, hv⟩ := hshaped .radius
    exact ⟨v, hv, fun _ => hv⟩
  · obtain ⟨v, hv⟩ := hshaped .lower
    exact ⟨v, hv, fun _ => hv⟩
  · obtain ⟨v, hv⟩ := hshaped .length
    exact ⟨v, hv, fun _ => hv⟩
  · intro _
    rw [rval_ghostOf hinj background c parked hreplay]
    show r ≤ position (absHead' (viewOfHead parked) [])
    rw [absHead'_viewOfHead]
    exact hparkedLe

open PalPeg.GalilScaffoldCounter (value) in
/-- A canonical counter that is not negative sits on the positive side. -/
theorem polOf_of_nonneg {counters : Ctr → Counter} {role : Ctr}
    (hcanonical : Canonical (counters role)) (hnonneg : 0 ≤ value (counters role)) :
    polOf counters role = true := by
  show (ctrOf (counters role)).2 = true
  generalize counters role = counter at hcanonical hnonneg
  rcases counter with ⟨pos, neg⟩
  cases neg with
  | nil => rfl
  | cons a neg =>
    rcases hcanonical with hpos | hneg
    · simp only at hpos
      subst hpos
      simp [PalPeg.GalilScaffoldCounter.value] at hnonneg
      omega
    · exact absurd hneg (by simp)

#print axioms absState''_ghostOf
#print axioms physWF_ghostOf

end PalPeg.GhostSection
