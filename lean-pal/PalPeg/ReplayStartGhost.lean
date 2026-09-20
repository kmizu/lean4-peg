import PalPeg.LocalReplayParked
import PalPeg.LocalWF
import PalPeg.CloseoutRadPack3
import PalPeg.GalilTruncTick

/-!
# The ghost successor of a `replayStart` state

The abstract local layer is a ghost of the proof, so its `replayStart` step need not be a local
step of a machine.  This file gives the successor and the facts it rests on.

* **Trace side.**  In `rewind` and `replayStart` the centre head is the right head moved left by
  the radius (`RewindCentre`, kept by every tick and hence along a pre-loaded trace), and a tick
  that lands in `replayStart` comes from a `rewind` state that is not replaying.
* **Ghost side.**  `replayCommitVm` is `LocalTick2.commitReplay` with the left head copied from the
  centre head and the three mirror banks re-attached to the tapes their counters own after the
  commit (the commit exchanges the roles of `radius` and `replay`, resets and pushes tapes, and
  does not touch the mirrors, so by itself it does not keep `LocalTick1.Inv`).  It keeps the bank
  invariant, its abstraction is the `replayStartVM` landing, and the parked right head stays far
  enough from the origin.
* `replayStartVM` fixes every field of its landing, so the landing is unique.

What the physical machine does at this step (exchanging a mirror tape with the left tape,
flipping the dp buffer) is carried by the representation relation, not by this file.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.ReplayStartGhost

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (ofNat inc reset)
open PalPeg.LocalState
open PalPeg.LocalTick1 (Inv CountersShaped)
open PalPeg.LocalCounter (SegCtr Seg)
open PalPeg.LocalMirror (Mirrored Shaped)
open PalPeg.LocalReplayParked (Mirrored1)

variable {P : ℕ}

/-- In `rewind` and `replayStart` the centre head is the right head moved left by the
radius. -/
def RewindCentre (c : Control) (s : GalilVM) : Prop :=
  c.mode = .rewind ∨ c.mode = .replayStart →
    ∃ r : ℕ, s.radius = ofNat r ∧ s.center = GalilScaffoldInputHead.left^[r] s.right

theorem rewindCentre_tick (Pw : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (hsource : RewindCentre c s)
    (h : Tick (galilFrameS Pw q first) delay ⟨c, s⟩ ⟨c', t⟩) : RewindCentre c' t := by
  cases h <;> first
    | (intro hmode; exfalso; simp_all; done)
    | skip
  case choose_select hm ho hs hrel =>
    intro _
    obtain ⟨hstep, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨0, rfl, rfl⟩
  case rewind_done hm hf hrel =>
    intro _
    obtain ⟨r, hradius, hcentre⟩ := hsource (Or.inl hm)
    obtain ⟨hstep, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨r, hradius, hcentre⟩
  case rewind_one hm hf hp hrel =>
    intro _
    obtain ⟨r, hradius, hcentre⟩ := hsource (Or.inl hm)
    obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    exact ⟨r, hradius, hcentre⟩
  case rewind_pair hm hf hp hrel =>
    intro _
    obtain ⟨r, hradius, hcentre⟩ := hsource (Or.inl hm)
    obtain ⟨⟨_, hstep⟩, hframe⟩ := hrel
    rw [hstep] at hframe
    subst hframe
    refine ⟨r + 1, ?_, ?_⟩
    · show inc s.radius = ofNat (r + 1)
      rw [hradius, PalPeg.GalilScaffoldCounter.inc_ofNat]
    · show GalilScaffoldInputHead.left s.center = GalilScaffoldInputHead.left^[r + 1] s.right
      rw [Function.iterate_succ_apply', ← hcentre]

#print axioms rewindCentre_tick

open PalPeg.GalilFinalAssembly in
/-- The rewind centre invariant at every state of a pre-loaded trace. -/
theorem rewindCentre_trace (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → RewindCentre (st i).ctl (st i).vm := by
  intro i
  induction i with
  | zero =>
    intro _ hmode
    rw [hP.start] at hmode
    rcases hmode with h | h <;> exact Mode.noConfusion h
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    exact rewindCentre_tick _ q first 2048 (ih (by omega)) (hP.trace.tick i hlt)

#print axioms rewindCentre_trace

/-- A tick that lands in `replayStart` comes from a `rewind` state that is not replaying,
and keeps the flag. -/
theorem notReplaying_of_tick_into_replayStart {σ : Type} {F : Frame σ} {delay : ℕ}
    {x y : State σ} (hsource : PalPeg.LocalWF.NoReplay x) (h : Tick F delay x y)
    (hmode : y.ctl.mode = .replayStart) : y.ctl.replaying = false := by
  cases h <;> first
    | (exfalso; simp_all; done)
    | skip
  case rewind_done hm hf hrel =>
    exact hsource (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))))

#print axioms notReplaying_of_tick_into_replayStart

/-- A mirror bank that is the tape itself. -/
def mirrorOfTape {k : ℕ} (t : PalPeg.Program.STape Seg) : Mirrored k := ⟨t, fun _ => t⟩

/-- The ghost state after the replay commit, with the three mirror banks re-attached. -/
def replayCommitVm (entry : ℕ) (c : GalilScaffoldController.Control) (x : GalilVML P) :
    GalilVML P :=
  let y := LocalTick2.commitReplay entry x
  { y with
    left := x.center
    ctl := c
    radiusMir := mirrorOfTape (y.phys (y.roles .radius))
    lowerMir := mirrorOfTape (y.phys (y.roles .lower))
    lengthMir := mirrorOfTape (y.phys (y.roles .length)) }

theorem countersShaped_commitReplay (entry : ℕ) {x : GalilVML P}
    (hshaped : CountersShaped x) : CountersShaped (LocalTick2.commitReplay entry x) := by
  intro c
  obtain ⟨v, hv⟩ := hshaped (LocalRoles.swapAt Ctr.radius Ctr.replay c)
  show ∃ v, SegCtr (LocalTick2.pushSlots _ (LocalTick2.resetSlots _ x.phys)
    (x.roles (LocalRoles.swapAt Ctr.radius Ctr.replay c))) v
  unfold LocalTick2.pushSlots LocalTick2.resetSlots
  by_cases hpush : x.roles (LocalRoles.swapAt Ctr.radius Ctr.replay c)
      ∈ [x.roles Ctr.length, x.roles Ctr.work]
  · rw [if_pos hpush]
    by_cases hreset : x.roles (LocalRoles.swapAt Ctr.radius Ctr.replay c)
        ∈ LocalTick2.ctrSlots LocalTick2.replayCleared x
    · rw [if_pos hreset]; exact ⟨_, PalPeg.LocalCounter.segCtr_push (PalPeg.LocalCounter.segCtr_reset _)⟩
    · rw [if_neg hreset]; exact ⟨_, PalPeg.LocalCounter.segCtr_push hv⟩
  · rw [if_neg hpush]
    by_cases hreset : x.roles (LocalRoles.swapAt Ctr.radius Ctr.replay c)
        ∈ LocalTick2.ctrSlots LocalTick2.replayCleared x
    · rw [if_pos hreset]; exact ⟨_, PalPeg.LocalCounter.segCtr_reset _⟩
    · rw [if_neg hreset]; exact ⟨_, hv⟩

theorem inv_replayCommitVm (entry : ℕ) (c : GalilScaffoldController.Control)
    {x : GalilVML P} (hinv : Inv x) : Inv (replayCommitVm entry c x) := by
  have hshaped := countersShaped_commitReplay entry hinv.shaped
  refine ⟨LocalRoles.moveRoles_injective hinv.roles, ⟨rfl, rfl, rfl⟩,
    ⟨hinv.views.2.1, hinv.views.2.1, hinv.views.2.2.1, hinv.views.2.2.2.1, hinv.views.2.2.2.2⟩,
    ?_, ?_, ?_, hshaped⟩
  · obtain ⟨v, hv⟩ := hshaped .radius; exact ⟨v, hv, fun _ => hv⟩
  · obtain ⟨v, hv⟩ := hshaped .lower; exact ⟨v, hv, fun _ => hv⟩
  · obtain ⟨v, hv⟩ := hshaped .length; exact ⟨v, hv, fun _ => hv⟩

#print axioms inv_replayCommitVm

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalArrival (abs' absHead')
open PalPeg.LocalReplayParked (abs'' absR rval physHead absR_eq_iter abs''_eq_abs' rval_commitReplay)

/-- The abstraction of the ghost replay commit is the `replayStartVM` landing. -/
theorem replayStartVM_replayCommitVm {x : GalilVML P} (entry : ℕ)
    (c : GalilScaffoldController.Control)
    (hinj : RolesInjective x)
    (hpl : x.pol Ctr.length = true) (hpw : x.pol Ctr.work = true)
    (hpre : x.ctl.replaying = false)
    (hflag : c.replaying = true ∨ LocalCounter.val (x.phys (x.roles .radius)) = 0)
    (hland : GalilScaffoldInputHead.left^[LocalCounter.val (x.phys (x.roles .radius))]
      (abs' x).right = (abs' x).center) :
    replayStartVM entry (abs'' x) (abs'' (replayCommitVm entry c x)) := by
  have hv : rval (replayCommitVm entry c x) = LocalCounter.val (x.phys (x.roles .radius)) :=
    (show rval (replayCommitVm entry c x) = rval (LocalTick2.commitReplay entry x) from rfl).trans
      (rval_commitReplay entry hinj)
  have hR : absR (replayCommitVm entry c x) = (abs' x).center := by
    rw [absR_eq_iter (by rcases hflag with h | h; exact Or.inl h; exact Or.inr (hv.trans h)), hv]
    exact hland
  have ha := LocalTick2.abs_commitReplay (entry := entry) hinj hpl hpw
  rw [abs''_eq_abs' hpre]
  refine ⟨?_, hR, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).replay = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).radius = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).length = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).remaining = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).cycle = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).fpp = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).chain = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).search = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).lower = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).dp = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).periodOnly = _; rw [ha]; try rfl)
    | (show (LocalState.abs (LocalTick2.commitReplay entry x)).walker = _; rw [ha]; try rfl)

#print axioms replayStartVM_replayCommitVm

open PalPeg.LocalReplayParked (ParkedOK) in
/-- The parked right head is far enough from the origin after the ghost replay commit. -/
theorem parkedOK_replayCommitVm {x : GalilVML P} (entry : ℕ)
    (c : GalilScaffoldController.Control) (hinj : RolesInjective x)
    (hradiusLe : LocalCounter.val (x.phys (x.roles .radius)) ≤ position (abs' x).right) :
    ParkedOK (replayCommitVm entry c x) := by
  intro _
  have hv : rval (replayCommitVm entry c x) = LocalCounter.val (x.phys (x.roles .radius)) :=
    (show rval (replayCommitVm entry c x) = rval (LocalTick2.commitReplay entry x) from rfl).trans
      (rval_commitReplay entry hinj)
  rw [hv]
  exact hradiusLe

#print axioms parkedOK_replayCommitVm

/-- The `replayStartVM` landing is determined by its source. -/
theorem replayStartVM_unique {entry : ℕ} {s t t' : GalilVM}
    (h : replayStartVM entry s t) (h' : replayStartVM entry s t') : t = t' := by
  unfold replayStartVM at h h'
  cases t
  cases t'
  simp_all

#print axioms replayStartVM_unique

/-- Truncation commutes with moving a head left any number of times. -/
theorem truncPH_left_iterate (d r : ℕ) (p : GalilScaffoldInputHead.PlaceHead) :
    GalilScaffoldInputHead.left^[r] (PalPeg.GalilThrottledRun.truncPH d p)
      = PalPeg.GalilThrottledRun.truncPH d (GalilScaffoldInputHead.left^[r] p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      PalPeg.GalilTruncTick.truncPH_left, ih]

end PalPeg.ReplayStartGhost
