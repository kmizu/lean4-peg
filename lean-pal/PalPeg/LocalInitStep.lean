import PalPeg.LocalSysConcrete
import PalPeg.GalilTickFair

/-!
# The local step of the `init` mode

`GalilScaffoldTopReplay.initVM` moves the three heads one place to the right, counts the first
letter in `length`, and starts the search from a zero lower bound: `work := 1`, the other search
counters, `lower` and the chain as they are at boot.  The `init` mode is only ever entered at
boot, where every counter is zero and both programs are halted, so the local step is a fixed
sequence of local operations: `moveRight` on the three cursors and on the left mirror, one
`push` on the `length` tape (and on its mirror bank) and one on the `work` tape, and the control
bits of the search and of the DP program.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PalPeg.LocalInitStep

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.LocalState (GalilVML Ctr RolesInjective absCtrs)
open PalPeg.LocalInputView (InputView moveRight)
open PalPeg.LocalArrival (abs' absHead' Ahead moveRight_ok)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalCounter (push val absCtr)
open PalPeg.Program (STape)

variable {P : ℕ}

/-- The counter bank after `init`: one unit on `length`, one on `work`. -/
def initPhys (x : GalilVML P) : Fin P → STape LocalCounter.Seg := fun j =>
  if j = x.roles .length then push (x.phys j)
  else if j = x.roles .work then push (x.phys j)
  else x.phys j

/-- **The local `init` step on the VM.**  The signs of `length` and `work` are set to positive:
both tapes hold zero, so the sign carries no information before the push. -/
def initVml (entry : ℕ) (x : GalilVML P) : GalilVML P :=
  { x with
    left := moveRight x.left
    center := moveRight x.center
    right := moveRight x.right
    phys := initPhys x
    pol := fun c => if c = .length ∨ c = .work then true else x.pol c
    lengthMir := LocalMirror.pushAll x.lengthMir
    chain := .idle
    searchMode := .grow
    searchFinalStage := false
    searchQuarter := 0
    dpPc := entry
    dpDone := true
    ctl := { x.ctl with mode := .scan, output := true } }

/-- **The local `init` step**, left mirror included. -/
def initStep (entry : ℕ) (m : Mirrored1 P) : Mirrored1 P :=
  ⟨initVml entry m.vm, moveRight m.mirL⟩

/-- A counter tape holding zero reads as the zero counter under either sign. -/
theorem absCtr_of_val_zero {t : STape LocalCounter.Seg} (hzero : val t = 0) (b : Bool) :
    absCtr t b = GalilScaffoldCounter.reset := by
  cases b <;> simp [absCtr, hzero, GalilScaffoldCounter.ofNat, LocalCounter.negOfNat,
    GalilScaffoldCounter.reset]

/-- The counters of the bank after `init`. -/
theorem absCtrs_initVml (entry : ℕ) {x : GalilVML P} (hinj : RolesInjective x)
    (hlength : val (x.phys (x.roles .length)) = 0) (hwork : val (x.phys (x.roles .work)) = 0)
    (c : Ctr) :
    absCtrs (initVml entry x) c
      = if c = .length ∨ c = .work then GalilScaffoldCounter.inc GalilScaffoldCounter.reset
        else absCtrs x c := by
  show absCtr (initPhys x (x.roles c)) (if c = .length ∨ c = .work then true else x.pol c) = _
  unfold initPhys
  by_cases hcl : c = .length
  · subst hcl
    rw [if_pos rfl, if_pos (Or.inl rfl), if_pos (Or.inl rfl), LocalCounter.absCtr_push,
      if_pos rfl, absCtr_of_val_zero hlength]
  · by_cases hcw : c = .work
    · subst hcw
      have hne : x.roles .work ≠ x.roles .length := fun h => hcl (hinj h)
      rw [if_neg hne, if_pos rfl, if_pos (Or.inr rfl), if_pos (Or.inr rfl),
        LocalCounter.absCtr_push, if_pos rfl, absCtr_of_val_zero hwork]
    · have hnl : x.roles c ≠ x.roles .length := fun h => hcl (hinj h)
      have hnw : x.roles c ≠ x.roles .work := fun h => hcw (hinj h)
      rw [if_neg hnl, if_neg hnw, if_neg (by tauto), if_neg (by tauto)]
      rfl

#print axioms absCtrs_initVml

/-- **The abstraction of the local `init` step is the `init` effect of the VM**, on a state whose
counters are all zero, whose DP tapes are reset, and whose three cursors stand on the same place
with the next cell available. -/
theorem initVM_initVml (entry : ℕ) {x : GalilVML P} (hinj : RolesInjective x)
    (hviews : PalPeg.LocalState.ViewsWF x) (hpending : x.pending = [])
    (hleft : absHead' x.left x.pending = absHead' x.right x.pending)
    (hcenter : absHead' x.center x.pending = absHead' x.right x.pending)
    (hcanRight : GalilScaffoldChainVerifier.canRight (absHead' x.right x.pending))
    (hzero : ∀ c : Ctr, val (x.phys (x.roles c)) = 0)
    (hdp : LocalBuffers.abs x.dpBuf = fun _ => GalilScaffoldTape.reset) :
    initVM entry (abs' x) (abs' (initVml entry x)) := by
  have hahead : ∀ v : InputView, Ahead v x.pending := fun v _ _ => Or.inr hpending
  have hcounter : ∀ c : Ctr, absCtrs x c = GalilScaffoldCounter.reset :=
    fun c => absCtr_of_val_zero (hzero c) _
  have hafter := absCtrs_initVml entry hinj (hzero .length) (hzero .work)
  have hright : absHead' (moveRight x.right) x.pending
      = GalilScaffoldChainVerifier.right (absHead' x.right x.pending) :=
    moveRight_ok hviews.2.2.1 (hahead _) hcanRight
  refine ⟨hright, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · show absHead' (moveRight x.left) x.pending = _
    rw [moveRight_ok hviews.1 (hahead _) (hleft ▸ hcanRight), hleft]
    rfl
  · show absHead' (moveRight x.center) x.pending = _
    rw [moveRight_ok hviews.2.1 (hahead _) (hcenter ▸ hcanRight), hcenter]
    rfl
  · show absCtrs (initVml entry x) .length = GalilScaffoldCounter.inc (absCtrs x .length)
    rw [hafter, if_pos (Or.inl rfl), hcounter]
  · show absCtrs (initVml entry x) .radius = absCtrs x .radius
    rw [hafter, if_neg (by decide)]
  · show absCtrs (initVml entry x) .remaining = absCtrs x .remaining
    rw [hafter, if_neg (by decide)]
  · show absCtrs (initVml entry x) .replay = absCtrs x .replay
    rw [hafter, if_neg (by decide)]
  · show absCtrs (initVml entry x) .cycle = absCtrs x .cycle
    rw [hafter, if_neg (by decide)]
  · show (⟨x.fppMode, ⟨⟨x.fppPc, LocalBuffers.abs x.fppBuf⟩, x.fppDone⟩,
        absCtrs (initVml entry x) .fppWork, PalPeg.LocalState.absPlace x.fppWalker,
        x.fppFinalStage⟩ : FppControl.State) = _
    rw [hafter, if_neg (by decide)]
    rfl
  · show (⟨.grow, false, absCtrs (initVml entry x) .span, absCtrs (initVml entry x) .work,
        absCtrs (initVml entry x) .debt, 0⟩ : GalilScaffoldSearchFinish.State)
      = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset (absCtrs x .radius)
    rw [hafter, hafter, hafter, if_neg (by decide), if_pos (Or.inr rfl), if_neg (by decide),
      hcounter, hcounter, hcounter]
    rfl
  · show absCtrs (initVml entry x) .lower = GalilScaffoldCounter.reset
    rw [hafter, if_neg (by decide), hcounter]
  · show (⟨⟨entry, LocalBuffers.abs x.dpBuf⟩, true⟩ : GalilScaffoldControl.Machine 12) = _
    rw [hdp]
    rfl

#print axioms initVM_initVml

/-- The `init` tick is canonical: it is not a scan tick, and it keeps the search cursor. -/
theorem canonical_of_init {entry initEntry delay : ℕ} {x y : State GalilVM}
    (hmode : x.ctl.mode = .init) (hinit : initVM initEntry x.vm y.vm) :
    PalPeg.GalilTickFair.Canonical entry delay x y where
  restartFirst := fun hscan => by rw [hmode] at hscan; cases hscan
  fallbackPlace := fun hscan => by rw [hmode] at hscan; cases hscan
  keepsSearchCursor := fun _ => ⟨hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **The local `init` step is a canonical `init` tick of the abstraction.** -/
theorem tick_initStep {Pw : Shared} (qq : ℕ) (first : Fin 9) (delay entry : ℕ)
    (hinit : Pw.init = initVM entry) {m : Mirrored1 P}
    (hmode : m.vm.ctl.mode = .init) (hreplaying : m.vm.ctl.replaying = false)
    (hinj : RolesInjective m.vm) (hviews : PalPeg.LocalState.ViewsWF m.vm)
    (hpending : m.vm.pending = [])
    (hleft : absHead' m.vm.left m.vm.pending = absHead' m.vm.right m.vm.pending)
    (hcenter : absHead' m.vm.center m.vm.pending = absHead' m.vm.right m.vm.pending)
    (hcanRight : GalilScaffoldChainVerifier.canRight (absHead' m.vm.right m.vm.pending))
    (hzero : ∀ c : Ctr, val (m.vm.phys (m.vm.roles c)) = 0)
    (hdp : LocalBuffers.abs m.vm.dpBuf = fun _ => GalilScaffoldTape.reset) :
    Tick (galilFrameS Pw qq first) delay (PalPeg.LocalReplayParked.absState'' m.vm)
        (PalPeg.LocalReplayParked.absState'' (initStep entry m).vm) ∧
      PalPeg.GalilTickFair.Canonical entry delay (PalPeg.LocalReplayParked.absState'' m.vm)
        (PalPeg.LocalReplayParked.absState'' (initStep entry m).vm) := by
  have hvm := initVM_initVml entry hinj hviews hpending hleft hcenter hcanRight hzero hdp
  have hbefore : PalPeg.LocalReplayParked.abs'' m.vm = abs' m.vm :=
    PalPeg.LocalReplayParked.abs''_eq_abs' hreplaying
  have hafter : PalPeg.LocalReplayParked.abs'' (initVml entry m.vm) = abs' (initVml entry m.vm) :=
    PalPeg.LocalReplayParked.abs''_eq_abs' hreplaying
  refine ⟨?_, canonical_of_init (initEntry := entry) hmode (by
    show initVM entry (PalPeg.LocalReplayParked.abs'' m.vm)
      (PalPeg.LocalReplayParked.abs'' (initVml entry m.vm))
    rw [hbefore, hafter]
    exact hvm)⟩
  show Tick _ delay ⟨m.vm.ctl, PalPeg.LocalReplayParked.abs'' m.vm⟩
    ⟨{ m.vm.ctl with mode := .scan, output := true },
      PalPeg.LocalReplayParked.abs'' (initVml entry m.vm)⟩
  rw [hbefore, hafter]
  exact Tick.init m.vm.ctl _ _ hmode (by
    show Pw.init _ _
    rw [hinit]
    exact hvm)

#print axioms tick_initStep

/-- **The local `init` step keeps the physical pack and the left mirror.** -/
theorem physWF_initStep (entry : ℕ) {m : Mirrored1 P}
    (hphys : PalPeg.LocalSysConcrete.PhysWF m.vm) (hmir : PalPeg.LocalReplayParked.MirInv1 m)
    (hreplaying : m.vm.ctl.replaying = false) :
    PalPeg.LocalSysConcrete.PhysWF (initStep entry m).vm ∧
      PalPeg.LocalReplayParked.MirInv1 (initStep entry m) := by
  have hinj := hphys.inv.roles
  have hother : ∀ c : Ctr, c ≠ .length → c ≠ .work →
      initPhys m.vm (m.vm.roles c) = m.vm.phys (m.vm.roles c) := fun c hl hw => by
    unfold initPhys
    rw [if_neg (fun h => hl (hinj h)), if_neg (fun h => hw (hinj h))]
  have hlengthTape : initPhys m.vm (m.vm.roles .length) = push (m.vm.phys (m.vm.roles .length)) := by
    unfold initPhys
    rw [if_pos rfl]
  refine ⟨⟨⟨hinj, ⟨?_, ?_, ?_⟩,
      ⟨PalPeg.LocalTick1.WF_moveRight hphys.inv.views.1,
        PalPeg.LocalTick1.WF_moveRight hphys.inv.views.2.1,
        PalPeg.LocalTick1.WF_moveRight hphys.inv.views.2.2.1,
        hphys.inv.views.2.2.2.1, hphys.inv.views.2.2.2.2⟩,
      hphys.inv.radiusShaped, hphys.inv.lowerShaped, ?_, ?_⟩, ?_, hphys.pend⟩,
    PalPeg.LocalReplaySwap.Twin.moveRight hmir.2 hphys.inv.views.2.1 hmir.1,
    PalPeg.LocalTick1.WF_moveRight hmir.2⟩
  · show m.vm.radiusMir.src = initPhys m.vm (m.vm.roles .radius)
    rw [hother .radius (by decide) (by decide)]
    exact hphys.inv.attached.1
  · show m.vm.lowerMir.src = initPhys m.vm (m.vm.roles .lower)
    rw [hother .lower (by decide) (by decide)]
    exact hphys.inv.attached.2.1
  · show (LocalMirror.pushAll m.vm.lengthMir).src = initPhys m.vm (m.vm.roles .length)
    rw [hlengthTape, LocalMirror.pushAll_src, hphys.inv.attached.2.2]
    rfl
  · obtain ⟨v, hshaped⟩ := hphys.inv.lengthShaped
    exact ⟨v + 1, LocalMirror.shaped_pushAll hshaped⟩
  · intro c
    obtain ⟨v, hv⟩ := hphys.inv.shaped c
    show ∃ v, LocalCounter.SegCtr (initPhys m.vm (m.vm.roles c)) v
    unfold initPhys
    by_cases hl : m.vm.roles c = m.vm.roles .length
    · rw [if_pos hl]
      exact ⟨v + 1, LocalCounter.segCtr_push hv⟩
    · rw [if_neg hl]
      by_cases hw : m.vm.roles c = m.vm.roles .work
      · rw [if_pos hw]
        exact ⟨v + 1, LocalCounter.segCtr_push hv⟩
      · rw [if_neg hw]
        exact ⟨v, hv⟩
  · intro hr
    exact absurd (show m.vm.ctl.replaying = true from hr) (by rw [hreplaying]; decide)

#print axioms physWF_initStep

/-- A counter tape that reads as the zero counter holds zero, whatever its sign. -/
theorem val_zero_of_absCtr_reset {t : STape LocalCounter.Seg} {b : Bool}
    (hreset : absCtr t b = GalilScaffoldCounter.reset) : val t = 0 := by
  cases b
  · have hneg := congrArg GalilScaffoldCounter.Counter.neg hreset
    simpa [absCtr, LocalCounter.negOfNat, GalilScaffoldCounter.reset] using hneg
  · have hpos := congrArg GalilScaffoldCounter.Counter.pos hreset
    simpa [absCtr, GalilScaffoldCounter.ofNat, GalilScaffoldCounter.reset] using hpos

/-- **At boot the premises of the local `init` step hold.**  A non-replaying state whose
abstraction is a truncated boot VM has every counter at zero, the DP tapes reset, and its three
cursors on the same place. -/
theorem premises_of_truncated_boot {x : GalilVML P} {w : List (Fin 2)} {d : ℕ}
    (hreplaying : x.ctl.replaying = false)
    (hboot : PalPeg.LocalReplayParked.abs'' x
      = PalPeg.GalilThrottledRun.truncVM d (GalilBootVM.initVM0 w)) :
    (∀ c : Ctr, val (x.phys (x.roles c)) = 0) ∧
      LocalBuffers.abs x.dpBuf = (fun _ => GalilScaffoldTape.reset) ∧
      absHead' x.left x.pending = absHead' x.right x.pending ∧
      absHead' x.center x.pending = absHead' x.right x.pending := by
  rw [PalPeg.LocalReplayParked.abs''_eq_abs' hreplaying] at hboot
  have hcounter : ∀ c : Ctr, absCtrs x c = GalilScaffoldCounter.reset := by
    intro c
    cases c
    · exact congrArg GalilVM.cycle hboot
    · exact congrArg GalilVM.remaining hboot
    · exact congrArg GalilVM.radius hboot
    · exact congrArg GalilVM.length hboot
    · exact congrArg GalilVM.replay hboot
    · exact congrArg GalilVM.lower hboot
    · exact congrArg (fun s : GalilVM => s.search.span) hboot
    · exact congrArg (fun s : GalilVM => s.search.work) hboot
    · exact congrArg (fun s : GalilVM => s.search.debt) hboot
    · exact congrArg (fun s : GalilVM => s.fpp.work) hboot
  refine ⟨fun c => val_zero_of_absCtr_reset (hcounter c), ?_, ?_, ?_⟩
  · exact congrArg (fun s : GalilVM => s.dp.config.tapes) hboot
  · exact (congrArg GalilVM.left hboot).trans (congrArg GalilVM.right hboot).symm
  · exact (congrArg GalilVM.center hboot).trans (congrArg GalilVM.right hboot).symm

#print axioms premises_of_truncated_boot

end PalPeg.LocalInitStep
