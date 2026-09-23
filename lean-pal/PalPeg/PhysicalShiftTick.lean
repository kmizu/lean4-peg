import PalPeg.PhysicalShiftStart
import PalPeg.PhysicalTickAssembly

/-!
# The shift-entry nonhead plan in the existing twelve view slots

All four heads are present at this entry. The common row owns the nonhead
tapes, and the normal view executor moves left, right and the verifier. The
entry's finite role changes fix every head bank.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.PhysicalShiftTick
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.GalilScaffoldInputHead (left PlaceHead)
open PalPeg.GalilScaffoldChainVerifier (right canRight)
open PalPeg.PhysicalWatchStep (afterInternal)
open PalPeg.PhysicalShiftStart (entryState)

noncomputable def row (consume : Bool) : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  PalPeg.LocalRoleFusion.flatten (PalPeg.PhysicalShiftStart.plan consume)

noncomputable def roles (consume : Bool) :
    PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM microRadius :=
  PalPeg.LocalRoleFusion.finalRoles (PalPeg.PhysicalShiftStart.plan consume)

def commands (consume : Bool) (v : Fin 4) : PalPeg.ConcreteLocalMachine.ViewCommand :=
  if v = 0 then .moveLeft else if v = 2 then .moveRight
  else if v = 3 then (if consume then .stepRight else .moveRight) else .stay

def headMove (consume : Bool) (v : Fin 4) (head : PlaceHead) : PlaceHead :=
  if v = 0 then left head else if v = 2 then right head
  else if v = 3 then (if consume then right (right head) else right head) else head

def moved (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) : State GalilVM :=
  let z := entryState consume x wm
  ⟨z.ctl, {z.vm with left := left x.vm.left, right := right x.vm.right, chain := .watch (PalPeg.GalilScaffoldChainWatch.immediate (afterInternal consume wm))}⟩

noncomputable def next (consume : Bool) (q : CoreControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → Window Γm microRadius) : CoreControl :=
  {(row consume).nq q input ws with onLetterBit := scanRightOnLetter q ws, leftFirstBit := scanLeftFirst q ws}

noncomputable def rule (consume : Bool) : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  tickRule (by decide) (next consume) (fun _ _ _ => commands consume)
    (row consume).acts (row consume).len_le

theorem headOp_commands (consume : Bool) (v : Fin 4) :
    headOp (commands consume v) = some (headMove consume v) := by
  cases consume <;> fin_cases v <;> rfl

theorem source_heads (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) : ∀ v, ∃ head, headOf x v = some head := by
  intro v
  fin_cases v <;> simp [headOf, hchain]

theorem moved_heads (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (v : Fin 4) :
    headOf (moved consume x wm) v = (headOf x v).map (headMove consume v) := by
  cases consume <;> fin_cases v <;>
    simp [headOf, moved, headMove, hchain, afterInternal, PalPeg.GalilScaffoldChainWatch.immediate,
      PalPeg.GalilScaffoldChainWatch.caught, PalPeg.GalilScaffoldChainVerifier.consume] <;> rfl

theorem moved_counters (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State) :
    counterOf (moved consume x wm) = counterOf (entryState consume x wm) := by
  funext c
  fin_cases c <;> rfl

theorem moved_cache (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (bit : Bool) (T M : STape Γm)
    (h : PalPeg.PhysicalCacheInvariant.Cache (entryState consume x wm) bit T M) :
    PalPeg.PhysicalCacheInvariant.Cache (moved consume x wm) bit T M := h

/-- Both verifier guards are provided by the two actual successful quanta.
The source abstraction identifies the represented view; no uniqueness theorem
for arbitrary views is needed. -/
theorem ready (consume : Bool) (x : State GalilVM) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm) (hright : canRight x.vm.right)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm))
    (v : Fin 4) (head : PlaceHead) (view : PalPeg.LocalInputView.InputView)
    (hh : headOf x v = some head) (ha : PalPeg.LocalArrival.absHead' view [] = head) :
    HeadReady (commands consume v) view := by
  have single : canRight head → HeadReady .moveRight view := by
    intro hc hg hn
    rw [← ha] at hc
    simpa [canRight, PalPeg.LocalArrival.absHead', hg, hn] using hc
  fin_cases v
  · trivial
  · trivial
  · have heq : head = x.vm.right := Option.some.inj hh.symm
    exact single (heq ▸ hright)
  · have heq : head = wm.machine.verifier := by simpa [headOf, hchain] using hh.symm
    cases consume with
    | false =>
      exact single (heq ▸ hsecond.1)
    | true =>
      apply headReady_stepRight_of_canRight
      · rw [ha, heq]; exact (hfirst rfl).1
      · rw [ha, heq]; exact hsecond.1

/-- Boundary snapshots and the remaining/mirror exchange are all outside the
four head banks, so they can be installed after the view executor finishes. -/
theorem roles_head (consume : Bool) (q : CoreControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → Window Γm microRadius) (v : Fin 4) (i : Fin 12) :
    roles consume q input ws (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
  have hr : PalPeg.PhysicalShiftEntry.entryRoles (slotIndex (headSlot v i)) = slotIndex (headSlot v i) := by
    apply PalPeg.PhysicalShiftEntry.roles_other
    · intro h
      have hh := slotIndex.injective h
      simp [headSlot, counterSlot] at hh
    · intro h
      have hh := slotIndex.injective h
      simp [headSlot, mirrorSlot] at hh
  simp only [roles, PalPeg.LocalRoleFusion.finalRoles, PalPeg.PhysicalShiftStart.plan, seqRule,
    PalPeg.LocalRoleFusion.routeRule, PalPeg.PhysicalShiftStart.entryChange, Equiv.trans_apply, hr]
  exact PalPeg.PhysicalWatchActions.fusedRoles_other consume q _ input _
    (by intro h; have hh := slotIndex.injective h; simp [headSlot, counterSlot] at hh)
    (by intro h; have hh := slotIndex.injective h; simp [headSlot, counterSlot] at hh)
    (by intro h; have hh := slotIndex.injective h; simp [headSlot, counterSlot] at hh)

/-- The common row's control already encodes all non-head observations. Only
the two observations of the moved comparison cursors need to be refreshed. -/
theorem next_control (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : CoreEnc w x p) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hn : EncControl w (entryState consume x wm)
      ((row consume).nq p.1 none (fun j => readWin blankM microRadius (p.2 j))))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    EncControl w (moved consume x wm) (next consume p.1 none (fun j => readWin blankM microRadius (p.2 j))) := by
  refine ⟨hn.ctl, hn.chainTag, hn.chainPhase, hn.chainForward, hn.chainBroken,
    hn.fppMode, hn.fppFinalStage, hn.fppPc, hn.fppDone, hn.dpPc, hn.dpDone,
    hn.searchMode, hn.searchFinalStage, hn.searchQuarter, hn.periodOnly, ?_, ?_, ?_⟩
  · intro i place hp
    apply hn.placeGap i place
    fin_cases i <;> exact hp
  · let T := fun slot => p.2 (slotIndex slot)
    have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
    have h := scanRightOnLetter_eq w arrived he.1.2 micro_le_margin hright hrep hlen
    rw [ht] at h
    exact h
  · let T := fun slot => p.2 (slotIndex slot)
    have ht : tapesOf T = p.2 := by funext j; simp [T, tapesOf]
    have h := scanLeftFirst_eq he.1.2 (by decide : 1 ≤ microRadius) micro_le_margin
    rw [ht] at h
    exact h

/-- The complete entry row moves all three active cursors and preserves the
same counters, inactive tape shapes and cache as the existing physical machine. -/
theorem running_ideal (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : CoreState) (he : PalPeg.PhysicalCacheInvariant.CoreInv w x p)
    (hmode : x.ctl.mode = .scan) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    let result := idealRun (rule consume) blankM p none 12
    PalPeg.PhysicalCacheInvariant.Running w (moved consume x wm)
      (result.1, fun j => result.2 (roles consume p.1 none
        (fun k => readWin blankM microRadius (p.2 k)) j)) := by
  dsimp only
  generalize htraj : idealRun (rule consume) blankM p none = trajectory
  have hr : PalPeg.PhysicalCacheInvariant.Running w x p :=
    ⟨p.2, he, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  have hn := PalPeg.PhysicalShiftStart.running_nonhead_ideal consume w x p hr hmode wm hchain hfirst hsecond
  have hctl : EncControl w (entryState consume x wm)
      ((row consume).nq p.1 none (fun j => readWin blankM microRadius (p.2 j))) := by
    obtain ⟨_, hi, _⟩ := hn
    exact hi.1.1.1.1
  have hrun := PalPeg.PhysicalTickAssembly.running_tick (row consume) (roles consume) (next consume)
    (fun _ _ _ => commands consume) w x (entryState consume x wm) (moved consume x wm) p none
    he.1.1 hn (roles_head consume p.1 none _) ⟨rfl, rfl, rfl⟩
    (next_control consume w arrived x p he.1.1 wm hctl hright hrep hlen)
    (headMove consume) (headOp_commands consume)
    (fun v => by rw [moved_heads consume x wm hchain v]; simp)
    (fun v head hh => by rw [moved_heads consume x wm hchain v, hh]; rfl)
    (source_heads x wm hchain) (ready consume x wm hchain hright hfirst hsecond)
    (fun _ => rfl) (fun _ => rfl) (moved_counters consume x wm) rfl rfl rfl
    (moved_cache consume x wm)
  generalize hother : idealRun (tickRule (by decide : 2 ≤ microRadius) (next consume)
    (fun _ _ _ => commands consume) (row consume).acts (row consume).len_le)
    blankM p none = other at hrun
  have heq : other = trajectory := hother.symm.trans htraj
  rw [heq] at hrun
  exact hrun

/-- One bounded physical step includes all twelve view slots and the final
finite role exchange. Its radius is the existing macroRadius = 1536. -/
noncomputable def step (consume : Bool) :
    PalPeg.Local.LocalStep (Fin 2) (PalPeg.LocalRoleRouting.Control CoreControl tapeCountM)
      Γm tapeCountM macroRadius :=
  PalPeg.LocalRoleRouting.route (compStep (iterRule (rule consume) 12))
    (PalPeg.PhysicalTickAssembly.macroRoles (roles consume))

theorem running (consume : Bool) (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : PalPeg.PhysicalCacheInvariant.Running w x (PalPeg.LocalRoleRouting.decode p))
    (hmode : x.ctl.mode = .scan) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (hchain : x.vm.chain = .watch wm)
    (hfirst : consume = true → PalPeg.GalilScaffoldChainWatch.Good wm)
    (hsecond : PalPeg.GalilScaffoldChainWatch.Good (afterInternal consume wm))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    PalPeg.PhysicalCacheInvariant.Running w (moved consume x wm)
      (PalPeg.LocalRoleRouting.decode ((step consume).apply blankM p none)) := by
  have hs := PalPeg.PhysicalTickAssembly.running_fused_route (rule consume) (roles consume)
    w x (moved consume x wm) p none he
    (fun T hT => running_ideal consume w arrived x (_, T) hT hmode wm hchain hfirst hsecond hright hrep hlen)
  exact hs

/-- info: 'PalPeg.PhysicalShiftTick.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

end PalPeg.PhysicalShiftTick
