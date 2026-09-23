import PalPeg.LocalRoleRouting
import PalPeg.PhysicalCountConsume
import PalPeg.PhysicalCounterCache

/-!
# The existing physical machine with finite tape roles

The alphabet, 118 physical tapes and fused radius remain those of
`PhysicalContract`. Only a finite role permutation is added around its control.
Boot, feed, starvation and both completed count cases hold for every assignment.
The boundary rotation below reuses the currently unnamed counter slot 10 as the
spare in watch states. Rebuilding it and strengthening the run invariant remain
required before the boundary dispatcher can be completed.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalRoles
open PalPeg.PhysicalEncoding
open PalPeg.PhysicalContract (macroRadius CoreControl TickCases)
open PalPeg.PhysicalScanCount (RestCommands scanMachine CountAtRest)
open PalPeg.PhysicalCountConsume (CountPlainMatch)
open PalPeg.LocalRoleRouting (decode)
open PalPeg.Program (STape)
open PalPeg.Local (LocalStep)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFinalAssembly2 (centreC placeC)

abbrev Roles := Equiv.Perm (Fin tapeCountM)
abbrev Control := PalPeg.LocalRoleRouting.Control PalPeg.PhysicalContract.Control tapeCountM
abbrev PhysicalState := PalPeg.LocalRoleRouting.Config PalPeg.PhysicalContract.Control Γm tapeCountM

noncomputable instance : Fintype Control := inferInstanceAs (Fintype (Roles × PalPeg.PhysicalContract.Control))
instance : DecidableEq Control := inferInstanceAs (DecidableEq (Roles × PalPeg.PhysicalContract.Control))

def Enc (w : List (Fin 2)) (x : State GalilVM) (p : PhysicalState) : Prop :=
  PalPeg.PhysicalContract.Enc w x (decode p)

noncomputable def machine (rest : RestCommands) :
    LocalStep (Fin 2) Control Γm tapeCountM macroRadius :=
  PalPeg.LocalRoleRouting.hold (scanMachine rest)

def initialControl : Control := (Equiv.refl _, PalPeg.PhysicalContract.initialControl)

theorem enc_initial (w : List (Fin 2)) :
    Enc w PalPeg.PhysicalContract.initialState
      (initialControl, fun _ => STape.blankTape blankM) :=
  PalPeg.PhysicalContract.enc_initial w

/-- Use this equation before specializing a large fused rule. It keeps elaboration
from expanding the twelve micro steps while transporting an encoding. -/
theorem enc_step (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (input : Option (Fin 2)) :
    Enc w x ((machine rest).apply blankM p input) ↔
      PalPeg.PhysicalContract.Enc w x ((scanMachine rest).apply blankM (decode p) input) := by
  unfold Enc machine
  rw [PalPeg.LocalRoleRouting.decode_hold]

theorem forward_feed (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (a : Fin 2) (henc : Enc w x p) :
    Enc w (PalPeg.GalilArriveChain.arriveState' a x) ((machine rest).apply blankM p (some a)) := by
  rw [enc_step]
  exact PalPeg.PhysicalScanCount.forward_feed rest w x (decode p) a henc

theorem forward_starved (rest : RestCommands) (w : List (Fin 2)) (x : State GalilVM)
    (p : PhysicalState) (henc : Enc w x p)
    (hs : PalPeg.FrameFunction.starvedTest x = true) :
    Enc w x ((machine rest).apply blankM p none) := by
  rw [enc_step]
  exact PalPeg.PhysicalTickDispatch.forward_starved _ w x (decode p) henc hs

open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.LocalSysConcrete (absSC)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalShadowConcrete (OnRun)
open PalPeg.LocalBlankState (tapeCount)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter)

/-- The final tick contract retains the same two completed active cases after
adding finite roles. The remainder is stated on this actual routed machine. -/
theorem cases_of_remaining (rest : RestCommands)
    (hother : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ (m : Mirrored1 (tapeCount 0)) (p : PhysicalState),
        PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        ¬ frozenAt w m → Enc w (absSC m) p →
        PalPeg.FrameFunction.starvedTest (absSC m) = false →
        Tick (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
          (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
            (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m)) →
        ¬ CountAtRest (absSC m) → ¬ CountPlainMatch (absSC m) →
        Enc w
          (tickFun (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
            (galilFrameS (PalPeg.GalilRunSkeleton.PofC centreC placeC 0 w) 1 0) 2048 (absSC m))
          ((machine rest).apply blankM p none)) :
    TickCases (machine rest) blankM Enc := by
  constructor
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved
    exact forward_starved rest w (absSC m) p henc hstarved
  · intro w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick
    by_cases hrest : CountAtRest (absSC m)
    · rw [enc_step]
      obtain ⟨hmode, hclock, hchain, hsearch⟩ := hrest
      exact PalPeg.PhysicalScanCount.forward_count_atRest rest w (absSC m) (decode p)
        henc hmode hstarved hclock hchain hsearch
    · by_cases hplain : CountPlainMatch (absSC m)
      · rw [enc_step]
        obtain ⟨hmode, hclock, wm, a, hchain, htok, hseen, hforward, hlag⟩ := hplain
        exact PalPeg.PhysicalCountConsume.forward_count_plain rest w (absSC m) (decode p)
          henc hmode hstarved hclock htick wm hchain a htok hseen hforward hlag
      · exact hother w st Tc hpre hcanon m p hon hnotFrozen henc hstarved htick hrest hplain

/-- Counter 10 is the chain's h counter in copy/back and is unnamed in watch.
Boundary/last/spare roles are 14/15/10, respectively. Other slots keep their names. -/
noncomputable def boundaryRoles : Roles :=
  (Equiv.swap (slotIndex (counterSlot 14)) (slotIndex (counterSlot 10))).trans
    (Equiv.swap (slotIndex (counterSlot 14)) (slotIndex (counterSlot 15)))

theorem counterIndex_ne {a b : Fin 16} (h : a ≠ b) :
    slotIndex (counterSlot a) ≠ slotIndex (counterSlot b) := by
  intro he
  have hs := slotIndex.injective he
  apply h
  simpa only [counterSlot, Sum.inr.injEq, Sum.inl.injEq] using hs

theorem boundaryRoles_boundary :
    boundaryRoles (slotIndex (counterSlot 14)) = slotIndex (counterSlot 10) := by
  simp only [boundaryRoles, Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne (counterIndex_ne (by decide)) (counterIndex_ne (by decide))

theorem boundaryRoles_last :
    boundaryRoles (slotIndex (counterSlot 15)) = slotIndex (counterSlot 14) := by
  rw [boundaryRoles, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne (counterIndex_ne (by decide : (15 : Fin 16) ≠ 14))
      (counterIndex_ne (by decide : (15 : Fin 16) ≠ 10)), Equiv.swap_apply_right]

theorem boundaryRoles_spare :
    boundaryRoles (slotIndex (counterSlot 10)) = slotIndex (counterSlot 15) := by
  simp only [boundaryRoles, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]

theorem boundaryRoles_other (j : Fin tapeCountM)
    (hboundary : j ≠ slotIndex (counterSlot 14)) (hlast : j ≠ slotIndex (counterSlot 15))
    (hspare : j ≠ slotIndex (counterSlot 10)) : boundaryRoles j = j := by
  simp only [boundaryRoles, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hboundary hspare,
    Equiv.swap_apply_of_ne_of_ne hboundary hlast]

/-- The generic three-role exchange is exactly this permutation of the existing
physical slot table. No new bank or tape layout is introduced. -/
noncomputable def cacheSlot (i : Fin 3) : Fin tapeCountM :=
  if i = 0 then slotIndex (counterSlot 14)
  else if i = 1 then slotIndex (counterSlot 15) else slotIndex (counterSlot 10)

theorem boundaryRoles_cacheSlot (i : Fin 3) :
    boundaryRoles (cacheSlot i) = PalPeg.PhysicalCounterCache.rotate cacheSlot i := by
  fin_cases i <;> simp only [cacheSlot, Fin.zero_eta, Fin.isValue, ↓reduceIte]
  · simpa [PalPeg.PhysicalCounterCache.rotate, PalPeg.LocalRoles.swapAt, cacheSlot]
      using boundaryRoles_boundary
  · simpa [PalPeg.PhysicalCounterCache.rotate, PalPeg.LocalRoles.swapAt, cacheSlot]
      using boundaryRoles_last
  · simpa [PalPeg.PhysicalCounterCache.rotate, PalPeg.LocalRoles.swapAt, cacheSlot]
      using boundaryRoles_spare

/-- Relative role composition in the finite control realizes the counter-bank
rotation proved by `PhysicalCounterCache`, whatever the current assignment. -/
theorem compose_boundary (roles : Roles) (i : Fin 3) :
    (boundaryRoles.trans roles) (cacheSlot i) =
      PalPeg.PhysicalCounterCache.rotate (fun j => roles (cacheSlot j)) i := by
  rw [Equiv.trans_apply, boundaryRoles_cacheSlot]
  rfl

/-- info: 'PalPeg.PhysicalRoles.forward_feed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forward_feed

/-- info: 'PalPeg.PhysicalRoles.cases_of_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cases_of_remaining

/-- info: 'PalPeg.PhysicalRoles.compose_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compose_boundary

end PalPeg.PhysicalRoles
