import PalPeg.PhysicalEncoding
import PalPeg.PhysicalGuardProbe
import PalPeg.ShadowedLocalFinal

/-!
# Contract for the fixed physical witness

Consumer: `ShadowedLocalFinal.given_physicalMachine_indexed`, at 0 / 1 / 0.
The machine parameters remain outside the word quantifier. `Obligations` is a
list of explicit hypotheses, not an instance or a discharged realization.

The outer encoding distinguishes blank boot from padded execution. The concrete
boot/feed transitions live in `PhysicalBootFeed`; ordinary tick cases are being
connected through `TickCases`. The running macro boundary carries the slot and
pending-work facts that the existing tick assembler consumes.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalContract
open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.GalilFinalAssembly2 (centreC placeC)
open PalPeg.CloseoutCheckW (PreTraceIMW CanonTrace)
open PalPeg.Local (LocalStep)
open PalPeg.LocalReplayParked (Mirrored1)
open PalPeg.LocalSysConcrete (absSC x0C Starved InvC)
open PalPeg.LocalShadowConcrete (OnRun TickSucc)
open PalPeg.LocalBlankState (tapeCount blankVML)
open PalPeg.ShadowedLocalFinal (localGood postPhase frozenAt heldAfter reportArrived)
open PalPeg.PhysicalEncoding (QPhys Γm blankM tapeCountM slotIndex)

/-- Enough for the 64 DP calls, the fixed FPP quantum and view primitives.
Each concrete action table still has to prove its length bound. -/
def microRadius : ℕ := 128
def macroRadius : ℕ := PalPeg.LocalStepFusion.iterRadius microRadius 12
def margin : ℕ := macroRadius

theorem macroRadius_eq : macroRadius = 1536 := by
  rw [macroRadius, PalPeg.LocalStepFusion.iterRadius_eq]
  rfl

theorem micro_le_margin : microRadius ≤ margin := by
  rw [margin, macroRadius_eq]
  decide

def fppBound : ℕ := max 321 (PalPeg.GalilFppMarkedCode.code.length + 1)
def dpBound : ℕ := PalPeg.GalilDpCode.code.length + 1

theorem fppBound_gt_start : 320 < fppBound := by
  exact Nat.lt_of_lt_of_le (by decide : 320 < 321)
    (Nat.le_max_left 321 (PalPeg.GalilFppMarkedCode.code.length + 1))

abbrev CoreControl := QPhys fppBound dpBound
abbrev Control := Unit ⊕ CoreControl
abbrev CoreState := CoreControl × (Fin tapeCountM → STape Γm)
abbrev PhysicalState := Control × (Fin tapeCountM → STape Γm)

/-- Source obligations of `enc_afterTickOfState`, carried at every macro boundary. -/
def MacroBoundary (q : CoreControl) : Prop :=
  q.slot.val = 0 ∧ ∀ v, (q.micro v).2.2.2 = 0

def CoreEnc (w : List (Fin 2)) (x : State GalilVM) (p : CoreState) : Prop :=
  PalPeg.PhysicalEncoding.Enc w margin x (p.1, fun slot => p.2 (slotIndex slot)) ∧
    MacroBoundary p.1

noncomputable def initialState : State GalilVM := absSC (x0C (blankVML 0) 2048).core

/-- A boot control word is finite and does not contain the future input. -/
def initialControl : Control := Sum.inl ()

def Enc (w : List (Fin 2)) (x : State GalilVM) (p : PhysicalState) : Prop :=
  match p.1 with
  | .inl _ => x = initialState ∧ ∀ tape,
      PalPeg.CloseoutCoreEnc12.TEqG blankM (STape.blankTape blankM) (p.2 tape)
  | .inr q => PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x (q, p.2)

/-- The outer encoding accepts exactly the consumer's blank initial configuration.
This does not yet supply the boot transition of a concrete `L0`. -/
theorem enc_initial (w : List (Fin 2)) :
    Enc w initialState (initialControl, fun _ => STape.blankTape blankM) := by
  exact ⟨rfl, fun _ => ⟨rfl, fun _ => rfl⟩⟩

/-- The padded encoding cannot itself be used as the consumer's blank boot case. -/
theorem padded_not_blank {fb db : ℕ} (w : List (Fin 2)) (padding : ℕ)
    (x : State GalilVM) (q : QPhys fb db) :
    ¬ PalPeg.PhysicalEncoding.Enc w padding x (q, fun _ => STape.blankTape blankM) := by
  intro henc
  have hpos := congrArg PalPeg.Local.pos (henc.2.fpp 0)
  rw [PalPeg.PhysicalEncoding.pos_padLeft] at hpos
  change 0 = _ + padding + 1 at hpos
  omega

/-- A running configuration supplies the fused radius on every physical tape. -/
theorem running_margin {w : List (Fin 2)} {x : State GalilVM}
    {q : CoreControl} {T : Fin tapeCountM → STape Γm}
    (henc : Enc w x (Sum.inr q, T)) (tape : Fin tapeCountM) :
    macroRadius ≤ PalPeg.Local.pos (T tape) := by
  obtain ⟨ideal, hexact, hteq⟩ := henc
  have hpos := hexact.1.2.margins (slotIndex.symm tape)
  simp only [Equiv.apply_symm_apply] at hpos
  rw [(hteq tape).1] at hpos
  exact hpos

/-- The same closure preserves the finite macro-boundary facts. -/
theorem running_boundary {w : List (Fin 2)} {x : State GalilVM}
    {q : CoreControl} {T : Fin tapeCountM → STape Γm}
    (henc : Enc w x (Sum.inr q, T)) : MacroBoundary q := by
  obtain ⟨_, hexact, _⟩ := henc
  exact hexact.2

/-- The eight proof arguments of the fixed final consumer. Moving ticks retain
ArrivedOnRun, including the consumed-input bound furnished by the actual tracked
run. Other contracts keep their existing OnRun and InvC premises. -/
structure Obligations {Q Γ : Type} {t K : ℕ} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ) (q0 : Q) (repQ outQ : Q → Bool)
    (Enc : List (Fin 2) → State GalilVM → Q × (Fin t → STape Γ) → Prop)
    (PhysFrozen : List (Fin 2) → Q × (Fin t → STape Γ) → Prop) : Prop where
  hencInit : ∀ w, Enc w (absSC (x0C (blankVML 0) 2048).core)
      (q0, fun _ => STape.blankTape blankSymbol)
  hforwardTick : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p successor, PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m → ¬ frozenAt w m →
        Enc w (absSC m) p →
        TickSucc (PofC centreC placeC 0 w) 1 0 2048
          (PalPeg.GalilTickFair.Canonical 0 2048) (Starved m.vm) (absSC m) successor →
        Enc w successor (L0.apply blankSymbol p none)
  hforwardFeed : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ letter m p, InvC (localGood (spare := 0)) w (heldAfter (Tc w.length) st) m →
        Enc w (absSC m) p →
        Enc w (PalPeg.GalilArriveChain.arriveState' letter (absSC m))
          (L0.apply blankSymbol p (some letter))
  hfrozenEnter : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m → frozenAt w m →
        Enc w (absSC m) p → PhysFrozen w p
  hfrozenKeep : ∀ (w : List (Fin 2)) p, PhysFrozen w p →
      PhysFrozen w (L0.apply blankSymbol p none)
  hfrozenQuiet : ∀ (w : List (Fin 2)) p, PhysFrozen w p → repQ p.1 = false
  hencRep : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        Enc w (absSC m) p → reportArrived 0 1 0 w (absSC m) = repQ p.1
  hencOut : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
      PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
      ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
        Enc w (absSC m) p → ReportPoint w (absSC m) →
        m.vm.ctl.output = outQ p.1

/-- Dispatcher obligations retain the actual run and canonical trace. In
particular a source invariant used by one branch need not hold on every state. -/
structure TickCases {Q Γ : Type} {t K : ℕ}
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ)
    (Enc : List (Fin 2) → State GalilVM → Q × (Fin t → STape Γ) → Prop) : Prop where
  starved : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
    PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
    ∀ m p, OnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
      ¬ frozenAt w m → Enc w (absSC m) p →
      PalPeg.FrameFunction.starvedTest (absSC m) = true →
      Enc w (absSC m) (L0.apply blankSymbol p none)
  active : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ),
    PreTraceIMW centreC placeC 0 1 0 w st Tc → CanonTrace 0 w st Tc →
    ∀ m p, PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m →
      ¬ frozenAt w m → Enc w (absSC m) p →
      PalPeg.FrameFunction.starvedTest (absSC m) = false →
      Tick (galilFrameS (PofC centreC placeC 0 w) 1 0) 2048 (absSC m)
        (PalPeg.GalilScaffoldTop.tickFun
          (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
          (galilFrameS (PofC centreC placeC 0 w) 1 0) 2048 (absSC m)) →
      Enc w (PalPeg.GalilScaffoldTop.tickFun
        (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w)
        (galilFrameS (PofC centreC placeC 0 w) 1 0) 2048 (absSC m))
        (L0.apply blankSymbol p none)

/-- These are exactly the two cases required by `Obligations.hforwardTick`.
All source-specific invariants stay available in the two hypotheses. The active
case also receives the existing relational tick, whose constructors carry the
legality of head moves; it need not reconstruct that evidence from the trace. -/
theorem forwardTick_of_cases {Q Γ : Type} {t K : ℕ}
    (L0 : LocalStep (Fin 2) Q Γ t K) (blankSymbol : Γ)
    (Enc : List (Fin 2) → State GalilVM → Q × (Fin t → STape Γ) → Prop)
    (hcases : TickCases L0 blankSymbol Enc)
    (w : List (Fin 2)) (st : ℕ → State GalilVM) (Tc : ℕ → ℕ)
    (hpre : PreTraceIMW centreC placeC 0 1 0 w st Tc) (hcanon : CanonTrace 0 w st Tc)
    (m : Mirrored1 (tapeCount 0)) (p : Q × (Fin t → STape Γ)) (successor : State GalilVM)
    (hon : PalPeg.LocalShadowConcrete.ArrivedOnRun (localGood (spare := 0)) (postPhase 0 1 0) w (heldAfter (Tc w.length) st) m)
    (hnotFrozen : ¬ frozenAt w m) (henc : Enc w (absSC m) p)
    (hsucc : TickSucc (PofC centreC placeC 0 w) 1 0 2048
      (PalPeg.GalilTickFair.Canonical 0 2048) (Starved m.vm) (absSC m) successor) :
    Enc w successor (L0.apply blankSymbol p none) := by
  rcases hsucc with ⟨hstarved, hkept⟩ | ⟨hmoves, htick, hcanonical⟩
  · rw [hkept]
    exact hcases.starved w st Tc hpre hcanon m p hon.onRun hnotFrozen henc
      ((PalPeg.ShadowedLocalFinal.starvedAbs_iff _).mp
        (PalPeg.ShadowedLocalFinal.starvedAbs_absSC.mpr hstarved))
  · have hcomputes := PalPeg.FrameFunction.computes_galilFrameFun centreC placeC 0 1 0 w successor.vm
    have hrestartFirst : (absSC m).ctl.mode = Mode.scan →
        (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).restartGuard (absSC m).vm = true →
        successor = ⟨{(absSC m).ctl with clock := 2048},
          (PalPeg.FrameFunction.galilFrameFun centreC placeC 0 1 0 w).restart (absSC m).vm⟩ := by
      intro hmode hguard
      obtain ⟨hctl, hrestart⟩ := hcanonical.restartFirst hmode
        ((restartGuardTest_iff _).mpr hguard)
      obtain ⟨-, hvm⟩ := hcomputes.restart _ _ hrestart
      exact (show (⟨successor.ctl, successor.vm⟩ : State GalilVM) = _ by rw [hctl, hvm])
    have hstep := PalPeg.GalilScaffoldTop.tick_eq_tickFun hcomputes htick hrestartFirst
      hcanonical.fallbackPlace
    rw [hstep] at htick ⊢
    exact hcases.active w st Tc hpre hcanon m p hon hnotFrozen henc
      (PalPeg.GalilScaffoldTop.bool_ne_true (fun hs => hmoves
        (PalPeg.ShadowedLocalFinal.starvedAbs_absSC.mp
          ((PalPeg.ShadowedLocalFinal.starvedAbs_iff _).mpr hs)))) htick

/-- info: 'PalPeg.PhysicalContract.forwardTick_of_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms forwardTick_of_cases

end PalPeg.PhysicalContract
