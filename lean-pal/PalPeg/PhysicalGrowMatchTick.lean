import PalPeg.PhysicalGrowMatch
import PalPeg.PhysicalLoanAssembly

/-! # A grow comparison, its finite control and both cursor moves

The nonhead row and the twelve-slot executor belong to one macro sweep.
The idle verifier has no abstract head and receives the stay command.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PalPeg.PhysicalGrowMatchTick
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program PalPeg.Local PalPeg.CloseoutCoreEnc12 PalPeg.LocalStepFusion
open PalPeg.PhysicalDebtMirror (RebuildingCore Rebuilding repaired repair)
open PalPeg.PhysicalGrowMatch (body prepared moved)
open PalPeg.PhysicalLoanInvariant (Balanced)
open PalPeg.GalilScaffoldInputHead (left PlaceHead)
open PalPeg.GalilScaffoldChainVerifier (right canRight)

def target (w : List (Fin 2)) (x : State GalilVM) : State GalilVM :=
  ⟨{x.ctl with clock := 2048, output := if onLetterTest w (moved x) then leftFirstTest (moved x) else x.ctl.output, replaying := x.ctl.replaying && !PalPeg.GalilScaffoldCounter.zero (moved x).replay}, moved x⟩

def commands (v : Fin 4) : PalPeg.ConcreteLocalMachine.ViewCommand :=
  if v = 0 then .moveLeft else if v = 2 then .moveRight else .stay

def headMove (v : Fin 4) (head : PlaceHead) : PlaceHead :=
  if v = 0 then left head else if v = 2 then right head else head

noncomputable def next (q : CoreControl) (input : Option (Fin 2))
    (ws : Fin tapeCountM → Window Γm microRadius) : CoreControl :=
  {body.nq q input ws with ctl := scanMatchedCtl q ws, onLetterBit := scanRightOnLetter q ws, leftFirstBit := scanLeftFirst q ws}

noncomputable def rule : ActRule (Fin 2) CoreControl Γm tapeCountM microRadius :=
  tickRule (by decide) next (fun _ _ _ => commands) body.acts body.len_le

def roles : PalPeg.LocalRoleRouting.RoleChange (Fin 2) CoreControl Γm tapeCountM microRadius :=
  fun _ _ _ => Equiv.refl _

theorem reads_repaired {K : ℕ} (q : CoreControl) (T : Fin tapeCountM → STape Γm) :
    scanRightOnLetter q (fun j => readWin blankM K (repaired T j)) =
      scanRightOnLetter q (fun j => readWin blankM K (T j)) ∧
    scanLeftFirst q (fun j => readWin blankM K (repaired T j)) =
      scanLeftFirst q (fun j => readWin blankM K (T j)) ∧
    scanReplayZero q (fun j => readWin blankM K (repaired T j)) =
      scanReplayZero q (fun j => readWin blankM K (T j)) := by
  constructor
  · simp only [scanRightOnLetter, landingLetter, PalPeg.PhysicalDebtFeed.view_repaired]
  constructor
  · simp [scanLeftFirst, centreRead, belowRead, repaired, repair, headSlot, mirrorSlot] <;> rfl
  · simp [scanReplayZero, decAct, decActAt, decSignAt, belowRead, repaired, repair, counterSlot, mirrorSlot] <;> rfl

theorem next_control (w arrived : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p)
    (hn : EncControl w (prepared x) (body.nq p.1 none (fun j => readWin blankM microRadius (p.2 j))))
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    EncControl w (target w x) (next p.1 none (fun j => readWin blankM microRadius (p.2 j))) := by
  have hs := he.1.1.1.1
  let T := fun slot => repaired p.2 (slotIndex slot)
  have ht : tapesOf T = repaired p.2 := by funext j; simp [T, tapesOf]
  have hreads := reads_repaired (K := microRadius) p.1 p.2
  have hon := scanRightOnLetter_eq w arrived hs.2 micro_le_margin hright hrep hlen
  have hf := scanLeftFirst_eq hs.2 (by decide : 1 ≤ microRadius) micro_le_margin
  have hz := scanReplayZero_eq hs.2 (by decide : 2 ≤ microRadius) micro_le_margin
  change scanRightOnLetter p.1 (fun j => readWin blankM microRadius (tapesOf T j)) = _ at hon
  change scanLeftFirst p.1 (fun j => readWin blankM microRadius (tapesOf T j)) = _ at hf
  change scanReplayZero p.1 (fun j => readWin blankM microRadius (tapesOf T j)) = _ at hz
  rw [ht, hreads.1] at hon
  rw [ht, hreads.2.1] at hf
  rw [ht, hreads.2.2] at hz
  have hon' : scanRightOnLetter p.1 (fun j => readWin blankM microRadius (p.2 j)) = onLetterTest w (moved x) := hon
  have hf' : scanLeftFirst p.1 (fun j => readWin blankM microRadius (p.2 j)) = leftFirstTest (moved x) := hf
  have hrepctl : p.1.ctl.replaying = x.ctl.replaying := congrArg PalPeg.GalilScaffoldController.Control.replaying hs.1.ctl
  have hout : p.1.ctl.output = x.ctl.output := congrArg PalPeg.GalilScaffoldController.Control.output hs.1.ctl
  have hstop : (p.1.ctl.replaying && !scanReplayZero p.1 (fun j => readWin blankM microRadius (p.2 j))) =
      (x.ctl.replaying && !PalPeg.GalilScaffoldCounter.zero (moved x).replay) := by
    rw [hrepctl, hz]
    cases hr : x.ctl.replaying <;> simp [moved, prepared, PalPeg.PhysicalMatchCounters.prepared,
      PalPeg.PhysicalGrowCount.grown, PalPeg.PhysicalDebtRebuild.paid, PalPeg.PhysicalGrowStorage.prepared, hr]
  refine ⟨?_, hn.chainTag, hn.chainPhase, hn.chainForward, hn.chainBroken,
    hn.fppMode, hn.fppFinalStage, hn.fppPc, hn.fppDone, hn.dpPc, hn.dpDone,
    hn.searchMode, hn.searchFinalStage, hn.searchQuarter, hn.periodOnly, ?_, hon', hf'⟩
  · change ctlAbs (scanMatchedCtl p.1 (fun j => readWin blankM microRadius (p.2 j))) = _
    change {ctlAbs p.1.ctl with clock := 2048, output := if scanRightOnLetter p.1 (fun j => readWin blankM microRadius (p.2 j)) then scanLeftFirst p.1 (fun j => readWin blankM microRadius (p.2 j)) else p.1.ctl.output, replaying := p.1.ctl.replaying && !scanReplayZero p.1 (fun j => readWin blankM microRadius (p.2 j))} = _
    rw [hstop, hon', hf', hout, hs.1.ctl]
    rfl
  · intro i place hp
    apply hn.placeGap i place
    fin_cases i <;> exact hp

theorem headOp_commands (v : Fin 4) : headOp (commands v) = some (headMove v) := by
  fin_cases v <;> rfl

theorem target_heads (w : List (Fin 2)) (x : State GalilVM) (v : Fin 4) :
    headOf (target w x) v = (headOf x v).map (headMove v) := by
  fin_cases v <;> simp [headOf, target, moved, prepared, PalPeg.PhysicalMatchCounters.prepared,
    PalPeg.PhysicalGrowCount.grown, PalPeg.PhysicalDebtRebuild.paid, PalPeg.PhysicalGrowStorage.prepared,
    headMove] <;> cases x.vm.chain <;> rfl

theorem unnamed_stays (x : State GalilVM) (v : Fin 4) (hh : headOf x v = none) : commands v = .stay := by
  fin_cases v <;> simp_all [headOf, commands]

theorem ready (x : State GalilVM) (hright : canRight x.vm.right)
    (v : Fin 4) (head : PlaceHead) (view : PalPeg.LocalInputView.InputView)
    (hh : headOf x v = some head) (ha : PalPeg.LocalArrival.absHead' view [] = head) :
    HeadReady (commands v) view := by
  fin_cases v
  · trivial
  · trivial
  · have heq : head = x.vm.right := Option.some.inj hh.symm
    intro hg hn
    rw [← heq, ← ha] at hright
    simpa [canRight, PalPeg.LocalArrival.absHead', hg, hn] using hright
  · trivial

theorem target_counters (w : List (Fin 2)) (x : State GalilVM) : counterOf (target w x) = counterOf (prepared x) := by
  funext c
  fin_cases c <;> rfl

theorem running_ideal (w arrived : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (he : RebuildingCore w x p) (hb : Balanced x) (hi : x.vm.chain = .idle)
    (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    Rebuilding w (target w x) (idealRun rule blankM p none 12) := by
  generalize htraj : idealRun rule blankM p none = trajectory
  have hr : Rebuilding w x p := ⟨p.2, he, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  have hn := PalPeg.PhysicalGrowMatch.body_ideal w x p hr hb
  have hctl : EncControl w (prepared x) (body.nq p.1 none (fun j => readWin blankM microRadius (p.2 j))) := by
    obtain ⟨_, hU, _⟩ := hn
    exact hU.1.1.1.1.1
  have hrun := PalPeg.PhysicalLoanAssembly.running_tick body roles next (fun _ _ _ => commands)
    w x (prepared x) (target w x) p none he hn (fun _ _ => rfl) ⟨rfl, rfl, rfl⟩
    (next_control w arrived x p he hctl hright hrep hlen) headMove headOp_commands
    (fun v => by rw [target_heads]; simp)
    (fun v head hh => by rw [target_heads, hh]; rfl) (unnamed_stays x)
    (ready x hright) (fun _ => rfl) (fun _ => rfl) (target_counters w x) rfl rfl rfl
    (by intros; simp [PalPeg.PhysicalCacheInvariant.Cache, target, moved, prepared,
      PalPeg.PhysicalMatchCounters.prepared, PalPeg.PhysicalGrowCount.grown,
      PalPeg.PhysicalDebtRebuild.paid, PalPeg.PhysicalGrowStorage.prepared, hi]) rfl
  generalize hother : idealRun (tickRule (by decide : 2 ≤ microRadius) next
    (fun _ _ _ => commands) body.acts body.len_le) blankM p none = other at hrun
  have heq : other = trajectory := hother.symm.trans htraj
  rw [heq] at hrun
  exact hrun

noncomputable def step := PalPeg.LocalRoleRouting.route (compStep (iterRule rule 12))
  (PalPeg.PhysicalTickAssembly.macroRoles roles)

theorem running (w arrived : List (Fin 2)) (x : State GalilVM)
    (p : PalPeg.LocalRoleRouting.Config CoreControl Γm tapeCountM)
    (he : Rebuilding w x (PalPeg.LocalRoleRouting.decode p)) (hb : Balanced x)
    (hi : x.vm.chain = .idle) (hright : canRight x.vm.right)
    (hrep : PalPeg.GalilScaffoldInputTrace.Represents x.vm.right.head arrived)
    (hlen : arrived.length ≤ w.length) :
    Rebuilding w (target w x) (PalPeg.LocalRoleRouting.decode (step.apply blankM p none)) := by
  apply PalPeg.PhysicalLoanAssembly.running_fused_route rule roles w x (target w x) p none he
  intro T hT
  have h := running_ideal w arrived x (_, T) hT hb hi hright hrep hlen
  dsimp only
  generalize hrun : idealRun rule blankM ((PalPeg.LocalRoleRouting.decode p).1, T) none 12 = result at h ⊢
  exact h

/-- info: 'PalPeg.PhysicalGrowMatchTick.running' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running

end PalPeg.PhysicalGrowMatchTick
