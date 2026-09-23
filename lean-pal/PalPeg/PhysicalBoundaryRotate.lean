import PalPeg.PhysicalConsumeStage
import PalPeg.PhysicalCacheInvariant
import PalPeg.PhysicalRoles

/-!
# Boundary snapshots by finite role exchange

After the ordinary consuming step, boundary and last still denote their old
snapshots. The prepared spare becomes boundary, old boundary becomes last, and
old last becomes spare. This proof transports the whole existing encoding;
heads, program tapes and mirrors retain their current physical tapes.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalBoundaryRotate
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract PalPeg.PhysicalConsumeStage
open PalPeg.PhysicalCountConsume PalPeg.PhysicalSpare PalPeg.PhysicalRoles
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.Program (STape)
open PalPeg.Local (pos)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.GalilScaffoldChainWatch (caught)
open PalPeg.GalilScaffoldCounter (Counter inc)
open PalPeg.CloseoutCoreEnc12

def rotatePol (pol : Fin 16 → Bool) : Fin 16 → Bool := fun c =>
  if c = 14 then pol 10 else if c = 15 then pol 14 else if c = 10 then pol 15 else pol c

noncomputable def rotateTapes (T : Slot → STape Γm) : Slot → STape Γm := fun slot =>
  if slot = counterSlot 14 then T (counterSlot 10)
  else if slot = counterSlot 15 then T (counterSlot 14)
  else if slot = counterSlot 10 then T (counterSlot 15) else T slot

def rotateControl (q : CoreControl) : CoreControl := {q with polarity := rotatePol q.polarity}

noncomputable def rotateCore (p : CoreState) : CoreState :=
  (rotateControl p.1, fun j => p.2 (boundaryRoles j))

theorem rotated_tapes (T : Fin tapeCountM → STape Γm) :
    (fun slot => T (boundaryRoles (slotIndex slot))) = rotateTapes (fun slot => T (slotIndex slot)) := by
  funext slot
  by_cases hb : slot = counterSlot 14
  · subst slot
    simp [rotateTapes, boundaryRoles_boundary]
  by_cases hl : slot = counterSlot 15
  · subst slot
    simp [rotateTapes, boundaryRoles_last, counterSlot]
  by_cases hs : slot = counterSlot 10
  · subst slot
    simp [rotateTapes, boundaryRoles_spare, counterSlot]
  rw [boundaryRoles_other _ (fun h => hb (slotIndex.injective h))
    (fun h => hl (slotIndex.injective h)) (fun h => hs (slotIndex.injective h))]
  simp [rotateTapes, hb, hl, hs]

/-- No physical control observation depends on the two snapshot values. -/
theorem encControl_unstaged {w : List (Fin 2)} {x : State GalilVM} {q : CoreControl}
    {wm : PalPeg.GalilScaffoldChainWatch.State}
    (he : EncControl w (stagedState x wm) q) : EncControl w (caughtState x wm) q :=
  ⟨he.ctl, he.chainTag, he.chainPhase, he.chainForward, he.chainBroken,
    he.fppMode, he.fppFinalStage, he.fppPc, he.fppDone, he.dpPc, he.dpDone,
    he.searchMode, he.searchFinalStage, he.searchQuarter, he.periodOnly,
    he.placeGap, he.onLetter, he.leftFirst⟩

/-- The existing slot predicate after rotating the three counter tapes. -/
theorem tapes_rotate (x : State GalilVM) (q : CoreControl)
    (T : Slot → STape Γm) (wm : PalPeg.GalilScaffoldChainWatch.State)
    (he : EncTapes margin (stagedState x wm) q.polarity q.gap q.micro q.fppLive q.dpLive T)
    (hb : (caught wm).machine.control.boundary = inc wm.machine.control.distance)
    (hl : (caught wm).machine.control.last = wm.machine.control.boundary)
    (seg : STape Seg) (hseg : absCtr seg (q.polarity 10) = inc wm.machine.control.distance)
    (htape : T (counterSlot 10) = padLeft margin (mapTape encSeg seg)) :
    EncTapes margin (caughtState x wm) (rotatePol q.polarity) q.gap q.micro q.fppLive q.dpLive
      (rotateTapes T) where
  margins := by
    intro slot
    simp only [rotateTapes]
    split_ifs <;> exact he.margins _
  heads := by
    intro v head hh
    obtain ⟨view, vt, ha, hv, hs, hc, hw⟩ := he.heads v head hh
    exact ⟨view, vt, ha, hv, fun i => by simpa [rotateTapes, counterSlot] using hs i, hc, hw⟩
  idleHead := by
    intro hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := he.idleHead hh
    exact ⟨view, vt, hv, fun i => by simpa [rotateTapes, counterSlot, headSlot] using hs i, hc, hw⟩
  fpp := by
    intro i
    cases hb : q.fppLive <;> simpa [rotateTapes, progSlotOf, counterSlot, hb, stagedState, caughtState] using he.fpp i
  dp := by
    intro i
    cases hb : q.dpLive <;> simpa [rotateTapes, dpSlotOf, counterSlot, hb, stagedState, caughtState] using he.dp i
  idleShape := by
    intro i
    cases hb : q.fppLive <;> simpa [rotateTapes, progSlotOf, counterSlot, hb] using he.idleShape i
  counters := by
    intro c value hv
    by_cases hc14 : c = 14
    · subst c
      have hvalue : inc wm.machine.control.distance = value := by
        simpa only [counterOf, caughtState, hb, Option.some.injEq] using hv
      exact ⟨seg, by simpa [rotatePol, hvalue] using hseg,
        by simpa [rotateTapes] using htape⟩
    by_cases hc15 : c = 15
    · subst c
      have hvalue : wm.machine.control.boundary = value := by
        simpa only [counterOf, caughtState, hl, Option.some.injEq] using hv
      obtain ⟨raw, ha, ht⟩ := he.counters 14 wm.machine.control.boundary rfl
      exact ⟨raw, by simpa [rotatePol, hvalue] using ha,
        by simpa [rotateTapes, counterSlot] using ht⟩
    by_cases hc10 : c = 10
    · subst c
      cases hv
    have hsame : counterOf (stagedState x wm) c = counterOf (caughtState x wm) c := by
      fin_cases c <;> first | exact (hc14 rfl).elim | exact (hc15 rfl).elim | rfl
    obtain ⟨raw, ha, ht⟩ := he.counters c value (hsame.trans hv)
    exact ⟨raw, by simpa [rotatePol, hc14, hc15, hc10] using ha,
      by simpa [rotateTapes, counterSlot, hc14, hc15, hc10] using ht⟩
  places := by
    intro i place hp
    obtain ⟨stack, junk, hj, hs, ht⟩ := he.places i place hp
    exact ⟨stack, junk, hj, hs, by simpa [rotateTapes, counterSlot] using ht⟩
  mirrors := by
    intro m value hv
    have hn14 : mirrorSource m ≠ 14 := by fin_cases m <;> decide
    have hn15 : mirrorSource m ≠ 15 := by fin_cases m <;> decide
    have hn10 : mirrorSource m ≠ 10 := by
      intro hn
      rw [hn] at hv
      cases hv
    have hsame : counterOf (stagedState x wm) (mirrorSource m) =
        counterOf (caughtState x wm) (mirrorSource m) := by fin_cases m <;> rfl
    obtain ⟨raw, ha, ht⟩ := he.mirrors m value (hsame.trans hv)
    exact ⟨raw, by simpa [rotatePol, hn14, hn15, hn10] using ha,
      by simpa [rotateTapes, counterSlot] using ht⟩
  period := by
    intro tape ht
    simpa [rotateTapes, counterSlot] using he.period tape ht
  answer := by
    intro tape ht
    simpa [rotateTapes, counterSlot] using he.answer tape ht

/-- All represented fields and macro-boundary facts survive the role exchange. -/
theorem core_rotate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State) (he : CoreEnc w (stagedState x wm) p)
    (hb : (caught wm).machine.control.boundary = inc wm.machine.control.distance)
    (hl : (caught wm).machine.control.last = wm.machine.control.boundary)
    (seg : STape Seg) (hseg : absCtr seg (p.1.polarity 10) = inc wm.machine.control.distance)
    (htape : p.2 spareIndex = padLeft margin (mapTape encSeg seg)) :
    CoreEnc w (caughtState x wm) (rotateCore p) := by
  refine ⟨⟨PalPeg.PhysicalFreeCounter.encControl_polarity (encControl_unstaged he.1.1) _, ?_⟩, he.2⟩
  change EncTapes margin (caughtState x wm) (rotatePol p.1.polarity) p.1.gap p.1.micro p.1.fppLive p.1.dpLive
    (fun slot => p.2 (boundaryRoles (slotIndex slot)))
  rw [rotated_tapes]
  exact tapes_rotate x p.1 (fun slot => p.2 (slotIndex slot)) wm he.1.2 hb hl seg hseg htape


/-- Rotate actual sweep tapes using only their observational representations. -/
theorem running_rotate (w : List (Fin 2)) (x : State GalilVM) (p : CoreState)
    (wm : PalPeg.GalilScaffoldChainWatch.State)
    (he : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (stagedState x wm) p)
    (hb : (caught wm).machine.control.boundary = inc wm.machine.control.distance)
    (hl : (caught wm).machine.control.last = wm.machine.control.boundary)
    (hs : Rep (p.1.polarity 10) (inc wm.machine.control.distance) (p.2 spareIndex)) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) (caughtState x wm) (rotateCore p) ∧
      Rep ((rotateCore p).1.polarity 10) wm.machine.control.last ((rotateCore p).2 spareIndex) := by
  obtain ⟨T, hT, ht⟩ := he
  obtain ⟨seg, hseg, hs⟩ := hs
  let U := Function.update T spareIndex (padLeft margin (mapTape encSeg seg))
  have hcore : CoreEnc w (stagedState x wm) (p.1, U) := by
    have hm : margin ≤ pos (padLeft margin (mapTape encSeg seg)) := by rw [pos_padLeft]; omega
    have hp : PalPeg.PhysicalFreeCounter.setPolarity p.1 10 (p.1.polarity 10) = p.1 := by
      unfold PalPeg.PhysicalFreeCounter.setPolarity
      rw [Function.update_eq_self]
    simpa only [hp, U, spareIndex] using
      PalPeg.PhysicalFreeCounter.core_free_counter hT 10 rfl (p.1.polarity 10) _ hm
  have hu : ∀ j, TEqG blankM (U j) (p.2 j) := by
    intro j
    by_cases hj : j = spareIndex
    · subst j; simpa only [U, Function.update_self] using hs
    · simpa only [U, Function.update_of_ne hj] using ht j
  constructor
  · exact ⟨fun j => U (boundaryRoles j),
      core_rotate w x (p.1, U) wm hcore hb hl seg hseg (Function.update_self _ _ _),
      fun j => hu (boundaryRoles j)⟩
  · obtain ⟨lastSeg, hlast, htape⟩ := hT.1.2.counters 15 wm.machine.control.last rfl
    refine ⟨lastSeg, ?_, ?_⟩
    · simpa [rotateCore, rotateControl, rotatePol] using hlast
    · change TEqG blankM (padLeft margin (mapTape encSeg lastSeg))
        (p.2 (boundaryRoles (slotIndex (counterSlot 10))))
      rw [boundaryRoles_spare, ← htape]
      exact ht _

/-- info: 'PalPeg.PhysicalBoundaryRotate.running_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_rotate

end PalPeg.PhysicalBoundaryRotate
