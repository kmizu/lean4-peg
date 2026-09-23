import PalPeg.ChainBoundaryCache
import PalPeg.PhysicalEncoding
import PalPeg.LocalRoles

/-!
# Bounded counter rebuilding and finite boundary-role rotation

The window compiler emits one action per increment and carries the new sign
between actions, including zero crossings. It works for a source and its
independent mirrors without equating their discarded tape segments.
The boundary schedule selects at most three such actions. Allocation and the
whole-machine dispatcher remain separate obligations.
-/
set_option autoImplicit false

namespace PalPeg.PhysicalCounterCache
open PalPeg.PhysicalEncoding PalPeg.ChainBoundaryCache
open PalPeg.GalilScaffoldCounter PalPeg.LocalCounter
open PalPeg.Program PalPeg.Local PalPeg.LocalStepFusion
open PalPeg.CloseoutCoreEnc12

/-- All decisions are taken from the same finite source window. -/
def increments {K : ℕ} (count : ℕ) (polarity : Bool) (window : Window Γm K) :
    Bool × List (Act Γm) :=
  match count with
  | 0 => (polarity, [])
  | n+1 =>
    let prior := increments n polarity window
    let bit := prior.1 || decide ((windowAfter K 1 window prior.2) 0 ≠ encSeg mark)
    (bit, prior.2 ++ [if bit then some (encSeg mark, .right) else some (blankM, .left)])

theorem increments_length {K : ℕ} (count : ℕ) (polarity : Bool) (window : Window Γm K) :
    (increments count polarity window).2.length = count := by
  induction count with
  | zero => rfl
  | succ n ih => simp only [increments, List.length_append, List.length_singleton, ih]

/-- The emitted actions update both source and arbitrary independently padded
mirror tapes. The source window suffices for every sign decision. -/
theorem increments_encode {K margin : ℕ} (count : ℕ) (hcount : count ≤ K)
    (hmargin : K ≤ margin) (polarity : Bool) (source segments : STape Seg) (c : Counter)
    (hsource : absCtr source polarity = c) (hsegments : absCtr segments polarity = c) :
    let compiled := increments count polarity (readWin blankM K (padLeft margin (mapTape encSeg source)))
    ∃ result : STape Seg, absCtr result compiled.1 = advanceCounter count c ∧
      actList blankM (padLeft margin (mapTape encSeg segments)) compiled.2
        = padLeft margin (mapTape encSeg result) := by
  induction count generalizing segments with
  | zero => exact ⟨segments, hsegments, rfl⟩
  | succ n ih =>
    let window := readWin blankM K (padLeft margin (mapTape encSeg source))
    let prior := increments n polarity window
    let bit := prior.1 || decide ((windowAfter K 1 window prior.2) 0 ≠ encSeg mark)
    obtain ⟨source', hsource', hsourceTape⟩ := ih (by omega) source hsource
    obtain ⟨segments', hsegments', hsegmentsTape⟩ := ih (by omega) segments hsegments
    have hw : windowAfter K 1 window prior.2 =
        readWin blankM 1 (padLeft margin (mapTape encSeg source')) := by
      rw [windowAfter_readWin blankM _ _
        (by simpa only [prior, increments_length] using hcount)
        (by rw [pos_padLeft]; omega)]
      exact congrArg (readWin blankM 1) hsourceTape
    have hbitSource : bit = (prior.1 || decide (val source' = 0)) := by
      dsimp only [bit]
      rw [hw]
      apply congrArg (fun b : Bool => prior.1 || b)
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      exact (counterZero_iff_below (K := 1) (margin := margin) (by decide) (by omega) source').symm
    have hsame : val segments' = val source' :=
      val_eq_of_absCtr_eq (hsegments'.trans hsource'.symm)
    have hbitTarget : bit = (prior.1 || decide (val segments' = 0)) := by
      rw [hsame]; exact hbitSource
    obtain ⟨result, habs, hacts⟩ := counter_inc_at (fun _ => prior.1) 0 bit
      segments' (advanceCounter n c) hsegments' hbitTarget
      (actList blankM (padLeft margin (mapTape encSeg segments)) prior.2) hsegmentsTape
    refine ⟨result, ?_, ?_⟩
    · change absCtr result bit = advanceCounter (n+1) c
      rw [advanceCounter_succ]
      exact habs
    · change actList blankM (padLeft margin (mapTape encSeg segments))
        (prior.2 ++ [if bit then some (encSeg mark, .right) else some (blankM, .left)]) = _
      rw [PalPeg.CloseoutCoreEnc13.actList_append]
      exact hacts

/-- The boundary cache needs at most three actions per tape, independently of
counter size, period length, and number of previous shifts. -/
theorem boundary_actions_length {K : ℕ} (phase : Fin 5) (polarity : Bool)
    (window : Window Γm K) : (increments (rate phase) polarity window).2.length ≤ 3 := by
  rw [increments_length]
  exact rate_le phase

/-- At a real period boundary the prepared physical spare represents the new
distance. The result can become boundary by a finite role rotation. -/
theorem boundary_spare {K margin h age : ℕ} {s : PalPeg.GalilScaffoldChainConsume.State}
    {spare : Counter} (hi : Inv h age s spare)
    (he : boundaryEvent s = true) (hd : Canonical s.distance)
    (hK : 3 ≤ K) (hmargin : K ≤ margin) (polarity : Bool)
    (source segments : STape Seg)
    (hsource : absCtr source polarity = spare) (hsegments : absCtr segments polarity = spare) :
    let compiled := increments (rate s.phase) polarity
      (readWin blankM K (padLeft margin (mapTape encSeg source)))
    ∃ result : STape Seg, absCtr result compiled.1 = inc s.distance ∧
      actList blankM (padLeft margin (mapTape encSeg segments)) compiled.2
        = padLeft margin (mapTape encSeg result) := by
  have hcanonical : Canonical spare := hsource ▸ absCtr_canonical source polarity
  obtain ⟨result, habs, hacts⟩ := increments_encode (rate s.phase)
    (Nat.le_trans (rate_le _) hK) hmargin polarity source segments spare hsource hsegments
  exact ⟨result, habs.trans (spare_eq_at_boundary hi he hcanonical hd), hacts⟩

open PalPeg.LocalRoles

/-- Logical roles 0/1/2 are boundary/last/spare. Rotation writes no tape. -/
def rotate {α : Type} (roles : Fin 3 → α) : Fin 3 → α :=
  fun i => roles (swapAt 0 1 (swapAt 0 2 i))

theorem rotate_injective {α : Type} {roles : Fin 3 → α} (hi : Function.Injective roles) :
    Function.Injective (rotate roles) :=
  hi.comp ((swapAt_injective 0 1).comp (swapAt_injective 0 2))

/-- The old boundary and last survive on separate tapes after the exchange. -/
theorem rotate_values {P : ℕ} (phys : Fin P → STape Seg)
    (roles : Fin 3 → Fin P) (pol : Fin 3 → Bool) :
    absL phys (rotate roles) (rotate pol) 0 = absL phys roles pol 2 ∧
    absL phys (rotate roles) (rotate pol) 1 = absL phys roles pol 0 ∧
    absL phys (rotate roles) (rotate pol) 2 = absL phys roles pol 1 := by
  simp [absL, rotate, swapAt]

/-- Rebuild and rotate the three independent tapes. This implements both
FIRST and LAST boundary assignments of the actual `consume` operation. -/
theorem boundary_rotate {K margin h age P : ℕ}
    {s : PalPeg.GalilScaffoldChainConsume.State} {spare : Counter}
    (hi : Inv h age s spare) (he : boundaryEvent s = true)
    (a : Fin 3) (ha : PalPeg.GalilScaffoldChainConsume.symbol s.period.focus = some a)
    (hd : Canonical s.distance) (hK : 3 ≤ K) (hmargin : K ≤ margin)
    (bank : Fin P → STape Seg) (roles : Fin 3 → Fin P) (pol : Fin 3 → Bool)
    (hinj : Function.Injective roles)
    (hboundary : absL bank roles pol 0 = s.boundary)
    (hlast : absL bank roles pol 1 = s.last)
    (hspare : absL bank roles pol 2 = spare) :
    let compiled := increments (rate s.phase) (pol 2)
      (readWin blankM K (padLeft margin (mapTape encSeg (bank (roles 2)))))
    ∃ result : STape Seg,
      actList blankM (padLeft margin (mapTape encSeg (bank (roles 2)))) compiled.2
        = padLeft margin (mapTape encSeg result) ∧
      let nextBank := Function.update bank (roles 2) result
      let nextPol := Function.update pol 2 compiled.1
      absL nextBank (rotate roles) (rotate nextPol) 0 =
        (PalPeg.GalilScaffoldChainConsume.consume s (some a)).boundary ∧
      absL nextBank (rotate roles) (rotate nextPol) 1 =
        (PalPeg.GalilScaffoldChainConsume.consume s (some a)).last ∧
      absL nextBank (rotate roles) (rotate nextPol) 2 = s.last ∧
      Inv h 0 (PalPeg.GalilScaffoldChainConsume.consume s (some a))
        (absL nextBank (rotate roles) (rotate nextPol) 2) := by
  let compiled := increments (rate s.phase) (pol 2)
    (readWin blankM K (padLeft margin (mapTape encSeg (bank (roles 2)))))
  obtain ⟨result, hresult, hacts⟩ := boundary_spare hi he hd hK hmargin (pol 2)
    (bank (roles 2)) (bank (roles 2)) hspare hspare
  refine ⟨result, hacts, ?_⟩
  let nextBank := Function.update bank (roles 2) result
  let nextPol := Function.update pol 2 compiled.1
  have hr0 : roles 0 ≠ roles 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)
  have hr1 : roles 1 ≠ roles 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hinj h)
  have hb : absL nextBank roles nextPol 0 = s.boundary := by
    simpa [absL, nextBank, nextPol, hr0] using hboundary
  have hl : absL nextBank roles nextPol 1 = s.last := by
    simpa [absL, nextBank, nextPol, hr1] using hlast
  have hs : absL nextBank roles nextPol 2 = inc s.distance := by
    simpa [absL, nextBank, nextPol] using hresult
  obtain ⟨hbRot, hlRot, hsRot⟩ := rotate_values nextBank roles nextPol
  change absL nextBank (rotate roles) (rotate nextPol) 0 = _ ∧
    absL nextBank (rotate roles) (rotate nextPol) 1 = _ ∧
    absL nextBank (rotate roles) (rotate nextPol) 2 = _ ∧ _
  rw [hbRot, hlRot, hsRot, hb, hl, hs]
  have he' : (PalPeg.GalilScaffoldChainPeriod.isFirst s.period.focus ||
    PalPeg.GalilScaffoldChainConsume.isLast s.period.focus) = true := he
  refine ⟨by simp [PalPeg.GalilScaffoldChainConsume.consume, ha, he'],
    by simp [PalPeg.GalilScaffoldChainConsume.consume, ha, he'], rfl, ?_⟩
  simpa only [nextAge, nextSpare, he, if_true] using inv_consume hi a ha

/-- info: 'PalPeg.PhysicalCounterCache.increments_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms increments_encode

/-- info: 'PalPeg.PhysicalCounterCache.boundary_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_rotate

/-- info: 'PalPeg.PhysicalCounterCache.rotate_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rotate_values

end PalPeg.PhysicalCounterCache
