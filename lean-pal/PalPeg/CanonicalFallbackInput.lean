import PalPeg.BranchSupply
import PalPeg.CanonicalFallback
import PalPeg.GalilLeafDp
import PalPeg.GalilPlaceEvents
import PalPeg.CanonicalSearchProgram

/-! # Fallback inputs from the actual finite packed prefix

No completed trace or cycle oracle is assumed: the prefix ending at the
mismatch supplies the counters and head geometry for the concrete fallback.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PalPeg.CanonicalFallbackInput
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilInvPlus3 PalPeg.GalilInvPlus2 PalPeg.GalilOracleDischarge
open PalPeg.GalilGlueBLeaves PalPeg.BranchSupply PalPeg.CanonicalFallback
open PalPeg.GalilLeafDp PalPeg.GalilInvPlus2
open PalPeg.GalilPlaceEvents Manacher
open PalPeg.GalilLeafMismatch

variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The scan counter used by fallback is exactly the current palindrome span.
Only the already constructed finite prefix is used. -/
theorem counters {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {c : Control} {s : GalilVM}
    (hRun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) :
    ShiftIdle s ∧ GalilScaffoldCounter.Canonical s.length ∧
    ∃ rad : ℕ, ScanInvariant raw (position s.center) rad s.left s.right ∧
      value s.length = (2*rad+1 : ℕ) := by
  obtain ⟨g,h0,hk,hTrace,_,hPack⟩ := hRun
  have hPrefix : ∀ i, i ≤ k →
      Steps (galilFrameS (PofC centre place entry raw) q first) 2048 i ⟨c₀,r₀⟩ (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact .zero _
    | succ i ih =>
      intro hi
      exact steps_trans (ih (by omega)) (.succ (hTrace.tick i (by omega)) (.zero _))
  have hFloor := hfloor_of_invLP2 centre place entry q first hI.1.1
  have hCP : ∀ i, i ≤ k → PalPeg.GalilCentreLive.CPack q (g i).ctl (g i).vm := by
    intro i hi
    exact PalPeg.GalilCentreLive.cpack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (hPrefix i hi) hFloor
      (PalPeg.GalilCentreLive.cpack_of_entry q hI.1.1.1.1.1 hI.1.1.1.2)
  have hFP : ∀ i, i ≤ k → PalPeg.GalilLengthFloor.FPack (g i).ctl (g i).vm := by
    intro i hi
    exact PalPeg.GalilLengthFloor.fpack_steps (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (hPrefix i hi) (PalPeg.GalilChainCoupling.hbudget_of_invLP centre place entry q first hI.1.1.1)
      (PalPeg.GalilLengthFloor.fpack_of_entry hI.1.1.1 (invLP2_copyIdle hI.1.1))
  have hExact : ∀ i, i ≤ k → RadiusExactOffRewindPhase (g i).ctl (g i).vm := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [h0]
      exact fun _ _ _ => radiusExact_of_entryCounters hI.1.1.1.2
    | succ i ih =>
      intro hi
      apply radiusExactOffRewindPhase_tick_of_replay centre place entry q first
        (hTrace.tick i (by omega))
        (fun hm => ((hFP i (by omega)).notInit hm).elim)
        (fun hm => ?_) (fun _ hr => ?_) (fun hm => ?_) (ih (by omega))
      · obtain ⟨hRep,hPres⟩ := scanRightRepresent (hPack i (by omega)).m2 hm
        exact (represented_position _ raw hRep hPres).1
      · exact PalPeg.CloseoutReplayCanRight.canRight_of_frontPack (hCP i (by omega)).front hr
      · obtain ⟨rem,r,_,_,_,_,_,hLeftPos,_,hLeftNonzero,_⟩ := (hPack i (by omega)).m2.shiftGeom hm
        have hp : 0 < position (g i).vm.center := by omega
        unfold position at hp
        split at hp <;> omega
  have hCPend := hCP k le_rfl
  have hFPend := hFP k le_rfl
  have hExactEnd := hExact k le_rfl
  have hPackEnd := hPack k le_rfl
  rw [hk] at hCPend hFPend hExactEnd hPackEnd
  obtain ⟨rad,hScan⟩ := hPackEnd.pack.scanGeom hm hr
  have hRad := hExactEnd (by rw [hm]; decide) (by rw [hm]; decide) (by rw [hm]; decide)
  change (position s.center : ℤ) + value s.radius = (position s.right : ℤ) at hRad
  have hRight : (position s.right : ℤ) = (position s.center : ℤ) + rad := by
    exact_mod_cast hScan.rightPos
  have hv : value s.radius = (rad : ℤ) := by omega
  have hSpan := hFPend.span (Or.inl hm)
  change value s.length = 2*value s.radius+1 at hSpan
  refine ⟨hCPend.idle (by rw [hm]; decide),hCPend.canon,rad,hScan,?_⟩
  rw [hSpan,hv]
  push_cast
  rfl

/-- A completed DP certificate gives exactly the Galil move bound used by
the canonical fallback branch. -/
theorem move_of_dpPack {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {Rad ℓ : ℕ} {vq : SearchVM} {z : ChainVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hav : canRight s.right) (hlen : value s.length = (2*Rad+1 : ℕ))
    (hkC : Rad < position s.center) (hdp : DpPack raw s Rad)
    (hℓ : ℓ = (value s.length).toNat) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
  have hs1 : s1.right = right s.right := by simp [s1,afterBirth_right,afterMismatch_right]
  have hrrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word _ raw hi.rightRep hav
  have hrpres : (right s.right).head.focus ≠ none := right_present _ raw hi.rightRep hi.rightPresent hav
  obtain ⟨a,xs,rs,q',hdec,hraw⟩ := represents_decompose (right s.right) raw hrrep hrpres
  have hrpos := right_position s.right hav
    (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hstream : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).length
      = position s.center + Rad + 1 := by
    rw [stream_length_of_place a xs rs q' hdec,hrpos,hi.rightPos]
  have hpal : PalAt (encoded ((a :: xs).reverse ++ rs ++ q')) (position s.center) Rad := by
    rw [← hraw]
    exact hi.palindrome
  obtain ⟨x,hwin⟩ := window_eq_cons_span a xs rs q' (right s.right).gap hstream hkC hpal
  rw [← hraw] at hwin
  have hℓrad : ℓ = 2*Rad+1 := by
    rw [hℓ,hlen]
    exact Int.toNat_natCast _
  have hwindow :
      (GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)
        = x :: Span raw (position s.center) Rad := by
    have hp : PalPeg.GalilTickFair.rightPlace s1 = ⟨a :: xs,(right s.right).gap⟩ := by
      apply PalPeg.GalilTickFair.rightPlace_of_represent _ (rs.map some) q'
      rw [hs1]
      exact hdec
    rw [hp]
    rw [hℓrad]
    exact hwin
  have hcontract := contract_of_dpPack hi hkC hdp
  have hmove := PalPeg.galil_move_of_contract x _ (isPal_span_of_palAt hi.palindrome) Rad
    (length_span_of_palAt hi.palindrome) hcontract
  change ℓ / 2 ≤ 4 * (ℓ / 2 + 1 -
    chosenRadius ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)))
  have hk : ℓ / 2 = Rad := by rw [hℓrad]; omega
  rw [hk]
  rw [hwindow]
  exact hmove

/-- An active least-candidate chain gives a coefficient-parametric move bound.
The only machine-side input is `Rad ≤ B*h`; minimality handles periods below
`2*h`, while the radius bound handles all larger periods. -/
theorem move_of_activeScaledBound {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {B Rad h ℓ : ℕ} {vq : SearchVM} {z : ChainVM}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hav : canRight s.right) (hlen : value s.length = (2*Rad+1 : ℕ))
    (hkC : Rad < position s.center)
    (hmin : PalPeg.CanonicalSearchProgram.MoveMinimal raw (position s.center) h)
    (hB : 4 ≤ B) (hbound : Rad ≤ B*h) (hℓ : ℓ = (value s.length).toNat) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ B * (ℓ / 2 + 1 - radius) := by
  let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
  have hs1 : s1.right = right s.right := by simp [s1,afterBirth_right,afterMismatch_right]
  have hrrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word _ raw hi.rightRep hav
  have hrpres : (right s.right).head.focus ≠ none :=
    right_present _ raw hi.rightRep hi.rightPresent hav
  obtain ⟨a,xs,rs,q',hdec,hraw⟩ := represents_decompose (right s.right) raw hrrep hrpres
  have hrpos := right_position s.right hav
    (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hstream : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).length
      = position s.center + Rad + 1 := by
    rw [stream_length_of_place a xs rs q' hdec,hrpos,hi.rightPos]
  have hpal : PalAt (encoded ((a :: xs).reverse ++ rs ++ q')) (position s.center) Rad := by
    rw [← hraw]
    exact hi.palindrome
  obtain ⟨x,hwin⟩ := window_eq_cons_span a xs rs q' (right s.right).gap hstream hkC hpal
  rw [← hraw] at hwin
  have hℓrad : ℓ = 2*Rad+1 := by
    rw [hℓ,hlen]
    exact Int.toNat_natCast _
  have hwindow :
      (GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)
        = x :: Span raw (position s.center) Rad := by
    have hp : PalPeg.GalilTickFair.rightPlace s1 =
        ⟨a :: xs,(right s.right).gap⟩ := by
      apply PalPeg.GalilTickFair.rightPlace_of_represent _ (rs.map some) q'
      rw [hs1]
      exact hdec
    rw [hp,hℓrad]
    exact hwin
  have hcontract : ∀ p, 0 < p →
      HasPeriod (Span raw (position s.center) Rad) p → 2*Rad ≤ B*p := by
    intro p hp hper
    by_cases hgoal : 2*Rad ≤ B*p
    · exact hgoal
    have hpRad : 2*p ≤ Rad := by
      by_contra hn
      have hpRad' : Rad < 2*p := by omega
      have h4p : 4*p ≤ B*p := Nat.mul_le_mul_right p hB
      omega
    have hpo : PeriodOn (encoded raw) p
        (position s.center-Rad) (position s.center+Rad) := by
      apply (hasPeriod_slice_iff (x := encoded raw) (p := p) hi.palindrome.2.1
        (by omega)).mp
      unfold Span at hper
      simpa [show position s.center + Rad + 1 - (position s.center - Rad) =
        2*Rad+1 by omega] using hper
    have heven : p % 2 = 0 := encoded_periodOn_even hpo hp (by omega)
      hi.palindrome.2.1
    obtain ⟨g,rfl⟩ : ∃ g, p = 2*g := ⟨p/2,by omega⟩
    have hg0 : 0 < g := by omega
    by_cases hgh : g < h
    · have h8 : 8*g ≤ B*(2*g) := by
        have := Nat.mul_le_mul_right (2*g) hB
        omega
      have hfour : 4*g ≤ Rad := by omega
      exact (hmin Rad hkC hi.palindrome g hg0 hgh hfour hper).elim
    · have hhg : h ≤ g := by omega
      calc
        2*Rad ≤ 2*(B*h) := Nat.mul_le_mul_left 2 hbound
        _ = B*(2*h) := by ring
        _ ≤ B*(2*g) := Nat.mul_le_mul_left B (Nat.mul_le_mul_left 2 hhg)
  have hmove := PalPeg.galil_move_of_scaledContract B x _
    (isPal_span_of_palAt hi.palindrome) Rad
    (length_span_of_palAt hi.palindrome) hcontract
  change ℓ / 2 ≤ B * (ℓ / 2 + 1 -
    chosenRadius ((GalilScaffoldPlace.stream
      (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)))
  have hk : ℓ / 2 = Rad := by rw [hℓrad]; omega
  rw [hk,hwindow]
  exact hmove

/-- Long-radius active fallback.  The current span carries the retained least
period `2*h`; the actual mismatching boundary says precisely that this period
does not extend to the fallback window. -/
theorem move_of_activePeriodBreak {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {Rad h ℓ : ℕ} {vq : SearchVM} {z : ChainVM}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hav : canRight s.right) (hlen : value s.length = (2*Rad+1 : ℕ))
    (hkC : Rad < position s.center) (hh0 : 0 < h) (hhk : 2*h ≤ Rad)
    (hperiod : HasPeriod (Span raw (position s.center) Rad) (2*h))
    (hminimal : ∀ p, 0 < p → p < 2*h →
      ¬ HasPeriod (Span raw (position s.center) Rad) p)
    (hbreak : ∀ x,
      (GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace
        (afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
          (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)))).take (ℓ+1)
        = x :: Span raw (position s.center) Rad →
      ¬ HasPeriod (x :: Span raw (position s.center) Rad) (2*h))
    (hℓ : ℓ = (value s.length).toNat) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s ⟨left s.left,right s.right,z⟩ vq)
  have hs1 : s1.right = right s.right := by simp [s1,afterBirth_right,afterMismatch_right]
  have hrrep : GalilScaffoldInputTrace.Represents (right s.right).head raw :=
    right_word _ raw hi.rightRep hav
  have hrpres : (right s.right).head.focus ≠ none :=
    right_present _ raw hi.rightRep hi.rightPresent hav
  obtain ⟨a,xs,rs,q',hdec,hraw⟩ := represents_decompose (right s.right) raw hrrep hrpres
  have hrpos := right_position s.right hav
    (represented_position _ raw hi.rightRep hi.rightPresent).1
  have hstream : (GalilScaffoldPlace.stream ⟨a :: xs,(right s.right).gap⟩).length
      = position s.center + Rad + 1 := by
    rw [stream_length_of_place a xs rs q' hdec,hrpos,hi.rightPos]
  have hpal : PalAt (encoded ((a :: xs).reverse ++ rs ++ q')) (position s.center) Rad := by
    rw [← hraw]
    exact hi.palindrome
  obtain ⟨x,hwin⟩ := window_eq_cons_span a xs rs q' (right s.right).gap hstream hkC hpal
  rw [← hraw] at hwin
  have hℓrad : ℓ = 2*Rad+1 := by
    rw [hℓ,hlen]
    exact Int.toNat_natCast _
  have hwindow :
      (GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)
        = x :: Span raw (position s.center) Rad := by
    have hp : PalPeg.GalilTickFair.rightPlace s1 =
        ⟨a :: xs,(right s.right).gap⟩ := by
      apply PalPeg.GalilTickFair.rightPlace_of_represent _ (rs.map some) q'
      rw [hs1]
      exact hdec
    rw [hp,hℓrad]
    exact hwin
  have hmove := PalPeg.galil_move_of_minimal_period_break x _
    (isPal_span_of_palAt hi.palindrome) Rad h
    (length_span_of_palAt hi.palindrome) hh0 hhk hperiod hminimal
    (hbreak x hwindow)
  change ℓ / 2 ≤ 4 * (ℓ / 2 + 1 -
    chosenRadius ((GalilScaffoldPlace.stream
      (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)))
  have hk : ℓ / 2 = Rad := by rw [hℓrad]; omega
  rw [hk,hwindow]
  exact hmove

/-- The coefficient-`4` specialization used by the original consumer. -/
theorem move_of_activeBound {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {Rad h ℓ : ℕ} {vq : SearchVM} {z : ChainVM}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hav : canRight s.right) (hlen : value s.length = (2*Rad+1 : ℕ))
    (hkC : Rad < position s.center)
    (hmin : PalPeg.CanonicalSearchProgram.MoveMinimal raw (position s.center) h)
    (hbound : Rad ≤ 4*h) (hℓ : ℓ = (value s.length).toNat) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  exact move_of_activeScaledBound (c := c) hi hav hlen hkC hmin
    (B := 4) (by omega) hbound hℓ

/-- The completed failed stage gives exactly the Galil move bound used by
the canonical fallback branch. -/
theorem move_of_stageFailed {raw : List (Fin 2)} {c : Control} {s : GalilVM}
    {Rad ℓ : ℕ} {vq : SearchVM} {z : ChainVM}
    (hP : Decodes (PofC centre place entry raw))
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hav : canRight s.right) (hlen : value s.length = (2*Rad+1 : ℕ))
    (hkC : Rad < position s.center) (hcen : CentreRep raw s)
    (hstage : StageFailed (PofC centre place entry raw) raw s Rad)
    (hℓ : ℓ = (value s.length).toNat) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
    let radius := chosenRadius
      ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1))
    ℓ / 2 ≤ 4 * (ℓ / 2 + 1 - radius) := by
  apply move_of_dpPack (centre := centre) (place := place) (entry := entry)
    (c := c) hP hi hav hlen hkC (dpPack_of_stageFailed hP hcen hstage) hℓ

/-- Construct the real fallback through its fresh restart at a mismatch.
The remaining oracle work starts at this exit, i.e. at replay. -/
theorem begin_at_mismatch {raw : List (Fin 2)} {c₀ : Control} {r₀ : GalilVM}
    (hI : InvLPS (PofC centre place entry raw) q first raw c₀ r₀)
    {k : ℕ} {c : Control} {s : GalilVM}
    (hRun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw k ⟨c₀,r₀⟩ ⟨c,s⟩)
    (hm : c.mode = .scan) (hr : c.replaying = false) (hav : canRight s.right)
    (hM : MInv raw c s)
    (hMis : read (GalilScaffoldInputHead.left s.left) ≠ read (right s.right))
    (hq : 0 < q) (h7 : first ≠ 7) (h8 : first ≠ 8) (vq : SearchVM) (z : ChainVM) :
    let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
      (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
    let u := beginFallbackAt (PalPeg.GalilTickFair.rightPlace s1) s1
    let ℓ := (value s.length).toNat
    let win := (GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take (ℓ+1)
    let radius := chosenRadius win
    beginFallbackVM' s1 u ∧ u.fpp.walker = PalPeg.GalilTickFair.rightPlace u ∧
    ∃ ticks y, Landing centre place entry q first raw ⟨{c with clock := 2048,mode := .copy},u⟩ y ℓ radius ticks ∧
      position y.vm.center = position (right s.right) - radius ∧
      Manacher.PalAt (encoded raw) (position (right s.right)-radius) radius ∧
      (∀ r', 2*r'+1 ≤ win.length →
        Manacher.PalAt (encoded raw) (position (right s.right)-r') r' → r' ≤ radius) ∧
      MInv raw y.ctl y.vm ∧ Frontier y.vm := by
  obtain ⟨hIdle,hCan,rad,hScan,hLen⟩ := counters centre place entry q first hI hRun hm hr
  let s1 := afterBirth (chainBorn (decide (vq.search.mode = .found)) s.chain)
    (afterMismatch s ⟨GalilScaffoldInputHead.left s.left,right s.right,z⟩ vq)
  have hR : s1.right = right s.right := by simp [s1,afterBirth_right,afterMismatch_right]
  have hL : s1.length = s.length := by simp [s1,afterBirth_length,afterMismatch_length]
  have hRem : s1.remaining = s.remaining := by simp [s1,afterBirth_remaining,afterMismatch_remaining]
  have hRep : GalilScaffoldInputTrace.Represents s1.right.head raw := by
    rw [hR]; exact right_word _ raw hScan.rightRep hav
  have hPresent : s1.right.head.focus ≠ none := by
    rw [hR]; exact right_present _ raw hScan.rightRep hScan.rightPresent hav
  have hValue : value s1.length = (value s.length).toNat := by rw [hL,hLen]; simp; omega
  have hEven : ((GalilScaffoldPlace.stream (PalPeg.GalilTickFair.rightPlace s1)).take
      ((value s.length).toNat+1)).length % 2 = 0 := by
    rw [List.length_take,PalPeg.GalilTickFair.rightPlace_length hRep,hR,hLen]
    simp only [Int.toNat_natCast]
    have hPos := right_position s.right hav (represented_position _ raw hScan.rightRep hScan.rightPresent).1
    have hRad := radius_lt_centre hScan
    have hRight := hScan.rightPos
    have heq : min (2*rad+1+1) (position (right s.right)) = 2*rad+2 := by omega
    rw [heq]
    omega
  have h := begin_to_scan (centre := centre) (place := place) (entry := entry)
    hq h7 h8 {c with clock := 2048,mode := .copy} rfl s1
    (by rw [shiftIdle_iff,hRem]; exact (shiftIdle_iff s).1 hIdle)
    hRep hPresent (by rw [hL]; exact hCan) (value s.length).toNat hValue hEven
  obtain ⟨hEntry,hPin,ticks,y,hLanding,hPos,hPal,hMax⟩ := h
  have hPos' := hPos
  have hPal' := hPal
  have hMax' := hMax
  rw [hR] at hPos' hPal' hMax'
  refine ⟨hEntry,hPin,ticks,y,hLanding,hPos',hPal',hMax',?_,?_⟩
  · let w0 : GalilScaffoldChainWatch.State :=
      ⟨⟨s1.right,GalilScaffoldChainConsume.ready 0 [] 0⟩,reset,reset⟩
    obtain ⟨a,xs,rs,queue,hDec,_⟩ :=
      fallback_replay (⟨s1.center,s1.left,s1.right,w0,s1.cycle,s1.radius⟩ : OnlyCompareState)
        hRep hPresent s1.length (by rw [hL]; exact hCan) (value s.length).toNat hValue
    have hp : PalPeg.GalilTickFair.rightPlace s1 = ⟨a :: xs,s1.right.gap⟩ :=
      PalPeg.GalilTickFair.rightPlace_of_represent _ _ _ hDec
    have hLenNat : value s.length = (value s.length).toNat := by rw [hLen]; simp; omega
    have hSpan : SpanRep {s with radius := ofNat rad} := by
      change value s.length = 2*value (ofNat rad)+1
      rw [hLen,ofNat_value]; push_cast; rfl
    have hLeftmost := leftmost_after_fallback_landing raw
      (s := {s with radius := ofNat rad}) (t := y.vm)
      (minv_same rfl rfl rfl rfl hM) hr hScan
      ⟨ofNat_canonical rad,ofNat_value rad⟩ hSpan hav hMis
      a xs rs queue (by rw [← hR]; exact hDec) (value s.length).toNat hLenNat
      (by simpa only [hp,hR] using hPal')
      (by simpa only [hp,hR] using hMax')
      (by simpa only [hp,hR] using hPos')
    have hRightPos := right_position s.right hav
      (represented_position _ raw hScan.rightRep hScan.rightPresent).1
    apply minv_after_fallback hLanding.restarted hLanding.replay
      (by rw [hRightPos] at hPos'; exact hPos')
      (by rw [hRightPos] at hLeftmost; exact hLeftmost) hLanding.replaying
  · exact frontier_after_fallback' hLanding.right hLanding.replay hPal

#print axioms counters
#print axioms begin_at_mismatch
end PalPeg.CanonicalFallbackInput
