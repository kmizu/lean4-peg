import PalPeg.GalilTrailScan

/-!
# The tick budget of the scan heads, as a property of the *reached* state

`GalilTrailScan.H_tickBudget` asks, at every tick before the checkpoint, for
`canRight` of the head that moves and for a place bound on the head *after* the
move.  Both halves are awkward: `canRight` is not part of the precondition of
`initVM`/`compareFound` (only of `shiftOne`), and the bound is about a head that
does not exist yet.

This file replaces it by `HeadsOK m y`: a property of the state the tick reaches
(`Sane` of the three scan heads plus their places `≤ 2(m+1)-1`).  It is strictly
weaker than `TickBudget` on the moving branches — `canRight` disappears, because
`Trails` only ever used it for `Sane` of the new head — and it is checked at the
states of the trace, where `front`-monotonicity and the checkpoint report speak.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailBudget

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilLookRefined PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly PalPeg.GalilTrailScan

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. A right move needs no `canRight`, only `Sane` of the target -/

/-- **`trails_right` without `canRight`.**  `GalilTrailProof.trails_right` used
`canRight` twice and only to produce `sane_right`; taking `Sane` of the moved head
as the hypothesis removes it. -/
theorem trails_right_of_sane {raw : List (Fin 2)} {m d : ℕ} {p : PH} (h : Trails raw m d p)
    (hs : GalilFrontMono.Sane (GalilScaffoldChainVerifier.right p))
    (hb : position (GalilScaffoldChainVerifier.right p) + d ≤ 2 * (m + 1) - 1) :
    Trails raw m d (GalilScaffoldChainVerifier.right p) := by
  refine ⟨represents_right h.rep, hs, ?_, fun _ => hb⟩
  by_cases hz : (GalilScaffoldChainVerifier.right p).head.right = []
  · exact GalilNeedBound.usedPH_le_of_position raw _ m (represents_right h.rep) hs hz (by omega)
  · rw [usedPH_right_of_stack _ _ (stack_ne_of_right_stack_ne hz)]; exact h.used

theorem trails_rightE {raw : List (Fin 2)} {m : ℕ} {p p' : PH} (h : Trails raw m 0 p)
    (he : p' = GalilScaffoldChainVerifier.right p) (hs : GalilFrontMono.Sane p')
    (hb : position p' ≤ 2 * (m + 1) - 1) : Trails raw m 0 p' := by
  rw [he] at hs hb ⊢; exact trails_right_of_sane h hs (by omega)

theorem trails_leftE {raw : List (Fin 2)} {m : ℕ} {p p' : PH} (h : Trails raw m 0 p)
    (he : p' = GalilScaffoldInputHead.left p) (hs : GalilFrontMono.Sane p') :
    Trails raw m 0 p' := by
  rw [he] at hs ⊢; exact trails_left h hs

theorem trails_copyE {raw : List (Fin 2)} {m : ℕ} {p p' : PH} (h : Trails raw m 0 p)
    (he : p' = p) : Trails raw m 0 p' := by rw [he]; exact h

/-! ## 2. The budget, as a property of one state -/

/-- **The place budget of a state.**  The three scan heads are off the clipped
origin and stand no further right than the checkpoint place `2(m+1)-1`. -/
structure HeadsOK (m : ℕ) (y : State GalilVM) : Prop where
  saneL : GalilFrontMono.Sane y.vm.left
  saneC : GalilFrontMono.Sane y.vm.center
  saneR : GalilFrontMono.Sane y.vm.right
  placeL : position y.vm.left ≤ 2 * (m + 1) - 1
  placeC : position y.vm.center ≤ 2 * (m + 1) - 1
  placeR : position y.vm.right ≤ 2 * (m + 1) - 1

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **The scan-head clauses travel along one tick**, given only the place budget of
the state the tick reaches. -/
theorem scanT_tick' {c c' : Control} {s t : GalilVM} {raw : List (Fin 2)} {m : ℕ}
    (hS : ScanT raw m ⟨c, s⟩) (hB : HeadsOK m ⟨c', t⟩)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ScanT raw m ⟨c', t⟩ := by
  obtain ⟨hL, hC, hR⟩ := hS
  obtain ⟨bL, bC, bR, pL, pC, pR⟩ := hB
  simp only at bL bC bR pL pC pR
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨hr, hl, hce, -⟩ : initVM entry s t := hi
    exact ⟨trails_rightE hR hl bL pL, trails_rightE hR hce bC pC, trails_rightE hR hr bR pR⟩
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨trails_copyE hL hl, trails_copyE hC hce, trails_copyE hR hr⟩
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨trails_copyE hL hl, trails_copyE hC hce, trails_copyE hR hr⟩
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact ⟨trails_copyE hL (by rw [ht]), trails_copyE hC (by rw [ht]),
      trails_copyE hR (by rw [ht])⟩
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hl, hr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    have e1 : t.left = GalilScaffoldInputHead.left s.left := by
      rw [hpl']; cases c.replaying <;> exact hl
    have e2 : t.center = s.center := by rw [hpl']; cases c.replaying <;> exact hce
    have e3 : t.right = GalilScaffoldChainVerifier.right s.right := by
      rw [hpl']; cases c.replaying <;> exact hr
    exact ⟨trails_leftE hL e1 bL, trails_copyE hC e2, trails_rightE hR e3 bR pR⟩
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    exact ⟨trails_leftE hL (by rw [ht]; exact hl) bL, trails_copyE hC (by rw [ht]; exact hce),
      trails_rightE hR (by rw [ht]; exact hrr) bR pR⟩
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨p, ht⟩ : beginFallbackVM' s' t := hb
    exact ⟨trails_leftE hL (by rw [ht]; exact hl) bL, trails_copyE hC (by rw [ht]; exact hce),
      trails_rightE hR (by rw [ht]; exact hrr) bR pR⟩
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcc, hcl, hcl2, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    have e1 : t.left = GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
    have e2 : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
    have e3 : t.right = s.right := by rw [ht]; rfl
    have hmidS : GalilFrontMono.Sane (GalilScaffoldChainVerifier.right s.left) :=
      (GalilFrontMono.right_sane hcl hL.sane).2
    have hstep : position (GalilScaffoldChainVerifier.right
        (GalilScaffoldChainVerifier.right s.left)) =
        position (GalilScaffoldChainVerifier.right s.left) + 1 :=
      (GalilFrontMono.right_sane hcl2 hmidS).1
    have hmidT : Trails raw m 0 (GalilScaffoldChainVerifier.right s.left) :=
      trails_right_of_sane hL hmidS (by rw [e1] at pL; omega)
    exact ⟨trails_rightE hmidT e1 bL pL, trails_rightE hC e2 bC pC, trails_copyE hR e3⟩
  case shift_done => exact ⟨hL, hC, hR⟩
  case copy_one =>
    rename_i hm hp hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case copy_done =>
    rename_i hm hp hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case home_start =>
    rename_i hm hl hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case home_step =>
    rename_i hm hl hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case fpp_slice =>
    rename_i hm hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case fpp_done =>
    rename_i hm hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case markEnd_step =>
    rename_i hm he hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans rfl]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans rfl]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans rfl]; exact hR⟩
  case markEnd_found =>
    rename_i hm he hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR⟩
  case choose_step =>
    rename_i hm hs hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR⟩
  case rewind_done =>
    rename_i hm hfi hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1])]; exact hL,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1])]; exact hC,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1])]; exact hR⟩
  case choose_select =>
    rename_i hm hodd hs hi
    exact ⟨by rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1])]; exact hR,
      by rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1])]; exact hR,
      by rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1])]; exact hR⟩
  case rewind_one =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    refine ⟨trails_leftE hL e1 bL, ?_, ?_⟩
    · rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact hC
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    have e2 : t.center = GalilScaffoldInputHead.left s.center :=
      (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    refine ⟨trails_leftE hL e1 bL, trails_leftE hC e2 bC, ?_⟩
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hce, -⟩ : replayStartVM entry s t := hi
    exact ⟨trails_copyE hC hl, trails_copyE hC hce, trails_copyE hC hr⟩

#print axioms trails_right_of_sane
#print axioms trails_rightE
#print axioms trails_leftE
#print axioms scanT_tick'

end Tick

/-! ## 3. Along a pre-loaded trace -/

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`scanT_trace` with the state budget.** -/
theorem scanT_trace' {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hbud : ∀ i, i ≤ Tc (m+1) → HeadsOK m (st i)) :
    ∀ i, i ≤ Tc (m+1) → ScanT raw m (st i) := by
  have hle : Tc (m+1) ≤ Tc raw.length := hP.mono (m+1) raw.length (by omega) le_rfl
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact scanT_boot raw m
  | succ i ih =>
    intro hi
    exact scanT_tick' (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hbud (i+1) hi) (hP.trace.tick i (by omega))

/-- **(Named) the place budget, as a property of the trace's states.**  This is the
pair/state form of `GalilTrailScan.H_tickBudget`. -/
def H_headsOK : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → HeadsOK m (st i)

/-- **The scan half of `H_trailF`, reduced to the state budget.** -/
theorem h_trailScan_of_headsOK (h : H_headsOK centre place entry q first) :
    H_trailScan centre place entry q first :=
  fun w hw st Tc hP m hm => scanT_trace' centre place entry q first hP hm
    (fun i hi => h w hw st Tc hP m hm i hi)

/-! ### 3.1 The right head's place is *proved* from the monotone frontier -/

/-- `R` never passes the checkpoint place, from `front`-monotonicity and the report. -/
theorem placeR_of_frontMono {st : ℕ → State GalilVM} {n m : ℕ}
    (hmono : ∀ i, i ≤ n → GalilRunTrace.front (st i).vm ≤ GalilRunTrace.front (st n).vm)
    (hnn : ∀ i, i ≤ n → 0 ≤ GalilScaffoldCounter.value (st i).vm.replay)
    (hz : GalilScaffoldCounter.value (st n).vm.replay = 0)
    (hpos : position (st n).vm.right = 2 * (m + 1) - 1) :
    ∀ i, i ≤ n → position (st i).vm.right ≤ 2 * (m + 1) - 1 :=
  fun i hi => position_right_le_of_front (hmono i hi) (hnn i hi) hz hpos

/-- At a report point the replay counter is zero (it is not replaying). -/
theorem replayZero_of_report {P : Shared} {w : List (Fin 2)} {k : ℕ} {x : State GalilVM}
    (h : PalPeg.GalilLedgerAssembly.ReportPointAt P q first w k x)
    (hrest : PalPeg.GalilScaffoldChainInputSupply.ReplayRest x.ctl x.vm) :
    GalilScaffoldCounter.value x.vm.replay = 0 := by
  rw [hrest (Or.inl h.notReplaying)]; rfl

/-- **(Named) the frontier data of a pre-loaded trace**: `front` is monotone, the
replay counter is a natural number, and `ReplayRest` holds. -/
def H_frontTrace : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    (∀ i j, i ≤ j → j ≤ Tc w.length →
        GalilRunTrace.front (st i).vm ≤ GalilRunTrace.front (st j).vm) ∧
    (∀ i, i ≤ Tc w.length → 0 ≤ GalilScaffoldCounter.value (st i).vm.replay) ∧
    (∀ i, i ≤ Tc w.length → PalPeg.GalilScaffoldChainInputSupply.ReplayRest (st i).ctl (st i).vm)

/-- **The `placeR` field, discharged.** -/
theorem placeR_of_preTrace (hf : H_frontTrace centre place entry q first)
    {w : List (Fin 2)} (hw : 0 < w.length) {st Tc} (hP : PreTrace centre place entry q first w st Tc)
    {m : ℕ} (hm : m < w.length) :
    ∀ i, i ≤ Tc (m+1) → position (st i).vm.right ≤ 2 * (m + 1) - 1 := by
  obtain ⟨hmono, hnn, hrest⟩ := hf w hw st Tc hP
  have hle : Tc (m+1) ≤ Tc w.length := hP.mono (m+1) w.length (by omega) le_rfl
  have hrep := hP.report (m+1) (by omega) (by omega)
  exact placeR_of_frontMono (fun i hi => hmono i (Tc (m+1)) hi hle)
    (fun i hi => hnn i (by omega)) (replayZero_of_report q first hrep (hrest _ hle)) hrep.atPrefix

/-! ### 3.2 The residual obligations -/

/-- **(Named) the three scan heads are never a letter at the clipped origin.** -/
def H_saneHeads : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → GalilFrontMono.Sane (st i).vm.left ∧
      GalilFrontMono.Sane (st i).vm.center ∧ GalilFrontMono.Sane (st i).vm.right

/-- **(Named) `L ≤ C ≤ R`**: the two inner heads never pass the right head. -/
def H_headOrder : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i ≤ Tc w.length → position (st i).vm.left ≤ position (st i).vm.right ∧
      position (st i).vm.center ≤ position (st i).vm.right

/-- **The scan half of `H_trailF` from the three named residuals.** -/
theorem h_trailScan_of_residuals (hs : H_saneHeads centre place entry q first)
    (ho : H_headOrder centre place entry q first)
    (hf : H_frontTrace centre place entry q first) : H_trailScan centre place entry q first := by
  refine h_trailScan_of_headsOK centre place entry q first
    (fun w hw st Tc hP m hm i hi => ?_)
  have hle : Tc (m+1) ≤ Tc w.length := hP.mono (m+1) w.length (by omega) le_rfl
  obtain ⟨s1, s2, s3⟩ := hs w hw st Tc hP i (by omega)
  obtain ⟨o1, o2⟩ := ho w hw st Tc hP i (by omega)
  have hpr := placeR_of_preTrace centre place entry q first hf hw hP hm i hi
  exact ⟨s1, s2, s3, by omega, by omega, hpr⟩

end Trace

#print axioms scanT_trace'
#print axioms h_trailScan_of_headsOK
#print axioms placeR_of_frontMono
#print axioms replayZero_of_report
#print axioms placeR_of_preTrace
#print axioms h_trailScan_of_residuals

end PalPeg.GalilTrailBudget
