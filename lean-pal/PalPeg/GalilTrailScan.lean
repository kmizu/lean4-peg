import PalPeg.GalilTrailProof
import PalPeg.GalilChainCoupling
import PalPeg.GalilFrontMono
import PalPeg.GalilFinalAssembly

/-!
# The scan-head half of the trailing invariant

`GalilTrailProof.TrailF` has four clauses: `L` and `C` as `FrontLe`, `R` as
`Trails … 0`, and two verifier clauses.  This file closes the first three
along every tick of `galilFrameS` and along a pre-loaded trace; the verifier
clauses are left to a separate module.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailScan

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilLookRefined PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. `FrontLe` is exactly the consumption bound of `Trails` -/

/-- `2·usedPH = position + [letter] + 2·|right stack|`, so the `FrontLe` bound of
`GalilLookRefined` is the `used` field of `Trails`.  Hence the scan-head clauses of
`TrailF` follow from `Trails … 0` on all three heads. -/
theorem frontLe_of_trails {raw : List (Fin 2)} {m d : ℕ} {p : PH} (h : Trails raw m d p) :
    FrontLe raw m p := by
  refine ⟨h.rep, h.sane, ?_⟩
  have h2 := GalilNeedBound.two_usedPH_of_rep raw p h.rep h.sane
  have := h.used
  omega

/-! ## 2. The carrier -/

/-- The three scan heads, each with the frontier clause of `Trails`. -/
structure ScanT (raw : List (Fin 2)) (m : ℕ) (x : State GalilVM) : Prop where
  left : Trails raw m 0 x.vm.left
  center : Trails raw m 0 x.vm.center
  right : Trails raw m 0 x.vm.right

theorem scanT_left {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} (h : ScanT raw m x) :
    FrontLe raw m x.vm.left := frontLe_of_trails h.left

theorem scanT_center {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} (h : ScanT raw m x) :
    FrontLe raw m x.vm.center := frontLe_of_trails h.center

/-- The budget of one right move: the move is possible and, if it empties the right
stack, it lands no further right than the checkpoint place `2(m+1)-1`. -/
def RightOK (m : ℕ) (p : PH) : Prop :=
  GalilScaffoldChainVerifier.canRight p ∧
    ((GalilScaffoldChainVerifier.right p).head.right = [] →
      position (GalilScaffoldChainVerifier.right p) ≤ 2 * (m + 1) - 1)

theorem trails_rightOK {raw : List (Fin 2)} {m : ℕ} {p : PH} (h : Trails raw m 0 p)
    (hb : RightOK m p) : Trails raw m 0 (GalilScaffoldChainVerifier.right p) :=
  trails_right h hb.1 (fun hz => by have := hb.2 hz; omega)

theorem trails_leftPos {raw : List (Fin 2)} {m : ℕ} {p : PH} (h : Trails raw m 0 p)
    (hp : 0 < position p) : Trails raw m 0 (GalilScaffoldInputHead.left p) :=
  trails_left h (GalilFrontMono.left_sane hp)

/-- **The named budget of one tick.**  The head moves of `galilFrameS` are: `R` right
(at `init` and at a comparison), `L` left (at a comparison and in `rewind`), `C` left
(in `rewind`), `C` right and `L` right twice (per shift unit).  Every other tick copies
a head or leaves the heads alone.  This record is what the scan-head clauses cannot
supply by themselves; it is the place-arithmetic obligation left open here. -/
structure TickBudget (m : ℕ) (c : Control) (s : GalilVM) : Prop where
  initR : c.mode = Mode.init → RightOK m s.right
  cmpR : c.mode = Mode.scan → c.clock = 1 → RightOK m s.right
  cmpL : c.mode = Mode.scan → c.clock = 1 → 0 < position s.left
  shiftC : c.mode = Mode.shift → RightOK m s.center
  shiftL : c.mode = Mode.shift → RightOK m s.left
  shiftL2 : c.mode = Mode.shift → RightOK m (GalilScaffoldChainVerifier.right s.left)
  rewL : c.mode = Mode.rewind → 0 < position s.left
  rewC : c.mode = Mode.rewind → 0 < position s.center

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- The heads after a comparison: `L` one place left, `R` one place right, `C` fixed. -/
theorem compare_heads {s s' : GalilVM}
    (hcmp : (galilFrameS (sharedC onLetter leftFirst centre place entry) q first).compare s s') :
    s'.left = GalilScaffoldInputHead.left s.left ∧
      s'.right = GalilScaffoldChainVerifier.right s.right ∧ s'.center = s.center := by
  obtain ⟨vs, vq, a, hvl, hvr, -, -, -, hteq⟩ :
    compareFound (sharedC onLetter leftFirst centre place entry) q first s s' := hcmp
  exact ⟨by rw [hteq]; cases a <;> exact hvl, by rw [hteq]; cases a <;> exact hvr,
    by rw [hteq]; cases a <;> rfl⟩


/-! ## 3. One tick -/

/-- **The scan-head clauses travel along one tick**, given the place budget of the
head moves that tick performs. -/
theorem scanT_tick {c c' : Control} {s t : GalilVM} {raw : List (Fin 2)} {m : ℕ}
    (hS : ScanT raw m ⟨c, s⟩) (hB : TickBudget m c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ScanT raw m ⟨c', t⟩ := by
  obtain ⟨hL, hC, hR⟩ := hS
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨hr, hl, hce, -⟩ : initVM entry s t := hi
    have hb := trails_rightOK hR (hB.initR hm)
    exact ⟨by rw [hl]; exact hb, by rw [hce]; exact hb, by rw [hr]; exact hb⟩
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨by rw [hl]; exact hL, by rw [hce]; exact hC, by rw [hr]; exact hR⟩
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact ⟨by rw [hl]; exact hL, by rw [hce]; exact hC, by rw [hr]; exact hR⟩
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact ⟨by rw [ht]; exact hL, by rw [ht]; exact hC, by rw [ht]; exact hR⟩
  case scan_match =>
    rename_i s' o hmt hm hc hcmp hav hpl ho
    obtain ⟨hl, hr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    have hpl' : t = (if c.replaying then
        {s' with replay := GalilScaffoldCounter.dec s'.replay} else s') := hpl
    refine ⟨?_, ?_, ?_⟩
    · have ht : t.left = GalilScaffoldInputHead.left s.left := by
        rw [hpl']; cases c.replaying <;> exact hl
      rw [ht]; exact trails_leftPos hL (hB.cmpL hm hc)
    · have ht : t.center = s.center := by rw [hpl']; cases c.replaying <;> exact hce
      rw [ht]; exact hC
    · have ht : t.right = GalilScaffoldChainVerifier.right s.right := by
        rw [hpl']; cases c.replaying <;> exact hr
      rw [ht]; exact trails_rightOK hR (hB.cmpR hm hc)
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    refine ⟨?_, ?_, ?_⟩
    · have h1 : t.left = GalilScaffoldInputHead.left s.left := by rw [ht]; exact hl
      rw [h1]; exact trails_leftPos hL (hB.cmpL hm hc)
    · have h1 : t.center = s.center := by rw [ht]; exact hce
      rw [h1]; exact hC
    · have h1 : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hrr
      rw [h1]; exact trails_rightOK hR (hB.cmpR hm hc)
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨p, ht⟩ : beginFallbackVM' s' t := hb
    refine ⟨?_, ?_, ?_⟩
    · have h1 : t.left = GalilScaffoldInputHead.left s.left := by rw [ht]; exact hl
      rw [h1]; exact trails_leftPos hL (hB.cmpL hm hc)
    · have h1 : t.center = s.center := by rw [ht]; exact hce
      rw [h1]; exact hC
    · have h1 : t.right = GalilScaffoldChainVerifier.right s.right := by rw [ht]; exact hrr
      rw [h1]; exact trails_rightOK hR (hB.cmpR hm hc)
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨-, -, -, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    refine ⟨?_, ?_, ?_⟩
    · have h1 : t.left = GalilScaffoldChainVerifier.right
          (GalilScaffoldChainVerifier.right s.left) := by rw [ht]; rfl
      rw [h1]; exact trails_rightOK (trails_rightOK hL (hB.shiftL hm)) (hB.shiftL2 hm)
    · have h1 : t.center = GalilScaffoldChainVerifier.right s.center := by rw [ht]; rfl
      rw [h1]; exact trails_rightOK hC (hB.shiftC hm)
    · have h1 : t.right = s.right := by rw [ht]; rfl
      rw [h1]; exact hR
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
    refine ⟨?_, ?_, ?_⟩
    · rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]
      exact trails_leftPos hL (hB.rewL ‹c.mode = Mode.rewind›)
    · rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]; exact hC
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR
  case rewind_pair =>
    rename_i hm hpr hfi hi
    refine ⟨?_, ?_, ?_⟩
    · rw [(congrArg GalilVM.left hi.2).trans (by rw [hi.1.2])]
      exact trails_leftPos hL (hB.rewL ‹c.mode = Mode.rewind›)
    · rw [(congrArg GalilVM.center hi.2).trans (by rw [hi.1.2])]
      exact trails_leftPos hC (hB.rewC ‹c.mode = Mode.rewind›)
    · rw [(congrArg GalilVM.right hi.2).trans (by rw [hi.1.2])]; exact hR
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hce, -⟩ : replayStartVM entry s t := hi
    exact ⟨by rw [hl]; exact hC, by rw [hce]; exact hC, by rw [hr]; exact hC⟩

#print axioms scanT_tick

#print axioms compare_heads

end Tick

/-! ## 4. The interface to `TrailF` -/

/-- The three scan-head clauses of `TrailF`, from `ScanT`.  The two verifier clauses
are the other half of `H_trailF` and are not proved here. -/
theorem trailF_of_scanT {raw : List (Fin 2)} {m : ℕ} {x : State GalilVM} (hS : ScanT raw m x)
    (hver : ∀ p, verOf x.vm.chain = some p → Trails raw m 0 p)
    (hlag : ∀ w, x.vm.chain = .watch w → GalilScaffoldCounter.positive w.lag = true →
      Trails raw m 1 w.machine.verifier) : TrailF raw m x :=
  ⟨scanT_left hS, scanT_center hS, hS.right, hver, hlag⟩

/-! ## 5. Along a trace -/

theorem scanT_boot (raw : List (Fin 2)) (m : ℕ) : ScanT raw m (boot raw) :=
  ⟨trails_initialHead raw m 0 (by omega), trails_initialHead raw m 0 (by omega),
    trails_initialHead raw m 0 (by omega)⟩

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The scan-head clauses up to the checkpoint `Tc (m+1)`.** -/
theorem scanT_trace {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hbud : ∀ i, i < Tc (m+1) → TickBudget m (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc (m+1) → ScanT raw m (st i) := by
  have hle : Tc (m+1) ≤ Tc raw.length := hP.mono (m+1) raw.length (by omega) le_rfl
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact scanT_boot raw m
  | succ i ih =>
    intro hi
    have hlt : i < Tc (m+1) := by omega
    exact scanT_tick (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hbud i hlt) (hP.trace.tick i (by omega))

end Trace

/-! ## 6. `R`'s place clause from the frontier

`GalilFrontMono.front s = position s.right + replay` does not decrease along a tick
(`front_tick_mono`), and `PreTrace.report` puts `R` on the place `2(m+1)-1` at the
checkpoint `Tc (m+1)`.  So the place half of `Trails … 0 R` needs no stack hypothesis
at all — it is monotonicity plus the checkpoint place. -/

theorem position_right_le_of_front {x y : GalilVM} {m : ℕ}
    (hmono : GalilRunTrace.front x ≤ GalilRunTrace.front y)
    (hx : 0 ≤ GalilScaffoldCounter.value x.replay)
    (hy : GalilScaffoldCounter.value y.replay = 0)
    (hpos : position y.right = 2 * (m + 1) - 1) :
    position x.right ≤ 2 * (m + 1) - 1 := by
  simp only [GalilRunTrace.front, hy, add_zero] at hmono
  have : (position x.right : ℤ) ≤ (position y.right : ℤ) := by linarith
  omega

/-- The `Trails … 0` clause assembled from a consumption bound and a place bound. -/
theorem trails_of_pos {raw : List (Fin 2)} {m : ℕ} {p : PH}
    (hrep : GalilScaffoldInputTrace.Represents p.head raw) (hsane : GalilFrontMono.Sane p)
    (hused : usedPH raw.length p ≤ m + 1) (hpos : position p ≤ 2 * (m + 1) - 1) :
    Trails raw m 0 p := ⟨hrep, hsane, hused, fun _ => by omega⟩

/-- The same, taking the consumption bound from `FrontLe`. -/
theorem trails_of_frontLe {raw : List (Fin 2)} {m : ℕ} {p : PH} (h : FrontLe raw m p)
    (hpos : position p ≤ 2 * (m + 1) - 1) : Trails raw m 0 p :=
  trails_of_pos h.1 h.2.1 (usedPH_le_of_frontLe raw m p h) hpos

/-- **The budget of a right move, from the frontier.**  This is the intended discharge of
the `RightOK` place clause: the new place of `R` is bounded by the checkpoint place. -/
theorem rightOK_of_front {m : ℕ} {p : PH} (hc : GalilScaffoldChainVerifier.canRight p)
    (hpos : position (GalilScaffoldChainVerifier.right p) ≤ 2 * (m + 1) - 1) :
    RightOK m p := ⟨hc, fun _ => hpos⟩

#print axioms frontLe_of_trails
#print axioms trails_rightOK
#print axioms trails_leftPos
#print axioms trailF_of_scanT
#print axioms scanT_boot
#print axioms scanT_trace
#print axioms position_right_le_of_front
#print axioms trails_of_frontLe
#print axioms rightOK_of_front

/-! ## 7. The remaining obligation, as one named hypothesis -/

/-- (B''-scan) The scan-head clauses of `TrailF` along every pre-loaded trace. -/
def H_trailScan (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) → ScanT w m (st i)

/-- **(Named) the place budget along every pre-loaded trace.**  This is everything the
scan-head half of `H_trailF` still needs: at each tick before the checkpoint `m+1`, a
right move of `R`/`C`/`L` is possible and lands no further right than the checkpoint
place `2(m+1)-1`, and a left move of `L`/`C` starts off the clipped origin. -/
def H_tickBudget (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry q : ℕ) (first : Fin 9) : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ m, m < w.length → ∀ i, i < Tc (m+1) → TickBudget m (st i).ctl (st i).vm

/-- **The scan-head half of `H_trailF`, reduced to the place budget.** -/
theorem h_trailScan_of_budget (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (h : H_tickBudget centre place entry q first) : H_trailScan centre place entry q first :=
  fun w hw st Tc hP m hm => scanT_trace centre place entry q first hP hm
    (fun i hi => h w hw st Tc hP m hm i hi)

/-- **`H_trailF` from the scan half and the verifier half.** -/
theorem h_trailF_of_parts (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (hscan : H_trailScan centre place entry q first)
    (hver : ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc,
      PreTrace centre place entry q first w st Tc → ∀ m, m < w.length → ∀ i, i ≤ Tc (m+1) →
        (∀ p, verOf (st i).vm.chain = some p → Trails w m 0 p) ∧
        (∀ v, (st i).vm.chain = .watch v → GalilScaffoldCounter.positive v.lag = true →
          Trails w m 1 v.machine.verifier)) :
    H_trailF centre place entry q first :=
  fun w hw st Tc hP m hm i hi =>
    trailF_of_scanT (hscan w hw st Tc hP m hm i hi) (hver w hw st Tc hP m hm i hi).1
      (hver w hw st Tc hP m hm i hi).2

/-- Alias with the name used in the assembly notes. -/
theorem trailScan_tick {onLetter leftFirst : GalilVM → Prop} {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9} {delay : ℕ}
    {c c' : Control} {s t : GalilVM} {raw : List (Fin 2)} {m : ℕ}
    (hS : ScanT raw m ⟨c, s⟩) (hB : TickBudget m c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : ScanT raw m ⟨c', t⟩ :=
  scanT_tick onLetter leftFirst centre place entry q first delay hS hB h

/-- Alias with the name used in the assembly notes. -/
theorem trailScan_trace {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ} {m : ℕ}
    (hP : PreTrace centre place entry q first raw st Tc) (hm : m < raw.length)
    (hbud : ∀ i, i < Tc (m+1) → TickBudget m (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc (m+1) → ScanT raw m (st i) :=
  scanT_trace centre place entry q first hP hm hbud

#print axioms h_trailScan_of_budget
#print axioms h_trailF_of_parts
#print axioms trailScan_tick
#print axioms trailScan_trace

end PalPeg.GalilTrailScan
