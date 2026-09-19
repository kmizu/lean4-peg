import PalPeg.GalilTrailBudget

/-!
# `L ≤ C ≤ R`: the three scan heads never pass one another

`GalilTrailBudget.H_headOrder` — `position L ≤ position R` and
`position C ≤ position R` at every state of a pre-loaded trace — is proved here
as a *tick invariant* `Order` (the stronger, chained form `L ≤ C ≤ R`).

The head moves of `galilFrameS` are (per `GalilTrailScan.scanT_tick`):
`init` and `choose_select` and `replayStart` put all three heads on one place;
a comparison moves `L` one left and `R` one right; `rewind` moves `L` (and, on
the `pair` tick, `C`) one left; one shift unit moves `C` one right and `L`
twice right; every other tick copies the heads.

Only two of those can break the order, and both are named in `OrderBudget`:

* a comparison *inside a replay* — `R` moves right, and the move has to exist
  (`canRight`).  Outside a replay the tick's own `available` hypothesis gives it,
  so nothing is assumed there;
* a shift unit — `L` gains two places and `C` one while `R` stands still, so the
  heads must be *strictly* separated (`radius ≥ 1`) while the machine shifts.

Everything else is unconditional, including the boot state (`initVM0` puts the
three heads on the same `initialHead`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace PalPeg.GalilTrailOrder

open PalPeg PalPeg.Program PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PegSeparation PalPeg.GalilStructuredSkeleton
open PalPeg.GalilThrottledRun PalPeg.GalilLookRefined PalPeg.GalilTrailProof
open PalPeg.GalilFinalAssembly PalPeg.GalilTrailScan PalPeg.GalilTrailBudget

abbrev PH := GalilScaffoldInputHead.PlaceHead

/-! ## 1. Head arithmetic, unconditional -/

theorem position_gap (h : GalilScaffoldInputHead.Head) :
    position (⟨h, true⟩ : PH) = 2 * h.left.length := rfl

theorem position_letter (h : GalilScaffoldInputHead.Head) :
    position (⟨h, false⟩ : PH) = 2 * h.left.length - 1 := rfl

theorem left_gap (h : GalilScaffoldInputHead.Head) :
    GalilScaffoldInputHead.left (⟨h, true⟩ : PH) = ⟨h, false⟩ := rfl

theorem left_letter (h : GalilScaffoldInputHead.Head) :
    GalilScaffoldInputHead.left (⟨h, false⟩ : PH)
      = ⟨GalilScaffoldInputHead.moveLeft h, true⟩ := rfl

theorem right_gap (h : GalilScaffoldInputHead.Head) :
    GalilScaffoldChainVerifier.right (⟨h, true⟩ : PH)
      = ⟨GalilScaffoldInputTrace.moveRight h, false⟩ := rfl

theorem right_letter (h : GalilScaffoldInputHead.Head) :
    GalilScaffoldChainVerifier.right (⟨h, false⟩ : PH) = ⟨h, true⟩ := rfl

theorem moveLeft_len (h : GalilScaffoldInputHead.Head) :
    (GalilScaffoldInputHead.moveLeft h).left.length = h.left.length - 1 := by
  rcases h with ⟨f, ls, rs, qs⟩
  cases ls <;> simp [GalilScaffoldInputHead.moveLeft]

theorem moveRight_len (h : GalilScaffoldInputHead.Head) :
    (GalilScaffoldInputTrace.moveRight h).left.length ≤ h.left.length + 1 := by
  rcases h with ⟨f, ls, rs, qs⟩
  cases rs with
  | cons a rs => simp [GalilScaffoldInputTrace.moveRight]
  | nil => cases qs <;> simp [GalilScaffoldInputTrace.moveRight]

theorem moveRight_len_eq {h : GalilScaffoldInputHead.Head}
    (hc : h.right ≠ [] ∨ h.incoming ≠ []) :
    (GalilScaffoldInputTrace.moveRight h).left.length = h.left.length + 1 := by
  rcases h with ⟨f, ls, rs, qs⟩
  cases rs with
  | cons a rs => simp [GalilScaffoldInputTrace.moveRight]
  | nil =>
    cases qs with
    | nil => simp at hc
    | cons a qs => simp [GalilScaffoldInputTrace.moveRight]

/-- A left step loses exactly one place (and stays at the clipped origin). -/
theorem pos_left (p : PH) :
    position (GalilScaffoldInputHead.left p) = position p - 1 := by
  rcases p with ⟨h, g⟩
  cases g with
  | true => rw [left_gap, position_letter, position_gap]
  | false => rw [left_letter, position_gap, position_letter, moveLeft_len]; omega

/-- A right step gains at most one place, whether or not it is legal. -/
theorem pos_right_le (p : PH) :
    position (GalilScaffoldChainVerifier.right p) ≤ position p + 1 := by
  rcases p with ⟨h, g⟩
  cases g with
  | false => rw [right_letter, position_gap, position_letter]; omega
  | true =>
    rw [right_gap, position_letter, position_gap]
    have := moveRight_len h
    omega

/-- A *legal* right step never loses a place. -/
theorem pos_le_right {p : PH} (hc : GalilScaffoldChainVerifier.canRight p) :
    position p ≤ position (GalilScaffoldChainVerifier.right p) := by
  rcases p with ⟨h, g⟩
  cases g with
  | false => rw [right_letter, position_gap, position_letter]; omega
  | true =>
    rw [right_gap, position_letter, position_gap]
    rcases hc with hc | hc
    · exact absurd hc (by simp)
    · have hc2 : h.right ≠ [] ∨ h.incoming ≠ [] := hc
      rw [moveRight_len_eq hc2]; omega

/-- A head off the clipped origin is `Sane`. -/
theorem sane_of_pos {p : PH} (h : 0 < position p) : GalilFrontMono.Sane p := by
  rcases p with ⟨hd, g⟩
  cases g with
  | true => exact Or.inl rfl
  | false =>
    refine Or.inr ?_
    rw [position_letter] at h
    exact (by omega : 0 < hd.left.length)

/-! ## 2. The carrier and the two named budget clauses -/

/-- The three scan heads, in order. -/
structure Order (s : GalilVM) : Prop where
  lc : position s.left ≤ position s.center
  cr : position s.center ≤ position s.right

theorem order_head_bounds {s : GalilVM} (h : Order s) :
    position s.left ≤ position s.right ∧ position s.center ≤ position s.right :=
  ⟨le_trans h.lc h.cr, h.cr⟩

/-- **The budget of one tick.**  Exactly the two places where a head move can
break the order: a comparison performed inside a replay (the right move must
exist) and a shift unit (the heads must be strictly separated). -/
structure OrderBudget (c : Control) (s : GalilVM) : Prop where
  replayR : c.mode = Mode.scan → c.clock = 1 → c.replaying = true →
    GalilScaffoldChainVerifier.canRight s.right
  shiftLC : c.mode = Mode.shift → position s.left + 1 ≤ position s.center
  shiftCR : c.mode = Mode.shift → position s.center + 1 ≤ position s.right

theorem order_of_eqs {s t : GalilVM} (h : Order s) (e1 : t.left = s.left)
    (e2 : t.center = s.center) (e3 : t.right = s.right) : Order t :=
  ⟨by rw [e1, e2]; exact h.lc, by rw [e2, e3]; exact h.cr⟩

theorem order_of_const {t : GalilVM} {p : PH} (e1 : t.left = p) (e2 : t.center = p)
    (e3 : t.right = p) : Order t :=
  ⟨le_of_eq (by rw [e1, e2]), le_of_eq (by rw [e2, e3])⟩

/-- The comparison step: `L` one left, `C` fixed, `R` one right. -/
theorem order_of_compare {s t : GalilVM} (h : Order s)
    (hcan : GalilScaffoldChainVerifier.canRight s.right)
    (e1 : t.left = GalilScaffoldInputHead.left s.left) (e2 : t.center = s.center)
    (e3 : t.right = GalilScaffoldChainVerifier.right s.right) : Order t := by
  obtain ⟨hlc, hcr⟩ := h
  have h1 := pos_left s.left
  have h2 := pos_le_right hcan
  refine ⟨?_, ?_⟩
  · rw [e1, e2]; omega
  · rw [e2, e3]; omega

/-- One shift unit: `L` twice right, `C` once right, `R` fixed. -/
theorem order_of_shift {s t : GalilVM}
    (e1 : t.left = GalilScaffoldChainVerifier.right (GalilScaffoldChainVerifier.right s.left))
    (e2 : t.center = GalilScaffoldChainVerifier.right s.center) (e3 : t.right = s.right)
    (hcC : GalilScaffoldChainVerifier.canRight s.center)
    (b1 : position s.left + 1 ≤ position s.center)
    (b2 : position s.center + 1 ≤ position s.right) : Order t := by
  have hC1 : position (GalilScaffoldChainVerifier.right s.center) = position s.center + 1 :=
    (GalilFrontMono.right_sane hcC (sane_of_pos (by omega))).1
  have h1 := pos_right_le s.left
  have h2 := pos_right_le (GalilScaffoldChainVerifier.right s.left)
  refine ⟨?_, ?_⟩
  · rw [e1, e2, hC1]; omega
  · rw [e2, e3, hC1]; omega

/-! ## 3. One tick -/

section Tick
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- **The order travels along one tick**, given the budget of the comparison and
shift branches. -/
theorem order_tick {c c' : Control} {s t : GalilVM}
    (hO : Order s) (hB : OrderBudget c s)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩) : Order t := by
  cases h
  case init =>
    rename_i hm hi
    obtain ⟨hr, hl, hce, -⟩ : initVM entry s t := hi
    exact order_of_const hl hce hr
  case scan_wait =>
    rename_i hm hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact order_of_eqs hO hl hce hr
  case scan_count =>
    rename_i hm hc hav hb
    obtain ⟨hl, hr, -, hce, -⟩ :=
      backgroundS_fields (sharedC onLetter leftFirst centre place entry) q first hb
    exact order_of_eqs hO hl hce hr
  case restart =>
    rename_i hm hb
    obtain ⟨w, -, -, -, -, ht⟩ : restartVM entry s t := hb
    exact order_of_eqs hO (by rw [ht]) (by rw [ht]) (by rw [ht])
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
    refine order_of_compare hO ?_ e1 e2 e3
    rcases hav with hrep | hcan
    · exact hB.replayR hm hc hrep
    · exact hcan
  case scan_shift =>
    rename_i s' hmt hg hm hc hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨w, -, ht⟩ : beginShiftVM' s' t := hb
    refine order_of_compare hO ?_ (by rw [ht]; exact hl) (by rw [ht]; exact hce)
      (by rw [ht]; exact hrr)
    rcases hav with hrep | hcan
    · exact hB.replayR hm hc hrep
    · exact hcan
  case scan_fallback =>
    rename_i s' hmt hm hc hg hr hcmp hav hb
    obtain ⟨hl, hrr, hce⟩ :=
      compare_heads onLetter leftFirst centre place entry q first hcmp
    obtain ⟨p, ht, -⟩ : beginFallbackVM' s' t := hb
    refine order_of_compare hO ?_ (by rw [ht]; exact hl) (by rw [ht]; exact hce)
      (by rw [ht]; exact hrr)
    rcases hav with hrep | hcan
    · exact hB.replayR hm hc hrep
    · exact hcan
  case shift_one =>
    rename_i hm hp hi
    obtain ⟨hcC, hcL, hcL2, w, hw, hv⟩ := hi.1
    have ht := hi.2
    rw [hv] at ht
    exact order_of_shift (by rw [ht]; rfl) (by rw [ht]; rfl) (by rw [ht]; rfl) hcC
      (hB.shiftLC hm) (hB.shiftCR hm)
  case shift_done => exact hO
  case copy_one =>
    rename_i hm hp hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case copy_done =>
    rename_i hm hp hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case home_start =>
    rename_i hm hl hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case home_step =>
    rename_i hm hl hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case fpp_slice =>
    rename_i hm hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case fpp_done =>
    rename_i hm hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case markEnd_step =>
    rename_i hm he hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans rfl)
      ((congrArg GalilVM.center hi.2).trans rfl)
      ((congrArg GalilVM.right hi.2).trans rfl)
  case markEnd_found =>
    rename_i hm he hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl))
      ((congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl))
      ((congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl))
  case choose_step =>
    rename_i hm hs hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl))
      ((congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl))
      ((congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl))
  case rewind_done =>
    rename_i hm hfi hi
    exact order_of_eqs hO ((congrArg GalilVM.left hi.2).trans (by rw [hi.1]; rfl))
      ((congrArg GalilVM.center hi.2).trans (by rw [hi.1]; rfl))
      ((congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl))
  case choose_select =>
    rename_i hm hodd hs hi
    exact order_of_const (p := s.right) ((congrArg GalilVM.left hi.2).trans (by rw [hi.1]; rfl))
      ((congrArg GalilVM.center hi.2).trans (by rw [hi.1]; rfl))
      ((congrArg GalilVM.right hi.2).trans (by rw [hi.1]; rfl))
  case rewind_one =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    have e2 : t.center = s.center := (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have e3 : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    have h1 := pos_left s.left
    exact ⟨by rw [e1, e2]; have := hO.lc; omega, by rw [e2, e3]; exact hO.cr⟩
  case rewind_pair =>
    rename_i hm hpr hfi hi
    have e1 : t.left = GalilScaffoldInputHead.left s.left :=
      (congrArg GalilVM.left hi.2).trans (by rw [hi.1.2]; rfl)
    have e2 : t.center = GalilScaffoldInputHead.left s.center :=
      (congrArg GalilVM.center hi.2).trans (by rw [hi.1.2]; rfl)
    have e3 : t.right = s.right := (congrArg GalilVM.right hi.2).trans (by rw [hi.1.2]; rfl)
    have h1 := pos_left s.left
    have h2 := pos_left s.center
    exact ⟨by rw [e1, e2]; have := hO.lc; omega,
      by rw [e2, e3]; have := hO.lc; have := hO.cr; omega⟩
  case replayStart =>
    rename_i o hm ho ho' hi
    obtain ⟨-, hr, hl, hce, -⟩ : replayStartVM entry s t := hi
    exact order_of_const hl hce hr

#print axioms order_tick

end Tick

/-! ## 4. Along a pre-loaded trace -/

theorem order_boot (w : List (Fin 2)) : Order (boot w).vm := ⟨le_rfl, le_rfl⟩

section Trace
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

theorem order_trace {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first raw st Tc)
    (hbud : ∀ i, i < Tc raw.length → OrderBudget (st i).ctl (st i).vm) :
    ∀ i, i ≤ Tc raw.length → Order (st i).vm := by
  intro i
  induction i with
  | zero => intro _; rw [hP.start]; exact order_boot raw
  | succ i ih =>
    intro hi
    exact order_tick (onLetterVM raw) leftFirstVM centre place entry q first 2048
      (ih (by omega)) (hbud i (by omega)) (hP.trace.tick i (by omega))

/-- **(Named) the order budget along every pre-loaded trace.** -/
def H_orderBudget : Prop :=
  ∀ w : List (Fin 2), 0 < w.length → ∀ st Tc, PreTrace centre place entry q first w st Tc →
    ∀ i, i < Tc w.length → OrderBudget (st i).ctl (st i).vm

/-- **`H_headOrder`, reduced to the comparison/shift budget.** -/
theorem h_headOrder_of_budget (h : H_orderBudget centre place entry q first) :
    H_headOrder centre place entry q first :=
  fun w hw st Tc hP i hi =>
    order_head_bounds
      (order_trace centre place entry q first hP (fun j hj => h w hw st Tc hP j hj) i hi)

end Trace

#print axioms pos_left
#print axioms pos_right_le
#print axioms pos_le_right
#print axioms order_boot
#print axioms order_trace
#print axioms h_headOrder_of_budget

end PalPeg.GalilTrailOrder
