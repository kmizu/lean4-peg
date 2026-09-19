import PalPeg.CanonicalLocalRealizes
import PalPeg.CloseoutCheckW
import PalPeg.GalilNoBelowFirst
/-!
# Period minimality on canonical prefixes from boot

The no-restart schedule never raises `GalilVM.lower`: search and phase steps
preserve it, while init/replayStart reset it.  Thus its value on any finite
packed prefix from boot is zero.  This removes the separate lower-period
history premise of `noBelow_first_of_result` on those prefixes.

No completed checkpoint trace is needed for `noBelow_first_canonical`; using
one there would presuppose the cycle oracle this lemma is meant to support.
The geometric origin, DP result, and their link to the active chain remain
explicit premises.  `OracleRun` now uses `packed_lower_zero` to supply lower
zero to its shift leaf.  This does not by itself produce that leaf or discharge
the cycle oracle.
-/

set_option autoImplicit false
namespace PalPeg.CanonicalPeriod
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton
open PalPeg.GalilScaffoldCounter

private theorem searchStep_lower {center : GalilScaffoldPlace.Place} {a : Bool} {v v' : SearchVM}
    (h : searchStep center a v v') : v'.lower = v.lower := by
  unfold searchStep at h
  cases hm : v.search.mode <;> simp only [hm] at h
  all_goals first
    | exact h.2.1
    | (rcases h with ⟨y, _, rfl⟩; rfl)
    | (rw [h])
    | (split at h <;> (rw [h] <;> rfl))

private theorem searchEffect_lower {P : Shared} {a : Bool} {s : GalilVM} {v : SearchVM}
    (h : searchEffect P a s v) : v.lower = s.lower := by
  rcases h with ⟨_, h⟩ | ⟨_, rfl⟩
  · exact searchStep_lower h
  · rfl

private theorem background_lower {P : Shared} {q : ℕ} {first : Fin 9} {s t : GalilVM}
    (h : (galilFrameS P q first).background s t) : t.lower = s.lower :=
  searchEffect_lower h.2.2.1

private theorem compare_lower {P : Shared} {q : ℕ} {first : Fin 9} {s t : GalilVM}
    (h : (galilFrameS P q first).compare s t) : t.lower = s.lower := by
  obtain ⟨vs, vq, a, _, _, _, hse, _, rfl⟩ := h
  rw [afterBirth_lower]
  cases a <;> exact searchEffect_lower hse

theorem tick_lower_zero {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q delay : ℕ} {first : Fin 9} {raw : List (Fin 2)} {x y : State GalilVM}
    (h : Tick (galilFrameS (PofC centre place entry raw) q first) delay x y)
    (hnr : x.ctl.mode = .scan → ¬ restartVM entry x.vm y.vm)
    (hz : x.vm.lower = reset) : y.vm.lower = reset := by
  cases h <;> simp only at hz ⊢
  case init c s t hm hi => exact hi.2.2.2.2.2.2.2.2.2.2.2.1
  case replayStart c s t o hm hi ho ho' => exact hi.2.2.2.2.2.2.2.2.2.2.2.1
  case scan_wait c s t hm ha hb => exact (background_lower hb).trans hz
  case scan_count c s t hm ha hc hb => exact (background_lower hb).trans hz
  case scan_match c s u t o hm ha hc hcmp hmt hpl ho =>
    change t = (if c.replaying then {u with replay := dec u.replay} else u) at hpl
    rw [hpl]
    split <;> exact (compare_lower hcmp).trans hz
  case scan_shift c s u t hm ha hc hcmp hmt hr hg hb =>
    obtain ⟨w, _, rfl⟩ := hb
    exact (compare_lower hcmp).trans hz
  case scan_fallback c s u t hm ha hc hcmp hmt hg hr hb =>
    obtain ⟨p, ht, _⟩ := hb
    rw [ht]
    exact (compare_lower hcmp).trans hz
  case restart c s t hm hb => exact False.elim (hnr hm hb)
  all_goals try exact hz
  all_goals
    rename_i he
    exact (congrArg GalilVM.lower he.2).trans hz

/-- Lower-zero is a prefix invariant; no future checkpoints are assumed. -/
theorem trace_lower_zero {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q delay : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {st : ℕ → State GalilVM} {e : ℕ}
    (hTick : ∀ i, i < e → Tick (galilFrameS (PofC centre place entry raw) q first)
      delay (st i) (st (i+1)))
    (hCanonical : ∀ i, i < e → PalPeg.GalilTickFair.Canonical entry delay (st i) (st (i+1)))
    (hZero : (st 0).vm.lower = reset) (i : ℕ) (hi : i ≤ e) : (st i).vm.lower = reset := by
  induction i with
  | zero => exact hZero
  | succ i ih =>
    exact tick_lower_zero (hTick i (by omega))
      (hCanonical i (by omega)).noRestart (ih (by omega))

/-- In particular, every state of a finite packed prefix from boot has lower zero. -/
theorem packed_lower_zero {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {n : ℕ} {y : State GalilVM}
    (h : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first raw n
      (PalPeg.GalilFinalAssembly.boot raw) y) : y.vm.lower = reset := by
  obtain ⟨g, hg0, hgn, ht, hc, _⟩ := h
  rw [← hgn]
  exact trace_lower_zero ht.tick hc (by rw [hg0]; rfl) n le_rfl

/-- The canonical trace selected by the final consumer has the same invariant. -/
theorem preTrace_lower_zero {centre : GalilVM → Fin 3}
    {place : GalilVM → GalilScaffoldPlace.Place} {entry q : ℕ} {first : Fin 9}
    {raw : List (Fin 2)} {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hTrace : PalPeg.GalilFinalAssembly.PreTrace centre place entry q first raw st Tc)
    (hCanonical : PalPeg.CloseoutCheckW.CanonTrace entry raw st Tc)
    (i : ℕ) (hi : i ≤ Tc raw.length) : (st i).vm.lower = reset :=
  trace_lower_zero hTrace.trace.tick hCanonical (by rw [hTrace.start]; rfl) i hi

open PalPeg.GalilScaffoldInputHead PalPeg.GalilScaffoldChainVerifier

/-- For the actual booted canonical run the DP lower bound is zero.  Thus the
first-shift period theorem needs no separate history excluding smaller periods.
The DP result and the geometric origin still have to be produced. -/
theorem noBelow_first_canonical (a : Fin 2) (ls rs suffix : List (Fin 2)) (gap : Bool)
    {centre : GalilVM → Fin 3} {place : GalilVM → GalilScaffoldPlace.Place}
    {entry q : ℕ} {first : Fin 9} {n : ℕ} {current : State GalilVM}
    (hRun : PalPeg.CloseoutCheckW.StepsIMWC centre place entry q first
      ((a :: ls).reverse ++ rs ++ suffix) n
      (PalPeg.GalilFinalAssembly.boot ((a :: ls).reverse ++ rs ++ suffix)) current)
    (org : ReadOrigin ((a :: ls).reverse ++ rs ++ suffix))
    (hC : org.center = position (represent ⟨a :: ls, gap⟩ (rs.map some) suffix))
    {s : OnlyCompareState} (he : Entry ((a :: ls).reverse ++ rs ++ suffix) org s)
    {span : ℕ} {y : GalilFppWide.Config 12}
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls, gap⟩).take (span + 1))
      (value current.vm.lower).toNat 0 y)
    (hy : y.pc = 346) (hout : y.pos 11 = org.interior.length + 1) :
    ∀ p, 0 < p → p < 2 * (org.interior.length + 1) →
      ¬ PalPeg.HasPeriod
        (Span ((a :: ls).reverse ++ rs ++ suffix) org.center org.radius) p := by
  apply noBelow_first_of_result a ls rs suffix gap org hC he hres hy hout
  rw [packed_lower_zero hRun]
  intro δ hPositive hLower
  have : δ ≤ 0 := by simpa [value, reset] using hLower
  omega

#print axioms noBelow_first_canonical
#print axioms preTrace_lower_zero
end PalPeg.CanonicalPeriod
