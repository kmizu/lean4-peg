import PalPeg.CloseoutPackRun48
import PalPeg.CloseoutLenNonneg

/-!
# `lag` is canonical and non-negative at every chain shape

`CloseoutPackRun48.lagCan_step` preserves `LagCan` (the `watch` shape) across a
`ChainStep`, but it needs the `back` shape's lag as an input (`hback`), because
`backDone` installs the `back` lag into the new watch.  Reading the constructors
of `ChainStep` (`GalilScaffoldTopChainVM:50`):

* `copyBit` — `lag` unchanged;
* `copyEnd` — `.copy … lag … → .back … lag …`, unchanged;
* `backStep` — unchanged;
* `backDone` — `.back … lag … → .watch ⟨_, lag, _⟩`, unchanged;
* `watchStep` — the only shape that touches it, through
  `GalilScaffoldChainWatch.Internal`.

So the property "every live shape's lag is canonical and non-negative" is closed
under `ChainStep` once the `watch` case is known, and `lagCan_step` supplies
that.  `LagAll` below states it for all three shapes at once, which removes the
`hback` side input.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutLagAll

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead
open PalPeg.CloseoutPackRun47 PalPeg.CloseoutPackRun48

/-- **(NAMED) `LagAll`**: the lag counter is canonical and non-negative at every
live chain shape. -/
def LagAll (z : ChainVM) : Prop :=
  (∀ wch : GalilScaffoldChainWatch.State, z = .watch wch →
    Canonical wch.lag ∧ 0 ≤ value wch.lag) ∧
  (∀ (v : GalilScaffoldChainPeriod.Tape) (h lag margin : Counter) (ver : PlaceHead),
    z = .back v h lag margin ver → Canonical lag ∧ 0 ≤ value lag) ∧
  (∀ (t : GalilScaffoldTape.Tape) (h : Counter) (p : GalilScaffoldPlace.Place)
      (v : GalilScaffoldChainPeriod.Tape) (lag margin : Counter) (ver : PlaceHead),
    z = .copy t h p v lag margin ver → Canonical lag ∧ 0 ≤ value lag)

/-- `LagAll` gives Run48's `LagCan`. -/
theorem lagAll_lagCan {z : ChainVM} (h : LagAll z) : LagCan z := h.1

/-- `LagAll` gives Run48's `hback` side input. -/
theorem lagAll_back {z : ChainVM} (h : LagAll z) :
    ∀ (v : GalilScaffoldChainPeriod.Tape) (hh lag margin : Counter) (ver : PlaceHead),
      z = .back v hh lag margin ver → Canonical lag ∧ 0 ≤ value lag := h.2.1

/-- `LagAll` at an idle chain. -/
theorem lagAll_idle : LagAll .idle := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- `LagAll` at a broken chain. -/
theorem lagAll_broken (w : GalilScaffoldChainWatch.State) : LagAll (.broken w) := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- **`LagAll` is closed under `ChainStep`.**  Every constructor but `watchStep`
carries `lag` through unchanged; `watchStep` is Run48's `lagCan_step`. -/
theorem lagAll_step {x z : ChainVM} (h : LagAll x) (hst : ChainStep x z) : LagAll z := by
  cases hst with
  | idle => exact h
  | brokenIdle w => exact h
  | watchBreak w hb => exact lagAll_broken _
  | copyBit t hh p v lag margin ver a one legal present =>
    refine ⟨by intros; simp_all, by intros; simp_all, ?_⟩
    intro t' h' p' v' lag' margin' ver' hc
    injection hc with _ _ _ _ he _ _
    subst he
    exact h.2.2 t hh p v lag margin ver rfl
  | copyEnd t hh p v lag margin ver b hleft hp hv =>
    refine ⟨by intros; simp_all, ?_, by intros; simp_all⟩
    intro v' h' lag' margin' ver' hb
    injection hb with _ _ he _ _
    subst he
    exact h.2.2 t hh p v lag margin ver rfl
  | backStep v hh lag margin ver hf =>
    refine ⟨by intros; simp_all, ?_, by intros; simp_all⟩
    intro v' h' lag' margin' ver' hb
    injection hb with _ _ he _ _
    subst he
    exact h.2.1 v hh lag margin ver rfl
  | backDone v hh lag margin ver hf =>
    refine ⟨?_, by intros; simp_all, by intros; simp_all⟩
    intro wch hw
    injection hw with he
    subst he
    exact h.2.1 v hh lag margin ver rfl
  | watchStep w w' ht =>
    refine ⟨?_, by intros; simp_all, by intros; simp_all⟩
    exact lagCan_step h.1 (lagAll_back h) (ChainStep.watchStep w w' ht)

/-- **`LagAll` is closed under `ChainMatched`.**  Every constructor either keeps
`lag` or `inc`s it, and `inc` preserves both halves
(`GalilScaffoldCounter.inc_canonical`, `CloseoutLenNonneg.nonneg_inc`). -/
theorem lagAll_matched {y z : ChainVM} (h : LagAll y) (hm : ChainMatched y z) : LagAll z := by
  cases hm with
  | brokenMatched w => exact lagAll_broken _
  | idle => exact h
  | copy t hh p v lag margin ver =>
    refine ⟨by intros; simp_all, by intros; simp_all, ?_⟩
    intro t' h' p' v' lag' margin' ver' hc
    injection hc with _ _ _ _ he _ _
    subst he
    obtain ⟨hc1, hc2⟩ := h.2.2 t hh p v lag margin ver rfl
    exact ⟨inc_canonical _ hc1, PalPeg.CloseoutLenNonneg.nonneg_inc hc2⟩
  | back v hh lag margin ver =>
    refine ⟨by intros; simp_all, ?_, by intros; simp_all⟩
    intro v' h' lag' margin' ver' hb
    injection hb with _ _ he _ _
    subst he
    obtain ⟨hc1, hc2⟩ := h.2.1 v hh lag margin ver rfl
    exact ⟨inc_canonical _ hc1, PalPeg.CloseoutLenNonneg.nonneg_inc hc2⟩
  | watch w w' ho =>
    refine ⟨?_, by intros; simp_all, by intros; simp_all⟩
    exact lagCan_matched h.1 (ChainMatched.watch w w' ho)
  | breaks w w' hb =>
    refine ⟨by intros; simp_all, by intros; simp_all, by intros; simp_all⟩

#print axioms lagAll_idle
#print axioms lagAll_step
#print axioms lagAll_matched

end PalPeg.CloseoutLagAll
