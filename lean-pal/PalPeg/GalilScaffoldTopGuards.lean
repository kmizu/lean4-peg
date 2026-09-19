import PalPeg.GalilScaffoldTopWatchGuard

/-!
# The concrete shift and fallback entries

Scala's shift branch: `!replaying && chain.canShift && chain.prediction() ==
right.read()`. On the unified VM `canShift` is `freshShiftGuard` on the
watching chain and the prediction is the period symbol under the verifier's
focus; the entry is `beginShiftVM` with the semiperiod length read from the
chain. The fallback entry is `beginFallbackVM` for some decoded right place.
With these in `galilShared`, the entry-existence hypotheses of
`compare_progress` hold outright, so a comparison always has a tick.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead

/-- `chain.canShift && chain.prediction() == right.read()` after the comparison:
watching, lag zero, phase 4, unbroken, and — in `periodOnly` — the
continuation countdown at its last cell (`cycleEnd`), otherwise `margin ≥ 0`
(`freshShiftGuard`); the prediction is the period symbol under the focus,
read before the shift entry's consume. -/
def shiftGuardVM (s : GalilVM) : Prop :=
  ∃ w : GalilScaffoldChainWatch.State, s.chain = .watch w ∧
    zero w.lag = true ∧ w.machine.control.phase = 4 ∧ w.machine.control.broken = false ∧
    (if s.periodOnly then singlePositive s.cycle = true else negative w.margin = false) ∧
    GalilScaffoldChainConsume.symbol w.machine.control.period.focus = read s.right

/-- The semiperiod length `h` of the watching chain, from its period tape:
the number of plain tokens plus the LAST token. -/
def periodLength (w : GalilScaffoldChainWatch.State) : ℕ :=
  w.machine.control.period.left.length + w.machine.control.period.right.length

def beginShiftVM' (s t : GalilVM) : Prop :=
  ∃ w : GalilScaffoldChainWatch.State, beginShiftVM (periodLength w) w s t

/-- **2026-09-19（モデル欠陥 `M-fallbackPlace`）**: 着地場所を search 自身の
walker の材料の中に収めた。Scala 正本の `beginFallback` は search の walker place
からコピーし、その walker は到着済みの入力しか見ていないので、
`stream p` が無制限なのはモデル欠陥だった（`Fair.fallbackPlace` がその分を
仮定として抱えており、`marksEntry` の残差 `WindowInOrigin` が塞がれていた）。
この形にすると **`WindowInOrigin` が着地でそのまま出る**
（`t.fpp.walker = p`、`t.right = s.right`）。 -/
def beginFallbackVM' (s t : GalilVM) : Prop :=
  ∃ p : GalilScaffoldPlace.Place, beginFallbackVM p s t ∧
    (GalilScaffoldPlace.stream p).length ≤ position s.right

theorem beginShift_exists (s : GalilVM) (hg : shiftGuardVM s) : ∃ t, beginShiftVM' s t := by
  obtain ⟨w, hw, _, _⟩ := hg
  exact ⟨_, w, hw, rfl⟩

theorem beginFallback_exists (s : GalilVM) : ∃ t, beginFallbackVM' s t :=
  ⟨_, ⟨[], false⟩, rfl, by simp [GalilScaffoldPlace.stream]⟩

/-- With the concrete entries, a comparison in scan mode always has a tick. -/
theorem compare_progress_concrete (onLetter leftFirst : GalilVM → Prop) (rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ)
    (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s : GalilVM) (hav : GalilScaffoldChainVerifier.canRight s.right)
    (hw : ∀ a : Bool, ∃ ch', ChainTick a s.chain ch') :
    ∃ (c' : Control) (t : GalilVM),
      Tick (galilFrame (galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry) q first)
        delay ⟨c, s⟩ ⟨c', t⟩ ∧ (c'.mode = .scan ∨ c'.mode = .shift ∨ c'.mode = .copy) :=
  compare_progress _ q first delay c hm hr hc s hav hw
    (fun s1 hg => beginShift_exists s1 hg) (fun s1 => beginFallback_exists s1)

#print axioms compare_progress_concrete

end PalPeg.GalilScaffoldChainInputSupply
