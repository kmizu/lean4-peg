import PalPeg.CloseoutPreload21
import PalPeg.GalilScaffoldTopSearch
import PalPeg.GalilScaffoldTopOutputTrace

/-!
# The two interface obligations of `CloseoutPreload21` §4, on the concrete frame

`CloseoutPreload21` closes both gaps of `CloseoutPreload19` §4 at the level of
`GalilScaffoldTop.Tick`, and leaves two interface obligations:

1. **the event coupling** — that the boolean a leg's `searchStep` consumes on a
   tick is the boolean `ScanTrace` records for that tick;
2. **availability and phase** — that `∀ s, F.available s` and `1 ≤ clock ≤ delay`
   hold for the concrete frame `galilFrameS P q first`.

§1 settles (1) *unconditionally*: on `galilFrameS` a background tick feeds
`searchStep` the literal `false` (`background_event_false`), and a comparison
tick whose outcome is `matched` feeds it the literal `true`
(`compare_event_true_of_matched`) while a mismatching one feeds `false`
(`compare_event_false_of_mismatch`).  Those are exactly the three `Tick` branches
`ScanTrace`'s three constructors carry, with exactly the booleans `as` records —
`scan_wait`/`scan_count` carry `F.background`, `scan_match` carries
`F.compare` + `F.matched`.

§2 settles the phase half of (2) unconditionally: `1 ≤ clock ≤ delay` is a
*tick invariant* (`ClockInv`, `tick_clockInv`, `stepsAll_clockInv`), so a leg
entered in phase stays in phase and `CloseoutPreload21`'s `h1`/`h2` need not be
assumed at each leg — only at the machine's start, where `Control.initial`
supplies them (`clockInv_initial`).

§3 reduces the availability half to a statement purely about the right input
head: `(galilFrameS P q first).available s` is *definitionally* `canRight
s.right` (`available_iff_canRight`).  **It is not derivable from
`SoundScanNR raw`**, which is an output-relation invariant
(`GalilScaffoldTopFallbackRestartAll.SoundScanNR`) and says nothing about the
head; the supply fact needs its own invariant.  That is the one missing input,
and with it `postRunP_of_machine` is still not provable here — §4.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload22

open PalPeg
open PalPeg.GalilScaffoldController (Control)
open PalPeg.GalilScaffoldTop (Frame State Tick)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM ScanVM SearchVM Shared searchStep
  searchLens scanLens galilFrameS searchEffect afterCompare afterMismatch)
open PalPeg.GalilScaffoldChainInputSupply (StepsAll)
open PalPeg.GalilScaffoldChainVerifier (canRight)

/-! ## 1. The event coupling, on `galilFrameS` -/

/-- **NAMED — a background tick feeds `searchStep` the boolean `false`.**  This
is the `scan_wait`/`scan_count` half of the coupling `CloseoutPreload21` §4
asks for: those two `Tick` branches carry `F.background s s'`, and `ScanTrace`
records `false` for them. -/
theorem background_event_false (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (hidle : s.chain = .idle) :
    searchStep (P.place s) false (searchLens.get s) (searchLens.get s') := by
  obtain ⟨-, -, hse, -, -⟩ := hb
  rcases hse with ⟨-, hs⟩ | ⟨hne, -⟩
  · exact hs
  · exact absurd hidle hne

/-- **NAMED — a matching comparison feeds `searchStep` the boolean `true`.**
This is the `scan_match` half of the coupling: that branch carries
`F.compare s s'` together with `F.matched s'`, and `ScanTrace` records `true`
for it. -/
theorem compare_event_true_of_matched (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hcmp : (galilFrameS P q first).compare s s')
    (hmt : (galilFrameS P q first).matched s') (hidle : s.chain = .idle) :
    searchStep (P.place s) true (searchLens.get s) (searchLens.get s') := by
  obtain ⟨vs, vq, a, -, -, ha, hse, -, ht⟩ := hcmp
  cases a with
  | false =>
      exfalso
      have hm' : (galilFrameS P q first).matched (scanLens.set s vs) := by
        subst ht
        have h0 : GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainInputSupply.afterBirth _ (afterMismatch s vs vq)).left
          = GalilScaffoldInputHead.read (PalPeg.GalilScaffoldChainInputSupply.afterBirth _ (afterMismatch s vs vq)).right := hmt
        rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_left, PalPeg.GalilScaffoldChainInputSupply.afterBirth_right] at h0
        exact h0
      exact Bool.noConfusion (ha.mpr hm')
  | true =>
      have hget : searchLens.get s' = vq := by
        subst ht; rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_searchGet]; rfl
      rw [hget]
      rcases hse with ⟨-, hs⟩ | ⟨hne, -⟩
      · exact hs
      · exact absurd hidle hne

/-- The mismatching comparison (the `scan_shift`/`scan_fallback` branches, which
leave `.scan` and so never occur inside a `ScanTrace`) feeds `false`. -/
theorem compare_event_false_of_mismatch (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hcmp : (galilFrameS P q first).compare s s')
    (hmt : ¬ (galilFrameS P q first).matched s') (hidle : s.chain = .idle) :
    searchStep (P.place s) false (searchLens.get s) (searchLens.get s') := by
  obtain ⟨vs, vq, a, -, -, ha, hse, -, ht⟩ := hcmp
  cases a with
  | true =>
      exfalso
      refine hmt ?_
      have : (galilFrameS P q first).matched (scanLens.set s vs) := ha.mp rfl
      subst ht
      show GalilScaffoldInputHead.read
          (PalPeg.GalilScaffoldChainInputSupply.afterBirth _ (afterCompare s vs vq)).left
        = GalilScaffoldInputHead.read
          (PalPeg.GalilScaffoldChainInputSupply.afterBirth _ (afterCompare s vs vq)).right
      rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_left,
        PalPeg.GalilScaffoldChainInputSupply.afterBirth_right]
      exact this
  | false =>
      have hget : searchLens.get s' = vq := by
        subst ht; rw [PalPeg.GalilScaffoldChainInputSupply.afterBirth_searchGet]; rfl
      rw [hget]
      rcases hse with ⟨-, hs⟩ | ⟨hne, -⟩
      · exact hs
      · exact absurd hidle hne

/-! ## 2. The phase half: `1 ≤ clock ≤ delay` is a tick invariant -/

/-- The clock phase `CloseoutPreload21`'s leg lemmas assume on entry. -/
def ClockInv (delay : ℕ) (c : Control) : Prop := 1 ≤ c.clock ∧ c.clock ≤ delay

/-- **NAMED — the phase is a tick invariant.**  Every `Tick` either keeps the
clock, decrements it from above one, or resets it to `delay`; so `1 ≤ clock ≤
delay` propagates through arbitrary runs and never has to be assumed again. -/
theorem tick_clockInv {σ : Type} {F : Frame σ} {delay : ℕ} {x y : State σ}
    (h : Tick F delay x y) (hd : 0 < delay) (hi : ClockInv delay x.ctl) :
    ClockInv delay y.ctl := by
  obtain ⟨h1, h2⟩ := hi
  refine ⟨?_, ?_⟩ <;> (cases h <;> dsimp only at h1 h2 ⊢ <;> omega)

/-- The phase holds at the machine's start. -/
theorem clockInv_initial (delay : ℕ) (hd : 0 < delay) :
    ClockInv delay (GalilScaffoldController.initial delay) := ⟨hd, le_rfl⟩

/-- The phase along a whole `StepsAll` run. -/
theorem stepsAll_clockInv {σ : Type} {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) (hd : 0 < delay)
    (hi : ClockInv delay x.ctl) : ClockInv delay y.ctl := by
  induction h with
  | zero x _ => exact hi
  | succ hx ht hr ih => exact ih (tick_clockInv ht hd hi)

/-! ## 3. The availability half, reduced to the right head -/

/-- **NAMED — availability on the concrete frame is exactly `canRight` of the
right input head.**  Definitional: `galilFrameS` inherits `available` from
`galilFrame`, which pulls `scanFrame`'s `fun s => canRight s.right` along
`scanLens`. -/
theorem available_iff_canRight (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) :
    (galilFrameS P q first).available s ↔ canRight s.right := Iff.rfl

/-- The hypothesis `CloseoutPreload21`'s leg lemmas take, in head language. -/
theorem availAll_of_canRight (P : Shared) (q : ℕ) (first : Fin 9)
    (h : ∀ s : GalilVM, canRight s.right) : ∀ s : GalilVM, (galilFrameS P q first).available s :=
  fun s => (available_iff_canRight P q first s).mpr (h s)

/-- Matching on the concrete frame is the comparison of the two head symbols. -/
theorem matched_iff (P : Shared) (q : ℕ) (first : Fin 9) (s : GalilVM) :
    (galilFrameS P q first).matched s ↔
      GalilScaffoldInputHead.read s.left = GalilScaffoldInputHead.read s.right := Iff.rfl

/-!
## 4. What is left

* **(i) closed.**  §1 is the coupling: the three `Tick` branches that stay in
  `.scan` hand `searchStep` exactly the booleans `ScanTrace` records.
* **(ii) half closed.**  The phase `1 ≤ clock ≤ 2048` is a tick invariant (§2),
  so it is free after the initial state.  Availability is *not*: §3 shows it is
  definitionally `canRight s.right`, and `SoundScanNR raw` — an output relation
  — does not mention the head, so `∀ s, F.available s` does not follow from the
  `StepsAll` invariant currently carried.

**Missing (one line):** an input-supply invariant on the right head — that
`canRight s.right` holds at every state of a scan leg (equivalently, that the
real-time feed has not run dry before the leg ends) — carried alongside
`SoundScanNR` in `StepsAll`; without it `postRunP_of_machine : PostRunP` is not
provable, and it is not proved here.

**無条件 PAL ∈ PEG は未完.**
-/

#print axioms background_event_false
#print axioms compare_event_true_of_matched
#print axioms compare_event_false_of_mismatch
#print axioms tick_clockInv
#print axioms clockInv_initial
#print axioms stepsAll_clockInv
#print axioms available_iff_canRight
#print axioms availAll_of_canRight
#print axioms matched_iff

end PalPeg.CloseoutPreload22
