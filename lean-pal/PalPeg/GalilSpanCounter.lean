import PalPeg.GalilScaffoldTopOutputCycle
import PalPeg.GalilLiveCentre

/-!
# The length counter is the span: `length = 2·radius + 1`

The `length` counter counts the places of the current palindrome span,
`2·radius + 1`. It is `1` after `init` and after a fallback (radius `0`),
grows by two at each matched comparison (radius by one), and both shrink
together during a shift. This relation lets the fallback window
`(stream …).take (length+1)` cover every radius below the current one,
which `leftmost_fallback` needs.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter GalilScaffoldInputHead
  GalilScaffoldChainVerifier

/-- The span relation between the counters. -/
def SpanRep (s : GalilVM) : Prop := value s.length = 2 * value s.radius + 1

theorem spanRep_afterCompare {s : GalilVM} {vs : ScanVM} {vq : SearchVM} (h : SpanRep s) :
    SpanRep (afterCompare s vs vq) := by
  unfold SpanRep at *
  rw [afterCompare_length, afterCompare_radius, inc_value, inc_value, inc_value]
  omega

theorem spanRep_replayDec (b : Bool) {s : GalilVM} (h : SpanRep s) : SpanRep (replayDec b s) := by
  unfold SpanRep at *
  rw [replayDec_length, replayDec_radius]
  exact h

theorem spanRep_background (P : Shared) (q : ℕ) (first : Fin 9) {s s' : GalilVM}
    (hb : (galilFrameS P q first).background s s') (h : SpanRep s) : SpanRep s' := by
  obtain ⟨_, _, _, _, _, hrad, hlen, _⟩ := backgroundS_fields P q first hb
  unfold SpanRep at *
  rw [hrad, hlen]
  exact h

theorem spanRep_watchSegE (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {es : List Bool}
    {c c' : Control} {s t : GalilVM} (h : WatchSegE P q first delay es c s c' t) :
    SpanRep s → SpanRep t := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | count c s s' _ _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | countR c s s' _ _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih => exact fun hs => ih (spanRep_afterCompare hs)
  | matchIdle c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact fun hs => ih (spanRep_afterCompare hs)
  | matchIdleR c s vs vq o _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    exact fun hs => ih (spanRep_replayDec true (spanRep_afterCompare hs))

theorem spanRep_scanSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) {n : ℕ}
    {c c' : Control} {s t : GalilVM} (h : ScanSeg P q first delay n c s c' t) :
    SpanRep s → SpanRep t := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | count c s s' _ _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ _ ih => exact fun hs => ih (spanRep_afterCompare hs)

theorem spanRep_watchSeg (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    {c c' : Control} {s t : GalilVM} (h : WatchSeg P q first delay c s c' t) :
    SpanRep s → SpanRep t := by
  induction h with
  | stop c s => exact id
  | wait c s s' _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | count c s s' _ _ _ _ hb _ ih => exact fun hs => ih (spanRep_background P q first hb hs)
  | «match» c s vs vq o _ _ _ _ _ _ _ _ _ _ ih => exact fun hs => ih (spanRep_afterCompare hs)

/-- The span relation on a shift state. -/
def SpanRepS (s : ShiftState) : Prop := value s.length = 2 * value s.radius + 1

theorem spanRepS_shiftTick {s : ShiftState} (h : SpanRepS s) : SpanRepS (shiftTick s) := by
  unfold SpanRepS at *
  simp only [shiftTick, dec_value]
  omega

theorem spanRepS_shiftRun {s t : ShiftState} {n : ℕ} (h : ShiftRun s n t) : SpanRepS s → SpanRepS t := by
  induction h with
  | stop s => exact id
  | next s _ _ _ _ _ ih => exact fun hs => ih (spanRepS_shiftTick hs)

theorem shiftLens_set_radius (s : GalilVM) (t : ShiftState) (ch : ChainVM) (cy : Counter) :
    (shiftLens.set s ⟨t, ch, cy⟩).radius = t.radius := rfl

theorem shiftLens_set_length (s : GalilVM) (t : ShiftState) (ch : ChainVM) (cy : Counter) :
    (shiftLens.set s ⟨t, ch, cy⟩).length = t.length := rfl

/-- After a mismatch and the shift entry, the shift run starts with the span
relation and keeps it to the resumed state. -/
theorem spanRep_shift {s1 : GalilVM} (h : ℕ) {t' : ShiftState} {v w : GalilScaffoldChainWatch.State}
    {cycle : Counter} (s2 : GalilVM)
    (hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩
      w reset h t' v cycle) (hs : SpanRep s1) :
    SpanRep (shiftLens.set s2 ⟨t', .watch v, cycle⟩) := by
  have h0 : SpanRepS ⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ := by
    unfold SpanRepS SpanRep at *
    simp only [inc_value]
    omega
  have h1 := spanRepS_shiftRun (shiftRun_of_chain hchain) h0
  unfold SpanRep SpanRepS at *
  rw [shiftLens_set_radius, shiftLens_set_length]
  exact h1

theorem spanRep_rounds (P : Shared) (q : ℕ) (first : Fin 9) (delay h : ℕ) {m : ℕ}
    {c c' : Control} {s s' : GalilVM} (hr : Rounds P q first delay h m c s c' s') :
    SpanRep s → SpanRep s' := by
  induction hr with
  | stop c s => exact id
  | next c s hseg _ _ _ w _ _ vs vq _ _ _ _ _ _ _ s2 _ hs2 _ hchain _ _ _ ih =>
    intro hs
    exact ih (spanRep_shift h s2 hchain (spanRep_scanSeg P q first delay hseg hs))

/-- The restart tick keeps the counters. -/
theorem spanRep_restart (x : GalilVM) (entry : ℕ) (w : GalilScaffoldChainWatch.State) (h : SpanRep x) :
    SpanRep {x with chain := .idle, lower := w.machine.control.last, search := GalilScaffoldSearchFinish.begin w.machine.control.last x.radius, dp := GalilScaffoldControl.reset entry x.dp} := h

/-- After `init` from reset counters. -/
theorem spanRep_of_init {s0 t : GalilVM} (hlen : t.length = inc s0.length) (hrad : t.radius = s0.radius)
    (h0r : s0.radius = reset) (h0l : s0.length = reset) : SpanRep t := by
  unfold SpanRep
  rw [hlen, hrad, h0r, h0l, inc_value, reset_eq_ofNat, ofNat_value]
  omega

/-- After a fallback: `length = 1`, `radius = 0`. -/
theorem spanRep_of_fallback {t : GalilVM} (hlen : t.length = ofNat 1) (hrad : t.radius = reset) : SpanRep t := by
  unfold SpanRep
  rw [hlen, hrad, reset_eq_ofNat, ofNat_value, ofNat_value]
  omega

/-- The span relation and the scan invariant make the fallback window
cover every radius below the current one: `2·(n - C) + 1 ≤ length`. -/
theorem span_covers {raw : List (Fin 2)} {s : GalilVM} {Rad : ℕ}
    (hi : ScanInvariant raw (position s.center) Rad s.left s.right)
    (hR : RadiusRep s.radius Rad) (hs : SpanRep s) {ℓ : ℕ} (hv : value s.length = ℓ) :
    2 * (position s.right - position s.center) + 1 ≤ ℓ := by
  have hp := hi.rightPos
  have hrv : value s.radius = Rad := hR.2
  unfold SpanRep at hs
  have e : position s.right - position s.center = Rad := by omega
  rw [e]
  omega

#print axioms spanRep_rounds
#print axioms span_covers

end PalPeg.GalilScaffoldChainInputSupply
