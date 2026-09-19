import PalPeg.GalilTickFair
import PalPeg.GalilScaffoldTopScanRun
import PalPeg.GalilScaffoldTopReplay

/-!
# The `init` / `replayStart` witnesses are `Fair`

`GalilTickFair.Fair` has three clauses.  The two scan clauses (`restartFirst`,
`fallbackPlace`) are vacuous out of mode `.init` / `.replayStart`; the third,
`keepsSearchCursor`, is **not** a consequence of `initVM` / `replayStartVM`
(neither relation mentions `periodOnly` or `walker`), so it has to be read off
the *witness*.  Here the witnesses of `GalilScaffoldTopScanRun.init_tick` and
`GalilScaffoldTopReplay.replayStart_tick` are made explicit (`initWitness` /
`replayStartWitness`) and shown to satisfy every field of `Fair`, together with
the ticks those lemmas (and hence `init_restarted` /
`fallback_replayStart_All`) produce.  Nothing about `Tick` determinism is
reproved and no `Tick`-level or choice-level witness is assumed fair.

The pins are independent of the input: `q`, `first` and the truncated word only
enter through `right s.right` (the head), never through `periodOnly`/`walker`,
so both ticks and both `Fair` facts hold uniformly in `q first delay`.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace PalPeg.CloseoutFairWitness

open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldChainVerifier
open PalPeg.GalilTickFair (Fair)

variable (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop)
  (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)

/-- The state built by `GalilScaffoldTopScanRun.init_tick`. -/
def initWitness (entry : ℕ) (s : GalilVM) : GalilVM :=
  ⟨GalilScaffoldChainVerifier.right s.right, GalilScaffoldChainVerifier.right s.right, GalilScaffoldChainVerifier.right s.right, .idle, s.cycle, s.remaining, s.radius,
    GalilScaffoldCounter.inc s.length, s.replay, s.fpp,
    GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset s.radius,
    GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩

/-- The state built by `GalilScaffoldTopReplay.replayStart_tick`. -/
def replayStartWitness (entry : ℕ) (s : GalilVM) : GalilVM :=
  ⟨s.center, s.center, s.center, .idle, s.cycle, s.remaining, GalilScaffoldCounter.reset,
    GalilScaffoldCounter.ofNat 1, s.radius, s.fpp,
    GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset,
    GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩

/-! ## The two cursor pins, read off the witnesses -/

theorem initWitness_periodOnly (entry : ℕ) (s : GalilVM) :
    (initWitness entry s).periodOnly = s.periodOnly := rfl

theorem initWitness_walker (entry : ℕ) (s : GalilVM) :
    (initWitness entry s).walker = s.walker := rfl

theorem replayStartWitness_periodOnly (entry : ℕ) (s : GalilVM) :
    (replayStartWitness entry s).periodOnly = s.periodOnly := rfl

theorem replayStartWitness_walker (entry : ℕ) (s : GalilVM) :
    (replayStartWitness entry s).walker = s.walker := rfl

/-! ## `Fair` for the two witnesses -/

theorem init_fair (entry delay : ℕ) (c : Control) (hm : c.mode = .init) (s : GalilVM) :
    Fair entry delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, initWitness entry s⟩ where
  restartFirst := by
    intro h _
    exact absurd (hm.symm.trans h) (by decide)
  fallbackPlace := by
    intro h _
    exact absurd (hm.symm.trans h) (by decide)
  keepsSearchCursor := by
    intro _
    exact ⟨initWitness_periodOnly entry s, initWitness_walker entry s⟩

theorem replayStart_fair (entry delay : ℕ) (c : Control) (hm : c.mode = .replayStart)
    (s : GalilVM) (o : Bool) :
    Fair entry delay ⟨c, s⟩
      ⟨{c with mode := .scan, clock := delay, output := o, replaying := GalilScaffoldCounter.positive s.radius}, replayStartWitness entry s⟩ where
  restartFirst := by
    intro h _
    exact absurd (hm.symm.trans h) (by decide)
  fallbackPlace := by
    intro h _
    exact absurd (hm.symm.trans h) (by decide)
  keepsSearchCursor := by
    intro _
    exact ⟨replayStartWitness_periodOnly entry s, replayStartWitness_walker entry s⟩

/-! ## The ticks of `init_tick` / `replayStart_tick`, with the witness exposed -/

theorem init_tick_witness (entry q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .init) (s : GalilVM) :
    Tick (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
      delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, initWitness entry s⟩ :=
  .init c s (initWitness entry s) hm
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem replayStartVM_witness (entry : ℕ) (s : GalilVM) :
    replayStartVM entry s (replayStartWitness entry s) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem replayStart_tick_witness (entry q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .replayStart) (s : GalilVM) :
    ∃ o : Bool,
      Tick (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
        delay ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := GalilScaffoldCounter.positive s.radius}, replayStartWitness entry s⟩ ∧
      (GalilScaffoldCounter.positive s.radius = true → o = c.output) := by
  classical
  set t : GalilVM := replayStartWitness entry s with hts
  have hrs : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).replayStart s t :=
    replayStartVM_witness entry s
  have hpos : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).replayPos t =
      GalilScaffoldCounter.positive s.radius := rfl
  cases hp : GalilScaffoldCounter.positive s.radius
  · refine ⟨if onLetter t then decide (leftFirst t) else c.output, ?_, ?_⟩
    · have ht := Tick.replayStart
        (F := galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
        (delay := delay) c s t (if onLetter t then decide (leftFirst t) else c.output) hm hrs
        (by rw [hpos, hp]; intro h; exact absurd h Bool.false_ne_true)
        (by
          rw [hpos, hp]; intro _
          refine ⟨fun hl => ?_, fun hl => ?_⟩
          · have hl' : onLetter t := hl
            show (if onLetter t then decide (leftFirst t) else c.output) = true ↔ leftFirst t
            rw [if_pos hl']; exact decide_eq_true_iff
          · have hl' : ¬ onLetter t := hl
            show (if onLetter t then decide (leftFirst t) else c.output) = c.output
            rw [if_neg hl'])
      rw [hpos, hp] at ht
      exact ht
    · intro h; exact absurd h Bool.false_ne_true
  · refine ⟨c.output, ?_, fun _ => rfl⟩
    have ht := Tick.replayStart
      (F := galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
      (delay := delay) c s t c.output hm hrs (by rw [hpos, hp]; intro _; rfl)
      (by rw [hpos, hp]; intro h; exact absurd h.symm Bool.false_ne_true)
    rw [hpos, hp] at ht
    exact ht

/-! ## Closeout: the ticks used downstream are fair -/

/-- The `init` tick of `init_restarted` (on `galilFrameS`) is fair. -/
theorem init_tick_fair_S (entry q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .init) (s : GalilVM) :
    Tick (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
      delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, initWitness entry s⟩ ∧
    Fair entry delay ⟨c, s⟩ ⟨{c with mode := .scan, output := true}, initWitness entry s⟩ :=
  ⟨tick_S_of_tick _ q first delay
      (init_tick_witness onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s)
      (by rw [hm]; decide),
   init_fair entry delay c hm s⟩

/-- The `replayStart` tick of `fallback_replayStart_All` (on `galilFrameS`) is fair. -/
theorem replayStart_tick_fair_S (entry q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control)
    (hm : c.mode = .replayStart) (s : GalilVM) :
    ∃ o : Bool,
      Tick (galilFrameS (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first)
        delay ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := GalilScaffoldCounter.positive s.radius}, replayStartWitness entry s⟩ ∧
      Fair entry delay ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := GalilScaffoldCounter.positive s.radius}, replayStartWitness entry s⟩ := by
  obtain ⟨o, ht, _⟩ :=
    replayStart_tick_witness onLetter leftFirst guard bs bf rs centre place entry q first delay c hm s
  exact ⟨o, tick_S_of_tick _ q first delay ht (by rw [hm]; decide),
    replayStart_fair entry delay c hm s o⟩

#print axioms init_fair
#print axioms replayStart_fair
#print axioms init_tick_witness
#print axioms replayStart_tick_witness
#print axioms init_tick_fair_S
#print axioms replayStart_tick_fair_S

end PalPeg.CloseoutFairWitness
