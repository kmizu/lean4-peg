import PalPeg.GalilScaffoldTopCopyChain

/-!
# ReplayStart and the fallback exit to scan

`stepReplayStart`: `replay := radius`, R and L copied from C, `radius := 0`,
`length := 1`, chain idle, search restarted, `replaying := replay > 0`,
clock reset, mode `scan`, output refreshed when not replaying and R is on a
letter. This module gives the concrete `Shared` effects on `GalilVM` (heads
and counters; the chain/search restart is left to the watch component), the
single `replayStart` tick, and the composition `fallback_to_scan`: from
`copy` mode to `scan` mode with L = R = C = the selected centre, `replay = r`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- `stepInit` on the VM: R right, L and C copied from R, `length++`. -/
def initVM (entry : ℕ) (s t : GalilVM) : Prop :=
  t.right = GalilScaffoldChainVerifier.right s.right ∧ t.left = GalilScaffoldChainVerifier.right s.right ∧
  t.center = GalilScaffoldChainVerifier.right s.right ∧ t.length = GalilScaffoldCounter.inc s.length ∧
  t.radius = s.radius ∧ t.remaining = s.remaining ∧ t.replay = s.replay ∧ t.cycle = s.cycle ∧ t.fpp = s.fpp ∧
  t.chain = .idle ∧ t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset s.radius ∧
  t.lower = GalilScaffoldCounter.reset ∧ t.dp = GalilScaffoldControl.reset entry s.dp

/-- `stepReplayStart` on the VM (chain/search restart abstracted into `watch`). -/
def replayStartVM (entry : ℕ) (s t : GalilVM) : Prop :=
  t.replay = s.radius ∧ t.right = s.center ∧ t.left = s.center ∧ t.center = s.center ∧
  t.radius = GalilScaffoldCounter.reset ∧ t.length = GalilScaffoldCounter.ofNat 1 ∧
  t.remaining = s.remaining ∧ t.cycle = s.cycle ∧ t.fpp = s.fpp ∧
  t.chain = .idle ∧ t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset ∧
  t.lower = GalilScaffoldCounter.reset ∧ t.dp = GalilScaffoldControl.reset entry s.dp

def replayPosVM (s : GalilVM) : Bool := GalilScaffoldCounter.positive s.replay

def replayExhaustedVM (s : GalilVM) : Bool := GalilScaffoldCounter.zero s.replay

def galilShared (onLetter leftFirst : GalilVM → Prop) (guard : GalilVM → Prop)
    (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) : Shared :=
  ⟨onLetter, leftFirst, initVM entry, replayStartVM entry, replayPosVM, replayExhaustedVM, guard, bs, bf, rs, centre, place⟩

theorem positive_ofNat (r : ℕ) : GalilScaffoldCounter.positive (GalilScaffoldCounter.ofNat r) = decide (0 < r) := by
  cases r <;> simp [GalilScaffoldCounter.positive, GalilScaffoldCounter.ofNat, List.replicate_succ]

/-- The `replayStart` tick from a state of the shape left by `fallback_chain`. -/
theorem replayStart_tick (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (c : Control) (hm : c.mode = .replayStart) (s : GalilVM) :
    ∃ (o : Bool) (t : GalilVM),
      Tick (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := GalilScaffoldCounter.positive s.radius}, t⟩ ∧
      t.replay = s.radius ∧ t.right = s.center ∧ t.left = s.center ∧ t.center = s.center ∧
      t.radius = GalilScaffoldCounter.reset ∧ t.length = GalilScaffoldCounter.ofNat 1 ∧
      t.remaining = s.remaining ∧ t.cycle = s.cycle ∧ t.fpp = s.fpp ∧ t.chain = .idle ∧
      (GalilScaffoldCounter.positive s.radius = true → o = c.output) ∧
      (GalilScaffoldCounter.positive s.radius = false →
        (onLetter t → (o = true ↔ leftFirst t)) ∧ (¬ onLetter t → o = c.output)) ∧
      t.search = GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset ∧
      t.lower = GalilScaffoldCounter.reset ∧ t.dp = GalilScaffoldControl.reset entry s.dp := by
  classical
  let t : GalilVM := ⟨s.center, s.center, s.center, .idle, s.cycle, s.remaining, GalilScaffoldCounter.reset,
    GalilScaffoldCounter.ofNat 1, s.radius, s.fpp, GalilScaffoldSearchFinish.begin GalilScaffoldCounter.reset GalilScaffoldCounter.reset,
    GalilScaffoldControl.reset entry s.dp, GalilScaffoldCounter.reset, s.periodOnly, s.walker⟩
  have hrs : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).replayStart s t :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hpos : (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first).replayPos t =
      GalilScaffoldCounter.positive s.radius := rfl
  cases hp : GalilScaffoldCounter.positive s.radius
  · -- not replaying: refresh the output
    refine ⟨if onLetter t then decide (leftFirst t) else c.output, t, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
    · have ht := Tick.replayStart (F := galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) (delay := delay)
        c s t (if onLetter t then decide (leftFirst t) else c.output) hm hrs
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
    · intro _
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · rw [if_pos hl]; exact decide_eq_true_iff
      · rw [if_neg hl]
  · -- replaying: output unchanged
    refine ⟨c.output, t, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩
    · have ht := Tick.replayStart (F := galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) (delay := delay)
        c s t c.output hm hrs (by rw [hpos, hp]; intro _; rfl)
        (by rw [hpos, hp]; intro h; exact absurd h.symm Bool.false_ne_true)
      rw [hpos, hp] at ht
      exact ht
    · intro _; rfl
    · intro h; exact absurd h.symm Bool.false_ne_true

/-- The fallback exit: from `copy` mode with the decoded `beginFallback`
state to `scan` mode, L = R = C on the selected centre (`r` places below the
old R), `replay = r`, `radius = 0`, `length = 1`, replaying iff `0 < r`. -/
theorem fallback_to_scan (onLetter leftFirst guard : GalilVM → Prop) (bs bf rs : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place) (entry : ℕ) (q : ℕ) (hq : 0 < q) (first : Fin 9)
    (h7 : first ≠ 7) (h8 : first ≠ 8) (delay : ℕ) (c : Control) (hm : c.mode = .copy) (s : GalilVM)
    (hi : ShiftIdle s) (old : GalilScaffoldControl.Machine 9) (p : GalilScaffoldPlace.Place)
    (length : GalilScaffoldCounter.Counter) (hc : GalilScaffoldCounter.Canonical length)
    (ℓ : ℕ) (hv : GalilScaffoldCounter.value length = ℓ)
    (hs : s.fpp = FppControl.beginFallback old p length)
    (hne : (GalilScaffoldPlace.stream p) ≠ [])
    (heven : ((GalilScaffoldPlace.stream p).take (ℓ+1)).length % 2 = 0) :
    let win := (GalilScaffoldPlace.stream p).take (ℓ+1)
    let r := chosenRadius win
    ∃ (n : ℕ) (o : Bool) (t : GalilVM),
      Steps (galilFrame (galilShared onLetter leftFirst guard bs bf rs centre place entry) q first) delay (n+1) ⟨c, s⟩
        ⟨{c with mode := .scan, clock := delay, output := o, replaying := decide (0 < r), odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)}, t⟩ ∧
      t.left = GalilScaffoldInputHead.left^[r] s.right ∧ t.right = GalilScaffoldInputHead.left^[r] s.right ∧
      t.center = GalilScaffoldInputHead.left^[r] s.right ∧
      t.replay = GalilScaffoldCounter.ofNat r ∧ t.radius = GalilScaffoldCounter.reset ∧
      t.length = GalilScaffoldCounter.ofNat 1 ∧ t.chain = .idle ∧
      t.fpp.program = GalilScaffoldControl.reset 320 t.fpp.program ∧ ShiftIdle t ∧
      (0 < r → o = c.output) := by
  intro win r
  obtain ⟨n, y, hg, hl, hc', hr, hlen, hrad, hprog, hi'⟩ :=
    fallback_chain (galilShared onLetter leftFirst guard bs bf rs centre place entry) q hq first h7 h8 delay c hm s hi old p length hc ℓ hv hs hne heven
  have hm' : ({c with mode := .replayStart, odd := oddAt false (win.length - (2*r+1)), pair := pairAt (2*r)} : Control).mode = .replayStart := rfl
  obtain ⟨o, t, ht, hrep, hR, hL, hC, hrad', hlen', hrem, hcyc, hfpp, hw, ho, _⟩ :=
    replayStart_tick onLetter leftFirst guard bs bf rs centre place entry q first delay _ hm' (rewindLens.set s y)
  have hrad'' : (rewindLens.set s y).radius = GalilScaffoldCounter.ofNat r := hrad
  have hcen : (rewindLens.set s y).center = GalilScaffoldInputHead.left^[r] s.right := hc'
  rw [hrad'', positive_ofNat] at ht ho
  refine ⟨n, o, t, steps_trans hg (.succ ht (.zero _)), ?_, ?_, ?_, ?_, hrad', hlen', hw, ?_, ?_, ?_⟩
  · rw [hL, hcen]
  · rw [hR, hcen]
  · rw [hC, hcen]
  · rw [hrep, hrad'']
  · rw [hfpp]; exact hprog
  · rw [shiftIdle_iff, hrem]
    show GalilScaffoldCounter.positive s.remaining = false
    exact (shiftIdle_iff s).1 hi
  · intro hr0
    exact ho (by simpa using hr0)

#print axioms fallback_to_scan

#print axioms replayStart_tick

end PalPeg.GalilScaffoldChainInputSupply
