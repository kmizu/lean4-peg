import PalPeg.GalilScaffoldTopScanMerge

/-!
# The scan → shift → scan cycle on the merged frame

`beginChainShift`: `chain.matched(); chain.beginShift(); length += 2;
remaining := chain.h`, then `stepShift` moves C by `h` and L by `2h` in unit
moves and returns to scan. On the unified VM `beginShiftVM h` fixes the
counters and the chain watch (`immediate`), and the shift phase is
`ChainShiftRun` from that state. This module composes the entry tick, the
shift run and the exit into one `Steps` from scan mode (clock 1) back to
scan mode.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController

/-- `beginChainShift` on the VM, for period length `h`: `chain.matched()`
(the immediate consume at lag zero), then `beginShift()` sets `periodOnly`
and resets the continuation countdown, `length += 2`, `remaining := h`.
The radius was already incremented by the comparison (`afterMismatch`). -/
def beginShiftVM (h : ℕ) (w : GalilScaffoldChainWatch.State) (s t : GalilVM) : Prop :=
  s.chain = .watch w ∧ t = {s with remaining := GalilScaffoldCounter.ofNat h, length := GalilScaffoldCounter.inc (GalilScaffoldCounter.inc s.length), chain := .watch (GalilScaffoldChainWatch.immediate w), cycle := GalilScaffoldCounter.reset, periodOnly := true}

theorem beginShiftVM_fpp (h : ℕ) (w : GalilScaffoldChainWatch.State) {s t : GalilVM} (hb : beginShiftVM h w s t) : t.fpp = s.fpp := by
  rw [hb.2]

/-- One scan→shift→scan cycle: the entry tick from scan mode with the clock
at one, a chain shift run of `n` units exhausting `remaining`, and the exit
back to scan mode with the output refreshed. -/
theorem scan_shift_cycle (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (h : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s s1 s2 : GalilVM) (hi : CopyIdle s)
    (hav : (galilFrame P q first).available s)
    (hcmp : (galilFrame P q first).compare s s1) (hmt : ¬ (galilFrame P q first).matched s1)
    (w : GalilScaffoldChainWatch.State)
    (hg : P.shiftGuard s1) (hb : P.beginShift s1 s2) (hs2 : beginShiftVM h w s1 s2)
    (hfpp : s1.fpp = s.fpp)
    {n : ℕ} {t : ShiftState} {v : GalilScaffoldChainWatch.State} {finish : GalilScaffoldCounter.Counter}
    (hrun : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩ (GalilScaffoldChainWatch.immediate w) s2.cycle n t v finish)
    (hz : GalilScaffoldCounter.positive t.remaining = false) :
    ∃ o : Bool, Steps (galilFrame P q first) delay (1 + (n+1)) ⟨c, s⟩
      ⟨{c with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨t, .watch v, finish⟩⟩ := by
  have ht1 : Tick (galilFrame P q first) delay ⟨c, s⟩ ⟨{c with clock := delay, mode := .shift}, s2⟩ :=
    .scan_shift c s s1 s2 hm (Or.inr hav) hc hcmp hmt hr hg hb
  have hm2 : ({c with clock := delay, mode := .shift} : Control).mode = .shift := rfl
  have hs2c : s2.chain = .watch (GalilScaffoldChainWatch.immediate w) := by rw [hs2.2]
  obtain ⟨o, hs⟩ := shift_phase_vm (fun v => P.onLetter (shiftLens.set s2 v))
    (fun v => P.leftFirst (shiftLens.set s2 v)) delay _ hm2 s2 _ hs2c hrun hz
  have hi2 : CopyIdle s2 := by
    rw [copyIdle_iff] at hi ⊢
    rw [hs2.2]
    show GalilScaffoldPlace.read s1.fpp.walker = none ∨ GalilScaffoldCounter.zero s1.fpp.work = true
    rw [hfpp]; exact hi
  obtain ⟨hg', _⟩ := steps_transfer_shift P q first delay (n+1) (s0 := s2) (v0 := shiftLens.get s2)
    (shiftLens.set_get s2).symm hm2 hi2 hs
  refine ⟨o, steps_trans (.succ ht1 (.zero _)) ?_⟩
  -- the exit record: `{c with clock := delay, mode := .shift}` then `mode := .scan, output := o`
  exact hg'

#print axioms scan_shift_cycle

end PalPeg.GalilScaffoldChainInputSupply
