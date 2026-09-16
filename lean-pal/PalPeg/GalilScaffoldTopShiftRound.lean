import PalPeg.GalilScaffoldTopInvariant
import PalPeg.GalilScaffoldTopShiftCycle

/-!
# A shift round from the lower layer's chain shift run

`found_supplied_restart` ends with a `ChainShiftRun` of `h` units from
`⟨cen, left l2, ofNat h, radiusCounter, lengthCounter⟩` on the immediate
watch, `radiusCounter` being the radius already incremented by the
comparison; that is exactly the shift state `beginShiftVM h w` produces. With
`chain_shift_exhausts` the run empties `remaining`, so `scan_shift_cycle`
gives the whole scan → shift → scan round on the merged frame.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

theorem shift_round (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) (h : ℕ)
    (c : Control) (hm : c.mode = .scan) (hr : c.replaying = false) (hc : c.clock = 1)
    (s s1 s2 : GalilVM) (hi : CopyIdle s)
    (hav : (galilFrame P q first).available s)
    (hcmp : (galilFrame P q first).compare s s1) (hmt : ¬ (galilFrame P q first).matched s1)
    (w : GalilScaffoldChainWatch.State)
    (hg : P.shiftGuard s1) (hb : P.beginShift s1 s2) (hs2 : beginShiftVM h w s1 s2)
    (hfpp : s1.fpp = s.fpp)
    {endpoint : ShiftState} {watchEnd : GalilScaffoldChainWatch.State} {cycleEnd : Counter}
    (hrun : ChainShiftRun ⟨s1.center, s1.left, ofNat h, s1.radius, inc (inc s1.length)⟩
      (GalilScaffoldChainWatch.immediate w) reset h endpoint watchEnd cycleEnd) :
    ∃ o : Bool, Steps (galilFrame P q first) delay (1 + (h+1)) ⟨c, s⟩
      ⟨{c with mode := .scan, clock := delay, output := o}, shiftLens.set s2 ⟨endpoint, .watch watchEnd, cycleEnd⟩⟩ := by
  have hs2' := hs2.2
  have hrun' : ChainShiftRun ⟨s2.center, s2.left, s2.remaining, s2.radius, s2.length⟩
      (GalilScaffoldChainWatch.immediate w) s2.cycle h endpoint watchEnd cycleEnd := by
    rw [hs2']; exact hrun
  have hz : positive endpoint.remaining = false :=
    chain_shift_exhausts h (by rw [hs2']) hrun'
  exact scan_shift_cycle P q first delay h c hm hr hc s s1 s2 hi hav hcmp hmt w hg hb hs2 hfpp hrun' hz

#print axioms shift_round

end PalPeg.GalilScaffoldChainInputSupply
