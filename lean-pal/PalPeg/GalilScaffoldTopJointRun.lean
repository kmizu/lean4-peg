import PalPeg.GalilScaffoldTopScanRun

/-!
# Joint scan/chain runs as scan-frame runs

A `JointRun` on enabled events from a clock in `1..delay` is a run of the
scan frame on `ScanVM` with a watching chain: counting ticks while the
clock is above one, a matched comparison at one. Availability of R
(`canRight`) is required at every counting tick, as `stepScan` only counts
when R can advance.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead GalilScaffoldChainVerifier

theorem toJoint_ofJoint (t : JointState) : (ScanVM.ofJoint t).toJoint t.watch t.clock = t := rfl

/-- Lifting a joint run on `n` enabled events. -/
theorem joint_run_lift (onLetter leftFirst : ScanVM → Prop) (delay : ℕ) (hd : 1 ≤ delay) (n : ℕ) :
    ∀ (c : Control) (s : ScanVM) (w : GalilScaffoldChainWatch.State) (t : JointState),
      s.chain = .watch w → c.mode = .scan → c.replaying = false → 1 ≤ c.clock →
      JointRun delay (s.toJoint w c.clock) (List.replicate n true) t →
      (∀ m u, m < n → JointRun delay (s.toJoint w c.clock) (List.replicate m true) u → canRight u.right) →
      ∃ c' : Control, Steps (scanFrame onLetter leftFirst) delay n ⟨c, s⟩ ⟨c', ScanVM.ofJoint t⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ c'.clock = t.clock ∧ 1 ≤ c'.clock ∧
        c'.odd = c.odd ∧ c'.pair = c.pair := by
  induction n with
  | zero =>
    intro c s w t hs hm hr hc h _
    cases h
    refine ⟨c, ?_, hm, hr, rfl, hc, rfl, rfl⟩
    have : ScanVM.ofJoint (s.toJoint w c.clock) = s := by
      cases s; simp [ScanVM.ofJoint, ScanVM.toJoint] at hs ⊢; exact hs.symm
    rw [this]; exact .zero _
  | succ n ih =>
    intro c s w t hs hm hr hc h hav
    rw [List.replicate_succ] at h
    cases h with
    | cons _ m _ _ _ ht hrun =>
      have hcan : canRight s.right := hav 0 (s.toJoint w c.clock) (by omega) (.nil _)
      cases ht with
      | count _ w' hc1 hw =>
        have hc2 : 1 < c.clock := by
          have : (s.toJoint w c.clock).clock ≠ 1 := hc1
          simp only [ScanVM.toJoint] at this
          omega
        have ht1 := count_lift onLetter leftFirst delay c hm hc2 s w hs ⟨s.left, s.right, w', c.clock - 1⟩ hcan
          (.count _ w' hc1 hw) rfl
        have hm1 : ({c with clock := c.clock - 1} : Control).mode = .scan := hm
        have hr1 : ({c with clock := c.clock - 1} : Control).replaying = false := hr
        have hc3 : 1 ≤ ({c with clock := c.clock - 1} : Control).clock := by
          show 1 ≤ c.clock - 1; omega
        have hrun' : JointRun delay ((ScanVM.ofJoint ⟨s.left, s.right, w', c.clock - 1⟩).toJoint w'
            ({c with clock := c.clock - 1} : Control).clock) (List.replicate n true) t := by
          simpa [ScanVM.ofJoint, ScanVM.toJoint] using hrun
        have hav' : ∀ m u, m < n → JointRun delay ((ScanVM.ofJoint ⟨s.left, s.right, w', c.clock - 1⟩).toJoint w'
            ({c with clock := c.clock - 1} : Control).clock) (List.replicate m true) u → canRight u.right := by
          intro m u hmn hu
          refine hav (m+1) u (by omega) ?_
          rw [List.replicate_succ]
          exact .cons _ _ _ _ _ (.count _ w' hc1 hw) (by simpa [ScanVM.ofJoint, ScanVM.toJoint] using hu)
        obtain ⟨c', hs', hm', hr', hc', hc1', ho', hp'⟩ := ih _ _ w' t rfl hm1 hr1 hc3 hrun' hav'
        exact ⟨c', .succ ht1 hs', hm', hr', hc', hc1', ho', hp'⟩
      | compare _ w' hc1 hcr hmt hw =>
        have hc2 : c.clock = 1 := hc1
        obtain ⟨o, ht1⟩ := compare_lift onLetter leftFirst delay c hm hr hc2 s w hs
          ⟨left s.left, right s.right, w', delay⟩ (.compare _ w' hc1 hcr hmt hw) rfl
        have hm1 : ({c with clock := delay, output := o, replaying := false} : Control).mode = .scan := hm
        have hr1 : ({c with clock := delay, output := o, replaying := false} : Control).replaying = false := rfl
        have hc3 : 1 ≤ ({c with clock := delay, output := o, replaying := false} : Control).clock := hd
        have hrun' : JointRun delay ((ScanVM.ofJoint ⟨left s.left, right s.right, w', delay⟩).toJoint w'
            ({c with clock := delay, output := o, replaying := false} : Control).clock) (List.replicate n true) t := by
          simpa [ScanVM.ofJoint, ScanVM.toJoint] using hrun
        have hav' : ∀ m u, m < n → JointRun delay ((ScanVM.ofJoint ⟨left s.left, right s.right, w', delay⟩).toJoint w'
            ({c with clock := delay, output := o, replaying := false} : Control).clock) (List.replicate m true) u →
            canRight u.right := by
          intro m u hmn hu
          refine hav (m+1) u (by omega) ?_
          rw [List.replicate_succ]
          exact .cons _ _ _ _ _ (.compare _ w' hc1 hcr hmt hw) (by simpa [ScanVM.ofJoint, ScanVM.toJoint] using hu)
        obtain ⟨c', hs', hm', hr', hc', hc1', ho', hp'⟩ := ih _ _ w' t rfl hm1 hr1 hc3 hrun' hav'
        exact ⟨c', .succ ht1 hs', hm', hr', hc', hc1', ho', hp'⟩

#print axioms joint_run_lift

end PalPeg.GalilScaffoldChainInputSupply
