import PalPeg.GalilScaffoldTopFound

/-!
# Scan runs with an arbitrary chain

`JointTick` drives the scan with a watching chain. In the preparation
phases (copy/back) and when the chain is idle or broken the scan behaves
the same and the chain takes its own tick, so `GTick` generalises
`JointTick` to `ChainVM` with `ChainTick`: idle when R is not available,
count while the clock is above one, matched comparison at one. `GRun`s on
enabled/disabled events lift to scan-frame runs exactly as `joint_run_lift`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead GalilScaffoldChainVerifier

structure GScan where
  left : PlaceHead
  right : PlaceHead
  chain : ChainVM
  clock : ℕ

inductive GTick (delay : ℕ) : Bool → GScan → GScan → Prop
  | idle (s : GScan) (ch' : ChainVM) (hn : ¬ canRight s.right) (ht : ChainTick false s.chain ch') :
      GTick delay false s ⟨s.left, s.right, ch', s.clock⟩
  | count (s : GScan) (ch' : ChainVM) (hc : s.clock ≠ 1) (ha : canRight s.right)
      (ht : ChainTick false s.chain ch') :
      GTick delay true s ⟨s.left, s.right, ch', s.clock - 1⟩
  | compare (s : GScan) (ch' : ChainVM) (hc : s.clock = 1) (hr : canRight s.right)
      (hm : read (left s.left) = read (right s.right))
      (ht : ChainTick true s.chain ch') :
      GTick delay true s ⟨left s.left, right s.right, ch', delay⟩

inductive GRun (delay : ℕ) : GScan → List Bool → GScan → Prop
  | nil (s : GScan) : GRun delay s [] s
  | cons (s m t : GScan) (a : Bool) (as : List Bool)
      (ht : GTick delay a s m) (hr : GRun delay m as t) : GRun delay s (a :: as) t

def GScan.vm (s : GScan) : ScanVM := ⟨s.left, s.right, s.chain⟩

/-- Lifting a general run: the clock stays in `1..delay`, the controller in
scan mode with `replaying = false`, `odd`/`pair` untouched. -/
theorem grun_lift (onLetter leftFirst : ScanVM → Prop) (delay : ℕ) (hd : 1 ≤ delay) (as : List Bool) :
    ∀ (c : Control) (s t : GScan), c.mode = .scan → c.replaying = false →
      c.clock = s.clock → 1 ≤ c.clock → GRun delay s as t →
      ∃ c' : Control, Steps (scanFrame onLetter leftFirst) delay as.length ⟨c, s.vm⟩ ⟨c', t.vm⟩ ∧
        c'.mode = .scan ∧ c'.replaying = false ∧ c'.clock = t.clock ∧ 1 ≤ c'.clock ∧
        c'.odd = c.odd ∧ c'.pair = c.pair := by
  induction as with
  | nil =>
    intro c s t hm hr hc hc1 h
    cases h
    exact ⟨c, .zero _, hm, hr, hc, hc1, rfl, rfl⟩
  | cons a as ih =>
    intro c s t hm hr hc hc1 h
    cases h with
    | cons _ m _ _ _ ht hrun =>
      cases ht with
      | idle _ ch' hn htc =>
        have h1 : Tick (scanFrame onLetter leftFirst) delay ⟨c, s.vm⟩ ⟨c, ⟨s.left, s.right, ch'⟩⟩ :=
          .scan_wait c s.vm _ hm ⟨hr, hn⟩ ⟨rfl, rfl, htc⟩
        obtain ⟨c', hs, hm', hr', hc', hc1', ho', hp'⟩ := ih c ⟨s.left, s.right, ch', s.clock⟩ t hm hr hc hc1 hrun
        exact ⟨c', .succ h1 hs, hm', hr', hc', hc1', ho', hp'⟩
      | count _ ch' hcne ha htc =>
        have hc2 : 1 < c.clock := by omega
        have h1 : Tick (scanFrame onLetter leftFirst) delay ⟨c, s.vm⟩
            ⟨{c with clock := c.clock - 1}, ⟨s.left, s.right, ch'⟩⟩ :=
          .scan_count c s.vm _ hm (Or.inr ha) hc2 ⟨rfl, rfl, htc⟩
        obtain ⟨c', hs, hm', hr', hc', hc1', ho', hp'⟩ := ih {c with clock := c.clock - 1}
          ⟨s.left, s.right, ch', s.clock - 1⟩ t hm hr (by show c.clock - 1 = s.clock - 1; rw [hc])
          (by show 1 ≤ c.clock - 1; omega) hrun
        exact ⟨c', .succ h1 hs, hm', hr', hc', hc1', ho', hp'⟩
      | compare _ ch' hc1' hra hmt htc =>
        classical
        let s'' : ScanVM := ⟨left s.left, right s.right, ch'⟩
        let o : Bool := if onLetter s'' then decide (leftFirst s'') else c.output
        have ho : refresh (scanFrame onLetter leftFirst) s'' c.output o := by
          refine ⟨fun hl => ?_, fun hl => ?_⟩
          · have hl' : onLetter s'' := hl
            show (if onLetter s'' then decide (leftFirst s'') else c.output) = true ↔ leftFirst s''
            rw [if_pos hl']; exact decide_eq_true_iff
          · have hl' : ¬ onLetter s'' := hl
            show (if onLetter s'' then decide (leftFirst s'') else c.output) = c.output
            rw [if_neg hl']
        have hcc : c.clock = 1 := by rw [hc]; exact hc1'
        have h1 := Tick.scan_match (F := scanFrame onLetter leftFirst) (delay := delay) c s.vm s'' s'' o hm
          (Or.inr hra) hcc ⟨rfl, rfl, by
            show ChainTick (decide (read (left s.left) = read (right s.right))) s.chain s''.chain
            rw [decide_eq_true hmt]; exact htc⟩ hmt rfl ho
        rw [hr] at h1
        obtain ⟨c', hs, hm', hr', hc', hc1', ho', hp'⟩ := ih {c with clock := delay, output := o, replaying := false}
          ⟨left s.left, right s.right, ch', delay⟩ t hm rfl rfl hd hrun
        refine ⟨c', .succ ?_ hs, hm', hr', hc', hc1', ho', hp'⟩
        exact h1

#print axioms grun_lift

end PalPeg.GalilScaffoldChainInputSupply
