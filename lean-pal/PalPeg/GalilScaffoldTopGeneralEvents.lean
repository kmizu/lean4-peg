import PalPeg.GalilScaffoldTopGeneralRun

/-!
# Events of a general scan run

A `GRun` yields one per-tick event list for both components: the heads
follow `ScanEvents` (skip on idle/count ticks, matched at comparisons) and
the chain follows `ChainTicks` on the same list. This is the general-chain
analogue of `joint_run_events`, and the interface to the lower layer's
supply lemmas, which take `ScanEvents` and `prepEvents`-shaped credit runs.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldChainVerifier

theorem grun_events {delay : ℕ} {s t : GScan} {as : List Bool} (hr : GRun delay s as t) :
    ∃ events : List Bool, events.length = as.length ∧
      ChainTicks events s.chain t.chain ∧
      (∀ (raw : List (Fin 2)) (c r : ℕ), ScanEvents raw c r s.left s.right events t.left t.right) := by
  induction hr with
  | nil s => exact ⟨[], rfl, .nil _, fun _ _ _ => .stop _ _ _⟩
  | cons s m t a as ht _ ih =>
    obtain ⟨events, hlen, hchain, hscan⟩ := ih
    cases ht with
    | idle _ ch' hn htc =>
      refine ⟨false :: events, by simp [hlen], .cons htc hchain, fun raw c r => ?_⟩
      exact .skip _ _ _ (hscan raw c r)
    | count _ ch' hc ha htc =>
      refine ⟨false :: events, by simp [hlen], .cons htc hchain, fun raw c r => ?_⟩
      exact .skip _ _ _ (hscan raw c r)
    | compare _ ch' hc hra hm htc =>
      refine ⟨true :: events, by simp [hlen], .cons htc hchain, fun raw c r => ?_⟩
      exact .matched _ _ _ hra hm (hscan raw c (r+1))

#print axioms grun_events

end PalPeg.GalilScaffoldChainInputSupply
