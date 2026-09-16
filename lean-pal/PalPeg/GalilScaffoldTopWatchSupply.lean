import PalPeg.GalilScaffoldTopWatchRun

/-!
# The watch period of a general run, in the lower layer's terms

A general scan run over the watch period, from the `watchStart` state to a
still-watching chain, yields the event list `ws`, the `Watch.Run`, the
verifier run with `watchConsumes ws initialRadius` consumes, the remaining
lag `watchLag ws initialRadius`, and the heads' `ScanEvents` — exactly the
hypotheses `watch_shift_supply` takes (`hrun`, `hexhausted`, `hwatch`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

theorem watchStart_lag (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) : (watchStart cen c ys b final).lag = final.lag := rfl

theorem watchStart_machine (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) :
    (watchStart cen c ys b final).machine = ⟨cen, GalilScaffoldChainConsume.ready c ys b⟩ := rfl

/-- The watch period from `watchStart` with unary lag `initialRadius`. -/
theorem watch_grun_supply {delay : ℕ} {g g' : GScan} {as : List Bool} (hr : GRun delay g as g')
    (cen : GalilScaffoldInputHead.PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (final : GalilScaffoldChainCredits.State) (initialRadius : ℕ)
    (hlag : final.lag = ofNat initialRadius)
    (hg : g.chain = .watch (watchStart cen c ys b final))
    (t' : GalilScaffoldChainWatch.State) (hg' : g'.chain = .watch t') :
    ∃ ws : List Bool, ws.length = as.length ∧
      GalilScaffoldChainWatch.Run (watchStart cen c ys b final) ws t' ∧
      GalilScaffoldChainVerifyRun.Run ⟨cen, GalilScaffoldChainConsume.ready c ys b⟩
        (watchConsumes ws initialRadius) t'.machine ∧
      t'.lag = ofNat (watchLag ws initialRadius) ∧
      (∀ (raw : List (Fin 2)) (c0 r : ℕ), ScanEvents raw c0 r g.left g.right ws g'.left g'.right) := by
  obtain ⟨ws, hlen, hchain, hscan⟩ := grun_events hr
  rw [hg, hg'] at hchain
  have hw := chainTicks_watch_run ws hchain
  obtain ⟨hv, hl⟩ := watch_run_verify ws initialRadius (by rw [watchStart_lag, hlag]) hw
  rw [watchStart_machine] at hv
  exact ⟨ws, hlen, hw, hv, hl, hscan⟩

#print axioms watch_grun_supply

end PalPeg.GalilScaffoldChainInputSupply
