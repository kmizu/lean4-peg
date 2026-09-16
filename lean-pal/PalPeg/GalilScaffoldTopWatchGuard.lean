import PalPeg.GalilScaffoldTopWatchSupply

/-!
# The shift guard from the watch period

Feeding the watch-period data of a general run (`watch_grun_supply`) into
the lower layer's `watch_shift_supply` and `shift_ready` gives, once the
lag is exhausted and the chain unbroken with enough distance, Scala's
`chain.canShift` condition `freshShiftGuard` on the controller's own watch
state — the watch run being deterministic, the lower layer's witness is the
controller's.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead

theorem watch_tick_unique {w m m' : GalilScaffoldChainWatch.State} {b : Bool}
    (h1 : GalilScaffoldChainWatch.Tick w b m) (h2 : GalilScaffoldChainWatch.Tick w b m') : m = m' := by
  cases h1 with
  | step hi ho =>
    cases h2 with
    | step hi' ho' =>
      have := internal_unique hi hi'
      subst this
      exact outer_unique ho ho'

theorem watch_run_unique {bs : List Bool} : ∀ {w m m' : GalilScaffoldChainWatch.State},
    GalilScaffoldChainWatch.Run w bs m → GalilScaffoldChainWatch.Run w bs m' → m = m' := by
  induction bs with
  | nil => intro w m m' h1 h2; cases h1; cases h2; rfl
  | cons b bs ih =>
    intro w m m' h1 h2
    cases h1 with
    | next ht hr =>
      cases h2 with
      | next ht' hr' =>
        have := watch_tick_unique ht ht'
        subst this
        exact ih hr hr'

theorem ready_distance (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3) :
    value (GalilScaffoldChainConsume.ready c ys b).distance = 0 := rfl

/-- The watch period of a general run yields the shift guard. -/
theorem watch_period_guard {raw : List (Fin 2)} (cen : PlaceHead) (c : Fin 3) (ys : List (Fin 3)) (b : Fin 3)
    (radius : Counter) (hrc : Canonical radius) (r0 : ℕ) (hr0 : value radius = r0)
    (sm dm : Bool) (bs cs : List Bool) (hbl : bs.length = ys.length + 1)
    {l0 rr0 : PlaceHead} (hi0 : ScanInvariant raw (position cen) r0 l0 rr0)
    {delay : ℕ} {g g' : GScan} {as : List Bool} (hr : GRun delay g as g')
    (hprep : ScanEvents raw (position cen) r0 l0 rr0 (sm :: (bs ++ dm :: cs)) g.left g.right)
    (hg : g.chain = .watch (watchStart cen c ys b (GalilScaffoldChainCredits.run
      (GalilScaffoldChainCredits.start radius) (GalilScaffoldChainCredits.prepEvents sm dm bs cs))))
    (t' : GalilScaffoldChainWatch.State) (hg' : g'.chain = .watch t')
    (hbroken : t'.machine.control.broken = false) :
    let initialRadius := r0 + (sm :: (bs ++ dm :: cs)).count true
    ∃ ws : List Bool, ws.length = as.length ∧
      (watchLag ws initialRadius = 0 → 4*(ys.length+1) ≤ initialRadius + ws.count true →
        GalilScaffoldChainCatch.freshShiftGuard t'.machine t'.lag t'.margin = true ∧
        value t'.machine.control.distance = initialRadius + ws.count true ∧
        ScanInvariant raw (position cen) (initialRadius + ws.count true) g'.left g'.right) := by
  intro initialRadius
  -- the credit state after preparation
  let final := GalilScaffoldChainCredits.run (GalilScaffoldChainCredits.start radius)
    (GalilScaffoldChainCredits.prepEvents sm dm bs cs)
  have hlcanon : Canonical final.lag :=
    credits_lag_canonical (GalilScaffoldChainCredits.prepEvents sm dm bs cs) (GalilScaffoldChainCredits.start radius) hrc
  have hmcanon : Canonical final.margin :=
    credits_margin_canonical (GalilScaffoldChainCredits.prepEvents sm dm bs cs) (GalilScaffoldChainCredits.start radius) hrc
  have hpv := (GalilScaffoldChainCredits.prep_value radius sm dm bs cs).2
  have hlagv : value final.lag = initialRadius := by
    show value final.lag = ((r0 + (sm :: (bs ++ dm :: cs)).count true : ℕ) : ℤ)
    rw [hpv, hr0]; push_cast; ring
  have hlagn : final.lag = ofNat initialRadius :=
    GalilScaffoldChainCatch.canonical_nat _ hlcanon _ hlagv
  obtain ⟨ws, hlen, hw, hv, hl, hscan⟩ := watch_grun_supply hr cen c ys b final initialRadius hlagn hg t' hg'
  refine ⟨ws, hlen, fun hexhausted h4 => ?_⟩
  have hwatch := hscan raw (position cen) initialRadius
  obtain ⟨t'', hw', hlag0, hz, hmach, hdist, hphase, hinv⟩ :=
    watch_shift_supply cen c ys b radius r0 hr0 sm dm bs cs hlcanon hi0 hprep hwatch hv hbroken hexhausted
  have heq : t'' = t' := watch_run_unique hw' hw
  subst heq
  refine ⟨?_, hdist, hinv⟩
  have hbal : GalilScaffoldChainWatch.balance (watchStart cen c ys b final) = 4*((ys.length+1 : ℕ) : ℤ) := by
    have := GalilScaffoldChainWatch.prepared_balance ⟨cen, GalilScaffoldChainConsume.ready c ys b⟩
      (ready_distance c ys b) radius sm dm bs cs
    rw [hbl] at this
    exact this
  have hd4 : (4*(ys.length+1) : ℤ) ≤ value t''.machine.control.distance := by
    rw [hdist]; exact_mod_cast h4
  exact GalilScaffoldChainWatch.shift_ready hw ⟨hlcanon, hmcanon⟩ (ys.length+1) hbal hz hd4 (hphase h4) hbroken

#print axioms watch_period_guard

end PalPeg.GalilScaffoldChainInputSupply
