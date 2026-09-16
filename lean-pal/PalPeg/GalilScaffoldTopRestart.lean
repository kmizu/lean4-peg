import PalPeg.GalilScaffoldTopReplay

/-!
# The Broken-chain restart

In the transition prelude, `chain.mode == Broken` with `margin ≥ 0`,
`last > 0`, `lag == 0` restarts the search from the confirmed lower bound
(`search.start(chain.last)`), idles the chain and resets the clock. On the
unified VM this is `restartVM`; the controller tick is `Tick.restart`. The
conditions are exactly those `joint_break_restart` derives after a break.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldCounter

/-- `search.start(chain.last)` after a break: lower bound `last`, search
scheduling state `begin last radius`, DP program reset at `entry`, chain idle. -/
def restartVM (entry : ℕ) (s t : GalilVM) : Prop :=
  ∃ w : GalilScaffoldChainWatch.State, s.chain = .broken w ∧
    negative w.margin = false ∧ positive w.machine.control.last = true ∧ zero w.lag = true ∧
    t = {s with chain := .idle, lower := w.machine.control.last, search := GalilScaffoldSearchFinish.begin w.machine.control.last s.radius, dp := GalilScaffoldControl.reset entry s.dp}

theorem restart_tick (onLetter leftFirst guard : GalilVM → Prop) (bs bf : GalilVM → GalilVM → Prop) (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
    (entry : ℕ) (q : ℕ) (first : Fin 9) (delay : ℕ) (c : Control) (hm : c.mode = .scan) (s : GalilVM)
    (w : GalilScaffoldChainWatch.State) (hs : s.chain = .broken w)
    (hmargin : negative w.margin = false) (hlast : positive w.machine.control.last = true)
    (hlag : zero w.lag = true) :
    Tick (galilFrame (galilShared onLetter leftFirst guard bs bf (restartVM entry) centre place entry) q first) delay ⟨c, s⟩
      ⟨{c with clock := delay}, {s with chain := .idle, lower := w.machine.control.last, search := GalilScaffoldSearchFinish.begin w.machine.control.last s.radius, dp := GalilScaffoldControl.reset entry s.dp}⟩ :=
  .restart c s _ hm ⟨w, hs, hmargin, hlast, hlag, rfl⟩

#print axioms restart_tick

end PalPeg.GalilScaffoldChainInputSupply
