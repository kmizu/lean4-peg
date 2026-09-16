import PalPeg.GalilScaffoldTopChainVM
import PalPeg.GalilScaffoldTopSearch

/-!
# The chain component: walks of the lower layer as chain steps

The lower-layer `GalilScaffoldChainPeriod.Copy`/`Back` walks are the same
relations as the copy/back steps of `ChainVM`, so they lift to `ChainSteps`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

/-- The lower-layer `Copy` walk of `n` answer cells is `n` copy steps. -/
theorem copy_steps (n : ℕ) : ∀ {t : GalilScaffoldTape.Tape} {c : Counter} {p : GalilScaffoldPlace.Place}
    {v : GalilScaffoldChainPeriod.Tape} {u d q z} (lag margin : Counter) (ver : GalilScaffoldInputHead.PlaceHead),
    GalilScaffoldChainPeriod.Copy t c p v n u d q z →
    ChainSteps n (.copy t c p v lag margin ver) (.copy u d q z lag (GalilScaffoldChainCredits.decFour^[n] margin) ver) := by
  induction n with
  | zero =>
    intro t c p v u d q z lag margin ver h
    cases h
    exact .zero _
  | succ n ih =>
    intro t c p v u d q z lag margin ver h
    cases h with
    | next a one legal present rest =>
      have := ih lag (GalilScaffoldChainCredits.decFour margin) ver rest
      rw [Function.iterate_succ_apply]
      exact .succ (.copyBit t c p v lag margin ver a one legal present) this

/-- The lower-layer `Back` walk of `n` ticks is `n` back steps ending in watch. -/
theorem back_steps (n : ℕ) : ∀ {v u : GalilScaffoldChainPeriod.Tape} (h lag margin : Counter)
    (ver : GalilScaffoldInputHead.PlaceHead), GalilScaffoldChainPeriod.Back v n u →
    ChainSteps n (.back v h lag margin ver) (.watch ⟨⟨ver, ⟨u, reset, reset, reset, 0, true, false⟩⟩, lag, margin⟩) := by
  induction n with
  | zero => intro v u h lag margin ver hb; cases hb
  | succ n ih =>
    intro v u h lag margin ver hb
    cases hb with
    | done _ hf => exact .succ (.backDone v h lag margin ver hf) (.zero _)
    | next _ hf hl hr => exact .succ (.backStep v h lag margin ver hf) (ih h lag margin ver hr)

#print axioms copy_steps
#print axioms back_steps

end PalPeg.GalilScaffoldChainInputSupply
