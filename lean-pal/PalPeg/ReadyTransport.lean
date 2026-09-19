import PalPeg.CloseoutPreload39
import PalPeg.ShapedRun
import PalPeg.BranchSupply
import PalPeg.GalilInvPlus3

set_option autoImplicit false

/-!
# `ReadyTransport`: the search readiness datum along shaped runs

`CloseoutPreload39.ReadyFieldP3 n` (readiness now, plus readiness along every paced future) is
carried across every tick by `readyField3_tick`, except at the two re-entries of a fresh
search.  On a `ShapedRun.ShapedSteps` run there are no `restart` ticks and every `replayStart`
tick lands in a fresh radius-`0` restart, so the datum travels from the single leaf `hfresh`
(the datum at a fresh restart with the stage budget).
-/

namespace PalPeg.ReadyTransport

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilRunSkeleton PalPeg.CloseoutPreload39
  PalPeg.CloseoutReadyStage PalPeg.ShapedRun PalPeg.GalilInvPlus3 PalPeg.GalilFoundStage
  PalPeg.GalilOracleLocal
open GalilScaffoldCounter

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- The datum is monotone in its fuel: a larger fuel asks only about longer futures. -/
theorem readyField3_mono {n n' : ℕ} {x : State GalilVM} (hn : n ≤ n') (h : ReadyFieldP3 n x) :
    ReadyFieldP3 n' x :=
  ⟨h.ready, h.readyS, fun hm hi => readyPacedS_mono hn le_rfl (h.paced hm hi),
    fun hm => readyPacedS_mono hn le_rfl (h.paced0 hm),
    fun hm => readyPacedS_mono hn le_rfl (h.shifting hm)⟩

/-- **The datum along a shaped run, from `hfresh` alone.** -/
theorem readyField3_alongShaped {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    {k : ℕ} {x y : State GalilVM} (h : ShapedSteps centre place entry q first w k x y)
    (hni : x.ctl.mode ≠ .init) (hx : ∃ n, ReadyFieldP3 n x) : ∃ n, ReadyFieldP3 n y := by
  classical
  induction h with
  | zero _ => exact hx
  | @succ _ x y z ht hnr hrs _ ih =>
    obtain ⟨n, hn⟩ := hx
    have key : ∃ n', n ≤ n' ∧
        (x.ctl.mode = .scan → restartVM entry x.vm y.vm → ReadyFieldP3 n' y) ∧
        (x.ctl.mode = .replayStart → ReadyFieldP3 n' y) := by
      by_cases h2 : x.ctl.mode = .replayStart
      · obtain ⟨hR, hm, hclk⟩ := hrs h2
        obtain ⟨m, hm'⟩ := hfresh y.ctl y.vm 0 reset hR (stageEntry_zero _) hm hclk
        exact ⟨max n m, le_max_left _ _, fun h3 _ => absurd (h2.symm.trans h3) (by decide),
          fun _ => readyField3_mono (le_max_right _ _) hm'⟩
      · exact ⟨n, le_rfl, fun h3 h4 => absurd h4 (hnr h3), fun h3 => absurd h3 h2⟩
    obtain ⟨n', hnn', hentry, hentry'⟩ := key
    exact ih (PalPeg.BranchSupply.tick_target_mode_ne_init ht)
      ⟨n', readyField3_tick centre place entry q first hni hn hnn' ht hentry hentry'⟩

#print axioms readyField3_alongShaped

/-- **The datum at every state of a shaped run out of an `InvLPS` origin**, from `hfresh`
alone: the origin's own datum is `hfresh` at the fresh restart its `ReplayStage` records,
transported along the recorded `WatchSegE` segment (a shaped run). -/
theorem readyField3_of_invLPS_shaped {w : List (Fin 2)}
    (hfresh : ∀ (c : Control) (r : GalilVM) (Rad : ℕ) (last : Counter),
      Restarted w r Rad last → StageEntry Rad last → c.mode = .scan → c.clock = 2048 →
      ∃ n, ReadyFieldP3 n ⟨c, r⟩)
    {c₀ : Control} {r₀ : GalilVM} (hI₀ : InvLPS (PofC centre place entry w) q first w c₀ r₀)
    {j : ℕ} {x : State GalilVM} (hs : ShapedSteps centre place entry q first w j ⟨c₀, r₀⟩ x) :
    ∃ n, ReadyFieldP3 n x := by
  obtain ⟨r, Rad, last, es, c, hR, hSE, hclk, hseg⟩ := hI₀.2
  have hm₀ : c₀.mode = .scan := (invS_mode hI₀.1.1.1.1.1).1
  have hm : c.mode = .scan := watchSegE_first_mode q first hseg hm₀
  obtain ⟨k, hsh⟩ := watchSegE_shaped centre place entry q first hseg
  have horig : ∃ n, ReadyFieldP3 n ⟨c₀, r₀⟩ :=
    readyField3_alongShaped centre place entry q first hfresh hsh (by rw [hm]; decide)
      (hfresh c r Rad last hR hSE hm hclk)
  exact readyField3_alongShaped centre place entry q first hfresh hs (by rw [hm₀]; decide) horig

#print axioms readyField3_of_invLPS_shaped

end

end PalPeg.ReadyTransport
