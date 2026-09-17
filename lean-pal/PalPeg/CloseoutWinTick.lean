import PalPeg.CloseoutWinOrigin
import PalPeg.CloseoutPackRun25

/-!
# `WindowInOrigin` one tick, with `Fair` replaced by the walker pin

`CloseoutPackRun25.windowInOrigin_tick` (:80) uses its `Fair` hypothesis at
exactly one branch — `scan_fallback`, through `windowInOrigin_of_fair` — and the
clause it reads there is `Fair.fallbackPlace`, whose content is
`y.vm.fpp.walker = y.vm.walker` (`GalilTickFair.Fair`).  That is
`CloseoutWinOrigin.WalkerPin` at the landing, a property of the landing state
alone.

So the tick lemma needs no `Fair`: the pin suffices, and the pin can be carried
as a field of a run-level bundle.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutWinTick

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldInputHead GalilScaffoldCounter
open PalPeg.CloseoutPackRun17
open PalPeg.GalilTickFair (Fair)
open PalPeg.GalilCentreLive (CPack cpack_tick)
open PalPeg.CloseoutPackRun25 PalPeg.CloseoutWinOrigin

section
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

theorem windowInOrigin_tick_pin {c c' : Control} {s t : GalilVM}
    (hpin : c.mode = Mode.scan → c'.mode = Mode.copy →
      PalPeg.CloseoutWinOrigin.WalkerPin t)
    (h : Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay
      ⟨c, s⟩ ⟨c', t⟩)
    (hx : c.mode = Mode.copy → WindowInOrigin s)
    (hw : c'.mode = Mode.copy → WalkerInOrigin t)
    (hm' : c'.mode = Mode.copy) : WindowInOrigin t := by
  cases h
  all_goals try (exfalso; revert hm'; simp [‹Control.mode _ = _›]; done)
  case scan_fallback =>
    exact PalPeg.CloseoutWinOrigin.windowInOrigin_of_pin
      (hpin ‹Control.mode c = Mode.scan› hm') (hw hm')
  case copy_one =>
    rename_i hm hp hi
    obtain ⟨a, ha, hv⟩ : ∃ a : Fin 3, GalilScaffoldPlace.read s.fpp.walker = some a ∧
        t.fpp = {s.fpp with program := FppControl.tape s.fpp 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec s.fpp.work, walker := GalilScaffoldPlace.left s.fpp.walker} := hi.1
    have ht : t = {s with fpp := t.fpp} := hi.2
    refine windowInOrigin_left ?_ ?_ (hx hm)
    · rw [hv]
    · rw [ht]


#print axioms windowInOrigin_tick_pin

end

end PalPeg.CloseoutWinTick
