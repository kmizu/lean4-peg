import PalPeg.CloseoutPackRun25

/-!
# Replaying implies the right head can still move

`CloseoutPackRun28.walkerInOrigin_of_run` — the producer of `WalkerInOrigin`,
and through it of `hme` (`H_marksEntry'`) — carries an obligation `hcan`:
at every reachable state with `replaying = true`, the right head satisfies
`canRight`.  That is not an extra assumption: it is the composition of two
facts already in the `FrontPack` invariant (`GalilFrontMono:93`).

* `FrontPack.replayPos` — `replaying = true → ∃ m, replay = ofNat (m+1)`;
* `FrontPack.frontier` — `Frontier s`, i.e. `position right + m ≤ 2 * arrived right`.

If the head could *not* move right it would sit on the final gap cell with an
empty right stack (`PopsIncoming`), and `consume_not_replaying_false`
(`GalilFrontier:342`) turns that plus a positive replay counter into `False`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutReplayCanRight

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilFrontMono
open PalPeg.GalilCentreLive
open PalPeg.CloseoutPackRun25 (FairSteps)
open GalilScaffoldTop
open GalilScaffoldController
open GalilScaffoldCounter

/-- **A positive replay counter keeps the right head movable.** -/
theorem canRight_of_frontier_replay {s : GalilVM} {m : ℕ}
    (hf : Frontier s) (hm : s.replay = ofNat (m + 1)) :
    GalilScaffoldChainVerifier.canRight s.right := by
  by_contra hc
  have h1 : s.right.gap = true := by
    cases hg : s.right.gap
    · exact absurd (Or.inl hg) hc
    · rfl
  have h2 : s.right.head.right = [] := by
    by_contra h0
    exact hc (Or.inr (Or.inl h0))
  exact consume_not_replaying_false hf ⟨h1, h2⟩ hm (Nat.succ_pos m)

/-- **`hcan` at a single `FrontPack` state.** -/
theorem canRight_of_frontPack {c : Control} {s : GalilVM}
    (hP : FrontPack c s) (hr : c.replaying = true) :
    GalilScaffoldChainVerifier.canRight s.right := by
  obtain ⟨m, hm⟩ := hP.replayPos hr
  exact canRight_of_frontier_replay hP.frontier hm

/-- **`hcan` straight out of the centre-live pack.**  `CPack.front` *is* a
`FrontPack` (`GalilCentreLive:152`), and `CloseoutPackRun25` already carries
`CPack` along the run — so the `hcan` obligation of
`CloseoutPackRun28.walkerInOrigin_of_run` is not an assumption at all. -/
theorem canRight_of_cpack {q : ℕ} {c : Control} {s : GalilVM}
    (hP : CPack q c s) (hr : c.replaying = true) :
    GalilScaffoldChainVerifier.canRight s.right :=
  canRight_of_frontPack hP.front hr

section Run
variable (onLetter leftFirst : GalilVM → Prop) (centre : GalilVM → Fin 3)
  (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9) (delay : ℕ)

/-- `CPack` travels along an ordinary run, exactly as `cpack_tick` does along
one tick.  The only input is `hfl`, already a hypothesis of
`CloseoutPackRun25.wpack_of_fair`. -/
theorem cpack_steps {n : ℕ} {x z : State GalilVM}
    (h : Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay n x z)
    (hfl : ∀ (m : ℕ) (y : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x y →
      y.ctl.mode = Mode.scan → 0 ≤ value y.vm.length)
    (hP : CPack q x.ctl x.vm) : CPack q z.ctl z.vm := by
  induction h with
  | zero x => exact hP
  | @succ n x w y ht _ ih =>
      exact ih (fun m u hu => hfl (m+1) u (.succ ht hu))
        (cpack_tick onLetter leftFirst centre place entry q first delay hP
          (hfl 0 x (.zero x)) ht)

/-- **The `hcan` obligation of `CloseoutPackRun28.walkerInOrigin_of_run` is a
theorem.**  It follows from the very pack (`CPack`) that
`CloseoutPackRun25.wpack_of_fair` already carries, with no new input beyond its
own `hfl`. -/
theorem hcan_of_cpack {x : State GalilVM}
    (hfl : ∀ (m : ℕ) (y : State GalilVM),
      Steps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay m x y →
      y.ctl.mode = Mode.scan → 0 ≤ value y.vm.length)
    (hP : CPack q x.ctl x.vm) (m : ℕ) (z : State GalilVM)
    (hz : FairSteps (galilFrameS (sharedC onLetter leftFirst centre place entry) q first)
      entry delay m x z) (hr : z.ctl.replaying = true) :
    GalilScaffoldChainVerifier.canRight z.vm.right :=
  canRight_of_cpack
    (cpack_steps onLetter leftFirst centre place entry q first delay hz.toSteps hfl hP) hr

end Run

#print axioms cpack_steps
#print axioms hcan_of_cpack
#print axioms canRight_of_frontier_replay
#print axioms canRight_of_frontPack
#print axioms canRight_of_cpack

end PalPeg.CloseoutReplayCanRight
