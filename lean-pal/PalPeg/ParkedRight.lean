import PalPeg.GalilFrontier
import PalPeg.LocalReplayParked
import PalPeg.BranchSupply
import PalPeg.ReplayStartGhost


/-!
# The right head of a replay is parked

While the scaffold replays, the local layer keeps its right view parked and reads the abstract
right head as `left^[replay]` of it (`LocalReplayParked.absR`).  To give the abstraction a section
one has to recover the parked head from the abstract state.  `Frontier`
(`position right + replay ≤ 2 · arrived`) is not enough: the abstract `right` pulls a letter from
`incoming` when the right stack is empty, and `left` does not put it back, so `left (right p) = p`
fails in general.  What holds is a fact of the history: the right head stands `replay` places to
the left of some head (`ParkedRight`), at every state of a pre-loaded trace
(`parkedRight_trace`).

`RightReplayMove` classifies what one tick does to the right head and the replay counter; the
parked form is kept in each of the four cases (`parkedRight_tick`).
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController GalilScaffoldInputHead

/-- The right head stands `replay` places to the left of a parked head. -/
def ParkedRight (s : GalilVM) : Prop :=
  ∃ r parked, s.replay = GalilScaffoldCounter.ofNat r ∧
    s.right = GalilScaffoldInputHead.left^[r] parked ∧ r ≤ position parked

theorem parkedRight_of_reset {s : GalilVM} (h : s.replay = GalilScaffoldCounter.reset) :
    ParkedRight s := ⟨0, s.right, h, rfl, Nat.zero_le _⟩

/-- The parked form is kept by every tick.  In `replayStart` the centre is `radius`
places to the left of the right head (`hcentre`), and a replaying state has a positive replay
counter (`hreplayPos`). -/
theorem parkedRight_tick {c : Control} {s t : GalilVM} (hmove : RightReplayMove c s t)
    (hparked : ParkedRight s)
    (hreplayPos : c.replaying = true → ∃ m, s.replay = GalilScaffoldCounter.ofNat (m + 1))
    (hcentre : c.mode = Mode.replayStart → ∃ r, s.radius = GalilScaffoldCounter.ofNat r ∧
      s.center = GalilScaffoldInputHead.left^[r] s.right ∧ r ≤ position s.right) :
    ParkedRight t := by
  cases hmove with
  | rested hreplay => exact parkedRight_of_reset hreplay
  | kept hright hreplay =>
      obtain ⟨r, parked, hr, hp, hle⟩ := hparked
      exact ⟨r, parked, hreplay.trans hr, hright.trans hp, hle⟩
  | replayed hreplaying hright hreplay =>
      obtain ⟨r, parked, hr, hp, hle⟩ := hparked
      obtain ⟨m, hm⟩ := hreplayPos hreplaying
      have hrm : r = m + 1 := ofNat_inj (hr.symm.trans hm)
      subst hrm
      refine ⟨m, parked, ?_, ?_, by omega⟩
      · rw [hreplay, hm]; rfl
      · rw [hright, hp]
        exact PalPeg.LocalReplayParked.right_left_iterate hle
  | started hmode hright hreplay =>
      obtain ⟨r, hrad, hcen, hle⟩ := hcentre hmode
      exact ⟨r, s.right, hreplay.trans hrad, hright.trans hcen, hle⟩

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.ParkedRight
open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
open PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilFinalAssembly

/-- Along a pre-loaded trace the right head is always in parked form. -/
theorem parkedRight_trace (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    {w : List (Fin 2)} (hw : 0 < w.length) {st : ℕ → State GalilVM} {Tc : ℕ → ℕ}
    (hP : PreTrace centre place entry q first w st Tc) :
    ∀ i, i ≤ Tc w.length → ParkedRight (st i).vm := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hP.start]
    exact parkedRight_of_reset rfl
  | succ i ih =>
    intro hi
    have hlt : i < Tc w.length := by omega
    have htick := hP.trace.tick i hlt
    have hpack : 1 ≤ i → PalPeg.GalilFrontMono.FrontPack (st i).ctl (st i).vm := fun hipos =>
      PalPeg.BranchSupply.frontPack_alongTrace centre place entry q first hw hP i hipos (by omega)
    have hrest : ReplayRest (st i).ctl (st i).vm := by
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · intro _; rw [hP.start]; rfl
      · exact (hpack hipos).rest
    have hmove := rightReplayMove_of_tick _ _ centre place entry q first 2048 hrest htick
    refine parkedRight_tick hmove (ih (by omega)) ?_ ?_
    · intro hreplaying
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [hP.start] at hreplaying
        exact absurd (show false = true from hreplaying) (by decide)
      · exact (hpack hipos).replayPos hreplaying
    · intro hmode
      have hipos : 1 ≤ i := by
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rw [hP.start] at hmode
          exact absurd (show Mode.init = Mode.replayStart from hmode) (by decide)
        · exact hipos
      obtain ⟨r, hradius, hcentre⟩ :=
        PalPeg.ReplayStartGhost.rewindCentre_trace centre place entry q first hP i (by omega)
          (Or.inr hmode)
      obtain ⟨r', hradius', hposition, -⟩ := (hpack hipos).rewind (Or.inr hmode)
      have hrr : r = r' := ofNat_inj (hradius.symm.trans hradius')
      exact ⟨r, hradius, hcentre, by omega⟩

#print axioms parkedRight_trace

end PalPeg.ParkedRight

