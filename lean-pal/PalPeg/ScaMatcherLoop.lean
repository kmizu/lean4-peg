import PalPeg.ScaHeadGen

/-!
# The matcher's main loop against the list-level verifier

At the loop head (site 13, `available B`) the matcher's heads encode a verifier state
`((pos, q), c)` of `GSVerifier.vStep` on the logical word `x ++ T` (`LoopRel`): `A = s + q`,
`B = |x| + pos + q`, `P = |x| + pos − s`, `Walk = c`, `U = P + c`, with `Cut = s`, `End = |x|`,
`First = s + p₁`, `KFirst = s + k·p₁`, `Reach = s + r`. This file proves the segments of the loop:
the shift after a mismatch or a report (`shift_period`, `shift_reset`), and the comparison
segments.
-/
set_option autoImplicit false
namespace PalPeg.ScaMatcherLoop
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen

/-- The matcher controller's frame. -/
abbrev mc (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) (site : ℕ) : Frame :=
  .matcherController k pe ok ph site

/-- The loop head: waiting for `B`. -/
def loopHead (k : ℕ) (pe : Bool) (ok : Bool) (ph : Option ℕ) : Ctl :=
  .pending [mc k (some pe) (some ok) ph 13] (.available "B")

/-- The heads at the loop head for the verifier state `((pos, q), c)`. -/
def LoopRel (lx s p₁ r k : ℕ) (pe : Bool) (pos q c : ℕ) (π : String → ℤ) : Prop :=
  π "Origin" = 0 ∧ π "Cut" = s ∧ π "End" = lx ∧
  (pe = true → π "First" = s + p₁ ∧ π "KFirst" = s + k * p₁ ∧ π "Reach" = s + r) ∧
  π "P" = lx + pos - s ∧ π "A" = s + q ∧ π "B" = lx + pos + q ∧ π "Walk" = c ∧
  π "U" = lx + pos - s + c

/-! ## Control transitions of the shift decision -/

theorem mc_22_reset (k : ℕ) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some true) ok ph 22] (.less "A" "KFirst")).resume matchTests true =
      .pending [mc k (some true) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut") := rfl

theorem mc_22_next (k : ℕ) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some true) ok ph 22] (.less "A" "KFirst")).resume matchTests false =
      .pending [mc k (some true) ok ph 23] (.less "Reach" "A") := rfl

theorem mc_23_reset (k : ℕ) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some true) ok ph 23] (.less "Reach" "A")).resume matchTests true =
      .pending [mc k (some true) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut") := rfl

theorem mc_23_period (k : ℕ) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some true) ok ph 23] (.less "Reach" "A")).resume matchTests false =
      .pending [mc k (some true) ok ph 24, .periodShift k true 1] (.copy "Walk" "Cut") := rfl

theorem mc_after_child (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) (site : ℕ)
    (hs : site = 24 ∨ site = 25) :
    liftCtl (mc k pe ok ph site) (.returned none) =
      .pending [mc k pe ok ph 11] (.copy "Walk" "Origin") := by
  rcases hs with rfl | rfl <;> rfl

theorem mc_11 (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k pe ok ph 11] (.copy "Walk" "Origin")).resume matchTests false =
      .pending [mc k pe ok ph 12] (.copy "U" "P") := rfl

theorem mc_12 (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k pe ok ph 12] (.copy "U" "P")).resume matchTests false =
      .pending [mc k pe (some true) ph 13] (.available "B") := rfl

/-! ## The two shifts, as counted runs -/

/-- Heads after the loop's re-entry (`Walk := Origin`, `U := P`). -/
def reenter (π : String → ℤ) : String → ℤ :=
  Function.update (Function.update π "Walk" (π "Origin")) "U" (π "P")

theorem reenter_run (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k pe ok ph 11] (.copy "Walk" "Origin")) :
    iterStep 2 v = some { v with
      ctl := .pending [mc k pe (some true) ph 13] (.available "B")
      pos := reenter v.pos } := by
  have e1 := step_copy hv
  rw [mc_11] at e1
  have e2 := step_copy (v := { v with
      pos := Function.update v.pos "Walk" (v.pos "Origin")
      ctl := .pending [mc k pe ok ph 12] (.copy "U" "P") }) rfl
  rw [mc_12] at e2
  simp only [iterStep, e1, e2, Option.bind_some]
  congr 2

/-- **The reset shift**, from the call of `ResetShift` to the next loop head. -/
theorem shift_reset (k : ℕ) (hk : 1 ≤ k) (pe ok : Option Bool) (ph : Option ℕ) (v : HVM) (q : ℕ)
    (hv : v.ctl = .pending [mc k pe ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut"))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" + 1 ≤ v.len) (hP0 : 0 ≤ v.pos "P")
    (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, iterStep n v = some { v with
      ctl := .pending [mc k pe (some true) ph 13] (.available "B")
      pos := reenter (rsPos v.pos q (rsShifts k q : ℕ)) } := by
  set f := mc k pe ok ph 25
  let vc : HVM := { v with ctl := .pending [.resetShift k true 0 none 1] (.equal "A" "Cut") }
  have hvc : vc.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none) := rs_start k
  obtain ⟨n, -, hrun⟩ := resetShift_run k hk vc q hvc hq hC hAL hBq hBL hP0 hPL
  have hl := iterStep_lift f n vc _ (by simp [vc, NonEmptyCtl]) hrun
  have hv' : liftVM f vc = v := by
    simp only [liftVM, vc, liftCtl]; rw [← hv]
  rw [hv'] at hl
  have hback : liftVM f { vc with
      ctl := .returned none
      pos := rsPos vc.pos q (rsShifts k q : ℕ) } =
      { v with
        ctl := .pending [mc k pe ok ph 11] (.copy "Walk" "Origin")
        pos := rsPos v.pos q (rsShifts k q : ℕ) } := by
    simp only [liftVM, vc]
    rw [mc_after_child k pe ok ph 25 (Or.inr rfl)]
  rw [hback] at hl
  refine ⟨n + 2, ?_⟩
  rw [iterStep_add, hl, Option.bind_some, reenter_run k pe ok ph _ rfl]

/-- **The period shift**, from the call of `PeriodShift` to the next loop head. -/
theorem shift_period (k : ℕ) (ok : Option Bool) (ph : Option ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = .pending [mc k (some true) ok ph 24, .periodShift k true 1] (.copy "Walk" "Cut"))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len) :
    iterStep (2 * t + 4) v = some { v with
      ctl := .pending [mc k (some true) (some true) ph 13] (.available "B")
      pos := reenter (psPos v.pos t) } := by
  set f := mc k (some true) ok ph 24
  let vc : HVM := { v with ctl := .pending [.periodShift k true 1] (.copy "Walk" "Cut") }
  have hvc : vc.ctl = Ctl.ofOutcome (next [.periodShift k true 0] none) := ps_start k
  have hrun := periodShift_run k vc t hvc ht h0 hF hA hA' hP hP'
  have hl := iterStep_lift f _ vc _ (by simp [vc, NonEmptyCtl]) hrun
  have hv' : liftVM f vc = v := by
    simp only [liftVM, vc, liftCtl]; rw [← hv]
  rw [hv'] at hl
  have hback : liftVM f { vc with ctl := .returned none, pos := psPos vc.pos t } =
      { v with
        ctl := .pending [mc k (some true) ok ph 11] (.copy "Walk" "Origin")
        pos := psPos v.pos t } := by
    simp only [liftVM, vc]
    rw [mc_after_child k (some true) ok ph 24 (Or.inl rfl)]
  rw [hback] at hl
  rw [show 2 * t + 4 = (2 * t + 2) + 2 by ring, iterStep_add, hl, Option.bind_some,
    reenter_run k (some true) ok ph _ rfl]

/-! ## Control transitions of the comparison part -/

section Trans
variable (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ)

theorem mc_13_wait :
    (Ctl.pending [mc k pe ok ph 13] (.available "B")).resume matchTests false =
      .pending [mc k pe ok ph 13] (.available "B") := rfl

theorem mc_13_go :
    (Ctl.pending [mc k pe ok ph 13] (.available "B")).resume matchTests true =
      .pending [mc k pe ok ph 14] (.symbols "A" "B") := rfl

theorem mc_14_hit :
    (Ctl.pending [mc k pe ok ph 14] (.symbols "A" "B")).resume matchTests true =
      .pending [mc k pe ok ph 15] (mv [("A", 1), ("B", 1)]) := rfl

theorem mc_14_miss_period :
    (Ctl.pending [mc k (some true) ok ph 14] (.symbols "A" "B")).resume matchTests false =
      .pending [mc k (some true) ok ph 22] (.less "A" "KFirst") := rfl

theorem mc_14_miss_reset :
    (Ctl.pending [mc k (some false) ok ph 14] (.symbols "A" "B")).resume matchTests false =
      .pending [mc k (some false) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut") := rfl

theorem mc_15_ok :
    (Ctl.pending [mc k pe (some true) ph 15] (mv [("A", 1), ("B", 1)])).resume matchTests false =
      .pending [mc k pe (some true) (some 0) 16] (.less "Walk" "Cut") := rfl

theorem mc_15_dead :
    (Ctl.pending [mc k pe (some false) ph 15] (mv [("A", 1), ("B", 1)])).resume matchTests false =
      .pending [mc k pe (some false) (some 0) 19] (.equal "A" "End") := rfl

theorem mc_16_go :
    (Ctl.pending [mc k pe ok ph 16] (.less "Walk" "Cut")).resume matchTests true =
      .pending [mc k pe ok ph 17] (.symbols "Walk" "U") := rfl

theorem mc_16_done :
    (Ctl.pending [mc k pe ok ph 16] (.less "Walk" "Cut")).resume matchTests false =
      .pending [mc k pe ok ph 19] (.equal "A" "End") := rfl

theorem mc_17_hit :
    (Ctl.pending [mc k pe ok ph 17] (.symbols "Walk" "U")).resume matchTests true =
      .pending [mc k pe ok ph 18] (mv [("Walk", 1), ("U", 1)]) := rfl

theorem mc_17_miss :
    (Ctl.pending [mc k pe ok ph 17] (.symbols "Walk" "U")).resume matchTests false =
      .pending [mc k pe (some false) ph 19] (.equal "A" "End") := rfl

theorem mc_18_again :
    (Ctl.pending [mc k pe (some true) (some 0) 18] (mv [("Walk", 1), ("U", 1)])).resume matchTests
      false = .pending [mc k pe (some true) (some 1) 16] (.less "Walk" "Cut") := rfl

theorem mc_18_done :
    (Ctl.pending [mc k pe ok (some 1) 18] (mv [("Walk", 1), ("U", 1)])).resume matchTests false =
      .pending [mc k pe ok (some 1) 19] (.equal "A" "End") := rfl

theorem mc_19_more :
    (Ctl.pending [mc k pe ok ph 19] (.equal "A" "End")).resume matchTests false =
      .pending [mc k pe ok ph 13] (.available "B") := rfl

theorem mc_19_report :
    (Ctl.pending [mc k pe (some true) ph 19] (.equal "A" "End")).resume matchTests true =
      .pending [mc k pe (some true) ph 20] (.assertEqual "Walk" "Cut") := rfl

theorem mc_19_dead_period :
    (Ctl.pending [mc k (some true) (some false) ph 19] (.equal "A" "End")).resume matchTests true =
      .pending [mc k (some true) (some false) ph 22] (.less "A" "KFirst") := rfl

theorem mc_19_dead_reset :
    (Ctl.pending [mc k (some false) (some false) ph 19] (.equal "A" "End")).resume matchTests true =
      .pending [mc k (some false) (some false) ph 25, .resetShift k true 0 none 1]
        (.equal "A" "Cut") := rfl

theorem mc_20 :
    (Ctl.pending [mc k pe ok ph 20] (.assertEqual "Walk" "Cut")).resume matchTests false =
      .pending [mc k pe ok ph 21] (.«match» "B") := rfl

theorem mc_21_period :
    (Ctl.pending [mc k (some true) ok ph 21] (.«match» "B")).resume matchTests false =
      .pending [mc k (some true) ok ph 22] (.less "A" "KFirst") := rfl

theorem mc_21_reset :
    (Ctl.pending [mc k (some false) ok ph 21] (.«match» "B")).resume matchTests false =
      .pending [mc k (some false) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut") := rfl

end Trans

end PalPeg.ScaMatcherLoop
