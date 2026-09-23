import PalPeg.ScaHeadGen
import PalPeg.GSVerifier
import PalPeg.GSReportDeadline

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
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" ≤ v.len)
    (hBF : v.pos "B" - q + (rsShifts k q : ℕ) ≤ v.len) (hP0 : 0 ≤ v.pos "P")
    (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, iterStep n v = some { v with
      ctl := .pending [mc k pe (some true) ph 13] (.available "B")
      pos := reenter (rsPos v.pos q (rsShifts k q : ℕ)) } := by
  set f := mc k pe ok ph 25
  let vc : HVM := { v with ctl := .pending [.resetShift k true 0 none 1] (.equal "A" "Cut") }
  have hvc : vc.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none) := rs_start k
  obtain ⟨n, -, hrun⟩ := resetShift_run k hk vc q hvc hq hC hAL hBq hBL hBF hP0 hPL
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

/-! ## One round of the prefix check -/

section Round
variable (k : ℕ) (pe : Option Bool)

theorem round_skip (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k pe (some true) ph 16] (.less "Walk" "Cut"))
    (he : v.pos "Cut" ≤ v.pos "Walk") :
    iterStep 1 v = some { v with ctl := .pending [mc k pe (some true) ph 19] (.equal "A" "End") } := by
  have e1 := step_less hv
  rw [show decide (v.pos "Walk" < v.pos "Cut") = false by simp; omega, mc_16_done] at e1
  simp [iterStep, e1]

/-- The move of one prefix comparison. -/
def walkMove (π : String → ℤ) : String → ℤ :=
  Function.update (Function.update π "Walk" (π "Walk" + 1)) "U" (π "U" + 1)

theorem walk_moveSeq (π : String → ℤ) (L : ℤ) (hW : 0 ≤ π "Walk" + 1 ∧ π "Walk" + 1 ≤ L)
    (hU : 0 ≤ π "U" + 1 ∧ π "U" + 1 ≤ L) :
    moveSeq blind L [⟨"Walk", 1⟩, ⟨"U", 1⟩] π = some (walkMove π) := by
  simp only [moveSeq, blind]
  simp [Function.update, walkMove]
  exact ⟨hW, hU⟩

theorem round_hit (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k pe (some true) ph 16] (.less "Walk" "Cut"))
    (hlt : v.pos "Walk" < v.pos "Cut") (hW : v.inRange "Walk") (hU : v.inRange "U")
    (heq : v.word[(v.pos "Walk").toNat]? = v.word[(v.pos "U").toNat]?)
    (hW1 : v.pos "Walk" + 1 ≤ v.len) (hU1 : v.pos "U" + 1 ≤ v.len) :
    iterStep 3 v = some { v with
      ctl := (Ctl.pending [mc k pe (some true) ph 18] (mv [("Walk", 1), ("U", 1)])).resume
        matchTests false
      pos := walkMove v.pos } := by
  have e1 := step_less hv
  rw [show decide (v.pos "Walk" < v.pos "Cut") = true by simp; omega, mc_16_go] at e1
  have e2 := step_symbols (v := { v with ctl := (.pending [mc k pe (some true) ph 17] (.symbols "Walk" "U")) }) rfl hW hU
  simp only [heq, decide_true] at e2
  rw [mc_17_hit] at e2
  have e3 := step_move (v := { v with ctl := (.pending [mc k pe (some true) ph 18] (mv [("Walk", 1), ("U", 1)])) }) (ms := [⟨"Walk", 1⟩, ⟨"U", 1⟩]) rfl
    (walk_moveSeq v.pos _ ⟨by have := hW.1; omega, hW1⟩ ⟨by have := hU.1; omega, hU1⟩)
  simp [iterStep, e1, e2, e3]
  rfl

theorem round_miss (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k pe (some true) ph 16] (.less "Walk" "Cut"))
    (hlt : v.pos "Walk" < v.pos "Cut") (hW : v.inRange "Walk") (hU : v.inRange "U")
    (hne : v.word[(v.pos "Walk").toNat]? ≠ v.word[(v.pos "U").toNat]?) :
    iterStep 2 v = some { v with
      ctl := .pending [mc k pe (some false) ph 19] (.equal "A" "End") } := by
  have e1 := step_less hv
  rw [show decide (v.pos "Walk" < v.pos "Cut") = true by simp; omega, mc_16_go] at e1
  have e2 := step_symbols (v := { v with ctl := (.pending [mc k pe (some true) ph 17] (.symbols "Walk" "U")) }) rfl hW hU
  simp only [hne, decide_false] at e2
  rw [mc_17_miss] at e2
  simp [iterStep, e1, e2]

end Round

/-! ## One comparison at the loop head -/

section Compare
variable (k : ℕ) (pe : Option Bool) (ok : Bool) (ph : Option ℕ)

theorem head_wait (v : HVM) (hv : v.ctl = .pending [mc k pe (some ok) ph 13] (.available "B"))
    (hB : v.len ≤ v.pos "B") :
    iterStep 1 v = some v := by
  have e1 := step_available hv
  rw [show decide (v.pos "B" < v.len) = false by simp; omega, mc_13_wait, ← hv] at e1
  simp [iterStep, e1]

/-- The move of one pattern-text comparison. -/
def abMove (π : String → ℤ) : String → ℤ :=
  Function.update (Function.update π "A" (π "A" + 1)) "B" (π "B" + 1)

theorem head_hit (v : HVM) (hv : v.ctl = .pending [mc k pe (some ok) ph 13] (.available "B"))
    (hB : v.pos "B" < v.len) (hA : v.inRange "A") (hB' : v.inRange "B")
    (heq : v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?)
    (hA1 : v.pos "A" + 1 ≤ v.len) (hB1 : v.pos "B" + 1 ≤ v.len) :
    iterStep 3 v = some { v with
      ctl := (Ctl.pending [mc k pe (some ok) ph 15] (mv [("A", 1), ("B", 1)])).resume
        matchTests false
      pos := abMove v.pos } := by
  have e1 := step_available hv
  rw [show decide (v.pos "B" < v.len) = true by simp; omega, mc_13_go] at e1
  have e2 := step_symbols (v := { v with ctl := (.pending [mc k pe (some ok) ph 14] (.symbols "A" "B")) })
    rfl hA hB'
  simp only [heq, decide_true] at e2
  rw [mc_14_hit] at e2
  have hm : moveSeq blind v.len [⟨"A", 1⟩, ⟨"B", 1⟩] v.pos = some (abMove v.pos) := by
    simp only [moveSeq, blind]
    simp [Function.update, abMove]
    exact ⟨⟨by have := hA.1; omega, hA1⟩, ⟨by have := hB'.1; omega, hB1⟩⟩
  have e3 := step_move (v := { v with ctl := (.pending [mc k pe (some ok) ph 15] (mv [("A", 1), ("B", 1)])) })
    (ms := [⟨"A", 1⟩, ⟨"B", 1⟩]) rfl hm
  simp [iterStep, e1, e2, e3]
  rfl

theorem head_miss (v : HVM) (hv : v.ctl = .pending [mc k pe (some ok) ph 13] (.available "B"))
    (hB : v.pos "B" < v.len) (hA : v.inRange "A") (hB' : v.inRange "B")
    (hne : v.word[(v.pos "A").toNat]? ≠ v.word[(v.pos "B").toNat]?) :
    iterStep 2 v = some { v with
      ctl := (Ctl.pending [mc k pe (some ok) ph 14] (.symbols "A" "B")).resume matchTests false } := by
  have e1 := step_available hv
  rw [show decide (v.pos "B" < v.len) = true by simp; omega, mc_13_go] at e1
  have e2 := step_symbols (v := { v with ctl := (.pending [mc k pe (some ok) ph 14] (.symbols "A" "B")) })
    rfl hA hB'
  simp only [hne, decide_false] at e2
  simp [iterStep, e1, e2]

end Compare

/-! ## The prefix check: up to two rounds -/

/-- The prefix check's outcome from `c`, with `hit c` the comparison at `c` (`c < s`): the new
`c` and whether no mismatch was seen. -/
def pcheck (hit : ℕ → Bool) (s c : ℕ) : ℕ × Bool :=
  if c < s then
    if hit c then
      if c + 1 < s then (if hit (c + 1) then (c + 2, true) else (c + 1, false)) else (c + 1, true)
    else (c, false)
  else (c, true)

/-- `d` prefix moves. -/
def walkMoves : ℕ → (String → ℤ) → String → ℤ
  | 0, π => π
  | d + 1, π => walkMoves d (walkMove π)

theorem walkMoves_pos (d : ℕ) (π : String → ℤ) :
    walkMoves d π "Walk" = π "Walk" + d ∧ walkMoves d π "U" = π "U" + d ∧
      ∀ h, h ≠ "Walk" → h ≠ "U" → walkMoves d π h = π h := by
  induction d generalizing π with
  | zero => simp [walkMoves]
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := ih (walkMove π)
    refine ⟨?_, ?_, fun h ha hb => ?_⟩
    · show walkMoves d (walkMove π) "Walk" = _
      rw [h1]; simp [walkMove]; push_cast; ring
    · show walkMoves d (walkMove π) "U" = _
      rw [h2]; simp [walkMove]; push_cast; ring
    · show walkMoves d (walkMove π) h = _
      rw [h3 h ha hb]; simp [walkMove, Function.update, ha, hb]

/-- **The prefix check**, from its first round to the end test: the heads `Walk`, `U` move by
`(pcheck …).1 − c` and `ok` becomes `(pcheck …).2`. -/
theorem prefix_part (k : ℕ) (pe : Option Bool) (v : HVM) (s c : ℕ) (hit : ℕ → Bool)
    (hv : v.ctl = .pending [mc k pe (some true) (some 0) 16] (.less "Walk" "Cut"))
    (hC : v.pos "Cut" = s) (hW : v.pos "Walk" = c)
    (hhit : ∀ d, d ≤ 1 → c + d < s →
      (v.word[(v.pos "Walk" + d).toNat]? = v.word[(v.pos "U" + d).toNat]? ↔ hit (c + d) = true))
    (hWr : ∀ d, d ≤ 1 → c + d < s → v.inRange "Walk" ∧ 0 ≤ v.pos "U" ∧ v.pos "U" + d + 1 ≤ v.len)
    (hs : (s : ℤ) ≤ v.len) :
    ∃ n ph', n ≤ 6 ∧ iterStep n v = some { v with
      ctl := .pending [mc k pe (some (pcheck hit s c).2) ph' 19] (.equal "A" "End")
      pos := walkMoves ((pcheck hit s c).1 - c) v.pos } := by
  have hl : v.len = (v.word.length : ℤ) := rfl
  by_cases hc : c < s
  · have hh0 := hhit 0 (by omega) (by omega)
    obtain ⟨hWr0, hU0, hU0'⟩ := hWr 0 (by omega) (by omega)
    simp only [Nat.cast_zero, add_zero] at hh0
    cases h0 : hit c
    · -- mismatch at `c`
      have hne : v.word[(v.pos "Walk").toNat]? ≠ v.word[(v.pos "U").toNat]? := by
        intro he; rw [(hh0.mp he)] at h0; exact absurd h0 (by simp)
      refine ⟨2, some 0, by omega, ?_⟩
      rw [round_miss k pe (some 0) v hv (by omega) hWr0 ⟨hU0, by omega⟩ hne]
      simp [pcheck, hc, h0, walkMoves]
    · -- hit at `c`
      have heq : v.word[(v.pos "Walk").toNat]? = v.word[(v.pos "U").toNat]? := hh0.mpr h0
      have e1 := round_hit k pe (some 0) v hv (by omega) hWr0 ⟨hU0, by omega⟩ heq
        (by have := hWr0.2; omega) (by omega)
      rw [mc_18_again] at e1
      set v1 : HVM := { v with
        ctl := .pending [mc k pe (some true) (some 1) 16] (.less "Walk" "Cut")
        pos := walkMove v.pos }
      have hW1 : v1.pos "Walk" = c + 1 := by simp [v1, walkMove, hW]
      have hC1 : v1.pos "Cut" = s := by simp [v1, walkMove, Function.update, hC]
      by_cases hc1 : c + 1 < s
      · have hh1 := hhit 1 le_rfl hc1
        obtain ⟨hWr1, hU1, hU1'⟩ := hWr 1 le_rfl hc1
        have hv1W : v1.pos "Walk" = v.pos "Walk" + 1 := by simp [v1, walkMove]
        have hv1U : v1.pos "U" = v.pos "U" + 1 := by simp [v1, walkMove]
        have hr1 : v1.inRange "Walk" := by
          simp only [HVM.inRange, HVM.len, v1] at hs ⊢
          rw [show walkMove v.pos "Walk" = v.pos "Walk" + 1 by simp [walkMove], hW]
          constructor <;> omega
        have hr2 : v1.inRange "U" := by
          simp only [HVM.inRange, HVM.len, v1] at hU1' ⊢
          rw [show walkMove v.pos "U" = v.pos "U" + 1 by simp [walkMove]]; constructor <;> omega
        cases h1 : hit (c + 1)
        · have hne : v1.word[(v1.pos "Walk").toNat]? ≠ v1.word[(v1.pos "U").toNat]? := by
            intro he; rw [hv1W, hv1U] at he
            simp only [Nat.cast_one] at hh1
            rw [hh1.mp he] at h1; exact absurd h1 (by simp)
          refine ⟨3 + 2, some 1, by omega, ?_⟩
          rw [iterStep_add, e1, Option.bind_some,
            round_miss k pe (some 1) v1 rfl (by omega) hr1 hr2 hne]
          simp [pcheck, hc, h0, hc1, h1, walkMoves, v1]
        · have heq1 : v1.word[(v1.pos "Walk").toNat]? = v1.word[(v1.pos "U").toNat]? := by
            rw [hv1W, hv1U]; simp only [Nat.cast_one] at hh1; exact hh1.mpr h1
          have e2 := round_hit k pe (some 1) v1 rfl (by omega) hr1 hr2 heq1
            (by
              simp only [HVM.len, v1]
              rw [show walkMove v.pos "Walk" = v.pos "Walk" + 1 by simp [walkMove], hW]
              simp only [HVM.len] at hs; omega)
            (by
              simp only [HVM.len, v1]
              rw [show walkMove v.pos "U" = v.pos "U" + 1 by simp [walkMove]]
              simp only [HVM.len] at hU1'; omega)
          rw [mc_18_done] at e2
          refine ⟨3 + 3, some 1, by omega, ?_⟩
          rw [iterStep_add, e1, Option.bind_some, e2]
          simp [pcheck, hc, h0, hc1, h1, walkMoves, v1]
      · refine ⟨3 + 1, some 1, by omega, ?_⟩
        rw [iterStep_add, e1, Option.bind_some,
          round_skip k pe (some 1) v1 rfl (by rw [hW1, hC1]; omega)]
        simp [pcheck, hc, h0, hc1, walkMoves, v1]
  · refine ⟨1, some 0, by omega, ?_⟩
    rw [round_skip k pe (some 0) v hv (by rw [hW, hC]; omega)]
    simp [pcheck, hc, walkMoves]

/-! ## `pcheck` is two verifier comparisons -/

section PCheck
variable {α : Type} [DecidableEq α] (u T : List α) (pos : ℕ)

/-- The comparison the prefix check makes at `c`. -/
def hitAt (c : ℕ) : Bool := decide (T[pos - u.length + c]? = u[c]?)

theorem vComp_eq (c : ℕ) :
    PalPeg.vComp u T pos c = if c < u.length ∧ hitAt u T pos c = true then c + 1 else c := by
  simp [PalPeg.vComp, hitAt]

theorem pcheck_fst (c : ℕ) :
    (pcheck (hitAt u T pos) u.length c).1 =
      PalPeg.vComp u T pos (PalPeg.vComp u T pos c) := by
  rw [vComp_eq u T pos c]
  unfold pcheck
  by_cases hc : c < u.length
  · cases h0 : hitAt u T pos c
    · simp [hc, h0, vComp_eq]
    · by_cases hc1 : c + 1 < u.length
      · cases h1 : hitAt u T pos (c + 1) <;> simp [hc, h0, hc1, h1, vComp_eq]
      · simp [hc, h0, hc1, vComp_eq]
  · simp [hc, vComp_eq]

theorem pcheck_snd (c : ℕ) (h : (pcheck (hitAt u T pos) u.length c).2 = false) :
    (pcheck (hitAt u T pos) u.length c).1 < u.length ∧
      hitAt u T pos (pcheck (hitAt u T pos) u.length c).1 = false := by
  unfold pcheck at h ⊢
  by_cases hc : c < u.length
  · cases h0 : hitAt u T pos c
    · simp [hc, h0]
    · by_cases hc1 : c + 1 < u.length
      · cases h1 : hitAt u T pos (c + 1) <;> simp_all
      · simp_all
  · simp_all

/-- A stuck check stays stuck. -/
theorem vComp_stuck (c : ℕ) (h : hitAt u T pos c = false) : PalPeg.vComp u T pos c = c := by
  rw [vComp_eq]; simp [h]

end PCheck

/-! ## The shift decision -/

/-- Where the controller is after deciding to shift. -/
def decisionCtl (k : ℕ) (pe : Bool) (ok : Option Bool) (ph : Option ℕ) : Ctl :=
  if pe then .pending [mc k (some true) ok ph 22] (.less "A" "KFirst")
  else .pending [mc k (some false) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut")

/-- **The shift decision and the shift**: a period shift when `k·p₁ ≤ q ≤ r` (with a period),
otherwise a reset. -/
theorem shift_any (k : ℕ) (hk : 1 ≤ k) (pe : Bool) (ok : Option Bool) (ph : Option ℕ) (v : HVM)
    (s p₁ r q : ℕ) (hv : v.ctl = decisionCtl k pe ok ph)
    (hC : v.pos "Cut" = s) (hA : v.pos "A" = s + q)
    (hper : pe = true → v.pos "First" = s + p₁ ∧ v.pos "KFirst" = s + k * p₁ ∧
      v.pos "Reach" = s + r)
    (hAL : v.pos "A" ≤ v.len) (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" ≤ v.len)
    (hBF : v.pos "B" - q + (rsShifts k q : ℕ) ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPq : v.pos "P" + q ≤ v.len) (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, (pe = true ∧ k * p₁ ≤ q ∧ q ≤ r →
        iterStep n v = some { v with
          ctl := .pending [mc k (some pe) (some true) ph 13] (.available "B")
          pos := reenter (psPos v.pos p₁) }) ∧
      (¬ (pe = true ∧ k * p₁ ≤ q ∧ q ≤ r) →
        iterStep n v = some { v with
          ctl := .pending [mc k (some pe) (some true) ph 13] (.available "B")
          pos := reenter (rsPos v.pos q (rsShifts k q : ℕ)) }) := by
  have hqk : ((q / k : ℕ) : ℤ) ≤ q := by exact_mod_cast Nat.div_le_self q k
  have hreset : ∀ (ok' : Option Bool) (w : HVM), w.pos = v.pos → w.len = v.len →
      w.ctl = .pending [mc k (some pe) ok' ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut") →
      ∃ n, iterStep n w = some { w with
        ctl := .pending [mc k (some pe) (some true) ph 13] (.available "B")
        pos := reenter (rsPos w.pos q (rsShifts k q : ℕ)) } := by
    intro ok' w hwp hwl hw
    exact shift_reset k hk (some pe) ok' ph w q hw (by rw [hwp, hA, hC])
      (by rw [hwp, hC]; positivity) (by rw [hwp, hwl]; exact hAL) (by rw [hwp]; exact hBq)
      (by rw [hwp, hwl]; exact hBL) (by rw [hwp, hwl]; exact hBF) (by rw [hwp]; exact hP0)
      (by rw [hwp, hwl]; exact hPL)
  cases pe with
  | false =>
    obtain ⟨n, hn⟩ := hreset ok v rfl rfl (by simpa [decisionCtl] using hv)
    exact ⟨n, fun h => absurd h.1 (by simp), fun _ => hn⟩
  | true =>
    obtain ⟨hF, hKF, hR⟩ := hper rfl
    have hv' : v.ctl = .pending [mc k (some true) ok ph 22] (.less "A" "KFirst") := by
      simpa [decisionCtl] using hv
    have e1 := step_less hv'
    have hkp : ((k * p₁ : ℕ) : ℤ) = (k : ℤ) * p₁ := by push_cast; ring
    let vr : HVM := { v with
      ctl := (.pending [mc k (some true) ok ph 25, .resetShift k true 0 none 1] (.equal "A" "Cut")) }
    by_cases h1 : q < k * p₁
    · have h1' : (q : ℤ) < (k : ℤ) * p₁ := by exact_mod_cast h1
      rw [show decide (v.pos "A" < v.pos "KFirst") = true by
        rw [hA, hKF]; simp only [decide_eq_true_eq]; omega, mc_22_reset] at e1
      obtain ⟨n, hn⟩ := hreset ok vr rfl rfl rfl
      refine ⟨1 + n, fun h => absurd h.2.1 (by omega), fun _ => ?_⟩
      rw [iterStep_add]; simp only [iterStep, e1, Option.bind_some]; exact hn
    · have h1' : (k : ℤ) * p₁ ≤ q := by exact_mod_cast (not_lt.mp h1)
      rw [show decide (v.pos "A" < v.pos "KFirst") = false by
        rw [hA, hKF]; simp only [decide_eq_false_iff_not, not_lt]; omega, mc_22_next] at e1
      have e2 := step_less (v := { v with
        ctl := (.pending [mc k (some true) ok ph 23] (.less "Reach" "A")) }) rfl
      by_cases h2 : r < q
      · rw [show decide (v.pos "Reach" < v.pos "A") = true by
          rw [hA, hR]; simp only [decide_eq_true_eq]; exact_mod_cast (by omega : s + r < s + q),
          mc_23_reset] at e2
        obtain ⟨n, hn⟩ := hreset ok vr rfl rfl rfl
        refine ⟨2 + n, fun h => absurd h.2.2 (by omega), fun _ => ?_⟩
        rw [iterStep_add]; simp only [iterStep, e1, e2, Option.bind_some]; exact hn
      · rw [show decide (v.pos "Reach" < v.pos "A") = false by
          rw [hA, hR]; simp only [decide_eq_false_iff_not, not_lt]
          exact_mod_cast (by omega : s + q ≤ s + r), mc_23_period] at e2
        have hp1 : (p₁ : ℤ) ≤ q := by
          have : p₁ ≤ k * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
          have : p₁ ≤ q := by omega
          exact_mod_cast this
        have hsp := shift_period k ok ph { v with
          ctl := (.pending [mc k (some true) ok ph 24, .periodShift k true 1] (.copy "Walk" "Cut")) }
          p₁ rfl (by simp only; rw [hC, hF]) (by simp only; rw [hC]; positivity)
          (by simp only; rw [hF]; simp only [HVM.len] at hAL ⊢; rw [hA] at hAL; omega)
          (by simp only; rw [hA]; omega) hAL hP0
          (by simp only; simp only [HVM.len] at hPq ⊢; omega)
        refine ⟨2 + (2 * p₁ + 4), fun _ => ?_, fun h => absurd ⟨rfl, by omega, by omega⟩ h⟩
        rw [iterStep_add]; simp only [iterStep, e1, e2, Option.bind_some]; exact hsp

/-! ## The logical word -/

section Word
variable (x T : List (Fin 2)) (m : ℕ)

theorem word_pat {i : ℕ} (hi : i < x.length) : (x ++ T.take m)[i]? = x[i]? := by
  rw [List.getElem?_append_left hi]

theorem word_txt (j : ℕ) (hj : j < m) : (x ++ T.take m)[x.length + j]? = T[j]? := by
  rw [List.getElem?_append_right (by omega), show x.length + j - x.length = j by omega,
    List.getElem?_take_of_lt hj]

theorem pat_drop {s q : ℕ} : x[s + q]? = (x.drop s)[q]? := by
  rw [List.getElem?_drop]

theorem pat_take {s c : ℕ} (hc : c < s) : x[c]? = (x.take s)[c]? := by
  rw [List.getElem?_take_of_lt hc]

end Word

/-- **At the loop head**: the heads encode the verifier state `z` on the word `x ++ T.take m`. -/
structure AtHead (x T : List (Fin 2)) (m k s p₁ r : ℕ) (pe ok : Bool) (z : PalPeg.VState)
    (v : HVM) : Prop where
  ctl : ∃ ph, v.ctl = .pending [mc k (some pe) (some ok) ph 13] (.available "B")
  word : v.word = x ++ T.take m
  rel : LoopRel x.length s p₁ r k pe z.1.pos z.1.q z.2 v.pos
  dead : ok = false → z.2 < s ∧ hitAt (x.take s) T z.1.pos z.2 = false
  cut : s ≤ z.1.pos
  sx : s ≤ x.length
  qv : z.1.q < x.length - s
  cs : z.2 ≤ s
  arr : z.1.pos + z.1.q ≤ m
  tl : m ≤ T.length

theorem end_more (k : ℕ) (pe ok : Option Bool) (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k pe ok ph 19] (.equal "A" "End")) (hne : v.pos "A" ≠ v.pos "End") :
    iterStep 1 v = some { v with ctl := .pending [mc k pe ok ph 13] (.available "B") } := by
  have e1 := step_equal hv
  rw [show decide (v.pos "A" = v.pos "End") = false by simp [hne], mc_19_more] at e1
  simp [iterStep, e1]

theorem abMove_other (π : String → ℤ) (h : String) (ha : h ≠ "A") (hb : h ≠ "B") :
    abMove π h = π h := by
  simp [abMove, Function.update, ha, hb]

theorem loopRel_hit {lx s p₁ r k : ℕ} {pe : Bool} {pos q c : ℕ} {π : String → ℤ} (d : ℕ)
    (h : LoopRel lx s p₁ r k pe pos q c π) :
    LoopRel lx s p₁ r k pe pos (q + 1) (c + d) (walkMoves d (abMove π)) := by
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := h
  obtain ⟨m1, m2, m3⟩ := walkMoves_pos d (abMove π)
  have o : ∀ h', h' ≠ "Walk" → h' ≠ "U" → h' ≠ "A" → h' ≠ "B" →
      walkMoves d (abMove π) h' = π h' := fun h' a b c' e => by
    rw [m3 h' a b, abMove_other π h' c' e]
  refine ⟨by rw [o _ (by decide) (by decide) (by decide) (by decide), hO],
    by rw [o _ (by decide) (by decide) (by decide) (by decide), hC],
    by rw [o _ (by decide) (by decide) (by decide) (by decide), hE],
    fun hp => ?_, by rw [o _ (by decide) (by decide) (by decide) (by decide), hP], ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hper hp
    exact ⟨by rw [o _ (by decide) (by decide) (by decide) (by decide), h1],
      by rw [o _ (by decide) (by decide) (by decide) (by decide), h2],
      by rw [o _ (by decide) (by decide) (by decide) (by decide), h3]⟩
  · rw [m3 _ (by decide) (by decide)]; simp [abMove, Function.update, hA]; push_cast; ring
  · rw [m3 _ (by decide) (by decide)]; simp [abMove, Function.update, hB]; push_cast; ring
  · rw [m1]; simp [abMove, Function.update, hW]
  · rw [m2]; simp [abMove, Function.update, hU]; push_cast; ring

/-- **A hit with more of `v` to go** is one `vStep`. -/
theorem step_hit (x T : List (Fin 2)) (m k s p₁ r : ℕ) (pe ok : Bool) (z : PalPeg.VState) (v : HVM)
    (h : AtHead x T m k s p₁ r pe ok z v) (hen : z.1.pos + z.1.q < m)
    (hhit : T[z.1.pos + z.1.q]? = (x.drop s)[z.1.q]?) (hmore : z.1.q + 1 < x.length - s) :
    ∃ n ok' v', iterStep n v = some v' ∧
      AtHead x T m k s p₁ r pe ok' (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T z) v' := by
  obtain ⟨⟨pos, q⟩, c⟩ := z
  simp only at hen hhit hmore
  obtain ⟨ph, hc⟩ := h.ctl
  have hrel : LoopRel x.length s p₁ r k pe pos q c v.pos := h.rel
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := hrel
  have hsx := h.sx
  have hcut : s ≤ pos := h.cut
  have hcs : c ≤ s := h.cs
  have htl := h.tl
  have hlen : v.len = x.length + m := by
    simp only [HVM.len, h.word, List.length_append, List.length_take]
    rw [Nat.min_eq_left htl]; push_cast; ring
  have hut : (x.take s).length = s := by simp [List.length_take]; omega
  -- the list-level step
  have hvs : PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c) =
      (⟨pos, q + 1⟩, PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c)) := by
    have hq : q ≠ (x.drop s).length := by simp; omega
    simp only [PalPeg.vStep, PalPeg.scanStep, hq, if_false, hhit, if_true]
  rw [hvs]
  -- the pattern-text comparison
  have hwA : v.word[(v.pos "A").toNat]? = (x.drop s)[q]? := by
    rw [hA, h.word, show ((s : ℤ) + q).toNat = s + q by omega, word_pat x T m (by omega), pat_drop]
  have hwB : v.word[(v.pos "B").toNat]? = T[pos + q]? := by
    rw [hB, h.word, show ((x.length : ℤ) + pos + q).toNat = x.length + (pos + q) by omega,
      word_txt x T m _ hen]
  have e1 := head_hit k (some pe) ok ph v hc (by rw [hB, hlen]; omega)
    ⟨by rw [hA]; omega, by rw [hA, hlen]; omega⟩ ⟨by rw [hB]; omega, by rw [hB, hlen]; omega⟩
    (by rw [hwA, hwB, hhit]) (by rw [hA, hlen]; omega) (by rw [hB, hlen]; omega)
  cases ok with
  | false =>
    rw [mc_15_dead] at e1
    obtain ⟨hdc, hdh⟩ := h.dead rfl
    have hst : PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c) = c := by
      rw [vComp_stuck _ _ _ _ hdh, vComp_stuck _ _ _ _ hdh]
    let v1 : HVM := { v with
      ctl := (.pending [mc k (some pe) (some false) (some 0) 19] (.equal "A" "End"))
      pos := abMove v.pos }
    have e2 := end_more k (some pe) (some false) (some 0) v1 rfl
      (by show abMove v.pos "A" ≠ abMove v.pos "End"; simp [abMove, Function.update]; rw [hA, hE]; omega)
    refine ⟨3 + 1, false, _, by rw [iterStep_add, e1, Option.bind_some, e2], ?_⟩
    refine ⟨⟨some 0, rfl⟩, h.word, ?_, fun _ => ⟨?_, ?_⟩, by dsimp only; omega, hsx,
      by dsimp only; omega, by dsimp only; rw [hst]; exact hcs, by dsimp only; omega, htl⟩
    · have := loopRel_hit 0 (show LoopRel x.length s p₁ r k pe pos q c v.pos from h.rel)
      simp only [walkMoves, Nat.add_zero] at this
      dsimp only; rw [hst]; exact this
    · dsimp only; rw [hst]; exact hdc
    · dsimp only; rw [hst]; exact hdh
  | true =>
    rw [mc_15_ok] at e1
    let v1 : HVM := { v with
      ctl := (.pending [mc k (some pe) (some true) (some 0) 16] (.less "Walk" "Cut"))
      pos := abMove v.pos }
    have hv1W : v1.pos "Walk" = c := by simp [v1, abMove, Function.update, hW]
    have hv1U : v1.pos "U" = x.length + pos - s + c := by simp [v1, abMove, Function.update, hU]
    have hv1C : v1.pos "Cut" = s := by simp [v1, abMove, Function.update, hC]
    have hv1len : v1.len = x.length + m := hlen
    obtain ⟨n2, ph', hn2, e2⟩ := prefix_part k (some pe) v1 s c (hitAt (x.take s) T pos) rfl hv1C hv1W
      (fun d hd hcd => by
        rw [hv1W, hv1U, show ((c : ℤ) + d).toNat = c + d by omega,
          show ((x.length : ℤ) + pos - s + c + d).toNat = x.length + (pos - s + c + d) by omega]
        simp only [v1, h.word]
        rw [word_pat x T m (by omega), word_txt x T m _ (by omega), pat_take x (by omega : c + d < s)]
        simp only [hitAt, hut, decide_eq_true_eq]
        rw [show pos - s + (c + d) = pos - s + c + d by omega]
        constructor <;> intro hh <;> exact hh.symm)
      (fun d hd hcd => ⟨⟨by rw [hv1W]; omega, by rw [hv1W, hv1len]; omega⟩,
        by rw [hv1U]; omega, by rw [hv1U, hv1len]; omega⟩)
      (by rw [hv1len]; omega)
    set cc := (pcheck (hitAt (x.take s) T pos) s c).1 with hcc
    set ok' := (pcheck (hitAt (x.take s) T pos) s c).2 with hok'
    have hccv : cc = PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c) := by
      rw [hcc, ← pcheck_fst (x.take s) T pos c, hut]
    have hccle : c ≤ cc := by rw [hccv]; exact (PalPeg.le_vComp _ _ _ _).trans (PalPeg.le_vComp _ _ _ _)
    have hccs : cc ≤ s := by
      have h1 := PalPeg.vComp_le_length (u := x.take s) (T := T) (pos := pos)
        (PalPeg.vComp_le_length (u := x.take s) (T := T) (pos := pos) (c := c) (by rw [hut]; exact hcs))
      rw [hut] at h1; rw [hccv]; exact h1
    let v2 : HVM := { v1 with
      ctl := (.pending [mc k (some pe) (some ok') ph' 19] (.equal "A" "End"))
      pos := walkMoves (cc - c) v1.pos }
    have e3 := end_more k (some pe) (some ok') ph' v2 rfl (by
      simp only [v2, v1]
      rw [(walkMoves_pos _ _).2.2 _ (by decide) (by decide), (walkMoves_pos _ _).2.2 _ (by decide) (by decide)]
      simp [abMove, Function.update]; rw [hA, hE]; omega)
    refine ⟨3 + (n2 + 1), ok', _, by rw [iterStep_add, e1, Option.bind_some, iterStep_add, e2,
      Option.bind_some, e3], ?_⟩
    refine ⟨⟨ph', rfl⟩, h.word, ?_, fun hd => ?_, by dsimp only; omega, hsx, by dsimp only; omega,
      by dsimp only; rw [← hccv]; exact hccs, by dsimp only; omega, htl⟩
    · have := loopRel_hit (cc - c) (show LoopRel x.length s p₁ r k pe pos q c v.pos from h.rel)
      rw [show c + (cc - c) = cc by omega] at this
      dsimp only; rw [← hccv]; exact this
    · have := pcheck_snd (x.take s) T pos c (by rw [hut]; exact hd)
      rw [hut, ← hcc] at this; dsimp only; rw [← hccv]; exact this

theorem mc_14_miss (k : ℕ) (pe : Bool) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some pe) ok ph 14] (.symbols "A" "B")).resume matchTests false =
      decisionCtl k pe ok ph := by
  cases pe <;> rfl

theorem reenter_other (π : String → ℤ) (h : String) (h1 : h ≠ "Walk") (h2 : h ≠ "U") :
    reenter π h = π h := by
  simp [reenter, Function.update, h1, h2]

theorem loopRel_period {lx s p₁ r k : ℕ} {pos q c : ℕ} {π : String → ℤ}
    (h : LoopRel lx s p₁ r k true pos q c π) (hp : p₁ ≤ q) :
    LoopRel lx s p₁ r k true (pos + p₁) (q - p₁) 0 (reenter (psPos π p₁)) := by
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := h
  obtain ⟨hF, hKF, hR⟩ := hper rfl
  have ev : ∀ h', reenter (psPos π p₁) h' =
      if h' = "U" then π "P" + p₁ else if h' = "Walk" then π "Origin"
      else if h' = "A" then π "A" - p₁ else if h' = "P" then π "P" + p₁
      else if h' = "KP" then π "KP" - p₁ else π h' := by
    intro h'
    simp only [reenter, psPos, Function.update]
    by_cases h1 : h' = "U" <;> by_cases h2 : h' = "Walk" <;> simp_all
  refine ⟨?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ev] <;> simp <;>
    push_cast <;> omega

theorem loopRel_reset {lx s p₁ r k : ℕ} {pe : Bool} {pos q c t : ℕ} {π : String → ℤ}
    (h : LoopRel lx s p₁ r k pe pos q c π) :
    LoopRel lx s p₁ r k pe (pos + t) 0 0 (reenter (rsPos π q t)) := by
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := h
  have ev : ∀ h', reenter (rsPos π q t) h' =
      if h' = "U" then π "P" + t else if h' = "Walk" then π "Origin"
      else if h' = "A" then π "A" - q else if h' = "B" then π "B" - q + t
      else if h' = "P" then π "P" + t else if h' = "KP" then π "KP" - t else π h' := by
    intro h'
    simp only [reenter, rsPos, Function.update]
    by_cases h1 : h' = "U" <;> by_cases h2 : h' = "Walk" <;> simp_all
  refine ⟨?_, ?_, ?_, fun hp => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev]; simp; omega
  · rw [ev]; simp; omega
  · rw [ev]; simp; omega
  · obtain ⟨hF, hKF, hR⟩ := hper hp
    exact ⟨by rw [ev]; simp; omega, by rw [ev]; simp; omega, by rw [ev]; simp; omega⟩
  all_goals (rw [ev]; simp; push_cast; omega)

theorem ceil_le_succ (q k : ℕ) (hk : 1 ≤ k) : max 1 (PalPeg.ceilDiv q k) ≤ q + 1 := by
  unfold PalPeg.ceilDiv
  have h1 := Nat.le_mul_of_pos_right q (show 0 < k by omega)
  have : (q + k - 1) / k < q + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.add_mul, Nat.one_mul]; omega)
  omega

/-- **A miss** is one `vStep` (a shift). With no period, `p₁` must be large enough that the
period branch never applies (`|v| < k·p₁`, as for `effPeriod = |v| + 1`). -/
theorem step_miss (x T : List (Fin 2)) (m k s p₁ r : ℕ) (hk : 1 ≤ k) (pe ok : Bool)
    (z : PalPeg.VState) (v : HVM) (h : AtHead x T m k s p₁ r pe ok z v)
    (hen : z.1.pos + z.1.q < m) (hmiss : T[z.1.pos + z.1.q]? ≠ (x.drop s)[z.1.q]?)
    (hnoper : pe = false → x.length - s < k * p₁) :
    ∃ n v', iterStep n v = some v' ∧
      AtHead x T m k s p₁ r pe true (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T z) v' := by
  obtain ⟨⟨pos, q⟩, c⟩ := z
  simp only at hen hmiss
  obtain ⟨ph, hc⟩ := h.ctl
  have hrel : LoopRel x.length s p₁ r k pe pos q c v.pos := h.rel
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := hrel
  have hsx := h.sx
  have hcut : s ≤ pos := h.cut
  have hqv : q < x.length - s := h.qv
  have htl := h.tl
  have hlen : v.len = x.length + m := by
    simp only [HVM.len, h.word, List.length_append, List.length_take]
    rw [Nat.min_eq_left htl]; push_cast; ring
  have hvs : PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c) =
      (⟨pos + PalPeg.gsShift k p₁ r q, PalPeg.gsNextQ k p₁ r q⟩, 0) := by
    have hq : q ≠ (x.drop s).length := by simp; omega
    simp only [PalPeg.vStep, PalPeg.scanStep, hq, if_false, hmiss]
  rw [hvs]
  have hwA : v.word[(v.pos "A").toNat]? = (x.drop s)[q]? := by
    rw [hA, h.word, show ((s : ℤ) + q).toNat = s + q by omega, word_pat x T m (by omega), pat_drop]
  have hwB : v.word[(v.pos "B").toNat]? = T[pos + q]? := by
    rw [hB, h.word, show ((x.length : ℤ) + pos + q).toNat = x.length + (pos + q) by omega,
      word_txt x T m _ hen]
  have e1 := head_miss k (some pe) ok ph v hc (by rw [hB, hlen]; omega)
    ⟨by rw [hA]; omega, by rw [hA, hlen]; omega⟩ ⟨by rw [hB]; omega, by rw [hB, hlen]; omega⟩
    (by rw [hwA, hwB]; exact fun he => hmiss he.symm)
  rw [mc_14_miss] at e1
  set v1 : HVM := { v with ctl := decisionCtl k pe (some ok) ph } with hv1
  have hv1len : v1.len = x.length + m := hlen
  obtain ⟨n, hper', hres⟩ := shift_any k hk pe (some ok) ph v1 s p₁ r q rfl hC hA
    (fun hp => hper hp) (by rw [hA, hv1len]; omega) (by rw [hB]; omega) (by rw [hB, hv1len]; omega)
    (by
      have htq := ceil_le_succ q k hk
      rw [← rsShifts_eq k q hk] at htq
      rw [hB, hv1len]; push_cast at htq ⊢; omega)
    (by rw [hP]; omega) (by rw [hP, hv1len]; omega)
    (by
      have : q / k ≤ q := Nat.div_le_self q k
      rw [hP, hv1len]; push_cast; omega)
  by_cases hbr : pe = true ∧ k * p₁ ≤ q ∧ q ≤ r
  · have e2 := hper' hbr
    refine ⟨2 + n, _, by rw [iterStep_add, e1, Option.bind_some, e2], ?_⟩
    have hsh : PalPeg.gsShift k p₁ r q = p₁ := by simp [PalPeg.gsShift, hbr.2]
    have hnq : PalPeg.gsNextQ k p₁ r q = q - p₁ := by simp [PalPeg.gsNextQ, hbr.2]
    have hp1q : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hbr.2.1
    rw [hsh, hnq]
    refine ⟨⟨ph, rfl⟩, h.word, ?_, fun h' => absurd h' (by simp), by dsimp only; omega, hsx,
      by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, htl⟩
    dsimp only
    have := loopRel_period (show LoopRel x.length s p₁ r k true pos q c v.pos by
      rw [← hbr.1]; exact h.rel) hp1q
    rw [hbr.1]; exact this
  · have e2 := hres hbr
    refine ⟨2 + n, _, by rw [iterStep_add, e1, Option.bind_some, e2], ?_⟩
    have hsh : PalPeg.gsShift k p₁ r q = max 1 (PalPeg.ceilDiv q k) := by
      unfold PalPeg.gsShift
      rw [if_neg]
      intro h3; apply hbr
      cases pe with
      | true => exact ⟨rfl, h3⟩
      | false => have := hnoper rfl; omega
    have hnq : PalPeg.gsNextQ k p₁ r q = 0 := by
      unfold PalPeg.gsNextQ
      rw [if_neg]
      intro h3; apply hbr
      cases pe with
      | true => exact ⟨rfl, h3⟩
      | false => have := hnoper rfl; omega
    have hts := rsShifts_eq k q hk
    have htq := ceil_le_succ q k hk
    rw [hsh, hnq, ← hts]
    rw [← hts] at htq
    refine ⟨⟨ph, rfl⟩, h.word, loopRel_reset (show LoopRel x.length s p₁ r k pe pos q c v.pos from h.rel),
      fun h' => absurd h' (by simp), by dsimp only; omega, hsx, by dsimp only; omega,
      by dsimp only; omega, by dsimp only; omega, htl⟩

theorem mc_19_dead (k : ℕ) (pe : Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some pe) (some false) ph 19] (.equal "A" "End")).resume matchTests true =
      decisionCtl k pe (some false) ph := by
  cases pe <;> rfl

theorem mc_21 (k : ℕ) (pe : Bool) (ok : Option Bool) (ph : Option ℕ) :
    (Ctl.pending [mc k (some pe) ok ph 21] (.«match» "B")).resume matchTests false =
      decisionCtl k pe ok ph := by
  cases pe <;> rfl

/-- At the end test with `A = End`: a live check reports (`assert_equal`, then `match B`), a dead
one goes straight to the shift decision. -/
theorem end_report (k : ℕ) (pe : Bool) (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k (some pe) (some true) ph 19] (.equal "A" "End"))
    (he : v.pos "A" = v.pos "End") (hwc : v.pos "Walk" = v.pos "Cut") :
    iterStep 3 v = some { v with
      ctl := decisionCtl k pe (some true) ph
      outputs := v.outputs ++ [v.pos "B" - v.patternSize] } := by
  have e1 := step_equal hv
  rw [show decide (v.pos "A" = v.pos "End") = true by simp [he], mc_19_report] at e1
  have e2 := step_assertEqual (v := { v with
    ctl := (.pending [mc k (some pe) (some true) ph 20] (.assertEqual "Walk" "Cut")) }) rfl hwc
  rw [mc_20] at e2
  have e3 := step_match (v := { v with
    ctl := (.pending [mc k (some pe) (some true) ph 21] (.«match» "B")) }) rfl
  rw [mc_21] at e3
  simp [iterStep, e1, e2, e3]

theorem end_dead (k : ℕ) (pe : Bool) (ph : Option ℕ) (v : HVM)
    (hv : v.ctl = .pending [mc k (some pe) (some false) ph 19] (.equal "A" "End"))
    (he : v.pos "A" = v.pos "End") :
    iterStep 1 v = some { v with ctl := decisionCtl k pe (some false) ph } := by
  have e1 := step_equal hv
  rw [show decide (v.pos "A" = v.pos "End") = true by simp [he], mc_19_dead] at e1
  simp [iterStep, e1]

theorem rsShifts_le (k q : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) : rsShifts k q ≤ q := by
  rw [rsShifts_eq k q hk]
  unfold PalPeg.ceilDiv
  have hkq : q + k - 1 ≤ k * q := by
    obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    ring_nf; omega
  have : (q + k - 1) / k ≤ q := Nat.div_le_of_le_mul hkq
  omega

/-- The heads a shift reads (not `Walk`, `U`). -/
def ShiftRel (lx s p₁ r k : ℕ) (pe : Bool) (pos q : ℕ) (π : String → ℤ) : Prop :=
  π "Origin" = 0 ∧ π "Cut" = s ∧ π "End" = lx ∧
  (pe = true → π "First" = s + p₁ ∧ π "KFirst" = s + k * p₁ ∧ π "Reach" = s + r) ∧
  π "P" = lx + pos - s ∧ π "A" = s + q ∧ π "B" = lx + pos + q

theorem loopRel_period' {lx s p₁ r k : ℕ} {pos q : ℕ} {π : String → ℤ}
    (h : ShiftRel lx s p₁ r k true pos q π) (hp : p₁ ≤ q) :
    LoopRel lx s p₁ r k true (pos + p₁) (q - p₁) 0 (reenter (psPos π p₁)) := by
  obtain ⟨hO, hC, hE, hper, hP, hA, hB⟩ := h
  obtain ⟨hF, hKF, hR⟩ := hper rfl
  have ev : ∀ h', reenter (psPos π p₁) h' =
      if h' = "U" then π "P" + p₁ else if h' = "Walk" then π "Origin"
      else if h' = "A" then π "A" - p₁ else if h' = "P" then π "P" + p₁
      else if h' = "KP" then π "KP" - p₁ else π h' := by
    intro h'
    simp only [reenter, psPos, Function.update]
    by_cases h1 : h' = "U" <;> by_cases h2 : h' = "Walk" <;> simp_all
  refine ⟨?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [ev] <;> simp <;>
    push_cast <;> omega

theorem loopRel_reset' {lx s p₁ r k : ℕ} {pe : Bool} {pos q t : ℕ} {π : String → ℤ}
    (h : ShiftRel lx s p₁ r k pe pos q π) :
    LoopRel lx s p₁ r k pe (pos + t) 0 0 (reenter (rsPos π q t)) := by
  obtain ⟨hO, hC, hE, hper, hP, hA, hB⟩ := h
  have ev : ∀ h', reenter (rsPos π q t) h' =
      if h' = "U" then π "P" + t else if h' = "Walk" then π "Origin"
      else if h' = "A" then π "A" - q else if h' = "B" then π "B" - q + t
      else if h' = "P" then π "P" + t else if h' = "KP" then π "KP" - t else π h' := by
    intro h'
    simp only [reenter, rsPos, Function.update]
    by_cases h1 : h' = "U" <;> by_cases h2 : h' = "Walk" <;> simp_all
  refine ⟨?_, ?_, ?_, fun hp => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ev]; simp; omega
  · rw [ev]; simp; omega
  · rw [ev]; simp; omega
  · obtain ⟨hF, hKF, hR⟩ := hper hp
    exact ⟨by rw [ev]; simp; omega, by rw [ev]; simp; omega, by rw [ev]; simp; omega⟩
  all_goals (rw [ev]; simp; push_cast; omega)

/-- **From the shift decision to the next loop head**, for any scan state `(pos, q)` about to
shift. -/
theorem shift_to_head (x T : List (Fin 2)) (m k s p₁ r : ℕ) (hk : 2 ≤ k) (pe : Bool)
    (ok : Option Bool) (ph : Option ℕ) (v : HVM) (pos q : ℕ)
    (hv : v.ctl = decisionCtl k pe ok ph) (hw : v.word = x ++ T.take m)
    (hO : v.pos "Origin" = 0) (hC : v.pos "Cut" = s) (hE : v.pos "End" = x.length)
    (hper : pe = true → v.pos "First" = s + p₁ ∧ v.pos "KFirst" = s + k * p₁ ∧
      v.pos "Reach" = s + r)
    (hP : v.pos "P" = x.length + pos - s) (hA : v.pos "A" = s + q)
    (hB : v.pos "B" = x.length + pos + q)
    (hsx : s < x.length) (hcut : s ≤ pos) (hqv : q ≤ x.length - s) (harr : pos + q ≤ m)
    (harr' : pos + q < m ∨ 1 ≤ q) (htl : m ≤ T.length)
    (hnoper : pe = false → x.length - s < k * p₁) (hp1 : pe = true → 1 ≤ p₁) :
    ∃ n v', iterStep n v = some v' ∧ v'.outputs = v.outputs ∧
      AtHead x T m k s p₁ r pe true
        ((⟨pos + PalPeg.gsShift k p₁ r q, PalPeg.gsNextQ k p₁ r q⟩ : PalPeg.ScanState), 0) v' := by
  have hlen : v.len = x.length + m := by
    simp only [HVM.len, hw, List.length_append, List.length_take]
    rw [Nat.min_eq_left htl]; push_cast; ring
  have hts := rsShifts_eq k q (by omega)
  have htq : (rsShifts k q : ℤ) ≤ q ∨ (q = 0 ∧ rsShifts k q = 1) := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · right; subst h0; exact ⟨rfl, by simp [rsShifts]⟩
    · left; exact_mod_cast rsShifts_le k q (by omega) h0
  have hqk : q / k + 1 ≤ q ∨ q = 0 := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · right; exact h0
    · left
      have : q / k < q := Nat.div_lt_self h0 (by omega)
      omega
  obtain ⟨n, hper', hres⟩ := shift_any k (by omega) pe ok ph v s p₁ r q hv hC hA hper
    (by rw [hA, hlen]; omega) (by rw [hB]; omega) (by rw [hB, hlen]; omega)
    (by rw [hB, hlen]; rcases htq with h1 | ⟨h1, h2⟩ <;> [omega; (rw [h2]; push_cast; omega)])
    (by rw [hP]; omega) (by rw [hP, hlen]; omega)
    (by rw [hP, hlen]; rcases hqk with h1 | h1 <;> [(push_cast; omega); (subst h1; simp; omega)])
  have hsr : ShiftRel x.length s p₁ r k pe pos q v.pos := ⟨hO, hC, hE, hper, hP, hA, hB⟩
  by_cases hbr : pe = true ∧ k * p₁ ≤ q ∧ q ≤ r
  · have e2 := hper' hbr
    have hsh : PalPeg.gsShift k p₁ r q = p₁ := by simp [PalPeg.gsShift, hbr.2]
    have hnq : PalPeg.gsNextQ k p₁ r q = q - p₁ := by simp [PalPeg.gsNextQ, hbr.2]
    have hp1q : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hbr.2.1
    have hp1' := hp1 hbr.1
    refine ⟨n, _, e2, rfl, ?_⟩
    rw [hsh, hnq]
    obtain rfl := hbr.1
    exact ⟨⟨ph, rfl⟩, hw, loopRel_period' hsr hp1q, fun h' => absurd h' (by simp),
      by dsimp only; omega, by omega, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, htl⟩
  · have e2 := hres hbr
    have hsh : PalPeg.gsShift k p₁ r q = max 1 (PalPeg.ceilDiv q k) := by
      unfold PalPeg.gsShift
      rw [if_neg]
      intro h3; apply hbr
      cases pe with
      | true => exact ⟨rfl, h3⟩
      | false => have := hnoper rfl; omega
    have hnq : PalPeg.gsNextQ k p₁ r q = 0 := by
      unfold PalPeg.gsNextQ
      rw [if_neg]
      intro h3; apply hbr
      cases pe with
      | true => exact ⟨rfl, h3⟩
      | false => have := hnoper rfl; omega
    refine ⟨n, _, e2, rfl, ?_⟩
    rw [hsh, hnq, ← hts]
    have htn : pos + rsShifts k q ≤ m := by
      rcases htq with h1 | ⟨h1, h2⟩
      · have : rsShifts k q ≤ q := by exact_mod_cast h1
        omega
      · rw [h2]; omega
    exact ⟨⟨ph, rfl⟩, hw, loopRel_reset' hsr, fun h' => absurd h' (by simp),
      by dsimp only; omega, by omega, by dsimp only; omega, by dsimp only; omega,
      by dsimp only; omega, htl⟩

theorem pcheck_done (hit : ℕ → Bool) (s c : ℕ) (h : (pcheck hit s c).2 = true) (hcs : c ≤ s)
    (hdl : hit c = true → c < s → s ≤ c + 2) : (pcheck hit s c).1 = s := by
  unfold pcheck at h ⊢
  by_cases hc : c < s
  · rw [if_pos hc] at h ⊢
    cases h0 : hit c
    · simp [h0] at h
    · simp only [h0, if_true] at h ⊢
      have hd := hdl h0 hc
      by_cases hc1 : c + 1 < s
      · simp only [hc1, if_true] at h ⊢
        cases h1 : hit (c + 1)
        · simp [h1] at h
        · simp only [h1, if_true]; omega
      · simp only [hc1, if_false]; omega
  · rw [if_neg hc]; omega

/-- **A hit, up to the end test**: `A`, `B` advance, the prefix check runs (if live), and the
controller waits at the end test with the verifier's new `c = vComp (vComp c)`. -/
theorem hit_to_end (x T : List (Fin 2)) (m k s p₁ r : ℕ) (pe ok : Bool) (z : PalPeg.VState)
    (v : HVM) (h : AtHead x T m k s p₁ r pe ok z v) (hen : z.1.pos + z.1.q < m)
    (hhit : T[z.1.pos + z.1.q]? = (x.drop s)[z.1.q]?) :
    ∃ n ok' ph' π', iterStep n v = some { v with
        ctl := .pending [mc k (some pe) (some ok') ph' 19] (.equal "A" "End")
        pos := π' } ∧
      LoopRel x.length s p₁ r k pe z.1.pos (z.1.q + 1)
        (PalPeg.vComp (x.take s) T z.1.pos (PalPeg.vComp (x.take s) T z.1.pos z.2)) π' ∧
      (ok' = false → PalPeg.vComp (x.take s) T z.1.pos (PalPeg.vComp (x.take s) T z.1.pos z.2) < s ∧
        hitAt (x.take s) T z.1.pos
          (PalPeg.vComp (x.take s) T z.1.pos (PalPeg.vComp (x.take s) T z.1.pos z.2)) = false) ∧
      (ok' = true → ok = true ∧ (pcheck (hitAt (x.take s) T z.1.pos) s z.2).2 = true) := by
  obtain ⟨⟨pos, q⟩, c⟩ := z
  simp only at hen hhit ⊢
  obtain ⟨ph, hc⟩ := h.ctl
  have hrel : LoopRel x.length s p₁ r k pe pos q c v.pos := h.rel
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := hrel
  have hsx := h.sx
  have hcut : s ≤ pos := h.cut
  have hcs : c ≤ s := h.cs
  have hqv : q < x.length - s := h.qv
  have htl := h.tl
  have hlen : v.len = x.length + m := by
    simp only [HVM.len, h.word, List.length_append, List.length_take]
    rw [Nat.min_eq_left htl]; push_cast; ring
  have hut : (x.take s).length = s := by simp [List.length_take]; omega
  have hwA : v.word[(v.pos "A").toNat]? = (x.drop s)[q]? := by
    rw [hA, h.word, show ((s : ℤ) + q).toNat = s + q by omega, word_pat x T m (by omega), pat_drop]
  have hwB : v.word[(v.pos "B").toNat]? = T[pos + q]? := by
    rw [hB, h.word, show ((x.length : ℤ) + pos + q).toNat = x.length + (pos + q) by omega,
      word_txt x T m _ hen]
  have e1 := head_hit k (some pe) ok ph v hc (by rw [hB, hlen]; omega)
    ⟨by rw [hA]; omega, by rw [hA, hlen]; omega⟩ ⟨by rw [hB]; omega, by rw [hB, hlen]; omega⟩
    (by rw [hwA, hwB, hhit]) (by rw [hA, hlen]; omega) (by rw [hB, hlen]; omega)
  cases ok with
  | false =>
    rw [mc_15_dead] at e1
    obtain ⟨hdc, hdh⟩ := h.dead rfl
    have hst : PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c) = c := by
      rw [vComp_stuck _ _ _ _ hdh, vComp_stuck _ _ _ _ hdh]
    refine ⟨3, false, some 0, abMove v.pos, e1, ?_, fun _ => ?_, fun h' => absurd h' (by simp)⟩
    · have := loopRel_hit 0 (show LoopRel x.length s p₁ r k pe pos q c v.pos from h.rel)
      simp only [walkMoves, Nat.add_zero] at this; rw [hst]; exact this
    · rw [hst]; exact ⟨hdc, hdh⟩
  | true =>
    rw [mc_15_ok] at e1
    let v1 : HVM := { v with
      ctl := (.pending [mc k (some pe) (some true) (some 0) 16] (.less "Walk" "Cut"))
      pos := abMove v.pos }
    have hv1W : v1.pos "Walk" = c := by simp [v1, abMove, Function.update, hW]
    have hv1U : v1.pos "U" = x.length + pos - s + c := by simp [v1, abMove, Function.update, hU]
    have hv1C : v1.pos "Cut" = s := by simp [v1, abMove, Function.update, hC]
    have hv1len : v1.len = x.length + m := hlen
    obtain ⟨n2, ph', hn2, e2⟩ := prefix_part k (some pe) v1 s c (hitAt (x.take s) T pos) rfl hv1C hv1W
      (fun d hd hcd => by
        rw [hv1W, hv1U, show ((c : ℤ) + d).toNat = c + d by omega,
          show ((x.length : ℤ) + pos - s + c + d).toNat = x.length + (pos - s + c + d) by omega]
        simp only [v1, h.word]
        rw [word_pat x T m (by omega), word_txt x T m _ (by omega), pat_take x (by omega : c + d < s)]
        simp only [hitAt, hut, decide_eq_true_eq]
        rw [show pos - s + (c + d) = pos - s + c + d by omega]
        constructor <;> intro hh <;> exact hh.symm)
      (fun d hd hcd => ⟨⟨by rw [hv1W]; omega, by rw [hv1W, hv1len]; omega⟩,
        by rw [hv1U]; omega, by rw [hv1U, hv1len]; omega⟩)
      (by rw [hv1len]; omega)
    set cc := (pcheck (hitAt (x.take s) T pos) s c).1 with hcc
    set ok' := (pcheck (hitAt (x.take s) T pos) s c).2 with hok'
    have hccv : cc = PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c) := by
      rw [hcc, ← pcheck_fst (x.take s) T pos c, hut]
    have hccle : c ≤ cc := by rw [hccv]; exact (PalPeg.le_vComp _ _ _ _).trans (PalPeg.le_vComp _ _ _ _)
    refine ⟨3 + n2, ok', ph', walkMoves (cc - c) (abMove v.pos),
      by rw [iterStep_add, e1, Option.bind_some, e2], ?_, fun hd => ?_, fun hd => ⟨rfl, hd⟩⟩
    · have := loopRel_hit (cc - c) (show LoopRel x.length s p₁ r k pe pos q c v.pos from h.rel)
      rw [show c + (cc - c) = cc by omega] at this
      rw [← hccv]; exact this
    · have := pcheck_snd (x.take s) T pos c (by rw [hut]; exact hd)
      rw [hut, ← hcc] at this; rw [← hccv]; exact this

/-- **A hit that completes `v`**: the report (when the prefix check is live), then the shift; two
`vStep`s. The deadline invariant at the state before rules out an unfinished live check. -/
theorem step_report (x T : List (Fin 2)) (m k s p₁ r : ℕ) (hk : 2 ≤ k) (pe ok : Bool)
    (z : PalPeg.VState) (v : HVM) (h : AtHead x T m k s p₁ r pe ok z v)
    (hen : z.1.pos + z.1.q < m) (hhit : T[z.1.pos + z.1.q]? = (x.drop s)[z.1.q]?)
    (hlast : z.1.q + 1 = x.length - s)
    (hdl : PalPeg.GSReportDeadline.DeadlineInv (x.take s) (x.drop s) T z)
    (hps : v.patternSize = x.length)
    (hnoper : pe = false → x.length - s < k * p₁) (hp1 : pe = true → 1 ≤ p₁) :
    ∃ n v', iterStep n v = some v' ∧
      v'.outputs = v.outputs ++
        (if (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T z).2 = s
          then [((z.1.pos + (x.length - s) : ℕ) : ℤ)] else []) ∧
      AtHead x T m k s p₁ r pe true
        (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T (PalPeg.vStep (x.take s) (x.drop s) k p₁ r T z)) v' := by
  obtain ⟨n1, ok', ph', π', e1, hrel', hdead', hlive'⟩ := hit_to_end x T m k s p₁ r pe ok z v h hen hhit
  obtain ⟨⟨pos, q⟩, c⟩ := z
  simp only at hen hhit hlast hrel' hdead' hlive' ⊢
  have hsx := h.sx
  have hcut : s ≤ pos := h.cut
  have hcs : c ≤ s := h.cs
  have htl := h.tl
  have hut : (x.take s).length = s := by simp [List.length_take]; omega
  set cc := PalPeg.vComp (x.take s) T pos (PalPeg.vComp (x.take s) T pos c) with hcc
  have hvs1 : PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q⟩ : PalPeg.ScanState), c) =
      (⟨pos, q + 1⟩, cc) := by
    have hq : q ≠ (x.drop s).length := by simp; omega
    simp only [PalPeg.vStep, PalPeg.scanStep, hq, if_false, hhit, if_true, hcc]
  have hvs2 : PalPeg.vStep (x.take s) (x.drop s) k p₁ r T ((⟨pos, q + 1⟩ : PalPeg.ScanState), cc) =
      (⟨pos + PalPeg.gsShift k p₁ r (q + 1), PalPeg.gsNextQ k p₁ r (q + 1)⟩, 0) := by
    have hq : q + 1 = (x.drop s).length := by simp; omega
    simp only [PalPeg.vStep, PalPeg.scanStep, hq, if_true]
  rw [hvs1, hvs2]
  obtain ⟨hO, hC, hE, hper, hP, hA, hB, hW, hU⟩ := hrel'
  set v1 : HVM := { v with
    ctl := (.pending [mc k (some pe) (some ok') ph' 19] (.equal "A" "End"))
    pos := π' } with hv1
  have hAE : v1.pos "A" = v1.pos "End" := by
    show π' "A" = π' "End"; rw [hA, hE]; push_cast; omega
  have hstep := fun (w : HVM) (ok'' : Option Bool) (hw : w.ctl = decisionCtl k pe ok'' ph')
      (hwp : w.pos = π') (hww : w.word = x ++ T.take m) =>
    shift_to_head x T m k s p₁ r hk pe ok'' ph' w pos (q + 1) hw hww
      (by rw [hwp]; exact hO) (by rw [hwp]; exact hC) (by rw [hwp]; exact hE)
      (fun hp => by rw [hwp]; exact hper hp) (by rw [hwp]; exact hP) (by rw [hwp]; exact hA)
      (by rw [hwp]; exact hB) (by omega) hcut (by omega) (by omega) (Or.inr (by omega)) htl hnoper hp1
  cases ok' with
  | true =>
    obtain ⟨hok, hpc⟩ := hlive' rfl
    have hdone : cc = s := by
      have := pcheck_done (hitAt (x.take s) T pos) s c hpc hcs (fun h0 hlt => by
        have hh : T[pos - (x.take s).length + c]? = (x.take s)[c]? := by
          simpa [hitAt] using h0
        have := PalPeg.GSReportDeadline.le_add_two_of_hit hdl (by simp; omega) hh
        rw [hut] at this; exact this)
      rw [hcc, ← pcheck_fst (x.take s) T pos c, hut]; exact this
    have hWC : v1.pos "Walk" = v1.pos "Cut" := by
      show π' "Walk" = π' "Cut"; rw [hW, hC, hdone]
    have e2 := end_report k pe ph' v1 rfl hAE hWC
    obtain ⟨n3, v', e3, ho3, hat⟩ := hstep { v1 with
        ctl := decisionCtl k pe (some true) ph'
        outputs := v1.outputs ++ [v1.pos "B" - v1.patternSize] } (some true) rfl rfl h.word
    refine ⟨n1 + (3 + n3), v', by rw [iterStep_add, e1, Option.bind_some, iterStep_add, e2,
      Option.bind_some, e3], ?_, hat⟩
    rw [ho3, if_pos hdone]
    show v.outputs ++ [π' "B" - v.patternSize] = _
    rw [hB, hps]; push_cast; congr 2; omega
  | false =>
    obtain ⟨hlt, -⟩ := hdead' rfl
    have e2 := end_dead k pe ph' v1 rfl hAE
    obtain ⟨n3, v', e3, ho3, hat⟩ := hstep { v1 with ctl := decisionCtl k pe (some false) ph' }
      (some false) rfl rfl h.word
    refine ⟨n1 + (1 + n3), v', by rw [iterStep_add, e1, Option.bind_some, iterStep_add, e2,
      Option.bind_some, e3], ?_, hat⟩
    rw [ho3, if_neg (by omega), List.append_nil]

end PalPeg.ScaMatcherLoop
