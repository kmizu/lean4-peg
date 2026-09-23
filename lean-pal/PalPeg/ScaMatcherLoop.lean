import PalPeg.ScaHeadGen
import PalPeg.GSVerifier

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
    ∃ n ph', iterStep n v = some { v with
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
      refine ⟨2, some 0, ?_⟩
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
          refine ⟨3 + 2, some 1, ?_⟩
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
          refine ⟨3 + 3, some 1, ?_⟩
          rw [iterStep_add, e1, Option.bind_some, e2]
          simp [pcheck, hc, h0, hc1, h1, walkMoves, v1]
      · refine ⟨3 + 1, some 1, ?_⟩
        rw [iterStep_add, e1, Option.bind_some,
          round_skip k pe (some 1) v1 rfl (by rw [hW1, hC1]; omega)]
        simp [pcheck, hc, h0, hc1, walkMoves, v1]
  · refine ⟨1, some 0, ?_⟩
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
    (hAL : v.pos "A" ≤ v.len) (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" + 1 ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPL : v.pos "P" + q + 1 ≤ v.len) :
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
      (by rw [hwp, hwl]; exact hBL) (by rw [hwp]; exact hP0) (by rw [hwp, hwl]; omega)
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
          (by simp only; simp only [HVM.len] at hPL ⊢; omega)
        refine ⟨2 + (2 * p₁ + 4), fun _ => ?_, fun h => absurd ⟨rfl, by omega, by omega⟩ h⟩
        rw [iterStep_add]; simp only [iterStep, e1, e2, Option.bind_some]; exact hsp

end PalPeg.ScaMatcherLoop
