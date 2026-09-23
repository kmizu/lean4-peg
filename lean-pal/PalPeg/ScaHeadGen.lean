import PalPeg.ScaHeadRun

/-!
# Contracts of the shared generators, run on their own chain

Each generator (`PeriodShift`, `ResetShift`, `First`, `Second`, `Decompose`, `Initialize`) is run
alone, from its fresh frame, by the matcher VM's `stepMatch`; its contract says where the heads
end up and after how many steps it returns. `ScaHeadRun.lift_run` then places the run inside
any caller. None of these generators emits `available`, so letter arrivals commute with their
steps (`stepMatch_append`).
-/
set_option autoImplicit false
namespace PalPeg.ScaHeadGen
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun

/-- `n` steps of the matcher VM. -/
def iterStep : ℕ → HVM → Option HVM
  | 0, v => some v
  | n + 1, v => (stepMatch v).bind (iterStep n)

theorem iterStep_add (m n : ℕ) (v : HVM) :
    iterStep (m + n) v = (iterStep m v).bind (iterStep n) := by
  induction m generalizing v with
  | zero => simp [iterStep]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [iterStep]
    cases stepMatch v with
    | none => rfl
    | some w => simp [ih]

/-! ## `PeriodShift k true` -/

/-- The pending event and chain of `PeriodShift` at its loop head. -/
def psLoop (k : ℕ) : Ctl := .pending [.periodShift k true 2] (.less "Walk" "First")

theorem ps_start (k : ℕ) :
    Ctl.ofOutcome (next [.periodShift k true 0] none) =
      .pending [.periodShift k true 1] (.copy "Walk" "Cut") := rfl

/-- Heads after `i` iterations of the `PeriodShift` loop. -/
def psPos (π : String → ℤ) (i : ℤ) : String → ℤ := fun h =>
  if h = "Walk" then π "Cut" + i
  else if h = "A" then π "A" - i
  else if h = "P" then π "P" + i
  else if h = "KP" then π "KP" - i
  else π h

theorem ps_first (k : ℕ) (v : HVM) (hv : v.ctl = .pending [.periodShift k true 1] (.copy "Walk" "Cut")) :
    iterStep 1 v = some { v with ctl := psLoop k, pos := psPos v.pos 0 } := by
  have hpos : Function.update v.pos "Walk" (v.pos "Cut") = psPos v.pos 0 := by
    funext h
    by_cases h1 : h = "Walk"
    · subst h1; simp [psPos]
    · simp only [psPos, Function.update_of_ne h1, if_neg h1]; split_ifs <;> simp_all
  simp only [iterStep, stepMatch, hv, Option.bind_some]
  rw [hpos]; rfl

theorem ps_exit (k : ℕ) (v : HVM) (hv : v.ctl = psLoop k) (hge : v.pos "First" ≤ v.pos "Walk") :
    iterStep 1 v = some { v with ctl := .returned none } := by
  have hd : decide (v.pos "Walk" < v.pos "First") = false := by simp; omega
  simp only [iterStep, stepMatch, hv, psLoop, Option.bind_some, hd]
  rfl

/-- The move of one `PeriodShift` iteration (searching). -/
def psMove : Event := mv [("Walk", 1), ("A", -1), ("P", 1), ("KP", -1)]

theorem ps_iter (k : ℕ) (v : HVM) (π : String → ℤ) (i : ℤ) (hv : v.ctl = psLoop k)
    (hp : v.pos = psPos π i) (hlt : π "Cut" + i < π "First")
    (hW : 0 ≤ π "Cut" + i + 1 ∧ π "Cut" + i + 1 ≤ v.len)
    (hA : 0 ≤ π "A" - i - 1 ∧ π "A" - i - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + i + 1 ∧ π "P" + i + 1 ≤ v.len) :
    iterStep 2 v = some { v with ctl := psLoop k, pos := psPos π (i + 1) } := by
  have hW' : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPos]
  have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPos]
  have hd : decide (v.pos "Walk" < v.pos "First") = true := by simp; omega
  have hmv : moveSeq blind v.len [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", -1⟩] v.pos =
      some (psPos π (i + 1)) := by
    simp only [moveSeq, blind, hp]
    simp [psPos, Function.update]
    refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
    funext h
    by_cases h1 : h = "KP" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "A" <;>
      by_cases h4 : h = "Walk" <;> simp_all [psPos] <;> omega
  have e1 : stepMatch v = some { v with ctl := .pending [.periodShift k true 3] psMove } := by
    simp only [stepMatch, hv, psLoop, hd]; rfl
  have e2 : stepMatch { v with ctl := .pending [.periodShift k true 3] psMove } =
      some { v with ctl := psLoop k, pos := psPos π (i + 1) } := by
    simp only [stepMatch, psMove, mv, List.map_cons, List.map_nil]
    have hmv' := hmv
    simp only [HVM.len] at hmv' ⊢
    rw [hmv']; rfl
  simp [iterStep, e1, e2]

theorem ps_loop_run (k : ℕ) (π : String → ℤ) (L : ℤ) :
    ∀ (m : ℕ) (v : HVM) (i : ℤ), v.ctl = psLoop k → v.pos = psPos π i → v.len = L →
      π "Cut" + i + m = π "First" → 0 ≤ π "Cut" + i → π "First" ≤ L →
      0 ≤ π "A" - (i + m) → π "A" - i ≤ L → 0 ≤ π "P" + i → π "P" + i + m ≤ L →
      iterStep (2 * m + 1) v = some { v with ctl := .returned none, pos := psPos π (i + m) }
  | 0, v, i, hv, hp, _, he, _, _, _, _, _, _ => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPos]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPos]
    rw [ps_exit k v hv (by omega)]
    simp [hp]
  | m + 1, v, i, hv, hp, hL, he, h1, h2, h3, h4, h5, h6 => by
    have hstep := ps_iter k v π i hv hp (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩
    rw [show 2 * (m + 1) + 1 = 2 + (2 * m + 1) by ring, iterStep_add, hstep, Option.bind_some]
    have := ps_loop_run k π L m { v with ctl := psLoop k, pos := psPos π (i + 1) } (i + 1) rfl rfl
      hL (by push_cast at he; omega) (by omega) h2 (by push_cast at h3; omega) (by omega) (by omega)
      (by push_cast at h6; omega)
    rw [this]
    congr 2
    push_cast; ring

/-- **`PeriodShift k true`, from its fresh frame**: after `2t + 2` steps, `t = First − Cut`, it
returns with `Walk = First`, `A − t`, `P + t`, `KP − t`. -/
theorem periodShift_run (k : ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.periodShift k true 0] none))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len) :
    iterStep (2 * t + 2) v = some { v with ctl := .returned none, pos := psPos v.pos t } := by
  rw [ps_start] at hv
  rw [show 2 * t + 2 = 1 + (2 * t + 1) by ring, iterStep_add, ps_first k v hv, Option.bind_some]
  have := ps_loop_run k v.pos v.len t { v with ctl := psLoop k, pos := psPos v.pos 0 } 0 rfl rfl
    rfl (by omega) (by omega) hF (by omega) (by omega) (by omega) (by omega)
  rw [this]
  simp

/-! ## `ResetShift k true` -/

/-- The searching shift: `P + 1`, `B + 1`, `KP − 1`. -/
def rsShift : Event := mv [("P", 1), ("B", 1), ("KP", -1)]

/-- Loop head of `ResetShift k true` at phase `ph`, knowing whether the rewind is non-empty. -/
def rsLoop (k ph : ℕ) (ne : Bool) : Ctl :=
  .pending [.resetShift k true ph (some ne) 2] (.equal "A" "Cut")

/-- Heads after rewinding `j` cells with `s` shifts. -/
def rsPos (π : String → ℤ) (j s : ℤ) : String → ℤ := fun h =>
  if h = "A" then π "A" - j
  else if h = "B" then π "B" - j + s
  else if h = "P" then π "P" + s
  else if h = "KP" then π "KP" - s
  else π h

theorem rs_start (k : ℕ) :
    Ctl.ofOutcome (next [.resetShift k true 0 none 0] none) =
      .pending [.resetShift k true 0 none 1] (.equal "A" "Cut") := rfl

theorem rs_first (k : ℕ) (v : HVM) (hv : v.ctl = .pending [.resetShift k true 0 none 1] (.equal "A" "Cut")) :
    iterStep 1 v = some { v with ctl := rsLoop k 0 (decide (v.pos "A" ≠ v.pos "Cut")) } := by
  simp only [iterStep, step_equal hv, Option.bind_some]
  congr 2
  by_cases h : v.pos "A" = v.pos "Cut" <;> simp [h, rsLoop] <;> rfl

theorem rsPos_zero (π : String → ℤ) : rsPos π 0 0 = π := by
  funext h; simp only [rsPos]; split_ifs <;> simp_all

/-- The rewind move: `A − 1`, `B − 1`. -/
def rsBack : Event := mv [("A", -1), ("B", -1)]

theorem rs_resume_back (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k true ph (some ne) 2] (.equal "A" "Cut")).resume matchTests false =
      .pending [.resetShift k true ph (some ne) 3] rsBack := rfl

/-- One `advance` of a frame that emits. -/
theorem next_single_emit (f f' : Frame) (r : Option Bool) (e : Event)
    (hs : stepFrame f r = some (.emit e f')) :
    next [f] r = some (.yielded e [f']) := by
  show advance (63 + 1) f r = _
  rw [advance, hs]
  rfl

theorem rs_resume_step (k ph : ℕ) (ne : Bool) (hph : ph + 1 < k) :
    (Ctl.pending [.resetShift k true ph (some ne) 3] rsBack).resume matchTests false =
      rsLoop k (ph + 1) ne := by
  have h : (ph + 1 == k) = false := by simp; omega
  have hs : stepFrame (.resetShift k true ph (some ne) 3) none =
      some (.emit (.equal "A" "Cut") (.resetShift k true (ph + 1) (some ne) 2)) := by
    simp only [stepFrame, stepResetShift, h]; rfl
  show Ctl.ofOutcome (next _ none) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rs_resume_wrap (k ph : ℕ) (ne : Bool) (hph : ph + 1 = k) :
    (Ctl.pending [.resetShift k true ph (some ne) 3] rsBack).resume matchTests false =
      .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift := by
  have h : (ph + 1 == k) = true := by simp; omega
  have hs : stepFrame (.resetShift k true ph (some ne) 3) none =
      some (.emit rsShift (.resetShift k true (ph + 1) (some ne) 5)) := by
    simp only [stepFrame, stepResetShift, h]; rfl
  show Ctl.ofOutcome (next _ none) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rs_resume_after_wrap (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k true ph (some ne) 5] rsShift).resume matchTests false =
      rsLoop k 0 ne := rfl

theorem rs_move_back (π : String → ℤ) (j s L : ℤ)
    (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ L) (hB : 0 ≤ π "B" - j + s - 1 ∧ π "B" - j + s - 1 ≤ L) :
    moveSeq blind L [⟨"A", -1⟩, ⟨"B", -1⟩] (rsPos π j s) = some (rsPos π (j + 1) s) := by
  simp only [moveSeq, blind]
  simp [rsPos, Function.update]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  funext h
  by_cases h1 : h = "KP" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "A" <;>
    by_cases h4 : h = "B" <;> simp_all [rsPos] <;> omega

theorem rs_move_shift (π : String → ℤ) (j s L : ℤ)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ L) (hB : 0 ≤ π "B" - j + s + 1 ∧ π "B" - j + s + 1 ≤ L) :
    moveSeq blind L [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩] (rsPos π j s) = some (rsPos π j (s + 1)) := by
  simp only [moveSeq, blind]
  simp [rsPos, Function.update]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ?_⟩
  funext h
  by_cases h1 : h = "KP" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "A" <;>
    by_cases h4 : h = "B" <;> simp_all [rsPos] <;> omega

theorem rs_iter (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 < k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s - 1 ∧ π "B" - j + s - 1 ≤ v.len) :
    iterStep 2 v = some { v with ctl := rsLoop k (ph + 1) ne, pos := rsPos π (j + 1) s } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPos, hne]
  have e1 := step_equal hv
  rw [hd, rs_resume_back] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack } =
      some { v with ctl := rsLoop k (ph + 1) ne, pos := rsPos π (j + 1) s } := by
    rw [step_move (v := { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack })
      (ms := [⟨"A", -1⟩, ⟨"B", -1⟩]) rfl (by simp only [HVM.len]; rw [hp]; exact rs_move_back π j s _ hA hB)]
    rw [show (Ctl.pending [.resetShift k true ph (some ne) 3] (.move [⟨"A", -1⟩, ⟨"B", -1⟩])) =
      .pending [.resetShift k true ph (some ne) 3] rsBack from rfl, rs_resume_step k ph ne hph]
  simp [iterStep, e1, e2]

theorem rs_wrap (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 = k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s - 1 ∧ π "B" - j + s - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len) (hB' : π "B" - j + s ≤ v.len) :
    iterStep 3 v = some { v with ctl := rsLoop k 0 ne, pos := rsPos π (j + 1) (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPos, hne]
  have e1 := step_equal hv
  rw [hd, rs_resume_back] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack } =
      some { v with
        ctl := .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift
        pos := rsPos π (j + 1) s } := by
    rw [step_move (v := { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack })
      (ms := [⟨"A", -1⟩, ⟨"B", -1⟩]) rfl (by simp only [HVM.len]; rw [hp]; exact rs_move_back π j s _ hA hB)]
    rw [show (Ctl.pending [.resetShift k true ph (some ne) 3] (.move [⟨"A", -1⟩, ⟨"B", -1⟩])) =
      .pending [.resetShift k true ph (some ne) 3] rsBack from rfl, rs_resume_wrap k ph ne hph]
  have e3 : stepMatch { v with
        ctl := .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift
        pos := rsPos π (j + 1) s } =
      some { v with ctl := rsLoop k 0 ne, pos := rsPos π (j + 1) (s + 1) } := by
    rw [step_move (ms := [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩]) rfl
      (by
        have hl : v.len = (v.word.length : ℤ) := rfl
        simp only [HVM.len]
        exact rs_move_shift π (j + 1) s _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)]
    rw [show (Ctl.pending [.resetShift k true (ph + 1) (some ne) 5] (.move [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩])) =
      .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift from rfl, rs_resume_after_wrap]
  simp [iterStep, e1, e2, e3]

theorem rs_resume_exit_shift (k ph : ℕ) (ne : Bool) (h : (!ne || ph != 0) = true) :
    (rsLoop k ph ne).resume matchTests true =
      .pending [.resetShift k true ph (some ne) 7] rsShift := by
  have hs : stepFrame (.resetShift k true ph (some ne) 2) (some true) =
      some (.emit rsShift (.resetShift k true ph (some ne) 7)) := by
    simp [stepFrame, stepResetShift, rsShift]
    cases ne <;> simp_all
  show Ctl.ofOutcome (next _ (some true)) = _
  rw [next_single_emit _ _ _ _ hs]; rfl

theorem rs_resume_exit_ret (k ph : ℕ) (ne : Bool) (h : (!ne || ph != 0) = false) :
    (rsLoop k ph ne).resume matchTests true = .returned none := by
  have hs : stepFrame (.resetShift k true ph (some ne) 2) (some true) = some (.ret none) := by
    simp [stepFrame, stepResetShift]
    cases ne <;> simp_all
  show Ctl.ofOutcome (advance (63 + 1) _ (some true)) = _
  rw [advance, hs]; rfl

theorem rs_resume_after_exit (k ph : ℕ) (ne : Bool) :
    (Ctl.pending [.resetShift k true ph (some ne) 7] rsShift).resume matchTests false =
      .returned none := rfl

/-- The loop's exit, with a last shift. -/
theorem rs_exit_shift (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = true) (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s + 1 ∧ π "B" - j + s + 1 ≤ v.len) :
    iterStep 2 v = some { v with ctl := .returned none, pos := rsPos π j (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPos, he]
  have e1 := step_equal hv
  rw [hd] at e1
  rw [show (Ctl.pending [.resetShift k true ph (some ne) 2] (.equal "A" "Cut")) = rsLoop k ph ne
    from rfl, rs_resume_exit_shift k ph ne h] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 7] rsShift } =
      some { v with ctl := .returned none, pos := rsPos π j (s + 1) } := by
    rw [step_move (ms := [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩]) rfl
      (by simp only [HVM.len]; rw [hp]; exact rs_move_shift π j s _ hP hB)]
    rw [show (Ctl.pending [.resetShift k true ph (some ne) 7] (.move [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩])) =
      .pending [.resetShift k true ph (some ne) 7] rsShift from rfl, rs_resume_after_exit]
  simp [iterStep, e1, e2]

/-- The loop's exit, without a last shift. -/
theorem rs_exit_ret (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = false) :
    iterStep 1 v = some { v with ctl := .returned none } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPos, he]
  have e1 := step_equal hv
  rw [hd] at e1
  rw [show (Ctl.pending [.resetShift k true ph (some ne) 2] (.equal "A" "Cut")) = rsLoop k ph ne
    from rfl, rs_resume_exit_ret k ph ne h] at e1
  simp [iterStep, e1]

end PalPeg.ScaHeadGen
