import PalPeg.ScaHeadRun
import PalPeg.GSScan

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

theorem modstep (j k : ℕ) (hk : 1 ≤ k) :
    (j % k + 1 < k → (j + 1) % k = j % k + 1 ∧ (j + 1) / k = j / k) ∧
    (j % k + 1 = k → (j + 1) % k = 0 ∧ (j + 1) / k = j / k + 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < k ∧ j = q * k + r :=
    ⟨j / k, j % k, Nat.mod_lt _ (by omega), by rw [Nat.div_add_mod' j k]⟩
  have hm : (q * k + r) % k = r := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hd : (q * k + r) / k = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  rw [hm, hd]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  · rw [Nat.add_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h,
      Nat.zero_add]
  · rw [Nat.add_assoc, h, show q * k + k = (q + 1) * k by ring, Nat.mul_mod_left]
  · rw [Nat.add_assoc, h, show q * k + k = (q + 1) * k by ring, Nat.mul_div_cancel _ (by omega)]

/-- The final shift count of `ResetShift` after rewinding `q` cells: `max 1 ⌈q/k⌉`. -/
def rsShifts (k q : ℕ) : ℕ := q / k + if q = 0 ∨ q % k ≠ 0 then 1 else 0

theorem rs_loop_run (k : ℕ) (hk : 1 ≤ k) (π : String → ℤ) (L : ℤ) (ne : Bool) (q : ℕ)
    (hne : ne = decide (q ≠ 0)) :
    ∀ (m : ℕ) (v : HVM) (j sh : ℕ), j + m = q → sh = j / k → v.ctl = rsLoop k (j % k) ne →
      v.pos = rsPos π j sh → v.len = L →
      π "A" - q = π "Cut" → 0 ≤ π "Cut" → π "A" - j ≤ L → (q : ℤ) ≤ π "B" →
      π "B" - j + sh + 1 ≤ L → 0 ≤ π "P" → π "P" + (q / k : ℕ) + 1 ≤ L →
      ∃ n, n ≤ 3 * m + 2 ∧
        iterStep n v = some { v with ctl := .returned none, pos := rsPos π q (rsShifts k q : ℕ) }
  | 0, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hBL, hP0, hPL => by
    have hj : j = q := by omega
    subst hj
    have hshq : sh = j / k := hsh
    by_cases hx : (!ne || j % k != 0) = true
    · refine ⟨2, by omega, ?_⟩
      rw [rs_exit_shift k (j % k) ne v π j sh hv hp (by omega) hx
        ⟨by positivity, by rw [hshq]; omega⟩ ⟨by omega, by omega⟩]
      have : (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx; simp at hx
        rcases hx with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      simp only [rsShifts, if_pos this, hshq, Nat.cast_add, Nat.cast_one]
    · refine ⟨1, by omega, ?_⟩
      have hx' : (!ne || j % k != 0) = false := by simpa using hx
      rw [rs_exit_ret k (j % k) ne v π j sh hv hp (by omega) hx']
      have : ¬ (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx'; simp at hx'; omega
      simp only [rsShifts, if_neg this, Nat.add_zero, ← hshq, hp]
  | m + 1, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hBL, hP0, hPL => by
    obtain ⟨hs1, hs2⟩ := modstep j k hk
    have hjq : sh ≤ q / k := by rw [hsh]; exact Nat.div_le_div_right (by omega)
    rcases Nat.lt_or_ge (j % k + 1) k with hph | hph
    · obtain ⟨hm1, hd1⟩ := hs1 hph
      have hstep := rs_iter k (j % k) ne v π j sh hv hp (by omega) hph
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      obtain ⟨n, hn, hrun⟩ := rs_loop_run k hk π L ne q hne m
        { v with ctl := rsLoop k (j % k + 1) ne, pos := rsPos π (↑j + 1) sh } (j + 1) sh
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        (by push_cast; omega) hP0 hPL
      refine ⟨2 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]
    · have hph' : j % k + 1 = k := by have := Nat.mod_lt j (show 0 < k by omega); omega
      obtain ⟨hm1, hd1⟩ := hs2 hph'
      have hj1 : sh + 1 ≤ q / k := by
        rw [hsh, ← hd1]; exact Nat.div_le_div_right (by omega)
      have hstep := rs_wrap k (j % k) ne v π j sh hv hp (by omega) hph'
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      obtain ⟨n, hn, hrun⟩ := rs_loop_run k hk π L ne q hne m
        { v with ctl := rsLoop k 0 ne, pos := rsPos π (↑j + 1) (↑sh + 1) } (j + 1) (sh + 1)
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        (by push_cast; omega) hP0 hPL
      refine ⟨3 + n, by omega, ?_⟩
      rw [iterStep_add, hstep, Option.bind_some, hrun]

/-- **`ResetShift k true`, from its fresh frame**: rewinding `q = A − Cut` cells, it returns
within `3q + 3` steps with `A = Cut`, `B − q + t`, `P + t`, `KP − t`, `t = max 1 ⌈q/k⌉`. -/
theorem resetShift_run (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" + 1 ≤ v.len) (hP0 : 0 ≤ v.pos "P")
    (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len) :
    ∃ n, n ≤ 3 * q + 3 ∧
      iterStep n v = some { v with
        ctl := .returned none
        pos := rsPos v.pos q (rsShifts k q : ℕ) } := by
  rw [rs_start] at hv
  have h1 := rs_first k v hv
  have hne : decide (v.pos "A" ≠ v.pos "Cut") = decide (q ≠ 0) := by
    simp only [decide_eq_decide]; omega
  rw [hne] at h1
  obtain ⟨n, hn, hrun⟩ := rs_loop_run k hk v.pos v.len (decide (q ≠ 0)) q rfl q
    { v with ctl := rsLoop k 0 (decide (q ≠ 0)) } 0 0 (by omega) (by simp) (by simp)
    (by simp [rsPos_zero]) rfl (by omega) hC (by simp; omega) hBq (by simp; omega) hP0 hPL
  refine ⟨1 + n, by omega, ?_⟩
  rw [iterStep_add, h1, Option.bind_some, hrun]

/-! ## Lifting counted runs, and the reset shift count -/

theorem iterStep_lift (f : Frame) :
    ∀ (n : ℕ) (v w : HVM), NonEmptyCtl v.ctl → iterStep n v = some w →
      iterStep n (liftVM f v) = some (liftVM f w)
  | 0, v, w, _, h => by simp [iterStep] at h; subst h; rfl
  | n + 1, v, w, hv, h => by
    simp only [iterStep] at h ⊢
    cases hs : stepMatch v with
    | none => simp [hs] at h
    | some v1 =>
      rw [hs, Option.bind_some] at h
      obtain ⟨cs, e, hc, -⟩ := stepMatch_ctl hs
      have hne : cs ≠ [] := by rw [hc] at hv; exact hv
      have hl : liftVM f v = { v with ctl := .pending (f :: cs) e } := by
        simp only [liftVM, hc, liftCtl]
      rw [hl, stepMatch_lift f v cs e hc hne, hs, Option.map_some, Option.bind_some]
      exact iterStep_lift f n v1 w (nonEmpty_step hv (MStep.step hs)) h

theorem rsShifts_eq (k q : ℕ) (hk : 1 ≤ k) : rsShifts k q = max 1 (PalPeg.ceilDiv q k) := by
  unfold rsShifts PalPeg.ceilDiv
  have ha := Nat.div_add_mod q k
  have hb := Nat.mod_lt q (show 0 < k by omega)
  split_ifs with h
  · rcases h with h | h
    · subst h; simp [Nat.div_eq_of_lt (show k - 1 < k by omega)]
    · have h1 : (q + k - 1) / k = q / k + 1 := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
        · rw [show (q / k + 1 + 1) * k = k * (q / k) + k + k by ring]; omega
      rw [h1, max_eq_right (Nat.le_add_left _ _)]
  · have h' : q ≠ 0 ∧ q % k = 0 := by
      constructor
      · exact fun h0 => h (Or.inl h0)
      · by_contra h0; exact h (Or.inr h0)
    have h1 : (q + k - 1) / k = q / k := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm]; omega
      · rw [show (q / k + 1) * k = k * (q / k) + k by ring]; omega
    have : 1 ≤ q / k := by
      rcases Nat.eq_zero_or_pos (q / k) with h0 | h0
      · rw [h0] at ha; omega
      · exact h0
    rw [h1, max_eq_right this, Nat.add_zero]

end PalPeg.ScaHeadGen
