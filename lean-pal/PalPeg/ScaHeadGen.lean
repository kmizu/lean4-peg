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

end PalPeg.ScaHeadGen
