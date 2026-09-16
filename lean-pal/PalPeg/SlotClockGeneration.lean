import PalPeg.SlotClockSweep

set_option autoImplicit false
namespace PalPeg.SlotClockGeneration
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock
open PalPeg.SlotClockSweep

def endpoint (a : Bool) (p : Fin 30) (leftward : Bool) (n : ℕ)
    (junk grown : List Symbol) (u : Symbol) : SConfig (Ctrl × Fin 2) Symbol 2 :=
  ⟨((a, p), 0), fun j => if j = slot a then
    if leftward then ⟨List.replicate n .tick ++ .edge :: junk, .edge, []⟩
    else ⟨junk, .edge, List.replicate n .tick ++ [.edge]⟩
    else ⟨grown, u, []⟩⟩

def grownNext (p : Fin 30) (n : ℕ) (grown : List Symbol) : List Symbol :=
  if p.val < 14 then grown else
    List.replicate n .tick ++ (if p = 14 then .edge else .tick) :: grown

def focusNext (p : Fin 30) (u : Symbol) : Symbol :=
  if p.val < 14 then u else .blank

theorem config_eq (a : Bool) (x y : SConfig (Ctrl × Fin 2) Symbol 2)
    (hs : x.state = y.state) (ha : x.tape (slot a) = y.tape (slot a))
    (hb : x.tape (slot (!a)) = y.tape (slot (!a))) : x = y := by
  have ht : x.tape = y.tape := by
    funext j
    have hj : j = slot a ∨ j = slot (!a) := by
      cases a <;> fin_cases j <;> simp [slot]
    rcases hj with rfl | rfl <;> assumption
  cases x; cases y
  simp_all

theorem left_step (a : Bool) (p : Fin 30) (he : p.val % 2 = 0)
    (n : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run (n + 1) (endpoint a p true n junk grown u) =
      endpoint a (nextPhase p) false n junk (grownNext p n grown) (focusNext p u) := by
  let T := (endpoint a p true n junk grown u).tape
  have ha : T (slot a) = ⟨List.replicate n .tick ++ .edge :: junk, .edge, []⟩ := by
    simp [T, endpoint]
  have hn : slot (!a) ≠ slot a := by cases a <;> decide
  have hb : T (slot (!a)) = ⟨grown, u, []⟩ := by simp [T, endpoint, hn]
  have hh := sweep_left a p he n junk [] .edge T ha
  apply config_eq a
  · exact hh.1
  · simpa [T, endpoint] using hh.2
  · by_cases hg : p.val < 14
    · have hi := idle_left a p he hg n junk [] .edge T ha
      simpa [T, endpoint, hn, grownNext, focusNext, hg] using hi
    · have hi := grow_left a p he (by omega) n junk [] grown .edge u T ha hb
      simpa [T, endpoint, hn, grownNext, focusNext, hg] using hi

theorem right_step (a : Bool) (p : Fin 30) (he : p.val % 2 ≠ 0) (hp : p ≠ 29)
    (n : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run (n + 1) (endpoint a p false n junk grown u) =
      endpoint a (nextPhase p) true n junk (grownNext p n grown) (focusNext p u) := by
  let T := (endpoint a p false n junk grown u).tape
  have ha : T (slot a) = ⟨junk, .edge, List.replicate n .tick ++ [.edge]⟩ := by
    simp [T, endpoint]
  have hn : slot (!a) ≠ slot a := by cases a <;> decide
  have hb : T (slot (!a)) = ⟨grown, u, []⟩ := by simp [T, endpoint, hn]
  have hh := sweep_right a p he hp n junk [] .edge T ha
  apply config_eq a
  · exact hh.1
  · simpa [T, endpoint] using hh.2
  · by_cases hg : p.val < 14
    · have hi := idle_right a p he hg n junk [] .edge T ha
      simpa [T, endpoint, hn, grownNext, focusNext, hg] using hi
    · have h14 : p ≠ 14 := by intro h; subst p; contradiction
      have hv : p.val ≠ 14 := by
        intro h
        exact h14 (Fin.ext h)
      have hi := grow_right a p he (by omega) hp n junk [] grown .edge u T ha hb
      simpa [T, endpoint, hn, grownNext, focusNext, hg, h14,
        List.replicate_succ', List.append_assoc] using hi

theorem final_step (a : Bool) (n m : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run (n + 1) (endpoint a 29 false n junk (List.replicate m .tick ++ .edge :: grown) u) =
      endpoint (!a) 0 true (n + 1 + m) grown (List.replicate n .tick ++ .edge :: junk) .edge := by
  let T := (endpoint a 29 false n junk (List.replicate m .tick ++ .edge :: grown) u).tape
  have hn : slot (!a) ≠ slot a := by cases a <;> decide
  have hh := final_sweep a n junk (List.replicate m .tick ++ .edge :: grown) .edge u T
    (by simp [T, endpoint]) (by simp [T, endpoint, hn])
  apply config_eq a
  · exact hh.1
  · have hr : slot a ≠ slot (!a) := Ne.symm hn
    simpa [T, endpoint, hr] using hh.2.1
  · simpa [T, endpoint, List.replicate_add, List.append_assoc] using hh.2.2

theorem ticks_join (n m : ℕ) (g : List Symbol) :
    List.replicate n .tick ++ .tick :: (List.replicate m .tick ++ g) =
      List.replicate (n + (m + 1)) .tick ++ g := by
  rw [← List.cons_append, ← List.replicate_succ, ← List.append_assoc, ← List.replicate_add]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- A complete generation of the concrete clock, for an arbitrary positive
interval length n+1 and arbitrary retained history on both tapes. -/
theorem generation (a : Bool) (n : ℕ) (junk grown : List Symbol) (u : Symbol) :
    run (30 * (n + 1)) (endpoint a 0 true n junk grown u) =
      endpoint (!a) 0 true (16 * (n + 1) - 1) grown
        (List.replicate n .tick ++ .edge :: junk) .edge := by
  rw [show 30 * (n + 1) = (n + 1) + 29 * (n + 1) by omega,
    run_add, left_step a 0 (by decide)]
  rw [show nextPhase (0 : Fin 30) = 1 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (0 : Fin 30).val < 14)]
  rw [show 29 * (n + 1) = (n + 1) + 28 * (n + 1) by omega,
    run_add, right_step a 1 (by decide) (by decide)]
  rw [show nextPhase (1 : Fin 30) = 2 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (1 : Fin 30).val < 14)]
  rw [show 28 * (n + 1) = (n + 1) + 27 * (n + 1) by omega,
    run_add, left_step a 2 (by decide)]
  rw [show nextPhase (2 : Fin 30) = 3 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (2 : Fin 30).val < 14)]
  rw [show 27 * (n + 1) = (n + 1) + 26 * (n + 1) by omega,
    run_add, right_step a 3 (by decide) (by decide)]
  rw [show nextPhase (3 : Fin 30) = 4 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (3 : Fin 30).val < 14)]
  rw [show 26 * (n + 1) = (n + 1) + 25 * (n + 1) by omega,
    run_add, left_step a 4 (by decide)]
  rw [show nextPhase (4 : Fin 30) = 5 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (4 : Fin 30).val < 14)]
  rw [show 25 * (n + 1) = (n + 1) + 24 * (n + 1) by omega,
    run_add, right_step a 5 (by decide) (by decide)]
  rw [show nextPhase (5 : Fin 30) = 6 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (5 : Fin 30).val < 14)]
  rw [show 24 * (n + 1) = (n + 1) + 23 * (n + 1) by omega,
    run_add, left_step a 6 (by decide)]
  rw [show nextPhase (6 : Fin 30) = 7 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (6 : Fin 30).val < 14)]
  rw [show 23 * (n + 1) = (n + 1) + 22 * (n + 1) by omega,
    run_add, right_step a 7 (by decide) (by decide)]
  rw [show nextPhase (7 : Fin 30) = 8 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (7 : Fin 30).val < 14)]
  rw [show 22 * (n + 1) = (n + 1) + 21 * (n + 1) by omega,
    run_add, left_step a 8 (by decide)]
  rw [show nextPhase (8 : Fin 30) = 9 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (8 : Fin 30).val < 14)]
  rw [show 21 * (n + 1) = (n + 1) + 20 * (n + 1) by omega,
    run_add, right_step a 9 (by decide) (by decide)]
  rw [show nextPhase (9 : Fin 30) = 10 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (9 : Fin 30).val < 14)]
  rw [show 20 * (n + 1) = (n + 1) + 19 * (n + 1) by omega,
    run_add, left_step a 10 (by decide)]
  rw [show nextPhase (10 : Fin 30) = 11 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (10 : Fin 30).val < 14)]
  rw [show 19 * (n + 1) = (n + 1) + 18 * (n + 1) by omega,
    run_add, right_step a 11 (by decide) (by decide)]
  rw [show nextPhase (11 : Fin 30) = 12 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (11 : Fin 30).val < 14)]
  rw [show 18 * (n + 1) = (n + 1) + 17 * (n + 1) by omega,
    run_add, left_step a 12 (by decide)]
  rw [show nextPhase (12 : Fin 30) = 13 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (12 : Fin 30).val < 14)]
  rw [show 17 * (n + 1) = (n + 1) + 16 * (n + 1) by omega,
    run_add, right_step a 13 (by decide) (by decide)]
  rw [show nextPhase (13 : Fin 30) = 14 by decide]
  simp only [grownNext, focusNext, if_pos (by decide : (13 : Fin 30).val < 14)]
  rw [show 16 * (n + 1) = (n + 1) + 15 * (n + 1) by omega,
    run_add, left_step a 14 (by decide)]
  rw [show nextPhase (14 : Fin 30) = 15 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(14 : Fin 30).val < 14),
    ↓reduceIte]
  rw [show 15 * (n + 1) = (n + 1) + 14 * (n + 1) by omega,
    run_add, right_step a 15 (by decide) (by decide)]
  rw [show nextPhase (15 : Fin 30) = 16 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(15 : Fin 30).val < 14),
    if_neg (by decide : (15 : Fin 30) ≠ 14), ticks_join]
  rw [show 14 * (n + 1) = (n + 1) + 13 * (n + 1) by omega,
    run_add, left_step a 16 (by decide)]
  rw [show nextPhase (16 : Fin 30) = 17 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(16 : Fin 30).val < 14),
    if_neg (by decide : (16 : Fin 30) ≠ 14), ticks_join]
  rw [show 13 * (n + 1) = (n + 1) + 12 * (n + 1) by omega,
    run_add, right_step a 17 (by decide) (by decide)]
  rw [show nextPhase (17 : Fin 30) = 18 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(17 : Fin 30).val < 14),
    if_neg (by decide : (17 : Fin 30) ≠ 14), ticks_join]
  rw [show 12 * (n + 1) = (n + 1) + 11 * (n + 1) by omega,
    run_add, left_step a 18 (by decide)]
  rw [show nextPhase (18 : Fin 30) = 19 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(18 : Fin 30).val < 14),
    if_neg (by decide : (18 : Fin 30) ≠ 14), ticks_join]
  rw [show 11 * (n + 1) = (n + 1) + 10 * (n + 1) by omega,
    run_add, right_step a 19 (by decide) (by decide)]
  rw [show nextPhase (19 : Fin 30) = 20 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(19 : Fin 30).val < 14),
    if_neg (by decide : (19 : Fin 30) ≠ 14), ticks_join]
  rw [show 10 * (n + 1) = (n + 1) + 9 * (n + 1) by omega,
    run_add, left_step a 20 (by decide)]
  rw [show nextPhase (20 : Fin 30) = 21 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(20 : Fin 30).val < 14),
    if_neg (by decide : (20 : Fin 30) ≠ 14), ticks_join]
  rw [show 9 * (n + 1) = (n + 1) + 8 * (n + 1) by omega,
    run_add, right_step a 21 (by decide) (by decide)]
  rw [show nextPhase (21 : Fin 30) = 22 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(21 : Fin 30).val < 14),
    if_neg (by decide : (21 : Fin 30) ≠ 14), ticks_join]
  rw [show 8 * (n + 1) = (n + 1) + 7 * (n + 1) by omega,
    run_add, left_step a 22 (by decide)]
  rw [show nextPhase (22 : Fin 30) = 23 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(22 : Fin 30).val < 14),
    if_neg (by decide : (22 : Fin 30) ≠ 14), ticks_join]
  rw [show 7 * (n + 1) = (n + 1) + 6 * (n + 1) by omega,
    run_add, right_step a 23 (by decide) (by decide)]
  rw [show nextPhase (23 : Fin 30) = 24 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(23 : Fin 30).val < 14),
    if_neg (by decide : (23 : Fin 30) ≠ 14), ticks_join]
  rw [show 6 * (n + 1) = (n + 1) + 5 * (n + 1) by omega,
    run_add, left_step a 24 (by decide)]
  rw [show nextPhase (24 : Fin 30) = 25 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(24 : Fin 30).val < 14),
    if_neg (by decide : (24 : Fin 30) ≠ 14), ticks_join]
  rw [show 5 * (n + 1) = (n + 1) + 4 * (n + 1) by omega,
    run_add, right_step a 25 (by decide) (by decide)]
  rw [show nextPhase (25 : Fin 30) = 26 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(25 : Fin 30).val < 14),
    if_neg (by decide : (25 : Fin 30) ≠ 14), ticks_join]
  rw [show 4 * (n + 1) = (n + 1) + 3 * (n + 1) by omega,
    run_add, left_step a 26 (by decide)]
  rw [show nextPhase (26 : Fin 30) = 27 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(26 : Fin 30).val < 14),
    if_neg (by decide : (26 : Fin 30) ≠ 14), ticks_join]
  rw [show 3 * (n + 1) = (n + 1) + 2 * (n + 1) by omega,
    run_add, right_step a 27 (by decide) (by decide)]
  rw [show nextPhase (27 : Fin 30) = 28 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(27 : Fin 30).val < 14),
    if_neg (by decide : (27 : Fin 30) ≠ 14), ticks_join]
  rw [show 2 * (n + 1) = (n + 1) + 1 * (n + 1) by omega,
    run_add, left_step a 28 (by decide)]
  rw [show nextPhase (28 : Fin 30) = 29 by decide]
  simp only [grownNext, focusNext, if_neg (by decide : ¬(28 : Fin 30).val < 14),
    if_neg (by decide : (28 : Fin 30) ≠ 14), ticks_join]
  simp only [one_mul]
  rw [final_step]
  congr 1
  omega

/-- info: 'PalPeg.SlotClockGeneration.generation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generation

/-- Proof-side boundary data, not registers of the finite machine. -/
structure Boundary where
  active : Bool
  interior : ℕ
  junk : List Symbol
  grown : List Symbol
  focus : Symbol

def Boundary.config (b : Boundary) :=
  endpoint b.active 0 true b.interior b.junk b.grown b.focus

def Boundary.next (b : Boundary) : Boundary :=
  ⟨!b.active, 16 * (b.interior + 1) - 1, b.grown,
    List.replicate b.interior .tick ++ .edge :: b.junk, .edge⟩

def elapsed : ℕ → Boundary → ℕ
  | 0, _ => 0
  | k + 1, b => 30 * (b.interior + 1) + elapsed k b.next

theorem generations (k : ℕ) (b : Boundary) :
    run (elapsed k b) b.config = ((Boundary.next^[k]) b).config := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [elapsed, run_add]
    have hg : run (30 * (b.interior + 1)) b.config = b.next.config :=
      generation b.active b.interior b.junk b.grown b.focus
    rw [hg, ih]
    rfl

theorem interval_growth (k : ℕ) (b : Boundary) :
    ((Boundary.next^[k]) b).interior + 1 = 16 ^ k * (b.interior + 1) := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    change ((Boundary.next^[k]) b.next).interior + 1 = _
    rw [ih]
    have hn : b.next.interior + 1 = 16 * (b.interior + 1) := by
      change 16 * (b.interior + 1) - 1 + 1 = _
      omega
    rw [hn, pow_succ]
    exact (Nat.mul_assoc _ _ _).symm

/-- info: 'PalPeg.SlotClockGeneration.generations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generations
/-- info: 'PalPeg.SlotClockGeneration.interval_growth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms interval_growth

end PalPeg.SlotClockGeneration
