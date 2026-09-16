import PalPeg.SlotClock

/-! Arbitrary-length sweeps of the concrete two-microstep clock. -/
set_option autoImplicit false
namespace PalPeg.SlotClockSweep
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.SlotClock

theorem round_plain (active : Bool) (p : Fin 30) (hp : p ≠ 29)
    (T : Fin 2 → STape Symbol) :
    machine.sRound ⟨((active, p), 0), T⟩ () =
      ⟨((active, if (moved (active, p) T (slot active)).focus = .edge then nextPhase p else p), 0),
        moved (active, p) T⟩ := by
  by_cases he : (moved (active, p) T (slot active)).focus = .edge
  all_goals simp only [round, roundState, finish, hp, he, ↓reduceIte]
  all_goals congr 1

theorem moved_active (active : Bool) (p : Fin 30) (T : Fin 2 → STape Symbol) :
    moved (active, p) T (slot active) =
      (T (slot active)).applyAction .blank
        ((T (slot active)).focus, if p.val % 2 = 0 then .left else .right) := by
  simp only [moved, advance, ↓reduceIte]

def run (N : ℕ) (x : SConfig (Ctrl × Fin 2) Symbol 2) :=
  (List.replicate N ()).foldl machine.sRound x

theorem run_succ (N : ℕ) (x : SConfig (Ctrl × Fin 2) Symbol 2) :
    run (N + 1) x = run N (machine.sRound x ()) := rfl

theorem run_add (M N : ℕ) (x : SConfig (Ctrl × Fin 2) Symbol 2) :
    run (M + N) x = run N (run M x) := by
  simp only [run, List.replicate_add, List.foldl_append]

theorem sweep_left (active : Bool) (p : Fin 30) (heven : p.val % 2 = 0)
    (n : ℕ) (junk right : List Symbol) (s : Symbol) (T : Fin 2 → STape Symbol)
    (hT : T (slot active) = ⟨List.replicate n .tick ++ .edge :: junk, s, right⟩) :
    let y := run (n + 1) ⟨((active, p), 0), T⟩
    y.state = ((active, nextPhase p), 0) ∧
      y.tape (slot active) = ⟨junk, .edge, List.replicate n .tick ++ s :: right⟩ := by
  have hp : p ≠ 29 := by intro hh; subst p; contradiction
  induction n generalizing s right T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    have ht : moved (active, p) T (slot active) = ⟨junk, .edge, s :: right⟩ := by
      rw [moved_active, hT]
      simp only [List.replicate_zero, List.nil_append, heven, ↓reduceIte, STape.applyAction]
    simp only [ht, ↓reduceIte, run, List.replicate_zero, List.foldl_nil,
      List.nil_append]
    exact ⟨trivial, trivial⟩
  | succ n ih =>
    rw [run_succ, round_plain active p hp]
    have ht : moved (active, p) T (slot active) =
        ⟨List.replicate n .tick ++ .edge :: junk, .tick, s :: right⟩ := by
      rw [moved_active, hT]
      simp only [List.replicate_succ, List.cons_append, heven, ↓reduceIte, STape.applyAction]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    have hh := ih (s :: right) .tick (moved (active, p) T) ht
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hh

theorem sweep_right (active : Bool) (p : Fin 30) (hodd : p.val % 2 ≠ 0) (hp : p ≠ 29)
    (n : ℕ) (left junk : List Symbol) (s : Symbol) (T : Fin 2 → STape Symbol)
    (hT : T (slot active) = ⟨left, s, List.replicate n .tick ++ .edge :: junk⟩) :
    let y := run (n + 1) ⟨((active, p), 0), T⟩
    y.state = ((active, nextPhase p), 0) ∧
      y.tape (slot active) = ⟨List.replicate n .tick ++ s :: left, .edge, junk⟩ := by
  induction n generalizing s left T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    have ht : moved (active, p) T (slot active) = ⟨s :: left, .edge, junk⟩ := by
      rw [moved_active, hT]
      simp only [List.replicate_zero, List.nil_append, if_neg hodd, STape.applyAction]
    simp only [ht, ↓reduceIte, run, List.replicate_zero, List.foldl_nil, List.nil_append]
    exact ⟨trivial, trivial⟩
  | succ n ih =>
    rw [run_succ, round_plain active p hp]
    have ht : moved (active, p) T (slot active) =
        ⟨s :: left, .tick, List.replicate n .tick ++ .edge :: junk⟩ := by
      rw [moved_active, hT]
      simp only [List.replicate_succ, List.cons_append, if_neg hodd, STape.applyAction]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    have hh := ih (s :: left) .tick (moved (active, p) T) ht
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using hh

theorem growing_round (active : Bool) (p : Fin 30) (hg : 14 ≤ p.val) (hp : p ≠ 29)
    (T : Fin 2 → STape Symbol) (l : List Symbol) (s : Symbol)
    (hT : T (slot (!active)) = ⟨l, s, []⟩) :
    (machine.sRound ⟨((active, p), 0), T⟩ ()).tape (slot (!active)) =
      ⟨(if p = 14 ∧ (T (slot active)).focus = .edge then .edge else .tick) :: l, .blank, []⟩ := by
  rw [round_plain active p hp]
  have hn : slot (!active) ≠ slot active := by cases active <;> decide
  change (T (slot (!active))).applyAction .blank
    (advance (active, p) (fun j => (T j).focus) (slot (!active))) = _
  simp only [advance, hn, ↓reduceIte, hg, hT, STape.applyAction]

theorem idle_round (active : Bool) (p : Fin 30) (hg : p.val < 14)
    (T : Fin 2 → STape Symbol) :
    (machine.sRound ⟨((active, p), 0), T⟩ ()).tape (slot (!active)) = T (slot (!active)) := by
  have hp : p ≠ 29 := by intro he; subst p; contradiction
  rw [round_plain active p hp]
  have hn : slot (!active) ≠ slot active := by cases active <;> decide
  change (T (slot (!active))).applyAction .blank
    (advance (active, p) (fun j => (T j).focus) (slot (!active))) = _
  simp only [advance, hn, ↓reduceIte, if_neg (by omega : ¬14 ≤ p.val)]
  rfl

theorem moved_idle (active : Bool) (p : Fin 30) (hg : p.val < 14)
    (T : Fin 2 → STape Symbol) :
    moved (active, p) T (slot (!active)) = T (slot (!active)) := by
  have hn : slot (!active) ≠ slot active := by cases active <;> decide
  simp only [moved, advance, hn, ↓reduceIte, if_neg (by omega : ¬14 ≤ p.val)]
  rfl

theorem idle_left (active : Bool) (p : Fin 30) (heven : p.val % 2 = 0)
    (hg : p.val < 14) (n : ℕ) (junk right : List Symbol) (s : Symbol)
    (T : Fin 2 → STape Symbol)
    (ha : T (slot active) = ⟨List.replicate n .tick ++ .edge :: junk, s, right⟩) :
    (run (n + 1) ⟨((active, p), 0), T⟩).tape (slot (!active)) = T (slot (!active)) := by
  have hp : p ≠ 29 := by intro hh; subst p; contradiction
  induction n generalizing right s T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    exact moved_idle active p hg T
  | succ n ih =>
    have ht : moved (active, p) T (slot active) =
        ⟨List.replicate n .tick ++ .edge :: junk, .tick, s :: right⟩ := by
      rw [moved_active, ha]
      simp only [List.replicate_succ, List.cons_append, heven, ↓reduceIte, STape.applyAction]
    rw [run_succ, round_plain active p hp]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    exact (ih (s :: right) .tick (moved (active, p) T) ht).trans (moved_idle active p hg T)

theorem idle_right (active : Bool) (p : Fin 30) (hodd : p.val % 2 ≠ 0)
    (hg : p.val < 14) (n : ℕ) (left junk : List Symbol) (s : Symbol)
    (T : Fin 2 → STape Symbol)
    (ha : T (slot active) = ⟨left, s, List.replicate n .tick ++ .edge :: junk⟩) :
    (run (n + 1) ⟨((active, p), 0), T⟩).tape (slot (!active)) = T (slot (!active)) := by
  have hp : p ≠ 29 := by intro hh; subst p; contradiction
  induction n generalizing left s T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    exact moved_idle active p hg T
  | succ n ih =>
    have ht : moved (active, p) T (slot active) =
        ⟨s :: left, .tick, List.replicate n .tick ++ .edge :: junk⟩ := by
      rw [moved_active, ha]
      simp only [List.replicate_succ, List.cons_append, if_neg hodd, STape.applyAction]
    rw [run_succ, round_plain active p hp]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    exact (ih (s :: left) .tick (moved (active, p) T) ht).trans (moved_idle active p hg T)

theorem moved_growing (active : Bool) (p : Fin 30) (hg : 14 ≤ p.val)
    (T : Fin 2 → STape Symbol) (l : List Symbol) (s : Symbol)
    (hT : T (slot (!active)) = ⟨l, s, []⟩) :
    moved (active, p) T (slot (!active)) =
      ⟨(if p = 14 ∧ (T (slot active)).focus = .edge then .edge else .tick) :: l, .blank, []⟩ := by
  have hn : slot (!active) ≠ slot active := by cases active <;> decide
  simp only [moved, advance, hn, ↓reduceIte, hg, hT, STape.applyAction]

theorem grow_left (active : Bool) (p : Fin 30) (heven : p.val % 2 = 0)
    (hg : 14 ≤ p.val) (n : ℕ) (junk right grown : List Symbol) (s u : Symbol)
    (T : Fin 2 → STape Symbol)
    (ha : T (slot active) = ⟨List.replicate n .tick ++ .edge :: junk, s, right⟩)
    (hb : T (slot (!active)) = ⟨grown, u, []⟩) :
    (run (n + 1) ⟨((active, p), 0), T⟩).tape (slot (!active)) =
      ⟨List.replicate n .tick ++
        (if p = 14 ∧ s = .edge then .edge else .tick) :: grown, .blank, []⟩ := by
  have hp : p ≠ 29 := by intro hh; subst p; contradiction
  induction n generalizing right grown s u T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    simpa only [run, List.replicate_zero, List.foldl_nil, List.nil_append, ha] using
      moved_growing active p hg T grown u hb
  | succ n ih =>
    have ht : moved (active, p) T (slot active) =
        ⟨List.replicate n .tick ++ .edge :: junk, .tick, s :: right⟩ := by
      rw [moved_active, ha]
      simp only [List.replicate_succ, List.cons_append, heven, ↓reduceIte, STape.applyAction]
    have hu := moved_growing active p hg T grown u hb
    simp only [ha] at hu
    rw [run_succ, round_plain active p hp]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    have hh := ih (s :: right)
      ((if p = 14 ∧ s = .edge then .edge else .tick) :: grown)
      .tick .blank (moved (active, p) T) ht hu
    simpa only [show Symbol.tick ≠ Symbol.edge by decide, and_false, ↓reduceIte,
      List.replicate_succ', List.append_assoc, List.singleton_append] using hh

theorem grow_right (active : Bool) (p : Fin 30) (hodd : p.val % 2 ≠ 0)
    (hg : 14 < p.val) (hp : p ≠ 29) (n : ℕ) (left junk grown : List Symbol)
    (s u : Symbol) (T : Fin 2 → STape Symbol)
    (ha : T (slot active) = ⟨left, s, List.replicate n .tick ++ .edge :: junk⟩)
    (hb : T (slot (!active)) = ⟨grown, u, []⟩) :
    (run (n + 1) ⟨((active, p), 0), T⟩).tape (slot (!active)) =
      ⟨List.replicate (n + 1) .tick ++ grown, .blank, []⟩ := by
  have h14 : p ≠ 14 := by intro hh; subst p; contradiction
  induction n generalizing left grown s u T with
  | zero =>
    rw [run_succ, round_plain active p hp]
    simpa only [run, List.replicate_zero, List.foldl_nil, List.replicate_succ,
      List.cons_append, List.nil_append, h14, false_and, ↓reduceIte] using
      moved_growing active p (by omega) T grown u hb
  | succ n ih =>
    have ht : moved (active, p) T (slot active) =
        ⟨s :: left, .tick, List.replicate n .tick ++ .edge :: junk⟩ := by
      rw [moved_active, ha]
      simp only [List.replicate_succ, List.cons_append, if_neg hodd, STape.applyAction]
    have hu := moved_growing active p (by omega) T grown u hb
    simp only [h14, false_and, ↓reduceIte] at hu
    rw [run_succ, round_plain active p hp]
    simp only [ht, if_neg (by decide : Symbol.tick ≠ Symbol.edge)]
    have hh := ih (s :: left) (.tick :: grown) .tick .blank (moved (active, p) T) ht hu
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using hh

theorem round_nonedge (active : Bool) (p : Fin 30) (T : Fin 2 → STape Symbol)
    (he : (moved (active, p) T (slot active)).focus ≠ .edge) :
    machine.sRound ⟨((active, p), 0), T⟩ () = ⟨((active, p), 0), moved (active, p) T⟩ := by
  simp only [round, roundState, finish, he, ↓reduceIte]
  congr 1

/-- The entire last sweep, including role exchange, for any interval length.
The growing tape may retain arbitrary historical cells to its left. -/
theorem final_sweep (active : Bool) (n : ℕ) (left grown : List Symbol)
    (s u : Symbol) (T : Fin 2 → STape Symbol)
    (ha : T (slot active) = ⟨left, s, List.replicate n .tick ++ [.edge]⟩)
    (hb : T (slot (!active)) = ⟨grown, u, []⟩) :
    let y := run (n + 1) ⟨((active, 29), 0), T⟩
    y.state = ((!active, 0), 0) ∧
      y.tape (slot active) = ⟨List.replicate n .tick ++ s :: left, .edge, []⟩ ∧
      y.tape (slot (!active)) = ⟨List.replicate (n + 1) .tick ++ grown, .edge, []⟩ := by
  induction n generalizing left grown s u T with
  | zero =>
    rw [run_succ]
    simp only [run, List.replicate_zero, List.foldl_nil, List.nil_append] at *
    cases active <;>
      simp_all [round, roundState, moved, advance, finish, slot, STape.applyAction,
        List.replicate_succ]
  | succ n ih =>
    have hm : moved (active, 29) T (slot active) =
        ⟨s :: left, .tick, List.replicate n .tick ++ [.edge]⟩ := by
      rw [moved_active, ha]
      simp [STape.applyAction, List.replicate_succ]
    have hn : slot (!active) ≠ slot active := by cases active <;> decide
    have hg : moved (active, 29) T (slot (!active)) = ⟨.tick :: grown, .blank, []⟩ := by
      simp [moved, advance, hn, hb, STape.applyAction]
    rw [run_succ, round_nonedge active 29 T (by rw [hm]; exact (by decide : Symbol.tick ≠ Symbol.edge))]
    have hh := ih (s :: left) (.tick :: grown) .tick .blank (moved (active, 29) T) hm hg
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using hh

/-- info: 'PalPeg.SlotClockSweep.final_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms final_sweep

/-- info: 'PalPeg.SlotClockSweep.grow_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grow_left
/-- info: 'PalPeg.SlotClockSweep.grow_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grow_right
/-- info: 'PalPeg.SlotClockSweep.idle_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_left
/-- info: 'PalPeg.SlotClockSweep.idle_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idle_right

/-- info: 'PalPeg.SlotClockSweep.sweep_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sweep_left
/-- info: 'PalPeg.SlotClockSweep.sweep_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sweep_right
end PalPeg.SlotClockSweep
