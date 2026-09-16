import PalPeg.ProgLang

/-! Exact source execution across changing observations. A blocked loop
retains its continuation; release selects the following action immediately. -/
set_option autoImplicit false

namespace PalPeg.ProgLangWait
open PalPeg.ProgLang
variable {A C : Type}

def observe : List (C → Bool) → Stack A C → Stack A C × List (Option A)
  | [], s => (s, [])
  | ev :: es, s =>
    let t := stepStack ev s
    let u := observe es t.1
    (u.1, t.2 :: u.2)

theorem observe_cons (ev : C → Bool) (es : List (C → Bool)) (s : Stack A C) :
    observe (ev :: es) s =
      ((observe es (stepStack ev s).1).1, (stepStack ev s).2 :: (observe es (stepStack ev s).1).2) := rfl

/-- Observationally equal source stacks stay equal after any nonempty
sequence, even when every call reads a different tape observation. -/
theorem observe_congr {s t : Stack A C}
    (h : ∀ ev, stepStack ev s = stepStack ev t)
    (ev : C → Bool) (es : List (C → Bool)) :
    observe (ev :: es) s = observe (ev :: es) t := by
  simp only [observe_cons, h]

theorem observe_append (xs ys : List (C → Bool)) (s : Stack A C) :
    observe (xs ++ ys) s =
      ((observe ys (observe xs s).1).1, (observe xs s).2 ++ (observe ys (observe xs s).1).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons ev xs ih => simp [observe, ih]

theorem observe_nonempty_congr {s t : Stack A C}
    (h : ∀ ev, stepStack ev s = stepStack ev t)
    (xs : List (C → Bool)) (hx : xs ≠ []) : observe xs s = observe xs t := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons ev es => exact observe_congr h ev es

theorem wait_release_to (c : C) (w : A) (s : Stack A C)
    (xs : List (C → Bool)) (last : C → Bool)
    (hw : ∀ ev ∈ xs, ev c = true) (hl : last c = false) :
    observe (xs ++ [last]) (.loop c w .skip :: s) =
      ((stepStack last s).1, List.replicate xs.length (some w) ++ [(stepStack last s).2]) := by
  induction xs with
  | nil => simp [observe, hl]
  | cons ev xs ih =>
    have he := hw ev (by simp)
    have ht : ∀ e ∈ xs, e c = true := fun e hm => hw e (by simp [hm])
    have hs := observe_nonempty_congr (fun e => stepStack_skip e (.loop c w .skip :: s))
      (xs ++ [last]) (by simp)
    simp only [List.cons_append, observe_cons, stepStack_loop, he, if_true]
    rw [hs, ih ht]
    simp [List.replicate_succ]

/-- Every supplied observation except the last still sees the wait guard.
The last observation releases it and emits the pending action. No fairness
or future-input assumption is hidden in this finite-prefix statement. -/
theorem wait_release (c : C) (w a : A) (s : Stack A C)
    (xs : List (C → Bool)) (last : C → Bool)
    (hw : ∀ ev ∈ xs, ev c = true) (hl : last c = false) :
    observe (xs ++ [last]) (.loop c w .skip :: .act a :: s) =
      (s, List.replicate xs.length (some w) ++ [some a]) := by
  induction xs with
  | nil => simp [observe, hl]
  | cons ev xs ih =>
    have he := hw ev (by simp)
    have ht : ∀ e ∈ xs, e c = true := fun e hm => hw e (by simp [hm])
    have hs : observe (xs ++ [last]) (.skip :: .loop c w .skip :: .act a :: s) =
        observe (xs ++ [last]) (.loop c w .skip :: .act a :: s) := by
      cases xs with
      | nil => exact observe_congr (fun e => stepStack_skip e _) last []
      | cons e es => exact observe_congr (fun e => stepStack_skip e _) e (es ++ [last])
    simp only [List.cons_append, observe_cons, stepStack_loop, he, if_true]
    rw [hs, ih ht]
    simp [List.replicate_succ]

/-- info: 'PalPeg.ProgLangWait.wait_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wait_release

end PalPeg.ProgLangWait
