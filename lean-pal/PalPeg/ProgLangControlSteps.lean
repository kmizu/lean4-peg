import PalPeg.ProgLang
import PalPeg.ProgLangWait

/-! Expose pure control transitions without changing the existing source
semantics. In particular a loop may commit its guard while its mandatory
action remains pending. Dispatch equivalence is proved, not postulated. -/
set_option autoImplicit false

namespace PalPeg.ProgLangControlSteps
open PalPeg.ProgLang
variable {A C : Type}

inductive Control (ev : C → Bool) : Stack A C → Stack A C → Prop where
  | skip (s) : Control ev (.skip :: s) s
  | seq (p q s) : Control ev (.seq p q :: s) (p :: q :: s)
  | branch (c p q s) : Control ev (.ite c p q :: s) ((if ev c then p else q) :: s)
  | loop_yes (c a b s) (h : ev c = true) :
      Control ev (.loop c a b :: s) (.act a :: b :: .loop c a b :: s)
  | loop_no (c a b s) (h : ev c = false) : Control ev (.loop c a b :: s) s

inductive Star (ev : C → Bool) : Stack A C → Stack A C → Prop where
  | refl (s) : Star ev s s
  | cons {s t u} (h : Control ev s t) (hs : Star ev t u) : Star ev s u

theorem Star.single {ev : C → Bool} {s t : Stack A C} (h : Control ev s t) : Star ev s t :=
  .cons h (.refl t)

theorem Star.trans {ev : C → Bool} {s t u : Stack A C}
    (h : Star ev s t) (hu : Star ev t u) : Star ev s u := by
  induction h with
  | refl => exact hu
  | cons h _ ih => exact .cons h (ih hu)

theorem Control.dispatch {ev : C → Bool} {s t : Stack A C} (h : Control ev s t) :
    stepStack ev s = stepStack ev t := by
  cases h with
  | skip => exact stepStack_skip ev _
  | seq p q s => exact stepStack_seq ev p q s
  | branch c p q s => exact stepStack_ite ev c p q s
  | loop_yes c a b s hc => simp [hc]
  | loop_no c a b s hc => simp [hc]

theorem Star.dispatch {ev : C → Bool} {s t : Stack A C} (h : Star ev s t) :
    stepStack ev s = stepStack ev t := by
  induction h with
  | refl => rfl
  | cons h _ ih => exact h.dispatch.trans ih

theorem Control.append {ev : C → Bool} {s t : Stack A C}
    (h : Control ev s t) (r : Stack A C) : Control ev (s ++ r) (t ++ r) := by
  cases h with
  | skip => exact .skip _
  | seq p q s => exact .seq p q (s ++ r)
  | branch c p q s => exact .branch c p q (s ++ r)
  | loop_yes c a b s hc => exact .loop_yes c a b (s ++ r) hc
  | loop_no c a b _ hc => exact .loop_no c a b _ hc

theorem Star.append {ev : C → Bool} {s t : Stack A C}
    (h : Star ev s t) (r : Stack A C) : Star ev (s ++ r) (t ++ r) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (h.append r) ih

theorem selected_path (ev : C → Bool) (s : Stack A C) (a : A) (t : Stack A C)
    (h : stepStack ev s = (t, some a)) : Star ev s (.act a :: t) := by
  induction s using stepStack.induct (ev := ev) with
  | case1 => simp at h
  | case2 r ih => exact .cons (.skip r) (ih (by simpa using h))
  | case3 b r =>
    simp only [stepStack_act, Prod.mk.injEq, Option.some.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact .refl _
  | case4 p q r ih => exact .cons (.seq p q r) (ih (by simpa using h))
  | case5 c p q r ih => exact .cons (.branch c p q r) (ih (by simpa using h))
  | case6 c b p r hc =>
    simp only [stepStack_loop, hc, if_true, Prod.mk.injEq, Option.some.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact Star.single (.loop_yes c _ p r hc)
  | case7 c b p r hc ih =>
    exact .cons (.loop_no c b p r (Bool.eq_false_iff.mpr hc)) (ih (by simpa [hc] using h))

/-- Every finite pure-control derivation to an action is exactly one
existing stepStack dispatch, including the exact remaining stack. -/
theorem selected_iff (ev : C → Bool) (s : Stack A C) (a : A) (t : Stack A C) :
    stepStack ev s = (t, some a) ↔ Star ev s (.act a :: t) := by
  constructor
  · exact selected_path ev s a t
  · intro h
    exact h.dispatch.trans (stepStack_act ev a t)

theorem dispatch_append (ev : C → Bool) (s t r : Stack A C) (a : A)
    (h : stepStack ev s = (t, some a)) : stepStack ev (s ++ r) = (t ++ r, some a) :=
  (selected_iff ev (s ++ r) a (t ++ r)).mpr ((selected_path ev s a t h).append r)

theorem halted_path (ev : C → Bool) (s : Stack A C)
    (h : (stepStack ev s).2 = none) : Star ev s [] := by
  induction s using stepStack.induct (ev := ev) with
  | case1 => exact .refl _
  | case2 r ih => exact .cons (.skip r) (ih (by simpa using h))
  | case3 b r => simp at h
  | case4 p q r ih => exact .cons (.seq p q r) (ih (by simpa using h))
  | case5 c p q r ih => exact .cons (.branch c p q r) (ih (by simpa using h))
  | case6 c b p r hc => simp [hc] at h
  | case7 c b p r hc ih =>
    exact .cons (.loop_no c b p r (Bool.eq_false_iff.mpr hc)) (ih (by simpa [hc] using h))

theorem halted_iff (ev : C → Bool) (s : Stack A C) :
    (stepStack ev s).2 = none ↔ Star ev s [] := by
  constructor
  · exact halted_path ev s
  · intro h
    rw [h.dispatch, stepStack_nil]

inductive Trace : List (C → Bool) → Stack A C → Stack A C → List (Option A) → Prop where
  | nil (s) : Trace [] s s []
  | emit {ev es s t u a as}
      (h : Star ev s (.act a :: t)) (ht : Trace es t u as) :
      Trace (ev :: es) s u (some a :: as)
  | halt {ev es s u as} (h : Star ev s []) (ht : Trace es [] u as) :
      Trace (ev :: es) s u (none :: as)

theorem Trace.observe {es : List (C → Bool)} {s t : Stack A C} {as : List (Option A)}
    (h : Trace es s t as) : ProgLangWait.observe es s = (t, as) := by
  induction h with
  | nil => rfl
  | emit h _ ih =>
    rw [ProgLangWait.observe_cons, h.dispatch, stepStack_act, ih]
  | halt h _ ih =>
    rw [ProgLangWait.observe_cons, h.dispatch, stepStack_nil, ih]

theorem trace_observe (es : List (C → Bool)) (s : Stack A C) :
    Trace es s (ProgLangWait.observe es s).1 (ProgLangWait.observe es s).2 := by
  induction es generalizing s with
  | nil => exact .nil s
  | cons ev es ih =>
    rcases he : stepStack ev s with ⟨t, o⟩
    cases o with
    | some a =>
      simp only [ProgLangWait.observe_cons, he]
      exact .emit (selected_path ev s a t he) (ih t)
    | none =>
      have hn : (stepStack ev s).2 = none := by rw [he]
      have ht : t = [] := by simpa only [he] using stepStack_snd_eq_none ev s hn
      subst t
      simp only [ProgLangWait.observe_cons, he]
      exact .halt (halted_path ev s hn) (ih [])

/-- The exposed control-path semantics describes precisely all finite
executions of the existing source interpreter, with the same labels. -/
theorem trace_iff (es : List (C → Bool)) (s t : Stack A C) (as : List (Option A)) :
    Trace es s t as ↔ ProgLangWait.observe es s = (t, as) := by
  constructor
  · exact Trace.observe
  · intro h
    have ht := trace_observe es s
    simpa only [h] using ht

/-- info: 'PalPeg.ProgLangControlSteps.selected_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms selected_iff

/-- info: 'PalPeg.ProgLangControlSteps.trace_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_iff

end PalPeg.ProgLangControlSteps
