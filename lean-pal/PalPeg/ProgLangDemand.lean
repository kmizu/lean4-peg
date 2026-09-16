import PalPeg.ProgLangControlSteps
import PalPeg.ProgLangLib

/-! A finite execution certificate which records the premises needed at
each action and guard. This is proof data for the existing interpreter,
not a second machine or a replacement for its control. -/
set_option autoImplicit false

namespace PalPeg.ProgLangDemand
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangControlSteps
variable {A C Γ Terminal : Type} {t : ℕ}

abbrev Tapes (Γ : Type) (t : ℕ) := Fin t → STape Γ

def action (I : Interp Terminal A C Γ t) (blank : Γ) (T : Tapes Γ t) (a : A) : Tapes Γ t :=
  fun j => (T j).applyAction blank (actVec I a T j)

inductive Checked (I : Interp Terminal A C Γ t) (blank : Γ)
    (okA : Tapes Γ t → A → Prop) (okC : Tapes Γ t → C → Prop) :
    Stack A C → Tapes Γ t → Tapes Γ t → Prop where
  | done (T) : Checked I blank okA okC [] T T
  | skip {s T U} (h : Checked I blank okA okC s T U) :
      Checked I blank okA okC (.skip :: s) T U
  | act {a s T U} (ha : okA T a) (h : Checked I blank okA okC s (action I blank T a) U) :
      Checked I blank okA okC (.act a :: s) T U
  | seq {p q s T U} (h : Checked I blank okA okC (p :: q :: s) T U) :
      Checked I blank okA okC (.seq p q :: s) T U
  | branch {c p q s T U} (hc : okC T c)
      (h : Checked I blank okA okC ((if evalConds I (fun j => (T j).focus) c then p else q) :: s) T U) :
      Checked I blank okA okC (.ite c p q :: s) T U
  | loop_yes {c a b s T U} (hc : okC T c)
      (he : evalConds I (fun j => (T j).focus) c = true)
      (h : Checked I blank okA okC (.act a :: b :: .loop c a b :: s) T U) :
      Checked I blank okA okC (.loop c a b :: s) T U
  | loop_no {c a b s T U} (hc : okC T c)
      (he : evalConds I (fun j => (T j).focus) c = false)
      (h : Checked I blank okA okC s T U) :
      Checked I blank okA okC (.loop c a b :: s) T U

variable {I : Interp Terminal A C Γ t} {blank : Γ}
variable {okA : Tapes Γ t → A → Prop} {okC : Tapes Γ t → C → Prop}

theorem Checked.control {s r : Stack A C} {T U : Tapes Γ t}
    (h : Checked I blank okA okC s T U)
    (hc : Control (evalConds I (fun j => (T j).focus)) s r) :
    Checked I blank okA okC r T U := by
  cases hc with
  | skip => cases h; assumption
  | seq => cases h; assumption
  | branch => cases h; assumption
  | loop_yes c a b s he => cases h <;> first | assumption | simp_all
  | loop_no c a b s he => cases h <;> first | assumption | simp_all

theorem Checked.controls {s r : Stack A C} {T U : Tapes Γ t}
    (h : Checked I blank okA okC s T U)
    (hc : Star (evalConds I (fun j => (T j).focus)) s r) :
    Checked I blank okA okC r T U := by
  induction hc with
  | refl => exact h
  | cons hc _ ih => exact ih (h.control hc)

theorem Checked.action_ready {a : A} {s : Stack A C} {T U : Tapes Γ t}
    (h : Checked I blank okA okC (.act a :: s) T U) :
    okA T a ∧ Checked I blank okA okC s (action I blank T a) U := by
  cases h with
  | act ha ht => exact ⟨ha, ht⟩

theorem Checked.branch_ready {c : C} {p q : Prog A C} {s : Stack A C} {T U : Tapes Γ t}
    (h : Checked I blank okA okC (.ite c p q :: s) T U) : okC T c := by
  cases h; assumption

theorem Checked.loop_ready {c : C} {a : A} {b : Prog A C} {s : Stack A C} {T U : Tapes Γ t}
    (h : Checked I blank okA okC (.loop c a b :: s) T U) : okC T c := by
  cases h <;> assumption

theorem Checked.append {s r : Stack A C} {T U V : Tapes Γ t}
    (h : Checked I blank okA okC s T U) (hr : Checked I blank okA okC r U V) :
    Checked I blank okA okC (s ++ r) T V := by
  induction h with
  | done => exact hr
  | skip _ ih => exact .skip (ih hr)
  | act ha _ ih => exact .act ha (ih hr)
  | seq _ ih => exact .seq (ih hr)
  | branch hc _ ih => exact .branch hc (ih hr)
  | loop_yes hc he _ ih => exact .loop_yes hc he (ih hr)
  | loop_no hc he _ ih => exact .loop_no hc he (ih hr)

theorem Checked.mono {okA' : Tapes Γ t → A → Prop} {okC' : Tapes Γ t → C → Prop}
    (ha : ∀ T a, okA T a → okA' T a) (hc : ∀ T c, okC T c → okC' T c)
    {s : Stack A C} {T U : Tapes Γ t} (h : Checked I blank okA okC s T U) :
    Checked I blank okA' okC' s T U := by
  induction h with
  | done T => exact .done T
  | skip _ ih => exact .skip ih
  | act h _ ih => exact .act (ha _ _ h) ih
  | seq _ ih => exact .seq ih
  | branch h _ ih => exact .branch (hc _ _ h) ih
  | loop_yes h he _ ih => exact .loop_yes (hc _ _ h) he ih
  | loop_no h he _ ih => exact .loop_no (hc _ _ h) he ih

def Allowed (pa : A → Prop) (pc : C → Prop) : Prog A C → Prop
  | .skip => True
  | .act a => pa a
  | .seq p q => Allowed pa pc p ∧ Allowed pa pc q
  | .ite c p q => pc c ∧ Allowed pa pc p ∧ Allowed pa pc q
  | .loop c a b => pc c ∧ pa a ∧ Allowed pa pc b

def AllowedStack (pa : A → Prop) (pc : C → Prop) : Stack A C → Prop
  | [] => True
  | p :: s => Allowed pa pc p ∧ AllowedStack pa pc s

theorem AllowedStack.control {pa : A → Prop} {pc : C → Prop} {ev : C → Bool}
    {s r : Stack A C} (hs : AllowedStack pa pc s) (h : Control ev s r) :
    AllowedStack pa pc r := by
  cases h with
  | skip => exact hs.2
  | seq => exact ⟨hs.1.1, hs.1.2, hs.2⟩
  | branch c p q s =>
    by_cases he : ev c = true
    · simpa only [if_pos he] using (show AllowedStack pa pc (p :: s) from ⟨hs.1.2.1, hs.2⟩)
    · simpa only [if_neg he] using (show AllowedStack pa pc (q :: s) from ⟨hs.1.2.2, hs.2⟩)
  | loop_yes => exact ⟨hs.1.2.1, hs.1.2.2, hs⟩
  | loop_no => exact hs.2

theorem AllowedStack.controls {pa : A → Prop} {pc : C → Prop} {ev : C → Bool}
    {s r : Stack A C} (hs : AllowedStack pa pc s) (h : Star ev s r) :
    AllowedStack pa pc r := by
  induction h with
  | refl => exact hs
  | cons h _ ih => exact ih (hs.control h)

private theorem checked_back {pa : A → Prop} {pc : C → Prop}
    (hg : ∀ T c, pc c → okC T c) {s r : Stack A C} {T U : Tapes Γ t}
    (hs : AllowedStack pa pc s) (hc : Control (evalConds I (fun j => (T j).focus)) s r)
    (h : Checked I blank okA okC r T U) : Checked I blank okA okC s T U := by
  cases hc with
  | skip => exact .skip h
  | seq => exact .seq h
  | branch c p q s => exact .branch (hg T c hs.1.1) h
  | loop_yes c a b s he => exact .loop_yes (hg T c hs.1.1) he h
  | loop_no c a b s he => exact .loop_no (hg T c hs.1.1) he h

private theorem checked_backs {pa : A → Prop} {pc : C → Prop}
    (hg : ∀ T c, pc c → okC T c) {s r : Stack A C} {T U : Tapes Γ t}
    (hs : AllowedStack pa pc s) (hc : Star (evalConds I (fun j => (T j).focus)) s r)
    (h : Checked I blank okA okC r T U) : Checked I blank okA okC s T U := by
  induction hc with
  | refl => exact h
  | cons hc _ ih => exact checked_back hg hs hc (ih (hs.control hc) h)

/-- Consume a budget on the actual remaining action trace. Unlike an
endpoint-only bound, this permits left moves and therefore also certifies
the GS reset chain without any monotonicity premise on its text heads. -/
theorem checked_of_run_budget {pa : A → Prop} {pc : C → Prop}
    {budget : Tapes Γ t → List (Fin t → Γ × Move) → Prop}
    (ha : ∀ T a as, pa a → budget T (actVec I a T :: as) →
      okA T a ∧ budget (action I blank T a) as)
    (hc : ∀ T c, pc c → okC T c)
    (N : ℕ) {s r : Stack A C} {T U : Tapes Γ t}
    (hr : runInputs I blank (List.replicate N none) (s, T) = (r, U))
    (hh : SEqAt I U r []) (hs : AllowedStack pa pc s)
    (hb : budget T (trace I blank (List.replicate N none) (s, T))) :
    Checked I blank okA okC s T U := by
  induction N generalizing s r T with
  | zero =>
    simp only [List.replicate_zero, runInputs_nil, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact checked_backs hc hs
      (halted_path _ _ (by simpa only [stepStack_nil] using congrArg Prod.snd hh)) (.done _)
  | succ N ih =>
    rw [List.replicate_succ, runInputs_cons] at hr
    rcases hd : stepStack (evalConds I (fun j => (T j).focus)) s with ⟨q, o⟩
    cases o with
    | some a =>
      have hp := selected_path _ _ _ _ hd
      have hs' := hs.controls hp
      have hb' : budget T (actVec I a T :: trace I blank (List.replicate N none) (q, action I blank T a)) := by
        change budget T (actVec I a T :: trace I blank (List.replicate N none)
          (q, fun j => (T j).applyAction blank (I.actOf a none (fun j => (T j).focus) j)))
        simpa only [List.replicate_succ, trace_cons, hd, microStep, List.singleton_append, actVec] using hb
      obtain ⟨har, hb''⟩ := ha T a _ hs'.1 hb'
      have ht : Checked I blank okA okC q (action I blank T a) U := by
        apply ih (s := q) (T := action I blank T a) (hh := hh) (hs := hs'.2) (hb := hb'')
        change runInputs I blank (List.replicate N none)
          (q, fun j => (T j).applyAction blank (I.actOf a none (fun j => (T j).focus) j)) = (r, U)
        simpa only [microStep, hd] using hr
      exact checked_backs hc hs hp (.act har ht)
    | none =>
      have hn : (stepStack (evalConds I (fun j => (T j).focus)) s).2 = none := by rw [hd]
      have hq : q = [] := by simpa only [hd] using stepStack_snd_eq_none _ _ hn
      subst q
      simp only [microStep, hd, runInputs_halted, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      exact checked_backs hc hs (halted_path _ _ hn) (.done _)

theorem checked_of_exec_budget {pa : A → Prop} {pc : C → Prop}
    {budget : Tapes Γ t → List (Fin t → Γ × Move) → Prop}
    (ha : ∀ T a as, pa a → budget T (actVec I a T :: as) →
      okA T a ∧ budget (action I blank T a) as)
    (hc : ∀ T c, pc c → okC T c)
    {p : Prog A C} {T : Tapes Γ t} {as : List (Fin t → Γ × Move)}
    (he : Exec I blank p T as) (hs : Allowed pa pc p) (hb : budget T as) :
    Checked I blank okA okC [p] T (applyTrace blank T as) := by
  obtain ⟨heq, s, hr, hh⟩ := he [] (List.replicate as.length none) (by simp)
  simp only [List.append_nil] at hr heq
  exact checked_of_run_budget ha hc as.length hr hh ⟨hs, trivial⟩ (by rw [heq]; exact hb)

end PalPeg.ProgLangDemand
