import PalPeg.ProgramMachine

/-! Finite right-hand blank padding is observationally irrelevant.
Left-list lengths remain exact: they determine the left boundary of a tape. -/
set_option autoImplicit false

namespace PalPeg.Program
open PegSeparation.RealTimeTM

variable {Γ Q Terminal : Type}

def RightBlankEq (blank : Γ) (xs ys : List Γ) : Prop :=
  ∀ n : ℕ, xs[n]?.getD blank = ys[n]?.getD blank

theorem RightBlankEq.cons {blank a : Γ} {xs ys : List Γ} (h : RightBlankEq blank xs ys) :
    RightBlankEq blank (a :: xs) (a :: ys) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact h n

theorem RightBlankEq.tail {blank : Γ} {xs ys : List Γ} (h : RightBlankEq blank xs ys) :
    RightBlankEq blank xs.tail ys.tail := by
  intro n
  have hn := h (n + 1)
  cases xs <;> cases ys <;> exact hn

theorem rightBlankEq_nil_replicate (blank : Γ) (N : ℕ) :
    RightBlankEq blank [] (List.replicate N blank) := by
  intro n
  cases he : (List.replicate N blank)[n]? with
  | none => rfl
  | some a =>
    have ha : a = blank := List.eq_of_mem_replicate (List.mem_of_getElem? he)
    simpa only [List.getElem?_nil, Option.getD_none, Option.getD_some] using ha.symm

theorem rightBlankEq_append_replicate (blank : Γ) (xs : List Γ) (N : ℕ) :
    RightBlankEq blank xs (xs ++ List.replicate N blank) := by
  induction xs with
  | nil => exact rightBlankEq_nil_replicate blank N
  | cons a xs ih => exact ih.cons

structure STape.BlankEq (blank : Γ) (T U : STape Γ) : Prop where
  left : T.left = U.left
  focus : T.focus = U.focus
  right : RightBlankEq blank T.right U.right

theorem STape.BlankEq.refl (blank : Γ) (T : STape Γ) : BlankEq blank T T :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem STape.BlankEq.symm {blank : Γ} {T U : STape Γ} (h : BlankEq blank T U) :
    BlankEq blank U T := ⟨h.left.symm, h.focus.symm, fun n => (h.right n).symm⟩

theorem STape.BlankEq.trans {blank : Γ} {T U V : STape Γ}
    (h : BlankEq blank T U) (g : BlankEq blank U V) : BlankEq blank T V :=
  ⟨h.left.trans g.left, h.focus.trans g.focus, fun n => (h.right n).trans (g.right n)⟩

theorem STape.BlankEq.padRight (blank : Γ) (T : STape Γ) (N : ℕ) :
    BlankEq blank T { T with right := T.right ++ List.replicate N blank } :=
  ⟨rfl, rfl, rightBlankEq_append_replicate blank T.right N⟩

/-- All writes and moves respect right-padding equivalence, including
stepping from the last represented cell into implicit blank space. -/
theorem STape.BlankEq.applyAction {blank : Γ} {T U : STape Γ} (h : BlankEq blank T U)
    (a : Γ × Move) : BlankEq blank (T.applyAction blank a) (U.applyAction blank a) := by
  obtain ⟨L, f, xs⟩ := T
  obtain ⟨L', g, ys⟩ := U
  obtain ⟨hl, _, hr⟩ := h
  change L = L' at hl
  subst L'
  obtain ⟨w, mv⟩ := a
  cases mv with
  | stay => exact ⟨rfl, rfl, hr⟩
  | left =>
    cases L with
    | nil => exact ⟨rfl, rfl, hr⟩
    | cons a L => exact ⟨rfl, rfl, hr.cons⟩
  | right =>
    have h0 := hr 0
    have ht := hr.tail
    cases xs <;> cases ys <;> exact ⟨rfl, h0, ht⟩

def ConfigBlankEq {t : ℕ} (blank : Γ) (x y : SConfig Q Γ t) : Prop :=
  x.state = y.state ∧ ∀ j, STape.BlankEq blank (x.tape j) (y.tape j)

namespace StructuredMachine
variable [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ] {t B : ℕ}

theorem microStep_blankEq (M : StructuredMachine Terminal Q Γ t B)
    {x y : SConfig Q Γ t} (h : ConfigBlankEq M.blank x y) (a : Option Terminal) :
    ConfigBlankEq M.blank (M.sMicroStep x a) (M.sMicroStep y a) := by
  obtain ⟨q, T⟩ := x
  obtain ⟨q', U⟩ := y
  obtain ⟨hq, hT⟩ := h
  change q = q' at hq
  subst q'
  have hf : (fun j => (T j).focus) = (fun j => (U j).focus) := funext fun j => (hT j).focus
  change (M.micro q a (fun j => (T j).focus)).1 = (M.micro q a (fun j => (U j).focus)).1 ∧ _
  simp only [sMicroStep, hf]
  exact ⟨trivial, fun j => (hT j).applyAction _⟩

theorem microSteps_blankEq (M : StructuredMachine Terminal Q Γ t B)
    (inputs : List (Option Terminal)) {x y : SConfig Q Γ t} (h : ConfigBlankEq M.blank x y) :
    ConfigBlankEq M.blank (inputs.foldl M.sMicroStep x) (inputs.foldl M.sMicroStep y) := by
  induction inputs generalizing x y with
  | nil => exact h
  | cons a inputs ih => exact ih (M.microStep_blankEq h a)

theorem round_blankEq (M : StructuredMachine Terminal Q Γ t B)
    {x y : SConfig Q Γ t} (h : ConfigBlankEq M.blank x y) (a : Terminal) :
    ConfigBlankEq M.blank (M.sRound x a) (M.sRound y a) :=
  M.microSteps_blankEq _ h

/-- A finite representation with extra blank cells has exactly the same
control states on every real input word as the unpadded representation. -/
theorem runFrom_blankEq (M : StructuredMachine Terminal Q Γ t B)
    (input : List Terminal) {x y : SConfig Q Γ t} (h : ConfigBlankEq M.blank x y) :
    ConfigBlankEq M.blank (input.foldl M.sRound x) (input.foldl M.sRound y) := by
  induction input generalizing x y with
  | nil => exact h
  | cons a input ih => exact ih (M.round_blankEq h a)

theorem accepting_runFrom_blankEq (M : StructuredMachine Terminal Q Γ t B)
    (input : List Terminal) {x y : SConfig Q Γ t} (h : ConfigBlankEq M.blank x y) :
    M.accepting (input.foldl M.sRound x).state = M.accepting (input.foldl M.sRound y).state :=
  congrArg M.accepting (M.runFrom_blankEq input h).1

end StructuredMachine
end PalPeg.Program
