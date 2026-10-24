import MacroPeg.CBV.SequentialStackPayload

namespace Shallot.MacroPeg.CBV.SequentialStackCode

/-! Source expressions, argument tails, and rule references in every live
task/frame remain bounded by the fixed source program. Combined with the
payload and frame-count invariants this controls every configuration field,
but is not itself an encoded-space or Turing-machine simulation theorem. -/

open SequentialStack

def TaskCode (g : MGrammar) (D : Nat) : Task → Prop
  | .expr _ _ e _ => sizeOf e ≤ D
  | .args _ _ es _ => sizeOf es ≤ D
  | .query _ i _ _ => i < g.rules.length
  | .value _ => True

def FrameCode (g : MGrammar) (D : Nat) : Frame → Prop
  | .seq _ _ b | .alt _ _ b _ => sizeOf b ≤ D
  | .star _ _ a _ => sizeOf (MExp.star a) ≤ D
  | .argHead _ _ es _ => sizeOf es ≤ D
  | .call _ i => i < g.rules.length
  | .notP _ | .argCons _ => True

def FramesCode (g : MGrammar) (D : Nat) (K : List Frame) : Prop := ∀ f ∈ K, FrameCode g D f

def ConfigCode (g : MGrammar) (D : Nat) (c : Config) : Prop :=
  TaskCode g D c.task ∧ FramesCode g D c.stack

theorem frames_cons {g : MGrammar} {D : Nat} {f : Frame} {K : List Frame}
    (hf : FrameCode g D f) (hK : FramesCode g D K) : FramesCode g D (f :: K) := by
  intro v hv
  rcases List.mem_cons.mp hv with he | hv
  · subst v; exact hf
  · exact hK v hv

theorem return_code (g : MGrammar) (x : List Char) (D : Nat) (v : SequentialStack.Value)
    (f : Frame) (K : List Frame) (next : Config)
    (hf : FrameCode g D f) (hK : FramesCode g D K)
    (hs : step g x ⟨.value v, f :: K⟩ = some next) : ConfigCode g D next := by
  cases v with
  | expr result =>
    cases f with
    | seq m E b =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some q => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨hf, hK⟩
    | alt m E b p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨hf, hK⟩
        | some q => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | notP p => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | star m E a p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some q =>
          by_cases hq : q < p
          · simp only [step, if_pos hq, Option.some.injEq] at hs; cases hs; exact ⟨hf, hK⟩
          · simp only [step, if_neg hq, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | argHead m E es p =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some q =>
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨hf, frames_cons trivial hK⟩
    | argCons _ | call _ _ => simp [step] at hs
  | args result =>
    cases f with
    | seq _ _ _ | alt _ _ _ _ | notP _ | star _ _ _ _ | argHead _ _ _ _ => simp [step] at hs
    | argCons span => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | call m i =>
      cases result with
      | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some result =>
        cases result with
        | none => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some Wq =>
          obtain ⟨W, q⟩ := Wq
          simp only [step, Option.some.injEq] at hs; cases hs
          exact ⟨hf, hK⟩

theorem step_code (g : MGrammar) (x : List Char) (D : Nat)
    (hcode : ∀ rule ∈ g.rules, sizeOf rule.body ≤ D) (c next : Config)
    (hc : ConfigCode g D c) (hs : step g x c = some next) : ConfigCode g D next := by
  obtain ⟨task, K⟩ := c
  obtain ⟨ht, hK⟩ := hc
  cases task with
  | expr m E e p =>
    cases e with
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _
    | callParam _ _ | invoke _ _ _ =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨trivial, hK⟩
    | seq a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      simp only [TaskCode, MExp.seq.sizeOf_spec] at ht
      exact ⟨by change sizeOf a ≤ D; omega, frames_cons (by change sizeOf b ≤ D; omega) hK⟩
    | alt a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      simp only [TaskCode, MExp.alt.sizeOf_spec] at ht
      exact ⟨by change sizeOf a ≤ D; omega, frames_cons (by change sizeOf b ≤ D; omega) hK⟩
    | notP a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      simp only [TaskCode, MExp.notP.sizeOf_spec] at ht
      exact ⟨by change sizeOf a ≤ D; omega, frames_cons trivial hK⟩
    | star a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨by change sizeOf a ≤ D; simp only [TaskCode, MExp.star.sizeOf_spec] at ht; omega,
        frames_cons ht hK⟩
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none => simp only [step, hr, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [step, hr, if_pos ha, Option.some.injEq] at hs; cases hs
          simp only [TaskCode, MExp.call.sizeOf_spec] at ht
          exact ⟨by change sizeOf args ≤ D; omega, frames_cons (ruleAtM_lt hr) hK⟩
        · simp only [step, hr, if_neg ha, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
  | args m E es p =>
    cases es with
    | nil => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | cons a es =>
      simp only [step, Option.some.injEq] at hs; cases hs
      simp only [TaskCode, List.cons.sizeOf_spec] at ht
      exact ⟨by change sizeOf a ≤ D; omega, frames_cons (by change sizeOf es ≤ D; omega) hK⟩
  | query m i E p =>
    cases m with
    | zero => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i with
        | none => simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some rule =>
          simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs
          exact ⟨hcode rule (ruleAtM_mem hr), hK⟩
      · simp only [step, if_neg hp, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
  | value v =>
    cases K with
    | nil => cases v <;> simp [step] at hs
    | cons f K =>
      have hf := hK f (by simp)
      have ht : FramesCode g D K := fun f hf => hK f (by simp [hf])
      exact return_code g x D v f K next hf ht hs

theorem runs_code (g : MGrammar) (x : List Char) (D : Nat)
    (hcode : ∀ rule ∈ g.rules, sizeOf rule.body ≤ D) {a b : Config}
    (h : Runs g x a b) (ha : ConfigCode g D a) : ConfigCode g D b := by
  revert ha
  induction h with
  | refl => exact fun ha => ha
  | cons hs ht ih => intro ha; exact ih (step_code g x D hcode _ _ ha hs)

noncomputable def programBudget (g : MGrammar) (e : MExp) : Nat :=
  SequentialStackRank.codeBudget g + sizeOf e

theorem reachable_code (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : ConfigCode g (programBudget g e) c := by
  have hcode : ∀ rule ∈ g.rules, sizeOf rule.body ≤ programBudget g e := by
    intro rule hr
    have hh := SequentialStackRank.codeBudget_spec g rule hr
    unfold programBudget
    omega
  apply runs_code g x (programBudget g e) hcode h
  refine ⟨?_, ?_⟩
  · change sizeOf e ≤ SequentialStackRank.codeBudget g + sizeOf e
    omega
  · intro f hf; cases hf

end Shallot.MacroPeg.CBV.SequentialStackCode
