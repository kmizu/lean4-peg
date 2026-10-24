import MacroPeg.CBV.SequentialStackCode
import MacroPeg.CBVtoCBN.CompilerAvailability
import MacroPeg.CBV.Indexed

namespace Shallot.MacroPeg.CBV.SequentialStackPool

open SequentialStack CBVtoCBN

def ExprOK (nodes : List CompileNode) (e : MExp) : Prop := ∃ a, ExprAvailable nodes a e
def ArgsOK (nodes : List CompileNode) (es : List MExp) : Prop := ∃ a, ArgsAvailable nodes a es

theorem ExprOK.seq {ns a b} (h : ExprOK ns (.seq a b)) : ExprOK ns a ∧ ExprOK ns b := by
  obtain ⟨arity, h⟩ := h
  exact ⟨⟨arity, h.seq.1⟩, ⟨arity, h.seq.2⟩⟩
theorem ExprOK.alt {ns a b} (h : ExprOK ns (.alt a b)) : ExprOK ns a ∧ ExprOK ns b := by
  obtain ⟨arity, h⟩ := h
  exact ⟨⟨arity, h.alt.1⟩, ⟨arity, h.alt.2⟩⟩
theorem ExprOK.star {ns a} (h : ExprOK ns (.star a)) : ExprOK ns a := by
  obtain ⟨arity, h⟩ := h; exact ⟨arity, h.star⟩
theorem ExprOK.notP {ns a} (h : ExprOK ns (.notP a)) : ExprOK ns a := by
  obtain ⟨arity, h⟩ := h; exact ⟨arity, h.notP⟩
theorem ExprOK.call {ns i es} (h : ExprOK ns (.call i es)) : ArgsOK ns es := by
  obtain ⟨arity, h⟩ := h; exact ⟨arity, h.call.1⟩
theorem ArgsOK.cons {ns a es} (h : ArgsOK ns (a :: es)) : ExprOK ns a ∧ ArgsOK ns es := by
  obtain ⟨arity, h⟩ := h
  exact ⟨⟨arity, h.cons.1⟩, ⟨arity, h.cons.2⟩⟩

def TaskOK (nodes : List CompileNode) : Task → Prop
  | .expr _ _ e _ => ExprOK nodes e
  | .args _ _ es _ => ArgsOK nodes es
  | .query _ _ _ _ | .value _ => True

def FrameOK (nodes : List CompileNode) : Frame → Prop
  | .seq _ _ b | .alt _ _ b _ => ExprOK nodes b
  | .star _ _ a _ => ExprOK nodes (.star a)
  | .argHead _ _ es _ => ArgsOK nodes es
  | .notP _ | .argCons _ | .call _ _ => True

def FramesOK (nodes : List CompileNode) (K : List Frame) : Prop := ∀ f ∈ K, FrameOK nodes f
def ConfigOK (nodes : List CompileNode) (c : Config) : Prop := TaskOK nodes c.task ∧ FramesOK nodes c.stack

theorem frames_cons {ns f K} (hf : FrameOK ns f) (hK : FramesOK ns K) : FramesOK ns (f :: K) := by
  intro v hv
  rcases List.mem_cons.mp hv with he | hv
  · subst v; exact hf
  · exact hK v hv

theorem return_ok (g : MGrammar) (x : List Char) (ns : List CompileNode)
    (v : SequentialStack.Value) (f : Frame) (K : List Frame) (next : Config)
    (hf : FrameOK ns f) (hK : FramesOK ns K)
    (hs : step g x ⟨.value v, f :: K⟩ = some next) : ConfigOK ns next := by
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
          exact ⟨trivial, hK⟩

theorem step_ok (g : MGrammar) (x : List Char) (start : MExp) (c next : Config)
    (hc : ConfigOK (compilerNodes g start) c) (hs : step g x c = some next) :
    ConfigOK (compilerNodes g start) next := by
  obtain ⟨task, K⟩ := c
  obtain ⟨ht, hK⟩ := hc
  cases task with
  | expr m E e p =>
    cases e with
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _
    | callParam _ _ | invoke _ _ _ =>
      simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | seq a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨ht.seq.1, frames_cons ht.seq.2 hK⟩
    | alt a b =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨ht.alt.1, frames_cons ht.alt.2 hK⟩
    | notP a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨ht.notP, frames_cons trivial hK⟩
    | star a =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨ht.star, frames_cons ht hK⟩
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none => simp only [step, hr, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [step, hr, if_pos ha, Option.some.injEq] at hs; cases hs
          exact ⟨ht.call, frames_cons trivial hK⟩
        · simp only [step, hr, if_neg ha, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
  | args m E es p =>
    cases es with
    | nil => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | cons a es =>
      simp only [step, Option.some.injEq] at hs; cases hs
      exact ⟨ht.cons.1, frames_cons ht.cons.2 hK⟩
  | query m i E p =>
    cases m with
    | zero => simp only [step, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
    | succ m =>
      by_cases hp : p ≤ x.length
      · cases hr : ruleAtM g.rules i with
        | none => simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
        | some rule =>
          simp only [step, if_pos hp, hr, Option.some.injEq] at hs; cases hs
          exact ⟨⟨rule.arity, compilerBody_available start hr⟩, hK⟩
      · simp only [step, if_neg hp, Option.some.injEq] at hs; cases hs; exact ⟨trivial, hK⟩
  | value v =>
    cases K with
    | nil => cases v <;> simp [step] at hs
    | cons f K =>
      exact return_ok g x (compilerNodes g start) v f K next (hK f (by simp))
        (fun f hf => hK f (by simp [hf])) hs

theorem runs_ok (g : MGrammar) (x : List Char) (e : MExp) {a b : Config}
    (h : Runs g x a b) (hi : ConfigOK (compilerNodes g e) a) : ConfigOK (compilerNodes g e) b := by
  revert hi
  induction h with
  | refl => exact fun hi => hi
  | cons hs ht ih => intro hi; exact ih (step_ok g x e _ _ hi hs)

theorem reachable_ok (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : ConfigOK (compilerNodes g e) c :=
  runs_ok g x e h ⟨⟨0, compilerStart_available g e⟩, fun f hf => by cases hf⟩

def exprPool (nodes : List CompileNode) : List MExp := nodes.flatMap fun node =>
  match node with
  | .expr _ e => [e]
  | _ => []

theorem ExprOK.mem {ns e} (h : ExprOK ns e) : e ∈ exprPool ns := by
  obtain ⟨arity, h⟩ := h
  exact List.mem_flatMap.mpr ⟨.expr arity e, h.self, by simp⟩

theorem ArgsOK.mem {ns es} (h : ArgsOK ns es) : ∀ a ∈ es, a ∈ exprPool ns := by
  induction es with
  | nil => intro a ha; cases ha
  | cons a es ih =>
    intro b hb
    rcases List.mem_cons.mp hb with he | hb
    · subst b; exact h.cons.1.mem
    · exact ih h.cons.2 b hb

end Shallot.MacroPeg.CBV.SequentialStackPool
