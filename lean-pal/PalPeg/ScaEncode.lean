import PalPeg.ScaProg
import PalPeg.ScaStackMachine

/-!
# From per-letter stack programs to a total PEG

A machine given by one stack program per input letter is a multi-stack machine (the programs are
local), hence a scaffold automaton, hence a total PEG. An abstract machine that such a program
simulates — a representation relation established at the start, kept by every letter, and
agreeing on acceptance — recognizes the same language.
-/
set_option autoImplicit false
namespace PalPeg.ScaEncode
open PalPeg.ScaLocal PalPeg.ScaProg

variable {Γ C : Type} {K : ℕ}

/-- One stack program per letter, with a common depth and width. -/
structure LetterProgs (Γ C : Type) (K : ℕ) where
  peek : ℕ
  prog : Fin 2 → Prog Γ C K
  init : C
  accept : C → Bool

def LetterProgs.depth (P : LetterProgs Γ C K) : ℕ :=
  max ((P.prog 0).depth P.peek) ((P.prog 1).depth P.peek)

def LetterProgs.width (P : LetterProgs Γ C K) : ℕ :=
  max (P.prog 0).width (P.prog 1).width

theorem LetterProgs.isLocal (P : LetterProgs Γ C K) (a : Fin 2) :
    IsLocal P.depth P.width ((P.prog a).eval P.peek) := by
  fin_cases a
  · exact (Prog.isLocal P.peek (P.prog 0)).mono (le_max_left _ _) (le_max_left _ _)
  · exact (Prog.isLocal P.peek (P.prog 1)).mono (le_max_right _ _) (le_max_right _ _)

/-- The rule performing letter `a`'s program. -/
noncomputable def LetterProgs.rule (P : LetterProgs Γ C K) (a : Fin 2) :
    Rule Γ C K P.depth P.width :=
  (P.isLocal a).choose

theorem LetterProgs.rule_run (P : LetterProgs Γ C K) (a : Fin 2) (c : C) (st : Fin K → List Γ) :
    (P.prog a).eval P.peek c st = (P.rule a).run c st :=
  (P.isLocal a).choose_spec c st

def toSM (r : Rewrite Γ K) : ScaStackMachine.Rewrite Γ K := ⟨r.pre, r.src, r.drop⟩

theorem apply_toSM (st : Fin K → List Γ) (r : Rewrite Γ K) :
    ScaStackMachine.apply st (toSM r) = apply st r := rfl

/-- The multi-stack machine of the letter programs. -/
noncomputable def LetterProgs.machine (P : LetterProgs Γ C K) :
    ScaStackMachine.StackMachine Γ C K P.width P.depth where
  init := P.init
  accept := P.accept
  step c a v := ((P.rule a).f c v).1 |> fun c' => (c', fun k => toSM (((P.rule a).f c v).2 k))
  pre_le c a v k := (P.rule a).pre_le c v k
  drop_le c a v k := (P.rule a).drop_le c v k

theorem LetterProgs.stepCfg (P : LetterProgs Γ C K) (cfg : C × (Fin K → List Γ)) (a : Fin 2) :
    P.machine.stepCfg cfg a = (P.prog a).eval P.peek cfg.1 cfg.2 := by
  rw [P.rule_run]
  rfl

theorem LetterProgs.run (P : LetterProgs Γ C K) (w : List (Fin 2)) :
    P.machine.run w = w.foldl (fun cfg a => (P.prog a).eval P.peek cfg.1 cfg.2) (P.init, fun _ => []) := by
  unfold ScaStackMachine.StackMachine.run
  congr 1
  funext cfg a
  exact P.stepCfg cfg a

/-- **An abstract machine simulated by letter programs has the same language.** -/
theorem accepts_iff {σ : Type} (P : LetterProgs Γ C K) (init : σ) (step : σ → Fin 2 → σ)
    (acc : σ → Bool) (Rep : σ → C → (Fin K → List Γ) → Prop)
    (h0 : Rep init P.init fun _ => [])
    (hstep : ∀ s c st a, Rep s c st →
      Rep (step s a) ((P.prog a).eval P.peek c st).1 ((P.prog a).eval P.peek c st).2)
    (hacc : ∀ s c st, Rep s c st → acc s = P.accept c) (w : List (Fin 2)) :
    P.machine.Accepts w ↔ acc (w.foldl step init) = true := by
  unfold ScaStackMachine.StackMachine.Accepts
  rw [P.run]
  suffices h : ∀ (s : σ) (cfg : C × (Fin K → List Γ)), Rep s cfg.1 cfg.2 →
      Rep (w.foldl step s) (w.foldl (fun cfg a => (P.prog a).eval P.peek cfg.1 cfg.2) cfg).1
        (w.foldl (fun cfg a => (P.prog a).eval P.peek cfg.1 cfg.2) cfg).2 by
    rw [hacc _ _ _ (h init (P.init, fun _ => []) h0)]
    exact Iff.rfl
  induction w with
  | nil => intro s cfg h; exact h
  | cons a rest ih =>
    intro s cfg h
    exact ih (step s a) _ (hstep s cfg.1 cfg.2 a h)

/-- **`PAL ∈ PEG`** from letter programs simulating an abstract machine that recognizes `PAL`. -/
theorem pal_in_peg {σ : Type} [Finite Γ] [Finite C] (P : LetterProgs Γ C K) (init : σ)
    (step : σ → Fin 2 → σ) (acc : σ → Bool) (Rep : σ → C → (Fin K → List Γ) → Prop)
    (h0 : Rep init P.init fun _ => [])
    (hstep : ∀ s c st a, Rep s c st →
      Rep (step s a) ((P.prog a).eval P.peek c st).1 ((P.prog a).eval P.peek c st).2)
    (hacc : ∀ s c st, Rep s c st → acc s = P.accept c)
    (hpal : ∀ w : List (Fin 2), acc (w.foldl step init) = true ↔ w ∈ PalPeg.PAL) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  ScaStackMachine.pal_in_peg_of_stackMachine P.machine fun w =>
    (accepts_iff P init step acc Rep h0 hstep hacc w).trans (hpal w)

/-- info: 'PalPeg.ScaEncode.pal_in_peg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg

end PalPeg.ScaEncode
