import PalPeg.ProgLangBank

/-! Disjoint tape banks: other slots preserve both local tapes and continuations. -/

set_option autoImplicit false

namespace PalPeg.ProgLangBank

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist

variable {A C Terminal Γ : Type} {n t : ℕ}

def tapeSlice {X : Type} (i : Fin n) (T : Fin (n * t) → X) : Fin t → X :=
  fun j => T (finProdFinEquiv (i, j))

def slotInterp (I : InterpF Terminal A C Γ t) (i : Fin n) :
    InterpF Terminal A C Γ (n * t) where
  condOf c σ := I.condOf c (tapeSlice i σ)
  actOf a u σ j :=
    let p := finProdFinEquiv.symm j
    if p.1 = i then I.actOf a u (tapeSlice i σ) p.2 else (σ j, .stay)
  flagOf := I.flagOf

@[simp] theorem slotInterp_at (I : InterpF Terminal A C Γ t)
    (i : Fin n) (a : A) (u : Option Terminal) (σ : Fin (n * t) → Γ)
    (j : Fin t) :
    (slotInterp I i).actOf a u σ (finProdFinEquiv (i, j)) =
      I.actOf a u (tapeSlice i σ) j := by
  simp only [slotInterp, Equiv.symm_apply_apply, ↓reduceIte]

@[simp] theorem slotInterp_other (I : InterpF Terminal A C Γ t)
    (i k : Fin n) (h : k ≠ i) (a : A) (u : Option Terminal)
    (σ : Fin (n * t) → Γ) (j : Fin t) :
    (slotInterp I i).actOf a u σ (finProdFinEquiv (k, j)) =
      (σ (finProdFinEquiv (k, j)), .stay) := by
  simp only [slotInterp, Equiv.symm_apply_apply, if_neg h]

theorem microStep_slot (I : InterpF Terminal A C Γ t) (i : Fin n)
    (blank : Γ) (u : Option Terminal) (s : Stack A C)
    (T : Fin (n * t) → STape Γ) :
    let y := microStep (slotInterp I i).toInterp blank u (s, T)
    (y.1, tapeSlice i y.2) = microStep I.toInterp blank u (s, tapeSlice i T) := by
  have hev : evalConds (slotInterp I i).toInterp (fun j => (T j).focus) =
      evalConds I.toInterp (fun j => (tapeSlice i T j).focus) := rfl
  simp only [microStep]
  rw [hev]
  refine Prod.ext ?_ ?_
  · rfl
  cases h : (stepStack (evalConds I.toInterp (fun j => (tapeSlice i T j).focus)) s).2 with
  | none => rfl
  | some a =>
      funext j
      simp only [tapeSlice, slotInterp_at]
      rfl

theorem microStep_slot_other (I : InterpF Terminal A C Γ t) (i k : Fin n)
    (h : k ≠ i) (blank : Γ) (u : Option Terminal) (s : Stack A C)
    (T : Fin (n * t) → STape Γ) :
    tapeSlice k (microStep (slotInterp I i).toInterp blank u (s, T)).2 =
      tapeSlice k T := by
  simp only [microStep]
  split
  · rfl
  · funext j
    simp only [tapeSlice, slotInterp_other I i k h]
    exact applyAction_stay_self blank _

def localState (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ)) :
    Stack A C × (Fin t → STape Γ) := ((x.1.1 i).val, tapeSlice i x.2)

theorem tick_local (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (i : Fin n)
    (blank : Γ) (u : Option Terminal)
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ)) :
    localState progs i (tick progs (fun k => slotInterp (I k) k) blank i u x) =
      microStep (I i).toInterp blank u (localState progs i x) := by
  have h := congrArg (fun y : Stack A C × (Fin (n * t) → STape Γ) =>
    (y.1, tapeSlice i y.2))
    (tick_selected progs (fun k => slotInterp (I k) k) blank i u x)
  exact h.trans (microStep_slot (I i) i blank u _ _)

theorem tick_local_other (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (i k : Fin n)
    (h : k ≠ i) (blank : Γ) (u : Option Terminal)
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ)) :
    localState progs k (tick progs (fun j => slotInterp (I j) j) blank i u x) =
      localState progs k x := by
  apply Prod.ext
  · simp [localState, tick_other progs _ blank i k h]
  · exact microStep_slot_other (I i) i k h blank u _ _

/-- A schedule records which slot receives each micro-input. -/
def runInterleaved (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) :
    List (Fin n × Option Terminal) →
      ((Bank progs × Bool) × (Fin (n * t) → STape Γ)) →
      ((Bank progs × Bool) × (Fin (n * t) → STape Γ))
  | [], x => x
  | (i, a) :: l, x => runInterleaved progs I blank l
      (tick progs (fun j => slotInterp (I j) j) blank i a x)

def localInputs (i : Fin n) : List (Fin n × Option Terminal) → List (Option Terminal)
  | [] => []
  | (j, a) :: l => if j = i then a :: localInputs i l else localInputs i l

/-- Arbitrary interleaving is exactly isolated execution on each slot's inputs. -/
theorem runInterleaved_local (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Fin n × Option Terminal))
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ)) :
    localState progs i (runInterleaved progs I blank l x) =
      runInputs (I i).toInterp blank (localInputs i l) (localState progs i x) := by
  induction l generalizing x with
  | nil => rfl
  | cons p l ih =>
      rcases p with ⟨j, a⟩
      simp only [runInterleaved, localInputs, ih]
      by_cases h : j = i
      · subst j
        rw [if_pos rfl, runInputs_cons, tick_local]
      · rw [if_neg h, tick_local_other progs I j i (Ne.symm h)]

/-- A local finite-program execution remains valid after arbitrary slot switches.
The premise counts only this slot's scheduled ticks, not global elapsed ticks. -/
theorem runInterleaved_exec (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Fin n × Option Terminal))
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ))
    (acts : List (Fin t → Γ × Move))
    (hstart : (x.1.1 i).val = [progs i])
    (he : Exec (I i).toInterp blank (progs i) (tapeSlice i x.2) acts)
    (hlen : (localInputs i l).length = acts.length) :
    tapeSlice i (runInterleaved progs I blank l x).2 =
        applyTrace blank (tapeSlice i x.2) acts ∧
      SEqAt (I i).toInterp (applyTrace blank (tapeSlice i x.2) acts)
        ((runInterleaved progs I blank l x).1.1 i).val [] := by
  obtain ⟨_, s, hs, heq⟩ := he [] (localInputs i l) hlen
  have h := runInterleaved_local progs I blank i l x
  simp only [localState, hstart] at h
  simp only [List.append_nil] at hs
  rw [hs] at h
  refine ⟨congrArg Prod.snd h, ?_⟩
  have hc := congrArg Prod.fst h
  change ((runInterleaved progs I blank l x).1.1 i).val = s at hc
  rw [hc]
  exact heq

/-- Extra scheduled ticks after a local program finishes are harmless. -/
theorem runInterleaved_exec_of_le (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Fin n × Option Terminal))
    (x : (Bank progs × Bool) × (Fin (n * t) → STape Γ))
    (acts : List (Fin t → Γ × Move))
    (hstart : (x.1.1 i).val = [progs i])
    (he : Exec (I i).toInterp blank (progs i) (tapeSlice i x.2) acts)
    (hlen : acts.length ≤ (localInputs i l).length) :
    tapeSlice i (runInterleaved progs I blank l x).2 =
      applyTrace blank (tapeSlice i x.2) acts := by
  obtain ⟨_, s, hs, heq⟩ := he [] ((localInputs i l).take acts.length)
    (List.length_take_of_le hlen)
  have h := runInterleaved_local progs I blank i l x
  simp only [localState, hstart] at h
  simp only [List.append_nil] at hs
  have hr : runInputs (I i).toInterp blank (localInputs i l)
      ([progs i], tapeSlice i x.2) =
      runInputs (I i).toInterp blank ((localInputs i l).drop acts.length)
        (s, applyTrace blank (tapeSlice i x.2) acts) := by
    conv_lhs => rw [← List.take_append_drop acts.length (localInputs i l)]
    rw [runInputs_append, hs]
  rw [hr] at h
  cases hd : (localInputs i l).drop acts.length with
  | nil => simpa only [hd, runInputs_nil] using congrArg Prod.snd h
  | cons a r =>
      rw [hd, runInputs_congr heq a r, runInputs_halted] at h
      exact congrArg Prod.snd h

/-- info: 'PalPeg.ProgLangBank.runInterleaved_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runInterleaved_exec

end PalPeg.ProgLangBank
