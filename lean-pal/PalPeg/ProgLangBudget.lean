import PalPeg.ProgLangBank

/-! Fixed-length slots for bounded transactions. Once an Exec proof has
returned to an empty continuation, unused slot ticks cannot alter the tapes. -/

set_option autoImplicit false

namespace PalPeg.ProgLang

open PegSeparation.RealTimeTM PalPeg.Program

variable {A C Γ Terminal : Type} {t : ℕ}

theorem runInputs_quiescent {I : Interp Terminal A C Γ t} {blank : Γ}
    {T : Fin t → STape Γ} {s : Stack A C} (h : SEqAt I T s [])
    (l : List (Option Terminal)) :
    ∃ s', runInputs I blank l (s, T) = (s', T) ∧ SEqAt I T s' [] := by
  cases l with
  | nil => exact ⟨s, rfl, h⟩
  | cons a l =>
      have hm : microStep I blank a (s, T) = ([], T) := by
        simp only [microStep]
        rw [h]
        simp only [stepStack_nil]
      exact ⟨[], by rw [runInputs_cons, hm, runInputs_halted], SEqAt.rfl' _ _ _⟩

/-- A bounded transaction can occupy a fixed larger slot without reading or
writing any further tape cells after completion. Extra input values do not
matter because there is no remaining action. -/
theorem Exec.runInputs_ge {I : Interp Terminal A C Γ t} {blank : Γ}
    {T : Fin t → STape Γ} {p : Prog A C} {tr : List (Fin t → Γ × Move)}
    (h : Exec I blank p T tr) (l : List (Option Terminal)) (hlen : tr.length ≤ l.length) :
    ∃ s, runInputs I blank l ([p], T) = (s, applyTrace blank T tr) ∧
      SEqAt I (applyTrace blank T tr) s [] := by
  have hp : (l.take tr.length).length = tr.length := by
    rw [List.length_take]; exact Nat.min_eq_left hlen
  obtain ⟨_, s, hs, hq⟩ := h [] (l.take tr.length) hp
  simp only [List.append_nil] at hs
  obtain ⟨s', hs', hq'⟩ := runInputs_quiescent hq (l.drop tr.length)
  refine ⟨s', ?_, hq'⟩
  rw [← List.take_append_drop tr.length l, runInputs_append, hs]
  exact hs'

/-- With one extra tick the continuation is literally empty, not merely
quiescent under the current tape readings. It therefore stays halted even
when another transaction subsequently changes the tapes. -/
theorem Exec.runInputs_gt {I : Interp Terminal A C Γ t} {blank : Γ}
    {T : Fin t → STape Γ} {p : Prog A C} {tr : List (Fin t → Γ × Move)}
    (h : Exec I blank p T tr) (l : List (Option Terminal)) (hlen : tr.length < l.length) :
    runInputs I blank l ([p], T) = ([], applyTrace blank T tr) := by
  have hp : (l.take tr.length).length = tr.length := by
    rw [List.length_take]; exact Nat.min_eq_left (Nat.le_of_lt hlen)
  obtain ⟨_, s, hs, hq⟩ := h [] (l.take tr.length) hp
  simp only [List.append_nil] at hs
  have hd : l.drop tr.length ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_drop, List.length_nil] at hh
    omega
  have hf : runInputs I blank (l.drop tr.length) (s, applyTrace blank T tr) =
      ([], applyTrace blank T tr) := by
    cases he : l.drop tr.length with
    | nil => exact False.elim (hd he)
    | cons a tail =>
        have hm : microStep I blank a (s, applyTrace blank T tr) =
            ([], applyTrace blank T tr) := by
          simp only [microStep]
          rw [hq]
          simp only [stepStack_nil]
        rw [runInputs_cons, hm, runInputs_halted]
  rw [← List.take_append_drop tr.length l, runInputs_append, hs]
  exact hf

end PalPeg.ProgLang

namespace PalPeg.ProgLangBank

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist

variable {A C Γ Terminal : Type} {n t : ℕ}

/-- A selected bank transaction receives a fixed slot at least as long as its
trace. The slot returns a quiescent continuation even when it finished early. -/
theorem runChunk_exec_le (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ))
    (tr : List (Fin t → Γ × Move)) (hstart : (x.1.1 i).val = [progs i])
    (he : Exec (I i).toInterp blank (progs i) x.2 tr) (hlen : tr.length ≤ l.length) :
    (runChunk progs I blank i l x).2 = applyTrace blank x.2 tr ∧
      SEqAt (I i).toInterp (applyTrace blank x.2 tr)
        ((runChunk progs I blank i l x).1.1 i).val [] := by
  obtain ⟨s, hs, hq⟩ := he.runInputs_ge l hlen
  have hh := runChunk_selected progs I blank i l x
  rw [hstart, hs] at hh
  refine ⟨congrArg Prod.snd hh, ?_⟩
  have hc := congrArg Prod.fst hh
  change ((runChunk progs I blank i l x).1.1 i).val = s at hc
  rw [hc]
  exact hq

/-- Strict slack makes the selected bank continuation literally empty. -/
theorem runChunk_exec_lt (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ))
    (tr : List (Fin t → Γ × Move)) (hstart : (x.1.1 i).val = [progs i])
    (he : Exec (I i).toInterp blank (progs i) x.2 tr) (hlen : tr.length < l.length) :
    (runChunk progs I blank i l x).2 = applyTrace blank x.2 tr ∧
      ((runChunk progs I blank i l x).1.1 i).val = [] := by
  have hh := runChunk_selected progs I blank i l x
  rw [hstart, he.runInputs_gt l hlen] at hh
  exact ⟨congrArg Prod.snd hh, congrArg Prod.fst hh⟩

/-- Restart only a literally empty finite control. Pending work is never
discarded by this operation; tapes and the acceptance flag are untouched. -/
noncomputable def restartDone (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (Bank progs × Bool) × (Fin t → STape Γ) := by
  classical
  exact if (x.1.1 i).val = [] then
    ((Function.update x.1.1 i (startCtrlS (progs i)), x.1.2), x.2) else x

theorem restartDone_eq (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) (h : (x.1.1 i).val = []) :
    restartDone progs i x =
      ((Function.update x.1.1 i (startCtrlS (progs i)), x.1.2), x.2) := by
  simp only [restartDone, if_pos h]

theorem restartDone_pending (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) (h : (x.1.1 i).val ≠ []) :
    restartDone progs i x = x := by
  simp only [restartDone, if_neg h]

@[simp] theorem restartDone_tapes (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (restartDone progs i x).2 = x.2 := by
  classical
  by_cases h : (x.1.1 i).val = [] <;> simp [restartDone, h]

theorem restartDone_other (progs : Fin n → Prog A C) (i j : Fin n) (hji : j ≠ i)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (restartDone progs i x).1.1 j = x.1.1 j := by
  classical
  by_cases h : (x.1.1 i).val = [] <;> simp [restartDone, h, hji]

/-- Entries at a call boundary may be unused or previously completed. -/
def AtBoundary (progs : Fin n → Prog A C) (b : Bank progs) : Prop :=
  ∀ i, (b i).val = [] ∨ (b i).val = [progs i]

theorem initialBank_boundary (progs : Fin n → Prog A C) :
    AtBoundary progs (initialBank progs) := fun _ => Or.inr rfl

theorem restartDone_fresh (progs : Fin n → Prog A C) (i : Fin n)
    (x : (Bank progs × Bool) × (Fin t → STape Γ))
    (h : (x.1.1 i).val = [] ∨ (x.1.1 i).val = [progs i]) :
    ((restartDone progs i x).1.1 i).val = [progs i] := by
  classical
  rcases h with h | h
  · rw [restartDone_eq progs i x h]
    simp [startCtrlS]
  · have hn : (x.1.1 i).val ≠ [] := by rw [h]; simp
    rw [restartDone_pending progs i x hn]
    exact h

end PalPeg.ProgLangBank
