import PalPeg.GSVerifierProgZLoop

/-! Bound head positions at every prefix by counting right moves in a
terminating execution. Left moves at the tape edge cannot invalidate it. -/
set_option autoImplicit false

namespace PalPeg.ProgLangHeadMoves
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
variable {Γ A C Terminal : Type} {t : ℕ}

def right (m : Move) : ℕ := if m = .right then 1 else 0

def count (j : Fin t) (acts : List (Fin t → Γ × Move)) : ℕ :=
  (acts.map (fun w => right (w j).2)).sum

@[simp] theorem count_nil (j : Fin t) : count (Γ := Γ) j [] = 0 := rfl
@[simp] theorem count_cons (j : Fin t) (w : Fin t → Γ × Move) (acts : List (Fin t → Γ × Move)) :
    count j (w :: acts) = right (w j).2 + count j acts := rfl
@[simp] theorem count_append (j : Fin t) (a b : List (Fin t → Γ × Move)) :
    count j (a ++ b) = count j a + count j b := by
  simp only [count, List.map_append, List.sum_append]

theorem count_le_length (j : Fin t) (acts : List (Fin t → Γ × Move)) :
    count j acts ≤ acts.length := by
  induction acts with
  | nil => rfl
  | cons w acts ih =>
    simp only [count_cons, List.length_cons]
    have h : right (w j).2 ≤ 1 := by unfold right; split <;> omega
    omega

theorem apply_head (blank : Γ) (T : STape Γ) (w : Γ × Move) :
    (T.applyAction blank w).left.length ≤ T.left.length + right w.2 := by
  rcases T with ⟨l, a, r⟩
  rcases w with ⟨b, m⟩
  cases m <;> cases l <;> cases r <;> simp [STape.applyAction, right]

theorem trace_head (blank : Γ) (T : Fin t → STape Γ) (acts : List (Fin t → Γ × Move)) (j : Fin t) :
    (applyTrace blank T acts j).left.length ≤ (T j).left.length + count j acts := by
  induction acts generalizing T with
  | nil => simp
  | cons w acts ih =>
    rw [applyTrace_cons, count_cons]
    have h := ih (fun j => (T j).applyAction blank (w j))
    have ha := apply_head blank (T j) (w j)
    omega

theorem trace_count_bound {I : Interp Terminal A C Γ t} {blank : Γ} {p : Prog A C}
    {T : Fin t → STape Γ} {acts : List (Fin t → Γ × Move)}
    (he : Exec I blank p T acts) (N : ℕ) (j : Fin t) :
    count j (trace I blank (List.replicate N none) ([p], T)) ≤ count j acts := by
  obtain ⟨ha, s, hs, heq⟩ := he [] (List.replicate acts.length none) (by simp)
  simp only [List.append_nil] at ha hs heq
  have htotal : trace I blank (List.replicate (N + acts.length) none) ([p], T) = acts := by
    rw [Nat.add_comm N acts.length, List.replicate_add, trace_append, ha, hs, trace_congr heq]
    simp
  have hprefix : count j (trace I blank (List.replicate N none) ([p], T)) ≤
      count j (trace I blank (List.replicate (N + acts.length) none) ([p], T)) := by
    rw [List.replicate_add, trace_append, count_append]
    omega
  simpa only [htotal] using hprefix

theorem prefix_head {I : Interp Terminal A C Γ t} {blank : Γ} {p : Prog A C}
    {T : Fin t → STape Γ} {acts : List (Fin t → Γ × Move)}
    (he : Exec I blank p T acts) (N : ℕ) (j : Fin t) :
    ((runInputs I blank (List.replicate N none) ([p], T)).2 j).left.length ≤
      (T j).left.length + count j acts := by
  rw [runInputs_snd_eq_applyTrace]
  exact (trace_head blank T _ j).trans (Nat.add_le_add_left (trace_count_bound he N j) _)

/-- Two text-head budgets, with exact program and endpoint semantics. -/
def Bounded (I : Interp Terminal A C Γ t) (blank : Γ) (j₁ j₂ : Fin t)
    (p : Prog A C) (T U : Fin t → STape Γ) (b₁ b₂ : ℕ) : Prop :=
  ∃ acts, Exec I blank p T acts ∧ applyTrace blank T acts = U ∧
    count j₁ acts ≤ b₁ ∧ count j₂ acts ≤ b₂

theorem Bounded.mono {I : Interp Terminal A C Γ t} {blank : Γ} {j₁ j₂ : Fin t}
    {p : Prog A C} {T U : Fin t → STape Γ} {a₁ a₂ b₁ b₂ : ℕ}
    (h : Bounded I blank j₁ j₂ p T U a₁ a₂) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    Bounded I blank j₁ j₂ p T U b₁ b₂ := by
  obtain ⟨acts, he, ht, hc₁, hc₂⟩ := h
  exact ⟨acts, he, ht, hc₁.trans h₁, hc₂.trans h₂⟩

theorem Bounded.of_runsTo {I : Interp Terminal A C Γ t} {blank : Γ} {j₁ j₂ : Fin t}
    {p : Prog A C} {T U : Fin t → STape Γ} {cost : ℕ}
    (h : GSVProgZLoop.RunsTo I blank p T U cost) : Bounded I blank j₁ j₂ p T U cost cost := by
  obtain ⟨acts, he, ht, hl⟩ := h
  exact ⟨acts, he, ht, hl ▸ count_le_length j₁ acts, hl ▸ count_le_length j₂ acts⟩

theorem Bounded.seq {I : Interp Terminal A C Γ t} {blank : Γ} {j₁ j₂ : Fin t}
    {p q : Prog A C} {T U V : Fin t → STape Γ} {a₁ a₂ b₁ b₂ : ℕ}
    (hp : Bounded I blank j₁ j₂ p T U a₁ a₂)
    (hq : Bounded I blank j₁ j₂ q U V b₁ b₂) :
    Bounded I blank j₁ j₂ (.seq p q) T V (a₁ + b₁) (a₂ + b₂) := by
  obtain ⟨a, ha, ea, ha₁, ha₂⟩ := hp
  obtain ⟨b, hb, eb, hb₁, hb₂⟩ := hq
  refine ⟨a ++ b, exec_seq ha (ea ▸ hb), ?_, ?_, ?_⟩
  · rw [applyTrace_append, ea, eb]
  · rw [count_append]; omega
  · rw [count_append]; omega

theorem Bounded.ite_pos {I : Interp Terminal A C Γ t} {blank : Γ} {j₁ j₂ : Fin t}
    {p q : Prog A C} {c : C} {T U : Fin t → STape Γ} {b₁ b₂ : ℕ}
    (hc : I.condOf c (fun j => (T j).focus) = true) (h : Bounded I blank j₁ j₂ p T U b₁ b₂) :
    Bounded I blank j₁ j₂ (.ite c p q) T U b₁ b₂ := by
  obtain ⟨acts, he, ht, h₁, h₂⟩ := h
  exact ⟨acts, exec_ite_pos hc he, ht, h₁, h₂⟩

theorem Bounded.ite_neg {I : Interp Terminal A C Γ t} {blank : Γ} {j₁ j₂ : Fin t}
    {p q : Prog A C} {c : C} {T U : Fin t → STape Γ} {b₁ b₂ : ℕ}
    (hc : I.condOf c (fun j => (T j).focus) = false) (h : Bounded I blank j₁ j₂ q T U b₁ b₂) :
    Bounded I blank j₁ j₂ (.ite c p q) T U b₁ b₂ := by
  obtain ⟨acts, he, ht, h₁, h₂⟩ := h
  exact ⟨acts, exec_ite_neg hc he, ht, h₁, h₂⟩

end PalPeg.ProgLangHeadMoves
