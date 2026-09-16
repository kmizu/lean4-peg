import PalPeg.ProgLangSum

/-! Finite read-only dispatch with arbitrary continuation programs. -/

set_option autoImplicit false

namespace PalPeg.ProgLang

open PegSeparation.RealTimeTM PalPeg.Program

variable {A C Γ Terminal K : Type} {t : ℕ}

def chooseList (cond : K → C) (body : K → Prog A C) : List K → Prog A C
  | [] => .skip
  | k :: ks => .ite (cond k) (body k) (chooseList cond body ks)

noncomputable def choose [Fintype K] (cond : K → C) (body : K → Prog A C) : Prog A C :=
  chooseList cond body Finset.univ.toList

theorem exec_chooseList [DecidableEq K] {I : Interp Terminal A C Γ t}
    {blank : Γ} {T : Fin t → STape Γ} {tr : List (Fin t → Γ × Move)}
    {cond : K → C} {body : K → Prog A C} {key : K}
    (ks : List K) (hk : key ∈ ks)
    (hc : ∀ a, I.condOf (cond a) (fun j => (T j).focus) = decide (key = a))
    (he : Exec I blank (body key) T tr) :
    Exec I blank (chooseList cond body ks) T tr := by
  induction ks with
  | nil => simp at hk
  | cons a ks ih =>
      by_cases ha : key = a
      · subst a
        exact exec_ite_pos (by rw [hc]; simp) he
      · exact exec_ite_neg (by rw [hc]; exact decide_eq_false ha)
          (ih ((List.mem_cons.mp hk).resolve_left ha))

theorem exec_choose [Fintype K] [DecidableEq K] {I : Interp Terminal A C Γ t}
    {blank : Γ} {T : Fin t → STape Γ} {tr : List (Fin t → Γ × Move)}
    {cond : K → C} {body : K → Prog A C} {key : K}
    (hc : ∀ a, I.condOf (cond a) (fun j => (T j).focus) = decide (key = a))
    (he : Exec I blank (body key) T tr) :
    Exec I blank (choose cond body) T tr :=
  exec_chooseList _ (by simp) hc he

end PalPeg.ProgLang
