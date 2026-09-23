import Mathlib

/-!
# Local updates of persistent stacks

A configuration is a finite control and `K` stacks. An update is **local** with depth `D` and
width `E` when it reads only the control and the top `D` elements of each stack, and rewrites each
stack as at most `E` pushed elements followed by some stack with at most `D` elements dropped
(or nothing). This is exactly what one scaffold node can do (Scala's persistent `Stack`s:
`push`, `drop`, `copyFrom`, `clear`). Local updates compose, so a bounded program of stack
operations per input letter is local.
-/
set_option autoImplicit false
namespace PalPeg.ScaLocal

variable {Γ C : Type} {K : ℕ}

/-- How one stack is rebuilt: pushed elements (top first), then stack `src` with `drop` removed. -/
structure Rewrite (Γ : Type) (K : ℕ) where
  pre : List Γ
  src : Option (Fin K)
  drop : ℕ

/-- The stack a rewrite builds from the old stacks. -/
def apply (st : Fin K → List Γ) (r : Rewrite Γ K) : List Γ :=
  r.pre ++ (match r.src with
    | none => []
    | some i => (st i).drop r.drop)

/-- The top `D` elements of each stack. -/
def view (D : ℕ) (st : Fin K → List Γ) : Fin K → List Γ := fun k => (st k).take D

/-- A local rule: from the control and the view, the new control and one rewrite per stack. -/
structure Rule (Γ C : Type) (K D E : ℕ) where
  f : C → (Fin K → List Γ) → C × (Fin K → Rewrite Γ K)
  pre_le : ∀ c v k, ((f c v).2 k).pre.length ≤ E
  drop_le : ∀ c v k, ((f c v).2 k).drop ≤ D

/-- The update a rule performs. -/
def Rule.run {D E : ℕ} (R : Rule Γ C K D E) (c : C) (st : Fin K → List Γ) : C × (Fin K → List Γ) :=
  ((R.f c (view D st)).1, fun k => apply st ((R.f c (view D st)).2 k))

/-- **`Φ` is local**: some rule performs it. -/
def IsLocal (D E : ℕ) (Φ : C → (Fin K → List Γ) → C × (Fin K → List Γ)) : Prop :=
  ∃ R : Rule Γ C K D E, ∀ c st, Φ c st = R.run c st

/-! ## Views of rewritten stacks -/

theorem take_apply {D : ℕ} (st : Fin K → List Γ) (r : Rewrite Γ K) (n : ℕ) (hd : r.drop ≤ D) :
    (apply st r).take n = (apply (view (D + n) st) r).take n := by
  unfold apply view
  rcases r with ⟨pre, src, dr⟩
  cases src with
  | none => rfl
  | some i =>
    have hdr : dr ≤ D := hd
    simp only [List.take_append]
    congr 1
    rw [List.drop_take, List.take_take]
    congr 1
    omega

/-- Dropping from a rewritten stack is again a rewrite. -/
def dropRewrite (r : Rewrite Γ K) (j : ℕ) : Rewrite Γ K :=
  ⟨r.pre.drop j, r.src, r.drop + (j - r.pre.length)⟩

theorem drop_apply (st : Fin K → List Γ) (r : Rewrite Γ K) (j : ℕ) :
    (apply st r).drop j = apply st (dropRewrite r j) := by
  unfold apply dropRewrite
  rcases r with ⟨pre, src, dr⟩
  simp only [List.drop_append]
  cases src with
  | none => simp
  | some i => simp [List.drop_drop]

/-- Rewrite by `r₂` the stacks that `rs₁` built: the composite rewrite on the original stacks. -/
def compose (rs₁ : Fin K → Rewrite Γ K) (r₂ : Rewrite Γ K) : Rewrite Γ K :=
  match r₂.src with
  | none => ⟨r₂.pre, none, 0⟩
  | some i =>
    let d := dropRewrite (rs₁ i) r₂.drop
    ⟨r₂.pre ++ d.pre, d.src, d.drop⟩

theorem apply_compose (st : Fin K → List Γ) (rs₁ : Fin K → Rewrite Γ K) (r₂ : Rewrite Γ K) :
    apply (fun k => apply st (rs₁ k)) r₂ = apply st (compose rs₁ r₂) := by
  unfold compose
  rcases r₂ with ⟨pre, src, dr⟩
  cases src with
  | none => simp [apply]
  | some i =>
    show pre ++ (apply st (rs₁ i)).drop dr = _
    rw [drop_apply]
    simp [apply, List.append_assoc]

theorem view_view (D₁ D₂ : ℕ) (st : Fin K → List Γ) :
    view D₁ (view (D₁ + D₂) st) = view D₁ st := by
  funext k
  simp only [view, List.take_take]
  congr 1
  omega

/-- **Composition of local rules.** -/
def Rule.comp {D₁ E₁ D₂ E₂ : ℕ} (R₁ : Rule Γ C K D₁ E₁) (R₂ : Rule Γ C K D₂ E₂) :
    Rule Γ C K (D₁ + D₂) (E₁ + E₂) where
  f c v :=
    let o₁ := R₁.f c (view D₁ v)
    let o₂ := R₂.f o₁.1 (fun k => (apply v (o₁.2 k)).take D₂)
    (o₂.1, fun k => compose o₁.2 (o₂.2 k))
  pre_le c v k := by
    simp only [compose]
    split
    · have := R₂.pre_le (R₁.f c (view D₁ v)).1
        (fun k => (apply v ((R₁.f c (view D₁ v)).2 k)).take D₂) k
      simp only at this ⊢
      omega
    · rename_i i _
      have h2 := R₂.pre_le (R₁.f c (view D₁ v)).1
        (fun k => (apply v ((R₁.f c (view D₁ v)).2 k)).take D₂) k
      have h1 := R₁.pre_le c (view D₁ v) i
      simp only [dropRewrite, List.length_append, List.length_drop]
      omega
  drop_le c v k := by
    simp only [compose]
    split
    · simp
    · rename_i i _
      have h2 := R₂.drop_le (R₁.f c (view D₁ v)).1
        (fun k => (apply v ((R₁.f c (view D₁ v)).2 k)).take D₂) k
      have h1 := R₁.drop_le c (view D₁ v) i
      simp only [dropRewrite]
      omega

theorem Rule.run_comp {D₁ E₁ D₂ E₂ : ℕ} (R₁ : Rule Γ C K D₁ E₁) (R₂ : Rule Γ C K D₂ E₂)
    (c : C) (st : Fin K → List Γ) :
    (R₁.comp R₂).run c st = R₂.run (R₁.run c st).1 (R₁.run c st).2 := by
  have hv : ∀ k, (apply (view (D₁ + D₂) st) ((R₁.f c (view D₁ st)).2 k)).take D₂
      = (apply st ((R₁.f c (view D₁ st)).2 k)).take D₂ := fun k =>
    (take_apply st _ D₂ (R₁.drop_le c _ k)).symm
  simp only [Rule.run, Rule.comp, view_view]
  have hview : view D₂ (fun k => apply st ((R₁.f c (view D₁ st)).2 k))
      = fun k => (apply (view (D₁ + D₂) st) ((R₁.f c (view D₁ st)).2 k)).take D₂ := by
    funext k; rw [hv k]; rfl
  rw [hview]
  refine Prod.ext rfl (funext fun k => ?_)
  exact (apply_compose st _ _).symm

theorem IsLocal.comp {D₁ E₁ D₂ E₂ : ℕ} {Φ₁ Φ₂ : C → (Fin K → List Γ) → C × (Fin K → List Γ)}
    (h₁ : IsLocal D₁ E₁ Φ₁) (h₂ : IsLocal D₂ E₂ Φ₂) :
    IsLocal (D₁ + D₂) (E₁ + E₂) (fun c st => Φ₂ (Φ₁ c st).1 (Φ₁ c st).2) := by
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  refine ⟨R₁.comp R₂, fun c st => ?_⟩
  show Φ₂ (Φ₁ c st).1 (Φ₁ c st).2 = _
  rw [Rule.run_comp, hR₁, hR₂]

/-- The rule that only changes the control. -/
def Rule.control (g : C → (Fin K → List Γ) → C) (D : ℕ) : Rule Γ C K D 0 where
  f c v := (g c v, fun k => ⟨[], some k, 0⟩)
  pre_le _ _ _ := le_rfl
  drop_le _ _ _ := Nat.zero_le _

theorem Rule.run_control (g : C → (Fin K → List Γ) → C) (D : ℕ) (c : C) (st : Fin K → List Γ) :
    (Rule.control g D).run c st = (g c (view D st), st) := by
  simp [Rule.run, Rule.control, apply]

/-- **Iterating a local update stays local.** -/
theorem IsLocal.iterate {D E : ℕ} {Φ : C → (Fin K → List Γ) → C × (Fin K → List Γ)}
    (h : IsLocal D E Φ) : ∀ n : ℕ,
      IsLocal (D * n) (E * n) (fun c st => (fun x : C × (Fin K → List Γ) => Φ x.1 x.2)^[n] (c, st))
  | 0 => ⟨Rule.control (fun c _ => c) 0, fun c st => by simp [Rule.run_control]⟩
  | n + 1 => by
    have := (IsLocal.iterate h n).comp h
    have heq : (fun c st => (fun x : C × (Fin K → List Γ) => Φ x.1 x.2)^[n + 1] (c, st))
        = (fun c st => Φ ((fun x : C × (Fin K → List Γ) => Φ x.1 x.2)^[n] (c, st)).1
            ((fun x : C × (Fin K → List Γ) => Φ x.1 x.2)^[n] (c, st)).2) := by
      funext c st
      rw [Function.iterate_succ_apply']
    rw [heq, Nat.mul_succ, Nat.mul_succ]
    exact this

/-! ## Primitive rules and combinators -/

/-- Enlarge the depth and width of a rule. -/
def Rule.mono {D E D' E' : ℕ} (R : Rule Γ C K D E) (hD : D ≤ D') (hE : E ≤ E') :
    Rule Γ C K D' E' where
  f c v := R.f c (view D v)
  pre_le c v k := (R.pre_le c _ k).trans hE
  drop_le c v k := (R.drop_le c _ k).trans hD

theorem Rule.run_mono {D E D' E' : ℕ} (R : Rule Γ C K D E) (hD : D ≤ D') (hE : E ≤ E')
    (c : C) (st : Fin K → List Γ) : (R.mono hD hE).run c st = R.run c st := by
  have hv : view D (view D' st) = view D st := by
    funext k; simp only [view, List.take_take]; congr 1; omega
  simp [Rule.run, Rule.mono, hv]

theorem IsLocal.mono {D E D' E' : ℕ} {Φ : C → (Fin K → List Γ) → C × (Fin K → List Γ)}
    (h : IsLocal D E Φ) (hD : D ≤ D') (hE : E ≤ E') : IsLocal D' E' Φ := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R.mono hD hE, fun c st => by rw [Rule.run_mono, hR]⟩

/-- Choose between two rules by the control and the view. -/
def Rule.ite {D E : ℕ} (p : C → (Fin K → List Γ) → Bool) (R₁ R₂ : Rule Γ C K D E) :
    Rule Γ C K D E where
  f c v := if p c v then R₁.f c v else R₂.f c v
  pre_le c v k := by split <;> [exact R₁.pre_le c v k; exact R₂.pre_le c v k]
  drop_le c v k := by split <;> [exact R₁.drop_le c v k; exact R₂.drop_le c v k]

theorem IsLocal.ite {D E : ℕ} {Φ₁ Φ₂ : C → (Fin K → List Γ) → C × (Fin K → List Γ)}
    (p : C → (Fin K → List Γ) → Bool) (h₁ : IsLocal D E Φ₁) (h₂ : IsLocal D E Φ₂) :
    IsLocal D E (fun c st => if p c (view D st) then Φ₁ c st else Φ₂ c st) := by
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  refine ⟨Rule.ite p R₁ R₂, fun c st => ?_⟩
  simp only [Rule.run, Rule.ite]
  split <;> simp [hR₁, hR₂, Rule.run]

/-- The rewrite that keeps a stack. -/
def keep (k : Fin K) : Rewrite Γ K := ⟨[], some k, 0⟩

theorem apply_keep (st : Fin K → List Γ) (k : Fin K) : apply st (keep k) = st k := by
  simp [apply, keep]

/-- One stack operation on stack `k`, with the control update `g`. -/
def Rule.op (D : ℕ) (g : C → (Fin K → List Γ) → C) (k : Fin K)
    (r : C → (Fin K → List Γ) → Rewrite Γ K) (hpre : ∀ c v, (r c v).pre.length ≤ 1)
    (hdrop : ∀ c v, (r c v).drop ≤ D) : Rule Γ C K D 1 where
  f c v := (g c v, fun j => if j = k then r c v else keep j)
  pre_le c v j := by dsimp only; split <;> simp [hpre, keep]
  drop_le c v j := by dsimp only; split <;> simp [hdrop, keep]

theorem Rule.run_op (D : ℕ) (g : C → (Fin K → List Γ) → C) (k : Fin K)
    (r : C → (Fin K → List Γ) → Rewrite Γ K) (hpre : ∀ c v, (r c v).pre.length ≤ 1)
    (hdrop : ∀ c v, (r c v).drop ≤ D) (c : C) (st : Fin K → List Γ) :
    (Rule.op D g k r hpre hdrop).run c st =
      (g c (view D st), Function.update st k (apply st (r c (view D st)))) := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : j = k
  · subst hj; simp [Rule.run, Rule.op]
  · simp [Rule.run, Rule.op, hj, apply_keep]

/-- `push x` on stack `k`. -/
def pushRw (x : Γ) (k : Fin K) : Rewrite Γ K := ⟨[x], some k, 0⟩
/-- `drop` on stack `k` (pop). -/
def popRw (k : Fin K) : Rewrite Γ K := ⟨[], some k, 1⟩
/-- `copyFrom i` into a stack. -/
def copyRw (i : Fin K) : Rewrite Γ K := ⟨[], some i, 0⟩
/-- `clear`. -/
def clearRw : Rewrite Γ K := ⟨[], none, 0⟩

theorem apply_push (st : Fin K → List Γ) (x : Γ) (k : Fin K) : apply st (pushRw x k) = x :: st k := by
  simp [apply, pushRw]
theorem apply_pop (st : Fin K → List Γ) (k : Fin K) : apply st (popRw k) = (st k).tail := by
  simp [apply, popRw]
theorem apply_copy (st : Fin K → List Γ) (i : Fin K) : apply st (copyRw i) = st i := by
  simp [apply, copyRw]
theorem apply_clear (st : Fin K → List Γ) : apply st (clearRw : Rewrite Γ K) = [] := by
  simp [apply, clearRw]

end PalPeg.ScaLocal
