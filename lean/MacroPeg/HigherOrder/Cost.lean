import MacroPeg.HigherOrder.Bounds

/-!
# A cost model for the decision procedure

The steps of `decideHO`, counted along the recursion of `den` (the same kind of model as `Properties/DecideCost.lean`
for first-order grammars):

* `valSize N τ`: the entries of a value (the cost of comparing two values);
* `elemsCost N τ`: building the list `elems N τ` — every candidate table, and the monotonicity check of every pair of
  entries;
* `denCost N t`: a parser operator computes its result at `N+1` positions (a star at each position walks down
  through smaller ones); a lambda builds its table, one body evaluation per argument; an application enumerates the
  arguments to find its index;
* `decideCost`: `maxEnv` rounds, each evaluating every rule body, then the start term.

**Closed form** (`decideCost_le`): if every type in the grammar and the start term — rule types, function types of
applications — has order `≤ k+1`, and every argument and binder type order `≤ k`, then the cost is at most
`tower (k+1) (C · ((N+1)(N+2))²)`, with `C` computed from the syntax alone (`gConst`): exponential for first-order
grammars, doubly exponential for order 2, `(k+1)`-fold exponential for order `k+1`.
-/

namespace Shallot.MacroPeg.HO

/-! ## The model -/

def valSize (N : Nat) : Ty → Nat
  | .p => N + 1
  | .arr a b => (elems N a).length * valSize N b

def elemsCost (N : Nat) : Ty → Nat
  | .p => (allVecs (resElems N) (N + 1)).length * (N + 1)
  | .arr a b => elemsCost N a + elemsCost N b + (allVecs (elems N b) (elems N a).length).length *
      ((elems N a).length * valSize N b + (elems N a).length * (elems N a).length * (valSize N a + valSize N b))

def denCost (N : Nat) {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → Nat
  | _, _, .eps | _, _, .any | _, _, .chr _ | _, _, .range _ _ => (N + 1) * (N + 2)
  | _, _, .lit s => (N + 1) * (N + 2 + s.length)
  | _, _, .seq a b | _, _, .alt a b => denCost N a + denCost N b + (N + 1) * (N + 2)
  | _, _, .notP a => denCost N a + (N + 1) * (N + 2)
  | _, _, .star a => denCost N a + (N + 1) * (N + 1) * (N + 2)
  | _, _, .var i _ | _, _, .rule i _ => i + 1
  | _, _, @Tm.lam _ _ a _ body => elemsCost N a + (elems N a).length * (denCost N body + 1)
  | _, _, @Tm.app _ _ a _ f y => denCost N f + denCost N y + elemsCost N a + (elems N a).length * (valSize N a + 1)

def TBodies.cost (N : Nat) {R : List Ty} : {S : List Ty} → TBodies R S → Nat
  | [], _ => 0
  | _ :: _, (t, ts) => denCost N t + TBodies.cost N ts

/-- The steps of `decideHO G t x` with `N = |x|`. -/
def decideCost {R : List Ty} (G : TGrammar R) (t : Tm R [] .p) (N : Nat) : Nat :=
  maxEnv N R * G.bodies.cost N + denCost N t + N + 1

/-! ## Orders inside terms -/

/-- Binder and argument types have order `≤ k`. -/
def Tm.OrdOK (k : Nat) {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → Prop
  | _, _, .seq a b | _, _, .alt a b => a.OrdOK k ∧ b.OrdOK k
  | _, _, .star a | _, _, .notP a => a.OrdOK k
  | _, _, @Tm.lam _ _ a _ body => a.order ≤ k ∧ body.OrdOK k
  | _, _, @Tm.app _ _ a _ f y => a.order ≤ k ∧ f.OrdOK k ∧ y.OrdOK k
  | _, _, _ => True

def TBodies.OrdOK (k : Nat) {R : List Ty} : {S : List Ty} → TBodies R S → Prop
  | [], _ => True
  | _ :: _, (t, ts) => t.OrdOK k ∧ TBodies.OrdOK k ts

/-! ## Constants from the syntax -/

/-- The weight of building `elems τ`, in units of `polyP N`. -/
def Ty.cw : Ty → Nat
  | .p => 2
  | .arr a b => a.cw + b.cw + 5 * a.size + 3 * b.size + 10

/-- The weight of evaluating `t`, in units of `polyP N ^ 2`. -/
def Tm.cd {R : List Ty} : {Γ : List Ty} → {τ : Ty} → Tm R Γ τ → Nat
  | _, _, .eps | _, _, .any | _, _, .chr _ | _, _, .range _ _ => 1
  | _, _, .lit s => s.length + 1
  | _, _, .seq a b | _, _, .alt a b => a.cd + b.cd + 2
  | _, _, .notP a | _, _, .star a => a.cd + 2
  | _, _, .var i _ | _, _, .rule i _ => i + 1
  | _, _, @Tm.lam _ _ a _ body => a.cw + a.size + body.cd + 3
  | _, _, @Tm.app _ _ a _ f y => f.cd + y.cd + a.cw + 2 * a.size + 5

def TBodies.cd {R : List Ty} : {S : List Ty} → TBodies R S → Nat
  | [], _ => 0
  | _ :: _, (t, ts) => t.cd + TBodies.cd ts + 2

/-- The constant of the closed form. -/
def gConst {R : List Ty} (G : TGrammar R) (t : Tm R [] .p) : Nat :=
  tySizeSum R + R.length + G.bodies.cd + t.cd + 10

/-! ## Arithmetic on one tower height -/

theorem lin (c x P : Nat) : c * x * P = c * (P * x) := by rw [Nat.mul_assoc, Nat.mul_comm x P]

section Arith

variable (k : Nat)

local notation "T" => tower (k + 1)

theorem T_add (a b : Nat) : T a + T b ≤ T (a + b + 2) := Nat.le_trans (by omega) (tower_add (k + 1) a b)
theorem T_mul (a b : Nat) : T a * T b ≤ T (a + b + 2) := tower_mul k a b
theorem T_addc (a c : Nat) : T a + c ≤ T (a + c) := tower_add_const (k + 1) a c
theorem T_mulc (a c : Nat) : c * T a ≤ T (a + c) := tower_mul_const k a c

theorem le_T {x a : Nat} (h : x ≤ a) : x ≤ T a := Nat.le_trans h (le_tower _ _)

end Arith

/-! ## Bounds -/

section Bounds

variable (N k : Nat)

local notation "T" => tower (k + 1)
local notation "P" => polyP N

theorem le_P : N + 1 ≤ P := by unfold polyP; exact Nat.le_mul_of_pos_right _ (by omega)

theorem elems_le_T {τ : Ty} (h : τ.order ≤ k) : (elems N τ).length ≤ T (P * τ.size) :=
  Nat.le_trans (elems_length_le N τ) (sizeBound_le_tower N τ k h)

theorem valSize_le : ∀ τ : Ty, τ.order ≤ k → valSize N τ ≤ T (P * τ.size)
  | .p, _ => le_T k (by simpa [Ty.size, valSize] using le_P N)
  | .arr a b, h => by
    simp only [Ty.order] at h
    have hP := two_le_polyP N
    calc valSize N (a ⇒ b) = (elems N a).length * valSize N b := rfl
      _ ≤ T (P * a.size) * T (P * b.size) :=
          Nat.mul_le_mul (elems_le_T N k (by omega)) (valSize_le b (by omega))
      _ ≤ T (P * a.size + P * b.size + 2) := T_mul k _ _
      _ ≤ T (P * (a ⇒ b).size) := tower_mono _ (by simp only [Ty.size, Nat.mul_add, Nat.mul_one]; omega)

theorem elemsCost_le : ∀ τ : Ty, τ.order ≤ k → elemsCost N τ ≤ T (τ.cw * P)
  | .p, _ => by
    have hs : (allVecs (resElems N) (N + 1)).length ≤ T (P * Ty.p.size) := by
      have hl : (allVecs (resElems N) (N + 1)).length = sizeBound N .p := by
        rw [length_allVecs]; simp [resElems, sizeBound]
      rw [hl]; exact sizeBound_le_tower N .p k (Nat.zero_le _)
    have h1 := le_P N
    calc elemsCost N .p = (allVecs (resElems N) (N + 1)).length * (N + 1) := rfl
      _ ≤ (N + 1) * T (P * Ty.p.size) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hs
      _ ≤ T (P * Ty.p.size + (N + 1)) := T_mulc k _ _
      _ ≤ T (Ty.p.cw * P) := tower_mono _ (by simp only [Ty.size, Ty.cw]; omega)
  | .arr a b, h => by
    simp only [Ty.order] at h
    have hP := two_le_polyP N
    have ea := elemsCost_le a (by omega)
    have eb := elemsCost_le b (by omega)
    have la := elems_le_T N k (τ := a) (by omega)
    have va := valSize_le N k a (by omega)
    have vb := valSize_le N k b (by omega)
    have hV : (allVecs (elems N b) (elems N a).length).length ≤ T (P * (a ⇒ b).size) := by
      rw [length_allVecs]
      exact Nat.le_trans (pow_le_pow_both (by
          have := bot_mem N b; exact List.length_pos_of_mem this) (elems_length_le N b) (elems_length_le N a))
        (sizeBound_le_tower N (a ⇒ b) k (by simp only [Ty.order]; omega))
    -- the pieces, each a tower of height `k+1`
    have h₁ : (elems N a).length * valSize N b ≤ T (P * a.size + P * b.size + 2) :=
      Nat.le_trans (Nat.mul_le_mul la vb) (T_mul k _ _)
    have h₂ : (elems N a).length * (elems N a).length ≤ T (P * a.size + P * a.size + 2) :=
      Nat.le_trans (Nat.mul_le_mul la la) (T_mul k _ _)
    have h₃ : valSize N a + valSize N b ≤ T (P * a.size + P * b.size + 2) :=
      Nat.le_trans (Nat.add_le_add va vb) (T_add k _ _)
    have h₄ := Nat.le_trans (Nat.mul_le_mul h₂ h₃) (T_mul k _ _)
    have h₅ := Nat.le_trans (Nat.add_le_add h₁ h₄) (T_add k _ _)
    have h₆ := Nat.le_trans (Nat.mul_le_mul hV h₅) (T_mul k _ _)
    have h₇ := Nat.le_trans (Nat.add_le_add (Nat.add_le_add ea eb) h₆)
      (Nat.le_trans (Nat.add_le_add (T_add k _ _) (Nat.le_refl _)) (T_add k _ _))
    refine Nat.le_trans h₇ (tower_mono _ ?_)
    simp only [Ty.cw, Ty.size, Nat.add_mul, Nat.mul_add, Nat.mul_one, lin]
    omega

/-- `Q = P²`. -/
theorem P_le_Q : P ≤ P * P := Nat.le_mul_of_pos_left _ (by have := two_le_polyP N; omega)

theorem denCost_le {R : List Ty} : ∀ {Γ : List Ty} {τ : Ty} (t : Tm R Γ τ), t.OrdOK k →
    denCost N t ≤ T (t.cd * (P * P))
  | _, _, .eps, _ | _, _, .any, _ | _, _, .chr _, _ | _, _, .range _ _, _ =>
    le_T k (by simp only [Tm.cd, Nat.one_mul]; exact Nat.le_trans (Nat.le_refl _) (P_le_Q N))
  | _, _, .lit s, _ => by
    apply le_T k
    simp only [denCost, Tm.cd]
    have h1 : N + 2 + s.length ≤ (N + 2) * (s.length + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have := Nat.le_mul_of_pos_left s.length (show 0 < N + 2 by omega)
      omega
    have h2 : (N + 1) * (N + 2 + s.length) ≤ P * (s.length + 1) := by
      unfold polyP; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
    have h3 : P * (s.length + 1) ≤ (s.length + 1) * (P * P) := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (P_le_Q N)
    omega
  | _, _, .seq a b, h | _, _, .alt a b, h => by
    have ha := denCost_le a h.1
    have hb := denCost_le b h.2
    have hP := two_le_polyP N
    have hQ := P_le_Q N
    refine Nat.le_trans (Nat.add_le_add (Nat.le_trans (Nat.add_le_add ha hb) (T_add k _ _)) (Nat.le_refl _))
      (Nat.le_trans (T_addc k _ _) (tower_mono _ ?_))
    simp only [show (N + 1) * (N + 2) = polyP N from rfl, Tm.cd, Nat.add_mul]
    omega
  | _, _, .notP a, h => by
    have ha := denCost_le a h
    have hP := two_le_polyP N
    have hQ := P_le_Q N
    refine Nat.le_trans (Nat.add_le_add ha (Nat.le_refl _)) (Nat.le_trans (T_addc k _ _) (tower_mono _ ?_))
    simp only [show (N + 1) * (N + 2) = polyP N from rfl, Tm.cd, Nat.add_mul]
    omega
  | _, _, .star a, h => by
    have ha := denCost_le a h
    have hP := two_le_polyP N
    have hc : (N + 1) * (N + 1) * (N + 2) ≤ P * P := by
      have e : (N + 1) * (N + 1) * (N + 2) = (N + 1) * polyP N := by unfold polyP; rw [Nat.mul_assoc]
      rw [e]; exact Nat.mul_le_mul_right _ (le_P N)
    refine Nat.le_trans (Nat.add_le_add ha hc) (Nat.le_trans (T_addc k _ _) (tower_mono _ ?_))
    simp only [Tm.cd, Nat.add_mul]
    omega
  | _, _, .var i _, _ | _, _, .rule i _, _ => le_T k (by
      simp only [Tm.cd]; exact Nat.le_mul_of_pos_right _ (by have := two_le_polyP N; exact Nat.mul_pos (by omega) (by omega)))
  | _, _, @Tm.lam _ _ a b body, h => by
    have hb := denCost_le body h.2
    have hP := two_le_polyP N
    have hQ := P_le_Q N
    have ea := elemsCost_le N k a h.1
    have la := elems_le_T N k (τ := a) h.1
    have h₁ := Nat.le_trans (Nat.mul_le_mul la (Nat.le_trans (Nat.add_le_add hb (Nat.le_refl 1)) (T_addc k _ _)))
      (T_mul k _ _)
    refine Nat.le_trans (Nat.add_le_add ea h₁) (Nat.le_trans (T_add k _ _) (tower_mono _ ?_))
    simp only [Tm.cd, Nat.add_mul]
    have : a.cw * P ≤ a.cw * (P * P) := Nat.mul_le_mul_left _ hQ
    have : P * a.size ≤ a.size * (P * P) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hQ
    omega
  | _, _, @Tm.app _ _ a b f y, h => by
    have hf := denCost_le f h.2.1
    have hy := denCost_le y h.2.2
    have hP := two_le_polyP N
    have hQ := P_le_Q N
    have ea := elemsCost_le N k a h.1
    have la := elems_le_T N k (τ := a) h.1
    have va := valSize_le N k a h.1
    have h₁ := Nat.le_trans (Nat.mul_le_mul la (Nat.le_trans (Nat.add_le_add va (Nat.le_refl 1)) (T_addc k _ _)))
      (T_mul k _ _)
    refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hf hy) ea) h₁)
      (Nat.le_trans (Nat.add_le_add (Nat.add_le_add (T_add k _ _) (Nat.le_refl _)) (Nat.le_refl _))
        (Nat.le_trans (Nat.add_le_add (T_add k _ _) (Nat.le_refl _)) (Nat.le_trans (T_add k _ _) (tower_mono _ ?_))))
    simp only [Tm.cd, Nat.add_mul]
    have : a.cw * P ≤ a.cw * (P * P) := Nat.mul_le_mul_left _ hQ
    have : P * a.size ≤ a.size * (P * P) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hQ
    have : 2 * a.size * (P * P) = 2 * (a.size * (P * P)) := Nat.mul_assoc _ _ _
    omega

theorem bodiesCost_le {R : List Ty} : ∀ {S : List Ty} (ts : TBodies R S), TBodies.OrdOK k ts →
    TBodies.cost N ts ≤ T (TBodies.cd ts * (P * P))
  | [], _, _ => le_T k (by simp [TBodies.cost])
  | _ :: _, (t, ts), h => by
    have h₁ := denCost_le N k t h.1
    have h₂ := bodiesCost_le ts h.2
    have hQ : 1 ≤ P * P := by have := two_le_polyP N; exact Nat.mul_pos (by omega) (by omega)
    refine Nat.le_trans (Nat.add_le_add h₁ h₂) (Nat.le_trans (T_add k _ _) (tower_mono _ ?_))
    simp only [TBodies.cd, Nat.add_mul]
    omega

/-- **The closed form of the cost.** -/
theorem decideCost_le {R : List Ty} (G : TGrammar R) (t : Tm R [] .p) (hR : ∀ τ ∈ R, τ.order ≤ k + 1)
    (hG : TBodies.OrdOK k G.bodies) (ht : t.OrdOK k) :
    decideCost G t N ≤ tower (k + 1) (gConst G t * (polyP N * polyP N)) := by
  have hP := two_le_polyP N
  have hQ := P_le_Q N
  have hE := maxEnv_le_tower N k R hR
  have hB := bodiesCost_le N k G.bodies hG
  have hD := denCost_le N k t ht
  have h₁ := Nat.le_trans (Nat.mul_le_mul hE hB) (T_mul k _ _)
  have h₂ := Nat.le_trans (Nat.add_le_add h₁ hD) (T_add k _ _)
  have h₃ := Nat.le_trans (Nat.add_le_add h₂ (Nat.le_refl (N + 1))) (T_addc k _ _)
  refine Nat.le_trans (by unfold decideCost; omega) (Nat.le_trans h₃ (tower_mono _ ?_))
  simp only [gConst, Nat.add_mul]
  have : polyP N * tySizeSum R ≤ tySizeSum R * (polyP N * polyP N) := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hQ
  have : R.length ≤ R.length * (polyP N * polyP N) := Nat.le_mul_of_pos_right _ (by omega)
  have : N + 1 ≤ polyP N := le_P N
  omega

end Bounds

end Shallot.MacroPeg.HO
