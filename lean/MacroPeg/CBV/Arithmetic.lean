import MacroPeg.CBV.Address
import Shallot.Peg.Separation.Reduce
import MacroPeg.HigherOrder.Mach.ValEnvTable

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

/-- Arithmetic needed for CBV table offsets and mixed-radix addresses. -/
inductive AddrExpr (V : Nat) where
  | num (n : Nat)
  | var (i : Fin V)
  | add (a b : AddrExpr V)
  | mul (a b : AddrExpr V)

namespace AddrExpr

def value {V : Nat} (f : Fin V → Nat) : AddrExpr V → Nat
  | .num n => n
  | .var i => f i
  | .add a b => value f a + value f b
  | .mul a b => value f a * value f b

def cost {V : Nat} (f : Fin V → Nat) : AddrExpr V → Nat
  | .num n => n + 1
  | .var _ => 1
  | .add a b => cost f a + cost f b + (3 * value f b + 8)
  | .mul a b => cost f a + cost f b + (value f b * (3 * value f a + 5) + 8)

structure Regs (K V : Nat) where
  out : Fin K
  a : Fin K
  b : Fin K
  tmp : Fin K
  vars : Fin V → Fin K
  ab : a ≠ b
  atmp : a ≠ tmp
  ao : a ≠ out
  btmp : b ≠ tmp
  bo : b ≠ out
  to : tmp ≠ out
  vo : ∀ i, vars i ≠ out

def compile {K V : Nat} (r : Regs K V) : AddrExpr V → NProg K
  | .num n => npushC r.out n
  | .var i => .prim (.dup (r.vars i) r.out (r.vo i))
  | .add a b =>
    .seq (compile r a) (.seq (compile r b)
      (.seq (nmv r.out r.a r.ao.symm) (.seq (nmv r.out r.b r.bo.symm)
        (.seq (addTo r.a r.b) (nmv r.b r.out r.bo)))))
  | .mul a b =>
    .seq (compile r a) (.seq (compile r b)
      (.seq (nmv r.out r.a r.ao.symm) (.seq (nmv r.out r.b r.bo.symm)
        (ve_mul r.a r.b r.tmp r.out r.btmp))))

/-- Only the variables occurring in an expression need a nonempty input frame. -/
def inputs {V : Nat} : AddrExpr V → List (Fin V)
  | .num _ => []
  | .var i => [i]
  | .add a b | .mul a b => inputs a ++ inputs b

/-- The address-arithmetic compiler preserves all input stacks and its scratch stacks. -/
theorem compile_runs_used {K V : Nat} (r : Regs K V) (f : Fin V → Nat) (e : AddrExpr V) :
    ∀ S : Lists K, (∀ i, i ∈ inputs e → ∃ l, S (r.vars i) = l ++ [f i]) → S r.tmp = [] →
    NRuns (compile r e) S (S.set r.out (S r.out ++ [value f e])) (cost f e) := by
  have hab := r.ab
  have hat := r.atmp
  have hao := r.ao
  have hbt := r.btmp
  have hbo := r.bo
  have hto := r.to
  induction e with
  | num n => intro S _ _; exact nruns_pushC _ _ _
  | var i =>
    intro S hf _
    obtain ⟨l, hl⟩ := hf i (by simp [inputs])
    exact nruns_dup _ _ (r.vo i) S hl
  | add a b ha hb =>
    intro S hf ht
    have x₁ := ha S (fun i hi => hf i (by simp only [inputs, List.mem_append]; exact Or.inl hi)) ht
    let S₁ := S.set r.out (S r.out ++ [value f a])
    have hf₁ : ∀ i, i ∈ inputs b → ∃ l, S₁ (r.vars i) = l ++ [f i] := by
      intro i hi
      rw [show S₁ (r.vars i) = S (r.vars i) from Lists.set_ne _ _ (r.vo i)]
      exact hf i (by simp only [inputs, List.mem_append]; exact Or.inr hi)
    have ht₁ : S₁ r.tmp = [] := by simp [Lists.set, S₁, Lists.set, r.to, ht]
    have x₂ := hb S₁ hf₁ ht₁
    let S₂ := S₁.set r.out (S₁ r.out ++ [value f b])
    have hy : S₂ r.out = (S r.out ++ [value f a]) ++ [value f b] := by simp [Lists.set, S₂, S₁]
    have x₃ := nruns_mv r.out r.a r.ao.symm S₂ hy
    let S₃ := (S₂.set r.a (S₂ r.a ++ [value f b])).set r.out (S r.out ++ [value f a])
    have hx : S₃ r.out = S r.out ++ [value f a] := by simp [Lists.set, S₃, r.ao]
    have x₄ := nruns_mv r.out r.b r.bo.symm S₃ hx
    let S₄ := (S₃.set r.b (S₃ r.b ++ [value f a])).set r.out (S r.out)
    have hA : S₄ r.a = S r.a ++ [value f b] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.ab, r.ao]
    have hB : S₄ r.b = S r.b ++ [value f a] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.ab.symm, r.bo]
    have hO : S₄ r.out = S r.out := by simp [Lists.set, S₄, r.bo]
    have hT : S₄ r.tmp = [] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.to, r.atmp.symm, r.btmp.symm, ht]
    have x₅ := nruns_addTo r.a r.b r.ab S₄ hA hB
    let S₅ := (S₄.set r.a (S r.a)).set r.b (S r.b ++ [value f a + value f b])
    have hB₅ : S₅ r.b = S r.b ++ [value f a + value f b] := by simp [Lists.set, S₅]
    have x₆ := nruns_mv r.b r.out r.bo S₅ hB₅
    have he : (S₅.set r.out (S₅ r.out ++ [value f a + value f b])).set r.b (S r.b) =
        S.set r.out (S r.out ++ [value f (.add a b)]) := by
      simp only [S₅, S₄, S₃, S₂, S₁, value]
      funext k
      by_cases hko : k = r.out
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      by_cases hka : k = r.a
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      by_cases hkb : k = r.b
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      simp [Lists.set, hko, hka, hkb]
    rw [he] at x₆
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq x₆))))).mono (by simp only [cost]; omega)
  | mul a b ha hb =>
    intro S hf ht
    have x₁ := ha S (fun i hi => hf i (by simp only [inputs, List.mem_append]; exact Or.inl hi)) ht
    let S₁ := S.set r.out (S r.out ++ [value f a])
    have hf₁ : ∀ i, i ∈ inputs b → ∃ l, S₁ (r.vars i) = l ++ [f i] := by
      intro i hi
      rw [show S₁ (r.vars i) = S (r.vars i) from Lists.set_ne _ _ (r.vo i)]
      exact hf i (by simp only [inputs, List.mem_append]; exact Or.inr hi)
    have ht₁ : S₁ r.tmp = [] := by simp [Lists.set, S₁, Lists.set, r.to, ht]
    have x₂ := hb S₁ hf₁ ht₁
    let S₂ := S₁.set r.out (S₁ r.out ++ [value f b])
    have hy : S₂ r.out = (S r.out ++ [value f a]) ++ [value f b] := by simp [Lists.set, S₂, S₁]
    have x₃ := nruns_mv r.out r.a r.ao.symm S₂ hy
    let S₃ := (S₂.set r.a (S₂ r.a ++ [value f b])).set r.out (S r.out ++ [value f a])
    have hx : S₃ r.out = S r.out ++ [value f a] := by simp [Lists.set, S₃, r.ao]
    have x₄ := nruns_mv r.out r.b r.bo.symm S₃ hx
    let S₄ := (S₃.set r.b (S₃ r.b ++ [value f a])).set r.out (S r.out)
    have hA : S₄ r.a = S r.a ++ [value f b] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.ab, r.ao]
    have hB : S₄ r.b = S r.b ++ [value f a] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.ab.symm, r.bo]
    have hO : S₄ r.out = S r.out := by simp [Lists.set, S₄, r.bo]
    have hT : S₄ r.tmp = [] := by simp [Lists.set, S₄, S₃, S₂, S₁, r.to, r.atmp.symm, r.btmp.symm, ht]
    have x₅ := ve_mul_runs r.a r.b r.tmp r.out r.btmp r.ab r.atmp r.ao r.bo r.to S₄ hA hB hT
    have he : ((S₄.set r.a (S r.a)).set r.b (S r.b)).set r.out
        (S₄ r.out ++ [value f b * value f a]) = S.set r.out (S r.out ++ [value f (.mul a b)]) := by
      rw [hO]
      simp only [S₄, S₃, S₂, S₁, value, Nat.mul_comm]
      funext k
      by_cases hko : k = r.out
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      by_cases hka : k = r.a
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      by_cases hkb : k = r.b
      · subst k; simp [Lists.set, hab, hao, hbo, Ne.symm hab, Ne.symm hao, Ne.symm hbo]
      simp [Lists.set, hko, hka, hkb]
    rw [he] at x₅
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by simp only [cost]; omega)

/-- Convenience rule when every variable register has a top value. -/
theorem compile_runs {K V : Nat} (r : Regs K V) (f : Fin V → Nat) (e : AddrExpr V)
    (S : Lists K) (hf : ∀ i, ∃ l, S (r.vars i) = l ++ [f i]) (ht : S r.tmp = []) :
    NRuns (compile r e) S (S.set r.out (S r.out ++ [value f e])) (cost f e) :=
  compile_runs_used r f e S (fun i _ => hf i) ht

/-- Address expressions are polynomial when their input registers are polynomially bounded functions. -/
theorem value_poly {V : Nat} (f : Nat → Fin V → Nat)
    (hf : ∀ i, IsPoly (fun n => f n i)) (e : AddrExpr V) : IsPoly (fun n => value (f n) e) := by
  induction e with
  | num n => exact isPoly_const n
  | var i => exact hf i
  | add a b ha hb => exact isPoly_add ha hb
  | mul a b ha hb => exact isPoly_mul ha hb

/-- The verified address program has polynomial stack time, counting arithmetic operations in unary. -/
theorem cost_poly {V : Nat} (f : Nat → Fin V → Nat)
    (hf : ∀ i, IsPoly (fun n => f n i)) (e : AddrExpr V) : IsPoly (fun n => cost (f n) e) := by
  induction e with
  | num n => exact isPoly_const (n + 1)
  | var _ => exact isPoly_const 1
  | add a b ha hb =>
    exact isPoly_add (isPoly_add ha hb)
      (isPoly_add (isPoly_mul (isPoly_const 3) (value_poly f hf b)) (isPoly_const 8))
  | mul a b ha hb =>
    exact isPoly_add (isPoly_add ha hb)
      (isPoly_add (isPoly_mul (value_poly f hf b)
        (isPoly_add (isPoly_mul (isPoly_const 3) (value_poly f hf a)) (isPoly_const 5))) (isPoly_const 8))

def power {V : Nat} (a : AddrExpr V) : Nat → AddrExpr V
  | 0 => .num 1
  | k + 1 => .mul (power a k) a

theorem value_power {V : Nat} (f : Fin V → Nat) (a : AddrExpr V) (k : Nat) :
    value f (power a k) = value f a ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power, value, ih, Nat.pow_succ]

def sumExpr {V : Nat} : List (AddrExpr V) → AddrExpr V
  | [] => .num 0
  | e :: es => .add e (sumExpr es)

theorem value_sumExpr {V : Nat} (f : Fin V → Nat) (es : List (AddrExpr V)) :
    value f (sumExpr es) = (es.map (value f)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sumExpr, value, ih]

def rankExpr {V : Nat} (base : AddrExpr V) : List (AddrExpr V) → AddrExpr V
  | [] => .num 0
  | a :: as => .add (.mul a (power base as.length)) (rankExpr base as)

theorem value_rankExpr {V : Nat} (f : Fin V → Nat) (base : AddrExpr V) (as : List (AddrExpr V)) :
    value f (rankExpr base as) = wordRank (value f base) (as.map (value f)) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [rankExpr, value, value_power, wordRank, ih]

def widthExpr {V : Nat} (g : MGrammar) (i : Nat) (base positions : AddrExpr V) : AddrExpr V :=
  match ruleAtM g.rules i with
  | none => .num 0
  | some r => .mul (power base r.arity) positions

def addressExpr {V : Nat} (g : MGrammar) (i : Nat) (base positions pos : AddrExpr V)
    (args : List (AddrExpr V)) : AddrExpr V :=
  .add (.add (sumExpr ((List.range i).map (fun j => widthExpr g j base positions)))
    (.mul (rankExpr base args) positions)) pos

/-- The compiled expression is the actual arithmetic address of a CBV table cell. -/
theorem value_addressExpr {V : Nat} (f : Fin V → Nat) (g : MGrammar) (x : List Char) (i p : Nat)
    (base positions pos : AddrExpr V) (args : List (AddrExpr V))
    (hb : value f base = (subStrs x).length) (hn : value f positions = x.length + 1) (hp : value f pos = p) :
    value f (addressExpr g i base positions pos args) = address g x i (args.map (value f)) p := by
  have ho : value f (sumExpr ((List.range i).map (fun j => widthExpr g j base positions))) = ruleOffset g x i := by
    rw [value_sumExpr, List.map_map]
    unfold ruleOffset
    congr 1
    apply List.map_congr_left
    intro j _
    cases hr : ruleAtM g.rules j <;> simp [Function.comp_def, widthExpr, ruleWidth, hr, value, value_power, hb, hn]
  simp only [addressExpr, value, ho, value_rankExpr, hb, hn, hp, address]

end AddrExpr
end Shallot.MacroPeg.CBV
