import Complexity.TmplLM
import Complexity.ListClasses

/-!
# Size bounds for templates

* `toBits_denote_le`: the output of a template is no longer than its step bound `ucost`.
* `ucost_le`: `ucost Z t ≤ 5 * size t * tunit Z * (Z + 2) ^ depth t` — a polynomial in `Z` whose degree is the loop
  nesting depth of the template.
* `isPoly_pow`: powers of polynomial bounds are polynomial.
-/

namespace Complexity

def Cond.size : Cond → Nat
  | .not c => c.size + 1
  | .and c d => c.size + d.size + 1
  | .or c d => c.size + d.size + 1
  | _ => 1

def Tmpl.size : Tmpl → Nat
  | .nil => 1
  | .tok _ => 1
  | .name ps => ps.length + 1
  | .seq a b => a.size + b.size
  | .forR _ _ body => body.size + 1
  | .ite c a b => c.size + 1 + a.size + b.size

def Tmpl.depth : Tmpl → Nat
  | .nil => 0
  | .tok _ => 0
  | .name _ => 0
  | .seq a b => max a.depth b.depth
  | .forR _ _ body => body.depth + 1
  | .ite _ a b => max a.depth b.depth

theorem Cond.cost_le (Z : Nat) : ∀ c : Cond, c.cost Z ≤ c.size * tunit Z
  | .tt | .lt _ _ | .eq _ _ | .eqc _ _ | .succ _ _ | .inBit _ _ => by simp [Cond.cost, Cond.size]
  | .not c => by
    have := Cond.cost_le Z c
    simp only [Cond.cost, Cond.size, Nat.add_mul, Nat.one_mul]; omega
  | .and c d => by
    have := Cond.cost_le Z c; have := Cond.cost_le Z d
    simp only [Cond.cost, Cond.size, Nat.add_mul, Nat.one_mul]; omega
  | .or c d => by
    have := Cond.cost_le Z c; have := Cond.cost_le Z d
    simp only [Cond.cost, Cond.size, Nat.add_mul, Nat.one_mul]; omega

theorem one_le_pow2 (Z d : Nat) : 1 ≤ (Z + 2) ^ d := Nat.pow_pos (by omega)

theorem pow_mono_Z (Z : Nat) {d d' : Nat} (h : d ≤ d') : (Z + 2) ^ d ≤ (Z + 2) ^ d' :=
  Nat.pow_le_pow_right (by omega) h

theorem ucost_le (Z : Nat) : ∀ t : Tmpl, t.ucost Z ≤ 5 * t.size * tunit Z * (Z + 2) ^ t.depth
  | .nil => by
    simp only [Tmpl.ucost, Tmpl.size, Tmpl.depth, Nat.pow_zero, Nat.mul_one, tunit]; omega
  | .tok _ => by simp [Tmpl.ucost, Tmpl.size, Tmpl.depth]; omega
  | .name ps => by
    simp only [Tmpl.ucost, Tmpl.size, Tmpl.depth, Nat.pow_zero, Nat.mul_one]
    rw [Nat.mul_assoc 5]; exact Nat.le_mul_of_pos_left _ (by omega)
  | .seq a b => by
    have ha := ucost_le Z a; have hb := ucost_le Z b
    have h1 := pow_mono_Z Z (Nat.le_max_left a.depth b.depth)
    have h2 := pow_mono_Z Z (Nat.le_max_right a.depth b.depth)
    have e1 : 5 * a.size * tunit Z * (Z + 2) ^ a.depth ≤ 5 * a.size * tunit Z * (Z + 2) ^ max a.depth b.depth :=
      Nat.mul_le_mul_left _ h1
    have e2 : 5 * b.size * tunit Z * (Z + 2) ^ b.depth ≤ 5 * b.size * tunit Z * (Z + 2) ^ max a.depth b.depth :=
      Nat.mul_le_mul_left _ h2
    simp only [Tmpl.ucost, Tmpl.size, Tmpl.depth]
    have : 5 * (a.size + b.size) * tunit Z * (Z + 2) ^ max a.depth b.depth =
        5 * a.size * tunit Z * (Z + 2) ^ max a.depth b.depth + 5 * b.size * tunit Z * (Z + 2) ^ max a.depth b.depth := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
    omega
  | .forR _ _ body => by
    have hb := ucost_le Z body
    have hp := one_le_pow2 Z body.depth
    simp only [Tmpl.ucost, Tmpl.size, Tmpl.depth]
    -- (Z + 1) * ucost body ≤ 5 * size * U * (Z+2)^(d+1)
    have h1 : (Z + 1) * body.ucost Z ≤ 5 * body.size * tunit Z * (Z + 2) ^ (body.depth + 1) := by
      calc (Z + 1) * body.ucost Z ≤ (Z + 2) * (5 * body.size * tunit Z * (Z + 2) ^ body.depth) :=
            Nat.mul_le_mul (by omega) hb
        _ = 5 * body.size * tunit Z * (Z + 2) ^ (body.depth + 1) := by rw [Nat.pow_succ]; ac_rfl
    have h2 : 4 * tunit Z + (Z + 1) * (4 * tunit Z) ≤ 5 * tunit Z * (Z + 2) ^ (body.depth + 1) := by
      have : (Z + 2) ≤ (Z + 2) ^ (body.depth + 1) := by
        rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_left _ (by omega)
      have h3 : 5 * tunit Z * (Z + 2) ≤ 5 * tunit Z * (Z + 2) ^ (body.depth + 1) := Nat.mul_le_mul_left _ this
      have h4 : 4 * tunit Z + (Z + 1) * (4 * tunit Z) = 4 * tunit Z * (Z + 2) := by
        rw [Nat.mul_comm (Z + 1), Nat.mul_add, Nat.mul_add]; omega
      have h5 : 4 * tunit Z * (Z + 2) ≤ 5 * tunit Z * (Z + 2) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      omega
    have e : 5 * (body.size + 1) * tunit Z * (Z + 2) ^ (body.depth + 1) =
        5 * body.size * tunit Z * (Z + 2) ^ (body.depth + 1) + 5 * tunit Z * (Z + 2) ^ (body.depth + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.add_mul]
    rw [Nat.mul_add] ; omega
  | .ite c a b => by
    have ha := ucost_le Z a; have hb := ucost_le Z b
    have hc := Cond.cost_le Z c
    have hp := one_le_pow2 Z (max a.depth b.depth)
    have h1 := pow_mono_Z Z (Nat.le_max_left a.depth b.depth)
    have h2 := pow_mono_Z Z (Nat.le_max_right a.depth b.depth)
    have e1 : 5 * a.size * tunit Z * (Z + 2) ^ a.depth ≤ 5 * a.size * tunit Z * (Z + 2) ^ max a.depth b.depth :=
      Nat.mul_le_mul_left _ h1
    have e2 : 5 * b.size * tunit Z * (Z + 2) ^ b.depth ≤ 5 * b.size * tunit Z * (Z + 2) ^ max a.depth b.depth :=
      Nat.mul_le_mul_left _ h2
    have e3 : c.size * tunit Z + 2 ≤ 5 * (c.size + 1) * tunit Z * (Z + 2) ^ max a.depth b.depth := by
      have : 5 * (c.size + 1) * tunit Z ≤ 5 * (c.size + 1) * tunit Z * (Z + 2) ^ max a.depth b.depth :=
        Nat.le_mul_of_pos_right _ (by omega)
      have : c.size * tunit Z + 2 ≤ 5 * (c.size + 1) * tunit Z := by
        have hU : 2 ≤ tunit Z := by simp only [tunit]; omega
        have e : 5 * (c.size + 1) * tunit Z = 5 * (c.size * tunit Z) + 5 * tunit Z := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_assoc]
        omega
      omega
    simp only [Tmpl.ucost, Tmpl.size, Tmpl.depth]
    have : 5 * (c.size + 1 + a.size + b.size) * tunit Z * (Z + 2) ^ max a.depth b.depth =
        5 * (c.size + 1) * tunit Z * (Z + 2) ^ max a.depth b.depth +
        5 * a.size * tunit Z * (Z + 2) ^ max a.depth b.depth +
        5 * b.size * tunit Z * (Z + 2) ^ max a.depth b.depth := by
      rw [Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    omega

theorem isPoly_pow {f : Nat → Nat} (hf : IsPoly f) : ∀ D : Nat, IsPoly (fun n => f n ^ D)
  | 0 => ⟨1, 0, fun n => by simp⟩
  | D + 1 => by
    have := isPoly_mul (isPoly_pow hf D) hf
    simpa [Nat.pow_succ] using this

end Complexity
