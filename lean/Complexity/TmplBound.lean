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

theorem toBits_length : ∀ ts : List Nat, (toBits ts).length = 4 * ts.length
  | [] => rfl
  | t :: ts => by
    simp only [toBits, List.flatMap_cons, List.length_append] at *
    have := toBits_length ts
    simp only [toBits] at this
    rw [this]; simp [tokBits]; omega

theorem encName_length (x : Name) : (encName x).length = (x.map (· + 1)).sum + 1 := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [encName, List.flatMap_cons, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem sum_le_of_le (Z : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x ≤ Z) → l.sum ≤ l.length * Z
  | [], _ => by simp
  | a :: l, h => by
    have := sum_le_of_le Z l (fun x hx => h x (List.mem_cons_of_mem a hx))
    have := h a List.mem_cons_self
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]; omega

theorem flatMap_range_len_le {f : Nat → List Nat} (n c : Nat) (h : ∀ v, v < n → (toBits (f v)).length ≤ c) :
    (toBits ((List.range n).flatMap f)).length ≤ n * c := by
  induction n with
  | zero => simp [toBits]
  | succ n ih =>
    have h1 := ih (fun v hv => h v (by omega))
    have h2 := h n (by omega)
    have e : (toBits ((List.range (n + 1)).flatMap f)).length =
        (toBits ((List.range n).flatMap f)).length + (toBits (f n)).length := by
      rw [List.range_succ, List.flatMap_append]
      simp [toBits_length]; omega
    rw [e, Nat.succ_mul]; omega

/-- A template's output is no longer than its step bound. -/
theorem toBits_denote_le (Z : Nat) : ∀ (t : Tmpl) (e : TEnv), t.Small Z → e.S ≤ Z → e.T ≤ Z →
    (∀ i, e.ctr i ≤ Z) → (toBits (t.denote e)).length ≤ t.ucost Z
  | .nil, _, _, _, _, _ => by simp [Tmpl.denote, toBits, Tmpl.ucost]
  | .tok _, _, _, _, _, _ => by simp [Tmpl.denote, toBits, tokBits, Tmpl.ucost, tunit]; omega
  | .name ps, e, hs, hS, hT, hc => by
    simp only [Tmpl.denote, Tmpl.ucost, toBits_length, encName_length, List.map_map]
    have hv : ∀ x ∈ ps.map (fun p => Part.val e p + 1), x ≤ 2 * Z + 1 := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have := hs p hp
      cases p with
      | const n => simp only [Part.val]; simp only [Part.Small] at this; omega
      | ctr i => simp only [Part.val]; have := hc i; omega
      | rev i c => simp only [Part.val]; simp only [Part.Small] at this; omega
    have := sum_le_of_le (2 * Z + 1) _ hv
    rw [List.length_map] at this
    have h2 : ps.length * (2 * Z + 1) ≤ ps.length * (25 * (Z + 3)) := Nat.mul_le_mul_left _ (by omega)
    simp only [Function.comp_def, tunit]
    rw [Nat.add_mul, Nat.one_mul]
    have h3 : ps.length * (100 * (Z + 3)) = 4 * (ps.length * (25 * (Z + 3))) := by
      rw [show 100 * (Z + 3) = 4 * (25 * (Z + 3)) by omega]; rw [Nat.mul_left_comm]
    omega
  | .seq a b, e, hs, hS, hT, hc => by
    have ha := toBits_denote_le Z a e hs.1 hS hT hc
    have hb := toBits_denote_le Z b e hs.2 hS hT hc
    simp only [Tmpl.denote, Tmpl.ucost, toBits_length, List.length_append] at ha hb ⊢; omega
  | .forR i b body, e, hs, hS, hT, hc => by
    have hbv : b.val e ≤ Z := by
      cases b with
      | const n => exact hs.1
      | S => exact hS
      | T => exact hT
    simp only [Tmpl.denote, Tmpl.ucost]
    have := flatMap_range_len_le (f := fun v => body.denote (e.set i v)) (b.val e) (body.ucost Z) (fun v hv =>
      toBits_denote_le Z body (e.set i v) hs.2 hS hT (fun j => by
        simp only [TEnv.set]; split
        · omega
        · exact hc j))
    have : b.val e * body.ucost Z ≤ (Z + 1) * (body.ucost Z + 4 * tunit Z) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | .ite c a b, e, hs, hS, hT, hc => by
    have ha := toBits_denote_le Z a e hs.2.1 hS hT hc
    have hb := toBits_denote_le Z b e hs.2.2 hS hT hc
    simp only [Tmpl.denote, Tmpl.ucost]
    split <;> omega

theorem isPoly_pow {f : Nat → Nat} (hf : IsPoly f) : ∀ D : Nat, IsPoly (fun n => f n ^ D)
  | 0 => ⟨1, 0, fun n => by simp⟩
  | D + 1 => by
    have := isPoly_mul (isPoly_pow hf D) hf
    simpa [Nat.pow_succ] using this

end Complexity
