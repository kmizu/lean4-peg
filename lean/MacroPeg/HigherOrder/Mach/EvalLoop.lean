import MacroPeg.HigherOrder.Mach.EvalLoopSpec
import Complexity.NFrame

/-!
# The evaluation loops on stacks

`evalP p` runs the whole evaluation stage with an item program `p`: it lays out the starting rule values, runs the
rounds of `fixT` (each body's items with `p`, keeping the top vector), runs the start items and answers whether the
code at the end of the input is `2` (`evalP_runs`).

Layout: the fuel is on `11`; the start items are moved (reversed, with their count on top) onto `6`, above whatever
`6` held; each round lays the bodies out on `STA` (`12`) and puts the finished numbers back on `BOD`; the new values
gather on `RV2`/`RVL2` and are compared with `RV`/`RVL` (`loop_eqP`). Scratch `18`–`26` is emptied before each item.

The states the program passes through are described by a record `Cf` of the stacks it uses (`Cf.toL`), so that
updates of stacks become record updates.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## States as records -/

/-- The stacks the evaluation loops use; the others are kept from a base state. -/
structure Cf where
  ev : List Nat
  evl : List Nat
  rv : List Nat
  w : List Nat
  rts : List Nat
  bod : List Nat
  fuel : List Nat
  sta : List Nat
  it : List Nat
  rvl : List Nat
  rv2 : List Nat
  rvl2 : List Nat
  s18 : List Nat
  s19 : List Nat
  s20 : List Nat
  s21 : List Nat
  s22 : List Nat
  s23 : List Nat
  s24 : List Nat
  s25 : List Nat
  s26 : List Nat
  valt : List Nat

/-- The stacks of a record over the base `B`. -/
def Cf.toL (B : Lists NK) (c : Cf) : Lists NK := fun i =>
  if i.val = 3 then c.ev else if i.val = 4 then c.evl else if i.val = 5 then c.rv else if i.val = 6 then c.w
  else if i.val = 9 then c.rts else if i.val = 10 then c.bod else if i.val = 11 then c.fuel
  else if i.val = 12 then c.sta else if i.val = 14 then c.it else if i.val = 15 then c.rvl
  else if i.val = 16 then c.rv2 else if i.val = 17 then c.rvl2 else if i.val = 18 then c.s18
  else if i.val = 19 then c.s19 else if i.val = 20 then c.s20 else if i.val = 21 then c.s21
  else if i.val = 22 then c.s22 else if i.val = 23 then c.s23 else if i.val = 24 then c.s24
  else if i.val = 25 then c.s25 else if i.val = 26 then c.s26 else if i.val = 37 then c.valt else B i

section ToL
variable (B : Lists NK) (c : Cf) (v : List Nat)

@[simp] theorem loop_set_ev : (c.toL B).set 3 v = ({ c with ev := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 3
  · subst h; rfl
  · have : i.val ≠ 3 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_ev : (c.toL B) 3 = c.ev := rfl

@[simp] theorem loop_set_evl : (c.toL B).set 4 v = ({ c with evl := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 4
  · subst h; rfl
  · have : i.val ≠ 4 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_evl : (c.toL B) 4 = c.evl := rfl

@[simp] theorem loop_set_rv : (c.toL B).set 5 v = ({ c with rv := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 5
  · subst h; rfl
  · have : i.val ≠ 5 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_rv : (c.toL B) 5 = c.rv := rfl

@[simp] theorem loop_set_w : (c.toL B).set 6 v = ({ c with w := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 6
  · subst h; rfl
  · have : i.val ≠ 6 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_w : (c.toL B) 6 = c.w := rfl

@[simp] theorem loop_set_rts : (c.toL B).set 9 v = ({ c with rts := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 9
  · subst h; rfl
  · have : i.val ≠ 9 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_rts : (c.toL B) 9 = c.rts := rfl

@[simp] theorem loop_set_bod : (c.toL B).set 10 v = ({ c with bod := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 10
  · subst h; rfl
  · have : i.val ≠ 10 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_bod : (c.toL B) 10 = c.bod := rfl

@[simp] theorem loop_set_fuel : (c.toL B).set 11 v = ({ c with fuel := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 11
  · subst h; rfl
  · have : i.val ≠ 11 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_fuel : (c.toL B) 11 = c.fuel := rfl

@[simp] theorem loop_set_sta : (c.toL B).set 12 v = ({ c with sta := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 12
  · subst h; rfl
  · have : i.val ≠ 12 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_sta : (c.toL B) 12 = c.sta := rfl

@[simp] theorem loop_set_it : (c.toL B).set 14 v = ({ c with it := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 14
  · subst h; rfl
  · have : i.val ≠ 14 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_it : (c.toL B) 14 = c.it := rfl

@[simp] theorem loop_set_rvl : (c.toL B).set 15 v = ({ c with rvl := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 15
  · subst h; rfl
  · have : i.val ≠ 15 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_rvl : (c.toL B) 15 = c.rvl := rfl

@[simp] theorem loop_set_rv2 : (c.toL B).set 16 v = ({ c with rv2 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 16
  · subst h; rfl
  · have : i.val ≠ 16 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_rv2 : (c.toL B) 16 = c.rv2 := rfl

@[simp] theorem loop_set_rvl2 : (c.toL B).set 17 v = ({ c with rvl2 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 17
  · subst h; rfl
  · have : i.val ≠ 17 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_rvl2 : (c.toL B) 17 = c.rvl2 := rfl

@[simp] theorem loop_set_s18 : (c.toL B).set 18 v = ({ c with s18 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 18
  · subst h; rfl
  · have : i.val ≠ 18 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s18 : (c.toL B) 18 = c.s18 := rfl

@[simp] theorem loop_set_s19 : (c.toL B).set 19 v = ({ c with s19 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 19
  · subst h; rfl
  · have : i.val ≠ 19 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s19 : (c.toL B) 19 = c.s19 := rfl

@[simp] theorem loop_set_s20 : (c.toL B).set 20 v = ({ c with s20 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 20
  · subst h; rfl
  · have : i.val ≠ 20 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s20 : (c.toL B) 20 = c.s20 := rfl

@[simp] theorem loop_set_s21 : (c.toL B).set 21 v = ({ c with s21 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 21
  · subst h; rfl
  · have : i.val ≠ 21 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s21 : (c.toL B) 21 = c.s21 := rfl

@[simp] theorem loop_set_s22 : (c.toL B).set 22 v = ({ c with s22 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 22
  · subst h; rfl
  · have : i.val ≠ 22 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s22 : (c.toL B) 22 = c.s22 := rfl

@[simp] theorem loop_set_s23 : (c.toL B).set 23 v = ({ c with s23 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 23
  · subst h; rfl
  · have : i.val ≠ 23 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s23 : (c.toL B) 23 = c.s23 := rfl

@[simp] theorem loop_set_s24 : (c.toL B).set 24 v = ({ c with s24 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 24
  · subst h; rfl
  · have : i.val ≠ 24 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s24 : (c.toL B) 24 = c.s24 := rfl

@[simp] theorem loop_set_s25 : (c.toL B).set 25 v = ({ c with s25 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 25
  · subst h; rfl
  · have : i.val ≠ 25 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s25 : (c.toL B) 25 = c.s25 := rfl

@[simp] theorem loop_set_s26 : (c.toL B).set 26 v = ({ c with s26 := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 26
  · subst h; rfl
  · have : i.val ≠ 26 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_s26 : (c.toL B) 26 = c.s26 := rfl

@[simp] theorem loop_set_valt : (c.toL B).set 37 v = ({ c with valt := v }).toL B := by
  funext i; simp only [Lists.set, Cf.toL]; by_cases h : i = 37
  · subst h; rfl
  · have : i.val ≠ 37 := fun e => h (Fin.ext e)
    simp [h, this]

@[simp] theorem loop_get_valt : (c.toL B) 37 = c.valt := rfl

@[simp] theorem loop_get_base0 : (c.toL B) 0 = B 0 := rfl
@[simp] theorem loop_get_base1 : (c.toL B) 1 = B 1 := rfl
@[simp] theorem loop_get_base2 : (c.toL B) 2 = B 2 := rfl
@[simp] theorem loop_get_base7 : (c.toL B) 7 = B 7 := rfl
@[simp] theorem loop_get_base8 : (c.toL B) 8 = B 8 := rfl
@[simp] theorem loop_get_base13 : (c.toL B) 13 = B 13 := rfl
@[simp] theorem loop_get_base27 : (c.toL B) 27 = B 27 := rfl
@[simp] theorem loop_get_base28 : (c.toL B) 28 = B 28 := rfl
@[simp] theorem loop_get_base29 : (c.toL B) 29 = B 29 := rfl
@[simp] theorem loop_get_base30 : (c.toL B) 30 = B 30 := rfl
@[simp] theorem loop_get_base31 : (c.toL B) 31 = B 31 := rfl
@[simp] theorem loop_get_base32 : (c.toL B) 32 = B 32 := rfl
@[simp] theorem loop_get_base33 : (c.toL B) 33 = B 33 := rfl
@[simp] theorem loop_get_base34 : (c.toL B) 34 = B 34 := rfl
@[simp] theorem loop_get_base35 : (c.toL B) 35 = B 35 := rfl
@[simp] theorem loop_get_base36 : (c.toL B) 36 = B 36 := rfl
@[simp] theorem loop_get_base38 : (c.toL B) 38 = B 38 := rfl
@[simp] theorem loop_get_base39 : (c.toL B) 39 = B 39 := rfl

end ToL

/-! ## Loops one pass at a time -/

theorem loop_unroll {i : Fin NK} {c : NTest} {p : NProg NK} {S S₁ S₂ : Lists NK} {T₁ T₂ : Nat}
    (hc : c.eval (S i) = true) (h₁ : NRuns p S S₁ T₁) (h₂ : NRuns (.loop i c p) S₁ S₂ T₂) :
    NRuns (.loop i c p) S S₂ (T₁ + 1 + T₂) :=
  let ⟨t₁, ht₁, x₁⟩ := h₁; let ⟨t₂, ht₂, x₂⟩ := h₂; ⟨t₁ + 1 + t₂, by omega, .loopC trivial hc x₁ x₂⟩

/-! ## Counting two numbers down together

`loop_minP mark` lowers the numbers `t` (stack `25`) and `L` (stack `26`) together until one of them is `0`: then
`25` holds `0` and `26` holds `L - t` if `t ≤ L`, else `1` (with `mark`) or `0`. It takes about `min t L` steps. -/

def loop_minElse (mark : Bool) : NProg NK :=
  if mark then .seq (.prim (.pop 25)) (.seq (.prim (.pushZ 25)) (.prim (.inc 26)))
  else .seq (.prim (.pop 25)) (.prim (.pushZ 25))

def loop_minP (mark : Bool) : NProg NK :=
  .loop 25 .pos (.ite 26 .pos (.seq (.prim (.dec 25)) (.prim (.dec 26))) (loop_minElse mark))

def loop_minRes (mark : Bool) (t L : Nat) : Nat := if t ≤ L then L - t else if mark then 1 else 0

/-- Two updates of `25` and `26` in either order. -/
theorem loop_set2526 (S : Lists NK) (a b a' b' : List Nat) :
    (((S.set 25 a).set 26 b).set 25 a').set 26 b' = (S.set 25 a').set 26 b' := by
  funext x; simp only [Lists.set]; by_cases h₁ : x = 26 <;> by_cases h₂ : x = 25 <;> simp [h₁, h₂]

theorem loop_minP_runs (mark : Bool) :
    ∀ (L t : Nat) (S : Lists NK), S 25 = [t] → S 26 = [L] →
      NRuns (loop_minP mark) S ((S.set 25 [0]).set 26 [loop_minRes mark t L]) (5 * L + 6)
  | L, 0, S, h25, h26 => by
    have e : (S.set 25 [0]).set 26 [loop_minRes mark 0 L] = S := by
      simp only [loop_minRes, Nat.zero_le, if_true, Nat.sub_zero]
      rw [← h25, ← h26, Lists.set_get_self, Lists.set_get_self]
    rw [e]
    exact (nruns_loop_exit (by simp [h25, NTest.eval])).mono (by omega)
  | 0, t + 1, S, h25, h26 => by
    have x₁ := nruns_pop 25 S (l := []) (v := t + 1) (by simpa using h25)
    have x₂ := nruns_pushZ 25 (S.set 25 [])
    rw [Lists.set_same, List.nil_append, Lists.set_set_u] at x₂
    have hel : NRuns (loop_minElse mark) S ((S.set 25 [0]).set 26 [loop_minRes mark (t + 1) 0]) 3 := by
      cases mark
      · have e : (S.set 25 [0]).set 26 [loop_minRes false (t + 1) 0] = S.set 25 [0] := by
          have : [loop_minRes false (t + 1) 0] = (S.set 25 [0]) 26 := by
            rw [Lists.set_ne _ _ (by decide), h26]; simp [loop_minRes]
          rw [this, Lists.set_get_self]
        rw [e]; exact (x₁.seq x₂).mono (by omega)
      · have x₃ := nruns_inc 26 (S.set 25 [0]) (l := []) (v := 0)
          (by rw [Lists.set_ne _ _ (by decide), h26]; rfl)
        have e : loop_minRes true (t + 1) 0 = 0 + 1 := by simp [loop_minRes]
        rw [e]; exact (x₁.seq (x₂.seq x₃)).mono (by omega)
    have hb := hel.iteF (i := 26) (c := .pos) (p := .seq (.prim (.dec 25)) (.prim (.dec 26)))
      (by simp [h26, NTest.eval])
    have hx := nruns_loop_exit (i := 25) (c := .pos) (p := .ite 26 .pos (.seq (.prim (.dec 25)) (.prim (.dec 26)))
      (loop_minElse mark)) (S := (S.set 25 [0]).set 26 [loop_minRes mark (t + 1) 0])
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_same]; simp [NTest.eval])
    exact (loop_unroll (by simp [h25, NTest.eval]) hb hx).mono (by omega)
  | L + 1, t + 1, S, h25, h26 => by
    have x₁ := nruns_dec 25 S (l := []) (v := t + 1) (by simpa using h25)
    simp only [Nat.add_sub_cancel, List.nil_append] at x₁
    have x₂ := nruns_dec 26 (S.set 25 [t]) (l := []) (v := L + 1)
      (by rw [Lists.set_ne _ _ (by decide), h26]; rfl)
    simp only [Nat.add_sub_cancel, List.nil_append] at x₂
    have hb := (x₁.seq x₂).iteT (i := 26) (c := .pos) (q := loop_minElse mark) (by simp [h26, NTest.eval])
    have ih := loop_minP_runs mark L t ((S.set 25 [t]).set 26 [L])
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_same]) (by rw [Lists.set_same])
    have e : loop_minRes mark (t + 1) (L + 1) = loop_minRes mark t L := by
      simp only [loop_minRes, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
    rw [e, loop_set2526] at *
    exact (loop_unroll (by simp [h25, NTest.eval]) hb ih).mono (by omega)

/-! ## Comparing two stacks

`loop_eqP A B` compares the stacks `A` and `B` from the top, pair by pair (`loop_minP true` on copies), moving the
compared numbers to `21` and `22`, and adds the number of mismatches (plus `1` if the lengths differ) to the top of
`18`; then it moves everything back. States are described by `EqSt` over a base. -/

/-- Whether `k` is one of the low stacks (below the scratch). -/
theorem loop_ne_hi {A : Fin NK} (k : Fin NK) (hA : A.val < 18) (hk : 18 ≤ k.val) : A ≠ k :=
  fun e => by subst e; omega

structure EqSt where
  a : List Nat
  b : List Nat
  x : List Nat
  y : List Nat
  f : List Nat
  g : List Nat
  h : List Nat

def EqSt.toL (S : Lists NK) (A B : Fin NK) (e : EqSt) : Lists NK := fun i =>
  if i = A then e.a else if i = B then e.b else if i.val = 21 then e.x else if i.val = 22 then e.y
  else if i.val = 18 then e.f else if i.val = 25 then e.g else if i.val = 26 then e.h else S i

section EqStL
variable (S : Lists NK) {A B : Fin NK} (e : EqSt) (v : List Nat)

theorem eqst_set_a : (e.toL S A B).set A v = ({ e with a := v }).toL S A B := by
  funext i; by_cases h : i = A <;> simp [Lists.set, EqSt.toL, h]

theorem eqst_set_b (hAB : A ≠ B) : (e.toL S A B).set B v = ({ e with b := v }).toL S A B := by
  funext i; by_cases h : i = B
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm hAB]
  · simp [Lists.set, EqSt.toL, h]

theorem eqst_get_a : (e.toL S A B) A = e.a := by simp [EqSt.toL]

theorem eqst_get_b (hAB : A ≠ B) : (e.toL S A B) B = e.b := by simp [EqSt.toL, Ne.symm hAB]

theorem eqst_set_x (hA : A.val < 18) (hB : B.val < 18) :
    (e.toL S A B).set 21 v = ({ e with x := v }).toL S A B := by
  have h₁ := loop_ne_hi 21 hA (by decide)
  have h₂ := loop_ne_hi 21 hB (by decide)
  have hv : ((21 : Fin NK)).val = 21 := rfl
  funext i; by_cases h : i = 21
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]
  · have : i.val ≠ 21 := fun e => h (Fin.ext e)
    simp [Lists.set, EqSt.toL, h, this]

theorem eqst_get_x (hA : A.val < 18) (hB : B.val < 18) : (e.toL S A B) 21 = e.x := by
  have h₁ := loop_ne_hi 21 hA (by decide)
  have h₂ := loop_ne_hi 21 hB (by decide)
  have hv : ((21 : Fin NK)).val = 21 := rfl
  simp [EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]

theorem eqst_set_y (hA : A.val < 18) (hB : B.val < 18) :
    (e.toL S A B).set 22 v = ({ e with y := v }).toL S A B := by
  have h₁ := loop_ne_hi 22 hA (by decide)
  have h₂ := loop_ne_hi 22 hB (by decide)
  have hv : ((22 : Fin NK)).val = 22 := rfl
  funext i; by_cases h : i = 22
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]
  · have : i.val ≠ 22 := fun e => h (Fin.ext e)
    simp [Lists.set, EqSt.toL, h, this]

theorem eqst_get_y (hA : A.val < 18) (hB : B.val < 18) : (e.toL S A B) 22 = e.y := by
  have h₁ := loop_ne_hi 22 hA (by decide)
  have h₂ := loop_ne_hi 22 hB (by decide)
  have hv : ((22 : Fin NK)).val = 22 := rfl
  simp [EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]

theorem eqst_set_f (hA : A.val < 18) (hB : B.val < 18) :
    (e.toL S A B).set 18 v = ({ e with f := v }).toL S A B := by
  have h₁ := loop_ne_hi 18 hA (by decide)
  have h₂ := loop_ne_hi 18 hB (by decide)
  have hv : ((18 : Fin NK)).val = 18 := rfl
  funext i; by_cases h : i = 18
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]
  · have : i.val ≠ 18 := fun e => h (Fin.ext e)
    simp [Lists.set, EqSt.toL, h, this]

theorem eqst_get_f (hA : A.val < 18) (hB : B.val < 18) : (e.toL S A B) 18 = e.f := by
  have h₁ := loop_ne_hi 18 hA (by decide)
  have h₂ := loop_ne_hi 18 hB (by decide)
  have hv : ((18 : Fin NK)).val = 18 := rfl
  simp [EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]

theorem eqst_set_g (hA : A.val < 18) (hB : B.val < 18) :
    (e.toL S A B).set 25 v = ({ e with g := v }).toL S A B := by
  have h₁ := loop_ne_hi 25 hA (by decide)
  have h₂ := loop_ne_hi 25 hB (by decide)
  have hv : ((25 : Fin NK)).val = 25 := rfl
  funext i; by_cases h : i = 25
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]
  · have : i.val ≠ 25 := fun e => h (Fin.ext e)
    simp [Lists.set, EqSt.toL, h, this]

theorem eqst_get_g (hA : A.val < 18) (hB : B.val < 18) : (e.toL S A B) 25 = e.g := by
  have h₁ := loop_ne_hi 25 hA (by decide)
  have h₂ := loop_ne_hi 25 hB (by decide)
  have hv : ((25 : Fin NK)).val = 25 := rfl
  simp [EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]

theorem eqst_set_h (hA : A.val < 18) (hB : B.val < 18) :
    (e.toL S A B).set 26 v = ({ e with h := v }).toL S A B := by
  have h₁ := loop_ne_hi 26 hA (by decide)
  have h₂ := loop_ne_hi 26 hB (by decide)
  have hv : ((26 : Fin NK)).val = 26 := rfl
  funext i; by_cases h : i = 26
  · subst h; simp [Lists.set, EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]
  · have : i.val ≠ 26 := fun e => h (Fin.ext e)
    simp [Lists.set, EqSt.toL, h, this]

theorem eqst_get_h (hA : A.val < 18) (hB : B.val < 18) : (e.toL S A B) 26 = e.h := by
  have h₁ := loop_ne_hi 26 hA (by decide)
  have h₂ := loop_ne_hi 26 hB (by decide)
  have hv : ((26 : Fin NK)).val = 26 := rfl
  simp [EqSt.toL, Ne.symm h₁, Ne.symm h₂, hv]

theorem eqst_of : S = EqSt.toL S A B ⟨S A, S B, S 21, S 22, S 18, S 25, S 26⟩ := by
  funext i; simp only [EqSt.toL]
  repeat' split
  all_goals first | (subst_vars; rfl) | rfl | (congr 1; exact Fin.ext (by assumption))

end EqStL

/-! ### The comparison program -/

section EqP
variable (A B : Fin NK) (hAB : A ≠ B) (hA : A.val < 18) (hB : B.val < 18)

/-- Compare the tops of `A` and `B` (both non-empty), count a mismatch on `18`, move both tops away. -/
def loop_eqTopP : NProg NK :=
  .seq (.prim (.dup A 25 (loop_ne_hi 25 hA (by decide)))) (.seq (.prim (.dup B 26 (loop_ne_hi 26 hB (by decide))))
    (.seq (loop_minP true) (.seq (.ite 26 .pos (.prim (.inc 18)) (nskip 23))
      (.seq (.prim (.pop 25)) (.seq (.prim (.pop 26))
        (.seq (nmv A 21 (loop_ne_hi 21 hA (by decide))) (nmv B 22 (loop_ne_hi 22 hB (by decide)))))))))

def loop_eqBody : NProg NK :=
  .ite B .nonempty (loop_eqTopP A B hA hB) (.seq (.prim (.inc 18)) (nmv A 21 (loop_ne_hi 21 hA (by decide))))

/-- Add to the top of `18` the number of mismatches between the stacks `A` and `B`. -/
def loop_eqP : NProg NK :=
  .seq (.loop A .nonempty (loop_eqBody A B hA hB))
    (.seq (.ite B .nonempty (.prim (.inc 18)) (nskip 23))
      (.seq (nmvAll 21 A (Ne.symm (loop_ne_hi 21 hA (by decide))))
        (nmvAll 22 B (Ne.symm (loop_ne_hi 22 hB (by decide))))))

end EqP

/-- The mismatches met while the first stack (top first) lasts. -/
def loop_mismL : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: ra, [] => 1 + loop_mismL ra []
  | a :: ra, b :: rb => (if a = b then 0 else 1) + loop_mismL ra rb

/-- All the mismatches of two stacks, top first. -/
def loop_mism (ra rb : List Nat) : Nat := loop_mismL ra rb + (if ra.length < rb.length then 1 else 0)

theorem loop_mism_zero : ∀ (ra rb : List Nat), loop_mism ra rb = 0 ↔ ra = rb
  | [], [] => by simp [loop_mism, loop_mismL]
  | [], _ :: _ => by simp [loop_mism, loop_mismL]
  | _ :: _, [] => by simp [loop_mism, loop_mismL]
  | a :: ra, b :: rb => by
    have ih := loop_mism_zero ra rb
    simp only [loop_mism, loop_mismL, List.length_cons, Nat.add_lt_add_iff_right] at ih ⊢
    by_cases h : a = b
    · subst h; simp only [if_true, Nat.zero_add, List.cons.injEq, true_and]; exact ih
    · simp only [h, if_false, List.cons.injEq, false_and, iff_false]; omega

theorem loop_minRes_true_zero (a b : Nat) : loop_minRes true a b = 0 ↔ a = b := by
  by_cases h : a ≤ b <;> simp [loop_minRes, h] <;> omega

section EqRuns
variable (S : Lists NK) {A B : Fin NK} (hAB : A ≠ B) (hA : A.val < 18) (hB : B.val < 18)

include hAB in
theorem loop_eqLoop_runs : ∀ (ra rb xs ys : List Nat) (c : Nat),
    NRuns (.loop A .nonempty (loop_eqBody A B hA hB))
      ((⟨ra.reverse, rb.reverse, xs, ys, [c], [], []⟩ : EqSt).toL S A B)
      ((⟨[], (rb.drop ra.length).reverse, xs ++ ra, ys ++ rb.take ra.length, [c + loop_mismL ra rb], [], []⟩ : EqSt).toL
        S A B)
      (5 * rb.sum + 25 * ra.length + 1)
  | [], rb, xs, ys, c => by
    simp only [List.reverse_nil, List.length_nil, List.drop_zero, List.append_nil, List.take_zero, loop_mismL,
      Nat.add_zero]
    exact (nruns_loop_exit (by rw [eqst_get_a]; rfl)).mono (by omega)
  | a :: ra, [], xs, ys, c => by
    have hSA : (EqSt.toL S A B ⟨(a :: ra).reverse, [], xs, ys, [c], [], []⟩) A = ra.reverse ++ [a] := by
      rw [eqst_get_a]; simp
    have x₁ := nruns_inc 18 (EqSt.toL S A B ⟨(a :: ra).reverse, [], xs, ys, [c], [], []⟩) (l := []) (v := c)
      (by rw [eqst_get_f S _ hA hB]; rfl)
    rw [eqst_set_f S _ _ hA hB] at x₁
    have x₂ := nruns_mv A 21 (loop_ne_hi 21 hA (by decide))
      (EqSt.toL S A B { (⟨(a :: ra).reverse, [], xs, ys, [c], [], []⟩ : EqSt) with f := [] ++ [c + 1] })
      (l := ra.reverse) (v := a) (by rw [eqst_get_a]; simp)
    rw [eqst_get_x S _ hA hB, eqst_set_x S _ _ hA hB, eqst_set_a] at x₂
    have hb := (x₁.seq x₂).iteF (i := B) (c := .nonempty) (p := loop_eqTopP A B hA hB)
      (by rw [eqst_get_b S _ hAB]; rfl)
    have ih := loop_eqLoop_runs ra [] (xs ++ [a]) ys (c + 1)
    have e : (⟨[], (List.drop (a :: ra).length []).reverse, xs ++ a :: ra, ys ++ List.take (a :: ra).length [],
        [c + loop_mismL (a :: ra) []], [], []⟩ : EqSt) =
        ⟨[], (List.drop ra.length []).reverse, xs ++ [a] ++ ra, ys ++ List.take ra.length [],
        [c + 1 + loop_mismL ra []], [], []⟩ := by
      simp [loop_mismL]; omega
    rw [e]
    exact (loop_unroll (by rw [hSA]; simp) hb ih).mono (by simp; omega)
  | a :: ra, b :: rb, xs, ys, c => by
    rw [List.reverse_cons, List.reverse_cons]
    let m := loop_minRes true a b
    let δ := if a = b then 0 else 1
    let ar := ra.reverse ++ [a]
    let br := rb.reverse ++ [b]
    have x₁ : NRuns (.prim (.dup A 25 (loop_ne_hi 25 hA (by decide))))
        ((⟨ar, br, xs, ys, [c], [], []⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c], [a], []⟩ : EqSt).toL S A B) 1 := by
      have h := nruns_dup A 25 (loop_ne_hi 25 hA (by decide)) ((⟨ar, br, xs, ys, [c], [], []⟩ : EqSt).toL S A B)
        (l := ra.reverse) (v := a) (by rw [eqst_get_a])
      rw [eqst_get_g S _ hA hB, eqst_set_g S _ _ hA hB] at h; exact h
    have x₂ : NRuns (.prim (.dup B 26 (loop_ne_hi 26 hB (by decide))))
        ((⟨ar, br, xs, ys, [c], [a], []⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c], [a], [b]⟩ : EqSt).toL S A B) 1 := by
      have h := nruns_dup B 26 (loop_ne_hi 26 hB (by decide)) ((⟨ar, br, xs, ys, [c], [a], []⟩ : EqSt).toL S A B)
        (l := rb.reverse) (v := b) (by rw [eqst_get_b S _ hAB])
      rw [eqst_get_h S _ hA hB, eqst_set_h S _ _ hA hB] at h; exact h
    have x₃ : NRuns (loop_minP true)
        ((⟨ar, br, xs, ys, [c], [a], [b]⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c], [0], [m]⟩ : EqSt).toL S A B)
        (5 * b + 6) := by
      have h := loop_minP_runs true b a ((⟨ar, br, xs, ys, [c], [a], [b]⟩ : EqSt).toL S A B)
        (by rw [eqst_get_g S _ hA hB]) (by rw [eqst_get_h S _ hA hB])
      rw [eqst_set_g S _ _ hA hB, eqst_set_h S _ _ hA hB] at h; exact h
    have x₄ : NRuns (.ite 26 .pos (.prim (.inc 18)) (nskip 23))
        ((⟨ar, br, xs, ys, [c], [0], [m]⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c + δ], [0], [m]⟩ : EqSt).toL S A B)
        3 := by
      by_cases hab : a = b
      · have hz : m = 0 := (loop_minRes_true_zero a b).2 hab
        have e : c + δ = c := by simp [δ, hab]
        rw [e]
        exact ((nruns_skip 23 _).iteF (by rw [eqst_get_h S _ hA hB, hz]; rfl)).mono (by omega)
      · have hz : m ≠ 0 := fun h => hab ((loop_minRes_true_zero a b).1 h)
        have hi := nruns_inc 18 ((⟨ar, br, xs, ys, [c], [0], [m]⟩ : EqSt).toL S A B) (l := []) (v := c)
          (by rw [eqst_get_f S _ hA hB]; rfl)
        rw [eqst_set_f S _ _ hA hB] at hi
        have e : c + δ = c + 1 := by simp [δ, hab]
        rw [e]
        refine (hi.iteT ?_).mono (by omega)
        rw [eqst_get_h S _ hA hB]
        obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [hk]; rfl
    have x₅ : NRuns (.prim (.pop 25))
        ((⟨ar, br, xs, ys, [c + δ], [0], [m]⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c + δ], [], [m]⟩ : EqSt).toL S A B)
        1 := by
      have h := nruns_pop 25 ((⟨ar, br, xs, ys, [c + δ], [0], [m]⟩ : EqSt).toL S A B) (l := []) (v := 0)
        (by rw [eqst_get_g S _ hA hB]; rfl)
      rw [eqst_set_g S _ _ hA hB] at h; exact h
    have x₆ : NRuns (.prim (.pop 26))
        ((⟨ar, br, xs, ys, [c + δ], [], [m]⟩ : EqSt).toL S A B) ((⟨ar, br, xs, ys, [c + δ], [], []⟩ : EqSt).toL S A B)
        1 := by
      have h := nruns_pop 26 ((⟨ar, br, xs, ys, [c + δ], [], [m]⟩ : EqSt).toL S A B) (l := []) (v := m)
        (by rw [eqst_get_h S _ hA hB]; rfl)
      rw [eqst_set_h S _ _ hA hB] at h; exact h
    have x₇ : NRuns (nmv A 21 (loop_ne_hi 21 hA (by decide)))
        ((⟨ar, br, xs, ys, [c + δ], [], []⟩ : EqSt).toL S A B)
        ((⟨ra.reverse, br, xs ++ [a], ys, [c + δ], [], []⟩ : EqSt).toL S A B) 2 := by
      have h := nruns_mv A 21 (loop_ne_hi 21 hA (by decide)) ((⟨ar, br, xs, ys, [c + δ], [], []⟩ : EqSt).toL S A B)
        (l := ra.reverse) (v := a) (by rw [eqst_get_a])
      rw [eqst_get_x S _ hA hB, eqst_set_x S _ _ hA hB, eqst_set_a] at h; exact h
    have x₈ : NRuns (nmv B 22 (loop_ne_hi 22 hB (by decide)))
        ((⟨ra.reverse, br, xs ++ [a], ys, [c + δ], [], []⟩ : EqSt).toL S A B)
        ((⟨ra.reverse, rb.reverse, xs ++ [a], ys ++ [b], [c + δ], [], []⟩ : EqSt).toL S A B) 2 := by
      have h := nruns_mv B 22 (loop_ne_hi 22 hB (by decide))
        ((⟨ra.reverse, br, xs ++ [a], ys, [c + δ], [], []⟩ : EqSt).toL S A B)
        (l := rb.reverse) (v := b) (by rw [eqst_get_b S _ hAB])
      rw [eqst_get_y S _ hA hB, eqst_set_y S _ _ hA hB, eqst_set_b S _ _ hAB] at h; exact h
    have hbody := (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq x₈))))))).iteT (i := B)
      (c := .nonempty) (q := .seq (.prim (.inc 18)) (nmv A 21 (loop_ne_hi 21 hA (by decide))))
      (by rw [eqst_get_b S _ hAB]; simp [br])
    have ih := loop_eqLoop_runs ra rb (xs ++ [a]) (ys ++ [b]) (c + δ)
    have e : (⟨[], (List.drop (a :: ra).length (b :: rb)).reverse, xs ++ a :: ra,
        ys ++ List.take (a :: ra).length (b :: rb), [c + loop_mismL (a :: ra) (b :: rb)], [], []⟩ : EqSt) =
        ⟨[], (List.drop ra.length rb).reverse, xs ++ [a] ++ ra, ys ++ [b] ++ List.take ra.length rb,
          [c + δ + loop_mismL ra rb], [], []⟩ := by
      simp [loop_mismL, δ, Nat.add_assoc]
    rw [e]
    refine (loop_unroll (by rw [eqst_get_a]; simp [ar]) hbody ih).mono ?_
    have : (b :: rb).sum = b + rb.sum := List.sum_cons
    simp only [List.length_cons, this]
    omega

include hAB in
/-- **Comparing two stacks**: the number of mismatches is added to the top of `18`; nothing else changes. -/
theorem loop_eqP_runs (ra rb : List Nat) (c : Nat) (hSA : S A = ra.reverse) (hSB : S B = rb.reverse)
    (h21 : S 21 = []) (h22 : S 22 = []) (h25 : S 25 = []) (h26 : S 26 = []) (h18 : S 18 = [c]) :
    NRuns (loop_eqP A B hA hB) S (S.set 18 [c + loop_mism ra rb]) (5 * rb.sum + 30 * (ra.length + rb.length) + 10) := by
  have hS : S = (⟨ra.reverse, rb.reverse, [], [], [c], [], []⟩ : EqSt).toL S A B := by
    conv => lhs; rw [eqst_of S (A := A) (B := B)]
    rw [hSA, hSB, h21, h22, h18, h25, h26]
  have hF : S.set 18 [c + loop_mism ra rb] =
      (⟨ra.reverse, rb.reverse, [], [], [c + loop_mism ra rb], [], []⟩ : EqSt).toL S A B := by
    conv => lhs; rw [hS]
    rw [eqst_set_f S _ _ hA hB]
  have x₁ := loop_eqLoop_runs S hAB hA hB ra rb [] [] c
  rw [← hS] at x₁
  simp only [List.nil_append] at x₁
  let n := ra.length
  have x₂ : NRuns (.ite B .nonempty (.prim (.inc 18)) (nskip 23))
      ((⟨[], (rb.drop n).reverse, ra, rb.take n, [c + loop_mismL ra rb], [], []⟩ : EqSt).toL S A B)
      ((⟨[], (rb.drop n).reverse, ra, rb.take n, [c + loop_mism ra rb], [], []⟩ : EqSt).toL S A B) 3 := by
    by_cases hl : n < rb.length
    · have hne : (rb.drop n).reverse ≠ [] := by simp; omega
      obtain ⟨l, v, hlv⟩ : ∃ l v, (rb.drop n).reverse = l ++ [v] :=
        ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
      have hi := nruns_inc 18 ((⟨[], (rb.drop n).reverse, ra, rb.take n, [c + loop_mismL ra rb], [], []⟩ : EqSt).toL
        S A B) (l := []) (v := c + loop_mismL ra rb) (by rw [eqst_get_f S _ hA hB]; rfl)
      rw [eqst_set_f S _ _ hA hB] at hi
      have e : loop_mism ra rb = loop_mismL ra rb + 1 := by simp [loop_mism, n] at hl ⊢; omega
      rw [e, ← Nat.add_assoc]
      refine (hi.iteT ?_).mono (by omega)
      rw [eqst_get_b S _ hAB, hlv]; simp
    · have e : loop_mism ra rb = loop_mismL ra rb := by simp [loop_mism, n] at hl ⊢; omega
      rw [e]
      refine ((nruns_skip 23 _).iteF ?_).mono (by omega)
      rw [eqst_get_b S _ hAB]
      have : rb.drop n = [] := List.drop_eq_nil_of_le (by omega)
      rw [this]; rfl
  have x₃ := nruns_mvAll 21 A (Ne.symm (loop_ne_hi 21 hA (by decide)))
    ((⟨[], (rb.drop n).reverse, ra, rb.take n, [c + loop_mism ra rb], [], []⟩ : EqSt).toL S A B)
  rw [eqst_get_x S _ hA hB, eqst_get_a, eqst_set_a, eqst_set_x S _ _ hA hB] at x₃
  have x₄ := nruns_mvAll 22 B (Ne.symm (loop_ne_hi 22 hB (by decide)))
    ((⟨[] ++ ra.reverse, (rb.drop n).reverse, [], rb.take n, [c + loop_mism ra rb], [], []⟩ : EqSt).toL S A B)
  rw [eqst_get_y S _ hA hB, eqst_get_b S _ hAB, eqst_set_b S _ _ hAB, eqst_set_y S _ _ hA hB] at x₄
  have e : (⟨[] ++ ra.reverse, (rb.drop n).reverse ++ (rb.take n).reverse, [], [], [c + loop_mism ra rb], [], []⟩ :
      EqSt) = ⟨ra.reverse, rb.reverse, [], [], [c + loop_mism ra rb], [], []⟩ := by
    rw [← List.reverse_append, List.take_append_drop, List.nil_append]
  rw [hF]
  refine (x₁.seq (x₂.seq (x₃.seq (e ▸ x₄)))).mono ?_
  simp only [List.length_take]
  have : min n rb.length ≤ rb.length := Nat.min_le_right _ _
  omega

end EqRuns

/-! ## The tables the item programs need -/

/-- The scratch stacks of a record are empty. -/
def Cf.Clean (c : Cf) : Prop :=
  c.s18 = [] ∧ c.s19 = [] ∧ c.s20 = [] ∧ c.s21 = [] ∧ c.s22 = [] ∧ c.s23 = [] ∧ c.s24 = [] ∧ c.s25 = [] ∧ c.s26 = []

/-- The record keeps the tables of `B`, and holds the rule values `Tf`. -/
theorem loop_env {B : Lists NK} {j cap : Nat} {st : PSt} {c : Cf} {Tf : List (List Nat)}
    (hE : EvalEnv B j cap st []) (hrts : c.rts = st.rt) (hvalt : c.valt = valTable j cap st.x.length st.tt)
    (hrv : c.rv = Tf.flatten) (hrvl : c.rvl = Tf.map List.length) (hcl : c.Clean) :
    EvalEnv (c.toL B) j cap st Tf where
  ct := hE.ct
  lt := hE.lt
  rt := hrts
  xs := hE.xs
  nx := hE.nx
  ord := hE.ord
  sz := hE.sz
  cnt := hE.cnt
  rows := hE.rows
  roff := hE.roff
  valt := hvalt
  envt := hE.envt
  rv := hrv
  rvl := hrvl
  cap := hE.cap
  scratch := by
    obtain ⟨h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ := hcl
    intro i hi₁ hi₂
    have hs := hE.scratch i hi₁ hi₂
    obtain ⟨n, hn⟩ := i
    simp only at hi₁ hi₂ hs
    have : n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ 26 < n := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
    all_goals first
      | assumption
      | (simp only [Cf.toL]; simp only [show ¬ n = 3 by omega, show ¬ n = 4 by omega, show ¬ n = 5 by omega,
          show ¬ n = 6 by omega, show ¬ n = 9 by omega, show ¬ n = 10 by omega, show ¬ n = 11 by omega,
          show ¬ n = 12 by omega, show ¬ n = 14 by omega, show ¬ n = 15 by omega, show ¬ n = 16 by omega,
          show ¬ n = 17 by omega, show ¬ n = 18 by omega, show ¬ n = 19 by omega, show ¬ n = 20 by omega,
          show ¬ n = 21 by omega, show ¬ n = 22 by omega, show ¬ n = 23 by omega, show ¬ n = 24 by omega,
          show ¬ n = 25 by omega, show ¬ n = 26 by omega, show ¬ n = 37 by omega, if_false]; exact hs)

/-! ## Moving an item to `IT` -/

def loop_pairP (src d : Fin NK) (hd : src ≠ d) (hs : src ≠ 14) : NProg NK :=
  .seq (.prim (.dup src 14 hs)) (nmv src d hd)

/-- Copy `n` numbers from the top of `src` to `IT` and move them to `d`. -/
def loop_movesP (src d : Fin NK) (hd : src ≠ d) (hs : src ≠ 14) : Nat → NProg NK
  | 0 => nskip 23
  | n + 1 => .seq (loop_pairP src d hd hs) (loop_movesP src d hd hs n)

theorem loop_movesP_runs (src d : Fin NK) (hd : src ≠ d) (hs : src ≠ 14) (hd14 : d ≠ 14) :
    ∀ (ws : List Nat) (S : Lists NK) (W : List Nat), S src = W ++ ws.reverse →
      NRuns (loop_movesP src d hd hs ws.length) S (((S.set 14 (S 14 ++ ws)).set d (S d ++ ws)).set src W)
        (3 * ws.length + 2)
  | [], S, W, h6 => by
    simp only [List.reverse_nil, List.append_nil] at h6
    simp only [List.append_nil, List.length_nil]
    rw [Lists.set_get_self, Lists.set_get_self, ← h6, Lists.set_get_self]
    exact nruns_skip 23 S
  | w :: ws, S, W, h6 => by
    have x₁ := nruns_dup src 14 hs S (l := W ++ ws.reverse) (v := w) (by rw [h6]; simp)
    have x₂ := nruns_mv src d hd (S.set 14 (S 14 ++ [w])) (l := W ++ ws.reverse) (v := w)
      (by rw [Lists.set_ne _ _ hs, h6]; simp)
    rw [Lists.set_ne _ _ hd14] at x₂
    have ih := loop_movesP_runs src d hd hs hd14 ws
      (((S.set 14 (S 14 ++ [w])).set d (S d ++ [w])).set src (W ++ ws.reverse)) W (by rw [Lists.set_same])
    have e : ((((((S.set 14 (S 14 ++ [w])).set d (S d ++ [w])).set src (W ++ ws.reverse)).set 14
        ((((S.set 14 (S 14 ++ [w])).set d (S d ++ [w])).set src (W ++ ws.reverse)) 14 ++ ws)).set d
        ((((S.set 14 (S 14 ++ [w])).set d (S d ++ [w])).set src (W ++ ws.reverse)) d ++ ws)).set src W) =
        ((S.set 14 (S 14 ++ w :: ws)).set d (S d ++ w :: ws)).set src W := by
      funext x; simp only [Lists.set]
      by_cases hx6 : x = src
      · simp [hx6]
      · by_cases hxd : x = d
        · subst hxd; simp [hx6]
        · by_cases hx14 : x = 14
          · subst hx14; simp only [hxd, hx6, if_false, if_true]; simp
          · simp [hx6, hxd, hx14]
    rw [e] at ih
    refine ((x₁.seq x₂).seq ih).mono ?_
    simp only [List.length_cons]; omega

/-! ## One item -/

/-- The stack after one item, with the tables. -/
abbrev loop_stp (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat)) :
    List (List Nat) :=
  stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs

/-- Move the item on top of `src` to `IT` (and its numbers to `d`), run `p`, clear `IT`. -/
def loop_itemP (p : NProg NK) (src d : Fin NK) (hd : src ≠ d) (hs : src ≠ 14) : NProg NK :=
  .seq (loop_movesP src d hd hs 4) (.seq p (nclr 14))

theorem loop_encItem_length (it : MItem) : (encItem it).length = 4 := rfl

section Item
variable {p : NProg NK} {B : Lists NK} {j cap : Nat} {st : PSt} {Tf : List (List Nat)} {it : MItem}
  (hpi : ItemRunsC p j cap st Tf it 100) (hE : EvalEnv B j cap st []) (c : Cf) (W : List Nat)
  (vs : List (List Nat)) (hrts : c.rts = st.rt) (hvalt : c.valt = valTable j cap st.x.length st.tt)
  (hrv : c.rv = Tf.flatten) (hrvl : c.rvl = Tf.map List.length) (hcl : c.Clean)
  (hit : c.it = []) (hev : c.ev = evFlat vs) (hevl : c.evl = evLens vs)
include hpi hE hrts hvalt hrv hrvl hcl hit hev hevl

/-- **One item of a body**: its numbers go from `STA` to `BOD`, the evaluation stack takes the step. -/
theorem loop_itemB_runs (hw : c.sta = W ++ (encItem it).reverse) :
    NRuns (loop_itemP p 12 10 (by decide) (by decide)) (c.toL B)
      ({ c with sta := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
                  evl := evLens (loop_stp j cap st Tf it vs) }.toL B) (itemCost j cap st Tf it vs + 123) := by
  have x₁ := loop_movesP_runs 12 10 (by decide) (by decide) (by decide) (encItem it) (c.toL B) W (by rw [loop_get_sta, hw])
  rw [loop_encItem_length] at x₁
  simp only [loop_get_it, loop_get_bod, loop_set_it, loop_set_bod, loop_set_sta, hit, List.nil_append] at x₁
  let c₁ : Cf := { c with it := encItem it, bod := c.bod ++ encItem it, sta := W }
  have x₂ := hpi (c₁.toL B) vs (loop_env hE hrts hvalt hrv hrvl hcl) rfl hev hevl
  simp only [loop_set_ev, loop_set_evl] at x₂
  have x₃ := nruns_clr 14 ({ { c₁ with ev := evFlat (loop_stp j cap st Tf it vs) } with
    evl := evLens (loop_stp j cap st Tf it vs) }.toL B)
  simp only [loop_set_it, loop_get_it] at x₃
  have e : { { { c₁ with ev := evFlat (loop_stp j cap st Tf it vs) } with
      evl := evLens (loop_stp j cap st Tf it vs) } with it := [] } =
      { c with sta := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
                evl := evLens (loop_stp j cap st Tf it vs) } := by
    cases c; simp only at hit; subst hit; rfl
  rw [e] at x₃
  refine (x₁.seq (x₂.seq x₃)).mono ?_
  simp only [c₁, loop_encItem_length]
  omega

/-- **One start item**: its numbers go from `6` to `BOD`, the evaluation stack takes the step. -/
theorem loop_itemS_runs (hw : c.w = W ++ (encItem it).reverse) :
    NRuns (loop_itemP p 6 10 (by decide) (by decide)) (c.toL B)
      ({ c with w := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
                  evl := evLens (loop_stp j cap st Tf it vs) }.toL B) (itemCost j cap st Tf it vs + 123) := by
  have x₁ := loop_movesP_runs 6 10 (by decide) (by decide) (by decide) (encItem it) (c.toL B) W (by rw [loop_get_w, hw])
  rw [loop_encItem_length] at x₁
  simp only [loop_get_it, loop_get_bod, loop_set_it, loop_set_bod, loop_set_w, hit, List.nil_append] at x₁
  let c₁ : Cf := { c with it := encItem it, bod := c.bod ++ encItem it, w := W }
  have x₂ := hpi (c₁.toL B) vs (loop_env hE hrts hvalt hrv hrvl hcl) rfl hev hevl
  simp only [loop_set_ev, loop_set_evl] at x₂
  have x₃ := nruns_clr 14 ({ { c₁ with ev := evFlat (loop_stp j cap st Tf it vs) } with
    evl := evLens (loop_stp j cap st Tf it vs) }.toL B)
  simp only [loop_set_it, loop_get_it] at x₃
  have e : { { { c₁ with ev := evFlat (loop_stp j cap st Tf it vs) } with
      evl := evLens (loop_stp j cap st Tf it vs) } with it := [] } =
      { c with w := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
                evl := evLens (loop_stp j cap st Tf it vs) } := by
    cases c; simp only at hit; subst hit; rfl
  rw [e] at x₃
  refine (x₁.seq (x₂.seq x₃)).mono ?_
  simp only [c₁, loop_encItem_length]
  omega

end Item

/-! ## The end of a body -/

/-- Beyond the branches of `caseTop`: the default runs, with the top lowered. -/
theorem loop_caseTop_default (i : Fin NK) : ∀ (ps : List (NProg NK)) (q : NProg NK) (v : Nat) (S : Lists NK)
    (l : List Nat), S i = l ++ [v + ps.length] → ∀ (S' : Lists NK) (T : Nat),
      NRuns q (S.set i (l ++ [v])) S' T → NRuns (caseTop i ps q) S S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := loop_caseTop_default i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seq h₂).iteF (by rw [hS']; simp)).mono (by omega)

/-- Keep the top vector of the evaluation stack: on `RV2`, its length on `RVL2` (`0` if there is none). -/
def loop_takeTopP : NProg NK :=
  .ite 4 .nonempty
    (.seq (.prim (.dup 4 18 (by decide))) (.seq (.prim (.dup 18 17 (by decide)))
      (.seq (moveN 18 3 19 (by decide)) (nmvAll 19 16 (by decide)))))
    (.prim (.pushZ 17))

/-- Keep the top vector, then clear the evaluation stack. -/
def loop_takeClearP : NProg NK := .seq loop_takeTopP (.seq (nclr 3) (nclr 4))

theorem loop_evLens_length (vs : List (List Nat)) : (evLens vs).length = vs.length := by simp [evLens]

theorem loop_evFlat_length (vs : List (List Nat)) : (evFlat vs).length = (vs.map List.length).sum := by
  simp [evFlat, List.length_flatten, List.map_reverse, List.sum_reverse]

theorem loop_takeClear_runs (B : Lists NK) (c : Cf) (vs : List (List Nat)) (hev : c.ev = evFlat vs)
    (hevl : c.evl = evLens vs) (h18 : c.s18 = []) (h19 : c.s19 = []) :
    NRuns loop_takeClearP (c.toL B)
      ({ c with ev := [], evl := [], rv2 := c.rv2 ++ vs.headD [], rvl2 := c.rvl2 ++ [(vs.headD []).length] }.toL B)
      (7 * (evFlat vs).length + 2 * vs.length + 12) := by
  cases vs with
  | nil =>
    have x₁ : NRuns (.prim (.pushZ 17)) (c.toL B) ({ c with rvl2 := c.rvl2 ++ [0] }.toL B) 1 := by
      have h := nruns_pushZ 17 (c.toL B)
      simp only [loop_get_rvl2, loop_set_rvl2] at h; exact h
    have x₂ : NRuns (nclr 3) ({ c with rvl2 := c.rvl2 ++ [0] }.toL B)
        ({ c with rvl2 := c.rvl2 ++ [0], ev := [] }.toL B) 1 := by
      have h := nruns_clr 3 ({ c with rvl2 := c.rvl2 ++ [0] }.toL B)
      simp only [loop_get_ev, loop_set_ev] at h; exact h.mono (by simp [hev, evFlat])
    have x₃ : NRuns (nclr 4) ({ c with rvl2 := c.rvl2 ++ [0], ev := [] }.toL B)
        ({ c with ev := [], evl := [], rv2 := c.rv2 ++ ([] : List (List Nat)).headD [],
                  rvl2 := c.rvl2 ++ [(([] : List (List Nat)).headD []).length] }.toL B) 1 := by
      have h := nruns_clr 4 ({ c with rvl2 := c.rvl2 ++ [0], ev := [] }.toL B)
      simp only [loop_get_evl, loop_set_evl] at h
      have e : c.rv2 ++ ([] : List (List Nat)).headD [] = c.rv2 := by simp
      rw [e]; exact h.mono (by simp [hevl, evLens])
    exact ((x₁.iteF (by simp [hevl, evLens])).seq (x₂.seq x₃)).mono (by simp)
  | cons v vs =>
    have x₁ : NRuns (.prim (.dup 4 18 (by decide))) (c.toL B) ({ c with s18 := [v.length] }.toL B) 1 := by
      have h := nruns_dup 4 18 (by decide) (c.toL B) (l := evLens vs) (v := v.length) (by simp [hevl, evLens_cons])
      simp only [loop_get_s18, loop_set_s18, h18, List.nil_append] at h; exact h
    have x₂ : NRuns (.prim (.dup 18 17 (by decide))) ({ c with s18 := [v.length] }.toL B)
        ({ c with s18 := [v.length], rvl2 := c.rvl2 ++ [v.length] }.toL B) 1 := by
      have h := nruns_dup 18 17 (by decide) ({ c with s18 := [v.length] }.toL B) (l := []) (v := v.length) rfl
      simp only [loop_get_rvl2, loop_set_rvl2] at h; exact h
    have x₃ : NRuns (moveN 18 3 19 (by decide)) ({ c with s18 := [v.length], rvl2 := c.rvl2 ++ [v.length] }.toL B)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := v.reverse }.toL B)
        (4 * v.length + 2) := by
      have h := nruns_moveN 18 3 19 (by decide) (by decide) (by decide)
        ({ c with s18 := [v.length], rvl2 := c.rvl2 ++ [v.length] }.toL B) (lc := []) (n := v.length) rfl
        (l := evFlat vs) (seg := v) (by simp [hev, evFlat_cons]) rfl
      have r : ({ c with s18 := [v.length], rvl2 := c.rvl2 ++ [v.length] }.toL B) 19 = [] := h19
      rw [r] at h
      simp only [loop_set_s18, loop_set_ev, loop_set_s19, List.nil_append] at h; exact h
    have x₄ : NRuns (nmvAll 19 16 (by decide))
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := v.reverse }.toL B)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := [], rv2 := c.rv2 ++ v }.toL B)
        (3 * v.length + 1) := by
      have h := nruns_mvAll 19 16 (by decide)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := v.reverse }.toL B)
      simp only [loop_set_s19, loop_set_rv2, loop_get_s19, loop_get_rv2, List.reverse_reverse,
        List.length_reverse] at h
      exact h
    have x₅ : NRuns (nclr 3)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := [], rv2 := c.rv2 ++ v }.toL B)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := [], s19 := [], rv2 := c.rv2 ++ v }.toL B)
        (2 * (evFlat vs).length + 1) := by
      have h := nruns_clr 3
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := evFlat vs, s19 := [], rv2 := c.rv2 ++ v }.toL B)
      simp only [loop_get_ev, loop_set_ev] at h; exact h
    have x₆ : NRuns (nclr 4)
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := [], s19 := [], rv2 := c.rv2 ++ v }.toL B)
        ({ c with ev := [], evl := [], rv2 := c.rv2 ++ (v :: vs).headD [],
                  rvl2 := c.rvl2 ++ [((v :: vs).headD []).length] }.toL B)
        (2 * (vs.length + 1) + 1) := by
      have h := nruns_clr 4
        ({ c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := [], s19 := [], rv2 := c.rv2 ++ v }.toL B)
      simp only [loop_get_evl, loop_set_evl] at h
      replace h := h.mono (show 2 * c.evl.length + 1 ≤ 2 * (vs.length + 1) + 1 by
        simp [hevl, evLens_cons, loop_evLens_length])
      have e : { c with s18 := [], rvl2 := c.rvl2 ++ [v.length], ev := [], s19 := [], rv2 := c.rv2 ++ v,
                        evl := [] } =
          { c with ev := [], evl := [], rv2 := c.rv2 ++ (v :: vs).headD [],
                   rvl2 := c.rvl2 ++ [((v :: vs).headD []).length] } := by
        cases c; simp only at h18 h19; subst h18 h19; rfl
      rw [← e]; exact h
    refine (((x₁.seq (x₂.seq (x₃.seq x₄))).iteT (by simp [hevl, evLens_cons])).seq (x₅.seq x₆)).mono ?_
    simp only [evFlat_cons, List.length_append, List.length_cons]
    omega

/-- At the end of a body: move the `13` to `BOD`, keep the top vector, clear the evaluation stack. -/
def loop_endP : NProg NK := .seq (nmv 12 10 (by decide)) loop_takeClearP

/-- One group of numbers on `6`: an item (tag below `13`) or the end of a body (`13`). -/
def loop_groupP (p : NProg NK) : NProg NK :=
  .seq (.prim (.dup 12 18 (by decide)))
    (caseTop 18 (List.replicate 13 (loop_itemP p 12 10 (by decide) (by decide))) (.seq (.prim (.pop 18)) loop_endP))

theorem loop_groupEnd_runs (p : NProg NK) (B : Lists NK) (c : Cf) (W : List Nat) (vs : List (List Nat))
    (hw : c.sta = W ++ [13]) (hev : c.ev = evFlat vs) (hevl : c.evl = evLens vs) (h18 : c.s18 = [])
    (h19 : c.s19 = []) :
    NRuns (loop_groupP p) (c.toL B)
      ({ c with sta := W, bod := c.bod ++ [13], ev := [], evl := [], rv2 := c.rv2 ++ vs.headD [],
                rvl2 := c.rvl2 ++ [(vs.headD []).length] }.toL B)
      (7 * (evFlat vs).length + 2 * vs.length + 45) := by
  have x₁ : NRuns (.prim (.dup 12 18 (by decide))) (c.toL B) ({ c with s18 := [13] }.toL B) 1 := by
    have h := nruns_dup 12 18 (by decide) (c.toL B) (l := W) (v := 13) (by rw [loop_get_sta, hw])
    rw [loop_get_s18, h18, List.nil_append, loop_set_s18] at h; exact h
  have x₂ : NRuns (.prim (.pop 18)) ({ c with s18 := [0] }.toL B) ({ c with s18 := [] }.toL B) 1 := by
    have h := nruns_pop 18 ({ c with s18 := [0] }.toL B) (l := []) (v := 0) rfl
    rw [loop_set_s18] at h; exact h
  have x₃ : NRuns (nmv 12 10 (by decide)) ({ c with s18 := [] }.toL B)
      ({ c with s18 := [], sta := W, bod := c.bod ++ [13] }.toL B) 2 := by
    have h := nruns_mv 12 10 (by decide) ({ c with s18 := [] }.toL B) (l := W) (v := 13) (by simp [hw])
    simp only [loop_get_bod, loop_set_bod, loop_set_sta] at h; exact h
  have x₄ := loop_takeClear_runs B { c with s18 := [], sta := W, bod := c.bod ++ [13] } vs hev hevl rfl h19
  have e : { { c with s18 := [], sta := W, bod := c.bod ++ [13] } with
        ev := [], evl := [], rv2 := c.rv2 ++ vs.headD [], rvl2 := c.rvl2 ++ [(vs.headD []).length] } =
      { c with sta := W, bod := c.bod ++ [13], ev := [], evl := [], rv2 := c.rv2 ++ vs.headD [],
               rvl2 := c.rvl2 ++ [(vs.headD []).length] } := by
    cases c; simp only at h18; subst h18; rfl
  rw [e] at x₄
  have x₅ := loop_caseTop_default 18 (List.replicate 13 (loop_itemP p 12 10 (by decide) (by decide)))
    (.seq (.prim (.pop 18)) loop_endP) 0 ({ c with s18 := [13] }.toL B) [] rfl _ _
    (by rw [List.nil_append, loop_set_s18]; exact x₂.seq (x₃.seq x₄))
  refine (x₁.seq x₅).mono ?_
  simp only [List.length_replicate]
  omega

theorem loop_groupItem_runs {p : NProg NK} {B : Lists NK} {j cap : Nat} {st : PSt} {Tf : List (List Nat)}
    {it : MItem} (hpi : ItemRunsC p j cap st Tf it 100) (hE : EvalEnv B j cap st []) (htag : it.tag < 13)
    (c : Cf) (W : List Nat) (vs : List (List Nat)) (hrts : c.rts = st.rt)
    (hvalt : c.valt = valTable j cap st.x.length st.tt) (hrv : c.rv = Tf.flatten)
    (hrvl : c.rvl = Tf.map List.length) (hcl : c.Clean) (hw : c.sta = W ++ (encItem it).reverse) (hit : c.it = [])
    (hev : c.ev = evFlat vs) (hevl : c.evl = evLens vs) :
    NRuns (loop_groupP p) (c.toL B)
      ({ c with sta := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
                evl := evLens (loop_stp j cap st Tf it vs) }.toL B) (itemCost j cap st Tf it vs + 151) := by
  have h18 : c.s18 = [] := hcl.1
  have x₁ : NRuns (.prim (.dup 12 18 (by decide))) (c.toL B) ({ c with s18 := [it.tag] }.toL B) 1 := by
    have h := nruns_dup 12 18 (by decide) (c.toL B) (l := W ++ [it.ctx, it.b, it.a]) (v := it.tag)
      (by rw [loop_get_sta, hw]; simp [encItem])
    rw [loop_get_s18, h18, List.nil_append, loop_set_s18] at h; exact h
  have x₂ := loop_itemB_runs hpi hE { c with s18 := [] } W vs hrts hvalt hrv hrvl
    (by obtain ⟨_, h⟩ := hcl; exact ⟨rfl, h⟩) hit hev hevl hw
  have e : { { c with s18 := [] } with
        sta := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
        evl := evLens (loop_stp j cap st Tf it vs) } =
      { c with sta := W, bod := c.bod ++ encItem it, ev := evFlat (loop_stp j cap st Tf it vs),
               evl := evLens (loop_stp j cap st Tf it vs) } := by
    cases c; simp only at h18; subst h18; rfl
  rw [e] at x₂
  have x₃ := caseTop_runs 18 (List.replicate 13 (loop_itemP p 12 10 (by decide) (by decide)))
    (.seq (.prim (.pop 18)) loop_endP) it.tag (by simpa using htag) ({ c with s18 := [it.tag] }.toL B) [] rfl _ _
    (by rw [List.getElem_replicate, loop_set_s18]; exact x₂)
  refine (x₁.seq x₃).mono ?_
  omega

/-! ## The bodies of a round -/

/-- Run the groups on `6` until it is empty. -/
def loop_bodiesP (p : NProg NK) : NProg NK := .loop 12 .nonempty (loop_groupP p)

/-- Running items, with the tables. -/
abbrev loop_run (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (l : List MItem) (vs : List (List Nat)) :
    List (List Nat) :=
  runT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf l vs

theorem loop_stp_length (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat)) :
    (loop_stp j cap st Tf it vs).length ≤ vs.length + 1 := by
  unfold loop_stp stepT
  split <;> (try split) <;> simp

theorem loop_run_length (j cap : Nat) (st : PSt) (Tf : List (List Nat)) :
    ∀ (l : List MItem) (vs : List (List Nat)), (loop_run j cap st Tf l vs).length ≤ vs.length + l.length
  | [], vs => by simp [loop_run, runT]
  | it :: l, vs => by
    have h₁ := loop_stp_length j cap st Tf it vs
    have h₂ := loop_run_length j cap st Tf l (loop_stp j cap st Tf it vs)
    have e : loop_run j cap st Tf (it :: l) vs = loop_run j cap st Tf l (loop_stp j cap st Tf it vs) := rfl
    rw [e]; simp only [List.length_cons]; omega

theorem loop_flatten_cons (l : List MItem) (it : MItem) : encItems (it :: l) = encItem it ++ encItems l := by
  simp [encItems]

section Bodies
variable {p : NProg NK} {B : Lists NK} {j cap : Nat} {st : PSt} {Tf : List (List Nat)}
  (hE : EvalEnv B j cap st [])

include hE in
/-- **The items of one body**, then the rest of the loop (`hcont`). -/
theorem loop_items_runs : ∀ (l : List MItem) (vs : List (List Nat)) (c : Cf) (Wr : List Nat) (Fin : Lists NK)
    (Tc : Nat), (∀ it ∈ l, ItemRunsC p j cap st Tf it 100) → (∀ it ∈ l, it.tag < 13) →
    c.rts = st.rt → c.valt = valTable j cap st.x.length st.tt → c.rv = Tf.flatten →
    c.rvl = Tf.map List.length → c.Clean → c.it = [] → c.sta = Wr ++ [13] ++ (encItems l).reverse →
    c.ev = evFlat vs → c.evl = evLens vs →
    NRuns (loop_bodiesP p)
      ({ c with
          sta := Wr, bod := c.bod ++ encItems l ++ [13], ev := [], evl := [],
          rv2 := c.rv2 ++ (loop_run j cap st Tf l vs).headD [],
          rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l vs).headD []).length] }.toL B) Fin Tc →
    NRuns (loop_bodiesP p) (c.toL B) Fin
      (runCost j cap st Tf l vs + 7 * (evFlat (loop_run j cap st Tf l vs)).length +
        2 * (loop_run j cap st Tf l vs).length + 46 + Tc)
  | [], vs, c, Wr, Fin, Tc, _, _, _, _, _, _, hcl, _, hw, hev, hevl, hcont => by
    have hw' : c.sta = Wr ++ [13] := by rw [hw]; simp [encItems]
    have x₁ := loop_groupEnd_runs p B c Wr vs hw' hev hevl hcl.1 hcl.2.1
    have e : c.bod ++ encItems [] ++ [13] = c.bod ++ [13] := by simp [encItems]
    rw [e] at hcont
    refine (loop_unroll (by rw [loop_get_sta, hw']; simp) x₁ hcont).mono ?_
    simp only [runCost]
    have : loop_run j cap st Tf [] vs = vs := rfl
    rw [this]; omega
  | it :: l, vs, c, Wr, Fin, Tc, hpl, htl, hrts, hvalt, hrv, hrvl, hcl, hit, hw, hev, hevl, hcont => by
    have hw' : c.sta = (Wr ++ [13] ++ (encItems l).reverse) ++ (encItem it).reverse := by
      rw [hw, loop_flatten_cons, List.reverse_append]; simp only [List.append_assoc]
    have x₁ := loop_groupItem_runs (hpl it List.mem_cons_self) hE (htl it List.mem_cons_self) c
      (Wr ++ [13] ++ (encItems l).reverse) vs hrts hvalt hrv hrvl hcl hw' hit hev hevl
    have hR : loop_run j cap st Tf (it :: l) vs = loop_run j cap st Tf l (loop_stp j cap st Tf it vs) := rfl
    rw [hR] at hcont ⊢
    have e : { { c with
          sta := Wr ++ [13] ++ (encItems l).reverse, bod := c.bod ++ encItem it,
          ev := evFlat (loop_stp j cap st Tf it vs), evl := evLens (loop_stp j cap st Tf it vs) } with
          sta := Wr, bod := c.bod ++ encItem it ++ encItems l ++ [13], ev := [], evl := [],
          rv2 := c.rv2 ++ (loop_run j cap st Tf l (loop_stp j cap st Tf it vs)).headD [],
          rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l (loop_stp j cap st Tf it vs)).headD []).length] } =
        { c with
          sta := Wr, bod := c.bod ++ encItems (it :: l) ++ [13], ev := [], evl := [],
          rv2 := c.rv2 ++ (loop_run j cap st Tf l (loop_stp j cap st Tf it vs)).headD [],
          rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l (loop_stp j cap st Tf it vs)).headD []).length] } := by
      simp only [loop_flatten_cons, List.append_assoc]
    have ih := loop_items_runs l (loop_stp j cap st Tf it vs)
      { c with
        sta := Wr ++ [13] ++ (encItems l).reverse, bod := c.bod ++ encItem it,
        ev := evFlat (loop_stp j cap st Tf it vs), evl := evLens (loop_stp j cap st Tf it vs) }
      Wr Fin Tc (fun i hi => hpl i (List.mem_cons_of_mem _ hi)) (fun i hi => htl i (List.mem_cons_of_mem _ hi))
      hrts hvalt hrv hrvl hcl hit rfl rfl rfl (by rw [e]; exact hcont)
    refine (loop_unroll (eval_nonempty_ne (by rw [loop_get_sta, hw']; simp)) x₁ ih).mono ?_
    simp only [runCost, loop_stp]
    omega

/-- The steps of the bodies of a round, beyond the item programs' own. -/
def loop_bodyCost (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (l : List MItem) : Nat :=
  runCost j cap st Tf l [] + 7 * (evFlat (loop_run j cap st Tf l [])).length +
    2 * (loop_run j cap st Tf l []).length + 47

include hE in
/-- **The bodies of a round**: each body's top vector goes to `RV2`, its length to `RVL2`. -/
theorem loop_bodies_runs : ∀ (bs : List (List MItem)) (c : Cf),
    (∀ it ∈ bs.flatten, ItemRunsC p j cap st Tf it 100) → (∀ it ∈ bs.flatten, it.tag < 13) →
    c.rts = st.rt → c.valt = valTable j cap st.x.length st.tt → c.rv = Tf.flatten →
    c.rvl = Tf.map List.length → c.Clean → c.it = [] → c.ev = [] → c.evl = [] → c.sta = (encBodies bs).reverse →
    NRuns (loop_bodiesP p) (c.toL B)
      ({ c with
          sta := [], bod := c.bod ++ encBodies bs,
          rv2 := c.rv2 ++ (bs.map (fun l => (loop_run j cap st Tf l []).headD [])).flatten,
          rvl2 := c.rvl2 ++ bs.map (fun l => ((loop_run j cap st Tf l []).headD []).length) }.toL B)
      ((bs.map (loop_bodyCost j cap st Tf)).sum + 1)
  | [], c, _, _, _, _, _, _, _, _, _, _, hw => by
    have e : { c with
        sta := [], bod := c.bod ++ encBodies [],
        rv2 := c.rv2 ++ (([] : List (List MItem)).map (fun l => (loop_run j cap st Tf l []).headD [])).flatten,
        rvl2 := c.rvl2 ++ ([] : List (List MItem)).map
          (fun l => ((loop_run j cap st Tf l []).headD []).length) } = c := by
      cases c; simp only [encBodies] at hw; subst hw; simp [encBodies]
    rw [e]
    exact nruns_loop_exit (by rw [loop_get_sta, hw]; rfl)
  | l :: bs, c, hpl, htl, hrts, hvalt, hrv, hrvl, hcl, hit, hev, hevl, hw => by
    have hpl₁ : ∀ it ∈ l, ItemRunsC p j cap st Tf it 100 := fun it h => hpl it (by simp [h])
    have htl₁ : ∀ it ∈ l, it.tag < 13 := fun it h => htl it (by simp [h])
    have hw' : c.sta = (encBodies bs).reverse ++ [13] ++ (encItems l).reverse := by
      rw [hw]; simp [encBodies, List.append_assoc]
    have ih := loop_bodies_runs bs
      { c with
        sta := (encBodies bs).reverse, bod := c.bod ++ encItems l ++ [13], ev := [], evl := [],
        rv2 := c.rv2 ++ (loop_run j cap st Tf l []).headD [],
        rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l []).headD []).length] }
      (fun it h => hpl it (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr h))
      (fun it h => htl it (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr h))
      hrts hvalt hrv hrvl hcl hit rfl rfl rfl
    have x := loop_items_runs hE l [] c (encBodies bs).reverse _ _ hpl₁ htl₁ hrts hvalt hrv hrvl hcl hit hw'
      (by rw [hev]; rfl) (by rw [hevl]; rfl) ih
    have e : { { c with
          sta := (encBodies bs).reverse, bod := c.bod ++ encItems l ++ [13], ev := [], evl := [],
          rv2 := c.rv2 ++ (loop_run j cap st Tf l []).headD [],
          rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l []).headD []).length] } with
          sta := [], bod := c.bod ++ encItems l ++ [13] ++ encBodies bs,
          rv2 := c.rv2 ++ (loop_run j cap st Tf l []).headD [] ++
            (bs.map (fun l => (loop_run j cap st Tf l []).headD [])).flatten,
          rvl2 := c.rvl2 ++ [((loop_run j cap st Tf l []).headD []).length] ++
            bs.map (fun l => ((loop_run j cap st Tf l []).headD []).length) } =
        { c with
          sta := [], bod := c.bod ++ encBodies (l :: bs),
          rv2 := c.rv2 ++ ((l :: bs).map (fun l => (loop_run j cap st Tf l []).headD [])).flatten,
          rvl2 := c.rvl2 ++ (l :: bs).map (fun l => ((loop_run j cap st Tf l []).headD []).length) } := by
      cases c; simp only at hev hevl; subst hev hevl; simp [encBodies, List.append_assoc]
    rw [e] at x
    refine x.mono ?_
    simp only [List.map_cons, List.sum_cons, loop_bodyCost]
    omega

end Bodies

/-! ## Comparing the rounds and moving the new values -/

def loop_eqUpdP : NProg NK := .seq (nclr 16) (.seq (nclr 17) (.seq (nclr 11) (.prim (.pushZ 11))))

def loop_neUpdP : NProg NK :=
  .seq (nclr 5) (.seq (nclr 15) (.seq (nmvAll 16 20 (by decide)) (.seq (nmvAll 20 5 (by decide))
    (.seq (nmvAll 17 20 (by decide)) (.seq (nmvAll 20 15 (by decide)) (.prim (.dec 11)))))))

/-- Compare the new values with the old: if equal, set the fuel to `0`; else move them and lower the fuel. -/
def loop_cmpP : NProg NK :=
  .seq (.prim (.pushZ 18)) (.seq (loop_eqP 16 5 (by decide) (by decide)) (.seq (loop_eqP 17 15 (by decide) (by decide))
    (.seq (.ite 18 .zero loop_eqUpdP loop_neUpdP) (.prim (.pop 18)))))

theorem loop_flat_inj : ∀ (R T : List (List Nat)), R.flatten = T.flatten → R.map List.length = T.map List.length →
    R = T
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | r :: R, t :: T, h₁, h₂ => by
    simp only [List.map_cons, List.cons.injEq] at h₂
    simp only [List.flatten_cons] at h₁
    have hr : r = t := by
      have := congrArg (List.take r.length) h₁
      rwa [List.take_left' rfl, h₂.1, List.take_left' rfl] at this
    subst hr
    rw [loop_flat_inj R T (List.append_cancel_left h₁) h₂.2]

theorem loop_sum_lengths (T : List (List Nat)) : (T.map List.length).sum = T.flatten.length := by
  simp [List.length_flatten]

theorem loop_cmp_runs (B : Lists NK) (c : Cf) (R T : List (List Nat)) (f : Nat) (hrv : c.rv = T.flatten)
    (hrvl : c.rvl = T.map List.length) (hrv2 : c.rv2 = R.flatten) (hrvl2 : c.rvl2 = R.map List.length)
    (hcl : c.Clean) (hfuel : c.fuel = [f + 1]) :
    NRuns loop_cmpP (c.toL B)
      ((if R = T then { c with rv2 := [], rvl2 := [], fuel := [0] }
        else { c with rv := R.flatten, rvl := R.map List.length, rv2 := [], rvl2 := [], fuel := [f] }).toL B)
      (5 * T.flatten.sum + 40 * (R.flatten.length + T.flatten.length + R.length + T.length) + 60) := by
  obtain ⟨h18, h19, h20, h21, h22, h23, h24, h25, h26⟩ := hcl
  have x₁ : NRuns (.prim (.pushZ 18)) (c.toL B) ({ c with s18 := [0] }.toL B) 1 := by
    have h := nruns_pushZ 18 (c.toL B)
    rw [loop_get_s18, h18, List.nil_append, loop_set_s18] at h; exact h
  let m₁ := loop_mism R.flatten.reverse T.flatten.reverse
  let m₂ := loop_mism (R.map List.length).reverse (T.map List.length).reverse
  have x₂ : NRuns (loop_eqP 16 5 (by decide) (by decide)) ({ c with s18 := [0] }.toL B)
      ({ c with s18 := [m₁] }.toL B) (5 * T.flatten.sum + 30 * (R.flatten.length + T.flatten.length) + 10) := by
    have h := loop_eqP_runs ({ c with s18 := [0] }.toL B) (A := 16) (B := 5) (by decide) (by decide) (by decide)
      R.flatten.reverse T.flatten.reverse 0 (by simp [hrv2]) (by simp [hrv]) h21 h22 h25 h26 rfl
    rw [loop_set_s18, Nat.zero_add] at h
    simpa only [List.sum_reverse, List.length_reverse] using h
  have x₃ : NRuns (loop_eqP 17 15 (by decide) (by decide)) ({ c with s18 := [m₁] }.toL B)
      ({ c with s18 := [m₁ + m₂] }.toL B) (5 * T.flatten.length + 30 * (R.length + T.length) + 10) := by
    have h := loop_eqP_runs ({ c with s18 := [m₁] }.toL B) (A := 17) (B := 15) (by decide) (by decide) (by decide)
      (R.map List.length).reverse (T.map List.length).reverse m₁ (by simp [hrvl2]) (by simp [hrvl]) h21 h22 h25 h26
      rfl
    rw [loop_set_s18] at h
    simpa only [List.sum_reverse, List.length_reverse, loop_sum_lengths, List.length_map] using h
  have x₄ := nruns_pop 18 ({ c with s18 := [0] }.toL B) (l := []) (v := 0) rfl
  rw [loop_set_s18] at x₄
  by_cases hRT : R = T
  · subst hRT
    have hm : m₁ + m₂ = 0 := by
      simp only [m₁, m₂, (loop_mism_zero _ _).2 rfl]
    have u₁ := nruns_clr 16 ({ c with s18 := [0] }.toL B)
    simp only [loop_set_rv2, loop_get_rv2] at u₁
    have u₂ := nruns_clr 17 ({ c with s18 := [0], rv2 := [] }.toL B)
    simp only [loop_set_rvl2, loop_get_rvl2] at u₂
    have u₃ := nruns_clr 11 ({ c with s18 := [0], rv2 := [], rvl2 := [] }.toL B)
    simp only [loop_set_fuel, loop_get_fuel] at u₃
    have u₄ := nruns_pushZ 11 ({ c with s18 := [0], rv2 := [], rvl2 := [], fuel := [] }.toL B)
    simp only [loop_set_fuel, loop_get_fuel, List.nil_append] at u₄
    have u₅ := nruns_pop 18 ({ c with s18 := [0], rv2 := [], rvl2 := [], fuel := [0] }.toL B) (l := []) (v := 0) rfl
    simp only [loop_set_s18] at u₅
    have e : { { c with s18 := [0], rv2 := [], rvl2 := [], fuel := [0] } with s18 := [] } =
        (if R = R then { c with rv2 := [], rvl2 := [], fuel := [0] }
          else { c with rv := R.flatten, rvl := R.map List.length, rv2 := [], rvl2 := [], fuel := [f] }) := by
      rw [if_pos rfl]; cases c; simp only at h18; subst h18; rfl
    rw [e] at u₅
    have hz : NTest.zero.eval (({ c with s18 := [m₁ + m₂] }.toL B) 18) = true := by
      rw [loop_get_s18, hm]; rfl
    rw [hm] at x₃
    refine (x₁.seq (x₂.seq (x₃.seq (((u₁.seq (u₂.seq (u₃.seq u₄))).iteT (q := loop_neUpdP) (by
      rw [loop_get_s18]; rfl)).seq u₅)))).mono ?_
    simp only [hrv2, hrvl2, hfuel, List.length_map, List.length_cons, List.length_nil]
    omega
  · have hm : m₁ + m₂ ≠ 0 := by
      intro h
      have h₁ : m₁ = 0 := by omega
      have h₂ : m₂ = 0 := by omega
      have e₁ := List.reverse_inj.1 ((loop_mism_zero _ _).1 h₁)
      have e₂ := List.reverse_inj.1 ((loop_mism_zero _ _).1 h₂)
      exact hRT (loop_flat_inj R T e₁ e₂)
    obtain ⟨m, hmm⟩ : ∃ m, m₁ + m₂ = m + 1 := ⟨m₁ + m₂ - 1, by omega⟩
    have u₁ := nruns_clr 5 ({ c with s18 := [m₁ + m₂] }.toL B)
    simp only [loop_set_rv, loop_get_rv] at u₁
    have u₂ := nruns_clr 15 ({ c with s18 := [m₁ + m₂], rv := [] }.toL B)
    simp only [loop_set_rvl, loop_get_rvl] at u₂
    have u₃ := nruns_mvAll 16 20 (by decide) ({ c with s18 := [m₁ + m₂], rv := [], rvl := [] }.toL B)
    have r : ({ c with s18 := [m₁ + m₂], rv := [], rvl := [] }.toL B) 20 = [] := h20
    rw [r, List.nil_append] at u₃
    simp only [loop_get_rv2, loop_set_s20, loop_set_rv2] at u₃
    have u₄ := nruns_mvAll 20 5 (by decide)
      ({ c with s18 := [m₁ + m₂], rv := [], rvl := [], s20 := c.rv2.reverse, rv2 := [] }.toL B)
    simp only [loop_get_s20, loop_get_rv, loop_set_s20, loop_set_rv, List.nil_append, List.reverse_reverse] at u₄
    have u₅ := nruns_mvAll 17 20 (by decide)
      ({ c with s18 := [m₁ + m₂], rv := c.rv2, rvl := [], s20 := [], rv2 := [] }.toL B)
    simp only [loop_get_s20, loop_get_rvl2, loop_set_s20, loop_set_rvl2, List.nil_append] at u₅
    have u₆ := nruns_mvAll 20 15 (by decide)
      ({ c with s18 := [m₁ + m₂], rv := c.rv2, rvl := [], s20 := c.rvl2.reverse, rv2 := [], rvl2 := [] }.toL B)
    simp only [loop_get_s20, loop_get_rvl, loop_set_s20, loop_set_rvl, List.nil_append, List.reverse_reverse] at u₆
    have u₇ := nruns_dec 11
      ({ c with s18 := [m₁ + m₂], rv := c.rv2, rvl := c.rvl2, s20 := [], rv2 := [], rvl2 := [] }.toL B)
      (l := []) (v := f + 1) (by rw [loop_get_fuel, hfuel]; rfl)
    simp only [loop_set_fuel, Nat.add_sub_cancel, List.nil_append] at u₇
    have u₈ := nruns_pop 18
      ({ c with s18 := [m₁ + m₂], rv := c.rv2, rvl := c.rvl2, s20 := [], rv2 := [], rvl2 := [], fuel := [f] }.toL B)
      (l := []) (v := m₁ + m₂) rfl
    simp only [loop_set_s18] at u₈
    have e : { { c with
        s18 := [m₁ + m₂], rv := c.rv2, rvl := c.rvl2, s20 := [], rv2 := [], rvl2 := [], fuel := [f] } with
        s18 := [] } =
        (if R = T then { c with rv2 := [], rvl2 := [], fuel := [0] }
          else { c with rv := R.flatten, rvl := R.map List.length, rv2 := [], rvl2 := [], fuel := [f] }) := by
      rw [if_neg hRT]; cases c; simp only at h18 h20 hrv2 hrvl2; subst h18 h20 hrv2 hrvl2; rfl
    rw [e] at u₈
    refine (x₁.seq (x₂.seq (x₃.seq (((u₁.seq (u₂.seq (u₃.seq (u₄.seq (u₅.seq (u₆.seq u₇)))))).iteF
      (p := loop_eqUpdP) (by rw [loop_get_s18, hmm]; rfl)).seq u₈)))).mono ?_
    simp only [hrv, hrvl, hrv2, hrvl2, List.length_reverse, List.length_map]
    omega

/-! ## A round, and the rounds -/

/-- One round: lay the bodies out on `6`, run them, compare and move. -/
def loop_roundP (p : NProg NK) : NProg NK := .seq (nmvAll 10 12 (by decide)) (.seq (loop_bodiesP p) loop_cmpP)

/-- The rounds, while the fuel lasts. -/
def loop_fixP (p : NProg NK) : NProg NK := .loop 11 .pos (loop_roundP p)

theorem loop_headD_length (vs : List (List Nat)) : (vs.headD []).length ≤ (evFlat vs).length := by
  cases vs with
  | nil => simp
  | cons v vs => simp [evFlat_cons]

/-- The extra steps of the bodies and of the comparison fit in a round's allowance. -/
theorem loop_round_sum (j cap : Nat) (st : PSt) (Tf : List (List Nat)) : ∀ (bs : List (List MItem)),
    (bs.map (loop_bodyCost j cap st Tf)).sum +
        40 * ((bs.map (fun l => (loop_run j cap st Tf l []).headD [])).flatten.length + bs.length) ≤
      (bs.map (fun l => runCost j cap st Tf l [] + 100 * (l.length +
        (evFlat (loop_run j cap st Tf l [])).length + 1))).sum
  | [] => by simp
  | l :: bs => by
    have ih := loop_round_sum j cap st Tf bs
    have h₁ := loop_headD_length (loop_run j cap st Tf l [])
    have h₂ := loop_run_length j cap st Tf l []
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append, List.length_cons,
      loop_bodyCost] at ih h₂ ⊢
    simp only [List.length_nil, Nat.zero_add] at h₂
    omega

section Rounds
variable {p : NProg NK} {B : Lists NK} {j cap : Nat} {st : PSt}
  (hE : EvalEnv B j cap st [])
  (hp : ∀ (Tf : List (List Nat)) (it : MItem), it ∈ st.bodies.flatten ++ st.start → ItemRunsC p j cap st Tf it 100)
  (hTag : ∀ it ∈ st.bodies.flatten, it.tag < 13)

/-- The rule values after a round. -/
abbrev loop_round (j cap : Nat) (st : PSt) (Tf : List (List Nat)) : List (List Nat) :=
  roundT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies Tf

include hE hp hTag in
/-- **One round**: the fuel drops to `0` if the values stay, else the new values replace them. -/
theorem loop_roundP_runs (c : Cf) (Tf : List (List Nat)) (f : Nat) (hrts : c.rts = st.rt)
    (hvalt : c.valt = valTable j cap st.x.length st.tt) (hcl : c.Clean) (hit : c.it = []) (hev : c.ev = [])
    (hevl : c.evl = []) (hw : c.sta = []) (hbod : c.bod = encBodies st.bodies) (hrv2 : c.rv2 = [])
    (hrvl2 : c.rvl2 = []) :
    NRuns (loop_roundP p) ({ c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [f + 1] }.toL B)
      ((if loop_round j cap st Tf = Tf then { c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [0] }
        else { c with
          rv := (loop_round j cap st Tf).flatten, rvl := (loop_round j cap st Tf).map List.length,
          fuel := [f] }).toL B)
      (roundCost j cap st Tf - 2) := by
  let c₀ : Cf := { c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [f + 1] }
  have x₁ := nruns_mvAll 10 12 (by decide) (c₀.toL B)
  simp only [loop_get_sta, loop_get_bod, loop_set_sta, loop_set_bod] at x₁
  rw [show c₀.sta = [] from hw, show c₀.bod = encBodies st.bodies from hbod, List.nil_append] at x₁
  let c₁ : Cf := { c₀ with sta := (encBodies st.bodies).reverse, bod := [] }
  have x₂ := loop_bodies_runs (p := p) (Tf := Tf) hE st.bodies c₁
    (fun it h => hp Tf it (List.mem_append_left _ h)) hTag hrts hvalt rfl rfl hcl hit hev hevl rfl
  let R := loop_round j cap st Tf
  have hR : (st.bodies.map (fun l => (loop_run j cap st Tf l []).headD [])) = R := rfl
  let c₂ : Cf := { c₀ with sta := [], bod := encBodies st.bodies, rv2 := R.flatten, rvl2 := R.map List.length }
  have e₂ : { c₁ with
      sta := [], bod := c₁.bod ++ encBodies st.bodies,
      rv2 := c₁.rv2 ++ (st.bodies.map (fun l => (loop_run j cap st Tf l []).headD [])).flatten,
      rvl2 := c₁.rvl2 ++ st.bodies.map (fun l => ((loop_run j cap st Tf l []).headD []).length) } = c₂ := by
    simp only [c₁, c₂, c₀, hR, hrv2, hrvl2, List.nil_append]
    rw [← hR, List.map_map]; rfl
  rw [e₂] at x₂
  have x₃ := loop_cmp_runs B c₂ R Tf f rfl rfl rfl rfl hcl rfl
  have e₃ : (if R = Tf then { c₂ with rv2 := [], rvl2 := [], fuel := [0] }
      else { c₂ with rv := R.flatten, rvl := R.map List.length, rv2 := [], rvl2 := [], fuel := [f] }) =
      (if R = Tf then { c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [0] }
        else { c with rv := R.flatten, rvl := R.map List.length, fuel := [f] }) := by
    cases c; simp only at hw hbod hrv2 hrvl2; subst hw hbod hrv2 hrvl2; rfl
  rw [e₃] at x₃
  refine (x₁.seq (x₂.seq x₃)).mono ?_
  have hs := loop_round_sum j cap st Tf st.bodies
  rw [hR] at hs
  have hRl : R.length = st.bodies.length := by simp [R, roundT]
  simp only [roundCost]
  simp only [loop_run] at hs ⊢
  omega

include hE hp hTag in
/-- **The rounds**: from the values `Tf` and fuel `f`, the loop ends with the values `fixT f Tf` and fuel `0`. -/
theorem loop_fixP_runs (c : Cf) (hrts : c.rts = st.rt) (hvalt : c.valt = valTable j cap st.x.length st.tt)
    (hcl : c.Clean) (hit : c.it = []) (hev : c.ev = []) (hevl : c.evl = []) (hw : c.sta = [])
    (hbod : c.bod = encBodies st.bodies) (hrv2 : c.rv2 = []) (hrvl2 : c.rvl2 = []) :
    ∀ (f : Nat) (Tf : List (List Nat)),
      NRuns (loop_fixP p) ({ c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [f] }.toL B)
        ({ c with
          rv := (fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies f Tf).flatten,
          rvl := (fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies f Tf).map List.length,
          fuel := [0] }.toL B)
        (fixCost j cap st f Tf)
  | 0, Tf => by
    simp only [fixT, fixCost]
    exact nruns_loop_exit (by rw [loop_get_fuel]; rfl)
  | f + 1, Tf => by
    have x₁ := loop_roundP_runs (p := p) hE hp hTag c Tf f hrts hvalt hcl hit hev hevl hw hbod hrv2 hrvl2
    have hpos : NTest.pos.eval (({ c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [f + 1] }.toL B) 11)
        = true := by rw [loop_get_fuel]; rfl
    have hRC : 100 ≤ roundCost j cap st Tf := by simp only [roundCost]; omega
    by_cases hR : loop_round j cap st Tf = Tf
    · rw [if_pos hR] at x₁
      have x₂ := nruns_loop_exit (i := 11) (c := .pos) (p := loop_roundP p)
        (S := { c with rv := Tf.flatten, rvl := Tf.map List.length, fuel := [0] }.toL B)
        (by rw [loop_get_fuel]; rfl)
      have e : fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies (f + 1) Tf = Tf := by
        simp only [fixT]; rw [if_pos hR]
      rw [e]
      refine (loop_unroll hpos x₁ x₂).mono ?_
      simp only [fixCost]; rw [if_pos hR]; omega
    · rw [if_neg hR] at x₁
      have ih := loop_fixP_runs c hrts hvalt hcl hit hev hevl hw hbod hrv2 hrvl2 f (loop_round j cap st Tf)
      have e : fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies (f + 1) Tf =
          fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies f (loop_round j cap st Tf) := by
        simp only [fixT]; rw [if_neg hR]
      rw [e]
      refine (loop_unroll hpos x₁ ih).mono ?_
      simp only [fixCost]; rw [if_neg hR]; simp only [loop_round] at hRC ⊢; omega

end Rounds

/-! ## Preparing: counting moves, zeros -/

/-- Move everything from `i` to `j` (reversing it), counting the numbers on `k`. -/
def loop_cntMvP (i j k : Fin NK) (hij : i ≠ j) : NProg NK := .loop i .nonempty (.seq (nmv i j hij) (.prim (.inc k)))

theorem loop_cntMv_runs (i j k : Fin NK) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (lk : List Nat) :
    ∀ (Ar : List Nat) (S : Lists NK) (m : Nat), S i = Ar.reverse → S k = lk ++ [m] →
      NRuns (loop_cntMvP i j k hij) S (((S.set i []).set j (S j ++ Ar)).set k (lk ++ [m + Ar.length]))
        (4 * Ar.length + 1)
  | [], S, m, hi, hk => by
    simp only [List.reverse_nil] at hi
    have e : ((S.set i []).set j (S j ++ [])).set k (lk ++ [m + ([] : List Nat).length]) = S := by
      funext x; simp only [Lists.set]
      by_cases hxk : x = k
      · subst hxk; simp [hk]
      · by_cases hxi : x = i
        · subst hxi; simp [hxk, hi, hij]
        · by_cases hxj : x = j
          · subst hxj; simp [hxk]
          · simp [hxk, hxi, hxj]
    rw [e]
    exact (nruns_loop_exit (by rw [hi]; rfl)).mono (by omega)
  | a :: Ar, S, m, hi, hk => by
    have x₁ := nruns_mv i j hij S (l := Ar.reverse) (v := a) (by rw [hi]; simp)
    have x₂ := nruns_inc k ((S.set j (S j ++ [a])).set i Ar.reverse) (l := lk) (v := m)
      (by rw [Lists.set_ne _ _ (Ne.symm hik), Lists.set_ne _ _ (Ne.symm hjk), hk])
    have ih := loop_cntMv_runs i j k hij hik hjk lk Ar
      (((S.set j (S j ++ [a])).set i Ar.reverse).set k (lk ++ [m + 1])) (m + 1)
      (by rw [Lists.set_ne _ _ hik, Lists.set_same]) (by rw [Lists.set_same])
    have e : (((((S.set j (S j ++ [a])).set i Ar.reverse).set k (lk ++ [m + 1])).set i []).set j
        ((((S.set j (S j ++ [a])).set i Ar.reverse).set k (lk ++ [m + 1])) j ++ Ar)).set k
        (lk ++ [m + 1 + Ar.length]) = ((S.set i []).set j (S j ++ a :: Ar)).set k (lk ++ [m + (a :: Ar).length]) := by
      have hl : m + 1 + Ar.length = m + (a :: Ar).length := by simp; omega
      rw [hl]
      funext x; simp only [Lists.set]
      by_cases hxk : x = k
      · simp [hxk]
      · by_cases hxj : x = j
        · subst hxj; simp [hxk, Ne.symm hij]
        · by_cases hxi : x = i
          · subst hxi; simp [hik, hij]
          · simp [hxk, hxj, hxi]
    rw [e] at ih
    refine (loop_unroll (by rw [hi]; simp) (x₁.seq x₂) ih).mono ?_
    simp only [List.length_cons]; omega

/-- Push `v` zeros on `RV`, the top `v` of `24` lowered to `0`. -/
def loop_zerosP : NProg NK := .loop 24 .pos (.seq (.prim (.dec 24)) (.prim (.pushZ 5)))

theorem loop_zeros_runs (l24 : List Nat) : ∀ (v : Nat) (S : Lists NK) (X : List Nat), S 24 = l24 ++ [v] → S 5 = X →
    NRuns loop_zerosP S ((S.set 24 (l24 ++ [0])).set 5 (X ++ List.replicate v 0)) (3 * v + 1)
  | 0, S, X, h24, h5 => by
    rw [List.replicate_zero, List.append_nil, ← h24, ← h5, Lists.set_get_self, Lists.set_get_self]
    exact nruns_loop_exit (by rw [h24]; simp)
  | v + 1, S, X, h24, h5 => by
    have x₁ := nruns_dec 24 S h24
    simp only [Nat.add_sub_cancel] at x₁
    have x₂ := nruns_pushZ 5 (S.set 24 (l24 ++ [v]))
    rw [Lists.set_ne _ _ (by decide), h5] at x₂
    have ih := loop_zeros_runs l24 v ((S.set 24 (l24 ++ [v])).set 5 (X ++ [0])) (X ++ [0])
      (by rw [Lists.set_ne _ _ (by decide), Lists.set_same]) (by rw [Lists.set_same])
    have e : ((((S.set 24 (l24 ++ [v])).set 5 (X ++ [0])).set 24 (l24 ++ [0])).set 5 (X ++ [0] ++ List.replicate v 0))
        = (S.set 24 (l24 ++ [0])).set 5 (X ++ List.replicate (v + 1) 0) := by
      rw [List.replicate_succ, List.append_assoc]
      funext x; simp only [Lists.set]
      by_cases h5 : x = 5 <;> by_cases h24 : x = 24 <;> simp [h5, h24]
    rw [e] at ih
    exact (loop_unroll (by rw [h24]; simp) (x₁.seq x₂) ih).mono (by omega)

/-! ## Preparing: the starting rule values -/

/-- The record with empty scratch stacks. -/
def Cf.clr (c : Cf) : Cf :=
  { c with s18 := [], s19 := [], s20 := [], s21 := [], s22 := [], s23 := [], s24 := [], s25 := [], s26 := [] }

theorem Cf.clr_clean (c : Cf) : c.clr.Clean := by
  simp [Cf.Clean, Cf.clr]

theorem loop_valT_out (j cap N : Nat) (tt : List (Nat × Nat)) (t : Nat) (h : tt.length < t) :
    valT j cap N tt t = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [valT]
  have : tt[k]? = none := List.getElem?_eq_none (by omega)
  simp [this]

theorem loop_valTable_get (j cap N : Nat) (tt : List (Nat × Nat)) (t : Nat)
    (h : t < (valTable j cap N tt).length) : (valTable j cap N tt)[t] = valT j cap N tt t := by
  simp [valTable, typeTable]

theorem loop_valTable_length (j cap N : Nat) (tt : List (Nat × Nat)) :
    (valTable j cap N tt).length = tt.length + 1 := by
  simp [valTable, typeTable]

/-- Push `valT t` on `22`, for `t` on `21` (popped) and the length `L` of `VALT` on `18`. -/
def loop_lookupP : NProg NK :=
  .seq (.prim (.dup 21 25 (by decide))) (.seq (.prim (.dup 18 26 (by decide))) (.seq (loop_minP false)
    (.seq (.prim (.pop 25))
      (.ite 26 .pos (.seq (.prim (.pop 26)) (peekAt 37 23 21 22 (by decide) (by decide)))
        (.seq (.prim (.pop 26)) (.seq (.prim (.pop 21)) (.prim (.pushZ 22))))))))

/-- One rule: its starting value (zeros) on `RV`, its length on `RVL` and added to the fuel. -/
def loop_ruleP : NProg NK :=
  .seq (.prim (.dup 20 21 (by decide))) (.seq loop_lookupP (.seq (.prim (.dup 22 15 (by decide)))
    (.seq (.prim (.dup 22 24 (by decide))) (.seq loop_zerosP (.seq (.prim (.pop 24))
      (.seq (addTo 22 11) (nmv 20 9 (by decide))))))))

section Rule
variable (B : Lists NK) (c : Cf) (j cap : Nat) (st : PSt) (hvalt : c.valt = valTable j cap st.x.length st.tt)
include hvalt

theorem loop_lookup_runs (Q : List Nat) (t : Nat) :
    NRuns loop_lookupP ({ c.clr with s18 := [st.tt.length + 1], s20 := Q, s21 := [t] }.toL B)
      ({ c.clr with s18 := [st.tt.length + 1], s20 := Q, s22 := [valT j cap st.x.length st.tt t] }.toL B)
      (20 * st.tt.length + 40) := by
  let L := st.tt.length + 1
  have x₁ : NRuns (.prim (.dup 21 25 (by decide))) ({ c.clr with s18 := [L], s20 := Q, s21 := [t] }.toL B)
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t] }.toL B) 1 := by
    have h := nruns_dup 21 25 (by decide) ({ c.clr with s18 := [L], s20 := Q, s21 := [t] }.toL B) (l := []) (v := t) rfl
    simp only [loop_get_s25, loop_set_s25] at h; exact h
  have x₂ : NRuns (.prim (.dup 18 26 (by decide))) ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t] }.toL B)
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t], s26 := [L] }.toL B) 1 := by
    have h := nruns_dup 18 26 (by decide) ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t] }.toL B) (l := [])
      (v := L) rfl
    simp only [loop_get_s26, loop_set_s26] at h; exact h
  have x₃ : NRuns (loop_minP false) ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t], s26 := [L] }.toL B)
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [0], s26 := [loop_minRes false t L] }.toL B) (5 * L + 6) := by
    have h := loop_minP_runs false L t ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [t], s26 := [L] }.toL B) rfl rfl
    simp only [loop_set_s25, loop_set_s26] at h; exact h
  have x₄ : NRuns (.prim (.pop 25))
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [0], s26 := [loop_minRes false t L] }.toL B)
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [loop_minRes false t L] }.toL B) 1 := by
    have h := nruns_pop 25
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s25 := [0], s26 := [loop_minRes false t L] }.toL B) (l := []) (v := 0) rfl
    simp only [loop_set_s25] at h; exact h
  have x₅ : NRuns (.ite 26 .pos (.seq (.prim (.pop 26)) (peekAt 37 23 21 22 (by decide) (by decide)))
        (.seq (.prim (.pop 26)) (.seq (.prim (.pop 21)) (.prim (.pushZ 22)))))
      ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [loop_minRes false t L] }.toL B)
      ({ c.clr with s18 := [L], s20 := Q, s22 := [valT j cap st.x.length st.tt t] }.toL B) (6 * L + 4 * L + 10) := by
    have hp₁ := nruns_pop 26 ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [loop_minRes false t L] }.toL B)
      (l := []) (v := loop_minRes false t L) rfl
    simp only [loop_set_s26] at hp₁
    by_cases ht : t < L
    · have hr : loop_minRes false t L = (L - t - 1) + 1 := by simp only [loop_minRes]; split <;> omega
      have hV : (({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [] }.toL B) 37) = valTable j cap st.x.length st.tt :=
        hvalt
      have hk : t < (({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [] }.toL B) 37).length := by
        rw [hV, loop_valTable_length]; exact ht
      have hpk := nruns_peekAt 37 23 21 22 (by decide) (by decide) (by decide)
        ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [] }.toL B) rfl (lc := []) (k := t) rfl hk
      simp only [hV, loop_valTable_get, loop_set_s21, loop_set_s22, loop_get_s22] at hpk
      rw [loop_valTable_length] at hpk
      refine ((hp₁.seq hpk).iteT (by rw [loop_get_s26, hr]; exact eval_pos_succ [] _)).mono ?_
      omega
    · have hr : loop_minRes false t L = 0 := by
        simp only [loop_minRes, Bool.false_eq_true, if_false]; split <;> omega
      have hv : valT j cap st.x.length st.tt t = 0 := loop_valT_out _ _ _ _ _ (by omega)
      have hp₂ : NRuns (.prim (.pop 21)) ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [] }.toL B)
          ({ c.clr with s18 := [L], s20 := Q, s26 := [] }.toL B) 1 := by
        have h := nruns_pop 21 ({ c.clr with s18 := [L], s20 := Q, s21 := [t], s26 := [] }.toL B) (l := []) (v := t) rfl
        simp only [loop_set_s21] at h; exact h
      have hp₃ : NRuns (.prim (.pushZ 22)) ({ c.clr with s18 := [L], s20 := Q, s26 := [] }.toL B)
          ({ c.clr with s18 := [L], s20 := Q, s22 := [0] }.toL B) 1 := by
        have h := nruns_pushZ 22 ({ c.clr with s18 := [L], s20 := Q, s26 := [] }.toL B)
        simp only [loop_get_s22, loop_set_s22] at h; exact h
      rw [hv]
      refine ((hp₁.seq (hp₂.seq hp₃)).iteF (by rw [loop_get_s26, hr]; rfl)).mono ?_
      omega
  refine (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono ?_
  simp only [L]; omega

theorem loop_rule_runs (t : Nat) (R D X Y : List Nat) (F : Nat) :
    NRuns loop_ruleP
      ({ c.clr with s18 := [st.tt.length + 1], s20 := R ++ [t], rts := D, rv := X, rvl := Y, fuel := [F] }.toL B)
      ({ c.clr with
          s18 := [st.tt.length + 1], s20 := R, rts := D ++ [t],
          rv := X ++ List.replicate (valT j cap st.x.length st.tt t) 0,
          rvl := Y ++ [valT j cap st.x.length st.tt t], fuel := [F + valT j cap st.x.length st.tt t] }.toL B)
      (20 * st.tt.length + 6 * valT j cap st.x.length st.tt t + 60) := by
  let L := st.tt.length + 1
  let v := valT j cap st.x.length st.tt t
  let c' : Cf := { c with rts := D, rv := X, rvl := Y, fuel := [F] }
  have x₁ : NRuns (.prim (.dup 20 21 (by decide))) ({ c'.clr with s18 := [L], s20 := R ++ [t] }.toL B)
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s21 := [t] }.toL B) 1 := by
    have h := nruns_dup 20 21 (by decide) ({ c'.clr with s18 := [L], s20 := R ++ [t] }.toL B) (l := R) (v := t) rfl
    simp only [loop_get_s21, loop_set_s21] at h; exact h
  have x₂ := loop_lookup_runs B c' j cap st hvalt (R ++ [t]) t
  have x₃ : NRuns (.prim (.dup 22 15 (by decide))) ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v] }.toL B)
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v] }.toL B) 1 := by
    have h := nruns_dup 22 15 (by decide) ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v] }.toL B)
      (l := []) (v := v) rfl
    simp only [loop_get_rvl, loop_set_rvl] at h; exact h
  have x₄ : NRuns (.prim (.dup 22 24 (by decide)))
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v] }.toL B)
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [v] }.toL B) 1 := by
    have h := nruns_dup 22 24 (by decide)
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v] }.toL B) (l := []) (v := v) rfl
    simp only [loop_get_s24, loop_set_s24] at h; exact h
  have x₅ : NRuns loop_zerosP
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [v] }.toL B)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [0],
          rv := X ++ List.replicate v 0 }.toL B) (3 * v + 1) := by
    have h := loop_zeros_runs [] v
      ({ c'.clr with s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [v] }.toL B) X rfl rfl
    simp only [loop_set_s24, loop_set_rv, List.nil_append] at h; exact h
  have x₆ : NRuns (.prim (.pop 24))
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [0],
          rv := X ++ List.replicate v 0 }.toL B)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], rv := X ++ List.replicate v 0 }.toL B) 1 := by
    have h := nruns_pop 24
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], s24 := [0],
          rv := X ++ List.replicate v 0 }.toL B) (l := []) (v := 0) rfl
    simp only [loop_set_s24] at h; exact h
  have x₇ : NRuns (addTo 22 11)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], rv := X ++ List.replicate v 0 }.toL B)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], rvl := Y ++ [v], rv := X ++ List.replicate v 0, fuel := [F + v] }.toL B)
      (3 * v + 2) := by
    have h := nruns_addTo 22 11 (by decide)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], s22 := [v], rvl := Y ++ [v], rv := X ++ List.replicate v 0 }.toL B)
      (l := []) (l' := []) (a := v) (b := F) rfl rfl
    simp only [loop_set_s22, loop_set_fuel, List.nil_append] at h; exact h
  have x₈ : NRuns (nmv 20 9 (by decide))
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], rvl := Y ++ [v], rv := X ++ List.replicate v 0, fuel := [F + v] }.toL B)
      ({ c.clr with
          s18 := [L], s20 := R, rts := D ++ [t], rv := X ++ List.replicate v 0,
          rvl := Y ++ [v], fuel := [F + v] }.toL B) 2 := by
    have h := nruns_mv 20 9 (by decide)
      ({ c'.clr with
          s18 := [L], s20 := R ++ [t], rvl := Y ++ [v], rv := X ++ List.replicate v 0, fuel := [F + v] }.toL B)
      (l := R) (v := t) rfl
    simp only [loop_get_rts, loop_set_rts, loop_set_s20] at h; exact h
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq x₈))))))).mono (by omega)

/-- The values of the rules `rs`: their lengths, and the zeros. -/
abbrev loop_vals (j cap : Nat) (st : PSt) (rs : List Nat) : List Nat := rs.map (valT j cap st.x.length st.tt)

theorem loop_rules_runs : ∀ (rs D X Y : List Nat) (F : Nat),
    NRuns (.loop 20 .nonempty loop_ruleP)
      ({ c.clr with s18 := [st.tt.length + 1], s20 := rs.reverse, rts := D, rv := X, rvl := Y, fuel := [F] }.toL B)
      ({ c.clr with
          s18 := [st.tt.length + 1], s20 := [], rts := D ++ rs,
          rv := X ++ (rs.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := Y ++ loop_vals j cap st rs, fuel := [F + (loop_vals j cap st rs).sum] }.toL B)
      ((rs.map (fun t => 20 * st.tt.length + 6 * valT j cap st.x.length st.tt t + 61)).sum + 1)
  | [], D, X, Y, F => by
    simp only [List.append_nil, List.map_nil, List.flatten_nil, List.sum_nil, Nat.add_zero, Nat.zero_add]
    exact nruns_loop_exit (by rw [loop_get_s20]; rfl)
  | t :: rs, D, X, Y, F => by
    have x₁ := loop_rule_runs B c j cap st hvalt t rs.reverse D X Y F
    have ih := loop_rules_runs rs (D ++ [t]) (X ++ List.replicate (valT j cap st.x.length st.tt t) 0)
      (Y ++ [valT j cap st.x.length st.tt t]) (F + valT j cap st.x.length st.tt t)
    have e : { c.clr with
        s18 := [st.tt.length + 1], s20 := [], rts := D ++ [t] ++ rs,
        rv := X ++ List.replicate (valT j cap st.x.length st.tt t) 0 ++
          (rs.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
        rvl := Y ++ [valT j cap st.x.length st.tt t] ++ loop_vals j cap st rs,
        fuel := [F + valT j cap st.x.length st.tt t + (loop_vals j cap st rs).sum] } =
        { c.clr with
          s18 := [st.tt.length + 1], s20 := [], rts := D ++ t :: rs,
          rv := X ++ ((t :: rs).map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := Y ++ loop_vals j cap st (t :: rs), fuel := [F + (loop_vals j cap st (t :: rs)).sum] } := by
      simp [List.append_assoc, Nat.add_assoc]
    rw [e] at ih
    have h20 : ({ c.clr with
        s18 := [st.tt.length + 1], s20 := (t :: rs).reverse, rts := D, rv := X, rvl := Y, fuel := [F] }.toL B) =
        ({ c.clr with
            s18 := [st.tt.length + 1], s20 := rs.reverse ++ [t], rts := D, rv := X, rvl := Y, fuel := [F] }.toL B) := by
      rw [List.reverse_cons]
    rw [h20]
    refine (loop_unroll (by rw [loop_get_s20]; simp) x₁ ih).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Prepare: the fuel `1`, the start items moved to `6` (with their count on top), the length of `VALT` on `18`,
then the rules' starting values and the fuel `Σ valT + 1`. -/
def loop_initP : NProg NK :=
  .seq (nclr 11) (.seq (npushC 11 1) (.seq (.prim (.pushZ 18)) (.seq (loop_cntMvP 12 6 18 (by decide))
    (.seq (nmv 18 6 (by decide)) (.seq (.prim (.pushZ 18)) (.seq (loop_cntMvP 37 19 18 (by decide))
      (.seq (nmvAll 19 37 (by decide)) (.seq (nmvAll 9 20 (by decide)) (.seq (.loop 20 .nonempty loop_ruleP)
        (.prim (.pop 18)))))))))))

theorem loop_init_runs (nb A W₀ rt : List Nat) :
    NRuns loop_initP ({ c.clr with fuel := nb, sta := A, w := W₀, rts := rt, rv := [], rvl := [] }.toL B)
      ({ c.clr with
          fuel := [1 + (loop_vals j cap st rt).sum], sta := [], w := W₀ ++ A.reverse ++ [A.length], rts := rt,
          rv := (rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := loop_vals j cap st rt }.toL B)
      (2 * nb.length + 4 * A.length + 7 * st.tt.length + 3 * rt.length +
        (rt.map (fun t => 20 * st.tt.length + 6 * valT j cap st.x.length st.tt t + 61)).sum + 30) := by
  have hVl : c.valt.length = st.tt.length + 1 := by rw [hvalt, loop_valTable_length]
  let c₁ : Cf := { c with fuel := nb, sta := A, w := W₀, rts := rt, rv := [], rvl := [] }
  have x₁ : NRuns (nclr 11) (c₁.clr.toL B) ({ c₁.clr with fuel := [] }.toL B) (2 * nb.length + 1) := by
    have h := nruns_clr 11 (c₁.clr.toL B)
    simp only [loop_set_fuel, loop_get_fuel] at h; exact h
  have x₂ : NRuns (npushC 11 1) ({ c₁.clr with fuel := [] }.toL B) ({ c₁.clr with fuel := [1] }.toL B) 2 := by
    have h := nruns_pushC 11 ({ c₁.clr with fuel := [] }.toL B) 1
    simp only [loop_set_fuel, loop_get_fuel] at h; exact h
  have x₃ : NRuns (.prim (.pushZ 18)) ({ c₁.clr with fuel := [1] }.toL B)
      ({ c₁.clr with fuel := [1], s18 := [0] }.toL B) 1 := by
    have h := nruns_pushZ 18 ({ c₁.clr with fuel := [1] }.toL B)
    simp only [loop_set_s18, loop_get_s18] at h; exact h
  have x₄ : NRuns (loop_cntMvP 12 6 18 (by decide)) ({ c₁.clr with fuel := [1], s18 := [0] }.toL B)
      ({ c₁.clr with fuel := [1], s18 := [A.length], sta := [], w := W₀ ++ A.reverse }.toL B)
      (4 * A.length + 1) := by
    have h := loop_cntMv_runs 12 6 18 (by decide) (by decide) (by decide) [] A.reverse
      ({ c₁.clr with fuel := [1], s18 := [0] }.toL B) 0 (by rw [loop_get_sta, List.reverse_reverse]; rfl) rfl
    simp only [loop_set_sta, loop_set_w, loop_set_s18, loop_get_w, List.nil_append, Nat.zero_add,
      List.length_reverse] at h
    exact h
  have x₅ : NRuns (nmv 18 6 (by decide))
      ({ c₁.clr with fuel := [1], s18 := [A.length], sta := [], w := W₀ ++ A.reverse }.toL B)
      ({ c₁.clr with fuel := [1], sta := [], w := W₀ ++ A.reverse ++ [A.length] }.toL B) 2 := by
    have h := nruns_mv 18 6 (by decide)
      ({ c₁.clr with fuel := [1], s18 := [A.length], sta := [], w := W₀ ++ A.reverse }.toL B) (l := [])
      (v := A.length) rfl
    simp only [loop_set_s18, loop_set_w, loop_get_w] at h; exact h
  have x₆ : NRuns (.prim (.pushZ 18)) ({ c₁.clr with fuel := [1], sta := [], w := W₀ ++ A.reverse ++ [A.length] }.toL B)
      ({ c₁.clr with fuel := [1], sta := [], w := W₀ ++ A.reverse ++ [A.length], s18 := [0] }.toL B) 1 := by
    have h := nruns_pushZ 18 ({ c₁.clr with fuel := [1], sta := [], w := W₀ ++ A.reverse ++ [A.length] }.toL B)
    simp only [loop_set_s18, loop_get_s18] at h; exact h
  let c₂ : Cf := { c₁ with fuel := [1], sta := [], w := W₀ ++ A.reverse ++ [A.length] }
  have x₇ : NRuns (loop_cntMvP 37 19 18 (by decide)) ({ c₂.clr with s18 := [0] }.toL B)
      ({ c₂.clr with s18 := [st.tt.length + 1], valt := [], s19 := c.valt.reverse }.toL B)
      (4 * (st.tt.length + 1) + 1) := by
    have h := loop_cntMv_runs 37 19 18 (by decide) (by decide) (by decide) [] c.valt.reverse
      ({ c₂.clr with s18 := [0] }.toL B) 0 (by simp [c₂, c₁, Cf.clr]) rfl
    simp only [loop_set_valt, loop_set_s19, loop_set_s18, loop_get_s19, List.nil_append, Nat.zero_add,
      List.length_reverse, hVl] at h
    exact h
  have x₈ : NRuns (nmvAll 19 37 (by decide))
      ({ c₂.clr with s18 := [st.tt.length + 1], valt := [], s19 := c.valt.reverse }.toL B)
      ({ c₂.clr with s18 := [st.tt.length + 1] }.toL B) (3 * (st.tt.length + 1) + 1) := by
    have h := nruns_mvAll 19 37 (by decide)
      ({ c₂.clr with s18 := [st.tt.length + 1], valt := [], s19 := c.valt.reverse }.toL B)
    simp only [loop_set_valt, loop_set_s19, loop_get_s19, loop_get_valt, List.nil_append, List.reverse_reverse,
      List.length_reverse, hVl] at h
    exact h
  have x₉ : NRuns (nmvAll 9 20 (by decide)) ({ c₂.clr with s18 := [st.tt.length + 1] }.toL B)
      ({ c₂.clr with s18 := [st.tt.length + 1], s20 := rt.reverse, rts := [], rv := [], rvl := [], fuel := [1] }.toL B)
      (3 * rt.length + 1) := by
    have h := nruns_mvAll 9 20 (by decide) ({ c₂.clr with s18 := [st.tt.length + 1] }.toL B)
    simp only [loop_set_rts, loop_set_s20, loop_get_s20, loop_get_rts] at h
    exact h
  have x₁₀ := loop_rules_runs B c₂ j cap st hvalt rt [] [] [] 1
  simp only [List.nil_append] at x₁₀
  have x₁₁ : NRuns (.prim (.pop 18))
      ({ c₂.clr with
          s18 := [st.tt.length + 1], s20 := [], rts := rt,
          rv := (rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := loop_vals j cap st rt, fuel := [1 + (loop_vals j cap st rt).sum] }.toL B)
      ({ c.clr with
          fuel := [1 + (loop_vals j cap st rt).sum], sta := [], w := W₀ ++ A.reverse ++ [A.length], rts := rt,
          rv := (rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := loop_vals j cap st rt }.toL B) 1 := by
    have h := nruns_pop 18
      ({ c₂.clr with
          s18 := [st.tt.length + 1], s20 := [], rts := rt,
          rv := (rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)).flatten,
          rvl := loop_vals j cap st rt, fuel := [1 + (loop_vals j cap st rt).sum] }.toL B) (l := [])
      (v := st.tt.length + 1) rfl
    simp only [loop_set_s18] at h
    exact h
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq (x₉.seq (x₁₀.seq x₁₁)))))))))).mono
    (by omega)

end Rule

/-! ## The start items and the answer -/

/-- Run the start items (on `6`, their number of numbers on `STA`). -/
def loop_startP (p : NProg NK) : NProg NK :=
  .loop 12 .pos (.seq (.prim (.dec 12)) (.seq (.prim (.dec 12)) (.seq (.prim (.dec 12)) (.seq (.prim (.dec 12))
    (loop_itemP p 6 10 (by decide) (by decide))))))

theorem loop_encItems_length (l : List MItem) : (encItems l).length = 4 * l.length := by
  induction l with
  | nil => simp [encItems]
  | cons it l ih => rw [loop_flatten_cons, List.length_append, ih, loop_encItem_length]; simp; omega

section Start
variable {p : NProg NK} {B : Lists NK} {j cap : Nat} {st : PSt} {Tf : List (List Nat)}
  (hE : EvalEnv B j cap st [])

include hE in
theorem loop_start_runs (W₀ : List Nat) : ∀ (l : List MItem) (vs : List (List Nat)) (c : Cf),
    (∀ it ∈ l, ItemRunsC p j cap st Tf it 100) →
    c.rts = st.rt → c.valt = valTable j cap st.x.length st.tt → c.rv = Tf.flatten →
    c.rvl = Tf.map List.length → c.Clean → c.it = [] → c.w = W₀ ++ (encItems l).reverse →
    c.sta = [4 * l.length] → c.ev = evFlat vs → c.evl = evLens vs →
    NRuns (loop_startP p) (c.toL B)
      ({ c with
          w := W₀, sta := [0], bod := c.bod ++ encItems l, ev := evFlat (loop_run j cap st Tf l vs),
          evl := evLens (loop_run j cap st Tf l vs) }.toL B)
      (runCost j cap st Tf l vs + 1)
  | [], vs, c, _, _, _, _, _, _, _, hw, hsta, hev, hevl => by
    have e : { c with
        w := W₀, sta := [0], bod := c.bod ++ encItems [], ev := evFlat (loop_run j cap st Tf [] vs),
        evl := evLens (loop_run j cap st Tf [] vs) } = c := by
      cases c; simp only [encItems, List.flatMap_nil, List.reverse_nil, List.append_nil, List.length_nil,
        Nat.mul_zero] at hw hsta hev hevl ⊢
      subst hw hsta hev hevl; rfl
    rw [e]
    exact nruns_loop_exit (by rw [loop_get_sta, hsta]; rfl)
  | it :: l, vs, c, hpl, hrts, hvalt, hrv, hrvl, hcl, hit, hw, hsta, hev, hevl => by
    have hs : c.sta = [4 * l.length + 3 + 1] := by rw [hsta]; simp; omega
    have d₁ : NRuns (.prim (.dec 12)) (c.toL B) ({ c with sta := [4 * l.length + 3] }.toL B) 1 := by
      have h := nruns_dec 12 (c.toL B) (l := []) (v := 4 * l.length + 3 + 1) (by rw [loop_get_sta, hs]; rfl)
      simp only [loop_set_sta, Nat.add_sub_cancel, List.nil_append] at h; exact h
    have d₂ : NRuns (.prim (.dec 12)) ({ c with sta := [4 * l.length + 3] }.toL B)
        ({ c with sta := [4 * l.length + 2] }.toL B) 1 := by
      have h := nruns_dec 12 ({ c with sta := [4 * l.length + 3] }.toL B) (l := []) (v := 4 * l.length + 2 + 1) rfl
      simp only [loop_set_sta, Nat.add_sub_cancel, List.nil_append] at h; exact h
    have d₃ : NRuns (.prim (.dec 12)) ({ c with sta := [4 * l.length + 2] }.toL B)
        ({ c with sta := [4 * l.length + 1] }.toL B) 1 := by
      have h := nruns_dec 12 ({ c with sta := [4 * l.length + 2] }.toL B) (l := []) (v := 4 * l.length + 1 + 1) rfl
      simp only [loop_set_sta, Nat.add_sub_cancel, List.nil_append] at h; exact h
    have d₄ : NRuns (.prim (.dec 12)) ({ c with sta := [4 * l.length + 1] }.toL B)
        ({ c with sta := [4 * l.length] }.toL B) 1 := by
      have h := nruns_dec 12 ({ c with sta := [4 * l.length + 1] }.toL B) (l := []) (v := 4 * l.length + 1) rfl
      simp only [loop_set_sta, Nat.add_sub_cancel, List.nil_append] at h; exact h
    have hw' : ({ c with sta := [4 * l.length] }).w = (W₀ ++ (encItems l).reverse) ++ (encItem it).reverse := by
      show c.w = _
      rw [hw, loop_flatten_cons, List.reverse_append, List.append_assoc]
    have x := loop_itemS_runs (hpl it List.mem_cons_self) hE { c with sta := [4 * l.length] }
      (W₀ ++ (encItems l).reverse) vs hrts hvalt hrv hrvl hcl hit hev hevl hw'
    have ih := loop_start_runs W₀ l (loop_stp j cap st Tf it vs)
      { c with
        sta := [4 * l.length], w := W₀ ++ (encItems l).reverse, bod := c.bod ++ encItem it,
        ev := evFlat (loop_stp j cap st Tf it vs), evl := evLens (loop_stp j cap st Tf it vs) }
      (fun i hi => hpl i (List.mem_cons_of_mem _ hi)) hrts hvalt hrv hrvl hcl hit rfl rfl rfl rfl
    have e : { { c with
          sta := [4 * l.length], w := W₀ ++ (encItems l).reverse, bod := c.bod ++ encItem it,
          ev := evFlat (loop_stp j cap st Tf it vs), evl := evLens (loop_stp j cap st Tf it vs) } with
          w := W₀, sta := [0], bod := c.bod ++ encItem it ++ encItems l,
          ev := evFlat (loop_run j cap st Tf l (loop_stp j cap st Tf it vs)),
          evl := evLens (loop_run j cap st Tf l (loop_stp j cap st Tf it vs)) } =
        { c with
          w := W₀, sta := [0], bod := c.bod ++ encItems (it :: l),
          ev := evFlat (loop_run j cap st Tf (it :: l) vs), evl := evLens (loop_run j cap st Tf (it :: l) vs) } := by
      simp only [loop_flatten_cons, List.append_assoc]; rfl
    rw [e] at ih
    refine (loop_unroll (by rw [loop_get_sta, hs]; exact eval_pos_succ [] _)
      (d₁.seq (d₂.seq (d₃.seq (d₄.seq x)))) ih).mono ?_
    simp only [runCost, loop_stp]
    omega

end Start

/-- Pick the answer: `true` iff the top of `EV` is `2`. -/
def loop_pickP : NProg NK := caseTop 3 [.halt false, .halt false, .halt true] (.halt false)

/-- The entry at the end of the input (index `NX`) of the top vector, if there is one. -/
def loop_ansNE : NProg NK :=
  .seq (.prim (.dup 1 25 (by decide))) (.seq (.prim (.dup 4 26 (by decide))) (.seq (loop_minP false)
    (.seq (.prim (.pop 25)) (.ite 26 .pos (.seq (.prim (.dec 26)) (.seq (moveN 26 3 20 (by decide)) loop_pickP))
      (.halt false)))))

def loop_ansP : NProg NK := .ite 4 .nonempty loop_ansNE (.halt false)

theorem loop_pick_halts (S : Lists NK) (l : List Nat) (v : Nat) (h : S 3 = l ++ [v]) :
    ∃ S', NHalts loop_pickP S (v == 2) S' 9 := by
  rcases v with _ | _ | _ | w
  · exact ⟨_, (caseTop_halts 3 _ _ 0 (by simp) S l h false _ 1 (nhalts_halt false _)).mono (by omega)⟩
  · exact ⟨_, (caseTop_halts 3 _ _ 1 (by simp) S l h false _ 1 (nhalts_halt false _)).mono (by omega)⟩
  · exact ⟨_, (caseTop_halts 3 _ _ 2 (by simp) S l h true _ 1 (nhalts_halt true _)).mono (by omega)⟩
  · have h' : S 3 = l ++ [w + [NProg.halt (K := NK) false, .halt false, .halt true].length] := by
      rw [h]; simp
    have hb : (w + 1 + 1 + 1 == 2) = false := by simp
    rw [hb]
    exact ⟨_, (caseTop_default 3 _ _ w S l h' false _ 1 (nhalts_halt false _)).mono (by simp)⟩

theorem loop_ans_halts (B : Lists NK) (c : Cf) (n : Nat) (hNX : B 1 = [n]) (vs : List (List Nat))
    (hev : c.ev = evFlat vs) (hevl : c.evl = evLens vs) (hcl : c.Clean) :
    ∃ S', NHalts loop_ansP (c.toL B) (((vs.headD []).getD n 0) == 2) S' (9 * (evFlat vs).length + 40) := by
  obtain ⟨_, _, h20, _, _, _, _, h25, h26⟩ := hcl
  cases vs with
  | nil =>
    have hb : ((([] : List (List Nat)).headD []).getD n 0 == 2) = false := by simp
    rw [hb]
    exact ⟨_, ((nhalts_halt false _).iteF (by rw [loop_get_evl, hevl]; rfl)).mono (by omega)⟩
  | cons v vs =>
    have x₁ : NRuns (.prim (.dup 1 25 (by decide))) (c.toL B) ({ c with s25 := [n] }.toL B) 1 := by
      have h := nruns_dup 1 25 (by decide) (c.toL B) (l := []) (v := n) (by rw [loop_get_base1, hNX]; rfl)
      have r : (c.toL B) 25 = [] := h25
      rw [r] at h; simp only [loop_set_s25, List.nil_append] at h; exact h
    have x₂ : NRuns (.prim (.dup 4 26 (by decide))) ({ c with s25 := [n] }.toL B)
        ({ c with s25 := [n], s26 := [v.length] }.toL B) 1 := by
      have h := nruns_dup 4 26 (by decide) ({ c with s25 := [n] }.toL B) (l := evLens vs) (v := v.length)
        (by rw [loop_get_evl]; simp [hevl, evLens_cons])
      have r : ({ c with s25 := [n] }.toL B) 26 = [] := h26
      rw [r] at h; simp only [loop_set_s26, List.nil_append] at h; exact h
    have x₃ : NRuns (loop_minP false) ({ c with s25 := [n], s26 := [v.length] }.toL B)
        ({ c with s25 := [0], s26 := [loop_minRes false n v.length] }.toL B) (5 * v.length + 6) := by
      have h := loop_minP_runs false v.length n ({ c with s25 := [n], s26 := [v.length] }.toL B) rfl rfl
      simp only [loop_set_s25, loop_set_s26] at h; exact h
    have x₄ : NRuns (.prim (.pop 25)) ({ c with s25 := [0], s26 := [loop_minRes false n v.length] }.toL B)
        ({ c with s25 := [], s26 := [loop_minRes false n v.length] }.toL B) 1 := by
      have h := nruns_pop 25 ({ c with s25 := [0], s26 := [loop_minRes false n v.length] }.toL B) (l := [])
        (v := 0) rfl
      simp only [loop_set_s25] at h; exact h
    have hEV : c.ev = evFlat vs ++ v := by rw [hev, evFlat_cons]
    by_cases hn : n < v.length
    · have hr : loop_minRes false n v.length = (v.length - n - 1) + 1 := by
        simp only [loop_minRes]; split <;> omega
      have y₁ : NRuns (.prim (.dec 26)) ({ c with s25 := [], s26 := [loop_minRes false n v.length] }.toL B)
          ({ c with s25 := [], s26 := [v.length - n - 1] }.toL B) 1 := by
        have h := nruns_dec 26 ({ c with s25 := [], s26 := [loop_minRes false n v.length] }.toL B) (l := [])
          (v := v.length - n - 1 + 1) (by rw [loop_get_s26, hr]; rfl)
        simp only [loop_set_s26, Nat.add_sub_cancel, List.nil_append] at h; exact h
      have hsplit : c.ev = (evFlat vs ++ v.take (n + 1)) ++ v.drop (n + 1) := by
        rw [hEV, List.append_assoc, List.take_append_drop]
      have y₂ := nruns_moveN 26 3 20 (by decide) (by decide) (by decide)
        ({ c with s25 := [], s26 := [v.length - n - 1] }.toL B) (lc := []) (n := v.length - n - 1) rfl
        (l := evFlat vs ++ v.take (n + 1)) (seg := v.drop (n + 1)) (by rw [loop_get_ev]; exact hsplit)
        (by simp; omega)
      have htop : (((({ c with s25 := [], s26 := [v.length - n - 1] }.toL B).set 26 []).set 3
          (evFlat vs ++ v.take (n + 1))).set 20
          (({ c with s25 := [], s26 := [v.length - n - 1] }.toL B) 20 ++ (v.drop (n + 1)).reverse)) 3 =
          (evFlat vs ++ v.take n) ++ [v[n]] := by
        rw [Lists.set_ne _ _ (by decide), Lists.set_same, List.take_succ_eq_append_getElem hn, List.append_assoc]
      obtain ⟨S', hS'⟩ := loop_pick_halts _ _ _ htop
      have hans : (((v :: vs).headD []).getD n 0 == 2) = (v[n] == 2) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      rw [hans]
      refine ⟨S', ((x₁.seqH (x₂.seqH (x₃.seqH (x₄.seqH ((y₁.seqH (y₂.seqH hS')).iteT ?_))))).iteT ?_).mono ?_⟩
      · rw [loop_get_s26, hr]; exact eval_pos_succ [] _
      · rw [loop_get_evl, hevl, evLens_cons]; simp
      · simp only [evFlat_cons, List.length_append]; omega
    · have hr : loop_minRes false n v.length = 0 := by
        simp only [loop_minRes, Bool.false_eq_true, if_false]; split <;> omega
      have hans : (((v :: vs).headD []).getD n 0 == 2) = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hn)]
      rw [hans]
      refine ⟨_, ((x₁.seqH (x₂.seqH (x₃.seqH (x₄.seqH ((nhalts_halt false _).iteF ?_))))).iteT ?_).mono ?_⟩
      · rw [loop_get_s26, hr]; rfl
      · rw [loop_get_evl, hevl, evLens_cons]; simp
      · simp only [evFlat_cons, List.length_append]; omega

/-! ## The whole evaluation -/

/-- The record of the stacks of `S`. -/
def Cf.ofL (S : Lists NK) : Cf :=
  ⟨S 3, S 4, S 5, S 6, S 9, S 10, S 11, S 12, S 14, S 15, S 16, S 17, S 18, S 19, S 20, S 21, S 22, S 23, S 24, S 25,
    S 26, S 37⟩

theorem loop_ofL (S : Lists NK) : (Cf.ofL S).toL S = S := by
  funext ⟨n, hn⟩
  match n, hn with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | 16, _ => rfl
  | 17, _ => rfl
  | 18, _ => rfl
  | 19, _ => rfl
  | 20, _ => rfl
  | 21, _ => rfl
  | 22, _ => rfl
  | 23, _ => rfl
  | 24, _ => rfl
  | 25, _ => rfl
  | 26, _ => rfl
  | 27, _ => rfl
  | 28, _ => rfl
  | 29, _ => rfl
  | 30, _ => rfl
  | 31, _ => rfl
  | 32, _ => rfl
  | 33, _ => rfl
  | 34, _ => rfl
  | 35, _ => rfl
  | 36, _ => rfl
  | 37, _ => rfl
  | 38, _ => rfl
  | 39, _ => rfl
  | n + 40, h => exact absurd h (by unfold NK; omega)

/-- The evaluation stage: prepare, run the rounds, run the start items, answer. -/
def evalP (p : NProg NK) : NProg NK :=
  .seq loop_initP (.seq (loop_fixP p) (.seq (nmv 6 12 (by decide)) (.seq (loop_startP p) loop_ansP)))

theorem loop_sum_rules (f : Nat → Nat) (a b : Nat) : ∀ (l : List Nat),
    (l.map (fun t => a + 6 * f t + b)).sum = l.length * (a + b) + 6 * (l.map f).sum
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [loop_sum_rules f a b l, Nat.add_mul]
    omega

/-- The steps outside the rounds and the start items fit in `1000 Z²`. -/
theorem loop_cost_fit (Z a r t s e : Nat) (hZ : 2 ≤ Z) (ha : a ≤ Z) (hr : r ≤ Z) (ht : t ≤ Z) (hs : s ≤ Z)
    (he : e ≤ Z) :
    2 * 1 + 4 * a + 7 * t + 3 * r + (r * (20 * t + 61) + 6 * s) + 30 + 2 + 1 + (9 * e + 40) ≤ 1000 * Z * Z := by
  have h₁ : r * (20 * t + 61) ≤ Z * (81 * Z) := Nat.mul_le_mul hr (by omega)
  have h₂ : Z * (81 * Z) = 81 * (Z * Z) := by rw [Nat.mul_left_comm]
  have h₃ : Z ≤ Z * Z := Nat.le_mul_self Z
  have h₄ : 4 ≤ Z * Z := Nat.mul_le_mul hZ hZ
  have h₅ : 1000 * Z * Z = 1000 * (Z * Z) := Nat.mul_assoc _ _ _
  omega

/-- **The evaluation stage on stacks.** From the tables of the reading (`EvalEnv` with no rule values yet), the
bodies on `BOD`, the start on `STA` and empty evaluation stacks, `evalP p` answers whether the code at the end of the
input is `2`, within `evalCost`. -/
theorem evalP_runs (p : NProg NK) (j cap : Nat) (st : PSt)
    (hp : ∀ (Tf : List (List Nat)) (it : MItem), it ∈ st.bodies.flatten ++ st.start → ItemRunsC p j cap st Tf it 100)
    (hTag : ∀ it ∈ st.bodies.flatten, it.tag < 13)
    (S : Lists NK) (hE : EvalEnv S j cap st []) (hB : S BOD = encBodies st.bodies) (hA : S STA = encItems st.start)
    (hNB : S NB = [st.bodies.length])
    (hEV : S EV = []) (hEVL : S EVL = []) (hIT : S IT = []) (hR2 : S RV2 = []) (hL2 : S RVL2 = []) :
    ∃ S', NHalts (evalP p) S
      (startCodeT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.rt st.bodies st.start == 2) S' (evalCost j cap st) := by
  let c := Cf.ofL S
  have hsc : ∀ k : Fin NK, 18 ≤ k.val → k.val ≤ 33 → S k = [] := hE.scratch
  have h5 : S 5 = [] := by have := hE.rv; simpa using this
  have h15 : S 15 = [] := by have := hE.rvl; simpa using this
  have hS₀ : S = ({ c.clr with
      fuel := [st.bodies.length], sta := encItems st.start, w := S 6, rts := st.rt, rv := [], rvl := [] }).toL S := by
    conv => lhs; rw [← loop_ofL S]
    congr 1
    simp only [c, Cf.ofL, Cf.clr, h5, h15, hE.rt, hNB, hA, hsc 18 (by decide) (by decide), hsc 19 (by decide) (by decide),
      hsc 20 (by decide) (by decide), hsc 21 (by decide) (by decide), hsc 22 (by decide) (by decide),
      hsc 23 (by decide) (by decide), hsc 24 (by decide) (by decide), hsc 25 (by decide) (by decide),
      hsc 26 (by decide) (by decide)]
  have hvalt : c.valt = valTable j cap st.x.length st.tt := hE.valt
  -- preparing
  let A := encItems st.start
  let V := loop_vals j cap st st.rt
  let Tf₀ := st.rt.map (fun t => List.replicate (valT j cap st.x.length st.tt t) 0)
  let c' : Cf := { c.clr with sta := [], w := S 6 ++ A.reverse ++ [A.length], rts := st.rt }
  have x₁ : NRuns loop_initP S ({ c' with rv := Tf₀.flatten, rvl := Tf₀.map List.length, fuel := [V.sum + 1] }.toL S)
      (2 * [st.bodies.length].length + 4 * A.length + 7 * st.tt.length + 3 * st.rt.length +
        (st.rt.map (fun t => 20 * st.tt.length + 6 * valT j cap st.x.length st.tt t + 61)).sum + 30) := by
    have h := loop_init_runs S c j cap st hvalt [st.bodies.length] A (S 6) st.rt
    rw [← hS₀] at h
    have e : Tf₀.map List.length = V := by simp [Tf₀, V, loop_vals, List.map_map, Function.comp_def]
    rw [e, Nat.add_comm V.sum 1]
    exact h
  -- the rounds
  let fuel₀ := V.sum + 1
  let Tfin := fixT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies fuel₀ Tf₀
  have x₂ := loop_fixP_runs (p := p) hE hp hTag c' rfl hvalt (Cf.clr_clean c) hIT hEV hEVL rfl hB hR2 hL2 fuel₀ Tf₀
  -- the start items
  let c₃ : Cf := { c' with rv := Tfin.flatten, rvl := Tfin.map List.length, fuel := [0] }
  let c₄ : Cf := { c₃ with sta := [A.length], w := S 6 ++ A.reverse }
  have x₃ : NRuns (nmv 6 12 (by decide)) (c₃.toL S) (c₄.toL S) 2 := by
    have h := nruns_mv 6 12 (by decide) (c₃.toL S) (l := S 6 ++ A.reverse) (v := A.length) rfl
    simp only [loop_set_sta, loop_get_sta, loop_set_w] at h
    exact h
  have x₄ := loop_start_runs (p := p) (Tf := Tfin) hE (S 6) st.start [] c₄
    (fun it h => hp Tfin it (List.mem_append_right _ h)) rfl hvalt rfl rfl (Cf.clr_clean c) hIT rfl
    (by show [A.length] = _; rw [loop_encItems_length]) hEV hEVL
  let Rs := loop_run j cap st Tfin st.start []
  obtain ⟨S', hans⟩ := loop_ans_halts S
    { c₄ with
      w := S 6, sta := [0], bod := c₄.bod ++ encItems st.start, ev := evFlat Rs, evl := evLens Rs }
    st.x.length hE.nx Rs rfl rfl (Cf.clr_clean c)
  have hcode : startCodeT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.rt st.bodies st.start =
      (Rs.headD []).getD st.x.length 0 := by
    simp only [startCodeT, List.length_map]; rfl
  refine ⟨S', ?_⟩
  rw [hcode]
  refine (x₁.seqH (x₂.seqH (x₃.seqH (x₄.seqH hans)))).mono ?_
  have hsum := loop_sum_rules (valT j cap st.x.length st.tt) (20 * st.tt.length) 61 st.rt
  have hfit := loop_cost_fit
    ((V.sum + 1) + st.rt.length + Tf₀.flatten.length + (valTable j cap st.x.length st.tt).sum + A.length +
      (evFlat Rs).length + st.x.length + st.tt.length + 2)
    A.length st.rt.length st.tt.length V.sum (evFlat Rs).length (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  simp only [evalCost, List.length_map]
  simp only [List.length_cons, List.length_nil] at hfit ⊢
  simp only [V, loop_vals, fuel₀, Tfin, Tf₀, Rs, loop_run, A] at hsum hfit ⊢
  omega

end Shallot.MacroPeg.Mach
