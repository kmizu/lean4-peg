import Complexity.NTable
import MacroPeg.HigherOrder.Tower

/-!
# Unary arithmetic for the front of the diagonal machine

Programs on stacks of numbers, each with its exact final state and a step bound:
* `mulAcc a b t r`: pop the top `x` of `a` and add `x * y` to the top of `r` (`y` the top of `b`, kept);
* `exp2P v a t`: replace the top `x` of `v` by `2 ^ x`;
* `towerP v a t j`: replace the top `x` of `v` by `tower j x`;
* `zerosP t d`: pop the top `x` of `t` and push `x` zeros on `d`;
* `takeP s d`: move the top of `s` to `d`, halting with `false` when `s` is empty (`takesP`: several in a row).

Loops whose body costs change from one round to the next use `nruns_family_var`.
-/

namespace Shallot.MacroPeg.KExp

open Complexity
open Shallot.MacroPeg.HO

variable {K : Nat}

/-! ## Loops with varying body costs -/

/-- `Σ_{i<r} (T i + 1)`. -/
def lsum (T : Nat → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => T 0 + 1 + lsum (fun i => T (i + 1)) r

theorem nruns_family_var {i : Fin K} {c : NTest} {p : NProg K} (F : Nat → Lists K) (n : Nat) (T : Nat → Nat)
    (htest : ∀ m, m < n → c.eval (F m i) = true) (hstop : c.eval (F n i) = false)
    (hbody : ∀ m, m < n → NRuns p (F m) (F (m + 1)) (T m)) :
    ∀ r m, m + r = n → NRuns (.loop i c p) (F m) (F n) (lsum (fun x => T (m + x)) r + 1)
  | 0, m, h => by
    obtain rfl : m = n := by omega
    exact ⟨1, by simp [lsum], .loopF trivial hstop⟩
  | r + 1, m, h => by
    obtain ⟨t₁, ht₁, x₁⟩ := hbody m (by omega)
    obtain ⟨t₂, ht₂, x₂⟩ := nruns_family_var F n T htest hstop hbody r (m + 1) (by omega)
    refine ⟨t₁ + 1 + t₂, ?_, .loopC trivial (htest m (by omega)) x₁ x₂⟩
    have e : (fun x => T (m + 1 + x)) = (fun x => T (m + (x + 1))) := funext fun x => by
      rw [show m + 1 + x = m + (x + 1) by omega]
    rw [e] at ht₂
    simp only [lsum, Nat.add_zero]
    omega

theorem lsum_doubling : ∀ (r m : Nat), lsum (fun x => 3 * 2 ^ (m + x) + 4) r + 3 * 2 ^ m ≤ 3 * 2 ^ (m + r) + 5 * r
  | 0, m => by simp [lsum]
  | r + 1, m => by
    have ih := lsum_doubling r (m + 1)
    have e : (fun x => 3 * 2 ^ (m + 1 + x) + 4) = (fun x => 3 * 2 ^ (m + (x + 1)) + 4) := funext fun x => by
      rw [show m + 1 + x = m + (x + 1) by omega]
    rw [e] at ih
    have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have h2 : m + 1 + r = m + (r + 1) := by omega
    rw [h2] at ih
    simp only [lsum, Nat.add_zero]
    omega

/-! ## Multiplying -/

/-- Pop the top `x` of `a` and add `x * y` to the top of `r`, `y` the top of `b` (`t` is scratch). -/
def mulAcc (a b t r : Fin K) (hbt : b ≠ t) : NProg K :=
  .seq (.loop a .pos (.seq (.prim (.dec a)) (.seq (.prim (.dup b t hbt)) (addTo t r)))) (.prim (.pop a))

theorem nruns_mulAcc (a b t r : Fin K) (hbt : b ≠ t) (hab : a ≠ b) (hat : a ≠ t) (har : a ≠ r) (hbr : b ≠ r)
    (htr : t ≠ r) (S : Lists K) {la lb lr : List Nat} {x y z : Nat} (ha : S a = la ++ [x]) (hb : S b = lb ++ [y])
    (hr : S r = lr ++ [z]) :
    NRuns (mulAcc a b t r hbt) S ((S.set a la).set r (lr ++ [z + x * y])) (x * (3 * y + 5) + 2) := by
  let F : Nat → Lists K := fun m => (S.set a (la ++ [x - m])).set r (lr ++ [z + m * y])
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, Nat.zero_mul, Nat.add_zero, ← ha, ← hr, Lists.set_get_self]
  have hFa : ∀ m, F m a = la ++ [x - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ har, Lists.set_same]
  have hFr : ∀ m, F m r = lr ++ [z + m * y] := fun m => by simp only [F, Lists.set_same]
  have hFb : ∀ m, F m b = lb ++ [y] := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hbr, Lists.set_ne _ _ (Ne.symm hab), hb]
  have hFt : ∀ m, F m t = S t := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ htr, Lists.set_ne _ _ (Ne.symm hat)]
  have hl := nruns_family_const (i := a) (c := .pos)
    (p := .seq (.prim (.dec a)) (.seq (.prim (.dup b t hbt)) (addTo t r))) F x (3 * y + 4)
    (fun m hm => by rw [hFa, show x - m = (x - m - 1) + 1 by omega]; simp)
    (by rw [hFa, Nat.sub_self]; simp)
    (fun m hm => by
      have d₁ := nruns_dec a (F m) (hFa m)
      let G := (F m).set a (la ++ [x - m - 1])
      have hGb : G b = lb ++ [y] := by simp only [G]; rw [Lists.set_ne _ _ (Ne.symm hab), hFb]
      have d₂ := nruns_dup b t hbt G hGb
      let H := G.set t (G t ++ [y])
      have hHt : H t = G t ++ [y] := by simp only [H, Lists.set_same]
      have hHr : H r = lr ++ [z + m * y] := by
        simp only [H, G]; rw [Lists.set_ne _ _ (Ne.symm htr), Lists.set_ne _ _ (Ne.symm har), hFr]
      have d₃ := nruns_addTo t r htr H hHt hHr
      have e : (H.set t (G t)).set r (lr ++ [z + m * y + y]) = F (m + 1) := by
        have hGt : G t = S t := by simp only [G]; rw [Lists.set_ne _ _ (Ne.symm hat), hFt]
        rw [hGt]
        simp only [H, G, F]
        rw [show z + m * y + y = z + (m + 1) * y by rw [Nat.succ_mul]; omega, show x - m - 1 = x - (m + 1) by omega]
        funext q
        by_cases q1 : q = r
        · subst q1; simp [Lists.set]
        · by_cases q2 : q = t
          · subst q2; simp [Lists.set, q1, Ne.symm hat]
          · by_cases q3 : q = a
            · subst q3; simp [Lists.set, q1, q2]
            · simp [Lists.set, q1, q2, q3]
      rw [e] at d₃
      exact (d₁.seq (d₂.seq d₃)).mono (by omega))
  rw [h0] at hl
  have hp := nruns_pop a (F x) (l := la) (v := 0) (by rw [hFa, Nat.sub_self])
  have e : (F x).set a la = (S.set a la).set r (lr ++ [z + x * y]) := by
    simp only [F]
    funext q
    by_cases q1 : q = a
    · subst q1; simp [Lists.set, har]
    · simp [Lists.set, q1]
  rw [e] at hp
  refine (hl.seq hp).mono ?_
  rw [Nat.mul_add, Nat.mul_add] ; omega

/-! ## Powers of two -/

/-- Replace the top `x` of `v` by `2 ^ x` (`a`, `t` are scratch). -/
def exp2P (v a t : Fin K) (hva : v ≠ a) (hvt : v ≠ t) : NProg K :=
  .seq (nmv v a hva) (.seq (.prim (.pushZ v)) (.seq (.prim (.inc v))
    (.seq (.loop a .pos (.seq (.prim (.dec a)) (.seq (.prim (.dup v t hvt)) (addTo t v)))) (.prim (.pop a)))))

def exp2Cost (x : Nat) : Nat := 3 * 2 ^ x + 5 * x + 6

theorem nruns_exp2 (v a t : Fin K) (hva : v ≠ a) (hvt : v ≠ t) (hat : a ≠ t) (S : Lists K) {lv : List Nat}
    {x : Nat} (hv : S v = lv ++ [x]) :
    NRuns (exp2P v a t hva hvt) S (S.set v (lv ++ [2 ^ x])) (exp2Cost x) := by
  have d₁ := nruns_mv v a hva S hv
  let S₁ := (S.set a (S a ++ [x])).set v lv
  have d₂ := nruns_pushZ v S₁
  have hS₁v : S₁ v = lv := by simp only [S₁, Lists.set_same]
  rw [hS₁v] at d₂
  have d₃ := nruns_inc v (S₁.set v (lv ++ [0])) (l := lv) (v := 0) (by simp)
  let F : Nat → Lists K := fun m => (S₁.set v (lv ++ [2 ^ m])).set a (S a ++ [x - m])
  have h0 : F 0 = (S₁.set v (lv ++ [0])).set v (lv ++ [0 + 1]) := by
    simp only [F, Nat.pow_zero, Nat.sub_zero, S₁]
    funext q
    by_cases q1 : q = a
    · subst q1; simp [Lists.set, Ne.symm hva]
    · by_cases q2 : q = v
      · simp [Lists.set, q2, hva]
      · simp [Lists.set, q1, q2]
  have hFa : ∀ m, F m a = S a ++ [x - m] := fun m => by simp only [F, Lists.set_same]
  have hFv : ∀ m, F m v = lv ++ [2 ^ m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ hva, Lists.set_same]
  have hFt : ∀ m, F m t = S t := fun m => by
    simp only [F, S₁]; rw [Lists.set_ne _ _ (Ne.symm hat), Lists.set_ne _ _ (Ne.symm hvt),
      Lists.set_ne _ _ (Ne.symm hvt), Lists.set_ne _ _ (Ne.symm hat)]
  have hl := nruns_family_var (i := a) (c := .pos)
    (p := .seq (.prim (.dec a)) (.seq (.prim (.dup v t hvt)) (addTo t v))) F x (fun m => 3 * 2 ^ m + 4)
    (fun m hm => by rw [hFa, show x - m = (x - m - 1) + 1 by omega]; simp)
    (by rw [hFa, Nat.sub_self]; simp)
    (fun m hm => by
      have e₁ := nruns_dec a (F m) (hFa m)
      let G := (F m).set a (S a ++ [x - m - 1])
      have hGv : G v = lv ++ [2 ^ m] := by simp only [G]; rw [Lists.set_ne _ _ hva, hFv]
      have e₂ := nruns_dup v t hvt G hGv
      let H := G.set t (G t ++ [2 ^ m])
      have hHt : H t = G t ++ [2 ^ m] := by simp only [H, Lists.set_same]
      have hHv : H v = lv ++ [2 ^ m] := by simp only [H]; rw [Lists.set_ne _ _ hvt, hGv]
      have e₃ := nruns_addTo t v (Ne.symm hvt) H hHt hHv
      have e : (H.set t (G t)).set v (lv ++ [2 ^ m + 2 ^ m]) = F (m + 1) := by
        have hGt : G t = S t := by simp only [G]; rw [Lists.set_ne _ _ (Ne.symm hat), hFt]
        rw [hGt]
        simp only [H, G, F]
        rw [show 2 ^ m + 2 ^ m = 2 ^ (m + 1) by rw [Nat.pow_succ]; omega, show x - m - 1 = x - (m + 1) by omega]
        funext q
        by_cases q1 : q = v
        · subst q1; simp [Lists.set, hva]
        · by_cases q2 : q = t
          · simp [Lists.set, S₁, q2, Ne.symm hat, Ne.symm hvt]
          · by_cases q3 : q = a
            · subst q3; simp [Lists.set, q1, q2]
            · simp [Lists.set, q1, q2, q3]
      rw [e] at e₃
      exact (e₁.seq (e₂.seq e₃)).mono (by omega))
      x 0 (by omega)
  rw [h0] at hl
  have hp := nruns_pop a (F x) (l := S a) (v := 0) (by rw [hFa, Nat.sub_self])
  have e : (F x).set a (S a) = S.set v (lv ++ [2 ^ x]) := by
    simp only [F, S₁]
    funext q
    by_cases q1 : q = a
    · subst q1; simp [Lists.set, Ne.symm hva]
    · by_cases q2 : q = v
      · subst q2; simp [Lists.set, q1]
      · simp [Lists.set, q1, q2]
  rw [e] at hp
  refine (d₁.seq (d₂.seq (d₃.seq (hl.seq hp)))).mono ?_
  have hs := lsum_doubling x 0
  simp only [Nat.zero_add, Nat.pow_zero] at hs ⊢
  unfold exp2Cost
  omega

/-! ## Towers -/

def towerP (v a t : Fin K) (hva : v ≠ a) (hvt : v ≠ t) : Nat → NProg K
  | 0 => nskip a
  | j + 1 => .seq (towerP v a t hva hvt j) (exp2P v a t hva hvt)

def towerCost (x : Nat) : Nat → Nat
  | 0 => 2
  | j + 1 => towerCost x j + exp2Cost (tower j x)

theorem nruns_tower (v a t : Fin K) (hva : v ≠ a) (hvt : v ≠ t) (hat : a ≠ t) (S : Lists K) {lv : List Nat}
    {x : Nat} (hv : S v = lv ++ [x]) :
    ∀ j, NRuns (towerP v a t hva hvt j) S (S.set v (lv ++ [tower j x])) (towerCost x j)
  | 0 => by
    have := nruns_skip a S
    rw [tower_zero, ← hv, Lists.set_get_self]; exact this
  | j + 1 => by
    have h₁ := nruns_tower v a t hva hvt hat S hv j
    have h₂ := nruns_exp2 v a t hva hvt hat (S.set v (lv ++ [tower j x])) (lv := lv) (x := tower j x) (by simp)
    rw [Lists.set_set_u, ← tower_succ] at h₂
    exact h₁.seq h₂

theorem towerCost_le (x : Nat) : ∀ j, towerCost x j ≤ 2 + j * (8 * tower j x + 6)
  | 0 => by simp [towerCost]
  | j + 1 => by
    have ih := towerCost_le x j
    have hm : tower j x ≤ tower (j + 1) x := tower_le_succ j x
    have hm' : j * (8 * tower j x + 6) ≤ j * (8 * tower (j + 1) x + 6) := Nat.mul_le_mul_left _ (by omega)
    have key : (j + 1) * (8 * tower (j + 1) x + 6) = j * (8 * tower (j + 1) x + 6) + (8 * tower (j + 1) x + 6) :=
      Nat.succ_mul _ _
    simp only [towerCost, exp2Cost]
    rw [← tower_succ, key]
    omega

theorem le_tower_height : ∀ j x : Nat, j ≤ tower j x
  | 0, _ => Nat.zero_le _
  | j + 1, x => by
    have := le_tower_height j x
    rw [tower_succ]
    have := @Nat.lt_two_pow_self (tower j x)
    omega

theorem tower_mono_height {i j : Nat} (h : i ≤ j) (x : Nat) : tower i x ≤ tower j x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (tower_le_succ _ _)

/-! ## Zeros -/

/-- Pop the top `x` of `t` and push `x` zeros on `d`. -/
def zerosP (t d : Fin K) : NProg K :=
  .seq (.loop t .pos (.seq (.prim (.dec t)) (.prim (.pushZ d)))) (.prim (.pop t))

theorem nruns_zeros (t d : Fin K) (htd : t ≠ d) (S : Lists K) {lt : List Nat} {x : Nat} (ht : S t = lt ++ [x]) :
    NRuns (zerosP t d) S ((S.set t lt).set d (S d ++ List.replicate x 0)) (3 * x + 2) := by
  let F : Nat → Lists K := fun m => (S.set t (lt ++ [x - m])).set d (S d ++ List.replicate m 0)
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, List.replicate_zero, List.append_nil, ← ht, Lists.set_get_self]
  have hFt : ∀ m, F m t = lt ++ [x - m] := fun m => by simp only [F]; rw [Lists.set_ne _ _ htd, Lists.set_same]
  have hFd : ∀ m, F m d = S d ++ List.replicate m 0 := fun m => by simp only [F, Lists.set_same]
  have hl := nruns_family_const (i := t) (c := .pos) (p := .seq (.prim (.dec t)) (.prim (.pushZ d))) F x 2
    (fun m hm => by rw [hFt, show x - m = (x - m - 1) + 1 by omega]; simp)
    (by rw [hFt, Nat.sub_self]; simp)
    (fun m hm => by
      have d₁ := nruns_dec t (F m) (hFt m)
      have d₂ := nruns_pushZ d ((F m).set t (lt ++ [x - m - 1]))
      have e : ((F m).set t (lt ++ [x - m - 1])).set d (((F m).set t (lt ++ [x - m - 1])) d ++ [0]) = F (m + 1) := by
        rw [Lists.set_ne _ _ (Ne.symm htd), hFd]
        simp only [F]
        rw [show x - m - 1 = x - (m + 1) by omega, List.replicate_succ', List.append_assoc]
        funext q
        by_cases q1 : q = d
        · subst q1; simp [Lists.set]
        · by_cases q2 : q = t
          · subst q2; simp [Lists.set, q1]
          · simp [Lists.set, q1, q2]
      rw [e] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [h0] at hl
  have hp := nruns_pop t (F x) (l := lt) (v := 0) (by rw [hFt, Nat.sub_self])
  have e : (F x).set t lt = (S.set t lt).set d (S d ++ List.replicate x 0) := by
    simp only [F]
    funext q
    by_cases q1 : q = t
    · subst q1; simp [Lists.set, htd]
    · simp [Lists.set, q1]
  rw [e] at hp
  exact (hl.seq hp).mono (by omega)

/-! ## Taking the tops of a stack -/

/-- Move the top of `s` to `d`; halt with `false` when `s` is empty. -/
def takeP (s d : Fin K) (hsd : s ≠ d) : NProg K := .ite s .nonempty (nmv s d hsd) (.halt false)

theorem nruns_take (s d : Fin K) (hsd : s ≠ d) (S : Lists K) {l : List Nat} {v : Nat} (h : S s = l ++ [v]) :
    NRuns (takeP s d hsd) S ((S.set d (S d ++ [v])).set s l) 3 :=
  (nruns_mv s d hsd S h).iteT (by rw [h]; simp)

theorem nhalts_take (s d : Fin K) (hsd : s ≠ d) (S : Lists K) (h : S s = []) :
    NHalts (takeP s d hsd) S false S 2 :=
  (nhalts_halt false S).iteF (by rw [h]; rfl)

/-- Take the tops of `s` onto the stacks `ds`, in order, then run `q`. -/
def takesP (s : Fin K) : (ds : List (Fin K)) → (∀ d ∈ ds, s ≠ d) → NProg K → NProg K
  | [], _, q => q
  | d :: ds, h, q => .seq (takeP s d (h d (by simp))) (takesP s ds (fun d' h' => h d' (by simp [h'])) q)

/-- **Too few tops**: the takes halt with `false`. -/
theorem nhalts_takes (s : Fin K) (q : NProg K) :
    ∀ (ds : List (Fin K)) (h : ∀ d ∈ ds, s ≠ d) (S : Lists K), (S s).length < ds.length →
      ∃ S', NHalts (takesP s ds h q) S false S' (3 * ds.length)
  | [], _, _, hl => by simp at hl
  | d :: ds, h, S, hl => by
    rcases List.eq_nil_or_concat (S s) with h0 | ⟨l, v, hv⟩
    · exact ⟨S, ((nhalts_take s d (h d (by simp)) S h0).seq).mono (by simp; omega)⟩
    · rw [List.concat_eq_append] at hv
      have r := nruns_take s d (h d (by simp)) S hv
      obtain ⟨S', hS'⟩ := nhalts_takes s q ds (fun d' h' => h d' (by simp [h']))
        ((S.set d (S d ++ [v])).set s l) (by
          rw [Lists.set_same]; rw [hv] at hl; simp at hl ⊢; omega)
      exact ⟨S', (r.seqH hS').mono (by simp; omega)⟩

end Shallot.MacroPeg.KExp
