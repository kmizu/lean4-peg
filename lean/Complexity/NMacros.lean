import Complexity.NKit

/-!
# Basic programs on stacks of numbers

Clearing a stack (`nclr`), moving the top (`nmv`) or everything (`nmvAll`, reversing), pushing a constant (`npushC`).
Each comes with its exact final state and a step bound.
-/

namespace Complexity

variable {K : Nat}

/-! ## Tests on stacks -/

@[simp] theorem eval_nonempty_snoc (l : List Nat) (v : Nat) : NTest.nonempty.eval (l ++ [v]) = true := by
  simp [NTest.eval]
@[simp] theorem eval_nonempty_nil : NTest.nonempty.eval [] = false := rfl
@[simp] theorem eval_pos_succ (l : List Nat) (v : Nat) : NTest.pos.eval (l ++ [v + 1]) = true := by simp [NTest.eval]
@[simp] theorem eval_pos_zero (l : List Nat) : NTest.pos.eval (l ++ [0]) = false := by simp [NTest.eval]
@[simp] theorem eval_pos_nil : NTest.pos.eval [] = false := rfl
@[simp] theorem eval_zero_zero (l : List Nat) : NTest.zero.eval (l ++ [0]) = true := by simp [NTest.eval]
@[simp] theorem eval_zero_succ (l : List Nat) (v : Nat) : NTest.zero.eval (l ++ [v + 1]) = false := by
  simp [NTest.eval]
@[simp] theorem eval_zero_nil : NTest.zero.eval [] = false := rfl

theorem eval_nonempty_ne {l : List Nat} (h : l ≠ []) : NTest.nonempty.eval l = true := by
  simp [NTest.eval, h]

/-! ## Primitive steps as `NRuns` -/

theorem nruns_pushZ (i : Fin K) (S : Lists K) : NRuns (.prim (.pushZ i)) S (S.set i (S i ++ [0])) 1 := nruns_prim _ S
theorem nruns_inc (i : Fin K) (S : Lists K) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    NRuns (.prim (.inc i)) S (S.set i (l ++ [v + 1])) 1 := by
  have := nruns_prim (.inc i) S; simp only [NPrim.apply, h, mapTop_snoc] at this; exact this
theorem nruns_dec (i : Fin K) (S : Lists K) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    NRuns (.prim (.dec i)) S (S.set i (l ++ [v - 1])) 1 := by
  have := nruns_prim (.dec i) S; simp only [NPrim.apply, h, mapTop_snoc] at this; exact this
theorem nruns_pop (i : Fin K) (S : Lists K) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    NRuns (.prim (.pop i)) S (S.set i l) 1 := by
  have := nruns_prim (.pop i) S; simp only [NPrim.apply, h, List.dropLast_concat] at this; exact this
theorem nruns_dup (i j : Fin K) (hij : i ≠ j) (S : Lists K) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    NRuns (.prim (.dup i j hij)) S (S.set j (S j ++ [v])) 1 := by
  have := nruns_prim (.dup i j hij) S; simp only [NPrim.apply, h, List.getLast?_concat, Option.toList_some] at this
  exact this

/-! ## Clearing -/

def nclr (i : Fin K) : NProg K := .loop i .nonempty (.prim (.pop i))

theorem nruns_clr (i : Fin K) (S : Lists K) : NRuns (nclr i) S (S.set i []) (2 * (S i).length + 1) := by
  let n := (S i).length
  let F : Nat → Lists K := fun m => S.set i ((S i).take (n - m))
  have h0 : F 0 = S := by simp only [F, Nat.sub_zero, List.take_length, n]; exact Lists.set_get_self S i
  have hn : F n = S.set i [] := by simp [F]
  have := nruns_family_const (i := i) (c := .nonempty) (p := .prim (.pop i)) F n 1
    (fun m hm => by simp only [F, Lists.set_same]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by simp [F])
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
      have hl : (S i).take (r + 1) = (S i).take r ++ [(S i)[r]'(by simp [n] at hr; omega)] := by
        rw [List.take_succ_eq_append_getElem]
      have := nruns_pop i (F m) (l := (S i).take r) (v := (S i)[r]'(by simp [n] at hr; omega))
        (by simp only [F, Lists.set_same, hr, hl])
      have e : (F m).set i ((S i).take r) = F (m + 1) := by
        simp only [F, Lists.set_set_u]; congr 2; omega
      rwa [e] at this)
  rw [h0, hn] at this
  exact this.mono (by omega)

/-! ## Moving -/

def nmv (i j : Fin K) (hij : i ≠ j) : NProg K := .seq (.prim (.dup i j hij)) (.prim (.pop i))

theorem nruns_mv (i j : Fin K) (hij : i ≠ j) (S : Lists K) {l : List Nat} {v : Nat} (h : S i = l ++ [v]) :
    NRuns (nmv i j hij) S ((S.set j (S j ++ [v])).set i l) 2 := by
  have h₁ := nruns_dup i j hij S h
  have h₂ := nruns_pop i (S.set j (S j ++ [v])) (l := l) (v := v) (by rw [Lists.set_ne _ _ hij]; exact h)
  exact h₁.seq h₂

/-- Move everything from `i` onto `j` (the order is reversed). -/
def nmvAll (i j : Fin K) (hij : i ≠ j) : NProg K := .loop i .nonempty (nmv i j hij)

theorem nruns_mvAll (i j : Fin K) (hij : i ≠ j) (S : Lists K) :
    NRuns (nmvAll i j hij) S ((S.set j (S j ++ (S i).reverse)).set i []) (3 * (S i).length + 1) := by
  let n := (S i).length
  let F : Nat → Lists K := fun m =>
    (S.set j (S j ++ ((S i).drop (n - m)).reverse)).set i ((S i).take (n - m))
  have h0 : F 0 = S := by
    simp only [F, Nat.sub_zero, n, List.take_length, List.drop_length, List.reverse_nil, List.append_nil]
    rw [Lists.set_get_self, Lists.set_get_self]
  have hn : F n = (S.set j (S j ++ (S i).reverse)).set i [] := by simp [F]
  have := nruns_family_const (i := i) (c := .nonempty) (p := nmv i j hij) F n 2
    (fun m hm => by simp only [F, Lists.set_same]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by simp [F])
    (fun m hm => by
      obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
      have hrl : r < (S i).length := by simp [n] at hr; omega
      have hl : (S i).take (r + 1) = (S i).take r ++ [(S i)[r]] := List.take_succ_eq_append_getElem hrl
      have hFi : F m i = (S i).take r ++ [(S i)[r]] := by simp only [F, Lists.set_same, hr, hl]
      have := nruns_mv i j hij (F m) hFi
      have hd : (S i).drop r = (S i)[r] :: (S i).drop (r + 1) := List.drop_eq_getElem_cons hrl
      have e : ((F m).set j (F m j ++ [(S i)[r]])).set i ((S i).take r) = F (m + 1) := by
        have hm1 : n - (m + 1) = r := by omega
        funext x
        by_cases hxi : x = i
        · subst hxi; simp [F, hm1]
        · rw [Lists.set_ne _ _ hxi]
          by_cases hxj : x = j
          · subst hxj
            rw [Lists.set_same]
            simp only [F, hm1, hr]
            rw [Lists.set_ne _ _ hxi, Lists.set_same, Lists.set_ne _ _ hxi, Lists.set_same]
            simp only [List.append_assoc]
            congr 1
            rw [hd, List.reverse_cons]
          · rw [Lists.set_ne _ _ hxj]
            simp only [F]
            rw [Lists.set_ne _ _ hxi, Lists.set_ne _ _ hxj, Lists.set_ne _ _ hxi, Lists.set_ne _ _ hxj]
      rwa [e] at this)
  rw [h0, hn] at this
  exact this.mono (by omega)

/-! ## Constants -/

/-- Push the constant `c`. -/
def npushC (i : Fin K) : Nat → NProg K
  | 0 => .prim (.pushZ i)
  | c + 1 => .seq (npushC i c) (.prim (.inc i))

theorem nruns_pushC (i : Fin K) (S : Lists K) : ∀ c, NRuns (npushC i c) S (S.set i (S i ++ [c])) (c + 1)
  | 0 => nruns_pushZ i S
  | c + 1 => by
    have h₁ := nruns_pushC i S c
    have h₂ := nruns_inc i (S.set i (S i ++ [c])) (l := S i) (v := c) (by simp)
    rw [Lists.set_set_u] at h₂
    exact h₁.seq h₂

/-! ## Branching on the top -/

/-- Branch on the top of `i` (popped): `ps[v]` for top `v < ps.length`, else `q` (with the top lowered by
`ps.length`, still on the stack). -/
def caseTop (i : Fin K) : List (NProg K) → NProg K → NProg K
  | [], q => q
  | p :: ps, q => .ite i .zero (.seq (.prim (.pop i)) p) (.seq (.prim (.dec i)) (caseTop i ps q))

theorem caseTop_runs (i : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K) (v : Nat) (hv : v < ps.length)
    (S : Lists K) (l : List Nat), S i = l ++ [v] → ∀ (S' : Lists K) (T : Nat),
      NRuns ps[v] (S.set i l) S' T → NRuns (caseTop i ps q) S S' (T + 2 * v + 2)
  | [], _, v, hv, _, _, _, _, _, _ => by simp at hv
  | p :: ps, q, 0, _, S, l, hS, S', T, h => by
    have h₁ := nruns_pop i S hS
    exact ((h₁.seq h).iteT (by rw [hS]; simp)).mono (by omega)
  | p :: ps, q, v + 1, hv, S, l, hS, S', T, h => by
    have h₁ := nruns_dec i S hS
    have h₂ := caseTop_runs i ps q v (by simpa using hv) (S.set i (l ++ [v])) l (by simp) S' T
      (by rw [Lists.set_set_u]; exact h)
    simp only [Nat.add_sub_cancel] at h₁
    exact ((h₁.seq h₂).iteF (by rw [hS]; simp)).mono (by omega)

theorem caseTop_halts (i : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K) (v : Nat) (hv : v < ps.length)
    (S : Lists K) (l : List Nat), S i = l ++ [v] → ∀ (b : Bool) (S' : Lists K) (T : Nat),
      NHalts ps[v] (S.set i l) b S' T → NHalts (caseTop i ps q) S b S' (T + 2 * v + 2)
  | [], _, v, hv, _, _, _, _, _, _, _ => by simp at hv
  | p :: ps, q, 0, _, S, l, hS, b, S', T, h => by
    have h₁ := nruns_pop i S hS
    exact ((h₁.seqH h).iteT (by rw [hS]; simp)).mono (by omega)
  | p :: ps, q, v + 1, hv, S, l, hS, b, S', T, h => by
    have h₁ := nruns_dec i S hS
    have h₂ := caseTop_halts i ps q v (by simpa using hv) (S.set i (l ++ [v])) l (by simp) b S' T
      (by rw [Lists.set_set_u]; exact h)
    simp only [Nat.add_sub_cancel] at h₁
    exact ((h₁.seqH h₂).iteF (by rw [hS]; simp)).mono (by omega)

/-- Beyond the branches: the default, with the top lowered. -/
theorem caseTop_default (i : Fin K) : ∀ (ps : List (NProg K)) (q : NProg K) (v : Nat) (S : Lists K) (l : List Nat),
    S i = l ++ [v + ps.length] → ∀ (b : Bool) (S' : Lists K) (T : Nat),
      NHalts q (S.set i (l ++ [v])) b S' T → NHalts (caseTop i ps q) S b S' (T + 2 * ps.length)
  | [], q, v, S, l, hS, b, S', T, h => by
    simp only [List.length_nil, Nat.add_zero] at hS ⊢
    rw [← hS, Lists.set_get_self] at h; exact h
  | p :: ps, q, v, S, l, hS, b, S', T, h => by
    simp only [List.length_cons] at hS ⊢
    have hS' : S i = l ++ [(v + ps.length) + 1] := by rw [hS]; congr 2
    have h₁ := nruns_dec i S hS'
    simp only [Nat.add_sub_cancel] at h₁
    have h₂ := caseTop_default i ps q v (S.set i (l ++ [v + ps.length])) l (by simp) b S' T
      (by rw [Lists.set_set_u]; exact h)
    exact ((h₁.seqH h₂).iteF (by rw [hS']; simp)).mono (by omega)

/-! ## Doing nothing -/

/-- No effect (push and pop on `s`). -/
def nskip (s : Fin K) : NProg K := .seq (.prim (.pushZ s)) (.prim (.pop s))

theorem nruns_skip (s : Fin K) (S : Lists K) : NRuns (nskip s) S S 2 := by
  have h₁ := nruns_pushZ s S
  have h₂ := nruns_pop s (S.set s (S s ++ [0])) (l := S s) (v := 0) (by simp)
  rw [Lists.set_set_u, Lists.set_get_self] at h₂
  exact h₁.seq h₂

end Complexity
