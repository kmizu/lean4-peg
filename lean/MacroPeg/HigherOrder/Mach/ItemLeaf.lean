import MacroPeg.HigherOrder.Mach.EvalSpec
import MacroPeg.HigherOrder.Mach.CodesNum
import MacroPeg.HigherOrder.Mach.TokChar
import Complexity.NFrame

/-!
# The leaf items on stacks (tags `0`–`4`)

A leaf item pushes `n` copies of the result codes of its parser at every position (`n` is entry `ctx` of `ENVT`),
or, for a literal number that names no literal, leaves the stack as it is.

The codes on `XS`, in the item and in the literals are numbers; a character is `Char.ofNat` of its code, whose
code is the code itself when it is valid and `0` otherwise (`leaf_norm`). So the program first *normalizes* the
codes it compares (`leaf_normTop`, counting down a copy in at most `v` steps).
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.HO Shallot.MacroPeg.Flat

/-! ## Normalized codes -/

/-- The code of `Char.ofNat v`. -/
def leaf_norm (v : Nat) : Nat := if v < 55296 ∨ (57343 < v ∧ v < 1114112) then v else 0

theorem leaf_toNat_ofNat (v : Nat) : (Char.ofNat v).toNat = leaf_norm v := by
  unfold leaf_norm
  by_cases h : v.isValidChar
  · rw [if_pos h]; exact (toNat_ofNat_iff v).mpr h
  · rw [if_neg h]
    unfold Char.ofNat
    rw [dif_neg h]; rfl

theorem leaf_norm_le (v : Nat) : leaf_norm v ≤ v := by
  unfold leaf_norm; split <;> omega

/-! ## Counting down a bounded number of times -/

section Generic

variable {K : Nat}

/-- Lower the top of `U` by `k`, stopping at `0`, in about `2 min v k` steps. -/
def leaf_decUpTo (U : Fin K) : Nat → NProg K
  | 0 => nskip U
  | k + 1 => .ite U .pos (.seq (.prim (.dec U)) (leaf_decUpTo U k)) (nskip U)

theorem leaf_decUpTo_runs (U : Fin K) : ∀ (k : Nat) (S : Lists K) (l : List Nat) (v : Nat), S U = l ++ [v] →
    NRuns (leaf_decUpTo U k) S (S.set U (l ++ [v - k])) (2 * min v k + 3)
  | 0, S, l, v, h => by
    have := nruns_skip U S
    rw [Nat.sub_zero, ← h, Lists.set_get_self]
    exact this.mono (by omega)
  | k + 1, S, l, v, h => by
    rcases v with _ | w
    · have x := (nruns_skip U S).iteF (i := U) (c := .pos)
        (p := .seq (.prim (.dec U)) (leaf_decUpTo U k)) (by rw [h]; simp)
      rw [Nat.zero_sub, ← h, Lists.set_get_self]
      exact x.mono (by omega)
    · have x₁ := nruns_dec U S h
      have x₂ := leaf_decUpTo_runs U k (S.set U (l ++ [w + 1 - 1])) l w (by simp)
      rw [Lists.set_set_u] at x₂
      have x := (x₁.seq x₂).iteT (i := U) (c := .pos) (q := nskip U) (by rw [h]; simp)
      rw [show w + 1 - (k + 1) = w - k by omega]
      exact x.mono (by omega)

theorem leaf_pos_false {L : Lists K} {U : Fin K} {e : Nat} (h : L U = [e]) (he : e = 0) :
    NTest.pos.eval (L U) = false := by rw [h, he]; rfl

theorem leaf_pos_true {L : Lists K} {U : Fin K} {e w : Nat} (h : L U = [e]) (he : e = w + 1) :
    NTest.pos.eval (L U) = true := by rw [h, he]; rfl

/-- Replace the top of `D` by `0`. -/
def leaf_zeroTop (D : Fin K) : NProg K := .seq (.prim (.pop D)) (.prim (.pushZ D))

theorem leaf_zeroTop_runs (D : Fin K) (S : Lists K) {l : List Nat} {v : Nat} (h : S D = l ++ [v]) :
    NRuns (leaf_zeroTop D) S (S.set D (l ++ [0])) 2 := by
  have x₁ := nruns_pop D S h
  have x₂ := nruns_pushZ D (S.set D l)
  rw [Lists.set_same, Lists.set_set_u] at x₂
  exact x₁.seq x₂

theorem leaf_ar₁ {v : Nat} (h1 : ¬ v < 55296) : v + 1 - 55296 = (v - 55296) + 1 := by omega
theorem leaf_ar₂ {v : Nat} (h2 : v ≤ 57343) : v + 1 - 55296 - 2048 = 0 := by omega
theorem leaf_ar₃ {v : Nat} (h2 : ¬ v ≤ 57343) : v + 1 - 55296 - 2048 = (v - 57344) + 1 := by omega
theorem leaf_ar₄ {v : Nat} (h3 : v < 1114112) : v + 1 - 55296 - 2048 - 1056768 = 0 := by omega
theorem leaf_ar₅ {v : Nat} (h3 : ¬ v < 1114112) : v + 1 - 55296 - 2048 - 1056768 = (v - 1114112) + 1 := by
  omega

/-- Normalize the top of `D` (scratch `U`, empty before and after). -/
def leaf_normTop (D U : Fin K) (h : D ≠ U) : NProg K :=
  .seq (.prim (.dup D U h)) (.seq (.prim (.inc U)) (.seq (leaf_decUpTo U 55296)
    (.seq (.ite U .pos (.seq (leaf_decUpTo U 2048)
        (.ite U .pos (.seq (leaf_decUpTo U 1056768) (.ite U .pos (leaf_zeroTop D) (nskip U))) (leaf_zeroTop D)))
      (nskip U)) (.prim (.pop U)))))

theorem leaf_normTop_runs (D U : Fin K) (h : D ≠ U) (S : Lists K) {l : List Nat} {v : Nat} (hD : S D = l ++ [v])
    (hU : S U = []) : NRuns (leaf_normTop D U h) S (S.set D (l ++ [leaf_norm v])) (2 * v + 30) := by
  have hUD : U ≠ D := Ne.symm h
  have x₁ := nruns_dup D U h S hD
  rw [hU, List.nil_append] at x₁
  have x₂ := nruns_inc U (S.set U [v]) (l := []) (v := v) (by simp)
  rw [Lists.set_set_u, List.nil_append] at x₂
  have x₃ := leaf_decUpTo_runs U 55296 (S.set U [v + 1]) [] (v + 1) (by simp)
  rw [Lists.set_set_u, List.nil_append] at x₃
  -- the final pop of `U`, from a state `S.set D d` with `U = [w]`
  have fin : ∀ (d : List Nat) (w : Nat), NRuns (.prim (.pop U)) ((S.set D d).set U [w]) (S.set D d) 1 := by
    intro d w
    have := nruns_pop U ((S.set D d).set U [w]) (l := []) (v := w) (by simp)
    have e : ((S.set D d).set U [w]).set U [] = S.set D d := by
      funext x
      by_cases hx : x = U
      · subst hx; simp [Lists.set, hUD, hU]
      · simp [Lists.set, hx]
    rwa [e] at this
  have keep : S.set D (l ++ [v]) = S := by rw [← hD, Lists.set_get_self]
  have zero : ∀ w, NRuns (leaf_zeroTop D) (S.set U [w]) ((S.set D (l ++ [0])).set U [w]) 2 := by
    intro w
    have := leaf_zeroTop_runs D (S.set U [w]) (l := l) (v := v) (by rw [Lists.set_ne _ _ h]; exact hD)
    rwa [Lists.set_comm hUD] at this
  have skip : ∀ w, NRuns (nskip U) (S.set U [w]) ((S.set D (l ++ [v])).set U [w]) 2 := by
    intro w; rw [keep]; exact nruns_skip U _
  by_cases h1 : v < 55296
  · have hn : leaf_norm v = v := by unfold leaf_norm; rw [if_pos (.inl h1)]
    have x₄ := (skip (v + 1 - 55296)).iteF (i := U) (c := .pos)
      (p := .seq (leaf_decUpTo U 2048)
        (.ite U .pos (.seq (leaf_decUpTo U 1056768) (.ite U .pos (leaf_zeroTop D) (nskip U))) (leaf_zeroTop D)))
      (leaf_pos_false (Lists.set_same _ _ _) (by omega))
    rw [hn]
    exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq (fin _ _))))).mono (by omega)
  have hw₁ := leaf_ar₁ h1
  have x₅ := leaf_decUpTo_runs U 2048 (S.set U [v + 1 - 55296]) [] (v + 1 - 55296) (by simp)
  rw [Lists.set_set_u, List.nil_append] at x₅
  by_cases h2 : v ≤ 57343
  · have hn : leaf_norm v = 0 := by unfold leaf_norm; rw [if_neg (by omega)]
    have x₆ := (zero (v + 1 - 55296 - 2048)).iteF (i := U) (c := .pos)
      (p := .seq (leaf_decUpTo U 1056768) (.ite U .pos (leaf_zeroTop D) (nskip U)))
      (leaf_pos_false (Lists.set_same _ _ _) (leaf_ar₂ h2))
    have x₇ := (x₅.seq x₆).iteT (i := U) (c := .pos) (q := nskip U) (leaf_pos_true (Lists.set_same _ _ _) hw₁)
    rw [hn]
    exact (x₁.seq (x₂.seq (x₃.seq (x₇.seq (fin _ _))))).mono (by omega)
  have hw₂ := leaf_ar₃ h2
  have x₈ := leaf_decUpTo_runs U 1056768 (S.set U [v + 1 - 55296 - 2048]) [] (v + 1 - 55296 - 2048) (by simp)
  rw [Lists.set_set_u, List.nil_append] at x₈
  by_cases h3 : v < 1114112
  · have hn : leaf_norm v = v := by unfold leaf_norm; rw [if_pos (.inr ⟨by omega, h3⟩)]
    have x₉ := (skip (v + 1 - 55296 - 2048 - 1056768)).iteF (i := U) (c := .pos) (p := leaf_zeroTop D)
      (leaf_pos_false (Lists.set_same _ _ _) (leaf_ar₄ h3))
    have x₁₀ := ((x₈.seq x₉).iteT (i := U) (c := .pos) (q := leaf_zeroTop D)
      (leaf_pos_true (Lists.set_same _ _ _) hw₂))
    have x₁₁ := (x₅.seq x₁₀).iteT (i := U) (c := .pos) (q := nskip U) (leaf_pos_true (Lists.set_same _ _ _) hw₁)
    rw [hn]
    exact (x₁.seq (x₂.seq (x₃.seq (x₁₁.seq (fin _ _))))).mono (by omega)
  · have hn : leaf_norm v = 0 := by unfold leaf_norm; rw [if_neg (by omega)]
    have hw₃ := leaf_ar₅ h3
    have x₉ := (zero (v + 1 - 55296 - 2048 - 1056768)).iteT (i := U) (c := .pos) (q := nskip U)
      (leaf_pos_true (Lists.set_same _ _ _) hw₃)
    have x₁₀ := ((x₈.seq x₉).iteT (i := U) (c := .pos) (q := leaf_zeroTop D)
      (leaf_pos_true (Lists.set_same _ _ _) hw₂))
    have x₁₁ := (x₅.seq x₁₀).iteT (i := U) (c := .pos) (q := nskip U) (leaf_pos_true (Lists.set_same _ _ _) hw₁)
    rw [hn]
    exact (x₁.seq (x₂.seq (x₃.seq (x₁₁.seq (fin _ _))))).mono (by omega)

/-! ## Comparing in about `5 min a b` steps -/

/-- The loop body: lower both copies, or (when the second is `0` first) set the first to `0` and mark. -/
def leaf_cmpBody (t u g : Fin K) : NProg K :=
  .ite u .pos (.seq (.prim (.dec t)) (.prim (.dec u))) (.seq (.prim (.pop t)) (.seq (.prim (.pushZ t)) (.prim (.inc g))))

/-- Compare the tops `a` of `i` and `b` of `j`: push `cmpRes a b` on `f`. Scratch `t u g` (restored). -/
def leaf_cmp (i j t u g f : Fin K) (hit : i ≠ t) (hju : j ≠ u) : NProg K :=
  .seq (.prim (.dup i t hit)) (.seq (.prim (.dup j u hju)) (.seq (.prim (.pushZ g))
    (.seq (.loop t .pos (leaf_cmpBody t u g))
      (.seq (.ite g .pos (npushC f 2) (.ite u .zero (npushC f 1) (npushC f 0)))
        (.seq (.prim (.pop t)) (.seq (.prim (.pop u)) (.prim (.pop g))))))))

theorem leaf_cmp_runs (i j t u g f : Fin K) (hit : i ≠ t) (hju : j ≠ u) (hd : [i, j, t, u, g, f].Nodup)
    (S : Lists K) {li lj : List Nat} {a b : Nat} (hi : S i = li ++ [a]) (hj : S j = lj ++ [b]) :
    NRuns (leaf_cmp i j t u g f hit hju) S (S.set f (S f ++ [cmpRes a b])) (5 * min a b + 20) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨_, _, _, _, _⟩, ⟨_, _, _, _⟩, ⟨htu, htg, htf⟩, ⟨hug, huf⟩, hgf⟩ := hd
  let reg : Nat → Lists K := fun m => ((S.set t (S t ++ [a - m])).set u (S u ++ [b - m])).set g (S g ++ [0])
  have x₁ := nruns_dup i t hit S hi
  have x₂ := nruns_dup j u hju (S.set t (S t ++ [a])) (l := lj) (v := b) (by rw [Lists.set_ne]; exact hj; assumption)
  have x₃ := nruns_pushZ g ((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b]))
  have e₀ : ((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b])).set g
      (((S.set t (S t ++ [a])).set u ((S.set t (S t ++ [a])) u ++ [b])) g ++ [0]) = reg 0 := by
    simp only [reg]; lists_eq
  rw [e₀] at x₃
  have hrt : ∀ m, reg m t = S t ++ [a - m] := fun m => by simp only [reg]; lists_at
  have hru : ∀ m, reg m u = S u ++ [b - m] := fun m => by simp only [reg]; lists_at
  have hrg : ∀ m, reg m g = S g ++ [0] := fun m => by simp only [reg]; lists_at
  have finish : ∀ (St : Lists K) (r vt vu vg : Nat), St = ((S.set t (S t ++ [vt])).set u (S u ++ [vu])).set g
      (S g ++ [vg]) → NRuns (.seq (.prim (.pop t)) (.seq (.prim (.pop u)) (.prim (.pop g))))
        (St.set f (S f ++ [r])) (S.set f (S f ++ [r])) 3 := by
    intro St r vt vu vg hSt
    have p₁ := nruns_pop t (St.set f (S f ++ [r])) (l := S t) (v := vt) (by rw [hSt]; lists_at)
    have p₂ := nruns_pop u ((St.set f (S f ++ [r])).set t (S t)) (l := S u) (v := vu) (by rw [hSt]; lists_at)
    have p₃ := nruns_pop g (((St.set f (S f ++ [r])).set t (S t)).set u (S u)) (l := S g) (v := vg)
      (by rw [hSt]; lists_at)
    have e : ((((St.set f (S f ++ [r])).set t (S t)).set u (S u)).set g (S g)) = S.set f (S f ++ [r]) := by
      rw [hSt]; lists_eq
    rw [e] at p₃
    exact p₁.seq (p₂.seq p₃)
  have step : ∀ m, m < a → m < b → NRuns (leaf_cmpBody t u g) (reg m) (reg (m + 1)) 4 := by
    intro m hma hmb
    have d₁ := nruns_dec t (reg m) (hrt m)
    have d₂ := nruns_dec u ((reg m).set t (S t ++ [a - m - 1])) (l := S u) (v := b - m)
      (by rw [Lists.set_ne _ _ (Ne.symm htu)]; exact hru m)
    have e : ((reg m).set t (S t ++ [a - m - 1])).set u (S u ++ [b - m - 1]) = reg (m + 1) := by
      simp only [reg]; lists_eq
    rw [e] at d₂
    exact ((d₁.seq d₂).iteT (by rw [hru, show b - m = (b - m - 1) + 1 by omega]; simp)).mono (by omega)
  by_cases hab : a ≤ b
  · have hl := nruns_family_const (i := t) (c := .pos) (p := leaf_cmpBody t u g) reg a 4
      (fun m hm => by rw [hrt, show a - m = (a - m - 1) + 1 by omega]; simp)
      (by rw [hrt, Nat.sub_self]; simp)
      (fun m hm => step m hm (by omega))
    have hmin : min a b = a := Nat.min_eq_left hab
    by_cases heq : a = b
    · subst heq
      have hc : cmpRes a a = 1 := by simp [cmpRes]
      have pc := nruns_pushC f (reg a) 1
      have hit' := (pc.iteT (i := u) (c := .zero) (q := npushC f 0) (by rw [hru, Nat.sub_self]; simp)).iteF
        (i := g) (c := .pos) (p := npushC f 2) (by rw [hrg]; simp)
      have hfin := finish (reg a) 1 0 0 0 (by simp only [reg, Nat.sub_self])
      rw [show (reg a) f = S f by simp only [reg]; lists_at] at hit'
      rw [hc]
      exact (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono (by omega)
    · have hlt : a < b := by omega
      have hc : cmpRes a b = 0 := by simp [cmpRes, hlt]
      have pc := nruns_pushC f (reg a) 0
      have hit' := (pc.iteF (i := u) (c := .zero) (p := npushC f 1)
        (by rw [hru, show b - a = (b - a - 1) + 1 by omega]; simp)).iteF
        (i := g) (c := .pos) (p := npushC f 2) (by rw [hrg]; simp)
      have hfin := finish (reg a) 0 0 (b - a) 0 (by simp only [reg, Nat.sub_self])
      rw [show (reg a) f = S f by simp only [reg]; lists_at] at hit'
      rw [hc]
      exact (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono (by omega)
  · have hba : b < a := by omega
    have hmin : min a b = b := Nat.min_eq_right (by omega)
    let mk : Lists K := ((S.set t (S t ++ [0])).set u (S u ++ [0])).set g (S g ++ [1])
    let F : Nat → Lists K := fun m => if m ≤ b then reg m else mk
    have hFt : ∀ m, m ≤ b → F m t = S t ++ [a - m] := fun m hm => by simp only [F, hm, if_true]; exact hrt m
    have hl := nruns_family_const (i := t) (c := .pos) (p := leaf_cmpBody t u g) F (b + 1) 4
      (fun m hm => by rw [hFt m (by omega), show a - m = (a - m - 1) + 1 by omega]; simp)
      (by simp only [F, show ¬ b + 1 ≤ b by omega, if_false, mk]; rw [show ((((S.set t (S t ++ [0])).set u
          (S u ++ [0])).set g (S g ++ [1])) t) = S t ++ [0] by lists_at]; simp)
      (fun m hm => by
        by_cases hmb : m < b
        · have hF : F m = reg m := by simp only [F, show m ≤ b by omega, if_true]
          have hF' : F (m + 1) = reg (m + 1) := by simp only [F, show m + 1 ≤ b by omega, if_true]
          rw [hF, hF']
          exact step m (by omega) hmb
        · obtain rfl : m = b := by omega
          have hF : F m = reg m := by simp only [F, Nat.le_refl, if_true]
          have hF' : F (m + 1) = mk := by simp only [F, show ¬ m + 1 ≤ m by omega, if_false]
          rw [hF, hF']
          have z₁ := nruns_pop t (reg m) (hrt m)
          have z₂ := nruns_pushZ t ((reg m).set t (S t))
          rw [Lists.set_same, Lists.set_set_u] at z₂
          have ig := nruns_inc g ((reg m).set t (S t ++ [0])) (l := S g) (v := 0)
            (by rw [Lists.set_ne _ _ (Ne.symm htg)]; exact hrg m)
          have e : ((reg m).set t (S t ++ [0])).set g (S g ++ [0 + 1]) = mk := by simp only [reg, mk]; lists_eq
          rw [e] at ig
          exact ((z₁.seq (z₂.seq ig)).iteF (by rw [hru, Nat.sub_self]; simp)).mono (by omega))
    have hF0 : F 0 = reg 0 := by simp [F]
    rw [hF0, show F (b + 1) = mk by simp only [F, show ¬ b + 1 ≤ b by omega, if_false]] at hl
    have hc : cmpRes a b = 2 := by simp [cmpRes, show ¬ a < b by omega, show a ≠ b by omega]
    have pc := nruns_pushC f mk 2
    have hit' := pc.iteT (i := g) (c := .pos) (q := .ite u .zero (npushC f 1) (npushC f 0))
      (by rw [show mk g = S g ++ [1] by simp only [mk]; lists_at]; simp)
    have hfin := finish mk 2 0 0 1 rfl
    rw [show mk f = S f by simp only [mk]; lists_at] at hit'
    rw [hc]
    exact (x₁.seq (x₂.seq (x₃.seq (hl.seq (hit'.seq hfin))))).mono (by omega)

/-! ## Copying a stack through a map -/

/-- `S'` agrees with `S` outside the stacks `l`. -/
def leaf_agree (S S' : Lists K) (l : List (Fin K)) : Prop := ∀ k, k ∉ l → S' k = S k

/-- Copy `X` onto `Y` in the same order, applying `g` to each copied top (scratch `W`, empty before and after). -/
def leaf_copyMap (X W Y : Fin K) (hXW : X ≠ W) (hWY : W ≠ Y) (g : NProg K) : NProg K :=
  .seq (nmvAll X W hXW) (.loop W .nonempty (.seq (.prim (.dup W Y hWY)) (.seq g (nmv W X (Ne.symm hXW)))))

theorem leaf_copyMap_runs (X W Y : Fin K) (hXW : X ≠ W) (hWY : W ≠ Y) (hXY : X ≠ Y) (g : NProg K)
    (h : Nat → Nat) (B : Nat) (S : Lists K) (hW : S W = [])
    (hg : ∀ (S' : Lists K) (l : List Nat) (v : Nat), leaf_agree S S' [X, W, Y] → v ∈ S X → S' Y = l ++ [v] →
      NRuns g S' (S'.set Y (l ++ [h v])) B) :
    NRuns (leaf_copyMap X W Y hXW hWY g) S (S.set Y (S Y ++ (S X).map h))
      (3 * (S X).length + 1 + ((S X).length * (B + 4) + 1)) := by
  have hWX := Ne.symm hXW
  have hYW := Ne.symm hWY
  have hYX := Ne.symm hXY
  let xs := S X
  have x₁ := nruns_mvAll X W hXW S
  rw [hW, List.nil_append] at x₁
  let F : Nat → Lists K := fun m =>
    ((S.set W (xs.drop m).reverse).set X (xs.take m)).set Y (S Y ++ (xs.take m).map h)
  have h0 : (S.set W (S X).reverse).set X [] = F 0 := by
    simp only [F, List.drop_zero, List.take_zero, List.map_nil, List.append_nil, xs]
    funext k
    by_cases hk : k = Y
    · subst hk; simp [Lists.set, hYX, hYW]
    · simp [Lists.set, hk]
  rw [h0] at x₁
  have hFW : ∀ m, F m W = (xs.drop m).reverse := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hWY, Lists.set_ne _ _ hWX, Lists.set_same]
  have hFX : ∀ m, F m X = xs.take m := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ hXY, Lists.set_same]
  have hFY : ∀ m, F m Y = S Y ++ (xs.take m).map h := fun m => by simp only [F, Lists.set_same]
  have hFa : ∀ m, leaf_agree S (F m) [X, W, Y] := fun m k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [F]; rw [Lists.set_ne _ _ hk.2.2, Lists.set_ne _ _ hk.1, Lists.set_ne _ _ hk.2.1]
  have hl := nruns_family_const (i := W) (c := .nonempty) (p := .seq (.prim (.dup W Y hWY)) (.seq g (nmv W X hWX)))
    F xs.length (B + 3)
    (fun m hm => by rw [hFW]; exact eval_nonempty_ne (by simp; omega))
    (by rw [hFW]; simp)
    (fun m hm => by
      have hd : xs.drop m = xs[m] :: xs.drop (m + 1) := List.drop_eq_getElem_cons hm
      have hW' : F m W = (xs.drop (m + 1)).reverse ++ [xs[m]] := by rw [hFW, hd, List.reverse_cons]
      have d₁ := nruns_dup W Y hWY (F m) hW'
      rw [hFY] at d₁
      let S₁ := (F m).set Y (S Y ++ (xs.take m).map h ++ [xs[m]])
      have hA : leaf_agree S S₁ [X, W, Y] := fun k hk => by
        have hk' := hk
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk'
        simp only [S₁]; rw [Lists.set_ne _ _ hk'.2.2]; exact hFa m k hk
      have d₂ := hg S₁ (S Y ++ (xs.take m).map h) xs[m] hA (List.getElem_mem hm) (by simp [S₁])
      rw [show S₁.set Y (S Y ++ (xs.take m).map h ++ [h xs[m]]) = (F m).set Y (S Y ++ (xs.take m).map h ++
        [h xs[m]]) by simp only [S₁, Lists.set_set_u]] at d₂
      have d₃ := nruns_mv W X hWX ((F m).set Y (S Y ++ (xs.take m).map h ++ [h xs[m]]))
        (l := (xs.drop (m + 1)).reverse) (v := xs[m]) (by rw [Lists.set_ne _ _ hWY, hW'])
      have e : ((((F m).set Y (S Y ++ (xs.take m).map h ++ [h xs[m]])).set X
          (((F m).set Y (S Y ++ (xs.take m).map h ++ [h xs[m]])) X ++ [xs[m]])).set W (xs.drop (m + 1)).reverse) =
          F (m + 1) := by
        rw [Lists.set_ne _ _ hXY, hFX, ← List.take_succ_eq_append_getElem hm]
        have ht : (xs.take (m + 1)).map h = (xs.take m).map h ++ [h xs[m]] := by
          rw [List.take_succ_eq_append_getElem hm, List.map_append]; rfl
        simp only [F, ht, List.append_assoc]
        funext k
        by_cases hkY : k = Y
        · subst hkY; simp [Lists.set, hYX, hYW]
        · by_cases hkX : k = X
          · subst hkX; simp [Lists.set, hXY, hXW]
          · by_cases hkW : k = W
            · subst hkW; simp [Lists.set, hWY, hWX]
            · simp [Lists.set, hkY, hkX, hkW]
      rw [e] at d₃
      exact (d₁.seq (d₂.seq d₃)).mono (by omega))
  have hend : F xs.length = S.set Y (S Y ++ (S X).map h) := by
    simp only [F, List.drop_length, List.reverse_nil, List.take_length, xs]
    rw [← hW, Lists.set_get_self, Lists.set_get_self]
  rw [hend] at hl
  exact (x₁.seq hl).mono (by simp only [xs, show B + 3 + 1 = B + 4 by omega]; omega)

/-! ## The loop over the positions -/

/-- For `q = 0, …, N`: run `posP` with the suffix of length `q` of `X` on `T` (reversed: its first symbol on top)
and `q + 2` on `Q`. `X` is consumed; `T`, `Q` are empty before and after. -/
def leaf_posLoop (X T Q : Fin K) (hXT : X ≠ T) (posP : NProg K) : NProg K :=
  .seq (npushC Q 2) (.seq posP (.seq (.loop X .nonempty (.seq (nmv X T hXT) (.seq (.prim (.inc Q)) posP)))
    (.seq (nclr T) (.prim (.pop Q)))))

/-- The state of the position loop at position `q`, with `cs` on `C`. -/
def leaf_posSt (S : Lists K) (X T Q C : Fin K) (xn : List Nat) (q : Nat) (cs : List Nat) : Lists K :=
  (((S.set X (xn.take (xn.length - q))).set T (xn.drop (xn.length - q)).reverse).set Q [q + 2]).set C cs

theorem leaf_posLoop_runs (X T Q C : Fin K) (hXT : X ≠ T) (hd : [X, T, Q, C].Nodup) (posP : NProg K)
    (f : Nat → Nat) (B : Nat) (S : Lists K) (hT : S T = []) (hQ : S Q = [])
    (hP : ∀ q, q ≤ (S X).length → ∀ cs, NRuns posP (leaf_posSt S X T Q C (S X) q cs)
      (leaf_posSt S X T Q C (S X) q (cs ++ [f q])) B) :
    NRuns (leaf_posLoop X T Q hXT posP) S ((S.set X []).set C (S C ++ (List.range ((S X).length + 1)).map f))
      (B + 3 + ((S X).length * (B + 4) + 1) + (2 * (S X).length + 3)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd
  obtain ⟨⟨_, hXQ, hXC⟩, ⟨hTQ, hTC⟩, hQC'⟩ := hd
  have hQC : Q ≠ C := hQC'.1
  generalize hxn : S X = xn at hP
  let G : Nat → Lists K := fun m => leaf_posSt S X T Q C xn m (S C ++ (List.range (m + 1)).map f)
  -- start
  have x₁ := nruns_pushC Q S 2
  rw [hQ, List.nil_append] at x₁
  have e₀ : S.set Q [2] = leaf_posSt S X T Q C xn 0 (S C) := by
    simp only [leaf_posSt, Nat.sub_zero, List.take_length, List.drop_length, List.reverse_nil]
    rw [← hxn, ← hT]; lists_eq
  rw [e₀] at x₁
  have x₂ := hP 0 (Nat.zero_le _) (S C)
  have hG0 : leaf_posSt S X T Q C xn 0 (S C ++ [f 0]) = G 0 := by simp [G]
  rw [hG0] at x₂
  have hGX : ∀ m, G m X = xn.take (xn.length - m) := fun m => by
    simp only [G, leaf_posSt]
    rw [Lists.set_ne _ _ hXC, Lists.set_ne _ _ hXQ, Lists.set_ne _ _ hXT, Lists.set_same]
  have hl := nruns_family_const (i := X) (c := .nonempty) (p := .seq (nmv X T hXT) (.seq (.prim (.inc Q)) posP))
    G xn.length (B + 3)
    (fun m hm => by rw [hGX]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hGX, Nat.sub_self]; simp)
    (fun m hm => by
      have hlt : xn.length - m - 1 < xn.length := by omega
      have ht : xn.take (xn.length - m) = xn.take (xn.length - m - 1) ++ [xn[xn.length - m - 1]] := by
        have := List.take_succ_eq_append_getElem hlt
        rwa [show xn.length - m - 1 + 1 = xn.length - m by omega] at this
      have d₁ := nruns_mv X T hXT (G m) (by rw [hGX, ht])
      have hdr : xn.drop (xn.length - m - 1) = xn[xn.length - m - 1] :: xn.drop (xn.length - m) := by
        have := List.drop_eq_getElem_cons hlt
        rwa [show xn.length - m - 1 + 1 = xn.length - m by omega] at this
      have e₁ : ((G m).set T ((G m) T ++ [xn[xn.length - m - 1]])).set X (xn.take (xn.length - m - 1)) =
          (((S.set X (xn.take (xn.length - (m + 1)))).set T (xn.drop (xn.length - (m + 1))).reverse).set Q
            [m + 2]).set C (S C ++ (List.range (m + 1)).map f) := by
        rw [show xn.length - (m + 1) = xn.length - m - 1 by omega, hdr, List.reverse_cons]
        simp only [G, leaf_posSt]
        funext k
        by_cases hkX : k = X
        · rw [hkX]; simp [Lists.set, hXT, hXQ, hXC]
        · by_cases hkT : k = T
          · rw [hkT]; simp [Lists.set, hTQ, hTC, Ne.symm hXT]
          · simp [Lists.set, hkX, hkT]
      rw [e₁] at d₁
      have d₂ := nruns_inc Q ((((S.set X (xn.take (xn.length - (m + 1)))).set T
        (xn.drop (xn.length - (m + 1))).reverse).set Q [m + 2]).set C (S C ++ (List.range (m + 1)).map f))
        (l := []) (v := m + 2) (by rw [Lists.set_ne _ _ hQC, Lists.set_same]; rfl)
      have e₂ : ((((S.set X (xn.take (xn.length - (m + 1)))).set T (xn.drop (xn.length - (m + 1))).reverse).set Q
          [m + 2]).set C (S C ++ (List.range (m + 1)).map f)).set Q ([] ++ [m + 2 + 1]) =
          leaf_posSt S X T Q C xn (m + 1) (S C ++ (List.range (m + 1)).map f) := by
        simp only [leaf_posSt, List.nil_append]
        rw [Lists.set_comm hQC, Lists.set_set_u, show m + 2 + 1 = m + 1 + 2 by omega,
          Lists.set_comm (Ne.symm hQC)]
      rw [e₂] at d₂
      have d₃ := hP (m + 1) (by omega) (S C ++ (List.range (m + 1)).map f)
      have e₃ : (S C ++ (List.range (m + 1)).map f ++ [f (m + 1)]) = S C ++ (List.range (m + 1 + 1)).map f := by
        rw [List.range_succ (n := m + 1), List.map_append, List.append_assoc]; rfl
      rw [e₃] at d₃
      exact (d₁.seq (d₂.seq d₃)).mono (by omega))
  -- the end: clear `T`, pop `Q`
  have hGT : G xn.length T = xn.reverse := by
    simp only [G, leaf_posSt, Nat.sub_self, List.drop_zero]
    rw [Lists.set_ne _ _ hTC, Lists.set_ne _ _ hTQ, Lists.set_same]
  have x₃ := nruns_clr T (G xn.length)
  rw [hGT] at x₃
  have x₄ := nruns_pop Q ((G xn.length).set T []) (l := []) (v := xn.length + 2)
    (by simp only [G, leaf_posSt]; rw [Lists.set_ne _ _ (Ne.symm hTQ), Lists.set_ne _ _ hQC, Lists.set_same]; rfl)
  have e₄ : ((G xn.length).set T []).set Q [] =
      (S.set X []).set C (S C ++ (List.range (xn.length + 1)).map f) := by
    simp only [G, leaf_posSt, Nat.sub_self, List.take_zero]
    funext k
    by_cases hkX : k = X
    · rw [hkX]; simp [Lists.set, hXT, hXQ, hXC]
    · by_cases hkT : k = T
      · rw [hkT]; simp [Lists.set, hTQ, hTC, Ne.symm hXT, hT]
      · by_cases hkQ : k = Q
        · rw [hkQ]; simp [Lists.set, hQC, Ne.symm hXQ, hQ]
        · simp [Lists.set, hkX, hkT, hkQ]
  rw [e₄] at x₄
  simp only [List.length_reverse] at x₃
  exact (x₁.seq (x₂.seq (hl.seq (x₃.seq x₄)))).mono (by rw [show B + 3 + 1 = B + 4 by omega]; omega)

theorem leaf_cmpRes_cases (a b : Nat) : cmpRes a b = 0 ∨ cmpRes a b = 1 ∨ cmpRes a b = 2 := by
  have := cmpRes_le a b; omega

/-- Compare, then branch three ways on the result. -/
theorem leaf_cmpThen_runs (i j t u g f : Fin K) (hit : i ≠ t) (hju : j ≠ u) (hd : [i, j, t, u, g, f].Nodup)
    (P₀ P₁ P₂ D : NProg K) (S S' : Lists K) {li lj : List Nat} {a b : Nat} (hi : S i = li ++ [a])
    (hj : S j = lj ++ [b]) (T : Nat) (h₀ : cmpRes a b = 0 → NRuns P₀ S S' T) (h₁ : cmpRes a b = 1 → NRuns P₁ S S' T)
    (h₂ : cmpRes a b = 2 → NRuns P₂ S S' T) :
    NRuns (.seq (leaf_cmp i j t u g f hit hju) (caseTop f [P₀, P₁, P₂] D)) S S' (5 * min a b + T + 26) := by
  have c₁ := leaf_cmp_runs i j t u g f hit hju hd S hi hj
  have back : (S.set f (S f ++ [cmpRes a b])).set f (S f) = S := by rw [Lists.set_set_u, Lists.set_get_self]
  have hcf : (S.set f (S f ++ [cmpRes a b])) f = S f ++ [cmpRes a b] := Lists.set_same _ _ _
  rcases leaf_cmpRes_cases a b with r | r | r
  · have := caseTop_runs f [P₀, P₁, P₂] D 0 (by simp) (S.set f (S f ++ [cmpRes a b])) (S f) (by rw [hcf, r])
      S' T (by rw [back]; exact h₀ r)
    exact (c₁.seq this).mono (by omega)
  · have := caseTop_runs f [P₀, P₁, P₂] D 1 (by simp) (S.set f (S f ++ [cmpRes a b])) (S f) (by rw [hcf, r])
      S' T (by rw [back]; exact h₁ r)
    exact (c₁.seq this).mono (by omega)
  · have := caseTop_runs f [P₀, P₁, P₂] D 2 (by simp) (S.set f (S f ++ [cmpRes a b])) (S f) (by rw [hcf, r])
      S' T (by rw [back]; exact h₂ r)
    exact (c₁.seq this).mono (by omega)

end Generic

/-! ## The scratch stacks of the leaf programs -/

/-- Peek scratch, and temporary copies. -/
abbrev leaf_PT : Fin NK := 18
/-- Indices for peeking, and temporary copies. -/
abbrev leaf_PC : Fin NK := 19
abbrev leaf_TG : Fin NK := 20
/-- The number of environments `n`. -/
abbrev leaf_NN : Fin NK := 21
/-- The (normalized) first argument; for literals the literal number, then the literal's length. -/
abbrev leaf_AA : Fin NK := 22
/-- The (normalized) second argument; for literals the literal as on `LTs` (codes plus one). -/
abbrev leaf_BB : Fin NK := 23
/-- The codes at the positions `0, …, N`. -/
abbrev leaf_C : Fin NK := 24
/-- The (normalized) input codes. -/
abbrev leaf_XN : Fin NK := 25
/-- The suffix at the current position. -/
abbrev leaf_T : Fin NK := 26
/-- The current position plus two. -/
abbrev leaf_Q : Fin NK := 27
abbrev leaf_t : Fin NK := 28
abbrev leaf_u : Fin NK := 29
abbrev leaf_g : Fin NK := 30
/-- The result of a comparison. -/
abbrev leaf_f : Fin NK := 31
/-- The normalized literal, its first code on top. -/
abbrev leaf_L : Fin NK := 32
/-- Whether the literal matches. -/
abbrev leaf_FL : Fin NK := 33

/-- Equalities of stacks updated at a few named places: compare at each named stack, then elsewhere. -/
macro "leaf_ext" "[" xs:term,* "]" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let mut tac ← `(Lean.Parser.Tactic.tacticSeq| simp [leaf_PT, leaf_PC, leaf_TG, leaf_NN, leaf_AA, leaf_BB, leaf_C, leaf_XN, leaf_T, leaf_Q, leaf_t, leaf_u, leaf_g, leaf_f, leaf_L, leaf_FL, EV, EVL, IT, ENVT, XS, LTs, NX, $hs,*])
  for x in xs.getElems.reverse do
    tac ← `(Lean.Parser.Tactic.tacticSeq|
      by_cases hk : k = $x
      · simp only [hk]; try simp [leaf_PT, leaf_PC, leaf_TG, leaf_NN, leaf_AA, leaf_BB, leaf_C, leaf_XN, leaf_T, leaf_Q, leaf_t, leaf_u, leaf_g, leaf_f, leaf_L, leaf_FL, EV, EVL, IT, ENVT, XS, LTs, NX, $hs,*]
      · try simp only [hk, if_false]
        try ($tac))
  `(tactic| (funext k; simp only [Lists.set]; ($tac)))

/-- Read a stack of stacks updated at a few named places. -/
macro "leaf_get" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Lists.set, leaf_PT, leaf_PC, leaf_TG, leaf_NN, leaf_AA, leaf_BB, leaf_C, leaf_XN, leaf_T, leaf_Q, leaf_t, leaf_u, leaf_g, leaf_f, leaf_L, leaf_FL, EV, EVL, IT, ENVT, XS, LTs, NX, $hs,*])

/-! ## Matching a literal -/

/-- Whether the first `m` symbols of `w` are there and are those of `s`. -/
def leaf_bit (s w : List Nat) (m : Nat) : Nat := if m ≤ w.length ∧ w.take m = s.take m then 1 else 0

/-- Compare the top of `L` with the top of `T` if the flag is still set; clear the flag unless equal. -/
def leaf_cmpCase : NProg NK :=
  .seq (leaf_cmp leaf_L leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide))
    (caseTop leaf_f [leaf_zeroTop leaf_FL, nskip leaf_f, leaf_zeroTop leaf_FL] (nskip leaf_f))

def leaf_matchBody : NProg NK :=
  .seq (.ite leaf_T .empty (leaf_zeroTop leaf_FL)
      (.seq (.ite leaf_FL .pos leaf_cmpCase (nskip leaf_f)) (nmv leaf_T leaf_PC (by decide))))
    (nmv leaf_L leaf_PT (by decide))

/-- Push on `FL` whether the literal on `L` (first symbol on top) starts the suffix on `T` (first symbol on top).
Scratch `PT PC t u g f`. -/
def leaf_matchP : NProg NK :=
  .seq (npushC leaf_FL 1) (.seq (.loop leaf_L .nonempty leaf_matchBody)
    (.seq (nmvAll leaf_PT leaf_L (by decide)) (nmvAll leaf_PC leaf_T (by decide))))

/-- The states of the matching loop. -/
def leaf_mSt (S : Lists NK) (s w lf : List Nat) (m mT b : Nat) : Lists NK :=
  ((((S.set leaf_L (s.drop m).reverse).set leaf_PT (s.take m)).set leaf_T (w.drop mT).reverse).set leaf_PC
    (w.take mT)).set leaf_FL (lf ++ [b])

theorem leaf_take_succ_eq {s w : List Nat} {m : Nat} (hs : m < s.length) (hw : m < w.length) :
    w.take (m + 1) = s.take (m + 1) ↔ w.take m = s.take m ∧ w[m] = s[m] := by
  rw [List.take_succ_eq_append_getElem hs, List.take_succ_eq_append_getElem hw]
  constructor
  · intro h
    have h₁ := List.append_inj h (by simp; omega)
    exact ⟨h₁.1, by simpa using h₁.2⟩
  · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]

theorem leaf_bit_succ_gone {s w : List Nat} {m : Nat} (hw : w.length ≤ m) : leaf_bit s w (m + 1) = 0 := by
  simp only [leaf_bit]; rw [if_neg (by omega)]

theorem leaf_bit_succ_zero {s w : List Nat} {m : Nat} (hs : m < s.length) (hw : m < w.length)
    (h : leaf_bit s w m = 0) : leaf_bit s w (m + 1) = 0 := by
  simp only [leaf_bit] at h ⊢
  rw [if_neg]
  intro ⟨_, h'⟩
  rw [leaf_take_succ_eq hs hw] at h'
  rw [if_pos ⟨by omega, h'.1⟩] at h; cases h

theorem leaf_bit_succ_one {s w : List Nat} {m : Nat} (hs : m < s.length) (hw : m < w.length)
    (h : leaf_bit s w m = 1) : leaf_bit s w (m + 1) = if w[m] = s[m] then 1 else 0 := by
  simp only [leaf_bit] at h ⊢
  have hm : m ≤ w.length ∧ w.take m = s.take m := by
    by_cases hc : m ≤ w.length ∧ w.take m = s.take m
    · exact hc
    · rw [if_neg hc] at h; cases h
  by_cases he : w[m] = s[m]
  · rw [if_pos he, if_pos ⟨by omega, (leaf_take_succ_eq hs hw).2 ⟨hm.2, he⟩⟩]
  · rw [if_neg he, if_neg (fun h' => he ((leaf_take_succ_eq hs hw).1 h'.2).2)]

theorem leaf_bit_le (s w : List Nat) (m : Nat) : leaf_bit s w m = 0 ∨ leaf_bit s w m = 1 := by
  unfold leaf_bit; split <;> simp

theorem leaf_mSt_FL (S : Lists NK) (s w lf : List Nat) (m mT b b' : Nat) :
    (leaf_mSt S s w lf m mT b).set leaf_FL (lf ++ [b']) = leaf_mSt S s w lf m mT b' := by
  unfold leaf_mSt; rw [Lists.set_set_u]

theorem leaf_mSt_moveT (S : Lists NK) (s w lf : List Nat) (m b : Nat) (hm : m < w.length) :
    NRuns (nmv leaf_T leaf_PC (by decide)) (leaf_mSt S s w lf m m b) (leaf_mSt S s w lf m (m + 1) b) 2 := by
  have hd : (w.drop m).reverse = (w.drop (m + 1)).reverse ++ [w[m]] := by
    rw [List.drop_eq_getElem_cons hm, List.reverse_cons]
  have x := nruns_mv leaf_T leaf_PC (by decide) (leaf_mSt S s w lf m m b) (l := (w.drop (m + 1)).reverse)
    (v := w[m]) (by unfold leaf_mSt; simp (config := {decide := true}) [Lists.set, hd])
  have ht := List.take_succ_eq_append_getElem hm
  have e : (((leaf_mSt S s w lf m m b).set leaf_PC ((leaf_mSt S s w lf m m b) leaf_PC ++ [w[m]])).set leaf_T
      (w.drop (m + 1)).reverse) = leaf_mSt S s w lf m (m + 1) b := by
    unfold leaf_mSt; leaf_ext [leaf_T, leaf_PC] []
  rw [e] at x; exact x

theorem leaf_mSt_moveL (S : Lists NK) (s w lf : List Nat) (m mT b : Nat) (hm : m < s.length) :
    NRuns (nmv leaf_L leaf_PT (by decide)) (leaf_mSt S s w lf m mT b) (leaf_mSt S s w lf (m + 1) mT b) 2 := by
  have hd : (s.drop m).reverse = (s.drop (m + 1)).reverse ++ [s[m]] := by
    rw [List.drop_eq_getElem_cons hm, List.reverse_cons]
  have x := nruns_mv leaf_L leaf_PT (by decide) (leaf_mSt S s w lf m mT b) (l := (s.drop (m + 1)).reverse)
    (v := s[m]) (by unfold leaf_mSt; simp (config := {decide := true}) [Lists.set, hd])
  have ht := List.take_succ_eq_append_getElem hm
  have e : (((leaf_mSt S s w lf m mT b).set leaf_PT ((leaf_mSt S s w lf m mT b) leaf_PT ++ [s[m]])).set leaf_L
      (s.drop (m + 1)).reverse) = leaf_mSt S s w lf (m + 1) mT b := by
    unfold leaf_mSt; leaf_ext [leaf_L, leaf_PT] []
  rw [e] at x; exact x

/-- One step of the matching loop. -/
theorem leaf_match_step (S : Lists NK) (s w lf : List Nat) (V : Nat) (hV : ∀ v ∈ s, v ≤ V) (m : Nat)
    (hm : m < s.length) :
    NRuns leaf_matchBody (leaf_mSt S s w lf m m (leaf_bit s w m))
      (leaf_mSt S s w lf (m + 1) (m + 1) (leaf_bit s w (m + 1))) (5 * V + 44) := by
  have hFT : ∀ mT b, (leaf_mSt S s w lf m mT b) leaf_T = (w.drop mT).reverse := fun mT b => by
    unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have hFF : ∀ mT b, (leaf_mSt S s w lf m mT b) leaf_FL = lf ++ [b] := fun mT b => by
    unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have hFf : ∀ mT b, (leaf_mSt S s w lf m mT b) leaf_f = S leaf_f := fun mT b => by
    unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have xL := leaf_mSt_moveL S s w lf m (m + 1) (leaf_bit s w (m + 1)) hm
  by_cases hw : w.length ≤ m
  · -- the suffix ran out
    have hb := leaf_bit_succ_gone (s := s) hw
    have z := leaf_zeroTop_runs leaf_FL (leaf_mSt S s w lf m m (leaf_bit s w m)) (hFF m _)
    rw [leaf_mSt_FL] at z
    have e : leaf_mSt S s w lf m m 0 = leaf_mSt S s w lf m (m + 1) (leaf_bit s w (m + 1)) := by
      rw [hb]; unfold leaf_mSt
      rw [List.drop_eq_nil_of_le hw, List.drop_eq_nil_of_le (show w.length ≤ m + 1 by omega),
        List.take_of_length_le hw, List.take_of_length_le (show w.length ≤ m + 1 by omega)]
    rw [e] at z
    have x := z.iteT (i := leaf_T) (c := .empty)
      (q := .seq (.ite leaf_FL .pos leaf_cmpCase (nskip leaf_f)) (nmv leaf_T leaf_PC (by decide)))
      (by rw [hFT, List.drop_eq_nil_of_le hw]; rfl)
    exact (x.seq xL).mono (by omega)
  have hw' : m < w.length := by omega
  have xT := leaf_mSt_moveT S s w lf m (leaf_bit s w (m + 1)) hw'
  have hne : NTest.empty.eval ((leaf_mSt S s w lf m m (leaf_bit s w m)) leaf_T) = false := by
    rw [hFT, List.drop_eq_getElem_cons hw']; simp [NTest.eval, hw']
  -- the flag step
  have flag : NRuns (.ite leaf_FL .pos leaf_cmpCase (nskip leaf_f)) (leaf_mSt S s w lf m m (leaf_bit s w m))
      (leaf_mSt S s w lf m m (leaf_bit s w (m + 1))) (5 * V + 37) := by
    rcases leaf_bit_le s w m with h0 | h1
    · have hb := leaf_bit_succ_zero hm hw' h0
      rw [hb]
      rw [h0]
      exact ((nruns_skip leaf_f _).iteF (by rw [hFF]; simp)).mono (by omega)
    · have hb := leaf_bit_succ_one hm hw' h1
      rw [h1]
      have hLs : (leaf_mSt S s w lf m m 1) leaf_L = (s.drop (m + 1)).reverse ++ [s[m]] := by
        have : (leaf_mSt S s w lf m m 1) leaf_L = (s.drop m).reverse := by
          unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
        rw [this, List.drop_eq_getElem_cons hm, List.reverse_cons]
      have hTs : (leaf_mSt S s w lf m m 1) leaf_T = (w.drop (m + 1)).reverse ++ [w[m]] := by
        rw [hFT, List.drop_eq_getElem_cons hw', List.reverse_cons]
      have c₁ := leaf_cmp_runs leaf_L leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide) (by decide) (leaf_mSt S s w lf m m 1) hLs hTs
      have hsV : s[m] ≤ V := hV _ (List.getElem_mem hm)
      have hfx : (leaf_mSt S s w lf m m 1) leaf_f = S leaf_f := hFf m 1
      have back : ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]])).set leaf_f (S leaf_f) = (leaf_mSt S s w lf m m 1) := by
        rw [Lists.set_set_u, ← hfx, Lists.set_get_self]
      have hcf : ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]])) leaf_f = S leaf_f ++ [cmpRes s[m] w[m]] := by
        rw [Lists.set_same, hfx]
      have hz : NRuns (leaf_zeroTop leaf_FL) (leaf_mSt S s w lf m m 1) (leaf_mSt S s w lf m m 0) 2 := by
        have := leaf_zeroTop_runs leaf_FL (leaf_mSt S s w lf m m 1) (hFF m 1); rwa [leaf_mSt_FL] at this
      have c₂ : NRuns (caseTop leaf_f [leaf_zeroTop leaf_FL, nskip leaf_f, leaf_zeroTop leaf_FL] (nskip leaf_f))
          ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]]))
          (leaf_mSt S s w lf m m (if w[m] = s[m] then 1 else 0)) 8 := by
        rcases leaf_cmpRes_cases s[m] w[m] with r | r | r
        · have hne : ¬ w[m] = s[m] := fun e => by rw [e, cmpRes_eq] at r; cases r
          rw [if_neg hne]
          have := caseTop_runs leaf_f [leaf_zeroTop leaf_FL, nskip leaf_f, leaf_zeroTop leaf_FL] (nskip leaf_f) 0
            (by simp) ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]]))
            (S leaf_f) (by rw [hcf, r]) _ _ (by rw [back]; exact hz)
          exact this.mono (by omega)
        · have he : w[m] = s[m] := (cmpRes_one.mp r).symm
          rw [if_pos he]
          have := caseTop_runs leaf_f [leaf_zeroTop leaf_FL, nskip leaf_f, leaf_zeroTop leaf_FL] (nskip leaf_f) 1
            (by simp) ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]]))
            (S leaf_f) (by rw [hcf, r]) _ _ (by rw [back]; exact nruns_skip leaf_f (leaf_mSt S s w lf m m 1))
          exact this.mono (by omega)
        · have hne : ¬ w[m] = s[m] := fun e => by rw [e, cmpRes_eq] at r; cases r
          rw [if_neg hne]
          have := caseTop_runs leaf_f [leaf_zeroTop leaf_FL, nskip leaf_f, leaf_zeroTop leaf_FL] (nskip leaf_f) 2
            (by simp) ((leaf_mSt S s w lf m m 1).set leaf_f ((leaf_mSt S s w lf m m 1) leaf_f ++ [cmpRes s[m] w[m]]))
            (S leaf_f) (by rw [hcf, r]) _ _ (by rw [back]; exact hz)
          exact this.mono (by omega)
      rw [hb]
      have := (c₁.seq c₂)
      exact (this.iteT (by rw [hFF]; simp)).mono (by have := Nat.min_le_left s[m] w[m]; omega)
  have x := (flag.seq xT).iteF (i := leaf_T) (c := .empty) (p := leaf_zeroTop leaf_FL) hne
  exact (x.seq xL).mono (by omega)

/-- **Matching**: push `leaf_bit s w s.length` on `FL`. -/
theorem leaf_match_runs (S : Lists NK) (s w lf : List Nat) (V : Nat) (hV : ∀ v ∈ s, v ≤ V)
    (hL : S leaf_L = s.reverse) (hT : S leaf_T = w.reverse) (hPT : S leaf_PT = []) (hPC : S leaf_PC = [])
    (hF : S leaf_FL = lf) :
    NRuns leaf_matchP S (S.set leaf_FL (lf ++ [leaf_bit s w s.length]))
      (s.length * (5 * V + 45) + 3 * s.length + 3 * w.length + 6) := by
  have x₁ := nruns_pushC leaf_FL S 1
  have hb0 : leaf_bit s w 0 = 1 := by simp [leaf_bit]
  have e₀ : S.set leaf_FL (S leaf_FL ++ [1]) = leaf_mSt S s w lf 0 0 (leaf_bit s w 0) := by
    rw [hb0, hF]; unfold leaf_mSt
    leaf_ext [leaf_L, leaf_PT, leaf_T, leaf_PC, leaf_FL] [hL, hT, hPT, hPC]
  rw [e₀] at x₁
  have hFL : ∀ m, (leaf_mSt S s w lf m m (leaf_bit s w m)) leaf_L = (s.drop m).reverse := fun m => by
    unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have hl := nruns_family_const (i := leaf_L) (c := .nonempty) (p := leaf_matchBody)
    (fun m => leaf_mSt S s w lf m m (leaf_bit s w m)) s.length (5 * V + 44)
    (fun m hm => by
      rw [hFL]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp; omega)))
    (by rw [hFL]; simp)
    (fun m hm => leaf_match_step S s w lf V hV m hm)
  -- restore `L` and `T`
  let F := leaf_mSt S s w lf s.length s.length (leaf_bit s w s.length)
  have x₂ := nruns_mvAll leaf_PT leaf_L (by decide) F
  have hFPT : F leaf_PT = s := by simp only [F]; unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have hFLL : F leaf_L = [] := by simp only [F]; unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  rw [hFPT, hFLL, List.nil_append] at x₂
  let F₂ := (F.set leaf_L s.reverse).set leaf_PT []
  have x₃ := nruns_mvAll leaf_PC leaf_T (by decide) F₂
  have hF₂PC : F₂ leaf_PC = w.take s.length := by
    simp only [F₂, F]; unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  have hF₂T : F₂ leaf_T = (w.drop s.length).reverse := by
    simp only [F₂, F]; unfold leaf_mSt; simp (config := {decide := true}) [Lists.set]
  rw [hF₂PC, hF₂T] at x₃
  have hw : (w.drop s.length).reverse ++ (w.take s.length).reverse = w.reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  rw [hw] at x₃
  have e : (F₂.set leaf_T w.reverse).set leaf_PC [] = S.set leaf_FL (lf ++ [leaf_bit s w s.length]) := by
    simp only [F₂, F]; unfold leaf_mSt
    leaf_ext [leaf_L, leaf_PT, leaf_T, leaf_PC, leaf_FL] [hL, hT, hPT, hPC]
  rw [e] at x₃
  have hlen : (w.take s.length).length ≤ w.length := by rw [List.length_take]; exact Nat.min_le_right _ _
  exact (x₁.seq (hl.seq (x₂.seq x₃))).mono (by
    have : s.length * (5 * V + 44 + 1) = s.length * (5 * V + 45) := by rw [show 5 * V + 44 + 1 = 5 * V + 45 by omega]
    omega)

/-! ## The programs at one position -/

/-- The state at position `q` of the position loop over `xn`, with `cs` on `C`. -/
abbrev leaf_P (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) : Lists NK :=
  leaf_posSt S leaf_XN leaf_T leaf_Q leaf_C xn q cs

theorem leaf_P_C (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) : leaf_P S xn q cs leaf_C = cs := by
  simp [leaf_posSt, Lists.set]

theorem leaf_P_Q (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) :
    leaf_P S xn q cs leaf_Q = [q + 2] := by
  simp (config := {decide := true}) [leaf_posSt, Lists.set]

theorem leaf_P_T (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) :
    leaf_P S xn q cs leaf_T = (xn.drop (xn.length - q)).reverse := by
  simp (config := {decide := true}) [leaf_posSt, Lists.set]

/-- The stacks other than `XN T Q C` are as in `S`. -/
theorem leaf_P_other (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) (k : Fin NK) (h1 : k ≠ leaf_XN)
    (h2 : k ≠ leaf_T) (h3 : k ≠ leaf_Q) (h4 : k ≠ leaf_C) : leaf_P S xn q cs k = S k := by
  simp [leaf_posSt, Lists.set, h1, h2, h3, h4]

theorem leaf_P_push (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) (v : Nat) :
    (leaf_P S xn q cs).set leaf_C (leaf_P S xn q cs leaf_C ++ [v]) = leaf_P S xn q (cs ++ [v]) := by
  rw [leaf_P_C]; simp only [leaf_posSt, Lists.set_set_u]

theorem leaf_push1_runs (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) :
    NRuns (npushC leaf_C 1) (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [1])) 2 := by
  have := nruns_pushC leaf_C (leaf_P S xn q cs) 1
  rwa [leaf_P_push] at this

/-- Push `q + 2`. -/
def leaf_pushQ : NProg NK := .prim (.dup leaf_Q leaf_C (by decide))

theorem leaf_pushQ_runs (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) :
    NRuns leaf_pushQ (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [q + 2])) 1 := by
  have := nruns_dup leaf_Q leaf_C (by decide) (leaf_P S xn q cs) (l := []) (v := q + 2) (by rw [leaf_P_Q]; rfl)
  rwa [leaf_P_push] at this

/-- Push `q + 1`. -/
def leaf_pushQ1 : NProg NK := .seq leaf_pushQ (.prim (.dec leaf_C))

theorem leaf_pushQ1_runs (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) :
    NRuns leaf_pushQ1 (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [q + 1])) 2 := by
  have x₁ := leaf_pushQ_runs S xn q cs
  have x₂ := nruns_dec leaf_C (leaf_P S xn q (cs ++ [q + 2])) (l := cs) (v := q + 2) (by rw [leaf_P_C])
  have e : (leaf_P S xn q (cs ++ [q + 2])).set leaf_C (cs ++ [q + 2 - 1]) = leaf_P S xn q (cs ++ [q + 1]) := by
    simp only [leaf_posSt, Lists.set_set_u]; rfl
  rw [e] at x₂
  exact x₁.seq x₂

/-- At position `0` push `1`; elsewhere run `P` (the suffix is not empty). -/
def leaf_posTest (P : NProg NK) : NProg NK := .ite leaf_T .empty (npushC leaf_C 1) P

theorem leaf_posTest_runs (P : NProg NK) (S : Lists NK) (xn : List Nat) (f : Nat → Nat) (B : Nat) (hf : f 0 = 1)
    (hP : ∀ q, 0 < q → q ≤ xn.length → ∀ cs, NRuns P (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [f q])) B)
    (q : Nat) (hq : q ≤ xn.length) (cs : List Nat) :
    NRuns (leaf_posTest P) (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [f q])) (B + 3) := by
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    rw [hf]
    exact ((leaf_push1_runs S xn 0 cs).iteT (by rw [leaf_P_T]; simp [NTest.eval])).mono (by omega)
  · have hT : NTest.empty.eval (leaf_P S xn q cs leaf_T) = false := by
      rw [leaf_P_T]
      have : xn.drop (xn.length - q) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
      simp [NTest.eval, this]
    exact ((hP q hpos hq cs).iteF hT).mono (by omega)

/-- The top of the suffix at a positive position. -/
theorem leaf_P_T_top (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) (hpos : 0 < q) (hq : q ≤ xn.length) :
    leaf_P S xn q cs leaf_T = (xn.drop (xn.length - q + 1)).reverse ++ [xn.getD (xn.length - q) 0] := by
  have hlt : xn.length - q < xn.length := by omega
  rw [leaf_P_T, List.drop_eq_getElem_cons hlt, List.reverse_cons, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hlt]; rfl

theorem leaf_cmpRes_zero {a b : Nat} (h : cmpRes a b = 0) : a < b := by
  unfold cmpRes at h; split at h
  · assumption
  · split at h <;> cases h

theorem leaf_cmpRes_two {a b : Nat} (h : cmpRes a b = 2) : b < a := by
  unfold cmpRes at h; split at h
  · cases h
  · split at h
    · cases h
    · omega

/-- The other stacks at a position state, for the stacks the position programs read. -/
theorem leaf_P_AA (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) : leaf_P S xn q cs leaf_AA = S leaf_AA :=
  leaf_P_other S xn q cs _ (by decide) (by decide) (by decide) (by decide)
theorem leaf_P_BB (S : Lists NK) (xn : List Nat) (q : Nat) (cs : List Nat) : leaf_P S xn q cs leaf_BB = S leaf_BB :=
  leaf_P_other S xn q cs _ (by decide) (by decide) (by decide) (by decide)

/-! ### Epsilon and any -/

def leaf_posEps : NProg NK := leaf_pushQ
def leaf_posAny : NProg NK := leaf_posTest leaf_pushQ1

theorem leaf_posAny_runs (S : Lists NK) (xn : List Nat) (q : Nat) (hq : q ≤ xn.length) (cs : List Nat) :
    NRuns leaf_posAny (leaf_P S xn q cs) (leaf_P S xn q (cs ++ [if q = 0 then 1 else q + 1])) 5 :=
  leaf_posTest_runs leaf_pushQ1 S xn (fun q => if q = 0 then 1 else q + 1) 2 rfl
    (fun q hpos _ cs => by
      simp only [show q ≠ 0 by omega, if_false]; exact leaf_pushQ1_runs S xn q cs) q hq cs

/-! ### One character -/

def leaf_posChr : NProg NK :=
  leaf_posTest (.seq (leaf_cmp leaf_AA leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide))
    (caseTop leaf_f [npushC leaf_C 1, leaf_pushQ1, npushC leaf_C 1] (nskip leaf_f)))

theorem leaf_posChr_runs (S : Lists NK) (xn : List Nat) {la : List Nat} {A : Nat} (hA : S leaf_AA = la ++ [A])
    (q : Nat) (hq : q ≤ xn.length) (cs : List Nat) :
    NRuns leaf_posChr (leaf_P S xn q cs)
      (leaf_P S xn q (cs ++ [if q ≠ 0 ∧ xn.getD (xn.length - q) 0 = A then q + 1 else 1])) (5 * A + 31) :=
  leaf_posTest_runs _ S xn (fun q => if q ≠ 0 ∧ xn.getD (xn.length - q) 0 = A then q + 1 else 1) (5 * A + 28)
    (by simp)
    (fun q hpos hq cs => by
      have h := leaf_cmpThen_runs leaf_AA leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide) (by decide)
        (npushC leaf_C 1) leaf_pushQ1 (npushC leaf_C 1) (nskip leaf_f) (leaf_P S xn q cs)
        (leaf_P S xn q (cs ++ [if q ≠ 0 ∧ xn.getD (xn.length - q) 0 = A then q + 1 else 1]))
        (by rw [leaf_P_AA]; exact hA) (leaf_P_T_top S xn q cs hpos hq) 2
        (fun r => by
          have := leaf_cmpRes_zero r
          rw [if_neg (by omega)]; exact leaf_push1_runs S xn q cs)
        (fun r => by
          have := cmpRes_one.mp r
          rw [if_pos ⟨by omega, this.symm⟩]; exact leaf_pushQ1_runs S xn q cs)
        (fun r => by
          have := leaf_cmpRes_two r
          rw [if_neg (by omega)]; exact leaf_push1_runs S xn q cs)
      exact h.mono (by have := Nat.min_le_left A (xn.getD (xn.length - q) 0); omega))
    q hq cs

/-! ### A range -/

def leaf_rangeHi : NProg NK :=
  .seq (leaf_cmp leaf_BB leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide))
    (caseTop leaf_f [npushC leaf_C 1, leaf_pushQ1, leaf_pushQ1] (nskip leaf_f))

def leaf_posRange : NProg NK :=
  leaf_posTest (.seq (leaf_cmp leaf_AA leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide))
    (caseTop leaf_f [leaf_rangeHi, leaf_rangeHi, npushC leaf_C 1] (nskip leaf_f)))

theorem leaf_posRange_runs (S : Lists NK) (xn : List Nat) {la lb : List Nat} {A B : Nat}
    (hA : S leaf_AA = la ++ [A]) (hB : S leaf_BB = lb ++ [B]) (q : Nat) (hq : q ≤ xn.length) (cs : List Nat) :
    NRuns leaf_posRange (leaf_P S xn q cs)
      (leaf_P S xn q (cs ++ [if q ≠ 0 ∧ (A ≤ xn.getD (xn.length - q) 0 ∧ xn.getD (xn.length - q) 0 ≤ B)
        then q + 1 else 1])) (5 * A + 5 * B + 60) :=
  leaf_posTest_runs _ S xn
    (fun q => if q ≠ 0 ∧ (A ≤ xn.getD (xn.length - q) 0 ∧ xn.getD (xn.length - q) 0 ≤ B) then q + 1 else 1)
    (5 * A + 5 * B + 57) (by simp)
    (fun q hpos hq cs => by
      let d := xn.getD (xn.length - q) 0
      let out := leaf_P S xn q (cs ++ [if q ≠ 0 ∧ (A ≤ d ∧ d ≤ B) then q + 1 else 1])
      have hi : NRuns leaf_rangeHi (leaf_P S xn q cs) out (5 * B + 28) ∨ ¬ A ≤ d := by
        by_cases hAd : A ≤ d
        · left
          have h := leaf_cmpThen_runs leaf_BB leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide)
            (by decide) (npushC leaf_C 1) leaf_pushQ1 leaf_pushQ1 (nskip leaf_f) (leaf_P S xn q cs) out
            (by rw [leaf_P_BB]; exact hB) (leaf_P_T_top S xn q cs hpos hq) 2
            (fun r => by
              have := leaf_cmpRes_zero r
              simp only [out]; rw [if_neg (by omega)]; exact leaf_push1_runs S xn q cs)
            (fun r => by
              have := cmpRes_one.mp r
              simp only [out]; rw [if_pos ⟨by omega, hAd, by omega⟩]; exact leaf_pushQ1_runs S xn q cs)
            (fun r => by
              have := leaf_cmpRes_two r
              simp only [out]; rw [if_pos ⟨by omega, hAd, by omega⟩]; exact leaf_pushQ1_runs S xn q cs)
          exact h.mono (by have := Nat.min_le_left B d; omega)
        · right; exact hAd
      have h := leaf_cmpThen_runs leaf_AA leaf_T leaf_t leaf_u leaf_g leaf_f (by decide) (by decide) (by decide)
        leaf_rangeHi leaf_rangeHi (npushC leaf_C 1) (nskip leaf_f) (leaf_P S xn q cs) out
        (by rw [leaf_P_AA]; exact hA) (leaf_P_T_top S xn q cs hpos hq) (5 * B + 28)
        (fun r => by
          have := leaf_cmpRes_zero r
          rcases hi with hi | hi
          · exact hi
          · exact absurd (by omega) hi)
        (fun r => by
          have := cmpRes_one.mp r
          rcases hi with hi | hi
          · exact hi
          · exact absurd (by omega) hi)
        (fun r => by
          have := leaf_cmpRes_two r
          simp only [out]; rw [if_neg (by omega)]
          exact (leaf_push1_runs S xn q cs).mono (by omega))
      exact h.mono (by have := Nat.min_le_left A d; omega))
    q hq cs

/-! ### A literal -/

/-- Lower the top of `C` by the top of `AA` (kept). Scratch `t`. -/
def leaf_subLen : NProg NK :=
  .seq (.prim (.dup leaf_AA leaf_t (by decide)))
    (.seq (.loop leaf_t .pos (.seq (.prim (.dec leaf_t)) (.prim (.dec leaf_C)))) (.prim (.pop leaf_t)))

theorem leaf_subLen_runs (Sx : Lists NK) {la lc : List Nat} {n c : Nat} (hA : Sx leaf_AA = la ++ [n])
    (ht : Sx leaf_t = []) (hC : Sx leaf_C = lc ++ [c]) :
    NRuns leaf_subLen Sx (Sx.set leaf_C (lc ++ [c - n])) (3 * n + 4) := by
  have x₁ := nruns_dup leaf_AA leaf_t (by decide) Sx hA
  rw [ht, List.nil_append] at x₁
  let F : Nat → Lists NK := fun m => (Sx.set leaf_t [n - m]).set leaf_C (lc ++ [c - m])
  have h0 : Sx.set leaf_t [n] = F 0 := by
    simp only [F, Nat.sub_zero]; rw [← hC]; leaf_ext [leaf_t, leaf_C] []
  rw [h0] at x₁
  have hFt : ∀ m, F m leaf_t = [n - m] := fun m => by simp only [F]; simp [Lists.set, leaf_t, leaf_C]
  have hFC : ∀ m, F m leaf_C = lc ++ [c - m] := fun m => by simp only [F]; simp [Lists.set]
  have hl := nruns_family_const (i := leaf_t) (c := .pos) (p := .seq (.prim (.dec leaf_t)) (.prim (.dec leaf_C)))
    F n 2
    (fun m hm => leaf_pos_true (hFt m) (show n - m = (n - m - 1) + 1 by omega))
    (leaf_pos_false (hFt n) (Nat.sub_self n))
    (fun m hm => by
      have d₁ := nruns_dec leaf_t (F m) (l := []) (v := n - m) (by rw [hFt]; rfl)
      have d₂ := nruns_dec leaf_C ((F m).set leaf_t ([] ++ [n - m - 1])) (l := lc) (v := c - m)
        (by rw [Lists.set_ne _ _ (by decide), hFC])
      have e : ((F m).set leaf_t ([] ++ [n - m - 1])).set leaf_C (lc ++ [c - m - 1]) = F (m + 1) := by
        simp only [F, List.nil_append, Nat.sub_sub]; leaf_ext [leaf_t, leaf_C] []
      rw [e] at d₂
      exact d₁.seq d₂)
  have x₃ := nruns_pop leaf_t (F n) (l := []) (v := 0) (by rw [hFt, Nat.sub_self]; rfl)
  have e : (F n).set leaf_t [] = Sx.set leaf_C (lc ++ [c - n]) := by
    simp only [F]; leaf_ext [leaf_t, leaf_C] [ht]
  rw [e] at x₃
  exact (x₁.seq (hl.seq x₃)).mono (by omega)

def leaf_posLit : NProg NK :=
  .seq leaf_matchP (.ite leaf_FL .pos (.seq (.prim (.pop leaf_FL)) (.seq leaf_pushQ leaf_subLen))
    (.seq (.prim (.pop leaf_FL)) (npushC leaf_C 1)))

theorem leaf_posLit_runs (S : Lists NK) (xn s : List Nat) (V : Nat) (hV : ∀ v ∈ s, v ≤ V) {la : List Nat}
    (hA : S leaf_AA = la ++ [s.length]) (hL : S leaf_L = s.reverse) (hPT : S leaf_PT = []) (hPC : S leaf_PC = [])
    (hF : S leaf_FL = []) (ht : S leaf_t = []) (q : Nat) (cs : List Nat) :
    NRuns leaf_posLit (leaf_P S xn q cs)
      (leaf_P S xn q (cs ++ [if leaf_bit s (xn.drop (xn.length - q)) s.length = 1 then q + 2 - s.length else 1]))
      (s.length * (5 * V + 45) + 6 * s.length + 3 * xn.length + 18) := by
  let w := xn.drop (xn.length - q)
  let P := leaf_P S xn q cs
  have hP : ∀ k : Fin NK, k ∉ [leaf_XN, leaf_T, leaf_Q, leaf_C] → P k = S k := fun k hk => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    exact leaf_P_other S xn q cs k hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
  have x₁ := leaf_match_runs P s w [] V hV (by rw [hP _ (by decide)]; exact hL) (leaf_P_T S xn q cs)
    (by rw [hP _ (by decide)]; exact hPT) (by rw [hP _ (by decide)]; exact hPC) (by rw [hP _ (by decide)]; exact hF)
  have hFL : (P.set leaf_FL ([] ++ [leaf_bit s w s.length])) leaf_FL = [] ++ [leaf_bit s w s.length] :=
    Lists.set_same _ _ _
  have back : (P.set leaf_FL ([] ++ [leaf_bit s w s.length])).set leaf_FL [] = P := by
    rw [Lists.set_set_u, show ([] : List Nat) = P leaf_FL by rw [hP _ (by decide)]; exact hF.symm,
      Lists.set_get_self]
  have x₂ := nruns_pop leaf_FL (P.set leaf_FL ([] ++ [leaf_bit s w s.length])) hFL
  rw [back] at x₂
  have hwl : w.length ≤ xn.length := by simp [w]
  rcases leaf_bit_le s w s.length with h0 | h1
  · have x₃ := leaf_push1_runs S xn q cs
    have x := (x₂.seq x₃).iteF (i := leaf_FL) (c := .pos) (p := .seq (.prim (.pop leaf_FL)) (.seq leaf_pushQ leaf_subLen))
      (by rw [hFL, h0]; rfl)
    have hr : (if leaf_bit s w s.length = 1 then q + 2 - s.length else 1) = 1 := by rw [h0]; rfl
    rw [hr]
    exact (x₁.seq x).mono (by omega)
  · have x₃ := leaf_pushQ_runs S xn q cs
    have x₄ := leaf_subLen_runs (leaf_P S xn q (cs ++ [q + 2])) (la := la) (n := s.length) (lc := cs) (c := q + 2)
      (by rw [leaf_P_AA]; exact hA)
      (by rw [leaf_P_other S xn q _ _ (by decide) (by decide) (by decide) (by decide)]; exact ht) (leaf_P_C _ _ _ _)
    have e : (leaf_P S xn q (cs ++ [q + 2])).set leaf_C (cs ++ [q + 2 - s.length]) =
        leaf_P S xn q (cs ++ [q + 2 - s.length]) := by simp only [leaf_posSt, Lists.set_set_u]
    rw [e] at x₄
    have x := (x₂.seq (x₃.seq x₄)).iteT (i := leaf_FL) (c := .pos) (q := .seq (.prim (.pop leaf_FL)) (npushC leaf_C 1))
      (by rw [hFL, h1]; rfl)
    have hr : (if leaf_bit s w s.length = 1 then q + 2 - s.length else 1) = q + 2 - s.length := by rw [h1]; rfl
    rw [hr]
    exact (x₁.seq x).mono (by omega)

/-! ## Pushing the copies -/

/-- Copy `C` onto `EV` and add `N + 1` (the top of `NX` plus one) to the top of `EVL`. Scratch `PT t`. -/
def leaf_copyOnce : NProg NK :=
  .seq (leaf_copyMap leaf_C leaf_PT EV (by decide) (by decide) (nskip leaf_t))
    (.seq (.prim (.dup NX leaf_t (by decide))) (.seq (.prim (.inc leaf_t)) (addTo leaf_t EVL)))

theorem leaf_copyOnce_runs (Sx : Lists NK) (N e : Nat) (le : List Nat) (hPT : Sx leaf_PT = []) (ht : Sx leaf_t = [])
    (hNX : Sx NX = [N]) (hC : (Sx leaf_C).length = N + 1) (hE : Sx EVL = le ++ [e]) :
    NRuns leaf_copyOnce Sx ((Sx.set EV (Sx EV ++ Sx leaf_C)).set EVL (le ++ [e + (N + 1)])) (12 * N + 30) := by
  have x₁ := leaf_copyMap_runs leaf_C leaf_PT EV (by decide) (by decide) (by decide) (nskip leaf_t) id 2 Sx hPT
    (fun S' l v _ _ hY => by
      have := nruns_skip leaf_t S'
      rwa [show S'.set EV (l ++ [id v]) = S' from (by rw [← hY, Lists.set_get_self] : S'.set EV (l ++ [v]) = S')])
  rw [List.map_id] at x₁
  let S₁ := Sx.set EV (Sx EV ++ Sx leaf_C)
  have x₂ := nruns_dup NX leaf_t (by decide) S₁ (l := []) (v := N) (by simp only [S₁]; rw [Lists.set_ne _ _ (by decide), hNX]; rfl)
  have ht₁ : S₁ leaf_t = [] := by simp only [S₁]; rw [Lists.set_ne _ _ (by decide), ht]
  rw [ht₁, List.nil_append] at x₂
  have x₃ := nruns_inc leaf_t (S₁.set leaf_t [N]) (l := []) (v := N) (by simp)
  rw [Lists.set_set_u] at x₃
  have x₄ := nruns_addTo leaf_t EVL (by decide) (S₁.set leaf_t ([] ++ [N + 1])) (l := []) (l' := le) (a := N + 1) (b := e)
    (by simp) (by rw [Lists.set_ne _ _ (by decide)]; simp only [S₁]; rw [Lists.set_ne _ _ (by decide), hE])
  have e₁ : ((S₁.set leaf_t ([] ++ [N + 1])).set leaf_t []).set EVL (le ++ [e + (N + 1)]) =
      S₁.set EVL (le ++ [e + (N + 1)]) := by
    rw [Lists.set_set_u, ← ht₁, Lists.set_get_self]
  rw [e₁] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by rw [hC]; omega)

/-- Push `n` copies of `C` (the top of `NN`, lowered to `0`). -/
def leaf_copyN : NProg NK := .loop leaf_NN .pos (.seq (.prim (.dec leaf_NN)) leaf_copyOnce)

theorem leaf_copyN_runs (Sx : Lists NK) (n N e : Nat) (le : List Nat) (hNN : Sx leaf_NN = [n]) (hPT : Sx leaf_PT = [])
    (ht : Sx leaf_t = []) (hNX : Sx NX = [N]) (hC : (Sx leaf_C).length = N + 1) (hE : Sx EVL = le ++ [e]) :
    NRuns leaf_copyN Sx (((Sx.set leaf_NN [0]).set EV (Sx EV ++ (List.replicate n (Sx leaf_C)).flatten)).set EVL
      (le ++ [e + n * (N + 1)])) (n * (12 * N + 32) + 1) := by
  let F : Nat → Lists NK := fun m => ((Sx.set leaf_NN [n - m]).set EV (Sx EV ++ (List.replicate m (Sx leaf_C)).flatten)).set
    EVL (le ++ [e + m * (N + 1)])
  have h0 : F 0 = Sx := by
    simp only [F, Nat.sub_zero, List.replicate_zero, List.flatten_nil, List.append_nil, Nat.zero_mul, Nat.add_zero]
    rw [← hNN, ← hE]; simp only [Lists.set_get_self]
  have hFN : ∀ m, F m leaf_NN = [n - m] := fun m => by simp only [F]; leaf_get []
  have hl := nruns_family_const (i := leaf_NN) (c := .pos) (p := .seq (.prim (.dec leaf_NN)) leaf_copyOnce) F n
    (12 * N + 31)
    (fun m hm => leaf_pos_true (hFN m) (show n - m = (n - m - 1) + 1 by omega))
    (leaf_pos_false (hFN n) (Nat.sub_self n))
    (fun m hm => by
      have d₁ := nruns_dec leaf_NN (F m) (l := []) (v := n - m) (by rw [hFN]; rfl)
      have d₂ := leaf_copyOnce_runs ((F m).set leaf_NN ([] ++ [n - m - 1])) N (e + m * (N + 1)) le
        (by simp only [F]; leaf_get [hPT]) (by simp only [F]; leaf_get [ht])
        (by simp only [F]; leaf_get [hNX]) (by simp only [F]; leaf_get [hC])
        (by simp only [F]; leaf_get [])
      have e₁ : ((((F m).set leaf_NN ([] ++ [n - m - 1])).set EV (((F m).set leaf_NN ([] ++ [n - m - 1])) EV ++
          ((F m).set leaf_NN ([] ++ [n - m - 1])) leaf_C)).set EVL (le ++ [e + m * (N + 1) + (N + 1)])) = F (m + 1) := by
        have hr : (List.replicate (m + 1) (Sx leaf_C)).flatten = (List.replicate m (Sx leaf_C)).flatten ++ Sx leaf_C := by
          rw [List.replicate_succ', List.flatten_append]; simp
        simp only [F, List.nil_append, Nat.sub_sub, hr, Nat.succ_mul, Nat.add_assoc]
        leaf_ext [leaf_NN, EV, EVL] []
      rw [e₁] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [h0] at hl
  have e : F n = ((Sx.set leaf_NN [0]).set EV (Sx EV ++ (List.replicate n (Sx leaf_C)).flatten)).set EVL
      (le ++ [e + n * (N + 1)]) := by simp only [F, Nat.sub_self]
  rw [e] at hl
  exact hl.mono (by
    have : n * (12 * N + 31 + 1) = n * (12 * N + 32) := by rw [show 12 * N + 31 + 1 = 12 * N + 32 by omega]
    omega)

/-! ## Reading the item -/

/-- Push entry `k` of the item (`IT`) on `o`. Scratch `PT PC`. -/
def leaf_getP (k : Nat) (o : Fin NK) (h : leaf_PT ≠ o) : NProg NK :=
  .seq (npushC leaf_PC k) (peekAt IT leaf_PT leaf_PC o (by decide) h)

theorem leaf_getP_runs (k : Nat) (o : Fin NK) (h : leaf_PT ≠ o) (hd : [IT, leaf_PT, leaf_PC, o].Nodup)
    (Sx : Lists NK) (it : MItem) (hIT : Sx IT = encItem it) (hPT : Sx leaf_PT = []) (hk : k < 4) :
    NRuns (leaf_getP k o h) Sx (Sx.set o (Sx o ++ [(encItem it)[k]'(by simp [encItem]; omega)])) 50 := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hd'
  have hPCo : leaf_PC ≠ o := hd'.2.2.1
  have x₁ := nruns_pushC leaf_PC Sx k
  have x₂ := nruns_peekAt IT leaf_PT leaf_PC o (by decide) h hd (Sx.set leaf_PC (Sx leaf_PC ++ [k]))
    (by rw [Lists.set_ne _ _ (by decide), hPT]) (lc := Sx leaf_PC) (k := k) (by rw [Lists.set_same])
    (by rw [Lists.set_ne _ _ (by decide), hIT]; simp [encItem]; omega)
  have e : ((Sx.set leaf_PC (Sx leaf_PC ++ [k])).set leaf_PC (Sx leaf_PC)).set o
      ((Sx.set leaf_PC (Sx leaf_PC ++ [k])) o ++ [(Sx.set leaf_PC (Sx leaf_PC ++ [k]) IT)[k]'(by
        rw [Lists.set_ne _ _ (by decide), hIT]; simp [encItem]; omega)]) =
      Sx.set o (Sx o ++ [(encItem it)[k]'(by simp [encItem]; omega)]) := by
    rw [Lists.set_set_u, Lists.set_get_self]
    congr 1
    rw [Lists.set_ne _ _ (Ne.symm hPCo)]
    congr 2
    simp only [Lists.set_ne _ _ (show IT ≠ leaf_PC by decide), hIT]
  rw [e] at x₂
  have : (Sx.set leaf_PC (Sx leaf_PC ++ [k]) IT).length = 4 := by rw [Lists.set_ne _ _ (by decide), hIT]; rfl
  exact (x₁.seq x₂).mono (by rw [this]; omega)

/-! ## Building the codes -/

/-- Copy the input codes onto `XN` through `g`. -/
def leaf_copyX (g : NProg NK) : NProg NK := leaf_copyMap XS leaf_PT leaf_XN (by decide) (by decide) g

/-- Copy the input codes through `g` (each code to `h code`), then run the position loop with `posP`. -/
def leaf_build (g posP : NProg NK) : NProg NK :=
  .seq (leaf_copyX g) (leaf_posLoop leaf_XN leaf_T leaf_Q (by decide) posP)

theorem leaf_build_runs (g posP : NProg NK) (h f : Nat → Nat) (Bg Bp : Nat) (Sb : Lists NK)
    (hXN : Sb leaf_XN = []) (hC : Sb leaf_C = []) (hPT : Sb leaf_PT = []) (hT : Sb leaf_T = []) (hQ : Sb leaf_Q = [])
    (hg : ∀ (S' : Lists NK) (l : List Nat) (v : Nat), leaf_agree Sb S' [XS, leaf_PT, leaf_XN] → v ∈ Sb XS →
      S' leaf_XN = l ++ [v] → NRuns g S' (S'.set leaf_XN (l ++ [h v])) Bg)
    (hP : ∀ q, q ≤ (Sb XS).length → ∀ cs, NRuns posP (leaf_P (Sb.set leaf_XN ((Sb XS).map h)) ((Sb XS).map h) q cs)
      (leaf_P (Sb.set leaf_XN ((Sb XS).map h)) ((Sb XS).map h) q (cs ++ [f q])) Bp) :
    NRuns (leaf_build g posP) Sb (Sb.set leaf_C ((List.range ((Sb XS).length + 1)).map f))
      ((Sb XS).length * (Bg + Bp + 14) + Bp + 12) := by
  have x₁ := leaf_copyMap_runs XS leaf_PT leaf_XN (by decide) (by decide) (by decide) g h Bg Sb hPT hg
  rw [hXN, List.nil_append] at x₁
  let S' := Sb.set leaf_XN ((Sb XS).map h)
  have hS'X : S' leaf_XN = (Sb XS).map h := Lists.set_same _ _ _
  have x₂ := leaf_posLoop_runs leaf_XN leaf_T leaf_Q leaf_C (by decide) (by decide) posP f Bp S'
    (by simp only [S']; rw [Lists.set_ne _ _ (by decide), hT]) (by simp only [S']; rw [Lists.set_ne _ _ (by decide), hQ])
    (by rw [hS'X]; simp only [List.length_map]; exact fun q hq cs => hP q hq cs)
  rw [hS'X] at x₂
  have e : (S'.set leaf_XN []).set leaf_C (S' leaf_C ++ (List.range (((Sb XS).map h).length + 1)).map f) =
      Sb.set leaf_C ((List.range ((Sb XS).length + 1)).map f) := by
    simp only [S', List.length_map]
    leaf_ext [leaf_XN, leaf_C] [hXN, hC]
  rw [e] at x₂
  simp only [List.length_map] at x₂
  have hm : (Sb XS).length * (Bg + Bp + 14) = (Sb XS).length * (Bg + 4) + (Sb XS).length * (Bp + 4) +
      (Sb XS).length * 6 := by
    rw [← Nat.mul_add, ← Nat.mul_add]; congr 1; omega
  exact (x₁.seq x₂).mono (by omega)

/-! ### Copying the input codes, raw or normalized -/

def leaf_gRaw : NProg NK := nskip leaf_t
def leaf_gNorm : NProg NK := leaf_normTop leaf_XN leaf_t (by decide)

theorem leaf_gRaw_ok (Sb S' : Lists NK) (l : List Nat) (v : Nat) (_ : leaf_agree Sb S' [XS, leaf_PT, leaf_XN])
    (_ : v ∈ Sb XS) (hY : S' leaf_XN = l ++ [v]) : NRuns leaf_gRaw S' (S'.set leaf_XN (l ++ [id v])) 2 := by
  have := nruns_skip leaf_t S'
  rwa [show S'.set leaf_XN (l ++ [id v]) = S' from (by rw [← hY, Lists.set_get_self] : S'.set leaf_XN (l ++ [v]) = S')]

theorem leaf_gNorm_ok (Sb : Lists NK) (V : Nat) (ht : Sb leaf_t = []) (hV : ∀ v ∈ Sb XS, v ≤ V) (S' : Lists NK)
    (l : List Nat) (v : Nat) (hA : leaf_agree Sb S' [XS, leaf_PT, leaf_XN]) (hv : v ∈ Sb XS)
    (hY : S' leaf_XN = l ++ [v]) : NRuns leaf_gNorm S' (S'.set leaf_XN (l ++ [leaf_norm v])) (2 * V + 30) :=
  (leaf_normTop_runs leaf_XN leaf_t (by decide) S' hY (by rw [hA _ (by decide)]; exact ht)).mono
    (by have := hV v hv; omega)

theorem leaf_codes_norm (xs : List Nat) : (xs.map Char.ofNat).map Char.toNat = xs.map leaf_norm := by
  rw [List.map_map]; exact List.map_congr_left (fun v _ => leaf_toNat_ofNat v)

/-! ### Tags `0`–`3` -/

def leaf_bld0 : NProg NK := leaf_build leaf_gRaw leaf_posEps
def leaf_bld1 : NProg NK := leaf_build leaf_gRaw leaf_posAny
/-- Read argument `k` of the item onto `o` and normalize it. -/
def leaf_getNorm (k : Nat) (o : Fin NK) (h : leaf_PT ≠ o) (hot : o ≠ leaf_t) : NProg NK :=
  .seq (leaf_getP k o h) (leaf_normTop o leaf_t hot)
def leaf_bld2 : NProg NK :=
  .seq (leaf_getNorm 1 leaf_AA (by decide) (by decide)) (.seq (leaf_build leaf_gNorm leaf_posChr) (.prim (.pop leaf_AA)))
def leaf_bld3 : NProg NK :=
  .seq (leaf_getNorm 1 leaf_AA (by decide) (by decide)) (.seq (leaf_getNorm 2 leaf_BB (by decide) (by decide))
    (.seq (leaf_build leaf_gNorm leaf_posRange) (.seq (.prim (.pop leaf_AA)) (.prim (.pop leaf_BB)))))

/-- What the builders need of the state. -/
structure leaf_BuildOK (Sb : Lists NK) (it : MItem) : Prop where
  it : Sb IT = encItem it
  xn : Sb leaf_XN = []
  c : Sb leaf_C = []
  pt : Sb leaf_PT = []
  t : Sb leaf_T = []
  q : Sb leaf_Q = []
  tt : Sb leaf_t = []
  aa : Sb leaf_AA = []
  bb : Sb leaf_BB = []

theorem leaf_bld0_runs (Sb : Lists NK) (it : MItem) (h : leaf_BuildOK Sb it) :
    NRuns leaf_bld0 Sb (Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat) .eps)) ((Sb XS).length * 17 + 13) := by
  have x := leaf_build_runs leaf_gRaw leaf_posEps id (· + 2) 2 1 Sb h.xn h.c h.pt h.t h.q
    (leaf_gRaw_ok Sb) (fun q _ cs => leaf_pushQ_runs _ _ q cs)
  rw [leafCodes_eps, List.length_map]
  exact x.mono (by omega)

theorem leaf_bld1_runs (Sb : Lists NK) (it : MItem) (h : leaf_BuildOK Sb it) :
    NRuns leaf_bld1 Sb (Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat) .any)) ((Sb XS).length * 21 + 17) := by
  have x := leaf_build_runs leaf_gRaw leaf_posAny id (fun q => if q = 0 then 1 else q + 1) 2 5 Sb h.xn h.c h.pt
    h.t h.q (leaf_gRaw_ok Sb) (fun q hq cs => leaf_posAny_runs _ _ q (by simpa using hq) cs)
  rw [leafCodes_any, List.length_map]
  exact x.mono (by omega)

/-- Read an argument of the item onto an empty stack and normalize it. -/
theorem leaf_getNorm_runs (k : Nat) (o : Fin NK) (h : leaf_PT ≠ o) (hot : o ≠ leaf_t)
    (hd : [IT, leaf_PT, leaf_PC, o].Nodup) (Sx : Lists NK) (it : MItem) (hIT : Sx IT = encItem it)
    (hPT : Sx leaf_PT = []) (ht : Sx leaf_t = []) (ho : Sx o = []) (hk : k < 4) :
    NRuns (leaf_getNorm k o h hot) Sx
      (Sx.set o [leaf_norm ((encItem it)[k]'(by simp [encItem]; omega))])
      (50 + (2 * (encItem it)[k]'(by simp [encItem]; omega) + 30)) := by
  have x₁ := leaf_getP_runs k o h hd Sx it hIT hPT hk
  rw [ho, List.nil_append] at x₁
  have x₂ := leaf_normTop_runs o leaf_t hot (Sx.set o [(encItem it)[k]'(by simp [encItem]; omega)]) (l := [])
    (v := (encItem it)[k]'(by simp [encItem]; omega)) (by simp) (by rw [Lists.set_ne _ _ (Ne.symm hot)]; exact ht)
  rw [Lists.set_set_u, List.nil_append] at x₂
  exact x₁.seq x₂

theorem leaf_bld2_runs (Sb : Lists NK) (it : MItem) (h : leaf_BuildOK Sb it) (V : Nat)
    (hV : ∀ v ∈ Sb XS, v ≤ V) (ha : it.a ≤ V) :
    NRuns leaf_bld2 Sb (Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat) (.chr (Char.ofNat it.a))))
      ((Sb XS).length * (7 * V + 75) + 7 * V + 130) := by
  have x₁ := leaf_getNorm_runs 1 leaf_AA (by decide) (by decide) (by decide) Sb it h.it h.pt h.tt h.aa (by omega)
  simp only [encItem, List.getElem_cons_succ, List.getElem_cons_zero] at x₁
  let Sb₁ := Sb.set leaf_AA [leaf_norm it.a]
  have hA : leaf_norm it.a ≤ V := Nat.le_trans (leaf_norm_le _) ha
  have hX : Sb₁ XS = Sb XS := by simp only [Sb₁]; leaf_get []
  have x₂ := leaf_build_runs leaf_gNorm leaf_posChr leaf_norm
    (fun q => if q ≠ 0 ∧ ((Sb XS).map leaf_norm).getD (((Sb XS).map leaf_norm).length - q) 0 = leaf_norm it.a
      then q + 1 else 1) (2 * V + 30) (5 * leaf_norm it.a + 31) Sb₁
    (by simp only [Sb₁]; leaf_get [h.xn]) (by simp only [Sb₁]; leaf_get [h.c]) (by simp only [Sb₁]; leaf_get [h.pt])
    (by simp only [Sb₁]; leaf_get [h.t]) (by simp only [Sb₁]; leaf_get [h.q])
    (leaf_gNorm_ok Sb₁ V (by simp only [Sb₁]; leaf_get [h.tt]) (by rw [hX]; exact hV))
    (fun q hq cs => by
      rw [hX]
      exact leaf_posChr_runs _ _ (la := []) (by simp only [Sb₁]; leaf_get []) q (by rw [hX] at hq; simpa using hq) cs)
  rw [hX] at x₂
  have x₃ := nruns_pop leaf_AA (Sb₁.set leaf_C ((List.range ((Sb XS).length + 1)).map
    (fun q => if q ≠ 0 ∧ ((Sb XS).map leaf_norm).getD (((Sb XS).map leaf_norm).length - q) 0 = leaf_norm it.a
      then q + 1 else 1))) (l := []) (v := leaf_norm it.a) (by simp only [Sb₁]; leaf_get [])
  have hc : leafCodes ((Sb XS).map Char.ofNat) (.chr (Char.ofNat it.a)) = (List.range ((Sb XS).length + 1)).map
      (fun q => if q ≠ 0 ∧ ((Sb XS).map leaf_norm).getD (((Sb XS).map leaf_norm).length - q) 0 = leaf_norm it.a
        then q + 1 else 1) := by
    rw [leafCodes_chr, leaf_codes_norm, leaf_toNat_ofNat, chrC, List.length_map]
    apply List.map_congr_left; intro q _; simp only [beq_iff_eq]
  have e : (Sb₁.set leaf_C ((List.range ((Sb XS).length + 1)).map
      (fun q => if q ≠ 0 ∧ ((Sb XS).map leaf_norm).getD (((Sb XS).map leaf_norm).length - q) 0 = leaf_norm it.a
        then q + 1 else 1))).set leaf_AA [] = Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat)
          (.chr (Char.ofNat it.a))) := by
    rw [hc]; simp only [Sb₁]; leaf_ext [leaf_AA, leaf_C] [h.aa]
  rw [e] at x₃
  have hm : (Sb XS).length * (2 * V + 30 + (5 * leaf_norm it.a + 31) + 14) ≤ (Sb XS).length * (7 * V + 75) :=
    Nat.mul_le_mul_left _ (by omega)
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

theorem leaf_bld3_runs (Sb : Lists NK) (it : MItem) (h : leaf_BuildOK Sb it) (V : Nat)
    (hV : ∀ v ∈ Sb XS, v ≤ V) (ha : it.a ≤ V) (hb : it.b ≤ V) :
    NRuns leaf_bld3 Sb (Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat) (.range (Char.ofNat it.a) (Char.ofNat it.b))))
      ((Sb XS).length * (12 * V + 104) + 14 * V + 300) := by
  have x₁ := leaf_getNorm_runs 1 leaf_AA (by decide) (by decide) (by decide) Sb it h.it h.pt h.tt h.aa (by omega)
  simp only [encItem, List.getElem_cons_succ, List.getElem_cons_zero] at x₁
  let Sb₁ := Sb.set leaf_AA [leaf_norm it.a]
  have x₂ := leaf_getNorm_runs 2 leaf_BB (by decide) (by decide) (by decide) Sb₁ it
    (by simp only [Sb₁]; leaf_get [h.it]) (by simp only [Sb₁]; leaf_get [h.pt]) (by simp only [Sb₁]; leaf_get [h.tt])
    (by simp only [Sb₁]; leaf_get [h.bb]) (by omega)
  simp only [encItem, List.getElem_cons_succ, List.getElem_cons_zero] at x₂
  let Sb₂ := Sb₁.set leaf_BB [leaf_norm it.b]
  have hA : leaf_norm it.a ≤ V := Nat.le_trans (leaf_norm_le _) ha
  have hB : leaf_norm it.b ≤ V := Nat.le_trans (leaf_norm_le _) hb
  have hX : Sb₂ XS = Sb XS := by simp only [Sb₂, Sb₁]; leaf_get []
  let f : Nat → Nat := fun q => if q ≠ 0 ∧ (leaf_norm it.a ≤ ((Sb XS).map leaf_norm).getD
      (((Sb XS).map leaf_norm).length - q) 0 ∧ ((Sb XS).map leaf_norm).getD (((Sb XS).map leaf_norm).length - q) 0 ≤
        leaf_norm it.b) then q + 1 else 1
  have x₃ := leaf_build_runs leaf_gNorm leaf_posRange leaf_norm f (2 * V + 30)
    (5 * leaf_norm it.a + 5 * leaf_norm it.b + 60) Sb₂
    (by simp only [Sb₂, Sb₁]; leaf_get [h.xn]) (by simp only [Sb₂, Sb₁]; leaf_get [h.c])
    (by simp only [Sb₂, Sb₁]; leaf_get [h.pt]) (by simp only [Sb₂, Sb₁]; leaf_get [h.t])
    (by simp only [Sb₂, Sb₁]; leaf_get [h.q])
    (leaf_gNorm_ok Sb₂ V (by simp only [Sb₂, Sb₁]; leaf_get [h.tt]) (by rw [hX]; exact hV))
    (fun q hq cs => by
      rw [hX]
      exact leaf_posRange_runs _ _ (la := []) (lb := []) (by simp only [Sb₂, Sb₁]; leaf_get [])
        (by simp only [Sb₂, Sb₁]; leaf_get []) q (by rw [hX] at hq; simpa using hq) cs)
  rw [hX] at x₃
  have x₄ := nruns_pop leaf_AA (Sb₂.set leaf_C ((List.range ((Sb XS).length + 1)).map f)) (l := [])
    (v := leaf_norm it.a) (by simp only [Sb₂, Sb₁]; leaf_get [])
  have x₅ := nruns_pop leaf_BB ((Sb₂.set leaf_C ((List.range ((Sb XS).length + 1)).map f)).set leaf_AA []) (l := [])
    (v := leaf_norm it.b) (by simp only [Sb₂, Sb₁]; leaf_get [])
  have hc : leafCodes ((Sb XS).map Char.ofNat) (.range (Char.ofNat it.a) (Char.ofNat it.b)) =
      (List.range ((Sb XS).length + 1)).map f := by
    rw [leafCodes_range, leaf_codes_norm, leaf_toNat_ofNat, leaf_toNat_ofNat, chrC, List.length_map]
    apply List.map_congr_left; intro q _; simp only [f, decide_eq_true_eq, List.length_map]
  have e : (((Sb₂.set leaf_C ((List.range ((Sb XS).length + 1)).map f)).set leaf_AA []).set leaf_BB []) =
      Sb.set leaf_C (leafCodes ((Sb XS).map Char.ofNat) (.range (Char.ofNat it.a) (Char.ofNat it.b))) := by
    rw [hc]; simp only [Sb₂, Sb₁]; leaf_ext [leaf_AA, leaf_BB, leaf_C] [h.aa, h.bb]
  rw [e] at x₅
  have hm : (Sb XS).length * (2 * V + 30 + (5 * leaf_norm it.a + 5 * leaf_norm it.b + 60) + 14) ≤
      (Sb XS).length * (12 * V + 104) := Nat.mul_le_mul_left _ (by omega)
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

/-! ## Pushing the vector -/

/-- Push a new vector: `n` copies of the codes that `bld` leaves on `C` (or, for `n = 0`, run `alt`). -/
def leaf_pushVec (bld alt : NProg NK) : NProg NK :=
  .seq (.prim (.pushZ EVL)) (.seq (.ite leaf_NN .pos (.seq bld (.seq leaf_copyN (nclr leaf_C))) alt)
    (.prim (.pop leaf_NN)))

theorem leaf_pushVec_yes (bld alt : NProg NK) (Sv Sw : Lists NK) (n N : Nat) (c : List Nat) (Tb : Nat) (hn : 0 < n)
    (hNN : Sv leaf_NN = [n]) (hb : NRuns bld (Sv.set EVL (Sv EVL ++ [0])) (Sw.set leaf_C c) Tb)
    (hwN : Sw leaf_NN = [n]) (hwE : Sw EVL = Sv EVL ++ [0]) (hwPT : Sw leaf_PT = []) (hwt : Sw leaf_t = [])
    (hwNX : Sw NX = [N]) (hwC : Sw leaf_C = []) (hc : c.length = N + 1) :
    NRuns (leaf_pushVec bld alt) Sv (((Sw.set EV (Sw EV ++ (List.replicate n c).flatten)).set EVL
      (Sv EVL ++ [n * (N + 1)])).set leaf_NN []) (Tb + n * (12 * N + 32) + 2 * N + 10) := by
  have x₁ := nruns_pushZ EVL Sv
  let W := Sw.set leaf_C c
  have x₂ := leaf_copyN_runs W n N 0 (Sv EVL) (by simp only [W]; leaf_get [hwN]) (by simp only [W]; leaf_get [hwPT])
    (by simp only [W]; leaf_get [hwt]) (by simp only [W]; leaf_get [hwNX]) (by simp only [W]; leaf_get [hc])
    (by simp only [W]; leaf_get [hwE])
  have hWC : W leaf_C = c := by simp only [W]; leaf_get []
  have hWE : W EV = Sw EV := by simp only [W]; leaf_get []
  rw [hWC, hWE, Nat.zero_add] at x₂
  let W₂ := ((W.set leaf_NN [0]).set EV (Sw EV ++ (List.replicate n c).flatten)).set EVL (Sv EVL ++ [n * (N + 1)])
  have x₃ := nruns_clr leaf_C W₂
  have hW₂C : W₂ leaf_C = c := by simp only [W₂, W]; leaf_get []
  rw [hW₂C, hc] at x₃
  have x₄ := nruns_pop leaf_NN (W₂.set leaf_C []) (l := []) (v := 0) (by simp only [W₂, W]; leaf_get [])
  have e : (W₂.set leaf_C []).set leaf_NN [] = ((Sw.set EV (Sw EV ++ (List.replicate n c).flatten)).set EVL
      (Sv EVL ++ [n * (N + 1)])).set leaf_NN [] := by
    simp only [W₂, W]; leaf_ext [leaf_C, leaf_NN, EV, EVL] [hwC]
  rw [e] at x₄
  have hy := (hb.seq (x₂.seq x₃)).iteT (i := leaf_NN) (c := .pos) (q := alt)
    (leaf_pos_true (by rw [Lists.set_ne _ _ (by decide)]; exact hNN) (show n = (n - 1) + 1 by omega))
  exact (x₁.seq (hy.seq x₄)).mono (by omega)

theorem leaf_pushVec_no (bld alt : NProg NK) (Sv Sa : Lists NK) (Ta : Nat) (hNN : Sv leaf_NN = [0])
    (ha : NRuns alt (Sv.set EVL (Sv EVL ++ [0])) Sa Ta) (haN : Sa leaf_NN = [0]) :
    NRuns (leaf_pushVec bld alt) Sv (Sa.set leaf_NN []) (Ta + 3) := by
  have x₁ := nruns_pushZ EVL Sv
  have x₂ := nruns_pop leaf_NN Sa (l := []) (v := 0) haN
  have hy := ha.iteF (i := leaf_NN) (c := .pos) (p := .seq bld (.seq leaf_copyN (nclr leaf_C)))
    (leaf_pos_false (by rw [Lists.set_ne _ _ (by decide)]; exact hNN) rfl)
  exact (x₁.seq (hy.seq x₂)).mono (by omega)

/-! ## The literal -/

/-- Move the literal from `BB` (codes plus one, last on top) to `L` (normalized codes, first on top), counting its
length on `AA`. Scratch `t`. -/
def leaf_moveLit : NProg NK :=
  .loop leaf_BB .nonempty (.seq (nmv leaf_BB leaf_L (by decide)) (.seq (.prim (.dec leaf_L))
    (.seq (leaf_normTop leaf_L leaf_t (by decide)) (.prim (.inc leaf_AA)))))

theorem leaf_moveLit_runs (Sx : Lists NK) (r : List Nat) (V : Nat) (hV : ∀ v ∈ r, v ≤ V)
    (hB : Sx leaf_BB = r.map (· + 1)) (hL : Sx leaf_L = []) (hA : Sx leaf_AA = [0]) (ht : Sx leaf_t = []) :
    NRuns leaf_moveLit Sx (((Sx.set leaf_BB []).set leaf_L (r.map leaf_norm).reverse).set leaf_AA [r.length])
      (r.length * (2 * V + 38) + 1) := by
  let k := r.length
  let F : Nat → Lists NK := fun m => ((Sx.set leaf_BB ((r.take (k - m)).map (· + 1))).set leaf_L
    ((r.drop (k - m)).map leaf_norm).reverse).set leaf_AA [m]
  have h0 : F 0 = Sx := by
    simp only [F, Nat.sub_zero, k, List.take_length, List.drop_length, List.map_nil, List.reverse_nil]
    leaf_ext [leaf_BB, leaf_L, leaf_AA] [hB, hL, hA]
  have hFB : ∀ m, F m leaf_BB = (r.take (k - m)).map (· + 1) := fun m => by simp only [F]; leaf_get []
  have hl := nruns_family_const (i := leaf_BB) (c := .nonempty) (p := .seq (nmv leaf_BB leaf_L (by decide))
      (.seq (.prim (.dec leaf_L)) (.seq (leaf_normTop leaf_L leaf_t (by decide)) (.prim (.inc leaf_AA))))) F k
    (2 * V + 36)
    (fun m hm => by rw [hFB]; exact eval_nonempty_ne (List.ne_nil_of_length_pos (by simp [k]; omega)))
    (by rw [hFB]; simp)
    (fun m hm => by
      have hlt : k - m - 1 < r.length := by omega
      have hr : k - m = (k - m - 1) + 1 := by omega
      have ht' : (r.take (k - m)).map (· + 1) = (r.take (k - m - 1)).map (· + 1) ++ [r[k - m - 1] + 1] := by
        have := List.take_succ_eq_append_getElem hlt
        rw [show k - m - 1 + 1 = k - m by omega] at this
        rw [this, List.map_append]; rfl
      have d₁ := nruns_mv leaf_BB leaf_L (by decide) (F m) (by rw [hFB, ht'])
      let G := ((F m).set leaf_L ((F m) leaf_L ++ [r[k - m - 1] + 1])).set leaf_BB
        ((r.take (k - m - 1)).map (· + 1))
      have hGL : G leaf_L = ((r.drop (k - m)).map leaf_norm).reverse ++ [r[k - m - 1] + 1] := by
        simp only [G, F]; leaf_get []
      have d₂ := nruns_dec leaf_L G hGL
      have d₃ := leaf_normTop_runs leaf_L leaf_t (by decide) (G.set leaf_L (((r.drop (k - m)).map leaf_norm).reverse ++
        [r[k - m - 1] + 1 - 1])) (l := ((r.drop (k - m)).map leaf_norm).reverse) (v := r[k - m - 1] + 1 - 1)
        (by leaf_get []) (by simp only [G, F]; leaf_get [ht])
      have d₄ := nruns_inc leaf_AA ((G.set leaf_L (((r.drop (k - m)).map leaf_norm).reverse ++
        [r[k - m - 1] + 1 - 1])).set leaf_L (((r.drop (k - m)).map leaf_norm).reverse ++ [leaf_norm (r[k - m - 1] + 1 - 1)]))
        (l := []) (v := m) (by simp only [G, F]; leaf_get [])
      have hd : r.drop (k - m - 1) = r[k - m - 1] :: r.drop (k - m) := by
        have := List.drop_eq_getElem_cons hlt
        rwa [show k - m - 1 + 1 = k - m by omega] at this
      have e : ((G.set leaf_L (((r.drop (k - m)).map leaf_norm).reverse ++ [r[k - m - 1] + 1 - 1])).set leaf_L
          (((r.drop (k - m)).map leaf_norm).reverse ++ [leaf_norm (r[k - m - 1] + 1 - 1)])).set leaf_AA ([] ++ [m + 1]) =
          F (m + 1) := by
        have hk : k - (m + 1) = k - m - 1 := by omega
        simp only [G, F, hk, hd, Nat.add_sub_cancel, List.map_cons, List.reverse_cons, List.nil_append]
        leaf_ext [leaf_BB, leaf_L, leaf_AA] []
      rw [e] at d₄
      have hv : r[k - m - 1] + 1 - 1 ≤ V := by have := hV _ (List.getElem_mem hlt); omega
      exact (d₁.seq (d₂.seq (d₃.seq d₄))).mono (by omega))
  rw [h0] at hl
  have e : F k = ((Sx.set leaf_BB []).set leaf_L (r.map leaf_norm).reverse).set leaf_AA [r.length] := by
    simp only [F, Nat.sub_self, List.take_zero, List.map_nil, List.drop_zero, k]
  rw [e] at hl
  exact hl.mono (by
    have : r.length * (2 * V + 36 + 1) ≤ r.length * (2 * V + 38) := Nat.mul_le_mul_left _ (by omega)
    simp only [k]; omega)

/-- The codes of a literal, from the matching bit. -/
theorem leaf_litC_eq (xs s : List Nat) :
    litC xs s = (List.range (xs.length + 1)).map
      (fun q => if leaf_bit s (xs.drop (xs.length - q)) s.length = 1 then q + 2 - s.length else 1) := by
  unfold litC
  apply List.map_congr_left
  intro q hq
  have hq' : q ≤ xs.length := Nat.lt_succ_iff.mp (List.mem_range.mp hq)
  have hw : (xs.drop (xs.length - q)).length = q := by simp; omega
  unfold leaf_bit
  rw [hw, List.take_length]
  by_cases h : s.length ≤ q ∧ (xs.drop (xs.length - q)).take s.length = s
  · rw [if_pos h, if_pos h, if_pos rfl]; omega
  · rw [if_neg h, if_neg h]; simp

def leaf_bld4 : NProg NK := .seq leaf_moveLit (.seq (leaf_build leaf_gNorm leaf_posLit) (nclr leaf_L))

theorem leaf_bld4_runs (Sb : Lists NK) (r : List Nat) (V : Nat) (hV : ∀ v ∈ Sb XS, v ≤ V) (hr : ∀ v ∈ r, v ≤ V)
    (hB : Sb leaf_BB = r.map (· + 1)) (hA : Sb leaf_AA = [0]) (hL : Sb leaf_L = []) (ht : Sb leaf_t = [])
    (hPT : Sb leaf_PT = []) (hPC : Sb leaf_PC = []) (hF : Sb leaf_FL = []) (hXN : Sb leaf_XN = [])
    (hC : Sb leaf_C = []) (hT : Sb leaf_T = []) (hQ : Sb leaf_Q = []) :
    NRuns leaf_bld4 Sb (((Sb.set leaf_BB []).set leaf_AA [r.length]).set leaf_C
      (leafCodes ((Sb XS).map Char.ofNat) (.lit (r.map Char.ofNat))))
      (r.length * (2 * V + 38) + 1 + ((Sb XS).length * (2 * V + 30 + (r.length * (5 * V + 51) + 3 * (Sb XS).length + 18)
        + 14) + (r.length * (5 * V + 51) + 3 * (Sb XS).length + 18) + 12) + (2 * r.length + 1)) := by
  have x₁ := leaf_moveLit_runs Sb r V hr hB hL hA ht
  let sl := r.map leaf_norm
  let Sb₁ := ((Sb.set leaf_BB []).set leaf_L sl.reverse).set leaf_AA [r.length]
  have hX : Sb₁ XS = Sb XS := by simp only [Sb₁]; leaf_get []
  have hsl : sl.length = r.length := List.length_map _
  have hslV : ∀ v ∈ sl, v ≤ V := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact Nat.le_trans (leaf_norm_le u) (hr u hu)
  let f : Nat → Nat := fun q => if leaf_bit sl (((Sb XS).map leaf_norm).drop (((Sb XS).map leaf_norm).length - q))
    sl.length = 1 then q + 2 - sl.length else 1
  have x₂ := leaf_build_runs leaf_gNorm leaf_posLit leaf_norm f (2 * V + 30)
    (sl.length * (5 * V + 45) + 6 * sl.length + 3 * ((Sb XS).map leaf_norm).length + 18) Sb₁
    (by simp only [Sb₁]; leaf_get [hXN]) (by simp only [Sb₁]; leaf_get [hC]) (by simp only [Sb₁]; leaf_get [hPT])
    (by simp only [Sb₁]; leaf_get [hT]) (by simp only [Sb₁]; leaf_get [hQ])
    (leaf_gNorm_ok Sb₁ V (by simp only [Sb₁]; leaf_get [ht]) (by rw [hX]; exact hV))
    (fun q _ cs => by
      rw [hX]
      exact leaf_posLit_runs _ _ sl V hslV (la := []) (by simp only [Sb₁]; leaf_get [hsl])
        (by simp only [Sb₁]; leaf_get []) (by simp only [Sb₁]; leaf_get [hPT]) (by simp only [Sb₁]; leaf_get [hPC])
        (by simp only [Sb₁]; leaf_get [hF]) (by simp only [Sb₁]; leaf_get [ht]) q cs)
  rw [hX] at x₂
  have x₃ := nruns_clr leaf_L (Sb₁.set leaf_C ((List.range ((Sb XS).length + 1)).map f))
  have hc : leafCodes ((Sb XS).map Char.ofNat) (.lit (r.map Char.ofNat)) =
      (List.range ((Sb XS).length + 1)).map f := by
    rw [leafCodes_lit, leaf_codes_norm, leaf_codes_norm, leaf_litC_eq, List.length_map]
    simp only [f, sl, List.length_map]
  have hL₁ : (Sb₁.set leaf_C ((List.range ((Sb XS).length + 1)).map f)) leaf_L = sl.reverse := by
    simp only [Sb₁]; leaf_get []
  rw [hL₁, List.length_reverse, hsl] at x₃
  have e : (Sb₁.set leaf_C ((List.range ((Sb XS).length + 1)).map f)).set leaf_L [] =
      ((Sb.set leaf_BB []).set leaf_AA [r.length]).set leaf_C
        (leafCodes ((Sb XS).map Char.ofNat) (.lit (r.map Char.ofNat))) := by
    rw [hc]; simp only [Sb₁]; leaf_ext [leaf_BB, leaf_L, leaf_AA, leaf_C] [hL]
  rw [e] at x₃
  simp only [hsl, List.length_map] at x₂
  have hm : r.length * (5 * V + 45) + 6 * r.length = r.length * (5 * V + 51) := by
    rw [show 5 * V + 51 = (5 * V + 45) + 6 by omega, Nat.mul_add r.length (5 * V + 45) 6, Nat.mul_comm 6 r.length]
  rw [hm] at x₂
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

/-! ## Finding the literal on `LTs` -/

theorem leaf_encLits_cons (l : List Nat) (rest : List (List Nat)) :
    encLits (l :: rest) = l.map (· + 1) ++ [0] ++ encLits rest := by simp [encLits]

theorem leaf_encLits_append (a b : List (List Nat)) : encLits (a ++ b) = encLits a ++ encLits b := by
  simp [encLits, List.flatMap_append]

theorem leaf_encLits_take_succ (lt : List (List Nat)) (m : Nat) (l : List Nat) (rest : List (List Nat))
    (h : lt.drop m = l :: rest) : encLits (lt.take (m + 1)) = encLits (lt.take m) ++ (l.map (· + 1) ++ [0]) := by
  have hm : m < lt.length := by
    have := congrArg List.length h; simp at this; omega
  have hl : lt[m] = l := by
    have := List.drop_eq_getElem_cons hm; rw [h] at this; exact (List.cons.inj this).1.symm
  rw [List.take_succ_eq_append_getElem hm, leaf_encLits_append, hl]
  simp [encLits]

/-- Move the positive numbers on top of `PT` to `LTs`. -/
def leaf_skipBlk : NProg NK := .loop leaf_PT .pos (nmv leaf_PT LTs (by decide))

/-- Copy the positive numbers on top of `PT` to `BB` and move them to `LTs`. -/
def leaf_copyBlk : NProg NK := .loop leaf_PT .pos (.seq (.prim (.dup leaf_PT leaf_BB (by decide))) (nmv leaf_PT LTs (by decide)))

theorem leaf_blk_test (rest : List Nat) (u : List Nat) (m : Nat) (hm : m < u.length) :
    NTest.pos.eval (rest ++ ((u.drop m).map (· + 1)).reverse) = true := by
  rw [List.drop_eq_getElem_cons hm, List.map_cons, List.reverse_cons, ← List.append_assoc]
  exact eval_pos_succ _ _

theorem leaf_copyBlk_runs (Y : Lists NK) (rest u : List Nat) (hrest : NTest.pos.eval rest = false)
    (hP : Y leaf_PT = rest ++ (u.map (· + 1)).reverse) :
    NRuns leaf_copyBlk Y (((Y.set leaf_PT rest).set LTs (Y LTs ++ u.map (· + 1))).set leaf_BB (Y leaf_BB ++ u.map (· + 1)))
      (5 * u.length + 1) := by
  let F : Nat → Lists NK := fun m => ((Y.set leaf_PT (rest ++ ((u.drop m).map (· + 1)).reverse)).set LTs
    (Y LTs ++ (u.take m).map (· + 1))).set leaf_BB (Y leaf_BB ++ (u.take m).map (· + 1))
  have h0 : F 0 = Y := by
    simp only [F, List.drop_zero, List.take_zero, List.map_nil, List.append_nil]
    rw [← hP]; simp only [Lists.set_get_self]
  have hFP : ∀ m, F m leaf_PT = rest ++ ((u.drop m).map (· + 1)).reverse := fun m => by simp only [F]; leaf_get []
  have hl := nruns_family_const (i := leaf_PT) (c := .pos)
    (p := .seq (.prim (.dup leaf_PT leaf_BB (by decide))) (nmv leaf_PT LTs (by decide))) F u.length 4
    (fun m hm => by rw [hFP]; exact leaf_blk_test rest u m hm)
    (by rw [hFP]; simpa using hrest)
    (fun m hm => by
      have hd : rest ++ ((u.drop m).map (· + 1)).reverse = (rest ++ ((u.drop (m + 1)).map (· + 1)).reverse) ++
          [u[m] + 1] := by
        rw [List.drop_eq_getElem_cons hm, List.map_cons, List.reverse_cons, List.append_assoc]
      have d₁ := nruns_dup leaf_PT leaf_BB (by decide) (F m) (by rw [hFP, hd])
      have d₂ := nruns_mv leaf_PT LTs (by decide) ((F m).set leaf_BB ((F m) leaf_BB ++ [u[m] + 1]))
        (l := rest ++ ((u.drop (m + 1)).map (· + 1)).reverse) (v := u[m] + 1)
        (by rw [Lists.set_ne _ _ (by decide), hFP, hd])
      have hmt : (u.map (· + 1)).take m ++ [u[m] + 1] = (u.map (· + 1)).take (m + 1) := by
        rw [List.take_succ_eq_append_getElem (by simpa using hm)]; simp
      have e : ((((F m).set leaf_BB ((F m) leaf_BB ++ [u[m] + 1])).set LTs
          (((F m).set leaf_BB ((F m) leaf_BB ++ [u[m] + 1])) LTs ++ [u[m] + 1])).set leaf_PT
          (rest ++ ((u.drop (m + 1)).map (· + 1)).reverse)) = F (m + 1) := by
        simp only [F]; leaf_ext [leaf_PT, LTs, leaf_BB] [hmt]
      rw [e] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [h0] at hl
  have e : F u.length = ((Y.set leaf_PT rest).set LTs (Y LTs ++ u.map (· + 1))).set leaf_BB
      (Y leaf_BB ++ u.map (· + 1)) := by
    simp only [F, List.drop_length, List.map_nil, List.reverse_nil, List.append_nil, List.take_length]
  rw [e] at hl
  exact hl.mono (by omega)

theorem leaf_skipBlk_runs (Y : Lists NK) (rest u : List Nat) (hrest : NTest.pos.eval rest = false)
    (hP : Y leaf_PT = rest ++ (u.map (· + 1)).reverse) :
    NRuns leaf_skipBlk Y ((Y.set leaf_PT rest).set LTs (Y LTs ++ u.map (· + 1))) (3 * u.length + 1) := by
  let F : Nat → Lists NK := fun m => (Y.set leaf_PT (rest ++ ((u.drop m).map (· + 1)).reverse)).set LTs
    (Y LTs ++ (u.take m).map (· + 1))
  have h0 : F 0 = Y := by
    simp only [F, List.drop_zero, List.take_zero, List.map_nil, List.append_nil]
    rw [← hP]; simp only [Lists.set_get_self]
  have hFP : ∀ m, F m leaf_PT = rest ++ ((u.drop m).map (· + 1)).reverse := fun m => by simp only [F]; leaf_get []
  have hl := nruns_family_const (i := leaf_PT) (c := .pos) (p := nmv leaf_PT LTs (by decide)) F u.length 2
    (fun m hm => by rw [hFP]; exact leaf_blk_test rest u m hm)
    (by rw [hFP]; simpa using hrest)
    (fun m hm => by
      have hd : rest ++ ((u.drop m).map (· + 1)).reverse = (rest ++ ((u.drop (m + 1)).map (· + 1)).reverse) ++
          [u[m] + 1] := by
        rw [List.drop_eq_getElem_cons hm, List.map_cons, List.reverse_cons, List.append_assoc]
      have d₂ := nruns_mv leaf_PT LTs (by decide) (F m) (by rw [hFP, hd])
      have hmt : (u.map (· + 1)).take m ++ [u[m] + 1] = (u.map (· + 1)).take (m + 1) := by
        rw [List.take_succ_eq_append_getElem (by simpa using hm)]; simp
      have e : (((F m).set LTs ((F m) LTs ++ [u[m] + 1])).set leaf_PT
          (rest ++ ((u.drop (m + 1)).map (· + 1)).reverse)) = F (m + 1) := by
        simp only [F]; leaf_ext [leaf_PT, LTs] [hmt]
      rw [e] at d₂
      exact d₂)
  rw [h0] at hl
  have e : F u.length = (Y.set leaf_PT rest).set LTs (Y LTs ++ u.map (· + 1)) := by
    simp only [F, List.drop_length, List.map_nil, List.reverse_nil, List.append_nil, List.take_length]
  rw [e] at hl
  exact hl.mono (by omega)

/-- Skip one literal: move it with its end mark from `PT` to `LTs` (nothing when `PT` is empty). -/
def leaf_skipOne : NProg NK :=
  .seq leaf_skipBlk (.ite leaf_PT .zero (nmv leaf_PT LTs (by decide)) (nskip leaf_t))

theorem leaf_encLits_split (lt : List (List Nat)) (m : Nat) :
    encLits (lt.take m) ++ encLits (lt.drop m) = encLits lt := by
  rw [← leaf_encLits_append, List.take_append_drop]

theorem leaf_skipOne_runs (Y : Lists NK) (lt : List (List Nat)) (m : Nat)
    (hP : Y leaf_PT = (encLits (lt.drop m)).reverse) (hL : Y LTs = encLits (lt.take m)) :
    NRuns leaf_skipOne Y ((Y.set leaf_PT (encLits (lt.drop (m + 1))).reverse).set LTs (encLits (lt.take (m + 1))))
      (3 * (encLits lt).length + 6) := by
  rcases hd : lt.drop m with _ | ⟨l, rest⟩
  · have hle : lt.length ≤ m := List.drop_eq_nil_iff.mp hd
    rw [hd] at hP
    have x₁ : NRuns leaf_skipBlk Y Y 1 := nruns_loop_exit (by rw [hP]; rfl)
    have x₂ := (nruns_skip leaf_t Y).iteF (i := leaf_PT) (c := .zero) (p := nmv leaf_PT LTs (by decide))
      (by rw [hP]; rfl)
    have e : (Y.set leaf_PT (encLits (lt.drop (m + 1))).reverse).set LTs (encLits (lt.take (m + 1))) = Y := by
      rw [List.drop_eq_nil_of_le (show lt.length ≤ m + 1 by omega), List.take_of_length_le (show lt.length ≤ m + 1 by omega),
        ← List.take_of_length_le hle, ← hL]
      leaf_ext [leaf_PT, LTs] [hP, encLits]
    rw [e]
    exact (x₁.seq x₂).mono (by omega)
  · rw [hd, leaf_encLits_cons, List.reverse_append, List.reverse_append] at hP
    have x₁ := leaf_skipBlk_runs Y ((encLits rest).reverse ++ [0].reverse) l (by simp) (by rw [hP, List.append_assoc])
    have x₂ := nruns_mv leaf_PT LTs (by decide) ((Y.set leaf_PT ((encLits rest).reverse ++ [0].reverse)).set LTs
      (Y LTs ++ l.map (· + 1))) (l := (encLits rest).reverse) (v := 0) (by leaf_get [])
    have hdr : lt.drop (m + 1) = rest := by rw [← List.drop_drop, hd]; rfl
    have e : ((((Y.set leaf_PT ((encLits rest).reverse ++ [0].reverse)).set LTs (Y LTs ++ l.map (· + 1))).set LTs
        (((Y.set leaf_PT ((encLits rest).reverse ++ [0].reverse)).set LTs (Y LTs ++ l.map (· + 1))) LTs ++ [0])).set
          leaf_PT (encLits rest).reverse) =
        (Y.set leaf_PT (encLits (lt.drop (m + 1))).reverse).set LTs (encLits (lt.take (m + 1))) := by
      rw [hdr, leaf_encLits_take_succ lt m l rest hd, ← hL]
      leaf_ext [leaf_PT, LTs] []
    rw [e] at x₂
    have hlen : l.length + 1 ≤ (encLits lt).length := by
      rw [← leaf_encLits_split lt m, hd, leaf_encLits_cons]; simp; omega
    have x := x₂.iteT (i := leaf_PT) (c := .zero) (q := nskip leaf_t) (by leaf_get [])
    exact (x₁.seq x).mono (by omega)

/-- Skip `a` literals (the top of `AA`, lowered to `0`). -/
def leaf_skipLits : NProg NK := .loop leaf_AA .pos (.seq (.prim (.dec leaf_AA)) leaf_skipOne)

theorem leaf_skipLits_runs (Y : Lists NK) (lt : List (List Nat)) (a : Nat) (hA : Y leaf_AA = [a])
    (hP : Y leaf_PT = (encLits lt).reverse) (hL : Y LTs = []) :
    NRuns leaf_skipLits Y (((Y.set leaf_AA [0]).set leaf_PT (encLits (lt.drop a)).reverse).set LTs
      (encLits (lt.take a))) (a * (3 * (encLits lt).length + 8) + 1) := by
  let F : Nat → Lists NK := fun m => ((Y.set leaf_AA [a - m]).set leaf_PT (encLits (lt.drop m)).reverse).set LTs
    (encLits (lt.take m))
  have h0 : F 0 = Y := by
    simp only [F, Nat.sub_zero, List.drop_zero, List.take_zero]
    leaf_ext [leaf_AA, leaf_PT, LTs] [hA, hP, hL, encLits]
  have hFA : ∀ m, F m leaf_AA = [a - m] := fun m => by simp only [F]; leaf_get []
  have hl := nruns_family_const (i := leaf_AA) (c := .pos) (p := .seq (.prim (.dec leaf_AA)) leaf_skipOne) F a
    (3 * (encLits lt).length + 7)
    (fun m hm => leaf_pos_true (hFA m) (show a - m = (a - m - 1) + 1 by omega))
    (leaf_pos_false (hFA a) (Nat.sub_self a))
    (fun m hm => by
      have d₁ := nruns_dec leaf_AA (F m) (l := []) (v := a - m) (by rw [hFA]; rfl)
      have d₂ := leaf_skipOne_runs ((F m).set leaf_AA ([] ++ [a - m - 1])) lt m (by simp only [F]; leaf_get [])
        (by simp only [F]; leaf_get [])
      have e : ((((F m).set leaf_AA ([] ++ [a - m - 1])).set leaf_PT (encLits (lt.drop (m + 1))).reverse).set LTs
          (encLits (lt.take (m + 1)))) = F (m + 1) := by
        simp only [F, List.nil_append, Nat.sub_sub]; leaf_ext [leaf_AA, leaf_PT, LTs] []
      rw [e] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [h0] at hl
  have e : F a = ((Y.set leaf_AA [0]).set leaf_PT (encLits (lt.drop a)).reverse).set LTs (encLits (lt.take a)) := by
    simp only [F, Nat.sub_self]
  rw [e] at hl
  exact hl.mono (by
    have : a * (3 * (encLits lt).length + 7 + 1) = a * (3 * (encLits lt).length + 8) := by
      rw [show 3 * (encLits lt).length + 7 + 1 = 3 * (encLits lt).length + 8 by omega]
    omega)

/-- Having found the literal: copy it to `BB` and put the rest back on `LTs`. -/
def leaf_findYes : NProg NK :=
  .seq leaf_copyBlk (.seq (nmv leaf_PT LTs (by decide)) (nmvAll leaf_PT LTs (by decide)))

theorem leaf_findYes_runs (Y : Lists NK) (lt : List (List Nat)) (a : Nat) (l : List Nat) (rest : List (List Nat))
    (hd : lt.drop a = l :: rest) (hP : Y leaf_PT = (encLits (lt.drop a)).reverse) (hL : Y LTs = encLits (lt.take a))
    (hB : Y leaf_BB = []) :
    NRuns leaf_findYes Y (((Y.set leaf_PT []).set LTs (encLits lt)).set leaf_BB (l.map (· + 1)))
      (8 * (encLits lt).length + 6) := by
  rw [hd, leaf_encLits_cons, List.reverse_append, List.reverse_append] at hP
  have x₁ := leaf_copyBlk_runs Y ((encLits rest).reverse ++ [0].reverse) l (by simp) (by rw [hP, List.append_assoc])
  rw [hB, List.nil_append] at x₁
  let Y₁ := ((Y.set leaf_PT ((encLits rest).reverse ++ [0].reverse)).set LTs (Y LTs ++ l.map (· + 1))).set leaf_BB
    (l.map (· + 1))
  have x₂ := nruns_mv leaf_PT LTs (by decide) Y₁ (l := (encLits rest).reverse) (v := 0) (by simp only [Y₁]; leaf_get [])
  let Y₂ := (Y₁.set LTs (Y₁ LTs ++ [0])).set leaf_PT (encLits rest).reverse
  have x₃ := nruns_mvAll leaf_PT LTs (by decide) Y₂
  have hY₂P : Y₂ leaf_PT = (encLits rest).reverse := by simp only [Y₂]; leaf_get []
  rw [hY₂P, List.reverse_reverse] at x₃
  have e : (Y₂.set LTs (Y₂ LTs ++ encLits rest)).set leaf_PT [] = ((Y.set leaf_PT []).set LTs (encLits lt)).set leaf_BB
      (l.map (· + 1)) := by
    have hs := leaf_encLits_split lt a
    rw [hd, leaf_encLits_cons, ← hL] at hs
    simp only [Y₂, Y₁]
    leaf_ext [leaf_PT, LTs, leaf_BB] [← hs]
  rw [e] at x₃
  have hlen : l.length + 1 + (encLits rest).length ≤ (encLits lt).length := by
    rw [← leaf_encLits_split lt a, hd, leaf_encLits_cons]; simp; omega
  exact (x₁.seq (x₂.seq x₃)).mono (by simp only [List.length_reverse]; omega)

/-! ## What `stepT` does for a leaf -/

theorem leaf_le_sum : ∀ {l : List Nat} {v : Nat}, v ∈ l → v ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | w :: l, v, .tail _ h => by have := leaf_le_sum h; simp; omega

theorem leaf_stepT (j cap : Nat) (x : List Char) (tt ct : List (Nat × Nat)) (lt Tf : List (List Nat)) (it : MItem)
    (vs : List (List Nat)) (h : it.tag ≤ 4) :
    stepT j cap x tt ct lt Tf it vs =
      match opOf tt lt it with
      | some (.leaf e) => (List.replicate (envT j cap x.length tt ct it.ctx) (leafCodes x e)).flatten :: vs
      | _ => vs := by
  have : it.tag = 0 ∨ it.tag = 1 ∨ it.tag = 2 ∨ it.tag = 3 ∨ it.tag = 4 := by omega
  unfold stepT
  rcases this with h0 | h0 | h0 | h0 | h0 <;>
    (rw [h0]; rcases vs with _ | ⟨v, _ | ⟨w, vs⟩⟩ <;> rfl)

/-! ## The branches -/

theorem leaf_length_rep (n : Nat) (c : List Nat) : ((List.replicate n c).flatten).length = n * c.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

/-- A branch for the tags `0`–`3`, from the state with `n` on `NN`. -/
theorem leaf_branch_runs (bld : NProg NK) (S : Lists NK) (n N : Nat) (c : List Nat) (Tb : Nat)
    (hNN : S leaf_NN = []) (hPT : S leaf_PT = []) (ht : S leaf_t = []) (hC : S leaf_C = []) (hNX : S NX = [N])
    (hc : c.length = N + 1)
    (hb : 0 < n → NRuns bld ((S.set leaf_NN [n]).set EVL (S EVL ++ [0]))
      (((S.set leaf_NN [n]).set EVL (S EVL ++ [0])).set leaf_C c) Tb) :
    NRuns (leaf_pushVec bld (nskip leaf_t)) (S.set leaf_NN [n])
      ((S.set EV (S EV ++ (List.replicate n c).flatten)).set EVL (S EVL ++ [((List.replicate n c).flatten).length]))
      (Tb + n * (12 * N + 32) + 2 * N + 10) := by
  rw [leaf_length_rep, hc]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have x := leaf_pushVec_no bld (nskip leaf_t) (S.set leaf_NN [0]) ((S.set leaf_NN [0]).set EVL
      ((S.set leaf_NN [0]) EVL ++ [0])) 2 (by leaf_get []) (nruns_skip leaf_t _) (by leaf_get [])
    have e : ((S.set leaf_NN [0]).set EVL ((S.set leaf_NN [0]) EVL ++ [0])).set leaf_NN [] =
        (S.set EV (S EV ++ (List.replicate 0 c).flatten)).set EVL (S EVL ++ [0 * (N + 1)]) := by
      leaf_ext [leaf_NN, EV, EVL] [hNN]
    rw [e] at x
    exact x.mono (by omega)
  · let Sw := (S.set leaf_NN [n]).set EVL (S EVL ++ [0])
    have hE : (S.set leaf_NN [n]) EVL = S EVL := by leaf_get []
    have x := leaf_pushVec_yes bld (nskip leaf_t) (S.set leaf_NN [n]) Sw n N c Tb hpos (by leaf_get [])
      (by rw [hE]; exact hb hpos) (by simp only [Sw]; leaf_get []) (by simp only [Sw]; leaf_get [hE])
      (by simp only [Sw]; leaf_get [hPT]) (by simp only [Sw]; leaf_get [ht]) (by simp only [Sw]; leaf_get [hNX])
      (by simp only [Sw]; leaf_get [hC]) hc
    have e : ((Sw.set EV (Sw EV ++ (List.replicate n c).flatten)).set EVL ((S.set leaf_NN [n]) EVL ++ [n * (N + 1)])).set
        leaf_NN [] = (S.set EV (S EV ++ (List.replicate n c).flatten)).set EVL (S EVL ++ [n * (N + 1)]) := by
      simp only [Sw]; leaf_ext [leaf_NN, EV, EVL] [hNN]
    rw [e] at x
    exact x

/-! ## Cost arithmetic -/

theorem leaf_kM {M a k c : Nat} (ha : a ≤ M) (h : c ≤ k * M) : a * c ≤ k * (M * M) := by
  have := Nat.mul_le_mul ha h
  rw [Nat.mul_left_comm] at this; exact this

theorem leaf_kMM {M a k c : Nat} (ha : a ≤ M) (h : c ≤ k * (M * M)) : a * c ≤ k * (M * M * M) := by
  have := Nat.mul_le_mul ha h
  rw [Nat.mul_left_comm] at this; rwa [Nat.mul_assoc M M M]

theorem leaf_M_MM {M : Nat} (hM : 1 ≤ M) : M ≤ M * M := Nat.le_mul_of_pos_left M hM
theorem leaf_MM_MMM {M : Nat} (hM : 1 ≤ M) : M * M ≤ M * M * M := Nat.le_mul_of_pos_right (M * M) hM

theorem leaf_bld4_cost {M N l V : Nat} (hM : 1 ≤ M) (hN : N ≤ M) (hl : l ≤ M) (hV : V ≤ M) :
    l * (2 * V + 38) + 1 + (N * (2 * V + 30 + (l * (5 * V + 51) + 3 * N + 18) + 14) + (l * (5 * V + 51) + 3 * N + 18)
      + 12) + (2 * l + 1) ≤ 300 * (M * M * M) := by
  have h₁ : l * (2 * V + 38) ≤ 40 * (M * M) := leaf_kM hl (by omega)
  have h₂ : l * (5 * V + 51) ≤ 56 * (M * M) := leaf_kM hl (by omega)
  have hP := leaf_M_MM hM
  have hQ := leaf_MM_MMM hM
  have h₃ : N * (2 * V + 30 + (l * (5 * V + 51) + 3 * N + 18) + 14) ≤ 123 * (M * M * M) :=
    leaf_kMM hN (by omega)
  omega

/-! ## The literal branch -/

/-- Read the literal number and skip that many literals. -/
def leaf_B4front : NProg NK :=
  .seq (leaf_getP 1 leaf_AA (by decide)) (.seq (nmvAll LTs leaf_PT (by decide)) leaf_skipLits)

def leaf_B4 : NProg NK :=
  .seq leaf_B4front
    (.seq (.ite leaf_PT .nonempty (.seq leaf_findYes (leaf_pushVec leaf_bld4 (nclr leaf_BB))) (.prim (.pop leaf_NN)))
      (.prim (.pop leaf_AA)))

/-- Reading the literal number and skipping that many literals. -/
theorem leaf_B4_front (S : Lists NK) (it : MItem) (lt : List (List Nat)) (n : Nat) (hS : ScratchEmpty S)
    (hIT : S IT = encItem it) (hLT : S LTs = encLits lt) :
    NRuns leaf_B4front (S.set leaf_NN [n])
      ((((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_PT (encLits (lt.drop it.a)).reverse).set LTs
        (encLits (lt.take it.a))) (50 + (3 * (encLits lt).length + 1) + (it.a * (3 * (encLits lt).length + 8) + 1)) := by
  have hAA : S leaf_AA = [] := hS _ (by decide) (by decide)
  have hPT : S leaf_PT = [] := hS _ (by decide) (by decide)
  have x₁ := leaf_getP_runs 1 leaf_AA (by decide) (by decide) (S.set leaf_NN [n]) it (by leaf_get [hIT])
    (by leaf_get [hPT]) (by omega)
  simp only [encItem, List.getElem_cons_succ, List.getElem_cons_zero] at x₁
  let S₁ := (S.set leaf_NN [n]).set leaf_AA ((S.set leaf_NN [n]) leaf_AA ++ [it.a])
  have x₂ := nruns_mvAll LTs leaf_PT (by decide) S₁
  have h₁P : S₁ leaf_PT = [] := by simp only [S₁]; leaf_get [hPT]
  have h₁L : S₁ LTs = encLits lt := by simp only [S₁]; leaf_get [hLT]
  rw [h₁P, h₁L, List.nil_append] at x₂
  have x₃ := leaf_skipLits_runs ((S₁.set leaf_PT (encLits lt).reverse).set LTs []) lt it.a
    (by simp only [S₁]; leaf_get [hAA]) (by leaf_get []) (by leaf_get [])
  have e : ((((S₁.set leaf_PT (encLits lt).reverse).set LTs []).set leaf_AA [0]).set leaf_PT
      (encLits (lt.drop it.a)).reverse).set LTs (encLits (lt.take it.a)) =
      (((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_PT (encLits (lt.drop it.a)).reverse).set LTs
        (encLits (lt.take it.a)) := by
    simp only [S₁]; leaf_ext [leaf_AA, leaf_PT, LTs, leaf_NN] []
  rw [e] at x₃
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

/-- No literal with that number: the stack stays. -/
theorem leaf_B4_none (S : Lists NK) (it : MItem) (lt : List (List Nat)) (n : Nat) (hS : ScratchEmpty S)
    (hIT : S IT = encItem it) (hLT : S LTs = encLits lt) (hno : lt.length ≤ it.a) :
    NRuns leaf_B4 (S.set leaf_NN [n]) S
      (50 + (3 * (encLits lt).length + 1) + (it.a * (3 * (encLits lt).length + 8) + 1) + 4) := by
  have x₁ := leaf_B4_front S it lt n hS hIT hLT
  rw [List.drop_eq_nil_of_le hno, List.take_of_length_le hno] at x₁
  let Y := (((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_PT (encLits ([] : List (List Nat))).reverse).set LTs
    (encLits lt)
  have x₂ := nruns_pop leaf_NN Y (l := []) (v := n) (by simp only [Y]; leaf_get [])
  have x₃ := nruns_pop leaf_AA (Y.set leaf_NN []) (l := []) (v := 0) (by simp only [Y]; leaf_get [])
  have hNN : S leaf_NN = [] := hS _ (by decide) (by decide)
  have hAA : S leaf_AA = [] := hS _ (by decide) (by decide)
  have hPT : S leaf_PT = [] := hS _ (by decide) (by decide)
  have e : (Y.set leaf_NN []).set leaf_AA [] = S := by
    simp only [Y]; leaf_ext [leaf_NN, leaf_AA, leaf_PT, LTs] [hNN, hAA, hPT, hLT, encLits]
  rw [e] at x₃
  have x := (x₂.iteF (i := leaf_PT) (c := .nonempty) (p := .seq leaf_findYes (leaf_pushVec leaf_bld4 (nclr leaf_BB)))
    (by simp only [Y]; leaf_get [encLits])).seq x₃
  exact (x₁.seq x).mono (by omega)

theorem leaf_mem_encLits {lt : List (List Nat)} {l : List Nat} {v : Nat} (hl : l ∈ lt) (hv : v ∈ l) :
    v + 1 ∈ encLits lt := by
  simp only [encLits, List.mem_flatMap]
  exact ⟨l, hl, List.mem_append_left _ (List.mem_map_of_mem hv)⟩

theorem leaf_length_le_encLits {lt : List (List Nat)} {l : List Nat} (hl : l ∈ lt) :
    l.length ≤ (encLits lt).length := by
  induction lt with
  | nil => cases hl
  | cons k lt ih =>
    rw [leaf_encLits_cons]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    rcases List.mem_cons.mp hl with h | h
    · subst h; omega
    · have := ih h; omega

theorem leaf_litCodes_length (x : List Char) (s : List Char) : (leafCodes x (.lit s)).length = x.length + 1 := by
  rw [leafCodes_lit, litC]; simp

/-- The literal with that number exists: push `n` copies of its codes. -/
theorem leaf_B4_some (S : Lists NK) (it : MItem) (lt : List (List Nat)) (n N V M : Nat) (hS : ScratchEmpty S)
    (hIT : S IT = encItem it) (hLT : S LTs = encLits lt) (hNX : S NX = [N]) (hXl : (S XS).length = N)
    (hV : ∀ v ∈ S XS, v ≤ V) (hlit : ∀ v ∈ encLits lt, v ≤ V) (ha : it.a < lt.length)
    (hM : 1 ≤ M) (hNM : N ≤ M) (hVM : V ≤ M) (haM : it.a ≤ M) (hEM : (encLits lt).length ≤ M)
    (hnM : n * (N + 1) ≤ M) :
    NRuns leaf_B4 (S.set leaf_NN [n])
      ((S.set EV (S EV ++ (List.replicate n (leafCodes ((S XS).map Char.ofNat) (.lit (lt[it.a].map Char.ofNat)))).flatten)).set
        EVL (S EVL ++ [((List.replicate n (leafCodes ((S XS).map Char.ofNat) (.lit (lt[it.a].map Char.ofNat)))).flatten).length]))
      (600 * (M * M * M)) := by
  have hNN : S leaf_NN = [] := hS _ (by decide) (by decide)
  have hAA : S leaf_AA = [] := hS _ (by decide) (by decide)
  have hBB : S leaf_BB = [] := hS _ (by decide) (by decide)
  have hPT : S leaf_PT = [] := hS _ (by decide) (by decide)
  have hPC : S leaf_PC = [] := hS _ (by decide) (by decide)
  have hL : S leaf_L = [] := hS _ (by decide) (by decide)
  have ht : S leaf_t = [] := hS _ (by decide) (by decide)
  have hFL : S leaf_FL = [] := hS _ (by decide) (by decide)
  have hXN : S leaf_XN = [] := hS _ (by decide) (by decide)
  have hC : S leaf_C = [] := hS _ (by decide) (by decide)
  have hT : S leaf_T = [] := hS _ (by decide) (by decide)
  have hQ : S leaf_Q = [] := hS _ (by decide) (by decide)
  let l := lt[it.a]
  let c := leafCodes ((S XS).map Char.ofNat) (.lit (l.map Char.ofNat))
  have hcl : c.length = N + 1 := by simp only [c]; rw [leaf_litCodes_length, List.length_map, hXl]
  have hd : lt.drop it.a = l :: lt.drop (it.a + 1) := List.drop_eq_getElem_cons ha
  have hl : l ∈ lt := List.getElem_mem ha
  have hlE : l.length ≤ (encLits lt).length := leaf_length_le_encLits hl
  have hr : ∀ v ∈ l, v ≤ V := fun v hv => by have := hlit _ (leaf_mem_encLits hl hv); omega
  have x₁ := leaf_B4_front S it lt n hS hIT hLT
  let Y := (((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_PT (encLits (lt.drop it.a)).reverse).set LTs
    (encLits (lt.take it.a))
  have x₂ := leaf_findYes_runs Y lt it.a l (lt.drop (it.a + 1)) hd (by simp only [Y]; leaf_get [])
    (by simp only [Y]; leaf_get []) (by simp only [Y]; leaf_get [hBB])
  let Y₄ := ((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_BB (l.map (· + 1))
  have e₄ : ((Y.set leaf_PT []).set LTs (encLits lt)).set leaf_BB (l.map (· + 1)) = Y₄ := by
    simp only [Y, Y₄]; leaf_ext [leaf_PT, LTs, leaf_BB, leaf_AA, leaf_NN] [hPT, hLT]
  rw [e₄] at x₂
  have hY₄E : Y₄ EVL = S EVL := by simp only [Y₄]; leaf_get []
  have hPTne : NTest.nonempty.eval (Y leaf_PT) = true := by
    simp only [Y]; rw [show (((S.set leaf_NN [n]).set leaf_AA [0]).set leaf_PT (encLits (lt.drop it.a)).reverse).set LTs
      (encLits (lt.take it.a)) leaf_PT = (encLits (lt.drop it.a)).reverse by leaf_get [], hd, leaf_encLits_cons]
    simp [NTest.eval]
  have hrep := leaf_length_rep n c
  rw [hcl] at hrep
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- no environments: push an empty vector
    subst h0
    have xc := nruns_clr leaf_BB (Y₄.set EVL (Y₄ EVL ++ [0]))
    have hB₄ : (Y₄.set EVL (Y₄ EVL ++ [0])) leaf_BB = l.map (· + 1) := by simp only [Y₄]; leaf_get []
    rw [hB₄] at xc
    have x₃ := leaf_pushVec_no leaf_bld4 (nclr leaf_BB) Y₄ ((Y₄.set EVL (Y₄ EVL ++ [0])).set leaf_BB []) _
      (by simp only [Y₄]; leaf_get []) xc (by simp only [Y₄]; leaf_get [])
    have x₄ := nruns_pop leaf_AA (((Y₄.set EVL (Y₄ EVL ++ [0])).set leaf_BB []).set leaf_NN []) (l := []) (v := 0)
      (by simp only [Y₄]; leaf_get [])
    have e : (((Y₄.set EVL (Y₄ EVL ++ [0])).set leaf_BB []).set leaf_NN []).set leaf_AA [] =
        (S.set EV (S EV ++ (List.replicate 0 c).flatten)).set EVL (S EVL ++ [((List.replicate 0 c).flatten).length]) := by
      rw [hY₄E]; simp only [Y₄]; leaf_ext [leaf_BB, leaf_NN, leaf_AA, EV, EVL] [hBB, hNN, hAA]
    rw [e] at x₄
    have x := ((x₂.seq x₃).iteT (i := leaf_PT) (c := .nonempty) (q := .prim (.pop leaf_NN)) hPTne).seq x₄
    have hP := leaf_M_MM hM
    have hQ := leaf_MM_MMM hM
    have h₁ : it.a * (3 * (encLits lt).length + 8) ≤ 11 * (M * M) := leaf_kM haM (by omega)
    simp only [List.length_map] at x
    exact (x₁.seq x).mono (by omega)
  · -- `n` copies of the codes
    let Sb := Y₄.set EVL (Y₄ EVL ++ [0])
    have hSbX : Sb XS = S XS := by simp only [Sb, Y₄]; leaf_get []
    have xb := leaf_bld4_runs Sb l V (by rw [hSbX]; exact hV) hr (by simp only [Sb, Y₄]; leaf_get [])
      (by simp only [Sb, Y₄]; leaf_get []) (by simp only [Sb, Y₄]; leaf_get [hL]) (by simp only [Sb, Y₄]; leaf_get [ht])
      (by simp only [Sb, Y₄]; leaf_get [hPT]) (by simp only [Sb, Y₄]; leaf_get [hPC])
      (by simp only [Sb, Y₄]; leaf_get [hFL]) (by simp only [Sb, Y₄]; leaf_get [hXN])
      (by simp only [Sb, Y₄]; leaf_get [hC]) (by simp only [Sb, Y₄]; leaf_get [hT]) (by simp only [Sb, Y₄]; leaf_get [hQ])
    rw [hSbX] at xb
    let Sw := (Sb.set leaf_BB []).set leaf_AA [l.length]
    have x₃ := leaf_pushVec_yes leaf_bld4 (nclr leaf_BB) Y₄ Sw n N c _ hpos (by simp only [Y₄]; leaf_get []) xb
      (by simp only [Sw, Sb, Y₄]; leaf_get []) (by simp only [Sw, Sb]; leaf_get [])
      (by simp only [Sw, Sb, Y₄]; leaf_get [hPT]) (by simp only [Sw, Sb, Y₄]; leaf_get [ht])
      (by simp only [Sw, Sb, Y₄]; leaf_get [hNX]) (by simp only [Sw, Sb, Y₄]; leaf_get [hC]) hcl
    let Sz := ((Sw.set EV (Sw EV ++ (List.replicate n c).flatten)).set EVL (Y₄ EVL ++ [n * (N + 1)])).set leaf_NN []
    have x₄ := nruns_pop leaf_AA Sz (l := []) (v := l.length) (by simp only [Sz, Sw, Sb, Y₄]; leaf_get [])
    have e : Sz.set leaf_AA [] = (S.set EV (S EV ++ (List.replicate n c).flatten)).set EVL
        (S EVL ++ [((List.replicate n c).flatten).length]) := by
      rw [hrep]; simp only [Sz, Sw, Sb, Y₄, hY₄E]
      leaf_ext [leaf_BB, leaf_NN, leaf_AA, EV, EVL] [hBB, hNN, hAA]
    rw [e] at x₄
    have x := ((x₂.seq x₃).iteT (i := leaf_PT) (c := .nonempty) (q := .prim (.pop leaf_NN)) hPTne).seq x₄
    have hP := leaf_M_MM hM
    have hQ := leaf_MM_MMM hM
    have h₁ : it.a * (3 * (encLits lt).length + 8) ≤ 11 * (M * M) := leaf_kM haM (by omega)
    have h₂ := leaf_bld4_cost (l := l.length) hM hNM (by omega) hVM
    rw [hXl] at x
    have h₃ : n * (12 * N + 32) ≤ 32 * M := by
      have := Nat.mul_le_mul_left n (show 12 * N + 32 ≤ 32 * (N + 1) by omega)
      rw [Nat.mul_left_comm] at this; omega
    exact (x₁.seq x).mono (by omega)

/-! ## The program -/

/-- Read the tag onto `TG` and the number of environments of the context onto `NN`. -/
def leaf_front : NProg NK :=
  .seq (leaf_getP 0 leaf_TG (by decide)) (.seq (leaf_getP 3 leaf_f (by decide))
    (peekAt ENVT leaf_PT leaf_f leaf_NN (by decide) (by decide)))

/-- **The leaf items** (tags `0`–`4`). -/
def itemLeafP : NProg NK :=
  .seq leaf_front (caseTop leaf_TG [leaf_pushVec leaf_bld0 (nskip leaf_t), leaf_pushVec leaf_bld1 (nskip leaf_t),
    leaf_pushVec leaf_bld2 (nskip leaf_t), leaf_pushVec leaf_bld3 (nskip leaf_t), leaf_B4] (nskip leaf_t))

theorem leaf_front_runs (S : Lists NK) (it : MItem) (env : List Nat) (hS : ScratchEmpty S) (hIT : S IT = encItem it)
    (hE : S ENVT = env) (hk : it.ctx < env.length) :
    NRuns leaf_front S ((S.set leaf_TG [it.tag]).set leaf_NN [env[it.ctx]])
      (100 + (6 * env.length + 4 * it.ctx + 6)) := by
  have hPT : S leaf_PT = [] := hS _ (by decide) (by decide)
  have hTG : S leaf_TG = [] := hS _ (by decide) (by decide)
  have hf : S leaf_f = [] := hS _ (by decide) (by decide)
  have hNN : S leaf_NN = [] := hS _ (by decide) (by decide)
  have x₁ := leaf_getP_runs 0 leaf_TG (by decide) (by decide) S it hIT hPT (by omega)
  rw [hTG, List.nil_append] at x₁
  simp only [encItem, List.getElem_cons_zero] at x₁
  have x₂ := leaf_getP_runs 3 leaf_f (by decide) (by decide) (S.set leaf_TG [it.tag]) it (by leaf_get [hIT])
    (by leaf_get [hPT]) (by omega)
  simp only [encItem, List.getElem_cons_succ, List.getElem_cons_zero] at x₂
  let S₂ := (S.set leaf_TG [it.tag]).set leaf_f ((S.set leaf_TG [it.tag]) leaf_f ++ [it.ctx])
  have hS₂E : S₂ ENVT = env := by simp only [S₂]; leaf_get [hE]
  have x₃ := nruns_peekAt ENVT leaf_PT leaf_f leaf_NN (by decide) (by decide) (by decide) S₂
    (by simp only [S₂]; leaf_get [hPT]) (lc := []) (k := it.ctx) (by simp only [S₂]; leaf_get [hf])
    (by rw [hS₂E]; exact hk)
  have e : (S₂.set leaf_f []).set leaf_NN (S₂ leaf_NN ++ [(S₂ ENVT)[it.ctx]'(by rw [hS₂E]; exact hk)]) =
      (S.set leaf_TG [it.tag]).set leaf_NN [env[it.ctx]] := by
    have hv : (S₂ ENVT)[it.ctx]'(by rw [hS₂E]; exact hk) = env[it.ctx] := by simp only [hS₂E]
    rw [hv]; simp only [S₂]; leaf_ext [leaf_f, leaf_NN, leaf_TG] [hf, hNN]
  rw [e, hS₂E] at x₃
  exact (x₁.seq (x₂.seq x₃)).mono (by omega)

theorem leaf_codes_length (x : List Char) (e : HExp) : (leafCodes x e).length = x.length + 1 := by
  simp [leafCodes, cn_flat_base]

/-- A branch for the tags `0`–`3`, on the evaluation stack. -/
theorem leaf_case03 (S : Lists NK) (it : MItem) (vs : List (List Nat)) (n N : Nat) (bld : NProg NK) (e : HExp)
    (Tb : Nat) (hS : ScratchEmpty S) (hIT : S IT = encItem it) (hNX : S NX = [N]) (hXl : (S XS).length = N)
    (hEV : S EV = evFlat vs) (hEVL : S EVL = evLens vs)
    (hb : ∀ Sb : Lists NK, leaf_BuildOK Sb it → Sb XS = S XS →
      NRuns bld Sb (Sb.set leaf_C (leafCodes ((S XS).map Char.ofNat) e)) Tb) :
    NRuns (leaf_pushVec bld (nskip leaf_t)) (S.set leaf_NN [n])
      ((S.set EV (evFlat ((List.replicate n (leafCodes ((S XS).map Char.ofNat) e)).flatten :: vs))).set EVL
        (evLens ((List.replicate n (leafCodes ((S XS).map Char.ofNat) e)).flatten :: vs)))
      (Tb + n * (12 * N + 32) + 2 * N + 10) := by
  have hc : (leafCodes ((S XS).map Char.ofNat) e).length = N + 1 := by rw [leaf_codes_length, List.length_map, hXl]
  have x := leaf_branch_runs bld S n N (leafCodes ((S XS).map Char.ofNat) e) Tb (hS _ (by decide) (by decide))
    (hS _ (by decide) (by decide)) (hS _ (by decide) (by decide)) (hS _ (by decide) (by decide)) hNX hc
    (fun _ => hb _ ⟨by leaf_get [hIT], by leaf_get [hS leaf_XN (by decide) (by decide)],
      by leaf_get [hS leaf_C (by decide) (by decide)], by leaf_get [hS leaf_PT (by decide) (by decide)],
      by leaf_get [hS leaf_T (by decide) (by decide)], by leaf_get [hS leaf_Q (by decide) (by decide)],
      by leaf_get [hS leaf_t (by decide) (by decide)], by leaf_get [hS leaf_AA (by decide) (by decide)],
      by leaf_get [hS leaf_BB (by decide) (by decide)]⟩ (by leaf_get []))
  rw [evFlat_cons, evLens_cons, ← hEV, ← hEVL]
  exact x

/-- Branch on the tag after the front. -/
theorem leaf_dispatch (S : Lists NK) (it : MItem) (n v : Nat) (hv : it.tag = v) (hv5 : v < 5) (final : Lists NK)
    (T₁ T : Nat) (hTG : S leaf_TG = []) (hf : NRuns leaf_front S ((S.set leaf_TG [it.tag]).set leaf_NN [n]) T₁)
    (hb : NRuns ([leaf_pushVec leaf_bld0 (nskip leaf_t), leaf_pushVec leaf_bld1 (nskip leaf_t),
      leaf_pushVec leaf_bld2 (nskip leaf_t), leaf_pushVec leaf_bld3 (nskip leaf_t), leaf_B4][v]'(by simp; omega))
      (S.set leaf_NN [n]) final T) :
    NRuns itemLeafP S final (T₁ + (T + 2 * v + 2)) := by
  have e : ((S.set leaf_TG [it.tag]).set leaf_NN [n]).set leaf_TG [] = S.set leaf_NN [n] := by
    leaf_ext [leaf_TG, leaf_NN] [hTG]
  have x := caseTop_runs leaf_TG [leaf_pushVec leaf_bld0 (nskip leaf_t), leaf_pushVec leaf_bld1 (nskip leaf_t),
      leaf_pushVec leaf_bld2 (nskip leaf_t), leaf_pushVec leaf_bld3 (nskip leaf_t), leaf_B4] (nskip leaf_t) v
    (by simp; omega) ((S.set leaf_TG [it.tag]).set leaf_NN [n]) [] (by leaf_get [hv]) final T (by rw [e]; exact hb)
  exact hf.seq x

theorem leaf_cost_final {Z T : Nat} (hZ : 1 ≤ Z) (h : T ≤ 1000 * (Z * Z * Z)) : T ≤ 1000 * (Z * Z * Z * Z * Z) := by
  have h₁ : Z * Z * Z ≤ Z * Z * Z * Z := Nat.le_mul_of_pos_right _ hZ
  have h₂ : Z * Z * Z * Z ≤ Z * Z * Z * Z * Z := Nat.le_mul_of_pos_right _ hZ
  omega

/-- **The leaf items run as `stepT`.** -/
theorem itemLeafP_runs (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (htag : it.tag ≤ 4)
    (hcur : it.ctx ≤ st.ct.length) : ItemRuns itemLeafP j cap st Tf it := by
  intro S vs hE hIT hEV hEVL
  have hS := hE.scratch
  have hX : S XS = st.x := hE.xs
  have hNX : S NX = [st.x.length] := hE.nx
  have hXl : (S XS).length = st.x.length := by rw [hX]
  have hlen : (envTable j cap st.x.length st.tt st.ct).length = st.ct.length + 1 := by simp [envTable]
  have x₁ := leaf_front_runs S it _ hS hIT hE.envt (by rw [hlen]; omega)
  have hent : (envTable j cap st.x.length st.tt st.ct)[it.ctx]'(by rw [hlen]; omega) =
      envT j cap st.x.length st.tt st.ct it.ctx := by simp [envTable]
  rw [hent, hlen] at x₁
  -- the size bounds
  generalize hZ : itemZ j cap st Tf it vs = Z
  have hZdef := hZ
  simp only [itemZ] at hZdef
  have hZ2 : 2 ≤ Z := by omega
  have hNZ : st.x.length ≤ Z := by omega
  have haZ : it.a ≤ Z := by omega
  have hbZ : it.b ≤ Z := by omega
  have hcZ : it.ctx ≤ Z := by omega
  have hctZ : st.ct.length ≤ Z := by omega
  have hEZ : (encLits st.lt).length ≤ Z := by omega
  have hxZ : ∀ v ∈ S XS, v ≤ Z := fun v hv => by rw [hX] at hv; have := leaf_le_sum hv; omega
  have hlZ : ∀ v ∈ encLits st.lt, v ≤ Z := fun v hv => by have := leaf_le_sum hv; omega
  have hres : ((evFlat (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs))).length ≤ Z := by omega
  have hP := leaf_M_MM (M := Z) (by omega)
  have hQ := leaf_MM_MMM (M := Z) (by omega)
  unfold itemCost
  rw [hZ]
  -- the result, by the tag
  have hstep := leaf_stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs htag
  simp only [List.length_map] at hstep
  rw [hstep] at hres ⊢
  rw [show List.map Char.ofNat st.x = List.map Char.ofNat (S XS) by rw [hX]] at hres ⊢
  have hTG : S leaf_TG = [] := hS _ (by decide) (by decide)
  generalize envT j cap st.x.length st.tt st.ct it.ctx = n at x₁ hres ⊢
  -- the copies fit in the result
  have hcopy : ∀ e : HExp, (evFlat ((List.replicate n (leafCodes ((S XS).map Char.ofNat) e)).flatten :: vs)).length ≤ Z →
      n * (12 * st.x.length + 32) ≤ 32 * Z := fun e h => by
    rw [evFlat_cons, List.length_append, leaf_length_rep, leaf_codes_length, List.length_map, hXl] at h
    have := Nat.mul_le_mul_left n (show 12 * st.x.length + 32 ≤ 32 * (st.x.length + 1) by omega)
    rw [Nat.mul_left_comm] at this; omega
  have hT₁ : 100 + (6 * (st.ct.length + 1) + 4 * it.ctx + 6) ≤ 20 * Z + 112 := by omega
  have hv : it.tag = 0 ∨ it.tag = 1 ∨ it.tag = 2 ∨ it.tag = 3 ∨ it.tag = 4 := by omega
  rcases hv with h0 | h0 | h0 | h0 | h0
  · simp only [opOf, h0] at hres ⊢
    have hb := leaf_case03 S it vs n st.x.length leaf_bld0 .eps _ hS hIT hNX hXl hEV hEVL
      (fun Sb hok hSX => by have := leaf_bld0_runs Sb it hok; rwa [hSX] at this)
    have x := leaf_dispatch S it n 0 h0 (by omega) _ _ _ hTG x₁ hb
    have := hcopy _ hres
    have h₁ : st.x.length * 17 ≤ 17 * (Z * Z) := leaf_kM hNZ (by omega)
    exact x.mono (leaf_cost_final (by omega) (by rw [hXl]; omega))
  · simp only [opOf, h0] at hres ⊢
    have hb := leaf_case03 S it vs n st.x.length leaf_bld1 .any _ hS hIT hNX hXl hEV hEVL
      (fun Sb hok hSX => by have := leaf_bld1_runs Sb it hok; rwa [hSX] at this)
    have x := leaf_dispatch S it n 1 h0 (by omega) _ _ _ hTG x₁ hb
    have := hcopy _ hres
    exact x.mono (leaf_cost_final (by omega) (by rw [hXl]; omega))
  · simp only [opOf, h0] at hres ⊢
    have hb := leaf_case03 S it vs n st.x.length leaf_bld2 (.chr (Char.ofNat it.a)) _ hS hIT hNX hXl hEV hEVL
      (fun Sb hok hSX => by
        have := leaf_bld2_runs Sb it hok Z (by rw [hSX]; exact hxZ) haZ; rwa [hSX] at this)
    have x := leaf_dispatch S it n 2 h0 (by omega) _ _ _ hTG x₁ hb
    have := hcopy _ hres
    have h₁ : (S XS).length * (7 * Z + 75) ≤ 82 * (Z * Z) := leaf_kM (by omega) (by omega)
    exact x.mono (leaf_cost_final (by omega) (by rw [hXl] at h₁ ⊢; omega))
  · simp only [opOf, h0] at hres ⊢
    have hb := leaf_case03 S it vs n st.x.length leaf_bld3 (.range (Char.ofNat it.a) (Char.ofNat it.b)) _ hS hIT hNX
      hXl hEV hEVL
      (fun Sb hok hSX => by
        have := leaf_bld3_runs Sb it hok Z (by rw [hSX]; exact hxZ) haZ hbZ; rwa [hSX] at this)
    have x := leaf_dispatch S it n 3 h0 (by omega) _ _ _ hTG x₁ hb
    have := hcopy _ hres
    have h₁ : (S XS).length * (12 * Z + 104) ≤ 116 * (Z * Z) := leaf_kM (by omega) (by omega)
    exact x.mono (leaf_cost_final (by omega) (by rw [hXl] at h₁ ⊢; omega))
  · simp only [opOf, h0, litOf] at hres ⊢
    by_cases ha : it.a < st.lt.length
    · rw [List.getElem?_eq_getElem ha] at hres ⊢
      simp only [Option.map_some] at hres ⊢
      have hnM : n * (st.x.length + 1) ≤ Z := by
        rw [evFlat_cons, List.length_append, leaf_length_rep, leaf_codes_length, List.length_map, hXl] at hres
        omega
      have hb := leaf_B4_some S it st.lt n st.x.length Z Z hS hIT hE.lt hNX hXl hxZ hlZ ha (by omega) hNZ
        (Nat.le_refl _) haZ hEZ hnM
      rw [evFlat_cons, evLens_cons, ← hEV, ← hEVL]
      have x := leaf_dispatch S it n 4 h0 (by omega) _ _ _ hTG x₁ hb
      exact x.mono (leaf_cost_final (by omega) (by omega))
    · rw [List.getElem?_eq_none (by omega)] at hres ⊢
      simp only [Option.map_none] at hres ⊢
      have hb := leaf_B4_none S it st.lt n hS hIT hE.lt (by omega)
      have e : (S.set EV (evFlat vs)).set EVL (evLens vs) = S := by
        rw [← hEV, ← hEVL, Lists.set_get_self, Lists.set_get_self]
      rw [e]
      have x := leaf_dispatch S it n 4 h0 (by omega) _ _ _ hTG x₁ hb
      have h₁ : it.a * (3 * (encLits st.lt).length + 8) ≤ 11 * (Z * Z) := leaf_kM haZ (by omega)
      exact x.mono (leaf_cost_final (by omega) (by omega))

end Shallot.MacroPeg.Mach
