import PalPeg.EndToEnd2
import PalPeg.GSDecompose2Work

/-!
# 2 記号への relabeling による `PassPeriodSum` の適用

`EndToEnd2.PassPeriodSum k C₁` は `x : List (Fin 2)` について述べられているが、
`PrepInstance.prepInstance` が要求する仮定は、機械アルファベット `Fin sc` に埋め込まれた
（実際には高々 2 記号しか使わない）語 `y : List (Fin sc)` についてのものである。

ここでは：

* `firstInner` / `firstOuter` / `extendReach` / `stripLoop2` / `stripLoop2Periods` が、
  リストの要素上でだけ単射な relabeling `f` の下で不変であること（`_map` 系の補題。
  これらの関数はすべて `List.getElem?` の等号判定だけを通じてリストを見るので、
  リストの要素上での単射性で十分）、
* その結果として、2 記号しか使わない `y : List (Fin sc)` に対して `PassPeriodSum` の仮定を
  そのまま適用できること（`passPeriodSum_of_two_symbols`）、
* さらに `Fin 2 ↪ Fin sc` の埋め込みの像に収まる語に対する便利版
  （`passPeriodSum_of_subset`）

を示す。
-/

namespace PalPeg

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
set_option linter.unusedSectionVars false

/-! ## `getElem?` と（リスト要素上で）単射な写像 -/

/-- `f` がリスト `v` の要素上で単射なら、`v.map f` の `getElem?` による等号判定は
`v` 自身のそれと一致する。 -/
private theorem getElem?_map_eq_iff {f : α → β} {v : List α}
    (hf : Set.InjOn f {z | z ∈ v}) (i j : ℕ) :
    (v.map f)[i]? = (v.map f)[j]? ↔ v[i]? = v[j]? := by
  rw [List.getElem?_map, List.getElem?_map]
  match hi : v[i]?, hj : v[j]? with
  | none, none => simp
  | none, some b => simp
  | some a, none => simp
  | some a, some b =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro h
      have ha : a ∈ v := List.mem_of_getElem? hi
      have hb : b ∈ v := List.mem_of_getElem? hj
      exact hf ha hb h
    · intro h; rw [h]

/-- `Set.InjOn` は `List.drop` で保たれる（`x.drop s` の要素は `x` の要素）。 -/
private theorem injOn_of_mem_drop {f : α → β} {x : List α}
    (hf : Set.InjOn f {z | z ∈ x}) (s : ℕ) : Set.InjOn f {z | z ∈ x.drop s} :=
  fun _ hz1 _ hz2 heq => hf (List.mem_of_mem_drop hz1) (List.mem_of_mem_drop hz2) heq

/-! ## `firstInner` の relabeling 不変性 -/

theorem firstInner_map {f : α → β} {v : List α} (hf : Set.InjOn f {z | z ∈ v}) (k p : ℕ) :
    ∀ (fuel q : ℕ), firstInner (v.map f) k p fuel q = firstInner v k p fuel q := by
  intro fuel
  induction fuel with
  | zero => intro q; rfl
  | succ fuel ih =>
    intro q
    have hlen : (v.map f).length = v.length := by simp
    have heq := getElem?_map_eq_iff hf q (p + q)
    by_cases hc : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
    · have hc' : p + q < (v.map f).length ∧ q < (k - 1) * p ∧
          (v.map f)[q]? = (v.map f)[p + q]? :=
        ⟨by rw [hlen]; exact hc.1, hc.2.1, heq.mpr hc.2.2⟩
      rw [firstInner, if_pos hc', firstInner, if_pos hc, ih]
    · have hc' : ¬ (p + q < (v.map f).length ∧ q < (k - 1) * p ∧
          (v.map f)[q]? = (v.map f)[p + q]?) := by
        rw [hlen, heq]; exact hc
      rw [firstInner, if_neg hc', firstInner, if_neg hc]

/-! ## `firstOuter` の relabeling 不変性 -/

theorem firstOuter_map {f : α → β} {v : List α} (hf : Set.InjOn f {z | z ∈ v}) (k bound : ℕ) :
    ∀ (fuel p : ℕ), firstOuter (v.map f) k bound fuel p = firstOuter v k bound fuel p := by
  intro fuel
  induction fuel with
  | zero => intro p; rfl
  | succ fuel ih =>
    intro p
    have hlen : (v.map f).length = v.length := by simp
    by_cases hc : p < v.length ∧ p < bound
    · have hc' : p < (v.map f).length ∧ p < bound := by rw [hlen]; exact hc
      rw [firstOuter, if_pos hc', hlen, firstOuter, if_pos hc]
      have hinner := firstInner_map hf k p (v.length + 1) 0
      rw [hinner]
      by_cases hq : firstInner v k p (v.length + 1) 0 = (k - 1) * p
      · rw [if_pos hq, if_pos hq]
      · rw [if_neg hq, if_neg hq, ih]
    · have hc' : ¬ (p < (v.map f).length ∧ p < bound) := by rw [hlen]; exact hc
      rw [firstOuter, if_neg hc', firstOuter, if_neg hc]

/-! ## `extendReach` の relabeling 不変性 -/

theorem extendReach_map {f : α → β} {v : List α} (hf : Set.InjOn f {z | z ∈ v}) (p : ℕ) :
    ∀ (fuel r : ℕ), extendReach (v.map f) p fuel r = extendReach v p fuel r := by
  intro fuel
  induction fuel with
  | zero => intro r; rfl
  | succ fuel ih =>
    intro r
    have hlen : (v.map f).length = v.length := by simp
    have heq := getElem?_map_eq_iff hf (r - p) r
    by_cases hc : r < v.length ∧ v[r - p]? = v[r]?
    · have hc' : r < (v.map f).length ∧ (v.map f)[r - p]? = (v.map f)[r]? :=
        ⟨by rw [hlen]; exact hc.1, heq.mpr hc.2⟩
      rw [extendReach, if_pos hc', extendReach, if_pos hc, ih]
    · have hc' : ¬ (r < (v.map f).length ∧ (v.map f)[r - p]? = (v.map f)[r]?) := by
        rw [hlen, heq]; exact hc
      rw [extendReach, if_neg hc', extendReach, if_neg hc]

/-! ## `stripLoop2` の relabeling 不変性 -/

theorem stripLoop2_map {f : α → β} {x : List α} (hf : Set.InjOn f {z | z ∈ x}) (k bound : ℕ) :
    ∀ (fuel s : ℕ), stripLoop2 (x.map f) k bound fuel s = stripLoop2 x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    have hdrop : (x.map f).drop s = (x.drop s).map f := (List.map_drop).symm
    have hfo := firstOuter_map (injOn_of_mem_drop hf s) k bound (x.length + 1) 1
    have hlen : (x.map f).length = x.length := by simp
    rcases hv : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only [stripLoop2, hdrop, hlen, hfo, hv]
    · have her : extendReach ((x.drop s).map f) p (x.length + 1) (k * p)
          = extendReach (x.drop s) p (x.length + 1) (k * p) :=
        extendReach_map (injOn_of_mem_drop hf s) p (x.length + 1) (k * p)
      simp only [stripLoop2, hdrop, hlen, hfo, hv, her, ih]

/-! ## `stripLoop2Periods` の relabeling 不変性 -/

theorem stripLoop2Periods_map {f : α → β} {x : List α} (hf : Set.InjOn f {z | z ∈ x})
    (k bound : ℕ) :
    ∀ (fuel s : ℕ),
      stripLoop2Periods (x.map f) k bound fuel s = stripLoop2Periods x k bound fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    have hdrop : (x.map f).drop s = (x.drop s).map f := (List.map_drop).symm
    have hfo := firstOuter_map (injOn_of_mem_drop hf s) k bound (x.length + 1) 1
    have hlen : (x.map f).length = x.length := by simp
    rcases hv : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
    · simp only [stripLoop2Periods, hdrop, hlen, hfo, hv]
    · have her : extendReach ((x.drop s).map f) p (x.length + 1) (k * p)
          = extendReach (x.drop s) p (x.length + 1) (k * p) :=
        extendReach_map (injOn_of_mem_drop hf s) p (x.length + 1) (k * p)
      simp only [stripLoop2Periods, hdrop, hlen, hfo, hv, her, ih]

/-! ## `y` が高々 2 記号しか使わないときの `PassPeriodSum` の適用 -/

/-- `y` の要素が `{a, b'}` の 2 値に収まるなら、それを `Fin 2` へ relabel した写像は
`y` の要素上で単射（`a ≠ b'` のとき）。 -/
private theorem injOn_two_symbols {sc : ℕ} {a b' : Fin sc} (hab : a ≠ b') (y : List (Fin sc))
    (hy : ∀ c ∈ y, c = a ∨ c = b') :
    Set.InjOn (fun c : Fin sc => if c = a then (0 : Fin 2) else 1) {z | z ∈ y} := by
  intro z1 hz1 z2 hz2 heq
  simp only [Set.mem_setOf_eq] at hz1 hz2
  dsimp only at heq
  by_cases h1 : z1 = a <;> by_cases h2 : z2 = a
  · rw [h1, h2]
  · exfalso
    rw [if_pos h1, if_neg h2] at heq
    exact absurd heq (by decide)
  · exfalso
    rw [if_neg h1, if_pos h2] at heq
    exact absurd heq (by decide)
  · have hz1' : z1 = b' := (hy z1 hz1).resolve_left h1
    have hz2' : z2 = b' := (hy z2 hz2).resolve_left h2
    rw [hz1', hz2']

/-- `PassPeriodSum k C₁`（`Fin 2` 上のもの）から、高々 2 記号しか使わない
`y : List (Fin sc)` に対する `stripLoop2Periods` の同じ上界が従う。 -/
theorem passPeriodSum_of_two_symbols {sc k C₁ : ℕ} (hsum : EndToEnd2.PassPeriodSum k C₁)
    (y : List (Fin sc)) (a b' : Fin sc) (hy : ∀ c ∈ y, c = a ∨ c = b') (b s : ℕ) :
    stripLoop2Periods y k b (y.length + 1) s ≤ C₁ * b := by
  by_cases hab : a = b'
  · -- 1 記号しか使わない場合：定数写像は `y` の要素上で自動的に単射
    have hy0 : ∀ c ∈ y, c = a := by
      intro c hc; rcases hy c hc with h | h
      · exact h
      · rw [← hab] at h; exact h
    have hInj : Set.InjOn (fun _ : Fin sc => (0 : Fin 2)) {z | z ∈ y} := by
      intro z1 hz1 z2 hz2 _
      simp only [Set.mem_setOf_eq] at hz1 hz2
      exact (hy0 z1 hz1).trans (hy0 z2 hz2).symm
    have hmap := stripLoop2Periods_map hInj k b (y.length + 1) s
    have hlen : (y.map (fun _ : Fin sc => (0 : Fin 2))).length = y.length := by simp
    have := hsum (y.map (fun _ : Fin sc => (0 : Fin 2))) b s
    rw [hlen] at this
    rw [hmap] at this
    exact this
  · have hInj := injOn_two_symbols hab y hy
    have hmap := stripLoop2Periods_map hInj k b (y.length + 1) s
    have hlen : (y.map (fun c : Fin sc => if c = a then (0 : Fin 2) else 1)).length
        = y.length := by simp
    have := hsum (y.map (fun c : Fin sc => if c = a then (0 : Fin 2) else 1)) b s
    rw [hlen] at this
    rw [hmap] at this
    exact this

/-- 便利版：`y` の記号が `Fin 2 ↪ Fin sc` の像に収まっているときの `passPeriodSum_of_two_symbols`。 -/
theorem passPeriodSum_of_subset {sc k C₁ : ℕ} (hsum : EndToEnd2.PassPeriodSum k C₁)
    (e : Fin 2 ↪ Fin sc) (y : List (Fin sc)) (hy : ∀ c ∈ y, c = e 0 ∨ c = e 1) (b s : ℕ) :
    stripLoop2Periods y k b (y.length + 1) s ≤ C₁ * b :=
  passPeriodSum_of_two_symbols hsum y (e 0) (e 1) hy b s

end PalPeg

