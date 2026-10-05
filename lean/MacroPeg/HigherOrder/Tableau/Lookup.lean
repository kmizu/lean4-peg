import MacroPeg.HigherOrder.Tableau.Grammar

/-!
# Where the rules of `gT M K` are

The level rules come first (`gT_levels`: the grammar contains the levels `0, …, K`), then the tableau rules, each at
the number given in `Grammar.lean`.
-/

namespace Shallot.MacroPeg.Tableau

open Complexity (TM)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels

/-! ## Uniform concatenations -/

theorem getElem?_flatMap_uniform {α β : Type} (f : α → List β) (n : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = n) → ∀ a b, b < n → (ha : a < l.length) →
      (l.flatMap f)[a * n + b]? = (f l[a])[b]?
  | [], _, _, _, _, ha => by simp at ha
  | x :: l, hf, 0, b, hb, _ => by
    simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getElem?_append_left (by rw [hf x List.mem_cons_self]; exact hb)]
  | x :: l, hf, a + 1, b, hb, ha => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by rw [hf x List.mem_cons_self, Nat.succ_mul]; omega),
      hf x List.mem_cons_self, show (a + 1) * n + b - n = a * n + b by rw [Nat.succ_mul]; omega]
    exact getElem?_flatMap_uniform f n l (fun y hy => hf y (List.mem_cons_of_mem _ hy)) a b hb (by simpa using ha)

theorem length_flatMap_uniform {α β : Type} (f : α → List β) (n : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = n) → (l.flatMap f).length = l.length * n
  | [], _ => by simp
  | x :: l, hf => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
      hf x List.mem_cons_self, length_flatMap_uniform f n l (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    omega

/-! ## The level rules -/

theorem length_blockRules (i : Nat) : (blockRules i).length = 12 := rfl

theorem length_levels (K : Nat) : (level1Rules ++ (List.range K).flatMap blockRules).length = base K := by
  rw [List.length_append, length_flatMap_uniform _ 12 _ (fun i _ => length_blockRules i)]
  simp [level1Rules, base, Nat.mul_comm]

section Levels

variable {kt : Nat} (M : TM kt) (K : Nat)

theorem gT_levels : HasLevels (gT M K) K := by
  refine ⟨fun i hi => ?_, fun i hi r hr => ?_⟩
  · simp only [gT]
    rw [List.append_assoc, List.getElem?_append_left (by simpa [level1Rules] using hi)]
  · simp only [gT]
    have hlen := length_flatMap_uniform blockRules 12 (List.range K) (fun i _ => length_blockRules i)
    rw [List.getElem?_append_left (by rw [length_levels]; unfold base; omega),
      List.getElem?_append_right (by simp [level1Rules, base]; omega),
      show base i + r - level1Rules.length = i * 12 + r by simp [level1Rules, base]; omega,
      getElem?_flatMap_uniform blockRules 12 (List.range K) (fun i _ => length_blockRules i) i r hr
        (by simpa using hi)]
    simp

/-- Rule `tb K + j` is tableau rule `j`. -/
theorem tab_get (j : Nat) : (gT M K).rules[tb K + j]? = (tabRules M K)[j]? := by
  simp only [gT]
  rw [List.getElem?_append_right (by rw [length_levels]; unfold tb; omega), length_levels]
  congr 1; unfold tb; omega

end Levels

/-! ## The tableau rules -/

theorem getElem?_append_off {α : Type} (l₁ l₂ : List α) (j : Nat) : (l₁ ++ l₂)[l₁.length + j]? = l₂[j]? := by
  rw [List.getElem?_append_right (by omega)]; congr 1; omega

section Tab

variable {kt : Nat} (M : TM kt) (K : Nat)

local notation "τK" => lvTy K

theorem len_FT : (tabFT K).length = 1 := rfl
theorem len_IN : (tabIN K).length = 3 := by simp [tabIN]
theorem len_ST : (tabST M K).length = M.nq := by simp [tabST]
theorem len_HD : (tabHD M K).length = kt := by simp [tabHD]
theorem len_SY : (tabSY M K).length = kt * M.na := by
  rw [tabSY, length_flatMap_uniform _ M.na _ (fun _ _ => by simp)]; simp

theorem g_FT : (gT M K).rules[rFT K]? = some ⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (ftsBody K)⟩ := by
  have := tab_get M K 0
  simp only [Nat.add_zero] at this
  rw [rFT, this]; rfl

theorem g_IN {s : Nat} (hs : s < 3) :
    (gT M K).rules[rIN K s]? = some ⟨τK ⇒ τK ⇒ Ty.p ⇒ Ty.p, lamsT [τK, τK, .p] (inBody K s)⟩ := by
  rw [rIN, Nat.add_assoc, tab_get, tabRules, show 1 + s = (tabFT K).length + s from rfl, getElem?_append_off,
    List.getElem?_append_left (by rw [len_IN]; exact hs)]
  simp [tabIN, hs]

theorem g_ST {q : Nat} (hq : q < M.nq) :
    (gT M K).rules[rST K q]? = some ⟨τK ⇒ Ty.p, lamsT [τK] (stateBody M K q)⟩ := by
  rw [rST, Nat.add_assoc, tab_get, tabRules,
    show 4 + q = (tabFT K).length + ((tabIN K).length + q) by rw [len_FT, len_IN]; omega,
    getElem?_append_off, getElem?_append_off, List.getElem?_append_left (by rw [len_ST]; exact hq)]
  simp [tabST, hq]

theorem g_HD (τ : Fin kt) :
    (gT M K).rules[rHD M K τ]? = some ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (headBody M K τ)⟩ := by
  rw [rHD, show tb K + 4 + M.nq + τ.val =
      tb K + ((tabFT K).length + ((tabIN K).length + ((tabST M K).length + τ.val))) by
      rw [len_FT, len_IN, len_ST]; omega,
    tab_get, tabRules, getElem?_append_off, getElem?_append_off, getElem?_append_off,
    List.getElem?_append_left (by rw [len_HD]; exact τ.isLt)]
  simp [tabHD]

theorem lt_uniform {kt na : Nat} (τ : Fin kt) {s : Nat} (hs : s < na) : τ.val * na + s < kt * na := by
  have := Nat.mul_le_mul_right na (show τ.val + 1 ≤ kt from τ.isLt); rw [Nat.succ_mul] at this; omega

theorem g_SY (τ : Fin kt) {s : Nat} (hs : s < M.na) :
    (gT M K).rules[rSY M K τ s]? = some ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (symBody M K τ s)⟩ := by
  rw [rSY, show tb K + 4 + M.nq + kt + τ.val * M.na + s =
      tb K + ((tabFT K).length + ((tabIN K).length + ((tabST M K).length + ((tabHD M K).length +
        (τ.val * M.na + s))))) by rw [len_FT, len_IN, len_ST, len_HD]; omega,
    tab_get, tabRules, getElem?_append_off, getElem?_append_off, getElem?_append_off, getElem?_append_off,
    List.getElem?_append_left (by rw [len_SY]; exact lt_uniform τ hs), tabSY,
    getElem?_flatMap_uniform _ M.na _ (fun _ _ => by simp) τ.val s hs (by simp)]
  simp [hs]

theorem g_RD (τ : Fin kt) {s : Nat} (hs : s < M.na) :
    (gT M K).rules[rRD M K τ s]? = some ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (readBody M K τ s)⟩ := by
  rw [rRD, show tb K + 4 + M.nq + kt + kt * M.na + τ.val * M.na + s =
      tb K + ((tabFT K).length + ((tabIN K).length + ((tabST M K).length + ((tabHD M K).length +
        ((tabSY M K).length + (τ.val * M.na + s)))))) by rw [len_FT, len_IN, len_ST, len_HD, len_SY]; omega,
    tab_get, tabRules, getElem?_append_off, getElem?_append_off, getElem?_append_off, getElem?_append_off,
    getElem?_append_off, tabRD, getElem?_flatMap_uniform _ M.na _ (fun _ _ => by simp) τ.val s hs (by simp)]
  simp [hs]

end Tab

end Shallot.MacroPeg.Tableau
