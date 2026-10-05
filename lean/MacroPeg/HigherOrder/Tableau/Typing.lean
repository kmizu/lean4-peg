import MacroPeg.HigherOrder.Tableau.Sim
import MacroPeg.HigherOrder.ExpSpace.Typing

/-!
# The tableau grammar is a well-typed grammar of order `K + 1`

Level-`i` numbers have type `lvTy i` of order `i`; the rules of block `i` have order `i + 2`, the tableau rules take
level-`K` numbers and have order `K + 1`. So `gT M K` is well typed (`gT_wellTyped`), its start is a closed parser
(`startT_hasTy`) and its order is `K + 1` (`gT_order`).
-/

namespace Shallot.MacroPeg.Tableau

open Complexity (TM Move)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.ExpSpace (rcall allChainH anyChainH hcodeE hsiteE hoptY hsemi bitC bit1 xorE newSite arrows
  hasTy_peg hasTy_codeE hasTy_siteE hasTy_optY hasTy_andP hasTy_apps hasTy_rcall hasTy_lamsT hasTy_allChainH
  hasTy_anyChainH peg_siteE le_foldr_max)

theorem order_lvTy : ∀ i, (lvTy i).order = i
  | 0 => rfl
  | i + 1 => by simp only [lvTy, Ty.order, order_lvTy i]; omega

/-! ## Generic typing helpers -/

section Helpers

variable {R : List HO.Ty} {Γ : List HO.Ty}

theorem hasTy_bit1G {a : HExp} (ha : HasTy R Γ a .p) : HasTy R Γ (bit1 a) .p := .seq ha (.lit Γ _)

theorem hasTy_xorG {P Q : HExp} (hP : HasTy R Γ P .p) (hQ : HasTy R Γ Q .p) : HasTy R Γ (xorE P Q) .p :=
  .alt (.seq (hasTy_andP hP) (.notP hQ)) (.seq (.notP hP) (hasTy_andP hQ))

theorem hasTy_newSiteG {B : HExp} (hB : HasTy R Γ B .p) : HasTy R Γ (newSite B) .p :=
  .alt (.seq (hasTy_andP hB) (.seq (.seq hasTy_codeE hasTy_optY) (.lit Γ _)))
    (.seq (.notP hB) (.seq hasTy_codeE hasTy_optY))

theorem hasTy_bitCG (b : Bool) : HasTy R Γ (bitC b) .p := by
  cases b
  · exact .notP (.eps Γ)
  · exact .eps Γ

theorem hasTy_guardG {C X Y : HExp} (hC : HasTy R Γ C .p) (hX : HasTy R Γ X .p) (hY : HasTy R Γ Y .p) :
    HasTy R Γ (guardE C X Y) .p := .alt (.seq (hasTy_andP hC) hX) (.seq (.notP hC) hY)

theorem hasTy_call1 {i : Nat} {τ σ : HO.Ty} (hr : R[i]? = some (arrows [τ] σ)) {a : HExp} (ha : HasTy R Γ a τ) :
    HasTy R Γ (rcall i [a]) σ :=
  hasTy_apps (.rule hr) rfl (fun j τ' a' h₁ h₂ => by
    cases j with
    | zero => simp at h₁ h₂; rw [← h₁, ← h₂]; exact ha
    | succ j => simp at h₁)

theorem hasTy_call2 {i : Nat} {τ₁ τ₂ σ : HO.Ty} (hr : R[i]? = some (arrows [τ₁, τ₂] σ)) {a b : HExp}
    (ha : HasTy R Γ a τ₁) (hb : HasTy R Γ b τ₂) : HasTy R Γ (rcall i [a, b]) σ :=
  hasTy_apps (.rule hr) rfl (fun j τ' a' h₁ h₂ => by
    match j with
    | 0 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact ha
    | 1 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact hb
    | _ + 2 => simp at h₁)

theorem hasTy_call3 {i : Nat} {τ₁ τ₂ τ₃ σ : HO.Ty} (hr : R[i]? = some (arrows [τ₁, τ₂, τ₃] σ)) {a b c : HExp}
    (ha : HasTy R Γ a τ₁) (hb : HasTy R Γ b τ₂) (hc : HasTy R Γ c τ₃) : HasTy R Γ (rcall i [a, b, c]) σ :=
  hasTy_apps (.rule hr) rfl (fun j τ' a' h₁ h₂ => by
    match j with
    | 0 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact ha
    | 1 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact hb
    | 2 => simp at h₁ h₂; rw [← h₁, ← h₂]; exact hc
    | _ + 3 => simp at h₁)

end Helpers

/-! ## Rule types in `gT` -/

section Types

variable {kt : Nat} (M : TM kt) (K : Nat)

local notation "τK" => lvTy K

theorem types_get (j : Nat) : (gT M K).types[j]? = ((gT M K).rules[j]?).map HRule.ty := by
  simp [HGrammar.types, List.getElem?_map]

theorem ty_l1 (j : Nat) (hj : j < 3) : (gT M K).types[j]? = (level1Rules[j]?).map HRule.ty := by
  rw [types_get, (gT_levels M K).1 j hj]

theorem ty_block {i : Nat} (hi : i < K) (r : Nat) (hr : r < 12) :
    (gT M K).types[base i + r]? = ((blockRules i)[r]?).map HRule.ty := by
  rw [types_get, (gT_levels M K).2 i hi r hr]

/-- The operations of level `i ≤ K` are well typed. -/
theorem ops_hasTy {Γ : List HO.Ty} : ∀ i, i ≤ K →
    HasTy (gT M K).types Γ (ops i).zero (lvTy i) ∧ HasTy (gT M K).types Γ (ops i).max (lvTy i) ∧
    (∀ e, HasTy (gT M K).types Γ e (lvTy i) →
      HasTy (gT M K).types Γ ((ops i).inc e) (lvTy i) ∧ HasTy (gT M K).types Γ ((ops i).dec e) (lvTy i) ∧
      HasTy (gT M K).types Γ ((ops i).isZero e) .p ∧ HasTy (gT M K).types Γ ((ops i).isMax e) .p) ∧
    (∀ a b, HasTy (gT M K).types Γ a (lvTy i) → HasTy (gT M K).types Γ b (lvTy i) → HasTy (gT M K).types Γ ((ops i).eq a b) .p)
  | 0, _ => by
    have h0 := ty_l1 M K 0 (by omega)
    have h1 := ty_l1 M K 1 (by omega)
    have h2 := ty_l1 M K 2 (by omega)
    simp only [level1Rules] at h0 h1 h2
    refine ⟨.seq hasTy_codeE hasTy_optY, .seq (.seq hasTy_codeE hasTy_optY) (.lit _ _), fun e he => ⟨?_, ?_, ?_, ?_⟩,
      fun a b ha hb => hasTy_call2 (σ := .p) h2 ha hb⟩
    · exact hasTy_newSiteG (hasTy_xorG (hasTy_bit1G he) (.seq hasTy_siteE (hasTy_call1 (σ := .p) h0 he)))
    · exact hasTy_newSiteG (hasTy_xorG (hasTy_bit1G he) (.seq hasTy_siteE (hasTy_call1 (σ := .p) h1 he)))
    · exact hasTy_call1 (σ := .p) h1 he
    · exact hasTy_call1 (σ := .p) h0 he
  | j + 1, hj => by
    have t := fun r (hr : r < 12) => ty_block M K (i := j) (by omega) r hr
    refine ⟨.rule (by simpa [blockRules, lvTy] using t 5 (by omega)), .rule (by simpa [blockRules, lvTy] using t 6 (by omega)),
      fun e he => ⟨?_, ?_, ?_, ?_⟩, fun a b ha hb => ?_⟩
    · exact hasTy_call1 (τ := lvTy (j + 1)) (σ := lvTy (j + 1)) (by simpa [blockRules, arrows, lvTy] using t 7 (by omega)) he
    · exact hasTy_call1 (τ := lvTy (j + 1)) (σ := lvTy (j + 1)) (by simpa [blockRules, arrows, lvTy] using t 8 (by omega)) he
    · exact hasTy_call1 (τ := lvTy (j + 1)) (σ := .p) (by simpa [blockRules, arrows, lvTy] using t 9 (by omega)) he
    · exact hasTy_call1 (τ := lvTy (j + 1)) (σ := .p) (by simpa [blockRules, arrows, lvTy] using t 10 (by omega)) he
    · exact hasTy_call2 (σ := .p) (by simpa [blockRules, arrows, lvTy] using t 11 (by omega)) ha hb

/-- The three level-1 rules are well typed. -/
theorem level1_hasTy : ∀ r ∈ level1Rules, HasTy (gT M K).types [] r.body r.ty := by
  have h0 := ty_l1 M K 0 (by omega)
  have h1 := ty_l1 M K 1 (by omega)
  have h2 := ty_l1 M K 2 (by omega)
  simp only [level1Rules] at h0 h1 h2
  intro r hr
  simp only [level1Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · apply hasTy_lamsT [.p]
    have hh : HasTy (gT M K).types [.p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _)) (.seq (hasTy_andP (hasTy_bit1G hh)) (.seq hasTy_siteE (hasTy_call1 (σ := .p) h0 hh)))
  · apply hasTy_lamsT [.p]
    have hh : HasTy (gT M K).types [.p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _)) (.seq (.notP (hasTy_bit1G hh)) (.seq hasTy_siteE (hasTy_call1 (σ := .p) h1 hh)))
  · apply hasTy_lamsT [.p, .p]
    have ha : HasTy (gT M K).types [.p, .p] (.var 1) .p := .var rfl
    have hh : HasTy (gT M K).types [.p, .p] (.var 0) .p := .var rfl
    exact .alt (hasTy_andP (.lit _ _))
      (.seq (.alt (.seq (hasTy_andP (hasTy_bit1G ha)) (hasTy_andP (hasTy_bit1G hh)))
        (.seq (.notP (hasTy_bit1G ha)) (.notP (hasTy_bit1G hh))))
        (.seq hasTy_siteE (hasTy_call2 (σ := .p) h2 ha hh)))

/-- The twelve rules of block `i < K` are well typed. -/
theorem block_hasTy {i : Nat} (hi : i < K) : ∀ r ∈ blockRules i, HasTy (gT M K).types [] r.body r.ty := by
  have t := fun r (hr : r < 12) => ty_block M K hi r hr
  have h0 : (gT M K).types[base i]? = some (arrows [lvTy i ⇒ .p, lvTy i] .p) := by
    simpa [blockRules, arrows] using t 0 (by omega)
  have h1 : (gT M K).types[base i + 1]? = some (arrows [lvTy i ⇒ .p, lvTy i] .p) := by
    simpa [blockRules, arrows] using t 1 (by omega)
  have h2 : (gT M K).types[base i + 2]? = some (arrows [lvTy i ⇒ .p, lvTy i] .p) := by
    simpa [blockRules, arrows] using t 2 (by omega)
  have h3 : (gT M K).types[base i + 3]? = some (arrows [lvTy i ⇒ .p] (lvTy i ⇒ .p)) := by
    simpa [blockRules, arrows] using t 3 (by omega)
  have h4 : (gT M K).types[base i + 4]? = some (arrows [lvTy i ⇒ .p, lvTy i ⇒ .p] (lvTy i ⇒ .p)) := by
    simpa [blockRules, arrows] using t 4 (by omega)
  have hops := fun {Γ : List HO.Ty} => ops_hasTy M K (Γ := Γ) i (by omega)
  intro r hr
  simp only [blockRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  -- in the contexts below, `var 0 : lvTy i` is the index and `var 1 : lvTy i ⇒ p` the number
  have hx : HasTy (gT M K).types [lvTy i, lvTy i ⇒ .p] (.var 0) (lvTy i) := .var rfl
  have hf : HasTy (gT M K).types [lvTy i, lvTy i ⇒ .p] (.var 1) (lvTy i ⇒ .p) := .var rfl
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply hasTy_lamsT [lvTy i ⇒ .p, lvTy i]
    exact .seq (hasTy_andP (.app hf hx))
      (hasTy_guardG ((hops.2.2.1 _ hx).2.2.2) (.eps _) (hasTy_call2 (σ := .p) h0 hf (hops.2.2.1 _ hx).1))
  · apply hasTy_lamsT [lvTy i ⇒ .p, lvTy i]
    have hd := (hops.2.2.1 _ hx).2.1
    exact hasTy_guardG (hops.2.2.1 _ hx).2.2.1 (.eps _) (.seq (hasTy_andP (.app hf hd)) (hasTy_call2 (σ := .p) h1 hf hd))
  · apply hasTy_lamsT [lvTy i ⇒ .p, lvTy i]
    have hd := (hops.2.2.1 _ hx).2.1
    exact hasTy_guardG (hops.2.2.1 _ hx).2.2.1 (.eps _) (.seq (.notP (.app hf hd)) (hasTy_call2 (σ := .p) h2 hf hd))
  · exact hasTy_lamsT [lvTy i ⇒ .p, lvTy i] (.notP (.app hf hx))
  · apply hasTy_lamsT [lvTy i ⇒ .p, lvTy i ⇒ .p, lvTy i]
    have hy : HasTy (gT M K).types [lvTy i, lvTy i ⇒ .p, lvTy i ⇒ .p] (.var 0) (lvTy i) := .var rfl
    have hP : HasTy (gT M K).types [lvTy i, lvTy i ⇒ .p, lvTy i ⇒ .p] (.var 2) (lvTy i ⇒ .p) := .var rfl
    have hQ : HasTy (gT M K).types [lvTy i, lvTy i ⇒ .p, lvTy i ⇒ .p] (.var 1) (lvTy i ⇒ .p) := .var rfl
    exact .alt (.seq (hasTy_andP (.app hP hy)) (hasTy_andP (.app hQ hy))) (.seq (.notP (.app hP hy)) (.notP (.app hQ hy)))
  · exact hasTy_lamsT [lvTy i] (.notP (.eps _))
  · exact hasTy_lamsT [lvTy i] (.eps _)
  · exact hasTy_lamsT [lvTy i ⇒ .p, lvTy i] (hasTy_xorG (.app hf hx) (hasTy_call2 (σ := .p) h1 hf hx))
  · exact hasTy_lamsT [lvTy i ⇒ .p, lvTy i] (hasTy_xorG (.app hf hx) (hasTy_call2 (σ := .p) h2 hf hx))
  · apply hasTy_lamsT [lvTy i ⇒ .p]
    have hg : HasTy (gT M K).types [lvTy i ⇒ .p] (.var 0) (lvTy i ⇒ .p) := .var rfl
    exact hasTy_call2 (σ := .p) h0 (hasTy_call1 (σ := lvTy i ⇒ .p) h3 hg) hops.1
  · apply hasTy_lamsT [lvTy i ⇒ .p]
    have hg : HasTy (gT M K).types [lvTy i ⇒ .p] (.var 0) (lvTy i ⇒ .p) := .var rfl
    exact hasTy_call2 (σ := .p) h0 hg hops.1
  · apply hasTy_lamsT [lvTy i ⇒ .p, lvTy i ⇒ .p]
    have hP : HasTy (gT M K).types [lvTy i ⇒ .p, lvTy i ⇒ .p] (.var 1) (lvTy i ⇒ .p) := .var rfl
    have hQ : HasTy (gT M K).types [lvTy i ⇒ .p, lvTy i ⇒ .p] (.var 0) (lvTy i ⇒ .p) := .var rfl
    exact hasTy_call2 (σ := .p) h0 (hasTy_call2 (σ := lvTy i ⇒ .p) h4 hP hQ) hops.1

end Types

/-! ## The tableau rules -/

section Tab

variable {kt : Nat} (M : TM kt) (K : Nat) {Γ : List HO.Ty}

local notation "τK" => lvTy K

theorem ty_FT : (gT M K).types[rFT K]? = some (arrows [.p, .p] .p) := by rw [types_get, g_FT]; rfl
theorem ty_IN {s : Nat} (hs : s < 3) : (gT M K).types[rIN K s]? = some (arrows [τK, τK, .p] .p) := by
  rw [types_get, g_IN M K hs]; rfl
theorem ty_ST {q : Nat} (hq : q < M.nq) : (gT M K).types[rST K q]? = some (arrows [τK] .p) := by
  rw [types_get, g_ST M K hq]; rfl
theorem ty_HD (τ : Fin kt) : (gT M K).types[rHD M K τ]? = some (arrows [τK, τK] .p) := by
  rw [types_get, g_HD M K τ]; rfl
theorem ty_SY (τ : Fin kt) {s : Nat} (hs : s < M.na) : (gT M K).types[rSY M K τ s]? = some (arrows [τK, τK] .p) := by
  rw [types_get, g_SY M K τ hs]; rfl
theorem ty_RD (τ : Fin kt) {s : Nat} (hs : s < M.na) : (gT M K).types[rRD M K τ s]? = some (arrows [τK, τK] .p) := by
  rw [types_get, g_RD M K τ hs]; rfl

/-- The level-`K` operations, in any context. -/
theorem opsK : HasTy (gT M K).types Γ (ops K).zero τK ∧ HasTy (gT M K).types Γ (ops K).max τK ∧
    (∀ e, HasTy (gT M K).types Γ e τK →
      HasTy (gT M K).types Γ ((ops K).inc e) τK ∧ HasTy (gT M K).types Γ ((ops K).dec e) τK ∧
      HasTy (gT M K).types Γ ((ops K).isZero e) .p ∧ HasTy (gT M K).types Γ ((ops K).isMax e) .p) ∧
    (∀ a b, HasTy (gT M K).types Γ a τK → HasTy (gT M K).types Γ b τK → HasTy (gT M K).types Γ ((ops K).eq a b) .p) :=
  ops_hasTy M K K (Nat.le_refl K)

theorem hasTy_skipE : HasTy (gT M K).types Γ skipE .p := .seq (.star hasTy_siteE) (.lit _ _)

theorem hasTy_ftE {Kc X : HExp} (hK : HasTy (gT M K).types Γ Kc .p) (hX : HasTy (gT M K).types Γ X .p) :
    HasTy (gT M K).types Γ (ftE K Kc X) .p :=
  .seq (hasTy_skipE M K) (hasTy_call2 (σ := .p) (ty_FT M K) hK hX)

theorem hasTy_symE (s : Nat) : HasTy (gT M K).types Γ (symE s) .p := by
  unfold symE
  split
  · exact .seq hasTy_codeE (.lit _ _)
  · split
    · exact .seq hasTy_codeE (.lit _ _)
    · exact .notP (.eps _)

theorem hasTy_readsE {r : List Nat} (hr : r ∈ readsList M.na kt) {tp : HExp} (htp : HasTy (gT M K).types Γ tp τK) :
    HasTy (gT M K).types Γ (readsE M K r tp) .p :=
  hasTy_allChainH _ (fun e he => by
    obtain ⟨τ, _, rfl⟩ := List.mem_map.1 he
    exact hasTy_call2 (σ := .p) (ty_RD M K τ (readsList_getD hr τ)) htp (opsK M K).1)

theorem hasTy_stAt {q : Nat} (hq : q < M.nq) {tp : HExp} (htp : HasTy (gT M K).types Γ tp τK) :
    HasTy (gT M K).types Γ (rcall (rST K q) [tp]) .p := hasTy_call1 (σ := .p) (ty_ST M K hq) htp

theorem hasTy_stateNext (q : Nat) {tp : HExp} (htp : HasTy (gT M K).types Γ tp τK) :
    HasTy (gT M K).types Γ (stateNext M K q tp) .p := by
  have h2 := two_lt_nq M
  refine hasTy_anyChainH _ (fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 he
    have := List.mem_range.1 (List.mem_filter.1 hq').1
    exact hasTy_stAt M K (by omega) htp
  · obtain ⟨q', hq', he⟩ := List.mem_flatMap.1 he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
    exact .seq (hasTy_andP (hasTy_stAt M K (mem_runStates.1 hq').1 htp))
      (hasTy_readsE M K (List.mem_filter.1 hr).1 htp)

theorem hasTy_movedE (τ : Fin kt) (mv : Move) {tp i : HExp} (htp : HasTy (gT M K).types Γ tp τK)
    (hi : HasTy (gT M K).types Γ i τK) : HasTy (gT M K).types Γ (movedE M K τ mv tp i) .p := by
  have ho := ((opsK M K).2.2.1 _ hi)
  cases mv
  · exact .alt (hasTy_guardG ho.2.2.2 (.notP (.eps _)) (hasTy_call2 (σ := .p) (ty_HD M K τ) htp ho.1))
      (.seq (hasTy_andP ho.2.2.1) (hasTy_call2 (σ := .p) (ty_HD M K τ) htp hi))
  · exact hasTy_call2 (σ := .p) (ty_HD M K τ) htp hi
  · exact .seq (.notP ho.2.2.1) (hasTy_call2 (σ := .p) (ty_HD M K τ) htp ho.2.1)

/-- The shape shared by `headNext` and `symNext`: a halted branch per halting state, a step branch per running state
and read vector. -/
theorem hasTy_nextChain {tp : HExp} (htp : HasTy (gT M K).types Γ tp τK) (X : HExp) (Y : Nat → List Nat → HExp)
    (hX : HasTy (gT M K).types Γ X .p)
    (hY : ∀ q' r, q' < M.nq → r ∈ readsList M.na kt → HasTy (gT M K).types Γ (Y q' r) .p) :
    HasTy (gT M K).types Γ (anyChainH ((List.range 2).map (fun q' => .seq (HExp.andP (rcall (rST K q') [tp])) X) ++
      (runStates M).flatMap (fun q' => (readsList M.na kt).map (fun r =>
        .seq (HExp.andP (rcall (rST K q') [tp])) (.seq (HExp.andP (readsE M K r tp)) (Y q' r)))))) .p := by
  have h2 := two_lt_nq M
  refine hasTy_anyChainH _ (fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 he
    exact .seq (hasTy_andP (hasTy_stAt M K (by have := List.mem_range.1 hq'; omega) htp)) hX
  · obtain ⟨q', hq', he⟩ := List.mem_flatMap.1 he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
    have hq := (mem_runStates.1 hq').1
    exact .seq (hasTy_andP (hasTy_stAt M K hq htp)) (.seq (hasTy_andP (hasTy_readsE M K hr htp)) (hY q' r hq hr))

theorem hasTy_initE (τ : Fin kt) (s : Nat) {i : HExp} (hi : HasTy (gT M K).types Γ i τK) :
    HasTy (gT M K).types Γ (initE K τ s i) .p := by
  unfold initE
  split
  · split
    · exact hasTy_call3 (σ := .p) (ty_IN M K (by omega)) hi (opsK M K).1 (.eps _)
    · exact .notP (.eps _)
  · exact hasTy_bitCG _

/-- The tableau rules are well typed. -/
theorem tab_hasTy : ∀ r ∈ tabRules M K, HasTy (gT M K).types [] r.body r.ty := by
  intro r hr
  simp only [tabRules, List.mem_append] at hr
  -- contexts: `[τK, τK]` is (time, index) with `var 1` the time
  have ht : HasTy (gT M K).types [τK, τK] (.var 1) τK := .var rfl
  have hi : HasTy (gT M K).types [τK, τK] (.var 0) τK := .var rfl
  rcases hr with hr | hr | hr | hr | hr | hr
  · simp only [tabFT, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    apply hasTy_lamsT [.p, .p]
    have hK : HasTy (gT M K).types [.p, .p] (.var 1) .p := .var rfl
    have hX : HasTy (gT M K).types [.p, .p] (.var 0) .p := .var rfl
    exact .alt (.seq (hasTy_andP (.seq hK (.lit _ _))) (hasTy_andP hX))
      (.seq (.seq hasTy_codeE (.alt (.lit _ _) (.lit _ _))) (hasTy_call2 (σ := .p) (ty_FT M K) hK hX))
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs := List.mem_range.1 hs
    apply hasTy_lamsT [τK, τK, .p]
    have hKc : HasTy (gT M K).types [.p, τK, τK] (.var 0) .p := .var rfl
    have hc : HasTy (gT M K).types [.p, τK, τK] (.var 1) τK := .var rfl
    have hI : HasTy (gT M K).types [.p, τK, τK] (.var 2) τK := .var rfl
    exact hasTy_guardG (hasTy_ftE M K hKc (.eps _))
      (hasTy_guardG ((opsK M K).2.2.2 _ _ hI hc) (hasTy_ftE M K hKc (hasTy_symE M K s))
        (hasTy_call3 (σ := .p) (ty_IN M K hs) hI ((opsK M K).2.2.1 _ hc).1 (.seq hKc (.lit _ _))))
      (hasTy_bitCG _)
  · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hr
    apply hasTy_lamsT [τK]
    have ht0 : HasTy (gT M K).types [τK] (.var 0) τK := .var rfl
    exact hasTy_guardG ((opsK M K).2.2.1 _ ht0).2.2.1 (hasTy_bitCG _)
      (hasTy_stateNext M K q ((opsK M K).2.2.1 _ ht0).2.1)
  · obtain ⟨τ, _, rfl⟩ := List.mem_map.1 hr
    apply hasTy_lamsT [τK, τK]
    have hd := ((opsK M K).2.2.1 _ ht).2.1
    exact hasTy_guardG ((opsK M K).2.2.1 _ ht).2.2.1 ((opsK M K).2.2.1 _ hi).2.2.1
      (hasTy_nextChain M K hd _ _ (hasTy_call2 (σ := .p) (ty_HD M K τ) hd hi)
        (fun _ _ _ _ => hasTy_movedE M K τ _ hd hi))
  · obtain ⟨τ, _, he⟩ := List.mem_flatMap.1 hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    have hs := List.mem_range.1 hs
    apply hasTy_lamsT [τK, τK]
    have hd := ((opsK M K).2.2.1 _ ht).2.1
    exact hasTy_guardG ((opsK M K).2.2.1 _ ht).2.2.1 (hasTy_initE M K τ s hi)
      (hasTy_nextChain M K hd _ _ (hasTy_call2 (σ := .p) (ty_SY M K τ hs) hd hi)
        (fun _ _ _ _ => hasTy_guardG (hasTy_call2 (σ := .p) (ty_HD M K τ) hd hi) (hasTy_bitCG _)
          (hasTy_call2 (σ := .p) (ty_SY M K τ hs) hd hi)))
  · obtain ⟨τ, _, he⟩ := List.mem_flatMap.1 hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
    have hs := List.mem_range.1 hs
    apply hasTy_lamsT [τK, τK]
    have ho := (opsK M K).2.2.1 _ hi
    exact .alt (.seq (hasTy_andP (hasTy_call2 (σ := .p) (ty_HD M K τ) ht hi)) (hasTy_call2 (σ := .p) (ty_SY M K τ hs) ht hi))
      (.seq (.notP ho.2.2.2) (hasTy_call2 (σ := .p) (ty_RD M K τ hs) ht ho.1))

end Tab

/-! ## The grammar -/

section Grammar

variable {kt : Nat} (M : TM kt) (K : Nat)

/-- **`gT M K` is well typed.** -/
theorem gT_wellTyped : (gT M K).WellTyped := by
  intro r hr
  simp only [gT, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · exact level1_hasTy M K r hr
  · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.1 hr
    exact block_hasTy M K (List.mem_range.1 hi) r hr
  · exact tab_hasTy M K r hr

/-- The start expression is a closed parser. -/
theorem startT_hasTy : HasTy (gT M K).types [] (startT K) .p :=
  .seq (hasTy_andP (hasTy_stAt M K (by have := two_lt_nq M; omega) (opsK M K).2.1)) (.star (.any _))

/-- Every rule type has order at most `K + 1`. -/
theorem rule_order_le : ∀ r ∈ (gT M K).rules, r.ty.order ≤ K + 1 := by
  intro r hr
  simp only [gT, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · simp only [level1Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [Ty.order]
  · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.1 hr
    have hi := List.mem_range.1 hi
    simp only [blockRules, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Ty.order, order_lvTy] <;> omega
  · simp only [tabRules, tabFT, tabIN, tabST, tabHD, tabSY, tabRD, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_flatMap] at hr
    rcases hr with rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp only [Ty.order, order_lvTy] <;> omega

/-- **`gT M K` has order `K + 1`**: the state rules take a level-`K` number. -/
theorem gT_order : (gT M K).order = K + 1 := by
  apply Nat.le_antisymm
  · apply foldr_max_le
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    exact rule_order_le M K r hr
  · have hmem : (lvTy K ⇒ Ty.p).order ∈ (gT M K).rules.map (fun r => r.ty.order) :=
      List.mem_map.2 ⟨_, List.mem_of_getElem? (g_ST M K (q := 0) (by have := two_lt_nq M; omega)), rfl⟩
    have h := le_foldr_max hmem
    simp only [Ty.order, order_lvTy] at h
    unfold HGrammar.order
    omega

end Grammar

end Shallot.MacroPeg.Tableau
