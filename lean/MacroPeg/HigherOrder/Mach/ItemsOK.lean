import MacroPeg.HigherOrder.Mach.EvalTables
import MacroPeg.HigherOrder.Bounds

/-!
# Every item of a reading is covered by the tables

After a successful reading of an instance of `UMPEG j` (`GOrd j g s`), every rule type is *needed* (order `≤ j`,
size below the cap `3L + 2`, `L` the length of the code) and every numbered item satisfies `ItemOK`: its context
types, the type of a variable it reads, and the argument type of an application are small, and the result type of
an application is needed (`itemsOK`).

The route:

* typed terms: every type of a subterm has order `≤ j` (`iok_order`) and size at most the rule sizes plus the context
  sizes plus twice the length of the code of the term (`iok_size`); the items of a term are then *good*
  (`iok_items`) for the bound `ΣR + ΣΓ + 3 · |serE t|`;
* the code of the instance is at least as long as the rule types and every body (`iok_len_*`);
* on the machine side, `sizeNum` is the capped size (`iok_sizeNum_eq`), so a good decoded item is `ItemOK`
  (`iok_itemOK_of_good`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## Sizes of lists of types -/

/-- The total size of a list of types. -/
def iok_sum (l : List HO.Ty) : Nat := (l.map HO.Ty.size).sum

theorem iok_sum_cons (τ : HO.Ty) (l : List HO.Ty) : iok_sum (τ :: l) = τ.size + iok_sum l := by
  simp [iok_sum]

theorem iok_size_le_sum_of_mem {τ : HO.Ty} : ∀ {l : List HO.Ty}, τ ∈ l → τ.size ≤ iok_sum l
  | [], h => by simp at h
  | σ :: l, h => by
    rw [iok_sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := iok_size_le_sum_of_mem h; omega

theorem iok_size_le_sum_of_get {τ : HO.Ty} {l : List HO.Ty} {i : Nat} (h : l[i]? = some τ) :
    τ.size ≤ iok_sum l :=
  iok_size_le_sum_of_mem (List.mem_of_getElem? h)

/-- The code of a list of rule types is at least as long as their total size. -/
theorem iok_sum_le_serTys : ∀ l : List HO.Ty, iok_sum l ≤ (KExp.serTys l).length
  | [] => by simp [iok_sum]
  | τ :: l => by
    have h₁ := iok_sum_le_serTys l
    have h₂ := iok_serTy_length τ
    rw [iok_sum_cons]; simp only [KExp.serTys, List.length_cons, List.length_append]; omega
where
  /-- The code of a type has exactly its size. -/
  iok_serTy_length : ∀ τ : HO.Ty, (KExp.serTy τ).length = τ.size
    | .p => rfl
    | .arr a b => by
      simp only [KExp.serTy, List.length_cons, List.length_append, iok_serTy_length a, iok_serTy_length b,
        HO.Ty.size]

/-! ## Types of typed terms -/

section Terms

variable {R : List HO.Ty}

/-- **Orders.** If the rules have order `≤ j`, the context and every binder order `< j`, the term has order `≤ j`. -/
theorem iok_order (j : Nat) (hR : ∀ ρ ∈ R, ρ.order ≤ j) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ), (∀ γ ∈ Γ, γ.order + 1 ≤ j) →
      KExp.lamOrd t.erase ≤ j → τ.order ≤ j
  | _, _, .eps, _, _ => by simp [HO.Ty.order]
  | _, _, .any, _, _ => by simp [HO.Ty.order]
  | _, _, .chr _, _, _ => by simp [HO.Ty.order]
  | _, _, .range _ _, _, _ => by simp [HO.Ty.order]
  | _, _, .lit _, _, _ => by simp [HO.Ty.order]
  | _, _, .seq _ _, _, _ => by simp [HO.Ty.order]
  | _, _, .alt _ _, _, _ => by simp [HO.Ty.order]
  | _, _, .star _, _, _ => by simp [HO.Ty.order]
  | _, _, .notP _, _, _ => by simp [HO.Ty.order]
  | _, _, .var _ h, hΓ, _ => by have := hΓ _ (List.mem_of_getElem? h); omega
  | _, _, .rule _ h, _, _ => hR _ (List.mem_of_getElem? h)
  | _, _, @Tm.lam _ _ a _ body, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd, Nat.max_le] at hl
    have hb := iok_order j hR body (by
      intro γ hγ
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exact hl.1
      · exact hΓ γ hγ) hl.2
    simp only [HO.Ty.order, Nat.max_le]
    exact ⟨hl.1, hb⟩
  | _, _, .app f y, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd, Nat.max_le] at hl
    have hf := iok_order j hR f hΓ hl.1
    simp only [HO.Ty.order, Nat.max_le] at hf
    exact hf.2

/-- **Sizes.** The type of a term is at most the rule sizes, the context sizes and twice the length of its code. -/
theorem iok_size : ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ),
    τ.size ≤ iok_sum R + iok_sum Γ + 2 * (KExp.serE t.erase).length
  | _, _, .eps => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .any => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .chr _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .range _ _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .lit _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .seq _ _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .alt _ _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .star _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .notP _ => by simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons]; omega
  | _, _, .var _ h => by have := iok_size_le_sum_of_get h; omega
  | _, _, .rule _ h => by have := iok_size_le_sum_of_get h; omega
  | _, _, @Tm.lam _ _ a _ body => by
    have hb := iok_size body
    have ha := iok_sum_le_serTys.iok_serTy_length a
    rw [iok_sum_cons] at hb
    simp only [HO.Ty.size, Tm.erase, KExp.serE, List.length_cons, List.length_append]
    omega
  | _, _, .app f _ => by
    have hf := iok_size f
    simp only [HO.Ty.size] at hf
    simp only [Tm.erase, KExp.serE, List.length_cons, List.length_append]
    omega

end Terms

/-! ## Good items -/

/-- An item is *good* for order `j` and size bound `B`: its context types have order `< j` and size `≤ B`, and an
application has argument order `< j`, result order `≤ j`, both sizes `≤ B`. -/
def iok_Good (j B : Nat) (it : Item) : Prop :=
  (∀ τ ∈ it.ctx, τ.order + 1 ≤ j ∧ τ.size ≤ B) ∧
    (∀ a b, it.op = .app a b → a.order + 1 ≤ j ∧ a.size ≤ B ∧ b.order ≤ j ∧ b.size ≤ B)

theorem iok_Good_mono {j B B' : Nat} {it : Item} (hB : B ≤ B') (h : iok_Good j B it) : iok_Good j B' it := by
  refine ⟨fun τ hτ => ?_, fun a b he => ?_⟩
  · have := h.1 τ hτ; omega
  · have := h.2 a b he; omega

/-- An item that is not an application, in a context of good types, is good. -/
theorem iok_Good_single {j B : Nat} {op : Op} {Γ : List HO.Ty} (hΓ : ∀ γ ∈ Γ, γ.order + 1 ≤ j)
    (hB : iok_sum Γ ≤ B) (hop : ∀ a b, op ≠ .app a b) : iok_Good j B ⟨op, Γ⟩ := by
  refine ⟨fun τ hτ => ⟨hΓ τ hτ, by have := iok_size_le_sum_of_mem (l := Γ) hτ; omega⟩, fun a b he => ?_⟩
  exact absurd he (hop a b)

section Items

variable {R : List HO.Ty}

/-- All items of a list are good. -/
abbrev iok_AllGood (j B : Nat) (l : List Item) : Prop := ∀ it ∈ l, iok_Good j B it

theorem iok_AllGood_append {j B : Nat} {l₁ l₂ : List Item} (h₁ : iok_AllGood j B l₁) (h₂ : iok_AllGood j B l₂) :
    iok_AllGood j B (l₁ ++ l₂) := by
  intro it hit
  rcases List.mem_append.1 hit with h | h
  · exact h₁ it h
  · exact h₂ it h

theorem iok_AllGood_mono {j B B' : Nat} {l : List Item} (hB : B ≤ B') (h : iok_AllGood j B l) :
    iok_AllGood j B' l :=
  fun it hit => iok_Good_mono hB (h it hit)

theorem iok_AllGood_single {j B : Nat} {it : Item} (h : iok_Good j B it) : iok_AllGood j B [it] := by
  intro it' hit'
  rw [List.mem_singleton] at hit'
  subst hit'
  exact h

/-- **The items of a typed term are good** for the bound `ΣR + ΣΓ + 3 · |serE t|`. -/
theorem iok_items (j : Nat) (hR : ∀ ρ ∈ R, ρ.order ≤ j) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ), (∀ γ ∈ Γ, γ.order + 1 ≤ j) → KExp.lamOrd t.erase ≤ j →
      iok_AllGood j (iok_sum R + iok_sum Γ + 3 * (KExp.serE t.erase).length) (items t)
  | _, _, .eps, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .any, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .chr _, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .range _ _, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .lit _, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .var _ _, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .rule _ _, hΓ, _ => iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp))
  | _, _, .seq a b, hΓ, hl | _, _, .alt a b, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd, Nat.max_le] at hl
    have ha := iok_items j hR a hΓ hl.1
    have hb := iok_items j hR b hΓ hl.2
    simp only [items, Tm.erase, KExp.serE, List.length_cons, List.length_append]
    refine iok_AllGood_append (iok_AllGood_append (iok_AllGood_mono ?_ ha) (iok_AllGood_mono ?_ hb))
      (iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp)))
    all_goals omega
  | _, _, .star a, hΓ, hl | _, _, .notP a, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd] at hl
    have ha := iok_items j hR a hΓ hl
    simp only [items, Tm.erase, KExp.serE, List.length_cons]
    exact iok_AllGood_append (iok_AllGood_mono (by omega) ha)
      (iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp)))
  | Γ, _, @Tm.lam _ _ a _ body, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd, Nat.max_le] at hl
    have hΓ' : ∀ γ ∈ a :: Γ, γ.order + 1 ≤ j := by
      intro γ hγ
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exact hl.1
      · exact hΓ γ hγ
    have hb := iok_items j hR body hΓ' hl.2
    have ha := iok_sum_le_serTys.iok_serTy_length a
    rw [iok_sum_cons] at hb
    simp only [items, Tm.erase, KExp.serE, List.length_cons, List.length_append]
    exact iok_AllGood_append (iok_AllGood_mono (by omega) hb)
      (iok_AllGood_single (iok_Good_single hΓ (by omega) (by simp)))
  | Γ, _, @Tm.app _ _ a b f y, hΓ, hl => by
    simp only [Tm.erase, KExp.lamOrd, Nat.max_le] at hl
    have hf := iok_items j hR f hΓ hl.1
    have hy := iok_items j hR y hΓ hl.2
    have hord := iok_order j hR f hΓ hl.1
    have hsz := iok_size f
    simp only [HO.Ty.order, Nat.max_le] at hord
    simp only [HO.Ty.size] at hsz
    simp only [items, Tm.erase, KExp.serE, List.length_cons, List.length_append]
    refine iok_AllGood_append (iok_AllGood_append (iok_AllGood_mono ?_ hf) (iok_AllGood_mono ?_ hy))
      (iok_AllGood_single ⟨fun τ hτ => ⟨hΓ τ hτ, ?_⟩, fun a' b' he => ?_⟩)
    · omega
    · omega
    · have := iok_size_le_sum_of_mem (l := Γ) hτ; omega
    · cases he
      exact ⟨hord.1, by omega, hord.2, by omega⟩

end Items

/-! ## Machine side: capped sizes, small types, contexts -/

/-- On a number that decodes, `sizeNum` is the size of the decoded type, capped. -/
theorem iok_sizeNum_eq {cap : Nat} (hcap : 1 ≤ cap) {tt : List (Nat × Nat)} :
    ∀ (k : Nat) {τ : HO.Ty}, tyOf tt k = some τ → sizeNum cap tt k = min cap τ.size
  | 0, τ, h => by
    rw [tyOf] at h; cases h
    rw [sizeNum]; simp only [HO.Ty.size]; omega
  | k + 1, τ, h => by
    rw [tyOf] at h
    split at h
    · rename_i a b hk
      split at h
      · rename_i hab
        split at h
        · rename_i σ ρ hσ hρ
          cases h
          rw [sizeNum]; simp only [hk]
          rw [if_pos hab, iok_sizeNum_eq hcap a hσ, iok_sizeNum_eq hcap b hρ]
          simp only [HO.Ty.size]
          omega
        · cases h
      · cases h
    · cases h

/-- A decoded type of order `< j` and size `< cap` is small. -/
theorem iok_small_of {j cap : Nat} {tt : List (Nat × Nat)} {k : Nat} {τ : HO.Ty} (h : tyOf tt k = some τ)
    (ho : τ.order + 1 ≤ j) (hs : τ.size < cap) : small j cap tt k := by
  have hpos := HO.Ty.size_pos τ
  refine ⟨by rw [ordNum_eq k h]; omega, ?_⟩
  rw [iok_sizeNum_eq (by omega) k h]; omega

/-- A decoded type of order `≤ j` and size `< cap` is needed. -/
theorem iok_need_of {j cap : Nat} {tt : List (Nat × Nat)} {k : Nat} {τ : HO.Ty} (h : tyOf tt k = some τ)
    (ho : τ.order ≤ j) (hs : τ.size < cap) : need j cap tt k := by
  have hpos := HO.Ty.size_pos τ
  refine ⟨by rw [ordNum_eq k h]; omega, ?_⟩
  rw [iok_sizeNum_eq (by omega) k h]; omega

/-- Type number `0` (the parser type) is small once `j ≥ 1` and `cap ≥ 2`. -/
theorem iok_small_zero {j cap : Nat} {tt : List (Nat × Nat)} (hj : 1 ≤ j) (hcap : 2 ≤ cap) : small j cap tt 0 := by
  refine ⟨?_, ?_⟩
  · rw [ordNum]; omega
  · rw [sizeNum]; omega

/-- A decoded context whose types are all of order `< j` and size `< cap` is small. -/
theorem iok_ctxSmall {j cap : Nat} {tt ct : List (Nat × Nat)} : ∀ (c : Nat) {Γ : List HO.Ty},
    ctxOf tt ct c = some Γ → (∀ τ ∈ Γ, τ.order + 1 ≤ j ∧ τ.size < cap) → ctxSmall j cap tt ct c
  | 0, _, _, _ => by rw [ctxSmall]; trivial
  | k + 1, Γ, h, hΓ => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Δ hτ hΔ
          simp only [Option.some.injEq] at h
          subst h
          rw [ctxSmall]
          simp only [hk, if_pos hp]
          have h₀ := hΓ τ List.mem_cons_self
          exact ⟨iok_small_of hτ h₀.1 h₀.2,
            iok_ctxSmall par hΔ (fun σ hσ => hΓ σ (List.mem_cons_of_mem _ hσ))⟩
        · cases h
      · cases h
    · cases h

/-- Tag `12` gives an application operation, with both type numbers decoding. -/
theorem iok_opOf_tag12 {tt : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {op : Op}
    (h : opOf tt lt it = some op) (htag : it.tag = 12) :
    ∃ a b, op = .app a b ∧ tyOf tt it.a = some a ∧ tyOf tt it.b = some b := by
  unfold opOf at h
  rw [htag] at h
  simp only at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, rfl, ha, hb⟩
  · cases h

/-- **A good decoded item is covered by the tables.** -/
theorem iok_itemOK_of_good {j cap B : Nat} {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {mi : MItem}
    {it : Item} (hw : TTWF tt) (hj : 1 ≤ j) (hB : B < cap) (hcap : 2 ≤ cap)
    (h : itemOf tt ct lt mi = some it) (hg : iok_Good j B it) : ItemOK j cap tt ct mi := by
  unfold itemOf at h
  split at h
  · rename_i op Γ hop hΓ
    cases h
    have hctx : ∀ τ ∈ Γ, τ.order + 1 ≤ j ∧ τ.size < cap := fun τ hτ => by
      have := hg.1 τ hτ; exact ⟨this.1, by omega⟩
    refine ⟨iok_ctxSmall _ hΓ hctx, fun h9 => ?_, fun h12 => ?_⟩
    · obtain ⟨hv, hle⟩ := varTy_ctx mi.ctx hΓ mi.a
      rcases hvt : varTy ct mi.ctx mi.a with _ | t
      · exact iok_small_zero hj hcap
      · rw [hvt, Option.bind_some] at hv
        obtain ⟨τ, hτ⟩ := tyOf_some hw t (hle t hvt)
        rw [hτ] at hv
        have hm : τ ∈ Γ := List.mem_of_getElem? hv.symm
        exact iok_small_of hτ (hctx τ hm).1 (hctx τ hm).2
    · obtain ⟨a, b, rfl, ha, hb⟩ := iok_opOf_tag12 hop h12
      have := hg.2 a b rfl
      exact ⟨iok_small_of ha this.1 (by omega), iok_need_of hb this.2.2.1 (by omega)⟩
  · cases h

/-! ## Lists, bodies and the length of the code -/

/-- An element of a list that maps to `r` has its image in `r`. -/
theorem iok_mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ a ∈ l, ∃ b ∈ r, f a = some b
  | [], _, _, a, ha => by simp at ha
  | c :: l, r, h, a, ha => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨b', hb', hf⟩ := iok_mapM_mem hbs a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', hf⟩

/-- A body is no longer than the code of all bodies. -/
theorem iok_serE_le_serBodies {e : HExp} : ∀ {es : List HExp}, e ∈ es →
    (KExp.serE e).length ≤ (KExp.serBodies es).length
  | [], h => by simp at h
  | e' :: es, h => by
    simp only [KExp.serBodies, List.length_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := iok_serE_le_serBodies h; omega

section Bodies

variable {R : List HO.Ty}

/-- Each item list of typed bodies is the items of a closed term among the bodies. -/
theorem iok_bodyItems : ∀ {S : List HO.Ty} (ts : TBodies R S), ∀ is ∈ bodyItems ts,
    ∃ (τ : HO.Ty) (t : Tm R [] τ), items t = is ∧ t.erase ∈ ts.erase
  | [], _, is, h => by simp [bodyItems] at h
  | τ :: _, (t, ts), is, h => by
    simp only [bodyItems, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨τ, t, rfl, by simp [TBodies.erase]⟩
    · obtain ⟨σ, t', h₁, h₂⟩ := iok_bodyItems ts is h
      exact ⟨σ, t', h₁, by simp only [TBodies.erase, List.mem_cons]; exact Or.inr h₂⟩

/-- The bodies of the rules built from typed bodies are those bodies. -/
theorem iok_map_body : ∀ {S : List HO.Ty} (ts : TBodies R S),
    (List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) S ts.erase).map HRule.body = ts.erase
  | [], _ => rfl
  | _ :: _, (_, ts) => by
    simp only [TBodies.erase, List.zipWith_cons_cons, List.map_cons, iok_map_body ts]

end Bodies

/-- The length of the code of an instance. -/
theorem iok_serIn_length (g : HGrammar) (s : HExp) (x : List Char) :
    (KExp.serIn g s x).length = (KExp.serTys g.types).length + (KExp.serBodies (g.rules.map HRule.body)).length +
      (KExp.serE s).length + (KExp.serStr x).length := by
  simp only [KExp.serIn, List.length_append, HGrammar.types]
  omega

/-! ## The main theorem -/

/-- **After a reading of an instance of order `j`, the tables cover every rule type and every item.** With
`L = tk.length` and the cap `3L + 2`: every rule type is needed and every numbered item is `ItemOK`. -/
theorem itemsOK (j : Nat) (hj : 1 ≤ j) {tk : List Nat} {g : HGrammar} {s : HExp} {x : List Char}
    {bis : List (List Flat.Item)} {is : List Flat.Item} {st : PSt}
    (hd : Flat.deser tk = some (g, s, x)) (hcr : Flat.checkRules g = some bis)
    (hinf : Flat.inferE g.types [] s = some (.p, is)) (hr : ReadOK st g.types bis is x)
    (hgo : KExp.GOrd j g s) :
    (∀ t ∈ st.rt, need j (3 * tk.length + 2) st.tt t) ∧
      (∀ it ∈ st.bodies.flatten ++ st.start, ItemOK j (3 * tk.length + 2) st.tt st.ct it) := by
  obtain ⟨hgord, hglam, hslam⟩ := hgo
  have hR : ∀ ρ ∈ g.types, ρ.order ≤ j := (order_le_iff j g).1 hgord
  -- the length of the code
  have hlen := iok_serIn_length g s x
  rw [← deser_sound hd] at hlen
  have hsR := iok_sum_le_serTys g.types
  -- the typed grammar and start
  obtain ⟨G, hG, hbis⟩ := checkRules_sound hcr
  have hrules : g.rules = List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) g.types G.bodies.erase :=
    (congrArg HGrammar.rules hG).symm
  have hbodies : g.rules.map HRule.body = G.bodies.erase := by rw [hrules, iok_map_body]
  obtain ⟨t₀, hts, hti⟩ := inferE_sound _ hinf
  -- every decoded item is good for the bound `3L + 1`
  have hgood : ∀ it ∈ bis.flatten ++ is, iok_Good j (3 * tk.length + 1) it := by
    intro it hit
    rcases List.mem_append.1 hit with hit | hit
    · obtain ⟨l, hl, hitl⟩ := List.mem_flatten.1 hit
      rw [← hbis] at hl
      obtain ⟨τ, t, hti', hmem⟩ := iok_bodyItems G.bodies l hl
      rw [← hbodies] at hmem
      obtain ⟨r, hr', hre⟩ := List.mem_map.1 hmem
      have hlo : KExp.lamOrd t.erase ≤ j := hre ▸ hglam r hr'
      have hle := iok_serE_le_serBodies hmem
      have hg := iok_items j hR t (fun _ h => by simp at h) hlo
      rw [hti'] at hg
      exact iok_Good_mono (by rw [show iok_sum [] = 0 from rfl]; omega) (hg it hitl)
    · have hlo : KExp.lamOrd t₀.erase ≤ j := hts ▸ hslam
      have hg := iok_items j hR t₀ (fun _ h => by simp at h) hlo
      rw [hti, hts] at hg
      exact iok_Good_mono (by rw [show iok_sum [] = 0 from rfl]; omega) (hg it hit)
  refine ⟨fun t ht => ?_, fun mi hmi => ?_⟩
  · obtain ⟨τ, hτ, hty⟩ := iok_mapM_mem hr.rt t ht
    have := iok_size_le_sum_of_mem hτ
    exact iok_need_of hty (hR τ hτ) (by omega)
  · -- the decoded item of `mi`
    have hdec : ∃ it ∈ bis.flatten ++ is, itemOf st.tt st.ct st.lt mi = some it := by
      rcases List.mem_append.1 hmi with hmi | hmi
      · obtain ⟨l, hl, hmil⟩ := List.mem_flatten.1 hmi
        obtain ⟨is', his', hdl⟩ := iok_mapM_mem hr.bodies l hl
        obtain ⟨it, hit, hdi⟩ := iok_mapM_mem hdl mi hmil
        exact ⟨it, List.mem_append_left _ (List.mem_flatten.2 ⟨is', his', hit⟩), hdi⟩
      · obtain ⟨it, hit, hdi⟩ := iok_mapM_mem hr.start mi hmi
        exact ⟨it, List.mem_append_right _ hit, hdi⟩
    obtain ⟨it, hit, hdi⟩ := hdec
    exact iok_itemOK_of_good hr.tt hj (by omega) (by omega) hdi (hgood it hit)

end Shallot.MacroPeg.Mach
