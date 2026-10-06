import MacroPeg.HigherOrder.Mach.EvalNum

/-!
# The order check on the tables of a reading

`ordNum`: the order of type number `k`, from the arrow table. `ordOK j st`: every rule type has order `≤ j` and every
lambda item binds a type of order `< j` — exactly `GOrd j g s` for the grammar and start that were read (`ordOK_iff`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-- The order of type number `k`. -/
def ordNum (tt : List (Nat × Nat)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    match tt[k]? with
    | some (a, b) => if a ≤ k ∧ b ≤ k then max (ordNum tt a + 1) (ordNum tt b) else 0
    | none => 0
termination_by k => k
decreasing_by all_goals omega

/-- The order check on a finished reading. -/
def ordOK (j : Nat) (st : PSt) : Bool :=
  st.rt.all (fun t => decide (ordNum st.tt t ≤ j)) &&
    (st.bodies.flatten ++ st.start).all (fun it => it.tag != 11 || decide (ordNum st.tt it.a + 1 ≤ j))

/-! ## `ordNum` is the order -/

/-- On a number that decodes, `ordNum` is the order of the decoded type. -/
theorem ordNum_eq {tt : List (Nat × Nat)} : ∀ (k : Nat) {τ : HO.Ty}, tyOf tt k = some τ → ordNum tt k = τ.order
  | 0, τ, h => by rw [tyOf] at h; cases h; rw [ordNum, Ty.order]
  | k + 1, τ, h => by
    rw [tyOf] at h
    split at h
    · rename_i a b hk
      split at h
      · rename_i hab
        split at h
        · rename_i σ ρ hσ hρ
          cases h
          rw [ordNum]; simp only [hk]
          rw [if_pos hab, ordNum_eq a hσ, ordNum_eq b hρ, Ty.order]
        · cases h
      · cases h
    · cases h

/-! ## Lambdas in a list of items -/

/-- Every lambda item of `is` binds a type of order `< j`. -/
def LamOK (j : Nat) (is : List Item) : Prop :=
  ∀ it ∈ is, ∀ a σ, it.op = .lam a σ → a.order + 1 ≤ j

theorem lamOK_append {j : Nat} {l₁ l₂ : List Item} : LamOK j (l₁ ++ l₂) ↔ LamOK j l₁ ∧ LamOK j l₂ := by
  unfold LamOK
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun it hi => h it (Or.inl hi), fun it hi => h it (Or.inr hi)⟩
  · rintro ⟨h₁, h₂⟩ it (hi | hi)
    · exact h₁ it hi
    · exact h₂ it hi

/-- A single item that is not a lambda never violates the bound. -/
theorem lamOK_single_nonlam {j : Nat} {op : Op} {Γ : List HO.Ty} (hop : ∀ a σ, op ≠ .lam a σ) :
    LamOK j [⟨op, Γ⟩] := by
  intro it hi a σ he
  simp only [List.mem_singleton] at hi
  subst hi
  exact absurd he (hop a σ)

/-- A leaf that is not a lambda: lambda order `0`, and its single item is fine. -/
theorem lamOK_leaf {j : Nat} {op : Op} {Γ : List HO.Ty} (hop : ∀ a σ, op ≠ .lam a σ) :
    0 ≤ j ↔ LamOK j [⟨op, Γ⟩] :=
  ⟨fun _ => lamOK_single_nonlam hop, fun _ => Nat.zero_le _⟩

theorem lamOK_single_lam {j : Nat} {a σ : HO.Ty} {Γ : List HO.Ty} :
    LamOK j [⟨.lam a σ, Γ⟩] ↔ a.order + 1 ≤ j := by
  constructor
  · intro h; exact h _ List.mem_cons_self a σ rfl
  · intro h it hi a' σ' he
    simp only [List.mem_singleton] at hi
    subst hi
    cases he
    exact h

/-- **The lambda order of a typed term is read off its items.** -/
theorem lamOrd_erase_le {R : List HO.Ty} (j : Nat) :
    ∀ {Γ : List HO.Ty} {τ : HO.Ty} (t : Tm R Γ τ), KExp.lamOrd t.erase ≤ j ↔ LamOK j (items t)
  | _, _, .eps => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .any => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .chr c => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .range lo hi => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .lit s => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .var i _ => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .rule i _ => by simp only [Tm.erase, KExp.lamOrd, items]; exact lamOK_leaf (by simp)
  | _, _, .seq a b => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, Nat.max_le, lamOrd_erase_le j a, lamOrd_erase_le j b]
    rw [and_iff_left (lamOK_single_nonlam (by simp))]
  | _, _, .alt a b => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, Nat.max_le, lamOrd_erase_le j a, lamOrd_erase_le j b]
    rw [and_iff_left (lamOK_single_nonlam (by simp))]
  | _, _, .star a => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, lamOrd_erase_le j a]
    rw [and_iff_left (lamOK_single_nonlam (by simp))]
  | _, _, .notP a => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, lamOrd_erase_le j a]
    rw [and_iff_left (lamOK_single_nonlam (by simp))]
  | _, _, .app f y => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, Nat.max_le, lamOrd_erase_le j f, lamOrd_erase_le j y]
    rw [and_iff_left (lamOK_single_nonlam (by simp))]
  | _, _, .lam body => by
    simp only [Tm.erase, KExp.lamOrd, items, lamOK_append, Nat.max_le, lamOrd_erase_le j body, lamOK_single_lam]
    exact And.comm

/-! ## The check on machine items -/

/-- A lambda operation comes only from tag `11`, with a binder number that decodes. -/
theorem opOf_lam {tt : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {a σ : HO.Ty}
    (h : opOf tt lt it = some (.lam a σ)) : it.tag = 11 ∧ tyOf tt it.a = some a := by
  unfold opOf at h
  split at h
  all_goals first
    | (simp at h; done)
    | (rename_i htag; split at h <;> cases h; exact ⟨htag, by assumption⟩)
    | (split at h <;> cases h)

/-- Tag `11` gives a lambda operation. -/
theorem opOf_tag11 {tt : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {op : Op}
    (h : opOf tt lt it = some op) (htag : it.tag = 11) : ∃ a σ, op = .lam a σ ∧ tyOf tt it.a = some a := by
  unfold opOf at h
  rw [htag] at h
  simp only at h
  split at h
  · rename_i a σ ha _
    cases h
    exact ⟨a, σ, rfl, ha⟩
  · cases h

/-- The machine check of one item. -/
def itemCheck (j : Nat) (tt : List (Nat × Nat)) (it : MItem) : Bool :=
  it.tag != 11 || decide (ordNum tt it.a + 1 ≤ j)

/-- The check of one decoded item is the bound on its lambda. -/
theorem itemCheck_iff {j : Nat} {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {it : MItem} {item : Item}
    (h : itemOf tt ct lt it = some item) :
    itemCheck j tt it = true ↔ ∀ a σ, item.op = .lam a σ → a.order + 1 ≤ j := by
  unfold itemOf at h
  split at h
  · rename_i op Γ hop _
    cases h
    by_cases htag : it.tag = 11
    · obtain ⟨a, σ, rfl, ha⟩ := opOf_tag11 hop htag
      simp only [itemCheck, htag, bne_self_eq_false, Bool.false_or, decide_eq_true_eq, ordNum_eq _ ha]
      constructor
      · intro hb a' σ' he; cases he; exact hb
      · intro hb; exact hb a σ rfl
    · have hc : itemCheck j tt it = true := by simp [itemCheck, htag]
      simp only [hc, true_iff]
      intro a σ he
      exact absurd (opOf_lam (he ▸ hop)).1 htag
  · cases h

/-- `all` on a list that maps to `r` is `∀` on `r`, given the per-element correspondence. -/
theorem all_of_mapM {α β : Type} {f : α → Option β} {p : α → Bool} {q : β → Prop}
    (hpq : ∀ a b, f a = some b → (p a = true ↔ q b)) :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → (l.all p = true ↔ ∀ b ∈ r, q b)
  | [], r, h => by
    simp at h
    subst h
    simp
  | a :: l, r, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_some h
    simp only [List.all_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp, hpq a b hb,
      all_of_mapM hpq hbs]

/-- The check of a decoded list of items is `LamOK`. -/
theorem itemsCheck_iff {j : Nat} {tt ct : List (Nat × Nat)} {lt : List (List Nat)} {l : List MItem}
    {is : List Item} (h : itemsOf tt ct lt l = some is) : l.all (itemCheck j tt) = true ↔ LamOK j is :=
  all_of_mapM (fun _ _ hb => itemCheck_iff hb) h

/-! ## The grammar side -/

theorem foldr_max_le (j : Nat) : ∀ l : List Nat, l.foldr max 0 ≤ j ↔ ∀ n ∈ l, n ≤ j
  | [] => by simp
  | n :: l => by simp only [List.foldr_cons, Nat.max_le, foldr_max_le j l, List.mem_cons, forall_eq_or_imp]

theorem order_le_iff (j : Nat) (g : HGrammar) : g.order ≤ j ↔ ∀ τ ∈ g.types, τ.order ≤ j := by
  simp only [HGrammar.order, foldr_max_le, HGrammar.types, List.mem_map]
  constructor
  · rintro h τ ⟨r, hr, rfl⟩; exact h _ ⟨r, hr, rfl⟩
  · rintro h n ⟨r, hr, rfl⟩; exact h _ ⟨r, hr, rfl⟩

/-- The rules of typed bodies satisfy the lambda bound iff their items do. -/
theorem bodies_lamOrd_iff {R : List HO.Ty} (j : Nat) : ∀ {S : List HO.Ty} (ts : TBodies R S),
    (∀ r ∈ List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) S ts.erase, KExp.lamOrd r.body ≤ j) ↔
      ∀ is ∈ bodyItems ts, LamOK j is
  | [], _ => by simp [TBodies.erase, bodyItems]
  | _ :: _, (t, ts) => by
    simp only [TBodies.erase, bodyItems, List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp,
      lamOrd_erase_le j t, bodies_lamOrd_iff j ts]

/-- **The order check on a finished reading decides `GOrd`.** -/
theorem ordOK_iff (j : Nat) {st : PSt} {g : HGrammar} {s : HExp} {x : List Char} {bis : List (List Item)}
    {is : List Item} (hr : ReadOK st g.types bis is x) (hcr : checkRules g = some bis)
    (hinf : inferE g.types [] s = some (.p, is)) : ordOK j st = true ↔ KExp.GOrd j g s := by
  -- rule types
  have hrt : st.rt.all (fun t => decide (ordNum st.tt t ≤ j)) = true ↔ g.order ≤ j := by
    rw [order_le_iff]
    exact all_of_mapM (p := fun t => decide (ordNum st.tt t ≤ j)) (q := fun τ => τ.order ≤ j)
      (fun _ _ hb => by rw [decide_eq_true_eq, ordNum_eq _ hb]) hr.rt
  -- bodies
  obtain ⟨G, hG, hbis⟩ := checkRules_sound hcr
  have hrules : g.rules = List.zipWith (fun τ b => (⟨τ, b⟩ : HRule)) g.types G.bodies.erase :=
    (congrArg HGrammar.rules hG).symm
  have hbod : st.bodies.all (fun l => l.all (itemCheck j st.tt)) = true ↔
      ∀ r ∈ g.rules, KExp.lamOrd r.body ≤ j := by
    rw [hrules, bodies_lamOrd_iff j G.bodies, hbis]
    exact all_of_mapM (fun _ _ hb => itemsCheck_iff hb) hr.bodies
  -- start
  obtain ⟨t, hts, hti⟩ := inferE_sound _ hinf
  have hst : st.start.all (itemCheck j st.tt) = true ↔ KExp.lamOrd s ≤ j := by
    rw [← hts, lamOrd_erase_le j t, hti]
    exact itemsCheck_iff hr.start
  have hdef : ordOK j st = (st.rt.all (fun t => decide (ordNum st.tt t ≤ j)) &&
      (st.bodies.all (fun l => l.all (itemCheck j st.tt)) && st.start.all (itemCheck j st.tt))) := by
    simp only [ordOK, List.all_append, List.all_flatten]; rfl
  rw [hdef, Bool.and_eq_true, Bool.and_eq_true, hrt, hbod, hst]
  rfl

end Shallot.MacroPeg.Mach
