import MacroPeg.HigherOrder.Typed
import MacroPeg.Properties.FiniteArgs

/-!
# A finite model of the types

Fix the input length `N`. A position is the number `q ≤ N` of symbols left. The meaning of a type is finite data:

* `Dom .p`: a parser's result at each position `0, …, N` — a list of `Res`, where `none` = no result (yet),
  `some none` = failure and `some (some j)` = success leaving `j` symbols;
* `Dom (a ⇒ b)`: a function, as the table of its values on `elems N a`, the list of all *well-formed* values of `a`
  (`elems`), in that order. `Dom.app f d` looks `d` up.

Values are ordered by information (`Dom.le`): `none ≤ r` at every position, pointwise on tables. A strictly larger
value has strictly more defined entries (`defCount_lt`), and a well-formed value has at most `maxCount N τ` of them —
so an increasing chain of rule tables stops growing after `Σ maxCount` steps. `maxCount N τ` and `(elems N τ).length`
grow as a tower of exponentials whose height is the order of `τ`.
-/

namespace Shallot.MacroPeg.HO

/-- The result at one position: `none` = no result, `some none` = failure, `some (some j)` = `j` symbols left. -/
abbrev Res := Option (Option Nat)

/-- The results possible at positions `≤ N`. -/
def resElems (N : Nat) : List Res := none :: some none :: (List.range (N + 1)).map (fun j => some (some j))

/-- All lists of length `m` over `xs`. -/
def allVecs {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | m + 1 => xs.flatMap (fun a => (allVecs xs m).map (a :: ·))

theorem mem_allVecs {α : Type} (xs : List α) :
    ∀ (m : Nat) (l : List α), l ∈ allVecs xs m ↔ l.length = m ∧ ∀ a ∈ l, a ∈ xs
  | 0, l => by cases l <;> simp [allVecs]
  | m + 1, l => by
    cases l with
    | nil => simp [allVecs]
    | cons a l =>
      simp only [allVecs, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons, List.mem_cons,
        forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨a', ha', l', hl', rfl, rfl⟩
        exact ⟨((mem_allVecs xs m l').1 hl').1, ha', ((mem_allVecs xs m l').1 hl').2⟩
      · rintro ⟨hl, ha, hrest⟩
        exact ⟨a, ha, l, (mem_allVecs xs m l).2 ⟨hl, hrest⟩, rfl, rfl⟩

/-! ## Values -/

def Dom : Ty → Type
  | .p => List Res
  | .arr _ b => List (Dom b)

instance Dom.decEq : (τ : Ty) → DecidableEq (Dom τ)
  | .p => inferInstanceAs (DecidableEq (List Res))
  | .arr _ b => @instDecidableEqList _ (Dom.decEq b)

/-- All well-formed values of `τ`, in a fixed order. -/
def elems (N : Nat) : (τ : Ty) → List (Dom τ)
  | .p => allVecs (resElems N) (N + 1)
  | .arr a b => allVecs (elems N b) (elems N a).length

/-- The least value: no result anywhere. -/
def bot (N : Nat) : (τ : Ty) → Dom τ
  | .p => List.replicate (N + 1) none
  | .arr a b => List.replicate (elems N a).length (bot N b)

/-- Apply a table to a value (the least value if the argument is not well formed). -/
def Dom.app {N : Nat} {a b : Ty} (f : Dom (a ⇒ b)) (d : Dom a) : Dom b :=
  (f : List (Dom b)).getD (indexIn d (elems N a)) (bot N b)

/-! ## The information order -/

/-- Two lists of the same length, related entry by entry. -/
inductive Pw {α : Type} (R : α → α → Prop) : List α → List α → Prop where
  | nil : Pw R [] []
  | cons {a b : α} {l l' : List α} : R a b → Pw R l l' → Pw R (a :: l) (b :: l')

def Dom.le : (τ : Ty) → Dom τ → Dom τ → Prop
  | .p, d, d' => Pw (fun r s => r = none ∨ r = s) (d : List Res) d'
  | .arr _ b, f, f' => Pw (Dom.le b) (f : List (Dom b)) f'

theorem forall₂_refl {α : Type} {R : α → α → Prop} (h : ∀ a, R a a) : ∀ l : List α, Pw R l l
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_refl h l)

theorem forall₂_trans {α : Type} {R : α → α → Prop} (h : ∀ a b c, R a b → R b c → R a c) :
    ∀ {l₁ l₂ l₃ : List α}, Pw R l₁ l₂ → Pw R l₂ l₃ → Pw R l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (h _ _ _ h₁ h₂) (forall₂_trans h t₁ t₂)

theorem Dom.le_refl : ∀ (τ : Ty) (d : Dom τ), Dom.le τ d d
  | .p, d => forall₂_refl (fun _ => .inr rfl) (d : List Res)
  | .arr _ b, f => forall₂_refl (Dom.le_refl b) (f : List (Dom b))

theorem Dom.le_trans : ∀ (τ : Ty) (d₁ d₂ d₃ : Dom τ), Dom.le τ d₁ d₂ → Dom.le τ d₂ d₃ → Dom.le τ d₁ d₃
  | .p, _, _, _, h₁, h₂ => forall₂_trans (R := fun r s : Res => r = none ∨ r = s) (fun r s t hrs hst => by
      rcases hrs with rfl | rfl
      · exact .inl rfl
      · exact hst) h₁ h₂
  | .arr _ b, _, _, _, h₁, h₂ => forall₂_trans (Dom.le_trans b) h₁ h₂

/-! ## Counting defined entries -/

/-- The number of defined entries. -/
def defCount : (τ : Ty) → Dom τ → Nat
  | .p, d => ((d : List Res).filter Option.isSome).length
  | .arr _ b, f => ((f : List (Dom b)).map (defCount b)).sum

/-- An upper bound on `defCount` for well-formed values. -/
def maxCount (N : Nat) : Ty → Nat
  | .p => N + 1
  | .arr a b => (elems N a).length * maxCount N b

theorem sum_map_le {α : Type} (f : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ a ∈ l, f a ≤ c) → (l.map f).sum ≤ l.length * c
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := sum_map_le f c l (fun b hb => h b (by simp [hb]))
    have := h a (by simp)
    omega

theorem defCount_le_maxCount (N : Nat) : ∀ (τ : Ty) (d : Dom τ), d ∈ elems N τ → defCount τ d ≤ maxCount N τ
  | .p, d, h => by
    have hl := ((mem_allVecs _ _ _).1 h).1
    simp only [defCount, maxCount]
    have := List.length_filter_le Option.isSome (d : List Res)
    omega
  | .arr a b, f, h => by
    obtain ⟨hl, hmem⟩ := (mem_allVecs _ _ _).1 h
    simp only [defCount, maxCount]
    rw [← hl]
    exact sum_map_le _ _ _ (fun d hd => defCount_le_maxCount N b d (hmem d hd))

theorem defCount_mono : ∀ (τ : Ty) {d d' : Dom τ}, Dom.le τ d d' → defCount τ d ≤ defCount τ d'
  | .p, _, _, h => by
    simp only [defCount]
    induction h with
    | nil => exact Nat.le_refl _
    | cons hrs _ ih =>
      rcases hrs with rfl | rfl
      · simp only [List.filter_cons, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        split <;> (try simp only [List.length_cons]) <;> omega
      · simp only [List.filter_cons]; split <;> simp [ih]
  | .arr _ b, _, _, h => by
    simp only [defCount]
    induction h with
    | nil => exact Nat.le_refl _
    | cons hd _ ih =>
      simp only [List.map_cons, List.sum_cons]
      have := defCount_mono b hd
      omega

/-- A strictly larger value has strictly more defined entries. -/
theorem defCount_lt : ∀ (τ : Ty) {d d' : Dom τ}, Dom.le τ d d' → d ≠ d' → defCount τ d < defCount τ d'
  | .p, _, _, h, hne => by
    simp only [defCount]
    induction h with
    | nil => exact absurd rfl hne
    | @cons r s l l' hrs hrest ih =>
      have hle : (l.filter Option.isSome).length ≤ (l'.filter Option.isSome).length := defCount_mono .p hrest
      by_cases hl : l = l'
      · subst hl
        rcases hrs with rfl | rfl
        · cases s with
          | none => exact absurd rfl hne
          | some s => simp
        · exact absurd rfl hne
      · have := ih hl
        rcases hrs with rfl | rfl
        · simp only [List.filter_cons, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          split <;> (try simp only [List.length_cons]) <;> omega
        · simp only [List.filter_cons]; split <;> simp [this]
  | .arr _ b, _, _, h, hne => by
    simp only [defCount]
    induction h with
    | nil => exact absurd rfl hne
    | @cons u v l l' huv hrest ih =>
      simp only [List.map_cons, List.sum_cons]
      have h₁ := defCount_mono b huv
      have h₂ : (l.map (defCount b)).sum ≤ (l'.map (defCount b)).sum := defCount_mono (.arr .p b) hrest
      by_cases hl : l = l'
      · subst hl
        have : u ≠ v := fun e => hne (by rw [e])
        have := defCount_lt b huv this
        omega
      · have := ih hl
        omega

/-! ## The least value -/

theorem bot_mem (N : Nat) : ∀ τ : Ty, bot N τ ∈ elems N τ
  | .p => (mem_allVecs _ _ _).2 ⟨by simp [bot], fun r hr => by
      simp only [bot, List.mem_replicate] at hr; rw [hr.2]; simp [resElems]⟩
  | .arr a b => (mem_allVecs _ _ _).2 ⟨by simp [bot], fun d hd => by
      simp only [bot, List.mem_replicate] at hd; rw [hd.2]; exact bot_mem N b⟩

theorem pw_replicate {α : Type} {R : α → α → Prop} (b : α) :
    ∀ l : List α, (∀ e ∈ l, R b e) → Pw R (List.replicate l.length b) l
  | [], _ => .nil
  | e :: l, h => .cons (h e (by simp)) (pw_replicate b l (fun e' he' => h e' (by simp [he'])))

theorem bot_le (N : Nat) : ∀ (τ : Ty) (d : Dom τ), d ∈ elems N τ → Dom.le τ (bot N τ) d
  | .p, d, h => by
    obtain ⟨hl, _⟩ := (mem_allVecs _ _ _).1 h
    simp only [Dom.le, bot]
    rw [← hl]
    exact pw_replicate none (d : List Res) (fun _ _ => Or.inl rfl)
  | .arr a b, f, h => by
    obtain ⟨hl, hmem⟩ := (mem_allVecs _ _ _).1 h
    simp only [Dom.le, bot]
    rw [← hl]
    exact pw_replicate (bot N b) (f : List (Dom b)) (fun d hd => bot_le N b d (hmem d hd))

end Shallot.MacroPeg.HO
