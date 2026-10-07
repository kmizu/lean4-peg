import Cfg.Semantics
import Cfg.Syntax

/-!
# Greibach normal form: generic tools

Small lemmas used by every stage of the construction of Greibach's standard form
(`Cfg/Greibach/GNF.lean`):

- `altsAt` agrees with list indexing, commutes with `map`, and is computed on `(List.range M).map f`.
- `SemRhs S rhs w`: `rhs` yields `w` when each nonterminal `j` is read as the language `S j`.
  `GenRhs g` is exactly `SemRhs (Gen g)`.
- `gen_sound`: `Gen g` is contained in every rule-closed interpretation (the induction principle used
  throughout).
- `len_induction`: strong induction on the length of the generated word.
-/

namespace Shallot.Cfg

/-! ## `altsAt` -/

/-- `altsAt` is list indexing. -/
theorem altsAt_eq_getElem? : ∀ (l : List (List Rhs)) (i : Nat), altsAt l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rs, n + 1 => by simp only [altsAt, List.getElem?_cons_succ]; exact altsAt_eq_getElem? rs n

/-- `altsAt` commutes with mapping the alternative lists. -/
theorem altsAt_map (f : List Rhs → List Rhs) (l : List (List Rhs)) (i : Nat) :
    altsAt (l.map f) i = (altsAt l i).map f := by
  rw [altsAt_eq_getElem?, altsAt_eq_getElem?, List.getElem?_map]

/-- A defined index is in range. -/
theorem altsAt_some_lt {l : List (List Rhs)} {i : Nat} {a : List Rhs} (h : altsAt l i = some a) :
    i < l.length := by
  rw [altsAt_eq_getElem?] at h
  exact (List.getElem?_eq_some_iff.mp h).1

/-- A defined alternative list is a member of the rule list. -/
theorem altsAt_some_mem {l : List (List Rhs)} {i : Nat} {a : List Rhs} (h : altsAt l i = some a) :
    a ∈ l := by
  rw [altsAt_eq_getElem?] at h
  exact List.mem_of_getElem? h

/-- Every in-range index is defined. -/
theorem altsAt_of_lt {l : List (List Rhs)} {i : Nat} (h : i < l.length) : ∃ a, altsAt l i = some a :=
  ⟨l[i], by rw [altsAt_eq_getElem?]; exact List.getElem?_eq_getElem h⟩

/-- `altsAt` on a tabulated rule list. -/
theorem altsAt_range_map (f : Nat → List Rhs) (M i : Nat) :
    altsAt ((List.range M).map f) i = if i < M then some (f i) else none := by
  rw [altsAt_eq_getElem?, List.getElem?_map]
  by_cases h : i < M
  · rw [List.getElem?_range h, if_pos h]; rfl
  · rw [if_neg h, List.getElem?_eq_none (by simp only [List.length_range]; omega)]; rfl

/-! ## Reading a right side under an interpretation -/

/-- `rhs` yields `w` when each nonterminal `j` is read as the language `S j`. -/
def SemRhs (S : Nat → List Char → Prop) : List Sym → List Char → Prop
  | [], w => w = []
  | .t c :: r, w => ∃ w', w = c :: w' ∧ SemRhs S r w'
  | .nt j :: r, w => ∃ w₁ w₂, w = w₁ ++ w₂ ∧ S j w₁ ∧ SemRhs S r w₂

/-- `SemRhs` of a concatenation splits the word. -/
theorem semRhs_append (S : Nat → List Char → Prop) :
    ∀ (r₁ r₂ : List Sym) (w : List Char),
      SemRhs S (r₁ ++ r₂) w ↔ ∃ w₁ w₂, w = w₁ ++ w₂ ∧ SemRhs S r₁ w₁ ∧ SemRhs S r₂ w₂
  | [], r₂, w => by
      simp only [List.nil_append, SemRhs]
      constructor
      · intro h; exact ⟨[], w, rfl, rfl, h⟩
      · rintro ⟨w₁, w₂, rfl, rfl, h⟩; exact h
  | .t c :: r, r₂, w => by
      simp only [List.cons_append, SemRhs]
      constructor
      · rintro ⟨w', rfl, h⟩
        obtain ⟨u, v, rfl, hu, hv⟩ := (semRhs_append S r r₂ w').mp h
        exact ⟨c :: u, v, rfl, ⟨u, rfl, hu⟩, hv⟩
      · rintro ⟨_, v, rfl, ⟨u, rfl, hu⟩, hv⟩
        exact ⟨u ++ v, rfl, (semRhs_append S r r₂ _).mpr ⟨u, v, rfl, hu, hv⟩⟩
  | .nt j :: r, r₂, w => by
      simp only [List.cons_append, SemRhs]
      constructor
      · rintro ⟨x, w', rfl, hx, h⟩
        obtain ⟨u, v, rfl, hu, hv⟩ := (semRhs_append S r r₂ w').mp h
        exact ⟨x ++ u, v, by rw [List.append_assoc], ⟨x, u, rfl, hx, hu⟩, hv⟩
      · rintro ⟨_, v, rfl, ⟨x, u, rfl, hx, hu⟩, hv⟩
        exact ⟨x, u ++ v, by rw [List.append_assoc], hx, (semRhs_append S r r₂ _).mpr ⟨u, v, rfl, hu, hv⟩⟩

/-- `SemRhs` of a single nonterminal. -/
theorem semRhs_single_nt (S : Nat → List Char → Prop) (j : Nat) (w : List Char) :
    SemRhs S [.nt j] w ↔ S j w := by
  simp only [SemRhs]
  constructor
  · rintro ⟨w₁, w₂, rfl, h, rfl⟩; rw [List.append_nil]; exact h
  · intro h; exact ⟨w, [], (List.append_nil w).symm, h, rfl⟩

/-- Monotonicity of `SemRhs`, needing the inclusion only for words no longer than the whole. -/
theorem semRhs_mono {S S' : Nat → List Char → Prop} :
    ∀ (r : List Sym) (w : List Char), (∀ j x, x.length ≤ w.length → S j x → S' j x) →
      SemRhs S r w → SemRhs S' r w
  | [], _, _, h => h
  | .t c :: r, w, hS, h => by
      obtain ⟨w', rfl, h⟩ := h
      exact ⟨w', rfl, semRhs_mono r w' (fun j x hx => hS j x (by simp only [List.length_cons]; omega)) h⟩
  | .nt j :: r, w, hS, h => by
      obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := h
      refine ⟨w₁, w₂, rfl, hS j w₁ (by simp only [List.length_append]; omega) h₁,
        semRhs_mono r w₂ (fun k x hx => hS k x (by simp only [List.length_append]; omega)) h₂⟩

/-- A nonempty right side whose nonterminals only yield nonempty words yields a nonempty word. -/
theorem semRhs_ne_nil {S : Nat → List Char → Prop} (hS : ∀ j x, S j x → x ≠ []) :
    ∀ (r : List Sym) (w : List Char), r ≠ [] → SemRhs S r w → w ≠ []
  | [], _, h, _ => absurd rfl h
  | .t _ :: _, _, _, h => by obtain ⟨_, rfl, _⟩ := h; exact List.cons_ne_nil _ _
  | .nt j :: _, _, _, h => by
      obtain ⟨w₁, w₂, rfl, h₁, _⟩ := h
      intro he
      exact hS j w₁ h₁ (List.append_eq_nil_iff.mp he).1

/-! ## `Gen` as the least rule-closed interpretation -/

/-- **The induction principle**: `Gen g` is contained in every interpretation closed under the rules. -/
theorem gen_sound {g : CFGrammar} (S : Nat → List Char → Prop)
    (hS : ∀ i alts rhs w, altsAt g.rules i = some alts → rhs ∈ alts → SemRhs S rhs w → S i w)
    {i : Nat} {w : List Char} (h : Gen g i w) : S i w :=
  Gen.rec (motive_1 := fun i w _ => S i w) (motive_2 := fun rhs w _ => SemRhs S rhs w)
    (fun i alts _ _ halts hmem _ ih => hS i alts _ _ halts hmem ih)
    rfl
    (fun _ _ w _ ih => ⟨w, rfl, ih⟩)
    (fun _ _ w₁ w₂ _ _ ih₁ ih₂ => ⟨w₁, w₂, rfl, ih₁, ih₂⟩) h

/-- `SemRhs (Gen g)` yields `GenRhs g`. -/
theorem genRhs_of_semRhs {g : CFGrammar} :
    ∀ (r : List Sym) (w : List Char), SemRhs (Gen g) r w → GenRhs g r w
  | [], _, h => by rw [show _ = [] from h]; exact GenRhs.nil
  | .t c :: r, _, h => by
      obtain ⟨w', rfl, h⟩ := h
      exact GenRhs.cons_t c r w' (genRhs_of_semRhs r w' h)
  | .nt j :: r, _, h => by
      obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := h
      exact GenRhs.cons_nt j r w₁ w₂ h₁ (genRhs_of_semRhs r w₂ h₂)

/-- `GenRhs g` yields `SemRhs (Gen g)`. -/
theorem semRhs_of_genRhs {g : CFGrammar} :
    ∀ {r : List Sym} {w : List Char}, GenRhs g r w → SemRhs (Gen g) r w
  | [], _, h => by cases h; rfl
  | .t _ :: _, _, h => by cases h with | cons_t _ _ w h => exact ⟨w, rfl, semRhs_of_genRhs h⟩
  | .nt _ :: _, _, h => by
      cases h with | cons_nt _ _ w₁ w₂ h₁ h₂ => exact ⟨w₁, w₂, rfl, h₁, semRhs_of_genRhs h₂⟩

/-- One rule application. -/
theorem gen_of_rule {g : CFGrammar} {i : Nat} {alts : List Rhs} {rhs : Rhs} {w : List Char}
    (halts : altsAt g.rules i = some alts) (hmem : rhs ∈ alts) (h : SemRhs (Gen g) rhs w) : Gen g i w :=
  Gen.prod i alts rhs w halts hmem (genRhs_of_semRhs rhs w h)

/-- Inverting one rule application. -/
theorem gen_cases {g : CFGrammar} {i : Nat} {w : List Char} (h : Gen g i w) :
    ∃ alts rhs, altsAt g.rules i = some alts ∧ rhs ∈ alts ∧ SemRhs (Gen g) rhs w := by
  cases h with
  | prod _ alts rhs _ halts hmem hrhs => exact ⟨alts, rhs, halts, hmem, semRhs_of_genRhs hrhs⟩

/-- A generating nonterminal is in range. -/
theorem gen_lt {g : CFGrammar} {i : Nat} {w : List Char} (h : Gen g i w) : i < g.rules.length := by
  obtain ⟨_, _, halts, _, _⟩ := gen_cases h
  exact altsAt_some_lt halts

/-- In a grammar without empty right sides, every generated word is nonempty. -/
theorem gen_ne_nil {g : CFGrammar} (hne : ∀ alts ∈ g.rules, ∀ rhs ∈ alts, rhs ≠ [])
    {i : Nat} {w : List Char} (h : Gen g i w) : w ≠ [] :=
  gen_sound (g := g) (fun _ x => x ≠ [])
    (fun _ _ rhs _ halts hmem hr => semRhs_ne_nil (fun _ _ h => h) rhs _
      (hne _ (altsAt_some_mem halts) rhs hmem) hr) h

/-! ## Strong induction on the word length -/

/-- Strong induction on the length of the word. -/
theorem len_induction (P : Nat → List Char → Prop)
    (step : ∀ i w, (∀ j x, x.length < w.length → P j x) → P i w) : ∀ i w, P i w := by
  have key : ∀ k i (w : List Char), w.length ≤ k → P i w := by
    intro k
    induction k with
    | zero => intro i w hw; exact step i w (fun j x hx => absurd hx (by omega))
    | succ k ih => intro i w hw; exact step i w (fun j x hx => ih j x (by omega))
  exact fun i w => key w.length i w (Nat.le_refl _)

/-! ## Symbols and ranges -/

/-- All nonterminals in the grammar's right sides are in range. -/
def RefsInRange (g : CFGrammar) : Prop :=
  ∀ alts ∈ g.rules, ∀ rhs ∈ alts, ∀ j, Sym.nt j ∈ rhs → j < g.rules.length

/-- No empty right side. -/
def EpsFree (g : CFGrammar) : Prop := ∀ alts ∈ g.rules, ∀ rhs ∈ alts, rhs ≠ []

/-- A unit right side: a single nonterminal. -/
def isUnitRhs : Rhs → Bool
  | [.nt _] => true
  | _ => false

/-- No unit right side. -/
def UnitFree (g : CFGrammar) : Prop := ∀ alts ∈ g.rules, ∀ rhs ∈ alts, isUnitRhs rhs = false

/-- A character's code is below `0x110000`. -/
theorem char_toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have h := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at h
  show c.val.toNat < _
  omega

end Shallot.Cfg
