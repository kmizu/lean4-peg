import Cfg.Greibach.GNFBase

/-!
# Greibach normal form, stages 1–2: cleaning and removing the empty word

- `cleanG g`: drop every right side that mentions a missing nonterminal (such a side generates nothing).
  Exactly the same language (`gen_cleanG_iff`), and afterwards `RefsInRange`.
- `epsG g`: replace each right side by all its variants with some nullable nonterminals deleted, and drop
  the empty variants. It generates exactly the nonempty words of `g` (`gen_epsG_iff`), is `EpsFree`, and
  keeps `RefsInRange`.

Nullability (`Gen g j []`) is decided classically: only existence of the grammar is claimed.
-/

namespace Shallot.Cfg

/-! ## Stage 1: cleaning -/

/-- Every nonterminal of the right side is below `n`. -/
def rhsInRange (n : Nat) (r : Rhs) : Bool :=
  r.all fun s => match s with
    | .nt j => decide (j < n)
    | .t _ => true

/-- Drop the right sides that mention a missing nonterminal. -/
def cleanG (g : CFGrammar) : CFGrammar :=
  ⟨g.rules.map (fun alts => alts.filter (rhsInRange g.rules.length)), g.start⟩

/-- Cleaning keeps the number of nonterminals. -/
theorem cleanG_length (g : CFGrammar) : (cleanG g).rules.length = g.rules.length := by
  simp only [cleanG, List.length_map]

/-- A right side read under an interpretation whose nonterminals are all below `n` is in range. -/
theorem rhsInRange_of_semRhs {S : Nat → List Char → Prop} {n : Nat} (hS : ∀ j x, S j x → j < n) :
    ∀ (r : List Sym) (w : List Char), SemRhs S r w → rhsInRange n r = true
  | [], _, _ => rfl
  | .t _ :: r, _, h => by
      obtain ⟨w', _, h⟩ := h
      have := rhsInRange_of_semRhs hS r w' h
      simp only [rhsInRange, List.all_cons, Bool.true_and] at this ⊢
      exact this
  | .nt j :: r, _, h => by
      obtain ⟨w₁, w₂, _, h₁, h₂⟩ := h
      have := rhsInRange_of_semRhs hS r w₂ h₂
      simp only [rhsInRange, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
      exact ⟨hS j w₁ h₁, this⟩

/-- A nonterminal of an in-range right side is in range. -/
theorem lt_of_rhsInRange {n : Nat} {r : Rhs} (h : rhsInRange n r = true) {j : Nat} (hj : Sym.nt j ∈ r) :
    j < n := by
  simp only [rhsInRange, List.all_eq_true] at h
  have := h _ hj
  simp only [decide_eq_true_eq] at this
  exact this

/-- After cleaning, all references are in range. -/
theorem cleanG_refs (g : CFGrammar) : RefsInRange (cleanG g) := by
  intro alts halts rhs hrhs j hj
  simp only [cleanG, List.mem_map] at halts
  obtain ⟨a, _, rfl⟩ := halts
  rw [cleanG_length]
  exact lt_of_rhsInRange (List.mem_filter.mp hrhs).2 hj

/-- **Cleaning keeps the language** (for every nonterminal). -/
theorem gen_cleanG_iff (g : CFGrammar) (i : Nat) (w : List Char) : Gen (cleanG g) i w ↔ Gen g i w := by
  constructor
  · intro h
    refine gen_sound (g := cleanG g) (Gen g) (fun i alts rhs w halts hmem hr => ?_) h
    simp only [cleanG, altsAt_map, Option.map_eq_some_iff] at halts
    obtain ⟨a, ha, rfl⟩ := halts
    exact gen_of_rule ha (List.mem_filter.mp hmem).1 hr
  · intro h
    refine gen_sound (g := g) (Gen (cleanG g)) (fun i alts rhs w halts hmem hr => ?_) h
    have hin : rhsInRange g.rules.length rhs = true :=
      rhsInRange_of_semRhs (fun j x hx => cleanG_length g ▸ gen_lt hx) rhs w hr
    have halts' : altsAt (cleanG g).rules i = some (alts.filter (rhsInRange g.rules.length)) := by
      simp only [cleanG, altsAt_map, halts, Option.map_some]
    exact gen_of_rule halts' (List.mem_filter.mpr ⟨hmem, hin⟩) hr

/-! ## Stage 2: removing the empty word -/

open Classical in
/-- All variants of a right side with some nullable nonterminals deleted. -/
noncomputable def variants (g : CFGrammar) : List Sym → List Rhs
  | [] => [[]]
  | .t c :: r => (variants g r).map (.t c :: ·)
  | .nt j :: r => (variants g r).map (.nt j :: ·) ++ (if Gen g j [] then variants g r else [])

/-- The grammar without the empty word: all nonempty variants of every right side. -/
noncomputable def epsG (g : CFGrammar) : CFGrammar :=
  ⟨g.rules.map (fun alts => (alts.flatMap (variants g)).filter (fun r => !r.isEmpty)), g.start⟩

/-- Removing the empty word keeps the number of nonterminals. -/
theorem epsG_length (g : CFGrammar) : (epsG g).rules.length = g.rules.length := by
  simp only [epsG, List.length_map]

/-- The alternatives of `epsG g`. -/
theorem altsAt_epsG (g : CFGrammar) (i : Nat) :
    altsAt (epsG g).rules i =
      (altsAt g.rules i).map (fun alts => (alts.flatMap (variants g)).filter (fun r => !r.isEmpty)) := by
  simp only [epsG, altsAt_map]

/-- A variant only uses symbols of the original side. -/
theorem mem_of_mem_variants (g : CFGrammar) :
    ∀ (r r' : List Sym), r' ∈ variants g r → ∀ s ∈ r', s ∈ r
  | [], r', h, s, hs => by
      simp only [variants, List.mem_singleton] at h; subst h; exact absurd hs (List.not_mem_nil)
  | .t c :: r, r', h, s, hs => by
      simp only [variants, List.mem_map] at h
      obtain ⟨r'', h'', rfl⟩ := h
      rcases List.mem_cons.mp hs with rfl | hs
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_variants g r r'' h'' s hs)
  | .nt j :: r, r', h, s, hs => by
      simp only [variants, List.mem_append, List.mem_map] at h
      rcases h with ⟨r'', h'', rfl⟩ | h
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_of_mem_variants g r r'' h'' s hs)
      · split at h
        · exact List.mem_cons_of_mem _ (mem_of_mem_variants g r r' h s hs)
        · exact absurd h List.not_mem_nil

/-- A variant's words are words of the original side. -/
theorem semRhs_of_mem_variants (g : CFGrammar) :
    ∀ (r r' : List Sym) (w : List Char), r' ∈ variants g r → SemRhs (Gen g) r' w → SemRhs (Gen g) r w
  | [], r', w, h, hw => by
      simp only [variants, List.mem_singleton] at h; subst h; exact hw
  | .t c :: r, r', w, h, hw => by
      simp only [variants, List.mem_map] at h
      obtain ⟨r'', h'', rfl⟩ := h
      obtain ⟨w', rfl, hw⟩ := hw
      exact ⟨w', rfl, semRhs_of_mem_variants g r r'' w' h'' hw⟩
  | .nt j :: r, r', w, h, hw => by
      simp only [variants, List.mem_append, List.mem_map] at h
      rcases h with ⟨r'', h'', rfl⟩ | h
      · obtain ⟨w₁, w₂, rfl, h₁, h₂⟩ := hw
        exact ⟨w₁, w₂, rfl, h₁, semRhs_of_mem_variants g r r'' w₂ h'' h₂⟩
      · split at h
        · rename_i hnull
          exact ⟨[], w, rfl, hnull, semRhs_of_mem_variants g r r' w h hw⟩
        · exact absurd h List.not_mem_nil

/-- Every word of a side, read with nonempty pieces generated by `g'`, is a word of some variant. -/
theorem exists_variant (g g' : CFGrammar) :
    ∀ (r : List Sym) (w : List Char),
      SemRhs (fun j x => Gen g j x ∧ (x ≠ [] → Gen g' j x)) r w →
        ∃ r' ∈ variants g r, SemRhs (Gen g') r' w
  | [], w, h => ⟨[], by simp only [variants, List.mem_singleton], h⟩
  | .t c :: r, _, h => by
      obtain ⟨w', rfl, h⟩ := h
      obtain ⟨r', hr', hw'⟩ := exists_variant g g' r w' h
      exact ⟨.t c :: r', by simp only [variants, List.mem_map]; exact ⟨r', hr', rfl⟩, w', rfl, hw'⟩
  | .nt j :: r, _, h => by
      obtain ⟨w₁, w₂, rfl, ⟨h₁, h₁'⟩, h₂⟩ := h
      obtain ⟨r', hr', hw'⟩ := exists_variant g g' r w₂ h₂
      by_cases he : w₁ = []
      · subst he
        refine ⟨r', ?_, hw'⟩
        simp only [variants, List.mem_append, if_pos h₁]
        exact Or.inr hr'
      · refine ⟨.nt j :: r', ?_, w₁, w₂, rfl, h₁' he, hw'⟩
        simp only [variants, List.mem_append, List.mem_map]
        exact Or.inl ⟨r', hr', rfl⟩

/-- `epsG g` has no empty right side. -/
theorem epsG_epsFree (g : CFGrammar) : EpsFree (epsG g) := by
  intro alts halts rhs hrhs
  simp only [epsG, List.mem_map] at halts
  obtain ⟨a, _, rfl⟩ := halts
  have := (List.mem_filter.mp hrhs).2
  intro he; subst he; simp at this

/-- Removing the empty word keeps references in range. -/
theorem epsG_refs {g : CFGrammar} (hg : RefsInRange g) : RefsInRange (epsG g) := by
  intro alts halts rhs hrhs j hj
  simp only [epsG, List.mem_map] at halts
  obtain ⟨a, ha, rfl⟩ := halts
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp (List.mem_filter.mp hrhs).1
  rw [epsG_length]
  exact hg a ha r hr j (mem_of_mem_variants g r rhs hv _ hj)

/-- **Removing the empty word**: `epsG g` generates exactly the nonempty words of `g`. -/
theorem gen_epsG_iff (g : CFGrammar) (i : Nat) (w : List Char) :
    Gen (epsG g) i w ↔ Gen g i w ∧ w ≠ [] := by
  constructor
  · intro h
    refine ⟨?_, gen_ne_nil (epsG_epsFree g) h⟩
    refine gen_sound (g := epsG g) (Gen g) (fun i alts rhs w halts hmem hr => ?_) h
    rw [altsAt_epsG, Option.map_eq_some_iff] at halts
    obtain ⟨a, ha, rfl⟩ := halts
    obtain ⟨r, hr', hv⟩ := List.mem_flatMap.mp (List.mem_filter.mp hmem).1
    exact gen_of_rule ha hr' (semRhs_of_mem_variants g r rhs w hv hr)
  · rintro ⟨h, hne⟩
    have key := gen_sound (g := g) (fun j x => Gen g j x ∧ (x ≠ [] → Gen (epsG g) j x))
      (fun i alts rhs w halts hmem hr => by
        refine ⟨gen_of_rule halts hmem (semRhs_mono rhs w (fun _ _ _ h => h.1) hr), fun hw => ?_⟩
        obtain ⟨r', hr', hw'⟩ := exists_variant g (epsG g) rhs w hr
        have hne' : r' ≠ [] := by
          intro he; subst he; exact hw hw'
        have halts' := altsAt_epsG g i
        rw [halts, Option.map_some] at halts'
        refine gen_of_rule halts' (List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨rhs, hmem, hr'⟩, ?_⟩) hw'
        cases r' with
        | nil => exact absurd rfl hne'
        | cons _ _ => rfl) h
    exact key.2 hne

end Shallot.Cfg
