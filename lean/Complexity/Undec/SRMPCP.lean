import Complexity.Undec.Defs

/-!
# Rewriting reduces to the modified correspondence problem

Following Forster, Heiter and Smolka (ITP 2018). Symbols of the rewriting system are below `n`; two fresh
symbols are added, `$ = n` and `# = n + 1`. The first card is `($, $ x #)`; the other cards are

* `(l, r)` for every rule `l → r`,
* `(#, #)`,
* `(a, a)` for every symbol `a < n`,
* the closing card `(y # $, $)`.

The first card itself is not among the other cards (it is not needed). A solution reads, on the top, the
string `x # x₁ # ⋯ # y # $`, and on the bottom the same string shifted by one segment: each segment is
rewritten into the next by the copy and rule cards above it.
-/

namespace Complexity.Undec

/-- The first card `($, $ x #)`. -/
def srFirst (x : Word) (n : Nat) : Card := ([n], n :: (x ++ [n + 1]))

/-- The cards for the rules, the separator, the copies and the closing card. -/
def srCards (R : SRS) (y : Word) (n : Nat) : List Card :=
  R ++ ([n + 1], [n + 1]) :: ((List.range n).map (fun a => ([a], [a])) ++ [(y ++ [n + 1, n], [n])])

/-! ## Tops and bottoms -/

/-- Tops of a cons. -/
theorem tops_cons (c : Card) (A : List Card) : tops (c :: A) = c.1 ++ tops A := by
  simp [tops]

/-- Bottoms of a cons. -/
theorem bots_cons (c : Card) (A : List Card) : bots (c :: A) = c.2 ++ bots A := by
  simp [bots]

/-- Tops of an append. -/
theorem tops_append (A B : List Card) : tops (A ++ B) = tops A ++ tops B := by
  simp [tops]

/-- Bottoms of an append. -/
theorem bots_append (A B : List Card) : bots (A ++ B) = bots A ++ bots B := by
  simp [bots]

/-- The copy cards of a word. -/
def copies (w : Word) : List Card := w.map (fun a => ([a], [a]))

/-- The copy cards of `w` have top `w`. -/
theorem tops_copies (w : Word) : tops (copies w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [copies, List.map_cons] at ih ⊢; rw [tops_cons, ih]; rfl

/-- The copy cards of `w` have bottom `w`. -/
theorem bots_copies (w : Word) : bots (copies w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [copies, List.map_cons] at ih ⊢; rw [bots_cons, ih]; rfl

/-! ## Rewriting -/

/-- Transitivity of rewriting. -/
theorem srStar_trans {R : SRS} {x y z : Word} (h1 : SRStar R x y) (h2 : SRStar R y z) : SRStar R x z := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact SRStar.step s (ih h2)

/-- One rewrite in a context. -/
theorem srStep_ctx {R : SRS} {x y : Word} (p q : Word) (h : SRStep R x y) : SRStep R (p ++ x ++ q) (p ++ y ++ q) := by
  cases h with
  | rw u v l r hr =>
    have := SRStep.rw (p ++ u) (v ++ q) l r hr
    simpa [List.append_assoc] using this

/-- Rewriting in a context. -/
theorem srStar_ctx {R : SRS} {x y : Word} (p q : Word) (h : SRStar R x y) : SRStar R (p ++ x ++ q) (p ++ y ++ q) := by
  induction h with
  | refl => exact SRStar.refl _
  | step s _ ih => exact SRStar.step (srStep_ctx p q s) ih

/-- Rewriting both halves of a concatenation. -/
theorem srStar_append {R : SRS} {u u' v v' : Word} (h1 : SRStar R u u') (h2 : SRStar R v v') :
    SRStar R (u ++ v) (u' ++ v') := by
  have a := srStar_ctx [] v h1
  have b := srStar_ctx u' [] h2
  simp only [List.nil_append, List.append_nil] at a b
  exact srStar_trans a b

/-- A rule is a rewrite. -/
theorem srStar_rule {R : SRS} {l r : Word} (h : (l, r) ∈ R) : SRStar R l r := by
  have := SRStep.rw [] [] l r h
  simp only [List.nil_append, List.append_nil] at this
  exact SRStar.step this (SRStar.refl _)

/-- With nonempty right sides, only the empty string rewrites to the empty string. -/
theorem srStar_nil {R : SRS} (hne : ∀ p ∈ R, p.1 ≠ [] ∧ p.2 ≠ []) {u w : Word} (h : SRStar R u w) :
    w = [] → u = [] := by
  induction h with
  | refl => exact id
  | step s _ ih =>
    intro hw
    have e := ih hw
    cases s with
    | rw u v l r hr =>
      have := (hne _ hr).2
      simp at e
      exact absurd e.2.1 this

/-! ## Separators -/

/-- Peeling a separator-free prefix off a string that has a separator. -/
theorem peel_sep (s : Nat) : ∀ (t x M N : Word), s ∉ t → t ++ M = x ++ s :: N →
    ∃ x2, x = t ++ x2 ∧ M = x2 ++ s :: N
  | [], x, M, N, _, h => ⟨x, rfl, by simpa using h⟩
  | a :: t, [], M, N, ht, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ht
  | a :: t, b :: x, M, N, ht, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨x2, e1, e2⟩ := peel_sep s t x M N (fun hm => ht (List.mem_cons_of_mem _ hm)) h.2
    exact ⟨x2, by rw [h.1, e1]; rfl, e2⟩

/-- Two separator-free strings before the first separator are equal. -/
theorem sep_eq (s : Nat) : ∀ (y x M N : Word), s ∉ y → s ∉ x → y ++ s :: M = x ++ s :: N → y = x ∧ M = N
  | [], [], M, N, _, _, h => by simpa using h
  | [], b :: x, M, N, _, hx, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hx
  | a :: y, [], M, N, hy, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hy
  | a :: y, b :: x, M, N, hy, hx, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨e1, e2⟩ := sep_eq s y x M N (fun hm => hy (List.mem_cons_of_mem _ hm))
      (fun hm => hx (List.mem_cons_of_mem _ hm)) h.2
    exact ⟨by rw [h.1, e1], e2⟩

/-- A string with symbols below `n` does not contain `n + k`. -/
theorem not_mem_of_below {w : Word} {n : Nat} (hw : ∀ a ∈ w, a < n) (k : Nat) : n + k ∉ w :=
  fun hm => absurd (hw _ hm) (by omega)

/-! ## The cards -/

/-- The kinds of cards. -/
theorem mem_srCards {R : SRS} {y : Word} {n : Nat} {c : Card} (h : c ∈ srCards R y n) :
    c ∈ R ∨ c = ([n + 1], [n + 1]) ∨ (∃ a, a < n ∧ c = ([a], [a])) ∨ c = (y ++ [n + 1, n], [n]) := by
  simp only [srCards, List.mem_append, List.mem_cons, List.mem_map, List.mem_range] at h
  rcases h with h | h | ⟨a, ha, e⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, e.symm⟩))
  · exact Or.inr (Or.inr (Or.inr h))
  · simp at h

/-- Rule cards are cards. -/
theorem rule_mem {R : SRS} {y : Word} {n : Nat} {c : Card} (h : c ∈ R) : c ∈ srCards R y n := by
  simp [srCards, h]

/-- The separator card is a card. -/
theorem sep_mem (R : SRS) (y : Word) (n : Nat) : ([n + 1], [n + 1]) ∈ srCards R y n := by
  simp [srCards]

/-- Copy cards are cards. -/
theorem copy_mem {R : SRS} {y : Word} {n a : Nat} (h : a < n) : ([a], [a]) ∈ srCards R y n := by
  simp [srCards, h]

/-- The closing card is a card. -/
theorem close_mem (R : SRS) (y : Word) (n : Nat) : (y ++ [n + 1, n], [n]) ∈ srCards R y n := by
  simp [srCards]

/-- The copy cards of a word below `n` are cards. -/
theorem copies_mem {R : SRS} {y w : Word} {n : Nat} (hw : ∀ a ∈ w, a < n) :
    ∀ c ∈ copies w, c ∈ srCards R y n := by
  intro c hc
  simp only [copies, List.mem_map] at hc
  obtain ⟨a, ha, e⟩ := hc
  exact e ▸ copy_mem (hw a ha)

/-! ## Rewriting gives a solution -/

/-- From `x` reaching `y`, cards whose top is `x #` followed by their bottom. -/
theorem sr_sound {R : SRS} {y : Word} {n : Nat} (hR : RulesBelow n R) {x : Word} (h : SRStar R x y) :
    (∀ a ∈ x, a < n) → ∃ A : List Card, (∀ c ∈ A, c ∈ srCards R y n) ∧ tops A = x ++ (n + 1) :: bots A := by
  induction h with
  | refl x =>
    intro _
    refine ⟨[(x ++ [n + 1, n], [n])], ?_, ?_⟩
    · intro c hc
      simp only [List.mem_singleton] at hc
      exact hc ▸ close_mem R x n
    · simp [tops, bots]
  | step s _ ih =>
    intro hx
    cases s with
    | rw u v l r hr =>
      have hu : ∀ a ∈ u, a < n := fun a ha => hx a (by simp [ha])
      have hv : ∀ a ∈ v, a < n := fun a ha => hx a (by simp [ha])
      have hr' := (hR _ hr).2
      obtain ⟨A, hA, e⟩ := ih (by
        intro a ha
        simp only [List.mem_append] at ha
        rcases ha with (ha | ha) | ha
        · exact hu a ha
        · exact hr' a ha
        · exact hv a ha)
      refine ⟨copies u ++ (l, r) :: (copies v ++ ([n + 1], [n + 1]) :: A), ?_, ?_⟩
      · intro c hc
        simp only [List.mem_append, List.mem_cons] at hc
        rcases hc with hc | hc | hc | hc | hc
        · exact copies_mem hu c hc
        · exact hc ▸ rule_mem hr
        · exact copies_mem hv c hc
        · exact hc ▸ sep_mem R _ n
        · exact hA c hc
      · simp only [tops_append, tops_cons, bots_append, bots_cons, tops_copies, bots_copies, e]
        simp

/-! ## A solution gives rewriting -/

/-- **The invariant.** If the consumed prefix `h` already rewrote to `g`, and the tops of `A` are the rest `x`
of the current segment, a separator, and the produced `g` followed by the bottoms of `A`, then `h ++ x`
reaches `y`. -/
theorem sr_complete {R : SRS} {y : Word} {n : Nat} (hR : RulesBelow n R) (hne : ∀ p ∈ R, p.1 ≠ [] ∧ p.2 ≠ [])
    (hy : ∀ a ∈ y, a < n) :
    ∀ (A : List Card), (∀ c ∈ A, c ∈ srCards R y n) → ∀ (h x g : Word), (∀ a ∈ x, a < n) →
      (∀ a ∈ g, a < n) → SRStar R h g → tops A = x ++ (n + 1) :: (g ++ bots A) → SRStar R (h ++ x) y
  | [], _, h, x, g, _, _, _, e => by
    simp [tops] at e
  | c :: A, hA, h, x, g, hx, hg, hhg, e => by
    have hA' : ∀ c ∈ A, c ∈ srCards R y n := fun c' hc => hA c' (List.mem_cons_of_mem _ hc)
    rw [tops_cons, bots_cons] at e
    rcases mem_srCards (hA c List.mem_cons_self) with hc | hc | ⟨a, ha, hc⟩ | hc
    · -- a rule card
      obtain ⟨t, b⟩ := c
      have ht := (hR _ hc).1
      have hb := (hR _ hc).2
      obtain ⟨x2, ex, eM⟩ := peel_sep (n + 1) t x _ _ (not_mem_of_below ht 1) e
      have := sr_complete hR hne hy A hA' (h ++ t) x2 (g ++ b)
        (fun a ha => hx a (by rw [ex]; simp [ha]))
        (fun a ha => by
          simp only [List.mem_append] at ha
          rcases ha with ha | ha
          · exact hg a ha
          · exact hb a ha)
        (srStar_append hhg (srStar_rule hc)) (by rw [eM]; simp)
      rw [ex]; simpa using this
    · -- the separator card
      subst hc
      have e' : [] ++ (n + 1) :: tops A = x ++ (n + 1) :: (g ++ ([n + 1] ++ bots A)) := by simpa using e
      obtain ⟨ex, eM⟩ := sep_eq (n + 1) [] x _ _ (by simp) (not_mem_of_below hx 1) e'
      subst ex
      have := sr_complete hR hne hy A hA' [] g [] hg (by simp) (SRStar.refl _) (by rw [eM]; simp)
      simp only [List.nil_append] at this
      simpa using srStar_trans hhg this
    · -- a copy card
      subst hc
      obtain ⟨x2, ex, eM⟩ := peel_sep (n + 1) [a] x _ _ (by simp; omega) e
      have := sr_complete hR hne hy A hA' (h ++ [a]) x2 (g ++ [a])
        (fun b hb => hx b (by rw [ex]; simp [hb]))
        (fun b hb => by
          simp only [List.mem_append, List.mem_singleton] at hb
          rcases hb with hb | hb
          · exact hg b hb
          · exact hb ▸ ha)
        (srStar_append hhg (SRStar.refl _)) (by rw [eM]; simp)
      rw [ex]; simpa using this
    · -- the closing card
      subst hc
      have e' : y ++ (n + 1) :: ([n] ++ tops A) = x ++ (n + 1) :: (g ++ ([n] ++ bots A)) := by simpa using e
      obtain ⟨eyx, eM⟩ := sep_eq (n + 1) y x _ _ (not_mem_of_below hy 1) (not_mem_of_below hx 1) e'
      have eM' : [] ++ (n + 0) :: tops A = g ++ (n + 0) :: bots A := by simpa using eM
      obtain ⟨eg, _⟩ := sep_eq (n + 0) [] g _ _ (by simp) (not_mem_of_below hg 0) eM'
      have hh := srStar_nil hne hhg eg.symm
      subst hh
      subst eyx
      exact SRStar.refl _

/-! ## The reduction -/

/-- **Rewriting reduces to the modified correspondence problem.** -/
theorem sr_mpcp (R : SRS) (x y : Word) (n : Nat) (hR : RulesBelow n R) (hne : ∀ p ∈ R, p.1 ≠ [] ∧ p.2 ≠ [])
    (hx : ∀ a ∈ x, a < n) (hy : ∀ a ∈ y, a < n) :
    SRStar R x y ↔ MPCPSol (srFirst x n) (srCards R y n) := by
  constructor
  · intro h
    obtain ⟨A, hA, e⟩ := sr_sound hR h hx
    refine ⟨A, hA, ?_⟩
    rw [tops_cons, bots_cons, e]
    simp [srFirst]
  · rintro ⟨A, hA, e⟩
    rw [tops_cons, bots_cons] at e
    simp only [srFirst, List.cons_append, List.cons.injEq, true_and,
      List.append_assoc] at e
    have := sr_complete hR hne hy A hA [] x [] hx (by simp) (SRStar.refl _) (by simpa using e)
    simpa using this

/-- All symbols of the cards are below `n + 2`. -/
theorem srCards_below (R : SRS) (x y : Word) (n : Nat) (hR : RulesBelow n R) (hx : ∀ a ∈ x, a < n)
    (hy : ∀ a ∈ y, a < n) : CardsBelow (n + 2) (srFirst x n :: srCards R y n) := by
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst hc
    refine ⟨by simp [srFirst], ?_⟩
    intro a ha
    simp only [srFirst, List.mem_cons, List.mem_append] at ha
    rcases ha with ha | ha | ha
    · omega
    · have := hx a ha; omega
    · simp at ha; omega
  · rcases mem_srCards hc with hc | hc | ⟨a, ha, hc⟩ | hc
    · exact ⟨fun a ha => by have := (hR _ hc).1 a ha; omega, fun a ha => by have := (hR _ hc).2 a ha; omega⟩
    · subst hc; simp
    · subst hc; refine ⟨?_, ?_⟩ <;> simp <;> omega
    · subst hc
      refine ⟨?_, by simp⟩
      intro b hb
      simp only [List.mem_append, List.mem_cons] at hb
      rcases hb with hb | hb | hb
      · have := hy b hb; omega
      · omega
      · simp at hb; omega

/-- Every card has a nonempty top and a nonempty bottom. -/
theorem srCards_nonempty (R : SRS) (x y : Word) (n : Nat) (hne : ∀ p ∈ R, p.1 ≠ [] ∧ p.2 ≠ []) :
    CardsNonempty (srFirst x n :: srCards R y n) := by
  intro c hc
  simp only [List.mem_cons] at hc
  rcases hc with hc | hc
  · subst hc; simp [srFirst]
  · rcases mem_srCards hc with hc | hc | ⟨a, _, hc⟩ | hc
    · exact hne _ hc
    · subst hc; simp
    · subst hc; simp
    · subst hc; simp

end Complexity.Undec
