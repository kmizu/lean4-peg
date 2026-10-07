import Shallot.Peg.Undecidable.PCP
import Complexity.Undec.Defs

/-!
# From cards over numbers to pairs of bit strings

Symbol `a` is written `1ᵃ0` (`bin`); the code is prefix-free, so `bin` is an injective monoid morphism
(`bin_append`, `bin_inj`). A list of cards and a list of indices into the card list say the same thing
(`indices_of_cards`), so solutions correspond (`pcpN_pcp`).
-/

namespace Shallot

/-- The unary prefix code: symbol `a` becomes `a` ones and a zero. -/
def bin (w : Complexity.Undec.Word) : List Bool := w.flatMap fun a => List.replicate a true ++ [false]

/-- The cards written in bits. -/
def toPCP (P : List Complexity.Undec.Card) : PCP := P.map fun c => (bin c.1, bin c.2)

theorem bin_nil : bin [] = [] := rfl

theorem bin_cons (a : Nat) (w : Complexity.Undec.Word) :
    bin (a :: w) = List.replicate a true ++ false :: bin w := by
  simp [bin]

theorem bin_append (u v : Complexity.Undec.Word) : bin (u ++ v) = bin u ++ bin v := by
  simp [bin, List.flatMap_append]

/-- Code words are prefix-free and injective. -/
theorem unary_prefix : ∀ (a b : Nat) (u v : List Bool),
    List.replicate a true ++ false :: u = List.replicate b true ++ false :: v → a = b ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, b + 1, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, u, v, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := unary_prefix a b u v h
    exact ⟨by omega, this.2⟩

/-- **`bin` is injective.** -/
theorem bin_inj : ∀ {u v : Complexity.Undec.Word}, bin u = bin v → u = v
  | [], [], _ => rfl
  | [], b :: v, h => by rw [bin_cons, bin_nil] at h; simp at h
  | a :: u, [], h => by rw [bin_cons, bin_nil] at h; simp at h
  | a :: u, b :: v, h => by
    rw [bin_cons, bin_cons] at h
    obtain ⟨rfl, h'⟩ := unary_prefix a b _ _ h
    rw [bin_inj h']

theorem bin_ne_nil {w : Complexity.Undec.Word} (h : w ≠ []) : bin w ≠ [] := by
  cases w with
  | nil => exact absurd rfl h
  | cons a w => rw [bin_cons]; simp

/-- The pair at index `i` of the bit instance. -/
theorem getD_toPCP : ∀ (P : List Complexity.Undec.Card) (i : Nat),
    (toPCP P).getD i ([], []) = (bin (P.getD i ([], [])).1, bin (P.getD i ([], [])).2)
  | [], i => by simp [toPCP, bin_nil]
  | c :: P, 0 => by simp [toPCP]
  | c :: P, i + 1 => by
    have := getD_toPCP P i
    simp only [toPCP, List.map_cons, List.getD_cons_succ] at this ⊢
    exact this

/-- The tops along indices are the code of the tops of the indexed cards. -/
theorem cat_top_toPCP (P : List Complexity.Undec.Card) (I : List Nat) :
    cat (toPCP P).top I = bin (Complexity.Undec.tops (I.map fun i => P.getD i ([], []))) := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    rw [cat_cons, ih, PCP.top, getD_toPCP]
    simp [Complexity.Undec.tops, bin_append]

/-- The bottoms along indices are the code of the bottoms of the indexed cards. -/
theorem cat_bot_toPCP (P : List Complexity.Undec.Card) (I : List Nat) :
    cat (toPCP P).bot I = bin (Complexity.Undec.bots (I.map fun i => P.getD i ([], []))) := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    rw [cat_cons, ih, PCP.bot, getD_toPCP]
    simp [Complexity.Undec.bots, bin_append]

/-- A card of `P` sits at some index. -/
theorem index_of_mem : ∀ {P : List Complexity.Undec.Card} {c : Complexity.Undec.Card}, c ∈ P →
    ∃ i, i < P.length ∧ P.getD i ([], []) = c
  | [], _, h => by simp at h
  | e :: P, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨i, hi, hc⟩ := index_of_mem h
      exact ⟨i + 1, by simp; omega, by simpa using hc⟩

/-- A list of cards of `P` is a list of indices into `P`. -/
theorem indices_of_cards (P : List Complexity.Undec.Card) : ∀ {A : List Complexity.Undec.Card},
    (∀ c ∈ A, c ∈ P) → ∃ I : List Nat, (∀ i ∈ I, i < P.length) ∧ I.map (fun i => P.getD i ([], [])) = A
  | [], _ => ⟨[], by simp, rfl⟩
  | c :: A, h => by
    obtain ⟨i, hi, hc⟩ := index_of_mem (h c List.mem_cons_self)
    obtain ⟨I, hI, hA⟩ := indices_of_cards P (fun e he => h e (List.mem_cons_of_mem _ he))
    refine ⟨i :: I, fun j hj => ?_, by rw [List.map_cons, hc, hA]⟩
    rcases List.mem_cons.1 hj with rfl | hj
    · exact hi
    · exact hI j hj

/-- An index in range picks a card of `P`. -/
theorem getD_mem : ∀ {P : List Complexity.Undec.Card} {i : Nat}, i < P.length → P.getD i ([], []) ∈ P
  | [], _, h => by simp at h
  | c :: P, 0, _ => by simp
  | c :: P, i + 1, h => by
    rw [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem (by simp at h; omega))

/-- **Solutions by cards are solutions by indices of the bit instance.** -/
theorem pcpN_pcp (P : List Complexity.Undec.Card) : Complexity.Undec.PCPNSol P ↔ PCPSol (toPCP P) := by
  constructor
  · rintro ⟨A, hne, hA, heq⟩
    obtain ⟨I, hI, rfl⟩ := indices_of_cards P hA
    refine ⟨I, fun h => hne (by rw [h]; rfl), fun i hi => ?_, ?_⟩
    · rw [toPCP, List.length_map]; exact hI i hi
    · rw [cat_top_toPCP, cat_bot_toPCP, heq]
  · rintro ⟨I, hne, hv, heq⟩
    refine ⟨I.map fun i => P.getD i ([], []), fun h => hne (List.map_eq_nil_iff.1 h), fun c hc => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
      have := hv i hi
      rw [toPCP, List.length_map] at this
      exact getD_mem this
    · rw [cat_top_toPCP, cat_bot_toPCP] at heq
      exact bin_inj heq

/-- Nonempty cards give nonempty bit pairs. -/
theorem toPCP_nonempty {P : List Complexity.Undec.Card} (h : Complexity.Undec.CardsNonempty P) :
    (toPCP P).NonemptyPairs := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
  exact ⟨bin_ne_nil (h c hc).1, bin_ne_nil (h c hc).2⟩

end Shallot
