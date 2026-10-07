import Shallot.Peg.Semantics

/-!
# Post's correspondence problem and the strings of Ford's grammar

An instance is a list of pairs of nonempty bit strings; a solution is a nonempty list of indices whose top strings
and bottom strings concatenate to the same string (`PCPSol`).

Ford's grammar reads the bits as the characters `'0'`, `'1'` and closes index `i` with a marker. Ford uses a
distinct terminal `aᵢ` per index; as characters are finitely many, the marker is the string `# |…| $` with `i`
bars (`mark`), and these strings are prefix-free (`mark_prefix`). The string of an index list `I` is its words
followed by its markers in reverse (`encS`), and a nonempty index list is determined by any prefix of the right
shape (`encS_unique`).
-/

namespace Shallot

/-- An instance of Post's correspondence problem over bits. -/
abbrev PCP := List (List Bool × List Bool)

/-- Every top and bottom string is nonempty (Ford's grammar needs it: an empty one would be left-recursive). -/
def PCP.NonemptyPairs (C : PCP) : Prop := ∀ p ∈ C, p.1 ≠ [] ∧ p.2 ≠ []

/-- The indices are in range. -/
def PCP.Valid (C : PCP) (I : List Nat) : Prop := ∀ i ∈ I, i < C.length

/-- The top string of index `i`. -/
def PCP.top (C : PCP) (i : Nat) : List Bool := (C.getD i ([], [])).1

/-- The bottom string of index `i`. -/
def PCP.bot (C : PCP) (i : Nat) : List Bool := (C.getD i ([], [])).2

/-- The concatenation of the strings of a side along the indices. -/
def cat (f : Nat → List Bool) (I : List Nat) : List Bool := (I.map f).flatten

/-- **A solution**: a nonempty list of valid indices with equal concatenations. -/
def PCPSol (C : PCP) : Prop := ∃ I : List Nat, I ≠ [] ∧ C.Valid I ∧ cat C.top I = cat C.bot I

/-! ## Characters -/

/-- A bit as a character. -/
def bitC (b : Bool) : Char := if b then '1' else '0'

/-- A bit string as characters. -/
def word (l : List Bool) : List Char := l.map bitC

/-- The marker of index `i`: `#`, `i` bars, `$`. -/
def mark (i : Nat) : List Char := '#' :: (List.replicate i '|' ++ ['$'])

/-- The markers of an index list, last index first. -/
def marks (I : List Nat) : List Char := (I.reverse.map mark).flatten

/-- The string of an index list on one side: the words, then the markers in reverse. -/
def encS (f : Nat → List Bool) (I : List Nat) : List Char := word (cat f I) ++ marks I

theorem word_append (a b : List Bool) : word (a ++ b) = word a ++ word b := by simp [word]

theorem cat_cons (f : Nat → List Bool) (i : Nat) (I : List Nat) : cat f (i :: I) = f i ++ cat f I := by
  simp [cat]

theorem cat_append (f : Nat → List Bool) (I J : List Nat) : cat f (I ++ J) = cat f I ++ cat f J := by
  simp [cat]

theorem marks_cons (i : Nat) (I : List Nat) : marks (i :: I) = marks I ++ mark i := by
  simp [marks]

theorem bitC_ne_hash (b : Bool) : bitC b ≠ '#' := by cases b <;> decide

/-! ## Markers are prefix-free -/

theorem bars_prefix : ∀ (a b : Nat) (u v : List Char),
    List.replicate a '|' ++ '$' :: u = List.replicate b '|' ++ '$' :: v → a = b ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, b + 1, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, u, v, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := bars_prefix a b u v h
    exact ⟨by omega, this.2⟩

/-- **Markers are prefix-free and injective.** -/
theorem mark_prefix {a b : Nat} {u v : List Char} (h : mark a ++ u = mark b ++ v) : a = b ∧ u = v := by
  simp only [mark, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
  exact bars_prefix a b u v h

/-- Two marker lists sharing a string are one a prefix of the other. -/
theorem blocks_prefix : ∀ (A B : List Nat) (r t : List Char),
    (A.map mark).flatten ++ r = (B.map mark).flatten ++ t →
      (∃ R, B = A ++ R ∧ r = (R.map mark).flatten ++ t) ∨ (∃ R, A = B ++ R ∧ t = (R.map mark).flatten ++ r)
  | [], B, r, t, h => .inl ⟨B, rfl, by simpa using h⟩
  | a :: A, [], r, t, h => .inr ⟨a :: A, rfl, by simpa using h.symm⟩
  | a :: A, b :: B, r, t, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := mark_prefix h
    rcases blocks_prefix A B r t h' with ⟨R, rfl, hr⟩ | ⟨R, rfl, ht⟩
    · exact .inl ⟨R, rfl, hr⟩
    · exact .inr ⟨R, rfl, ht⟩

/-! ## The strings of index lists are determined -/

/-- A word followed by `#` or nothing: its first `#` is where the word ends. -/
theorem word_hash {a b : List Bool} {u v : List Char} (hu : u = [] ∨ u.head? = some '#')
    (hv : v = [] ∨ v.head? = some '#') (h : word a ++ u = word b ++ v) : a = b ∧ u = v := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons y b =>
      simp only [word, List.map_nil, List.nil_append, List.map_cons, List.cons_append] at h
      subst h
      rcases hu with h₁ | h₁ <;> simp at h₁
      exact absurd h₁ (bitC_ne_hash y)
  | cons x a ih =>
    cases b with
    | nil =>
      simp only [word, List.map_nil, List.nil_append, List.map_cons, List.cons_append] at h
      subst h
      rcases hv with h₁ | h₁ <;> simp at h₁
      exact absurd h₁ (bitC_ne_hash x)
    | cons y b =>
      simp only [word, List.map_cons, List.cons_append, List.cons.injEq] at h
      have hxy : x = y := by cases x <;> cases y <;> simp_all [bitC]
      subst hxy
      have := ih (b := b) h.2
      exact ⟨by rw [this.1], this.2⟩

theorem marks_head (I : List Nat) : marks I = [] ∨ (marks I).head? = some '#' := by
  cases h : I.reverse with
  | nil => left; simp [marks, h]
  | cons i J => right; simp [marks, h, mark]

/-- The concatenation along nonempty words is empty only for the empty list. -/
theorem cat_eq_nil {f : Nat → List Bool} {C : PCP} (hf : ∀ i, i < C.length → f i ≠ []) {R : List Nat}
    (hR : C.Valid R) (h : cat f R = []) : R = [] := by
  cases R with
  | nil => rfl
  | cons i R => rw [cat_cons] at h; exact absurd (List.append_eq_nil_iff.1 h).1 (hf i (hR i (by simp)))

/-- **A nonempty index list is determined by its string, followed by a marker or nothing.** -/
theorem encS_unique {C : PCP} {f : Nat → List Bool} (hf : ∀ i, i < C.length → f i ≠ []) {L I : List Nat}
    (hL : C.Valid L) (hI : C.Valid I) (hne : L ≠ []) {r t : List Char} (ht : t = [] ∨ t.head? = some '#')
    (h : encS f L ++ r = encS f I ++ t) : L = I ∧ r = t := by
  have hmL : marks L ≠ [] := by
    cases h' : L.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.1 h') hne
    | cons i J => simp [marks, h', mark]
  -- the words end at the first `#`
  have hw := word_hash (a := cat f L) (b := cat f I) (u := marks L ++ r) (v := marks I ++ t)
    (by right; rcases marks_head L with h₁ | h₁; exact absurd h₁ hmL; cases hm : marks L with
        | nil => exact absurd hm hmL
        | cons c cs => rw [hm] at h₁; simpa using h₁)
    (by rcases marks_head I with h₁ | h₁
        · rw [h₁]; simpa using ht
        · right; cases hm : marks I with
          | nil => rw [hm] at h₁; simp at h₁
          | cons c cs => rw [hm] at h₁; simpa using h₁)
    (by simpa [encS, List.append_assoc] using h)
  obtain ⟨hcat, hm⟩ := hw
  -- the markers, read in blocks, are one a prefix of the other
  rcases blocks_prefix L.reverse I.reverse r t hm with ⟨R, hR, hr⟩ | ⟨R, hR, htr⟩
  · -- `I = R.reverse ++ L`, so the words of `R.reverse` are empty
    have hI' : I = R.reverse ++ L := by
      have := congrArg List.reverse hR; simpa using this
    have hRv : C.Valid R.reverse := fun i hi => hI i (by rw [hI']; exact List.mem_append_left _ hi)
    have : cat f R.reverse = [] := by
      rw [hI', cat_append] at hcat
      have := congrArg List.length hcat
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hR0 : R = [] := by simpa using cat_eq_nil hf hRv this
    subst hR0
    exact ⟨by simpa using hI'.symm, by simpa using hr⟩
  · -- `L = R.reverse ++ I`, so the words of `R.reverse` are empty
    have hL' : L = R.reverse ++ I := by
      have := congrArg List.reverse hR; simpa using this
    have hRv : C.Valid R.reverse := fun i hi => hL i (by rw [hL']; exact List.mem_append_left _ hi)
    have : cat f R.reverse = [] := by
      rw [hL', cat_append] at hcat
      have := congrArg List.length hcat
      simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hR0 : R = [] := by simpa using cat_eq_nil hf hRv this
    subst hR0
    exact ⟨by simpa using hL', by simpa using htr.symm⟩

end Shallot
