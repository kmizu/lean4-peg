import Shallot.Peg.Undecidable.PCP
import Shallot.Peg.Determinism

/-!
# Ford's grammar for Post's correspondence problem

Ford (POPL 2004, §3.4) builds, for an instance `C`, the grammar
`A ← x₁ A a₁ / … / xₙ A aₙ / ε`, `B ← y₁ B a₁ / … / yₙ B aₙ / ε`, `D ← &. &(A !.) B !.` (`fordG`).

The side rule `A` (and likewise `B`):
- succeeds only by eating the string of an index list (`side_sound`);
- always succeeds, because every `xᵢ` is nonempty (`side_total`);
- on the string of an index list followed by a marker or nothing, eats exactly that string (`side_complete`), even
  though ordered choice commits to the first alternative that succeeds: an alternative that succeeds eats the string
  of an index list, and that list is determined (`encS_unique`).

So `D` accepts exactly the common strings of the two sides, and **the language of `fordG C` is nonempty iff `C` has
a solution** (`ford_iff`).
-/

namespace Shallot

/-! ## Characters and literals -/

theorem beqChar_true_iff {c d : Char} : beqChar c d = true ↔ c = d := by
  unfold beqChar
  simp only [beq_iff_eq]
  exact ⟨fun h => by have := congrArg Char.ofNat h; simpa using this, fun h => h ▸ rfl⟩

theorem strip_eq : ∀ {s u r : List Char}, stripPrefix? s u = some r → u = s ++ r
  | [], u, r, h => by simp [stripPrefix?] at h; simp [h]
  | _ :: _, [], _, h => by simp [stripPrefix?] at h
  | c :: cs, d :: ds, r, h => by
    unfold stripPrefix? at h
    split at h
    · rename_i hcd
      rw [beqChar_true_iff.1 hcd, strip_eq h]; rfl
    · cases h

theorem strip_append (s r : List Char) : stripPrefix? s (s ++ r) = some r := by
  induction s with
  | nil => rfl
  | cons c cs ih => simp [stripPrefix?, beqChar_true_iff.2 rfl, ih]

/-- A literal always has a derivation. -/
theorem lit_total (g : Grammar) (s u : List Char) : ∃ o, Derives g (.lit s) u o := by
  cases h : stripPrefix? s u with
  | none => exact ⟨_, .litFail s u h⟩
  | some r => exact ⟨_, .litOk s u r h⟩

theorem lit_ok {g : Grammar} {s u r : List Char} {t : PTree} (h : Derives g (.lit s) u (.ok t r)) : u = s ++ r := by
  cases h with
  | litOk _ _ _ h => exact strip_eq h

/-- A nonempty word does not start with `#`. -/
theorem lit_word_fail (g : Grammar) {l : List Bool} (hl : l ≠ []) {t : List Char}
    (ht : t = [] ∨ t.head? = some '#') : Derives g (.lit (word l)) t .fail := by
  apply Derives.litFail
  cases l with
  | nil => exact absurd rfl hl
  | cons b l =>
    rcases ht with rfl | ht
    · rfl
    · cases t with
      | nil => simp at ht
      | cons c t =>
        simp at ht; subst ht
        simp only [word, List.map_cons, stripPrefix?]
        have : beqChar (bitC b) '#' = false := by
          cases h : beqChar (bitC b) '#'
          · rfl
          · exact absurd (beqChar_true_iff.1 h) (bitC_ne_hash b)
        simp [this]

/-! ## The side rules -/

/-- The alternative of index `i` of a side: its word, the side again, its marker. -/
def sideAlt (f : Nat → List Bool) (self i : Nat) : PExp := .seq (.lit (word (f i))) (.seq (.nt self) (.lit (mark i)))

/-- The alternatives of the indices in order, then `ε`. -/
def sideAlts (f : Nat → List Bool) (self : Nat) : List Nat → PExp
  | [] => .eps
  | i :: is => .alt (sideAlt f self i) (sideAlts f self is)

section Side

variable {g : Grammar} {f : Nat → List Bool} {self n : Nat}

/-- An alternative that succeeds eats its word, a string of the side and its marker. -/
theorem sideAlt_ok {i : Nat} {u r : List Char} {t : PTree} (h : Derives g (sideAlt f self i) u (.ok t r)) :
    ∃ u₁ r₁ t₁, u = word (f i) ++ u₁ ∧ Derives g (.nt self) u₁ (.ok t₁ r₁) ∧ r₁ = mark i ++ r := by
  cases h with
  | seqOk _ _ _ u₁ _ _ _ h₁ h₂ =>
    cases h₂ with
    | seqOk _ _ _ r₁ _ t₁ _ h₃ h₄ => exact ⟨u₁, r₁, t₁, lit_ok h₁, h₃, lit_ok h₄⟩

theorem encS_cons (f : Nat → List Bool) (i : Nat) (I : List Nat) (r : List Char) :
    encS f (i :: I) ++ r = word (f i) ++ (encS f I ++ (mark i ++ r)) := by
  simp [encS, cat_cons, word_append, marks_cons, List.append_assoc]

variable (hr : ruleAt g.rules self = some (sideAlts f self (List.range n)))
variable (hf : ∀ i, i < n → f i ≠ [])
include hr hf

omit hf in
theorem nt_ok {u r : List Char} {t : PTree} (h : Derives g (.nt self) u (.ok t r)) :
    ∃ t', Derives g (sideAlts f self (List.range n)) u (.ok t' r) := by
  cases h with
  | ntOk _ e _ _ t' hr' hd => rw [hr] at hr'; cases hr'; exact ⟨t', hd⟩

omit hr in
/-- The alternatives succeed only by eating the string of an index list, given that for shorter inputs. -/
theorem alts_sound {u : List Char}
    (ih : ∀ u' r' t', u'.length < u.length → Derives g (.nt self) u' (.ok t' r') →
      ∃ I, (∀ i ∈ I, i < n) ∧ u' = encS f I ++ r') :
    ∀ (is : List Nat) (r : List Char) (t : PTree), (∀ i ∈ is, i < n) → Derives g (sideAlts f self is) u (.ok t r) →
      ∃ I, (∀ i ∈ I, i < n) ∧ u = encS f I ++ r
  | [], r, t, _, h => by
    cases h with
    | eps => exact ⟨[], by simp, by simp [encS, cat, marks, word]⟩
  | i :: is, r, t, his, h => by
    cases h with
    | altL _ _ _ _ _ h =>
      obtain ⟨u₁, r₁, t₁, rfl, h₁, rfl⟩ := sideAlt_ok h
      have hi := his i (by simp)
      have hlen : u₁.length < (word (f i) ++ u₁).length := by
        have : (word (f i)).length ≠ 0 := by simpa [word] using hf i hi
        simp; omega
      obtain ⟨I, hI, rfl⟩ := ih u₁ _ t₁ hlen h₁
      refine ⟨i :: I, fun j hj => ?_, by rw [encS_cons]⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact hI j hj
    | altR _ _ _ _ _ _ h₂ => exact alts_sound ih is r _ (fun j hj => his j (by simp [hj])) h₂

theorem side_sound_aux : ∀ (m : Nat) (u r : List Char) (t : PTree), u.length ≤ m →
    Derives g (.nt self) u (.ok t r) → ∃ I, (∀ i ∈ I, i < n) ∧ u = encS f I ++ r
  | 0, u, r, t, hu, h => by
    obtain ⟨t', h'⟩ := nt_ok hr h
    exact alts_sound hf (fun u' _ _ hu' _ => absurd hu' (by omega)) _ r t' (fun i hi => List.mem_range.1 hi) h'
  | m + 1, u, r, t, hu, h => by
    obtain ⟨t', h'⟩ := nt_ok hr h
    exact alts_sound hf (fun u' r' t'' hu' h'' => side_sound_aux m u' r' t'' (by omega) h'') _ r t'
      (fun i hi => List.mem_range.1 hi) h'

/-- **A side succeeds only by eating the string of an index list.** -/
theorem side_sound {u r : List Char} {t : PTree} (h : Derives g (.nt self) u (.ok t r)) :
    ∃ I, (∀ i ∈ I, i < n) ∧ u = encS f I ++ r :=
  side_sound_aux hr hf u.length u r t (Nat.le_refl _) h

omit hr in
/-- An alternative has a derivation when the side has one on shorter inputs. -/
theorem sideAlt_total {u : List Char} (ih : ∀ u', u'.length < u.length → ∃ t r, Derives g (.nt self) u' (.ok t r))
    {i : Nat} (hi : i < n) : ∃ o, Derives g (sideAlt f self i) u o := by
  cases hs : stripPrefix? (word (f i)) u with
  | none => exact ⟨_, .seqFail₁ _ _ _ (.litFail _ _ hs)⟩
  | some u₁ =>
    have hu := strip_eq hs
    have hlen : u₁.length < u.length := by
      have : (word (f i)).length ≠ 0 := by simpa [word] using hf i hi
      rw [hu]; simp; omega
    obtain ⟨t₁, r₁, h₁⟩ := ih u₁ hlen
    obtain ⟨o, h₂⟩ := lit_total g (mark i) r₁
    cases o with
    | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ (.litOk _ _ _ hs) (.seqFail₂ _ _ _ _ _ h₁ h₂)⟩
    | ok t₂ r₂ => exact ⟨_, .seqOk _ _ _ _ _ _ _ (.litOk _ _ _ hs) (.seqOk _ _ _ _ _ _ _ h₁ h₂)⟩

omit hr in
theorem alts_total {u : List Char} (ih : ∀ u', u'.length < u.length → ∃ t r, Derives g (.nt self) u' (.ok t r)) :
    ∀ is : List Nat, (∀ i ∈ is, i < n) → ∃ t r, Derives g (sideAlts f self is) u (.ok t r)
  | [], _ => ⟨_, _, .eps u⟩
  | i :: is, his => by
    obtain ⟨o, h⟩ := sideAlt_total hf ih (his i (by simp))
    cases o with
    | ok t r => exact ⟨_, _, .altL _ _ _ _ _ h⟩
    | fail =>
      obtain ⟨t, r, h'⟩ := alts_total ih is (fun j hj => his j (by simp [hj]))
      exact ⟨_, _, .altR _ _ _ _ _ h h'⟩

theorem side_total_aux : ∀ (m : Nat) (u : List Char), u.length ≤ m → ∃ t r, Derives g (.nt self) u (.ok t r)
  | 0, u, hu => by
    obtain ⟨t, r, h⟩ := alts_total hf (u := u) (fun u' hu' => absurd hu' (by omega)) (List.range n)
      (fun i hi => List.mem_range.1 hi)
    exact ⟨_, _, .ntOk _ _ _ _ _ hr h⟩
  | m + 1, u, hu => by
    obtain ⟨t, r, h⟩ := alts_total hf (u := u) (fun u' hu' => side_total_aux m u' (by omega)) (List.range n)
      (fun i hi => List.mem_range.1 hi)
    exact ⟨_, _, .ntOk _ _ _ _ _ hr h⟩

/-- **A side always succeeds**, as every word is nonempty. -/
theorem side_total (u : List Char) : ∃ t r, Derives g (.nt self) u (.ok t r) :=
  side_total_aux hr hf u.length u (Nat.le_refl _)

/-- An alternative that succeeds eats the string of an index list headed by its index. -/
theorem sideAlt_sound {i : Nat} {u r : List Char} {t : PTree} (h : Derives g (sideAlt f self i) u (.ok t r)) :
    ∃ J, (∀ j ∈ J, j < n) ∧ u = encS f (i :: J) ++ r := by
  obtain ⟨u₁, r₁, t₁, rfl, h₁, rfl⟩ := sideAlt_ok h
  obtain ⟨J, hJ, rfl⟩ := side_sound hr hf h₁
  exact ⟨J, hJ, by rw [encS_cons]⟩

omit hr hf in
/-- The alternatives, where all fail, give `ε`; where one succeeds and every one that succeeds stops at `t`, they
stop at `t`. -/
theorem alts_ok {u t : List Char} (ht : ∀ i, i < n → ∀ r tr, Derives g (sideAlt f self i) u (.ok tr r) → r = t)
    (htot : ∀ i, i < n → ∃ o, Derives g (sideAlt f self i) u o) :
    ∀ is : List Nat, (∀ i ∈ is, i < n) → (u = t ∨ ∃ i ∈ is, ∃ tr, Derives g (sideAlt f self i) u (.ok tr t)) →
      ∃ tr, Derives g (sideAlts f self is) u (.ok tr t)
  | [], _, hex => by
    rcases hex with rfl | ⟨i, hi, _⟩
    · exact ⟨_, .eps _⟩
    · cases hi
  | i :: is, his, hex => by
    obtain ⟨o, h⟩ := htot i (his i (by simp))
    cases o with
    | ok tr r =>
      have := ht i (his i (by simp)) r tr h
      subst this
      exact ⟨_, .altL _ _ _ _ _ h⟩
    | fail =>
      have hex' : u = t ∨ ∃ j ∈ is, ∃ tr, Derives g (sideAlt f self j) u (.ok tr t) := by
        rcases hex with h' | ⟨j, hj, tr, hj'⟩
        · exact .inl h'
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact absurd (derives_det h hj') (by simp)
          · exact .inr ⟨j, hj, tr, hj'⟩
      obtain ⟨tr, h'⟩ := alts_ok ht htot is (fun j hj => his j (by simp [hj])) hex'
      exact ⟨_, .altR _ _ _ _ _ h h'⟩

/-- **On the string of an index list followed by a marker or nothing, a side eats exactly that string.** -/
theorem side_complete : ∀ (I : List Nat), (∀ i ∈ I, i < n) → ∀ t : List Char, (t = [] ∨ t.head? = some '#') →
    ∃ tr, Derives g (.nt self) (encS f I ++ t) (.ok tr t) := by
  intro I hI t ht
  have hv : ∀ (L : List Nat), (∀ j ∈ L, j < n) → PCP.Valid (List.replicate n ([], [])) L := fun L hL j hj => by
    simpa using hL j hj
  have hf' : ∀ i, i < (List.replicate n (([] : List Bool), ([] : List Bool))).length → f i ≠ [] := fun i hi =>
    hf i (by simpa using hi)
  -- every alternative that succeeds stops at `t`
  have hstop : ∀ i, i < n → ∀ r tr, Derives g (sideAlt f self i) (encS f I ++ t) (.ok tr r) → r = t := by
    intro i hi r tr h
    obtain ⟨J, hJ, he⟩ := sideAlt_sound hr hf h
    exact (encS_unique hf' (hv (i :: J) (fun j hj => by
      rcases List.mem_cons.1 hj with rfl | hj
      · exact hi
      · exact hJ j hj)) (hv I hI) (by simp) ht he.symm).2
  have htot : ∀ i, i < n → ∃ o, Derives g (sideAlt f self i) (encS f I ++ t) o :=
    fun i hi => sideAlt_total hf (fun u' _ => side_total hr hf u') hi
  -- some alternative stops at `t`, or the string is empty
  have hex : encS f I ++ t = t ∨ ∃ i ∈ List.range n, ∃ tr, Derives g (sideAlt f self i) (encS f I ++ t) (.ok tr t) := by
    cases I with
    | nil => left; simp [encS, cat, marks, word]
    | cons i J =>
      right
      have hi := hI i (by simp)
      obtain ⟨tr₁, h₁⟩ := side_complete J (fun j hj => hI j (by simp [hj])) (mark i ++ t) (by right; simp [mark])
      obtain ⟨t₂, h₂⟩ : ∃ t₂, Derives g (.lit (mark i)) (mark i ++ t) (.ok t₂ t) :=
        ⟨_, .litOk _ _ _ (strip_append _ _)⟩
      refine ⟨i, List.mem_range.2 hi, .seq (.leaf (word (f i))) (.seq tr₁ t₂), ?_⟩
      rw [encS_cons]
      exact .seqOk _ _ _ _ _ (.leaf (word (f i))) (.seq tr₁ t₂) (.litOk _ _ _ (strip_append _ _))
        (.seqOk _ _ _ _ _ tr₁ t₂ h₁ h₂)
  obtain ⟨tr, h⟩ := alts_ok hstop htot (List.range n) (fun i hi => List.mem_range.1 hi) hex
  exact ⟨_, .ntOk _ _ _ _ _ hr h⟩

end Side

end Shallot
