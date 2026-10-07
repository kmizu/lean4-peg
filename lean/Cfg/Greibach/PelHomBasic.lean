import Cfg.Greibach.PelHomDefs

/-!
# Basic facts for the inverse-homomorphism simulation

Ordered choice over lists (`chain`), families that hit or miss, letter classes, the state list, and one step
of the image (`img_cases`): from every state either the image is exhausted at the very end, or its next letter
is the letter at some offset of some block, and the state moves to `nextSt`.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt beqChar leChar)

section Generic

variable {G : Grammar}

/-- An ordered choice over a list fails when every member fails. -/
theorem chain_fail {α : Type} {F : α → PExp} {u : List Char} :
    ∀ {l : List α}, (∀ y ∈ l, Derives G (F y) u .fail) → Derives G (chain l F) u .fail
  | [], _ => phFail_fail u
  | y :: _, h => .altFail _ _ _ (h y List.mem_cons_self)
      (chain_fail fun z hz => h z (List.mem_cons_of_mem y hz))

/-- An ordered choice over a list succeeds like its member `y₁` when every other member fails. -/
theorem chain_ok {α : Type} {F : α → PExp} {u : List Char} {y₁ : α} {t : PTree} {r : List Char}
    (h₁ : Derives G (F y₁) u (.ok t r)) :
    ∀ {l : List α}, y₁ ∈ l → (∀ y ∈ l, y ≠ y₁ → Derives G (F y) u .fail) →
      ∃ t', Derives G (chain l F) u (.ok t' r)
  | [], hm, _ => absurd hm List.not_mem_nil
  | y :: l, hm, hf => by
    rcases Classical.em (y = y₁) with hy | hy
    · subst hy; exact ⟨_, .altL _ _ _ _ _ h₁⟩
    · have hm' : y₁ ∈ l := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm hy
        · exact h
      obtain ⟨t', ht'⟩ := chain_ok h₁ hm' (fun z hz hzne => hf z (List.mem_cons_of_mem y hz) hzne)
      exact ⟨_, .altR _ _ _ _ _ (hf y List.mem_cons_self hy) ht'⟩

/-- A family hitting `(q₁, u₁)` has its member for `q₁` succeed. -/
theorem Hits.ok {Q : List St} {F : St → PExp} {u : List Char} {q₁ : St} {u₁ : List Char}
    (h : Hits G Q F u q₁ u₁) : ∃ t, Derives G (F q₁) u (.ok t u₁) :=
  (h.2 q₁ h.1).1 rfl

/-- `chain Q F` succeeds when `F` hits. -/
theorem Hits.chain_ok {Q : List St} {F : St → PExp} {u : List Char} {q₁ : St} {u₁ : List Char}
    (h : Hits G Q F u q₁ u₁) : ∃ t, Derives G (chain Q F) u (.ok t u₁) := by
  obtain ⟨t, ht⟩ := h.ok
  exact Shallot.Cfg.chain_ok ht h.1 (fun y hy hne => (h.2 y hy).2 hne)

/-- `chain Q F` fails when `F` misses. -/
theorem Misses.chain_fail {Q : List St} {F : St → PExp} {u : List Char} (h : Misses G Q F u) :
    Derives G (chain Q F) u .fail :=
  Shallot.Cfg.chain_fail h

/-- `guardEq q` hits `(q, u)`. -/
theorem guardEq_hits {Q : List St} {q : St} {u : List Char} (hq : q ∈ Q) :
    Hits G Q (guardEq q) u q u := by
  refine ⟨hq, fun q' _ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · subst h; exact ⟨_, by simp only [guardEq]; exact .eps u⟩
  · have : q ≠ q' := fun e => h e.symm
    simp only [guardEq, if_neg this]; exact phFail_fail u

/-- The sequencing pattern `q' ↦ chain Q (y ↦ A y · B y q')`. -/
def chainSeq (Q : List St) (A : St → PExp) (B : St → St → PExp) : St → PExp :=
  fun q' => chain Q (fun y => .seq (A y) (B y q'))

/-- Sequencing a hit with a hit. -/
theorem chainSeq_hits {Q : List St} {A : St → PExp} {B : St → St → PExp} {u u₁ u₂ : List Char}
    {q₁ q₂ : St} (hA : Hits G Q A u q₁ u₁) (hB : Hits G Q (B q₁) u₁ q₂ u₂) :
    Hits G Q (chainSeq Q A B) u q₂ u₂ := by
  unfold chainSeq
  refine ⟨hB.1, fun q' hq' => ⟨fun he => ?_, fun hne => ?_⟩⟩
  · subst he
    obtain ⟨t₁, ht₁⟩ := hA.ok
    obtain ⟨t₂, ht₂⟩ := hB.ok
    exact Shallot.Cfg.chain_ok (F := fun y => PExp.seq (A y) (B y _)) (y₁ := q₁)
      (.seqOk _ _ _ _ _ _ _ ht₁ ht₂) hA.1
      (fun y hy hne => .seqFail₁ _ _ _ ((hA.2 y hy).2 hne))
  · refine Shallot.Cfg.chain_fail (fun y hy => ?_)
    rcases Classical.em (y = q₁) with h | h
    · subst h
      obtain ⟨t₁, ht₁⟩ := hA.ok
      exact .seqFail₂ _ _ _ _ _ ht₁ ((hB.2 q' hq').2 hne)
    · exact .seqFail₁ _ _ _ ((hA.2 y hy).2 h)

/-- Sequencing a hit with a miss. -/
theorem chainSeq_misses₂ {Q : List St} {A : St → PExp} {B : St → St → PExp} {u u₁ : List Char}
    {q₁ : St} (hA : Hits G Q A u q₁ u₁) (hB : Misses G Q (B q₁) u₁) :
    Misses G Q (chainSeq Q A B) u := by
  unfold chainSeq
  intro q' hq'
  refine Shallot.Cfg.chain_fail (fun y hy => ?_)
  rcases Classical.em (y = q₁) with h | h
  · subst h
    obtain ⟨t₁, ht₁⟩ := hA.ok
    exact .seqFail₂ _ _ _ _ _ ht₁ (hB q' hq')
  · exact .seqFail₁ _ _ _ ((hA.2 y hy).2 h)

/-- Sequencing a miss with anything. -/
theorem chainSeq_misses₁ {Q : List St} {A : St → PExp} {B : St → St → PExp} {u : List Char}
    (hA : Misses G Q A u) : Misses G Q (chainSeq Q A B) u := by
  unfold chainSeq
  exact fun _ _ => Shallot.Cfg.chain_fail (fun y hy => .seqFail₁ _ _ _ (hA y hy))

end Generic

/-- `beqChar` is equality. -/
theorem beqChar_iff {c d : Char} : beqChar c d = true ↔ c = d := by
  simp only [beqChar, beq_iff_eq]; exact Char.toNat_inj

/-- The ordered choice of the letters of `l` reads a letter of `l`. -/
theorem anyOf_cons_mem {G : Grammar} {a : Char} {u : List Char} :
    ∀ {l : List Char}, a ∈ l → ∃ t, Derives G (anyOf l) (a :: u) (.ok t u)
  | [], h => absurd h List.not_mem_nil
  | c :: l, h => by
    rcases Classical.em (c = a) with hc | hc
    · exact ⟨_, .altL _ _ _ _ _ (.chrOk c a u (beqChar_iff.mpr hc))⟩
    · have hl : a ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hc
        · exact h
      obtain ⟨t, ht⟩ := anyOf_cons_mem (u := u) (G := G) hl
      have hb : beqChar c a = false := by
        cases hb : beqChar c a
        · rfl
        · exact absurd (beqChar_iff.mp hb) hc
      exact ⟨_, .altR _ _ _ _ _ (.chrFail c a u hb) ht⟩

/-- The ordered choice of the letters of `l` fails on a letter outside `l`. -/
theorem anyOf_cons_not_mem {G : Grammar} {a : Char} {u : List Char} :
    ∀ {l : List Char}, a ∉ l → Derives G (anyOf l) (a :: u) .fail
  | [], _ => phFail_fail _
  | c :: l, h => by
    have hb : beqChar c a = false := by
      cases hb : beqChar c a
      · rfl
      · exact absurd (List.mem_cons.mpr (Or.inl (beqChar_iff.mp hb).symm)) h
    exact .altFail _ _ _ (.chrFail c a u hb) (anyOf_cons_not_mem (fun hl => h (List.mem_cons_of_mem c hl)))

/-- The ordered choice of letters fails on the empty input. -/
theorem anyOf_nil {G : Grammar} : ∀ {l : List Char}, Derives G (anyOf l) [] .fail
  | [] => phFail_fail _
  | c :: _ => .altFail _ _ _ (.chrEmpty c) anyOf_nil

/-- The class of a letter is at most the length. -/
theorem clsOf_le (a : Char) : ∀ S : List Char, clsOf S a ≤ S.length
  | [] => Nat.le_refl 0
  | c :: cs => by
    simp only [clsOf, List.length_cons]
    split
    · omega
    · have := clsOf_le a cs; omega

/-- The class of a letter, characterized by the first `k` letters and the `k`-th. -/
theorem clsOf_eq_iff (a : Char) :
    ∀ (S : List Char) (k : Nat), k ≤ S.length →
      (clsOf S a = k ↔ a ∉ S.take k ∧ (match S[k]? with | some c => c = a | none => True))
  | [], k, hk => by
    have : k = 0 := by simp at hk; omega
    subst this; simp [clsOf]
  | c :: cs, 0, _ => by
    simp only [clsOf, List.take_zero, List.getElem?_cons_zero]
    constructor
    · intro h; split at h
      · next he => exact ⟨List.not_mem_nil, he.symm⟩
      · omega
    · intro ⟨_, h⟩; simp [h]
  | c :: cs, k + 1, hk => by
    have ih := clsOf_eq_iff a cs k (by simp at hk; omega)
    simp only [clsOf, List.take_succ_cons, List.getElem?_cons_succ, List.mem_cons, not_or]
    constructor
    · intro h; split at h
      · omega
      · next he => exact ⟨⟨he, (ih.mp (by omega)).1⟩, (ih.mp (by omega)).2⟩
    · intro ⟨⟨h1, h2⟩, h3⟩; simp only [if_neg h1]; have := ih.mpr ⟨h2, h3⟩; omega

/-- The letter at a letter's class position. -/
theorem getElem?_clsOf (a : Char) : ∀ S : List Char,
    (a ∈ S → S[clsOf S a]? = some a) ∧ (a ∉ S → S[clsOf S a]? = none)
  | [] => ⟨fun h => absurd h List.not_mem_nil, fun _ => rfl⟩
  | c :: cs => by
    have ih := getElem?_clsOf a cs
    simp only [clsOf]
    split
    · next he => subst he; exact ⟨fun _ => rfl, fun h => absurd List.mem_cons_self h⟩
    · next he =>
      simp only [List.getElem?_cons_succ, List.mem_cons, he, false_or]
      exact ih

namespace PhSim

variable (M : PhSim)

/-- The block of a letter's class is the letter's block. -/
theorem blk_clsOf (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) (a : Char) : M.blk (clsOf M.S a) = M.h a := by
  unfold blk
  by_cases ha : a ∈ M.S
  · rw [(getElem?_clsOf a M.S).1 ha]
  · rw [(getElem?_clsOf a M.S).2 ha, hS a ha]

/-- Reading a source letter of class `k`. -/
theorem sel_cons {G : Grammar} {k : Nat} (hk : k ≤ M.S.length) (a : Char) (u : List Char) :
    (clsOf M.S a = k → ∃ t, Derives G (M.sel k) (a :: u) (.ok t u)) ∧
      (clsOf M.S a ≠ k → Derives G (M.sel k) (a :: u) .fail) := by
  have hc := clsOf_eq_iff a M.S k hk
  by_cases hm : a ∈ M.S.take k
  · obtain ⟨t, ht⟩ := anyOf_cons_mem (G := G) (u := u) hm
    refine ⟨fun h => absurd hm (hc.mp h).1, fun _ => ?_⟩
    exact .seqFail₁ _ _ _ (.notOk _ _ _ _ ht)
  · have hn : Derives G (.notP (anyOf (M.S.take k))) (a :: u) (.ok .notT (a :: u)) :=
      .notFail _ _ (anyOf_cons_not_mem hm)
    unfold sel
    revert hc
    cases hs : M.S[k]? with
    | none =>
      intro hc
      exact ⟨fun _ => ⟨_, .seqOk _ _ _ _ _ _ _ hn (.anyOk a u)⟩,
        fun h => absurd (hc.mpr ⟨hm, trivial⟩) h⟩
    | some c =>
      intro hc
      refine ⟨fun h => ⟨_, .seqOk _ _ _ _ _ _ _ hn (.chrOk c a u (beqChar_iff.mpr (hc.mp h).2))⟩,
        fun h => ?_⟩
      have hb : beqChar c a = false := by
        cases hb : beqChar c a
        · rfl
        · exact absurd (hc.mpr ⟨hm, beqChar_iff.mp hb⟩) h
      exact .seqFail₂ _ _ _ _ _ hn (.chrFail c a u hb)

/-- Reading a source letter fails on the empty source. -/
theorem sel_nil {G : Grammar} (k : Nat) : Derives G (M.sel k) [] .fail := by
  have hn : Derives G (.notP (anyOf (M.S.take k))) [] (.ok .notT []) := .notFail _ _ anyOf_nil
  unfold sel
  cases M.S[k]? with
  | none => exact .seqFail₂ _ _ _ _ _ hn .anyFail
  | some c => exact .seqFail₂ _ _ _ _ _ hn (.chrEmpty c)

/-- The states. -/
theorem mem_stList {q : St} :
    q ∈ M.stList ↔ q = none ∨ ∃ k i, q = some (k, i) ∧ k ≤ M.S.length ∧ 0 < i ∧ i < (M.blk k).length := by
  simp only [stList, List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro (h | ⟨k, hk, j, hj, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, j + 1, rfl, by omega, by omega, by omega⟩
  · rintro (h | ⟨k, i, rfl, hk, hi, hil⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, by omega, i - 1, by omega, by congr; omega⟩

/-- The boundary is a state. -/
theorem none_mem_stList : (none : St) ∈ M.stList := List.mem_cons_self

/-- The next state is a state. -/
theorem nextSt_mem {k : Nat} (hk : k ≤ M.S.length) (i : Nat) : M.nextSt k i ∈ M.stList := by
  unfold nextSt
  split
  · exact (M.mem_stList).mpr (Or.inr ⟨k, i + 1, rfl, hk, by omega, by omega⟩)
  · exact M.none_mem_stList

/-- Reading the letter at offset `i` of a block. -/
theorem drop_blk {k i : Nat} {d : Char} (hd : (M.blk k)[i]? = some d) (u : List Char) :
    (M.blk k).drop i ++ M.hflat u = d :: M.img (M.nextSt k i) u := by
  have hi : i < (M.blk k).length := by
    rcases Nat.lt_or_ge i (M.blk k).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hd; cases hd
  rw [List.drop_eq_getElem_cons hi]
  have : (M.blk k)[i] = d := by rw [List.getElem?_eq_getElem hi] at hd; injection hd
  rw [this]
  unfold nextSt
  split
  · rfl
  · next hn =>
    have : (M.blk k).drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [List.cons_append, this, List.nil_append]; rfl

/-- **One image step.** From a state, either the source is exhausted at a boundary, or the next image letter
is the letter `d` at offset `i` of a block of class `k`, after which the state is `nextSt k i`: either we were
inside that block (no source letter is read), or at a boundary before a source letter of class `k` (`i = 0`). -/
theorem img_cases (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {q : St} {u : List Char}
    (hq : q ∈ M.stList) :
    (q = none ∧ u = []) ∨
      ∃ k i d u', k ≤ M.S.length ∧ (M.blk k)[i]? = some d ∧ M.img q u = d :: M.img (M.nextSt k i) u' ∧
        ((q = some (k, i) ∧ u' = u) ∨ (q = none ∧ i = 0 ∧ ∃ a, u = a :: u' ∧ clsOf M.S a = k)) := by
  rcases (M.mem_stList).mp hq with rfl | ⟨k, i, rfl, hk, _, hil⟩
  · cases u with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons a u' =>
      right
      have hb := M.blk_clsOf hS a
      obtain ⟨d, tl, hdt⟩ := List.exists_cons_of_ne_nil (hne a)
      have hd : (M.blk (clsOf M.S a))[0]? = some d := by rw [hb, hdt]; rfl
      refine ⟨clsOf M.S a, 0, d, u', clsOf_le a M.S, hd, ?_, Or.inr ⟨rfl, rfl, a, rfl, rfl⟩⟩
      rw [← M.drop_blk hd u']
      simp only [img, hflat, List.map_cons, List.flatten_cons, List.drop_zero, hb]
  · right
    have hd : (M.blk k)[i]? = some (M.blk k)[i] := List.getElem?_eq_getElem hil
    exact ⟨k, i, _, u, hk, hd, M.drop_blk hd u, Or.inl ⟨rfl, rfl⟩⟩

/-- `testAt` at a known letter. -/
theorem testAt_of {P : Char → Bool} {l : List Char} {i : Nat} {d : Char} (hd : l[i]? = some d) :
    testAt P l i = P d := by
  simp only [testAt, hd]

end PhSim

end Shallot.Cfg
