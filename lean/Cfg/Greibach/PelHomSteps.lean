import Cfg.Greibach.PelHomBasic

/-!
# Letters and literals of the image; the rules of the simulating grammar

- `step1_spec`: reading one image letter (`step1`) hits the next state exactly when the letter passes the test.
- `litT_spec`: reading an image literal (`litT`) hits the state after it exactly when the image starts with it.
- The rules: every item has its body as its rule (`ruleAt_code`), so calls behave like bodies; the
  subexpression list is closed under subexpressions and rule bodies.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt beqChar leChar stripPrefix? ruleAt_mem)

namespace PhSim

variable (M : PhSim)

/-- At a boundary with the source exhausted, reading an image letter fails. -/
theorem step1_none_nil {G : Grammar} (P : Char → Bool) : Misses G M.stList (M.step1 P none) [] := by
  intro q' _
  refine chain_fail (fun k _ => ?_)
  split
  · exact M.sel_nil k
  · exact phFail_fail _

/-- At a boundary before a letter of class `k`, the alternatives for other classes fail. -/
theorem step1_none_other {G : Grammar} (P : Char → Bool) (q' : St) {a : Char} {u : List Char} {j : Nat}
    (hj : j < M.S.length + 1) (hne : clsOf M.S a ≠ j) :
    Derives G (if testAt P (M.blk j) 0 = true ∧ M.nextSt j 0 = q' then M.sel j else phFail) (a :: u) .fail := by
  split
  · exact (M.sel_cons (by omega) a u).2 hne
  · exact phFail_fail _

/-- **One image letter.** -/
theorem step1_spec (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {G : Grammar}
    (P : Char → Bool) {q : St} {u : List Char} (hq : q ∈ M.stList) :
    (M.img q u = [] ∧ Misses G M.stList (M.step1 P q) u) ∨
      ∃ d q₁ u₁, M.img q u = d :: M.img q₁ u₁ ∧ q₁ ∈ M.stList ∧
        (P d = true → Hits G M.stList (M.step1 P q) u q₁ u₁) ∧
        (P d = false → Misses G M.stList (M.step1 P q) u) := by
  rcases M.img_cases hne hS (u := u) hq with ⟨rfl, rfl⟩ | ⟨k, i, d, u', hk, hd, himg, hsrc⟩
  · exact Or.inl ⟨rfl, M.step1_none_nil P⟩
  · right
    have ht : testAt P (M.blk k) i = P d := testAt_of hd
    refine ⟨d, M.nextSt k i, u', himg, M.nextSt_mem hk i, ?_⟩
    rcases hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, a, rfl, hcls⟩
    · refine ⟨fun hP => ⟨M.nextSt_mem hk i, fun q' _ => ⟨fun he => ?_, fun hne' => ?_⟩⟩, fun hP q' _ => ?_⟩
      · subst he
        exact ⟨_, by simp only [step1, ht, hP, and_self, if_true]; exact .eps _⟩
      · have : ¬(testAt P (M.blk k) i = true ∧ M.nextSt k i = q') := fun h => hne' h.2.symm
        simp only [step1, if_neg this]; exact phFail_fail _
      · have : ¬(testAt P (M.blk k) i = true ∧ M.nextSt k i = q') := by
          rw [ht, hP]; exact fun h => Bool.false_ne_true h.1
        simp only [step1, if_neg this]; exact phFail_fail _
    · have hkr : k ∈ List.range (M.S.length + 1) := List.mem_range.mpr (by omega)
      refine ⟨fun hP => ⟨M.nextSt_mem hk 0, fun q' _ => ⟨fun he => ?_, fun hne' => ?_⟩⟩, fun hP q' _ => ?_⟩
      · subst he
        obtain ⟨t, hsel⟩ := (M.sel_cons (G := G) hk a u').1 hcls
        have hF : Derives G (if testAt P (M.blk k) 0 = true ∧ M.nextSt k 0 = M.nextSt k 0 then M.sel k
            else phFail) (a :: u') (.ok t u') := by
          rw [if_pos ⟨ht.trans hP, rfl⟩]; exact hsel
        exact chain_ok (F := fun j => if testAt P (M.blk j) 0 = true ∧ M.nextSt j 0 = M.nextSt k 0 then M.sel j
            else phFail) (y₁ := k) hF hkr
          (fun j hj hjk => M.step1_none_other P _ (List.mem_range.mp hj) (by rw [hcls]; exact fun h => hjk h.symm))
      · refine chain_fail (fun j hj => ?_)
        rcases Classical.em (j = k) with rfl | hjk
        · have : ¬(testAt P (M.blk j) 0 = true ∧ M.nextSt j 0 = q') := fun h => hne' h.2.symm
          simp only [if_neg this]; exact phFail_fail _
        · exact M.step1_none_other P _ (List.mem_range.mp hj) (by rw [hcls]; exact fun h => hjk h.symm)
      · refine chain_fail (fun j hj => ?_)
        rcases Classical.em (j = k) with rfl | hjk
        · have : ¬(testAt P (M.blk j) 0 = true ∧ M.nextSt j 0 = q') := by
            rw [ht, hP]; exact fun h => Bool.false_ne_true h.1
          simp only [if_neg this]; exact phFail_fail _
        · exact M.step1_none_other P _ (List.mem_range.mp hj) (by rw [hcls]; exact fun h => hjk h.symm)

/-- `litT` on a nonempty literal is the sequencing pattern. -/
theorem litT_cons (c : Char) (s : List Char) (q : St) :
    M.litT (c :: s) q = chainSeq M.stList (M.step1 (beqChar c) q) (M.litT s) := rfl

/-- **An image literal.** -/
theorem litT_spec (hne : ∀ a, M.h a ≠ []) (hS : ∀ a, a ∉ M.S → M.h a = M.h₀) {G : Grammar} :
    ∀ (s : List Char) (q : St) (u : List Char), q ∈ M.stList →
      (∀ r, stripPrefix? s (M.img q u) = some r → ∃ q₁ u₁, r = M.img q₁ u₁ ∧ Hits G M.stList (M.litT s q) u q₁ u₁) ∧
      (stripPrefix? s (M.img q u) = none → Misses G M.stList (M.litT s q) u)
  | [], q, u, hq => by
    refine ⟨fun r hr => ⟨q, u, ?_, ?_⟩, fun hr => ?_⟩
    · simp only [stripPrefix?] at hr; injection hr with hr; exact hr.symm
    · exact guardEq_hits hq
    · simp only [stripPrefix?] at hr; cases hr
  | c :: s, q, u, hq => by
    rw [M.litT_cons]
    rcases M.step1_spec hne hS (G := G) (beqChar c) hq with ⟨himg, hmiss⟩ | ⟨d, q₁, u₁, himg, _, hhit, hmiss⟩
    · refine ⟨fun r hr => ?_, fun _ => chainSeq_misses₁ hmiss⟩
      rw [himg] at hr; simp only [stripPrefix?] at hr; cases hr
    · rw [himg]
      cases hb : beqChar c d with
      | false =>
        refine ⟨fun r hr => ?_, fun _ => chainSeq_misses₁ (hmiss hb)⟩
        simp only [stripPrefix?, hb] at hr; cases hr
      | true =>
        have ih := litT_spec hne hS (G := G) s q₁ u₁ (hhit hb).1
        simp only [stripPrefix?, hb, if_true]
        refine ⟨fun r hr => ?_, fun hr => chainSeq_misses₂ (hhit hb) (ih.2 hr)⟩
        obtain ⟨q₂, u₂, hr', hh⟩ := ih.1 r hr
        exact ⟨q₂, u₂, hr', chainSeq_hits (hhit hb) hh⟩

/-! ## Subexpressions and rules -/

/-- An expression is among its subexpressions. -/
theorem mem_subs_self (e : PExp) : e ∈ subs e := by
  cases e <;> simp [subs]

/-- Subexpressions of subexpressions are subexpressions. -/
theorem subs_trans : ∀ {x e e' : PExp}, e ∈ subs x → e' ∈ subs e → e' ∈ subs x
  | .seq a b, e, e', h, h' => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with rfl | h | h
    · simp only [subs, List.mem_cons, List.mem_append] at h'; exact h'
    · exact Or.inr (Or.inl (subs_trans h h'))
    · exact Or.inr (Or.inr (subs_trans h h'))
  | .alt a b, e, e', h, h' => by
    simp only [subs, List.mem_cons, List.mem_append] at h ⊢
    rcases h with rfl | h | h
    · simp only [subs, List.mem_cons, List.mem_append] at h'; exact h'
    · exact Or.inr (Or.inl (subs_trans h h'))
    · exact Or.inr (Or.inr (subs_trans h h'))
  | .star a, e, e', h, h' => by
    simp only [subs, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simp only [subs, List.mem_cons] at h'; exact h'
    · exact Or.inr (subs_trans h h')
  | .notP a, e, e', h, h' => by
    simp only [subs, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · simp only [subs, List.mem_cons] at h'; exact h'
    · exact Or.inr (subs_trans h h')
  | .eps, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'
  | .any, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'
  | .chr _, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'
  | .range _ _, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'
  | .lit _, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'
  | .nt _, e, e', h, h' => by simp only [subs, List.mem_singleton] at h; subst h; exact h'

/-- The subexpression list is closed under subexpressions. -/
theorem elist_sub {e e' : PExp} (he : e ∈ M.elist) (h' : e' ∈ subs e) : e' ∈ M.elist := by
  simp only [elist, List.mem_append, List.mem_flatMap] at he ⊢
  rcases he with he | ⟨r, hr, he⟩
  · exact Or.inl (subs_trans he h')
  · exact Or.inr ⟨r, hr, subs_trans he h'⟩

/-- Rule bodies are in the subexpression list. -/
theorem elist_rule {i : Nat} {r : PExp} (hr : ruleAt M.g.rules i = some r) : r ∈ M.elist := by
  simp only [elist, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨r, ruleAt_mem hr, mem_subs_self r⟩

/-- The start call is in the subexpression list. -/
theorem elist_start : PExp.nt M.g.start ∈ M.elist := by
  simp only [elist, List.mem_append]; exact Or.inl (mem_subs_self _)

/-- The children of `seq`. -/
theorem elist_seq {a b : PExp} (h : PExp.seq a b ∈ M.elist) : a ∈ M.elist ∧ b ∈ M.elist :=
  ⟨M.elist_sub h (by simp [subs, mem_subs_self]), M.elist_sub h (by simp [subs, mem_subs_self])⟩

/-- The children of `alt`. -/
theorem elist_alt {a b : PExp} (h : PExp.alt a b ∈ M.elist) : a ∈ M.elist ∧ b ∈ M.elist :=
  ⟨M.elist_sub h (by simp [subs, mem_subs_self]), M.elist_sub h (by simp [subs, mem_subs_self])⟩

/-- The child of `star`. -/
theorem elist_star {a : PExp} (h : PExp.star a ∈ M.elist) : a ∈ M.elist :=
  M.elist_sub h (by simp [subs, mem_subs_self])

/-- The child of `notP`. -/
theorem elist_notP {a : PExp} (h : PExp.notP a ∈ M.elist) : a ∈ M.elist :=
  M.elist_sub h (by simp [subs, mem_subs_self])

/-- The items. -/
theorem mem_items {e : PExp} {q q' : St} :
    (e, q, q') ∈ M.items ↔ e ∈ M.elist ∧ q ∈ M.stList ∧ q' ∈ M.stList := by
  simp only [items, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨e₁, he, q₁, hq, q₂, hq', rfl, rfl, rfl⟩; exact ⟨he, hq, hq'⟩
  · rintro ⟨he, hq, hq'⟩; exact ⟨e, he, q, hq, q', hq', rfl, rfl, rfl⟩

/-- Looking up the first index of a member. -/
theorem ruleAt_phIdx (f : Item → PExp) {x : Item} : ∀ {l : List Item}, x ∈ l →
    ruleAt (l.map f) (phIdx x l) = some (f x)
  | [], h => absurd h List.not_mem_nil
  | y :: l, h => by
    rcases Classical.em (x = y) with hxy | hxy
    · subst hxy; simp [phIdx, ruleAt]
    · have hl : x ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hxy
        · exact h
      simp only [phIdx, if_neg hxy, List.map_cons, ruleAt]
      exact ruleAt_phIdx f hl

/-- An item's rule is its body. -/
theorem ruleAt_code {x : Item} (hx : x ∈ M.items) : ruleAt M.grammar.rules (M.code x) = some (M.body x) :=
  ruleAt_phIdx M.body hx

/-- A call succeeds like its body. -/
theorem N_ok {x : Item} (hx : x ∈ M.items) {u r : List Char} {t : PTree}
    (h : Derives M.grammar (M.body x) u (.ok t r)) : Derives M.grammar (M.N x) u (.ok (.nodeNT (M.code x) t) r) :=
  .ntOk _ _ _ _ _ (M.ruleAt_code hx) h

/-- A call fails like its body. -/
theorem N_fail {x : Item} (hx : x ∈ M.items) {u : List Char}
    (h : Derives M.grammar (M.body x) u .fail) : Derives M.grammar (M.N x) u .fail :=
  .ntFail _ _ _ (M.ruleAt_code hx) h

/-- Hits of the bodies are hits of the calls. -/
theorem hits_N {e : PExp} {q q₁ : St} {u u₁ : List Char} (he : e ∈ M.elist) (hq : q ∈ M.stList)
    (h : Hits M.grammar M.stList (fun q' => M.body (e, q, q')) u q₁ u₁) :
    Hits M.grammar M.stList (M.NF e q) u q₁ u₁ := by
  refine ⟨h.1, fun q' hq' => ⟨fun he' => ?_, fun hne => ?_⟩⟩
  · obtain ⟨t, ht⟩ := (h.2 q' hq').1 he'
    exact ⟨_, M.N_ok ((M.mem_items).mpr ⟨he, hq, hq'⟩) ht⟩
  · exact M.N_fail ((M.mem_items).mpr ⟨he, hq, hq'⟩) ((h.2 q' hq').2 hne)

/-- Misses of the bodies are misses of the calls. -/
theorem misses_N {e : PExp} {q : St} {u : List Char} (he : e ∈ M.elist) (hq : q ∈ M.stList)
    (h : Misses M.grammar M.stList (fun q' => M.body (e, q, q')) u) :
    Misses M.grammar M.stList (M.NF e q) u :=
  fun q' hq' => M.N_fail ((M.mem_items).mpr ⟨he, hq, hq'⟩) (h q' hq')

/-- `FL e q` succeeds when the calls of `e` miss. -/
theorem FL_ok {e : PExp} {q : St} {u : List Char} (h : Misses M.grammar M.stList (M.NF e q) u) :
    Derives M.grammar (M.FL e q) u (.ok .notT u) :=
  .notFail _ _ h.chain_fail

/-- `FL e q` fails when the calls of `e` hit. -/
theorem FL_fail {e : PExp} {q q₁ : St} {u u₁ : List Char} (h : Hits M.grammar M.stList (M.NF e q) u q₁ u₁) :
    Derives M.grammar (M.FL e q) u .fail := by
  obtain ⟨t, ht⟩ := h.chain_ok
  exact .notOk _ _ _ _ ht

end PhSim

end Shallot.Cfg
