import MacroPeg.Properties.Visits
import MacroPeg.Properties.SpecializeCorrect

/-!
# The size of the memo table: an upper bound for the finite-argument fragment, a lower bound for Macro PEG

A memoizing (packrat) call-by-name evaluator stores one entry per visited judgment `(call expression, position)`. Its
table size is what decides the packrat complexity, so this file bounds the number of distinct visited call judgments
(`Visits`, `IsCall`).

* **Upper bound** (`memo_bound`): for a well-formed finite-argument grammar (`FGrammar`, see `FiniteArgs.lean`) and an
  admissible entry, the visited call judgments on an input `x` inject into the numbers below
  `(|env| + Σ_B |D|^arity(B)) · (|x| + 1)`: linear in the input length.
* **Lower bound** (`exp_visits_all`, `no_linear_memo_bound`): the fixed grammar `F(x) ← "a" (F(x "0") / F(x "1"))` with
  the start `F(ε)` visits `F(w)` for all `2^n` bit strings `w` of length `n` on the input `a^n`. So for general Macro PEG
  (actual arguments may be built) no bound `N · (|x| + 1)` holds, whatever the constant `N`.

What is and is not claimed: the measure is the number of distinct judgments when call expressions are compared as
syntax. It is not the running time, it says nothing about evaluators that share subterms or represent arguments
differently, and it is not a lower bound on the complexity of the recognition problem.
-/

namespace Shallot.MacroPeg

def IsCall : MExp → Prop
  | .call _ _ => True
  | _ => False

/-! ## Upper bound for the finite-argument fragment -/

/-- Everything the evaluation of the entry visits is related to some expression of the specialized grammar. -/
theorem visits_rel (F : FGrammar) (hF : F.WF) {e e' : MExp} {x x' : List Char} (h : Visits F.toMacro e x e' x') :
    ∀ p, Rel F F.specs e p → ∃ p', Rel F F.specs e' p' := by
  induction h with
  | self => exact fun p hp => ⟨p, hp⟩
  | seqL _ ih => intro p hp; cases hp with | seq h₁ _ => exact ih _ h₁
  | seqR _ _ ih => intro p hp; cases hp with | seq _ h₂ => exact ih _ h₂
  | altL _ ih => intro p hp; cases hp with | alt h₁ _ => exact ih _ h₁
  | altR _ _ ih => intro p hp; cases hp with | alt _ h₂ => exact ih _ h₂
  | star _ ih => intro p hp; cases hp with | star h₁ => exact ih _ h₁
  | starR _ _ ih => intro p hp; exact ih p hp
  | notP _ ih => intro p hp; cases hp with | notP h₁ => exact ih _ h₁
  | call hr _ _ ih =>
    intro p hp
    cases hp with
    | envRef _ hi =>
      obtain ⟨q, hq, hrq⟩ := F.ruleAtM_toMacro_none_env hi
      rw [hrq] at hr; cases hr
      refine ih q ?_
      show Rel F F.specs (MExp.subst [] (embedExp q)) q
      rw [subst_embedExp_any]; exact rel_embed F F.specs q (hF.1 q (List.mem_of_getElem? hq))
    | specRef B w hm =>
      obtain ⟨rB, hrB, hl, _⟩ := (F.specs_specSet hF).1 _ hm
      rw [F.ruleAtM_toMacro_frag hrB] at hr; cases hr
      exact ih _ (rel_spec F F.specs hF hl rB.body (hF.2.2 rB (List.mem_of_getElem? hrB))
        ((F.specs_specSet hF).2 B w rB hm hrB))

/-- A call expression is related only to a nonterminal of the specialized grammar. -/
theorem rel_call_nt {F : FGrammar} {i : Nat} {args : List MExp} {p : PExp} (h : Rel F F.specs (.call i args) p) :
    ∃ k, p = .nt k ∧ k < F.env.length + F.specs.length := by
  cases h with
  | envRef _ hi => exact ⟨i, rfl, by omega⟩
  | specRef B w hm => exact ⟨_, rfl, by have := codeOn_lt hm; omega⟩

/-- The nonterminal determines the call expression. -/
theorem rel_call_inj {F : FGrammar} {e e' : MExp} {p p' : PExp} (hc : IsCall e)
    (h : Rel F F.specs e p) (h' : Rel F F.specs e' p') (hp : p = p') : e = e' := by
  cases h with
  | envRef i hi =>
    cases h' with
    | envRef i' _ => simp only [PExp.nt.injEq] at hp; subst hp; rfl
    | specRef B' w' _ => simp only [PExp.nt.injEq] at hp; omega
    | _ => cases hp
  | specRef B w hm =>
    cases h' with
    | envRef i' hi' => simp only [PExp.nt.injEq] at hp; omega
    | specRef B' w' hm' =>
      simp only [PExp.nt.injEq] at hp
      obtain ⟨rfl, rfl⟩ := codeOn_inj hm hm' (by omega)
      rfl
    | _ => cases hp
  | _ => exact absurd hc id

/-- The table slot of a visited call judgment: its nonterminal, and the length of the consumed prefix. -/
noncomputable def memoSlot (F : FGrammar) (x : List Char) (e : MExp) (x' : List Char) : Nat :=
  @dite _ (∃ k, Rel F F.specs e (.nt k)) (Classical.propDecidable _)
    (fun h => Classical.choose h * (x.length + 1) + (x.length - x'.length)) (fun _ => 0)

theorem slot_div_mod {k d L : Nat} (hd : d ≤ L) : (d + k * (L + 1)) / (L + 1) = k ∧ (d + k * (L + 1)) % (L + 1) = d := by
  constructor
  · rw [Nat.add_mul_div_right _ _ (Nat.succ_pos L), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- **Upper bound on the memo table.** For a well-formed finite-argument grammar and an admissible entry, the call
judgments visited by call-by-name evaluation of the entry on `x` are numbered injectively by numbers below
`(|env| + |specs|) · (|x| + 1)`, where `|specs| = Σ_B |D|^arity(B)` (`memo_bound_sum`). -/
theorem memo_bound (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) (x : List Char) :
    ∀ e x', Visits F.toMacro (F.entry A ks) x e x' → IsCall e →
      memoSlot F x e x' < (F.env.length + F.specs.length) * (x.length + 1) ∧
      ∀ e₂ x₂, Visits F.toMacro (F.entry A ks) x e₂ x₂ → IsCall e₂ →
        memoSlot F x e x' = memoSlot F x e₂ x₂ → e = e₂ ∧ x' = x₂ := by
  have hentry : Rel F F.specs (F.entry A ks) (.nt (F.env.length + F.code A ks)) :=
    .specRef A ks ((F.mem_specs A ks).2 hv)
  -- every visited call has a nonterminal below `N`, and a suffix position
  have key : ∀ e x', Visits F.toMacro (F.entry A ks) x e x' → IsCall e →
      ∃ h : (∃ k, Rel F F.specs e (.nt k)), Classical.choose h < F.env.length + F.specs.length ∧
        x'.length ≤ x.length ∧ ∃ p, x = p ++ x' := by
    intro e x' hvis hc
    obtain ⟨p, hp⟩ := visits_rel F hF hvis _ hentry
    match e, hc, hp with
    | .call i args, _, hp =>
      obtain ⟨k, rfl, _⟩ := rel_call_nt hp
      have hex : ∃ k, Rel F F.specs (.call i args) (.nt k) := ⟨k, hp⟩
      obtain ⟨k', hkeq, hk'⟩ := rel_call_nt (Classical.choose_spec hex)
      simp only [PExp.nt.injEq] at hkeq
      rw [← hkeq] at hk'
      obtain ⟨q, hq⟩ := visits_suffix hvis
      exact ⟨hex, hk', by rw [hq, List.length_append]; omega, q, hq⟩
  intro e x' hvis hc
  obtain ⟨hex, hk, hlen, q, hq⟩ := key e x' hvis hc
  have hslot : memoSlot F x e x' = (x.length - x'.length) + Classical.choose hex * (x.length + 1) := by
    rw [memoSlot, dif_pos hex]; omega
  refine ⟨?_, ?_⟩
  · rw [hslot]
    have : (Classical.choose hex + 1) * (x.length + 1) ≤ (F.env.length + F.specs.length) * (x.length + 1) :=
      Nat.mul_le_mul_right _ hk
    rw [Nat.succ_mul] at this
    omega
  · intro e₂ x₂ hvis₂ hc₂ heq
    obtain ⟨hex₂, _, hlen₂, q₂, hq₂⟩ := key e₂ x₂ hvis₂ hc₂
    have hslot₂ : memoSlot F x e₂ x₂ = (x.length - x₂.length) + Classical.choose hex₂ * (x.length + 1) := by
      rw [memoSlot, dif_pos hex₂]; omega
    rw [hslot, hslot₂] at heq
    have h₁ := slot_div_mod (k := Classical.choose hex) (Nat.sub_le x.length x'.length)
    have h₂ := slot_div_mod (k := Classical.choose hex₂) (Nat.sub_le x.length x₂.length)
    rw [heq] at h₁
    have hk : Classical.choose hex = Classical.choose hex₂ := h₁.1.symm.trans h₂.1
    have hd : x.length - x'.length = x.length - x₂.length := h₁.2.symm.trans h₂.2
    refine ⟨rel_call_inj hc (Classical.choose_spec hex) (Classical.choose_spec hex₂) (by rw [hk]), ?_⟩
    exact List.append_inj_right' (hq.symm.trans hq₂) (by omega)

/-- The same bound with `|specs|` written as `Σ_B |D|^arity(B)`. -/
theorem memo_bound_sum (F : FGrammar) (hF : F.WF) {A : Nat} {ks : List Nat} (hv : F.ValidVec A ks) (x : List Char)
    (e : MExp) (x' : List Char) (h : Visits F.toMacro (F.entry A ks) x e x') (hc : IsCall e) :
    memoSlot F x e x' < (F.env.length + (F.rules.map (fun r => F.D.length ^ r.arity)).sum) * (x.length + 1) := by
  rw [← FGrammar.length_specs]; exact (memo_bound F hF hv x e x' h hc).1

/-! ## Lower bound: exponentially many visited calls -/

/-- `F(x) ← "a" (F(x "0") / F(x "1"))`. -/
def expG : MGrammar :=
  ⟨[⟨1, .seq (.lit ['a']) (.alt (.call 0 [.seq (.param 0) (.lit ['0'])]) (.call 0 [.seq (.param 0) (.lit ['1'])]))⟩]⟩

def expStart : MExp := .call 0 [.eps]

def bitLit (b : Bool) : MExp := .lit [if b then '1' else '0']

/-- The argument built after the choices `w` (most recent first). -/
def argOf : List Bool → MExp
  | [] => .eps
  | b :: w => .seq (argOf w) (bitLit b)

theorem argOf_inj : ∀ {w w' : List Bool}, argOf w = argOf w' → w = w'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | b :: w, b' :: w', h => by
    simp only [argOf, MExp.seq.injEq, bitLit, MExp.lit.injEq, List.cons.injEq, and_true] at h
    obtain ⟨hw, hb⟩ := h
    rw [argOf_inj hw]
    cases b <;> cases b' <;> simp_all

def aPow (n : Nat) : List Char := List.replicate n 'a'

theorem strip_a (rest : List Char) : Shallot.stripPrefix? ['a'] ('a' :: rest) = some rest := by
  simp [Shallot.stripPrefix?, Shallot.beqChar]

/-- Every call of `F` fails on every `a^m`. -/
theorem expF_fails : ∀ (m : Nat) (arg : MExp), MDerives expG .callByName (.call 0 [arg]) (aPow m) .fail
  | 0, arg => .callNameFail 0 [arg] _ [] rfl rfl rfl (.seqFail₁ _ _ _ (.litFail ['a'] [] rfl))
  | m + 1, arg =>
    .callNameFail 0 [arg] _ _ rfl rfl rfl
      (.seqFail₂ _ _ _ (aPow m) _ (.litOk ['a'] _ _ (strip_a _))
        (.altFail _ _ _ (expF_fails m _) (expF_fails m _)))

/-- One step: from `F(argOf w)` on `a^(m+1)` the evaluation visits `F(argOf (b :: w))` on `a^m`, for both `b`. -/
theorem exp_step (w : List Bool) (b : Bool) (m : Nat) :
    Visits expG (.call 0 [argOf w]) (aPow (m + 1)) (.call 0 [argOf (b :: w)]) (aPow m) := by
  refine .call rfl rfl (.seqR (.litOk ['a'] _ (aPow m) (strip_a _)) ?_)
  cases b with
  | false => exact .altL (.self _ _)
  | true => exact .altR (expF_fails m _) (.self _ _)

theorem exp_visits : ∀ (w : List Bool) (n : Nat), w.length ≤ n →
    Visits expG expStart (aPow n) (.call 0 [argOf w]) (aPow (n - w.length))
  | [], n, _ => by
    show Visits expG expStart (aPow n) expStart (aPow (n - 0))
    rw [Nat.sub_zero]; exact .self _ _
  | b :: w, n, h => by
    have hlen : n - w.length = (n - (b :: w).length) + 1 := by simp only [List.length_cons] at h ⊢; omega
    have ih := exp_visits w n (by simp only [List.length_cons] at h; omega)
    rw [hlen] at ih
    exact ih.trans (exp_step w b _)

/-- **Lower bound.** On `a^n` the evaluation of `F(ε)` visits `F(argOf w)` at the end of the input for every bit string
`w` of length `n`: `2^n` distinct call judgments (`argOf_inj`). -/
theorem exp_visits_all (n : Nat) (w : List Bool) (hw : w.length = n) :
    Visits expG expStart (aPow n) (.call 0 [argOf w]) [] := by
  have := exp_visits w n (by omega)
  rwa [hw, Nat.sub_self] at this

/-! ### No linear bound -/

/-- All bit strings of length `n`. -/
def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).map (false :: ·) ++ (allWords n).map (true :: ·)

theorem length_allWords : ∀ n, (allWords n).length = 2 ^ n
  | 0 => rfl
  | n + 1 => by simp [allWords, length_allWords n, Nat.pow_succ]; omega

theorem mem_allWords : ∀ {n : Nat} {w : List Bool}, w ∈ allWords n → w.length = n
  | 0, w, h => by simp [allWords] at h; subst h; rfl
  | n + 1, w, h => by
    simp only [allWords, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [mem_allWords hv]

theorem nodup_map_of_inj {α β : Type} (f : α → β) :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hl, hinj => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj f hl.2 (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy))⟩
    intro hmem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hmem
    exact hl.1 (hinj a List.mem_cons_self b (List.mem_cons_of_mem _ hb) hfb.symm ▸ hb)

theorem nodup_allWords : ∀ n, (allWords n).Nodup
  | 0 => by simp [allWords]
  | n + 1 => by
    rw [allWords, List.nodup_append]
    refine ⟨nodup_map_of_inj _ (nodup_allWords n) (fun a _ b _ h => by simpa using h),
      nodup_map_of_inj _ (nodup_allWords n) (fun a _ b _ h => by simpa using h), ?_⟩
    intro a ha b hb hab
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hb
    simp at hab

/-- A duplicate-free list of numbers below `M` has at most `M` elements. -/
theorem nodup_length_le : ∀ (M : Nat) (l : List Nat), l.Nodup → (∀ a ∈ l, a < M) → l.length ≤ M
  | 0, [], _, _ => Nat.le_refl _
  | 0, a :: _, _, h => absurd (h a List.mem_cons_self) (Nat.not_lt_zero _)
  | M + 1, l, hl, h => by
    have hsub : ∀ a ∈ l.erase M, a < M := by
      intro a ha
      obtain ⟨hne, hmem⟩ := (List.Nodup.mem_erase_iff hl).1 ha
      have := h a hmem; omega
    have ih := nodup_length_le M (l.erase M) (hl.erase M) hsub
    by_cases hM : M ∈ l
    · rw [List.length_erase_of_mem hM] at ih; omega
    · rw [List.erase_of_not_mem hM] at ih; omega

theorem two_mul_add_one_le_pow : ∀ m, 3 ≤ m → 2 * m + 1 ≤ 2 ^ m
  | 0, h | 1, h | 2, h => absurd h (by decide)
  | 3, _ => by decide
  | m + 4, _ => by
    have := two_mul_add_one_le_pow (m + 3) (by omega)
    have h2 : 2 ≤ 2 ^ (m + 3) := by
      have := @Nat.lt_two_pow_self (m + 3); omega
    rw [Nat.pow_succ]; omega

/-- For every `N` some `n` has `N · (n + 1) < 2^n`. -/
theorem exists_pow_gt (N : Nat) : ∃ n, N * (n + 1) < 2 ^ n := by
  refine ⟨(N + 3) + (N + 3), ?_⟩
  have h1 : N < 2 ^ (N + 3) := by have := @Nat.lt_two_pow_self (N + 3); omega
  have h2 := two_mul_add_one_le_pow (N + 3) (by omega)
  rw [Nat.pow_add, show N + 3 + (N + 3) + 1 = 2 * (N + 3) + 1 by omega]
  calc N * (2 * (N + 3) + 1) < 2 ^ (N + 3) * (2 * (N + 3) + 1) := Nat.mul_lt_mul_of_pos_right h1 (by omega)
    _ ≤ 2 ^ (N + 3) * 2 ^ (N + 3) := Nat.mul_le_mul_left _ h2

/-- **No linear memo table for general Macro PEG.** There is no constant `N` such that, on every input `x`, the call
judgments visited by call-by-name evaluation of `F(ε)` in `expG` can be numbered injectively below `N · (|x| + 1)` —
the bound that `memo_bound` gives for every finite-argument grammar. -/
theorem no_linear_memo_bound :
    ¬ ∃ N : Nat, ∀ x : List Char, ∃ slot : MExp → List Char → Nat,
      ∀ e x', Visits expG expStart x e x' → IsCall e →
        slot e x' < N * (x.length + 1) ∧
        ∀ e₂ x₂, Visits expG expStart x e₂ x₂ → IsCall e₂ → slot e x' = slot e₂ x₂ → e = e₂ ∧ x' = x₂ := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hn⟩ := exists_pow_gt N
  obtain ⟨slot, hslot⟩ := hN (aPow n)
  have hlen : (aPow n).length = n := List.length_replicate
  let img := (allWords n).map (fun w => slot (.call 0 [argOf w]) [])
  have hvis : ∀ w ∈ allWords n, Visits expG expStart (aPow n) (.call 0 [argOf w]) [] :=
    fun w hw => exp_visits_all n w (mem_allWords hw)
  have hnodup : img.Nodup := by
    refine nodup_map_of_inj _ (nodup_allWords n) ?_
    intro a ha b hb hab
    exact argOf_inj (by
      have := ((hslot _ _ (hvis a ha) trivial).2 _ _ (hvis b hb) trivial hab).1
      simpa using this)
  have hlt : ∀ v ∈ img, v < N * (n + 1) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
    have := (hslot _ _ (hvis w hw) trivial).1
    rwa [hlen] at this
  have := nodup_length_le _ img hnodup hlt
  rw [List.length_map, length_allWords] at this
  omega

end Shallot.MacroPeg
