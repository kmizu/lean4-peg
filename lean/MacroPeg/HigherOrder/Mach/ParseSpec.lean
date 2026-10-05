import MacroPeg.HigherOrder.Mach.Parse

/-!
# The reading machine is correct: basics

Runs compose (`pruns_add`); a stopped machine stays stopped (`pruns_halted`). Items decode through the tables
(`itemOf`), and decoding is stable when the tables grow (`tyOf_extend`, `ctxOf_extend`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## Runs -/

theorem pruns_add (s : PSt) (m n : Nat) : pruns s (m + n) = pruns (pruns s m) n := by
  induction m generalizing s with
  | zero => simp [pruns]
  | succ m ih => rw [Nat.succ_add]; exact ih (pstep s)

theorem pstep_halted {s : PSt} (h : s.ctl = []) : pstep s = s := by simp [pstep, h]

theorem pruns_halted {s : PSt} (h : s.ctl = []) : ∀ n, pruns s n = s
  | 0 => rfl
  | n + 1 => by simp only [pruns, pstep_halted h]; exact pruns_halted h n

/-- The machine reaches `s'` from `s` in `n` steps. -/
def Reach (s s' : PSt) (n : Nat) : Prop := pruns s n = s'

theorem Reach.trans {s s₁ s₂ : PSt} {m n : Nat} (h₁ : Reach s s₁ m) (h₂ : Reach s₁ s₂ n) : Reach s s₂ (m + n) := by
  unfold Reach at *; rw [pruns_add, h₁, h₂]

theorem Reach.step (s : PSt) : Reach s (pstep s) 1 := rfl

theorem Reach.refl (s : PSt) : Reach s s 0 := rfl

/-- The machine stops rejecting. -/
def Fails (s : PSt) : Prop := ∃ n, (pruns s n).ctl = [] ∧ (pruns s n).ok = false

theorem Fails.of_reach {s s' : PSt} {n : Nat} (h : Reach s s' n) (hf : Fails s') : Fails s := by
  obtain ⟨m, h₁, h₂⟩ := hf
  exact ⟨n + m, by rw [pruns_add, h]; exact h₁, by rw [pruns_add, h]; exact h₂⟩

theorem Fails.fail (s : PSt) : Fails s.fail := ⟨0, rfl, rfl⟩

theorem Fails.of_step {s : PSt} (h : Fails (pstep s)) : Fails s := Fails.of_reach (Reach.step s) h

/-! ## Decoding items -/

/-- The literal with number `i`. -/
def litOf (lt : List (List Nat)) (i : Nat) : Option (List Char) := (lt[i]?).map (List.map Char.ofNat)

def opOf (tt : List (Nat × Nat)) (lt : List (List Nat)) (it : MItem) : Option Op :=
  match it.tag with
  | 0 => some (.leaf .eps)
  | 1 => some (.leaf .any)
  | 2 => some (.leaf (.chr (Char.ofNat it.a)))
  | 3 => some (.leaf (.range (Char.ofNat it.a) (Char.ofNat it.b)))
  | 4 => (litOf lt it.a).map (fun s => .leaf (.lit s))
  | 5 => some .seq
  | 6 => some .alt
  | 7 => some .star
  | 8 => some .notP
  | 9 => some (.var it.a)
  | 10 => some (.rule it.a)
  | 11 =>
    match tyOf tt it.a, tyOf tt it.b with
    | some a, some σ => some (.lam a σ)
    | _, _ => none
  | 12 =>
    match tyOf tt it.a, tyOf tt it.b with
    | some a, some b => some (.app a b)
    | _, _ => none
  | _ => none

def itemOf (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (it : MItem) : Option Item :=
  match opOf tt lt it, ctxOf tt ct it.ctx with
  | some op, some Γ => some ⟨op, Γ⟩
  | _, _ => none

def itemsOf (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (l : List MItem) : Option (List Item) :=
  l.mapM (itemOf tt ct lt)

/-! ## Growing tables -/

/-- Well-formed contexts: each extends a smaller context by a type in the table. -/
def CTWF (tt ct : List (Nat × Nat)) : Prop := ∀ k (h : k < ct.length), ct[k].1 ≤ k ∧ ct[k].2 ≤ tt.length

theorem tyOf_extend {tt tt' : List (Nat × Nat)} (hw : TTWF tt) (he : ∃ e, tt' = tt ++ e) {i : Nat} (hi : i ≤ tt.length) :
    tyOf tt' i = tyOf tt i := by
  obtain ⟨e, rfl⟩ := he; exact tyOf_append hw e i hi

theorem ctxOf_some {tt ct : List (Nat × Nat)} (hw : TTWF tt) (hc : CTWF tt ct) :
    ∀ c, c ≤ ct.length → ∃ Γ, ctxOf tt ct c = some Γ
  | 0, _ => ⟨[], by rw [ctxOf]⟩
  | k + 1, hk => by
    have hlt : k < ct.length := by omega
    obtain ⟨hp, ht⟩ := hc k hlt
    obtain ⟨τ, hτ⟩ := tyOf_some hw ct[k].2 ht
    obtain ⟨Γ, hΓ⟩ := ctxOf_some hw hc ct[k].1 (by omega)
    refine ⟨τ :: Γ, ?_⟩
    rw [ctxOf]
    simp only [List.getElem?_eq_getElem hlt, hp, if_true, hτ, hΓ]

theorem ctxOf_extend {tt ct tt' ct' : List (Nat × Nat)} (hw : TTWF tt) (hc : CTWF tt ct)
    (het : ∃ e, tt' = tt ++ e) (hec : ∃ e, ct' = ct ++ e) :
    ∀ c, c ≤ ct.length → ctxOf tt' ct' c = ctxOf tt ct c
  | 0, _ => by rw [ctxOf, ctxOf]
  | k + 1, hk => by
    have hlt : k < ct.length := by omega
    obtain ⟨hp, ht⟩ := hc k hlt
    obtain ⟨e, rfl⟩ := hec
    have hg : (ct ++ e)[k]? = ct[k]? := List.getElem?_append_left hlt
    rw [ctxOf, ctxOf, hg]
    simp only [List.getElem?_eq_getElem hlt, hp, if_true]
    rw [tyOf_extend hw het ht, ctxOf_extend hw hc het ⟨e, rfl⟩ ct[k].1 (by omega)]

/-! ## Reading a type -/

theorem pruns_succ (s : PSt) (n : Nat) : pruns s (n + 1) = pruns (pstep s) n := rfl

/-- **Reading a type**: the machine consumes the type's code and pushes its number. -/
theorem readType_ok : ∀ (f : Nat) (l : List Nat) (τ : HO.Ty) (rest : List Nat), parseTy f l = some (τ, rest) →
    ∀ (s : PSt) (K : List Nat), s.tk = l → s.ctl = 1 :: K → TTWF s.tt →
      ∃ n tt' i, Reach s { s with tk := rest, ctl := K, ty := i :: s.ty, tt := tt' } n ∧
        TTWF tt' ∧ (∃ e, tt' = s.tt ++ e) ∧ i ≤ tt'.length ∧ tyOf tt' i = some τ ∧ n + 3 * rest.length ≤ 3 * l.length
  | 0, _, _, _, h, _, _, _, _, _ => by simp [parseTy] at h
  | _ + 1, [], _, _, h, _, _, _, _, _ => by simp [parseTy] at h
  | f + 1, t :: l, τ, rest, h, s, K, htk, hctl, hw => by
    match t, h with
    | 0, h =>
      simp only [parseTy, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨1, s.tt, 0, ?_, hw, ⟨[], by simp⟩, Nat.zero_le _, by rw [tyOf], by simp; omega⟩
      show pstep s = _
      simp [pstep, hctl, readType, htk]
    | 1, h =>
      simp only [parseTy] at h
      split at h
      · rename_i a l₁ ha
        obtain ⟨⟨b, l₂⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        -- push the frame for the right side, read the left side
        let s₁ : PSt := { s with tk := l, ctl := 1 :: 12 :: K }
        have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readType, htk, s₁]
        obtain ⟨n₁, tt₁, i₁, x₂, hw₁, he₁, hi₁, hτ₁, hn₁⟩ := readType_ok f l a l₁ ha s₁ (12 :: K) rfl rfl hw
        -- frame 12: read the right side
        let s₂ : PSt := { s₁ with tk := l₁, ctl := 12 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
        let s₃ : PSt := { s₂ with ctl := 1 :: 13 :: K }
        have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃]
        obtain ⟨n₂, tt₂, i₂, x₄, hw₂, he₂, hi₂, hτ₂, hn₂⟩ := readType_ok f l₁ b l₂ hb s₃ (13 :: K) rfl rfl hw₁
        -- frame 13: register the arrow
        let s₄ : PSt := { s₃ with tk := l₂, ctl := 13 :: K, ty := i₂ :: s₃.ty, tt := tt₂ }
        have hi₁' : i₁ ≤ tt₂.length := by
          obtain ⟨e, he⟩ := he₂
          rw [he, show s₃.tt = tt₁ from rfl, List.length_append]; omega
        let s₅ : PSt :=
          { s with
            tk := l₂
            ctl := K
            ty := (intern tt₂ i₁ i₂).2 :: s.ty
            tt := (intern tt₂ i₁ i₂).1 }
        have x₅ : Reach s₄ s₅ 1 := by
          show pstep s₄ = _
          simp [pstep, s₄, s₃, s₂, s₁, s₅]
        refine ⟨1 + n₁ + 1 + n₂ + 1, (intern tt₂ i₁ i₂).1, (intern tt₂ i₁ i₂).2,
          (((x₁.trans x₂).trans x₃).trans x₄).trans x₅, intern_wf hw₂ hi₁' hi₂, ?_, intern_snd_le _ _ _, ?_, ?_⟩
        · obtain ⟨e₁, rfl⟩ := he₁
          obtain ⟨e₂, rfl⟩ := he₂
          obtain ⟨e₃, h₃⟩ := intern_prefix (s.tt ++ e₁ ++ e₂) i₁ i₂
          exact ⟨e₁ ++ e₂ ++ e₃, by rw [h₃]; simp⟩
        · rw [tyOf_intern hw₂ hi₁' hi₂ (by rw [tyOf_extend hw₁ he₂ hi₁]; exact hτ₁) hτ₂]
        · simp only [List.length_cons] at hn₁ hn₂ ⊢; omega
      · cases h
    | _ + 2, h => simp [parseTy] at h

theorem parseTy_shorter {f : Nat} {l : List Nat} {τ : HO.Ty} {r : List Nat} (h : parseTy f l = some (τ, r)) :
    r.length < l.length := by
  have := parseTy_sound h
  have := Shallot.MacroPeg.Flat.length_serTy_pos τ
  rw [‹l = _›]; simp; omega

/-- **A malformed type makes the machine fail.** -/
theorem readType_fail : ∀ (f : Nat) (l : List Nat), l.length ≤ f → parseTy f l = none →
    ∀ (s : PSt) (K : List Nat), s.tk = l → s.ctl = 1 :: K → TTWF s.tt → Fails s
  | 0, l, hl, _, s, K, htk, hctl, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact Fails.of_step (by simp [pstep, hctl, readType, htk]; exact Fails.fail _)
  | f + 1, [], _, _, s, K, htk, hctl, _ =>
    Fails.of_step (by simp [pstep, hctl, readType, htk]; exact Fails.fail _)
  | f + 1, t :: l, hl, h, s, K, htk, hctl, hw => by
    match t, h with
    | 0, h => simp [parseTy] at h
    | 1, h =>
      let s₁ : PSt := { s with tk := l, ctl := 1 :: 12 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readType, htk, s₁]
      simp only [parseTy] at h
      split at h
      · rename_i a l₁ ha
        have hb : parseTy f l₁ = none := by
          cases hb : parseTy f l₁ with
          | none => rfl
          | some p => rw [hb] at h; simp at h
        obtain ⟨n₁, tt₁, i₁, x₂, hw₁, _, _, _, _⟩ := readType_ok f l a l₁ ha s₁ (12 :: K) rfl rfl hw
        let s₂ : PSt := { s₁ with tk := l₁, ctl := 12 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
        let s₃ : PSt := { s₂ with ctl := 1 :: 13 :: K }
        have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃]
        have := parseTy_shorter ha
        exact Fails.of_reach ((x₁.trans x₂).trans x₃)
          (readType_fail f l₁ (by simp at hl; omega) hb s₃ (13 :: K) rfl rfl hw₁)
      · rename_i ha
        exact Fails.of_reach x₁ (readType_fail f l (by simp at hl; omega) ha s₁ (12 :: K) rfl rfl hw)
    | k + 2, _ => exact Fails.of_step (by simp [pstep, hctl, readType, htk]; exact Fails.fail _)

/-! ## Facts about the tables -/

theorem tyOf_le {tt : List (Nat × Nat)} : ∀ {i : Nat} {τ : HO.Ty}, tyOf tt i = some τ → i ≤ tt.length
  | 0, _, _ => Nat.zero_le _
  | k + 1, _, h => by
    rw [tyOf] at h
    cases hk : tt[k]? with
    | none => rw [hk] at h; cases h
    | some _ => have := (List.getElem?_eq_some_iff.1 hk).1; omega

theorem tyOf_eq_p {tt : List (Nat × Nat)} : ∀ {i : Nat}, tyOf tt i = some .p → i = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [tyOf] at h
    split at h
    · split at h
      · split at h
        · simp at h
        · cases h
      · cases h
    · cases h

theorem ctxOf_le {tt ct : List (Nat × Nat)} : ∀ {c : Nat} {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → c ≤ ct.length
  | 0, _, _ => Nat.zero_le _
  | k + 1, _, h => by
    rw [ctxOf] at h
    cases hk : ct[k]? with
    | none => rw [hk] at h; cases h
    | some _ => have := (List.getElem?_eq_some_iff.1 hk).1; omega

/-- The tables of `s'` extend those of `s`. -/
structure Grows (tt ct : List (Nat × Nat)) (lt : List (List Nat)) (tt' ct' : List (Nat × Nat))
    (lt' : List (List Nat)) : Prop where
  tt : ∃ e, tt' = tt ++ e
  ct : ∃ e, ct' = ct ++ e
  lt : ∃ e, lt' = lt ++ e

theorem Grows.refl (tt ct : List (Nat × Nat)) (lt : List (List Nat)) : Grows tt ct lt tt ct lt :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem Grows.trans {tt ct tt₁ ct₁ tt₂ ct₂ : List (Nat × Nat)} {lt lt₁ lt₂ : List (List Nat)}
    (h₁ : Grows tt ct lt tt₁ ct₁ lt₁) (h₂ : Grows tt₁ ct₁ lt₁ tt₂ ct₂ lt₂) : Grows tt ct lt tt₂ ct₂ lt₂ := by
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h₁
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := h₂
  exact ⟨⟨a ++ a', by simp⟩, ⟨b ++ b', by simp⟩, ⟨c ++ c', by simp⟩⟩

theorem tyOf_grow {tt tt' : List (Nat × Nat)} (hw : TTWF tt) (he : ∃ e, tt' = tt ++ e) {i : Nat} {τ : HO.Ty}
    (h : tyOf tt i = some τ) : tyOf tt' i = some τ := by
  rw [tyOf_extend hw he (tyOf_le h), h]

theorem ctxOf_grow {tt ct tt' ct' : List (Nat × Nat)} (hw : TTWF tt) (hc : CTWF tt ct) (het : ∃ e, tt' = tt ++ e)
    (hec : ∃ e, ct' = ct ++ e) {c : Nat} {Γ : List HO.Ty} (h : ctxOf tt ct c = some Γ) : ctxOf tt' ct' c = some Γ := by
  rw [ctxOf_extend hw hc het hec c (ctxOf_le h), h]

theorem litOf_grow {lt lt' : List (List Nat)} (he : ∃ e, lt' = lt ++ e) {i : Nat} {str : List Char}
    (h : litOf lt i = some str) : litOf lt' i = some str := by
  obtain ⟨e, rfl⟩ := he
  unfold litOf at *
  cases hi : lt[i]? with
  | none => rw [hi] at h; cases h
  | some v =>
    rw [hi] at h
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hi).1, hi]; exact h

theorem itemOf_grow {tt ct tt' ct' : List (Nat × Nat)} {lt lt' : List (List Nat)} (hw : TTWF tt) (hc : CTWF tt ct)
    (hg : Grows tt ct lt tt' ct' lt') {it : MItem} {i : Item} (h : itemOf tt ct lt it = some i) :
    itemOf tt' ct' lt' it = some i := by
  unfold itemOf at *
  split at h
  · rename_i op Γ hop hΓ
    rw [ctxOf_grow hw hc hg.tt hg.ct hΓ]
    have hop' : opOf tt' lt' it = some op := by
      unfold opOf at *
      split at hop <;> first
        | exact hop
        | (simp only [Option.map_eq_some_iff] at hop ⊢
           obtain ⟨str, hs, rfl⟩ := hop
           exact ⟨str, litOf_grow hg.lt hs, rfl⟩)
        | (split at hop
           · rename_i a b ha hb
             rw [tyOf_grow hw hg.tt ha, tyOf_grow hw hg.tt hb]; exact hop
           · cases hop)
    rw [hop']; exact h
  · cases h

theorem itemsOf_grow {tt ct tt' ct' : List (Nat × Nat)} {lt lt' : List (List Nat)} (hw : TTWF tt) (hc : CTWF tt ct)
    (hg : Grows tt ct lt tt' ct' lt') : ∀ {l : List MItem} {is : List Item}, itemsOf tt ct lt l = some is →
      itemsOf tt' ct' lt' l = some is
  | [], _, h => h
  | it :: l, is, h => by
    unfold itemsOf at *
    rw [List.mapM_cons] at h ⊢
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨i, hi, is', his, rfl⟩ := h
    rw [itemOf_grow hw hc hg hi]
    have := itemsOf_grow hw hc hg (l := l) his
    unfold itemsOf at this
    simp [this]

end Shallot.MacroPeg.Mach
