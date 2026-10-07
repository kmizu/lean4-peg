import Cfg.Greibach.StdDrives

/-!
# The encoding homomorphism and its blocks (for `greibach_std`)

Following Nipkow's `xihat` and `enc_h`: `ξ̂(p)` is `ξ(p)` with `¢ pushcode(S)` prepended for the productions of the
start `S`, and `h(a) = c ξ̂(p₁) c … c ξ̂(pₘ) c d` over the productions `pᵢ` whose right side starts with `a`.

- `enc_block`, `block_decomp`: `h(w)` is a concatenation of blocks whose middles are any chosen `ξ̂`-codes.
- `blocks_align`, `block_parse`, `blocks_to_ps`: conversely, block words with `c`-free middles that spell `h(w)`
  have the `ξ̂`-codes of a production list matching `w` as middles.
-/

namespace Shallot.Cfg
namespace GStd

/-- `ξ̂(p)`: for the start's productions, `¢ pushcode(S) ξ(p)`; otherwise `ξ(p)`. -/
def xihat (S : Nat) (p : GProd) : List Char := if p.1 = S then '$' :: (pushcode S ++ xi p) else xi p

/-- The productions whose right side starts with `a`. -/
def prodsOf (P : List GProd) (a : Char) : List GProd := P.filter (fun p => p.2.1 == a)

/-- **The encoding homomorphism** on letters: `c ξ̂(p₁) c … c ξ̂(pₘ) c d`. -/
def encH (S : Nat) (P : List GProd) (a : Char) : List Char :=
  ((prodsOf P a).map (fun p => 'c' :: xihat S p)).flatten ++ ['c', 'd']

/-! ## Letters of the codes -/

/-- The push code is brackets. -/
theorem pushcode_bracket (i : Nat) : ∀ c ∈ pushcode i, isBracket c = true := by
  intro c hc
  simp only [pushcode, List.mem_cons, List.mem_append, List.mem_replicate] at hc
  rcases hc with h | ⟨_, h⟩ | h | h
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · cases h

/-- The pop code is brackets. -/
theorem popcode_bracket (i : Nat) : ∀ c ∈ popcode i, isBracket c = true := by
  intro c hc
  simp only [popcode, List.mem_cons, List.mem_append, List.mem_replicate] at hc
  rcases hc with h | ⟨_, h⟩ | h | h
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · cases h

/-- `ξ(p)` is brackets. -/
theorem xi_bracket (p : GProd) : ∀ c ∈ xi p, isBracket c = true := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact popcode_bracket _ c h
  · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp h
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hl
    subst hi
    exact pushcode_bracket i c hcl

/-- `ξ̂(p)` is brackets and `¢`. -/
theorem xihat_chars (S : Nat) (p : GProd) : ∀ c ∈ xihat S p, c = '$' ∨ isBracket c = true := by
  intro c hc
  unfold xihat at hc
  split at hc
  · rcases List.mem_cons.mp hc with h | h
    · exact Or.inl h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (pushcode_bracket _ c h)
      · exact Or.inr (xi_bracket _ c h)
  · exact Or.inr (xi_bracket _ c hc)

/-- Brackets and `¢` are in `T`. -/
theorem isT_of_chars {c : Char} (h : c = '$' ∨ isBracket c = true) : isT c = true := by
  rcases h with h | h
  · subst h; rfl
  · simp [isT, h]

/-- Brackets and `¢` are not `c`. -/
theorem ne_c_of_chars {c : Char} (h : c = '$' ∨ isBracket c = true) : c ≠ 'c' := by
  rintro rfl
  rcases h with h | h
  · cases h
  · cases h

/-- Brackets and `¢` are not `d`. -/
theorem ne_d_of_chars {c : Char} (h : c = '$' ∨ isBracket c = true) : c ≠ 'd' := by
  rintro rfl
  rcases h with h | h
  · cases h
  · cases h

/-- Letters of `T` are not `d`. -/
theorem ne_d_of_isT {c : Char} (h : isT c = true) : c ≠ 'd' := by
  rintro rfl; cases h

/-! ## Blocks of the encoding -/

/-- Peeling the leading `c` off a `c d`-terminated block body. -/
theorem cc_shift (f : GProd → List Char) (qs : List GProd) :
    (qs.map (fun q => 'c' :: f q)).flatten ++ ['c', 'd'] = 'c' :: ((qs.map (fun q => f q ++ ['c'])).flatten ++ ['d']) := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [List.map_cons, List.flatten_cons, List.append_assoc, ih]; simp

/-- Letters of `c`-prefixed `ξ̂`-codes are in `T`. -/
theorem flatten_c_xihat_isT (S : Nat) (qs : List GProd) :
    ∀ c ∈ (qs.map (fun q => 'c' :: xihat S q)).flatten, isT c = true := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hl
  subst hq
  rcases List.mem_cons.mp hcl with h | h
  · subst h; rfl
  · exact isT_of_chars (xihat_chars S q c h)

/-- Letters of `c`-suffixed `ξ̂`-codes are in `T`. -/
theorem flatten_xihat_c_isT (S : Nat) (qs : List GProd) :
    ∀ c ∈ (qs.map (fun q => xihat S q ++ ['c'])).flatten, isT c = true := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
  obtain ⟨q, _, hq⟩ := List.mem_map.mp hl
  subst hq
  rcases List.mem_append.mp hcl with h | h
  · exact isT_of_chars (xihat_chars S q c h)
  · simp at h; subst h; rfl

/-- One block: any production for `a` can be selected as the middle. -/
theorem enc_block (S : Nat) {P : List GProd} {p : GProd} (hp : p ∈ P) :
    ∃ x z, encH S P p.2.1 = blk (x, xihat S p, z) ∧ (∀ c ∈ x, isT c = true) ∧ (∀ c ∈ z, isT c = true) := by
  have hm : p ∈ prodsOf P p.2.1 := List.mem_filter.mpr ⟨hp, by simp⟩
  obtain ⟨qs1, qs2, hsplit⟩ := List.append_of_mem hm
  refine ⟨(qs1.map (fun q => 'c' :: xihat S q)).flatten, (qs2.map (fun q => xihat S q ++ ['c'])).flatten,
    ?_, flatten_c_xihat_isT S qs1, flatten_xihat_c_isT S qs2⟩
  rw [encH, hsplit, List.map_append, List.flatten_append, List.append_assoc, List.map_cons, List.flatten_cons,
    List.append_assoc, cc_shift]
  simp [blk]

/-- **Block decomposition**: `h(w)` for the letters of a production list is a block word with their `ξ̂`-codes as
middles. -/
theorem block_decomp (S : Nat) (P : List GProd) : ∀ (ps : List GProd), (∀ p ∈ ps, p ∈ P) →
    ∃ bs : List (List Char × List Char × List Char),
      ((ps.map (·.2.1)).map (encH S P)).flatten = (bs.map blk).flatten ∧
      bs.map (fun b => b.2.1) = ps.map (xihat S) ∧
      ∀ b ∈ bs, (∀ c ∈ b.1, isT c = true) ∧ (∀ c ∈ b.2.2, isT c = true)
  | [], _ => ⟨[], rfl, rfl, fun b hb => by cases hb⟩
  | p :: ps, hP => by
    obtain ⟨x, z, he, hx, hz⟩ := enc_block S (hP p List.mem_cons_self)
    obtain ⟨bs, h1, h2, h3⟩ := block_decomp S P ps (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    refine ⟨(x, xihat S p, z) :: bs, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, he, h1]
    · simp [h2]
    · intro b hb
      rcases List.mem_cons.mp hb with h | h
      · subst h; exact ⟨hx, hz⟩
      · exact h3 b h

/-! ## Parsing block words back -/

/-- A separator-free prefix before a separator is unique. -/
theorem prefix_unique {s : Char} : ∀ {y y' z z' : List Char}, s ∉ y → s ∉ y' →
    y ++ s :: z = y' ++ s :: z' → y = y' ∧ z = z'
  | [], [], z, z', _, _, h => by simpa using h
  | [], c :: y', z, z', _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | c :: y, [], z, z', hy, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hy
  | c :: y, c' :: y', z, z', hy, hy', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hc, h⟩ := h
    have := prefix_unique (fun hm => hy (List.mem_cons_of_mem _ hm)) (fun hm => hy' (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [hc, this.1], this.2⟩

/-- Two lists of `s`-terminated, otherwise `s`-free words with the same concatenation are equal. -/
theorem blocks_align {s : Char} : ∀ {xss yss : List (List Char)}, xss.flatten = yss.flatten →
    (∀ xs ∈ xss, ∃ p, xs = p ++ [s] ∧ s ∉ p) → (∀ ys ∈ yss, ∃ p, ys = p ++ [s] ∧ s ∉ p) → xss = yss
  | [], [], _, _, _ => rfl
  | [], ys :: yss, h, _, hy => by
    obtain ⟨p, hp, _⟩ := hy ys List.mem_cons_self
    subst hp
    simp at h
  | xs :: xss, [], h, hx, _ => by
    obtain ⟨p, hp, _⟩ := hx xs List.mem_cons_self
    subst hp
    simp at h
  | xs :: xss, ys :: yss, h, hx, hy => by
    obtain ⟨p, hp, hps⟩ := hx xs List.mem_cons_self
    obtain ⟨q, hq, hqs⟩ := hy ys List.mem_cons_self
    subst hp; subst hq
    simp only [List.flatten_cons, List.append_assoc, List.singleton_append] at h
    obtain ⟨h1, h2⟩ := prefix_unique hps hqs h
    rw [h1, blocks_align h2 (fun x hm => hx x (List.mem_cons_of_mem _ hm))
      (fun y hm => hy y (List.mem_cons_of_mem _ hm))]

/-- A `c`-free middle delimited by two `c`s in a `c`-separated body is one of the fragments. -/
theorem cfrag_parse {c : Char} {f : GProd → List Char} (hf : ∀ q, c ∉ f q) {y : List Char} (hy : c ∉ y) :
    ∀ (qs : List GProd) (x z : List Char),
      x ++ c :: (y ++ c :: z) = (qs.map (fun q => c :: f q)).flatten ++ [c] → ∃ q ∈ qs, y = f q
  | [], x, z, h => by
    have := congrArg List.length h
    simp at this; omega
  | q :: qs, x, z, h => by
    have hrest : ∃ r, (qs.map (fun q => c :: f q)).flatten ++ [c] = c :: r := by
      cases qs with
      | nil => exact ⟨[], rfl⟩
      | cons q' qs' => exact ⟨f q' ++ ((qs'.map (fun q => c :: f q)).flatten ++ [c]), by simp⟩
    obtain ⟨r, hr⟩ := hrest
    have h : x ++ c :: (y ++ c :: z) = c :: (f q ++ c :: r) := by
      rw [h, ← hr]; simp
    cases x with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, true_and] at h
      exact ⟨q, List.mem_cons_self, (prefix_unique hy (hf q) h).1⟩
    | cons x0 x' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨_, h⟩ := h
      rw [← hr] at h
      rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
      · cases a' with
        | nil =>
          simp only [List.nil_append] at h2
          obtain ⟨q', hq', hy'⟩ := cfrag_parse hf hy qs [] z (by simpa using h2)
          exact ⟨q', List.mem_cons_of_mem _ hq', hy'⟩
        | cons a0 a'' =>
          simp only [List.cons_append, List.cons.injEq] at h2
          exact absurd (h1 ▸ List.mem_append_right x' (h2.1 ▸ List.mem_cons_self)) (hf q)
      · obtain ⟨q', hq', hy'⟩ := cfrag_parse hf hy qs c' z h2.symm
        exact ⟨q', List.mem_cons_of_mem _ hq', hy'⟩

/-- `ξ̂`-codes are `c`-free. -/
theorem xihat_no_c (S : Nat) (q : GProd) : 'c' ∉ xihat S q := fun h => ne_c_of_chars (xihat_chars S q _ h) rfl

/-- **Inverting one block**: a block equal to `h(a)` with a `c`-free middle has the `ξ̂`-code of a production for
`a` as middle. -/
theorem block_parse (S : Nat) (P : List GProd) {a : Char} {b : List Char × List Char × List Char}
    (he : blk b = encH S P a) (hy : 'c' ∉ b.2.1) : ∃ p ∈ P, p.2.1 = a ∧ b.2.1 = xihat S p := by
  obtain ⟨x, y, z⟩ := b
  have he' : (x ++ 'c' :: (y ++ 'c' :: z)) ++ ['d'] =
      ((prodsOf P a).map (fun p => 'c' :: xihat S p)).flatten ++ ['c'] ++ ['d'] := by
    rw [encH] at he; simpa [blk] using he
  have h := List.append_cancel_right he'
  obtain ⟨q, hq, hyq⟩ := cfrag_parse (xihat_no_c S) hy _ x z h
  obtain ⟨hqP, hqa⟩ := List.mem_filter.mp hq
  exact ⟨q, hqP, by simpa using hqa, hyq⟩

/-- **Inverting a block word**: blocks with `c`-free middles spelling the letters' blocks yield a production list
matching the word, with the `ξ̂`-codes as middles. -/
theorem blocks_to_ps (S : Nat) (P : List GProd) : ∀ (w : List Char) (bs : List (List Char × List Char × List Char)),
    bs.map blk = w.map (encH S P) → (∀ b ∈ bs, 'c' ∉ b.2.1) →
    ∃ ps : List GProd, ps.map (·.2.1) = w ∧ (∀ p ∈ ps, p ∈ P) ∧ bs.map (fun b => b.2.1) = ps.map (xihat S)
  | [], [], _, _ => ⟨[], rfl, (fun p hp => by cases hp), rfl⟩
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: w, b :: bs, h, hc => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨p, hpP, hpa, hpy⟩ := block_parse S P h.1 (hc b List.mem_cons_self)
    obtain ⟨ps, h1, h2, h3⟩ := blocks_to_ps S P w bs h.2 (fun b' hb => hc b' (List.mem_cons_of_mem _ hb))
    refine ⟨p :: ps, by simp [h1, hpa], ?_, by simp [h3, hpy]⟩
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact hpP
    · exact h2 q hq

/-- Each letter's block ends in exactly one `d`. -/
theorem encH_d (S : Nat) (P : List GProd) (a : Char) : ∃ p, encH S P a = p ++ ['d'] ∧ 'd' ∉ p := by
  refine ⟨((prodsOf P a).map (fun p => 'c' :: xihat S p)).flatten ++ ['c'], by simp [encH], ?_⟩
  intro hd
  rcases List.mem_append.mp hd with h | h
  · exact ne_d_of_isT (flatten_c_xihat_isT S _ _ h) rfl
  · simp at h

end GStd
end Shallot.Cfg
