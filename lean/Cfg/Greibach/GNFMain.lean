import Cfg.Greibach.GNFCorner

/-!
# Greibach normal form, stage 4: the construction

For an `EpsFree`, `UnitFree`, `RefsInRange` grammar `G` with `n` nonterminals, `gnfG G` has the indices
- `E < n`: the old nonterminal `E`, with sides `a ⟦β⟧` (if `F = E`) and `a ⟦β⟧ ⟨E/F⟩` for each side
  `F → a β` of `G` (`eAlts`);
- `tIdx n A C = n + (n·A + C)`: `⟨A/C⟩`, the nonempty words `v` with `LeftCorner G A C v`, with sides
  `h ⟦γ⟧ t` for each side `D → C Y γ`, `h` a side of `Y` (`[c]` for a terminal, `eAlts E` for `E`), and
  `t` either empty (if `D = A`) or `⟨A/D⟩` (`tAlts`);
- `n + n·n`: the fresh start, with the sides of `eAlts G.start`;
- `termIdx n c = n + n·n + 1 + c.toNat`: the terminal `c`, with the single side `c`.

`⟦β⟧` (`tr`) replaces each terminal `c` by its nonterminal `termIdx n c`.

`Sem G` is the intended language of each index. This file proves the sides sound for `Sem G`
(`gnfG_sound`); `Cfg/Greibach/GNFComplete.lean` proves completeness and the shape.
-/

namespace Shallot.Cfg

/-! ## Indices -/

/-- The index of `⟨A/C⟩`. -/
def tIdx (n A C : Nat) : Nat := n + (n * A + C)

/-- The fresh start index. -/
def sIdx (n : Nat) : Nat := n + n * n

/-- The index of the terminal `c`. -/
def termIdx (n : Nat) (c : Char) : Nat := n + n * n + 1 + c.toNat

/-- The number of indices of the new grammar. -/
@[irreducible] def gnfBound (n : Nat) : Nat := n + n * n + 1 + 0x110000

/-- `⟨A/C⟩` lies in its block. -/
theorem tIdx_bounds {n A C : Nat} (hA : A < n) (hC : C < n) : n ≤ tIdx n A C ∧ tIdx n A C < n + n * n := by
  have : n * (A + 1) ≤ n * n := Nat.mul_le_mul_left n hA
  rw [Nat.mul_add, Nat.mul_one] at this
  unfold tIdx; omega

/-- Decoding `⟨A/C⟩`. -/
theorem tIdx_decode {n A C : Nat} (hC : C < n) :
    (tIdx n A C - n) / n = A ∧ (tIdx n A C - n) % n = C := by
  have hn : n > 0 := by omega
  have h : tIdx n A C - n = n * A + C := by unfold tIdx; omega
  rw [h, Nat.mul_add_div hn, Nat.mul_add_mod, Nat.div_eq_of_lt hC, Nat.mod_eq_of_lt hC]
  exact ⟨rfl, rfl⟩

/-- Every index of the `⟨A/C⟩` block is some `⟨A/C⟩` with `A, C < n`. -/
theorem tIdx_encode {n i : Nat} (h₁ : n ≤ i) (h₂ : i < n + n * n) :
    (i - n) / n < n ∧ (i - n) % n < n ∧ i = tIdx n ((i - n) / n) ((i - n) % n) := by
  have hn : 0 < n := by
    cases n with
    | zero => simp at h₂
    | succ k => omega
  refine ⟨(Nat.div_lt_iff_lt_mul hn).mpr (by omega), Nat.mod_lt _ hn, ?_⟩
  have := Nat.div_add_mod (i - n) n
  unfold tIdx; omega

/-- A terminal index lies above the fresh start and below the bound. -/
theorem termIdx_bounds (n : Nat) (c : Char) :
    sIdx n < termIdx n c ∧ termIdx n c < gnfBound n := by
  have := char_toNat_lt c
  unfold sIdx termIdx gnfBound; omega

/-- Decoding a terminal index. -/
theorem termIdx_decode (n : Nat) (c : Char) : Char.ofNat (termIdx n c - (n + n * n + 1)) = c := by
  have : termIdx n c - (n + n * n + 1) = c.toNat := by unfold termIdx; omega
  rw [this, Char.ofNat_toNat]

/-! ## The construction -/

/-- `⟦s⟧`: terminals become their nonterminals. -/
def trSym (n : Nat) : Sym → Sym
  | .t c => .nt (termIdx n c)
  | .nt j => .nt j

/-- `⟦β⟧`. -/
def tr (n : Nat) (β : List Sym) : List Sym := β.map (trSym n)

/-- The sides of `E` contributed by a side of `F`. -/
def eRule (n E F : Nat) : Rhs → List Rhs
  | .t a :: β => (if F = E then [.t a :: tr n β] else []) ++ [.t a :: (tr n β ++ [.nt (tIdx n E F)])]
  | _ => []

/-- The sides of an old nonterminal `E`. -/
def eAlts (G : CFGrammar) (E : Nat) : List Rhs :=
  if E < G.rules.length then
    (List.range G.rules.length).flatMap fun F => (altsOf G F).flatMap (eRule G.rules.length E F)
  else []

/-- The Greibach sides of a symbol. -/
def heads (G : CFGrammar) : Sym → List Rhs
  | .t c => [[.t c]]
  | .nt E => eAlts G E

/-- The possible tails `t` of a side of `⟨A/C⟩` from a side of `D`. -/
def tails (n A D : Nat) : List Rhs := (if D = A then [[]] else []) ++ [[.nt (tIdx n A D)]]

/-- The sides of `⟨A/C⟩` contributed by a side of `D`. -/
def tRule (G : CFGrammar) (A C D : Nat) : Rhs → List Rhs
  | .nt C' :: Y :: γ =>
      if C' = C then
        (heads G Y).flatMap fun h => (tails G.rules.length A D).map fun t => h ++ tr G.rules.length γ ++ t
      else []
  | _ => []

/-- The sides of `⟨A/C⟩`. -/
def tAlts (G : CFGrammar) (A C : Nat) : List Rhs :=
  (List.range G.rules.length).flatMap fun D => (altsOf G D).flatMap (tRule G A C D)

/-- The sides of every index of the new grammar. -/
def gnfAlts (G : CFGrammar) (i : Nat) : List Rhs :=
  let n := G.rules.length
  if i < n then eAlts G i
  else if i < n + n * n then tAlts G ((i - n) / n) ((i - n) % n)
  else if i = n + n * n then eAlts G G.start
  else [[.t (Char.ofNat (i - (n + n * n + 1)))]]

/-- **The Greibach grammar**, with the fresh start `sIdx n`. -/
def gnfG (G : CFGrammar) : CFGrammar :=
  ⟨(List.range (gnfBound G.rules.length)).map (gnfAlts G), sIdx G.rules.length⟩

/-- The intended language of every index. -/
def Sem (G : CFGrammar) (i : Nat) (w : List Char) : Prop :=
  let n := G.rules.length
  if i < n then Gen G i w
  else if i < n + n * n then LeftCorner G ((i - n) / n) ((i - n) % n) w ∧ w ≠ []
  else if i = n + n * n then Gen G G.start w
  else w = [Char.ofNat (i - (n + n * n + 1))]

/-! ## Reading the indices -/

/-- `Sem` at an old nonterminal. -/
theorem sem_lt {G : CFGrammar} {j : Nat} (h : j < G.rules.length) (x : List Char) :
    Sem G j x ↔ Gen G j x := by
  simp only [Sem, if_pos h]

/-- `Sem` at `⟨A/C⟩`. -/
theorem sem_tIdx {G : CFGrammar} {A C : Nat} (hA : A < G.rules.length) (hC : C < G.rules.length)
    (x : List Char) : Sem G (tIdx G.rules.length A C) x ↔ LeftCorner G A C x ∧ x ≠ [] := by
  obtain ⟨h₁, h₂⟩ := tIdx_bounds hA hC
  obtain ⟨d₁, d₂⟩ := tIdx_decode (A := A) hC
  simp only [Sem, if_neg (show ¬ tIdx G.rules.length A C < G.rules.length by omega), if_pos h₂, d₁, d₂]

/-- `Sem` at the fresh start. -/
theorem sem_sIdx (G : CFGrammar) (x : List Char) : Sem G (sIdx G.rules.length) x ↔ Gen G G.start x := by
  simp only [Sem, sIdx]
  rw [if_neg (by omega), if_neg (by omega), if_pos trivial]

/-- `Sem` at a terminal index. -/
theorem sem_termIdx (G : CFGrammar) (c : Char) (x : List Char) :
    Sem G (termIdx G.rules.length c) x ↔ x = [c] := by
  have := (termIdx_bounds G.rules.length c).1
  unfold sIdx at this
  simp only [Sem]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), termIdx_decode]

/-- The alternatives of `gnfG G`. -/
theorem altsAt_gnfG (G : CFGrammar) (i : Nat) :
    altsAt (gnfG G).rules i = if i < gnfBound G.rules.length then some (gnfAlts G i) else none := by
  simp only [gnfG]
  exact altsAt_range_map (gnfAlts G) (gnfBound G.rules.length) i

/-- `gnfAlts` at an old nonterminal. -/
theorem gnfAlts_lt {G : CFGrammar} {j : Nat} (h : j < G.rules.length) : gnfAlts G j = eAlts G j := by
  simp only [gnfAlts, if_pos h]

/-- `gnfAlts` at `⟨A/C⟩`. -/
theorem gnfAlts_tIdx {G : CFGrammar} {A C : Nat} (hA : A < G.rules.length) (hC : C < G.rules.length) :
    gnfAlts G (tIdx G.rules.length A C) = tAlts G A C := by
  obtain ⟨h₁, h₂⟩ := tIdx_bounds hA hC
  obtain ⟨d₁, d₂⟩ := tIdx_decode (A := A) hC
  simp only [gnfAlts, if_neg (show ¬ tIdx G.rules.length A C < G.rules.length by omega), if_pos h₂, d₁, d₂]

/-- `gnfAlts` at the fresh start. -/
theorem gnfAlts_sIdx (G : CFGrammar) : gnfAlts G (sIdx G.rules.length) = eAlts G G.start := by
  simp only [gnfAlts, sIdx]
  rw [if_neg (by omega), if_neg (by omega), if_pos trivial]

/-- `gnfAlts` at a terminal index. -/
theorem gnfAlts_termIdx (G : CFGrammar) (c : Char) :
    gnfAlts G (termIdx G.rules.length c) = [[.t c]] := by
  have := (termIdx_bounds G.rules.length c).1
  unfold sIdx at this
  simp only [gnfAlts]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), termIdx_decode]

/-! ## Members of the side lists -/

/-- A member of `eAlts`. -/
theorem mem_eAlts {G : CFGrammar} {E : Nat} {rhs : Rhs} :
    rhs ∈ eAlts G E ↔ E < G.rules.length ∧ ∃ F r, F < G.rules.length ∧ r ∈ altsOf G F ∧
      rhs ∈ eRule G.rules.length E F r := by
  unfold eAlts
  split
  · rename_i hE
    simp only [List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨F, hF, r, hr, hm⟩; exact ⟨hE, F, r, hF, hr, hm⟩
    · rintro ⟨_, F, r, hF, hr, hm⟩; exact ⟨F, hF, r, hr, hm⟩
  · rename_i hE
    simp only [List.not_mem_nil, false_iff, not_and]
    intro h; exact absurd h hE

/-- A member of `eRule`. -/
theorem mem_eRule {n E F : Nat} {r rhs : Rhs} (h : rhs ∈ eRule n E F r) :
    ∃ a β, r = .t a :: β ∧ ((F = E ∧ rhs = .t a :: tr n β) ∨ rhs = .t a :: (tr n β ++ [.nt (tIdx n E F)])) := by
  match r, h with
  | .t a :: β, h =>
      simp only [eRule, List.mem_append, List.mem_singleton] at h
      refine ⟨a, β, rfl, ?_⟩
      rcases h with h | h
      · split at h
        · rename_i hF; exact Or.inl ⟨hF, List.mem_singleton.mp h⟩
        · exact absurd h List.not_mem_nil
      · exact Or.inr h

/-- A member of `tAlts`. -/
theorem mem_tAlts {G : CFGrammar} {A C : Nat} {rhs : Rhs} :
    rhs ∈ tAlts G A C ↔ ∃ D r, D < G.rules.length ∧ r ∈ altsOf G D ∧ rhs ∈ tRule G A C D r := by
  simp only [tAlts, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨D, hD, r, hr, hm⟩; exact ⟨D, r, hD, hr, hm⟩
  · rintro ⟨D, r, hD, hr, hm⟩; exact ⟨D, hD, r, hr, hm⟩

/-- A member of `tRule`. -/
theorem mem_tRule {G : CFGrammar} {A C D : Nat} {r rhs : Rhs} :
    rhs ∈ tRule G A C D r ↔ ∃ Y γ h t, r = .nt C :: Y :: γ ∧ h ∈ heads G Y ∧ t ∈ tails G.rules.length A D ∧
      rhs = h ++ tr G.rules.length γ ++ t := by
  constructor
  · intro hm
    match r, hm with
    | .nt C' :: Y :: γ, hm' =>
        clear hm
        have hm := hm'
        clear hm'
        simp only [tRule] at hm
        split at hm
        · rename_i hC
          subst hC
          simp only [List.mem_flatMap, List.mem_map] at hm
          obtain ⟨h, hh, t, ht, rfl⟩ := hm
          exact ⟨Y, γ, h, t, rfl, hh, ht, rfl⟩
        · exact absurd hm List.not_mem_nil
  · rintro ⟨Y, γ, h, t, rfl, hh, ht, rfl⟩
    simp only [tRule, ↓reduceIte, List.mem_flatMap, List.mem_map]
    exact ⟨h, hh, t, ht, rfl⟩

/-- A member of `tails`. -/
theorem mem_tails {n A D : Nat} {t : Rhs} : t ∈ tails n A D ↔ (D = A ∧ t = []) ∨ t = [.nt (tIdx n A D)] := by
  simp only [tails, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h)
    · split at h
      · rename_i hD; exact Or.inl ⟨hD, List.mem_singleton.mp h⟩
      · exact absurd h List.not_mem_nil
    · exact Or.inr h
  · rintro (⟨hD, rfl⟩ | h)
    · exact Or.inl (by rw [if_pos hD]; exact List.mem_singleton_self _)
    · exact Or.inr h

/-! ## Soundness -/

/-- The right sides of `G` reference only old nonterminals. -/
theorem refs_of_mem_altsOf {G : CFGrammar} (hR : RefsInRange G) {i : Nat} {r : Rhs} (h : r ∈ altsOf G i) :
    ∀ j, Sym.nt j ∈ r → j < G.rules.length := by
  obtain ⟨a, ha, hra⟩ := mem_rules_of_mem_altsOf h
  exact hR a ha r hra

/-- Reading `⟦β⟧` under `Sem G` is reading `β` under `Gen G`. -/
theorem semRhs_of_tr {G : CFGrammar} :
    ∀ (β : List Sym), (∀ j, Sym.nt j ∈ β → j < G.rules.length) → ∀ (u : List Char),
      SemRhs (Sem G) (tr G.rules.length β) u → SemRhs (Gen G) β u
  | [], _, _, h => h
  | .t c :: β, hβ, _, h => by
      obtain ⟨x, y, rfl, hx, hy⟩ := h
      rw [sem_termIdx] at hx; subst hx
      exact ⟨y, rfl, semRhs_of_tr β (fun j hj => hβ j (List.mem_cons_of_mem _ hj)) y hy⟩
  | .nt j :: β, hβ, _, h => by
      obtain ⟨x, y, rfl, hx, hy⟩ := h
      rw [sem_lt (hβ j List.mem_cons_self)] at hx
      exact ⟨x, y, rfl, hx, semRhs_of_tr β (fun k hk => hβ k (List.mem_cons_of_mem _ hk)) y hy⟩

/-- The sides of `eAlts G E` are sound: they yield words of `E`. -/
theorem eAlts_sound {G : CFGrammar} (hR : RefsInRange G) {E : Nat} {rhs : Rhs} (hm : rhs ∈ eAlts G E)
    {w : List Char} (hw : SemRhs (Sem G) rhs w) : Gen G E w := by
  obtain ⟨hE, F, r, hF, hr, hrule⟩ := mem_eAlts.mp hm
  obtain ⟨a, β, rfl, hcase⟩ := mem_eRule hrule
  have hβ : ∀ j, Sym.nt j ∈ β → j < G.rules.length :=
    fun j hj => refs_of_mem_altsOf hR hr j (List.mem_cons_of_mem _ hj)
  rcases hcase with ⟨rfl, rfl⟩ | rfl
  · obtain ⟨w', rfl, hw'⟩ := hw
    exact gen_of_altsOf hr ⟨w', rfl, semRhs_of_tr β hβ w' hw'⟩
  · obtain ⟨w', rfl, hw'⟩ := hw
    obtain ⟨u, v, rfl, hu, hv⟩ := (semRhs_append _ _ _ _).mp hw'
    rw [semRhs_single_nt, sem_tIdx hE hF] at hv
    have := gen_of_leftCorner hv.1 (gen_of_altsOf hr ⟨u, rfl, semRhs_of_tr β hβ u hu⟩)
    rw [List.cons_append] at this
    exact this

/-- Every index's words are nonempty under `Sem`, for an `EpsFree` grammar. -/
theorem sem_ne_nil {G : CFGrammar} (hε : EpsFree G) {i : Nat} {w : List Char} (h : Sem G i w) : w ≠ [] := by
  simp only [Sem] at h
  split at h
  · exact gen_ne_nil hε h
  · split at h
    · exact h.2
    · split at h
      · exact gen_ne_nil hε h
      · subst h; exact List.cons_ne_nil _ _

/-- The sides of `tAlts G A C` are sound: they yield nonempty left-corner words. -/
theorem tAlts_sound {G : CFGrammar} (hε : EpsFree G) (hR : RefsInRange G) {A C : Nat}
    (hA : A < G.rules.length) {rhs : Rhs} (hm : rhs ∈ tAlts G A C) {w : List Char}
    (hw : SemRhs (Sem G) rhs w) : LeftCorner G A C w ∧ w ≠ [] := by
  obtain ⟨D, r, hD, hr, hrule⟩ := mem_tAlts.mp hm
  obtain ⟨Y, γ, h, t, rfl, hh, ht, rfl⟩ := mem_tRule.mp hrule
  have hγ : ∀ j, Sym.nt j ∈ γ → j < G.rules.length :=
    fun j hj => refs_of_mem_altsOf hR hr j (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hj))
  obtain ⟨xy, z, rfl, hxy, hz⟩ := (semRhs_append _ _ _ _).mp hw
  obtain ⟨x, y, rfl, hx, hy⟩ := (semRhs_append _ _ _ _).mp hxy
  have hyG := semRhs_of_tr γ hγ y hy
  have hYγ : SemRhs (Gen G) (Y :: γ) (x ++ y) ∧ x ≠ [] := by
    cases Y with
    | t c =>
        simp only [heads, List.mem_singleton] at hh; subst hh
        obtain ⟨x', rfl, hx'⟩ := hx
        cases hx'
        exact ⟨⟨y, rfl, hyG⟩, List.cons_ne_nil _ _⟩
    | nt E =>
        have hE := eAlts_sound hR hh hx
        exact ⟨⟨x, y, rfl, hE, hyG⟩, gen_ne_nil hε hE⟩
  have hzc : LeftCorner G A D z := by
    rcases mem_tails.mp ht with ⟨rfl, rfl⟩ | rfl
    · cases hz; exact .refl
    · rw [semRhs_single_nt, sem_tIdx hA hD] at hz; exact hz.1
  refine ⟨LeftCorner.step hr hYγ.1 hzc, ?_⟩
  intro he
  exact hYγ.2 (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp he).1).1

/-- **Soundness**: every word of an index of `gnfG G` is in its intended language. -/
theorem gnfG_sound {G : CFGrammar} (hε : EpsFree G) (hR : RefsInRange G) {i : Nat} {w : List Char}
    (h : Gen (gnfG G) i w) : Sem G i w := by
  refine gen_sound (g := gnfG G) (Sem G) (fun i alts rhs w halts hmem hr => ?_) h
  rw [altsAt_gnfG] at halts
  split at halts
  · cases halts
    by_cases h₁ : i < G.rules.length
    · rw [gnfAlts_lt h₁] at hmem
      rw [sem_lt h₁]; exact eAlts_sound hR hmem hr
    · by_cases h₂ : i < G.rules.length + G.rules.length * G.rules.length
      · obtain ⟨hA, hC, hi⟩ := tIdx_encode (Nat.le_of_not_lt h₁) h₂
        rw [hi] at hmem ⊢
        rw [gnfAlts_tIdx hA hC] at hmem
        rw [sem_tIdx hA hC]
        exact tAlts_sound hε hR hA hmem hr
      · by_cases h₃ : i = G.rules.length + G.rules.length * G.rules.length
        · have hi : i = sIdx G.rules.length := h₃
          rw [hi] at hmem ⊢
          rw [gnfAlts_sIdx] at hmem
          rw [sem_sIdx]; exact eAlts_sound hR hmem hr
        · simp only [gnfAlts, if_neg h₁, if_neg h₂, if_neg h₃, List.mem_singleton] at hmem
          subst hmem
          obtain ⟨w', rfl, hw'⟩ := hr
          cases hw'
          simp only [Sem, if_neg h₁, if_neg h₂, if_neg h₃]
  · cases halts

end Shallot.Cfg
