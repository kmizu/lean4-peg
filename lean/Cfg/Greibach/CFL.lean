import Cfg.Greibach.CFLYmid

/-!
# Greibach's hardest language is context-free

Following Nipkow's Isabelle formalization (AFP `Greibach_Hardest`, `theorem CFL_L0`; "this property
is left implicit in Greibach's paper"). The grammar is Nipkow's `G` with nonterminals
`NZ = 0`, `NF = 1`, `NM = 2`:

- `NZ → ε | NF c ¢ NM c NF d`
- `NF → ε | t NF` for every `t ∈ T`
- `NM → ε | NM NM | ( NM ) | [ NM ] | c NF d NF c`

`NF` generates `T*`, `NM` generates the middle language `Ymid` (`Cfg/Greibach/CFLYmid.lean`), and
`NZ` generates `L0`.

- Soundness (`l0_gen_sound`, Nipkow's `Lang_G_subset`): every generated word lies in the intended
  language `Rsol` of its nonterminal, by mutual induction on `Gen`/`GenRhs`.
- Completeness (`gen_NZ_of_L0`, Nipkow's `L0_subset_Lang`): via `Ymid_of_L0` and
  `gen_NM_of_spread` (Nipkow's `sprd_bal_imp_mbal` composed with `mbal_imp_Lang_NM`), by induction
  on the balanced word.
-/

namespace Shallot.Cfg

/-- The letters of Greibach's alphabet `T`, listed. -/
def tAlph : List Char := ['(', ')', '[', ']', 'c', '$']

/-- `isT` is membership in `tAlph`. -/
theorem isT_iff_mem {c : Char} : isT c = true ↔ c ∈ tAlph := by
  simp only [isT, isBracket, tAlph, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
    beq_iff_eq, or_assoc]

/-- **The grammar for `L0`** (Nipkow's `G`): nonterminals `NZ = 0` (start), `NF = 1`, `NM = 2`. -/
def l0Grammar : CFGrammar where
  rules := [
    [[], [.nt 1, .t 'c', .t '$', .nt 2, .t 'c', .nt 1, .t 'd']],
    [] :: tAlph.map (fun a => [.t a, .nt 1]),
    [[], [.nt 2, .nt 2], [.t '(', .nt 2, .t ')'], [.t '[', .nt 2, .t ']'],
      [.t 'c', .nt 1, .t 'd', .nt 1, .t 'c']]]
  start := 0

/-! ## Soundness -/

/-- **The intended languages** (Nipkow's `Rsol`): `L0` for `NZ`, `T*` for `NF`, `Ymid` for `NM`. -/
def Rsol : Nat → List Char → Prop
  | 0 => L0
  | 1 => TStar
  | 2 => Ymid
  | _ => fun _ => False

/-- A right side generates `w` when its nonterminals are read as their `Rsol` languages
(Nipkow's `inst_syms Rsol`). -/
def RsolRhs : List Sym → List Char → Prop
  | [], w => w = []
  | .t c :: rest, w => ∃ w', w = c :: w' ∧ RsolRhs rest w'
  | .nt j :: rest, w => ∃ w₁ w₂, w = w₁ ++ w₂ ∧ Rsol j w₁ ∧ RsolRhs rest w₂

/-- The `NZ` productions keep `Rsol` closed (Nipkow's `incl_NZ_big` and the `ε` case). -/
theorem rsol_NZ {rhs : List Sym} {w : List Char}
    (hmem : rhs ∈ [[], [.nt 1, .t 'c', .t '$', .nt 2, .t 'c', .nt 1, .t 'd']])
    (h : RsolRhs rhs w) : L0 w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact Or.inl h
  · simp only [RsolRhs, Rsol] at h
    obtain ⟨x, _, rfl, hx, _, rfl, _, rfl, W, _, rfl, hW, _, rfl, z, _, rfl, hz, _, rfl, rfl⟩ := h
    exact L0_of_Ymid hx hW hz

/-- The `NF` productions keep `Rsol` closed. -/
theorem rsol_NF {rhs : List Sym} {w : List Char}
    (hmem : rhs ∈ ([] :: tAlph.map (fun a => [.t a, .nt 1]) : List Rhs))
    (h : RsolRhs rhs w) : TStar w := by
  rcases List.mem_cons.mp hmem with rfl | hmem
  · simp only [RsolRhs] at h
    subst h
    exact TStar_nil
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    simp only [RsolRhs, Rsol] at h
    obtain ⟨_, rfl, w₁, _, rfl, hw₁, rfl⟩ := h
    intro c hc
    simp only [List.append_nil, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact isT_iff_mem.mpr ha
    · exact hw₁ c hc

/-- The `NM` productions keep `Rsol` closed (Nipkow's cases via `Ymid_Nil`, `Ymid_app`,
`Ymid_wrap`, `Ymid_gap`). -/
theorem rsol_NM {rhs : List Sym} {w : List Char}
    (hmem : rhs ∈ ([[], [.nt 2, .nt 2], [.t '(', .nt 2, .t ')'], [.t '[', .nt 2, .t ']'],
      [.t 'c', .nt 1, .t 'd', .nt 1, .t 'c']] : List Rhs))
    (h : RsolRhs rhs w) : Ymid w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · simp only [RsolRhs] at h
    subst h
    exact Ymid_nil
  · simp only [RsolRhs, Rsol] at h
    obtain ⟨w₁, _, rfl, h₁, w₂, _, rfl, h₂, rfl⟩ := h
    rw [List.append_nil]
    exact Ymid_append h₁ h₂
  · simp only [RsolRhs, Rsol] at h
    obtain ⟨_, rfl, W, _, rfl, hW, _, rfl, rfl⟩ := h
    exact Ymid_paren hW
  · simp only [RsolRhs, Rsol] at h
    obtain ⟨_, rfl, W, _, rfl, hW, _, rfl, rfl⟩ := h
    exact Ymid_brack hW
  · simp only [RsolRhs, Rsol] at h
    obtain ⟨_, rfl, z, _, rfl, hz, _, rfl, x, _, rfl, hx, _, rfl, rfl⟩ := h
    exact Ymid_gap ⟨z, x, hz, hx, rfl⟩

/-- Every production of `l0Grammar` keeps `Rsol` closed. -/
theorem rsol_closed {i : Nat} {alts : List Rhs} {rhs : List Sym} {w : List Char}
    (halts : altsAt l0Grammar.rules i = some alts) (hmem : rhs ∈ alts) (h : RsolRhs rhs w) :
    Rsol i w := by
  match i, halts with
  | 0, halts =>
      simp only [l0Grammar, altsAt, Option.some.injEq] at halts
      subst halts
      exact rsol_NZ hmem h
  | 1, halts =>
      simp only [l0Grammar, altsAt, Option.some.injEq] at halts
      subst halts
      exact rsol_NF hmem h
  | 2, halts =>
      simp only [l0Grammar, altsAt, Option.some.injEq] at halts
      subst halts
      exact rsol_NM hmem h
  | _ + 3, halts => simp [l0Grammar, altsAt] at halts

/-- **Soundness** (Nipkow's `Lang_G_subset`): every word generated by a nonterminal lies in its
intended language. Mutual induction on `Gen`/`GenRhs`. -/
theorem l0_gen_sound {i : Nat} {w : List Char} (h : Gen l0Grammar i w) : Rsol i w := by
  induction h using Gen.rec (motive_2 := fun rhs w _ => RsolRhs rhs w) with
  | prod i alts rhs w halts hmem _ ih => exact rsol_closed halts hmem ih
  | nil => rfl
  | cons_t c rest w _ ih => exact ⟨w, rfl, ih⟩
  | cons_nt j rest w₁ w₂ _ _ ih₁ ih₂ => exact ⟨w₁, w₂, rfl, ih₁, ih₂⟩

/-! ## Completeness -/

/-- `NF` generates every word of `T*` (Nipkow's `Talph_sub_Lang_NF`). -/
theorem gen_NF : ∀ {w : List Char}, TStar w → Gen l0Grammar 1 w
  | [], _ => Gen.prod 1 _ [] [] rfl (List.mem_cons_self ..) GenRhs.nil
  | a :: w, h => by
      have ha : a ∈ tAlph := isT_iff_mem.mp (h a (List.mem_cons_self ..))
      have hw : Gen l0Grammar 1 w := gen_NF (fun c hc => h c (List.mem_cons_of_mem _ hc))
      have hrhs : GenRhs l0Grammar [.t a, .nt 1] (a :: (w ++ [])) :=
        GenRhs.cons_t a _ _ (GenRhs.cons_nt 1 [] w [] hw GenRhs.nil)
      rw [List.append_nil] at hrhs
      exact Gen.prod 1 _ _ _ rfl
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) hrhs

/-- `NM` generates the empty word. -/
theorem gen_NM_nil : Gen l0Grammar 2 [] :=
  Gen.prod 2 _ [] [] rfl (by simp) GenRhs.nil

/-- `NM` generates concatenations (production `NM → NM NM`). -/
theorem gen_NM_append {u v : List Char} (hu : Gen l0Grammar 2 u) (hv : Gen l0Grammar 2 v) :
    Gen l0Grammar 2 (u ++ v) := by
  have hrhs : GenRhs l0Grammar [.nt 2, .nt 2] (u ++ (v ++ [])) :=
    GenRhs.cons_nt 2 _ u _ hu (GenRhs.cons_nt 2 [] v [] hv GenRhs.nil)
  rw [List.append_nil] at hrhs
  exact Gen.prod 2 _ _ _ rfl (by simp) hrhs

/-- `NM` generates every gap (production `NM → c NF d NF c`). -/
theorem gen_NM_gap {g : List Char} (hg : IsGap g) : Gen l0Grammar 2 g := by
  obtain ⟨z, x, hz, hx, rfl⟩ := hg
  have hrhs : GenRhs l0Grammar [.t 'c', .nt 1, .t 'd', .nt 1, .t 'c']
      ('c' :: (z ++ 'd' :: (x ++ ['c']))) :=
    GenRhs.cons_t _ _ _ (GenRhs.cons_nt 1 _ z _ (gen_NF hz) (GenRhs.cons_t _ _ _
      (GenRhs.cons_nt 1 _ x _ (gen_NF hx) (GenRhs.cons_t _ _ _ GenRhs.nil))))
  exact Gen.prod 2 _ _ _ rfl (by simp) hrhs

/-- `NM` generates every word spreading the empty bracket word (Nipkow's `sprd_emptybw` with
`mbal_imp_Lang_NM`). -/
theorem gen_NM_of_spread_nil {W v : List Char} (h : Spread W v) : v = [] → Gen l0Grammar 2 W := by
  induction h with
  | nil => intro _; exact gen_NM_nil
  | gap hg _ ih => intro hv; exact gen_NM_append (gen_NM_gap hg) (ih hv)
  | brk _ _ _ => intro hv; cases hv

/-- `NM` wraps a word between two words spreading `[]` in a bracket pair `o`…`c'`, given the
production `NM → o NM c'`. -/
theorem gen_NM_wrap {o c' : Char} {U₁ U₂ U₃ W₁ : List Char}
    (hp : [Sym.t o, .nt 2, .t c'] ∈ ([[], [.nt 2, .nt 2], [.t '(', .nt 2, .t ')'],
      [.t '[', .nt 2, .t ']'], [.t 'c', .nt 1, .t 'd', .nt 1, .t 'c']] : List Rhs))
    (h₁ : Gen l0Grammar 2 U₁) (hW : Gen l0Grammar 2 (W₁ ++ U₂)) (h₃ : Gen l0Grammar 2 U₃) :
    Gen l0Grammar 2 (U₁ ++ o :: (W₁ ++ (U₂ ++ c' :: U₃))) := by
  have hrhs : GenRhs l0Grammar [.t o, .nt 2, .t c'] (o :: ((W₁ ++ U₂) ++ [c'])) :=
    GenRhs.cons_t _ _ _ (GenRhs.cons_nt 2 _ _ _ hW (GenRhs.cons_t _ _ _ GenRhs.nil))
  have hmid : Gen l0Grammar 2 (o :: ((W₁ ++ U₂) ++ [c'])) := Gen.prod 2 _ _ _ rfl hp hrhs
  have := gen_NM_append h₁ (gen_NM_append hmid h₃)
  simpa [List.append_assoc] using this

/-- Peeling a wrapped bracket word `o v c'` off a spread word. -/
theorem spread_wrap_inv {W v : List Char} {o c' : Char} (h : Spread W (o :: (v ++ [c']))) :
    ∃ U₁ W₁ U₂ U₃, W = U₁ ++ o :: (W₁ ++ (U₂ ++ c' :: U₃)) ∧ Spread U₁ [] ∧ Spread W₁ v ∧
      Spread U₂ [] ∧ Spread U₃ [] := by
  obtain ⟨U₁, W', rfl, hU₁, hW'⟩ := h.head o _ rfl
  obtain ⟨W₁, W₂, rfl, hW₁, hW₂⟩ := hW'.split v [c'] rfl
  obtain ⟨U₂, U₃, rfl, hU₂, hU₃⟩ := hW₂.head c' [] rfl
  exact ⟨U₁, W₁, U₂, U₃, rfl, hU₁, hW₁, hU₂, hU₃⟩

/-- **`NM` generates `Ymid`** (Nipkow's `sprd_bal_imp_mbal` composed with `mbal_imp_Lang_NM`):
induction on the balanced word. -/
theorem gen_NM_of_spread {v : List Char} (hd : Dyck v) : ∀ {W}, Spread W v → Gen l0Grammar 2 W := by
  induction hd with
  | nil => intro W h; exact gen_NM_of_spread_nil h rfl
  | @append u v _ _ ihu ihv =>
      intro W h
      obtain ⟨W₁, W₂, rfl, h₁, h₂⟩ := h.split u v rfl
      exact gen_NM_append (ihu h₁) (ihv h₂)
  | @paren u _ ih =>
      intro W h
      obtain ⟨U₁, W₁, U₂, U₃, rfl, h₁, hW₁, h₂, h₃⟩ := spread_wrap_inv h
      have hW : Spread (W₁ ++ U₂) u := by simpa using hW₁.append h₂
      exact gen_NM_wrap (by simp) (gen_NM_of_spread_nil h₁ rfl) (ih hW)
        (gen_NM_of_spread_nil h₃ rfl)
  | @brack u _ ih =>
      intro W h
      obtain ⟨U₁, W₁, U₂, U₃, rfl, h₁, hW₁, h₂, h₃⟩ := spread_wrap_inv h
      have hW : Spread (W₁ ++ U₂) u := by simpa using hW₁.append h₂
      exact gen_NM_wrap (by simp) (gen_NM_of_spread_nil h₁ rfl) (ih hW)
        (gen_NM_of_spread_nil h₃ rfl)

/-- **Completeness** (Nipkow's `L0_subset_Lang`): `NZ` generates every word of `L0`. -/
theorem gen_NZ_of_L0 {w : List Char} (hw : L0 w) : Gen l0Grammar 0 w := by
  by_cases hne : w = []
  · subst hne
    exact Gen.prod 0 _ [] [] rfl (List.mem_cons_self ..) GenRhs.nil
  · obtain ⟨x, W, z, hx, ⟨v, hd, hs⟩, hz, rfl⟩ := Ymid_of_L0 hw hne
    have hrhs : GenRhs l0Grammar [.nt 1, .t 'c', .t '$', .nt 2, .t 'c', .nt 1, .t 'd']
        (x ++ 'c' :: '$' :: (W ++ 'c' :: (z ++ ['d']))) :=
      GenRhs.cons_nt 1 _ x _ (gen_NF hx) (GenRhs.cons_t _ _ _ (GenRhs.cons_t _ _ _
        (GenRhs.cons_nt 2 _ W _ (gen_NM_of_spread hd hs) (GenRhs.cons_t _ _ _
          (GenRhs.cons_nt 1 _ z _ (gen_NF hz) (GenRhs.cons_t _ _ _ GenRhs.nil))))))
    exact Gen.prod 0 _ _ _ rfl (by simp) hrhs

/-! ## The theorem -/

/-- `l0Grammar` generates exactly `L0` (Nipkow's `Lang_G_NZ`). -/
theorem l0Grammar_language (w : List Char) : L0 w ↔ l0Grammar.language w :=
  ⟨gen_NZ_of_L0, fun h => l0_gen_sound (i := 0) h⟩

/-- **Greibach's hardest language is context-free** (Nipkow's `CFL_L0`). -/
theorem l0_cfl : IsCFL L0 := ⟨l0Grammar, l0Grammar_language⟩

end Shallot.Cfg
