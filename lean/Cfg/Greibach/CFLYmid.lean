import Cfg.Greibach.Defs

/-!
# The middle language of `L0`: bracket blocks interleaved with gaps

Following Nipkow's Isabelle formalization (AFP `Greibach_Hardest`, section "`L0` is context-free"):
every non-empty word of `L0` has the shape `x c ¢ W c z d` with `x, z ∈ T*` and `W` a sequence of
bracket letters interspersed with *gaps* `c z' d x' c` (`x', z' ∈ T*`) whose bracket letters form a
balanced word.

Nipkow states the middle language `Ymid` with `interl` (interleaving a list of bracket blocks with a
list of gaps) and proves its completeness half through the relation `sprd`. Here `sprd` is used for
both halves: `Spread W v` says that `W` is the word `v` of bracket letters with gaps inserted
anywhere, and `Ymid W := ∃ v, Dyck v ∧ Spread W v`. This is the same language as Nipkow's `Ymid`
(his `interl_sprd` is the `⊆` half of that identity) and avoids the length bookkeeping of `interl`.

Contents:
- `Spread` and its algebra (`Spread.append`, `Spread.split`, `Spread.head`);
- `Ymid` and its closure under `ε`, gaps, concatenation and wrapping (`Ymid_nil`, `Ymid_gap`,
  `Ymid_append`, `Ymid_paren`, `Ymid_brack`);
- the bridge between `Ymid` and the block-list form of `L0` (`L0_of_Ymid`, `Ymid_of_L0`).
-/

namespace Shallot.Cfg

/-- `T*`: every letter of the word is in Greibach's alphabet `T`. -/
def TStar (w : List Char) : Prop := ∀ c ∈ w, isT c = true

/-- Every letter of the word is a bracket. -/
def Bracks (w : List Char) : Prop := ∀ c ∈ w, isBracket c = true

/-- A gap `c z d x c` with `z, x ∈ T*` (Nipkow's `Gap`). -/
def IsGap (g : List Char) : Prop :=
  ∃ z x, TStar z ∧ TStar x ∧ g = 'c' :: (z ++ 'd' :: (x ++ ['c']))

/-- **Spreading** (Nipkow's `sprd`): `W` is the bracket word `v` with gaps inserted anywhere. -/
inductive Spread : List Char → List Char → Prop
  | nil : Spread [] []
  | gap {g W v : List Char} : IsGap g → Spread W v → Spread (g ++ W) v
  | brk {b : Char} {W v : List Char} : isBracket b = true → Spread W v → Spread (b :: W) (b :: v)

/-- **The middle language** (Nipkow's `Ymid`): gaps spread into a balanced bracket word. -/
def Ymid (W : List Char) : Prop := ∃ v, Dyck v ∧ Spread W v

/-! ## Elementary facts about `T*`, brackets and `Dyck` -/

/-- `T*` of a concatenation. -/
theorem TStar_append {u v : List Char} (hu : TStar u) (hv : TStar v) : TStar (u ++ v) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hu c h
  · exact hv c h

/-- The empty word is in `T*`. -/
theorem TStar_nil : TStar [] := fun _ h => absurd h List.not_mem_nil

/-- Balanced words consist of bracket letters only. -/
theorem Dyck.bracks {v : List Char} (h : Dyck v) : Bracks v := by
  induction h with
  | nil => intro c hc; exact absurd hc List.not_mem_nil
  | append _ _ ihu ihv =>
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact ihu c h
      · exact ihv c h
  | paren _ ih =>
      intro c hc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | h | rfl
      · rfl
      · exact ih c h
      · rfl
  | brack _ ih =>
      intro c hc
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | h | rfl
      · rfl
      · exact ih c h
      · rfl

/-- `$` is not a bracket. -/
theorem isBracket_dollar : isBracket '$' = false := by decide

/-! ## The algebra of `Spread` -/

/-- A bracket word spreads to itself (no gaps). -/
theorem Spread.self : ∀ {y : List Char}, Bracks y → Spread y y
  | [], _ => Spread.nil
  | b :: _, h => Spread.brk (h b (List.mem_cons_self ..))
      (Spread.self (fun c hc => h c (List.mem_cons_of_mem _ hc)))

/-- A single gap spreads to the empty bracket word. -/
theorem Spread.ofGap {g : List Char} (hg : IsGap g) : Spread g [] := by
  have h := Spread.gap hg Spread.nil
  rwa [List.append_nil] at h

/-- Spreading is compatible with concatenation (Nipkow's `sprd_brk_list` generalized). -/
theorem Spread.append {W₁ v₁ W₂ v₂ : List Char} (h₁ : Spread W₁ v₁) (h₂ : Spread W₂ v₂) :
    Spread (W₁ ++ W₂) (v₁ ++ v₂) := by
  induction h₁ with
  | nil => exact h₂
  | gap hg _ ih => rw [List.append_assoc]; exact Spread.gap hg ih
  | brk hb _ ih => exact Spread.brk hb ih

/-- Splitting the bracket word splits the spread word (Nipkow's `sprd_split`). -/
theorem Spread.split {W v : List Char} (h : Spread W v) :
    ∀ v₁ v₂, v = v₁ ++ v₂ → ∃ W₁ W₂, W = W₁ ++ W₂ ∧ Spread W₁ v₁ ∧ Spread W₂ v₂ := by
  induction h with
  | nil =>
      intro v₁ v₂ hv
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hv.symm
      exact ⟨[], [], rfl, Spread.nil, Spread.nil⟩
  | gap hg _ ih =>
      intro v₁ v₂ hv
      obtain ⟨W₁, W₂, rfl, h₁, h₂⟩ := ih v₁ v₂ hv
      exact ⟨_ ++ W₁, W₂, (List.append_assoc ..).symm, Spread.gap hg h₁, h₂⟩
  | @brk b W v hb hW ih =>
      intro v₁ v₂ hv
      cases v₁ with
      | nil => exact ⟨[], b :: W, rfl, Spread.nil, by rw [List.nil_append] at hv; rw [← hv]; exact Spread.brk hb hW⟩
      | cons c v₁' =>
          simp only [List.cons_append, List.cons.injEq] at hv
          obtain ⟨rfl, hv'⟩ := hv
          obtain ⟨W₁, W₂, rfl, h₁, h₂⟩ := ih v₁' v₂ hv'
          exact ⟨b :: W₁, W₂, rfl, Spread.brk hb h₁, h₂⟩

/-- The first bracket of the bracket word is preceded by gaps only (Nipkow's `sprd_head`). -/
theorem Spread.head {W v : List Char} (h : Spread W v) :
    ∀ b v', v = b :: v' → ∃ U W', W = U ++ b :: W' ∧ Spread U [] ∧ Spread W' v' := by
  induction h with
  | nil => intro b v' hv; cases hv
  | gap hg _ ih =>
      intro b v' hv
      obtain ⟨U, W', rfl, hU, hW'⟩ := ih b v' hv
      exact ⟨_ ++ U, W', (List.append_assoc ..).symm, Spread.gap hg hU, hW'⟩
  | brk _ hW _ =>
      intro b v' hv
      simp only [List.cons.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact ⟨[], _, rfl, Spread.nil, hW⟩

/-! ## Closure properties of `Ymid` (Nipkow's `Ymid_Nil`, `Ymid_gap`, `Ymid_app`, `Ymid_wrap`) -/

/-- `ε ∈ Ymid`. -/
theorem Ymid_nil : Ymid [] := ⟨[], Dyck.nil, Spread.nil⟩

/-- Every gap is in `Ymid`. -/
theorem Ymid_gap {g : List Char} (hg : IsGap g) : Ymid g := ⟨[], Dyck.nil, Spread.ofGap hg⟩

/-- `Ymid` is closed under concatenation. -/
theorem Ymid_append {W₁ W₂ : List Char} (h₁ : Ymid W₁) (h₂ : Ymid W₂) : Ymid (W₁ ++ W₂) := by
  obtain ⟨v₁, hd₁, hs₁⟩ := h₁
  obtain ⟨v₂, hd₂, hs₂⟩ := h₂
  exact ⟨v₁ ++ v₂, Dyck.append hd₁ hd₂, Spread.append hs₁ hs₂⟩

/-- `Ymid` is closed under wrapping in `(`…`)`. -/
theorem Ymid_paren {W : List Char} (h : Ymid W) : Ymid ('(' :: (W ++ [')'])) := by
  obtain ⟨v, hd, hs⟩ := h
  exact ⟨_, Dyck.paren hd, Spread.brk rfl (Spread.append hs (Spread.brk rfl Spread.nil))⟩

/-- `Ymid` is closed under wrapping in `[`…`]`. -/
theorem Ymid_brack {W : List Char} (h : Ymid W) : Ymid ('[' :: (W ++ [']'])) := by
  obtain ⟨v, hd, hs⟩ := h
  exact ⟨_, Dyck.brack hd, Spread.brk rfl (Spread.append hs (Spread.brk rfl Spread.nil))⟩

/-! ## Bridging `Ymid` and the block-list form of `L0` (Nipkow's `mkblocks`, `blocks_decomp`) -/

/-- The concatenation of the middle components of a block list. -/
def mids (bs : List (List Char × List Char × List Char)) : List Char := (bs.map fun b => b.2.1).flatten

/-- Every block's outer components lie in `T*`. -/
def OuterT (bs : List (List Char × List Char × List Char)) : Prop :=
  ∀ b ∈ bs, (∀ c ∈ b.1, isT c = true) ∧ (∀ c ∈ b.2.2, isT c = true)

/-- Every block's middle component consists of brackets. -/
def MidBr (bs : List (List Char × List Char × List Char)) : Prop :=
  ∀ b ∈ bs, ∀ c ∈ b.2.1, isBracket c = true

/-- **Blocks to a spread word** (Nipkow's `blocks_decomp`, tail form): a bracket block `y`, the
end `z₀ d` of its block and a list of further blocks read as `W c z d` with `W` spreading the
concatenated middles. -/
theorem spread_of_blocks : ∀ (bs : List (List Char × List Char × List Char)), OuterT bs → MidBr bs →
    ∀ y z₀, Bracks y → TStar z₀ →
      ∃ W z, TStar z ∧ Spread W (y ++ mids bs) ∧
        y ++ 'c' :: (z₀ ++ 'd' :: (bs.map blk).flatten) = W ++ 'c' :: (z ++ ['d'])
  | [], _, _, y, z₀, hy, hz₀ => ⟨y, z₀, hz₀, by simpa [mids] using Spread.self hy, by simp⟩
  | (x₁, y₁, z₁) :: bs, hT, hB, y, z₀, hy, hz₀ => by
      have hT' : OuterT bs := fun b hb => hT b (List.mem_cons_of_mem _ hb)
      have hB' : MidBr bs := fun b hb => hB b (List.mem_cons_of_mem _ hb)
      have h₁ := hT (x₁, y₁, z₁) (List.mem_cons_self ..)
      have hy₁ : Bracks y₁ := hB (x₁, y₁, z₁) (List.mem_cons_self ..)
      obtain ⟨W', z, hz, hs, heq⟩ := spread_of_blocks bs hT' hB' y₁ z₁ hy₁ h₁.2
      have hgap : IsGap ('c' :: (z₀ ++ 'd' :: (x₁ ++ ['c']))) := ⟨z₀, x₁, hz₀, h₁.1, rfl⟩
      refine ⟨y ++ ('c' :: (z₀ ++ 'd' :: (x₁ ++ ['c']))) ++ W', z, hz, ?_, ?_⟩
      · have : y ++ mids ((x₁, y₁, z₁) :: bs) = y ++ ([] ++ (y₁ ++ mids bs)) := by simp [mids]
        rw [this, List.append_assoc]
        exact Spread.append (Spread.self hy) (Spread.gap hgap hs)
      · simp only [List.map_cons, List.flatten_cons, blk, List.append_assoc, List.cons_append,
          List.nil_append] at heq ⊢
        rw [← heq]

/-- **A spread word to blocks** (Nipkow's `mkblocks`, tail form): `W c z d` with `W` spreading `v`
reads as a bracket block `y`, an end `z₀ d`, and further blocks whose middles complete `v`. -/
theorem blocks_of_spread {W v : List Char} (h : Spread W v) :
    ∀ z, TStar z → ∃ y z₀ : List Char, ∃ bs : List (List Char × List Char × List Char),
      Bracks y ∧ TStar z₀ ∧ OuterT bs ∧ MidBr bs ∧ y ++ mids bs = v ∧
        W ++ 'c' :: (z ++ ['d']) = y ++ 'c' :: (z₀ ++ 'd' :: (bs.map blk).flatten) := by
  induction h with
  | nil =>
      intro z hz
      exact ⟨[], z, [], fun _ h => absurd h List.not_mem_nil, hz,
        fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, rfl, by simp⟩
  | gap hg _ ih =>
      intro z hz
      obtain ⟨zz, xx, hzz, hxx, rfl⟩ := hg
      obtain ⟨y, z₀, bs, hy, hz₀, hT, hB, hv, heq⟩ := ih z hz
      refine ⟨[], zz, (xx, y, z₀) :: bs, fun _ h => absurd h List.not_mem_nil, hzz, ?_, ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hxx, hz₀⟩
        · exact hT b hb
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hy
        · exact hB b hb
      · simpa [mids] using hv
      · simp only [List.map_cons, List.flatten_cons, blk, List.append_assoc, List.cons_append,
          List.nil_append] at heq ⊢
        rw [heq]
  | brk hb _ ih =>
      intro z hz
      obtain ⟨y, z₀, bs, hy, hz₀, hT, hB, hv, heq⟩ := ih z hz
      refine ⟨_ :: y, z₀, bs, ?_, hz₀, hT, hB, by rw [← hv]; rfl, by rw [List.cons_append, heq]; rfl⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hy c hc

/-- **`Ymid` to `L0`** (Nipkow's `Ymid_imp_L0`): `x c ¢ W c z d ∈ L0` for `x, z ∈ T*`, `W ∈ Ymid`. -/
theorem L0_of_Ymid {x W z : List Char} (hx : TStar x) (hW : Ymid W) (hz : TStar z) :
    L0 (x ++ 'c' :: '$' :: (W ++ 'c' :: (z ++ ['d']))) := by
  obtain ⟨v, hd, hs⟩ := hW
  obtain ⟨y, z₀, bs, _, hz₀, hT, hB, hv, heq⟩ := blocks_of_spread hs z hz
  refine Or.inr ⟨(x, '$' :: y, z₀) :: bs, List.cons_ne_nil _ _, ?_, ?_, hB, v, hd, ?_⟩
  · rw [heq]
    simp [blk]
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hx, hz₀⟩
    · exact hT b hb
  · have : (((x, '$' :: y, z₀) :: bs).map fun b => b.2.1).flatten = '$' :: (y ++ mids bs) := by
      simp [mids]
    rw [this, hv]

/-- **`L0` to `Ymid`** (Nipkow's `L0_imp_Ymid`): a non-empty word of `L0` is `x c ¢ W c z d` with
`x, z ∈ T*` and `W ∈ Ymid`. -/
theorem Ymid_of_L0 {w : List Char} (hw : L0 w) (hne : w ≠ []) :
    ∃ x W z, TStar x ∧ Ymid W ∧ TStar z ∧ w = x ++ 'c' :: '$' :: (W ++ 'c' :: (z ++ ['d'])) := by
  rcases hw with h | ⟨bs, hbs, rfl, hT, hB, v, hd, hv⟩
  · exact absurd h hne
  cases bs with
  | nil => exact absurd rfl hbs
  | cons b bs =>
      obtain ⟨x₀, y₀, z₀⟩ := b
      have hT' : OuterT bs := fun b hb => hT b (List.mem_cons_of_mem _ hb)
      have h₀ := hT (x₀, y₀, z₀) (List.mem_cons_self ..)
      have hB' : MidBr bs := hB
      have hv' : y₀ ++ mids bs = '$' :: v := by simpa [mids] using hv
      cases y₀ with
      | nil =>
          have hmem : '$' ∈ mids bs := by rw [List.nil_append] at hv'; rw [hv']; exact List.mem_cons_self ..
          obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hmem
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hl
          have := hB' b' hb' '$' hcl
          rw [isBracket_dollar] at this
          exact absurd this Bool.false_ne_true
      | cons c y₀' =>
          simp only [List.cons_append, List.cons.injEq] at hv'
          obtain ⟨rfl, hv''⟩ := hv'
          have hy₀' : Bracks y₀' := fun c hc =>
            hd.bracks c (by rw [← hv'']; exact List.mem_append_left _ hc)
          obtain ⟨W, z, hz, hs, heq⟩ := spread_of_blocks bs hT' hB' y₀' z₀ hy₀' h₀.2
          refine ⟨x₀, W, z, h₀.1, ⟨v, hd, by rw [← hv'']; exact hs⟩, hz, ?_⟩
          rw [← heq]
          simp [blk]

end Shallot.Cfg
