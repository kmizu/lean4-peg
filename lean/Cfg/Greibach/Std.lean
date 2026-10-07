import Cfg.Greibach.StdBlocks

/-!
# Greibach's hardest-language theorem for grammars in standard form

Following Nipkow's `Greibach_2_1_std` (AFP `Greibach_Hardest`): for a grammar `g` in standard form, the homomorphism
`h(a) = c ξ̂(p₁) c … c ξ̂(pₘ) c d` (`GStd.encH`) satisfies `L(g) - {ε} = h⁻¹(L0 - {ε})` (`greibach_std`). A letter
heading no right side gets the block `c d`, so `h` has finitely many distinct blocks.

- `forward`: a complete drive's encoding is a block word whose middles are `¢` followed by a balanced word.
- `backward`: a nonempty `L0`-word `h(w)` parses back into a production list whose codes run the stack machine from
  `[start]` to `[]`, hence a drive.
-/

namespace Shallot.Cfg
namespace GStd

/-- Productions not expanding `S` have `ξ̂ = ξ`. -/
theorem map_xihat_no_S {S : Nat} : ∀ {qs : List GProd}, (∀ p ∈ qs, p.1 ≠ S) → qs.map (xihat S) = qs.map xi
  | [], _ => rfl
  | q :: qs, h => by
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨by simp [xihat, h q List.mem_cons_self], map_xihat_no_S (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

/-- The middles of a derivation from `S` whose first production expands `S` and no later one does. -/
theorem flatten_xihat {S : Nat} {p0 : GProd} {ps : List GProd} (h0 : p0.1 = S) (hS : ∀ p ∈ ps, p.1 ≠ S) :
    ((p0 :: ps).map (xihat S)).flatten = '$' :: (pushcode S ++ ((p0 :: ps).map xi).flatten) := by
  simp only [List.map_cons, List.flatten_cons, map_xihat_no_S hS]
  simp [xihat, h0]

/-- A run from `[S]`: after `pushcode S`, the stack is the encoding of `[S]`. -/
theorem stkRun_push_start (S : Nat) (u : List Char) :
    stkRun [] (pushcode S ++ u) = stkRun (stkenc [S]) u := by
  rw [stkRun_append, stkRun_pushcode, Option.bind_some]
  simp [stkenc]

/-- **Forward direction**: the encoding of a word with a complete drive is in `L0`. -/
theorem forward {g : CFGrammar} (hs : StdForm g) {ps : List GProd} {w : List Char}
    (hd : Drives (prods g) ps [g.start] w []) : L0 ((w.map (encH g.start (prods g))).flatten) := by
  have hlet := hd.letters
  cases hd with
  | @cons _ a Bs ps' _ w' _ hp hd' =>
    have hnoS : ∀ p ∈ ps', p.1 ≠ g.start :=
      hd'.no_start (fun p hq => prods_start hs hq) (by simpa using prods_start hs hp)
    obtain ⟨bs, h1, h2, h3⟩ := block_decomp g.start (prods g) ((g.start, a, Bs) :: ps') hlet.2
    rw [hlet.1] at h1
    refine Or.inr ⟨bs, ?_, h1, h3, ?_, ?_⟩
    · intro hb; subst hb; cases h2
    · cases bs with
      | nil => cases h2
      | cons b0 bs' =>
        simp only [List.map_cons, List.cons.injEq] at h2
        intro b hb c hc
        have hm : b.2.1 ∈ ps'.map (xihat g.start) := h2.2 ▸ List.mem_map_of_mem hb
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
        rw [← hqe, xihat, if_neg (hnoS q hq)] at hc
        exact xi_bracket q c hc
    · refine ⟨pushcode g.start ++ (((g.start, a, Bs) :: ps').map xi).flatten, ?_, ?_⟩
      · rw [dyck_iff_stkRun, stkRun_push_start]
        exact drives_stkRun (Drives.cons hp hd')
      · rw [h2]; exact flatten_xihat rfl hnoS

/-- A nonempty word has a nonempty encoding. -/
theorem encode_ne_nil (S : Nat) (P : List GProd) {w : List Char} (hw : w ≠ []) :
    (w.map (encH S P)).flatten ≠ [] := by
  cases w with
  | nil => exact absurd rfl hw
  | cons a w =>
    obtain ⟨p, hp, _⟩ := encH_d S P a
    simp [hp]

/-- **Backward direction**: a nonempty word whose encoding is in `L0` has a complete drive. -/
theorem backward (g : CFGrammar) {w : List Char} (hw : w ≠ [])
    (hL : L0 ((w.map (encH g.start (prods g))).flatten)) : ∃ ps, Drives (prods g) ps [g.start] w [] := by
  rcases hL with he | ⟨bs, hne, hbw, hxz, htl, v, hv, hy⟩
  · exact absurd he (encode_ne_nil _ _ hw)
  -- the middles are brackets and `¢`
  have hychars : ∀ b ∈ bs, ∀ c ∈ b.2.1, c = '$' ∨ isBracket c = true := by
    intro b hb c hc
    have hm : c ∈ (bs.map fun b => b.2.1).flatten := List.mem_flatten.mpr ⟨b.2.1, List.mem_map_of_mem hb, hc⟩
    rw [hy] at hm
    rcases List.mem_cons.mp hm with h | h
    · exact Or.inl h
    · exact Or.inr (dyck_bracket hv c h)
  -- the blocks align with the letters' blocks
  have halign : bs.map blk = w.map (encH g.start (prods g)) := by
    refine blocks_align (s := 'd') hbw.symm ?_ ?_
    · intro xs hxs
      obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hxs
      subst hbe
      refine ⟨b.1 ++ 'c' :: (b.2.1 ++ 'c' :: b.2.2), by simp [blk], ?_⟩
      intro hd
      simp only [List.mem_append, List.mem_cons] at hd
      rcases hd with h | h | h | h | h
      · exact ne_d_of_isT ((hxz b hb).1 _ h) rfl
      · cases h
      · exact ne_d_of_chars (hychars b hb _ h) rfl
      · cases h
      · exact ne_d_of_isT ((hxz b hb).2 _ h) rfl
    · intro ys hys
      obtain ⟨a, _, hae⟩ := List.mem_map.mp hys
      subst hae
      exact encH_d _ _ a
  obtain ⟨ps, hpw, hpP, hpy⟩ := blocks_to_ps g.start (prods g) w bs halign
    (fun b hb hc => ne_c_of_chars (hychars b hb _ hc) rfl)
  cases ps with
  | nil => exact absurd hpw.symm hw
  | cons p0 ps' =>
    have hflat : ((p0 :: ps').map (xihat g.start)).flatten = '$' :: v := by rw [← hpy]; exact hy
    -- the first production expands the start
    have h0 : p0.1 = g.start := by
      apply Classical.byContradiction
      intro hne0
      simp only [List.map_cons, List.flatten_cons, xihat, if_neg hne0, xi, popcode] at hflat
      simp at hflat
    -- no later one does
    have hnoS : ∀ p ∈ ps', p.1 ≠ g.start := by
      cases bs with
      | nil => exact absurd rfl hne
      | cons b0 bs' =>
        simp only [List.map_cons, List.cons.injEq] at hpy
        intro q hq hqS
        have hm : xihat g.start q ∈ bs'.map (fun b => b.2.1) := hpy.2 ▸ List.mem_map_of_mem hq
        obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hm
        have hc : '$' ∈ b.2.1 := by rw [hbe]; simp [xihat, hqS]
        have := htl b hb '$' hc
        cases this
    rw [flatten_xihat h0 hnoS, List.cons.injEq] at hflat
    rw [← hflat.2, dyck_iff_stkRun, stkRun_push_start] at hv
    have hd := drives_of_stkRun hpP hv
    rw [hpw] at hd
    exact ⟨_, hd⟩

end GStd

open GStd in
/-- **Greibach's hardest-language theorem for grammars in standard form** (after Nipkow's `Greibach_2_1_std`): the
nonempty words of the language are exactly the nonempty inverse image of `L0` under a nonerasing homomorphism `h`,
which maps every letter outside the finite list `S` (the letters heading right sides) to `c d`. -/
theorem greibach_std (g : CFGrammar) (hs : StdForm g) :
    ∃ (h : Char → List Char) (S : List Char), (∀ a, h a ≠ []) ∧ (∀ a, a ∉ S → h a = ['c', 'd']) ∧
      ∀ w, w ≠ [] → (g.language w ↔ invHom h L0 w) := by
  refine ⟨encH g.start (prods g), (prods g).map (·.2.1), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨p, hp, _⟩ := encH_d g.start (prods g) a
    rw [hp] at ha
    simp at ha
  · intro a ha
    have hnil : prodsOf (prods g) a = [] := by
      rw [prodsOf, List.filter_eq_nil_iff]
      intro p hp hpa
      exact ha (List.mem_map.mpr ⟨p, hp, by simpa using hpa⟩)
    simp [encH, hnil]
  · intro w hw
    rw [language_iff_drives hs]
    constructor
    · rintro ⟨ps, hd⟩
      exact forward hs hd
    · intro hL
      exact backward g hw hL

end Shallot.Cfg
