import MacroPeg.HigherOrder.ExpSpace.Grammar

/-!
# Addresses on the sites of the input

Fix the machine `M` and the input `w` (`n = |w|` sites). `sfxS j` is the input from site `j` on (`#` when `j = n`).
An address parser `A` represents the bit vector `v` (`RepA`) when, run at site `j`, it reads through the `x` iff
`vⱼ = 1`. A zero-width test `e` computes the Boolean `b` at `x` (`Test`) when it succeeds iff `b`.

* the scans `ALL1`, `ALL0`, `EQ` compute "all remaining bits are `1`", "… `0`", "the remaining bits agree";
* `H0` represents `0…0`, `incE H` represents `incBits v`, `decE H` represents `decBits v`.
-/

namespace Shallot.MacroPeg.ExpSpace

open Shallot.MacroPeg (ATM MGrammar MacroObs codeE siteE optY siteStr sitesStr tapeRest codeStr codeE_ok siteE_ok
  obs_seq obs_seq_none obs_alt_some obs_alt_none obs_lit_ok obs_char_fail obs_eps)
open Shallot.MacroPeg.HO

/-! ## Zero-width tests -/

section Tests

variable {g : HGrammar}

/-- `e` succeeds at `x` iff `b`. -/
def Test (g : HGrammar) (e : HExp) (x : List Char) (b : Bool) : Prop :=
  if b then ∃ y, HObs g e x (some y) else HObs g e x none

theorem test_true {e : HExp} {x y : List Char} (h : HObs g e x (some y)) : Test g e x true := ⟨y, h⟩
theorem test_false {e : HExp} {x : List Char} (h : HObs g e x none) : Test g e x false := h

theorem test_and {e : HExp} {x : List Char} {b : Bool} (h : Test g e x b) :
    HObs g (HExp.andP e) x (if b then some x else none) := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact hobs_and_some hy
  | false => exact hobs_and_none h

theorem test_not {e : HExp} {x : List Char} {b : Bool} (h : Test g e x b) :
    HObs g (.notP e) x (if b then none else some x) := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact hobs_not_ok hy
  | false => exact hobs_not_fail h

/-- A guard on a test. -/
theorem test_guard {C X Y : HExp} {x : List Char} {b : Bool} {r₁ r₂ : Option (List Char)} (hC : Test g C x b)
    (hX : HObs g X x r₁) (hY : HObs g Y x r₂) :
    HObs g (.alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)) x (if b then r₁ else r₂) := by
  cases b with
  | true => obtain ⟨y, hy⟩ := hC; exact HO.guard_pos hy hX
  | false => exact HO.guard_neg hC hY

theorem test_xor {P Q : HExp} {x : List Char} {p q : Bool} (hP : Test g P x p) (hQ : Test g Q x q) :
    Test g (xorE P Q) x (p != q) := by
  unfold xorE
  cases p <;> cases q
  · exact hobs_alt_fail (hobs_seq_fail (test_and hP)) (hobs_seq_ok (test_not hP) (test_and hQ))
  · exact ⟨_, hobs_alt_fail (hobs_seq_fail (test_and hP)) (hobs_seq_ok (test_not hP) (test_and hQ))⟩
  · exact ⟨_, hobs_alt_ok (hobs_seq_ok (test_and hP) (test_not hQ))⟩
  · exact hobs_alt_fail (hobs_seq_ok (test_and hP) (test_not hQ)) (hobs_seq_fail (test_not hP))

end Tests

/-! ## Plain pieces on sites -/

section Pieces

variable {g : HGrammar}

theorem hobs_lit (s rest : List Char) : HObs g (.lit s) (s ++ rest) (some rest) :=
  hobs_of_peg (G := ⟨[]⟩) (e := .lit s) trivial (obs_lit_ok s rest)

theorem hsiteE_ok (j : Nat) (b : Bool) (rest : List Char) : HObs g hsiteE (siteStr j b ++ rest) (some rest) :=
  hobs_of_peg (G := ⟨[]⟩) peg_siteE (siteE_ok j b rest)

theorem hhash_site (j : Nat) (b : Bool) (rest : List Char) : HObs g hhash (siteStr j b ++ rest) none := by
  refine ⟨1, ?_⟩
  rw [hrun.eq_def]
  cases j <;> simp [hhash, siteStr, codeStr, Shallot.stripPrefix?, Shallot.beqChar, List.replicate_succ]

theorem hhash_end : HObs g hhash ['#'] (some []) := hobs_lit ['#'] []

theorem hsiteE_hash (rest : List Char) : HObs g hsiteE ('#' :: rest) none :=
  hobs_of_peg (G := ⟨[]⟩) peg_siteE (Shallot.MacroPeg.siteE_hash rest)

/-- Reading a site through the `x` (bit `1`) or not (bit `0`). -/
theorem readOne_ok (j : Nat) (b : Bool) (rest : List Char) :
    HObs g (.seq (.seq hcodeE hoptY) (.lit ['x'])) (siteStr j b ++ rest) (some (tapeRest true rest)) := by
  refine hobs_of_peg (G := ⟨[]⟩) (e := .seq (.seq codeE optY) (.lit ['x']))
    ⟨⟨peg_codeE, peg_optY⟩, trivial⟩ ?_
  unfold siteStr tapeRest optY
  cases b with
  | true =>
    simp only [if_pos, List.append_assoc, List.cons_append, List.nil_append]
    exact obs_seq (obs_seq (codeE_ok j _) (obs_alt_some (obs_lit_ok ['y'] _))) (obs_lit_ok ['x'] _)
  | false =>
    simp only [List.append_assoc, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    exact obs_seq (obs_seq (codeE_ok j _) (obs_alt_none (obs_char_fail _ (by decide)) (obs_eps _)))
      (obs_lit_ok ['x'] _)

theorem readZero_ok (j : Nat) (b : Bool) (rest : List Char) :
    HObs g (.seq hcodeE hoptY) (siteStr j b ++ rest) (some (tapeRest false rest)) := by
  refine hobs_of_peg (G := ⟨[]⟩) (e := .seq codeE optY) ⟨peg_codeE, peg_optY⟩ ?_
  unfold siteStr tapeRest optY
  cases b with
  | true =>
    simp only [if_pos, List.append_assoc, List.cons_append, List.nil_append]
    exact obs_seq (codeE_ok j _) (obs_alt_some (obs_lit_ok ['y'] _))
  | false =>
    simp only [List.append_assoc, List.cons_append, List.nil_append, Bool.false_eq_true, ↓reduceIte]
    exact obs_seq (codeE_ok j _) (obs_alt_none (obs_char_fail _ (by decide)) (obs_eps _))

/-- After reading a site, `;` is next iff the bit read was `1`. -/
theorem hsemi_rest (t : Bool) (rest : List Char) :
    HObs g hsemi (tapeRest t rest) (if t then some rest else none) := by
  cases t
  · exact hobs_of_peg (G := ⟨[]⟩) (e := .lit [';']) trivial (obs_char_fail _ (by decide))
  · exact hobs_lit [';'] rest

/-- A site carries `y` iff its input symbol is `1`. -/
theorem hasY_ok (j : Nat) (b : Bool) (rest : List Char) :
    Test g (.seq hcodeE (.lit ['y'])) (siteStr j b ++ rest) b := by
  have hc : HObs g hcodeE (siteStr j b ++ rest) (some ((if b then ['y'] else []) ++ ['x', ';'] ++ rest)) :=
    hobs_of_peg (G := ⟨[]⟩) peg_codeE (by unfold siteStr; simpa [List.append_assoc] using codeE_ok j _)
  cases b with
  | true =>
    have hy : HObs g (.lit ['y']) (['y'] ++ (['x', ';'] ++ rest)) (some (['x', ';'] ++ rest)) := hobs_lit _ _
    simp only [if_pos, List.append_assoc] at hc
    exact ⟨_, hobs_seq_ok hc hy⟩
  | false =>
    have hy : HObs g (.lit ['y']) ('x' :: (';' :: rest)) none :=
      hobs_of_peg (G := ⟨[]⟩) (e := .lit ['y']) trivial (obs_char_fail _ (by decide))
    simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at hc
    exact hobs_seq_ok hc hy

end Pieces

/-! ## Addresses -/

section Addresses

variable (M : ATM) (w : List Bool)

local notation "G" => g2 M
local notation "n" => w.length

/-- The input from site `j` on. -/
def sfxS (j : Nat) : List Char := sitesStr (w.drop j) j

theorem sfxS_site {j : Nat} (hj : j < n) : sfxS w j = siteStr j (w.getD j false) ++ sfxS w (j + 1) :=
  Shallot.MacroPeg.sitesStr_drop hj

theorem sfxS_end : sfxS w n = ['#'] := by simp [sfxS, sitesStr]

/-- `A` represents the address `v`. -/
def RepA (A : HExp) (v : List Bool) : Prop :=
  HExp.Cl 0 A ∧ v.length = n ∧ (∀ j < n, HObs G A (sfxS w j) (some (tapeRest (v.getD j false) (sfxS w (j + 1))))) ∧
    HObs G A (sfxS w n) none

variable {M w}

theorem bit1_test {A : HExp} {v : List Bool} (hA : RepA M w A v) {j : Nat} (hj : j < n) :
    Test G (bit1 A) (sfxS w j) (v.getD j false) := by
  have h := hA.2.2.1 j hj
  have hs := hsemi_rest (g := G) (v.getD j false) (sfxS w (j + 1))
  cases hv : v.getD j false with
  | true => rw [hv] at h hs; exact ⟨_, hobs_seq_ok h hs⟩
  | false => rw [hv] at h hs; exact hobs_seq_ok h hs

/-- The scans start at `#` with success and otherwise look at the current site. -/
theorem hhash_not_site {j : Nat} (hj : j < n) : HObs G (HExp.andP hhash) (sfxS w j) none := by
  rw [sfxS_site w hj]; exact hobs_and_none (hhash_site j _ _)

theorem hhash_at_end : HObs G (HExp.andP hhash) (sfxS w n) (some (sfxS w n)) := by
  rw [sfxS_end]; exact hobs_and_some hhash_end

theorem siteE_step {j : Nat} (hj : j < n) {e : HExp} {r : Option (List Char)} (h : HObs G e (sfxS w (j + 1)) r) :
    HObs G (.seq hsiteE e) (sfxS w j) r := by
  rw [sfxS_site w hj]; exact hobs_seq_ok (hsiteE_ok j _ _) h

theorem test_and_seq {P Q : HExp} {x : List Char} {p q : Bool} (hP : Test G P x p) (hQ : HObs G Q x (if q then some x else none)) :
    HObs G (.seq (HExp.andP P) Q) x (if p && q then some x else none) := by
  cases p with
  | true => obtain ⟨y, hy⟩ := hP; simpa using hobs_seq_ok (hobs_and_some hy) hQ
  | false => simpa using hobs_seq_fail (g := G) (B := Q) (hobs_and_none hP)

theorem all1_call {h : HExp} (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs G (all1E M h) x r) : HObs G (rcall (rALL1 M) [h]) x r :=
  hobs_call (g2_all1 M) rfl (fun c hc => by simp at hc; rw [hc]; exact hh)
    (by rw [List.reverse_singleton, inst_all1]; exact hr)

theorem drop_getD {v : List Bool} {i : Nat} (hi : i < v.length) : v.drop i = v.getD i false :: v.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `ALL1(h)` at site `i`: all bits from `i` on are `1`. -/
theorem all1_ok {h : HExp} {v : List Bool} (hh : RepA M w h v) :
    ∀ d i, i + d = n → Test G (rcall (rALL1 M) [h]) (sfxS w i) ((v.drop i).all id) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = n := by omega
    subst hin
    have hv : v.drop w.length = [] := by simp [hh.2.1]
    rw [hv]
    exact ⟨_, all1_call hh.1 (hobs_alt_ok hhash_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < n := by omega
    have hrec := ih (i + 1) (by omega)
    have hbit := bit1_test hh hlt
    rw [drop_getD (by rw [hh.2.1]; exact hlt), List.all_cons]
    cases hb : v.getD i false with
    | false =>
      rw [hb] at hbit
      exact all1_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_fail (hobs_and_none hbit)))
    | true =>
      rw [hb] at hbit
      obtain ⟨y, hy⟩ := hbit
      simp only [id, Bool.true_and]
      cases hall : (v.drop (i + 1)).all id with
      | true =>
        rw [hall] at hrec
        obtain ⟨z, hz⟩ := hrec
        exact ⟨_, all1_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok (hobs_and_some hy) (siteE_step hlt hz)))⟩
      | false =>
        rw [hall] at hrec
        exact all1_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok (hobs_and_some hy) (siteE_step hlt hrec)))

theorem bit1_end {A : HExp} {v : List Bool} (hA : RepA M w A v) : HObs G (bit1 A) (sfxS w n) none :=
  hobs_seq_fail hA.2.2.2

theorem hsiteE_end : HObs G hsiteE (sfxS w n) none := by
  rw [sfxS_end]; exact hsiteE_hash []

theorem all0_call {h : HExp} (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs G (all0E M h) x r) : HObs G (rcall (rALL0 M) [h]) x r :=
  hobs_call (g2_all0 M) rfl (fun c hc => by simp at hc; rw [hc]; exact hh)
    (by rw [List.reverse_singleton, inst_all0]; exact hr)

/-- `ALL0(h)` at site `i`: all bits from `i` on are `0`. -/
theorem all0_ok {h : HExp} {v : List Bool} (hh : RepA M w h v) :
    ∀ d i, i + d = n → Test G (rcall (rALL0 M) [h]) (sfxS w i) ((v.drop i).all (! ·)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = n := by omega
    subst hin
    have hv : v.drop w.length = [] := by simp [hh.2.1]
    rw [hv]
    exact ⟨_, all0_call hh.1 (hobs_alt_ok hhash_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < n := by omega
    have hrec := ih (i + 1) (by omega)
    have hbit := bit1_test hh hlt
    rw [drop_getD (by rw [hh.2.1]; exact hlt), List.all_cons]
    cases hb : v.getD i false with
    | true =>
      rw [hb] at hbit
      obtain ⟨y, hy⟩ := hbit
      exact all0_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_fail (hobs_not_ok hy)))
    | false =>
      rw [hb] at hbit
      simp only [Bool.not_false, Bool.true_and]
      cases hall : (v.drop (i + 1)).all (! ·) with
      | true =>
        rw [hall] at hrec
        obtain ⟨z, hz⟩ := hrec
        exact ⟨_, all0_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok (hobs_not_fail hbit) (siteE_step hlt hz)))⟩
      | false =>
        rw [hall] at hrec
        exact all0_call hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok (hobs_not_fail hbit) (siteE_step hlt hrec)))

theorem eq_call {a h : HExp} (ha : HExp.Cl 0 a) (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs G (eqE M a h) x r) : HObs G (rcall (rEQ M) [a, h]) x r :=
  hobs_call (g2_eq M) rfl (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ha
      · exact hh)
    (by rw [show [a, h].reverse = [h, a] from rfl, inst_eq]; exact hr)

/-- The two bits at a site agree (a zero-width test). -/
theorem same_obs {a h : HExp} {va vh : List Bool} (ha : RepA M w a va) (hh : RepA M w h vh) {j : Nat} (hj : j < n) :
    HObs G (.alt (.seq (HExp.andP (bit1 a)) (HExp.andP (bit1 h))) (.seq (.notP (bit1 a)) (.notP (bit1 h))))
      (sfxS w j) (if va.getD j false = vh.getD j false then some (sfxS w j) else none) := by
  have hA := bit1_test ha hj
  have hH := bit1_test hh hj
  cases hx : va.getD j false <;> cases hy : vh.getD j false <;> rw [hx] at hA <;> rw [hy] at hH <;>
    (try simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false])
  · exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hA)) (hobs_seq_ok (hobs_not_fail hA) (hobs_not_fail hH))
  · obtain ⟨z, hz⟩ := hH
    exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hA)) (hobs_seq_ok (hobs_not_fail hA) (hobs_not_ok hz))
  · obtain ⟨z, hz⟩ := hA
    exact hobs_alt_fail (hobs_seq_ok (hobs_and_some hz) (hobs_and_none hH)) (hobs_seq_fail (hobs_not_ok hz))
  · obtain ⟨z, hz⟩ := hA
    obtain ⟨z', hz'⟩ := hH
    exact hobs_alt_ok (hobs_seq_ok (hobs_and_some hz) (hobs_and_some hz'))

/-- `EQ(a, h)` at site `i`: the bits from `i` on agree. -/
theorem eq_ok {a h : HExp} {va vh : List Bool} (ha : RepA M w a va) (hh : RepA M w h vh) :
    ∀ d i, i + d = n → Test G (rcall (rEQ M) [a, h]) (sfxS w i) (decide (va.drop i = vh.drop i)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = n := by omega
    subst hin
    have h₁ : va.drop w.length = [] := by simp [ha.2.1]
    have h₂ : vh.drop w.length = [] := by simp [hh.2.1]
    rw [h₁, h₂]
    exact ⟨_, eq_call ha.1 hh.1 (hobs_alt_ok hhash_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < n := by omega
    have hrec := ih (i + 1) (by omega)
    have hs := same_obs ha hh hlt
    have hda := drop_getD (v := va) (i := i) (by rw [ha.2.1]; exact hlt)
    have hdh := drop_getD (v := vh) (i := i) (by rw [hh.2.1]; exact hlt)
    rw [hda, hdh]
    simp only [List.cons.injEq]
    by_cases he : va.getD i false = vh.getD i false
    · rw [if_pos he] at hs
      simp only [he, true_and]
      cases hall : decide (va.drop (i + 1) = vh.drop (i + 1)) with
      | true =>
        rw [hall] at hrec
        obtain ⟨z, hz⟩ := hrec
        exact ⟨_, eq_call ha.1 hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok hs (siteE_step hlt hz)))⟩
      | false =>
        rw [hall] at hrec
        exact eq_call ha.1 hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_ok hs (siteE_step hlt hrec)))
    · rw [if_neg he] at hs
      simp only [he, false_and, decide_false]
      exact eq_call ha.1 hh.1 (hobs_alt_fail (hhash_not_site hlt) (hobs_seq_fail hs))

end Addresses

end Shallot.MacroPeg.ExpSpace
