import MacroPeg.HigherOrder.ExpSpace.Address
import MacroPeg.HigherOrder.Levels.NatBits

/-!
# Level-1 numbers: bit vectors on the bit sites

The input starts with `m` bit sites `1ʲ0x;` (`siteStr j false`), then `|`, then anything (`z`). A level-1 number
`x < 2^m` is a parser that, run at site `j`, reads through the `x` iff bit `m-1-j` of `x` is set (`Rep1`): the
address parsers of `ExpSpace/Address.lean`, with `|` instead of `#` after the sites and a value in `ℕ`.

The three scan rules (`ALL1`, `ALL0`, `EQ`, rule numbers `0, 1, 2` of any grammar that starts with `level1Rules`)
decide, at the start of the input, whether a number is the largest one, zero, or equal to another. The successor and
the predecessor are the plain parsers `incB` / `decB` (one site at a time, looking ahead with the scans).
-/

namespace Shallot.MacroPeg.Levels

open Shallot.MacroPeg (siteStr tapeRest)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.ExpSpace (Test test_true test_false test_and test_not test_guard test_xor hobs_lit hsiteE_ok
  readOne_ok readZero_ok hsemi_rest hcodeE hsiteE hoptY hsemi rcall bit1 xorE newSite cl_hcodeE cl_hsiteE cl_hoptY
  cl_rcall drop_getD peg_codeE peg_siteE incBits decBits)

/-! ## The bit sites -/

/-- `c` bit sites from site `j` on. -/
def bitsFrom : Nat → Nat → List Char
  | _, 0 => []
  | j, c + 1 => siteStr j false ++ bitsFrom (j + 1) c

/-- The input from bit site `j` on: the remaining bit sites, `|`, then `z`. -/
def sfxB (m : Nat) (z : List Char) (j : Nat) : List Char := bitsFrom j (m - j) ++ '|' :: z

theorem sfxB_site {m : Nat} (z : List Char) {j : Nat} (hj : j < m) :
    sfxB m z j = siteStr j false ++ sfxB m z (j + 1) := by
  unfold sfxB
  rw [show m - j = (m - (j + 1)) + 1 by omega]
  simp [bitsFrom, List.append_assoc]

theorem sfxB_end (m : Nat) (z : List Char) : sfxB m z m = '|' :: z := by simp [sfxB, bitsFrom]

/-! ## Pieces at `|` -/

section Pieces

variable {g : HGrammar}

def hbar : HExp := .lit ['|']

theorem hbar_site (j : Nat) (b : Bool) (rest : List Char) : HObs g hbar (siteStr j b ++ rest) none := by
  refine ⟨1, ?_⟩
  rw [hrun.eq_def]
  cases j <;> simp [hbar, siteStr, Shallot.MacroPeg.codeStr, Shallot.stripPrefix?, Shallot.beqChar, List.replicate_succ]

theorem hbar_end (z : List Char) : HObs g hbar ('|' :: z) (some z) := hobs_lit ['|'] z

theorem hcodeE_bar (z : List Char) : HObs g hcodeE ('|' :: z) none :=
  hobs_of_peg (G := ⟨[]⟩) peg_codeE
    (Shallot.MacroPeg.obs_seq (Shallot.MacroPeg.obs_star_none (Shallot.MacroPeg.obs_char_fail _ (by decide)))
      (Shallot.MacroPeg.obs_char_fail _ (by decide)))

theorem hsiteE_bar (z : List Char) : HObs g hsiteE ('|' :: z) none :=
  hobs_of_peg (G := ⟨[]⟩) peg_siteE
    (Shallot.MacroPeg.obs_seq_none (Shallot.MacroPeg.obs_seq_none
      (Shallot.MacroPeg.obs_seq (Shallot.MacroPeg.obs_star_none (Shallot.MacroPeg.obs_char_fail _ (by decide)))
        (Shallot.MacroPeg.obs_char_fail _ (by decide)))))

end Pieces

/-! ## The scan rules -/

def all1B (h : HExp) : HExp := .alt (HExp.andP hbar) (.seq (HExp.andP (bit1 h)) (.seq hsiteE (rcall 0 [h])))
def all0B (h : HExp) : HExp := .alt (HExp.andP hbar) (.seq (.notP (bit1 h)) (.seq hsiteE (rcall 1 [h])))
def eq1B (a h : HExp) : HExp :=
  .alt (HExp.andP hbar)
    (.seq (.alt (.seq (HExp.andP (bit1 a)) (HExp.andP (bit1 h))) (.seq (.notP (bit1 a)) (.notP (bit1 h))))
      (.seq hsiteE (rcall 2 [a, h])))

/-- The first rules of every grammar built on level-1 numbers. -/
def level1Rules : List HRule :=
  [⟨Ty.p ⇒ Ty.p, lamsT [.p] (all1B (.var 0))⟩,
   ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all0B (.var 0))⟩,
   ⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (eq1B (.var 1) (.var 0))⟩]

/-- `g` starts with the level-1 rules. -/
def HasLevel1 (g : HGrammar) : Prop := ∀ i < 3, g.rules[i]? = level1Rules[i]?

/-- The successor and the predecessor (bit `j` flips iff all later bits are `1`, resp. `0`). -/
def incB (h : HExp) : HExp := newSite (xorE (bit1 h) (.seq hsiteE (rcall 0 [h])))
def decB (h : HExp) : HExp := newSite (xorE (bit1 h) (.seq hsiteE (rcall 1 [h])))

/-- Zero and the largest number. -/
def zeroB : HExp := .seq hcodeE hoptY
def maxB : HExp := .seq (.seq hcodeE hoptY) (.lit ['x'])

/-! ## Substitution into the bodies -/

section Inst

theorem substC_bit1 (σ : List HExp) (k : Nat) (h : HExp) : HExp.substC σ k (bit1 h) = bit1 (HExp.substC σ k h) := rfl

theorem inst_all1B (h : HExp) : HExp.substC [h] 0 (all1B (.var 0)) = all1B h := by
  simp [all1B, bit1, hsemi, hbar, HExp.substC, Shallot.MacroPeg.ExpSpace.substC_rcall]
theorem inst_all0B (h : HExp) : HExp.substC [h] 0 (all0B (.var 0)) = all0B h := by
  simp [all0B, bit1, hsemi, hbar, HExp.substC, Shallot.MacroPeg.ExpSpace.substC_rcall]
theorem inst_eq1B (a h : HExp) : HExp.substC [h, a] 0 (eq1B (.var 1) (.var 0)) = eq1B a h := by
  simp [eq1B, bit1, hsemi, hbar, HExp.substC, Shallot.MacroPeg.ExpSpace.substC_rcall]

theorem substC_incB (σ : List HExp) (k : Nat) (h : HExp) : HExp.substC σ k (incB h) = incB (HExp.substC σ k h) := by
  simp [incB, newSite, xorE, bit1, hsemi, HExp.substC, Shallot.MacroPeg.ExpSpace.substC_rcall]
theorem substC_decB (σ : List HExp) (k : Nat) (h : HExp) : HExp.substC σ k (decB h) = decB (HExp.substC σ k h) := by
  simp [decB, newSite, xorE, bit1, hsemi, HExp.substC, Shallot.MacroPeg.ExpSpace.substC_rcall]

end Inst

/-! ## Level-1 numbers -/

section Level1

variable {g : HGrammar} (hg : HasLevel1 g) (m : Nat) (z : List Char)

local notation "S" => sfxB m z

/-- `A` represents the bit vector `v` on the bit sites. -/
def RepB (g : HGrammar) (m : Nat) (z : List Char) (A : HExp) (v : List Bool) : Prop :=
  HExp.Cl 0 A ∧ v.length = m ∧
    (∀ j < m, HObs g A (sfxB m z j) (some (tapeRest (v.getD j false) (sfxB m z (j + 1))))) ∧
    HObs g A (sfxB m z m) none

/-- `A` represents the level-1 number `x`. -/
def Rep1 (g : HGrammar) (m : Nat) (z : List Char) (A : HExp) (x : Nat) : Prop :=
  RepB g m z A (bitsMSB m x) ∧ x < 2 ^ m

variable {m z}

include hg in
theorem g_all1 : g.rules[0]? = some ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all1B (.var 0))⟩ := hg 0 (by omega)
include hg in
theorem g_all0 : g.rules[1]? = some ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all0B (.var 0))⟩ := hg 1 (by omega)
include hg in
theorem g_eq1 : g.rules[2]? = some ⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (eq1B (.var 1) (.var 0))⟩ := hg 2 (by omega)

theorem bit1_testB {A : HExp} {v : List Bool} (hA : RepB g m z A v) {j : Nat} (hj : j < m) :
    Test g (bit1 A) (S j) (v.getD j false) := by
  have h := hA.2.2.1 j hj
  have hs := hsemi_rest (g := g) (v.getD j false) (S (j + 1))
  cases hv : v.getD j false with
  | true => rw [hv] at h hs; exact ⟨_, hobs_seq_ok h hs⟩
  | false => rw [hv] at h hs; exact hobs_seq_ok h hs

theorem bit1_endB {A : HExp} {v : List Bool} (hA : RepB g m z A v) : HObs g (bit1 A) (S m) none :=
  hobs_seq_fail hA.2.2.2

theorem bar_not_site {j : Nat} (hj : j < m) : HObs g (HExp.andP hbar) (S j) none := by
  rw [sfxB_site z hj]; exact hobs_and_none (hbar_site j _ _)

theorem bar_at_end : HObs g (HExp.andP hbar) (S m) (some (S m)) := by
  rw [sfxB_end]; exact hobs_and_some (hbar_end z)

theorem siteE_stepB {j : Nat} (hj : j < m) {e : HExp} {r : Option (List Char)} (h : HObs g e (S (j + 1)) r) :
    HObs g (.seq hsiteE e) (S j) r := by
  rw [sfxB_site z hj]; exact hobs_seq_ok (hsiteE_ok j _ _) h

theorem test_siteE_stepB {j : Nat} (hj : j < m) {e : HExp} {b : Bool} (h : Test g e (S (j + 1)) b) :
    Test g (.seq hsiteE e) (S j) b := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact ⟨y, siteE_stepB hj hy⟩
  | false => exact siteE_stepB hj h

theorem hsiteE_endB : HObs g hsiteE (S m) none := by rw [sfxB_end]; exact hsiteE_bar z

include hg in
theorem all1_callB {h : HExp} (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs g (all1B h) x r) : HObs g (rcall 0 [h]) x r :=
  hobs_call (g_all1 hg) rfl (fun c hc => by simp at hc; rw [hc]; exact hh)
    (by rw [List.reverse_singleton, inst_all1B]; exact hr)

include hg in
theorem all0_callB {h : HExp} (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs g (all0B h) x r) : HObs g (rcall 1 [h]) x r :=
  hobs_call (g_all0 hg) rfl (fun c hc => by simp at hc; rw [hc]; exact hh)
    (by rw [List.reverse_singleton, inst_all0B]; exact hr)

include hg in
theorem eq_callB {a h : HExp} (ha : HExp.Cl 0 a) (hh : HExp.Cl 0 h) {x : List Char} {r : Option (List Char)}
    (hr : HObs g (eq1B a h) x r) : HObs g (rcall 2 [a, h]) x r :=
  hobs_call (g_eq1 hg) rfl (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ha
      · exact hh)
    (by rw [show [a, h].reverse = [h, a] from rfl, inst_eq1B]; exact hr)

include hg in
/-- `ALL1(h)` at site `i`: all bits from `i` on are `1`. -/
theorem all1_okB {h : HExp} {v : List Bool} (hh : RepB g m z h v) :
    ∀ d i, i + d = m → Test g (rcall 0 [h]) (S i) ((v.drop i).all id) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = m := by omega
    subst hin
    have hv : v.drop i = [] := by simp [hh.2.1]
    rw [hv]
    exact ⟨_, all1_callB hg hh.1 (hobs_alt_ok bar_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < m := by omega
    have hrec := ih (i + 1) (by omega)
    have hbit := bit1_testB hh hlt
    rw [drop_getD (by rw [hh.2.1]; exact hlt), List.all_cons]
    cases hb : v.getD i false with
    | false =>
      rw [hb] at hbit
      exact all1_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt) (hobs_seq_fail (hobs_and_none hbit)))
    | true =>
      rw [hb] at hbit
      obtain ⟨y, hy⟩ := hbit
      simp only [id, Bool.true_and]
      cases hall : (v.drop (i + 1)).all id with
      | true =>
        rw [hall] at hrec
        obtain ⟨u, hu⟩ := hrec
        exact ⟨_, all1_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt)
          (hobs_seq_ok (hobs_and_some hy) (siteE_stepB hlt hu)))⟩
      | false =>
        rw [hall] at hrec
        exact all1_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt)
          (hobs_seq_ok (hobs_and_some hy) (siteE_stepB hlt hrec)))

include hg in
/-- `ALL0(h)` at site `i`: all bits from `i` on are `0`. -/
theorem all0_okB {h : HExp} {v : List Bool} (hh : RepB g m z h v) :
    ∀ d i, i + d = m → Test g (rcall 1 [h]) (S i) ((v.drop i).all (! ·)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = m := by omega
    subst hin
    have hv : v.drop i = [] := by simp [hh.2.1]
    rw [hv]
    exact ⟨_, all0_callB hg hh.1 (hobs_alt_ok bar_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < m := by omega
    have hrec := ih (i + 1) (by omega)
    have hbit := bit1_testB hh hlt
    rw [drop_getD (by rw [hh.2.1]; exact hlt), List.all_cons]
    cases hb : v.getD i false with
    | true =>
      rw [hb] at hbit
      obtain ⟨y, hy⟩ := hbit
      exact all0_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt) (hobs_seq_fail (hobs_not_ok hy)))
    | false =>
      rw [hb] at hbit
      simp only [Bool.not_false, Bool.true_and]
      cases hall : (v.drop (i + 1)).all (! ·) with
      | true =>
        rw [hall] at hrec
        obtain ⟨u, hu⟩ := hrec
        exact ⟨_, all0_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt)
          (hobs_seq_ok (hobs_not_fail hbit) (siteE_stepB hlt hu)))⟩
      | false =>
        rw [hall] at hrec
        exact all0_callB hg hh.1 (hobs_alt_fail (bar_not_site hlt)
          (hobs_seq_ok (hobs_not_fail hbit) (siteE_stepB hlt hrec)))

/-- The two bits at a site agree (a zero-width test). -/
theorem same_obsB {a h : HExp} {va vh : List Bool} (ha : RepB g m z a va) (hh : RepB g m z h vh) {j : Nat}
    (hj : j < m) :
    HObs g (.alt (.seq (HExp.andP (bit1 a)) (HExp.andP (bit1 h))) (.seq (.notP (bit1 a)) (.notP (bit1 h))))
      (S j) (if va.getD j false = vh.getD j false then some (S j) else none) := by
  have hA := bit1_testB ha hj
  have hH := bit1_testB hh hj
  cases hx : va.getD j false <;> cases hy : vh.getD j false <;> rw [hx] at hA <;> rw [hy] at hH <;>
    (try simp only [↓reduceIte, Bool.false_eq_true, Bool.true_eq_false])
  · exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hA)) (hobs_seq_ok (hobs_not_fail hA) (hobs_not_fail hH))
  · obtain ⟨u, hu⟩ := hH
    exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hA)) (hobs_seq_ok (hobs_not_fail hA) (hobs_not_ok hu))
  · obtain ⟨u, hu⟩ := hA
    exact hobs_alt_fail (hobs_seq_ok (hobs_and_some hu) (hobs_and_none hH)) (hobs_seq_fail (hobs_not_ok hu))
  · obtain ⟨u, hu⟩ := hA
    obtain ⟨u', hu'⟩ := hH
    exact hobs_alt_ok (hobs_seq_ok (hobs_and_some hu) (hobs_and_some hu'))

include hg in
/-- `EQ(a, h)` at site `i`: the bits from `i` on agree. -/
theorem eq_okB {a h : HExp} {va vh : List Bool} (ha : RepB g m z a va) (hh : RepB g m z h vh) :
    ∀ d i, i + d = m → Test g (rcall 2 [a, h]) (S i) (decide (va.drop i = vh.drop i)) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i = m := by omega
    subst hin
    have h₁ : va.drop i = [] := by simp [ha.2.1]
    have h₂ : vh.drop i = [] := by simp [hh.2.1]
    rw [h₁, h₂]
    exact ⟨_, eq_callB hg ha.1 hh.1 (hobs_alt_ok bar_at_end)⟩
  | succ d ih =>
    intro i hi
    have hlt : i < m := by omega
    have hrec := ih (i + 1) (by omega)
    have hs := same_obsB ha hh hlt
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
        obtain ⟨u, hu⟩ := hrec
        exact ⟨_, eq_callB hg ha.1 hh.1 (hobs_alt_fail (bar_not_site hlt) (hobs_seq_ok hs (siteE_stepB hlt hu)))⟩
      | false =>
        rw [hall] at hrec
        exact eq_callB hg ha.1 hh.1 (hobs_alt_fail (bar_not_site hlt) (hobs_seq_ok hs (siteE_stepB hlt hrec)))
    · rw [if_neg he] at hs
      simp only [he, false_and, decide_false]
      exact eq_callB hg ha.1 hh.1 (hobs_alt_fail (bar_not_site hlt) (hobs_seq_fail hs))

/-- Reading a site with the bit given by a test. -/
theorem newSite_repB {B : HExp} {nb : Nat → Bool} (hB : ∀ j < m, Test g B (S j) (nb j))
    (hBend : Test g B (S m) false) :
    (∀ j < m, HObs g (newSite B) (S j) (some (tapeRest (nb j) (S (j + 1))))) ∧ HObs g (newSite B) (S m) none := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have h := test_guard (hB j hj) (by rw [sfxB_site z hj]; exact readOne_ok (g := g) j _ _)
      (by rw [sfxB_site z hj]; exact readZero_ok (g := g) j _ _)
    cases hb : nb j <;> rw [hb] at h <;> exact h
  · exact test_guard hBend
      (by rw [sfxB_end]; exact hobs_seq_fail (B := .lit ['x']) (hobs_seq_fail (B := hoptY) (hcodeE_bar z)))
      (by rw [sfxB_end]; exact hobs_seq_fail (B := hoptY) (hcodeE_bar z))

theorem cl_newSiteB {B : HExp} (hB : HExp.Cl 0 B) : HExp.Cl 0 (newSite B) :=
  ⟨⟨hB, ⟨cl_hcodeE 0, cl_hoptY 0⟩, trivial⟩, ⟨hB, cl_hcodeE 0, cl_hoptY 0⟩⟩

include hg in
theorem inc_repB {H : HExp} {v : List Bool} (hH : RepB g m z H v) : RepB g m z (incB H) (incBits v) := by
  have hcl : HExp.Cl 0 (xorE (bit1 H) (.seq hsiteE (rcall 0 [H]))) := by
    have h1 : HExp.Cl 0 (bit1 H) := ⟨hH.1, trivial⟩
    have h2 : HExp.Cl 0 (.seq hsiteE (rcall 0 [H])) :=
      ⟨cl_hsiteE 0, cl_rcall (fun a ha => by simp at ha; rw [ha]; exact hH.1)⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, h2⟩⟩
  have hB : ∀ j < m, Test g (xorE (bit1 H) (.seq hsiteE (rcall 0 [H]))) (S j) ((incBits v).getD j false) := by
    intro j hj
    rw [Shallot.MacroPeg.ExpSpace.incBits_getD v j (by rw [hH.2.1]; exact hj)]
    exact test_xor (bit1_testB hH hj) (test_siteE_stepB hj (all1_okB hg hH (m - (j + 1)) (j + 1) (by omega)))
  have hBend : Test g (xorE (bit1 H) (.seq hsiteE (rcall 0 [H]))) (S m) false :=
    test_xor (p := false) (q := false) (bit1_endB hH) (hobs_seq_fail hsiteE_endB)
  obtain ⟨hs, he⟩ := newSite_repB hB hBend
  exact ⟨cl_newSiteB hcl, by rw [Shallot.MacroPeg.ExpSpace.length_incBits, hH.2.1], hs, he⟩

include hg in
theorem dec_repB {H : HExp} {v : List Bool} (hH : RepB g m z H v) : RepB g m z (decB H) (decBits v) := by
  have hcl : HExp.Cl 0 (xorE (bit1 H) (.seq hsiteE (rcall 1 [H]))) := by
    have h1 : HExp.Cl 0 (bit1 H) := ⟨hH.1, trivial⟩
    have h2 : HExp.Cl 0 (.seq hsiteE (rcall 1 [H])) :=
      ⟨cl_hsiteE 0, cl_rcall (fun a ha => by simp at ha; rw [ha]; exact hH.1)⟩
    exact ⟨⟨h1, h2⟩, ⟨h1, h2⟩⟩
  have hB : ∀ j < m, Test g (xorE (bit1 H) (.seq hsiteE (rcall 1 [H]))) (S j) ((decBits v).getD j false) := by
    intro j hj
    rw [Shallot.MacroPeg.ExpSpace.decBits_getD v j (by rw [hH.2.1]; exact hj)]
    exact test_xor (bit1_testB hH hj) (test_siteE_stepB hj (all0_okB hg hH (m - (j + 1)) (j + 1) (by omega)))
  have hBend : Test g (xorE (bit1 H) (.seq hsiteE (rcall 1 [H]))) (S m) false :=
    test_xor (p := false) (q := false) (bit1_endB hH) (hobs_seq_fail hsiteE_endB)
  obtain ⟨hs, he⟩ := newSite_repB hB hBend
  exact ⟨cl_newSiteB hcl, by rw [Shallot.MacroPeg.ExpSpace.length_decBits, hH.2.1], hs, he⟩

/-! ## As numbers -/

include hg in
theorem isMax_rep1 {A : HExp} {x : Nat} (hA : Rep1 g m z A x) : Test g (rcall 0 [A]) (S 0) (x == 2 ^ m - 1) := by
  have h := all1_okB hg hA.1 m 0 (by omega)
  simp only [List.drop_zero, bitsMSB_all] at h
  have he : allBelow x m = (x == 2 ^ m - 1) := by
    cases hb : allBelow x m
    · exact (beq_eq_false_iff_ne.2 (fun e => by rw [(allBelow_iff hA.2).2 e] at hb; cases hb)).symm
    · exact (beq_iff_eq.2 ((allBelow_iff hA.2).1 hb)).symm
  rwa [he] at h

include hg in
theorem isZero_rep1 {A : HExp} {x : Nat} (hA : Rep1 g m z A x) : Test g (rcall 1 [A]) (S 0) (x == 0) := by
  have h := all0_okB hg hA.1 m 0 (by omega)
  simp only [List.drop_zero, bitsMSB_none] at h
  have he : noneBelow x m = (x == 0) := by
    cases hb : noneBelow x m
    · exact (beq_eq_false_iff_ne.2 (fun e => by rw [(noneBelow_iff hA.2).2 e] at hb; cases hb)).symm
    · exact (beq_iff_eq.2 ((noneBelow_iff hA.2).1 hb)).symm
  rwa [he] at h

include hg in
theorem eq_rep1 {A B : HExp} {x y : Nat} (hA : Rep1 g m z A x) (hB : Rep1 g m z B y) :
    Test g (rcall 2 [A, B]) (S 0) (x == y) := by
  have h := eq_okB hg hA.1 hB.1 m 0 (by omega)
  simp only [List.drop_zero] at h
  have he : decide (bitsMSB m x = bitsMSB m y) = (x == y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : bitsMSB m x ≠ bitsMSB m y := fun e => hxy (bitsMSB_inj hA.2 hB.2 e)
      simp [this, hxy]
  exact he ▸ h

include hg in
theorem inc_rep1 {A : HExp} {x : Nat} (hA : Rep1 g m z A x) (hx : x + 1 < 2 ^ m) : Rep1 g m z (incB A) (x + 1) := by
  have := inc_repB hg hA.1
  rw [incBits_bitsMSB] at this
  exact ⟨this, hx⟩

include hg in
theorem dec_rep1 {A : HExp} {x : Nat} (hA : Rep1 g m z A x) (hx : 0 < x) : Rep1 g m z (decB A) (x - 1) := by
  have := dec_repB hg hA.1
  rw [decBits_bitsMSB m x hx] at this
  exact ⟨this, by have := hA.2; omega⟩

theorem zero_rep1 : Rep1 g m z zeroB 0 := by
  refine ⟨⟨⟨cl_hcodeE 0, cl_hoptY 0⟩, length_bitsMSB m 0, fun j hj => ?_, ?_⟩, Nat.one_le_two_pow⟩
  · have h0 : (bitsMSB m 0).getD j false = false := by rw [bitsMSB_zero]; simp [List.getD_eq_getElem?_getD, hj]
    rw [h0, sfxB_site z hj]
    exact readZero_ok (g := g) j false (S (j + 1))
  · rw [sfxB_end]; exact hobs_seq_fail (hcodeE_bar z)

theorem max_rep1 : Rep1 g m z maxB (2 ^ m - 1) := by
  refine ⟨⟨⟨⟨cl_hcodeE 0, cl_hoptY 0⟩, trivial⟩, length_bitsMSB m _, fun j hj => ?_, ?_⟩,
    Nat.sub_lt (Nat.two_pow_pos m) Nat.one_pos⟩
  · have h1 : (bitsMSB m (2 ^ m - 1)).getD j false = true := by
      rw [bitsMSB_max]; simp [List.getD_eq_getElem?_getD, hj]
    rw [h1, sfxB_site z hj]
    exact readOne_ok (g := g) j false (S (j + 1))
  · rw [sfxB_end]; exact hobs_seq_fail (hobs_seq_fail (hcodeE_bar z))

end Level1

end Shallot.MacroPeg.Levels
