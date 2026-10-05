import MacroPeg.HigherOrder.Tableau.Lookup

/-!
# Reading the input

`FT(Kc, X)` scans the input sites for the one whose unary code is `Kc` and tests `X` there (`ft_test`).
`INPUT_s(i, c, Kc)` walks the input sites with a counter `c` and the code `Kc` of site `c`; it decides whether cell
`i` of the initial tape `0` holds `s` (`input_test`): the input bit at `i` if `i < |w|`, the blank otherwise.
-/

namespace Shallot.MacroPeg.Tableau

open Complexity (TM initCfg bitSym)
open Shallot.MacroPeg (MacroObs codeStr cNum codeP codeE)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.ExpSpace (Test rcall hcodeE hsiteE bitC substC_rcall substC_of_cl peg_codeE peg_siteE
  cl_emb_peg hobs_lit cl_rcall test_bitC test_guard_test)

/-! ## Unary codes -/

/-- The unary code of input site `j`, as a parser. -/
def kc (j : Nat) : HExp := emb 0 (cNum j)

theorem kc_succ (j : Nat) : kc (j + 1) = .seq (kc j) hone := rfl

theorem peg_cNum : ∀ j, PegOnly (cNum j)
  | 0 => trivial
  | j + 1 => ⟨peg_cNum j, trivial⟩

theorem cl_kc (j : Nat) : HExp.Cl 0 (kc j) := cl_emb_peg _ (peg_cNum j)

theorem code_match {g : HGrammar} (k j : Nat) (rest : List Char) :
    HObs g (.seq (kc k) hzero) (codeStr j ++ rest) (if j = k then some rest else none) :=
  hobs_of_peg (G := ⟨[]⟩) (e := codeP k) ⟨peg_cNum k, trivial⟩ (Shallot.MacroPeg.codeP_match k j rest)

theorem code_hash {g : HGrammar} (k : Nat) (rest : List Char) : HObs g (.seq (kc k) hzero) ('#' :: rest) none :=
  hobs_of_peg (G := ⟨[]⟩) (e := codeP k) ⟨peg_cNum k, trivial⟩ (Shallot.MacroPeg.codeP_hash k rest)

/-! ## Pieces on input sites -/

section Pieces

variable {g : HGrammar}

theorem hcodeE_code (j : Nat) (rest : List Char) : HObs g hcodeE (codeStr j ++ rest) (some rest) :=
  hobs_of_peg (G := ⟨[]⟩) peg_codeE (Shallot.MacroPeg.codeE_ok j rest)

theorem inSiteE_ok (j : Nat) (b : Bool) (rest : List Char) : HObs g inSiteE (inSite j b ++ rest) (some rest) := by
  unfold inSite inSiteE
  rw [List.append_assoc]
  refine hobs_seq_ok (hcodeE_code j _) ?_
  cases b
  · exact hobs_alt_ok (hobs_lit ['a'] rest)
  · exact hobs_alt_fail (hobs_of_peg (G := ⟨[]⟩) (e := .lit ['a']) trivial
      (Shallot.MacroPeg.obs_char_fail rest (by decide))) (hobs_lit ['b'] rest)

theorem inSiteE_hash (rest : List Char) : HObs g inSiteE ('#' :: rest) none :=
  hobs_seq_fail (hobs_of_peg (G := ⟨[]⟩) peg_codeE
    (Shallot.MacroPeg.obs_seq (Shallot.MacroPeg.obs_star_none (Shallot.MacroPeg.obs_char_fail _ (by decide)))
      (Shallot.MacroPeg.obs_char_fail _ (by decide))))

/-- The symbol test at a site: `s` is the input symbol of the site. -/
theorem symE_test (s j : Nat) (b : Bool) (rest : List Char) : Test g (symE s) (inSite j b ++ rest) (s == bitSym b) := by
  unfold inSite
  rw [List.append_assoc]
  have hc := hcodeE_code (g := g) j ([if b then 'b' else 'a'] ++ rest)
  have hab : HObs g (.lit ['a']) (['b'] ++ rest) none :=
    hobs_of_peg (G := ⟨[]⟩) (e := .lit ['a']) trivial (Shallot.MacroPeg.obs_char_fail rest (by decide))
  have hba : HObs g (.lit ['b']) (['a'] ++ rest) none :=
    hobs_of_peg (G := ⟨[]⟩) (e := .lit ['b']) trivial (Shallot.MacroPeg.obs_char_fail rest (by decide))
  unfold symE
  by_cases h1 : s = 1
  · subst h1
    cases b
    · exact ⟨_, hobs_seq_ok hc (hobs_lit ['a'] rest)⟩
    · exact hobs_seq_ok hc hab
  · by_cases h2 : s = 2
    · subst h2
      cases b
      · exact hobs_seq_ok hc hba
      · exact ⟨_, hobs_seq_ok hc (hobs_lit ['b'] rest)⟩
    · rw [if_neg h1, if_neg h2]
      have : (s == bitSym b) = false := by cases b <;> simp [bitSym] <;> omega
      rw [this]; exact hobs_fail

end Pieces

/-! ## Finding a site -/

section Find

variable {kt : Nat} (M : TM kt) (K : Nat)

local notation "GT" => gT M K

theorem ft_call {Kc X : HExp} (hK : HExp.Cl 0 Kc) (hX : HExp.Cl 0 X) {x : List Char} {b : Bool}
    (h : Test GT (.alt (.seq (HExp.andP (.seq Kc hzero)) (HExp.andP X)) (.seq inSiteE (rcall (rFT K) [Kc, X]))) x b) :
    Test GT (rcall (rFT K) [Kc, X]) x b := by
  refine test_call (g_FT M K) rfl (allClosed_cons hK (allClosed_cons hX allClosed_nil)) ?_
  have hb : HExp.substC [X, Kc] 0 (ftsBody K) =
      .alt (.seq (HExp.andP (.seq Kc hzero)) (HExp.andP X)) (.seq inSiteE (rcall (rFT K) [Kc, X])) := by
    simp [ftsBody, HExp.substC, substC_rcall, hzero, inSiteE, hcodeE,
      substC_of_cl [X, Kc] (cl_emb_peg _ peg_codeE) (Nat.zero_le 0)]
  rw [show [Kc, X].reverse = [X, Kc] from rfl, hb]
  exact h

/-- **FT**: scanning the sites from `j`, the site with code `k` is found iff it is there, and then `X` is tested. -/
theorem ft_test {X : HExp} (hX : HExp.Cl 0 X) (k : Nat) {bX : Bool} :
    ∀ (v : List Bool) (j : Nat), (j ≤ k → k < j + v.length → Test GT X (inSitesFrom k (v.drop (k - j)) ++ ['#']) bX) →
      Test GT (rcall (rFT K) [kc k, X]) (inSitesFrom j v ++ ['#'])
        (if j ≤ k ∧ k < j + v.length then bX else false)
  | [], j, _ => by
    simp only [List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
    refine ft_call M K (cl_kc k) hX ?_
    exact hobs_alt_fail (hobs_seq_fail (hobs_and_none (code_hash k []))) (hobs_seq_fail (inSiteE_hash []))
  | b :: v, j, hXk => by
    refine ft_call M K (cl_kc k) hX ?_
    simp only [inSitesFrom, List.append_assoc]
    have hc := code_match (g := gT M K) k j ([if b then 'b' else 'a'] ++ (inSitesFrom (j + 1) v ++ ['#']))
    have hrec := ft_test hX k v (j + 1) (fun h₁ h₂ => by
      have := hXk (by omega) (by simp; omega)
      rwa [show k - j = (k - (j + 1)) + 1 by omega, List.drop_succ_cons] at this)
    have hskip := inSiteE_ok (g := gT M K) j b (inSitesFrom (j + 1) v ++ ['#'])
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl] at hc
      have hX' := hXk (Nat.le_refl _) (by simp)
      simp only [Nat.sub_self, List.drop_zero, inSitesFrom, List.append_assoc] at hX'
      have hc' : HObs GT (.seq (kc j) hzero) (inSite j b ++ (inSitesFrom (j + 1) v ++ ['#']))
          (some ([if b then 'b' else 'a'] ++ (inSitesFrom (j + 1) v ++ ['#']))) := by
        unfold inSite; simpa [List.append_assoc] using hc
      rw [if_neg (by omega)] at hrec
      rw [if_pos (by simp)]
      cases bX with
      | true => obtain ⟨y, hy⟩ := hX'; exact ⟨_, hobs_alt_ok (hobs_seq_ok (hobs_and_some hc') (hobs_and_some hy))⟩
      | false =>
        exact hobs_alt_fail (hobs_seq_ok (hobs_and_some hc') (hobs_and_none hX')) (hobs_seq_ok hskip hrec)
    · rw [if_neg hjk] at hc
      have hc' : HObs GT (.seq (kc k) hzero) (inSite j b ++ (inSitesFrom (j + 1) v ++ ['#'])) none := by
        unfold inSite; simpa [List.append_assoc] using hc
      have hcond : (j ≤ k ∧ k < j + (b :: v).length) ↔ (j + 1 ≤ k ∧ k < j + 1 + v.length) := by
        simp only [List.length_cons]; omega
      simp only [show (j ≤ k ∧ k < j + (b :: v).length) = (j + 1 ≤ k ∧ k < j + 1 + v.length) from propext hcond]
      cases hb : (if j + 1 ≤ k ∧ k < j + 1 + v.length then bX else false) with
      | true =>
        rw [hb] at hrec; obtain ⟨y, hy⟩ := hrec
        exact ⟨_, hobs_alt_fail (hobs_seq_fail (hobs_and_none hc')) (hobs_seq_ok hskip hy)⟩
      | false =>
        rw [hb] at hrec
        exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hc')) (hobs_seq_ok hskip hrec)

end Find

/-! ## Skipping the bit sites -/

theorem star_bits {g : HGrammar} (z : List Char) : ∀ c j, HObs g (.star hsiteE) (bitsFrom j c ++ '|' :: z) (some ('|' :: z))
  | 0, _ => hobs_star_fail (hsiteE_bar z)
  | c + 1, j => by
    simp only [bitsFrom, List.append_assoc]
    exact hobs_star_ok (Shallot.MacroPeg.ExpSpace.hsiteE_ok j false _) (star_bits z c (j + 1))

theorem skip_ok {g : HGrammar} (m : Nat) (w : List Bool) : HObs g skipE (encChars m w) (some (inputTail w)) := by
  unfold encChars sfxB skipE
  exact hobs_seq_ok (star_bits _ _ _) (hobs_lit ['|'] _)

theorem test_seq_some {g : HGrammar} {A B : HExp} {x y : List Char} {b : Bool} (hA : HObs g A x (some y))
    (hB : Test g B y b) : Test g (.seq A B) x b := by
  cases b with
  | true => obtain ⟨u, hu⟩ := hB; exact ⟨u, hobs_seq_ok hA hu⟩
  | false => exact hobs_seq_ok hA hB

theorem inSitesFrom_drop (w : List Bool) {c : Nat} (hc : c < w.length) :
    inSitesFrom c (w.drop c) = inSite c (w[c]'hc) ++ inSitesFrom (c + 1) (w.drop (c + 1)) := by
  rw [List.drop_eq_getElem_cons hc]; rfl

/-! ## The initial tape `0` -/

theorem nat_beq_comm (a b : Nat) : (a == b) = (b == a) := by
  by_cases h : a = b
  · subst h; rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

/-- Cell `i` of the initial tape `0`. -/
def initCell (w : List Bool) (i : Nat) : Nat := match w[i]? with | some b => bitSym b | none => 0

section Input

variable {kt : Nat} (M : TM kt) (K : Nat) (m : Nat) (w : List Bool)

local notation "GT" => gT M K
local notation "L" => encChars m w

/-- **FT from the start**: the site with code `k` exists iff `k < |w|`, and then `X` is tested there. -/
theorem ftE_test {X : HExp} (hX : HExp.Cl 0 X) (k : Nat) {bX : Bool}
    (hXk : k < w.length → Test GT X (inSitesFrom k (w.drop k) ++ ['#']) bX) :
    Test GT (ftE K (kc k) X) L (if k < w.length then bX else false) := by
  have h := ft_test M K hX k w 0 (fun _ h₂ => by simpa using hXk (by omega))
  simp only [Nat.zero_le, true_and, Nat.zero_add] at h
  exact test_seq_some (skip_ok m w) h

theorem cl_ftE {Kc X : HExp} (hK : HExp.Cl 0 Kc) (hX : HExp.Cl 0 X) : HExp.Cl 0 (ftE K Kc X) :=
  ⟨⟨cl_emb_peg _ (show PegOnly (.star Shallot.MacroPeg.siteE) from peg_siteE), trivial⟩,
    cl_rcall (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact hK
      · exact hX)⟩

theorem cl_symE (s : Nat) : HExp.Cl 0 (symE s) := by
  unfold symE; split
  · exact ⟨cl_emb_peg _ peg_codeE, trivial⟩
  · split
    · exact ⟨cl_emb_peg _ peg_codeE, trivial⟩
    · exact trivial

theorem ops_eq_substC (σ : List HExp) (k i : Nat) (a b : HExp) :
    HExp.substC σ k ((ops i).eq a b) = (ops i).eq (HExp.substC σ k a) (HExp.substC σ k b) := by
  cases i <;> simp [ops, substC_rcall]

theorem substC_ftE (σ : List HExp) (k : Nat) (Kc X : HExp) :
    HExp.substC σ k (ftE K Kc X) = ftE K (HExp.substC σ k Kc) (HExp.substC σ k X) := by
  have h : HExp.substC σ k skipE = skipE :=
    substC_of_cl σ (m := 0) ⟨cl_emb_peg _ (show PegOnly (.star Shallot.MacroPeg.siteE) from peg_siteE), trivial⟩
      (Nat.zero_le k)
  simp [ftE, HExp.substC, substC_rcall, h]

/-- **INPUT**: walking the input sites from `c`, the loop decides whether cell `i` of the initial tape holds `s`. -/
theorem input_test (hspec : Spec GT m (inputTail w) K) (hn : w.length < E m K) {s : Nat} (hs : s < 3) {I : HExp}
    {i : Nat} (hI : Levels.Rep GT m (inputTail w) K I i) :
    ∀ d c C, c + d = w.length → c ≤ i → Levels.Rep GT m (inputTail w) K C c →
      Test GT (rcall (rIN K s) [I, C, kc c]) L (initCell w i == s) := by
  intro d
  induction d with
  | zero =>
    intro c C hc hci hC
    have hcl := (hspec.cl hI).1
    refine test_call (g_IN M K hs) rfl (allClosed_cons hcl (allClosed_cons (hspec.cl hC).1
      (allClosed_cons (cl_kc c) allClosed_nil))) ?_
    rw [show [I, C, kc c].reverse = [kc c, C, I] from rfl]
    simp only [inBody, guardE, HExp.substC, substC_ftE, ops_eq_substC, (ops_substC _ 0 K).2.1, substC_rcall,
      List.map_cons, List.map_nil, substC_of_cl _ (cl_symE s) (Nat.zero_le 0),
      Shallot.MacroPeg.ExpSpace.substC_andP, hone]
    have hb : HExp.substC [kc c, C, I] 0 (bitC (s == 0)) = bitC (s == 0) := by cases (s == 0) <;> rfl
    simp only [hb, List.getD_cons_zero, List.getD_cons_succ, Nat.lt_irrefl, ↓reduceIte, Nat.not_lt_zero,
      Nat.sub_zero, show ¬ (1 : Nat) < 0 from by omega]
    have hft := ftE_test M K m w (X := .eps) (bX := true) trivial c (fun _ => ⟨_, hobs_eps⟩)
    rw [if_neg (by omega)] at hft
    have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
    have hcell : initCell w i = 0 := by simp [initCell, hnone]
    rw [hcell, show ((0 : Nat) == s) = (s == 0) from nat_beq_comm 0 s]
    exact test_guard_neg hft (test_bitC (s == 0) L)
  | succ d ih =>
    intro c C hc hci hC
    have hcl := (hspec.cl hI).1
    refine test_call (g_IN M K hs) rfl (allClosed_cons hcl (allClosed_cons (hspec.cl hC).1
      (allClosed_cons (cl_kc c) allClosed_nil))) ?_
    rw [show [I, C, kc c].reverse = [kc c, C, I] from rfl]
    simp only [inBody, guardE, HExp.substC, substC_ftE, ops_eq_substC, (ops_substC _ 0 K).2.1, substC_rcall,
      List.map_cons, List.map_nil, substC_of_cl _ (cl_symE s) (Nat.zero_le 0),
      Shallot.MacroPeg.ExpSpace.substC_andP, hone]
    have hb : HExp.substC [kc c, C, I] 0 (bitC (s == 0)) = bitC (s == 0) := by cases (s == 0) <;> rfl
    simp only [hb, List.getD_cons_zero, List.getD_cons_succ, Nat.lt_irrefl, ↓reduceIte, Nat.not_lt_zero,
      Nat.sub_zero, show ¬ (1 : Nat) < 0 from by omega]
    have hcn : c < w.length := by omega
    have hft := ftE_test M K m w (X := .eps) (bX := true) trivial c (fun _ => ⟨_, hobs_eps⟩)
    rw [if_pos hcn] at hft
    refine test_guard_pos hft ?_
    have heq := hspec.eq hI hC
    by_cases hic : i = c
    · subst hic
      rw [show (i == i) = true from beq_self_eq_true i] at heq
      refine test_guard_pos heq ?_
      have hsym := ftE_test M K m w (cl_symE s) i (bX := s == bitSym (w[i]'hcn)) (fun h => by
        rw [inSitesFrom_drop w h, List.append_assoc]; exact symE_test s i _ _)
      rw [if_pos hcn] at hsym
      have hcell : initCell w i = bitSym (w[i]'hcn) := by simp [initCell, List.getElem?_eq_getElem hcn]
      rw [hcell, nat_beq_comm]
      exact hsym
    · rw [show (i == c) = false from by simp [hic]] at heq
      refine test_guard_neg heq ?_
      have hinc := hspec.inc hC (by omega)
      rw [show HExp.seq (kc c) (.lit ['1']) = kc (c + 1) from rfl]
      exact ih (c + 1) _ (by omega) (by omega) hinc

end Input

end Shallot.MacroPeg.Tableau
