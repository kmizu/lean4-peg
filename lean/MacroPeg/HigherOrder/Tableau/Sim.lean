import MacroPeg.HigherOrder.Tableau.Input

/-!
# The tableau grammar follows the run

For every time `t` below `E m K`, a representation of `t` and of cells `i`, the tests `STATE_q(t)`, `HEAD_τ(t, i)` and
`SYM_{τ,s}(t, i)` decide the state, the head positions and the cells of `M.run (initCfg kt w) t` (`tableau_sim`), by
induction on `t`. At time `t + 1` the state and the symbols under the heads at time `t` select, among the finite
disjunctions of the rule bodies, exactly the case of `TM.step`.
-/

namespace Shallot.MacroPeg.Tableau

open Complexity (TM Cfg Move initCfg bitSym InRange)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.ExpSpace (Test rcall allChainH anyChainH bitC substC_rcall substC_of_cl test_bitC substC_andP)

/-! ## Tests: determinacy, alternatives, finite disjunctions and conjunctions -/

section Tests

variable {g : HGrammar} {x : List Char}

theorem test_det {e : HExp} {b b' : Bool} (h : Test g e x b) (h' : Test g e x b') : b = b' := by
  cases b <;> cases b'
  · rfl
  · obtain ⟨y, hy⟩ := h'; have := hobs_det h hy; cases this
  · obtain ⟨y, hy⟩ := h; have := hobs_det hy h'; cases this
  · rfl

theorem test_alt {A B : HExp} {a b : Bool} (hA : Test g A x a) (hB : Test g B x b) : Test g (.alt A B) x (a || b) := by
  cases a with
  | true => obtain ⟨y, hy⟩ := hA; exact ⟨y, hobs_alt_ok hy⟩
  | false =>
    cases b with
    | true => obtain ⟨y, hy⟩ := hB; exact ⟨y, hobs_alt_fail hA hy⟩
    | false => exact hobs_alt_fail hA hB

theorem test_seq_not_true {Z W : HExp} (hZ : Test g Z x true) : Test g (.seq (.notP Z) W) x false := by
  obtain ⟨y, hy⟩ := hZ; exact hobs_seq_fail (hobs_not_ok hy)

/-- A finite disjunction succeeds iff one of its tests does. -/
theorem test_any : ∀ es : List HExp, (∀ e ∈ es, ∃ v, Test g e x v) →
    ∃ b, Test g (anyChainH es) x b ∧ (b = true ↔ ∃ e ∈ es, Test g e x true)
  | [], _ => ⟨false, hobs_fail, by simp⟩
  | e :: es, h => by
    obtain ⟨v, hv⟩ := h e List.mem_cons_self
    obtain ⟨b, hb, hiff⟩ := test_any es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    refine ⟨v || b, test_alt hv hb, ?_⟩
    constructor
    · intro hvb
      cases v with
      | true => exact ⟨e, List.mem_cons_self, hv⟩
      | false =>
        obtain ⟨e', he', ht⟩ := hiff.1 (by simpa using hvb)
        exact ⟨e', List.mem_cons_of_mem _ he', ht⟩
    · rintro ⟨e', he', ht⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · rw [test_det hv ht]; rfl
      · rw [hiff.2 ⟨e', he', ht⟩, Bool.or_true]

/-- A finite conjunction of lookaheads succeeds iff all its tests do. -/
theorem test_all : ∀ es : List HExp, (∀ e ∈ es, ∃ v, Test g e x v) →
    ∃ b, Test g (allChainH es) x b ∧ (b = true ↔ ∀ e ∈ es, Test g e x true)
  | [], _ => ⟨true, ⟨x, hobs_eps⟩, by simp⟩
  | e :: es, h => by
    obtain ⟨v, hv⟩ := h e List.mem_cons_self
    obtain ⟨b, hb, hiff⟩ := test_all es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    refine ⟨v && b, test_seq_and hv hb, ?_⟩
    constructor
    · intro hvb
      simp only [Bool.and_eq_true] at hvb
      intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · rw [hvb.1] at hv; exact hv
      · exact hiff.1 hvb.2 e' he'
    · intro hall
      have h1 := test_det hv (hall e List.mem_cons_self)
      have h2 := hiff.2 (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
      rw [h1, h2]; rfl

/-- Turn an existential result into the expected Boolean. -/
theorem test_of_iff {e : HExp} {b c : Bool} (h : Test g e x b) (hiff : b = true ↔ c = true) : Test g e x c := by
  have : b = c := Bool.eq_iff_iff.2 hiff
  rwa [this] at h

end Tests

/-! ## Substituting into the builders -/

section Subst

variable {kt : Nat} (M : TM kt) (K : Nat) (σ : List HExp) (k : Nat)

theorem substC_bitC' (b : Bool) : HExp.substC σ k (bitC b) = bitC b := by cases b <;> rfl

theorem substC_readsE (r : List Nat) (tp : HExp) :
    HExp.substC σ k (readsE M K r tp) = readsE M K r (HExp.substC σ k tp) := by
  simp [readsE, Shallot.MacroPeg.ExpSpace.substC_allChainH, substC_rcall, (ops_substC σ k K).1, Function.comp_def]

theorem substC_stateNext (q : Nat) (tp : HExp) :
    HExp.substC σ k (stateNext M K q tp) = stateNext M K q (HExp.substC σ k tp) := by
  simp [stateNext, Shallot.MacroPeg.ExpSpace.substC_anyChainH, substC_rcall, substC_readsE, List.map_flatMap,
    HExp.substC, Function.comp_def]

theorem substC_movedE (τ : Fin kt) (mv : Move) (tp i : HExp) :
    HExp.substC σ k (movedE M K τ mv tp i) = movedE M K τ mv (HExp.substC σ k tp) (HExp.substC σ k i) := by
  cases mv <;> simp [movedE, guardE, HExp.substC, substC_rcall, (ops_substC σ k K).2.1, (ops_substC σ k K).2.2.1,
    (ops_substC σ k K).2.2.2.1, (ops_substC σ k K).2.2.2.2, HExp.failAlways]

theorem substC_headNext (τ : Fin kt) (tp i : HExp) :
    HExp.substC σ k (headNext M K τ tp i) = headNext M K τ (HExp.substC σ k tp) (HExp.substC σ k i) := by
  simp [headNext, Shallot.MacroPeg.ExpSpace.substC_anyChainH, substC_rcall, substC_readsE, substC_movedE,
    List.map_flatMap, HExp.substC, Function.comp_def]

theorem substC_symNext (τ : Fin kt) (s : Nat) (tp i : HExp) :
    HExp.substC σ k (symNext M K τ s tp i) = symNext M K τ s (HExp.substC σ k tp) (HExp.substC σ k i) := by
  simp [symNext, Shallot.MacroPeg.ExpSpace.substC_anyChainH, substC_rcall, substC_readsE, guardE,
    List.map_flatMap, HExp.substC, Function.comp_def]

theorem substC_initE (τ : Fin kt) (s : Nat) (i : HExp) :
    HExp.substC σ k (initE K τ s i) = initE K τ s (HExp.substC σ k i) := by
  unfold initE
  split
  · split
    · simp [substC_rcall, (ops_substC σ k K).1, HExp.substC]
    · rfl
  · exact substC_bitC' σ k _

end Subst

theorem test_true_iff {g : HGrammar} {x : List Char} {e : HExp} {b : Bool} (h : Test g e x b) :
    Test g e x true ↔ b = true :=
  ⟨fun h' => (test_det h' h).symm, fun hb => by rw [hb] at h; exact h⟩

/-! ## The run -/

section Run

variable {kt : Nat} (M : TM kt) (w : List Bool)

/-- The configuration at time `t`. -/
abbrev cfg (t : Nat) : Complexity.Cfg kt := M.run (initCfg kt w) t

theorem cfg_succ (t : Nat) : cfg M w (t + 1) = M.step (cfg M w t) := rfl

theorem move_le (mv : Move) (p : Nat) : mv.apply p ≤ p + 1 := by cases mv <;> simp [Move.apply] <;> omega

/-- A head moves at most one cell per step. -/
theorem pos_le : ∀ (t : Nat) (τ : Fin kt), (cfg M w t).pos τ ≤ t
  | 0, _ => Nat.le_refl 0
  | t + 1, τ => by
    rw [cfg_succ]
    unfold TM.step
    split
    · exact Nat.le_trans (pos_le t τ) (by omega)
    · exact Nat.le_trans (move_le _ _) (by have := pos_le t τ; omega)

/-- The symbols under the heads, as a list. -/
def readL (c : Complexity.Cfg kt) : List Nat := (List.finRange kt).map c.read

theorem rv_readL (c : Complexity.Cfg kt) : rv (readL c) = c.read := by
  funext τ; simp [rv, readL, List.getD_eq_getElem?_getD]

theorem readL_mem (c : Complexity.Cfg kt) (h : InRange M c) : readL c ∈ readsList M.na kt := by
  refine (mem_allVecs _ _ _).2 ⟨by simp [readL], fun s hs => ?_⟩
  simp only [readL, List.mem_map] at hs
  obtain ⟨τ, _, rfl⟩ := hs
  exact List.mem_range.2 (h.2 τ _)

theorem eq_readL {c : Complexity.Cfg kt} {r : List Nat} (hr : r.length = kt) :
    (∀ τ : Fin kt, c.read τ = r.getD τ.val 0) ↔ r = readL c := by
  constructor
  · intro h
    apply List.ext_getElem (by simp [readL, hr])
    intro j h₁ h₂
    have := h ⟨j, by rw [hr] at h₁; exact h₁⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some] at this
    simp [readL, this]
  · rintro rfl τ; simp [readL, List.getD_eq_getElem?_getD]

end Run

/-! ## The tests at one time -/

section Machine

variable {kt : Nat} (M : TM kt) (K m : Nat) (w : List Bool)

local notation "GT" => gT M K
local notation "Z" => inputTail w
local notation "L" => encChars m w

/-- The tests at time `t` decide the configuration at time `t`. -/
def Good (t : Nat) (T : HExp) : Prop :=
  (∀ q < M.nq, Test GT (rcall (rST K q) [T]) L ((cfg M w t).state == q)) ∧
  (∀ (τ : Fin kt) I i, Levels.Rep GT m Z K I i → Test GT (rcall (rHD M K τ) [T, I]) L ((cfg M w t).pos τ == i)) ∧
  (∀ (τ : Fin kt) s, s < M.na → ∀ I i, Levels.Rep GT m Z K I i →
    Test GT (rcall (rSY M K τ s) [T, I]) L ((cfg M w t).cells τ i == s))

variable {M K m w}

theorem cl_two {A B : HExp} (hA : HExp.Cl 0 A) (hB : HExp.Cl 0 B) : AllClosed [A, B] :=
  allClosed_cons hA (allClosed_cons hB allClosed_nil)

theorem st_call {q : Nat} (hq : q < M.nq) {T : HExp} (hT : HExp.Cl 0 T) {b : Bool}
    (h : Test GT (guardE ((ops K).isZero T) (bitC (q == 2)) (stateNext M K q ((ops K).dec T))) L b) :
    Test GT (rcall (rST K q) [T]) L b := by
  refine test_call (g_ST M K hq) rfl (allClosed_cons hT allClosed_nil) ?_
  rw [List.reverse_singleton]
  simpa [stateBody, guardE, HExp.substC, substC_andP, substC_stateNext, substC_bitC', (ops_substC [T] 0 K).2.1,
    (ops_substC [T] 0 K).2.2.1, (ops_substC [T] 0 K).2.2.2.1] using h

theorem hd_call (τ : Fin kt) {T I : HExp} (hT : HExp.Cl 0 T) (hI : HExp.Cl 0 I) {b : Bool}
    (h : Test GT (guardE ((ops K).isZero T) ((ops K).isZero I) (headNext M K τ ((ops K).dec T) I)) L b) :
    Test GT (rcall (rHD M K τ) [T, I]) L b := by
  refine test_call (g_HD M K τ) rfl (cl_two hT hI) ?_
  rw [show [T, I].reverse = [I, T] from rfl]
  simpa [headBody, guardE, HExp.substC, substC_andP, substC_headNext, (ops_substC [I, T] 0 K).2.2.1,
    (ops_substC [I, T] 0 K).2.2.2.1] using h

theorem sy_call (τ : Fin kt) {s : Nat} (hs : s < M.na) {T I : HExp} (hT : HExp.Cl 0 T) (hI : HExp.Cl 0 I) {b : Bool}
    (h : Test GT (guardE ((ops K).isZero T) (initE K τ s I) (symNext M K τ s ((ops K).dec T) I)) L b) :
    Test GT (rcall (rSY M K τ s) [T, I]) L b := by
  refine test_call (g_SY M K τ hs) rfl (cl_two hT hI) ?_
  rw [show [T, I].reverse = [I, T] from rfl]
  simpa [symBody, guardE, HExp.substC, substC_andP, substC_symNext, substC_initE, (ops_substC [I, T] 0 K).2.2.1,
    (ops_substC [I, T] 0 K).2.2.2.1] using h

theorem rd_call (τ : Fin kt) {s : Nat} (hs : s < M.na) {T I : HExp} (hT : HExp.Cl 0 T) (hI : HExp.Cl 0 I) {b : Bool}
    (h : Test GT (.alt (.seq (HExp.andP (rcall (rHD M K τ) [T, I])) (rcall (rSY M K τ s) [T, I]))
      (.seq (.notP ((ops K).isMax I)) (rcall (rRD M K τ s) [T, (ops K).inc I]))) L b) :
    Test GT (rcall (rRD M K τ s) [T, I]) L b := by
  refine test_call (g_RD M K τ hs) rfl (cl_two hT hI) ?_
  rw [show [T, I].reverse = [I, T] from rfl]
  simpa [readBody, HExp.substC, substC_andP, substC_rcall, (ops_substC [I, T] 0 K).2.1,
    (ops_substC [I, T] 0 K).2.2.2.2] using h

/-- **READ**: the head of tape `τ` is at a cell `≥ i` holding `s`. -/
theorem read_loop (hspec : Spec (gT M K) m (inputTail w) K) {t : Nat} {Tp : HExp} (hTp : HExp.Cl 0 Tp) (hG : Good M K m w t Tp) (τ : Fin kt) {s : Nat}
    (hs : s < M.na) (hp : (cfg M w t).pos τ < E m K) :
    ∀ d i I, i + d + 1 = E m K → Levels.Rep GT m Z K I i →
      Test GT (rcall (rRD M K τ s) [Tp, I]) L
        (decide (i ≤ (cfg M w t).pos τ ∧ (cfg M w t).cells τ ((cfg M w t).pos τ) = s)) := by
  intro d
  induction d with
  | zero =>
    intro i I hi hI
    have hcl := (hspec.cl hI).1
    have hmax := hspec.isMax hI
    rw [show (i == E m K - 1) = true by simp; omega] at hmax
    refine rd_call τ hs hTp hcl (test_of_iff (test_alt (test_seq_and (hG.2.1 τ I i hI) (hG.2.2 τ s hs I i hI))
      (test_seq_not_true hmax)) ?_)
    simp only [Bool.or_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨h₁, h₂⟩; subst h₁; exact ⟨Nat.le_refl _, h₂⟩
    · rintro ⟨h₁, h₂⟩
      have : (cfg M w t).pos τ = i := by omega
      rw [this] at h₂ ⊢; exact ⟨rfl, h₂⟩
  | succ d ih =>
    intro i I hi hI
    have hcl := (hspec.cl hI).1
    have hmax := hspec.isMax hI
    rw [show (i == E m K - 1) = false by simp; omega] at hmax
    have hinc := hspec.inc hI (by omega)
    have hrec := ih (i + 1) _ (by omega) hinc
    refine rd_call τ hs hTp hcl (test_of_iff (test_alt (test_seq_and (hG.2.1 τ I i hI) (hG.2.2 τ s hs I i hI))
      (test_seq_not hmax hrec)) ?_)
    simp only [Bool.not_false, Bool.true_and, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
      · subst h₁; exact ⟨Nat.le_refl _, h₂⟩
      · exact ⟨by omega, h₂⟩
    · rintro ⟨h₁, h₂⟩
      by_cases he : (cfg M w t).pos τ = i
      · left; rw [he] at h₂ ⊢; exact ⟨rfl, h₂⟩
      · right; exact ⟨by omega, h₂⟩

/-- The symbol under head `τ` at time `t` is `s`. -/
theorem read_test (hspec : Spec (gT M K) m (inputTail w) K) {t : Nat} {Tp : HExp} (hTp : HExp.Cl 0 Tp) (hG : Good M K m w t Tp) (τ : Fin kt) {s : Nat}
    (hs : s < M.na) (hp : (cfg M w t).pos τ < E m K) :
    Test GT (rcall (rRD M K τ s) [Tp, (ops K).zero]) L ((cfg M w t).read τ == s) := by
  have h := read_loop hspec hTp hG τ hs hp (E m K - 1) 0 _ (by have := E_pos m K; omega) hspec.zero
  refine test_of_iff h ?_
  simp [Complexity.Cfg.read]

/-- The symbols under the heads at time `t` are `r`. -/
theorem reads_test (hspec : Spec (gT M K) m (inputTail w) K) {t : Nat} {Tp : HExp} (hTp : HExp.Cl 0 Tp) (hG : Good M K m w t Tp)
    (hpos : ∀ τ, (cfg M w t).pos τ < E m K) {r : List Nat} (hr : ∀ τ : Fin kt, r.getD τ.val 0 < M.na) :
    Test GT (readsE M K r Tp) L (decide (∀ τ : Fin kt, (cfg M w t).read τ = r.getD τ.val 0)) := by
  obtain ⟨b, hb, hiff⟩ := test_all ((List.finRange kt).map (fun τ => rcall (rRD M K τ (r.getD τ.val 0)) [Tp, (ops K).zero]))
    (fun e he => by
      simp only [List.mem_map] at he
      obtain ⟨τ, _, rfl⟩ := he
      exact ⟨_, read_test hspec hTp hG τ (hr τ) (hpos τ)⟩)
  refine test_of_iff hb (hiff.trans ?_)
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index, forall_apply_eq_imp_iff,
    decide_eq_true_eq]
  exact forall_congr' fun τ => (test_true_iff (read_test hspec hTp hG τ (hr τ) (hpos τ))).trans (by simp)

end Machine

end Shallot.MacroPeg.Tableau
