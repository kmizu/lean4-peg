import MacroPeg.HigherOrder.Levels.Level1
import MacroPeg.HigherOrder.ExpSpace.Sim
import MacroPeg.HigherOrder.Tower

/-!
# Numbers of every level

Level `0` numbers are the level-1 parsers of `Level1.lean` (values below `E 0 = 2^m`). A level-`(i+1)` number `x`
(below `E (i+1) = 2^(E i)`) is a function from level-`i` numbers to zero-width tests: applied to a representation of
`u` it succeeds iff bit `u` of `x` is set (`Rep`). Its type is `lvTy (i+1) = lvTy i ⇒ p`, of order `i+1`.

Every operation is a rule, so that function values are partial applications of rules (no lambda appears inside a rule
body, and substitution never goes under a binder). Block `i` (twelve rules, from `base i`) builds the operations of
level `i+1` from those of level `i`:

* loops over level-`i` numbers: `ALLFROM(P, u)` (all `u' ≥ u` satisfy `P`), `BELOW1(x, u)` / `BELOW0(x, u)` (all bits
  of `x` below `u` are set / clear), with the helpers `NEGAPP(x, u) = ¬ x u` and `IFF(x, y, u) = (x u ↔ y u)`;
* the operations of level `i+1`: `ZERO`, `MAX`, `INC(x) = λu. x u xor BELOW1(x, u)`, `DEC`, `ISZERO`, `ISMAX`, `EQ`.

`spec_succ` proves the operations of level `i+1` correct from those of level `i`; `spec_all` gives every level up to
`K` in a grammar that contains the blocks.
-/

namespace Shallot.MacroPeg.Levels

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.ExpSpace (Test test_true test_false test_and test_not test_guard test_xor rcall xorE cl_rcall
  test_guard_test)

/-! ## Types, sizes and operations -/

/-- The type of level-`i` numbers (order `i`). -/
def lvTy : Nat → HO.Ty
  | 0 => .p
  | i + 1 => lvTy i ⇒ .p

/-- The number of level-`i` values. -/
def E (m i : Nat) : Nat := tower (i + 1) m

theorem E_succ (m i : Nat) : E m (i + 1) = 2 ^ E m i := rfl

/-- The first rule of block `i`. -/
def base (i : Nat) : Nat := 3 + 12 * i

structure LOps where
  zero : HExp
  max : HExp
  inc : HExp → HExp
  dec : HExp → HExp
  isZero : HExp → HExp
  isMax : HExp → HExp
  eq : HExp → HExp → HExp

/-- The operations of level `i`. -/
def ops : Nat → LOps
  | 0 => ⟨zeroB, maxB, incB, decB, fun x => rcall 1 [x], fun x => rcall 0 [x], fun a b => rcall 2 [a, b]⟩
  | i + 1 => ⟨.rule (base i + 5), .rule (base i + 6), fun x => rcall (base i + 7) [x], fun x => rcall (base i + 8) [x],
      fun x => rcall (base i + 9) [x], fun x => rcall (base i + 10) [x], fun a b => rcall (base i + 11) [a, b]⟩

/-! ## Block `i` -/

section Block

variable (i : Nat)

local notation "b" => base i
local notation "τ" => lvTy i

def guardE (C X Y : HExp) : HExp := .alt (.seq (HExp.andP C) X) (.seq (.notP C) Y)

def allFromBody : HExp :=
  .seq (HExp.andP (.app (.var 1) (.var 0)))
    (guardE ((ops i).isMax (.var 0)) .eps (rcall b [.var 1, (ops i).inc (.var 0)]))
def below1Body : HExp :=
  guardE ((ops i).isZero (.var 0)) .eps
    (.seq (HExp.andP (.app (.var 1) ((ops i).dec (.var 0)))) (rcall (b + 1) [.var 1, (ops i).dec (.var 0)]))
def below0Body : HExp :=
  guardE ((ops i).isZero (.var 0)) .eps
    (.seq (.notP (.app (.var 1) ((ops i).dec (.var 0)))) (rcall (b + 2) [.var 1, (ops i).dec (.var 0)]))
def negAppBody : HExp := .notP (.app (.var 1) (.var 0))
def iffBody : HExp :=
  .alt (.seq (HExp.andP (.app (.var 2) (.var 0))) (HExp.andP (.app (.var 1) (.var 0))))
    (.seq (.notP (.app (.var 2) (.var 0))) (.notP (.app (.var 1) (.var 0))))
def incBody : HExp := xorE (.app (.var 1) (.var 0)) (rcall (b + 1) [.var 1, .var 0])
def decBody : HExp := xorE (.app (.var 1) (.var 0)) (rcall (b + 2) [.var 1, .var 0])
def isZeroBody : HExp := rcall b [rcall (b + 3) [.var 0], (ops i).zero]
def isMaxBody : HExp := rcall b [.var 0, (ops i).zero]
def eqBody : HExp := rcall b [rcall (b + 4) [.var 1, .var 0], (ops i).zero]

/-- The twelve rules of block `i`. -/
def blockRules : List HRule :=
  [⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (allFromBody i)⟩,
   ⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (below1Body i)⟩,
   ⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (below0Body i)⟩,
   ⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (negAppBody)⟩,
   ⟨(τ ⇒ .p) ⇒ (τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ ⇒ .p, τ] (iffBody)⟩,
   ⟨τ ⇒ .p, lamsT [τ] HExp.failAlways⟩,
   ⟨τ ⇒ .p, lamsT [τ] .eps⟩,
   ⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (incBody i)⟩,
   ⟨(τ ⇒ .p) ⇒ τ ⇒ .p, lamsT [τ ⇒ .p, τ] (decBody i)⟩,
   ⟨(τ ⇒ .p) ⇒ .p, lamsT [τ ⇒ .p] (isZeroBody i)⟩,
   ⟨(τ ⇒ .p) ⇒ .p, lamsT [τ ⇒ .p] (isMaxBody i)⟩,
   ⟨(τ ⇒ .p) ⇒ (τ ⇒ .p) ⇒ .p, lamsT [τ ⇒ .p, τ ⇒ .p] (eqBody i)⟩]

end Block

/-- `g` contains block `i` at `base i`. -/
def HasBlock (g : HGrammar) (i : Nat) : Prop := ∀ r < 12, g.rules[base i + r]? = (blockRules i)[r]?

/-! ## Representations -/

section Rep

variable (g : HGrammar) (m : Nat) (z : List Char)

local notation "L" => sfxB m z 0

/-- `A` represents the level-`i` number `x`. -/
def Rep : Nat → HExp → Nat → Prop
  | 0, A, x => Rep1 g m z A x
  | i + 1, F, x => HExp.Cl 0 F ∧ x < E m (i + 1) ∧ ∀ A u, Rep i A u → Test g (.app F A) L (x.testBit u)

/-- The operations of level `i` are correct. -/
structure Spec (i : Nat) : Prop where
  cl : ∀ {A x}, Rep g m z i A x → HExp.Cl 0 A ∧ x < E m i
  zero : Rep g m z i (ops i).zero 0
  max : Rep g m z i (ops i).max (E m i - 1)
  inc : ∀ {A x}, Rep g m z i A x → x + 1 < E m i → Rep g m z i ((ops i).inc A) (x + 1)
  dec : ∀ {A x}, Rep g m z i A x → 0 < x → Rep g m z i ((ops i).dec A) (x - 1)
  isZero : ∀ {A x}, Rep g m z i A x → Test g ((ops i).isZero A) L (x == 0)
  isMax : ∀ {A x}, Rep g m z i A x → Test g ((ops i).isMax A) L (x == E m i - 1)
  eq : ∀ {A x B y}, Rep g m z i A x → Rep g m z i B y → Test g ((ops i).eq A B) L (x == y)

variable {g m z}

/-- **Level 0.** -/
theorem spec_zero (hg : HasLevel1 g) : Spec g m z 0 where
  cl := fun hA => ⟨hA.1.1, hA.2⟩
  zero := zero_rep1
  max := max_rep1
  inc := fun hA hx => inc_rep1 hg hA hx
  dec := fun hA hx => dec_rep1 hg hA hx
  isZero := fun hA => isZero_rep1 hg hA
  isMax := fun hA => isMax_rep1 hg hA
  eq := fun hA hB => eq_rep1 hg hA hB

end Rep

/-! ## Tests at the start of the input -/

section TestKit

variable {g : HGrammar} {x : List Char}

theorem test_seq_and {X Y : HExp} {p q : Bool} (hX : Test g X x p) (hY : Test g Y x q) :
    Test g (.seq (HExp.andP X) Y) x (p && q) := by
  cases p with
  | false => exact hobs_seq_fail (hobs_and_none hX)
  | true =>
    obtain ⟨y, hy⟩ := hX
    cases q with
    | true => obtain ⟨y', hy'⟩ := hY; exact ⟨y', hobs_seq_ok (hobs_and_some hy) hy'⟩
    | false => exact hobs_seq_ok (hobs_and_some hy) hY

theorem test_guard_pos {C X Y : HExp} {b : Bool} (hC : Test g C x true) (hX : Test g X x b) :
    Test g (guardE C X Y) x b := by
  obtain ⟨y, hy⟩ := hC
  cases b with
  | true => obtain ⟨y', hy'⟩ := hX; exact ⟨y', HO.guard_pos hy hy'⟩
  | false => exact HO.guard_pos hy hX

theorem test_guard_neg {C X Y : HExp} {b : Bool} (hC : Test g C x false) (hY : Test g Y x b) :
    Test g (guardE C X Y) x b := by
  cases b with
  | true => obtain ⟨y', hy'⟩ := hY; exact ⟨y', HO.guard_neg hC hy'⟩
  | false => exact HO.guard_neg hC hY

theorem test_eps : Test g .eps x true := ⟨x, hobs_eps⟩
theorem test_failAlways : Test g HExp.failAlways x false := hobs_fail

theorem test_call {i : Nat} {τ : HO.Ty} {τs : List HO.Ty} {B : HExp} {as : List HExp}
    (hr : g.rules[i]? = some ⟨τ, lamsT τs B⟩) (hl : τs.length = as.length) (has : AllClosed as) {b : Bool}
    (h : Test g (HExp.substC as.reverse 0 B) x b) : Test g (rcall i as) x b := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact ⟨y, hobs_call hr hl has hy⟩
  | false => exact hobs_call hr hl has h

end TestKit

theorem allClosed_cons {a : HExp} {as : List HExp} (ha : HExp.Cl 0 a) (has : AllClosed as) : AllClosed (a :: as) :=
  fun c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ha
    · exact has c hc

theorem allClosed_nil : AllClosed [] := fun _ h => by simp at h

theorem E_pos (m i : Nat) : 0 < E m i := by
  unfold E; rw [tower_succ]; exact Nat.two_pow_pos _

/-! ## Substituting into the operations -/

open Shallot.MacroPeg.ExpSpace (substC_rcall substC_of_cl cl_emb_peg peg_codeE peg_optY cl_hcodeE cl_hoptY)

theorem cl_zeroB : HExp.Cl 0 zeroB := ⟨cl_hcodeE 0, cl_hoptY 0⟩

theorem ops_substC (σ : List HExp) (k : Nat) : ∀ i : Nat,
    HExp.substC σ k (ops i).zero = (ops i).zero ∧
    (∀ e, HExp.substC σ k ((ops i).inc e) = (ops i).inc (HExp.substC σ k e)) ∧
    (∀ e, HExp.substC σ k ((ops i).dec e) = (ops i).dec (HExp.substC σ k e)) ∧
    (∀ e, HExp.substC σ k ((ops i).isZero e) = (ops i).isZero (HExp.substC σ k e)) ∧
    (∀ e, HExp.substC σ k ((ops i).isMax e) = (ops i).isMax (HExp.substC σ k e))
  | 0 => ⟨substC_of_cl σ cl_zeroB (Nat.zero_le k), fun e => substC_incB σ k e, fun e => substC_decB σ k e,
      fun e => by simp [ops, substC_rcall], fun e => by simp [ops, substC_rcall]⟩
  | _ + 1 => ⟨rfl, fun e => by simp [ops, substC_rcall], fun e => by simp [ops, substC_rcall],
      fun e => by simp [ops, substC_rcall], fun e => by simp [ops, substC_rcall]⟩

/-! ## From level `i` to level `i + 1` -/

section Succ

variable {g : HGrammar} {m : Nat} {z : List Char} {i : Nat} (hb : HasBlock g i) (hs : Spec g m z i)

local notation "L" => sfxB m z 0

include hb in
theorem g_block (r : Nat) (hr : r < 12) : g.rules[base i + r]? = (blockRules i)[r]? := hb r hr

/-- `P` decides the predicate `p` on level-`i` numbers. -/
def PredRep (g : HGrammar) (m : Nat) (z : List Char) (i : Nat) (P : HExp) (p : Nat → Bool) : Prop :=
  HExp.Cl 0 P ∧ ∀ A u, Rep g m z i A u → Test g (.app P A) (sfxB m z 0) (p u)

/-- All of `u, …, E - 1` satisfy `p`. -/
def allFrom (p : Nat → Bool) (u E : Nat) : Bool := (List.range' u (E - u)).all p

theorem allFrom_step (p : Nat → Bool) {u E : Nat} (hu : u < E) :
    allFrom p u E = (p u && if u = E - 1 then true else allFrom p (u + 1) E) := by
  unfold allFrom
  rw [show E - u = (E - (u + 1)) + 1 by omega, List.range'_succ, List.all_cons]
  by_cases h : u = E - 1
  · rw [if_pos h, show E - (u + 1) = 0 by omega]; simp
  · rw [if_neg h]

theorem allFrom_zero_iff (p : Nat → Bool) (E : Nat) : allFrom p 0 E = true ↔ ∀ u < E, p u = true := by
  unfold allFrom
  simp only [List.all_eq_true, List.mem_range'_1, Nat.sub_zero, Nat.zero_add]
  exact ⟨fun h u hu => h u ⟨Nat.zero_le _, hu⟩, fun h u hu => h u hu.2⟩

include hb hs in
/-- **ALLFROM**: all level-`i` numbers from `u` on satisfy `P`. -/
theorem allFrom_ok {P : HExp} {p : Nat → Bool} (hP : PredRep g m z i P p) :
    ∀ d u A, u + d + 1 = E m i → Rep g m z i A u → Test g (rcall (base i) [P, A]) L (allFrom p u (E m i)) := by
  intro d
  induction d with
  | zero =>
    intro u A hu hA
    have hcl := hs.cl hA
    refine test_call (hb 0 (by omega)) rfl (allClosed_cons hP.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hmax := hs.isMax hA
    rw [show (u == E m i - 1) = true by simp; omega] at hmax
    have hbody : HExp.substC [A, P] 0 (allFromBody i) =
        .seq (HExp.andP (.app P A)) (guardE ((ops i).isMax A) .eps (rcall (base i) [P, (ops i).inc A])) := by
      simp [allFromBody, guardE, HExp.substC, substC_rcall, (ops_substC [A, P] 0 i).2.1,
        (ops_substC [A, P] 0 i).2.2.2.2]
    rw [show [P, A].reverse = [A, P] from rfl, hbody, allFrom_step p (by omega), if_pos (by omega),
      Bool.and_true]
    have := test_seq_and (hP.2 A u hA) (test_guard_pos (Y := rcall (base i) [P, (ops i).inc A]) hmax test_eps)
    simpa using this
  | succ d ih =>
    intro u A hu hA
    have hcl := hs.cl hA
    refine test_call (hb 0 (by omega)) rfl (allClosed_cons hP.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hmax := hs.isMax hA
    rw [show (u == E m i - 1) = false by simp; omega] at hmax
    have hinc := hs.inc hA (by omega)
    have hrec := ih (u + 1) _ (by omega) hinc
    have hbody : HExp.substC [A, P] 0 (allFromBody i) =
        .seq (HExp.andP (.app P A)) (guardE ((ops i).isMax A) .eps (rcall (base i) [P, (ops i).inc A])) := by
      simp [allFromBody, guardE, HExp.substC, substC_rcall, (ops_substC [A, P] 0 i).2.1,
        (ops_substC [A, P] 0 i).2.2.2.2]
    rw [show [P, A].reverse = [A, P] from rfl, hbody, allFrom_step p (by omega), if_neg (by omega)]
    exact test_seq_and (hP.2 A u hA) (test_guard_neg hmax hrec)

end Succ

theorem test_seq_not {g : HGrammar} {x : List Char} {X Y : HExp} {p q : Bool} (hX : Test g X x p)
    (hY : Test g Y x q) : Test g (.seq (.notP X) Y) x (!p && q) := by
  cases p with
  | true => obtain ⟨y, hy⟩ := hX; exact hobs_seq_fail (hobs_not_ok hy)
  | false =>
    cases q with
    | true => obtain ⟨y', hy'⟩ := hY; exact ⟨y', hobs_seq_ok (hobs_not_fail hX) hy'⟩
    | false => exact hobs_seq_ok (hobs_not_fail hX) hY

theorem allBelow_succ (x u : Nat) : allBelow x (u + 1) = (x.testBit u && allBelow x u) := by
  simp [allBelow, List.range_succ, List.all_append, Bool.and_comm]

theorem noneBelow_succ (x u : Nat) : noneBelow x (u + 1) = (!x.testBit u && noneBelow x u) := by
  simp [noneBelow, List.range_succ, List.all_append, Bool.and_comm]

section Below

variable {g : HGrammar} {m : Nat} {z : List Char} {i : Nat} (hb : HasBlock g i) (hs : Spec g m z i)

local notation "L" => sfxB m z 0

/-- `X` decides the bits of `x`. -/
def BitRep (g : HGrammar) (m : Nat) (z : List Char) (i : Nat) (X : HExp) (x : Nat) : Prop :=
  HExp.Cl 0 X ∧ ∀ A u, Rep g m z i A u → Test g (.app X A) (sfxB m z 0) (x.testBit u)

include hb hs in
/-- **BELOW1**: all bits of `x` below `u` are set. -/
theorem below1_ok {X : HExp} {x : Nat} (hX : BitRep g m z i X x) :
    ∀ u A, Rep g m z i A u → Test g (rcall (base i + 1) [X, A]) L (allBelow x u) := by
  intro u
  induction u with
  | zero =>
    intro A hA
    have hcl := hs.cl hA
    refine test_call (hb 1 (by omega)) rfl (allClosed_cons hX.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hz := hs.isZero hA
    simp only [beq_self_eq_true] at hz
    have hbody : HExp.substC [A, X] 0 (below1Body i) = guardE ((ops i).isZero A) .eps
        (.seq (HExp.andP (.app X ((ops i).dec A))) (rcall (base i + 1) [X, (ops i).dec A])) := by
      simp [below1Body, guardE, HExp.substC, substC_rcall, (ops_substC [A, X] 0 i).2.2.1,
        (ops_substC [A, X] 0 i).2.2.2.1]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, show allBelow x 0 = true by simp [allBelow]]
    exact test_guard_pos hz test_eps
  | succ u ih =>
    intro A hA
    have hcl := hs.cl hA
    refine test_call (hb 1 (by omega)) rfl (allClosed_cons hX.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hz := hs.isZero hA
    rw [show (u + 1 == 0) = false by simp] at hz
    have hdec := hs.dec hA (by omega)
    simp only [Nat.add_sub_cancel] at hdec
    have hbody : HExp.substC [A, X] 0 (below1Body i) = guardE ((ops i).isZero A) .eps
        (.seq (HExp.andP (.app X ((ops i).dec A))) (rcall (base i + 1) [X, (ops i).dec A])) := by
      simp [below1Body, guardE, HExp.substC, substC_rcall, (ops_substC [A, X] 0 i).2.2.1,
        (ops_substC [A, X] 0 i).2.2.2.1]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, allBelow_succ]
    exact test_guard_neg hz (test_seq_and (hX.2 _ _ hdec) (ih _ hdec))

include hb hs in
/-- **BELOW0**: all bits of `x` below `u` are clear. -/
theorem below0_ok {X : HExp} {x : Nat} (hX : BitRep g m z i X x) :
    ∀ u A, Rep g m z i A u → Test g (rcall (base i + 2) [X, A]) L (noneBelow x u) := by
  intro u
  induction u with
  | zero =>
    intro A hA
    have hcl := hs.cl hA
    refine test_call (hb 2 (by omega)) rfl (allClosed_cons hX.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hz := hs.isZero hA
    simp only [beq_self_eq_true] at hz
    have hbody : HExp.substC [A, X] 0 (below0Body i) = guardE ((ops i).isZero A) .eps
        (.seq (.notP (.app X ((ops i).dec A))) (rcall (base i + 2) [X, (ops i).dec A])) := by
      simp [below0Body, guardE, HExp.substC, substC_rcall, (ops_substC [A, X] 0 i).2.2.1,
        (ops_substC [A, X] 0 i).2.2.2.1]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, show noneBelow x 0 = true by simp [noneBelow]]
    exact test_guard_pos hz test_eps
  | succ u ih =>
    intro A hA
    have hcl := hs.cl hA
    refine test_call (hb 2 (by omega)) rfl (allClosed_cons hX.1 (allClosed_cons hcl.1 allClosed_nil)) ?_
    have hz := hs.isZero hA
    rw [show (u + 1 == 0) = false by simp] at hz
    have hdec := hs.dec hA (by omega)
    simp only [Nat.add_sub_cancel] at hdec
    have hbody : HExp.substC [A, X] 0 (below0Body i) = guardE ((ops i).isZero A) .eps
        (.seq (.notP (.app X ((ops i).dec A))) (rcall (base i + 2) [X, (ops i).dec A])) := by
      simp [below0Body, guardE, HExp.substC, substC_rcall, (ops_substC [A, X] 0 i).2.2.1,
        (ops_substC [A, X] 0 i).2.2.2.1]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, noneBelow_succ]
    exact test_guard_neg hz (test_seq_not (hX.2 _ _ hdec) (ih _ hdec))

end Below

theorem test_notT {g : HGrammar} {x : List Char} {e : HExp} {b : Bool} (h : Test g e x b) :
    Test g (.notP e) x (!b) := by
  cases b with
  | true => obtain ⟨y, hy⟩ := h; exact hobs_not_ok hy
  | false => exact ⟨x, hobs_not_fail h⟩

theorem test_iff {g : HGrammar} {x : List Char} {X Y : HExp} {p q : Bool} (hX : Test g X x p) (hY : Test g Y x q) :
    Test g (.alt (.seq (HExp.andP X) (HExp.andP Y)) (.seq (.notP X) (.notP Y))) x (p == q) := by
  cases p <;> cases q
  · exact ⟨_, hobs_alt_fail (hobs_seq_fail (hobs_and_none hX)) (hobs_seq_ok (hobs_not_fail hX) (hobs_not_fail hY))⟩
  · obtain ⟨u, hu⟩ := hY
    exact hobs_alt_fail (hobs_seq_fail (hobs_and_none hX)) (hobs_seq_ok (hobs_not_fail hX) (hobs_not_ok hu))
  · obtain ⟨u, hu⟩ := hX
    exact hobs_alt_fail (hobs_seq_ok (hobs_and_some hu) (hobs_and_none hY)) (hobs_seq_fail (hobs_not_ok hu))
  · obtain ⟨u, hu⟩ := hX
    obtain ⟨u', hu'⟩ := hY
    exact ⟨_, hobs_alt_ok (hobs_seq_ok (hobs_and_some hu) (hobs_and_some hu'))⟩

theorem bool_eq_of_iff {b c : Bool} {P : Prop} (hb : b = true ↔ P) (hc : c = true ↔ P) : b = c :=
  Bool.eq_iff_iff.2 (hb.trans hc.symm)

section SpecSucc

variable {g : HGrammar} {m : Nat} {z : List Char} {i : Nat} (hb : HasBlock g i) (hs : Spec g m z i)

local notation "L" => sfxB m z 0

theorem cl_pair {X A : HExp} (hX : HExp.Cl 0 X) (hA : HExp.Cl 0 A) : AllClosed [X, A] :=
  allClosed_cons hX (allClosed_cons hA allClosed_nil)

include hb hs in
/-- **From level `i` to level `i + 1`.** -/
theorem spec_succ : Spec g m z (i + 1) where
  cl := fun hF => ⟨hF.1, hF.2.1⟩
  zero := ⟨trivial, E_pos m (i + 1), fun A u hA => by
    refine test_call (hb 5 (by omega)) rfl (allClosed_cons (hs.cl hA).1 allClosed_nil) ?_
    rw [Nat.zero_testBit]; exact test_failAlways⟩
  max := ⟨trivial, Nat.sub_lt (E_pos m (i + 1)) Nat.one_pos, fun A u hA => by
    refine test_call (hb 6 (by omega)) rfl (allClosed_cons (hs.cl hA).1 allClosed_nil) ?_
    have hu := (hs.cl hA).2
    rw [E_succ, (eq_max_iff_testBit (E := E m i) (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)).1 rfl u hu]
    exact test_eps⟩
  inc := fun {X x} hF hx => ⟨cl_rcall (fun a ha => by simp at ha; rw [ha]; exact hF.1), hx, fun A u hA => by
    have hcl := (hs.cl hA).1
    refine test_call (hb 7 (by omega)) rfl (cl_pair hF.1 hcl) ?_
    have hbody : HExp.substC [A, X] 0 (incBody i) = xorE (.app X A) (rcall (base i + 1) [X, A]) := by
      simp [incBody, xorE, HExp.substC, substC_rcall]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, testBit_succ]
    exact test_xor (hF.2.2 A u hA) (below1_ok hb hs ⟨hF.1, hF.2.2⟩ u A hA)⟩
  dec := fun {X x} hF hx => ⟨cl_rcall (fun a ha => by simp at ha; rw [ha]; exact hF.1),
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) hF.2.1, fun A u hA => by
    have hcl := (hs.cl hA).1
    refine test_call (hb 8 (by omega)) rfl (cl_pair hF.1 hcl) ?_
    have hbody : HExp.substC [A, X] 0 (decBody i) = xorE (.app X A) (rcall (base i + 2) [X, A]) := by
      simp [decBody, xorE, HExp.substC, substC_rcall]
    rw [show [X, A].reverse = [A, X] from rfl, hbody, testBit_pred x u hx]
    exact test_xor (hF.2.2 A u hA) (below0_ok hb hs ⟨hF.1, hF.2.2⟩ u A hA)⟩
  isZero := fun {X x} hF => by
    refine test_call (hb 9 (by omega)) rfl (allClosed_cons hF.1 allClosed_nil) ?_
    have hbody : HExp.substC [X] 0 (isZeroBody i) = rcall (base i) [rcall (base i + 3) [X], (ops i).zero] := by
      simp [isZeroBody, HExp.substC, substC_rcall, (ops_substC [X] 0 i).1]
    rw [List.reverse_singleton, hbody]
    have hP : PredRep g m z i (rcall (base i + 3) [X]) (fun u => !x.testBit u) :=
      ⟨cl_rcall (fun a ha => by simp at ha; rw [ha]; exact hF.1), fun A u hA => by
        refine test_call (hb 3 (by omega)) rfl (cl_pair hF.1 (hs.cl hA).1) ?_
        have hbody' : HExp.substC [A, X] 0 negAppBody = .notP (.app X A) := by simp [negAppBody, HExp.substC]
        rw [show [X, A].reverse = [A, X] from rfl, hbody']
        exact test_notT (hF.2.2 A u hA)⟩
    have h := allFrom_ok hb hs hP (E m i - 1) 0 _ (by have := E_pos m i; omega) hs.zero
    have he : allFrom (fun u => !x.testBit u) 0 (E m i) = (x == 0) := by
      apply bool_eq_of_iff ((allFrom_zero_iff _ _).trans _) (beq_iff_eq)
      rw [eq_zero_iff_testBit (E := E m i) hF.2.1]
      simp
    rwa [he] at h
  isMax := fun {X x} hF => by
    refine test_call (hb 10 (by omega)) rfl (allClosed_cons hF.1 allClosed_nil) ?_
    have hbody : HExp.substC [X] 0 (isMaxBody i) = rcall (base i) [X, (ops i).zero] := by
      simp [isMaxBody, HExp.substC, substC_rcall, (ops_substC [X] 0 i).1]
    rw [List.reverse_singleton, hbody]
    have h := allFrom_ok hb hs (p := x.testBit) ⟨hF.1, hF.2.2⟩ (E m i - 1) 0 _ (by have := E_pos m i; omega) hs.zero
    have he : allFrom x.testBit 0 (E m i) = (x == E m (i + 1) - 1) := by
      apply bool_eq_of_iff ((allFrom_zero_iff _ _).trans ?_) beq_iff_eq
      rw [E_succ, eq_max_iff_testBit (E := E m i) hF.2.1]
    rwa [he] at h
  eq := fun {X x Y y} hF hG => by
    refine test_call (hb 11 (by omega)) rfl (cl_pair hF.1 hG.1) ?_
    have hbody : HExp.substC [Y, X] 0 (eqBody i) = rcall (base i) [rcall (base i + 4) [X, Y], (ops i).zero] := by
      simp [eqBody, HExp.substC, substC_rcall, (ops_substC [Y, X] 0 i).1]
    rw [show [X, Y].reverse = [Y, X] from rfl, hbody]
    have hP : PredRep g m z i (rcall (base i + 4) [X, Y]) (fun u => x.testBit u == y.testBit u) :=
      ⟨cl_rcall (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact hF.1
          · exact hG.1), fun A u hA => by
        refine test_call (hb 4 (by omega)) rfl (allClosed_cons hF.1 (cl_pair hG.1 (hs.cl hA).1)) ?_
        have hbody' : HExp.substC [A, Y, X] 0 iffBody = .alt (.seq (HExp.andP (.app X A)) (HExp.andP (.app Y A)))
            (.seq (.notP (.app X A)) (.notP (.app Y A))) := by simp [iffBody, HExp.substC]
        rw [show [X, Y, A].reverse = [A, Y, X] from rfl, hbody']
        exact test_iff (hF.2.2 A u hA) (hG.2.2 A u hA)⟩
    have h := allFrom_ok hb hs hP (E m i - 1) 0 _ (by have := E_pos m i; omega) hs.zero
    have he : allFrom (fun u => x.testBit u == y.testBit u) 0 (E m i) = (x == y) := by
      apply bool_eq_of_iff ((allFrom_zero_iff _ _).trans _) beq_iff_eq
      rw [eq_iff_testBit (E := E m i) hF.2.1 hG.2.1]
      simp
    rwa [he] at h

end SpecSucc

/-! ## All levels -/

/-- `g` contains the level-1 rules and blocks `0, …, K-1`. -/
def HasLevels (g : HGrammar) (K : Nat) : Prop := HasLevel1 g ∧ ∀ i < K, HasBlock g i

/-- **Every level up to `K` is correct.** -/
theorem spec_all {g : HGrammar} {K : Nat} (hg : HasLevels g K) (m : Nat) (z : List Char) :
    ∀ i ≤ K, Spec g m z i
  | 0, _ => spec_zero hg.1
  | i + 1, hi => spec_succ (hg.2 i (by omega)) (spec_all hg m z i (by omega))

end Shallot.MacroPeg.Levels
