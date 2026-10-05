import MacroPeg.Properties.Observation
import MacroPeg.Determinism

/-!
# First-order call-by-name Macro PEG is PSPACE-hard

A single fixed first-order call-by-name Macro PEG `qbfG` evaluates quantified Boolean formulas: for every QBF `φ` in
prenex CNF, `qbfG` consumes the whole encoding `enc φ` iff `φ` is true, and fails on it otherwise (`qbf_reduction`).
The encoding has polynomial length (`enc_length`) and is computed by a simple structural map, so `L(qbfG)` is
PSPACE-hard under polynomial-time many-one reductions, given the PSPACE-completeness of TQBF (Stockmeyer–Meyer 1973,
an external fact not formalized here). Plain PEG is recognized in linear time by packrat parsing, so unless P = PSPACE
this fixed first-order Macro PEG defines a language no plain PEG defines.

The grammar (rule numbers in brackets):

```
[0] Q(C, A) ← "A" &Q(C "1", A / C "0") Q(C "1", A)
            / "E" (Q(C "1", A / C "0") / Q(C "1", A))
            / "#" M(A)
[1] M(A)    ← (Cl(A) ";")* !.
[2] Cl(A)   ← TL(A) Lit* / FL(A) Cl(A)
[3] TL(A)   ← "+" &A Code / "-" !A Code
[4] FL(A)   ← "+" !A Code / "-" &A Code
[5] Lit     ← ("+" / "-") Code
[6] Code    ← "1"* "0"
start: Q(ε, !ε)
```

`C = "1"^k` counts the quantifiers read so far, and `A` is the assignment: a choice of the codes `1^j 0` of the variables
set to true (`A / C "0"` sets variable `k` to true). A literal `+v` is true iff `&A` succeeds on the code of `v`. The
arguments are built (`C "1"`, `A / C "0"`), so the grammar is outside the finite-argument fragment, as it must be.
-/

namespace Shallot.MacroPeg

/-! ## Composition rules for observations (any grammar, call-by-name) -/

section Obs

variable {g : MGrammar}

theorem obs_eps (x : List Char) : MacroObs g .eps x (some x) := ⟨_, .eps x, rfl⟩

theorem stripPrefix_append : ∀ (s rest : List Char), Shallot.stripPrefix? s (s ++ rest) = some rest
  | [], _ => rfl
  | c :: s, rest => by simp [Shallot.stripPrefix?, Shallot.beqChar, stripPrefix_append s rest]

theorem obs_lit_ok (s rest : List Char) : MacroObs g (.lit s) (s ++ rest) (some rest) :=
  ⟨_, .litOk s _ rest (stripPrefix_append s rest), rfl⟩

theorem obs_lit_fail {s x : List Char} (h : Shallot.stripPrefix? s x = none) : MacroObs g (.lit s) x none :=
  ⟨_, .litFail s x h, rfl⟩

theorem obs_char_fail {c d : Char} (rest : List Char) (h : Shallot.beqChar c d = false) :
    MacroObs g (.lit [c]) (d :: rest) none :=
  obs_lit_fail (by simp [Shallot.stripPrefix?, h])

theorem obs_char_nil (c : Char) : MacroObs g (.lit [c]) [] none := obs_lit_fail rfl

theorem obs_seq {a b : MExp} {x y : List Char} {r : Option (List Char)} (ha : MacroObs g a x (some y))
    (hb : MacroObs g b y r) : MacroObs g (.seq a b) x r := by
  obtain ⟨o₁, d₁, h₁⟩ := ha
  obtain ⟨t₁, rfl⟩ := restOf_eq_some h₁
  obtain ⟨o₂, d₂, h₂⟩ := hb
  cases o₂ with
  | fail => exact ⟨_, .seqFail₂ _ _ _ _ _ d₁ d₂, h₂⟩
  | ok t z => exact ⟨_, .seqOk _ _ _ _ _ _ _ d₁ d₂, h₂⟩

theorem obs_seq_none {a b : MExp} {x : List Char} (ha : MacroObs g a x none) : MacroObs g (.seq a b) x none := by
  obtain ⟨o, d, h⟩ := ha
  have := restOf_eq_none h; subst this
  exact ⟨_, .seqFail₁ _ _ _ d, rfl⟩

theorem obs_alt_some {a b : MExp} {x y : List Char} (ha : MacroObs g a x (some y)) :
    MacroObs g (.alt a b) x (some y) := by
  obtain ⟨o, d, h⟩ := ha
  obtain ⟨t, rfl⟩ := restOf_eq_some h
  exact ⟨_, .altL _ _ _ _ _ d, rfl⟩

theorem obs_alt_none {a b : MExp} {x : List Char} {r : Option (List Char)} (ha : MacroObs g a x none)
    (hb : MacroObs g b x r) : MacroObs g (.alt a b) x r := by
  obtain ⟨o₁, d₁, h₁⟩ := ha
  have := restOf_eq_none h₁; subst this
  obtain ⟨o₂, d₂, h₂⟩ := hb
  cases o₂ with
  | fail => exact ⟨_, .altFail _ _ _ d₁ d₂, h₂⟩
  | ok t z => exact ⟨_, .altR _ _ _ _ _ d₁ d₂, h₂⟩

theorem obs_not_some {a : MExp} {x y : List Char} (ha : MacroObs g a x (some y)) : MacroObs g (.notP a) x none := by
  obtain ⟨o, d, h⟩ := ha
  obtain ⟨t, rfl⟩ := restOf_eq_some h
  exact ⟨_, .notOk _ _ _ _ d, rfl⟩

theorem obs_not_none {a : MExp} {x : List Char} (ha : MacroObs g a x none) : MacroObs g (.notP a) x (some x) := by
  obtain ⟨o, d, h⟩ := ha
  have := restOf_eq_none h; subst this
  exact ⟨_, .notFail _ _ d, rfl⟩

/-- `&a` -/
def andP (a : MExp) : MExp := .notP (.notP a)

theorem obs_and_some {a : MExp} {x y : List Char} (ha : MacroObs g a x (some y)) : MacroObs g (andP a) x (some x) :=
  obs_not_none (obs_not_some ha)

theorem obs_and_none {a : MExp} {x : List Char} (ha : MacroObs g a x none) : MacroObs g (andP a) x none :=
  obs_not_some (obs_not_none ha)

theorem obs_star_none {a : MExp} {x : List Char} (ha : MacroObs g a x none) : MacroObs g (.star a) x (some x) := by
  obtain ⟨o, d, h⟩ := ha
  have := restOf_eq_none h; subst this
  exact ⟨_, .starNil _ _ d, rfl⟩

theorem obs_star_some {a : MExp} {x y z : List Char} (ha : MacroObs g a x (some y))
    (hs : MacroObs g (.star a) y (some z)) : MacroObs g (.star a) x (some z) := by
  obtain ⟨o₁, d₁, h₁⟩ := ha
  obtain ⟨t₁, rfl⟩ := restOf_eq_some h₁
  obtain ⟨o₂, d₂, h₂⟩ := hs
  obtain ⟨t₂, rfl⟩ := restOf_eq_some h₂
  exact ⟨_, .starCons _ _ _ _ _ _ d₁ d₂, rfl⟩

theorem obs_any_some (c : Char) (rest : List Char) : MacroObs g .any (c :: rest) (some rest) := ⟨_, .anyOk c rest, rfl⟩
theorem obs_any_nil : MacroObs g .any [] none := ⟨_, .anyFail, rfl⟩

theorem obs_call {i : Nat} {args : List MExp} {r : MRule} {x : List Char} {res : Option (List Char)}
    (hr : ruleAtM g.rules i = some r) (ha : r.arity = args.length) (hb : MacroObs g (MExp.subst args r.body) x res) :
    MacroObs g (.call i args) x res := by
  obtain ⟨o, d, h⟩ := hb
  cases o with
  | fail => exact ⟨_, .callNameFail i args r x rfl hr ha d, h⟩
  | ok t z => exact ⟨_, .callNameOk i args r x z t rfl hr ha d, h⟩

theorem macroObs_unique {e : MExp} {x : List Char} {r r' : Option (List Char)} (h : MacroObs g e x r)
    (h' : MacroObs g e x r') : r = r' := by
  obtain ⟨o, d, rfl⟩ := h
  obtain ⟨o', d', rfl⟩ := h'
  rw [mderives_det d d']

end Obs

/-! ## The grammar -/

def one : MExp := .lit ['1']
def zero : MExp := .lit ['0']
def p0 : MExp := .param 0
def p1 : MExp := .param 1

def qBody : MExp :=
  .alt (.seq (.lit ['A']) (.seq (andP (.call 0 [.seq p0 one, .alt p1 (.seq p0 zero)])) (.call 0 [.seq p0 one, p1])))
    (.alt (.seq (.lit ['E']) (.alt (.call 0 [.seq p0 one, .alt p1 (.seq p0 zero)]) (.call 0 [.seq p0 one, p1])))
      (.seq (.lit ['#']) (.call 1 [p1])))
def mBody : MExp := .seq (.star (.seq (.call 2 [p0]) (.lit [';']))) (.notP .any)
def clBody : MExp := .alt (.seq (.call 3 [p0]) (.star (.call 5 []))) (.seq (.call 4 [p0]) (.call 2 [p0]))
def tlBody : MExp :=
  .alt (.seq (.lit ['+']) (.seq (andP p0) (.call 6 []))) (.seq (.lit ['-']) (.seq (.notP p0) (.call 6 [])))
def flBody : MExp :=
  .alt (.seq (.lit ['+']) (.seq (.notP p0) (.call 6 []))) (.seq (.lit ['-']) (.seq (andP p0) (.call 6 [])))
def litBody : MExp := .seq (.alt (.lit ['+']) (.lit ['-'])) (.call 6 [])
def codeBody : MExp := .seq (.star one) zero

def qbfG : MGrammar :=
  ⟨[⟨2, qBody⟩, ⟨1, mBody⟩, ⟨1, clBody⟩, ⟨1, tlBody⟩, ⟨1, flBody⟩, ⟨0, litBody⟩, ⟨0, codeBody⟩]⟩

/-- `"1"^k` -/
def cNum : Nat → MExp
  | 0 => .eps
  | k + 1 => .seq (cNum k) one

/-- `1^k 0`, the code of variable `k`. -/
def codeP (k : Nat) : MExp := .seq (cNum k) zero

/-- The assignment: the codes of the variables in `S`, as an ordered choice (`!ε` for the empty set). -/
def asg : List Nat → MExp
  | [] => .notP .eps
  | j :: S => .alt (asg S) (codeP j)

def qCall (k : Nat) (S : List Nat) : MExp := .call 0 [cNum k, asg S]
def qbfStart : MExp := qCall 0 []

theorem qbfStart_eq : qbfStart = .call 0 [.eps, .notP .eps] := rfl

/-! ## QBF -/

/-- A literal: sign (`true` = positive) and variable. -/
abbrev QLit := Bool × Nat
abbrev QMatrix := List (List QLit)

def litTrue (S : List Nat) (l : QLit) : Bool := if l.1 then decide (l.2 ∈ S) else !decide (l.2 ∈ S)
def clauseTrue (S : List Nat) (cl : List QLit) : Bool := cl.any (litTrue S)
def matrixTrue (S : List Nat) (m : QMatrix) : Bool := m.all (clauseTrue S)

/-- Truth of the prenex formula with prefix `q` (`true` = ∀, `false` = ∃) quantifying variables `k, k+1, …`, under the
assignment `S` (the true variables) of the variables already quantified; unquantified variables are false. -/
def qbfTrue : List Bool → Nat → List Nat → QMatrix → Bool
  | [], _, S, m => matrixTrue S m
  | true :: q, k, S, m => qbfTrue q (k + 1) (k :: S) m && qbfTrue q (k + 1) S m
  | false :: q, k, S, m => qbfTrue q (k + 1) (k :: S) m || qbfTrue q (k + 1) S m

def codeStr (v : Nat) : List Char := List.replicate v '1' ++ ['0']
def litStr (l : QLit) : List Char := (if l.1 then '+' else '-') :: codeStr l.2
def litsStr (ls : List QLit) : List Char := ls.flatMap litStr
def matrixStr (m : QMatrix) : List Char := m.flatMap (fun cl => litsStr cl ++ [';'])
def prefixStr (q : List Bool) : List Char := q.map (fun b => if b then 'A' else 'E')
def enc (q : List Bool) (m : QMatrix) : List Char := prefixStr q ++ '#' :: matrixStr m

/-! ## Correctness, bottom-up -/

theorem cNum_ok {g : MGrammar} : ∀ (k i : Nat) (rest : List Char), k ≤ i →
    MacroObs g (cNum k) (List.replicate i '1' ++ '0' :: rest) (some (List.replicate (i - k) '1' ++ '0' :: rest))
  | 0, i, rest, _ => by
    show MacroObs g .eps _ (some (List.replicate (i - 0) '1' ++ '0' :: rest))
    rw [Nat.sub_zero]; exact obs_eps _
  | k + 1, i, rest, h => by
    refine obs_seq (cNum_ok k i rest (by omega)) ?_
    have : i - k = (i - (k + 1)) + 1 := by omega
    rw [this, List.replicate_succ, List.cons_append]
    exact obs_lit_ok (g := g) ['1'] _

theorem cNum_fail {g : MGrammar} : ∀ (k i : Nat) (rest : List Char), i < k →
    MacroObs g (cNum k) (List.replicate i '1' ++ '0' :: rest) none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, rest, h => by
    by_cases hik : i < k
    · exact obs_seq_none (cNum_fail k i rest hik)
    · have hk : k = i := by omega
      subst hk
      refine obs_seq (cNum_ok k k rest (Nat.le_refl _)) ?_
      rw [Nat.sub_self]
      exact obs_char_fail _ (by decide)

theorem codeP_match {g : MGrammar} (k i : Nat) (rest : List Char) :
    MacroObs g (codeP k) (codeStr i ++ rest) (if i = k then some rest else none) := by
  unfold codeStr
  rw [List.append_assoc, List.singleton_append]
  by_cases hki : k ≤ i
  · refine obs_seq (cNum_ok k i rest hki) ?_
    by_cases hik : i = k
    · subst hik; rw [Nat.sub_self, if_pos rfl]; exact obs_lit_ok (g := g) ['0'] rest
    · rw [if_neg hik, show i - k = (i - k - 1) + 1 by omega, List.replicate_succ, List.cons_append]
      exact obs_char_fail _ (by decide)
  · rw [if_neg (by omega)]
    exact obs_seq_none (cNum_fail k i rest (by omega))

theorem asg_match {g : MGrammar} : ∀ (S : List Nat) (i : Nat) (rest : List Char),
    MacroObs g (asg S) (codeStr i ++ rest) (if i ∈ S then some rest else none)
  | [], i, rest => by
    rw [if_neg (List.not_mem_nil)]
    exact obs_not_some (obs_eps _)
  | j :: S, i, rest => by
    by_cases hS : i ∈ S
    · rw [if_pos (List.mem_cons_of_mem _ hS)]
      have := asg_match (g := g) S i rest
      rw [if_pos hS] at this
      exact obs_alt_some this
    · have h₁ := asg_match (g := g) S i rest
      rw [if_neg hS] at h₁
      refine obs_alt_none h₁ ?_
      have h₂ := codeP_match (g := g) j i rest
      by_cases hij : i = j
      · rw [if_pos hij] at h₂; rw [if_pos (by simp [hij])]; exact h₂
      · rw [if_neg hij] at h₂; rw [if_neg (by simp [hij, hS])]; exact h₂

theorem star_one {g : MGrammar} (rest : List Char) : ∀ i : Nat,
    MacroObs g (.star one) (List.replicate i '1' ++ '0' :: rest) (some ('0' :: rest))
  | 0 => obs_star_none (obs_char_fail _ (by decide))
  | i + 1 => by
    rw [List.replicate_succ, List.cons_append]
    exact obs_star_some (obs_lit_ok (g := g) ['1'] _) (star_one rest i)

theorem code_ok (v : Nat) (rest : List Char) : MacroObs qbfG (.call 6 []) (codeStr v ++ rest) (some rest) := by
  refine obs_call (r := ⟨0, codeBody⟩) rfl rfl ?_
  show MacroObs qbfG (.seq (.star one) zero) _ _
  unfold codeStr
  rw [List.append_assoc, List.singleton_append]
  exact obs_seq (star_one rest v) (obs_lit_ok (g := qbfG) ['0'] rest)

theorem lit_ok (l : QLit) (rest : List Char) : MacroObs qbfG (.call 5 []) (litStr l ++ rest) (some rest) := by
  refine obs_call (r := ⟨0, litBody⟩) rfl rfl ?_
  show MacroObs qbfG (.seq (.alt (.lit ['+']) (.lit ['-'])) (.call 6 [])) _ _
  obtain ⟨b, v⟩ := l
  cases b with
  | true =>
    show MacroObs qbfG _ ('+' :: (codeStr v ++ rest)) _
    exact obs_seq (obs_alt_some (obs_lit_ok (g := qbfG) ['+'] _)) (code_ok v rest)
  | false =>
    show MacroObs qbfG _ ('-' :: (codeStr v ++ rest)) _
    exact obs_seq (obs_alt_none (obs_char_fail _ (by decide)) (obs_lit_ok (g := qbfG) ['-'] _)) (code_ok v rest)

theorem lit_semi (rest : List Char) : MacroObs qbfG (.call 5 []) (';' :: rest) none := by
  refine obs_call (r := ⟨0, litBody⟩) rfl rfl ?_
  exact obs_seq_none (obs_alt_none (obs_char_fail _ (by decide)) (obs_char_fail _ (by decide)))

theorem lits_star (rest : List Char) : ∀ ls : List QLit,
    MacroObs qbfG (.star (.call 5 [])) (litsStr ls ++ ';' :: rest) (some (';' :: rest))
  | [] => obs_star_none (lit_semi rest)
  | l :: ls => by
    show MacroObs qbfG _ ((litStr l ++ litsStr ls) ++ ';' :: rest) _
    rw [List.append_assoc]
    exact obs_star_some (lit_ok l _) (lits_star rest ls)

theorem tl_match (S : List Nat) (l : QLit) (rest : List Char) :
    MacroObs qbfG (.call 3 [asg S]) (litStr l ++ rest) (if litTrue S l then some rest else none) := by
  refine obs_call (r := ⟨1, tlBody⟩) rfl rfl ?_
  show MacroObs qbfG (.alt (.seq (.lit ['+']) (.seq (andP (asg S)) (.call 6 [])))
    (.seq (.lit ['-']) (.seq (.notP (asg S)) (.call 6 [])))) _ _
  obtain ⟨b, v⟩ := l
  have hA := asg_match (g := qbfG) S v rest
  cases b with
  | true =>
    show MacroObs qbfG _ ('+' :: (codeStr v ++ rest)) _
    by_cases hv : v ∈ S
    · rw [if_pos hv] at hA
      rw [show litTrue S (true, v) = true by simp [litTrue, hv], if_pos rfl]
      exact obs_alt_some (obs_seq (obs_lit_ok (g := qbfG) ['+'] _) (obs_seq (obs_and_some hA) (code_ok v rest)))
    · rw [if_neg hv] at hA
      rw [show litTrue S (true, v) = false by simp [litTrue, hv]]
      exact obs_alt_none (obs_seq (obs_lit_ok (g := qbfG) ['+'] _) (obs_seq_none (obs_and_none hA)))
        (obs_seq_none (obs_char_fail _ (by decide)))
  | false =>
    show MacroObs qbfG _ ('-' :: (codeStr v ++ rest)) _
    by_cases hv : v ∈ S
    · rw [if_pos hv] at hA
      rw [show litTrue S (false, v) = false by simp [litTrue, hv]]
      exact obs_alt_none (obs_seq_none (obs_char_fail _ (by decide)))
        (obs_seq (obs_lit_ok (g := qbfG) ['-'] _) (obs_seq_none (obs_not_some hA)))
    · rw [if_neg hv] at hA
      rw [show litTrue S (false, v) = true by simp [litTrue, hv], if_pos rfl]
      exact obs_alt_none (obs_seq_none (obs_char_fail _ (by decide)))
        (obs_seq (obs_lit_ok (g := qbfG) ['-'] _) (obs_seq (obs_not_none hA) (code_ok v rest)))

theorem fl_match (S : List Nat) (l : QLit) (rest : List Char) :
    MacroObs qbfG (.call 4 [asg S]) (litStr l ++ rest) (if litTrue S l then none else some rest) := by
  refine obs_call (r := ⟨1, flBody⟩) rfl rfl ?_
  show MacroObs qbfG (.alt (.seq (.lit ['+']) (.seq (.notP (asg S)) (.call 6 [])))
    (.seq (.lit ['-']) (.seq (andP (asg S)) (.call 6 [])))) _ _
  obtain ⟨b, v⟩ := l
  have hA := asg_match (g := qbfG) S v rest
  cases b with
  | true =>
    show MacroObs qbfG _ ('+' :: (codeStr v ++ rest)) _
    by_cases hv : v ∈ S
    · rw [if_pos hv] at hA
      rw [show litTrue S (true, v) = true by simp [litTrue, hv], if_pos rfl]
      exact obs_alt_none (obs_seq (obs_lit_ok (g := qbfG) ['+'] _) (obs_seq_none (obs_not_some hA)))
        (obs_seq_none (obs_char_fail _ (by decide)))
    · rw [if_neg hv] at hA
      rw [show litTrue S (true, v) = false by simp [litTrue, hv]]
      exact obs_alt_some (obs_seq (obs_lit_ok (g := qbfG) ['+'] _) (obs_seq (obs_not_none hA) (code_ok v rest)))
  | false =>
    show MacroObs qbfG _ ('-' :: (codeStr v ++ rest)) _
    by_cases hv : v ∈ S
    · rw [if_pos hv] at hA
      rw [show litTrue S (false, v) = false by simp [litTrue, hv]]
      exact obs_alt_none (obs_seq_none (obs_char_fail _ (by decide)))
        (obs_seq (obs_lit_ok (g := qbfG) ['-'] _) (obs_seq (obs_and_some hA) (code_ok v rest)))
    · rw [if_neg hv] at hA
      rw [show litTrue S (false, v) = true by simp [litTrue, hv], if_pos rfl]
      exact obs_alt_none (obs_seq_none (obs_char_fail _ (by decide)))
        (obs_seq (obs_lit_ok (g := qbfG) ['-'] _) (obs_seq_none (obs_and_none hA)))

theorem tl_semi (S : List Nat) (rest : List Char) : MacroObs qbfG (.call 3 [asg S]) (';' :: rest) none :=
  obs_call (r := ⟨1, tlBody⟩) rfl rfl
    (obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) (obs_seq_none (obs_char_fail _ (by decide))))

theorem fl_semi (S : List Nat) (rest : List Char) : MacroObs qbfG (.call 4 [asg S]) (';' :: rest) none :=
  obs_call (r := ⟨1, flBody⟩) rfl rfl
    (obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) (obs_seq_none (obs_char_fail _ (by decide))))

theorem cl_match (S : List Nat) (rest : List Char) : ∀ ls : List QLit,
    MacroObs qbfG (.call 2 [asg S]) (litsStr ls ++ ';' :: rest)
      (if clauseTrue S ls then some (';' :: rest) else none)
  | [] => by
    refine obs_call (r := ⟨1, clBody⟩) rfl rfl ?_
    exact obs_alt_none (obs_seq_none (tl_semi S rest)) (obs_seq_none (fl_semi S rest))
  | l :: ls => by
    refine obs_call (r := ⟨1, clBody⟩) rfl rfl ?_
    show MacroObs qbfG (.alt (.seq (.call 3 [asg S]) (.star (.call 5 [])))
      (.seq (.call 4 [asg S]) (.call 2 [asg S]))) ((litStr l ++ litsStr ls) ++ ';' :: rest) _
    rw [List.append_assoc]
    have ht := tl_match S l (litsStr ls ++ ';' :: rest)
    have hf := fl_match S l (litsStr ls ++ ';' :: rest)
    by_cases hl : litTrue S l = true
    · rw [if_pos hl] at ht
      rw [show clauseTrue S (l :: ls) = true by simp [clauseTrue, hl], if_pos rfl]
      exact obs_alt_some (obs_seq ht (lits_star rest ls))
    · rw [if_neg hl] at ht
      rw [if_neg hl] at hf
      rw [show clauseTrue S (l :: ls) = clauseTrue S ls by simp [clauseTrue, hl]]
      exact obs_alt_none (obs_seq_none ht) (obs_seq hf (cl_match S rest ls))

theorem cl_nil (S : List Nat) : MacroObs qbfG (.call 2 [asg S]) [] none := by
  refine obs_call (r := ⟨1, clBody⟩) rfl rfl ?_
  refine obs_alt_none (obs_seq_none ?_) (obs_seq_none ?_)
  · exact obs_call (r := ⟨1, tlBody⟩) rfl rfl
      (obs_alt_none (obs_seq_none (obs_char_nil _)) (obs_seq_none (obs_char_nil _)))
  · exact obs_call (r := ⟨1, flBody⟩) rfl rfl
      (obs_alt_none (obs_seq_none (obs_char_nil _)) (obs_seq_none (obs_char_nil _)))

theorem clauses_star (S : List Nat) : ∀ m : QMatrix,
    ∃ rem, MacroObs qbfG (.star (.seq (.call 2 [asg S]) (.lit [';']))) (matrixStr m) (some rem) ∧
      (rem = [] ↔ matrixTrue S m = true)
  | [] => ⟨[], obs_star_none (obs_seq_none (cl_nil S)), by simp [matrixTrue]⟩
  | cl :: m => by
    show ∃ rem, MacroObs qbfG _ ((litsStr cl ++ [';']) ++ matrixStr m) (some rem) ∧ _
    rw [List.append_assoc, List.singleton_append]
    have hc := cl_match S (matrixStr m) cl
    by_cases ht : clauseTrue S cl = true
    · rw [if_pos ht] at hc
      obtain ⟨rem, hrem, hiff⟩ := clauses_star S m
      refine ⟨rem, obs_star_some (obs_seq hc (obs_lit_ok (g := qbfG) [';'] _)) hrem, ?_⟩
      rw [hiff]; simp [matrixTrue, ht]
    · rw [if_neg ht] at hc
      refine ⟨_, obs_star_none (obs_seq_none hc), ?_⟩
      simp only [matrixTrue, List.all_cons, Bool.and_eq_true]
      constructor
      · intro h
        cases cl <;> simp [litsStr] at h
      · intro h; exact absurd h.1 ht

theorem m_match (S : List Nat) (m : QMatrix) :
    MacroObs qbfG (.call 1 [asg S]) (matrixStr m) (if matrixTrue S m then some [] else none) := by
  refine obs_call (r := ⟨1, mBody⟩) rfl rfl ?_
  show MacroObs qbfG (.seq (.star (.seq (.call 2 [asg S]) (.lit [';']))) (.notP .any)) _ _
  obtain ⟨rem, hrem, hiff⟩ := clauses_star S m
  by_cases ht : matrixTrue S m = true
  · rw [if_pos ht]
    have := hiff.2 ht; subst this
    exact obs_seq hrem (obs_not_none obs_any_nil)
  · rw [if_neg ht]
    refine obs_seq hrem ?_
    cases rem with
    | nil => exact absurd (hiff.1 rfl) ht
    | cons c rest => exact obs_not_some (obs_any_some c rest)

theorem q_match (m : QMatrix) : ∀ (q : List Bool) (k : Nat) (S : List Nat),
    MacroObs qbfG (qCall k S) (prefixStr q ++ '#' :: matrixStr m) (if qbfTrue q k S m then some [] else none)
  | [], k, S => by
    refine obs_call (r := ⟨2, qBody⟩) rfl rfl ?_
    refine obs_alt_none (obs_seq_none (obs_char_fail _ (by decide)))
      (obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) ?_)
    exact obs_seq (obs_lit_ok (g := qbfG) ['#'] _) (m_match S m)
  | true :: q, k, S => by
    refine obs_call (r := ⟨2, qBody⟩) rfl rfl ?_
    show MacroObs qbfG _ ('A' :: (prefixStr q ++ '#' :: matrixStr m)) _
    have h₁ := q_match m q (k + 1) (k :: S)
    have h₂ := q_match m q (k + 1) S
    have hrest : MacroObs qbfG (.alt (.seq (.lit ['E']) (.alt (qCall (k + 1) (k :: S)) (qCall (k + 1) S)))
        (.seq (.lit ['#']) (.call 1 [asg S]))) ('A' :: (prefixStr q ++ '#' :: matrixStr m)) none :=
      obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) (obs_seq_none (obs_char_fail _ (by decide)))
    by_cases hb₁ : qbfTrue q (k + 1) (k :: S) m = true
    · rw [if_pos hb₁] at h₁
      by_cases hb₂ : qbfTrue q (k + 1) S m = true
      · rw [if_pos hb₂] at h₂
        rw [show qbfTrue (true :: q) k S m = true by simp [qbfTrue, hb₁, hb₂], if_pos rfl]
        exact obs_alt_some (obs_seq (obs_lit_ok (g := qbfG) ['A'] _) (obs_seq (obs_and_some h₁) h₂))
      · rw [if_neg hb₂] at h₂
        rw [show qbfTrue (true :: q) k S m = false by simp [qbfTrue, hb₁, hb₂]]
        exact obs_alt_none (obs_seq (obs_lit_ok (g := qbfG) ['A'] _) (obs_seq (obs_and_some h₁) h₂)) hrest
    · rw [if_neg hb₁] at h₁
      rw [show qbfTrue (true :: q) k S m = false by simp [qbfTrue, hb₁]]
      exact obs_alt_none (obs_seq (obs_lit_ok (g := qbfG) ['A'] _) (obs_seq_none (obs_and_none h₁))) hrest
  | false :: q, k, S => by
    refine obs_call (r := ⟨2, qBody⟩) rfl rfl ?_
    show MacroObs qbfG _ ('E' :: (prefixStr q ++ '#' :: matrixStr m)) _
    have h₁ := q_match m q (k + 1) (k :: S)
    have h₂ := q_match m q (k + 1) S
    refine obs_alt_none (obs_seq_none (obs_char_fail _ (by decide))) ?_
    have hhash : MacroObs qbfG (.seq (.lit ['#']) (.call 1 [asg S])) ('E' :: (prefixStr q ++ '#' :: matrixStr m))
        none := obs_seq_none (obs_char_fail _ (by decide))
    by_cases hb₁ : qbfTrue q (k + 1) (k :: S) m = true
    · rw [if_pos hb₁] at h₁
      rw [show qbfTrue (false :: q) k S m = true by simp [qbfTrue, hb₁], if_pos rfl]
      exact obs_alt_some (obs_seq (obs_lit_ok (g := qbfG) ['E'] _) (obs_alt_some h₁))
    · rw [if_neg hb₁] at h₁
      by_cases hb₂ : qbfTrue q (k + 1) S m = true
      · rw [if_pos hb₂] at h₂
        rw [show qbfTrue (false :: q) k S m = true by simp [qbfTrue, hb₂], if_pos rfl]
        exact obs_alt_some (obs_seq (obs_lit_ok (g := qbfG) ['E'] _) (obs_alt_none h₁ h₂))
      · rw [if_neg hb₂] at h₂
        rw [show qbfTrue (false :: q) k S m = false by simp [qbfTrue, hb₁, hb₂]]
        exact obs_alt_none (obs_seq (obs_lit_ok (g := qbfG) ['E'] _) (obs_alt_none h₁ h₂)) hhash

/-! ## The reduction -/

/-- The observation of the start on an encoded formula is decided by the formula's truth. -/
theorem qbf_obs (q : List Bool) (m : QMatrix) :
    MacroObs qbfG qbfStart (enc q m) (if qbfTrue q 0 [] m then some [] else none) :=
  q_match m q 0 []

/-- **PSPACE-hardness of first-order CBN Macro PEG.** The fixed grammar `qbfG` consumes the whole encoding of a QBF iff
the formula is true. -/
theorem qbf_reduction (q : List Bool) (m : QMatrix) :
    MRecognizesAll qbfG qbfStart (enc q m) ↔ qbfTrue q 0 [] m = true := by
  constructor
  · intro h
    cases ht : qbfTrue q 0 [] m with
    | true => rfl
    | false =>
      have := macroObs_unique h (qbf_obs q m)
      rw [if_neg (by simp [ht])] at this
      cases this
  · intro h
    have := qbf_obs q m
    rwa [if_pos h] at this

/-- On a false formula the grammar fails (a finite failure derivation, not non-termination). -/
theorem qbf_reject (q : List Bool) (m : QMatrix) :
    MacroObs qbfG qbfStart (enc q m) none ↔ qbfTrue q 0 [] m = false := by
  constructor
  · intro h
    cases ht : qbfTrue q 0 [] m with
    | false => rfl
    | true =>
      have := macroObs_unique h (qbf_obs q m)
      rw [if_pos ht] at this
      cases this
  · intro h
    have := qbf_obs q m
    rwa [if_neg (by simp [h])] at this

/-- The encoding's length: one symbol per quantifier, `#`, and per clause its literals (`v + 2` symbols each) and `;`.
Quadratic in the size of the formula, computed by a structural map. -/
theorem enc_length (q : List Bool) (m : QMatrix) :
    (enc q m).length = q.length + 1 + (m.map (fun cl => (cl.map (fun l => l.2 + 2)).sum + 1)).sum := by
  have hf : (fun a : QLit => a.snd + 1 + 1) = (fun l => l.snd + 2) := by funext a; omega
  simp [enc, prefixStr, matrixStr, litsStr, litStr, codeStr, List.length_flatMap, hf]
  omega

/-! ## Examples -/

/-- `∀x. x ∨ ¬x` is true. -/
example : MRecognizesAll qbfG qbfStart (enc [true] [[(true, 0), (false, 0)]]) :=
  (qbf_reduction _ _).2 (by decide)
/-- `∀x. x` is false. -/
example : MacroObs qbfG qbfStart (enc [true] [[(true, 0)]]) none := (qbf_reject _ _).2 (by decide)
/-- `∃x ∀y. (x ∨ y) ∧ (x ∨ ¬y)` is true. -/
example : MRecognizesAll qbfG qbfStart (enc [false, true] [[(true, 0), (true, 1)], [(true, 0), (false, 1)]]) :=
  (qbf_reduction _ _).2 (by decide)
/-- `∀x ∃y. (x ∨ y) ∧ (¬x ∨ ¬y) ∧ (x ∨ ¬y)` is false. -/
example : MacroObs qbfG qbfStart
    (enc [true, false] [[(true, 0), (true, 1)], [(false, 0), (false, 1)], [(true, 0), (false, 1)]]) none :=
  (qbf_reject _ _).2 (by decide)

end Shallot.MacroPeg
