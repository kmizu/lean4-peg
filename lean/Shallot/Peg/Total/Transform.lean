import Shallot.Peg.Total.Mask

/-!
# The transformed grammar

For an original expression `e` and an open set `S` (`Guarded.lean`), `tr n e S` gives three expressions of the
transformed grammar (`n` is the number of original rules):

* `z` succeeds iff `e` succeeds consuming nothing (and then consumes nothing);
* `p` succeeds iff `e` succeeds consuming at least one character, with the same consumption;
* `l` succeeds iff `e` loops (has no derivation); it is only used under predicates.

Derived from them: `r = z / p` (succeeds exactly as `e`) and `fl = !r !l` (succeeds iff `e` fails, consuming
nothing). A call `A` with `A ∈ S` loops; with `A ∉ S` it calls the nonterminal `(k, A, S)` whose rule is the kind-`k`
part of `tr n (body A) (S ∪ {A})`. After consumption the second part of a sequence, and every further repetition
step, runs with `S = ∅`. Repetition is `p a S · (p a ∅)* · fl a ∅ / fl a S`: the original loops when a step succeeds
without consuming, so iteration continues only on consuming steps and must end where the body fails.

`newG g` lists the rules of all coded nonterminals `idx n k A S` (`Mask.lean`) and, last, the new start rule
`r (start, ∅)`.
-/

namespace Shallot

/-- The three transformed expressions of an original expression. -/
structure Tr where
  /-- succeeds iff the original succeeds consuming nothing -/
  z : PExp
  /-- succeeds iff the original succeeds consuming input, with the same consumption -/
  p : PExp
  /-- succeeds iff the original loops -/
  l : PExp

/-- An expression that always fails. -/
def fl0 : PExp := .notP .eps

/-- Succeeds exactly as the original. -/
def Tr.r (T : Tr) : PExp := .alt T.z T.p

/-- Succeeds iff the original fails, consuming nothing. -/
def Tr.fl (T : Tr) : PExp := .seq (.notP T.r) (.notP T.l)

/-- Sequence: `ta`, `tb` at the current open set, `tb0` for the second part after consumption. -/
def seqT (ta tb tb0 : Tr) : Tr :=
  ⟨.seq ta.z tb.z, .alt (.seq ta.z tb.p) (.seq ta.p tb0.r), .alt ta.l (.alt (.seq ta.z tb.l) (.seq ta.p tb0.l))⟩

/-- Prioritized choice: the second alternative runs only where the first fails. -/
def altT (ta tb : Tr) : Tr := ⟨.alt ta.z (.seq ta.fl tb.z), .alt ta.p (.seq ta.fl tb.p), .alt ta.l (.seq ta.fl tb.l)⟩

/-- Not-predicate. -/
def notT (ta : Tr) : Tr := ⟨ta.fl, fl0, ta.l⟩

/-- Rest of a repetition after a consuming step: consuming steps, then the body must fail. -/
def starRest (ta0 : Tr) : PExp := .seq (.star ta0.p) ta0.fl

/-- Repetition: `ta` for the first step, `ta0` for the steps after consumption. -/
def starT (ta ta0 : Tr) : Tr :=
  ⟨ta.fl, .seq ta.p (starRest ta0), .notP (.alt ta.fl (.seq ta.p (starRest ta0)))⟩

/-- A call of rule `A` with open set `S`. -/
def ntT (n A S : Nat) : Tr :=
  if A < n then
    (if S.testBit A then ⟨fl0, fl0, .eps⟩ else ⟨.nt (idx n 0 A S), .nt (idx n 1 A S), .nt (idx n 2 A S)⟩)
  else ⟨fl0, fl0, fl0⟩

/-- A literal: the empty literal consumes nothing, any other consumes. -/
def litT : List Char → Tr
  | [] => ⟨.lit [], fl0, fl0⟩
  | c :: cs => ⟨fl0, .lit (c :: cs), fl0⟩

/-- **The transformation** of an expression with open set `S`. -/
def tr (n : Nat) : PExp → Nat → Tr
  | .eps, _ => ⟨.eps, fl0, fl0⟩
  | .any, _ => ⟨fl0, .any, fl0⟩
  | .chr c, _ => ⟨fl0, .chr c, fl0⟩
  | .range lo hi, _ => ⟨fl0, .range lo hi, fl0⟩
  | .lit s, _ => litT s
  | .nt A, S => ntT n A S
  | .seq a b, S => seqT (tr n a S) (tr n b S) (tr n b 0)
  | .alt a b, S => altT (tr n a S) (tr n b S)
  | .notP a, S => notT (tr n a S)
  | .star a, S => starT (tr n a S) (tr n a 0)

/-- The kind-`k` part. -/
def comp (k : Nat) (T : Tr) : PExp :=
  match k with
  | 0 => T.z
  | 1 => T.p
  | _ => T.l

/-- The body of an original rule (`ε` out of range; never used there). -/
def body (g : Grammar) (A : Nat) : PExp := (ruleAt g.rules A).getD .eps

/-- The rule of the coded nonterminal `i`. -/
def ruleOf (g : Grammar) (i : Nat) : PExp :=
  comp (i % 3) (tr g.rules.length (body g ((i / 3) % g.rules.length))
    (ins ((i / 3) / g.rules.length) ((i / 3) % g.rules.length)))

/-- The number of coded nonterminals; it is also the index of the new start rule. -/
def bound (g : Grammar) : Nat := 3 * (2 ^ g.rules.length * g.rules.length)

/-- **The transformed grammar.** -/
def newG (g : Grammar) : Grammar where
  rules := (List.range (bound g)).map (ruleOf g) ++ [(tr g.rules.length (.nt g.start) 0).r]
  start := bound g

/-! ## Rules of the transformed grammar -/

theorem ruleAt_eq (l : List PExp) (i : Nat) : ruleAt l i = l[i]? := by
  induction l generalizing i with
  | nil => rfl
  | cons r rs ih => cases i with
    | zero => rfl
    | succ i => simp [ruleAt, ih]

theorem newG_rule_lt {g : Grammar} {i : Nat} (hi : i < bound g) : ruleAt (newG g).rules i = some (ruleOf g i) := by
  rw [ruleAt_eq]
  have hl : i < ((List.range (bound g)).map (ruleOf g)).length := by simpa using hi
  simp only [newG]
  rw [List.getElem?_append_left hl]
  simp [hi]

theorem newG_rule_start (g : Grammar) : ruleAt (newG g).rules (bound g) = some (tr g.rules.length (.nt g.start) 0).r := by
  rw [ruleAt_eq]
  simp [newG]

theorem newG_rule_gt {g : Grammar} {i : Nat} (hi : bound g < i) : ruleAt (newG g).rules i = none := by
  rw [ruleAt_eq]
  simp [newG]
  omega

theorem body_eq {g : Grammar} {A : Nat} {e : PExp} (h : ruleAt g.rules A = some e) : body g A = e := by
  simp [body, h]

/-- The rule of the coded nonterminal `(k, A, S)`. -/
theorem newG_rule_idx {g : Grammar} {k A S : Nat} {e : PExp} (hk : k < 3) (hA : A < g.rules.length)
    (hS : S < 2 ^ g.rules.length) (he : ruleAt g.rules A = some e) :
    ruleAt (newG g).rules (idx g.rules.length k A S) = some (comp k (tr g.rules.length e (ins S A))) := by
  rw [newG_rule_lt (idx_lt hk hA hS)]
  simp only [ruleOf, idx_mod hk, idx_div hk, idx_A hA, idx_S hA, body_eq he]

end Shallot
