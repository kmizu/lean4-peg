import Cfg.Greibach.PelHomPad
import Shallot.Peg.Soundness
import Shallot.Peg.Completeness

/-!
# The simulating grammar for an inverse homomorphism

Fix a grammar `g` over the image alphabet and a nonerasing `h` with finitely many distinct blocks: `h a = h₀`
outside a finite list `S`. A source letter `a` falls in the **class** `clsOf S a` (its first position in `S`,
or `S.length` when `a ∉ S`), and the class determines the block `blk k`.

A **state** `q : St` is a position inside the image of a source word: `none` is a block boundary, `some (k, i)`
is the offset `i` (with `0 < i < |blk k|`) inside a block of class `k` whose letter was already read. The image
still to be read at state `q` with source `u` is `img q u`. The states form the finite list `stList`.

The new grammar has one rule per **item** `(e, q, q')`: a subexpression `e` of `g` started at state `q` and
required to end at state `q'`. Its rule `body` succeeds, reading the source between the two positions, exactly
when `e` succeeds on the image and ends at state `q'`; failure of `e` is tested by `FL e q`, which says that
no end state works. Every body first evaluates what `e` would evaluate, so non-termination is mirrored too.
-/

namespace Shallot.Cfg

open Shallot (Grammar Derives PExp PTree Outcome ruleAt beqChar leChar)

/-- A position inside a block: `none` at a boundary, `some (k, i)` at offset `i` of a block of class `k`. -/
abbrev St := Option (Nat × Nat)

/-- An item: a subexpression with its start and end states. -/
abbrev Item := PExp × St × St

/-- The ordered choice over a list, ending in failure. -/
def chain {α : Type} : List α → (α → PExp) → PExp
  | [], _ => phFail
  | y :: l, F => .alt (F y) (chain l F)

/-- `ε` when the two states agree, failure otherwise. -/
def guardEq (q q' : St) : PExp := if q = q' then .eps else phFail

/-- The class of a letter: its first position in the list, or the length when absent. -/
def clsOf : List Char → Char → Nat
  | [], _ => 0
  | c :: cs, a => if a = c then 0 else clsOf cs a + 1

/-- Whether a letter is among a list: the ordered choice of its letters. -/
def anyOf (l : List Char) : PExp := chain l PExp.chr

/-- Test the letter at an offset of a block (false past the end). -/
def testAt (P : Char → Bool) (l : List Char) (i : Nat) : Bool :=
  match l[i]? with
  | some d => P d
  | none => false

/-- The subexpressions of an expression, itself first. -/
def subs : PExp → List PExp
  | .seq a b => .seq a b :: (subs a ++ subs b)
  | .alt a b => .alt a b :: (subs a ++ subs b)
  | .star a => .star a :: subs a
  | .notP a => .notP a :: subs a
  | e => [e]

open Classical in
/-- The first index of an item in a list (the length when absent). -/
noncomputable def phIdx (x : Item) : List Item → Nat
  | [] => 0
  | y :: l => if x = y then 0 else phIdx x l + 1

/-- The data of the simulation. -/
structure PhSim where
  /-- The grammar over the image alphabet. -/
  g : Grammar
  /-- The homomorphism on letters. -/
  h : Char → List Char
  /-- The letters with a special block. -/
  S : List Char
  /-- The block of every other letter. -/
  h₀ : List Char

namespace PhSim

variable (M : PhSim)

/-- The block of class `k`. -/
def blk (k : Nat) : List Char :=
  match M.S[k]? with
  | some c => M.h c
  | none => M.h₀

/-- The image of a source word. -/
def hflat (u : List Char) : List Char := (u.map M.h).flatten

/-- The image still to be read at a state with source `u`. -/
def img : St → List Char → List Char
  | none, u => M.hflat u
  | some (k, i), u => (M.blk k).drop i ++ M.hflat u

/-- All states. -/
def stList : List St :=
  none :: (List.range (M.S.length + 1)).flatMap
    (fun k => (List.range ((M.blk k).length - 1)).map (fun j => some (k, j + 1)))

/-- The state after the letter at offset `i` of a block of class `k`. -/
def nextSt (k i : Nat) : St := if i + 1 < (M.blk k).length then some (k, i + 1) else none

/-- Read a source letter of class `k`. -/
def sel (k : Nat) : PExp :=
  .seq (.notP (anyOf (M.S.take k)))
    (match M.S[k]? with
     | some c => .chr c
     | none => .any)

/-- Read one image letter satisfying `P`, from state `q` to state `q'`. -/
def step1 (P : Char → Bool) : St → St → PExp
  | some (k, i), q' => if testAt P (M.blk k) i = true ∧ M.nextSt k i = q' then .eps else phFail
  | none, q' => chain (List.range (M.S.length + 1))
      (fun k => if testAt P (M.blk k) 0 = true ∧ M.nextSt k 0 = q' then M.sel k else phFail)

/-- Read the image literal `s` from state `q` to state `q'`. -/
def litT : List Char → St → St → PExp
  | [], q, q' => guardEq q q'
  | c :: s, q, q' => chain M.stList (fun y => .seq (M.step1 (beqChar c) q y) (litT s y q'))

/-- The subexpressions of `g` (with its start call). -/
def elist : List PExp := subs (.nt M.g.start) ++ M.g.rules.flatMap subs

/-- All items. -/
def items : List Item :=
  M.elist.flatMap (fun e => M.stList.flatMap (fun q => M.stList.map (fun q' => (e, q, q'))))

/-- The rule index of an item. -/
noncomputable def code (x : Item) : Nat := phIdx x M.items

/-- The call of an item. -/
noncomputable def N (x : Item) : PExp := .nt (M.code x)

/-- The calls of `e` from `q`, indexed by the end state. -/
noncomputable def NF (e : PExp) (q : St) : St → PExp := fun q' => M.N (e, q, q')

/-- `e` fails from `q`: no end state works. -/
noncomputable def FL (e : PExp) (q : St) : PExp := .notP (chain M.stList (M.NF e q))

/-- The rule of an item. -/
noncomputable def body : Item → PExp
  | (.eps, q, q') => guardEq q q'
  | (.any, q, q') => M.step1 (fun _ => true) q q'
  | (.chr c, q, q') => M.step1 (beqChar c) q q'
  | (.range lo hi, q, q') => M.step1 (fun d => leChar lo d && leChar d hi) q q'
  | (.lit s, q, q') => M.litT s q q'
  | (.nt i, q, q') =>
    match ruleAt M.g.rules i with
    | some r => M.N (r, q, q')
    | none => phFail
  | (.seq e₁ e₂, q, q') => chain M.stList (fun y => .seq (M.N (e₁, q, y)) (M.N (e₂, y, q')))
  | (.alt e₁ e₂, q, q') => .alt (M.N (e₁, q, q')) (.seq (M.FL e₁ q) (M.N (e₂, q, q')))
  | (.star e, q, q') =>
    .alt (chain M.stList (fun y => .seq (M.N (e, q, y)) (M.N (.star e, y, q'))))
      (.seq (M.FL e q) (guardEq q q'))
  | (.notP e, q, q') => .seq (M.FL e q) (guardEq q q')

/-- **The simulating grammar.** -/
noncomputable def grammar : Grammar :=
  { rules := M.items.map M.body, start := M.code (.nt M.g.start, none, none) }

end PhSim

/-- A family of expressions indexed by end states **hits** `(q₁, u₁)` from source `u`: the member for `q₁`
succeeds with rest `u₁`, every other member fails. -/
def Hits (G : Grammar) (Q : List St) (F : St → PExp) (u : List Char) (q₁ : St) (u₁ : List Char) : Prop :=
  q₁ ∈ Q ∧ ∀ q' ∈ Q, (q' = q₁ → ∃ t, Derives G (F q') u (.ok t u₁)) ∧ (q' ≠ q₁ → Derives G (F q') u .fail)

/-- A family **misses** from source `u`: every member fails. -/
def Misses (G : Grammar) (Q : List St) (F : St → PExp) (u : List Char) : Prop :=
  ∀ q' ∈ Q, Derives G (F q') u .fail

end Shallot.Cfg
