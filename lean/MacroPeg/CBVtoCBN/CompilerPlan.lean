import MacroPeg.CBVtoCBN.Repetition
import MacroPeg.CBVtoCBN.ParameterTests
import MacroPeg.CBVtoCBN.ClockGrammar
import MacroPeg.CBVtoCBN.CaptureStep
import MacroPeg.CBVtoCBN.EmptyInput
import MacroPeg.Properties.MExpEq

namespace Shallot.MacroPeg.CBVtoCBN

/-- Finite code locations for the translation. Source calls are traversed only through their arguments. -/
inductive CompileNode where
  | expr (envArity : Nat) (e : MExp)
  | args (envArity callee : Nat) (actuals : List MExp) (stage : Nat)
  | lookup (callee : Nat)
  deriving DecidableEq

mutual
  def collectNodes (envArity : Nat) (e : MExp) : List CompileNode :=
    .expr envArity e :: match e with
    | .seq a b | .alt a b => collectNodes envArity a ++ collectNodes envArity b
    | .star a | .notP a => collectNodes envArity a
    | .call callee actuals => collectArgNodes envArity actuals ++
        (List.range (actuals.length + 1)).map (.args envArity callee actuals)
    | _ => []

  def collectArgNodes (envArity : Nat) : List MExp → List CompileNode
    | [] => []
    | a :: args => collectNodes envArity a ++ collectArgNodes envArity args
end

def compilerNodes (source : MGrammar) (start : MExp) : List CompileNode :=
  collectNodes 0 start ++ source.rules.flatMap (fun r => collectNodes r.arity r.body) ++
    (List.range source.rules.length).map CompileNode.lookup

/-- One fixed-size slot per code location keeps addresses independent of the input. -/
def compilerSlotSize (digits : Nat) : Nat := 64 + 4 * digits

def compilerAddress (nodes : List CompileNode) (digits : Nat) (node : CompileNode) : Nat :=
  4 + compilerSlotSize digits * nodes.idxOf node

def compilerEnvArity (source : MGrammar) : CompileNode → Nat
  | .expr a _ | .args a _ _ _ => a
  | .lookup callee => match ruleAtM source.rules callee with
    | some r => r.arity
    | none => 0

def compilerCaptured : CompileNode → Nat
  | .args _ _ _ stage => stage
  | _ => 0

/-- Every primary predicate takes current position, queried endpoint, input length, clock, and environment.
Argument stages append the captured values accumulated so far. Each value uses four counters. -/
def compilerWidth (source : MGrammar) (digits : Nat) (node : CompileNode) : Nat :=
  5 + 2 * digits + 4 * compilerEnvArity source node + 4 * compilerCaptured node

def compilerFailRule : MRule := ⟨0, MExp.failAlways⟩

def primaryRule (width : Nat) (e : MExp) : MRule := ⟨width, e⟩

def compilerCall (address width : Nat) : MExp := .call address (paramsFrom 0 width)

/-- Adapt the failure predicate to templates which omit the unused queried endpoint. -/
def compilerFailureAdapter (failure width : Nat) : MRule :=
  ⟨width - 2, .call failure (.param 0 :: .param 1 :: .eps :: .param 2 :: paramsFrom 2 (width - 4))⟩

/-- Terminal clauses use the frozen complement of the current position and the queried remaining length. -/
def compilerAtomBodies (a : Atom) : MExp × MExp :=
  (terminalSuccessP (.param 1) (.param 2) a.exp, terminalFailureP (.param 1) a.exp)

/-- Each fragment is tagged by its offset within the owning node's slot. -/
abbrev CompileFragments := List (Nat × List MRule)

def compilerExpressionFragments (source : MGrammar) (nodes : List CompileNode) (digits : Nat)
    (base envArity : Nat) (e : MExp) : CompileFragments := Id.run do
  let width := 5 + 2 * digits + 4 * envArity
  let rest := width - 4
  let addr := fun a => compilerAddress nodes digits (.expr envArity a)
  let allArgs := paramsFrom 0 width
  let failAdapter := compilerFailureAdapter (base + 1) width
  let terminal := fun a =>
    let pair := compilerAtomBodies a
    [(0, [primaryRule width pair.1, primaryRule width pair.2, failAdapter])]
  match e with
  | .eps => return terminal .eps
  | .any => return terminal .any
  | .chr c => return terminal (.chr c)
  | .range lo hi => return terminal (.range lo hi)
  | .lit w => return terminal (.lit w)
  | .param k =>
    if k < envArity then
      let value := 5 + 2 * digits + 4 * k
      return [(0, [primaryRule width (parameterSuccessP 0 (.param (value + 1)) (.param (value + 2)) (.param 1) (.param 2)),
        primaryRule width (.call (base + 10) [.param 0, .param 1, .param (value + 1), .param (value + 2)]), failAdapter]),
        (10, parameterFailureBlock (base + 10) 0)]
    else return [(0, [primaryRule width MExp.failAlways, primaryRule width .eps, failAdapter])]
  | .alt a b =>
    return [(0, [primaryRule width (altSuccessP (.call (addr a) allArgs) (.call (addr a + 1) allArgs) (.call (addr b) allArgs)),
      primaryRule width (.seq (.call (addr a + 1) allArgs) (.call (addr b + 1) allArgs)), failAdapter])]
  | .seq a b =>
    return [(0, [primaryRule width (.call (base + 10) (.eps :: allArgs)),
      primaryRule width (.call (base + 20) (.param 0 :: .param 1 :: paramsFrom 4 rest)), failAdapter]),
      (10, sequenceSuccessBlock (base + 10) (addr a) (addr b) rest),
      (20, sequenceFailureBlock (base + 20) (addr a) (addr a + 2) (addr b + 2) rest)]
  | .star a =>
    return [(0, [primaryRule width (compilerCall (base + 10) width), primaryRule width MExp.failAlways, failAdapter]),
      (10, repetitionBlock (base + 10) (addr a) (addr a + 2) rest)]
  | .notP a =>
    return [(0, [primaryRule width (.seq (equalPositionP (.param 0) (.param 3)) (.call (addr a + 1) allArgs)),
      primaryRule width (.call (base + 10) (.eps :: .param 0 :: .param 1 :: paramsFrom 4 rest)), failAdapter]),
      (10, pairSearchBlock (base + 10) (base + 13) (rest + 2)),
      (13, [⟨rest + 4, .call (addr a) (.param 2 :: .param 3 :: .param 0 :: .param 1 :: paramsFrom 4 rest)⟩])]
  | .call callee actuals =>
    match ruleAtM source.rules callee with
    | some rule =>
      if rule.arity = actuals.length then
        let entry := compilerAddress nodes digits (.args envArity callee actuals 0)
        return [(0, [primaryRule width (compilerCall entry width), primaryRule width (compilerCall (entry + 1) width), failAdapter])]
      else return [(0, [primaryRule width MExp.failAlways, primaryRule width .eps, failAdapter])]
    | none => return [(0, [primaryRule width MExp.failAlways, primaryRule width .eps, failAdapter])]
  | _ => return [(0, [primaryRule width MExp.failAlways, primaryRule width MExp.failAlways, failAdapter])]

/-- Capturing an argument extends the continuation tuple; evaluating that argument retains the caller environment. -/
def compilerArgumentFragments (source : MGrammar) (s : Strategy) (nodes : List CompileNode) (digits : Nat)
    (base envArity callee : Nat) (actuals : List MExp) (stage : Nat) : CompileFragments := Id.run do
  let exprWidth := 5 + 2 * digits + 4 * envArity
  let width := exprWidth + 4 * stage
  let allArgs := paramsFrom 0 width
  let dead := [(0, [primaryRule width MExp.failAlways, primaryRule width .eps])]
  match ruleAtM source.rules callee with
  | none => return dead
  | some rule =>
    if rule.arity ≠ actuals.length then return dead
    if stage = actuals.length then
      let lookup := compilerAddress nodes digits (.lookup callee)
      let args := paramsFrom 0 (5 + 2 * digits) ++ paramsFrom exprWidth (4 * stage)
      return [(0, [primaryRule width (.call lookup args), primaryRule width (.call (lookup + 1) args)])]
    match actuals[stage]? with
    | none => return dead
    | some a =>
      let argument := compilerAddress nodes digits (.expr envArity a)
      let next := compilerAddress nodes digits (.args envArity callee actuals (stage + 1))
      let thread := s == .callByValueSeq
      let nextArgs := paramsFrom 4 width ++ paramsFrom 0 4
      return [(0, [primaryRule width (.call (base + 10) (.eps :: allArgs)),
        primaryRule width (.alt (compilerCall (base + 6) width) (.call (base + 20) (.eps :: allArgs)))]),
        (5, [⟨width + 2, .call argument (.param 0 :: .param 1 :: .param 2 :: .param 3 :: paramsFrom 6 (exprWidth - 4))⟩,
          ⟨width, .call (argument + 1) (paramsFrom 0 exprWidth)⟩,
          ⟨width + 4, .call next nextArgs⟩,
          ⟨width + 4, .call (next + 1) nextArgs⟩]),
        (10, captureBlock (base + 10) (base + 5) (base + 7) thread (width - 2)),
        (20, captureBlock (base + 20) (base + 5) (base + 8) thread (width - 2))]

/-- Table lookup enters the called body's environment at the predecessor clock value. -/
def compilerLookupFragments (source : MGrammar) (nodes : List CompileNode) (digits base callee : Nat) : CompileFragments :=
  match ruleAtM source.rules callee with
  | none => [(0, [compilerFailRule, compilerFailRule])]
  | some rule =>
    let width := 5 + 2 * digits + 4 * rule.arity
    let ctxSize := 4 + 4 * rule.arity
    let body := compilerAddress nodes digits (.expr rule.arity rule.body)
    let successClock := base + 10
    let failureClock := base + 11 + 2 * digits
    let successPack := base + 12 + 4 * digits
    let failurePack := base + 13 + 4 * digits
    let clockArgs := .param 4 :: (paramsFrom 5 (2 * digits) ++ paramsFrom 0 4 ++ paramsFrom (5 + 2 * digits) (4 * rule.arity))
    let bodyArgs := paramsFrom (1 + 2 * digits) 4 ++ (.param 0 :: (paramsFrom 1 (2 * digits) ++ paramsFrom (5 + 2 * digits) (4 * rule.arity)))
    [(0, [primaryRule width (.call successClock clockArgs), primaryRule width (.call failureClock clockArgs)]),
     (3, [⟨ctxSize, MExp.failAlways⟩]),
     (10, clockBlock successClock successPack (base + 3) digits ctxSize),
     (11 + 2 * digits, clockBlock failureClock failurePack (base + 3) digits ctxSize),
     (12 + 4 * digits, [⟨width, .call body bodyArgs⟩, ⟨width, .call (body + 1) bodyArgs⟩])]

def compilerFragments (source : MGrammar) (s : Strategy) (nodes : List CompileNode) (digits base : Nat) :
    CompileNode → CompileFragments
  | .expr arity e => compilerExpressionFragments source nodes digits base arity e
  | .args arity callee actuals stage => compilerArgumentFragments source s nodes digits base arity callee actuals stage
  | .lookup callee => compilerLookupFragments source nodes digits base callee

/-- Select a rule from disjoint, statically placed fragments; unused addresses explicitly fail. -/
def compilerFragmentAt : CompileFragments → Nat → MRule
  | [], _ => compilerFailRule
  | (offset, rules) :: fragments, slot =>
    if offset ≤ slot ∧ slot - offset < rules.length then (rules[slot - offset]?).getD compilerFailRule
    else compilerFragmentAt fragments slot

def compilerNodeRules (source : MGrammar) (s : Strategy) (nodes : List CompileNode)
    (digits base : Nat) (node : CompileNode) : List MRule :=
  (List.range (compilerSlotSize digits)).map
    (compilerFragmentAt (compilerFragments source s nodes digits base node))

def compilerGeneratedRules (source : MGrammar) (s : Strategy) (nodes : List CompileNode) (digits : Nat) : List MRule :=
  (List.range nodes.length).flatMap (fun i => compilerNodeRules source s nodes digits
    (4 + compilerSlotSize digits * i) (nodes[i]?.getD (.expr 0 .eps)))

def compilerFrontRules (source : MGrammar) (s : Strategy) (start : MExp) (alphabet : List Char)
    (digits : Nat) : List MRule :=
  let root := compilerAddress (compilerNodes source start) digits (.expr 0 start)
  let initial := .call root (.param 0 :: .eps :: .eps :: .param 0 :: .param 0 :: repeatPair (.param 0) .eps digits)
  let top := .alt (emptyInputP source s start)
    (.seq (andP .any) (.seq (.call 2 [.eps]) (.star .any)))
  [⟨4, spanEqBody 0 alphabet⟩, ⟨0, top⟩, ⟨1, findLengthBody 2 3⟩, ⟨1, initial⟩]

/-- The executable candidate translation. Whole-grammar correctness is a remaining proof obligation.
The finite alphabet parameter permits small executable checks; the intended unrestricted instance uses `unicodeAlphabet`. -/
def compileCandidate (source : MGrammar) (s : Strategy) (start : MExp) (alphabet : List Char) (digits : Nat) : MGrammar :=
  ⟨compilerFrontRules source s start alphabet digits ++
    compilerGeneratedRules source s (compilerNodes source start) digits⟩

def candidateStart : MExp := .call 1 []

end Shallot.MacroPeg.CBVtoCBN
