import MacroPeg.CBV.ParSimulation.Repetition
import MacroPeg.CBV.PrefixClockGrammar
import MacroPeg.CBVtoCBN.CompilerPlan

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters
open CBVtoCBN (CompileNode compilerNodes compilerEnvArity compilerCaptured compilerSlotSize
  paramsFrom compilerFragmentAt CompileFragments compilerFailRule emptyInputP)

/-! Executable Seq-to-Par translation. `Recognition.translate_recognizes`
proves language preservation for its unrestricted instance. Explicit
alphabet and clock parameters remain available for executable checks. -/

def address (nodes : List CompileNode) (digits : Nat) (node : CompileNode) : Nat :=
  8 + compilerSlotSize digits * nodes.idxOf node

def width (source : MGrammar) (digits : Nat) (node : CompileNode) : Nat :=
  3 + digits + 2 * compilerEnvArity source node + 2 * compilerCaptured node

def failureAdapter (target fullWidth : Nat) : MRule :=
  ⟨fullWidth - 1, .call target (.param 0 :: .lit [] :: paramsFrom 1 (fullWidth - 2))⟩

def parameterFailureRules (entry order matcher : Nat) : List MRule :=
  [⟨3, parameterFailure (entry + 1) (.param 0) (.param 1) (.param 2)⟩,
    ⟨4, existsBody (entry + 1) (entry + 2) 3⟩,
    ⟨4, parameterCandidateBody order matcher⟩]

def notCandidateBody (success ctxSize : Nat) : MExp :=
  .call success (.param 1 :: .param 0 :: paramsFrom 2 ctxSize)

def expressionFragments (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) : CompileFragments := Id.run do
  let w := 3 + digits + 2 * arity
  let rest := w - 2
  let addr := fun e => address nodes digits (.expr arity e)
  let all := paramsFrom 0 w
  let adapter := failureAdapter (base + 1) w
  let primary := fun yes no => (0, [⟨w, yes⟩, ⟨w, no⟩, adapter])
  let terminal := fun a => [primary (terminalSuccess 0 (.param 0) (.param 1) a)
    (terminalFailure (.param 0) a)]
  match e with
  | .eps => return terminal .eps
  | .any => return terminal .any
  | .chr c => return terminal (.chr c)
  | .range lo hi => return terminal (.range lo hi)
  | .lit s => return terminal (.lit s)
  | .param k =>
    if k < arity then
      let v := 3 + digits + 2 * k
      return [primary (parameterSuccess 1 2 (.param v) (.param (v + 1)) (.param 0) (.param 1))
          (.call (base + 10) [.param v, .param (v + 1), .param 0]),
        (10, parameterFailureRules (base + 10) 1 2)]
    else return [primary MExp.failAlways .eps]
  | .alt a b =>
    return [primary
      (.alt (.call (addr a) all) (.seq (.call (addr a + 1) all) (.call (addr b) all)))
      (.seq (.call (addr a + 1) all) (.call (addr b + 1) all))]
  | .seq a b =>
    return [primary (.call (base + 10) (.lit [] :: all))
        (.alt (.call (addr a + 1) all) (.call (base + 20) (.lit [] :: .param 0 :: paramsFrom 2 rest))),
      (10, [⟨w + 1, existsBody (base + 10) (base + 11) w⟩,
        ⟨w + 1, sequenceTestBody (addr a) (addr b) rest⟩]),
      (20, [⟨w, existsBody (base + 20) (base + 21) (w - 1)⟩,
        ⟨w, sequenceFailureTestBody (addr a) (addr b + 2) rest⟩])]
  | .star a =>
    return [primary (.call (base + 10) all) MExp.failAlways,
      (10, [⟨w, repetitionBody 0 (addr a + 2) (base + 11) rest⟩,
        ⟨w + 1, existsBody (base + 11) (base + 12) w⟩,
        ⟨w + 1, repetitionCandidateBody 1 (addr a) (base + 10) rest⟩])]
  | .notP a =>
    return [primary (.seq (.call 0 [.param 0, .param 1]) (.call (addr a + 1) all))
        (.call (base + 10) (.lit [] :: .param 0 :: paramsFrom 2 rest)),
      (10, [⟨w, existsBody (base + 10) (base + 11) (w - 1)⟩,
        ⟨w, notCandidateBody (addr a) rest⟩])]
  | .call callee actuals =>
    let stage := address nodes digits (.args arity callee actuals 0)
    return [primary (.call stage all) (.call (stage + 1) all)]
  | _ => return [primary MExp.failAlways .eps]

/-- The candidate endpoint precedes the caller's entire stage state. The
new interval is appended only after the argument-success predicate holds. -/
def argumentCandidateBody (argument next callerWidth stageWidth : Nat) : MExp :=
  .seq (.call argument (.param 1 :: .param 0 :: paramsFrom 3 (callerWidth - 2)))
    (.call next (.param 0 :: .param 2 ::
      (paramsFrom 3 (stageWidth - 2) ++ [.param 1, .param 0])))

def argumentFragments (source : MGrammar) (nodes : List CompileNode) (digits base arity callee : Nat)
    (actuals : List MExp) (stage : Nat) : CompileFragments := Id.run do
  let callerWidth := 3 + digits + 2 * arity
  let w := callerWidth + 2 * stage
  let all := paramsFrom 0 w
  let primary := fun yes no => (0, [⟨w, yes⟩, ⟨w, no⟩])
  match ruleAtM source.rules callee with
  | none => return [primary MExp.failAlways .eps]
  | some rule =>
    if rule.arity ≠ actuals.length then return [primary MExp.failAlways .eps]
    else if stage = actuals.length then
      let lookup := address nodes digits (.lookup callee)
      let packed := paramsFrom 0 (3 + digits) ++ paramsFrom callerWidth (2 * stage)
      return [primary (.call lookup packed) (.call (lookup + 1) packed)]
    else
      match actuals[stage]? with
      | none => return [primary MExp.failAlways .eps]
      | some a =>
        let arg := address nodes digits (.expr arity a)
        let next := address nodes digits (.args arity callee actuals (stage + 1))
        return [primary (.call (base + 10) (.lit [] :: all))
            (.alt (.call (arg + 1) (paramsFrom 0 callerWidth)) (.call (base + 20) (.lit [] :: all))),
          (10, [⟨w + 1, existsBody (base + 10) (base + 11) w⟩,
            ⟨w + 1, argumentCandidateBody arg next callerWidth w⟩]),
          (20, [⟨w + 1, existsBody (base + 20) (base + 21) w⟩,
            ⟨w + 1, argumentCandidateBody arg (next + 1) callerWidth w⟩])]

def lookupClockParams (digits envSize : Nat) : List MExp :=
  .param 2 :: (paramsFrom 3 digits ++ .param 0 :: .param 1 :: paramsFrom (3 + digits) envSize)

def lookupPackParams (digits envSize : Nat) : List MExp :=
  .param (1 + digits) :: .param (2 + digits) :: .param 0 ::
    (paramsFrom 1 digits ++ paramsFrom (3 + digits) envSize)

def lookupFragments (source : MGrammar) (nodes : List CompileNode) (digits base callee : Nat) : CompileFragments := Id.run do
  match ruleAtM source.rules callee with
  | none => return [(0, [⟨0, MExp.failAlways⟩, ⟨0, .eps⟩])]
  | some rule =>
    let w := 3 + digits + 2 * rule.arity
    let ctxSize := 2 + 2 * rule.arity
    let body := address nodes digits (.expr rule.arity rule.body)
    let failureClock := base + 11 + 2 * digits
    let successPack := base + 12 + 4 * digits
    let failurePack := base + 13 + 4 * digits
    let onZero := base + 14 + 4 * digits
    let rotated := lookupClockParams digits (2 * rule.arity)
    let packed := lookupPackParams digits (2 * rule.arity)
    return [(0, [⟨w, .call (base + 10) rotated⟩, ⟨w, .call failureClock rotated⟩]),
      (10, clockBlock (base + 10) 0 successPack onZero digits ctxSize),
      (11 + 2 * digits, clockBlock failureClock 0 failurePack onZero digits ctxSize),
      (12 + 4 * digits, [⟨w, .call body packed⟩, ⟨w, .call (body + 1) packed⟩, ⟨ctxSize, MExp.failAlways⟩])]

def fragments (source : MGrammar) (nodes : List CompileNode) (digits base : Nat) : CompileNode → CompileFragments
  | .expr a e => expressionFragments nodes digits base a e
  | .args a callee actuals stage => argumentFragments source nodes digits base a callee actuals stage
  | .lookup callee => lookupFragments source nodes digits base callee

def nodeRules (source : MGrammar) (nodes : List CompileNode) (digits base : Nat) (node : CompileNode) : List MRule :=
  (List.range (compilerSlotSize digits)).map (compilerFragmentAt (fragments source nodes digits base node))

def generatedRules (source : MGrammar) (nodes : List CompileNode) (digits : Nat) : List MRule :=
  (List.range nodes.length).flatMap (fun i => nodeRules source nodes digits
    (8 + compilerSlotSize digits * i) (nodes[i]?.getD (.expr 0 .eps)))

def frontRules (source : MGrammar) (start : MExp) (alphabet : List Char) (digits : Nat) : List MRule :=
  let root := address (compilerNodes source start) digits (.expr 0 start)
  let initial := .call root (.lit [] :: .param 0 :: .param 0 :: List.replicate digits (.param 0))
  let top := .alt (emptyInputP source .callByValueSeq start)
    (.seq (.andP .any) (.seq (.call 4 [.star .any]) (.star .any)))
  [⟨2, equalBody 0⟩, ⟨2, leBody 1 0⟩, ⟨4, intervalBody 2 0 alphabet⟩,
    ⟨0, top⟩, ⟨1, initial⟩, compilerFailRule, compilerFailRule, compilerFailRule]

def compileCandidate (source : MGrammar) (start : MExp) (alphabet : List Char) (digits : Nat) : MGrammar :=
  ⟨frontRules source start alphabet digits ++ generatedRules source (compilerNodes source start) digits⟩

def candidateStart : MExp := .call 3 []

end Shallot.MacroPeg.CBV.ParSimulation
