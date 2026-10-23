import MacroPeg.CBV.ParSimulation.CompiledLookup

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode compilerSlotSize compilerFragmentAt clockValue finishSeq finishSeq_cons)

def SyntaxCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv) (e : MExp) : Prop :=
  ∀ p, p ≤ x.length → ∀ q, q ≤ x.length → ExprCorrect c x ds E e p q

def stageValues (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q : Nat) : List MExp :=
  stateValues x ds (E ++ C) p q

theorem stageValues_split (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q : Nat) :
    stageValues x ds E C p q = stateValues x ds E p q ++ prefixValues x (envPositions x.length C) := by
  simp [stageValues, stateValues, statePositions, envPositions_append, prefixValues_append, prefixValues, List.append_assoc]

def argumentResult (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (remaining : List MExp) (p : Nat) : Res :=
  let T := tblV c.source x .callByValueSeq (clockValue x.length ds)
  finishSeq (fun W q => valAt (T callee (decodeEnv x C ++ W)) q)
    (evSeqArgs c.source x .callByValueSeq T (decodeEnv x E) remaining p)

theorem argumentResult_nil (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee p : Nat) : argumentResult c x ds E C callee [] p =
      valAt (tblV c.source x .callByValueSeq (clockValue x.length ds) callee (decodeEnv x C)) p := by
  simp [argumentResult, evSeqArgs, finishSeq]

theorem argumentResult_cons (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (a : MExp) (remaining : List MExp) (p : Nat) :
    argumentResult c x ds E C callee (a :: remaining) p =
      CBVtoCBN.seqResult (sourceResult c x ds E a p)
        (fun j => argumentResult c x ds E (C ++ [(p, j)]) callee remaining j) := by
  unfold argumentResult
  rw [finishSeq_cons]
  simp [sourceResult, decodeEnv, List.map_append, List.append_assoc]

theorem ValidEnv.append_capture {n : Nat} {C : CapturedEnv} (hv : ValidEnv n C) {p j : Nat}
    (hp : p ≤ n) (hj : j ≤ p) : ValidEnv n (C ++ [(p, j)]) := by
  intro span hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hv span hm
  · have he := List.mem_singleton.mp hm
    subst span
    exact ⟨hj, hp⟩

def argumentRule (source : MGrammar) (nodes : List CompileNode) (digits base arity callee : Nat)
    (actuals : List MExp) (stage : Nat) (failure : Bool) : MRule :=
  compilerFragmentAt (argumentFragments source nodes digits base arity callee actuals stage) (primarySlot failure)

theorem argumentRule_arity (source : MGrammar) (nodes : List CompileNode) (digits base arity callee : Nat)
    (actuals : List MExp) (stage : Nat) (failure : Bool) :
    (argumentRule source nodes digits base arity callee actuals stage failure).arity =
      3 + digits + 2 * arity + 2 * stage := by
  cases hr : ruleAtM source.rules callee with
  | none => cases failure <;> simp [argumentRule, argumentFragments, hr, compilerFragmentAt, primarySlot]
  | some rule =>
    by_cases ha : rule.arity = actuals.length
    · by_cases ht : stage = actuals.length
      · cases failure <;> simp [argumentRule, argumentFragments, hr, ha, ht, compilerFragmentAt, primarySlot]
      · cases hget : actuals[stage]? <;> cases failure <;>
          simp [argumentRule, argumentFragments, hr, ha, ht, hget, compilerFragmentAt, primarySlot]
    · cases failure <;> simp [argumentRule, argumentFragments, hr, ha, compilerFragmentAt, primarySlot]

def CompilerConfig.argumentCall (c : CompilerConfig) (arity callee : Nat) (actuals : List MExp)
    (stage : Nat) (failure : Bool) (args : List MExp) : MExp :=
  .call (c.address (.args arity callee actuals stage) + primarySlot failure) args

theorem CompilerConfig.argument_unfold (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E C : CapturedEnv) (callee : Nat) (actuals : List MExp) (stage : Nat)
    (hc : C.length = stage) (hn : .args E.length callee actuals stage ∈ c.nodes)
    (p q : Nat) (failure : Bool) (P : Prop) :
    Predicate c.target .callByValuePar (c.argumentCall E.length callee actuals stage failure (stageValues x ds E C p q)) x P ↔
    Predicate c.target .callByValuePar (MExp.subst (stageValues x ds E C p q)
      (argumentRule c.source c.nodes c.digits (c.address (.args E.length callee actuals stage))
        E.length callee actuals stage failure).body) x P := by
  have hr := c.at (.args E.length callee actuals stage) hn (primarySlot failure)
    (by cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega)
  change ruleAtM c.target.rules (c.address (.args E.length callee actuals stage) + primarySlot failure) =
    some (argumentRule c.source c.nodes c.digits (c.address (.args E.length callee actuals stage))
      E.length callee actuals stage failure) at hr
  have hv := prefixValues_args c.target x (statePositions x.length ds (E ++ C) p q)
  have ha : (argumentRule c.source c.nodes c.digits (c.address (.args E.length callee actuals stage))
      E.length callee actuals stage failure).arity = (stageValues x ds E C p q).length := by
    rw [argumentRule_arity, stageValues, stateValues_length, List.length_append, hd, hc]; omega
  have ho : ∀ r, SObs c.target .callByValuePar
      (c.argumentCall E.length callee actuals stage failure (stageValues x ds E C p q)) x r ↔
      SObs c.target .callByValuePar (MExp.subst (stageValues x ds E C p q)
        (argumentRule c.source c.nodes c.digits (c.address (.args E.length callee actuals stage))
          E.length callee actuals stage failure).body) x r := fun r => par_call_iff hr ha hv r
  exact ⟨fun h => ⟨fun hp => (ho _).1 (h.1 hp), fun hp => (ho _).1 (h.2 hp)⟩,
    fun h => ⟨fun hp => (ho _).2 (h.1 hp), fun hp => (ho _).2 (h.2 hp)⟩⟩

def ArgsCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (actuals : List MExp) (stage p q : Nat) : Prop :=
  Predicate c.target .callByValuePar
    (c.argumentCall E.length callee actuals stage false (stageValues x ds E C p q)) x
    (argumentResult c x ds E C callee (actuals.drop stage) p = some (some q)) ∧
  Predicate c.target .callByValuePar
    (c.argumentCall E.length callee actuals stage true (stageValues x ds E C p q)) x
    (argumentResult c x ds E C callee (actuals.drop stage) p = some none)

end Shallot.MacroPeg.CBV.ParSimulation
