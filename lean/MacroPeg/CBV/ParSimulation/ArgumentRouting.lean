import MacroPeg.CBV.ParSimulation.ArgumentState

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters
open CBVtoCBN (paramsFrom subst_paramsFrom_take subst_paramsFrom_slice subst_paramsFrom_cons
  subst_paramsFrom substArgs_append)

theorem stageValues_subst_caller (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (p q : Nat) :
    MExp.substArgs (stageValues x ds E C p q) (paramsFrom 0 (3 + c.digits + 2 * E.length)) =
      stateValues x ds E p q := by
  rw [stageValues_split, show 3 + c.digits + 2 * E.length = (stateValues x ds E p q).length by
    rw [stateValues_length, hd]]
  exact subst_paramsFrom_take _ _

theorem stageValues_subst_all (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (stage : Nat) (hc : C.length = stage) (p q : Nat) :
    MExp.substArgs (stageValues x ds E C p q) (paramsFrom 0 (3 + c.digits + 2 * E.length + 2 * stage)) =
      stageValues x ds E C p q := by
  have hlen : (stageValues x ds E C p q).length = 3 + c.digits + 2 * E.length + 2 * stage := by
    rw [stageValues, stateValues_length, List.length_append, hd, hc]; omega
  rw [← hlen]
  exact subst_paramsFrom _

theorem stageValues_subst_finish (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E C : CapturedEnv) (stage : Nat) (hc : C.length = stage) (p q : Nat) :
    MExp.substArgs (stageValues x ds E C p q)
      (paramsFrom 0 (3 + c.digits) ++ paramsFrom (3 + c.digits + 2 * E.length) (2 * stage)) =
      stateValues x ds C p q := by
  let header := prefixValues x ([x.length - p, x.length - q, x.length] ++ ds)
  let caller := prefixValues x (envPositions x.length E)
  let captured := prefixValues x (envPositions x.length C)
  have hH : header.length = 3 + c.digits := by simp [header, hd]; omega
  have hE : caller.length = 2 * E.length := by simp [caller, envPositions_length]
  have hC : captured.length = 2 * stage := by simp [captured, envPositions_length, hc]
  have hState : stageValues x ds E C p q = header ++ (caller ++ captured) := by
    simp [stageValues, stateValues, statePositions, envPositions_append, header, caller, captured,
      prefixValues_append, prefixValues, List.append_assoc]
  have hResult : stateValues x ds C p q = header ++ captured := by
    simp [stateValues, statePositions, header, captured, prefixValues_append, prefixValues]
  rw [hState, hResult, substArgs_append, ← hH, subst_paramsFrom_take]
  have hTail := subst_paramsFrom_slice (header ++ caller) captured []
  simp only [List.append_nil, List.length_append, List.append_assoc, hH, hE, hC] at hTail
  rw [hH, hTail]

theorem argumentCandidateBody_subst (argument next : Nat) (j p q : MExp)
    (caller captured : List MExp) :
    MExp.subst (j :: p :: q :: (caller ++ captured))
      (argumentCandidateBody argument next (caller.length + 2) (caller.length + captured.length + 2)) =
      .seq (.call argument (p :: j :: caller))
        (.call next (j :: q :: ((caller ++ captured) ++ [p, j]))) := by
  have hCaller := subst_paramsFrom_slice [j, p, q] caller captured
  have hAll := subst_paramsFrom_slice [j, p, q] (caller ++ captured) []
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.cons_append, List.nil_append] at hCaller
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.cons_append, List.nil_append,
    List.append_nil, List.length_append] at hAll
  simp only [argumentCandidateBody, MExp.subst, MExp.substArgs, argAt, substArgs_append,
    Nat.add_sub_cancel_right]
  rw [hCaller, hAll]

theorem argumentCandidate_state_subst (c : CompilerConfig) (x : List Char) (ds : List Nat)
    (hd : ds.length = c.digits) (E C : CapturedEnv) (stage : Nat) (hc : C.length = stage)
    (argument next p q j : Nat) :
    MExp.subst (.lit (x.take (x.length - j)) :: stageValues x ds E C p q)
      (argumentCandidateBody argument next (3 + c.digits + 2 * E.length)
        (3 + c.digits + 2 * E.length + 2 * stage)) =
      .seq (.call argument (stateValues x ds E p j))
        (.call next (stageValues x ds E (C ++ [(p, j)]) j q)) := by
  let caller := prefixValues x (restPositions x.length ds E)
  let captured := prefixValues x (envPositions x.length C)
  have hCaller : caller.length + 2 = 3 + c.digits + 2 * E.length := by
    simp only [caller, prefixValues_length, restPositions_length, hd]; omega
  have hStage : caller.length + captured.length + 2 = 3 + c.digits + 2 * E.length + 2 * stage := by
    simp only [caller, captured, prefixValues_length, restPositions_length, envPositions_length, hd, hc]; omega
  have hState : stageValues x ds E C p q =
      .lit (x.take (x.length - p)) :: .lit (x.take (x.length - q)) :: (caller ++ captured) := by
    simp [stageValues, stateValues, statePositions, caller, captured, restPositions,
      envPositions_append, prefixValues_append, prefixValues, List.append_assoc]
  rw [hState, ← hStage, ← hCaller, argumentCandidateBody_subst]
  simp [stateValues, stageValues, statePositions, caller, captured, restPositions,
    envPositions_append, envPositions, prefixValues_append, prefixValues, List.append_assoc]

end Shallot.MacroPeg.CBV.ParSimulation
