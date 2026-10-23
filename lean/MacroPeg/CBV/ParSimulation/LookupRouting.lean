import MacroPeg.CBV.ParSimulation.CompiledSequence

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (substArgs_append subst_paramsFrom_slice subst_param_at RulesAt predClock)

theorem lookupClockParams_subst (p q N : MExp) (ds env : List MExp) :
    MExp.substArgs (p :: q :: N :: (ds ++ env)) (lookupClockParams ds.length env.length) =
      N :: (ds ++ p :: q :: env) := by
  have hD := subst_paramsFrom_slice [p, q, N] ds env
  have hE := subst_paramsFrom_slice (p :: q :: N :: ds) env []
  simp only [List.length_cons, List.length_nil, Nat.zero_add, List.cons_append, List.nil_append] at hD
  simp only [List.length_cons, List.append_nil, List.cons_append] at hE
  simp only [lookupClockParams, MExp.substArgs, substArgs_append, MExp.subst, argAt]
  rw [hD, show 3 + ds.length = ds.length + 1 + 1 + 1 by omega, hE]

theorem lookupPackParams_subst (p q N : MExp) (ds env : List MExp) :
    MExp.substArgs (N :: (ds ++ p :: q :: env)) (lookupPackParams ds.length env.length) =
      p :: q :: N :: (ds ++ env) := by
  have hP := subst_param_at (N :: ds) p (q :: env)
  have hQ := subst_param_at ((N :: ds) ++ [p]) q env
  have hD := subst_paramsFrom_slice [N] ds (p :: q :: env)
  have hE := subst_paramsFrom_slice ((N :: ds) ++ [p, q]) env []
  simp only [List.length_cons, List.length_append, List.length_nil, Nat.zero_add,
    List.cons_append, List.nil_append, List.append_assoc, List.append_nil] at hP hQ hD hE
  have hP' : MExp.subst (N :: (ds ++ p :: q :: env)) (.param (1 + ds.length)) = p := by
    simpa only [Nat.add_comm] using hP
  have hQ' : MExp.subst (N :: (ds ++ p :: q :: env)) (.param (2 + ds.length)) = q := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hQ
  simp only [lookupPackParams, MExp.substArgs, substArgs_append, hP', hQ']
  rw [hD, show 3 + ds.length = ds.length + 1 + (1 + (1 + 0)) by omega, hE]
  rfl

theorem RulesAt.clock_iff {g : MGrammar} {entry equal next onZero digits : Nat} (ctx : List Nat)
    (h : RulesAt g entry (clockBlock entry equal next onZero digits ctx.length))
    (hEqual : ruleAtM g.rules equal = some ⟨2, equalBody equal⟩)
    (x : List Char) (ds : List Nat) (hd : ds.length = digits) (hv : ∀ k ∈ ds, k ≤ x.length)
    (r : Option (List Char)) :
    SObs g .callByValuePar (.call entry (prefixValues x (x.length :: (ds ++ ctx)))) x r ↔
      match predClock x.length ds with
      | none => SObs g .callByValuePar (.call onZero (prefixValues x ctx)) x r
      | some out => SObs g .callByValuePar (.call next (prefixValues x (x.length :: (out ++ ctx)))) x r := by
  obtain ⟨pre, tail, hpre, hg⟩ := h.split (by simp [clockBlock])
  have hEq := hEqual
  rw [hg] at hEq
  have ht := clockBlock_iff pre tail equal next onZero digits ctx (by simpa only [hpre] using hEq) x ds hd hv r
  cases hc : predClock x.length ds <;> simpa only [hc, hpre, ← hg] using ht

end Shallot.MacroPeg.CBV.ParSimulation
