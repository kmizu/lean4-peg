import MacroPeg.CBVtoCBN.CompiledSyntax

namespace Shallot.MacroPeg.CBVtoCBN

/-- Route a canonical expression context into the clock fragment, retaining positions and environment. -/
def lookupClockParams (clocks values : Nat) : List MExp :=
  .param 4 :: (paramsFrom 5 clocks ++ paramsFrom 0 4 ++ paramsFrom (5 + clocks) values)

/-- Route the clock fragment's result into a called rule body. -/
def lookupBodyParams (clocks values : Nat) : List MExp :=
  paramsFrom (1 + clocks) 4 ++ (.param 0 :: (paramsFrom 1 clocks ++ paramsFrom (5 + clocks) values))

theorem subst_lookupClockParams (p ps q qs N : MExp) (C V : List MExp) :
    MExp.substArgs ([p, ps, q, qs, N] ++ (C ++ V)) (lookupClockParams C.length V.length) =
      N :: (C ++ [p, ps, q, qs] ++ V) := by
  have hC := subst_paramsFrom_slice [p, ps, q, qs, N] C V
  have hP := subst_paramsFrom_slice [] [p, ps, q, qs] (N :: (C ++ V))
  have hV := subst_paramsFrom_slice ([p, ps, q, qs, N] ++ C) V []
  simp only [List.length_cons, List.length_nil, List.nil_append, List.cons_append, List.append_nil] at hC hP hV
  have hvpos : C.length + 1 + 1 + 1 + 1 + 1 = 5 + C.length := by omega
  rw [hvpos] at hV
  simp only [lookupClockParams, MExp.substArgs, substArgs_append, MExp.subst, List.cons_append, List.nil_append, argAt]
  rw [hC, hP, hV]

theorem subst_lookupBodyParams (p ps q qs N : MExp) (C V : List MExp) :
    MExp.substArgs (N :: (C ++ ([p, ps, q, qs] ++ V))) (lookupBodyParams C.length V.length) =
      [p, ps, q, qs, N] ++ (C ++ V) := by
  have hP := subst_paramsFrom_slice (N :: C) [p, ps, q, qs] V
  have hC := subst_paramsFrom_slice [N] C ([p, ps, q, qs] ++ V)
  have hV := subst_paramsFrom_slice (N :: (C ++ [p, ps, q, qs])) V []
  simp only [List.length_cons, List.length_nil, List.nil_append, List.cons_append, List.append_nil,
    List.length_append, List.append_assoc] at hC hP hV
  simp only [lookupBodyParams, substArgs_append, MExp.substArgs, MExp.subst, argAt,
    List.cons_append, List.nil_append]
  rw [show 1 + C.length = C.length + 1 by omega]
  rw [hP, hC]
  rw [show 5 + C.length = C.length + (0 + 1 + 1 + 1 + 1) + 1 by omega, hV]
  simp only [List.cons_append, List.nil_append]

/-- The source table oracle and the target lookup predicates share this canonical context. -/
def CompilerConfig.lookupCall (c : CompilerConfig) (callee : Nat) (failure : Bool) (args : List MExp) : MExp :=
  .call (c.address (.lookup callee) + primarySlot failure) args

def LookupCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv) (callee p q : Nat) : Prop :=
  let result := valAt (tblV c.source x c.strategy (clockValue x.length ds) callee (decodeEnv x E)) p
  RootTest c.target (c.lookupCall callee false (evalArgs x ds E p q)) x (result = some (some q)) ∧
    RootTest c.target (c.lookupCall callee true (evalArgs x ds E p q)) x (result = some none)

end Shallot.MacroPeg.CBVtoCBN
