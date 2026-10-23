import MacroPeg.CBV.ParSimulation.CompilerLayout

namespace Shallot.MacroPeg.CBV.ParSimulation

open PrefixCounters RootObservation
open CBVtoCBN (CompileNode compilerSlotSize compilerFragmentAt clockValue)

/-- Source captures use remaining-input coordinates, as does the source
table evaluator. Target values encode the two absolute endpoints. -/
abbrev CapturedEnv := List (Nat × Nat)

def ValidEnv (n : Nat) (E : CapturedEnv) : Prop :=
  ∀ span ∈ E, span.2 ≤ span.1 ∧ span.1 ≤ n

def decodeEnv (x : List Char) (E : CapturedEnv) : List (List Char) :=
  E.map (fun span => pre x span.1 span.2)

def envPositions (n : Nat) : CapturedEnv → List Nat
  | [] => []
  | (a, b) :: E => (n - a) :: (n - b) :: envPositions n E

theorem envPositions_length (n : Nat) (E : CapturedEnv) :
    (envPositions n E).length = 2 * E.length := by
  induction E with
  | nil => rfl
  | cons span E ih => simp only [envPositions, List.length_cons, ih]; omega

theorem envPositions_append (n : Nat) (E C : CapturedEnv) :
    envPositions n (E ++ C) = envPositions n E ++ envPositions n C := by
  induction E with
  | nil => rfl
  | cons span E ih => simp only [envPositions, List.cons_append, ih]

def statePositions (n : Nat) (ds : List Nat) (E : CapturedEnv) (p q : Nat) : List Nat :=
  (n - p) :: (n - q) :: n :: (ds ++ envPositions n E)

def stateValues (x : List Char) (ds : List Nat) (E : CapturedEnv) (p q : Nat) : List MExp :=
  prefixValues x (statePositions x.length ds E p q)

theorem stateValues_length (x : List Char) (ds : List Nat) (E : CapturedEnv) (p q : Nat) :
    (stateValues x ds E p q).length = 3 + ds.length + 2 * E.length := by
  simp only [stateValues, prefixValues_length, statePositions, List.length_cons,
    List.length_append, envPositions_length]
  omega

def primarySlot (failure : Bool) : Nat := if failure then 1 else 0

def expressionRule (nodes : List CompileNode) (digits base arity : Nat) (e : MExp) (failure : Bool) : MRule :=
  compilerFragmentAt (expressionFragments nodes digits base arity e) (primarySlot failure)

theorem expressionRule_arity (nodes : List CompileNode) (digits base arity : Nat)
    (e : MExp) (failure : Bool) : (expressionRule nodes digits base arity e failure).arity = 3 + digits + 2 * arity := by
  cases e with
  | param k =>
    by_cases hk : k < arity <;> cases failure <;>
      simp [expressionRule, expressionFragments, compilerFragmentAt, primarySlot, hk]
  | eps | any | chr _ | range _ _ | lit _ | alt _ _ | seq _ _ | star _ | notP _ | call _ _
    | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ =>
    cases failure <;> simp [expressionRule, expressionFragments, compilerFragmentAt, primarySlot]

def CompilerConfig.exprCall (c : CompilerConfig) (arity : Nat) (e : MExp)
    (failure : Bool) (args : List MExp) : MExp :=
  .call (c.address (.expr arity e) + primarySlot failure) args

theorem CompilerConfig.equal_rule (c : CompilerConfig) :
    ruleAtM c.target.rules 0 = some ⟨2, equalBody 0⟩ := rfl

theorem CompilerConfig.order_rule (c : CompilerConfig) :
    ruleAtM c.target.rules 1 = some ⟨2, leBody 1 0⟩ := rfl

theorem CompilerConfig.interval_rule (c : CompilerConfig) :
    ruleAtM c.target.rules 2 = some ⟨4, intervalBody 2 0 c.alphabet⟩ := rfl

theorem CompilerConfig.expr_unfold (c : CompilerConfig) {arity : Nat} {e : MExp}
    (hn : .expr arity e ∈ c.nodes) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (he : E.length = arity) (p q : Nat) (failure : Bool) (P : Prop) :
    Predicate c.target .callByValuePar (c.exprCall arity e failure (stateValues x ds E p q)) x P ↔
      Predicate c.target .callByValuePar
        (MExp.subst (stateValues x ds E p q)
          (expressionRule c.nodes c.digits (c.address (.expr arity e)) arity e failure).body) x P := by
  have hs : primarySlot failure < compilerSlotSize c.digits := by
    cases failure <;> simp [primarySlot, compilerSlotSize] <;> omega
  have hr := c.at (.expr arity e) hn (primarySlot failure) hs
  change ruleAtM c.target.rules (c.address (.expr arity e) + primarySlot failure) =
    some (expressionRule c.nodes c.digits (c.address (.expr arity e)) arity e failure) at hr
  have hArgs := prefixValues_args c.target x (statePositions x.length ds E p q)
  have hArity : (expressionRule c.nodes c.digits (c.address (.expr arity e)) arity e failure).arity =
      (stateValues x ds E p q).length := by rw [expressionRule_arity, stateValues_length, hd, he]
  have hObs : ∀ r, SObs c.target .callByValuePar (c.exprCall arity e failure (stateValues x ds E p q)) x r ↔
      SObs c.target .callByValuePar (MExp.subst (stateValues x ds E p q)
        (expressionRule c.nodes c.digits (c.address (.expr arity e)) arity e failure).body) x r :=
    fun r => par_call_iff hr hArity hArgs r
  exact ⟨fun h => ⟨fun hp => (hObs _).1 (h.1 hp), fun hp => (hObs _).1 (h.2 hp)⟩,
    fun h => ⟨fun hp => (hObs _).2 (h.1 hp), fun hp => (hObs _).2 (h.2 hp)⟩⟩

def sourceResult (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (e : MExp) (p : Nat) : Res :=
  evV c.source x .callByValueSeq (tblV c.source x .callByValueSeq (clockValue x.length ds)) (decodeEnv x E) e p

def ExprCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (e : MExp) (p q : Nat) : Prop :=
  Predicate c.target .callByValuePar (c.exprCall E.length e false (stateValues x ds E p q)) x
    (sourceResult c x ds E e p = some (some q)) ∧
  Predicate c.target .callByValuePar (c.exprCall E.length e true (stateValues x ds E p q)) x
    (sourceResult c x ds E e p = some none)

theorem expressionRule_atom (nodes : List CompileNode) (digits base arity : Nat) (a : CBVtoCBN.Atom)
    (failure : Bool) :
    expressionRule nodes digits base arity a.exp failure =
      ⟨3 + digits + 2 * arity,
        if failure then terminalFailure (.param 0) a else terminalSuccess 0 (.param 0) (.param 1) a⟩ := by
  cases a <;> cases failure <;> rfl

/-- The atom clauses of the actual generated Par code match the source
table evaluator, rather than only an independently supplied template. -/
theorem compiledAtom_correct (c : CompilerConfig) (x : List Char) (ds : List Nat) (hd : ds.length = c.digits)
    (E : CapturedEnv) (a : CBVtoCBN.Atom) (hn : .expr E.length a.exp ∈ c.nodes)
    (p q : Nat) (hp : p ≤ x.length) (hq : q ≤ x.length) : ExprCorrect c x ds E a.exp p q := by
  constructor
  · rw [c.expr_unfold hn x ds hd E rfl p q false, expressionRule_atom]
    change Predicate c.target .callByValuePar
      (MExp.subst (stateValues x ds E p q) (terminalSuccess 0 (.param 0) (.param 1) a)) x _
    have hsub : MExp.subst (stateValues x ds E p q) (terminalSuccess 0 (.param 0) (.param 1) a) =
        terminalSuccess 0 (.lit (x.take (x.length - p))) (.lit (x.take (x.length - q))) a := by
      cases a <;> rfl
    rw [hsub]
    exact terminal_success_test c.equal_rule _ _ _ _ _ a p q hp hq
  · rw [c.expr_unfold hn x ds hd E rfl p q true, expressionRule_atom]
    change Predicate c.target .callByValuePar
      (MExp.subst (stateValues x ds E p q) (terminalFailure (.param 0) a)) x _
    have hsub : MExp.subst (stateValues x ds E p q) (terminalFailure (.param 0) a) =
        terminalFailure (.lit (x.take (x.length - p))) a := by cases a <;> rfl
    rw [hsub]
    exact terminal_failure_test _ _ _ _ _ _ a p hp

end Shallot.MacroPeg.CBV.ParSimulation
