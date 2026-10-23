import MacroPeg.CBVtoCBN.CompilerAvailability

namespace Shallot.MacroPeg.CBVtoCBN

/-- Environments store source intervals in remaining-input coordinates. -/
abbrev CapturedEnv := List (Nat × Nat)

def ValidEnv (n : Nat) (E : CapturedEnv) : Prop := ∀ span ∈ E, span.2 ≤ span.1 ∧ span.1 ≤ n

def decodeEnv (x : List Char) (E : CapturedEnv) : List (List Char) :=
  E.map (fun span => pre x span.1 span.2)

def envArgs (n : Nat) : CapturedEnv → List MExp
  | [] => []
  | (a, b) :: E => skipN a :: skipN (n - a) :: skipN b :: skipN (n - b) :: envArgs n E

theorem envArgs_length (n : Nat) (E : CapturedEnv) : (envArgs n E).length = 4 * E.length := by
  induction E with
  | nil => rfl
  | cons span E ih => simp only [envArgs, List.length_cons, ih]; omega

theorem envArgs_append (n : Nat) (E F : CapturedEnv) : envArgs n (E ++ F) = envArgs n E ++ envArgs n F := by
  induction E with
  | nil => rfl
  | cons span E ih => simp only [List.cons_append, envArgs, ih]

theorem decodeEnv_length (x : List Char) (E : CapturedEnv) : (decodeEnv x E).length = E.length := List.length_map _

theorem decodeEnv_append (x : List Char) (E F : CapturedEnv) : decodeEnv x (E ++ F) = decodeEnv x E ++ decodeEnv x F :=
  List.map_append

def evalRest (x : List Char) (ds : List Nat) (E : CapturedEnv) : List MExp :=
  skipN x.length :: (clockArgs x.length ds ++ envArgs x.length E)

def evalArgs (x : List Char) (ds : List Nat) (E : CapturedEnv) (p q : Nat) : List MExp :=
  skipN p :: skipN (x.length - p) :: skipN q :: skipN (x.length - q) :: evalRest x ds E

theorem evalRest_length (x : List Char) (ds : List Nat) (E : CapturedEnv) :
    (evalRest x ds E).length = 1 + 2 * ds.length + 4 * E.length := by
  simp only [evalRest, List.length_cons, List.length_append, clockArgs_length, envArgs_length]
  omega

theorem evalArgs_length (x : List Char) (ds : List Nat) (E : CapturedEnv) (p q : Nat) :
    (evalArgs x ds E p q).length = 5 + 2 * ds.length + 4 * E.length := by
  simp only [evalArgs, List.length_cons, evalRest_length]
  omega

/-- A fixed source and start expression determine one target grammar and all its code addresses. -/
structure CompilerConfig where
  source : MGrammar
  strategy : Strategy
  start : MExp
  alphabet : List Char
  digits : Nat

def CompilerConfig.nodes (c : CompilerConfig) : List CompileNode := compilerNodes c.source c.start

def CompilerConfig.target (c : CompilerConfig) : MGrammar := compileCandidate c.source c.strategy c.start c.alphabet c.digits

def CompilerConfig.address (c : CompilerConfig) (node : CompileNode) : Nat := compilerAddress c.nodes c.digits node

def CompilerConfig.exprCall (c : CompilerConfig) (arity : Nat) (e : MExp) (failure : Bool) (args : List MExp) : MExp :=
  .call (c.address (.expr arity e) + if failure then 1 else 0) args

/-- Both total target predicates are kept separate, including when the source approximant is unknown. -/
def ExprCorrect (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (e : MExp) (p q : Nat) : Prop :=
  let result := evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) e p
  RootTest c.target (c.exprCall E.length e false (evalArgs x ds E p q)) x (result = some (some q)) ∧
    RootTest c.target (c.exprCall E.length e true (evalArgs x ds E p q)) x (result = some none)

theorem CompilerConfig.firstOrder (c : CompilerConfig) : c.target.FirstOrder :=
  compileCandidate_firstOrder _ _ _ _ _

theorem CompilerConfig.at (c : CompilerConfig) (node : CompileNode) (hn : node ∈ c.nodes)
    (slot : Nat) (hs : slot < compilerSlotSize c.digits) :
    ruleAtM c.target.rules (c.address node + slot) =
      some (compilerFragmentAt (compilerFragments c.source c.strategy c.nodes c.digits (c.address node) node) slot) :=
  compileCandidate_at _ _ _ _ _ node hn slot hs

end Shallot.MacroPeg.CBVtoCBN
