import MacroPeg.CBV.LastCodewordHelpers
import MacroPeg.CBV.SelectedCodewordRecursive

/-! Both the header and the selected stop may use the same independent
nullary recursive parser component. The unary verifier retains its value. -/
namespace Shallot.MacroPeg.CBV.SelectedCodewordHelpers
open ClockFreezing (Table)
open RecursiveParserStability (Installed Lexical)
open RecursiveCodeGrammar (canonical)
open LastCodewordHelpers (lexical_environment lexical_syntax)

structure Header extends RecursiveCodeGrammar.Header where
  condition : MExp
  conditionLexical : Lexical bodies.length condition

abbrev lexical (H : Header) := RecursiveCodeGrammar.lexical H.toHeader
abbrev LexicalTable (H : Header) := RecursiveCodeGrammar.LexicalTable H.toHeader
abbrev pick (H : Header) := LastCodewordHelpers.pick H.toHeader
abbrev floor (H : Header) := LastCodewordHelpers.floor H.toHeader
abbrev syntax_eval (H : Header) := LastCodewordHelpers.syntax_eval H.toHeader
abbrev lexical_table (H : Header) := LastCodewordHelpers.lexical_table H.toHeader
abbrev physical_lexical (H : Header) := LastCodewordHelpers.physical_lexical H.toHeader
abbrev prefixAt (H : Header) := LastCodewordHelpers.prefixAt H.toHeader
abbrev prefix_eval (H : Header) := LastCodewordHelpers.prefix_eval H.toHeader

def step (H : Header) : MExp := SelectedCodewordVerification.step H.head H.condition

theorem step_lexical (H : Header) : Lexical H.bodies.length (step H) :=
  ⟨H.lexical,H.lexical,H.conditionLexical⟩

def argument (H : Header) : MExp := .star (step H)
theorem argument_lexical (H : Header) : Lexical H.bodies.length (argument H) := step_lexical H
def argumentAt (H : Header) (x : List Char) (p : Nat) : Res := lexical H (argument H) x p

def verifier (H : Header) : MExp := SelectedCodewordVerification.verifier (step H)

theorem verifier_syntax (H : Header) : HelperArgument.Syntax H.bodies.length (verifier H) :=
  ⟨⟨⟨lexical_syntax _ _ (step_lexical H),True.intro⟩,lexical_syntax _ _ (step_lexical H)⟩,True.intro⟩

def wordProbe (H : Header) (x : List Char) (p : Nat) : Res :=
  match lexical H H.head x p with
  | some (some j) => evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
      (canonical H.bodies x) [pre x p j] (verifier H) j
  | other => other

def probe (H : Header) (x : List Char) (p : Nat) : Res :=
  SelectedCodewordVerification.probe (RecursiveParserStability.grammar H.bodies) x .callByValuePar
    (canonical H.bodies x) H.head H.condition p

def guard (H : Header) : MExp := .alt (.notP (step H)) (.andP (.call H.bodies.length [H.head]))

theorem stable (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (hr : ruleAtM g.rules H.bodies.length=some ⟨1,verifier H⟩)
    (x : List Char) (s : Strategy) : ClockFreezing.StableRows g x s (pick H) (floor H x) :=
  LastCodewordHelpers.stable_unary H.toHeader (verifier H) (verifier_syntax H) g hg hr x s

theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (argument H) p=argumentAt H x p :=
  hLex E _ (argument_lexical H) p hp

theorem step_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (step H) p=lexical H (step H) x p :=
  hLex E _ (step_lexical H) p hp

theorem probe_eval (H : Header) (g : MGrammar) (hg : Installed H.bodies g)
    (x : List Char) (s : Strategy) (T : Table) (hOk : OkTV x.length T)
    (hLex : LexicalTable H g x s T) (p : Nat) (hp : p≤x.length) :
    SelectedCodewordVerification.probe g x s T H.head H.condition p=probe H x p := by
  unfold probe SelectedCodewordVerification.probe
  rw [show SelectedCodewordVerification.step H.head H.condition=step H from rfl,
    step_eval H g x s T hLex [] p hp]
  change (match lexical H (step H) x p with
    | some none => some (some p)
    | some (some _) => match evV g x s T [] H.head p with
      | some (some j) => evV g x s T [pre x p j] (verifier H) j
      | other => other
    | none => none)=
    (match lexical H (step H) x p with
    | some none => some (some p)
    | some (some _) => wordProbe H x p
    | none => none)
  cases lexical H (step H) x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      rw [hLex [] H.head H.lexical p hp]
      change (match lexical H H.head x p with
        | some (some j) => evV g x s T [pre x p j] (verifier H) j | other => other)=
        (match lexical H H.head x p with
        | some (some j) => evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
          (canonical H.bodies x) [pre x p j] (verifier H) j | other => other)
      cases hv : lexical H H.head x p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j =>
          have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp hv).1
          exact syntax_eval H g hg x s T hOk hLex [pre x p j] (verifier H) (verifier_syntax H) j hj

end Shallot.MacroPeg.CBV.SelectedCodewordHelpers
