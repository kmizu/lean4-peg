import Complexity.BoolCircuit
import MacroPeg.CBV.ForwardBooleanSyntax

/-! Compile numbered Boolean circuits to the data language of one fixed Seq
grammar. This is an explicit input encoding, not an input-preserving compiler
for arbitrary Par grammars. -/
namespace Shallot.MacroPeg.CBV.CircuitProgram
open ForwardQueryScan ForwardBooleanProgram
namespace Circuit
abbrev Gate := Complexity.BoolCircuit.Gate
abbrev values := Complexity.BoolCircuit.values
end Circuit

def lower : Circuit.Gate → Gate
  | .bit true => .yes
  | .bit false => .no
  | .neg i => .neg i
  | .conj i j => .both i j

def compileFrom (initial : List Node) (gates : List Circuit.Gate) : List Node :=
  gates.foldl (fun P g => (P.length,lower g)::P) initial

def program (gates : List Circuit.Gate) : List Node := compileFrom [] gates

def input (gates : List Circuit.Gate) (root : Nat) : List Char := identifier root ++ encode (program gates)

theorem lower_eval (W : List Bool) (g : Circuit.Gate) :
    gateValue (fun i => W.getD i false) (lower g) = g.eval W := by
  cases g with
  | bit b => cases b <;> rfl
  | neg _ | conj _ _ => rfl

theorem lookup_snoc (W : List Bool) (b : Bool) (i : Nat) :
    (W++[b]).getD i false = if i=W.length then b else W.getD i false := by
  induction W generalizing i with
  | nil => cases i <;> rfl
  | cons w W ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

theorem compileFrom_length (gates : List Circuit.Gate) (initial : List Node) :
    (compileFrom initial gates).length = initial.length + gates.length := by
  induction gates generalizing initial with
  | nil => simp [compileFrom]
  | cons g gs ih =>
    simpa only [compileFrom,List.foldl_cons,List.length_cons,Nat.add_assoc,Nat.add_comm 1]
      using ih ((initial.length,lower g)::initial)

theorem compileFrom_correct (gates : List Circuit.Gate) (P : List Node) (W : List Bool)
    (hlen : P.length=W.length) (hvalue : value P = fun i => W.getD i false) :
    value (compileFrom P gates) = fun i => (Complexity.BoolCircuit.run W gates).getD i false := by
  induction gates generalizing P W with
  | nil => exact hvalue
  | cons g gs ih =>
    apply ih ((P.length,lower g)::P) (W++[g.eval W])
    · simp [hlen]
    · funext i
      simp only [value,hvalue,lower_eval,lookup_snoc,hlen]

theorem program_length (gates : List Circuit.Gate) : (program gates).length = gates.length := by
  simpa only [program,List.length_nil,Nat.zero_add] using compileFrom_length gates []

theorem program_correct (gates : List Circuit.Gate) :
    value (program gates) = fun i => (Circuit.values gates).getD i false :=
  compileFrom_correct gates [] [] rfl rfl

theorem table_correct (gates : List Circuit.Gate) :
    tableLookup (evaluateTable (program gates)) = fun i => (Circuit.values gates).getD i false := by
  rw [ForwardBooleanProgram.table_correct,program_correct]

/-- A single input-independent, first-order Seq grammar evaluates every
numbered Boolean circuit; no gate is duplicated in the data translation. -/
theorem recognizes (gates : List Circuit.Gate) (root : Nat) :
    SObs grammar .callByValueSeq ForwardBooleanSyntax.entry (input gates root) (some []) ↔
      (Circuit.values gates).getD root false = true := by
  rw [input,ForwardBooleanSyntax.entry_program_recognizes,table_correct]

theorem input_language_iff (gates : List Circuit.Gate) (root : Nat) :
    ForwardBooleanSyntax.ProgramLanguage (input gates root) ↔
      (Circuit.values gates).getD root false = true := by
  rw [← ForwardBooleanSyntax.language_iff,recognizes]

theorem normalized_recognizes (gates : List Circuit.Gate) (root : Nat) :
    SObs normalizedGrammar .callByValueSeq ForwardBooleanSyntax.normalizedEntry (input gates root) (some []) ↔
      (Circuit.values gates).getD root false = true := by
  rw [ForwardBooleanSyntax.normalized_language_iff]
  rw [← ForwardBooleanSyntax.language_iff,recognizes]

def OperandsBound (bound : Nat) : Gate → Prop
  | .yes | .no => True
  | .neg i => i ≤ bound
  | .both i j => i ≤ bound ∧ j ≤ bound

def ProgramBound (bound : Nat) (P : List Node) : Prop :=
  ∀ node ∈ P, node.1 ≤ bound ∧ OperandsBound bound node.2

theorem lower_bounded {g : Circuit.Gate} {bound : Nat}
    (h : g.Before bound) : OperandsBound bound (lower g) := by
  cases g with
  | bit b => cases b <;> trivial
  | neg _ => simp only [Complexity.BoolCircuit.Gate.Before] at h; exact Nat.le_of_lt h
  | conj _ _ => exact ⟨Nat.le_of_lt h.1,Nat.le_of_lt h.2⟩

theorem compileFrom_bounded {bound : Nat} (gates : List Circuit.Gate) (P : List Node)
    (hP : ProgramBound bound P) (hg : ∀ g ∈ gates, OperandsBound bound (lower g))
    (hsize : P.length + gates.length ≤ bound) : ProgramBound bound (compileFrom P gates) := by
  induction gates generalizing P with
  | nil => exact hP
  | cons g gs ih =>
    apply ih ((P.length,lower g)::P)
    · intro node hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact ⟨by simp only [List.length_cons] at hsize; omega,hg g (by simp)⟩
      · exact hP node hn
    · intro a ha; exact hg a (by simp [ha])
    · simp only [List.length_cons] at hsize ⊢
      omega

theorem program_bounded {gates : List Circuit.Gate} (h : Complexity.BoolCircuit.WellFormed gates) :
    ProgramBound gates.length (program gates) := by
  apply compileFrom_bounded gates [] (by intro node hn; cases hn)
  · intro g hg
    exact lower_bounded (Complexity.BoolCircuit.wellFormed_bound h g hg)
  · simp

theorem header_length (n : Nat) : (header n).length = n+3 := by
  simp [header,identifier]

theorem gateWord_length_bound {bound : Nat} {g : Gate} (h : OperandsBound bound g) :
    (gateWord g).length ≤ 2*bound+4 := by
  cases g <;> simp [OperandsBound,gateWord,identifier] at * <;> omega

theorem encode_length_bound (P : List Node) (bound : Nat) (h : ProgramBound bound P) :
    (encode P).length ≤ P.length * (3*bound+8) := by
  induction P with
  | nil => simp [encode]
  | cons node P ih =>
    obtain ⟨i,g⟩ := node
    have hn := h (i,g) (by simp)
    have hg : (gateWord g).length ≤ 2*bound+4 := gateWord_length_bound hn.2
    have hp := ih (fun node hm => h node (by simp [hm]))
    simp only [encode,List.length_append,List.length_cons,header_length]
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- For a well-formed numbered circuit and a root index at most its size,
the complete serialized Seq input has an explicit quadratic length bound.
This is a size bound, not a logspace transducer certification. -/
theorem input_length_bound {gates : List Circuit.Gate} (h : Complexity.BoolCircuit.WellFormed gates)
    {root : Nat} (hr : root ≤ gates.length) :
    (input gates root).length ≤ gates.length * (3*gates.length+8) + gates.length+1 := by
  have hp := encode_length_bound (program gates) gates.length (program_bounded h)
  rw [program_length] at hp
  simp only [input,List.length_append]
  have hi : (identifier root).length = root+1 := by simp [identifier]
  rw [hi]
  omega

end Shallot.MacroPeg.CBV.CircuitProgram
