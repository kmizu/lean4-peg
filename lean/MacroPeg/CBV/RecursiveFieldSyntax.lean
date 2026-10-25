import MacroPeg.CBV.TupleFieldCompiler
import MacroPeg.CBV.DelimitedValueSafety

/-! A recursive multi-argument header, with raw first-order control in its
body. Each self call evaluates fresh Par actuals and recaptures their values
from its own mandatory covering anchor. Helpers are independent nullary PEGs. -/
namespace Shallot.MacroPeg.CBV.RecursiveFieldSyntax

mutual
  def exprCheck (helpers arity scope : Nat) (d : Char) : MExp → Bool
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | .param i => decide (i<scope)
    | .call i args => if i<helpers then decide (args=[])
        else (decide (i=helpers) && decide (args.length=arity)) && argsCheck helpers arity scope d args
    | .seq a b | .alt a b => exprCheck helpers arity scope d a && exprCheck helpers arity scope d b
    | .notP a | .star a => exprCheck helpers arity scope d a
    | _ => false
  def argsCheck (helpers arity scope : Nat) (d : Char) : List MExp → Bool
    | [] => true
    | a::args => (exprCheck helpers arity scope d a && DelimitedValueSafety.check d a) &&
        argsCheck helpers arity scope d args
end

mutual
  def emit (helpers arity : Nat) (d : Char) (js : List Nat) : MExp → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .param i => .param i
    | .call i args => if i=helpers then TupleFieldTransfer.head helpers arity d js (emitArgs helpers arity d js args)
        else .call i (emitArgs helpers arity d js args)
    | .seq a b => .seq (emit helpers arity d js a) (emit helpers arity d js b)
    | .alt a b => .alt (emit helpers arity d js a) (emit helpers arity d js b)
    | .notP a => .notP (emit helpers arity d js a)
    | .star a => .star (emit helpers arity d js a)
    | _ => MExp.failAlways
  def emitArgs (helpers arity : Nat) (d : Char) (js : List Nat) : List MExp → List MExp
    | [] => []
    | a::args => emit helpers arity d js a::emitArgs helpers arity d js args
end

theorem emitArgs_length (helpers arity : Nat) (d : Char) (js : List Nat) (args : List MExp) :
    (emitArgs helpers arity d js args).length=args.length := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [emitArgs,List.length_cons,ih]

mutual
  theorem source_firstOrder (helpers arity scope : Nat) (d : Char) : ∀ e,
      exprCheck helpers arity scope d e=true → e.FirstOrder
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .call i args,hc => by
      by_cases hi : i<helpers
      · have he : args=[] := of_decide_eq_true (by simpa only [exprCheck,if_pos hi] using hc)
        subst args; trivial
      · exact args_firstOrder helpers arity scope d args (Bool.and_eq_true_iff.mp (by simpa only [exprCheck,if_neg hi] using hc)).2
    | .seq a b,hc | .alt a b,hc =>
      ⟨source_firstOrder helpers arity scope d a (Bool.and_eq_true_iff.mp hc).1,
        source_firstOrder helpers arity scope d b (Bool.and_eq_true_iff.mp hc).2⟩
    | .notP a,hc | .star a,hc => source_firstOrder helpers arity scope d a hc
    | .dbg _,hc | .lam _ _,hc | .callParam _ _,hc | .invoke _ _ _,hc => by cases hc
  theorem args_firstOrder (helpers arity scope : Nat) (d : Char) : ∀ args,
      argsCheck helpers arity scope d args=true → MExp.FirstOrderArgs args
    | [],_ => trivial
    | a::args,hc => ⟨source_firstOrder helpers arity scope d a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1,
        args_firstOrder helpers arity scope d args (Bool.and_eq_true_iff.mp hc).2⟩
end

mutual
  theorem emit_firstOrder (helpers arity : Nat) (d : Char) (js : List Nat) : ∀ e,
      (emit helpers arity d js e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
    | .call i args => by
      have ha := emitArgs_firstOrder helpers arity d js args
      simp only [emit]
      split
      · exact TupleFieldTransfer.head_firstOrder _ _ _ _ _ ha
      · exact ha
    | .seq a b | .alt a b => ⟨emit_firstOrder helpers arity d js a,emit_firstOrder helpers arity d js b⟩
    | .notP a | .star a => emit_firstOrder helpers arity d js a
  theorem emitArgs_firstOrder (helpers arity : Nat) (d : Char) (js : List Nat) : ∀ args,
      MExp.FirstOrderArgs (emitArgs helpers arity d js args)
    | [] => trivial
    | a::args => ⟨emit_firstOrder helpers arity d js a,emitArgs_firstOrder helpers arity d js args⟩
end

theorem args_checked (helpers arity scope : Nat) (d : Char) : ∀ args,
    argsCheck helpers arity scope d args=true → ∀ i, (hi : i<args.length) →
    exprCheck helpers arity scope d args[i]=true ∧ DelimitedValueSafety.check d args[i]=true
  | [],_,i,hi => by simp at hi
  | a::args,hc,0,_ => Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1
  | a::args,hc,i+1,hi => args_checked helpers arity scope d args (Bool.and_eq_true_iff.mp hc).2 i (by simpa using hi)

theorem emitArgs_get (helpers arity : Nat) (d : Char) (js : List Nat) : ∀ args i, (hi : i<args.length) →
    (emitArgs helpers arity d js args)[i]'(by rw [emitArgs_length]; exact hi)=emit helpers arity d js args[i]
  | a::args,0,_ => rfl
  | a::args,i+1,hi => emitArgs_get helpers arity d js args i (by simpa using hi)

def source (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (body : MExp) :=
  TupleFieldCompiler.source bodies arity d js body
def target (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (body : MExp) :=
  TupleFieldCompiler.target bodies arity d js (emit bodies.length arity d js body)

def check (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (body root : MExp) : Bool :=
  decide (0<arity ∧ js≠[]) && js.all (fun i => decide (i<arity)) &&
    (List.range arity).all (fun i => decide (i∈js)) &&
    bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) &&
    exprCheck bodies.length arity arity d body && exprCheck bodies.length arity 0 d root

structure Checked (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (body root : MExp) : Prop where
  positive : 0<arity
  nonempty : js≠[]
  scope : ∀ i∈js, i<arity
  cover : ∀ i, i<arity → i∈js
  library : RecursiveParserStability.Valid bodies
  body : exprCheck bodies.length arity arity d body=true
  root : exprCheck bodies.length arity 0 d root=true

theorem checked (bodies : List MExp) (arity : Nat) (d : Char) (js : List Nat) (body root : MExp)
    (hc : check bodies arity d js body root=true) : Checked bodies arity d js body root := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hn,hs⟩,hv⟩,hb⟩,he⟩,hr⟩ := hc
  have hn := of_decide_eq_true hn
  refine ⟨hn.1,hn.2,?_,?_,?_,he,hr⟩
  · intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hs i hi)
  · intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hv i (List.mem_range.mpr hi))
  · intro b hb'; exact DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hb b hb')

end Shallot.MacroPeg.CBV.RecursiveFieldSyntax
