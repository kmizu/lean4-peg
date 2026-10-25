import MacroPeg.CBV.RetainedCaptureEffects

namespace Shallot.MacroPeg.CBV.ConsumingPatternChecks
open RetainedPatternSyntax
open RetainedCaptureEffects (safeCheck effects EnvSafe)
open MaskedScannerAbsorption (enabled)
abbrev Term := RetainedPatternSyntax.Expr

mutual
  def termCheck (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (required : List Bool)
      (hasParent parentFree : Bool) : Term → Bool
    | .parent => hasParent
    | .helper i => decide (i<bodies.length)
    | .user i a => (decide (i<clients.length) && termCheck bodies clients arity A required hasParent parentFree a) &&
        (!enabled required i || safeCheck bodies clients (effects bodies clients A) A parentFree a)
    | .copy args => decide (args.length=arity) && argsCheck bodies clients arity A required hasParent parentFree args
    | .seq a b | .alt a b => termCheck bodies clients arity A required hasParent parentFree a && termCheck bodies clients arity A required hasParent parentFree b
    | .notP a | .star a => termCheck bodies clients arity A required hasParent parentFree a
    | _ => true
  def argsCheck (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (required : List Bool)
      (hasParent parentFree : Bool) : List Term → Bool
    | [] => true
    | a::args => (termCheck bodies clients arity A required hasParent parentFree a &&
        safeCheck bodies clients (effects bodies clients A) A parentFree a) && argsCheck bodies clients arity A required hasParent parentFree args
end

def check (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (d : Char) (pattern : List Nat)
    (required : List Bool) (root : Term) : Bool :=
  decide (0<arity ∧ pattern≠[] ∧ d∉A ∧ required.length=clients.length) && pattern.all (fun i => decide (i<arity)) &&
    bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) && MaskedScannerAbsorption.check bodies A .eps &&
    RetainedCaptureEffects.check bodies clients A && clients.zipIdx.all (fun (e,i) => termCheck bodies clients arity A required true (enabled required i) e) &&
    termCheck bodies clients arity A required false false root

structure Checked (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (d : Char) (pattern : List Nat)
    (required : List Bool) (root : Term) : Prop where
  nonempty : 0<arity
  pattern_nonempty : pattern≠[]
  separator : d∉A
  required_length : required.length=clients.length
  scope : ∀ i∈pattern, i<arity
  library : RecursiveParserStability.Valid bodies
  helpers : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies A) A
  returns : RetainedCaptureEffects.Valid bodies clients A
  client_checks : ∀ (i : Nat) (e : Term), clients[i]?=some e → termCheck bodies clients arity A required true (enabled required i) e=true
  root_check : termCheck bodies clients arity A required false false root=true

theorem checked (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (d : Char) (pattern : List Nat)
    (required : List Bool) (root : Term) (hc : check bodies clients arity A d pattern required root=true) :
    Checked bodies clients arity A d pattern required root := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨hn,hj⟩,hb⟩,hm⟩,hr⟩,hu⟩,he⟩ := hc
  have hn := of_decide_eq_true hn
  refine ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,fun i hi => of_decide_eq_true (List.all_eq_true.mp hj i hi),
    fun b hb' => DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hb b hb'),
    (MaskedScannerAbsorption.checked bodies A .eps hm).1,RetainedCaptureEffects.checked bodies clients A hr,?_,he⟩
  intro i e hi
  exact List.all_eq_true.mp hu (e,i) (List.mem_of_getElem? (show clients.zipIdx[i]?=some (e,i) from by simp [List.getElem?_zipIdx,hi]))

theorem args_checked (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (required : List Bool) (hasParent parentFree : Bool) :
    ∀ args, argsCheck bodies clients arity A required hasParent parentFree args=true → ∀ i, (hi : i<args.length) →
      termCheck bodies clients arity A required hasParent parentFree args[i]=true ∧
        safeCheck bodies clients (effects bodies clients A) A parentFree args[i]=true
  | [],_,i,hi => by simp at hi
  | a::args,h,0,_ => (Bool.and_eq_true_iff.mp h).1 |> Bool.and_eq_true_iff.mp
  | a::args,h,i+1,hi => args_checked bodies clients arity A required hasParent parentFree args (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi)

end Shallot.MacroPeg.CBV.ConsumingPatternChecks
