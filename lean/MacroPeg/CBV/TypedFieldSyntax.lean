import MacroPeg.CBV.TypedFieldTransfer
import MacroPeg.CBV.CaptureAlphabetEffects
import MacroPeg.CBV.MutualFieldLayout

/-! Finite heterogeneous retained-field grammars. Each header declares its
own delimiter, parameter alphabets, output alphabet and replay pattern.
Consuming producer calls are allowed inside actuals, with their real result
effects. Zero-arity headers and empty replay patterns are included. -/
namespace Shallot.MacroPeg.CBV.TypedFieldSyntax
open CaptureAlphabetEffects (Alphabet Environment Signature)
open MutualFieldSyntax (transfer_rules_length flatMap_rule)

structure Header where
  parameters : List Alphabet
  result : Alphabet
  delimiter : Char
  pattern : List Nat
  body : MExp

def signatures (headers : List Header) : List Signature :=
  headers.map (fun s => ⟨s.parameters,s.result⟩)
def address (headers : List Header) (i : Nat) : Nat :=
  ((headers.take i).map (fun s => s.parameters.length+1)).sum

mutual
  def exprCheck (headers : List Header) (Γ : List Alphabet) : MExp → Bool
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | .param i => decide (i<Γ.length)
    | .call i args => match headers[i]? with
      | none => false
      | some s => argsCheck headers Γ s.parameters args
    | .seq a b | .alt a b => exprCheck headers Γ a && exprCheck headers Γ b
    | .notP a | .star a => exprCheck headers Γ a
    | _ => false
  def argsCheck (headers : List Header) (Γ : List Alphabet) : List Alphabet → List MExp → Bool
    | [],[] => true
    | A::As,a::args => (exprCheck headers Γ a && CaptureAlphabetEffects.check (signatures headers) Γ A a) &&
        argsCheck headers Γ As args
    | _,_ => false
end

mutual
  def emit (headers : List Header) : MExp → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .param i => .param i
    | .call i args => match headers[i]? with
      | none => MExp.failAlways
      | some s => TupleFieldTransfer.head (address headers i) s.parameters.length s.delimiter s.pattern
          (emitArgs headers args)
    | .seq a b => .seq (emit headers a) (emit headers b)
    | .alt a b => .alt (emit headers a) (emit headers b)
    | .notP a => .notP (emit headers a)
    | .star a => .star (emit headers a)
    | _ => MExp.failAlways
  def emitArgs (headers : List Header) : List MExp → List MExp
    | [] => []
    | a::args => emit headers a::emitArgs headers args
end

def source (headers : List Header) : MGrammar :=
  ⟨headers.map (fun s => ⟨s.parameters.length,TupleFieldTransfer.sourceBody s.delimiter s.pattern s.body⟩)⟩
def target (headers : List Header) : MGrammar :=
  ⟨headers.flatMap (fun s => TupleFieldTransfer.rules s.parameters.length s.delimiter s.pattern (emit headers s.body))⟩
def headerCheck (headers : List Header) (s : Header) : Bool :=
  s.parameters.all (fun A => decide (s.delimiter∉A)) &&
    s.pattern.all (fun i => decide (i<s.parameters.length)) &&
    UsedFieldCapture.check s.parameters.length s.pattern (emit headers s.body) && exprCheck headers s.parameters s.body
def check (headers : List Header) (root : MExp) : Bool :=
  headers.all (headerCheck headers) && CaptureAlphabetEffects.grammarCheck (source headers) (signatures headers) &&
    exprCheck headers [] root

structure HeaderValid (headers : List Header) (s : Header) : Prop where
  free : ∀ A∈s.parameters, s.delimiter∉A
  scope : ∀ i∈s.pattern, i<s.parameters.length
  used : ParameterSupport.Supports (UsedFieldCapture.Allowed s.parameters.length s.pattern) (emit headers s.body)
  body : exprCheck headers s.parameters s.body=true
structure Valid (ss : List Header) : Prop where
  headers : ∀ s∈ss, HeaderValid ss s
  effects : CaptureAlphabetEffects.grammarCheck (source ss) (signatures ss)=true

theorem header_checked (headers : List Header) (s : Header) (hc : headerCheck headers s=true) :
    HeaderValid headers s := by
  simp only [headerCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hf,hs⟩,hu⟩,hb⟩ := hc
  exact ⟨(by intro A hA; exact of_decide_eq_true (List.all_eq_true.mp hf A hA)),
    (by intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hs i hi)),UsedFieldCapture.checked _ _ _ hu,hb⟩

theorem checked (headers : List Header) (root : MExp) (hc : check headers root=true) :
    Valid headers ∧ exprCheck headers [] root=true := by
  obtain ⟨hh,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hh,hg⟩ := Bool.and_eq_true_iff.mp hh
  exact ⟨⟨(by intro s hs; exact header_checked headers s (List.all_eq_true.mp hh s hs)),hg⟩,hr⟩

theorem args_length (headers : List Header) (Γ : List Alphabet) : ∀ As args,
    argsCheck headers Γ As args=true → args.length=As.length
  | [],[],_ => rfl
  | _::As,_::args,h => congrArg Nat.succ (args_length headers Γ As args (Bool.and_eq_true_iff.mp h).2)
  | [],_::_,h | _::_,[],h => by cases h

theorem args_effect (headers : List Header) (Γ : List Alphabet) : ∀ As args,
    argsCheck headers Γ As args=true → CaptureAlphabetEffects.checkArgs (signatures headers) Γ As args=true
  | [],[],_ => rfl
  | A::As,a::args,h => Bool.and_eq_true_iff.mpr
      ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2,args_effect headers Γ As args (Bool.and_eq_true_iff.mp h).2⟩
  | [],_::_,h | _::_,[],h => by cases h

theorem args_checked (headers : List Header) (Γ : List Alphabet) : ∀ As args,
    argsCheck headers Γ As args=true → ∀ i, (hi : i<args.length) →
    ∃ A, As[i]?=some A ∧ exprCheck headers Γ args[i]=true ∧
      CaptureAlphabetEffects.check (signatures headers) Γ A args[i]=true
  | [],[],_,i,hi => by simp at hi
  | A::As,a::args,h,0,_ => ⟨A,rfl,(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1)⟩
  | A::As,a::args,h,i+1,hi => by
    obtain ⟨B,hB,hc,he⟩ := args_checked headers Γ As args (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi)
    exact ⟨B,hB,hc,he⟩
  | [],_::_,h,_,_ | _::_,[],h,_,_ => by cases h

theorem environment_length {Γ : List Alphabet} {E : List (List Char)} (h : Environment Γ E) :
    E.length=Γ.length := by induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem environment_free {Γ : List Alphabet} {E : List (List Char)} (h : Environment Γ E)
    (d : Char) (hf : ∀ A∈Γ, d∉A) : DelimitedValueSafety.Environment d E := by
  induction h with
  | nil => intro w hw; cases hw
  | @cons A w As ws hw ht ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · intro hd; exact hf A (by simp) (hw d hd)
    · exact ih (by intro B hB; exact hf B (by simp [hB])) v hv

mutual
  theorem source_firstOrder (headers : List Header) (Γ : List Alphabet) : ∀ e,
      exprCheck headers Γ e=true → e.FirstOrder
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .call i args,h => by
      cases hs : headers[i]? with
      | none => simp [exprCheck,hs] at h
      | some s => exact args_firstOrder headers Γ s.parameters args (by simpa only [exprCheck,hs] using h)
    | .seq a b,h | .alt a b,h => ⟨source_firstOrder headers Γ a (Bool.and_eq_true_iff.mp h).1,
        source_firstOrder headers Γ b (Bool.and_eq_true_iff.mp h).2⟩
    | .notP a,h | .star a,h => source_firstOrder headers Γ a h
    | .dbg _,h | .lam _ _,h | .callParam _ _,h | .invoke _ _ _,h => by cases h
  theorem args_firstOrder (headers : List Header) (Γ : List Alphabet) : ∀ As args,
      argsCheck headers Γ As args=true → MExp.FirstOrderArgs args
    | [],[],_ => True.intro
    | A::As,a::args,h => ⟨source_firstOrder headers Γ a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1,
        args_firstOrder headers Γ As args (Bool.and_eq_true_iff.mp h).2⟩
    | [],_::_,h | _::_,[],h => by cases h
end

mutual
  theorem emit_firstOrder (headers : List Header) : ∀ e, (emit headers e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
    | .call i args => by
      simp only [emit]
      split
      · trivial
      · exact TupleFieldTransfer.head_firstOrder _ _ _ _ _ (emitArgs_firstOrder headers args)
    | .seq a b | .alt a b => ⟨emit_firstOrder headers a,emit_firstOrder headers b⟩
    | .notP a | .star a => emit_firstOrder headers a
  theorem emitArgs_firstOrder (headers : List Header) : ∀ args, MExp.FirstOrderArgs (emitArgs headers args)
    | [] => True.intro
    | a::args => ⟨emit_firstOrder headers a,emitArgs_firstOrder headers args⟩
end

theorem emitArgs_length (headers : List Header) : ∀ args, (emitArgs headers args).length=args.length
  | [] => rfl
  | a::args => congrArg Nat.succ (emitArgs_length headers args)
theorem emitArgs_get (headers : List Header) : ∀ args i (hi : i<args.length),
    (emitArgs headers args)[i]'(by rw [emitArgs_length]; exact hi)=emit headers args[i]
  | _::_,0,_ => rfl
  | _::args,i+1,hi => emitArgs_get headers args i (by simpa using hi)

theorem signature_at (headers : List Header) (i : Nat) (s : Header) (hs : headers[i]?=some s) :
    (signatures headers)[i]?=some ⟨s.parameters,s.result⟩ := by simp [signatures,List.getElem?_map,hs]
theorem source_row (headers : List Header) (i : Nat) (s : Header) (hs : headers[i]?=some s) :
    ruleAtM (source headers).rules i=some ⟨s.parameters.length,TupleFieldTransfer.sourceBody s.delimiter s.pattern s.body⟩ := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hs]

theorem target_block (headers : List Header) (i : Nat) (s : Header) (hs : headers[i]?=some s)
    (slot : Nat) (hslot : slot<s.parameters.length+1) :
    ruleAtM (target headers).rules (address headers i+slot)=
      ruleAtM (TupleFieldTransfer.rules s.parameters.length s.delimiter s.pattern (emit headers s.body)) slot := by
  have hl : ((headers.take i).flatMap (fun s =>
      TupleFieldTransfer.rules s.parameters.length s.delimiter s.pattern (emit headers s.body))).length=
      ((headers.take i).map (fun s => s.parameters.length+1)).sum := by simp [List.length_flatMap,transfer_rules_length]
  unfold target address
  rw [←hl]
  exact flatMap_rule headers _ i s hs slot (by rw [transfer_rules_length]; exact hslot)

theorem target_rows (headers : List Header) (i : Nat) (s : Header) (hs : headers[i]?=some s) :
    TupleFieldTransfer.Installed (target headers) (address headers i) s.parameters.length s.delimiter s.pattern (emit headers s.body) := by
  constructor
  · intro j hj
    exact (target_block headers i s hs j (by omega)).trans (TupleFieldTransfer.rules_projection _ _ _ _ j hj)
  · exact (target_block headers i s hs s.parameters.length (by omega)).trans (TupleFieldTransfer.rules_entry _ _ _ _)

theorem source_firstOrder_grammar (headers : List Header) (hv : Valid headers) : (source headers).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact ⟨DelimiterTemplate.compile_firstOrder _ _,source_firstOrder headers s.parameters s.body (hv.headers s hs).body⟩
theorem target_firstOrder_grammar (headers : List Header) : (target headers).FirstOrder := by
  intro r hr
  obtain ⟨s,hs,hr⟩ := List.mem_flatMap.mp hr
  exact TupleFieldTransfer.rules_firstOrder _ _ _ _ (emit_firstOrder headers s.body) r hr
theorem rule_count (headers : List Header) :
    (target headers).rules.length=(headers.map (fun s => s.parameters.length+1)).sum := by
  simp [target,List.length_flatMap,transfer_rules_length]

end Shallot.MacroPeg.CBV.TypedFieldSyntax
