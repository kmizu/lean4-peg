import MacroPeg.CBV.RecursiveFieldSyntax

/-! Multiple mutually recursive Par headers with independent arities and
field orders covering the parameters read by their continuations. Every
source actual is still preflighted, including values not recaptured.
Empty anchors are allowed when the continuation reads no incoming parameter.
Actual captures are checked delimiter-free. -/
namespace Shallot.MacroPeg.CBV.MutualFieldSyntax

structure Header where
  arity : Nat
  pattern : List Nat
  body : MExp

def address (helpers : Nat) (headers : List Header) (i : Nat) : Nat :=
  helpers+((headers.take i).map (fun s => s.arity+1)).sum

mutual
  def exprCheck (helpers : Nat) (headers : List Header) (scope : Nat) (d : Char) : MExp → Bool
    | .eps | .any | .chr _ | .range _ _ | .lit _ => true
    | .param i => decide (i<scope)
    | .call i args => if i<helpers then decide (args=[]) else
        match headers[i-helpers]? with
        | none => false
        | some s => decide (args.length=s.arity) && argsCheck helpers headers scope d args
    | .seq a b | .alt a b => exprCheck helpers headers scope d a && exprCheck helpers headers scope d b
    | .notP a | .star a => exprCheck helpers headers scope d a
    | _ => false
  def argsCheck (helpers : Nat) (headers : List Header) (scope : Nat) (d : Char) : List MExp → Bool
    | [] => true
    | a::as => (exprCheck helpers headers scope d a && DelimitedValueSafety.check d a) &&
        argsCheck helpers headers scope d as
end

mutual
  def emit (helpers : Nat) (headers : List Header) (d : Char) : MExp → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .param i => .param i
    | .call i args => if i<helpers then .call i (emitArgs helpers headers d args) else
        match headers[i-helpers]? with
        | none => MExp.failAlways
        | some s => TupleFieldTransfer.head (address helpers headers (i-helpers)) s.arity d s.pattern
            (emitArgs helpers headers d args)
    | .seq a b => .seq (emit helpers headers d a) (emit helpers headers d b)
    | .alt a b => .alt (emit helpers headers d a) (emit helpers headers d b)
    | .notP a => .notP (emit helpers headers d a)
    | .star a => .star (emit helpers headers d a)
    | _ => MExp.failAlways
  def emitArgs (helpers : Nat) (headers : List Header) (d : Char) : List MExp → List MExp
    | [] => []
    | a::as => emit helpers headers d a::emitArgs helpers headers d as
end

def source (bodies : List MExp) (headers : List Header) (d : Char) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++headers.map (fun s => ⟨s.arity,TupleFieldTransfer.sourceBody d s.pattern s.body⟩)⟩
def target (bodies : List MExp) (headers : List Header) (d : Char) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++headers.flatMap (fun s =>
    TupleFieldTransfer.rules s.arity d s.pattern (emit bodies.length headers d s.body))⟩

def headerCheck (helpers : Nat) (headers : List Header) (d : Char) (s : Header) : Bool :=
  decide (0<s.arity) && s.pattern.all (fun i => decide (i<s.arity)) &&
    UsedFieldCapture.check s.arity s.pattern (emit helpers headers d s.body) &&
    exprCheck helpers headers s.arity d s.body
def check (bodies : List MExp) (headers : List Header) (d : Char) (root : MExp) : Bool :=
  bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) &&
    headers.all (headerCheck bodies.length headers d) && exprCheck bodies.length headers 0 d root

structure HeaderValid (helpers : Nat) (headers : List Header) (d : Char) (s : Header) : Prop where
  positive : 0<s.arity
  scope : ∀ i∈s.pattern, i<s.arity
  used : ParameterSupport.Supports (UsedFieldCapture.Allowed s.arity s.pattern) (emit helpers headers d s.body)
  body : exprCheck helpers headers s.arity d s.body=true
structure Valid (bodies : List MExp) (headers : List Header) (d : Char) : Prop where
  library : RecursiveParserStability.Valid bodies
  headers : ∀ s∈headers, HeaderValid bodies.length headers d s

theorem header_checked (helpers : Nat) (headers : List Header) (d : Char) (s : Header)
    (hc : headerCheck helpers headers d s=true) : HeaderValid helpers headers d s := by
  simp only [headerCheck,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hn,hs⟩,hu⟩,hb⟩ := hc
  have hn := of_decide_eq_true hn
  exact ⟨hn,(by intro i hi; exact of_decide_eq_true (List.all_eq_true.mp hs i hi)),
    UsedFieldCapture.checked _ _ _ hu,hb⟩

theorem checked (bodies : List MExp) (headers : List Header) (d : Char) (root : MExp)
    (hc : check bodies headers d root=true) :
    Valid bodies headers d ∧ exprCheck bodies.length headers 0 d root=true := by
  obtain ⟨h,hr⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hb,hh⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨⟨(by intro b hm; exact DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hb b hm)),
    (by intro s hm; exact header_checked _ _ _ s (List.all_eq_true.mp hh s hm))⟩,hr⟩

theorem emitArgs_length (helpers : Nat) (headers : List Header) (d : Char) (args : List MExp) :
    (emitArgs helpers headers d args).length=args.length := by
  induction args with
  | nil => rfl
  | cons a as ih => simp only [emitArgs,List.length_cons,ih]

mutual
  theorem source_firstOrder (helpers : Nat) (headers : List Header) (scope : Nat) (d : Char) : ∀ e,
      exprCheck helpers headers scope d e=true → e.FirstOrder
    | .eps,_ | .any,_ | .chr _,_ | .range _ _,_ | .lit _,_ | .param _,_ => trivial
    | .call i args,hc => by
      by_cases hi : i<helpers
      · have he : args=[] := of_decide_eq_true (by simpa only [exprCheck,if_pos hi] using hc)
        subst args; trivial
      · cases hs : headers[i-helpers]? with
        | none => simp [exprCheck,hi,hs] at hc
        | some s =>
          have hh := Bool.and_eq_true_iff.mp (show
            (decide (args.length=s.arity) && argsCheck helpers headers scope d args)=true by
              simpa only [exprCheck,if_neg hi,hs] using hc)
          exact args_firstOrder helpers headers scope d args hh.2
    | .seq a b,hc | .alt a b,hc => ⟨source_firstOrder helpers headers scope d a (Bool.and_eq_true_iff.mp hc).1,
        source_firstOrder helpers headers scope d b (Bool.and_eq_true_iff.mp hc).2⟩
    | .notP a,hc | .star a,hc => source_firstOrder helpers headers scope d a hc
    | .dbg _,hc | .lam _ _,hc | .callParam _ _,hc | .invoke _ _ _,hc => by cases hc
  theorem args_firstOrder (helpers : Nat) (headers : List Header) (scope : Nat) (d : Char) : ∀ args,
      argsCheck helpers headers scope d args=true → MExp.FirstOrderArgs args
    | [],_ => trivial
    | a::as,hc => ⟨source_firstOrder helpers headers scope d a (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).1,
        args_firstOrder helpers headers scope d as (Bool.and_eq_true_iff.mp hc).2⟩
end

mutual
  theorem emit_firstOrder (helpers : Nat) (headers : List Header) (d : Char) : ∀ e,
      (emit helpers headers d e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial
    | .call i args => by
      have ha := emitArgs_firstOrder helpers headers d args
      simp only [emit]
      split
      · exact ha
      · split
        · trivial
        · exact TupleFieldTransfer.head_firstOrder _ _ _ _ _ ha
    | .seq a b | .alt a b => ⟨emit_firstOrder helpers headers d a,emit_firstOrder helpers headers d b⟩
    | .notP a | .star a => emit_firstOrder helpers headers d a
  theorem emitArgs_firstOrder (helpers : Nat) (headers : List Header) (d : Char) : ∀ args,
      MExp.FirstOrderArgs (emitArgs helpers headers d args)
    | [] => trivial
    | a::as => ⟨emit_firstOrder helpers headers d a,emitArgs_firstOrder helpers headers d as⟩
end

theorem args_checked (helpers : Nat) (headers : List Header) (scope : Nat) (d : Char) : ∀ args,
    argsCheck helpers headers scope d args=true → ∀ i, (hi : i<args.length) →
    exprCheck helpers headers scope d args[i]=true ∧ DelimitedValueSafety.check d args[i]=true
  | [],_,i,hi => by simp at hi
  | a::as,hc,0,_ => Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1
  | a::as,hc,i+1,hi => args_checked helpers headers scope d as (Bool.and_eq_true_iff.mp hc).2 i (by simpa using hi)

theorem emitArgs_get (helpers : Nat) (headers : List Header) (d : Char) : ∀ args i, (hi : i<args.length) →
    (emitArgs helpers headers d args)[i]'(by rw [emitArgs_length]; exact hi)=emit helpers headers d args[i]
  | a::as,0,_ => rfl
  | a::as,i+1,hi => emitArgs_get helpers headers d as i (by simpa using hi)

/-- Every previously accepted fully covering header still passes the
weaker reference-sensitive check. The generated syntax is unchanged. -/
theorem header_check_of_cover (helpers : Nat) (headers : List Header) (d : Char) (s : Header)
    (hn : 0<s.arity) (hs : ∀ i∈s.pattern, i<s.arity)
    (cover : ∀ i, i<s.arity → i∈s.pattern) (hb : exprCheck helpers headers s.arity d s.body=true) :
    headerCheck helpers headers d s=true := by
  have hu := UsedFieldCapture.check_complete s.arity s.pattern (emit helpers headers d s.body)
    (UsedFieldCapture.of_cover _ _ _ (emit_firstOrder _ _ _ _) cover)
  simp only [headerCheck,Bool.and_eq_true]
  exact ⟨⟨⟨by simp [hn],List.all_eq_true.mpr (by intro i hi; exact decide_eq_true (hs i hi))⟩,hu⟩,hb⟩

end Shallot.MacroPeg.CBV.MutualFieldSyntax
