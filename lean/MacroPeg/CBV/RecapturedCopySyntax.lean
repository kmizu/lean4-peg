import MacroPeg.CBV.RecapturedCopyTransfer
import MacroPeg.CBV.ControlledCaptureEffects
import MacroPeg.CBV.ConsumingPatternChecks

namespace Shallot.MacroPeg.CBV.RecapturedCopySyntax
open RetainedPatternSyntax
abbrev Term := RetainedPatternSyntax.Expr

mutual
  def emit (helpers clients arity : Nat) (d : Char) (body : List Nat) : Term → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .parent => .param 0
    | .helper i => .call i []
    | .user i a => .call (helpers+i) [emit helpers clients arity d body a]
    | .copy args => RecapturedCopyTransfer.head (helpers+clients) arity d body (emitArgs helpers clients arity d body args)
    | .seq a b => .seq (emit helpers clients arity d body a) (emit helpers clients arity d body b)
    | .alt a b => .alt (emit helpers clients arity d body a) (emit helpers clients arity d body b)
    | .notP a => .notP (emit helpers clients arity d body a)
    | .star a => .star (emit helpers clients arity d body a)
  def emitArgs (h n arity : Nat) (d : Char) (body : List Nat) : List Term → List MExp
    | [] => []
    | a::args => emit h n arity d body a::emitArgs h n arity d body args
end

theorem emitArgs_eq_map (h n arity : Nat) (d : Char) (body : List Nat) (args : List Term) : emitArgs h n arity d body args=args.map (emit h n arity d body) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [emitArgs,List.map_cons,ih]
theorem emitArgs_length (h n arity : Nat) (d : Char) (body : List Nat) (args : List Term) : (emitArgs h n arity d body args).length=args.length := by simp [emitArgs_eq_map]

def targetClients (helpers : Nat) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) : List MRule :=
  clients.map (fun e => ⟨1,emit helpers clients.length arity d body e⟩)
def source (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++(RetainedPatternSyntax.clientRules bodies.length clients true++[⟨arity,(.star (DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d body)))⟩])⟩
def target (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++(targetClients bodies.length clients arity d body++RecapturedCopyTransfer.rules arity d body)⟩

def patternCheck (arity : Nat) (body : List Nat) : Bool :=
  decide (body≠[]) && body.all (fun i => decide (i<arity))

theorem pattern_checked (arity : Nat) (body : List Nat) (hc : patternCheck arity body=true) :
    body≠[] ∧ ∀ i∈body, i<arity := by
  obtain ⟨hn,hs⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨of_decide_eq_true hn,fun i hi => of_decide_eq_true (List.all_eq_true.mp hs i hi)⟩

def check (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (d : Char) (body : List Nat)
    (required : List Bool) (root : Term) : Bool :=
  patternCheck arity body && ConsumingPatternChecks.check bodies clients arity A d [0] required root

theorem checked (bodies : List MExp) (clients : List Term) (arity : Nat) (A : List Char) (d : Char) (body : List Nat)
    (required : List Bool) (root : Term) (hc : check bodies clients arity A d body required root=true) :
    patternCheck arity body=true ∧ ConsumingPatternChecks.Checked bodies clients arity A d [0] required root := by
  obtain ⟨he,hc⟩ := Bool.and_eq_true_iff.mp hc
  exact ⟨he,ConsumingPatternChecks.checked bodies clients arity A d [0] required root hc⟩

mutual
  theorem emit_firstOrder (h n arity : Nat) (d : Char) (body : List Nat) : ∀ e, (emit h n arity d body e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .parent | .helper _ => True.intro
    | .user _ a => ⟨emit_firstOrder h n arity d body a,True.intro⟩
    | .copy args => RecapturedCopyTransfer.head_firstOrder _ _ _ _ _ (emitArgs_firstOrder h n arity d body args)
    | .seq a b | .alt a b => ⟨emit_firstOrder h n arity d body a,emit_firstOrder h n arity d body b⟩
    | .notP a | .star a => emit_firstOrder h n arity d body a
  theorem emitArgs_firstOrder (h n arity : Nat) (d : Char) (body : List Nat) : ∀ args, MExp.FirstOrderArgs (emitArgs h n arity d body args)
    | [] => True.intro
    | a::args => ⟨emit_firstOrder h n arity d body a,emitArgs_firstOrder h n arity d body args⟩
end

theorem source_installed (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) :
    RecursiveParserStability.Installed bodies (source bodies clients arity d body) := DelimitedCopySyntax.installed_append _ _
theorem target_installed (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) :
    RecursiveParserStability.Installed bodies (target bodies clients arity d body) := DelimitedCopySyntax.installed_append _ _

theorem source_user (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) (i : Nat) (e : Term) (hi : clients[i]?=some e) :
    ruleAtM (source bodies clients arity d body).rules (bodies.length+i)=some ⟨1,.seq (.param 0) (render bodies.length clients.length true e)⟩ := by
  have hidx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp),List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [RetainedPatternSyntax.clientRules] using hidx)]
  simp [RetainedPatternSyntax.clientRules,List.getElem?_map,hi]

theorem target_user (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) (i : Nat) (e : Term) (hi : clients[i]?=some e) :
    ruleAtM (target bodies clients arity d body).rules (bodies.length+i)=some ⟨1,emit bodies.length clients.length arity d body e⟩ := by
  have hidx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp),List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [targetClients] using hidx)]
  simp [targetClients,List.getElem?_map,hi]

theorem source_copy (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) :
    ruleAtM (source bodies clients arity d body).rules (bodies.length+clients.length)=some ⟨arity,(.star (DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d body)))⟩ := by
  simp [source,RetainedPatternSyntax.clientRules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem target_extra (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) (k : Nat) :
    ruleAtM (target bodies clients arity d body).rules (bodies.length+clients.length+k)=ruleAtM (RecapturedCopyTransfer.rules arity d body) k := by
  simp [target,targetClients,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map,Nat.add_assoc]

theorem target_copy (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) :
    RecapturedCopyTransfer.Installed (target bodies clients arity d body) (bodies.length+clients.length) arity d body := by
  constructor
  · intro i hi
    exact (target_extra bodies clients arity d body i).trans (RecapturedCopyTransfer.rules_projection arity d body i hi)
  · exact (target_extra bodies clients arity d body arity).trans (RecapturedCopyTransfer.rules_loop arity d body)

theorem source_firstOrder (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (source bodies clients arity d body).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · rcases List.mem_append.mp h with h|h
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact ⟨True.intro,render_firstOrder _ _ _ _⟩
    · have he : r=⟨arity,(.star (DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d body)))⟩ := by simpa using h
      subst r; exact DelimiterTemplate.compile_firstOrder _ _
theorem target_firstOrder (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (target bodies clients arity d body).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · rcases List.mem_append.mp h with h|h
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact emit_firstOrder _ _ _ _ _ _
    · exact RecapturedCopyTransfer.rules_firstOrder arity d body r h

end Shallot.MacroPeg.CBV.RecapturedCopySyntax
