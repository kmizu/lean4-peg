import MacroPeg.CBV.ParentPatternTransfer
import MacroPeg.CBV.DelimitedPatternCompiler

namespace Shallot.MacroPeg.CBV.RetainedPatternSyntax
open DelimiterTemplate DelimitedWordPattern

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | parent | helper (i : Nat) | user (i : Nat) (a : Expr) | copy (args : List Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

mutual
  def render (helpers clients : Nat) (parallel : Bool) : Expr → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .parent => .param 0
    | .helper i => .call i []
    | .user i a => .call (helpers+i) [render helpers clients parallel a]
    | .copy args => if parallel then .call (helpers+clients) (renderArgs helpers clients parallel args)
        else DelimitedPatternEvaluation.targetHead (helpers+clients) (renderArgs helpers clients parallel args)
    | .seq a b => .seq (render helpers clients parallel a) (render helpers clients parallel b)
    | .alt a b => .alt (render helpers clients parallel a) (render helpers clients parallel b)
    | .notP a => .notP (render helpers clients parallel a)
    | .star a => .star (render helpers clients parallel a)
  def renderArgs (helpers clients : Nat) (parallel : Bool) : List Expr → List MExp
    | [] => []
    | a::args => render helpers clients parallel a::renderArgs helpers clients parallel args
end

theorem renderArgs_eq_map (h n : Nat) (parallel : Bool) (args : List Expr) : renderArgs h n parallel args=args.map (render h n parallel) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [renderArgs,List.map_cons,ih]
theorem renderArgs_length (h n : Nat) (parallel : Bool) (args : List Expr) : (renderArgs h n parallel args).length=args.length := by simp [renderArgs_eq_map]

def clientRules (helpers : Nat) (clients : List Expr) (parallel : Bool) : List MRule :=
  clients.map (fun e => ⟨1,if parallel then .seq (.param 0) (render helpers clients.length true e) else render helpers clients.length false e⟩)
def source (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++(clientRules bodies.length clients true++[⟨arity,compile d (sourceParts d pattern)⟩])⟩
def target (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) : MGrammar :=
  ⟨bodies.map (fun b => ⟨0,b⟩)++(clientRules bodies.length clients false++
    (List.range arity).map (fun i => ⟨1,compile d (afterParts d i pattern)⟩))⟩

mutual
  def termCheck (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (hasParent : Bool) : Expr → Bool
    | .parent => hasParent
    | .helper i => decide (i<bodies.length)
    | .user i a => decide (i<clients.length) && termCheck bodies clients arity alphabet hasParent a
    | .copy args => decide (args.length=arity) && argsCheck bodies clients arity alphabet hasParent args
    | .seq a b | .alt a b => termCheck bodies clients arity alphabet hasParent a && termCheck bodies clients arity alphabet hasParent b
    | .notP a | .star a => termCheck bodies clients arity alphabet hasParent a
    | _ => true
  def argsCheck (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (hasParent : Bool) : List Expr → Bool
    | [] => true
    | a::args => (termCheck bodies clients arity alphabet hasParent a &&
        MaskedScannerAbsorption.check bodies alphabet (render bodies.length clients.length true a)) && argsCheck bodies clients arity alphabet hasParent args
end

def check (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Expr) : Bool :=
  decide (0<arity ∧ pattern≠[] ∧ d∉alphabet) && pattern.all (fun i => decide (i<arity)) &&
    bodies.all (DelimitedCopySyntax.lexicalCheck bodies.length) && clients.all (termCheck bodies clients arity alphabet true) &&
    termCheck bodies clients arity alphabet false root

mutual
  theorem render_firstOrder (h n : Nat) (parallel : Bool) : ∀ e, (render h n parallel e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .parent | .helper _ => True.intro
    | .user _ a => ⟨render_firstOrder h n parallel a,True.intro⟩
    | .copy args => by
      have ha := renderArgs_firstOrder h n parallel args
      cases parallel with
      | true => exact ha
      | false => exact ⟨DelimitedPatternCompiler.preflight_firstOrder _ ha,
          DelimitedPatternCompiler.passes_firstOrder (h+n) _ ha _ (fun i hi => List.mem_range.mp hi)⟩
    | .seq a b | .alt a b => ⟨render_firstOrder h n parallel a,render_firstOrder h n parallel b⟩
    | .notP a | .star a => render_firstOrder h n parallel a
  theorem renderArgs_firstOrder (h n : Nat) (parallel : Bool) : ∀ args, MExp.FirstOrderArgs (renderArgs h n parallel args)
    | [] => True.intro
    | a::args => ⟨render_firstOrder h n parallel a,renderArgs_firstOrder h n parallel args⟩
end

theorem source_installed (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) :
    RecursiveParserStability.Installed bodies (source bodies clients arity d pattern) := DelimitedCopySyntax.installed_append _ _
theorem target_installed (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) :
    RecursiveParserStability.Installed bodies (target bodies clients arity d pattern) := DelimitedCopySyntax.installed_append _ _

theorem source_user (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (source bodies clients arity d pattern).rules (bodies.length+i)=some ⟨1,.seq (.param 0) (render bodies.length clients.length true e)⟩ := by
  have hidx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp),List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [clientRules] using hidx)]
  simp [clientRules,List.getElem?_map,hi]

theorem target_user (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (target bodies clients arity d pattern).rules (bodies.length+i)=some ⟨1,render bodies.length clients.length false e⟩ := by
  have hidx := (List.getElem?_eq_some_iff.mp hi).1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simp),List.length_map,Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [clientRules] using hidx)]
  simp [clientRules,List.getElem?_map,hi]

theorem source_copy (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) :
    ruleAtM (source bodies clients arity d pattern).rules (bodies.length+clients.length)=some ⟨arity,compile d (sourceParts d pattern)⟩ := by
  simp [source,clientRules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map]

theorem target_copy (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat) (i : Nat) (hi : i<arity) :
    ruleAtM (target bodies clients arity d pattern).rules (bodies.length+clients.length+i)=some ⟨1,compile d (afterParts d i pattern)⟩ := by
  simp [target,clientRules,ruleAtM_eq_getElem?,List.getElem?_append_right,List.length_map,List.getElem?_map,List.getElem?_range hi,Nat.add_assoc]

theorem source_firstOrder (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (source bodies clients arity d pattern).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · rcases List.mem_append.mp h with h|h
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact ⟨True.intro,render_firstOrder _ _ _ _⟩
    · have he : r=⟨arity,compile d (sourceParts d pattern)⟩ := by simpa using h
      subst r; exact compile_firstOrder _ _
theorem target_firstOrder (bodies : List MExp) (clients : List Expr) (arity : Nat) (d : Char) (pattern : List Nat)
    (hb : RecursiveParserStability.Valid bodies) : (target bodies clients arity d pattern).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with h|h
  · obtain ⟨b,hm,rfl⟩ := List.mem_map.mp h
    exact RecursiveParserStability.lexical_firstOrder _ b (hb b hm)
  · rcases List.mem_append.mp h with h|h
    · obtain ⟨e,he,rfl⟩ := List.mem_map.mp h
      exact render_firstOrder _ _ _ _
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
      exact compile_firstOrder _ _

theorem args_checked (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (hasParent : Bool) :
    ∀ args, argsCheck bodies clients arity alphabet hasParent args=true → ∀ i, (hi : i<args.length) →
      termCheck bodies clients arity alphabet hasParent args[i]=true ∧
        MaskedScannerAbsorption.check bodies alphabet (render bodies.length clients.length true args[i])=true
  | [],_,i,hi => by simp at hi
  | a::args,h,0,_ => (Bool.and_eq_true_iff.mp h).1 |> Bool.and_eq_true_iff.mp
  | a::args,h,i+1,hi => args_checked bodies clients arity alphabet hasParent args (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi)

structure Checked (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Expr) : Prop where
  nonempty : 0<arity
  pattern_nonempty : pattern≠[]
  separator : d∉alphabet
  scope : ∀ i∈pattern, i<arity
  library : RecursiveParserStability.Valid bodies
  client_checks : ∀ (i : Nat) (e : Expr), clients[i]?=some e → termCheck bodies clients arity alphabet true e=true
  root_check : termCheck bodies clients arity alphabet false root=true

theorem checked (bodies : List MExp) (clients : List Expr) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Expr)
    (hc : check bodies clients arity alphabet d pattern root=true) : Checked bodies clients arity alphabet d pattern root := by
  simp only [check,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hn,hj⟩,hb⟩,hu⟩,he⟩ := hc
  have hn := of_decide_eq_true hn
  exact ⟨hn.1,hn.2.1,hn.2.2,fun i hi => of_decide_eq_true (List.all_eq_true.mp hj i hi),
    fun b hb' => DelimitedCopySyntax.lexical_checked _ b (List.all_eq_true.mp hb b hb'),
    fun i e hi => List.all_eq_true.mp hu e (List.mem_of_getElem? hi),he⟩

end Shallot.MacroPeg.CBV.RetainedPatternSyntax
