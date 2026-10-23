import MacroPeg.CBVtoCBN.CompilerLayout

namespace Shallot.MacroPeg.CBVtoCBN

/-- A source subtree is available together with all code locations collected from it. -/
def ExprAvailable (nodes : List CompileNode) (arity : Nat) (e : MExp) : Prop :=
  ∀ node ∈ collectNodes arity e, node ∈ nodes

def ArgsAvailable (nodes : List CompileNode) (arity : Nat) (es : List MExp) : Prop :=
  ∀ node ∈ collectArgNodes arity es, node ∈ nodes

def StagesAvailable (nodes : List CompileNode) (arity callee : Nat) (es : List MExp) : Prop :=
  ∀ stage, stage ≤ es.length → .args arity callee es stage ∈ nodes

theorem ExprAvailable.self {nodes : List CompileNode} {arity : Nat} {e : MExp}
    (h : ExprAvailable nodes arity e) : .expr arity e ∈ nodes := h _ (collectNodes_self _ _)

theorem ExprAvailable.seq {nodes : List CompileNode} {arity : Nat} {a b : MExp}
    (h : ExprAvailable nodes arity (.seq a b)) : ExprAvailable nodes arity a ∧ ExprAvailable nodes arity b := by
  constructor
  · intro node hn; exact h node (List.mem_cons_of_mem _ (List.mem_append_left _ hn))
  · intro node hn; exact h node (List.mem_cons_of_mem _ (List.mem_append_right _ hn))

theorem ExprAvailable.alt {nodes : List CompileNode} {arity : Nat} {a b : MExp}
    (h : ExprAvailable nodes arity (.alt a b)) : ExprAvailable nodes arity a ∧ ExprAvailable nodes arity b := by
  constructor
  · intro node hn; exact h node (List.mem_cons_of_mem _ (List.mem_append_left _ hn))
  · intro node hn; exact h node (List.mem_cons_of_mem _ (List.mem_append_right _ hn))

theorem ExprAvailable.star {nodes : List CompileNode} {arity : Nat} {a : MExp}
    (h : ExprAvailable nodes arity (.star a)) : ExprAvailable nodes arity a := by
  intro node hn; exact h node (List.mem_cons_of_mem _ hn)

theorem ExprAvailable.notP {nodes : List CompileNode} {arity : Nat} {a : MExp}
    (h : ExprAvailable nodes arity (.notP a)) : ExprAvailable nodes arity a := by
  intro node hn; exact h node (List.mem_cons_of_mem _ hn)

theorem ExprAvailable.call {nodes : List CompileNode} {arity callee : Nat} {es : List MExp}
    (h : ExprAvailable nodes arity (.call callee es)) :
    ArgsAvailable nodes arity es ∧ StagesAvailable nodes arity callee es := by
  constructor
  · intro node hn; exact h node (List.mem_cons_of_mem _ (List.mem_append_left _ hn))
  · intro stage hs; exact h _ (collectNodes_argumentStage arity callee es stage hs)

theorem ArgsAvailable.cons {nodes : List CompileNode} {arity : Nat} {a : MExp} {es : List MExp}
    (h : ArgsAvailable nodes arity (a :: es)) : ExprAvailable nodes arity a ∧ ArgsAvailable nodes arity es := by
  constructor
  · intro node hn; exact h node (List.mem_append_left _ hn)
  · intro node hn; exact h node (List.mem_append_right _ hn)

theorem compilerStart_available (source : MGrammar) (start : MExp) :
    ExprAvailable (compilerNodes source start) 0 start := by
  intro node hn
  exact List.mem_append_left _ (List.mem_append_left _ hn)

theorem compilerBody_available {source : MGrammar} (start : MExp) {callee : Nat} {rule : MRule}
    (hr : ruleAtM source.rules callee = some rule) :
    ExprAvailable (compilerNodes source start) rule.arity rule.body := by
  intro node hn
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨rule, ?_, hn⟩
  rw [ruleAtM_eq_getElem?] at hr
  exact List.mem_of_getElem? hr

end Shallot.MacroPeg.CBVtoCBN
