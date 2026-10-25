import MacroPeg.CBV.DelimitedPatternCallTransfer
import MacroPeg.CBV.DelimitedPatternCompiler

namespace Shallot.MacroPeg.CBV.RecursivePatternSyntax
open DelimiterTemplate DelimitedWordPattern

inductive Expr where
  | eps | any | chr (c : Char) | range (a b : Char) | lit (w : List Char)
  | user (i : Nat) | copy (args : List Expr)
  | seq (a b : Expr) | alt (a b : Expr) | notP (a : Expr) | star (a : Expr)
  deriving Repr

mutual
  def render (n : Nat) (parallel : Bool) : Expr → MExp
    | .eps => .eps | .any => .any | .chr c => .chr c | .range a b => .range a b | .lit w => .lit w
    | .user i => .call i []
    | .copy args => if parallel then .call n (renderArgs n parallel args)
        else DelimitedPatternEvaluation.targetHead n (renderArgs n parallel args)
    | .seq a b => .seq (render n parallel a) (render n parallel b)
    | .alt a b => .alt (render n parallel a) (render n parallel b)
    | .notP a => .notP (render n parallel a)
    | .star a => .star (render n parallel a)
  def renderArgs (n : Nat) (parallel : Bool) : List Expr → List MExp
    | [] => []
    | a::args => render n parallel a::renderArgs n parallel args
end

theorem renderArgs_eq_map (n : Nat) (parallel : Bool) (args : List Expr) : renderArgs n parallel args=args.map (render n parallel) := by
  induction args with
  | nil => rfl
  | cons a args ih => simp only [renderArgs,List.map_cons,ih]

theorem renderArgs_length (n : Nat) (parallel : Bool) (args : List Expr) : (renderArgs n parallel args).length=args.length := by simp [renderArgs_eq_map]

def sourceBodies (clients : List Expr) := clients.map (render clients.length true)
def targetBodies (clients : List Expr) := clients.map (render clients.length false)
def source (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) :=
  DelimitedPatternCompiler.source (sourceBodies clients) arity d js
def target (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) :=
  DelimitedPatternCompiler.target (targetBodies clients) arity d js

mutual
  def termCheck (clients : List Expr) (arity : Nat) (alphabet : List Char) : Expr → Bool
    | .user i => decide (i<clients.length)
    | .copy args => decide (args.length=arity) && argsCheck clients arity alphabet args
    | .seq a b | .alt a b => termCheck clients arity alphabet a && termCheck clients arity alphabet b
    | .notP a | .star a => termCheck clients arity alphabet a
    | _ => true
  def argsCheck (clients : List Expr) (arity : Nat) (alphabet : List Char) : List Expr → Bool
    | [] => true
    | a::args => (termCheck clients arity alphabet a &&
        MaskedScannerAbsorption.check (sourceBodies clients) alphabet (render clients.length true a)) && argsCheck clients arity alphabet args
end

def check (clients : List Expr) (arity : Nat) (alphabet : List Char) (d : Char) (js : List Nat) (root : Expr) : Bool :=
  decide (0<arity ∧ js≠[] ∧ d∉alphabet) && js.all (fun i => decide (i<arity)) &&
    clients.all (termCheck clients arity alphabet) && termCheck clients arity alphabet root

mutual
  theorem render_firstOrder (n : Nat) (parallel : Bool) : ∀ e, (render n parallel e).FirstOrder
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .user _ => True.intro
    | .copy args => by
      have ha := renderArgs_firstOrder n parallel args
      cases parallel with
      | true => exact ha
      | false => exact ⟨DelimitedPatternCompiler.preflight_firstOrder _ ha,
          DelimitedPatternCompiler.passes_firstOrder n _ ha _ (fun i hi => List.mem_range.mp hi)⟩
    | .seq a b | .alt a b => ⟨render_firstOrder n parallel a,render_firstOrder n parallel b⟩
    | .notP a | .star a => render_firstOrder n parallel a
  theorem renderArgs_firstOrder (n : Nat) (parallel : Bool) : ∀ args, MExp.FirstOrderArgs (renderArgs n parallel args)
    | [] => True.intro
    | a::args => ⟨render_firstOrder n parallel a,renderArgs_firstOrder n parallel args⟩
end

mutual
  theorem source_closed (n : Nat) : ∀ e, ReplayFallbackFusion.Closed (render n true e)
    | .eps | .any | .chr _ | .range _ _ | .lit _ | .user _ => True.intro
    | .copy args => sourceArgs_closed n args
    | .seq a b | .alt a b => ⟨source_closed n a,source_closed n b⟩
    | .notP a | .star a => source_closed n a
  theorem sourceArgs_closed (n : Nat) : ∀ args, ReplayFallbackFusion.ClosedArgs (renderArgs n true args)
    | [] => True.intro
    | a::args => ⟨source_closed n a,sourceArgs_closed n args⟩
end

theorem source_installed (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) :
    RecursiveParserStability.Installed (sourceBodies clients) (source clients arity d js) := DelimitedPatternCompiler.source_installed _ _ _ _

theorem source_user (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (source clients arity d js).rules i=some ⟨0,render clients.length true e⟩ :=
  source_installed clients arity d js i _ (by simp [sourceBodies,List.getElem?_map,hi])

theorem target_user (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (e : Expr) (hi : clients[i]?=some e) :
    ruleAtM (target clients arity d js).rules i=some ⟨0,render clients.length false e⟩ :=
  DelimitedPatternCompiler.target_installed (targetBodies clients) arity d js i _ (by simp [targetBodies,List.getElem?_map,hi])

theorem source_copy (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) :
    ruleAtM (source clients arity d js).rules clients.length=some ⟨arity,compile d (sourceParts d js)⟩ := by
  simpa [source,sourceBodies] using DelimitedPatternCompiler.source_rule (sourceBodies clients) arity d js

theorem target_copy (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (hi : i<arity) :
    ruleAtM (target clients arity d js).rules (clients.length+i)=some ⟨1,compile d (afterParts d i js)⟩ := by
  simpa [target,targetBodies] using DelimitedPatternCompiler.target_rule (targetBodies clients) arity d js i hi

theorem source_firstOrder (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) : (source clients arity d js).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hl|hc
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hl
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    exact render_firstOrder _ _ _
  · have he : r=⟨arity,compile d (sourceParts d js)⟩ := by simpa using hc
    subst r; exact compile_firstOrder _ _

theorem target_firstOrder (clients : List Expr) (arity : Nat) (d : Char) (js : List Nat) : (target clients arity d js).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hl|hc
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hl
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
    exact render_firstOrder _ _ _
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact compile_firstOrder _ _

theorem args_checked (clients : List Expr) (arity : Nat) (alphabet : List Char) :
    ∀ args, argsCheck clients arity alphabet args=true → ∀ i, (hi : i<args.length) →
      termCheck clients arity alphabet args[i]=true ∧
        MaskedScannerAbsorption.check (sourceBodies clients) alphabet (render clients.length true args[i])=true
  | [],_,i,hi => by simp at hi
  | a::args,h,0,_ => (Bool.and_eq_true_iff.mp h).1 |> Bool.and_eq_true_iff.mp
  | a::args,h,i+1,hi => args_checked clients arity alphabet args (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi)

theorem checked (clients : List Expr) (arity : Nat) (alphabet : List Char) (d : Char) (js : List Nat) (root : Expr)
    (hc : check clients arity alphabet d js root=true) :
    (0<arity ∧ js≠[] ∧ d∉alphabet) ∧ (∀ i∈js, i<arity) ∧
      (∀ (i : Nat) (e : Expr), clients[i]?=some e → termCheck clients arity alphabet e=true) ∧ termCheck clients arity alphabet root=true := by
  obtain ⟨h,he⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨h,hb⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hn,hj⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true hn,fun i hi => of_decide_eq_true (List.all_eq_true.mp hj i hi),
    fun i e hi => List.all_eq_true.mp hb e (List.mem_of_getElem? hi),he⟩

end Shallot.MacroPeg.CBV.RecursivePatternSyntax
