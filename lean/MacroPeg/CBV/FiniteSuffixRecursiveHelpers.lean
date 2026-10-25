import MacroPeg.CBV.FiniteSuffixRecursiveSyntax

namespace Shallot.MacroPeg.CBV.FiniteSuffixRecursiveHelpers
open FiniteSuffixRecursiveSyntax
open RegularCaptureProduct (Node)
open ClockFreezing (Table)
open RecursiveParserStability (Lexical Installed)
abbrev Spec := FiniteSuffixRecursiveSyntax.Rule

abbrev sourceTable (nodes : List Node) (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :=
  RecursiveParserStability.frozen (sourceBodies nodes) (source nodes R rs) x .callByValuePar k
abbrev targetTable (nodes : List Node) (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :=
  RecursiveParserStability.frozen (targetBodies nodes R) (target nodes R rs) x .callByValueSeq k

/-- Stabilization is proved for actual installed helper rows. The compiler
never receives a row semantics oracle or a termination certificate. -/
theorem frozen_lexical_base {bodies : List MExp} (hb : RecursiveParserStability.Valid bodies)
    {g h : MGrammar} (hg : Installed bodies g) (hh : Installed bodies h) (x : List Char) (s t : Strategy)
    (k : Nat) (E F : List (List Char)) (e : MExp) (he : Lexical bodies.length e) (p : Nat) (hp : p≤x.length) :
    evV g x s (RecursiveParserStability.frozen bodies g x s k) E e p=
      evV h x t (tblV h x t (iterBoundV h x)) F e p := by
  apply RecursiveParserStability.lexical_eval hg hh x s t _ _ (ClockFreezing.frozen_ok _ _ _ _ _ _) _ E F e he p hp
  intro i hi q hq
  have hchoose : RecursiveParserStability.pick bodies i=true := by simp [RecursiveParserStability.pick,hi]
  rw [ClockFreezing.frozen_rows g x s _ _ k i hchoose []]
  have hn := List.getElem?_eq_getElem hi
  have hrow := RecursiveParserStability.helper_rows_eq hb hg (RecursiveParserStability.installed bodies)
    x s s (RecursiveParserStability.floor bodies x) i hi [] []
  rw [hrow]
  have hfixed := agreeV_from (RegularCaptureProduct.bound_fixed (RecursiveParserStability.grammar bodies) x s) 1
  have hc := hfixed i ⟨0,bodies[i]⟩ [] (RecursiveParserStability.installed bodies i bodies[i] hn) (by simp [words]) q hq
  rw [show RecursiveParserStability.floor bodies x=iterBoundV (RecursiveParserStability.grammar bodies) x+1 from rfl,←hc]
  exact RegularCaptureProduct.canonical_helpers_eq hb (RecursiveParserStability.installed bodies) hh x s t i q hi hq

theorem source_query (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (E : List (List Char)) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) :
    evV (source nodes R rs) x .callByValuePar (sourceTable nodes R rs x k) E (.call i []) p=
      evV (base nodes R) x .callByValueSeq (FiniteWordCaptureSelection.table nodes (FiniteSuffixReplay.palette R) x) [] (.call i []) p :=
  frozen_lexical_base (RegularCaptureProduct.helper_valid hn) (source_installed nodes R rs)
    (RegularCaptureProduct.original_installed nodes _) x _ _ k E [] (.call i []) (by simpa [Lexical] using hi) p hp

theorem target_lexical (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (e : MExp) (he : Lexical (base nodes R).rules.length e) (p : Nat) (hp : p≤x.length) :
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] e p=
      evV (base nodes R) x .callByValueSeq (FiniteWordCaptureSelection.table nodes (FiniteSuffixReplay.palette R) x) [] e p := by
  have hb : Installed (targetBodies nodes R) (base nodes R) := by
    simpa using RegularCaptureProduct.component_installed nodes (ExactWordCaptureMachine.observer (FiniteSuffixReplay.palette R)) []
  exact frozen_lexical_base (RegularCaptureProduct.component_valid nodes hn _ (ExactWordCaptureMachine.observer_valid _).1)
    (target_installed nodes R rs) hb x _ _ k [] [] e (by simpa [targetBodies,RegularCaptureProduct.component] using he) p hp

theorem target_query (nodes : List Node) (hn : RegularCaptureProduct.Valid nodes) (R : List (List Char)) (rs : List Spec)
    (x : List Char) (k : Nat) (i p : Nat) (hi : i<(base nodes R).rules.length) (hp : p≤x.length) :
    evV (target nodes R rs) x .callByValueSeq (targetTable nodes R rs x k) [] (.call i []) p=
      evV (base nodes R) x .callByValueSeq (FiniteWordCaptureSelection.table nodes (FiniteSuffixReplay.palette R) x) [] (.call i []) p :=
  target_lexical nodes hn R rs x k (.call i []) hi p hp

theorem source_ok (nodes : List Node) (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :
    OkTV x.length (sourceTable nodes R rs x k) := ClockFreezing.frozen_ok _ _ _ _ _ _

theorem target_ok (nodes : List Node) (R : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :
    OkTV x.length (targetTable nodes R rs x k) := ClockFreezing.frozen_ok _ _ _ _ _ _

end Shallot.MacroPeg.CBV.FiniteSuffixRecursiveHelpers
