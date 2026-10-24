import MacroPeg.CBV.DynamicScannerCorrespondence
import MacroPeg.CBV.StatefulActionExamples
import MacroPeg.CBV.StatefulScannerFastTable

namespace Shallot.MacroPeg.CBV.DynamicScannerFusionExamples
open DynamicScannerCompiler
open DynamicScannerCorrespondence
open DynamicScannerCapture (observer)
abbrev Form := DynamicScannerCompiler.Expr
abbrev machine := StatefulActionExamples.machine

def initial : Arg := .star (.lit ['a'])
def child : Arg := .seq (.param 0) (.lit ['a'])
def finish : Form := .seq (.lit ['!']) (.param 0)
def bodies : List Form := [
  .alt finish (.seq (.lit ['Z']) (.seq (.user 1 child) (.seq (.lit ['?']) (.param 0)))),
  .alt finish (.seq (.lit ['X']) (.seq (.user 0 child) (.seq (.lit ['?']) (.param 0))))]
def eof : Form := .notP .any
def root : Form := .seq (.user 0 initial) eof
def input := ("abZ"++"aaX"++"aaab!aaa"++"?aa?a").toList

theorem syntax_checked : bodies.all (check machine bodies)=true ∧ check machine bodies root=true := by
  decide +kernel

/-- Unlike fixed-action inference, the finite frontier check accepts
nonidentity stars and choices whose full transition actions differ. -/
theorem genuinely_dynamic :
    TotalCaptureSafety.check machine (DependentCaptureFilter.render initial)=true ∧
    TotalCaptureSafety.check machine (.alt (.lit ['a']) (.lit ['a','a']))=true ∧
    CaptureActionSafety.infer machine CaptureActionSafety.identity (DependentCaptureFilter.render initial)=none ∧
    CaptureActionSafety.infer machine CaptureActionSafety.identity (.alt (.lit ['a']) (.lit ['a','a']))=none := by
  decide +kernel

theorem language (x : List Char) (rest : Option (List Char)) :
    SObs (source machine 0 bodies) .callByValuePar (sourceExpr machine bodies root) x rest ↔
    SObs (target machine 0 bodies) .callByValueSeq (targetExpr machine bodies [] root) x rest :=
  checked_observations_iff machine 0 bodies syntax_checked.1 root syntax_checked.2 x rest

/-- Actual mutually recursive source and generated target tables. Captures
a → aa → aaa require starts 1 → 0 → 1; all parent values are reused on return. -/
theorem mutual_returns :
    evV (source machine 0 bodies) input .callByValuePar
      (tblV (source machine 0 bodies) input .callByValuePar (input.length+4)) []
      (sourceExpr machine bodies root) input.length=some (some 0) ∧
    evV (target machine 0 bodies) input .callByValueSeq
      (tblV (target machine 0 bodies) input .callByValueSeq (input.length+4)) []
      (targetExpr machine bodies [] root) input.length=some (some 0) := by
  constructor
  · apply StatefulScannerFastTable.physical machine _ _ _ (fun r => helper_rule machine _ r) 3
    decide +kernel
  · apply StatefulScannerFastTable.physical machine _ _ _ (fun r => helper_rule machine _ r) 3
    decide +kernel

theorem short_copies :
    ∀ x∈["abZaaXaaab!aa?aa?a".toList,"abZaaXaaab!aaa?a?a".toList,"abZaaXaaab!aaa?aa?".toList],
    evV (source machine 0 bodies) x .callByValuePar
      (tblV (source machine 0 bodies) x .callByValuePar (x.length+4)) []
      (sourceExpr machine bodies root) x.length=some none ∧
    evV (target machine 0 bodies) x .callByValueSeq
      (tblV (target machine 0 bodies) x .callByValueSeq (x.length+4)) []
      (targetExpr machine bodies [] root) x.length=some none := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  all_goals
    constructor
    all_goals
      apply StatefulScannerFastTable.physical machine _ _ _ (fun r => helper_rule machine _ r) 3
      decide +kernel

/-- The previous construction's demonstrated boundary is rejected by the
new syntax checker, rather than assumed away as a successful-scan premise. -/
theorem frontier_boundary_checked :
    TotalCaptureSafety.check machine (.lit ['a','!'])=false ∧
    check machine bodies (.user 0 (.lit ['a','!']))=false ∧
    TotalCaptureSafety.check machine (.lit ['b'])=false := by
  decide +kernel

def loopRoot : Form := .user 0 (.star (.lit []))

/-- A nullable argument is undefined at every ordinary physical clock on
every original input, even before a scanner or callee could reject. -/
theorem undefined_argument (x : List Char) :
    (∀ k, evV (source machine 0 bodies) x .callByValuePar
      (tblV (source machine 0 bodies) x .callByValuePar k) [] (sourceExpr machine bodies loopRoot) x.length=none) ∧
    (∀ k, evV (target machine 0 bodies) x .callByValueSeq
      (tblV (target machine 0 bodies) x .callByValueSeq k) [] (targetExpr machine bodies [] loopRoot) x.length=none) := by
  have hs : ∀ k, evV (source machine 0 bodies) x .callByValuePar
      (tblV (source machine 0 bodies) x .callByValuePar k) [] (sourceExpr machine bodies loopRoot) x.length=none := by
    intro k
    change evV _ _ _ _ _ (.call 2 [.star (.lit [])]) x.length=none
    rw [evV_call_par (source_rule machine 0 bodies 0 _ rfl) rfl (by decide)]
    have hloop : evV (source machine 0 bodies) x .callByValuePar
        (tblV (source machine 0 bodies) x .callByValuePar k) [] (.star (.lit [])) x.length=none := by
      rw [evV_star]
      exact evStar_stuck
        (by change some (some (sfx x x.length).length)=some (some x.length)
            rw [length_sfx x (Nat.le_refl _)]) (Nat.lt_irrefl _)
    simp only [evParArgs,hloop]
  exact ⟨hs,(undefined_iff machine 0 bodies (bodies_check_sound machine bodies syntax_checked.1)
    loopRoot (check_sound machine bodies loopRoot (by decide +kernel)) x).mp hs⟩

theorem argument_failure_clock_zero :
    evV (source machine 0 bodies) ['!'] .callByValuePar
      (tblV (source machine 0 bodies) ['!'] .callByValuePar 0) []
      (sourceExpr machine bodies (.user 0 (.lit ['a']))) 1=some none ∧
    evV (target machine 0 bodies) ['!'] .callByValueSeq
      (tblV (target machine 0 bodies) ['!'] .callByValueSeq 0) []
      (targetExpr machine bodies [] (.user 0 (.lit ['a']))) 1=some none := by
  decide +kernel

theorem even_and_empty_captures : ∀ x∈["aa!aa".toList,['!']],
    evV (source machine 0 bodies) x .callByValuePar
      (tblV (source machine 0 bodies) x .callByValuePar (x.length+2)) []
      (sourceExpr machine bodies root) x.length=some (some 0) ∧
    evV (target machine 0 bodies) x .callByValueSeq
      (tblV (target machine 0 bodies) x .callByValueSeq (x.length+2)) []
      (targetExpr machine bodies [] root) x.length=some (some 0) := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  all_goals
    constructor
    all_goals
      apply StatefulScannerFastTable.physical machine _ _ _ (fun r => helper_rule machine _ r) 1
      decide +kernel

def chosen : Form := .seq (.user 0 (.alt (.lit ['a']) (.lit ['a','a']))) eof
def long : Form := .seq (.user 0 (.lit ['a','a'])) eof

theorem committed_choice :
    evV (source machine 0 bodies) "aa!aa".toList .callByValuePar
      (tblV (source machine 0 bodies) "aa!aa".toList .callByValuePar 7) []
      (sourceExpr machine bodies chosen) 5=some none ∧
    evV (target machine 0 bodies) "aa!aa".toList .callByValueSeq
      (tblV (target machine 0 bodies) "aa!aa".toList .callByValueSeq 7) []
      (targetExpr machine bodies [] chosen) 5=some none ∧
    evV (source machine 0 bodies) "aa!aa".toList .callByValuePar
      (tblV (source machine 0 bodies) "aa!aa".toList .callByValuePar 7) []
      (sourceExpr machine bodies long) 5=some (some 0) ∧
    evV (target machine 0 bodies) "aa!aa".toList .callByValueSeq
      (tblV (target machine 0 bodies) "aa!aa".toList .callByValueSeq 7) []
      (targetExpr machine bodies [] long) 5=some (some 0) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    apply StatefulScannerFastTable.physical machine _ _ _ (fun r => helper_rule machine _ r) 1
    decide +kernel

end Shallot.MacroPeg.CBV.DynamicScannerFusionExamples
