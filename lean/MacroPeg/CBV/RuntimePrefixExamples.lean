import MacroPeg.CBV.RuntimePrefixGrammar
import MacroPeg.CBV.PrefixCodeCaptureExamples

/-! The concrete unbounded runtime header satisfies the compiler's code
certificate. Recursive Seq observations below follow from the all-input
translation, rather than only from finite candidate executions. -/
namespace Shallot.MacroPeg.CBV.RuntimePrefixExamples
open RuntimePrefixGrammar
open RuntimeShiftFilter (scanner)
open NestedScannerArguments (accepts)

def code (w : List Char) : Prop := w.dropWhile (accepts ['a'])=['#']

theorem code_prefixFree : PrefixCodeCapture.PrefixFree code := by
  rintro u v hu hv ⟨r,hr⟩
  change u.dropWhile (accepts ['a'])=['#'] at hu
  change v.dropWhile (accepts ['a'])=['#'] at hv
  rw [←hr] at hv
  have he : r=[] := by simpa [List.dropWhile_append,hu] using hv
  simpa [he] using hr

theorem scanner_captured (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E scanner p=some (some q)) : code (pre x p q) := by
  let before := (sfx x p).takeWhile (accepts ['a'])
  let after := (sfx x p).dropWhile (accepts ['a'])
  have hsplit : sfx x p=before++after := (List.takeWhile_append_dropWhile (p := accepts ['a']) (l := sfx x p)).symm
  have hxs := suffix_trans (sfx_is_suffix x p) ⟨before,hsplit⟩
  rw [RuntimeShiftFilter.scanner,evV_seq_ok (NestedScannerArguments.scan_eval g x s T E ['a'] p hp)] at h
  change evV g x s T E (.lit ['#']) after.length=some (some q) at h
  simp only [evV,sfx_suffix hxs.choose_spec] at h
  cases hs : Shallot.stripPrefix? ['#'] after with
  | none => simp [hs] at h
  | some rest =>
    have hq : rest.length=q := by simpa only [hs,Option.some.injEq] using h
    have ha : after=['#']++rest := (CBVtoCBN.stripPrefix_exact _ _ _).mp hs
    have hfull : sfx x p=(before++['#'])++rest := by rw [hsplit,ha,List.append_assoc]
    have hc := pre_eq (sfx_is_suffix x p) hfull
    rw [length_sfx x hp,hq] at hc
    rw [hc]
    change (before++['#']).dropWhile (accepts ['a'])=['#']
    rw [List.dropWhile_append_of_pos (List.all_eq_true.mp (List.all_takeWhile (p := accepts ['a']) (l := sfx x p)))]
    rfl

def header : Header where
  head := scanner
  pure := by
    simp [RuntimeShiftFilter.scanner,NestedScannerArguments.scan,NestedScannerArguments.choice,
      ParserPrefixFusion.Pure,MExp.failAlways]
  code := code
  prefixFree := code_prefixFree
  captured := scanner_captured

def recursiveTail (mark : Char) (next : Nat) : MExp :=
  .alt (.seq (.lit [mark]) (.seq (.call next []) (.seq (.lit ['?']) (.param 0)))) (.lit ['!'])
def tails : List MExp := [recursiveTail '@' 1,recursiveTail '%' 0]
def root : MExp := .call 0 []
def good : List Char := "aa#aa#aa#@aaa#aaa#aaa#%a#a#a#!?aaa#aaa#?aa#aa#".toList
def shortParent : List Char := "aa#aa#aa#@aaa#aaa#aaa#%a#a#a#!?aaa#aaa#?aa#".toList
def unequalChild : List Char := "aa#aa#aa#@aaa#aa#aaa#%a#a#a#!?aaa#aaa#?aa#aa#".toList

theorem source_execution :
    evV (source header tails) good .callByValuePar
      (tblV (source header tails) good .callByValuePar 8) [] (render header tails true root) good.length=some (some 0) ∧
    evV (source header tails) shortParent .callByValuePar
      (tblV (source header tails) shortParent .callByValuePar 8) [] (render header tails true root) shortParent.length=some none ∧
    evV (source header tails) unequalChild .callByValuePar
      (tblV (source header tails) unequalChild .callByValuePar 8) [] (render header tails true root) unequalChild.length=some none := by
  decide +kernel

/-- Without the preflight, Seq would query the still-undefined stage-zero
row after one header although the original two-header argument has already
failed. The generated call preserves the finite failure at stage zero. -/
theorem preflight_stage_zero :
    evV (source header tails) "a#".toList .callByValuePar
      (tblV (source header tails) "a#".toList .callByValuePar 0) []
      (render header tails true root) 2=some none ∧
    evV (target header tails) "a#".toList .callByValueSeq
      (tblV (target header tails) "a#".toList .callByValueSeq 0) []
      (render header tails false root) 2=some none ∧
    evV (target header tails) "a#".toList .callByValueSeq
      (tblV (target header tails) "a#".toList .callByValueSeq 0) []
      (.call 0 [scanner]) 2=none := by
  decide +kernel

theorem all_inputs (x : List Char) (r : Option (List Char)) :
    SObs (source header tails) .callByValuePar (render header tails true root) x r ↔
      SObs (target header tails) .callByValueSeq (render header tails false root) x r :=
  observations_iff header tails root x r

/-- This also closes the all-input correspondence for the exact source and
candidate target grammars from the earlier physical recursive examples. -/
theorem previous_candidate_all_inputs (x : List Char) (r : Option (List Char)) :
    SObs PrefixCodeCaptureExamples.source .callByValuePar PrefixCodeCaptureExamples.sourceCall x r ↔
      SObs PrefixCodeCaptureExamples.target .callByValueSeq PrefixCodeCaptureExamples.targetCall x r :=
  observations_iff header [recursiveTail '@' 0] root x r

theorem translated_execution :
    SObs (target header tails) .callByValueSeq (render header tails false root) good (some []) ∧
    SObs (target header tails) .callByValueSeq (render header tails false root) shortParent none ∧
    SObs (target header tails) .callByValueSeq (render header tails false root) unequalChild none := by
  have accept (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 8) [] (render header tails true root) x.length=some (some 0)) :
      SObs (target header tails) .callByValueSeq (render header tails false root) x (some []) := by
    apply (all_inputs x (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 8 (Nat.le_refl _) h
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  have reject (x : List Char)
      (h : evV (source header tails) x .callByValuePar
        (tblV (source header tails) x .callByValuePar 8) [] (render header tails true root) x.length=some none) :
      SObs (target header tails) .callByValueSeq (render header tails false root) x none := by
    apply (all_inputs x none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header tails) (by decide)
      (render_firstOrder header tails true root) 8 (Nat.le_refl _) h
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩
  exact ⟨accept good source_execution.1,reject shortParent source_execution.2.1,
    reject unequalChild source_execution.2.2⟩

end Shallot.MacroPeg.CBV.RuntimePrefixExamples
