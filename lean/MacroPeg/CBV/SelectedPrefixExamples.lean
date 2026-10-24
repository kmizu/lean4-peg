import MacroPeg.CBV.SelectedPrefixGrammar
import MacroPeg.CBV.RuntimePrefixExamples
import MacroPeg.CBV.NullableStarControl

/-! Original argument selection may fail or diverge independently of the
header. Certificates are derived from the actual argument syntax below. -/
namespace Shallot.MacroPeg.CBV.SelectedPrefixExamples
open SelectedPrefixGrammar
open RuntimeShiftFilter (scanner)
open RuntimePrefixExamples (code scanner_captured code_prefixFree)

def two : MExp := .seq scanner scanner
def headTest : MExp := .seq two (.lit ['X'])
def guardedHead : MExp := .seq (.notP headTest) scanner

theorem guarded_captured (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s T E guardedHead p=some (some q)) : code (pre x p q) := by
  cases ht : evV g x s T E headTest p with
  | none =>
    have hn : evV g x s T E (.notP headTest) p=none := by simp only [evV,ht]
    rw [guardedHead,evV_seq_none hn] at h
    cases h
  | some result => cases result with
    | none =>
      have hn : evV g x s T E (.notP headTest) p=some (some p) := by simp only [evV,ht]
      rw [guardedHead,evV_seq_ok hn] at h
      exact scanner_captured g x s T E p q hp h
    | some j =>
      have hn : evV g x s T E (.notP headTest) p=some none := by simp only [evV,ht]
      rw [guardedHead,evV_seq_fail hn] at h
      cases h

def header : RuntimePrefixGrammar.Header where
  head := guardedHead
  pure := by
    simp [guardedHead,headTest,two,RuntimeShiftFilter.scanner,NestedScannerArguments.scan,
      NestedScannerArguments.choice,ParserPrefixFusion.Pure,MExp.failAlways]
  code := code
  prefixFree := code_prefixFree
  captured := guarded_captured

def Shape (a : MExp) : Prop :=
  ∀ (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p q : Nat), p≤x.length →
    evV g x s T E a p=some (some q) →
    ∃ u v, code u ∧ code v ∧ pre x p q=u++v

theorem two_shape : Shape two := by
  intro g x s T E p q hp h
  have he := RuntimePrefixGrammar.argument_eval RuntimePrefixExamples.header g x s T E p
  change evV g x s T E two p=_ at he
  rw [he] at h
  cases hfirst : RuntimePrefixGrammar.lexical RuntimePrefixExamples.header x p with
  | none => simp [hfirst] at h
  | some result => cases result with
    | none => simp [hfirst] at h
    | some j =>
      simp only [hfirst] at h
      have ha := RuntimePrefixGrammar.lexical_success RuntimePrefixExamples.header x p j hp hfirst
      have hb := RuntimePrefixGrammar.lexical_success RuntimePrefixExamples.header x j q ha.1 h
      exact ⟨pre x p j,pre x j q,ha.2.2,hb.2.2,
        SequenceArguments.pre_concat hp hb.1 ha.2.1 hb.2.1⟩

theorem before_not_shape (a test : MExp) (ha : Shape a) : Shape (.seq (.notP test) a) := by
  intro g x s T E p q hp h
  cases ht : evV g x s T E test p with
  | none =>
    have hn : evV g x s T E (.notP test) p=none := by simp only [evV,ht]
    rw [evV_seq_none hn] at h
    cases h
  | some result => cases result with
    | none =>
      have hn : evV g x s T E (.notP test) p=some (some p) := by simp only [evV,ht]
      rw [evV_seq_ok hn] at h
      exact ha g x s T E p q hp h
    | some j =>
      have hn : evV g x s T E (.notP test) p=some none := by simp only [evV,ht]
      rw [evV_seq_fail hn] at h
      cases h

theorem after_not_shape (a test : MExp) (ha : Shape a) : Shape (.seq a (.notP test)) := by
  intro g x s T E p q hp h
  cases hv : evV g x s T E a p with
  | none => rw [evV_seq_none hv] at h; cases h
  | some result => cases result with
    | none => rw [evV_seq_fail hv] at h; cases h
    | some j =>
      rw [evV_seq_ok hv] at h
      cases ht : evV g x s T E test j with
      | none => simp only [evV,ht] at h; cases h
      | some result => cases result with
        | none =>
          have he : j=q := by simpa only [evV,ht,Option.some.injEq] using h
          subst q
          exact ha g x s T E p j hp hv
        | some z => simp only [evV,ht] at h; cases h

theorem alt_shape (a b : MExp) (ha : Shape a) (hb : Shape b) : Shape (.alt a b) := by
  intro g x s T E p q hp h
  cases hv : evV g x s T E a p with
  | none => rw [evV_alt_none hv] at h; cases h
  | some result => cases result with
    | none => rw [evV_alt_fail hv] at h; exact hb g x s T E p q hp h
    | some j =>
      rw [evV_alt_ok hv] at h
      have he : j=q := by simpa only [Option.some.injEq] using h
      subst q
      exact ha g x s T E p j hp hv

theorem empty_loop_none (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) : evV g x s T E (.star (.lit [])) p=none := by
  rw [evV_star]
  exact NullableStarControl.never_fail_star_none _ (by intro q; simp [evV,Shallot.stripPrefix?]) p

theorem empty_loop_shape : Shape (.star (.lit [])) := by
  intro g x s T E p q hp h
  rw [empty_loop_none] at h
  cases h

def firstArg : MExp := .alt (.seq (.notP (.lit ['a'])) two) (.seq two (.notP (.lit ['Z'])))
def secondArg : MExp := .alt (.seq (.notP (.lit ['U'])) firstArg) (.star (.lit []))

theorem first_shape : Shape firstArg :=
  alt_shape _ _ (before_not_shape _ _ two_shape) (after_not_shape _ _ two_shape)
theorem second_shape : Shape secondArg :=
  alt_shape _ _ (before_not_shape _ _ first_shape) empty_loop_shape

def users : List (User header) := [
  {arg := firstArg, pure := by
    simp [firstArg,two,RuntimeShiftFilter.scanner,NestedScannerArguments.scan,
      NestedScannerArguments.choice,ParserPrefixFusion.Pure,MExp.failAlways]
   captured := first_shape, body := RuntimePrefixExamples.recursiveTail '@' 1},
  {arg := secondArg, pure := by
    simp [secondArg,firstArg,two,RuntimeShiftFilter.scanner,NestedScannerArguments.scan,
      NestedScannerArguments.choice,ParserPrefixFusion.Pure,MExp.failAlways]
   captured := second_shape, body := RuntimePrefixExamples.recursiveTail '%' 0}]
def root : MExp := .call 0 []

theorem all_inputs (e : MExp) (x : List Char) (r : Option (List Char)) :
    SObs (source header users) .callByValuePar (render header users true e) x r ↔
      SObs (target header users) .callByValueSeq (render header users false e) x r :=
  observations_iff header users e x r

/-- B succeeds but the independently tested body head fails. Ordinary
stage-zero tables differ; the source seed is a genuine first-stage failure. -/
theorem early_head_failure :
    evV (source header users) "a#a#X".toList .callByValuePar
      (tblV (source header users) "a#a#X".toList .callByValuePar 0) [] (render header users true root) 5=none ∧
    evV (source header users) "a#a#X".toList .callByValuePar
      (tblV (source header users) "a#a#X".toList .callByValuePar 1) [] (render header users true root) 5=some none ∧
    evV (source header users) "a#a#X".toList .callByValuePar
      (sourceTable header users "a#a#X".toList 0) [] (render header users true root) 5=some none ∧
    evV (target header users) "a#a#X".toList .callByValueSeq
      (tblV (target header users) "a#a#X".toList .callByValueSeq 0) [] (render header users false root) 5=some none := by
  decide +kernel

theorem selected_argument_execution :
    evV (source header users) RuntimePrefixExamples.good .callByValuePar
      (tblV (source header users) RuntimePrefixExamples.good .callByValuePar 8) []
      (render header users true root) RuntimePrefixExamples.good.length=some (some 0) ∧
    evV (source header users) RuntimePrefixExamples.shortParent .callByValuePar
      (tblV (source header users) RuntimePrefixExamples.shortParent .callByValuePar 8) []
      (render header users true root) RuntimePrefixExamples.shortParent.length=some none ∧
    evV (source header users) "a#a#Z".toList .callByValuePar
      (tblV (source header users) "a#a#Z".toList .callByValuePar 0) [] (render header users true root) 5=some none ∧
    evV (target header users) "a#a#Z".toList .callByValueSeq
      (tblV (target header users) "a#a#Z".toList .callByValueSeq 0) [] (render header users false root) 5=some none := by
  decide +kernel

theorem undefined_at_every_stage (k : Nat) :
    evV (source header users) "U".toList .callByValuePar
      (tblV (source header users) "U".toList .callByValuePar k) [] (render header users true (.call 1 [])) 1=none ∧
    evV (target header users) "U".toList .callByValueSeq
      (tblV (target header users) "U".toList .callByValueSeq k) [] (render header users false (.call 1 [])) 1=none := by
  have harg : argument header users[1] "U".toList 1=none := by decide +kernel
  exact undefined_argument header users 1 users[1] rfl "U".toList 1 harg _ _ [] []

theorem translated_execution :
    SObs (target header users) .callByValueSeq (render header users false root)
      RuntimePrefixExamples.good (some []) ∧
    SObs (target header users) .callByValueSeq (render header users false root)
      RuntimePrefixExamples.shortParent none := by
  constructor
  · apply (all_inputs root RuntimePrefixExamples.good (some [])).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header users) (by decide)
      (render_firstOrder header users true root) 8 (Nat.le_refl _) selected_argument_execution.1
    rw [sfx_self] at hd
    obtain ⟨t,rest,rfl,hlen⟩ := obsR_ok ho
    have hr : rest=[] := List.length_eq_zero_iff.mp hlen
    subst rest
    exact ⟨_,hd,rfl⟩
  · apply (all_inputs root RuntimePrefixExamples.shortParent none).mp
    obtain ⟨o,hd,ho⟩ := evV_derives (source_firstOrder header users) (by decide)
      (render_firstOrder header users true root) 8 (Nat.le_refl _) selected_argument_execution.2.1
    rw [sfx_self,obsR_fail ho] at hd
    exact ⟨_,hd,rfl⟩

end Shallot.MacroPeg.CBV.SelectedPrefixExamples
