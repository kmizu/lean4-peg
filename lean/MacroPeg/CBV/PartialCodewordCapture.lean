import MacroPeg.CBV.RuntimeShiftFilter
import MacroPeg.CBV.LastCodewordCandidate

/-! An experimental fixed Seq grammar for captures ending inside a runtime
codeword. Finite kernel executions below are not an all-input translation
or a proof about the general Par/Seq language classes. -/
namespace Shallot.MacroPeg.CBV.PartialCodewordCapture
open NestedScannerArguments (scan)
open RuntimeShiftFilter (block scanner)
open CodewordReplay (power)

def look (a : MExp) : MExp := .notP (.notP a)
def runA : MExp := scan ['a']
def argument : MExp := .seq (.star (.seq scanner (look scanner))) runA
def eof : MExp := .notP .any

def source : MGrammar := ⟨[⟨1,.seq scanner (.seq (.param 0)
  (.seq (.lit ['!']) (.seq (.param 0) eof)))⟩]⟩
def sourceRoot : MExp := .call 0 [argument]

/-- The final lookahead ties the comparison to the actual replay endpoint.
A successful comparison of an earlier prefix alone is insufficient. -/
def checkBody : MExp :=
  .seq (.star (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))))
    (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['!']))))

def restArgument : MExp := .seq (.lit ['#']) argument

def target : MGrammar := ⟨[
  ⟨1,checkBody⟩,
  ⟨2,.seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['!'])
    (.seq (.param 0) (.seq (.param 1) eof))))⟩,
  ⟨1,.seq (.lit ['#']) (.seq (.param 0) (.seq (.lit ['!']) (.seq (.param 0) eof)))⟩]⟩

def longTest : MExp := look (.seq scanner scanner)
def targetRoot : MExp := .seq (look (.call 0 [runA]))
  (.alt (.seq longTest (.call 1 [runA,restArgument]))
    (.seq (.notP longTest) (.call 2 [runA])))

def captured (k n : Nat) : List Char := power (block k) n ++ List.replicate k 'a'
def input (k n : Nat) : List Char := block k ++ captured k n ++ ['!'] ++ captured k n

/-- The intended captures have an unbounded partial final codeword. In
particular positive k cannot be represented as any number of whole copies
of this same runtime codeword. This is a syntactic boundary, not separation. -/
theorem captured_not_whole (k n m : Nat) (hk : 0<k) :
    captured k n ≠ power (block k) m := by
  intro h
  have len : ∀ n, (power (block k) n).length = n*(k+1) := by
    intro n
    induction n with
    | zero => simp [power]
    | succ n ih => simp [power,block,Nat.add_mul,Nat.mul_add]
  have hh := congrArg List.length h
  simp only [captured,List.length_append,List.length_replicate,len] at hh
  have hm := congrArg (fun t => t % (k+1)) hh
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_add,
    Nat.zero_mod] at hm
  simp only [Nat.mod_eq_of_lt (by omega : k<k+1)] at hm
  omega

/-- A scanner can resume at any real suffix, independently of grammar,
strategy, table, or retained values. -/
theorem run_at (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (k p : Nat)
    (c : Char) (rest : List Char) (hc : NestedScannerArguments.accepts ['a'] c = false)
    (hp : p≤x.length) (hs : sfx x p=List.replicate k 'a'++c::rest) :
    evV g x s T E runA p=some (some (c::rest).length) := by
  rw [runA,NestedScannerArguments.scan_eval g x s T E ['a'] p hp,hs]
  have hd : (List.replicate k 'a'++c::rest).dropWhile
      (NestedScannerArguments.accepts ['a'])=c::rest := by
    clear hs
    induction k with
    | zero => simp [hc]
    | succ k ih => simpa [List.replicate_succ,NestedScannerArguments.accepts,Shallot.beqChar] using ih
  rw [hd]

/-- The actual argument captures n complete runtime words and then the
partial a-run of the last word, for all lengths and counts. This derives
its endpoint from evaluation rather than assuming a capture shape. -/
theorem argument_at (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (k n p : Nat) (rest : List Char)
    (hp : p≤x.length)
    (hs : sfx x p=power (block k) (n+1)++List.replicate k 'a'++'!'::rest) :
    evV g x s T E argument p=
      some (some ('#'::(List.replicate k 'a'++'!'::rest)).length) := by
  let A := fun q => evV g x s T E scanner q
  let finalRest := List.replicate k 'a'++'!'::rest
  have hblock : block k≠[] := by simp [block]
  have hstep : ∀ j r, j≤x.length → sfx x j=block k++r → A j=some (some r.length) :=
    fun j r hj hr => PrefixCodeCapture.scanner_at g x s T E j k r hj hr
  have ht := LastCodewordCandidate.constant_trace x (block k) hblock A hstep
    (n+1) p finalRest hp (by simpa only [finalRest,List.append_assoc] using hs)
  have hb : finalRest.length≤x.length := by have := InlineRepeat.trace_le ht; omega
  have hrest : sfx x finalRest.length=finalRest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p)
      ⟨power (block k) (n+1),by simpa only [finalRest,List.append_assoc] using hs⟩).choose_spec
  have hrun := run_at g x s T E k finalRest.length '!' rest (by decide) hb hrest
  have hend : A finalRest.length=some none := by
    rw [show A finalRest.length=evV g x s T E (.seq runA (.lit ['#'])) finalRest.length from rfl,
      evV_seq_ok hrun]
    have hbang : sfx x ('!'::rest).length='!'::rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x finalRest.length) ⟨List.replicate k 'a',hrest⟩).choose_spec
    simp only [List.length_cons] at hbang
    simp only [evV,List.length_cons,hbang]
    rfl
  obtain ⟨q,hq,_,hstar⟩ := LastCodewordRotation.last_trace A n p _ ht hend
  have hs' : sfx x p=power (block k) n++(block k++finalRest) := by
    rw [hs,LastCodewordCandidate.power_succ_right]
    simp only [finalRest,List.append_assoc]
  have ht' := LastCodewordCandidate.constant_trace x (block k) hblock A hstep
    n p (block k++finalRest) hp hs'
  have he : q=(block k++finalRest).length := by
    have hh := (InlineRepeat.trace_steps (LastCodewordRotation.step_trace hq)).symm.trans
      (InlineRepeat.trace_steps ht')
    simpa using hh
  have hsuffix : sfx x (block k++finalRest).length=block k++finalRest :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨power (block k) n,hs'⟩).choose_spec
  have hb' : (block k++finalRest).length≤x.length := by
    have := InlineRepeat.trace_le ht'; omega
  have hstar' : evV g x s T E (.star (.seq scanner (look scanner))) p=
      some (some (block k++finalRest).length) := by
    change evV g x s T E (LastCodewordRotation.argument scanner) p=_
    rw [LastCodewordRotation.argument_eval]
    exact he ▸ hstar
  rw [argument,evV_seq_ok hstar']
  exact run_at g x s T E k _ '#' finalRest (by decide) hb'
    (by simpa only [block,List.append_assoc,List.singleton_append] using hsuffix)

theorem input_split (k n : Nat) :
    input k n=captured k n++('#'::(List.replicate k 'a'++'!'::captured k n)) := by
  have commute : block k++power (block k) n=power (block k) n++block k := by
    rw [←LastCodewordCandidate.power_succ_right]
    simp [power,List.replicate_succ]
  calc
    input k n = (block k++power (block k) n)++
        (List.replicate k 'a'++'!'::captured k n) := by
      simp [input,captured,List.append_assoc]
    _ = (power (block k) n++block k)++
        (List.replicate k 'a'++'!'::captured k n) := by rw [commute]
    _ = _ := by simp [captured,block,List.append_assoc]

/-- The complete value is obtained from the actual successful capture at
all k,n, including empty and short captures. -/
theorem actual_capture (g : MGrammar) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (k n : Nat) :
    let x := input k n
    let q := ('#'::(List.replicate k 'a'++'!'::captured k n)).length
    evV g x s T E argument x.length=some (some q) ∧
      pre x x.length q=captured k n := by
  dsimp only []
  constructor
  · apply argument_at g (input k n) s T E k n _ (captured k n) (Nat.le_refl _)
    rw [sfx_self]
    simp only [input,captured,power,List.replicate_succ,List.flatten_cons,
      List.append_assoc,List.cons_append,List.nil_append]
  · exact pre_eq ⟨[],by simp⟩ (input_split k n)

theorem firstOrder : source.FirstOrder ∧ target.FirstOrder ∧
    sourceRoot.FirstOrder ∧ targetRoot.FirstOrder := by
  simp [MGrammar.FirstOrder,source,target,sourceRoot,targetRoot,checkBody,restArgument,
    longTest,argument,runA,scanner,look,eof,scan,NestedScannerArguments.choice,
    MExp.FirstOrder,MExp.FirstOrderArgs,MExp.failAlways]

/-- The failed prefix-only check is preserved as a concrete rejected
compilation attempt, rather than hidden by the corrected examples. -/
def prefixOnly : MGrammar := ⟨[
  ⟨1,.seq (.star (.seq (.lit ['#']) (.seq (.param 0) (look (.lit ['#'])))))
      (.seq (.lit ['#']) (.param 0))⟩,
  target.rules[1],target.rules[2]]⟩

theorem prefix_only_false_positive :
    let x := "#a#!#a".toList
    evV prefixOnly x .callByValueSeq (tblV prefixOnly x .callByValueSeq 1)
      [] targetRoot x.length = some (some 0) := by
  decide +kernel

def samples : List (List Char) :=
  [input 0 0,input 0 3,input 1 0,input 1 1,input 2 2,input 5 3]

/-- Ordinary physical Par and Seq tables accept the same concrete inputs,
including short captures, empty captures, multiple words, and full reuse. -/
theorem sample_executions : ∀ x ∈ samples,
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [] sourceRoot x.length = some (some 0) ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [] targetRoot x.length = some (some 0) := by
  decide +kernel

/-- A prefix-only preflight accepts #a#!#a incorrectly. Requiring the
comparison to reach ! removes this concrete false positive. -/
theorem endpoint_regression :
    let x := "#a#!#a".toList
    evV source x .callByValuePar (tblV source x .callByValuePar 1) [] sourceRoot x.length = some none ∧
    evV target x .callByValueSeq (tblV target x .callByValueSeq 1) [] targetRoot x.length = some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.PartialCodewordCapture
