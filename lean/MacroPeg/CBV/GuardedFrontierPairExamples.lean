import MacroPeg.CBV.GuardedFrontierPairCompiler
import MacroPeg.CBV.IndependentFrontierExamples

namespace Shallot.MacroPeg.CBV.GuardedFrontierPairExamples
open IndependentFrontierExamples (helpers left right ds root selection entries templateRoot sample tail
  recursiveTail recursiveEntries recursiveNested nullableArgs nullableSelection nullableRoot)
open GuardedPairSyntax (render parGrammar seqGrammar query sourceRule sourceBody)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gate : MExp := .seq (.andP (.lit ['a']))
  (.alt (.seq (.call 1 []) (.lit ['!'])) (.seq (.call 2 []) (.lit ['!'])))
def queries (q : MExp) : List MExp := [.eps,.eps,.eps,q]
def original (q body : MExp) : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++
  [⟨2,.seq (.andP q) (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) body)⟩]⟩

theorem checked : GuardedFrontierPairCompiler.check (original gate tail) selection entries (queries gate)=true := by decide +kernel

theorem root_checked : GuardedFrontierPairCompiler.rootCheck selection entries root (templateRoot ds)=true := by decide +kernel

theorem target_layout : (seqGrammar entries (queries gate)).rules.map MRule.arity=[0,0,0,0,0,0,0,0,0,0,2,2] := by decide +kernel

def sourceRun (x : List Char) (k : Nat) := evV (original gate tail) x .callByValuePar
  (tblV (original gate tail) x .callByValuePar k) [] root x.length

def targetRun (x : List Char) (k : Nat) := evV (seqGrammar entries (queries gate)) x .callByValueSeq
  (tblV (seqGrammar entries (queries gate)) x .callByValueSeq k) [] (render entries false (templateRoot ds)) x.length

theorem source_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'], sourceRun (sample n c) 20=some (some 0) := by decide +kernel

theorem target_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'], targetRun (sample n c) 20=some (some 0) := by decide +kernel

theorem source_gate_failure : sourceRun (sample 0 'b') 20=some none := by decide +kernel

theorem target_gate_failure : targetRun (sample 0 'b') 20=some none := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs (original gate tail) .callByValuePar root x rest ↔
      SObs (seqGrammar entries (queries gate)) .callByValueSeq (render entries false (templateRoot ds)) x rest :=
  GuardedFrontierPairCompiler.observations_iff (original gate tail) selection entries (queries gate) checked root
    (templateRoot ds) root_checked x rest

theorem recursive_checked : GuardedFrontierPairCompiler.check (original gate (recursiveTail root)) selection recursiveEntries (queries gate)=true := by decide +kernel

theorem recursive_root_checked : GuardedFrontierPairCompiler.rootCheck selection recursiveEntries root (templateRoot ds)=true := by decide +kernel

theorem recursive_source : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (original gate (recursiveTail root)) x .callByValuePar (tblV (original gate (recursiveTail root)) x .callByValuePar 20)
      [] root x.length=some (some 0) := by decide +kernel

theorem recursive_target : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (seqGrammar recursiveEntries (queries gate)) x .callByValueSeq (tblV (seqGrammar recursiveEntries (queries gate)) x .callByValueSeq 20)
      [] (render recursiveEntries false (templateRoot ds)) x.length=some (some 0) := by decide +kernel

/-- The real recursive query must run at the original position, before
maxScanner consumes the two captures' common source span. -/
theorem query_at_wrong_position_fails : evV (seqGrammar entries (queries gate)) (sample 1 'b') .callByValueSeq
    (tblV (seqGrammar entries (queries gate)) (sample 1 'b') .callByValueSeq 20) [] (render entries false gate)
    (ScannerFrontier.finalPos left.alphabet right.alphabet (sample 1 'b') (sample 1 'b').length)=some none := by decide +kernel

def failedQueries := queries MExp.failAlways

theorem nullable_checked : GuardedFrontierPairCompiler.check (original MExp.failAlways tail) nullableSelection entries failedQueries=true := by decide +kernel

theorem nullable_root_checked : GuardedFrontierPairCompiler.rootCheck nullableSelection entries nullableRoot (templateRoot nullableArgs)=true := by decide +kernel

theorem nullable_source (x : List Char) (k : Nat) :
    evV (original MExp.failAlways tail) x .callByValuePar (tblV (original MExp.failAlways tail) x .callByValuePar k)
      [] nullableRoot x.length=none := by
  have hs : evV (original MExp.failAlways tail) x .callByValuePar (tblV (original MExp.failAlways tail) x .callByValuePar k)
      [] (.star .eps) x.length=none := by rw [evV_star]; exact evStar_stuck (j := x.length) rfl (by omega)
  have ha : evV (original MExp.failAlways tail) x .callByValuePar (tblV (original MExp.failAlways tail) x .callByValuePar k) []
      (FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck) x.length=none := evV_seq_none hs
  have hr : ruleAtM (original MExp.failAlways tail).rules 3=some ⟨2,.seq (.andP MExp.failAlways)
      (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) tail)⟩ := rfl
  change evV _ _ _ _ [] (.call 3 [FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck,
    FrontierArgumentNormalization.argument right]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none ha]

theorem nullable_target (x : List Char) (k : Nat) :
    evV (seqGrammar entries failedQueries) x .callByValueSeq (tblV (seqGrammar entries failedQueries) x .callByValueSeq k) []
      (render entries false (templateRoot nullableArgs)) x.length=none :=
  (GuardedFrontierPairCompiler.undefined_iff (original MExp.failAlways tail) nullableSelection entries failedQueries nullable_checked
    nullableRoot (templateRoot nullableArgs) nullable_root_checked x).mp (nullable_source x) k

theorem prematurely_running_query_changes_undefinedness :
    evV (seqGrammar entries failedQueries) ['!'] .callByValueSeq (tblV (seqGrammar entries failedQueries) ['!'] .callByValueSeq 1) []
      (render entries false (.call 3 [])) 1=some none ∧
    evV (seqGrammar entries failedQueries) ['!'] .callByValueSeq (tblV (seqGrammar entries failedQueries) ['!'] .callByValueSeq 1) []
      (render entries false (templateRoot nullableArgs)) 1=none := by decide +kernel

def cycleQueries := queries (.call 3 [])

theorem cycle_checked : GuardedPairSyntax.check entries cycleQueries=true := by decide +kernel

theorem cycle_rows (x : List Char) (k : Nat) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV (parGrammar entries cycleQueries) x .callByValuePar k 3 W) p=none := by
  have hr : entries[3]?=some ⟨some (left.alphabet,right.alphabet),tail⟩ := rfl
  have hs : ruleAtM (parGrammar entries cycleQueries).rules 3=some (sourceRule entries cycleQueries 3
      ⟨some (left.alphabet,right.alphabet),tail⟩) := by rw [GuardedPairSyntax.par_rule,hr]; rfl
  induction k generalizing W with
  | zero => rfl
  | succ k ih =>
    rw [valAt_tblV_succ hs W hp]
    have hq : evV (parGrammar entries cycleQueries) x .callByValuePar (tblV (parGrammar entries cycleQueries) x .callByValuePar k) W
        (render entries true (.call 3 [])) p=none := by
      rw [GuardedPairSimulation.source_call entries cycleQueries x _ W 3 _ hr p hp]
      exact ih _
    have hpref : evV (parGrammar entries cycleQueries) x .callByValuePar (tblV (parGrammar entries cycleQueries) x .callByValuePar k) W
        (.andP (render entries true (.call 3 []))) p=none := by rw [CallLookahead.evV_peek,hq]; rfl
    exact evV_seq_none hpref

theorem cycle_source (x : List Char) (k : Nat) :
    evV (parGrammar entries cycleQueries) x .callByValuePar (tblV (parGrammar entries cycleQueries) x .callByValuePar k) []
      (render entries true (.call 3 [])) x.length=none := by
  rw [GuardedPairSimulation.source_call entries cycleQueries x _ [] 3 _ (show entries[3]?=some ⟨some (left.alphabet,right.alphabet),tail⟩ from rfl) x.length (Nat.le_refl _)]
  exact cycle_rows x k _ _ (Nat.le_refl _)

theorem cycle_target (x : List Char) (k : Nat) :
    evV (seqGrammar entries cycleQueries) x .callByValueSeq (tblV (seqGrammar entries cycleQueries) x .callByValueSeq k) []
      (render entries false (.call 3 [])) x.length=none :=
  (GuardedPairCorrespondence.undefined_iff entries cycleQueries cycle_checked (.call 3 []) x).mp (cycle_source x) k

def tinyEntries : List MixedScannerPairFusion.Entry := [⟨some ([],[]),.eps⟩]

theorem extra_header_clock_is_real :
    evV (parGrammar tinyEntries []) [] .callByValuePar (tblV (parGrammar tinyEntries []) [] .callByValuePar 1) [] (render tinyEntries true (.call 0 [])) 0=some (some 0) ∧
    evV (seqGrammar tinyEntries []) [] .callByValueSeq (tblV (seqGrammar tinyEntries []) [] .callByValueSeq 1) [] (render tinyEntries false (.call 0 [])) 0=none ∧
    evV (seqGrammar tinyEntries []) [] .callByValueSeq (tblV (seqGrammar tinyEntries []) [] .callByValueSeq 2) [] (render tinyEntries false (.call 0 [])) 0=some (some 0) := by decide +kernel

theorem retained_query_rejected : GuardedPairSyntax.check entries (queries (.param 0))=false := by decide +kernel

end Shallot.MacroPeg.CBV.GuardedFrontierPairExamples
