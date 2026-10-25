import MacroPeg.CBV.CapturedOriginCompiler
import MacroPeg.CBV.IndependentFrontierExamples

namespace Shallot.MacroPeg.CBV.CapturedOriginExamples
open IndependentFrontierExamples (helpers left right ds root selection entries templateRoot sample tail recursiveTail recursiveEntries recursiveNested
  nullableArgs nullableSelection nullableRoot)
open CapturedOriginQuery (Plan compile)
open CapturedOriginNormalization (generatedQueries)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def gate : Plan := .alt (.after false (.lit ['c'])) (.after true (.lit ['b']))
def plans (q : Plan) : List Plan := [.test .eps,.test .eps,.test .eps,q]
def original (q : Plan) (body : MExp) : MGrammar := ⟨helpers.map (fun b => ⟨0,b⟩) ++
  [⟨2,.seq (.andP (compile left.alphabet right.alphabet false q))
    (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) body)⟩]⟩

theorem checked : CapturedOriginCompiler.check (original gate tail) selection entries (plans gate)=true := by decide +kernel

theorem root_checked : CapturedOriginCompiler.rootCheck selection entries root (templateRoot ds)=true := by decide +kernel

theorem old_closed_check_rejects : GuardedPairSyntax.check entries (generatedQueries entries (plans gate) false)=false := by decide +kernel

theorem header_query_is_closed : GuardedPairSyntax.check entries (generatedQueries entries (plans gate) true)=true := by decide +kernel

def sourceRun (x : List Char) (k : Nat) := evV (original gate tail) x .callByValuePar (tblV (original gate tail) x .callByValuePar k) [] root x.length

def targetRun (x : List Char) (k : Nat) := evV (CapturedOriginCompiler.target entries (plans gate)) x .callByValueSeq
  (tblV (CapturedOriginCompiler.target entries (plans gate)) x .callByValueSeq k) [] (GuardedPairSyntax.render entries false (templateRoot ds)) x.length

theorem source_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'], sourceRun (sample n c) 20=some (some 0) := by decide +kernel

theorem target_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'], targetRun (sample n c) 20=some (some 0) := by decide +kernel

theorem query_depends_on_retained_values :
    evV (original gate tail) (sample 1 'b') .callByValuePar (tblV (original gate tail) (sample 1 'b') .callByValuePar 20)
      [['a','b'],['a']] (compile left.alphabet right.alphabet false gate) (sample 1 'b').length=some (some (sample 1 'b').length) ∧
    evV (original gate tail) (sample 1 'b') .callByValuePar (tblV (original gate tail) (sample 1 'b') .callByValuePar 20)
      [['a'],['a','b']] (compile left.alphabet right.alphabet false gate) (sample 1 'b').length=some none := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs (original gate tail) .callByValuePar root x rest ↔
      SObs (CapturedOriginCompiler.target entries (plans gate)) .callByValueSeq (GuardedPairSyntax.render entries false (templateRoot ds)) x rest :=
  CapturedOriginCompiler.observations_iff (original gate tail) selection entries (plans gate) checked root (templateRoot ds) root_checked x rest

theorem recursive_checked : CapturedOriginCompiler.check (original gate (recursiveTail root)) selection recursiveEntries (plans gate)=true := by decide +kernel

theorem recursive_root_checked : CapturedOriginCompiler.rootCheck selection recursiveEntries root (templateRoot ds)=true := by decide +kernel

theorem recursive_source : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (original gate (recursiveTail root)) x .callByValuePar (tblV (original gate (recursiveTail root)) x .callByValuePar 20)
      [] root x.length=some (some 0) := by decide +kernel

theorem recursive_target : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (CapturedOriginCompiler.target recursiveEntries (plans gate)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target recursiveEntries (plans gate)) x .callByValueSeq 20) []
      (GuardedPairSyntax.render recursiveEntries false (templateRoot ds)) x.length=some (some 0) := by decide +kernel

def recursiveGate : Plan := .alt (.after false (.seq (.lit ['c']) (.call 0 [])))
  (.after true (.seq (.lit ['b']) (.call 0 [])))

theorem recursive_query_tail_checked : CapturedOriginCompiler.check (original recursiveGate tail) selection entries (plans recursiveGate)=true := by decide +kernel

theorem recursive_query_tail_executes : ∀ c∈['b','c'],
    evV (CapturedOriginCompiler.target entries (plans recursiveGate)) (sample 2 c) .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans recursiveGate)) (sample 2 c) .callByValueSeq 20) []
      (GuardedPairSyntax.render entries false (templateRoot ds)) (sample 2 c).length=some (some 0) := by decide +kernel

theorem non_origin_tail_rejected : CapturedOriginQuery.check entries (.after false (.param 1))=false := by decide +kernel

def nullableGate : Plan := .star (.after false .eps)

theorem nullable_plan_checked : CapturedOriginNormalization.check entries (plans nullableGate)=true := by decide +kernel

theorem nullable_closed_rows (x : List Char) (k : Nat) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV (CapturedOriginNormalization.prepared entries (plans nullableGate)) x .callByValuePar k 3 W) p=none := by
  let g := CapturedOriginNormalization.prepared entries (plans nullableGate)
  have hr : ruleAtM g.rules 3=some ⟨2,.seq (.andP (GuardedPairSyntax.render entries true
      (compile left.alphabet right.alphabet true nullableGate)))
      (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) tail)⟩ := rfl
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr W hp]
    have hq : evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true nullableGate)) p=none := by
      change evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (.star (.andP (.seq (GuardedPairSyntax.render entries true (NestedScannerArguments.scan left.alphabet)) .eps))) p=none
      rw [CapturedOriginQuery.render_scan,evV_star]
      apply evStar_stuck (j := p)
      · rw [CallLookahead.evV_peek,evV_seq_ok (NestedScannerArguments.scan_eval g x .callByValuePar (tblV g x .callByValuePar k) W left.alphabet p hp)]
        rfl
      · omega
    have hpre : evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (.andP (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true nullableGate))) p=none := by
      rw [CallLookahead.evV_peek,hq]; rfl
    exact evV_seq_none hpre

theorem nullable_closed_source (x : List Char) (k : Nat) :
    evV (CapturedOriginNormalization.prepared entries (plans nullableGate)) x .callByValuePar
      (tblV (CapturedOriginNormalization.prepared entries (plans nullableGate)) x .callByValuePar k) []
      (GuardedPairSyntax.render entries true (.call 3 [])) x.length=none := by
  rw [GuardedPairSimulation.source_call entries _ x _ [] 3 _
    (show entries[3]?=some ⟨some (left.alphabet,right.alphabet),tail⟩ from rfl) x.length (Nat.le_refl _)]
  exact nullable_closed_rows x k _ _ (Nat.le_refl _)

theorem nullable_bound_source (x : List Char) (k : Nat) :
    evV (CapturedOriginNormalization.source entries (plans nullableGate)) x .callByValuePar
      (tblV (CapturedOriginNormalization.source entries (plans nullableGate)) x .callByValuePar k) []
      (GuardedPairSyntax.render entries true (.call 3 [])) x.length=none := by
  rw [CapturedOriginNormalization.physical entries (plans nullableGate) nullable_plan_checked x k [] (.call 3 []) x.length (Nat.le_refl _)]
  exact nullable_closed_source x k

theorem nullable_bound_target (x : List Char) (k : Nat) :
    evV (CapturedOriginCompiler.target entries (plans nullableGate)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans nullableGate)) x .callByValueSeq k) []
      (GuardedPairSyntax.render entries false (.call 3 [])) x.length=none :=
  (GuardedPairCorrespondence.undefined_iff entries (generatedQueries entries (plans nullableGate) true)
    (Bool.and_eq_true_iff.mp nullable_plan_checked).2 (.call 3 []) x).mp (nullable_closed_source x) k

theorem nullable_argument_checked : CapturedOriginCompiler.check (original gate tail) nullableSelection entries (plans gate)=true := by decide +kernel

theorem nullable_argument_root : CapturedOriginCompiler.rootCheck nullableSelection entries nullableRoot (templateRoot nullableArgs)=true := by decide +kernel

theorem nullable_argument_source (x : List Char) (k : Nat) :
    evV (original gate tail) x .callByValuePar (tblV (original gate tail) x .callByValuePar k) [] nullableRoot x.length=none := by
  have hs : evV (original gate tail) x .callByValuePar (tblV (original gate tail) x .callByValuePar k) [] (.star .eps) x.length=none := by
    rw [evV_star]; exact evStar_stuck (j := x.length) rfl (by omega)
  have ha : evV (original gate tail) x .callByValuePar (tblV (original gate tail) x .callByValuePar k) []
      (FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck) x.length=none := evV_seq_none hs
  have hr : ruleAtM (original gate tail).rules 3=some ⟨2,.seq (.andP (compile left.alphabet right.alphabet false gate))
      (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) tail)⟩ := rfl
  change evV _ _ _ _ [] (.call 3 [FrontierArgumentNormalization.argument IndependentFrontierExamples.stuck,
    FrontierArgumentNormalization.argument right]) _=none
  rw [evV_call_par hr rfl (by decide),evPar_cons_none ha]

theorem nullable_argument_target (x : List Char) (k : Nat) :
    evV (CapturedOriginCompiler.target entries (plans gate)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans gate)) x .callByValueSeq k) []
      (GuardedPairSyntax.render entries false (templateRoot nullableArgs)) x.length=none :=
  (CapturedOriginCompiler.undefined_iff (original gate tail) nullableSelection entries (plans gate) nullable_argument_checked nullableRoot
    (templateRoot nullableArgs) nullable_argument_root x).mp (nullable_argument_source x) k

theorem skipping_argument_preflight_accepts : evV (CapturedOriginCompiler.target entries (plans gate)) (sample 1 'b') .callByValueSeq
    (tblV (CapturedOriginCompiler.target entries (plans gate)) (sample 1 'b') .callByValueSeq 20) []
    (GuardedPairSyntax.render entries false (.call 3 [])) (sample 1 'b').length=some (some 0) := by decide +kernel

end Shallot.MacroPeg.CBV.CapturedOriginExamples
