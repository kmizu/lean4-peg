import MacroPeg.CBV.CapturedOriginExamples
import MacroPeg.CBV.StatefulScannerBridge

namespace Shallot.MacroPeg.CBV.NestedCapturedOriginExamples
open IndependentFrontierExamples (helpers left right ds root selection entries templateRoot sample tail recursiveTail recursiveEntries recursiveNested)
open CapturedOriginQuery (Plan compile frontier choose)
open CapturedOriginNormalization (generatedQueries)
open CapturedOriginExamples (plans original)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def probe : Plan := .follow false (.after true .eps)
def bothNonempty : Plan := .notP probe

theorem checked : CapturedOriginCompiler.check (original bothNonempty tail) selection entries (plans bothNonempty)=true := by decide +kernel

theorem root_checked : CapturedOriginCompiler.rootCheck selection entries root (templateRoot ds)=true := by decide +kernel

theorem source_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    evV (original bothNonempty tail) (sample n c) .callByValuePar (tblV (original bothNonempty tail) (sample n c) .callByValuePar 20) []
      root (sample n c).length=some (some 0) := by decide +kernel

theorem target_both_orders : ∀ n∈[1,2,4], ∀ c∈['b','c'],
    evV (CapturedOriginCompiler.target entries (plans bothNonempty)) (sample n c) .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans bothNonempty)) (sample n c) .callByValueSeq 20) []
      (GuardedPairSyntax.render entries false (templateRoot ds)) (sample n c).length=some (some 0) := by decide +kernel

theorem same_origin_is_essential :
    evV (original bothNonempty tail) (sample 1 'b') .callByValuePar (tblV (original bothNonempty tail) (sample 1 'b') .callByValuePar 20)
      [['a','b'],['a']] (compile left.alphabet right.alphabet false bothNonempty) (sample 1 'b').length=some (some (sample 1 'b').length) ∧
    evV (original bothNonempty tail) (sample 1 'b') .callByValuePar (tblV (original bothNonempty tail) (sample 1 'b') .callByValuePar 20)
      [['a'],['b']] (compile left.alphabet right.alphabet false bothNonempty) (sample 1 'b').length=some none := by decide +kernel

theorem recursive_checked : CapturedOriginCompiler.check (original bothNonempty (recursiveTail root)) selection recursiveEntries (plans bothNonempty)=true := by decide +kernel

theorem recursive_root_checked : CapturedOriginCompiler.rootCheck selection recursiveEntries root (templateRoot ds)=true := by decide +kernel

theorem recursive_source : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (original bothNonempty (recursiveTail root)) x .callByValuePar (tblV (original bothNonempty (recursiveTail root)) x .callByValuePar 20)
      [] root x.length=some (some 0) := by decide +kernel

theorem recursive_target : ∀ pair∈[((1,'b'),(2,'c')),((2,'c'),(1,'b'))],
    let x := recursiveNested pair.1.1 pair.1.2 pair.2.1 pair.2.2
    evV (CapturedOriginCompiler.target recursiveEntries (plans bothNonempty)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target recursiveEntries (plans bothNonempty)) x .callByValueSeq 20) []
      (GuardedPairSyntax.render recursiveEntries false (templateRoot ds)) x.length=some (some 0) := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs (original bothNonempty tail) .callByValuePar root x rest ↔
      SObs (CapturedOriginCompiler.target entries (plans bothNonempty)) .callByValueSeq
        (GuardedPairSyntax.render entries false (templateRoot ds)) x rest :=
  CapturedOriginCompiler.observations_iff (original bothNonempty tail) selection entries (plans bothNonempty) checked root
    (templateRoot ds) root_checked x rest

def scanArgs : List FrontierArgumentNormalization.Argument :=
  [⟨left.alphabet,helpers,NestedScannerArguments.scan left.alphabet⟩,⟨right.alphabet,helpers,NestedScannerArguments.scan right.alphabet⟩]
def scanSelection : FrontierArgumentCompiler.Selection := [none,none,none,some scanArgs]
def scanRoot := MExp.call 3 (FrontierArgumentNormalization.arguments scanArgs)
def leftOnly := ['b','b','!','b','b',':']
def rightOnly := ['c','c','!',':','c','c']
def emptyPair := ['!',':']

theorem empty_cases_checked : CapturedOriginCompiler.check (original probe tail) scanSelection entries (plans probe)=true := by decide +kernel

theorem empty_root_checked : CapturedOriginCompiler.rootCheck scanSelection entries scanRoot (templateRoot scanArgs)=true := by decide +kernel

theorem empty_cases_source : ∀ x∈[leftOnly,rightOnly,emptyPair],
    evV (original probe tail) x .callByValuePar (tblV (original probe tail) x .callByValuePar 20) [] scanRoot x.length=some (some 0) := by decide +kernel

theorem empty_cases_target : ∀ x∈[leftOnly,rightOnly,emptyPair],
    evV (CapturedOriginCompiler.target entries (plans probe)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans probe)) x .callByValueSeq 20) []
      (GuardedPairSyntax.render entries false (templateRoot scanArgs)) x.length=some (some 0) := by decide +kernel

def nestedProbe : Plan := .follow false (.follow true (.notP (.after true .eps)))

theorem nested_empty_branch_checked : CapturedOriginCompiler.check (original nestedProbe tail) scanSelection entries (plans nestedProbe)=true := by decide +kernel

theorem nested_empty_branch_target : evV (CapturedOriginCompiler.target entries (plans nestedProbe)) rightOnly .callByValueSeq
    (tblV (CapturedOriginCompiler.target entries (plans nestedProbe)) rightOnly .callByValueSeq 20) []
    (GuardedPairSyntax.render entries false (templateRoot scanArgs)) rightOnly.length=some (some 0) := by decide +kernel

theorem nested_empty_branch_source : evV (original nestedProbe tail) rightOnly .callByValuePar
    (tblV (original nestedProbe tail) rightOnly .callByValuePar 20) [] scanRoot rightOnly.length=some (some 0) :=
  (CapturedOriginCompiler.bounds (original nestedProbe tail) scanSelection entries (plans nestedProbe) nested_empty_branch_checked
    scanRoot (templateRoot scanArgs) empty_root_checked rightOnly 20).2.eq_of_some nested_empty_branch_target

/-- A symbolic four-case result for every input, table and environment.
It is not a finite enumeration of possible retained words. -/
theorem canonical_probe_eval (es : List MixedScannerPairFusion.Entry) (g : MGrammar) (x : List Char) (T : ClockFreezing.Table)
    (E : List (List Char)) (A B : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T E (GuardedPairSyntax.render es true (compile A B true probe)) p=
      if ScannerFrontierValues.starts A (sfx x p) && ScannerFrontierValues.starts B (sfx x p)
      then some none else some (some p) := by
  change evV g x .callByValuePar T E (.andP (GuardedPairSyntax.render es true (choose A B (fun fa fb =>
    if fa then .seq (NestedScannerArguments.scan A) (frontier fa fb (.after true .eps)) else compile A B true (.after true .eps))))) p=_
  rw [CallLookahead.evV_peek,CapturedOriginQuery.choose_eval es g x T E A B _ p hp]
  cases ha : ScannerFrontierValues.starts A (sfx x p) <;> cases hb : ScannerFrontierValues.starts B (sfx x p)
  all_goals simp only [ha,hb,Bool.false_and,Bool.true_and,if_false,if_true,Bool.false_eq_true,frontier,compile,GuardedPairSyntax.render]
  all_goals try simp only [CapturedOriginQuery.render_scan]
  all_goals first
    | rw [evV_seq_ok (NestedScannerArguments.scan_eval g x .callByValuePar T E A p hp)]; rfl
    | change CallLookahead.peek p (evV g x .callByValuePar T E (.andP (.seq
        (GuardedPairSyntax.render es true (NestedScannerArguments.scan B)) .eps)) p)=some (some p)
      rw [CapturedOriginQuery.render_scan,CallLookahead.evV_peek,evV_seq_ok (NestedScannerArguments.scan_eval g x .callByValuePar T E B p hp)]
      rfl

def nullable : Plan := .star probe

theorem nullable_checked : CapturedOriginCompiler.check (original nullable tail) scanSelection entries (plans nullable)=true := by decide +kernel

theorem nullable_root_checked : CapturedOriginCompiler.rootCheck scanSelection entries scanRoot (templateRoot scanArgs)=true := by decide +kernel

theorem star_fails_to_progress : evV (CapturedOriginCompiler.target entries (plans nullable)) leftOnly .callByValueSeq
    (tblV (CapturedOriginCompiler.target entries (plans nullable)) leftOnly .callByValueSeq 20) []
    (GuardedPairSyntax.render entries false (templateRoot scanArgs)) leftOnly.length=none := by decide +kernel

theorem star_stops_when_both_nonempty : evV (CapturedOriginCompiler.target entries (plans nullable)) (sample 1 'b') .callByValueSeq
    (tblV (CapturedOriginCompiler.target entries (plans nullable)) (sample 1 'b') .callByValueSeq 20) []
    (GuardedPairSyntax.render entries false (templateRoot scanArgs)) (sample 1 'b').length=some (some 0) := by decide +kernel

theorem scan_preflight (es : List MixedScannerPairFusion.Entry) (g : MGrammar) (x : List Char) (T : ClockFreezing.Table)
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar T [] (GuardedPairSyntax.render es true (FrontierArgumentNormalization.preflight scanArgs)) p=some (some p) := by
  change evV g x .callByValuePar T [] (FrontierArgumentNormalization.preflight scanArgs) p=some (some p)
  rw [FrontierArgumentNormalization.preflight_eval]
  change FrontierArgumentNormalization.gate p (evParArgs g x .callByValuePar T []
    [.seq (NestedScannerArguments.scan left.alphabet) (.notP (NestedScannerArguments.choice left.alphabet)),
     .seq (NestedScannerArguments.scan right.alphabet) (.notP (NestedScannerArguments.choice right.alphabet))] p)=some (some p)
  rw [evPar_cons_ok (ScannerFrontierValues.scanner_argument g x .callByValuePar T [] left.alphabet p hp),
    evPar_cons_ok (ScannerFrontierValues.scanner_argument g x .callByValuePar T [] right.alphabet p hp),evPar_nil]
  rfl

theorem nullable_closed_rows (x : List Char) (k : Nat) (W : List (List Char)) (p : Nat) (hp : p≤x.length)
    (hbits : (ScannerFrontierValues.starts left.alphabet (sfx x p) && ScannerFrontierValues.starts right.alphabet (sfx x p))=false) :
    valAt (tblV (CapturedOriginNormalization.prepared entries (plans nullable)) x .callByValuePar k 3 W) p=none := by
  let g := CapturedOriginNormalization.prepared entries (plans nullable)
  have hr : ruleAtM g.rules 3=some ⟨2,.seq (.andP (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true nullable)))
      (.seq (ScannedPairFusion.maxScanner left.alphabet right.alphabet) tail)⟩ := rfl
  cases k with
  | zero => rfl
  | succ k =>
    rw [valAt_tblV_succ hr W hp]
    have hprobe := canonical_probe_eval entries g x (tblV g x .callByValuePar k) W left.alphabet right.alphabet p hp
    rw [hbits] at hprobe
    have hq : evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true nullable)) p=none := by
      change evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (.star (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true probe))) p=none
      rw [evV_star]; exact evStar_stuck hprobe (by omega)
    have hpref : evV g x .callByValuePar (tblV g x .callByValuePar k) W
        (.andP (GuardedPairSyntax.render entries true (compile left.alphabet right.alphabet true nullable))) p=none := by
      rw [CallLookahead.evV_peek,hq]; rfl
    exact evV_seq_none hpref

/-- Every input with at least one empty capture has a nullable nested
replay test. The complete original program remains undefined at every clock. -/
theorem nullable_source_all_clocks (x : List Char) (k : Nat)
    (hbits : (ScannerFrontierValues.starts left.alphabet x && ScannerFrontierValues.starts right.alphabet x)=false) :
    evV (original nullable tail) x .callByValuePar (tblV (original nullable tail) x .callByValuePar k) [] scanRoot x.length=none := by
  rw [CapturedOriginCompiler.source_phase (original nullable tail) scanSelection entries (plans nullable) nullable_checked
    scanRoot (templateRoot scanArgs) nullable_root_checked x k]
  change evV (CapturedOriginNormalization.prepared entries (plans nullable)) x .callByValuePar
    (tblV (CapturedOriginNormalization.prepared entries (plans nullable)) x .callByValuePar k) []
    (.seq (GuardedPairSyntax.render entries true (FrontierArgumentNormalization.preflight scanArgs))
      (GuardedPairSyntax.render entries true (.call 3 []))) x.length=none
  rw [evV_seq_ok (scan_preflight entries _ x _ x.length (Nat.le_refl _))]
  rw [GuardedPairSimulation.source_call entries _ x _ [] 3 _
    (show entries[3]?=some ⟨some (left.alphabet,right.alphabet),tail⟩ from rfl) x.length (Nat.le_refl _)]
  exact nullable_closed_rows x k _ _ (Nat.le_refl _) (by simpa only [sfx,Nat.sub_self,List.drop_zero] using hbits)

theorem nullable_target_all_clocks (x : List Char) (k : Nat)
    (hbits : (ScannerFrontierValues.starts left.alphabet x && ScannerFrontierValues.starts right.alphabet x)=false) :
    evV (CapturedOriginCompiler.target entries (plans nullable)) x .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans nullable)) x .callByValueSeq k) []
      (GuardedPairSyntax.render entries false (templateRoot scanArgs)) x.length=none :=
  (CapturedOriginCompiler.undefined_iff (original nullable tail) scanSelection entries (plans nullable) nullable_checked scanRoot
    (templateRoot scanArgs) nullable_root_checked x).mp (fun k => nullable_source_all_clocks x k hbits) k

def divergingTail : Plan := .follow false (.after true (.star .eps))

theorem diverging_tail_checked : CapturedOriginCompiler.check (original divergingTail tail) scanSelection entries (plans divergingTail)=true := by decide +kernel

theorem nonempty_replay_fails_before_diverging_tail :
    evV (original divergingTail tail) (sample 1 'b') .callByValuePar
      (tblV (original divergingTail tail) (sample 1 'b') .callByValuePar 20) [] scanRoot (sample 1 'b').length=some none ∧
    evV (CapturedOriginCompiler.target entries (plans divergingTail)) (sample 1 'b') .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans divergingTail)) (sample 1 'b') .callByValueSeq 20) []
      (GuardedPairSyntax.render entries false (templateRoot scanArgs)) (sample 1 'b').length=some none := by decide +kernel

theorem empty_replay_enters_diverging_tail :
    evV (original divergingTail tail) leftOnly .callByValuePar (tblV (original divergingTail tail) leftOnly .callByValuePar 20) [] scanRoot leftOnly.length=none ∧
    evV (CapturedOriginCompiler.target entries (plans divergingTail)) leftOnly .callByValueSeq
      (tblV (CapturedOriginCompiler.target entries (plans divergingTail)) leftOnly .callByValueSeq 20) []
      (GuardedPairSyntax.render entries false (templateRoot scanArgs)) leftOnly.length=none := by decide +kernel

/-- A state-changing scanner can stop before another copy of the same
nonempty word. The stateless frontier specialization must not be generalized. -/
theorem stateful_frontier_can_replay :
    StatefulScanner.run StatefulScannerBridge.changedState 0 ['a','b','a','b']=(1,['a','b']) ∧
    Shallot.stripPrefix? ['a','b'] (StatefulScanner.run StatefulScannerBridge.changedState 0 ['a','b','a','b']).2=some [] := by decide +kernel

end Shallot.MacroPeg.CBV.NestedCapturedOriginExamples
