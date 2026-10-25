import MacroPeg.CBV.RecursivePatternCompiler
import MacroPeg.CBV.DelimitedPatternExamples

namespace Shallot.MacroPeg.CBV.RecursivePatternExamples
open RecursivePatternSyntax
abbrev Term := RecursivePatternSyntax.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def arity : Nat := 4
def d : Char := '#'
def alphabet : List Char := ['a','b','c']
def pattern : List Nat := [0,2,1,0,3,2,1]
def balanced : Term := .alt (.seq (.chr 'a') (.seq (.user 0) (.chr 'c'))) (.chr 'b')
def prefixParser : Term := .seq (.star (.chr 'a')) (.chr 'b')
def peek (e : Term) : Term := .notP (.notP e)
def gap : Term := .star (.seq (.notP (.chr d)) .any)
def skipSegments : Nat → Term
  | 0 => .eps
  | n+1 => .seq gap (.seq (.lit [d]) (skipSegments n))
def queryNext : Term := peek (.seq (skipSegments pattern.length) (.alt (.notP .any) (.user 2)))
def actuals : List Term := [.user 3,.user 4,.user 5,.user 6]
def copyBody : Term := .copy actuals
def longActual : Term := .seq queryNext (.user 0)
def shortActual : Term := .seq queryNext (.user 1)
def starActual : Term := .seq queryNext (.star (.chr 'a'))
def emptyActual : Term := .seq queryNext .eps
def clients : List Term := [balanced,prefixParser,copyBody,longActual,shortActual,starActual,emptyActual]
def entry : Term := .seq (.star (.user 2)) (.notP .any)
def original := source clients arity d pattern
def generated := target clients arity d pattern
def originalRoot := render clients.length true entry
def generatedRoot := render clients.length false entry
abbrev block := DelimitedPatternExamples.block
abbrev words := DelimitedPatternExamples.words

theorem checked : RecursivePatternCompiler.check original originalRoot clients arity alphabet d pattern entry=true := by decide +kernel
theorem source_arities : original.rules.map MRule.arity=[0,0,0,0,0,0,0,4] := by decide +kernel
theorem target_arities : generated.rules.map MRule.arity=[0,0,0,0,0,0,0,1,1,1,1] := by decide +kernel

def streams := [block 0,block 2++block 1,block 1++block 3++block 2]
theorem source_streams : streams.all (fun x =>
    evV original x .callByValuePar (tblV original x .callByValuePar 24) [] originalRoot x.length==some (some 0))=true := by decide +kernel
theorem target_streams : streams.all (fun x =>
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq 24) [] generatedRoot x.length==some (some 0))=true := by decide +kernel

theorem callback_actual_words :
    evParArgs original (block 2++block 1) .callByValuePar (tblV original (block 2++block 1) .callByValuePar 24) []
      (renderArgs clients.length true actuals) (block 2++block 1).length=some (some (words 2)) := by decide +kernel

theorem callback_residual :
    evV original (block 2++block 1) .callByValuePar (tblV original (block 2++block 1) .callByValuePar 24) [] (.call 2 []) (block 2++block 1).length=some (some (block 1).length) ∧
    evV generated (block 2++block 1) .callByValueSeq (tblV generated (block 2++block 1) .callByValueSeq 24) [] (.call 2 []) (block 2++block 1).length=some (some (block 1).length) := by decide +kernel

def badNext := block 1++DelimitedPatternExamples.wrongBlock
theorem later_block_controls_current_actual :
    evV original badNext .callByValuePar (tblV original badNext .callByValuePar 24) [] (.call 3 []) badNext.length=some none ∧
    evV generated badNext .callByValueSeq (tblV generated badNext .callByValueSeq 24) [] (.call 3 []) badNext.length=some none := by decide +kernel

def nestedActual : Term := .seq (peek (.copy [.user 0,.user 1,.star (.chr 'a'),.eps])) (.user 0)
def nestedEntry : Term := .seq (.copy [nestedActual,.user 4,.user 5,.user 6]) (.notP .any)
theorem nested_checked : RecursivePatternCompiler.check original (render clients.length true nestedEntry) clients arity alphabet d pattern nestedEntry=true := by decide +kernel
theorem direct_copy_inside_actual :
    evV original (block 4) .callByValuePar (tblV original (block 4) .callByValuePar 24) [] (render clients.length true nestedEntry) (block 4).length=some (some 0) ∧
    evV generated (block 4) .callByValueSeq (tblV generated (block 4) .callByValueSeq 24) [] (render clients.length false nestedEntry) (block 4).length=some (some 0) := by decide +kernel

theorem client_body_is_transformed : MExp.beqE (render clients.length true copyBody) (render clients.length false copyBody)=false := by decide +kernel
theorem independent_library_rejects_callbacks :
    (sourceBodies clients).all (DelimitedCopySyntax.lexicalCheck clients.length)=false := by decide +kernel

def loop0 : Term := .copy [.user 1,.eps,.eps,.eps]
def loop1 : Term := .seq (peek (.user 0)) .eps
def loopClients : List Term := [loop0,loop1]
def loopEntry : Term := .user 0

theorem loop_checked : RecursivePatternSyntax.check loopClients arity alphabet d pattern loopEntry=true := by decide +kernel

theorem loop_rows (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV (source loopClients arity d pattern) x .callByValuePar k 0 []) p=none ∧
      valAt (tblV (source loopClients arity d pattern) x .callByValuePar k 1 []) p=none := by
  intro k
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    have h0 : evV (source loopClients arity d pattern) x .callByValuePar (tblV (source loopClients arity d pattern) x .callByValuePar k) [] (.call 0 []) p=none := by
      rw [evV_call_par (source_user loopClients arity d pattern 0 loop0 rfl) rfl (by decide),evPar_nil]
      exact ih.1
    have h1 : evV (source loopClients arity d pattern) x .callByValuePar (tblV (source loopClients arity d pattern) x .callByValuePar k) [] (.call 1 []) p=none := by
      rw [evV_call_par (source_user loopClients arity d pattern 1 loop1 rfl) rfl (by decide),evPar_nil]
      exact ih.2
    constructor
    · rw [valAt_tblV_succ (source_user loopClients arity d pattern 0 loop0 rfl) [] hp]
      change evV _ _ _ _ [] (.call 2 [.call 1 [],.eps,.eps,.eps]) p=none
      have hr : ruleAtM (source loopClients arity d pattern).rules 2=some ⟨4,DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d pattern)⟩ := rfl
      rw [evV_call_par hr rfl (by decide),evPar_cons_none h1]
    · rw [valAt_tblV_succ (source_user loopClients arity d pattern 1 loop1 rfl) [] hp]
      change evV _ _ _ _ [] (.seq (.andP (.call 0 [])) .eps) p=none
      rw [evV_seq_none (by rw [CallLookahead.evV_peek,h0]; rfl)]

theorem callback_loop_source (x : List Char) (k : Nat) :
    evV (source loopClients arity d pattern) x .callByValuePar (tblV (source loopClients arity d pattern) x .callByValuePar k) [] (render loopClients.length true loopEntry) x.length=none := by
  rw [show render loopClients.length true loopEntry=.call 0 [] from rfl,
    evV_call_par (source_user loopClients arity d pattern 0 loop0 rfl) rfl (by decide),evPar_nil]
  exact (loop_rows x x.length (Nat.le_refl _) k).1

theorem callback_loop_target (x : List Char) (k : Nat) :
    evV (target loopClients arity d pattern) x .callByValueSeq (tblV (target loopClients arity d pattern) x .callByValueSeq k) [] (render loopClients.length false loopEntry) x.length=none := by
  exact (RecursivePatternCorrespondence.physical loopClients arity alphabet d pattern loopEntry loop_checked x k x.length (Nat.le_refl _)).symm.trans (callback_loop_source x k)

def laterLoop : Term := .copy [.eps,.eps,.eps,.user 1]
theorem later_loop_checked : RecursivePatternSyntax.check loopClients arity alphabet d pattern laterLoop=true := by decide +kernel
theorem later_loop_source (x : List Char) (k : Nat) :
    evV (source loopClients arity d pattern) x .callByValuePar (tblV (source loopClients arity d pattern) x .callByValuePar k) [] (render loopClients.length true laterLoop) x.length=none := by
  have hh : evV (source loopClients arity d pattern) x .callByValuePar (tblV (source loopClients arity d pattern) x .callByValuePar k) [] (.call 1 []) x.length=none := by
    rw [evV_call_par (source_user loopClients arity d pattern 1 loop1 rfl) rfl (by decide),evPar_nil]
    exact (loop_rows x x.length (Nat.le_refl _) k).2
  change evV _ _ _ _ [] (.call 2 [.eps,.eps,.eps,.call 1 []]) x.length=none
  have hr : ruleAtM (source loopClients arity d pattern).rules 2=some ⟨4,DelimiterTemplate.compile d (DelimitedWordPattern.sourceParts d pattern)⟩ := rfl
  rw [evV_call_par hr rfl (by decide),evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_ok rfl,evPar_cons_none hh]

theorem later_loop_target (x : List Char) (k : Nat) :
    evV (target loopClients arity d pattern) x .callByValueSeq (tblV (target loopClients arity d pattern) x .callByValueSeq k) [] (render loopClients.length false laterLoop) x.length=none := by
  exact (RecursivePatternCorrespondence.physical loopClients arity alphabet d pattern laterLoop later_loop_checked x k x.length (Nat.le_refl _)).symm.trans (later_loop_source x k)

theorem preflight_is_required :
    evV (target loopClients arity d pattern) ['a'] .callByValueSeq (tblV (target loopClients arity d pattern) ['a'] .callByValueSeq 4) []
      (DelimitedPatternEvaluation.passes loopClients.length (renderArgs loopClients.length false [.eps,.eps,.eps,.user 1]) (List.range arity)) 1=some none := by decide +kernel

theorem wrong_arity_rejected : RecursivePatternSyntax.check clients arity alphabet d pattern (.copy [.user 0])=false := by decide +kernel
theorem out_of_scope_rejected : RecursivePatternSyntax.check clients arity alphabet d pattern (.user 99)=false := by decide +kernel
theorem separator_capture_rejected : RecursivePatternSyntax.check clients arity alphabet d pattern (.copy [.lit [d],.eps,.eps,.eps])=false := by decide +kernel

theorem wrong_source_rejected :
    RecursivePatternCompiler.check generated originalRoot clients arity alphabet d pattern entry=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RecursivePatternCompiler.physical original originalRoot clients arity alphabet d pattern entry checked x k

end Shallot.MacroPeg.CBV.RecursivePatternExamples
