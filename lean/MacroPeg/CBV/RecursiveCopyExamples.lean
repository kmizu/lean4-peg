import MacroPeg.CBV.RecursiveCopyCompiler
import MacroPeg.CBV.DelimitedCopyExamples

namespace Shallot.MacroPeg.CBV.RecursiveCopyExamples
open RecursiveCopySyntax
abbrev Term := RecursiveCopySyntax.Expr
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def d := '#'
def alphabet := ['a','b','c']
def peek (e : Term) : Term := .notP (.notP e)
def gap : Term := .star (.seq (.notP (.chr d)) .any)
def skipBlock : Term := .seq gap (.seq (.lit [d]) (.seq gap (.seq (.lit [d]) (.seq gap (.seq (.lit [d]) .eps)))))

def balanced : Term := .alt (.seq (.chr 'a') (.seq (.user 0) (.chr 'c'))) (.chr 'b')
def prefixParser : Term := .seq (.star (.chr 'a')) (.chr 'b')
def copyBody : Term := .copy (.user 3) (.user 4)
/-- Each actual validates the next complete block recursively, or EOF.
The query restores the original position before the actual captures data. -/
def queryNext : Term := peek (.seq skipBlock (.alt (.notP .any) (.user 2)))
def shortActual : Term := .seq queryNext (.user 1)
def longActual : Term := .seq queryNext (.user 0)
def clients : List Term := [balanced,prefixParser,copyBody,shortActual,longActual]
def entry : Term := .seq (.star (.user 2)) (.notP .any)
abbrev original := source clients d
abbrev generated := target clients d
def originalRoot := render clients.length true entry
def generatedRoot := render clients.length false entry
abbrev short := DelimitedCopyExamples.short
abbrev long := DelimitedCopyExamples.long
abbrev block := DelimitedCopyExamples.block

def streams : List (List Char) := [block 1,block 2++block 1,block 1++block 3++block 2]

theorem checked : RecursiveCopyCompiler.check original originalRoot clients alphabet d entry=true := by decide +kernel

theorem grammar_layout : original.rules.map MRule.arity=[0,0,0,0,0,2] ∧
    generated.rules.map MRule.arity=[0,0,0,0,0,1,1] := by decide +kernel

theorem actual_callback_tuples :
    evParArgs original (block 2++block 1) .callByValuePar (tblV original (block 2++block 1) .callByValuePar 20) []
      [.call 3 [],.call 4 []] (block 2++block 1).length=some (some [short 2,long 2]) := by decide +kernel

theorem source_streams : ∀ x∈streams,
    evV original x .callByValuePar (tblV original x .callByValuePar 20) [] originalRoot x.length=some (some 0) := by decide +kernel

theorem target_streams : ∀ x∈streams,
    evV generated x .callByValueSeq (tblV generated x .callByValueSeq 20) [] generatedRoot x.length=some (some 0) := by decide +kernel

/-- The first client consumes one block after recursively validating later
ones. The lookahead callback does not change its actual returned suffix. -/
theorem callback_preserves_actual_residual :
    evV original (block 2++block 1) .callByValuePar (tblV original (block 2++block 1) .callByValuePar 20) []
      (.call 2 []) (block 2++block 1).length=some (some (block 1).length) ∧
    evV generated (block 2++block 1) .callByValueSeq (tblV generated (block 2++block 1) .callByValueSeq 20) []
      (.call 2 []) (block 2++block 1).length=some (some (block 1).length) := by decide +kernel

def badNext := block 1++DelimitedCopyExamples.wrongShort

theorem later_bad_block_changes_first_actual :
    evV original badNext .callByValuePar (tblV original badNext .callByValuePar 20) [] (.call 3 []) badNext.length=some none ∧
    evV generated badNext .callByValueSeq (tblV generated badNext .callByValueSeq 20) [] (.call 3 []) badNext.length=some none := by decide +kernel

/-- A copy call can occur directly inside a lookahead in another actual,
without first being named as a nullary client. -/
def nestedActual : Term := .seq (peek (.copy (.user 1) (.user 0))) (.user 1)
def nestedEntry : Term := .seq (.copy nestedActual (.user 4)) (.notP .any)

theorem nested_checked : RecursiveCopyCompiler.check original (render clients.length true nestedEntry) clients alphabet d nestedEntry=true := by decide +kernel

theorem direct_copy_inside_actual :
    evV original (block 4) .callByValuePar (tblV original (block 4) .callByValuePar 20) [] (render clients.length true nestedEntry) (block 4).length=some (some 0) ∧
    evV generated (block 4) .callByValueSeq (tblV generated (block 4) .callByValueSeq 20) [] (render clients.length false nestedEntry) (block 4).length=some (some 0) := by decide +kernel

theorem actual_client_body_is_transformed :
    MExp.beqE (render clients.length true copyBody) (render clients.length false copyBody)=false := by decide +kernel

theorem independent_library_check_rejects_callbacks :
    (sourceBodies clients).all (DelimitedCopySyntax.lexicalCheck clients.length)=false := by decide +kernel

theorem same_physical_clock (x : List Char) (k : Nat) :
    evV original x .callByValuePar (tblV original x .callByValuePar k) [] originalRoot x.length=
      evV generated x .callByValueSeq (tblV generated x .callByValueSeq k) [] generatedRoot x.length :=
  RecursiveCopyCompiler.physical original originalRoot clients alphabet d entry checked x k

theorem original_language : (fun x => SObs original .callByValuePar originalRoot x (some []))=
    (fun x => SObs generated .callByValueSeq generatedRoot x (some [])) :=
  RecursiveCopyCompiler.language_translation original originalRoot clients alphabet d entry checked

/-- A genuine same-position callback cycle: client0 invokes copy(user1,eps),
whose first actual looks ahead to client0 again. No stopping oracle is input. -/
def loop0 : Term := .copy (.user 1) .eps
def loop1 : Term := .seq (peek (.user 0)) .eps
def loopClients : List Term := [loop0,loop1]
def loopEntry : Term := .user 0
abbrev loopSource := source loopClients d
abbrev loopTarget := target loopClients d

theorem loop_checked : RecursiveCopyCompiler.check loopSource (render loopClients.length true loopEntry) loopClients alphabet d loopEntry=true := by decide +kernel

theorem callback_loop_rows (x : List Char) (p : Nat) (hp : p≤x.length) : ∀ k,
    valAt (tblV loopSource x .callByValuePar k 0 []) p=none ∧ valAt (tblV loopSource x .callByValuePar k 1 []) p=none
  | 0 => ⟨rfl,rfl⟩
  | k+1 => by
    obtain ⟨h0,h1⟩ := callback_loop_rows x p hp k
    have hr0 := source_user loopClients d 0 loop0 rfl
    have hr1 := source_user loopClients d 1 loop1 rfl
    have hc0 : evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 0 []) p=none := by
      rw [evV_call_par hr0 rfl (by decide)]
      exact h0
    have hc1 : evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 1 []) p=none := by
      rw [evV_call_par hr1 rfl (by decide)]
      exact h1
    constructor
    · rw [valAt_tblV_succ hr0 [] hp]
      change evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 2 [.call 1 [],.eps]) p=none
      have hf : ruleAtM loopSource.rules 2=some ⟨2,DelimiterTemplate.compile d (DelimitedCopyTemplates.sourceBlockParts d)⟩ := source_copy loopClients d
      rw [evV_call_par hf (args := [.call 1 [],.eps]) rfl (by decide),evPar_cons_none hc1]
    · rw [valAt_tblV_succ hr1 [] hp]
      change evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.seq (.andP (.call 0 [])) .eps) p=none
      have hh : evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.andP (.call 0 [])) p=none := by rw [CallLookahead.evV_peek,hc0]; rfl
      exact evV_seq_none hh

theorem callback_loop_source (x : List Char) (k : Nat) :
    evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (render loopClients.length true loopEntry) x.length=none := by
  rw [show render loopClients.length true loopEntry=.call 0 [] from rfl,evV_call_par (source_user loopClients d 0 loop0 rfl) rfl (by decide)]
  exact (callback_loop_rows x x.length (Nat.le_refl _) k).1

theorem callback_loop_target (x : List Char) (k : Nat) :
    evV loopTarget x .callByValueSeq (tblV loopTarget x .callByValueSeq k) [] (render loopClients.length false loopEntry) x.length=none :=
  (RecursiveCopyCompiler.physical loopSource (render loopClients.length true loopEntry) loopClients alphabet d loopEntry loop_checked x k).symm.trans (callback_loop_source x k)

def laterLoop : Term := .copy .eps (.user 1)
theorem later_loop_checked : RecursiveCopyCompiler.check loopSource (render loopClients.length true laterLoop) loopClients alphabet d laterLoop=true := by decide +kernel

theorem later_loop_source (x : List Char) (k : Nat) :
    evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (render loopClients.length true laterLoop) x.length=none := by
  have hh : evV loopSource x .callByValuePar (tblV loopSource x .callByValuePar k) [] (.call 1 []) x.length=none := by
    rw [evV_call_par (source_user loopClients d 1 loop1 rfl) rfl (by decide)]
    exact (callback_loop_rows x x.length (Nat.le_refl _) k).2
  have hf : ruleAtM loopSource.rules 2=some ⟨2,DelimiterTemplate.compile d (DelimitedCopyTemplates.sourceBlockParts d)⟩ := source_copy loopClients d
  rw [show render loopClients.length true laterLoop=.call 2 [.eps,.call 1 []] from rfl,
    evV_call_par hf (args := [.eps,.call 1 []]) rfl (by decide),evPar_cons_ok rfl,evPar_cons_none hh]

theorem later_loop_target (x : List Char) (k : Nat) :
    evV loopTarget x .callByValueSeq (tblV loopTarget x .callByValueSeq k) [] (render loopClients.length false laterLoop) x.length=none :=
  (RecursiveCopyCompiler.physical loopSource (render loopClients.length true laterLoop) loopClients alphabet d laterLoop later_loop_checked x k).symm.trans (later_loop_source x k)

def noPreflight : MExp := .seq (.andP (.call 2 [.eps])) (.call 3 [.call 1 []])
theorem preflight_remains_necessary :
    evV loopTarget ['a'] .callByValueSeq (tblV loopTarget ['a'] .callByValueSeq 4) [] noPreflight 1=some none := by decide +kernel

/-- Positive output still cannot contain the separator merely because
calls and recursive queries are now allowed inside actuals. -/
def badNested : Term := .copy (.copy (.lit ['a']) (.lit ['a'])) (.lit ['a'])
theorem delimiter_producing_actual_rejected : termCheck clients alphabet d badNested=false := by decide +kernel

def wrongClients : List Term := [balanced,prefixParser,.eps,shortActual,longActual]
theorem changed_callback_declaration_rejected :
    RecursiveCopyCompiler.check (source wrongClients d) originalRoot clients alphabet d entry=false := by decide +kernel

theorem out_of_scope_client_rejected : RecursiveCopySyntax.check clients alphabet d (.user 99)=false := by decide +kernel

end Shallot.MacroPeg.CBV.RecursiveCopyExamples
