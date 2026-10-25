import MacroPeg.CBV.CheckedOriginCompiler

namespace Shallot.MacroPeg.CBV.CheckedOriginExamples
open ReplayControlFusion (Part Plan)
open CheckedOriginCompiler

/-- The real callee's ordinary row consumes its retained value. Its empty
clone succeeds at zero width on a/b, and recurses forever on other inputs. -/
def starts : MExp := .alt (.chr 'a') (.chr 'b')
def query : MExp := .alt (.andP starts) (.seq (.notP starts) (.call 1 [.lit []]))
def word (c : Char) : MExp := .seq (.chr c) (.star (.chr 'c'))
def parentTail : MExp := .seq (.chr '!')
  (.seq (.alt (.seq (.chr '@') (.call 0 [word 'a'])) .eps) (.param 0))
def parts : List Part := [⟨false,.call 1 [.lit []]⟩,⟨true,parentTail⟩,⟨true,.eps⟩]
def entries : List MixedForwardingCompiler.Entry :=
  [.origin (.alt (.guard (.leaf 0) (.leaf 1)) (.leaf 2)),
   .growth ⟨9,1,.chr 'X',query⟩]
def grammar := source parts entries

def specs : List MultiplyingPrefixCompiler.Spec :=
  [⟨1,0,.seq (.param 0) parentTail,.eps⟩,⟨9,1,.chr 'X',query⟩]

/-- The zero head is the real raw Spec call R(empty), followed by a tail
depending on the parent's retained word. There is no pre-unfolded header. -/
theorem actual_raw_specs : grammar=MultiplyingPrefixCompiler.source specs := by rfl

theorem checked : check parts entries=true := by decide +kernel

theorem original_header : ruleAtM grammar.rules 0=some ⟨1,
    .alt (.seq (.call 1 [.lit []]) (.seq (.param 0) parentTail)) (.seq (.param 0) .eps)⟩ := by rfl

theorem actual_callee : ruleAtM grammar.rules 1=some ⟨1,
    MultiplyingPrefixCompiler.sourceBody ⟨9,1,.chr 'X',query⟩⟩ := by rfl

/-- Ordinary row 1 is not zero width; only the actual empty-bound clone 3
can receive the certificate. This is not a global empty capture assumption. -/
theorem inferred_clones :
    ParReturnEffects.infer (EmptyArgumentSpecialization.target grammar)=([3],[]) := by decide +kernel

theorem rejected_ordinary_row :
    ParReturnEffects.check (EmptyArgumentSpecialization.target grammar) [1,3] []=false := by decide +kernel

theorem call_zero : ParReturnEffects.emptyEffect grammar (.call 1 [.lit []])=.zero := by decide +kernel

theorem old_syntactic_gate_rejects : EmptyArgumentSpecialization.zeroCheck (.call 1 [.lit []])=false := by rfl

def root : MExp := .seq (.call 0 [word 'b']) (.notP .any)

theorem target_size : (target parts entries).rules.length=9 := by decide +kernel

theorem source_capture_restore : evV grammar "bcc!@acc!accbcc".toList .callByValuePar
    (tblV grammar "bcc!@acc!accbcc".toList .callByValuePar 8) [] root 15=some (some 0) := by decide +kernel

theorem target_capture_restore : evV (target parts entries) "bcc!@acc!accbcc".toList .callByValueSeq
    (tblV (target parts entries) "bcc!@acc!accbcc".toList .callByValueSeq 8) [] (render parts entries root) 15=some (some 0) := by decide +kernel

theorem source_old_longer : evV grammar "bcccc!@a!abcccc".toList .callByValuePar
    (tblV grammar "bcccc!@a!abcccc".toList .callByValuePar 8) [] root 15=some (some 0) := by decide +kernel

theorem target_old_longer : evV (target parts entries) "bcccc!@a!abcccc".toList .callByValueSeq
    (tblV (target parts entries) "bcccc!@a!abcccc".toList .callByValueSeq 8) [] (render parts entries root) 15=some (some 0) := by decide +kernel

theorem short_restore_rejected : evV (target parts entries) "bcc!@acc!accbc".toList .callByValueSeq
    (tblV (target parts entries) "bcc!@acc!accbc".toList .callByValueSeq 8) [] (render parts entries root) 14=some none := by decide +kernel

theorem all_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs grammar .callByValuePar e x rest ↔ SObs (target parts entries) .callByValueSeq (render parts entries e) x rest :=
  observations_iff parts entries checked e he x rest

theorem all_undefined (e : MExp) (he : e.FirstOrder) (x : List Char) :
    (∀ k, evV grammar x .callByValuePar (tblV grammar x .callByValuePar k) [] e x.length=none) ↔
      (∀ k, evV (target parts entries) x .callByValueSeq (tblV (target parts entries) x .callByValueSeq k) []
        (render parts entries e) x.length=none) :=
  undefined_iff parts entries checked e he x

/-- Arity/missing-rule checks happen before nullable actual arguments. -/
theorem missing_dead : ParReturnEffects.analyze grammar [] [] (.call 9 [.star (.lit [])])=.dead := by decide +kernel

theorem arity_dead : ParReturnEffects.analyze grammar [] [] (.call 1 [.eps,.star (.lit [])])=.dead := by decide +kernel

theorem ordinary_row_consumes : valAt (tblV grammar ['a','b'] .callByValuePar 2 1 [['a']]) 2=some (some 1) := by decide +kernel

theorem header_diverges (rest : List Char) (k : Nat) :
    valAt (tblV grammar ('X'::rest) .callByValuePar k 1 [[]]) (rest.length+1)=none := by
  induction k with
  | zero => simp [tblV,valAt]
  | succ k ih =>
    rw [valAt_tblV_succ actual_callee [[]] (by simp)]
    have hmissing : ruleAtM grammar.rules 9=none := rfl
    simpa [MultiplyingPrefixCompiler.sourceBody,RepeatedWordArguments.expression,query,starts,evV,
      MExp.andP,hmissing,actual_callee,evParArgs,Shallot.stripPrefix?,sfx,Shallot.beqChar,pre] using ih

def consumingParts : List Part := [⟨false,.chr 'a'⟩,⟨true,.eps⟩]
def consumingEntries : List MixedForwardingCompiler.Entry := [.origin (.guard (.leaf 0) (.leaf 1))]

theorem consuming_query_rejected : check consumingParts consumingEntries=false := by decide +kernel

theorem header_call_diverges (rest : List Char) (k : Nat) (E : List (List Char)) :
    evV grammar ('X'::rest) .callByValuePar (tblV grammar ('X'::rest) .callByValuePar k) E
      (.call 1 [.lit []]) (rest.length+1)=none := by
  rw [evV_call_par actual_callee rfl (by decide)]
  simpa [evParArgs,evV,Shallot.stripPrefix?,sfx,pre] using header_diverges rest k

theorem compiled_header_diverges (rest : List Char) (k : Nat) :
    evV (target parts entries) ('X'::rest) .callByValueSeq
      (tblV (target parts entries) ('X'::rest) .callByValueSeq k) []
      (render parts entries (.call 1 [.lit []])) (rest.length+1)=none :=
  (all_undefined (.call 1 [.lit []]) (by trivial) ('X'::rest)).mp
    (fun j => header_call_diverges rest j []) k

/-- Omitting the effect gate would change a concrete residual. This is a
boundary of this transformation, not a language-class separation. -/
theorem unchecked_query_changes_result :
    evV (source consumingParts consumingEntries) ['a','a'] .callByValuePar
      (tblV (source consumingParts consumingEntries) ['a','a'] .callByValuePar 2) [] (.call 0 [.lit ['a']]) 2=some (some 0) ∧
    evV (target consumingParts consumingEntries) ['a','a'] .callByValueSeq
      (tblV (target consumingParts consumingEntries) ['a','a'] .callByValueSeq 2) []
      (render consumingParts consumingEntries (.call 0 [.lit ['a']])) 2=some (some 1) := by decide +kernel

end Shallot.MacroPeg.CBV.CheckedOriginExamples
