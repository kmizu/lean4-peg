import MacroPeg.CBV.GuardedFinitePrefix

namespace Shallot.MacroPeg.CBV.GuardedFinitePrefixExamples
open GuardedFinitePrefix
open ClockFreezing (Table)
open FinitePrefixControl (Prefix)
open RecursiveScannerProductCompiler (Arg sourceExpr plain target offset)
open RecursiveCaptureProfiles (scopeCheck)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def machine : StatefulScanner.Machine 3 := ⟨fun q =>
  if q=0 then [('a',0)] else if q=1 then [('a',2)] else [('a',0)]⟩
def alphabet : List Char := ['a']
def labels : LiteralPrefixObservation.Labels 3 := fun q =>
  some (if q=1 then ['a','a'] else if q=2 then ['a'] else [])
def read : Words 3 := fun u => .literalQuery alphabet 0
  (if u=[] then 0 else if u=['a'] then 2 else 1) labels
def finish : Words 3 := fun u => if u=[] then .replayQuery
  else .shift 0 (fun q => if q=0 then some u else none)

/-- The first branch can consume aa only when the retained query fails
there. The second checks the old value and then consumes a. -/
def dependentPrefix : Prefix := .alt (.seq (.lit ['a','a']) (.query false))
  (.seq (.notP (.query false)) (.lit ['a']))
def committed : Prefix := .alt (.lit ['a','a']) (.lit ['a'])
def controls : Nat → Control 3 := fun i => if i=1 then .ready .replayQuery
  else if i=2 then .star (.finite committed)
  else if i=3 then .star (.finite (.query true))
  else .star (.finite dependentPrefix)
def copyBody : Arg := .alt (.seq (.user 1 (.seq (.param 0) (.param 0))) (.param 0)) (.lit [])
def bodies : List Arg := [.lit [],copyBody,.lit [],.lit []]
def argument : Arg := .user 1 (.lit ['a'])
def root : Arg := .user 0 argument

theorem checked : check machine read finish controls bodies alphabet=true ∧
    scopeCheck bodies root=true ∧ AlphabetCaptureProfiles.literalCheck alphabet root=true := by decide +kernel

def sourceRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (source machine controls bodies) x .callByValuePar
    (tblV (source machine controls bodies) x .callByValuePar k) [] (sourceExpr machine e) x.length

def targetRun (e : Arg) (x : List Char) (k : Nat) :=
  evV (target machine (entries read finish controls) bodies) x .callByValueSeq
    (tblV (target machine (entries read finish controls) bodies) x .callByValueSeq k) []
    (plain machine bodies [] e) x.length

theorem recursive_source_samples : ∀ nr∈[(1,0),(2,1),(3,1),(4,0),(5,1),(6,1),(7,1),(8,1),(10,0),(11,1),(12,1)],
    sourceRun root (List.replicate nr.1 'a') 4=some (some nr.2) := by decide +kernel

theorem recursive_target_samples : ∀ nr∈[(1,0),(2,1),(3,1),(4,0),(5,1),(6,1),(7,1),(8,1),(10,0),(11,1),(12,1)],
    ∃ k, targetRun root (List.replicate nr.1 'a') k=some (some nr.2) := by
  intro nr hn
  exact (defined_iff machine read finish controls bodies alphabet checked.1 root checked.2.1 checked.2.2
    (List.replicate nr.1 'a') (some nr.2)).mp ⟨4,recursive_source_samples nr hn⟩

theorem target_direct : targetRun root "aaaa".toList 8=some (some 0) := by decide +kernel

def productRoot : Arg := .user 1 (.user 0 (.lit ['a']))
theorem product_direct : sourceRun productRoot "aaaa".toList 2=some (some 1) ∧
    targetRun productRoot "aaaa".toList 3=some (some 1) := by decide +kernel

/-- Committing aa before the final replay query must not retry a when
that query fails. A naive alternative of guarded leaves consumes too far. -/
theorem committed_source : sourceRun (.user 2 (.lit ['a'])) "aa".toList 1=some (some 1) ∧
    targetRun (.user 2 (.lit ['a'])) "aa".toList 2=some (some 1) := by decide +kernel

theorem naive_commit_wrong :
    evV ⟨[]⟩ "aa".toList .callByValuePar (fun _ _ => []) [['a']]
      (.seq (.star (.alt (.seq (.lit ['a','a']) (.andP (.param 0)))
        (.seq (.lit ['a']) (.andP (.param 0))))) (.param 0)) 2=some (some 0) := by decide +kernel

theorem empty_capture : sourceRun (.user 0 (.lit [])) "aaaa".toList 1=some (some 0) ∧
    targetRun (.user 0 (.lit [])) "aaaa".toList 2=some (some 0) := by decide +kernel

theorem outside_alphabet : sourceRun root "aab".toList 4=some (some 2) ∧
    ∃ k, targetRun root "aab".toList k=some (some 2) := by
  have hs : sourceRun root "aab".toList 4=some (some 2) := by decide +kernel
  exact ⟨hs,(defined_iff machine read finish controls bodies alphabet checked.1 root checked.2.1
    checked.2.2 "aab".toList (some 2)).mp ⟨4,hs⟩⟩

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source machine controls bodies) .callByValuePar (sourceExpr machine root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation machine read finish controls bodies alphabet checked.1 root checked.2.1 checked.2.2

theorem nullable_source (k : Nat) : sourceRun (.user 3 (.lit ['a'])) "aa".toList k=none := by
  have hr := source_rule machine controls bodies 3 (.lit []) (by rfl)
  have hb (T : Table) : evV (source machine controls bodies) "aa".toList .callByValuePar T [['a']]
      (.seq (.seq (original (controls 3)) (.param 0)) (.lit [])) 2=none := by
    have hs : evV (source machine controls bodies) "aa".toList .callByValuePar T [['a']]
        (.star (.seq (.andP (.param 0)) (.andP (.param 0)))) 2=none := by
      rw [evV_star,evStar_stuck (show evV (source machine controls bodies) "aa".toList .callByValuePar T [['a']]
        (.seq (.andP (.param 0)) (.andP (.param 0))) 2=some (some 2) from by simp only [MExp.andP,evV]; decide +kernel) (by omega)]
    exact evV_seq_none (evV_seq_none hs)
  change evV (source machine controls bodies) "aa".toList .callByValuePar
    (tblV (source machine controls bodies) "aa".toList .callByValuePar k) []
    (.call (offset machine+3) [.lit ['a']]) 2=none
  rw [evV_call_par hr rfl (by decide)]
  change valAt (tblV (source machine controls bodies) "aa".toList .callByValuePar k
    (offset machine+3) [['a']]) 2=none
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr _ (by decide : 2≤"aa".toList.length)]; exact hb _

theorem nullable_target : ∀ k, targetRun (.user 3 (.lit ['a'])) "aa".toList k=none :=
  (undefined_iff machine read finish controls bodies alphabet checked.1 (.user 3 (.lit ['a']))
    (by decide +kernel) (by decide +kernel) "aa".toList).mp nullable_source

theorem bad_read_rejected : atomCheck (fun _ => read []) finish committed=false := by decide +kernel

theorem bad_finish_rejected : atomCheck read (fun _ => .replayQuery) dependentPrefix=false := by decide +kernel

end Shallot.MacroPeg.CBV.GuardedFinitePrefixExamples
