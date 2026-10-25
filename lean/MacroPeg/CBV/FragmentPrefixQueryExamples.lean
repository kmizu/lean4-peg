import MacroPeg.CBV.FragmentPrefixQuery

namespace Shallot.MacroPeg.CBV.FragmentPrefixQueryExamples
open FragmentPrefixQuery
open RuntimeShiftFilter (scanner)
open PartialCodewordCapture (eof)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def tails : List FragmentMixedRecursive.Part := [(true,.eps)]
def bodies : List Body := [.after true 0,.after false 0,.leaf 2]
def positive : MExp := .call 0 [.eps,.chr 'a']
def negative : MExp := .call 1 [.eps,.chr 'a']
def independent : MExp := .call 2 [.eps,.chr 'a']
def probing : MExp := .call 0 [.eps,.seq (.chr 'a') (.andP (.call 0 []))]
def root : MExp := .seq probing (.seq scanner (.seq (.chr 'a') eof))

theorem checked : check tails bodies=true := by decide +kernel

theorem raw_rules :
    ruleAtM (source tails bodies).rules 0=some ⟨1,.seq scanner (.andP (.param 0))⟩ ∧
    ruleAtM (source tails bodies).rules 1=some ⟨1,.seq scanner (.notP (.param 0))⟩ := by
  constructor <;> rfl

/-- The scanner length varies with the actual input. The complete capture
includes a proper final a-fragment beyond that scanner's endpoint. -/
theorem unbounded_prefix_samples :
    ∀ n∈[1,2,4],
    let w := List.replicate n 'a'++['#','a']
    let x := List.replicate n 'a'++['#']++w
    evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar 2) []
      (ControlledFragmentReplay.argument .eps (.chr 'a')) x.length=some (some (n+1)) ∧
    pre x x.length (n+1)=w ∧
    evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar 2) []
      (sourceRender tails bodies positive) x.length=some (some (n+2)) ∧
    evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq 2) []
      (targetRender tails bodies positive) x.length=some (some (n+2)) := by decide +kernel

/-- Both query polarities depend on the full captured aa#a. The short
copy aa# rejects the positive query and permits the negative query. -/
theorem full_and_short_copy :
    evV (source tails bodies) "aa#aa#a".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#a".toList .callByValuePar 2) []
      (sourceRender tails bodies negative) 7=some none ∧
    evV (source tails bodies) "aa#aa#".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#".toList .callByValuePar 2) []
      (sourceRender tails bodies positive) 6=some none ∧
    evV (source tails bodies) "aa#aa#".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#".toList .callByValuePar 2) []
      (sourceRender tails bodies negative) 6=some (some 3) ∧
    evV (target tails bodies) "aa#aa#".toList .callByValueSeq
      (tblV (target tails bodies) "aa#aa#".toList .callByValueSeq 2) []
      (targetRender tails bodies negative) 6=some (some 3) := by decide +kernel

/-- The actual final-fragment test calls the very same raw query user
with a fresh empty capture. Its caller then inspects its complete aa#a. -/
theorem same_user_probe :
    evV (source tails bodies) "aa#aa#a".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#a".toList .callByValuePar 2) []
      (sourceRender tails bodies probing) 7=some (some 4) ∧
    evV (target tails bodies) "aa#aa#a".toList .callByValueSeq
      (tblV (target tails bodies) "aa#aa#a".toList .callByValueSeq 2) []
      (targetRender tails bodies probing) 7=some (some 4) := by decide +kernel

/-- Empty initial tables cannot execute the independent scanner row
before the original user has a physical row. -/
theorem clock_zero :
    evV (source tails bodies) "aa#aa#a".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#a".toList .callByValuePar 0) []
      (sourceRender tails bodies independent) 7=none ∧
    evV (target tails bodies) "aa#aa#a".toList .callByValueSeq
      (tblV (target tails bodies) "aa#aa#a".toList .callByValueSeq 0) []
      (targetRender tails bodies independent) 7=none ∧
    evV (source tails bodies) "aa#aa#a".toList .callByValuePar
      (tblV (source tails bodies) "aa#aa#a".toList .callByValuePar 1) []
      (sourceRender tails bodies independent) 7=some (some 4) ∧
    evV (target tails bodies) "aa#aa#a".toList .callByValueSeq
      (tblV (target tails bodies) "aa#aa#a".toList .callByValueSeq 1) []
      (targetRender tails bodies independent) 7=some (some 4) := by decide +kernel

/-- The real argument aa fails on a#, although the scanner itself would
succeed. Removing the argument preview wrongly admits that success. -/
theorem preflight_required :
    evV (source tails bodies) "a#".toList .callByValuePar
      (tblV (source tails bodies) "a#".toList .callByValuePar 1) []
      (sourceRender tails bodies (.call 2 [.eps,.lit ['a','a']])) 2=some none ∧
    evV (target tails bodies) "a#".toList .callByValueSeq
      (tblV (target tails bodies) "a#".toList .callByValueSeq 1) []
      (targetRender tails bodies (.call 2 [.eps,.lit ['a','a']])) 2=some none ∧
    evV (target tails bodies) "a#".toList .callByValueSeq
      (tblV (target tails bodies) "a#".toList .callByValueSeq 1) []
      (.call 4 [.eps]) 2=some (some 0) := by decide +kernel

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source tails bodies) .callByValuePar
      (sourceRender tails bodies root) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation tails bodies checked root

/-- One fixed start expression checks the repeated variable-length word,
including the recursive query selecting the final fragment. -/
theorem whole_samples : ∀ n∈[1,2,4],
    let w := List.replicate n 'a'++['#','a']
    let x := List.replicate n 'a'++['#']++w
    evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar 2) []
      (sourceRender tails bodies root) x.length=some (some 0) ∧
    evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq 2) []
      (targetRender tails bodies root) x.length=some (some 0) := by decide +kernel

theorem negative_language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (source tails bodies) .callByValuePar
      (sourceRender tails bodies (.seq negative (.lit "aa#".toList))) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  language_translation tails bodies checked (.seq negative (.lit "aa#".toList))

def nullable : MExp := .call 2 [.eps,.star .eps]

theorem nullable_source (x : List Char) (clock : Nat) :
    evV (source tails bodies) x .callByValuePar (tblV (source tails bodies) x .callByValuePar clock) []
      (sourceRender tails bodies nullable) x.length=none := by
  let g := source tails bodies
  let T := tblV g x .callByValuePar clock
  have hloop (q : Nat) : evV g x .callByValuePar T [] (.star .eps) q=none :=
    evStar_stuck rfl (Nat.lt_irrefl q)
  have harg : evV g x .callByValuePar T []
      (ControlledFragmentReplay.argument .eps (.star .eps)) x.length=none := by
    cases hs : evV g x .callByValuePar T [] (.star (ControlledPartialCapture.step .eps)) x.length with
    | none => exact evV_seq_none hs
    | some v => cases v with
      | none => exact False.elim (evStar_ne_fail _ hs)
      | some q => rw [ControlledFragmentReplay.argument,evV_seq_ok hs]; exact hloop q
  change evV g x .callByValuePar T [] (.call 2 [ControlledFragmentReplay.argument .eps (.star .eps)]) x.length=none
  rw [evV_call_par (source_rule tails bodies 2 (.leaf 2) (by rfl)) rfl (by decide)]
  change evV (source tails bodies) x .callByValuePar T []
    (ControlledFragmentReplay.argument .eps (.star .eps)) x.length=none at harg
  simp only [evParArgs,harg]

theorem nullable_target (x : List Char) (clock : Nat) :
    evV (target tails bodies) x .callByValueSeq (tblV (target tails bodies) x .callByValueSeq clock) []
      (targetRender tails bodies nullable) x.length=none :=
  (undefined_iff tails bodies checked nullable x).mp (nullable_source x) clock

theorem invalid_copy_rejected :
    copyCheck [(true,MExp.lit ['!'])] 0=false ∧ copyCheck [(false,MExp.eps)] 0=false ∧
    check tails [.after true 1]=false := by decide +kernel

end Shallot.MacroPeg.CBV.FragmentPrefixQueryExamples
