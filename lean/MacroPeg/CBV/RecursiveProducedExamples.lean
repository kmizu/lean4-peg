import MacroPeg.CBV.RecursiveProducedCorrespondence

namespace Shallot.MacroPeg.CBV.RecursiveProducedExamples
open RecursiveProducedCompiler
open ReplayControlFusion (Part)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- This producer is an actual recursive user, not an unfolded pure parser. -/
def producer : MExp := .call 1 [.lit []]
def producerBody : MExp := .alt (.seq (.chr 'a') producer) (.chr 'b')
def continuation : MExp := .seq (.chr '!') (.seq (.call 2 [.param 0])
  (.seq (.alt (.seq (.chr '@') (.call 0 [producer])) .eps) (.param 0)))
def ps : List Part := [⟨false,producerBody⟩]
def specs : List Entry := [.produced producer continuation,.origin (.leaf 0),.growth ⟨2,3,.chr '#',.chr 'g'⟩]
abbrev grammar := source ps specs
abbrev compiled := target ps specs

def entry : MExp := .seq (.call 0 [producer]) (.notP .any)
theorem checked : check ps specs=true := by decide +kernel
theorem root_checked : conforms specs entry=true := by decide +kernel
theorem old_pure_gate_rejects : ProducedPrefixCompiler.check ps specs=false := by decide +kernel

theorem actual_producer : ruleAtM grammar.rules 1=some ⟨1,producerBody⟩ := by rfl

theorem producer_closed : ReplayFallbackFusion.Closed producerBody := by trivial

theorem producer_call (input rest : List Char) (t : MTree)
    (hd : MDerives grammar .callByValuePar producerBody input (.ok t rest)) :
    MDerives grammar .callByValuePar producer input (.ok (.nodeCall 1 t) rest) := by
  apply MDerives.callParOk 1 [.lit []] ⟨1,producerBody⟩ input rest [.lit []] t rfl actual_producer rfl
  · exact .cons _ _ input [] input _ [] (.litOk [] input input rfl) rfl (.nil input)
  · simpa only [ReplayFallbackFusion.subst_closed _ producerBody producer_closed] using hd

def word (n : Nat) : List Char := List.replicate n 'a'++['b']

/-- The same fixed recursive producer captures every a^n b, with no word
palette or length bound, before either parent or child continuation runs. -/
theorem producer_ok (n : Nat) (rest : List Char) :
    ∃ t, MDerives grammar .callByValuePar producer (word n++rest) (.ok t rest) := by
  induction n with
  | zero =>
    exact ⟨_,producer_call _ _ _ (.altR _ _ _ _ _ (.seqFail₁ _ _ _ (.chrFail 'a' 'b' rest rfl)) (.chrOk 'b' 'b' rest rfl))⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    have hh : word (n+1)++rest='a'::(word n++rest) := by simp [word,List.replicate_succ]
    rw [hh]
    exact ⟨_,producer_call _ _ _ (.altL _ _ _ _ _ (.seqOk _ _ _ _ _ _ _ (.chrOk 'a' 'a' _ rfl) ht))⟩

theorem producer_unbounded (n : Nat) : SObs grammar .callByValuePar producer (word n) (some []) := by
  obtain ⟨t,ht⟩ := producer_ok n []
  exact ⟨.ok t [],by simpa using ht,rfl⟩

theorem actual_argument_capture (n : Nat) (rest : List Char) :
    DerivesArgsPar grammar .callByValuePar (word n++rest) [producer] [.lit (word n)] := by
  obtain ⟨t,ht⟩ := producer_ok n rest
  exact .cons producer [] _ (word n) rest t [] ht rfl (.nil _)

theorem capture_lengths : ∀ bound, ∃ n, (word n).length>bound := by
  intro bound
  exact ⟨bound,by simp [word]⟩

def simple (w : List Char) := w++['!']++w++['g']++w
def nested (w v : List Char) := w++['!']++w++['g','@']++simple v++w

def sourceRun (e : MExp) (x : List Char) (k : Nat) := evV grammar x .callByValuePar (tblV grammar x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) := evV compiled x .callByValueSeq (tblV compiled x .callByValueSeq k) [] (render ps specs e) x.length

theorem fixed_target : compiled.rules.length=16 := by decide +kernel

theorem source_fresh_captures : ∀ pair∈[(0,3),(3,0),(1,2)], sourceRun entry (nested (word pair.1) (word pair.2)) 12=some (some 0) := by decide +kernel

theorem target_fresh_captures : ∀ pair∈[(0,3),(3,0),(1,2)], targetRun entry (nested (word pair.1) (word pair.2)) 12=some (some 0) := by decide +kernel

theorem short_parent_rejected : targetRun entry (word 3++['!']++word 3++['g','@']++simple (word 0)++word 2) 12=some none := by decide +kernel

theorem observations (e : MExp) (he : e.FirstOrder) (hs : conforms specs e=true) (x : List Char) (rest : Option (List Char)) :
    SObs grammar .callByValuePar e x rest ↔ SObs compiled .callByValueSeq (render ps specs e) x rest :=
  RecursiveProducedCorrespondence.observations_iff ps specs checked e he hs x rest

/-- The original prefix actually spends another recursive call level. -/
def tinySpecs : List Entry := [.produced producer (.param 0),.origin (.leaf 0)]
abbrev tinySource := source ps tinySpecs
abbrev tinyTarget := target ps tinySpecs

theorem tiny_checked : check ps tinySpecs=true := by decide +kernel

theorem same_clock_differs :
    evV tinySource ['b','b'] .callByValuePar (tblV tinySource ['b','b'] .callByValuePar 1) [] (.call 0 [producer]) 2=none ∧
    evV tinySource ['b','b'] .callByValuePar (tblV tinySource ['b','b'] .callByValuePar 2) [] (.call 0 [producer]) 2=some (some 0) ∧
    evV tinyTarget ['b','b'] .callByValueSeq (tblV tinyTarget ['b','b'] .callByValueSeq 1) []
      (render ps tinySpecs (.call 0 [producer])) 2=some (some 0) := by decide +kernel

theorem wrong_capture_rejected : conforms specs (.call 0 [.lit ['a']])=false ∧
    sourceRun (.call 0 [.lit ['a']]) "ab!aga".toList 12=some (some 0) ∧
    targetRun (.call 0 [.lit ['a']]) "ab!aga".toList 12=some none := by decide +kernel

theorem producer_failure_preserved : sourceRun entry ['X'] 12=some none ∧
    targetRun entry ['X'] 12=some none := by decide +kernel

/-- The producer calls the very client whose prefix is being removed.
The correspondence does not rely on a disjoint, unchanged producer grammar. -/
def coupledParts : List Part := [⟨false,.alt (.seq (.chr 'a') (.call 0 [producer])) (.chr 'b')⟩]
def coupledSpecs : List Entry := [.produced producer .eps,.origin (.leaf 0)]

theorem coupled_checked : check coupledParts coupledSpecs=true := by decide +kernel
theorem coupled_root_checked : conforms coupledSpecs (.call 0 [producer])=true := by decide +kernel

theorem coupled_source : ∀ n∈[0,1,3],
    evV (source coupledParts coupledSpecs) (word n) .callByValuePar
      (tblV (source coupledParts coupledSpecs) (word n) .callByValuePar 12) [] (.call 0 [producer]) (n+1)=some (some 0) := by decide +kernel

theorem coupled_target : ∀ n∈[0,1,3],
    evV (target coupledParts coupledSpecs) (word n) .callByValueSeq
      (tblV (target coupledParts coupledSpecs) (word n) .callByValueSeq 12) []
      (render coupledParts coupledSpecs (.call 0 [producer])) (n+1)=some (some 0) := by decide +kernel

theorem coupled_language (x : List Char) :
    SObs (source coupledParts coupledSpecs) .callByValuePar (.call 0 [producer]) x (some []) ↔
      SObs (target coupledParts coupledSpecs) .callByValueSeq (render coupledParts coupledSpecs (.call 0 [producer])) x (some []) :=
  RecursiveProducedCorrespondence.observations_iff coupledParts coupledSpecs coupled_checked (.call 0 [producer])
    (by trivial) coupled_root_checked x (some [])

theorem open_producer_rejected : check [] [.produced (.param 0) .eps]=false := by decide +kernel

def loopParts : List Part := [⟨false,producer⟩]
def loopSpecs : List Entry := [.produced producer (.chr '!'),.origin (.leaf 0)]
abbrev loopGrammar := source loopParts loopSpecs

theorem loop_checked : check loopParts loopSpecs=true := by decide +kernel
theorem loop_root_checked : conforms loopSpecs (.call 0 [producer])=true := by decide +kernel

theorem actual_loop : ruleAtM loopGrammar.rules 1=some ⟨1,producer⟩ := by rfl

/-- Recursive producers need not terminate. The actual argument preflight
keeps a deleted prefix from introducing any finite result on any input. -/
theorem loop_rows (x : List Char) (k : Nat) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV loopGrammar x .callByValuePar k 1 E) p=none := by
  induction k generalizing E with
  | zero => simp [tblV,valAt]
  | succ k ih =>
    rw [valAt_tblV_succ actual_loop E hp]
    change evV loopGrammar x .callByValuePar (tblV loopGrammar x .callByValuePar k) E (.call 1 [.lit []]) p=none
    rw [evV_call_par actual_loop rfl (by decide)]
    simpa [evParArgs,evV,Shallot.stripPrefix?,length_sfx x hp,pre] using ih [[]]

theorem loop_source (x : List Char) (k : Nat) :
    evV loopGrammar x .callByValuePar (tblV loopGrammar x .callByValuePar k) [] (.call 0 [producer]) x.length=none := by
  have hr : ruleAtM loopGrammar.rules 0=some ⟨1,.seq producer (.chr '!')⟩ := rfl
  have hd : evV loopGrammar x .callByValuePar (tblV loopGrammar x .callByValuePar k) [] producer x.length=none := by
    change evV loopGrammar x .callByValuePar (tblV loopGrammar x .callByValuePar k) [] (.call 1 [.lit []]) x.length=none
    rw [evV_call_par actual_loop rfl (by decide)]
    simpa [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),pre] using loop_rows x k [[]] x.length (Nat.le_refl _)
  rw [evV_call_par hr rfl (by decide),evPar_cons_none hd]

theorem loop_target (x : List Char) (k : Nat) :
    evV (target loopParts loopSpecs) x .callByValueSeq (tblV (target loopParts loopSpecs) x .callByValueSeq k) []
      (render loopParts loopSpecs (.call 0 [producer])) x.length=none :=
  (RecursiveProducedCorrespondence.undefined_iff loopParts loopSpecs loop_checked x [] (.call 0 [producer]) (by trivial)
    loop_root_checked x.length (Nat.le_refl _)).mp (loop_source x) k

end Shallot.MacroPeg.CBV.RecursiveProducedExamples
