import MacroPeg.CBV.FoldedUserPrefix

namespace Shallot.MacroPeg.CBV.FoldedUserPrefixExamples
open LeadingReplayStar (User sourceRender)
open ExpressionContext (Context plug)
abbrev Arg := LeadingReplayStar.Arg
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- R replays the forwarded parent value, then can call the original
caller F with a doubled fresh argument and restore its parent's value. -/
def B : Arg := .alt
  (.seq (.lit ['!']) (.seq (.user 0 (.seq (.param 0) (.param 0))) (.param 0)))
  (.lit ['d'])
def users : List User := [
  .repeated [] B (.lit ['z']),
  .control ⟨[⟨some [],B⟩],.leaf 0,none⟩]
def normalized := LeadingReplayStar.sourceGrammar [] users
def C : Context := .seq (.seq (.star .hole) (.atom (.seq (.lit []) (.param 0)))) (.atom (.lit ['z']))
def expandedB := sourceRender [] users B
def raw := FoldedUserPrefix.source normalized 0 1 C
def target := LeadingReplayStar.targetGrammar [] users
def entry : Arg := .user 0 (.lit ['a','b'])

theorem checked : FoldedUserPrefix.check normalized 0 1 expandedB C=true := by decide +kernel

theorem valid : LeadingReplayStar.Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,LeadingReplayStar.converted,User.toControl,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    ReplayControlFusion.Plan.All,B,LeadingReplayStar.replay,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (LeadingReplayStar.specs users) entry := by
  have hlen : (LeadingReplayStar.specs users).length=2 := (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted users)).trans rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

/-- The actual source F calls R(param0) as its consuming repeated prefix;
R's body in turn calls F with a different, doubled captured argument. -/
theorem raw_rules : ruleAtM raw.rules 0=some ⟨1,plug (.call 1 [.param 0]) C⟩ ∧
    ruleAtM raw.rules 1=some ⟨1,ReplayCallInlining.body expandedB⟩ := ⟨rfl,rfl⟩

def tree (w : List Char) : Nat → List Char
  | 0 => w++['z']
  | d+1 => w++['!']++tree (w++w) d++w++w++['z']

def sourceRun (x : List Char) (k : Nat) :=
  evV raw x .callByValuePar (tblV raw x .callByValuePar k) [] (sourceRender [] users entry) x.length
def normalizedRun (x : List Char) (k : Nat) :=
  evV normalized x .callByValuePar (tblV normalized x .callByValuePar k) [] (sourceRender [] users entry) x.length
def targetRun (x : List Char) (k : Nat) :=
  evV target x .callByValueSeq (tblV target x .callByValueSeq k) [] (LeadingReplayStar.targetRender [] users entry) x.length

theorem source_mutual_recursion : ∀ d∈[0,1,2,3], sourceRun (tree ['a','b'] d) 12=some (some 0) := by decide +kernel

theorem source_repeated_prefix :
    sourceRun (['a','b','d','a','b','d','a','b','z']) 8=some (some 0) := by decide +kernel

theorem direct_target_mutual : targetRun (tree ['a','b'] 1) 12=some (some 0) := by decide +kernel

theorem restoration_failures : ∀ x∈["ab!ababzaabz".toList,"ab!abzababz".toList],
    sourceRun x 8=some none ∧ targetRun x 12=some none := by decide +kernel

theorem preflight_required :
    evV ⟨[⟨1,.lit []⟩]⟩ ['b'] .callByValuePar (tblV ⟨[⟨1,.lit []⟩]⟩ ['b'] .callByValuePar 2)
      [['a']] (.call 0 [.param 0]) 1=some none ∧
    evV ⟨[⟨1,.lit []⟩]⟩ ['b'] .callByValuePar (tblV ⟨[⟨1,.lit []⟩]⟩ ['b'] .callByValuePar 2)
      [['a']] (.lit []) 1=some (some 1) := by decide +kernel

theorem same_rule_rejected : FoldedUserPrefix.check normalized 0 0 expandedB C=false := by decide +kernel

theorem bad_parameter_rejected : FoldedUserPrefix.check normalized 0 1 (.param 1) C=false := by decide +kernel

/-- Removing a real call frame changes approximation clocks, even though
all finite observations are preserved cofinally. -/
theorem clocks_differ : sourceRun ['a','b','d','a','b','z'] 1=none ∧
    normalizedRun ['a','b','d','a','b','z'] 1=some (some 0) := by decide +kernel

theorem observations (x : List Char) (rest : Option (List Char)) :
    SObs raw .callByValuePar (sourceRender [] users entry) x rest ↔
      SObs target .callByValueSeq (LeadingReplayStar.targetRender [] users entry) x rest :=
  (FoldedUserPrefix.observations normalized (LeadingReplayStar.source_firstOrder [] users) 0 1 expandedB C checked
    _ (OriginControlNormalization.render_firstOrder [] (LeadingReplayStar.ambient users) (LeadingReplayStar.specs users) entry) x rest).trans
    (LeadingReplayStar.observations_iff [] (by simp [RegularCaptureProduct.Valid]) users valid entry entry_valid x rest)

theorem language : ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs raw .callByValuePar (sourceRender [] users entry) x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  FoldedUserPrefix.language_translation [] (by simp [RegularCaptureProduct.Valid]) users valid 0 1 expandedB C checked entry entry_valid

end Shallot.MacroPeg.CBV.FoldedUserPrefixExamples
