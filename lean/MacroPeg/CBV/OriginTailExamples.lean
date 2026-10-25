import MacroPeg.CBV.OriginTailRawCompiler

namespace Shallot.MacroPeg.CBV.OriginTailExamples
open MultiplyingPrefixCompiler (Spec sourceBody)
open MixedGrowthCompiler (Entry)
open ReplayControlFusion (Part Plan)
open RepeatedWordArguments (copies)
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def probe : MExp := .seq (.notP (.chr 'X')) (.call 2 [.star (.chr 'c')])
def parts : List Part := [⟨false,probe⟩,
  ⟨true,.seq (.chr 'g') (.param 0)⟩,
  ⟨true,.seq (.chr 'g') (.seq (.param 0) (.chr '?'))⟩]
def tail : MExp := .seq (.chr '!') (.seq (.param 0) (.seq (.call 0 [.lit ['x']]) (.param 0)))
def parent : Spec := ⟨1,3,tail,.chr 'F'⟩
def child : Plan := .guard (.leaf 0) (.alt (.leaf 1) (.leaf 2))
def specs : List Entry := [.growth parent,.origin child,.growth ⟨9,2,.eps,.eps⟩]
abbrev original := MixedGrowthCompiler.source parts specs
abbrev target := OriginTailInlining.target parts specs 0 parent child
abbrev render := OriginTailInlining.render parts specs 0 parent child

theorem parent_lookup : specs[0]?=some (.growth parent) := rfl
theorem child_lookup : specs[parent.callee]?=some (.origin child) := rfl
theorem checked : OriginTailInlining.check parts specs 0=true := by decide +kernel
theorem old_rejected : OriginHeadInlining.check parts specs 0=false := by decide +kernel
theorem firstOrder : original.FirstOrder := by
  simp [original,MixedGrowthCompiler.source,MixedGrowthCompiler.body,specs,parent,tail,parts,probe,child,
    sourceBody,Plan.exp,ReplayControlFusion.sourceLeaf,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression,MExp.andP]

def entry : MExp := .call 0 [.lit ['a']]
def dynamic : MExp := .call 0 [.seq (.star (.chr 'c')) (.chr 'd')]
def sourceRun (e : MExp) (x : List Char) (k : Nat) := evV original x .callByValuePar (tblV original x .callByValuePar k) [] e x.length
def targetRun (e : MExp) (x : List Char) (k : Nat) := evV target x .callByValueSeq (tblV target x .callByValueSeq k) [] (render e) x.length
def input (n : Nat) := let w := List.replicate n 'c'++['d']; copies w 3++['g']++copies w 3++['!']++w++['x','F']++w

theorem parent_scope : sourceRun entry ['a','a','a','g','a','a','a','!','a','x','F','a'] 16=some (some 0) ∧
    targetRun entry ['a','a','a','g','a','a','a','!','a','x','F','a'] 16=some (some 0) := by decide +kernel
theorem dynamic_source : ∀ n∈[0,1,4], sourceRun dynamic (input n) 16=some (some 0) := by decide +kernel
theorem dynamic_target : ∀ n∈[0,1,4], targetRun dynamic (input n) 16=some (some 0) := by decide +kernel
theorem child_scope_leak_rejected : targetRun entry (copies ['a'] 3++['g']++copies ['a'] 3++['!']++copies ['a'] 3++['x','F']++copies ['a'] 3) 16=some none := by decide +kernel
theorem committed_suffix : sourceRun entry (copies ['a'] 3++['g']++copies ['a'] 3++['?','!','a','x','F','a']) 16=some none ∧
    targetRun entry (copies ['a'] 3++['g']++copies ['a'] 3++['?','!','a','x','F','a']) 16=some none := by decide +kernel
theorem query_still_required : targetRun (.call 0 [.lit ['X']]) (copies ['X'] 3++['g']++copies ['X'] 3++['!','X','x','F','X']) 16=some none := by decide +kernel
theorem failed_preflight : targetRun entry ['a','F'] 16=some (some 0) ∧
    targetRun (.call 0 [.star (.lit [])]) ['a','a','a'] 16=none := by decide +kernel
theorem fixed_target : target.rules.length=24 := rfl

theorem observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs original .callByValuePar e x rest ↔ SObs target .callByValueSeq (render e) x rest :=
  OriginTailInlining.observations_iff parts specs 0 parent child parent_lookup child_lookup firstOrder checked e he x rest

/-- A zero-width closed result can return at the original position when
its continuation begins by replaying the parent's retained value. -/
def zeroParts : List Part := [⟨false,.andP (.chr 'a')⟩,⟨true,.seq (.chr 'g') (.param 0)⟩]
def zeroTail : MExp := .seq (.param 0) (.seq (.lit ['a','a','!']) (.seq (.call 2 [.lit ['x']]) (.param 0)))
def zeroParent : Spec := ⟨1,3,zeroTail,.chr 'F'⟩
def zeroChild : Plan := .alt (.leaf 0) (.leaf 1)
def zeroSpecs : List Entry := [.growth zeroParent,.origin zeroChild,.growth ⟨9,2,.eps,.eps⟩]
abbrev zeroOriginal := MixedGrowthCompiler.source zeroParts zeroSpecs
abbrev zeroTarget := OriginTailInlining.target zeroParts zeroSpecs 0 zeroParent zeroChild
abbrev zeroRender := OriginTailInlining.render zeroParts zeroSpecs 0 zeroParent zeroChild

theorem zero_checked : OriginTailInlining.check zeroParts zeroSpecs 0=true := by decide +kernel
theorem zero_firstOrder : zeroOriginal.FirstOrder := by
  simp [zeroOriginal,MixedGrowthCompiler.source,MixedGrowthCompiler.body,zeroParts,zeroTail,zeroParent,zeroChild,zeroSpecs,
    sourceBody,Plan.exp,ReplayControlFusion.sourceLeaf,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression,MExp.andP]
theorem zero_return : evV zeroOriginal ['a','a','a','!','x','a'] .callByValuePar (tblV zeroOriginal ['a','a','a','!','x','a'] .callByValuePar 16) [] entry 6=some (some 0) ∧
    evV zeroTarget ['a','a','a','!','x','a'] .callByValueSeq (tblV zeroTarget ['a','a','a','!','x','a'] .callByValueSeq 16) [] (zeroRender entry) 6=some (some 0) := by decide +kernel
theorem zero_replay_alternative : evV zeroTarget ['b','b','b','g','b','b','b','b','a','a','!','x','b'] .callByValueSeq
    (tblV zeroTarget ['b','b','b','g','b','b','b','b','a','a','!','x','b'] .callByValueSeq 16) [] (zeroRender (.call 0 [.lit ['b']])) 13=some (some 0) := by decide +kernel

theorem zero_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs zeroOriginal .callByValuePar e x rest ↔ SObs zeroTarget .callByValueSeq (zeroRender e) x rest :=
  OriginTailInlining.observations_iff zeroParts zeroSpecs 0 zeroParent zeroChild rfl rfl zero_firstOrder zero_checked e he x rest

/-- A result-level negative query is supported by the replaying tail slot;
its inner, consuming closed atom is only a query dependency. -/
def negativeParts : List Part := [⟨false,.chr 'X'⟩]
def negativeChild : Plan := .notP (.leaf 0)
def negativeSpecs : List Entry := [.growth zeroParent,.origin negativeChild,.growth ⟨9,2,.eps,.eps⟩]
theorem negative_checked : OriginTailInlining.check negativeParts negativeSpecs 0=true := by decide +kernel
theorem negative_result : evV (OriginTailInlining.target negativeParts negativeSpecs 0 zeroParent negativeChild) ['a','a','a','!','x','a'] .callByValueSeq
    (tblV (OriginTailInlining.target negativeParts negativeSpecs 0 zeroParent negativeChild) ['a','a','a','!','x','a'] .callByValueSeq 16) []
    (OriginTailInlining.render negativeParts negativeSpecs 0 zeroParent negativeChild entry) 6=some (some 0) := by decide +kernel

theorem early_consumer_rejected : OriginTailInlining.check [⟨false,.chr 'a'⟩]
    [.growth zeroParent,.origin (.leaf 0),.growth ⟨9,2,.eps,.eps⟩] 0=false := by decide +kernel
theorem arbitrary_tail_early_query_rejected : OriginTailInlining.check zeroParts
    [.growth parent,.origin (.leaf 0),.growth ⟨9,2,.eps,.eps⟩] 0=false := by decide +kernel

theorem only_replay_exits : OriginTailParts.flowCheck parts tail child=true ∧
    OriginTailParts.flowCheck parts tail (.leaf 0)=false := by decide +kernel

def nullParts : List Part := [⟨false,.star (.lit [])⟩,⟨true,.eps⟩]
def nullChild : Plan := .guard (.leaf 0) (.leaf 1)
def nullSpecs : List Entry := [.growth parent,.origin nullChild,.growth ⟨9,2,.eps,.eps⟩]
abbrev nullOriginal := MixedGrowthCompiler.source nullParts nullSpecs
abbrev nullTarget := OriginTailInlining.target nullParts nullSpecs 0 parent nullChild
abbrev nullRender := OriginTailInlining.render nullParts nullSpecs 0 parent nullChild

theorem null_checked : OriginTailInlining.check nullParts nullSpecs 0=true := by decide +kernel

theorem null_firstOrder : nullOriginal.FirstOrder := by
  simp [nullOriginal,MixedGrowthCompiler.source,MixedGrowthCompiler.body,nullParts,nullSpecs,nullChild,parent,tail,
    sourceBody,Plan.exp,ReplayControlFusion.sourceLeaf,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression,MExp.andP]

theorem null_source (x : List Char) (k : Nat) :
    evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar k) [] (.call 0 [.lit []]) x.length=none := by
  have hr1 : ruleAtM nullOriginal.rules 1=some ⟨1,Plan.exp (ReplayControlFusion.sourceLeaf nullParts) nullChild⟩ := rfl
  have hrow1 (j p : Nat) (hp : p≤x.length) : valAt (tblV nullOriginal x .callByValuePar j 1 [[]]) p=none := by
    cases j with
    | zero => rfl
    | succ j =>
      rw [valAt_tblV_succ hr1 [[]] hp]
      have hstar : evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar j) [[]] (.star (.lit [])) p=none := by
        rw [evV_star]
        exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (by omega)
      have hquery : evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar j) [[]] (.andP (.star (.lit []))) p=none := by
        rw [CallLookahead.evV_peek,hstar]; rfl
      exact evV_seq_none hquery
  have hr0 : ruleAtM nullOriginal.rules 0=some ⟨1,sourceBody parent⟩ := rfl
  have hrow0 : valAt (tblV nullOriginal x .callByValuePar k 0 [[]]) x.length=none := by
    cases k with
    | zero => rfl
    | succ j =>
      rw [valAt_tblV_succ hr0 [[]] (Nat.le_refl _)]
      have harg : evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar j) [[]]
          (RepeatedWordArguments.expression (.param 0) parent.factor) x.length=some (some x.length) := by
        rw [WordArguments.word_eval _ _ _ _ _ _ (RepeatedWordArguments.expression_word (.param 0) True.intro _),
          RepeatedWordArguments.expression_value _ (.param 0) [] rfl]
        simp [WordArguments.literal,RepeatedWordArguments.copies_nil,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _)]
      have hcall : evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar j) [[]]
          (.call parent.callee [RepeatedWordArguments.expression (.param 0) parent.factor]) x.length=none := by
        change evV nullOriginal x .callByValuePar (tblV nullOriginal x .callByValuePar j) [[]]
          (.call 1 [RepeatedWordArguments.expression (.param 0) parent.factor]) x.length=none
        rw [evV_call_par hr1 rfl (by decide)]
        simpa only [evParArgs,harg,pre,Nat.sub_self,List.take_zero] using hrow1 j x.length (Nat.le_refl _)
      exact evV_alt_none (evV_seq_none hcall)
  rw [evV_call_par hr0 rfl (by decide)]
  simpa only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),pre,Nat.sub_self,List.take_zero] using hrow0

theorem null_target (x : List Char) (k : Nat) :
    evV nullTarget x .callByValueSeq (tblV nullTarget x .callByValueSeq k) [] (nullRender (.call 0 [.lit []])) x.length=none :=
  (OriginTailInlining.undefined_iff nullParts nullSpecs 0 parent nullChild rfl rfl null_firstOrder null_checked
    (.call 0 [.lit []]) (by trivial) x).mp (null_source x) k

/-- The original Spec frontend also permits a parent-dependent continuation
when a prepared zero-head child returns through a replay branch. -/
def rawParent : Spec := ⟨1,3,.seq (.param 0) (.chr '!'),.chr 'F'⟩
def rawSpecs : List Spec := [rawParent,⟨9,0,.eps,.seq (.chr 'g') (.param 0)⟩]
def rawChild : Plan := .alt (.leaf 2) (.leaf 3)
theorem raw_checked : OriginTailRawCompiler.check rawSpecs 0=true := by decide +kernel
theorem raw_firstOrder : (MultiplyingPrefixCompiler.source rawSpecs).FirstOrder := by
  simp [MultiplyingPrefixCompiler.source,rawSpecs,rawParent,sourceBody,MGrammar.FirstOrder,MExp.FirstOrder,MExp.FirstOrderArgs,
    RepeatedWordArguments.expression]
theorem raw_target : evV (OriginTailRawCompiler.target rawSpecs 0 rawParent rawChild) ['a','a','a','g','a','a','a','a','!'] .callByValueSeq
    (tblV (OriginTailRawCompiler.target rawSpecs 0 rawParent rawChild) ['a','a','a','g','a','a','a','a','!'] .callByValueSeq 16) []
    (OriginTailRawCompiler.render rawSpecs 0 rawParent rawChild entry) 9=some (some 0) := by decide +kernel

theorem raw_observations (e : MExp) (he : e.FirstOrder) (x : List Char) (rest : Option (List Char)) :
    SObs (MultiplyingPrefixCompiler.source rawSpecs) .callByValuePar e x rest ↔
      SObs (OriginTailRawCompiler.target rawSpecs 0 rawParent rawChild) .callByValueSeq (OriginTailRawCompiler.render rawSpecs 0 rawParent rawChild e) x rest :=
  OriginTailRawCompiler.observations_iff rawSpecs 0 rawParent rawChild rfl rfl raw_firstOrder raw_checked e he x rest

end Shallot.MacroPeg.CBV.OriginTailExamples
