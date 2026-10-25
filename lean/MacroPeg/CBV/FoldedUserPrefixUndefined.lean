import MacroPeg.CBV.FoldedUserPrefixExamples

namespace Shallot.MacroPeg.CBV.FoldedUserPrefixExamples.Nullable
open LeadingReplayStar (User sourceRender)
abbrev Arg := LeadingReplayStar.Arg
abbrev C := FoldedUserPrefixExamples.C
def users : List User := [
  .repeated [] (.lit []) (.lit ['z']),
  .control ⟨[⟨some [],.lit []⟩],.leaf 0,none⟩]
def normalized := LeadingReplayStar.sourceGrammar [] users
def raw := FoldedUserPrefix.source normalized 0 1 C
def target := LeadingReplayStar.targetGrammar [] users
def entry : Arg := .user 0 (.lit [])

theorem checked : FoldedUserPrefix.check normalized 0 1 (.lit []) C=true := by decide +kernel

theorem valid : LeadingReplayStar.Valid [] users := by
  have hlen : ∀ us : List ContinuationFamily.User, (ContinuationFamily.specs us).length=us.length :=
    fun us => ContinuationFamily.emit_length 0 us
  simp [LeadingReplayStar.Valid,ContinuationFamily.Valid,ContinuationFamily.Shapes,ContinuationFamily.User.Shape,
    users,LeadingReplayStar.converted,User.toControl,
    OriginControlNormalization.LeavesValid,OriginControlNormalization.Valid,OriginControlNormalization.Closed,
    ReplayControlFusion.Plan.All,LeadingReplayStar.replay,hlen]

theorem entry_valid : OriginControlNormalization.Valid [] (LeadingReplayStar.specs users) entry := by
  have hlen : (LeadingReplayStar.specs users).length=2 := (ContinuationFamily.emit_length 0 (LeadingReplayStar.converted users)).trans rfl
  simp [entry,OriginControlNormalization.Valid,hlen]

theorem normalized_none (x : List Char) (k : Nat) :
    evV normalized x .callByValuePar (tblV normalized x .callByValuePar k) [] (sourceRender [] users entry) x.length=none := by
  let step := MExp.seq (.seq (.lit []) (.param 0)) (.lit [])
  let fbody := MExp.seq (.seq (.star step) (.seq (.lit []) (.param 0))) (.lit ['z'])
  have hr : ruleAtM normalized.rules 0=some ⟨1,fbody⟩ := rfl
  have hb (T : ClockFreezing.Table) : evV normalized x .callByValuePar T [[]] fbody x.length=none := by
    have hs : evV normalized x .callByValuePar T [[]] step x.length=some (some x.length) := by
      simp only [step,evV,Shallot.stripPrefix?,List.getElem?_cons_zero,length_sfx x (Nat.le_refl _)]
    have hstar : evV normalized x .callByValuePar T [[]] (.star step) x.length=none := by
      rw [evV_star,evStar_stuck hs (by omega)]
    exact evV_seq_none (evV_seq_none hstar)
  change evV normalized x .callByValuePar (tblV normalized x .callByValuePar k) [] (.call 0 [.lit []]) x.length=none
  rw [evV_call_par hr rfl (by decide)]
  simp only [evParArgs,evV,Shallot.stripPrefix?,length_sfx x (Nat.le_refl _),pre,Nat.sub_self,List.take_zero]
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [[]] (Nat.le_refl _)]; exact hb _

theorem source_none (x : List Char) : ∀ k,
    evV raw x .callByValuePar (tblV raw x .callByValuePar k) [] (sourceRender [] users entry) x.length=none :=
  (BoundedBodyRewrite.undefined_iff (FoldedUserPrefix.related normalized 0 1 (.lit []) C checked)
    x [] (sourceRender [] users entry) x.length).mpr (normalized_none x)

theorem target_none (x : List Char) : ∀ k,
    evV target x .callByValueSeq (tblV target x .callByValueSeq k) []
      (LeadingReplayStar.targetRender [] users entry) x.length=none :=
  (FoldedUserPrefix.undefined_iff [] (by simp [RegularCaptureProduct.Valid]) users valid 0 1 (.lit []) C checked entry entry_valid x).mp
    (source_none x)

theorem non_replay_callee_rejected :
    FoldedUserPrefix.check ⟨[⟨1,ExpressionContext.plug (ReplayCallInlining.body (.lit [])) C⟩,⟨1,.lit []⟩]⟩
      0 1 (.lit []) C=false := by decide +kernel

end Shallot.MacroPeg.CBV.FoldedUserPrefixExamples.Nullable
