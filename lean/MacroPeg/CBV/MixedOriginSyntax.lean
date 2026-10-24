import MacroPeg.CBV.MixedOriginControl

/-! Connect origin-control normalization to ordinary original call syntax.
No evaluation relation is required from the user of the translation. -/
namespace Shallot.MacroPeg.CBV.MixedOriginSyntax
open AdjacentCallsiteRecursive (Header argument)
open MixedAdjacentRecursive (Body)
open MixedOriginControl

def sourceExpr {H : Header} : Body H → MExp
  | .call i a => .call (i+1) [argument H a]
  | .replay i a => .call (i+1) [sourceExpr a]
  | .seq a b => .seq (sourceExpr a) (sourceExpr b)
  | .alt a b => .alt (sourceExpr a) (sourceExpr b)
  | .star a => .star (sourceExpr a)
  | .notP a => .notP (sourceExpr a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w

def WellTyped {H : Header} (specs : List Spec) : Body H → Prop
  | .call i _ => ∃ s, specs[i]?=some s ∧ s.split=true
  | .replay i a => (∃ s, specs[i]?=some s ∧ s.split=false) ∧ WellTyped specs a
  | .seq a b | .alt a b => WellTyped specs a ∧ WellTyped specs b
  | .star a | .notP a => WellTyped specs a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => True

theorem source_syntax (H : Header) (specs : List Spec) :
    ∀ e, WellTyped specs e → render H specs e=sourceExpr e
  | .call i a, h => by
    obtain ⟨s,hr,hs⟩ := h
    simp only [render,sourceExpr,hr,hs,ite_true]
  | .replay i a, h => by
    obtain ⟨s,hr,hs⟩ := h.1
    simp only [render,sourceExpr,hr,hs,Bool.false_eq_true,ite_false,source_syntax H specs a h.2]
  | .seq a b, h | .alt a b, h => by simp only [render,sourceExpr,source_syntax H specs a h.1,source_syntax H specs b h.2]
  | .star a, h | .notP a, h => by simp only [render,sourceExpr,source_syntax H specs a h]
  | .param _, _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => rfl

def originalLeaf (H : Header) (parts : List (Part H)) (i : Nat) : MExp :=
  match parts[i]? with
  | none => MExp.failAlways
  | some r => if r.stuck then .star .eps else .seq (MixedAdjacentRecursive.sourcePrefix H r.split) (sourceExpr r.body)
def original (H : Header) (parts : List (Part H)) (specs : List Spec) : MGrammar :=
  ⟨⟨1,.param 0⟩::specs.map (fun s => ⟨1,s.plan.exp (originalLeaf H parts)⟩)⟩

theorem source_eq_original (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hBodies : ∀ r∈parts, WellTyped specs r.body) : source H parts specs=original H parts specs := by
  have hleaf : sourceLeaf H parts specs=originalLeaf H parts := by
    funext j
    unfold sourceLeaf originalLeaf
    cases hr : parts[j]? with
    | none => rfl
    | some r => simp only [source_syntax H specs r.body (hBodies r (List.mem_of_getElem? hr))]
  simp only [source,original,hleaf]

theorem original_firstOrder (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hBodies : ∀ r∈parts, WellTyped specs r.body) : (original H parts specs).FirstOrder := by
  rw [←source_eq_original H parts specs hBodies]
  exact source_firstOrder H parts specs

theorem sourceExpr_firstOrder (H : Header) (specs : List Spec) (e : Body H) (he : WellTyped specs e) :
    (sourceExpr e).FirstOrder := by
  rw [←source_syntax H specs e he]
  exact render_firstOrder H specs e

theorem original_observations (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (hBodies : ∀ r∈parts, WellTyped specs r.body)
    (e : Body H) (he : WellTyped specs e) (x : List Char) (r : Option (List Char)) :
    SObs (original H parts specs) .callByValuePar (sourceExpr e) x r ↔
    SObs (target H parts specs) .callByValueSeq (targetRender H parts specs e) x r := by
  rw [←source_eq_original H parts specs hBodies,←source_syntax H specs e he]
  exact observations_iff H parts specs hValid e x r

/-- The unchanged original language has one fixed first-order Seq
translation. All premises inspect syntax or rule kinds. -/
theorem original_language_translation (H : Header) (parts : List (Part H)) (specs : List Spec)
    (hValid : Valid H parts specs) (hBodies : ∀ r∈parts, WellTyped specs r.body)
    (e : Body H) (he : WellTyped specs e) :
    (original H parts specs).FirstOrder ∧ (sourceExpr e).FirstOrder ∧
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (original H parts specs) .callByValuePar (sourceExpr e) x (some []) ↔
      SObs g .callByValueSeq start x (some []) :=
  ⟨original_firstOrder H parts specs hBodies,sourceExpr_firstOrder H specs e he,
    target H parts specs,targetRender H parts specs e,
    MixedAdjacentRecursive.target_firstOrder H _,MixedAdjacentRecursive.render_firstOrder H _ false false _,
    fun x => original_observations H parts specs hValid hBodies e he x (some [])⟩

end Shallot.MacroPeg.CBV.MixedOriginSyntax
