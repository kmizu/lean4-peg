import MacroPeg.CBV.MixedAdjacentRecursive

namespace Shallot.MacroPeg.CBV.MixedAdjacentSyntax
open MixedAdjacentRecursive
open AdjacentCallsiteRecursive (Header Argument argument)

/-- Direct ordinary source calls, including recursive user calls inside
an arbitrary replay user's actual argument. -/
def sourceExpr (H : Header) : Body H → MExp
  | .call i a => .call (i+1) [argument H a]
  | .replay i a => .call (i+1) [sourceExpr H a]
  | .seq a b => .seq (sourceExpr H a) (sourceExpr H b)
  | .alt a b => .alt (sourceExpr H a) (sourceExpr H b)
  | .star a => .star (sourceExpr H a)
  | .notP a => .notP (sourceExpr H a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w

/-- Check only callee existence and which of the two source entry shapes
it uses. Actual arguments to replay users have arbitrary Body syntax. -/
def WellTyped {H : Header} (tails : List (Spec H)) : Body H → Prop
  | .call i _ => ∃ r, tails[i]?=some r ∧ r.split=true
  | .replay i a => (∃ r, tails[i]?=some r ∧ r.split=false) ∧ WellTyped tails a
  | .seq a b | .alt a b => WellTyped tails a ∧ WellTyped tails b
  | .star a | .notP a => WellTyped tails a
  | _ => True

theorem source_syntax (H : Header) (tails : List (Spec H)) :
    ∀ e, WellTyped tails e → ∀ split, render H tails true split e=sourceExpr H e
  | .call i a, ⟨r,hr,hkind⟩, split => by simp only [render,hr,hkind,ite_true,sourceExpr]
  | .replay i a, ⟨⟨r,hr,hkind⟩,ha⟩, split => by
    simp only [render,hr,hkind,Bool.false_eq_true,ite_false,sourceExpr,source_syntax H tails a ha split]
  | .seq a b, h, split | .alt a b, h, split => by
    simp only [render,sourceExpr,source_syntax H tails a h.1 split,source_syntax H tails b h.2 split]
  | .star a, h, split | .notP a, h, split => by
    simp only [render,sourceExpr,source_syntax H tails a h split]
  | .param _, _, _ | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _ => rfl

def original (H : Header) (tails : List (Spec H)) : MGrammar :=
  ⟨⟨1,.param 0⟩::tails.map (fun r => ⟨1,.seq (sourcePrefix H r.split) (sourceExpr H r.body)⟩)⟩

theorem source_eq_original (H : Header) (tails : List (Spec H))
    (hs : ∀ r∈tails, WellTyped tails r.body) : source H tails=original H tails := by
  unfold source original
  congr 2
  apply List.map_congr_left
  intro r hr
  rw [source_syntax H tails r.body (hs r hr) r.split]

theorem original_firstOrder (H : Header) (tails : List (Spec H))
    (hs : ∀ r∈tails, WellTyped tails r.body) : (original H tails).FirstOrder := by
  rw [←source_eq_original H tails hs]
  exact source_firstOrder H tails

theorem sourceExpr_firstOrder (H : Header) (tails : List (Spec H))
    (e : Body H) (he : WellTyped tails e) : (sourceExpr H e).FirstOrder := by
  rw [←source_syntax H tails e he false]
  exact render_firstOrder H tails true false e

theorem original_observations (H : Header) (tails : List (Spec H))
    (hs : ∀ r∈tails, WellTyped tails r.body) (e : Body H) (he : WellTyped tails e)
    (x : List Char) (r : Option (List Char)) :
    SObs (original H tails) .callByValuePar (sourceExpr H e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false false e) x r := by
  have hh := observations_iff H tails e x r
  rw [source_eq_original H tails hs,source_syntax H tails e he false] at hh
  exact hh

theorem original_language_translation (H : Header) (tails : List (Spec H))
    (hs : ∀ r∈tails, WellTyped tails r.body) (e : Body H) (he : WellTyped tails e) :
    ∃ (g : MGrammar) (start : MExp),
      (original H tails).FirstOrder ∧ (sourceExpr H e).FirstOrder ∧
      g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (original H tails) .callByValuePar (sourceExpr H e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target H tails,render H tails false false e,original_firstOrder H tails hs,
    sourceExpr_firstOrder H tails e he,target_firstOrder H tails,render_firstOrder H tails false false e,
    fun x => original_observations H tails hs e he x (some [])⟩

end Shallot.MacroPeg.CBV.MixedAdjacentSyntax
