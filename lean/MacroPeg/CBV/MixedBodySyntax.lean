import MacroPeg.CBV.MixedBodyStar
import MacroPeg.CBV.BodySyntaxNormalization

namespace Shallot.MacroPeg.CBV.MixedBodySyntax
open AdjacentCallsiteRecursive (Header)
open MixedAdjacentRecursive (Body)
open MixedOriginControl (Part Spec render)
open MixedBodyForm (Form)
open ContinuationPlan (sequence)
open BodySyntaxNormalization (sequence_congr)
variable {H : Header}

inductive Expression (H : Header) where
  | leaf : Part H → Expression H
  | alt : Expression H → Expression H → Expression H
  | notP : Expression H → Expression H
  | seq : Expression H → Expression H → Expression H
  | star : Expression H → Expression H

def Expression.body : Expression H → Body H
  | .leaf r => MixedBodyLeaves.raw r
  | .alt a b => .alt a.body b.body
  | .notP a => .notP a.body
  | .seq a b => .seq a.body b.body
  | .star a => .star a.body

def normalize : Expression H → Form H
  | .leaf r => MixedBodyForm.atom r
  | .alt a b => MixedBodyForm.choice (normalize a) (normalize b)
  | .notP a => MixedBodyForm.neg (normalize a)
  | .seq a b => MixedBodyForm.compose (normalize a) (normalize b)
  | .star a => MixedBodyStar.iterate (normalize a)

/-- Full partial evaluator preservation at every valid physical position. -/
theorem evaluator_eq (H : Header) (ps : List Spec)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) :
    ∀ b, ∀ p, p≤x.length →
    evV g x s T E (render H ps b.body) p=
    evV g x s T E (render H ps (normalize b).syntax) p
  | .leaf r, _, _ => rfl
  | .alt a b, p, hp => by
    rw [normalize,MixedBodyForm.choice_syntax]
    change ReplayFallbackFusion.orElse
      (evV g x s T E (render H ps a.body) p)
      (evV g x s T E (render H ps b.body) p)=_
    rw [evaluator_eq H ps g x s hs T hT E a p hp,
      evaluator_eq H ps g x s hs T hT E b p hp]
    rfl
  | .notP a, p, hp => by
    rw [normalize,MixedBodyForm.neg_syntax]
    change (match evV g x s T E (render H ps a.body) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [evaluator_eq H ps g x s hs T hT E a p hp]
    rfl
  | .seq a b, p, hp => by
    rw [normalize,MixedBodyForm.compose_eval]
    exact sequence_congr x.length _ _ _ _
      (evaluator_eq H ps g x s hs T hT E a)
      (evaluator_eq H ps g x s hs T hT E b)
      (GreedyRotation.evaluator_decreasing g x s hs T hT E _
        (MixedOriginControl.render_firstOrder H ps (normalize a).syntax)) p hp

  | .star a, p, hp => by
    rw [normalize,←MixedBodyStar.repeat_eval H ps _ g x s hs T hT E p hp]
    apply evStar_congr p
    intro q hq
    exact evaluator_eq H ps g x s hs T hT E a q (by omega)

/-- Only ordinary replay leaves in a general-capture user's source body.
Generated divergence leaves are independent of its capture. -/
def Ordinary : Expression H → Prop
  | .leaf r => r.split=false ∨ r.stuck=true
  | .alt a b | .seq a b => Ordinary a ∧ Ordinary b
  | .notP a | .star a => Ordinary a

private theorem copies_ordinary (ls : List (Part H)) (P : ReplayControlFusion.Plan) (K : Body H)
    (h : ∀ r∈ls, r.split=false ∨ r.stuck=true) :
    ∀ r∈MixedBodyLeaves.copies ls P K, r.split=false ∨ r.stuck=true := by
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
  have hi' : i<ls.length := by simpa [MixedBodyLeaves.copies] using hi
  simp only [MixedBodyLeaves.copies,List.getElem_mapIdx]
  split <;> exact h ls[i] (List.getElem_mem hi')

private theorem append_ordinary (ls rs : List (Part H))
    (hl : ∀ r∈ls, r.split=false ∨ r.stuck=true)
    (hr : ∀ r∈rs, r.split=false ∨ r.stuck=true) :
    ∀ r∈ls++rs, r.split=false ∨ r.stuck=true := by
  intro r h
  rcases List.mem_append.mp h with h|h
  · exact hl r h
  · exact hr r h

private theorem compose_ordinary (f g : Form H)
    (hf : ∀ r∈f.leaves, r.split=false ∨ r.stuck=true)
    (hg : ∀ r∈g.leaves, r.split=false ∨ r.stuck=true) :
    ∀ r∈(MixedBodyForm.compose f g).leaves, r.split=false ∨ r.stuck=true := by
  have hj := append_ordinary _ _ hf hg
  exact append_ordinary _ _ hj (copies_ordinary _ _ _ hj)

private theorem repeatThen_ordinary (f g : Form H) (B : Body H)
    (hf : ∀ r∈f.leaves, r.split=false ∨ r.stuck=true)
    (hg : ∀ r∈g.leaves, r.split=false ∨ r.stuck=true) :
    ∀ r∈(MixedBodyForm.repeatThen f B g).leaves, r.split=false ∨ r.stuck=true := by
  have hj := append_ordinary _ _ hf hg
  exact append_ordinary _ _ (append_ordinary _ _ hj (copies_ordinary _ _ _ hj))
    (copies_ordinary _ _ _ hj)

theorem normalize_ordinary : ∀ e : Expression H, Ordinary e →
    ∀ r∈(normalize e).leaves, r.split=false ∨ r.stuck=true
  | .leaf r, h => by intro v hv; obtain rfl := List.mem_singleton.mp hv; exact h
  | .notP a, h => normalize_ordinary a h
  | .alt a b, h => append_ordinary _ _ (normalize_ordinary a h.1) (normalize_ordinary b h.2)
  | .seq a b, h => compose_ordinary _ _ (normalize_ordinary a h.1) (normalize_ordinary b h.2)
  | .star a, h => by
    have hf : ∀ r∈(MixedBodyStar.strict (normalize a)).leaves, r.split=false ∨ r.stuck=true := by
      apply append_ordinary _ _ (normalize_ordinary a h)
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    apply repeatThen_ordinary _ _ _ hf
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inl rfl

end Shallot.MacroPeg.CBV.MixedBodySyntax
