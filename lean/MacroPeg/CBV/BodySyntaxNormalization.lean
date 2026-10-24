import MacroPeg.CBV.NullableStarControl

namespace Shallot.MacroPeg.CBV.BodySyntaxNormalization
open OriginControlNormalization (Leaf render)
open BodyNormalForm (Form)
open RegularCaptureProduct (Node)
open ContinuationPlan (sequence)
abbrev Arg := RecursiveArgumentCompiler.Expr

/-- Recursive source syntax. Sequential and predicate structure is supplied
before normalization, not reconstructed from a preselected leaf layout. -/
inductive Body where
  | leaf : Leaf → Body
  | alt : Body → Body → Body
  | notP : Body → Body
  | seq : Body → Body → Body
  | starThen : Body → Arg → Body → Body
  | star : Body → Body

def Body.expression : Body → Arg
  | .leaf r => LeafContinuation.raw r
  | .alt a b => .alt a.expression b.expression
  | .notP a => .notP a.expression
  | .seq a b => .seq a.expression b.expression
  | .starThen a B c => .seq (.star (.seq a.expression B)) c.expression
  | .star a => .star a.expression

def normalize : Body → Form
  | .leaf r => BodyNormalForm.atom r
  | .alt a b => BodyNormalForm.choice (normalize a) (normalize b)
  | .notP a => BodyNormalForm.neg (normalize a)
  | .seq a b => BodyNormalForm.compose (normalize a) (normalize b)
  | .starThen a B c => BodyNormalForm.repeatThen (normalize a) B (normalize c)
  | .star a => NullableStarControl.iterate (normalize a)

/-- This is a check on generated finite syntax. It does not assert any
semantic equivalence or success of a replacement parser. -/
def Ready : Body → Prop
  | .leaf _ => True
  | .alt a b | .seq a b => Ready a ∧ Ready b
  | .notP a | .star a => Ready a
  | .starThen a _ c => Ready a ∧ Ready c ∧ LeafContinuation.Consumer (normalize a).plan

/-- Rewriting a bounded parser on the left of a sequence requires agreement
on every reachable endpoint, including empty success. -/
theorem sequence_congr (n : Nat) (a a' b b' : Nat → Res)
    (ha : ∀ q, q≤n → a q=a' q) (hb : ∀ q, q≤n → b q=b' q)
    (hdec : GreedyRotation.Decreasing n a') (p : Nat) (hp : p≤n) :
    sequence a b p=sequence a' b' p := by
  simp only [sequence,ha p hp]
  cases h : a' p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some q => exact hb q (Nat.le_trans (hdec p hp q h) hp)

/-- Full partial evaluator preservation at every valid physical position. -/
theorem evaluator_eq (nodes : List Node) (ambient : List Leaf) (ps : List ReplayControlFusion.Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) :
    ∀ b, Ready b → ∀ p, p≤x.length →
    evV g x s T E (render nodes ambient ps b.expression) p=
    evV g x s T E (render nodes ambient ps (normalize b).syntax) p
  | .leaf r, _, _, _ => rfl
  | .alt a b, hr, p, hp => by
    rw [normalize,BodyNormalForm.choice_syntax]
    change ReplayFallbackFusion.orElse
      (evV g x s T E (render nodes ambient ps a.expression) p)
      (evV g x s T E (render nodes ambient ps b.expression) p)=_
    rw [evaluator_eq nodes ambient ps g x s hs T hT E a hr.1 p hp,
      evaluator_eq nodes ambient ps g x s hs T hT E b hr.2 p hp]
    rfl
  | .notP a, hr, p, hp => by
    rw [normalize,BodyNormalForm.neg_syntax]
    change (match evV g x s T E (render nodes ambient ps a.expression) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [evaluator_eq nodes ambient ps g x s hs T hT E a hr p hp]
    rfl
  | .seq a b, hr, p, hp => by
    rw [normalize,BodyNormalForm.compose_eval]
    exact sequence_congr x.length _ _ _ _
      (evaluator_eq nodes ambient ps g x s hs T hT E a hr.1)
      (evaluator_eq nodes ambient ps g x s hs T hT E b hr.2)
      (GreedyRotation.evaluator_decreasing g x s hs T hT E _
        (OriginControlNormalization.render_firstOrder nodes ambient ps (normalize a).syntax)) p hp
  | .starThen a B c, hr, p, hp => by
    rw [normalize,←BodyNormalForm.repeatThen_eval nodes ambient ps _ _ B hr.2.2 g x s hs T hT E p hp]
    have hstar : ∀ q, q≤x.length →
        evV g x s T E (render nodes ambient ps (.star (.seq a.expression B))) q=
        evV g x s T E (render nodes ambient ps (.star (.seq (normalize a).syntax B))) q := by
      intro q hq
      apply evStar_congr q
      intro z hz
      change sequence (fun w => evV g x s T E (render nodes ambient ps a.expression) w)
        (fun w => evV g x s T E (render nodes ambient ps B) w) z=_
      rw [sequence,evaluator_eq nodes ambient ps g x s hs T hT E a hr.1 z (by omega)]
      rfl
    exact sequence_congr x.length _ _ _ _ hstar
      (evaluator_eq nodes ambient ps g x s hs T hT E c hr.2.1)
      (GreedyRotation.evaluator_decreasing g x s hs T hT E _
        (OriginControlNormalization.render_firstOrder nodes ambient ps (.star (.seq (normalize a).syntax B)))) p hp

  | .star a, hr, p, hp => by
    rw [normalize,←NullableStarControl.repeat_eval nodes ambient ps _ g x s hs T hT E p hp]
    apply evStar_congr p
    intro q hq
    exact evaluator_eq nodes ambient ps g x s hs T hT E a hr q (by omega)

end Shallot.MacroPeg.CBV.BodySyntaxNormalization
