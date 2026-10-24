import MacroPeg.CBV.BodySyntaxCompiler

/-! Derive a source-body view directly from ordinary argument syntax.
Recognized replay heads are syntax, not supplied equivalence certificates. -/
namespace Shallot.MacroPeg.CBV.ArgumentBodyView
open BodySyntaxNormalization (Body Ready)
open OriginControlNormalization (Leaf render)
open RegularCaptureProduct (Node)
open ContinuationPlan (sequence)
abbrev Arg := RecursiveArgumentCompiler.Expr

def replayHead : Arg → Arg → Option Leaf
  | .param 0, b => some ⟨some [],b⟩
  | .lit u, .param 0 => some ⟨some u,NullableStarControl.identity⟩
  | .lit u, .seq (.param 0) b => some ⟨some u,b⟩
  | _, _ => none

def view : Arg → Body
  | .lit w => .leaf ⟨none,.lit w⟩
  | .param 0 => .leaf ⟨some [],NullableStarControl.identity⟩
  | .param (k+1) => .leaf ⟨none,.param (k+1)⟩
  | .helper i => .leaf ⟨none,.helper i⟩
  | .user i a => .leaf ⟨none,.user i a⟩
  | .seq a b => match replayHead a b with
    | some r => .leaf r
    | none => .seq (view a) (view b)
  | .alt a b => .alt (view a) (view b)
  | .notP a => .notP (view a)
  | .star a => .star (view a)

theorem ready : ∀ a, Ready (view a)
  | .lit _ | .param 0 | .param (_+1) | .helper _ | .user _ _ => trivial
  | .alt a b => ⟨ready a,ready b⟩
  | .notP a | .star a => ready a
  | .seq a b => by
    unfold view
    split
    · trivial
    · exact ⟨ready a,ready b⟩

theorem empty_literal (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.lit []) p=some (some p) := by
  have hlen : (sfx x p).length=p := by simp [sfx]; omega
  change some (some (sfx x p).length)=_
  rw [hlen]

/-- Padding a replay with an initial empty literal and a final positive
empty test preserves the actual partial parser at valid positions. -/
theorem bare_replay (nodes : List Node) (ambient : List Leaf) (ps : List ReplayControlFusion.Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.param 0) p=
    evV g x s T E (render nodes ambient ps (LeafContinuation.raw ⟨some [],NullableStarControl.identity⟩)) p := by
  have hi : (fun q => evV g x s T E (render nodes ambient ps NullableStarControl.identity) q)=
      (fun q => some (some q)) := by
    funext q; exact NullableStarControl.identity_eval nodes ambient ps g x s T E q
  change _=sequence (sequence (fun q => evV g x s T E (.lit []) q)
    (fun q => evV g x s T E (.param 0) q))
    (fun q => evV g x s T E (render nodes ambient ps NullableStarControl.identity) q) p
  rw [hi,NullableStarControl.sequence_identity]
  simp only [sequence,empty_literal g x s T E p hp]

theorem replayHead_eval (nodes : List Node) (ambient : List Leaf) (ps : List ReplayControlFusion.Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) (a b : Arg) (r : Leaf) (h : replayHead a b=some r) :
    evV g x s T E (render nodes ambient ps (.seq a b)) p=
    evV g x s T E (render nodes ambient ps (LeafContinuation.raw r)) p := by
  cases a with
  | param k =>
    cases k with
    | zero =>
      simp only [replayHead,Option.some.injEq] at h
      subst r
      change _=(match evV g x s T E (.lit []) p with
        | some (some j) => evV g x s T E (render nodes ambient ps (.seq (.param 0) b)) j
        | other => other)
      rw [empty_literal g x s T E p hp]
    | succ k => simp [replayHead] at h
  | lit u =>
    cases b with
    | param k =>
      cases k with
      | zero =>
        simp only [replayHead,Option.some.injEq] at h
        subst r
        have hi : (fun q => evV g x s T E (render nodes ambient ps NullableStarControl.identity) q)=
            (fun q => some (some q)) := by
          funext q; exact NullableStarControl.identity_eval nodes ambient ps g x s T E q
        change _=sequence (fun q => evV g x s T E (.seq (.lit u) (.param 0)) q)
          (fun q => evV g x s T E (render nodes ambient ps NullableStarControl.identity) q) p
        rw [hi,NullableStarControl.sequence_identity]
        rfl
      | succ k => simp [replayHead] at h
    | seq b c =>
      cases b with
      | param k =>
        cases k with
        | zero =>
          simp only [replayHead,Option.some.injEq] at h
          subst r
          exact (GuardedStarFactor.sequence_assoc (fun q => evV g x s T E (.lit u) q)
            (fun q => evV g x s T E (.param 0) q)
            (fun q => evV g x s T E (render nodes ambient ps c) q) p).symm
        | succ k => simp [replayHead] at h
      | lit _ | helper _ | user _ _ | seq _ _ | alt _ _ | star _ | notP _ => simp [replayHead] at h
    | lit _ | helper _ | user _ _ | alt _ _ | star _ | notP _ => simp [replayHead] at h
  | helper _ | user _ _ | seq _ _ | alt _ _ | star _ | notP _ => simp [replayHead] at h

/-- The automatically generated view has exactly the original evaluator;
no syntax validity/closedness assumption is needed for this local bridge. -/
theorem evaluator_eq (nodes : List Node) (ambient : List Leaf) (ps : List ReplayControlFusion.Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) :
    ∀ a, ∀ p, p≤x.length → evV g x s T E (render nodes ambient ps a) p=
      evV g x s T E (render nodes ambient ps (view a).expression) p
  | .lit _, _, _ | .param (_+1), _, _ | .helper _, _, _ | .user _ _, _, _ => rfl
  | .param 0, p, hp => bare_replay nodes ambient ps g x s T E p hp
  | .alt a b, p, hp => by
    change ReplayFallbackFusion.orElse
      (evV g x s T E (render nodes ambient ps a) p) (evV g x s T E (render nodes ambient ps b) p)=_
    rw [evaluator_eq nodes ambient ps g x s hs T hT E a p hp,
      evaluator_eq nodes ambient ps g x s hs T hT E b p hp]
    rfl
  | .notP a, p, hp => by
    change (match evV g x s T E (render nodes ambient ps a) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [evaluator_eq nodes ambient ps g x s hs T hT E a p hp]
    rfl
  | .star a, p, hp => by
    apply evStar_congr p
    intro q hq
    exact evaluator_eq nodes ambient ps g x s hs T hT E a q (by omega)
  | .seq a b, p, hp => by
    cases hr : replayHead a b with
    | some r =>
      have hv : (view (.seq a b)).expression=LeafContinuation.raw r := by simp [view,hr,Body.expression]
      rw [hv]
      exact replayHead_eval nodes ambient ps g x s T E p hp a b r hr
    | none =>
      have hv : (view (.seq a b)).expression=.seq (view a).expression (view b).expression := by simp [view,hr,Body.expression]
      rw [hv]
      exact BodySyntaxNormalization.sequence_congr x.length _ _ _ _
        (evaluator_eq nodes ambient ps g x s hs T hT E a)
        (evaluator_eq nodes ambient ps g x s hs T hT E b)
        (GreedyRotation.evaluator_decreasing g x s hs T hT E _
          (OriginControlNormalization.render_firstOrder nodes ambient ps (view a).expression)) p hp

end Shallot.MacroPeg.CBV.ArgumentBodyView
