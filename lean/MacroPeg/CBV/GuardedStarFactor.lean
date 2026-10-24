import MacroPeg.CBV.GreedyRotation

/-! Expose the first A of a greedy (A B)* without requiring a final A.
Look ahead at the complete next iteration before rotating its A forward. -/
namespace Shallot.MacroPeg.CBV.GuardedStarFactor
open ContinuationPlan (sequence)
open GreedyRotation (Decreasing negative)

def eligible (A B : Nat → Res) (p : Nat) : Res :=
  match sequence A B p with | some (some _) => A p | other => other

/-- Once a complete first iteration has succeeded, rotate only those later
A's whose full A B iteration succeeds. This does not consume the A of a
failed final iteration. -/
theorem positive (n : Nat) (A B : Nat → Res) (hA : Decreasing n A) (hB : Decreasing n B) :
    ∀ p, p≤n → ∀ j k, A p=some (some j) → B j=some (some k) →
      evStar (sequence A B) p=sequence (evStar (sequence B (eligible A B))) B j := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp j k ha hb
    have hj := hA p hp j ha
    have hk := hB j (by omega) k hb
    have hab : sequence A B p=some (some k) := by simp only [sequence,ha,hb]
    by_cases hkp : k<p
    · rw [evStar_ok hab hkp]
      cases hx : sequence A B k with
      | none =>
        have hel : eligible A B k=none := by rw [eligible,hx]
        have hh : sequence B (eligible A B) j=none := by simp only [sequence,hb,hel]
        simp only [evStar_none hx,sequence,evStar_none hh]
      | some result => cases result with
        | none =>
          have hel : eligible A B k=some none := by rw [eligible,hx]
          have hh : sequence B (eligible A B) j=some none := by simp only [sequence,hb,hel]
          simp only [evStar_fail hx,sequence,evStar_fail hh,hb]
        | some l =>
          cases ham : A k with
          | none => simp [sequence,ham] at hx
          | some ar => cases ar with
            | none => simp [sequence,ham] at hx
            | some m =>
              have hbm : B m=some (some l) := by simpa only [sequence,ham] using hx
              have hi := ih k hkp (by omega) m l ham hbm
              have hm := hA k (by omega) m ham
              have hel : eligible A B k=some (some m) := by rw [eligible,hx]; exact ham
              have hh : sequence B (eligible A B) j=some (some m) := by simp only [sequence,hb,hel]
              by_cases hmj : m<j
              · change _=(match evStar (sequence B (eligible A B)) j with
                  | some (some z) => B z | other => other)
                rw [evStar_ok hh hmj]
                exact hi
              · have he : m=j := by omega
                subst m
                exact hi
    · have hk' : k=p := by omega
      have hj' : j=p := by omega
      subst k
      subst j
      have hel : eligible A B p=some (some p) := by rw [eligible,hab]; exact ha
      have hh : sequence B (eligible A B) p=some (some p) := by simp only [sequence,hb,hel]
      simp only [evStar_stuck hab (by omega),sequence,evStar_stuck hh (by omega)]

def factor (A B C : Nat → Res) (p : Nat) : Res :=
  ReplayFallbackFusion.orElse
    (sequence (eligible A B) (sequence (evStar (sequence B (eligible A B))) (sequence B C)) p)
    (sequence (negative (sequence A B)) C p)

theorem sequence_assoc (A B C : Nat → Res) (p : Nat) :
    sequence (sequence A B) C p=sequence A (sequence B C) p := by
  unfold sequence
  cases A p with
  | none => rfl
  | some result => cases result <;> rfl

/-- Complete partial-result identity for `(A B)* C`, not just accepted words. -/
theorem correct (n : Nat) (A B C : Nat → Res) (hA : Decreasing n A) (hB : Decreasing n B)
    (p : Nat) (hp : p≤n) : sequence (evStar (sequence A B)) C p=factor A B C p := by
  cases hx : sequence A B p with
  | none =>
    have hel : eligible A B p=none := by rw [eligible,hx]
    simp only [factor,sequence,hel,evStar_none hx,ReplayFallbackFusion.orElse]
  | some result => cases result with
    | none =>
      have hel : eligible A B p=some none := by rw [eligible,hx]
      have hn : negative (sequence A B) p=some (some p) := by rw [negative,hx]
      simp only [factor,sequence,hel,hn,evStar_fail hx,ReplayFallbackFusion.orElse]
    | some k =>
      cases ha : A p with
      | none => simp [sequence,ha] at hx
      | some ar => cases ar with
        | none => simp [sequence,ha] at hx
        | some j =>
          have hb : B j=some (some k) := by simpa only [sequence,ha] using hx
          have hs := positive n A B hA hB p hp j k ha hb
          have hel : eligible A B p=some (some j) := by rw [eligible,hx]; exact ha
          have hn : negative (sequence A B) p=some none := by rw [negative,hx]
          unfold factor
          simp only [sequence,hel,hn]
          rw [hs]
          change sequence (sequence (evStar (sequence B (eligible A B))) B) C j=
            ReplayFallbackFusion.orElse (sequence (evStar (sequence B (eligible A B))) (sequence B C) j) (some none)
          rw [sequence_assoc]
          cases sequence (evStar (sequence B (eligible A B))) (sequence B C) j with
          | none => rfl
          | some r => cases r <;> rfl


def guarded (A B C : Nat → Res) (p : Nat) : Res :=
  ReplayFallbackFusion.orElse
    (match sequence A B p with
      | some (some _) => sequence A (sequence (evStar (sequence B (eligible A B))) (sequence B C)) p
      | other => other)
    (sequence (negative (sequence A B)) C p)

theorem factor_guarded (A B C : Nat → Res) (p : Nat) : factor A B C p=guarded A B C p := by
  apply congrArg (fun r => ReplayFallbackFusion.orElse r (sequence (negative (sequence A B)) C p))
  change (match eligible A B p with
    | some (some j) => sequence (evStar (sequence B (eligible A B))) (sequence B C) j
    | other => other)=_
  rw [eligible]
  cases sequence A B p with
  | none => rfl
  | some result => cases result <;> rfl

theorem correct_guarded (n : Nat) (A B C : Nat → Res) (hA : Decreasing n A) (hB : Decreasing n B)
    (p : Nat) (hp : p≤n) : sequence (evStar (sequence A B)) C p=guarded A B C p :=
  (correct n A B C hA hB p hp).trans (factor_guarded A B C p)

/-- All guards and repeats are actual inline expressions. -/
def expression (A B C : MExp) : MExp :=
  let G := .seq (.andP (.seq A B)) A
  .alt (.seq G (.seq (.star (.seq B G)) (.seq B C))) (.seq (.notP (.seq A B)) C)

theorem eligible_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (A B : MExp) (p : Nat) :
    evV g x s T E (.seq (.andP (.seq A B)) A) p=
    eligible (fun q => evV g x s T E A q) (fun q => evV g x s T E B q) p := by
  change (match evV g x s T E (.andP (.seq A B)) p with
    | some (some j) => evV g x s T E A j | other => other)=_
  rw [CallLookahead.evV_peek]
  unfold eligible
  change (match CallLookahead.peek p (evV g x s T E (.seq A B) p) with
    | some (some j) => evV g x s T E A j | other => other)=
    (match evV g x s T E (.seq A B) p with | some (some _) => evV g x s T E A p | other => other)
  cases evV g x s T E (.seq A B) p with
  | none => rfl
  | some r => cases r <;> rfl

theorem expression_eq (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (A B C : MExp)
    (ha : A.FirstOrder) (hb : B.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.star (.seq A B)) C) p=evV g x s T E (expression A B C) p := by
  have he := correct x.length (fun q => evV g x s T E A q) (fun q => evV g x s T E B q)
    (fun q => evV g x s T E C q)
    (GreedyRotation.evaluator_decreasing g x s hs T hT E A ha)
    (GreedyRotation.evaluator_decreasing g x s hs T hT E B hb) p hp
  let G : MExp := .seq (.andP (.seq A B)) A
  have hg : (fun q => evV g x s T E G q)=eligible (fun q => evV g x s T E A q) (fun q => evV g x s T E B q) := by
    funext q
    exact eligible_eval g x s T E A B q
  change sequence (evStar (sequence (fun q => evV g x s T E A q) (fun q => evV g x s T E B q)))
      (fun q => evV g x s T E C q) p=
    ReplayFallbackFusion.orElse
      (sequence (fun q => evV g x s T E G q)
        (sequence (evStar (sequence (fun q => evV g x s T E B q) (fun q => evV g x s T E G q)))
          (sequence (fun q => evV g x s T E B q) (fun q => evV g x s T E C q))) p)
      (sequence (negative (sequence (fun q => evV g x s T E A q) (fun q => evV g x s T E B q)))
        (fun q => evV g x s T E C q) p)
  rw [hg]
  exact he

end Shallot.MacroPeg.CBV.GuardedStarFactor
