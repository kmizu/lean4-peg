import MacroPeg.CBV.ContinuationPlan

/-! PEG repetition rotates only with its stopping test. Preserve complete
partial results, including recursive undefinedness and zero-consumption loops. -/
namespace Shallot.MacroPeg.CBV.GreedyRotation
open ContinuationPlan (sequence)

def negative (f : Nat → Res) (p : Nat) : Res :=
  match f p with | some (some _) => some none | some none => some (some p) | none => none

def Decreasing (n : Nat) (f : Nat → Res) : Prop :=
  ∀ p, p≤n → ∀ j, f p=some (some j) → j≤p

/-- `(A B)* A = A (B A)* !B` for deterministic partial parsers. The extra
negative test is essential when B succeeds but the next A fails. -/
theorem rotate (n : Nat) (A B : Nat → Res) (hA : Decreasing n A) (hB : Decreasing n B) :
    ∀ p, p≤n → sequence (evStar (sequence A B)) A p=
      sequence A (sequence (evStar (sequence B A)) (negative B)) p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    cases ha : A p with
    | none =>
      have hab : sequence A B p=none := by simp only [sequence,ha]
      rw [show sequence (evStar (sequence A B)) A p=none by rw [sequence,evStar_none hab]]
      simp only [sequence,ha]
    | some ar => cases ar with
      | none =>
        have hab : sequence A B p=some none := by simp only [sequence,ha]
        simp only [sequence,evStar_fail hab,ha]
      | some j =>
        have hj := hA p hp j ha
        cases hb : B j with
        | none =>
          have hab : sequence A B p=none := by simp only [sequence,ha,hb]
          have hba : sequence B A j=none := by simp only [sequence,hb]
          simp only [sequence,ha,evStar_none hab,evStar_none hba]
        | some br => cases br with
          | none =>
            have hab : sequence A B p=some none := by simp only [sequence,ha,hb]
            have hba : sequence B A j=some none := by simp only [sequence,hb]
            simp only [sequence,ha,evStar_fail hab,evStar_fail hba,negative,hb]
          | some k =>
            have hk := hB j (by omega) k hb
            have hab : sequence A B p=some (some k) := by simp only [sequence,ha,hb]
            by_cases hkp : k<p
            · have hi := ih k hkp (by omega)
              change (match evStar (sequence A B) p with | some (some z) => A z | other => other)=_
              rw [evStar_ok hab hkp]
              change sequence (evStar (sequence A B)) A k=_
              rw [hi]
              simp only [sequence,ha]
              cases hc : A k with
              | none =>
                have hba : sequence B A j=none := by simp only [sequence,hb,hc]
                simp only [evStar_none hba]
              | some cr => cases cr with
                | none =>
                  have hba : sequence B A j=some none := by simp only [sequence,hb,hc]
                  simp only [evStar_fail hba,negative,hb]
                | some l =>
                  have hl := hA k (by omega) l hc
                  have hba : sequence B A j=some (some l) := by simp only [sequence,hb,hc]
                  by_cases hlj : l<j
                  · rw [evStar_ok hba hlj]
                  · have he : l=j := by omega
                    subst l
                    have hkj : k=j := by omega
                    subst k
                    dsimp only []
            · have hkp' : k=p := by omega
              have hjp : j=p := by omega
              subst k
              subst j
              have hba : sequence B A p=some (some p) := by simp only [sequence,hb,ha]
              simp only [sequence,ha,evStar_stuck hab (by omega),evStar_stuck hba (by omega)]

theorem evaluator_decreasing (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) :
    Decreasing x.length (fun p => evV g x s T E e p) := by
  intro p hp j hj
  have h := WordStarFilter.success_prefix hs hT E e he p j hp hj
  have hl := congrArg List.length h.2
  rw [List.length_append,length_sfx x hp,length_sfx x h.1] at hl
  omega

theorem expression_eq (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (A B : MExp)
    (hA : A.FirstOrder) (hB : B.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (.star (.seq A B)) A) p=
    evV g x s T E (.seq A (.seq (.star (.seq B A)) (.notP B))) p := by
  exact rotate x.length (fun q => evV g x s T E A q) (fun q => evV g x s T E B q)
    (evaluator_decreasing g x s hs T hT E A hA) (evaluator_decreasing g x s hs T hT E B hB) p hp

end Shallot.MacroPeg.CBV.GreedyRotation
