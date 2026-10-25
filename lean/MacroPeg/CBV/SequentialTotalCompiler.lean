import MacroPeg.CBV.SequentialTotalCorrectness
import MacroPeg.CBV.SequentialResultCompiler

namespace Shallot.MacroPeg.CBV.SequentialTotalCompiler
open SequentialTotalSyntax SequentialTotalControl
open SequentialLocalCorrectness (canonical clock)

theorem mode_defined (m : Mode) (p : Nat) (r : Res) : ∃ v, modeResult m p r=some v := by
  cases m <;> cases r with
  | none => exact ⟨none,rfl⟩
  | some v => cases v with
    | none => simp [modeResult,successResult,zeroResult,positiveResult,failureResult]
    | some q => by_cases hq : q=p <;>
        simp [modeResult,successResult,zeroResult,positiveResult,failureResult,hq]

/-- A concrete finite physical clock returns an actual result for every
generated mode, also when the original program is undefined. -/
theorem total_at (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) (m : Mode) :
    ∃ v, evV (target g) x .callByValueSeq
      (tblV (target g) x .callByValueSeq (clock (target g) x)) E
      ((compile g g.rules.length e).get m) p=some v := by
  have hc := get_correct _ _ (SequentialTotalCorrectness.expression g hg x E e he p hp) m
  obtain ⟨v,hv⟩ := mode_defined m p (evV g x .callByValueSeq (canonical g x) E e p)
  exact ⟨v,hc.trans hv⟩

theorem canonical_success_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (q : Nat) (hq : q≤x.length) :
    evV g x .callByValueSeq (canonical g x) [] e x.length=some (some q) ↔
      SObs g .callByValueSeq e x (some (sfx x q)) :=
  (SequentialClock.finite_eval_iff g x [] e x.length (Nat.le_refl _) (some q)).symm.trans
    (SequentialResultCompiler.finite_success_iff g hg e he x q hq)

/-- Every successful residual is preserved by one input-independent fixed
Seq grammar. Source failure and undefinedness both reject finitely. -/
theorem successes_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (q : Nat) (hq : q≤x.length) :
    SObs g .callByValueSeq e x (some (sfx x q)) ↔
      SObs (target g) .callByValueSeq (start g e) x (some (sfx x q)) := by
  rw [←canonical_success_iff g hg e he x q hq,
    ←canonical_success_iff (target g) (target_firstOrder g) (start g e) (start_firstOrder g e) x q hq,
    SequentialTotalCorrectness.start_correct g hg x [] e he x.length (Nat.le_refl _)]
  cases evV g x .callByValueSeq (canonical g x) [] e x.length with
  | none => simp [successResult]
  | some v => cases v <;> simp [successResult]

theorem recognizes (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    SObs g .callByValueSeq e x (some []) ↔
      SObs (target g) .callByValueSeq (start g e) x (some []) := by
  simpa only [sfx,Nat.sub_zero,List.drop_length] using successes_iff g hg e he x 0 (by omega)

theorem language_translation (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) :
    (fun x => SObs g .callByValueSeq e x (some []))=
      (fun x => SObs (target g) .callByValueSeq (start g e) x (some [])) := by
  funext x
  exact propext (recognizes g hg e he x)

theorem total_observation (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) : ∃ result, SObs (target g) .callByValueSeq (start g e) x result := by
  obtain ⟨v,hv⟩ := total_at g hg x [] e he x.length (Nat.le_refl _) .success
  have hs := (tblV_stable (target g) x .callByValueSeq (Nat.le_refl _)).mp
    (show ∃ k, evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) [] (start g e) x.length=some v from ⟨_,hv⟩)
  cases v with
  | none => exact ⟨none,(decideObsV_iff (target_firstOrder g) (by decide) (start_firstOrder g e) x none).mp
      (by simp [decideObsV,hs])⟩
  | some q => exact ⟨some (sfx x q),(decideObsV_iff (target_firstOrder g) (by decide) (start_firstOrder g e) x _).mp
      (by simp [decideObsV,hs])⟩

end Shallot.MacroPeg.CBV.SequentialTotalCompiler
