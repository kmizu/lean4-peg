import Complexity.ListCompile
import Complexity.LKit

/-! Injective register renaming preserves execution and untouched registers.
The background may contain an unexpanded binary continuation. -/

namespace Complexity

def LProg.rename {k m : Nat} (ρ : Fin k → Fin m) : LProg k → LProg m
  | .push i e => .push (ρ i) e
  | .pop i => .pop (ρ i)
  | .copy i j => .copy (ρ i) (ρ j)
  | .seq p q => .seq (p.rename ρ) (q.rename ρ)
  | .ite i c p q => .ite (ρ i) c (p.rename ρ) (q.rename ρ)
  | .loop i c p => .loop (ρ i) c (p.rename ρ)
  | .halt b => .halt b

noncomputable def Lists.frame {k m : Nat} (L : Lists k) (ρ : Fin k → Fin m) (R : Lists m) : Lists m :=
  fun j => if h : ∃ i, ρ i = j then L (Classical.choose h) else R j

theorem Lists.frame_get {k m : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (L : Lists k) (i : Fin k) : L.frame ρ R (ρ i) = L i := by
  simp only [Lists.frame, dif_pos (show ∃ j, ρ j = ρ i from ⟨i, rfl⟩)]
  congr 1
  exact hi (Classical.choose_spec (show ∃ j, ρ j = ρ i from ⟨i, rfl⟩))

theorem Lists.frame_outside {k m : Nat} {ρ : Fin k → Fin m} (R : Lists m) (L : Lists k)
    (j : Fin m) (h : ¬ ∃ i, ρ i = j) : L.frame ρ R j = R j := by simp [Lists.frame, h]

theorem Lists.frame_set {k m : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (L : Lists k) (i : Fin k) (l : List Nat) :
    (L.set i l).frame ρ R = (L.frame ρ R).set (ρ i) l := by
  funext j
  by_cases hj : ∃ a, ρ a = j
  · obtain ⟨a, rfl⟩ := hj
    simp only [Lists.frame_get hi, Lists.set]
    have he : ρ a = ρ i ↔ a = i := ⟨fun h => hi h, congrArg ρ⟩
    simp only [he]
  · have hji : j ≠ ρ i := by intro he; exact hj ⟨i, he.symm⟩
    simp [Lists.frame_outside R _ j hj, Lists.set_ne _ _ hji]

theorem Lists.frame_eq {k m : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (L : Lists k) (h : ∀ i, R (ρ i) = L i) : L.frame ρ R = R := by
  funext j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [Lists.frame_get hi, h]
  · exact Lists.frame_outside R L j hj

theorem lenOK_frame {k m B : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    {R : Lists m} {L : Lists k} (hR : LenOK B R) (hL : LenOK B L) : LenOK B (L.frame ρ R) := by
  intro j
  by_cases hj : ∃ i, ρ i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [Lists.frame_get hi]; exact hL i
  · rw [Lists.frame_outside R L j hj]; exact hR j

noncomputable def LOutcome.frame {k m : Nat} (ρ : Fin k → Fin m) (R : Lists m) : LOutcome k → LOutcome m
  | .cont L => .cont (L.frame ρ R)
  | .stop b L => .stop b (L.frame ρ R)

theorem LExec.rename_frame {k m B : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (hR : LenOK B R) {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k}
    (h : LExec (LenOK B) p L t o) :
    LExec (LenOK B) (p.rename ρ) (L.frame ρ R) t (o.frame ρ R) := by
  induction h with
  | @push i e L h h' =>
    have hh := lenOK_frame hi hR h'
    rw [Lists.frame_set hi] at hh
    simpa only [LProg.rename, LOutcome.frame, Lists.frame_set hi, Lists.frame_get hi] using
      LExec.push (i := ρ i) (e := e) (lenOK_frame hi hR h)
        (by simpa only [Lists.frame_get hi] using hh)
  | @pop i L h h' =>
    have hh := lenOK_frame hi hR h'
    rw [Lists.frame_set hi] at hh
    simpa only [LProg.rename, LOutcome.frame, Lists.frame_set hi, Lists.frame_get hi] using
      LExec.pop (i := ρ i) (lenOK_frame hi hR h)
        (by simpa only [Lists.frame_get hi] using hh)
  | @copy i j L hij h h' =>
    have hh := lenOK_frame hi hR h'
    rw [Lists.frame_set hi] at hh
    simpa only [LProg.rename, LOutcome.frame, Lists.frame_set hi, Lists.frame_get hi] using
      LExec.copy (hi.ne hij) (lenOK_frame hi hR h)
        (by simpa only [Lists.frame_get hi] using hh)
  | halt h => exact .halt (lenOK_frame hi hR h)
  | seqC _ _ ih1 ih2 => exact .seqC ih1 ih2
  | seqS _ ih => exact .seqS ih
  | iteT h hc _ ih => exact .iteT (lenOK_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih
  | iteF h hc _ ih => exact .iteF (lenOK_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih
  | loopF h hc => exact .loopF (lenOK_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc)
  | loopC h hc _ _ ih1 ih2 =>
    exact .loopC (lenOK_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih1 ih2
  | loopS h hc _ ih => exact .loopS (lenOK_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih

theorem LExec.weaken {k : Nat} {Q Q' : Lists k → Prop} (hQ : ∀ L, Q L → Q' L)
    {p : LProg k} {L : Lists k} {t : Nat} {o : LOutcome k} (h : LExec Q p L t o) : LExec Q' p L t o := by
  induction h with
  | push h h' => exact .push (hQ _ h) (hQ _ h')
  | pop h h' => exact .pop (hQ _ h) (hQ _ h')
  | copy hij h h' => exact .copy hij (hQ _ h) (hQ _ h')
  | halt h => exact .halt (hQ _ h)
  | seqC _ _ ih1 ih2 => exact .seqC ih1 ih2
  | seqS _ ih => exact .seqS ih
  | iteT h hc _ ih => exact .iteT (hQ _ h) hc ih
  | iteF h hc _ ih => exact .iteF (hQ _ h) hc ih
  | loopF h hc => exact .loopF (hQ _ h) hc
  | loopC h hc _ _ ih1 ih2 => exact .loopC (hQ _ h) hc ih1 ih2
  | loopS h hc _ ih => exact .loopS (hQ _ h) hc ih

theorem Runs.weaken {k : Nat} {Q Q' : Lists k → Prop} (hQ : ∀ L, Q L → Q' L)
    {p : LProg k} {L L' : Lists k} {T : Nat} (h : Runs Q p L L' T) : Runs Q' p L L' T := by
  obtain ⟨t, ht, hx⟩ := h
  exact ⟨t, ht, hx.weaken hQ⟩

end Complexity
