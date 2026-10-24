import Complexity.ListRename
import Complexity.NBoundedTransfer

/-! Numeric subprograms can share an input register while retaining disjoint
outputs and preserving all ambient registers, with the same space capacity. -/
namespace Complexity

def NPrim.rename {k m : Nat} (ρ : Fin k → Fin m) (hi : Function.Injective ρ) : NPrim k → NPrim m
  | .pushZ i => .pushZ (ρ i)
  | .inc i => .inc (ρ i)
  | .dec i => .dec (ρ i)
  | .pop i => .pop (ρ i)
  | .dup i j h => .dup (ρ i) (ρ j) (hi.ne h)

def NProg.rename {k m : Nat} (ρ : Fin k → Fin m) (hi : Function.Injective ρ) : NProg k → NProg m
  | .prim p => .prim (p.rename ρ hi)
  | .seq p q => .seq (p.rename ρ hi) (q.rename ρ hi)
  | .ite i c p q => .ite (ρ i) c (p.rename ρ hi) (q.rename ρ hi)
  | .loop i c p => .loop (ρ i) c (p.rename ρ hi)
  | .halt b => .halt b

theorem NPrim.rename_apply {k m : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (S : Lists k) (p : NPrim k) :
    (p.rename ρ hi).apply (S.frame ρ R) = (p.apply S).frame ρ R := by
  cases p <;> simp only [NPrim.rename,NPrim.apply,Lists.frame_get hi,Lists.frame_set hi]

theorem nfits_frame {k m B : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    {R : Lists m} {S : Lists k} (hR : NFits B R) (hS : NFits B S) : NFits B (S.frame ρ R) := by
  refine ⟨hR.1,fun j => ?_⟩
  by_cases hj : ∃ i, ρ i=j
  · obtain ⟨i,rfl⟩ := hj
    rw [Lists.frame_get hi]
    exact hS.2 i
  · rw [Lists.frame_outside R S j hj]
    exact hR.2 j

theorem NExec.rename_frame {k m B : Nat} {ρ : Fin k → Fin m} (hi : Function.Injective ρ)
    (R : Lists m) (hR : NFits B R) {p : NProg k} {S : Lists k} {t : Nat} {o : LOutcome k}
    (h : NExec (NFits B) p S t o) :
    NExec (NFits B) (p.rename ρ hi) (S.frame ρ R) t (o.frame ρ R) := by
  induction h with
  | @prim a S h h' =>
    have hh := nfits_frame hi hR h'
    rw [← NPrim.rename_apply hi] at hh
    simpa only [NProg.rename,LOutcome.frame,← NPrim.rename_apply hi] using
      NExec.prim (a := a.rename ρ hi) (nfits_frame hi hR h) hh
  | halt h => exact .halt (nfits_frame hi hR h)
  | seqC _ _ ih1 ih2 => exact .seqC ih1 ih2
  | seqS _ ih => exact .seqS ih
  | iteT h hc _ ih => exact .iteT (nfits_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih
  | iteF h hc _ ih => exact .iteF (nfits_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih
  | loopF h hc => exact .loopF (nfits_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc)
  | loopC h hc _ _ ih1 ih2 =>
    exact .loopC (nfits_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih1 ih2
  | loopS h hc _ ih => exact .loopS (nfits_frame hi hR h) (by simpa only [Lists.frame_get hi] using hc) ih

def LOutcome.satisfies {k : Nat} (Q : Lists k → Prop) : LOutcome k → Prop
  | .cont R => Q R
  | .stop _ R => Q R

theorem NExec.post {k : Nat} {Q : Lists k → Prop} {p : NProg k}
    {S : Lists k} {t : Nat} {o : LOutcome k} (h : NExec Q p S t o) :
    o.satisfies Q := by
  induction h with
  | prim _ h => exact h
  | halt h => exact h
  | seqC _ _ _ ih => exact ih
  | seqS _ ih => exact ih
  | iteT _ _ _ ih => exact ih
  | iteF _ _ _ ih => exact ih
  | loopF h _ => exact h
  | loopC _ _ _ _ _ ih => exact ih
  | loopS _ _ _ ih => exact ih

theorem NBoundedTransfer.FitsRuns.rename_frame {k m B : Nat} {ρ : Fin k → Fin m}
    (hi : Function.Injective ρ) (R : Lists m) (hR : NFits B R)
    {p : NProg k} {S S' : Lists k} {T : Nat} (h : FitsRuns B p S S' T) :
    FitsRuns B (p.rename ρ hi) (S.frame ρ R) (S'.frame ρ R) T := by
  obtain ⟨t,ht,he⟩ := h
  exact ⟨t,ht,he.rename_frame hi R hR⟩

theorem NExec.weaken {k : Nat} {Q Q' : Lists k → Prop} (hQ : ∀ S, Q S → Q' S)
    {p : NProg k} {S : Lists k} {t : Nat} {o : LOutcome k} (h : NExec Q p S t o) :
    NExec Q' p S t o := by
  induction h with
  | prim h h' => exact .prim (hQ _ h) (hQ _ h')
  | halt h => exact .halt (hQ _ h)
  | seqC _ _ ih1 ih2 => exact .seqC ih1 ih2
  | seqS _ ih => exact .seqS ih
  | iteT h hc _ ih => exact .iteT (hQ _ h) hc ih
  | iteF h hc _ ih => exact .iteF (hQ _ h) hc ih
  | loopF h hc => exact .loopF (hQ _ h) hc
  | loopC h hc _ _ ih1 ih2 => exact .loopC (hQ _ h) hc ih1 ih2
  | loopS h hc _ ih => exact .loopS (hQ _ h) hc ih

theorem NBoundedTransfer.FitsRuns.mono_space {k B C : Nat} (hBC : B ≤ C)
    {p : NProg k} {S S' : Lists k} {T : Nat} (h : FitsRuns B p S S' T) :
    FitsRuns C p S S' T := by
  obtain ⟨t,ht,he⟩ := h
  refine ⟨t,ht,he.weaken (fun S hS => ?_)⟩
  exact ⟨Nat.le_trans hS.1 hBC,fun i => Nat.le_trans (hS.2 i) hBC⟩

end Complexity
