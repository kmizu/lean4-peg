import MacroPeg.CBV.LeafContinuation

/-! Guard-only leaves do not receive consuming continuations. Track only
leaves that can be selected as outputs of a Consumer control tree. -/
namespace Shallot.MacroPeg.CBV.ConsumingPlanOutputs
open ReplayControlFusion (Plan)
open LeafContinuation (Consumer chain)
open ContinuationPlan (sequence sem sem_congr)

def outputs : Plan → List Nat
  | .leaf i => [i]
  | .alt a b => outputs a ++ outputs b
  | .guard _ b => outputs b
  | .notP _ => []

theorem chain_correct (n offset : Nat) (L R : Nat → Nat → Res) (K : Nat → Res)
    (hQuery : ∀ i, i<n → ∀ p, R i p=L i p) :
    ∀ P, Consumer P → P.All (fun i => i<n) →
    (∀ i, i∈outputs P → i<n → ∀ p, R (offset+i) p=sequence (L i) K p) → ∀ p,
    sem R (chain offset P) p=sequence (sem L P) K p
  | .leaf i, _, hi, ht, p => ht i (by simp [outputs]) hi p
  | .notP _, hc, _, _, _ => False.elim hc
  | .guard a b, hc, hp, ht, p => by
    have ha := sem_congr n R L hQuery a hp.1 p
    have ib := chain_correct n offset L R K hQuery b hc hp.2 ht p
    change (match sem R a p with | some (some _) => sem R (chain offset b) p | other => other)=_
    rw [ha,ib]
    simp only [sequence,sem,Plan.eval]
    cases Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl
  | .alt a b, hc, hp, ht, p => by
    have ha := sem_congr n R L hQuery a hp.1 p
    have ia := chain_correct n offset L R K hQuery a hc.1 hp.1
      (fun i hi hn => ht i (List.mem_append.mpr (Or.inl hi)) hn) p
    have ib := chain_correct n offset L R K hQuery b hc.2 hp.2
      (fun i hi hn => ht i (List.mem_append.mpr (Or.inr hi)) hn) p
    change ReplayFallbackFusion.orElse
      (match sem R a p with | some (some _) => sem R (chain offset a) p | other => other)
      (match (match sem R a p with | some (some _) => some none | some none => some (some p) | none => none) with
        | some (some _) => sem R (chain offset b) p | other => other)=_
    rw [ha,ia,ib]
    simp only [sequence,sem,Plan.eval,ReplayFallbackFusion.orElse]
    cases Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        cases K j with
        | none => rfl
        | some result => cases result <;> rfl

end Shallot.MacroPeg.CBV.ConsumingPlanOutputs
