import MacroPeg.CBV.LeafContinuation

/-! Guard-only leaves do not receive consuming continuations. Track only
leaves that can be selected as outputs of a Consumer control tree. -/
namespace Shallot.MacroPeg.CBV.ConsumingPlanOutputs
open ReplayControlFusion (Plan)
open LeafContinuation (Consumer chain)
open ContinuationPlan (bind)
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

theorem bind_correct (n offset : Nat) (L R : Nat → Nat → Res)
    (hQuery : ∀ i, i<n → ∀ p, R i p=L i p)
    (Q : Plan) (hQ : Q.All (fun i => i<n))
    : ∀ P, P.All (fun i => i<n) →
    (∀ i, i∈outputs P → i<n → ∀ p, R (offset+i) p=sequence (L i) (sem L Q) p) → ∀ p,
      sem R (bind offset P Q) p=sequence (sem L P) (sem L Q) p
  | .leaf i, hi, hTail, p => hTail i (by simp [outputs]) hi p
  | .alt a b, hP, hTail, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have hb := sem_congr n R L hQuery b hP.2 p
    have ia := bind_correct n offset L R hQuery Q hQ a hP.1 (fun i hi hn => hTail i (List.mem_append.mpr (Or.inl hi)) hn) p
    have ib := bind_correct n offset L R hQuery Q hQ b hP.2 (fun i hi hn => hTail i (List.mem_append.mpr (Or.inr hi)) hn) p
    change ReplayFallbackFusion.orElse
      (match sem R a p with | some (some _) => sem R (bind offset a Q) p | other => other)
      (match (match sem R a p with | some (some _) => some none | some none => some (some p) | none => none) with
        | some (some _) => sem R (bind offset b Q) p | other => other)=_
    rw [ha,ia,ib]
    simp only [sequence, sem, Plan.eval, ReplayFallbackFusion.orElse]
    cases hv : Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        cases hq : Plan.eval (fun i => L i j) j Q with
        | none => rfl
        | some result => cases result <;> rfl
  | .notP a, hP, _, p => by
    have ha := sem_congr n R L hQuery a hP p
    have hq := sem_congr n R L hQuery Q hQ p
    change (match (match sem R a p with | some (some _) => some none | some none => some (some p) | none => none) with
      | some (some _) => sem R Q p | other => other)=_
    rw [ha,hq]
    simp only [sequence, sem, Plan.eval]
    cases hv : Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl
  | .guard a b, hP, hTail, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have ib := bind_correct n offset L R hQuery Q hQ b hP.2 hTail p
    change (match sem R a p with | some (some _) => sem R (bind offset b Q) p | other => other)=_
    rw [ha,ib]
    simp only [sequence, sem, Plan.eval]
    cases hv : Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl


theorem bind_bound (n offset total : Nat) (hn : n≤total) (ho : offset+n≤total)
    (Q : Plan) (hq : Q.All (fun i => i<total)) :
    ∀ P, P.All (fun i => i<n) → (bind offset P Q).All (fun i => i<total)
  | .leaf i, hi => by change i<n at hi; change offset+i<total; omega
  | .notP a, ha => ⟨Plan.all_imp (fun _ hi => Nat.lt_of_lt_of_le hi hn) a ha,hq⟩
  | .guard a b, hp => ⟨Plan.all_imp (fun _ hi => Nat.lt_of_lt_of_le hi hn) a hp.1,
      bind_bound n offset total hn ho Q hq b hp.2⟩
  | .alt a b, hp => by
    have ha := Plan.all_imp (fun _ hi => Nat.lt_of_lt_of_le hi hn) a hp.1
    exact ⟨⟨ha,bind_bound n offset total hn ho Q hq a hp.1⟩,
      ha,bind_bound n offset total hn ho Q hq b hp.2⟩

end Shallot.MacroPeg.CBV.ConsumingPlanOutputs
