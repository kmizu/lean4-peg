import MacroPeg.CBV.MixedForwardingReset

namespace Shallot.MacroPeg.CBV.OriginHeadPlan
open ReplayControlFusion (Part Plan)

def follow (r : Res) (K : Nat → Res) : Res := match r with
  | some (some q) => K q
  | other => other

def shift (base : Nat) : Plan → Plan
  | .leaf i => .leaf (base+i)
  | .alt a b => .alt (shift base a) (shift base b)
  | .notP a => .notP (shift base a)
  | .guard a b => .guard (shift base a) (shift base b)

/-- Commit to the selected child branch before running the suffix. Merely
appending a suffix separately to both alternatives would retry the child. -/
def after (base done tail : Nat) : Plan → Plan
  | .leaf i => .leaf (done+i)
  | .alt a b => .alt (.guard (shift base a) (after base done tail a))
      (.guard (.notP (shift base a)) (after base done tail b))
  | .notP a => .guard (.notP (shift base a)) (.leaf tail)
  | .guard a b => .guard (shift base a) (after base done tail b)

theorem shift_eval (base : Nat) (L S : Nat → Res) (p : Nat) :
    ∀ P, Plan.All (fun i => L (base+i)=S i) P → (shift base P).eval L p=P.eval S p
  | .leaf i,h => h
  | .alt a b,h | .guard a b,h => by simp only [shift,Plan.eval,shift_eval base L S p a h.1,shift_eval base L S p b h.2]
  | .notP a,h => by simp only [shift,Plan.eval,shift_eval base L S p a h]

theorem after_eval (base done tail : Nat) (L S : Nat → Res) (K : Nat → Res) (p : Nat)
    (htail : L tail=K p) : ∀ P,
    Plan.All (fun i => L (base+i)=S i ∧ L (done+i)=follow (S i) K) P →
    (after base done tail P).eval L p=follow (P.eval S p) K
  | .leaf i,h => h.2
  | .alt a b,h => by
    have ha := shift_eval base L S p a (Plan.all_imp (fun _ h => h.1) a h.1)
    have ia := after_eval base done tail L S K p htail a h.1
    have ib := after_eval base done tail L S K p htail b h.2
    simp only [after,Plan.eval,ha,ia,ib]
    cases hv : a.eval S p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some q =>
        simp only [follow,ReplayFallbackFusion.orElse]
        cases K q with
        | none => rfl
        | some r => cases r <;> rfl
  | .notP a,h => by
    have ha := shift_eval base L S p a (Plan.all_imp (fun _ h => h.1) a h)
    simp only [after,Plan.eval,ha,htail]
    cases hv : a.eval S p with
    | none => rfl
    | some r => cases r <;> rfl
  | .guard a b,h => by
    have ha := shift_eval base L S p a (Plan.all_imp (fun _ h => h.1) a h.1)
    have ib := after_eval base done tail L S K p htail b h.2
    simp only [after,Plan.eval,ha,ib]
    cases hv : a.eval S p with
    | none => rfl
    | some r => cases r <;> rfl

theorem shift_all (base : Nat) (A : Nat → Prop) : ∀ P,
    Plan.All (fun i => A (base+i)) P → Plan.All A (shift base P)
  | .leaf i,h => h
  | .alt a b,h | .guard a b,h => ⟨shift_all base A a h.1,shift_all base A b h.2⟩
  | .notP a,h => shift_all base A a h

theorem after_all (base done tail : Nat) (A : Nat → Prop) (ht : A tail) : ∀ P,
    Plan.All (fun i => A (base+i) ∧ A (done+i)) P → Plan.All A (after base done tail P)
  | .leaf i,h => h.2
  | .alt a b,h => ⟨⟨shift_all base A a (Plan.all_imp (fun _ h => h.1) a h.1),after_all base done tail A ht a h.1⟩,
      shift_all base A a (Plan.all_imp (fun _ h => h.1) a h.1),after_all base done tail A ht b h.2⟩
  | .notP a,h => ⟨shift_all base A a (Plan.all_imp (fun _ h => h.1) a h),ht⟩
  | .guard a b,h => ⟨shift_all base A a (Plan.all_imp (fun _ h => h.1) a h.1),after_all base done tail A ht b h.2⟩

end Shallot.MacroPeg.CBV.OriginHeadPlan
