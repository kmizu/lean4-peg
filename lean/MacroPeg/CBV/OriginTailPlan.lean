import MacroPeg.CBV.OriginHeadRawCompiler

namespace Shallot.MacroPeg.CBV.OriginTailPlan
open OriginHeadPlan (follow shift shift_eval)
open ReplayControlFusion (Part Plan)

/-- Only successful exits execute the continuation. Query subtrees do not
inherit the continuation's retained-value requirements. -/
def Exits (L : Nat → Prop) (N : Prop) : Plan → Prop
  | .leaf i => L i
  | .alt a b => Exits L N a ∧ Exits L N b
  | .guard _ b => Exits L N b
  | .notP _ => N

def append (base tail : Nat) (done : Nat → Plan) : Plan → Plan
  | .leaf i => done i
  | .alt a b => .alt (.guard (shift base a) (append base tail done a))
      (.guard (.notP (shift base a)) (append base tail done b))
  | .notP a => .guard (.notP (shift base a)) (.leaf tail)
  | .guard a b => .guard (shift base a) (append base tail done b)

theorem exits_imp {L R : Nat → Prop} {N M : Prop} (hl : ∀ i, L i → R i) (hn : N → M) :
    ∀ P, Exits L N P → Exits R M P
  | .leaf i,h => hl i h
  | .alt a b,h => ⟨exits_imp hl hn a h.1,exits_imp hl hn b h.2⟩
  | .guard _ b,h => exits_imp hl hn b h
  | .notP _,h => hn h

theorem append_eval (base tail : Nat) (done : Nat → Plan) (L S : Nat → Res) (K : Nat → Res) (p : Nat) :
    ∀ P, Plan.All (fun i => L (base+i)=S i) P →
      Exits (fun i => (done i).eval L p=follow (S i) K) (L tail=K p) P →
      (append base tail done P).eval L p=follow (P.eval S p) K
  | .leaf i,_,h => h
  | .alt a b,h,hx => by
    have ha := shift_eval base L S p a h.1
    have ia := append_eval base tail done L S K p a h.1 hx.1
    have ib := append_eval base tail done L S K p b h.2 hx.2
    simp only [append,Plan.eval,ha,ia,ib]
    cases a.eval S p with
    | none => rfl
    | some r => cases r with
      | none => rfl
      | some q =>
        simp only [follow,ReplayFallbackFusion.orElse]
        cases K q with
        | none => rfl
        | some r => cases r <;> rfl
  | .notP a,h,hx => by
    have ha := shift_eval base L S p a h
    have ht : L tail=K p := hx
    simp only [append,Plan.eval,ha,ht]
    cases a.eval S p with
    | none => rfl
    | some r => cases r <;> rfl
  | .guard a b,h,hx => by
    have ha := shift_eval base L S p a h.1
    have ib := append_eval base tail done L S K p b h.2 hx
    simp only [append,Plan.eval,ha,ib]
    cases a.eval S p with
    | none => rfl
    | some r => cases r <;> rfl

end Shallot.MacroPeg.CBV.OriginTailPlan
