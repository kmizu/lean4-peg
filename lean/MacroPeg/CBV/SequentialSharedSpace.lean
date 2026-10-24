import MacroPeg.CBV.SequentialSharedStack
import MacroPeg.CBV.SequentialCaptureRegions

/-! Captured-character accounting for the machine with shared environments.
The certificates below are proof-only: no accounting fields are added to the
runtime machine. Integer cursors and control records are not counted here. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedSpace
open SequentialSharedStack
open SequentialCaptureRegions (Kind Window weight)

inductive ScopedValue : Kind → SequentialSharedStack.Value → Prop where
  | expr {p : Nat} {r : Res} (h : OkR p r) : ScopedValue (.expr p) (.expr r)
  | args {p : Nat} {r : ArgsResult}
      (h : ∀ W q, r = some (some (W,q)) → Window p q W) : ScopedValue (.args p) (.args r)

inductive ScopedTask : Task → Kind → Prop where
  | expr {m e p cap} (hp : p ≤ cap) : ScopedTask (.expr m e p) (.expr cap)
  | args {m es p} : ScopedTask (.args m es p) (.args p)
  | query {m i W p cap} (hp : weight W + p ≤ cap) :
      ScopedTask (.query m i W p) (.expr cap)
  | value {v k} (h : ScopedValue k v) : ScopedTask (.value v) k

/-- Only scope frames save environments. The credit consumed by a fresh
callee environment comes from the caller's already consumed arguments. -/
inductive ScopedFrame : Frame → CaptureEnv → Kind → CaptureEnv → Kind → Prop where
  | seq {m E b p cap} (hp : p ≤ cap) :
      ScopedFrame (.seq m b) E (.expr p) E (.expr cap)
  | alt {m E b p cap} (hp : p ≤ cap) :
      ScopedFrame (.alt m b p) E (.expr p) E (.expr cap)
  | notP {E p cap} (hp : p ≤ cap) : ScopedFrame (.notP p) E (.expr p) E (.expr cap)
  | star {m E a p cap} (hp : p ≤ cap) :
      ScopedFrame (.star m a p) E (.expr p) E (.expr cap)
  | argHead {m E es p} : ScopedFrame (.argHead m es p) E (.expr p) E (.args p)
  | argCons {E p q} (hq : q ≤ p) : ScopedFrame (.argCons (p,q)) E (.args q) E (.args p)
  | call {m i E p cap} (hp : p ≤ cap) : ScopedFrame (.call m i) E (.args p) E (.expr cap)
  | scope {W E p cap} (hp : weight W + p ≤ cap) :
      ScopedFrame (.scope E) W (.expr p) E (.expr cap)

inductive ScopedStack : CaptureEnv → Kind → List Frame → Nat → Prop where
  | nil {E k n} (hp : weight E + k.bound ≤ n) : ScopedStack E k [] n
  | cons {E E' k k' n f K} (head : ScopedFrame f E k E' k')
      (tail : ScopedStack E' k' K n) : ScopedStack E k (f::K) n

def Scoped (n : Nat) (c : Config) : Prop :=
  ∃ k, ScopedTask c.task k ∧ ScopedStack c.env k c.stack n

private theorem result_mono {p q : Nat} {r : Res} (h : OkR p r) (hp : p ≤ q) : OkR q r :=
  fun j hj => Nat.le_trans (h j hj) hp

theorem return_scoped (g : MGrammar) (x : List Char)
    {v : SequentialSharedStack.Value} {kind out : Kind} {final : Nat} {E E' : CaptureEnv} {f : Frame} {K : List Frame} {next : Config}
    (hv : ScopedValue kind v) (hf : ScopedFrame f E kind E' out) (ht : ScopedStack E' out K final)
    (hs : step g x ⟨.value v,E,f::K⟩ = some next) : Scoped final next := by
  cases hf with
  | @seq m E b p cap hp =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none =>
        cases hs
        exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none =>
          cases hs
          exact ⟨_,.value (.expr (okR_fail _)),ht⟩
        | some q =>
          cases hs
          exact ⟨_,.expr (Nat.le_trans (hr q rfl) hp),ht⟩
  | @alt m E b p cap hp =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.expr hp,ht⟩
        | some q => cases hs; exact ⟨_,.value (.expr (okR_ok (Nat.le_trans (hr q rfl) hp))),ht⟩
  | @notP E p cap hp =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_ok hp)),ht⟩
        | some q => cases hs; exact ⟨_,.value (.expr (okR_fail _)),ht⟩
  | @star m E a p cap hp =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_ok hp)),ht⟩
        | some q =>
          by_cases hq : q<p
          · simp only [step,if_pos hq] at hs
            cases hs
            exact ⟨_,.expr (by omega),ht⟩
          · simp only [step,if_neg hq] at hs
            cases hs
            exact ⟨_,.value (.expr (okR_none _)),ht⟩
  | @argHead m E es p =>
    cases hv with
    | @expr _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
        | some q =>
          have hq := hr q rfl
          simp only [step,Nat.min_eq_left hq] at hs
          cases hs
          exact ⟨_,.args,.cons (.argCons hq) ht⟩
  | @argCons E p j hj =>
    cases hv with
    | @args _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.args (by intro W q he; cases he)),ht⟩
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          cases hs
          refine ⟨_,.value (.args ?_),ht⟩
          intro V r he
          cases he
          exact .cons hj (hr W q rfl)
  | @call m i E p cap hp =>
    cases hv with
    | @args _ result hr =>
      cases result with
      | none => cases hs; exact ⟨_,.value (.expr (okR_none _)),ht⟩
      | some r => cases r with
        | none => cases hs; exact ⟨_,.value (.expr (okR_fail _)),ht⟩
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          cases hs
          have hW := hr W q rfl
          exact ⟨_,.query (by have hw := hW.weight; have hq := hW.descending; omega),ht⟩

  | @scope W E p cap hp =>
    cases hv with
    | @expr _ r hr =>
      cases hs
      exact ⟨_,.value (.expr (result_mono hr (by omega))),ht⟩

theorem step_scoped (g : MGrammar) (x : List Char) {final : Nat} {c next : Config}
    (h : Scoped final c) (hs : step g x c = some next) : Scoped final next := by
  obtain ⟨task,E,K⟩ := c
  obtain ⟨kind,hTask,hStack⟩ := h
  cases hTask with
  | @expr m e p cap hp =>
    cases e with
    | seq a b =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _),.cons (.seq hp) hStack⟩
    | alt a b =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _),.cons (.alt hp) hStack⟩
    | notP a =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _),.cons (.notP hp) hStack⟩
    | star a =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _),.cons (.star hp) hStack⟩
    | call i args =>
      cases hr : ruleAtM g.rules i with
      | none =>
        simp only [step,hr] at hs
        cases hs
        exact ⟨_,.value (.expr (okR_fail _)),hStack⟩
      | some rule =>
        by_cases ha : rule.arity=args.length
        · simp only [step,hr,if_pos ha] at hs
          cases hs
          exact ⟨_,.args,.cons (.call hp) hStack⟩
        · simp only [step,hr,if_neg ha] at hs
          cases hs
          exact ⟨_,.value (.expr (okR_fail _)),hStack⟩
    | eps | any | chr _ | range _ _ | lit _ | param _ | dbg _ | lam _ _ | callParam _ _ | invoke _ _ _ =>
      cases hs
      exact ⟨_,.value (.expr (result_mono (SequentialCaptureRegions.atom_descending x E _ p) hp)),hStack⟩
  | @args m es p =>
    cases es with
    | nil =>
      cases hs
      refine ⟨_,.value (.args ?_),hStack⟩
      intro W q he
      cases he
      exact .nil p
    | cons a args =>
      cases hs
      exact ⟨_,.expr (Nat.le_refl _),.cons .argHead hStack⟩
  | @query m i W p cap hp =>
    cases m with
    | zero => cases hs; exact ⟨_,.value (.expr (okR_none _)),hStack⟩
    | succ m =>
      by_cases hn : p≤x.length
      · cases hr : ruleAtM g.rules i with
        | none =>
          simp only [step,if_pos hn,hr] at hs
          cases hs
          exact ⟨_,.value (.expr (okR_none _)),hStack⟩
        | some rule =>
          simp only [step,if_pos hn,hr] at hs
          cases hs
          exact ⟨_,.expr (Nat.le_refl _),.cons (.scope hp) hStack⟩
      · simp only [step,if_neg hn] at hs
        cases hs
        exact ⟨_,.value (.expr (okR_none _)),hStack⟩
  | @value v k hv =>
    cases hStack with
    | nil => cases v <;> simp [step] at hs
    | cons hf ht => exact return_scoped g x hv hf ht hs

theorem runs_scoped (g : MGrammar) (x : List Char) {final : Nat} {a b : Config}
    (h : Runs g x a b) (ha : Scoped final a) : Scoped final b := by
  induction h with
  | refl => exact ha
  | cons hs ht ih => exact ih (step_scoped g x ha hs)

theorem initial_scoped (g : MGrammar) (x : List Char) (e : MExp) :
    Scoped x.length (initial g x e) :=
  ⟨_,.expr (Nat.le_refl _),.nil (by simp [weight, Kind.bound, initial])⟩

/-- Every actual reachable state satisfies the credit invariant. -/
theorem reachable_scoped (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : Scoped x.length c :=
  runs_scoped g x h (initial_scoped g x e)


def taskCaptures : Task → CaptureEnv
  | .query _ _ W _ => W
  | .value (.args (some (some (W,_)))) => W
  | _ => []

def frameCaptures : Frame → CaptureEnv
  | .argCons span => [span]
  | .scope E => E
  | _ => []

/-- Every retained copy is counted, including the current environment, all
suspended scopes, pending argument heads, and the current argument result. -/
def retainedCaptures (c : Config) : CaptureEnv :=
  taskCaptures c.task ++ c.env ++ c.stack.flatMap frameCaptures

theorem weight_append (A B : CaptureEnv) : weight (A ++ B) = weight A + weight B := by
  simp [weight, List.map_append, List.sum_append]

theorem ScopedFrame.credit {f : Frame} {E E' : CaptureEnv} {kind out : Kind}
    (h : ScopedFrame f E kind E' out) :
    weight E + weight (frameCaptures f) + kind.bound ≤ weight E' + out.bound := by
  cases h <;> simp only [frameCaptures, weight, List.map_nil, List.sum_nil,
    List.map_cons, List.sum_cons, Kind.bound, Nat.add_zero] at * <;> omega

theorem ScopedStack.credit {E : CaptureEnv} {kind : Kind} {K : List Frame} {n : Nat}
    (h : ScopedStack E kind K n) :
    weight E + weight (K.flatMap frameCaptures) + kind.bound ≤ n := by
  induction h with
  | nil hp => simpa [weight] using hp
  | cons hf ht ih =>
    have hh := hf.credit
    simp only [List.flatMap_cons, weight_append]
    omega

theorem ScopedTask.credit {task : Task} {kind : Kind} (h : ScopedTask task kind) :
    weight (taskCaptures task) ≤ kind.bound := by
  cases h with
  | expr _ | args => simp [taskCaptures, weight]
  | query hp => simp only [taskCaptures, Kind.bound]; omega
  | value hv =>
    cases hv with
    | expr _ => simp [taskCaptures, weight]
    | @args p result hr =>
      cases result with
      | none => simp [taskCaptures, weight]
      | some r => cases r with
        | none => simp [taskCaptures, weight]
        | some Wq =>
          obtain ⟨W,q⟩ := Wq
          have hw := (hr W q rfl).weight
          simp only [taskCaptures, Kind.bound]
          omega

/-- Global capture weight, including every suspended activation, is bounded by
input length at every reachable state, not just at completed calls. -/
theorem reachable_weight (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) : weight (retainedCaptures c) ≤ x.length := by
  obtain ⟨kind,ht,hK⟩ := reachable_scoped g x e c h
  have htask := ht.credit
  have hstack := hK.credit
  simp only [retainedCaptures, weight_append]
  omega

/-- Decoding a span never stores more than its charged interval length, even
for arbitrary out-of-range span endpoints. -/
theorem decoded_weight_le (x : List Char) (E : CaptureEnv) :
    ((SequentialSpanRecompute.decodeEnv x E).map List.length).sum ≤ weight E := by
  induction E with
  | nil => simp [SequentialSpanRecompute.decodeEnv, weight]
  | cons span E ih =>
    have hspan : (pre x span.1 span.2).length ≤ span.1 - span.2 := by
      simp only [pre, List.length_take]
      exact Nat.min_le_left _ _
    change (pre x span.1 span.2).length + _ ≤ (span.1 - span.2) + _
    exact Nat.add_le_add hspan ih

/-- Even if each retained span is materialized as its own character word, the
sum of the lengths of all those words is at most the original input length.
This counts character payload only, not integer metadata or interpreter space. -/
theorem reachable_captured_characters (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ((SequentialSpanRecompute.decodeEnv x (retainedCaptures c)).map List.length).sum ≤
      x.length :=
  Nat.le_trans (decoded_weight_le x _) (reachable_weight g x e c h)

end Shallot.MacroPeg.CBV.SequentialSharedSpace
