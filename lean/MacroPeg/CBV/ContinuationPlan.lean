import MacroPeg.CBV.OriginControlNormalization

/-! Push a consuming continuation into origin-control leaves while preserving
PEG commitment. Later failure must not reopen a successful alternative. -/
namespace Shallot.MacroPeg.CBV.ContinuationPlan
open ReplayControlFusion (Plan)

/-- Existing leaves remain usable as guards; appended leaves execute the
selected old leaf followed by the continuation. -/
def bind (offset : Nat) : Plan → Plan → Plan
  | .leaf i, _ => .leaf (offset+i)
  | .alt a b, Q => .alt (.guard a (bind offset a Q)) (.guard (.notP a) (bind offset b Q))
  | .notP a, Q => .guard (.notP a) Q
  | .guard a b, Q => .guard a (bind offset b Q)

def sem (L : Nat → Nat → Res) (P : Plan) (p : Nat) : Res := P.eval (fun i => L i p) p

def sequence (a b : Nat → Res) (p : Nat) : Res :=
  match a p with | some (some j) => b j | other => other

theorem sem_congr (n : Nat) (L R : Nat → Nat → Res) (h : ∀ i, i<n → ∀ p, L i p=R i p)
    (P : Plan) (hP : P.All (fun i => i<n)) (p : Nat) : sem L P p=sem R P p := by
  apply Plan.eval_congr
  exact Plan.all_imp (fun i hi => h i hi p) P hP

/-- The local appended-leaf premise is instantiated by actual generated
expressions in `expression_eq` below. -/
theorem bind_correct (n offset : Nat) (L R : Nat → Nat → Res)
    (hQuery : ∀ i, i<n → ∀ p, R i p=L i p)
    (Q : Plan) (hQ : Q.All (fun i => i<n))
    (hTail : ∀ i, i<n → ∀ p, R (offset+i) p=sequence (L i) (sem L Q) p) :
    ∀ P, P.All (fun i => i<n) → ∀ p,
      sem R (bind offset P Q) p=sequence (sem L P) (sem L Q) p
  | .leaf i, hi, p => hTail i hi p
  | .alt a b, hP, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have hb := sem_congr n R L hQuery b hP.2 p
    have ia := bind_correct n offset L R hQuery Q hQ hTail a hP.1 p
    have ib := bind_correct n offset L R hQuery Q hQ hTail b hP.2 p
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
  | .notP a, hP, p => by
    have ha := sem_congr n R L hQuery a hP p
    have hq := sem_congr n R L hQuery Q hQ p
    change (match (match sem R a p with | some (some _) => some none | some none => some (some p) | none => none) with
      | some (some _) => sem R Q p | other => other)=_
    rw [ha,hq]
    simp only [sequence, sem, Plan.eval]
    cases hv : Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl
  | .guard a b, hP, p => by
    have ha := sem_congr n R L hQuery a hP.1 p
    have ib := bind_correct n offset L R hQuery Q hQ hTail b hP.2 p
    change (match sem R a p with | some (some _) => sem R (bind offset b Q) p | other => other)=_
    rw [ha,ib]
    simp only [sequence, sem, Plan.eval]
    cases hv : Plan.eval (fun i => L i p) p a with
    | none => rfl
    | some result => cases result <;> rfl

theorem bind_bounded (n : Nat) (Q : Plan) (hQ : Q.All (fun i => i<n)) :
    ∀ P, P.All (fun i => i<n) → (bind n P Q).All (fun i => i<2*n)
  | .leaf i, hi => by change i<n at hi; change n+i<2*n; omega
  | .alt a b, hP => by
    have ha := Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) a hP.1
    exact ⟨⟨ha,bind_bounded n Q hQ a hP.1⟩,ha,bind_bounded n Q hQ b hP.2⟩
  | .notP a, hP =>
    ⟨Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) a hP,
      Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) Q hQ⟩
  | .guard a b, hP =>
    ⟨Plan.all_imp (fun i (hi : i<n) => show i<2*n by omega) a hP.1,bind_bounded n Q hQ b hP.2⟩

def expressions (n : Nat) (L : Nat → MExp) (Q : Plan) (i : Nat) : MExp :=
  if i<n then L i else .seq (L (i-n)) (Q.exp L)

theorem expressions_firstOrder (n : Nat) (L : Nat → MExp) (hL : ∀ i, (L i).FirstOrder) (Q : Plan) (i : Nat) :
    (expressions n L Q i).FirstOrder := by
  unfold expressions
  split
  · exact hL _
  · exact ⟨hL _,Plan.exp_firstOrder hL Q⟩

/-- Complete actual evaluator equality, without any table, parser, or
continuation oracle. Undefinedness and failure after commitment are included. -/
theorem expression_eq (n : Nat) (L : Nat → MExp) (P Q : Plan)
    (hP : P.All (fun i => i<n)) (hQ : Q.All (fun i => i<n))
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E ((bind n P Q).exp (expressions n L Q)) p =
      evV g x s T E (.seq (P.exp L) (Q.exp L)) p := by
  have hc := bind_correct n n (fun i z => evV g x s T E (L i) z)
    (fun i z => evV g x s T E (expressions n L Q i) z)
    (by intro i hi z; simp only [expressions,if_pos hi]) Q hQ
    (by
      intro i hi z
      rw [show expressions n L Q (n+i)=.seq (L i) (Q.exp L) by simp only [expressions,if_neg (by omega : ¬n+i<n),Nat.add_sub_cancel_left]]
      change (match evV _ _ _ _ E (L i) z with | some (some j) => evV _ _ _ _ E (Q.exp L) j | other => other)=_
      simp only [sequence,sem]
      cases evV g x s T E (L i) z with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some j => exact Plan.exp_eval g x s T E L j Q) P hP p
  rw [Plan.exp_eval]
  change sem (fun i z => evV g x s T E (expressions n L Q i) z) (bind n P Q) p=_
  rw [hc]
  change _=(match evV _ _ _ _ E (P.exp L) p with | some (some j) => evV _ _ _ _ E (Q.exp L) j | other => other)
  rw [Plan.exp_eval]
  simp only [sequence, sem]
  cases hv : Plan.eval (fun i => evV g x s T E (L i) p) p P with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j => exact (Plan.exp_eval g x s T E L j Q).symm

end Shallot.MacroPeg.CBV.ContinuationPlan
