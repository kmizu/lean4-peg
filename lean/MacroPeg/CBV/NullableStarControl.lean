import MacroPeg.CBV.BodyNormalForm

/-! A predicate output succeeds without consuming. Under star this is
undefined, so replace that output by an explicitly divergent guarded branch. -/
namespace Shallot.MacroPeg.CBV.NullableStarControl
open ReplayControlFusion (Plan)
open ContinuationPlan (sem sequence)
open OriginControlNormalization (Leaf render)
open BodyNormalForm (Form)
open RegularCaptureProduct (Node)
abbrev Arg := RecursiveArgumentCompiler.Expr

def freeze (d z : Nat) : Plan → Plan
  | .leaf i => .leaf i
  | .alt a b => .alt (freeze d z a) (freeze d z b)
  | .guard a b => .guard a (freeze d z b)
  | .notP a => .guard (.notP a) (.guard (.leaf d) (.leaf z))

theorem consumer (d z : Nat) : ∀ P, LeafContinuation.Consumer (freeze d z P)
  | .leaf _ => trivial
  | .alt a b => ⟨consumer d z a,consumer d z b⟩
  | .guard _ b => consumer d z b
  | .notP _ => trivial

theorem bounded (n : Nat) : ∀ P, P.All (fun i => i<n) →
    (freeze n (n+1) P).All (fun i => i<n+2)
  | .leaf i, hi => by change i<n at hi; change i<n+2; omega
  | .alt a b, hp => ⟨bounded n a hp.1,bounded n b hp.2⟩
  | .guard a b, hp => ⟨Plan.all_imp (fun _ hi => by omega) a hp.1,bounded n b hp.2⟩
  | .notP a, ha => ⟨Plan.all_imp (fun _ hi => by omega) a ha,by simp [Plan.All]⟩

def Change (p : Nat) (a b : Res) : Prop := b=a ∨ a=some (some p) ∧ b=none

theorem eval_change (n z : Nat) (L R : Nat → Nat → Res)
    (hQuery : ∀ i, i<n → ∀ p, R i p=L i p) (hd : ∀ p, R n p=none) :
    ∀ P, P.All (fun i => i<n) → ∀ p,
    Change p (sem L P p) (sem R (freeze n z P) p)
  | .leaf i, hi, p => Or.inl (hQuery i hi p)
  | .notP a, ha, p => by
    have h := ContinuationPlan.sem_congr n R L hQuery a ha p
    change Change p (GreedyRotation.negative (fun q => sem L a q) p)
      (match GreedyRotation.negative (fun q => sem R a q) p with
        | some (some _) => (match R n p with | some (some _) => R z p | other => other)
        | other => other)
    unfold GreedyRotation.negative
    dsimp only []
    rw [h,hd]
    cases sem L a p with
    | none => exact Or.inl rfl
    | some r => cases r with
      | none => exact Or.inr ⟨rfl,rfl⟩
      | some _ => exact Or.inl rfl
  | .guard a b, hp, p => by
    have h := ContinuationPlan.sem_congr n R L hQuery a hp.1 p
    have hb := eval_change n z L R hQuery hd b hp.2 p
    change Change p (match sem L a p with | some (some _) => sem L b p | other => other)
      (match sem R a p with | some (some _) => sem R (freeze n z b) p | other => other)
    rw [h]
    cases sem L a p with
    | none => exact Or.inl rfl
    | some r => cases r with
      | none => exact Or.inl rfl
      | some _ => exact hb
  | .alt a b, hp, p => by
    have ha := eval_change n z L R hQuery hd a hp.1 p
    have hb := eval_change n z L R hQuery hd b hp.2 p
    change Change p (ReplayFallbackFusion.orElse (sem L a p) (sem L b p))
      (ReplayFallbackFusion.orElse (sem R (freeze n z a) p) (sem R (freeze n z b) p))
    rcases ha with ha|⟨ha,hf⟩
    · rw [ha]
      cases sem L a p with
      | none => exact Or.inl rfl
      | some r => cases r with
        | none => exact hb
        | some _ => exact Or.inl rfl
    · rw [ha,hf]
      exact Or.inr ⟨rfl,rfl⟩

/-- Star cannot observe replacing an empty success by undefinedness. -/
theorem star_change (A B : Nat → Res) : ∀ p,
    (∀ q, q≤p → Change q (A q) (B q)) → evStar A p=evStar B p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro h
    rcases h p (Nat.le_refl p) with he|⟨ha,hb⟩
    · cases ha : A p with
      | none => rw [evStar_none ha,evStar_none (he.trans ha)]
      | some r => cases r with
        | none => rw [evStar_fail ha,evStar_fail (he.trans ha)]
        | some j =>
          by_cases hj : j<p
          · rw [evStar_ok ha hj,evStar_ok (he.trans ha) hj]
            exact ih j hj (fun q hq => h q (by omega))
          · rw [evStar_stuck ha hj,evStar_stuck (he.trans ha) hj]
    · rw [evStar_stuck ha (by omega),evStar_none hb]

theorem never_fail_star_none (A : Nat → Res) (h : ∀ q, A q≠some none) : ∀ p, evStar A p=none := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    cases ha : A p with
    | none => exact evStar_none ha
    | some r => cases r with
      | none => exact False.elim (h p ha)
      | some j =>
        by_cases hj : j<p
        · rw [evStar_ok ha hj]; exact ih j hj
        · exact evStar_stuck ha hj

/-- A nested star eventually repeats an empty successful inner star or is
already undefined. No position or parser-decrease hypothesis is needed. -/
theorem nested_star_none (A : Nat → Res) (p : Nat) : evStar (evStar A) p=none :=
  never_fail_star_none (evStar A) (fun q => evStar_ne_fail q) p

/-- Positive epsilon returns the actual origin even outside the input range. -/
def identity : Arg := .notP (.notP (.lit []))
def diverge : Leaf := ⟨none,.star identity⟩
def dummy : Leaf := ⟨some [],.lit []⟩

def strict (f : Form) : Form :=
  ⟨f.leaves++[diverge,dummy],freeze f.leaves.length (f.leaves.length+1) f.plan,
    by simpa only [List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using bounded _ _ f.bounded,
    by simp⟩

def done : Form := BodyNormalForm.neg (BodyNormalForm.atom ⟨none,.notP (.lit [])⟩)
def iterate (f : Form) : Form := BodyNormalForm.repeatThen (strict f) identity done

theorem identity_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render nodes ambient ps identity) p=some (some p) := by
  simp [identity,render,evV,stripPrefix?]

theorem diverge_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (render nodes ambient ps (LeafContinuation.raw diverge)) p=none := by
  change evStar (fun q => evV g x s T E (render nodes ambient ps identity) q) p=none
  exact evStar_stuck (identity_eval nodes ambient ps g x s T E p) (by omega)

theorem strict_change (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (f : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    Change p (evV g x s T E (render nodes ambient ps f.syntax) p)
      (evV g x s T E (render nodes ambient ps (strict f).syntax) p) := by
  rw [BodyNormalForm.Form.syntax,BodyNormalForm.Form.syntax,StarThenPlan.control_eval,StarThenPlan.control_eval]
  apply eval_change _ _ _ _ _ _ _ f.bounded p
  · intro i hi q
    rw [show (strict f).leaves=f.leaves++[diverge,dummy] from rfl,
      StarThenPlan.lookup_prefix _ _ i hi]
  · intro q
    have hd : LeafContinuation.lookup (strict f).leaves f.leaves.length=LeafContinuation.raw diverge := by
      simp [strict,LeafContinuation.lookup]
    rw [hd]
    exact diverge_eval nodes ambient ps g x s T E q

theorem sequence_identity (A : Nat → Res) (p : Nat) : sequence A (fun q => some (some q)) p=A p := by
  unfold sequence
  cases A p with
  | none => rfl
  | some r => cases r <;> rfl

theorem repeat_eval (nodes : List Node) (ambient : List Leaf) (ps : List Plan) (f : Form)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.star (render nodes ambient ps f.syntax)) p=
    evV g x s T E (render nodes ambient ps (iterate f).syntax) p := by
  have hstar := star_change (fun q => evV g x s T E (render nodes ambient ps f.syntax) q)
    (fun q => evV g x s T E (render nodes ambient ps (strict f).syntax) q) p
    (fun q _ => strict_change nodes ambient ps f g x s T E q)
  have he := BodyNormalForm.repeatThen_eval nodes ambient ps (strict f) done
    identity (consumer _ _ _) g x s hs T hT E p hp
  have hi : (fun q => evV g x s T E (render nodes ambient ps identity) q)=(fun q => some (some q)) := by
    funext q; exact identity_eval nodes ambient ps g x s T E q
  change sequence (evStar (sequence (fun q => evV g x s T E (render nodes ambient ps (strict f).syntax) q)
    (fun q => evV g x s T E (render nodes ambient ps identity) q)))
    (fun q => evV g x s T E (render nodes ambient ps identity) q) p=_ at he
  rw [hi] at he
  have hid : sequence (fun q => evV g x s T E (render nodes ambient ps (strict f).syntax) q)
      (fun q => some (some q))=(fun q => evV g x s T E (render nodes ambient ps (strict f).syntax) q) := by
    funext q; exact sequence_identity _ q
  rw [hid,sequence_identity] at he
  exact hstar.trans he

end Shallot.MacroPeg.CBV.NullableStarControl
