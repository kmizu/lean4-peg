import MacroPeg.CBV.SequentialTotalStages
import MacroPeg.CBV.SequentialTotalLayout
import MacroPeg.CBV.SequentialTotalFirstOrder

/-! Discharge the transformation's recursive-row assumptions by induction on
remaining input length and on the finite empty-call stage. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalCorrectness
open SequentialTotalSyntax SequentialTotalControl SequentialTotalCalls SequentialTotalStages
open SequentialLocalCorrectness (canonical)
open SequentialLocalClosure (rounds)

def EmptyAt (g : MGrammar) (x : List Char) (p j : Nat) : Prop :=
  ∀ i r (hr : ruleAtM g.rules i=some r), ∀ m,
    valAt (canonical (target g) x (emptyIndex g i j m) []) p=
      modeResult m p (rounds g x p (canonical g x) j ⟨i,ruleAtM_lt hr⟩)

def OrdinaryAt (g : MGrammar) (x : List Char) (p : Nat) : Prop :=
  ∀ i r, ruleAtM g.rules i=some r → ∀ W, r.arity=W.length → ∀ m,
    valAt (canonical (target g) x (ordinaryIndex g i m) W) p=
      modeResult m p (valAt (canonical g x i W) p)

def StageExpression (g : MGrammar) (x : List Char) (p j : Nat) : Prop :=
  ∀ E e, e.FirstOrder → Realizes (target g) x (canonical (target g) x) E (compile g j e) p
    (evV g x .callByValueSeq (stage g x p j) E e p)

/-- Every target mode is the *total* result flag of the actual source
evaluation, including arbitrary incoming captures and mutually recursive
parameterized calls. The source undefined result gives finite failure of
all flags, rather than activating the source's finite-failure control. -/
theorem position (g : MGrammar) (hg : g.FirstOrder) (x : List Char) : ∀ p, p≤x.length →
    OrdinaryAt g x p ∧
    (∀ E e, e.FirstOrder → Realizes (target g) x (canonical (target g) x) E
      (compile g g.rules.length e) p (evV g x .callByValueSeq (canonical g x) E e p)) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp
    have make (j : Nat) (hj : j≤g.rules.length) (empty : EmptyAt g x p j) :
        StageExpression g x p j := by
      intro E e he
      apply SequentialTotalExpression.expression g (target g) x (stage g x p j)
        (canonical (target g) x) E j p hp (stage_descending g x p j) _ _ e he
      · constructor
        · intro i r hr m
          exact ⟨_,ordinary_rule g i r hr m⟩
        · intro i r hr m W q hw hq
          rw [lower_row g x p j i W q hp hq]
          exact (ih q hq (by omega)).1 i r hr W hw.symm m
        · intro i r hr m
          have ht := empty_rule g i r hr j hj m
          rw [emptyCall,evV_call_seq ht rfl,evSeq_nil]
          change valAt (canonical (target g) x (emptyIndex g i j m) []) p=_
          rw [empty i r hr m,here_row g x p j i r hr (List.replicate r.arity []) hp]
      · intro a ha q hq
        rw [lower_expression g x p j E a q hp hq]
        exact (ih q hq (by omega)).2 E a ha
    have staged : ∀ j, j≤g.rules.length → EmptyAt g x p j ∧ StageExpression g x p j := by
      intro j
      induction j with
      | zero =>
        intro hj
        have hz : EmptyAt g x p 0 := by
          intro i r hr m
          have ht := empty_rule g i r hr 0 (by omega) m
          rw [SequentialLocalCorrectness.canonical_unfold (target g) x _ _ ht [] rfl p hp]
          cases m <;> rfl
        exact ⟨hz,make 0 hj hz⟩
      | succ j ij =>
        intro hj
        obtain ⟨ej,xj⟩ := ij (by omega)
        have enext : EmptyAt g x p (j+1) := by
          intro i r hr m
          have ht := empty_rule g i r hr (j+1) hj m
          rw [SequentialLocalCorrectness.canonical_unfold (target g) x _ _ ht [] rfl p hp]
          have he := SequentialResultSyntax.emptyBody_firstOrder r (hg r (ruleAtM_mem hr))
          have hx := get_correct _ _ (xj [] (SequentialResultSyntax.emptyBody r) he) m
          rw [next_round g x p j i r hr (hg r (ruleAtM_mem hr))]
          exact hx
        exact ⟨enext,make (j+1) hj enext⟩
    have finalStage := (staged g.rules.length (Nat.le_refl _)).2
    have full : ∀ E e, e.FirstOrder → Realizes (target g) x (canonical (target g) x) E
        (compile g g.rules.length e) p (evV g x .callByValueSeq (canonical g x) E e p) := by
      intro E e he
      have h := finalStage E e he
      rw [full_expression g x p hp E e] at h
      exact h
    refine ⟨?_,full⟩
    intro i r hr W hlen m
    rw [SequentialLocalCorrectness.canonical_unfold (target g) x _ _
      (ordinary_rule g i r hr m) W hlen p hp]
    have h := get_correct _ _ (full W r.body (hg r (ruleAtM_mem hr))) m
    rw [SequentialLocalCorrectness.canonical_unfold g x i r hr W hlen p hp]
    exact h

theorem expression (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    Realizes (target g) x (canonical (target g) x) E (compile g g.rules.length e) p
      (evV g x .callByValueSeq (canonical g x) E e p) :=
  (position g hg x p hp).2 E e he

theorem start_correct (g : MGrammar) (hg : g.FirstOrder) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV (target g) x .callByValueSeq (canonical (target g) x) E (start g e) p=
      successResult (evV g x .callByValueSeq (canonical g x) E e p) :=
  success_correct _ _ (expression g hg x E e he p hp)

end Shallot.MacroPeg.CBV.SequentialTotalCorrectness
