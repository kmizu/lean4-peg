import MacroPeg.CBV.SelectedProducerSimulation

namespace Shallot.MacroPeg.CBV.SelectedProducerCorrespondence
open SelectedProducerNormalization
open SelectedProducerSimulation (Rows Simulation)

abbrev sourceTable (g : MGrammar) (x : List Char) (k : Nat) := tblV g x .callByValuePar k
abbrev targetTable (g : MGrammar) (ps : Selection) (x : List Char) (k : Nat) := tblV (target g ps) x .callByValuePar k
abbrev sourceStable (g : MGrammar) (x : List Char) := StablePar.table g x
abbrev targetStable (g : MGrammar) (ps : Selection) (x : List Char) := StablePar.table (target g ps) x

theorem forward_evaluator (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char) (k : Nat)
    (rows : Rows g ps x (sourceStable g x) (sourceTable g x k) (targetStable g ps x))
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV g x .callByValuePar (sourceTable g x k) E e p)
      (evV (target g ps) x .callByValuePar (targetStable g ps x) E e p) := by
  apply SelectedProducerSimulation.evaluator g ps hc g (target g ps) x _ _ _
    ⟨fun _ => rfl,arities g ps,tblV_ok _ _ _ k,tblV_sound (source_firstOrder g ps hc) (by decide) k,rows,?_⟩ E e he hcon p hp
  intro i r hr d hd F q j hq ea _
  have h := (StablePar.eval_le g x k F d.head q hq).eq_of_some ea
  rwa [ReplayFallbackFusion.closed_env _ _ _ _ d.head (checked g ps hc i r hr d hd).2.2 F q] at h

theorem backward_evaluator (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char) (k : Nat)
    (rows : Rows g ps x (sourceStable g x) (targetTable g ps x k) (sourceStable g x))
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV (target g ps) x .callByValuePar (targetTable g ps x k) E e p)
      (evV g x .callByValuePar (sourceStable g x) E e p) := by
  apply SelectedProducerSimulation.evaluator g ps hc (target g ps) g x _ _ _
    ⟨arities g ps,fun _ => rfl,tblV_ok _ _ _ k,tblV_sound (target_firstOrder g ps hc) (by decide) k,rows,?_⟩ E e he hcon p hp
  intro i r hr d hd F q j hq _ eb
  rwa [ReplayFallbackFusion.closed_env _ _ _ _ d.head (checked g ps hc i r hr d hd).2.2 F q] at eb

theorem forward_rows (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char) (k : Nat) :
    Rows g ps x (sourceStable g x) (sourceTable g x k) (targetStable g ps x) := by
  induction k with
  | zero => constructor
            · intro i r hr hs W hw p hp; exact Or.inl rfl
            · intro i r hr d hs w hw p j hj; exact Or.inl rfl
  | succ k ih =>
    constructor
    · intro i r hr hs W hw p hp
      have ht : ruleAtM (target g ps).rules i=some ⟨r.arity,r.body⟩ := by rw [target_rule,hr]; simp [body,hs]
      rw [valAt_tblV_succ hr W hp,StablePar.row_eq _ x i _ ht W hw p hp]
      exact forward_evaluator g ps hc x k ih W r.body (source_firstOrder g ps hc _ (ruleAtM_mem hr)) (body_conforms g ps hc i r hr) p hp
    · intro i r hr d hs w hw p j hj
      have hp := hj.1.1
      have hsel := checked g ps hc i r hr d hs
      have ht : ruleAtM (target g ps).rules i=some ⟨r.arity,.seq (.param 0) d.tail⟩ := by rw [target_rule,hr]; simp [body,hs]
      have hw1 : [w]∈words (subStrs x) r.arity := by rw [hsel.1]; exact StablePar.singleton_mem x w hw
      rw [valAt_tblV_succ hr [w] hp,StablePar.row_eq _ x i _ ht [w] hw1 p hp,hsel.2.1]
      have hfo := source_firstOrder g ps hc _ (ruleAtM_mem hr)
      have hcon := body_conforms g ps hc i r hr
      rw [hsel.2.1] at hfo hcon
      have hrep := GuardedReplayControl.aligned_replay (target g ps) x w .callByValuePar (targetStable g ps x) p j hj.1
      rw [evV_seq_ok hrep]
      cases ed : evV g x .callByValuePar (sourceTable g x k) [w] d.head p with
      | none => rw [evV_seq_none ed]; exact Or.inl rfl
      | some v =>
        have he := (StablePar.eval_le g x k [w] d.head p hp).eq_of_some ed
        rw [ReplayFallbackFusion.closed_env _ _ _ _ d.head hsel.2.2 [w] p,hj.2] at he
        cases v with
        | none => cases he
        | some q =>
          have hq : q=j := by simpa only [Option.some.injEq] using he.symm
          subst q
          rw [evV_seq_ok ed]
          exact forward_evaluator g ps hc x k ih [w] d.tail hfo.2 (Bool.and_eq_true_iff.mp hcon).2 j hj.1.2.1

theorem backward_rows (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char) (k : Nat) :
    Rows g ps x (sourceStable g x) (targetTable g ps x k) (sourceStable g x) := by
  induction k with
  | zero => constructor
            · intro i r hr hs W hw p hp; exact Or.inl rfl
            · intro i r hr d hs w hw p j hj; exact Or.inl rfl
  | succ k ih =>
    constructor
    · intro i r hr hs W hw p hp
      have ht : ruleAtM (target g ps).rules i=some ⟨r.arity,r.body⟩ := by rw [target_rule,hr]; simp [body,hs]
      rw [valAt_tblV_succ ht W hp,StablePar.row_eq _ x i _ hr W hw p hp]
      exact backward_evaluator g ps hc x k ih W r.body (source_firstOrder g ps hc _ (ruleAtM_mem hr)) (body_conforms g ps hc i r hr) p hp
    · intro i r hr d hs w hw p j hj
      have hp := hj.1.1
      have hsel := checked g ps hc i r hr d hs
      have ht : ruleAtM (target g ps).rules i=some ⟨r.arity,.seq (.param 0) d.tail⟩ := by rw [target_rule,hr]; simp [body,hs]
      have hw1 : [w]∈words (subStrs x) r.arity := by rw [hsel.1]; exact StablePar.singleton_mem x w hw
      rw [valAt_tblV_succ ht [w] hp,StablePar.row_eq _ x i _ hr [w] hw1 p hp,hsel.2.1]
      have hfo := source_firstOrder g ps hc _ (ruleAtM_mem hr)
      have hcon := body_conforms g ps hc i r hr
      rw [hsel.2.1] at hfo hcon
      have hrep := GuardedReplayControl.aligned_replay (target g ps) x w .callByValuePar (targetTable g ps x k) p j hj.1
      have hd : evV g x .callByValuePar (sourceStable g x) [w] d.head p=some (some j) := by
        rw [ReplayFallbackFusion.closed_env _ _ _ _ d.head hsel.2.2 [w] p]; exact hj.2
      rw [evV_seq_ok hrep,evV_seq_ok hd]
      exact backward_evaluator g ps hc x k ih [w] d.tail hfo.2 (Bool.and_eq_true_iff.mp hcon).2 j hj.1.2.1

theorem stable_eq (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (sourceStable g x) E e p=
      evV (target g ps) x .callByValuePar (targetStable g ps x) E e p :=
  WordExpansionRefinement.antisymm
    (forward_evaluator g ps hc x _ (forward_rows g ps hc x _) E e he hcon p hp)
    (backward_evaluator g ps hc x _ (backward_rows g ps hc x _) E e he hcon p hp)

theorem observations_iff (g : MGrammar) (ps : Selection) (hc : check g ps=true)
    (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValuePar e x rest ↔ SObs (target g ps) .callByValuePar e x rest := by
  rw [←decideObsV_iff (source_firstOrder g ps hc) (by decide) he,
    ←decideObsV_iff (target_firstOrder g ps hc) (by decide) he]
  unfold decideObsV
  rw [stable_eq g ps hc x [] e he hcon x.length (Nat.le_refl _)]

theorem defined_iff (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (p : Nat) (hp : p≤x.length) (v : Option Nat) :
    (∃ k, evV g x .callByValuePar (sourceTable g x k) E e p=some v) ↔
      ∃ k, evV (target g ps) x .callByValuePar (targetTable g ps x k) E e p=some v := by
  constructor
  · rintro ⟨k,hk⟩
    have hs := (StablePar.eval_le g x k E e p hp).eq_of_some hk
    rw [stable_eq g ps hc x E e he hcon p hp] at hs
    exact ⟨_,hs⟩
  · rintro ⟨k,hk⟩
    have hs := (StablePar.eval_le (target g ps) x k E e p hp).eq_of_some hk
    rw [←stable_eq g ps hc x E e he hcon p hp] at hs
    exact ⟨_,hs⟩

theorem undefined_iff (g : MGrammar) (ps : Selection) (hc : check g ps=true) (x : List Char)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hcon : conforms ps e=true) (p : Nat) (hp : p≤x.length) :
    (∀ k, evV g x .callByValuePar (sourceTable g x k) E e p=none) ↔
      (∀ k, evV (target g ps) x .callByValuePar (targetTable g ps x k) E e p=none) := by
  constructor
  · intro h k
    cases ht : evV (target g ps) x .callByValuePar (targetTable g ps x k) E e p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff g ps hc x E e he hcon p hp v).mpr ⟨k,ht⟩
      rw [h j] at hj; cases hj
  · intro h k
    cases ht : evV g x .callByValuePar (sourceTable g x k) E e p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff g ps hc x E e he hcon p hp v).mp ⟨k,ht⟩
      rw [h j] at hj; cases hj

end Shallot.MacroPeg.CBV.SelectedProducerCorrespondence
