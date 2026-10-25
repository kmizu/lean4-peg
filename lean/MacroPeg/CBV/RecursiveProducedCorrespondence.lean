import MacroPeg.CBV.RecursiveProducedSimulation

namespace Shallot.MacroPeg.CBV.RecursiveProducedCorrespondence
open RecursiveProducedCompiler
open RecursiveProducedSimulation (Rows Captured Declared)
open ReplayControlFusion (Part)

abbrev sourceTable (ps : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (source ps es) x .callByValuePar k
abbrev normalizedTable (ps : List Part) (es : List Entry) (x : List Char) (k : Nat) := tblV (normalized ps es) x .callByValuePar k
abbrev sourceStable (ps : List Part) (es : List Entry) (x : List Char) := StablePar.table (source ps es) x
abbrev normalizedStable (ps : List Part) (es : List Entry) (x : List Char) := StablePar.table (normalized ps es) x

theorem source_declared (ps : List Part) (es : List Entry) : Declared (source ps es) es := by
  intro i
  rw [source_rule]
  cases es[i]? <;> rfl

theorem normalized_declared (ps : List Part) (es : List Entry) (hc : check ps es=true) : Declared (normalized ps es) es := by
  intro i
  rw [normalized_rule ps es hc]
  cases es[i]? <;> rfl

theorem forward_evaluator (ps : List Part) (es : List Entry) (hc : check ps es=true) (x : List Char) (k : Nat)
    (rows : Rows es (source ps es) x (sourceStable ps es x) (sourceTable ps es x k) (normalizedStable ps es x))
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p)
      (evV (normalized ps es) x .callByValuePar (normalizedStable ps es x) E e p) := by
  apply RecursiveProducedSimulation.evaluator es (source ps es) _ _ x _ _ _
    (source_declared ps es) (normalized_declared ps es hc) (tblV_ok _ _ _ k)
    (tblV_sound (source_firstOrder ps es hc) (by decide) k) rows ?_ E e he hs p hp
  intro i D B hi F q j hq ha _
  have hd := (StablePar.eval_le (source ps es) x k F D q hq).eq_of_some ha
  rw [ReplayFallbackFusion.closed_env _ _ _ _ D (entry_checked ps es hc _ (List.mem_of_getElem? hi)) F q] at hd
  exact hd

theorem backward_evaluator (ps : List Part) (es : List Entry) (hc : check ps es=true) (x : List Char) (k : Nat)
    (rows : Rows es (source ps es) x (sourceStable ps es x) (normalizedTable ps es x k) (sourceStable ps es x))
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV (normalized ps es) x .callByValuePar (normalizedTable ps es x k) E e p)
      (evV (source ps es) x .callByValuePar (sourceStable ps es x) E e p) := by
  apply RecursiveProducedSimulation.evaluator es (source ps es) _ _ x _ _ _
    (normalized_declared ps es hc) (source_declared ps es) (tblV_ok _ _ _ k)
    (tblV_sound (normalized_firstOrder ps es hc) (by decide) k) rows ?_ E e he hs p hp
  intro i D B hi F q j hq _ hb
  rwa [ReplayFallbackFusion.closed_env _ _ _ _ D (entry_checked ps es hc _ (List.mem_of_getElem? hi)) F q] at hb

/-- Forward rows are proved against an actual stable normalized table. A
producer's capture invariant is the original stable parser's own result. -/
theorem forward_rows (ps : List Part) (es : List Entry) (hc : check ps es=true) (x : List Char) (k : Nat) :
    Rows es (source ps es) x (sourceStable ps es x) (sourceTable ps es x k) (normalizedStable ps es x) := by
  induction k with
  | zero =>
    intro i e hi w hw p hp
    cases e with
    | growth r => exact Or.inl rfl
    | origin P => exact Or.inl rfl
    | produced D B => intro j hj; exact Or.inl rfl
  | succ k ih =>
    intro i e hi w hw p hp
    have hsrc : ruleAtM (source ps es).rules i=some ⟨1,body ps e⟩ := by rw [source_rule,hi]; rfl
    have hnorm : ruleAtM (normalized ps es).rules i=some ⟨1,normalizedBody ps e⟩ := by rw [normalized_rule ps es hc,hi]; rfl
    have hfo := source_firstOrder ps es hc _ (ruleAtM_mem hsrc)
    have hcon := conforms_body ps es hc e (List.mem_of_getElem? hi)
    have hw1 := StablePar.singleton_mem x w hw
    cases e with
    | growth r =>
      rw [valAt_tblV_succ hsrc [w] hp,StablePar.row_eq _ x i _ hnorm [w] hw1 p hp]
      exact forward_evaluator ps es hc x k ih [w] _ hfo hcon p hp
    | origin P =>
      rw [valAt_tblV_succ hsrc [w] hp,StablePar.row_eq _ x i _ hnorm [w] hw1 p hp]
      exact forward_evaluator ps es hc x k ih [w] _ hfo hcon p hp
    | produced D B =>
      intro j hj
      rw [valAt_tblV_succ hsrc [w] hp,StablePar.row_eq _ x i _ hnorm [w] hw1 p hp]
      change RLe (evV (source ps es) x .callByValuePar (sourceTable ps es x k) [w] (.seq D B) p)
        (evV (normalized ps es) x .callByValuePar (normalizedStable ps es x) [w] (.seq (.param 0) B) p)
      have hr := GuardedReplayControl.aligned_replay (normalized ps es) x w .callByValuePar (normalizedStable ps es x) p j hj.1
      rw [evV_seq_ok hr]
      have hclosed := entry_checked ps es hc (.produced D B) (List.mem_of_getElem? hi)
      cases hd : evV (source ps es) x .callByValuePar (sourceTable ps es x k) [w] D p with
      | none => rw [evV_seq_none hd]; exact Or.inl rfl
      | some v =>
        have hstable := (StablePar.eval_le (source ps es) x k [w] D p hp).eq_of_some hd
        rw [ReplayFallbackFusion.closed_env _ _ _ _ D hclosed [w] p,hj.2] at hstable
        cases v with
        | none => cases hstable
        | some q =>
          have hq : q=j := by simpa only [Option.some.injEq] using hstable.symm
          subst q
          rw [evV_seq_ok hd]
          exact forward_evaluator ps es hc x k ih [w] B hfo.2 (Bool.and_eq_true_iff.mp hcon).2 j hj.1.2.1

/-- Reverse rows rebuild the source prefix from the very capture obtained
by argument evaluation. No closed parser totality premise is required. -/
theorem backward_rows (ps : List Part) (es : List Entry) (hc : check ps es=true) (x : List Char) (k : Nat) :
    Rows es (source ps es) x (sourceStable ps es x) (normalizedTable ps es x k) (sourceStable ps es x) := by
  induction k with
  | zero =>
    intro i e hi w hw p hp
    cases e with
    | growth r => exact Or.inl rfl
    | origin P => exact Or.inl rfl
    | produced D B => intro j hj; exact Or.inl rfl
  | succ k ih =>
    intro i e hi w hw p hp
    have hsrc : ruleAtM (source ps es).rules i=some ⟨1,body ps e⟩ := by rw [source_rule,hi]; rfl
    have hnorm : ruleAtM (normalized ps es).rules i=some ⟨1,normalizedBody ps e⟩ := by rw [normalized_rule ps es hc,hi]; rfl
    have hfo := source_firstOrder ps es hc _ (ruleAtM_mem hsrc)
    have hcon := conforms_body ps es hc e (List.mem_of_getElem? hi)
    have hw1 := StablePar.singleton_mem x w hw
    cases e with
    | growth r =>
      rw [valAt_tblV_succ hnorm [w] hp,StablePar.row_eq _ x i _ hsrc [w] hw1 p hp]
      exact backward_evaluator ps es hc x k ih [w] _ hfo hcon p hp
    | origin P =>
      rw [valAt_tblV_succ hnorm [w] hp,StablePar.row_eq _ x i _ hsrc [w] hw1 p hp]
      exact backward_evaluator ps es hc x k ih [w] _ hfo hcon p hp
    | produced D B =>
      intro j hj
      rw [valAt_tblV_succ hnorm [w] hp,StablePar.row_eq _ x i _ hsrc [w] hw1 p hp]
      change RLe (evV (normalized ps es) x .callByValuePar (normalizedTable ps es x k) [w] (.seq (.param 0) B) p)
        (evV (source ps es) x .callByValuePar (sourceStable ps es x) [w] (.seq D B) p)
      have hr := GuardedReplayControl.aligned_replay (normalized ps es) x w .callByValuePar (normalizedTable ps es x k) p j hj.1
      have hd : evV (source ps es) x .callByValuePar (sourceStable ps es x) [w] D p=some (some j) := by
        rw [ReplayFallbackFusion.closed_env _ _ _ _ D (entry_checked ps es hc _ (List.mem_of_getElem? hi)) [w] p]
        exact hj.2
      rw [evV_seq_ok hr,evV_seq_ok hd]
      exact backward_evaluator ps es hc x k ih [w] B hfo.2 (Bool.and_eq_true_iff.mp hcon).2 j hj.1.2.1

/-- Original and normalized stable results agree. Recursive producer calls
may spend different finite physical clocks; no same-clock equality is claimed. -/
theorem stable_eq (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true)
    (p : Nat) (hp : p≤x.length) :
    evV (source ps es) x .callByValuePar (sourceStable ps es x) E e p=
      evV (normalized ps es) x .callByValuePar (normalizedStable ps es x) E e p :=
  WordExpansionRefinement.antisymm
    (forward_evaluator ps es hc x _ (forward_rows ps es hc x _) E e he hs p hp)
    (backward_evaluator ps es hc x _ (backward_rows ps es hc x _) E e he hs p hp)

theorem normalization_observations (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (normalized ps es) .callByValuePar e x rest := by
  rw [←decideObsV_iff (source_firstOrder ps es hc) (by decide) he,
    ←decideObsV_iff (normalized_firstOrder ps es hc) (by decide) he]
  unfold decideObsV
  rw [stable_eq ps es hc x [] e he hs x.length (Nat.le_refl _)]

theorem observations_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔
      SObs (target ps es) .callByValueSeq (render ps es e) x rest :=
  (normalization_observations ps es hc e he hs x rest).trans
    (MixedForwardingCorrespondence.observations_iff _ _ (valid ps es hc) e he x rest)

/-- Explicit cofinality in the real tables. The finite saturation bounds
depend on the input, as in the existing first-order CBV decision proof. -/
theorem physical_bounds (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true)
    (p : Nat) (hp : p≤x.length) :
    RLe (evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p)
      (evV (target ps es) x .callByValueSeq
        (tblV (target ps es) x .callByValueSeq (iterBoundV (normalized ps es) x)) E (render ps es e) p) ∧
    RLe (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p)
      (evV (source ps es) x .callByValuePar (sourceStable ps es x) E e p) := by
  constructor
  · have h := StablePar.eval_le (source ps es) x k E e p hp
    rw [stable_eq ps es hc x E e he hs p hp] at h
    exact h.trans (MixedForwardingCorrespondence.physical_bounds _ _ (valid ps es hc) x
      (iterBoundV (normalized ps es) x) E e he p hp).1
  · have h := (MixedForwardingCorrespondence.physical_bounds _ _ (valid ps es hc) x k E e he p hp).2
    exact h.trans (backward_evaluator ps es hc x _ (backward_rows ps es hc x _) E e he hs p hp)

theorem defined_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true)
    (p : Nat) (hp : p≤x.length) (v : Option Nat) :
    (∃ k, evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p=some v) ↔
      ∃ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p=some v := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨_,(physical_bounds ps es hc x k E e he hs p hp).1.eq_of_some hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨_,(physical_bounds ps es hc x k E e he hs p hp).2.eq_of_some hk⟩

theorem undefined_iff (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (x : List Char) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true)
    (p : Nat) (hp : p≤x.length) :
    (∀ k, evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p=none) := by
  constructor
  · intro h k
    cases ht : evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff ps es hc x E e he hs p hp v).mpr ⟨k,ht⟩
      rw [h j] at hj
      cases hj
  · intro h k
    cases ht : evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p with
    | none => rfl
    | some v =>
      obtain ⟨j,hj⟩ := (defined_iff ps es hc x E e he hs p hp v).mp ⟨k,ht⟩
      rw [h j] at hj
      cases hj

theorem language_translation (ps : List Part) (es : List Entry) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target ps es,render ps es e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff ps es hc e he hs x (some [])⟩

end Shallot.MacroPeg.CBV.RecursiveProducedCorrespondence
