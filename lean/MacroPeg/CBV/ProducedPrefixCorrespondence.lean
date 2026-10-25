import MacroPeg.CBV.ProducedPrefixEvaluation

namespace Shallot.MacroPeg.CBV.ProducedPrefixCorrespondence
open ProducedPrefixCompiler
open ProducedPrefixEvaluation
open ReplayControlFusion (Part Plan)

theorem tables_rows (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (x : List Char) (k : Nat) : Rows ps es x k := by
  induction k with
  | zero =>
    intro i e hi
    cases e with
    | growth r => intro W p hp; rfl
    | origin P => intro W p hp; rfl
    | produced D B => intro w p j h; rfl
  | succ k ih =>
    intro i e hi
    have hs : ruleAtM (source ps es).rules i=some ⟨1,body ps e⟩ := by rw [source_rule,hi]; rfl
    have ht : ruleAtM (normalized ps es).rules i=some ⟨1,normalizedBody ps e⟩ := by rw [normalized_rule _ _ hc,hi]; rfl
    have hfo := hg ⟨1,body ps e⟩ (ruleAtM_mem hs)
    have hcon := (checked ps es hc).2.2 e (List.mem_of_getElem? hi)
    cases e with
    | growth r =>
      intro W p hp
      rw [valAt_tblV_succ hs W hp,valAt_tblV_succ ht W hp]
      exact evaluator ps es hg hc x k ih W _ hfo hcon p hp
    | origin P =>
      intro W p hp
      rw [valAt_tblV_succ hs W hp,valAt_tblV_succ ht W hp]
      exact evaluator ps es hg hc x k ih W _ hfo hcon p hp
    | produced D B =>
      intro w p j h
      rw [valAt_tblV_succ hs [w] h.1.1,valAt_tblV_succ ht [w] h.1.1]
      have hD := (checked ps es hc).2.1 (.produced D B) (List.mem_of_getElem? hi)
      have hd : evV (source ps es) x .callByValuePar (sourceTable ps es x k) [w] D p=some (some j) :=
        (producer_eval ps es x k [w] D hD p).trans h.2
      have hp0 := GuardedReplayControl.aligned_replay (normalized ps es) x w .callByValuePar (normalizedTable ps es x k) p j h.1
      change evV (source ps es) x .callByValuePar (sourceTable ps es x k) [w] (.seq D B) p=
        evV (normalized ps es) x .callByValuePar (normalizedTable ps es x k) [w] (.seq (.param 0) B) p
      rw [evV_seq_ok hd,evV_seq_ok hp0]
      exact evaluator ps es hg hc x k ih [w] B hfo.2 (Bool.and_eq_true_iff.mp hcon).2 j h.1.2.1

theorem normalization_evaluator_eq (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (p : Nat) (hp : p≤x.length) :
    evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p=
      evV (normalized ps es) x .callByValuePar (normalizedTable ps es x k) E e p :=
  evaluator ps es hg hc x k (tables_rows ps es hg hc x k) E e he hs p hp

theorem normalization_observations (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔ SObs (normalized ps es) .callByValuePar e x rest := by
  have hf : (normalized ps es).FirstOrder := MixedForwardingCompiler.original_firstOrder _ _ (checked ps es hc).1
  rw [←decideObsV_iff hg (by decide) he,←decideObsV_iff hf (by decide) he]
  have hd : decideObsV .callByValuePar (source ps es) x e=decideObsV .callByValuePar (normalized ps es) x e := by
    unfold decideObsV
    rw [ScannerPairFusion.stable_result_eq (source ps es) (normalized ps es) x .callByValuePar .callByValuePar e e
      (fun k => normalization_evaluator_eq ps es hg hc x k [] e he hs x.length (Nat.le_refl _))]
  rw [hd]

theorem observations_iff (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source ps es) .callByValuePar e x rest ↔
      SObs (target ps es) .callByValueSeq (render ps es e) x rest :=
  (normalization_observations ps es hg hc e he hs x rest).trans
    (MixedForwardingCorrespondence.observations_iff _ _ (checked ps es hc).1 e he x rest)

theorem undefined_iff (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (x : List Char) :
    (∀ k, evV (source ps es) x .callByValuePar (sourceTable ps es x k) [] e x.length=none) ↔
      (∀ k, evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) [] (render ps es e) x.length=none) :=
  BoundedBodyRewrite.undefined_of_observations _ _ hg (MixedForwardingCompiler.target_firstOrder _ _)
    .callByValuePar .callByValueSeq (by decide) (by decide) e _ he (MixedForwardingCompiler.render_firstOrder _ _ e) x
    (fun rest => observations_iff ps es hg hc e he hs x rest)

theorem physical_bounds (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (x : List Char) (k : Nat) (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) (p : Nat) (hp : p≤x.length) :
    RLe (evV (source ps es) x .callByValuePar (sourceTable ps es x k) E e p)
      (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p) ∧
    RLe (evV (target ps es) x .callByValueSeq (tblV (target ps es) x .callByValueSeq k) E (render ps es e) p)
      (evV (source ps es) x .callByValuePar (sourceTable ps es x ((es.length+2)*k)) E e p) := by
  have hb := MixedForwardingCorrespondence.physical_bounds _ _ (checked ps es hc).1 x k E e he p hp
  have hlen : (entries ps es).length=es.length := by simp [entries]
  rw [hlen] at hb
  rw [normalization_evaluator_eq ps es hg hc x k E e he hs p hp,
    normalization_evaluator_eq ps es hg hc x ((es.length+2)*k) E e he hs p hp]
  exact hb

theorem language_translation (ps : List Part) (es : List Entry) (hg : (source ps es).FirstOrder) (hc : check ps es=true)
    (e : MExp) (he : e.FirstOrder) (hs : conforms es e=true) :
    ∃ (g : MGrammar) (entry : MExp), g.FirstOrder ∧ entry.FirstOrder ∧
      ∀ x, SObs (source ps es) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq entry x (some []) :=
  ⟨target ps es,render ps es e,MixedForwardingCompiler.target_firstOrder _ _,MixedForwardingCompiler.render_firstOrder _ _ e,
    fun x => observations_iff ps es hg hc e he hs x (some [])⟩

end Shallot.MacroPeg.CBV.ProducedPrefixCorrespondence
