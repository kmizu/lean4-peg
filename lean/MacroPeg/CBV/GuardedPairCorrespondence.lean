import MacroPeg.CBV.GuardedPairSimulation

namespace Shallot.MacroPeg.CBV.GuardedPairCorrespondence
open GuardedPairSyntax GuardedPairSimulation ScannerFrontier
open MixedScannerPairFusion (Entry arity)

abbrev sourceTable (es : List Entry) (qs : List MExp) (x : List Char) (k : Nat) := tblV (parGrammar es qs) x .callByValuePar k
abbrev targetTable (es : List Entry) (qs : List MExp) (x : List Char) (k : Nat) := tblV (seqGrammar es qs) x .callByValueSeq k

theorem case_rules (es : List Entry) (qs : List MExp) (i : Nat) (r : Entry)
    (hr : es[i]?=some r) (A B : List Char) (hc : r.pairing=some (A,B)) :
    ruleAtM (seqGrammar es qs).rules (3*i+1)=some ⟨2,body true (render es false r.tail)⟩ ∧
    ruleAtM (seqGrammar es qs).rules (3*i+2)=some ⟨2,body false (render es false r.tail)⟩ := by
  constructor
  · simpa [hr,slot,caseRule,arity,hc] using seq_rule es qs i 1 (by omega)
  · simpa [hr,slot,caseRule,arity,hc] using seq_rule es qs i 2 (by omega)

theorem dispatch_next (es : List Entry) (qs : List MExp) (x : List Char) (i : Nat) (r : Entry)
    (hr : es[i]?=some r) (A B : List Char) (hc : r.pairing=some (A,B))
    (E : List (List Char)) (p k : Nat) (hp : p≤x.length) :
    evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (k+1)) E (dispatch A B (3*i+1) (3*i+2)) p=
      evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) (values r x p)
        (render es false r.tail) (finalPos A B x p) := by
  have hh := case_rules es qs i r hr A B hc
  simpa only [values,hc] using dispatch_body_eval E A B (3*i+1) (3*i+2) (render es false r.tail)
    (render_firstOrder _ _ _) hh.1 hh.2 k p hp

theorem dispatch_zero (es : List Entry) (qs : List MExp) (x : List Char) (i : Nat) (r : Entry)
    (hr : es[i]?=some r) (A B : List Char) (hc : r.pairing=some (A,B))
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x 0) E (dispatch A B (3*i+1) (3*i+2)) p=none := by
  have hh := case_rules es qs i r hr A B hc
  rw [dispatch_eval _ E A B _ _ _ _ hh.1 hh.2 rfl rfl p hp]
  cases firstStops A B (sfx x p) <;> rfl

/-- The extra nullary target header costs at most one extra physical call
round for every original round. Query computation is not assumed total. -/
theorem forward_rows (es : List Entry) (qs : List MExp) (hc : check es qs=true) (x : List Char) (k : Nat) :
    Rows true es x (sourceTable es qs x k) (targetTable es qs x (2*k)) := by
  induction k with
  | zero => intro i r hr p hp; exact Or.inl rfl
  | succ k ih =>
    intro i r hr p hp
    change RLe (valAt (sourceTable es qs x (k+1) i (values r x p)) p)
      (valAt (targetTable es qs x (2*(k+1)) (3*i) []) p)
    have hs : ruleAtM (parGrammar es qs).rules i=some (sourceRule es qs i r) := by rw [par_rule,hr]; rfl
    have ht : ruleAtM (seqGrammar es qs).rules (3*i)=some (header es qs i r) := by
      simpa [Nat.add_zero,hr,slot] using seq_rule es qs i 0 (by omega)
    rw [show 2*(k+1)=(2*k+1)+1 by omega]
    rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht [] hp]
    cases hb : r.pairing with
    | none =>
      simp only [sourceRule,sourceBody,header,values,hb]
      exact (forward_evaluator es qs x _ _ (tblV_ok _ _ _ k) ih r.tail [] p hp).trans
        (evV_mono (tblV_step (seqGrammar es qs) x .callByValueSeq (2*k)) _ p)
    | some pair =>
      obtain ⟨A,B⟩ := pair
      simp only [sourceRule,sourceBody,header,hb]
      change RLe (evV _ _ _ _ (values r x p) (.seq (.andP (render es true (query qs i)))
        (.seq (ScannedPairFusion.maxScanner A B) (render es true r.tail))) p)
        (evV _ _ _ _ [] (.seq (.andP (render es false (query qs i))) (dispatch A B (3*i+1) (3*i+2))) p)
      have henv := ReplayFallbackFusion.closed_env (parGrammar es qs) x .callByValuePar (sourceTable es qs x k)
        _ (checked es qs hc i r hr).1 (values r x p) p
      have hquery := (forward_evaluator es qs x _ _ (tblV_ok _ _ _ k) ih (query qs i) [] p hp).trans
        (evV_mono (tblV_step (seqGrammar es qs) x .callByValueSeq (2*k)) _ p)
      cases eq : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) [] (render es true (query qs i)) p with
      | none =>
        have hpref : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) (values r x p)
            (.andP (render es true (query qs i))) p=none := by rw [CallLookahead.evV_peek,henv,eq]; rfl
        rw [evV_seq_none hpref]; exact Or.inl rfl
      | some v =>
        have et := hquery.eq_of_some eq
        cases v with
        | none =>
          have hpref : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) (values r x p)
              (.andP (render es true (query qs i))) p=some none := by rw [CallLookahead.evV_peek,henv,eq]; rfl
          have htpre : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (2*k+1)) []
              (.andP (render es false (query qs i))) p=some none := by rw [CallLookahead.evV_peek,et]; rfl
          rw [evV_seq_fail hpref,evV_seq_fail htpre]; exact RLe.refl _
        | some j =>
          have hpref : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) (values r x p)
              (.andP (render es true (query qs i))) p=some (some p) := by rw [CallLookahead.evV_peek,henv,eq]; rfl
          have htpre : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (2*k+1)) []
              (.andP (render es false (query qs i))) p=some (some p) := by rw [CallLookahead.evV_peek,et]; rfl
          rw [evV_seq_ok hpref,evV_seq_ok htpre,
            evV_seq_ok (ScannedPairFusion.maxScanner_eval _ x .callByValuePar _ (values r x p) A B p hp),
            dispatch_next es qs x i r hr A B hb [] p (2*k) hp]
          exact forward_evaluator es qs x _ _ (tblV_ok _ _ _ k) ih r.tail (values r x p) _
            (Nat.le_trans (finalPos_le A B x p hp) (Nat.le_trans (commonPos_le A B x p hp) hp))

/-- Target dispatch adds a call layer, so every target result is already
present at the same original physical clock. -/
theorem backward_rows (es : List Entry) (qs : List MExp) (hc : check es qs=true) (x : List Char) (k : Nat) :
    Rows false es x (sourceTable es qs x k) (targetTable es qs x k) := by
  induction k with
  | zero => intro i r hr p hp; exact Or.inl rfl
  | succ k ih =>
    intro i r hr p hp
    change RLe (valAt (targetTable es qs x (k+1) (3*i) []) p)
      (valAt (sourceTable es qs x (k+1) i (values r x p)) p)
    have hs : ruleAtM (parGrammar es qs).rules i=some (sourceRule es qs i r) := by rw [par_rule,hr]; rfl
    have ht : ruleAtM (seqGrammar es qs).rules (3*i)=some (header es qs i r) := by
      simpa [Nat.add_zero,hr,slot] using seq_rule es qs i 0 (by omega)
    rw [valAt_tblV_succ hs _ hp,valAt_tblV_succ ht [] hp]
    cases hb : r.pairing with
    | none =>
      simp only [sourceRule,sourceBody,header,values,hb]
      exact backward_evaluator es qs x _ _ (tblV_ok _ _ _ k) ih r.tail [] p hp
    | some pair =>
      obtain ⟨A,B⟩ := pair
      simp only [sourceRule,sourceBody,header,hb]
      change RLe (evV _ _ _ _ [] (.seq (.andP (render es false (query qs i))) (dispatch A B (3*i+1) (3*i+2))) p)
        (evV _ _ _ _ (values r x p) (.seq (.andP (render es true (query qs i)))
        (.seq (ScannedPairFusion.maxScanner A B) (render es true r.tail))) p)
      have henv := ReplayFallbackFusion.closed_env (parGrammar es qs) x .callByValuePar (sourceTable es qs x k)
        _ (checked es qs hc i r hr).1 (values r x p) p
      have hquery := backward_evaluator es qs x _ _ (tblV_ok _ _ _ k) ih (query qs i) [] p hp
      cases eq : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) [] (render es false (query qs i)) p with
      | none =>
        have htpre : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) []
            (.andP (render es false (query qs i))) p=none := by rw [CallLookahead.evV_peek,eq]; rfl
        rw [evV_seq_none htpre]; exact Or.inl rfl
      | some v =>
        have esrc := hquery.eq_of_some eq
        cases v with
        | none =>
          have htpre : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) []
              (.andP (render es false (query qs i))) p=some none := by rw [CallLookahead.evV_peek,eq]; rfl
          have hpref : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) (values r x p)
              (.andP (render es true (query qs i))) p=some none := by rw [CallLookahead.evV_peek,henv,esrc]; rfl
          rw [evV_seq_fail htpre,evV_seq_fail hpref]; exact RLe.refl _
        | some j =>
          have htpre : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) []
              (.andP (render es false (query qs i))) p=some (some p) := by rw [CallLookahead.evV_peek,eq]; rfl
          have hpref : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) (values r x p)
              (.andP (render es true (query qs i))) p=some (some p) := by rw [CallLookahead.evV_peek,henv,esrc]; rfl
          rw [evV_seq_ok htpre,evV_seq_ok hpref,
            evV_seq_ok (ScannedPairFusion.maxScanner_eval _ x .callByValuePar _ (values r x p) A B p hp)]
          cases k with
          | zero => rw [dispatch_zero es qs x i r hr A B hb [] p hp]; exact Or.inl rfl
          | succ k =>
            rw [dispatch_next es qs x i r hr A B hb [] p k hp]
            exact (evV_mono (tblV_step (seqGrammar es qs) x .callByValueSeq k) _ _).trans
              (backward_evaluator es qs x _ _ (tblV_ok _ _ _ (k+1)) ih r.tail (values r x p) _
                (Nat.le_trans (finalPos_le A B x p hp) (Nat.le_trans (commonPos_le A B x p hp) hp)))

theorem defined_iff (es : List Entry) (qs : List MExp) (hc : check es qs=true) (e : MExp)
    (x : List Char) (E : List (List Char)) (p : Nat) (hp : p≤x.length) (v : Option Nat) :
    (∃ k, evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) E (render es true e) p=some v) ↔
      ∃ k, evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) E (render es false e) p=some v := by
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨2*k,(forward_evaluator es qs x _ _ (tblV_ok _ _ _ k) (forward_rows es qs hc x k) e E p hp).eq_of_some hk⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,(backward_evaluator es qs x _ _ (tblV_ok _ _ _ k) (backward_rows es qs hc x k) e E p hp).eq_of_some hk⟩

theorem stable_eq (es : List Entry) (qs : List MExp) (hc : check es qs=true) (e : MExp) (x : List Char) :
    evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x (iterBoundV (parGrammar es qs) x)) [] (render es true e) x.length=
      evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (iterBoundV (seqGrammar es qs) x)) [] (render es false e) x.length := by
  have hh (v : Option Nat) :
      evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x (iterBoundV (parGrammar es qs) x)) [] (render es true e) x.length=some v ↔
        evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (iterBoundV (seqGrammar es qs) x)) [] (render es false e) x.length=some v :=
    (tblV_stable _ x _ (Nat.le_refl _)).symm.trans
      ((defined_iff es qs hc e x [] x.length (Nat.le_refl _) v).trans (tblV_stable _ x _ (Nat.le_refl _)))
  cases hs : evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x (iterBoundV (parGrammar es qs) x)) [] (render es true e) x.length with
  | some v => exact ((hh v).mp hs).symm
  | none =>
    cases ht : evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x (iterBoundV (seqGrammar es qs) x)) [] (render es false e) x.length with
    | none => rfl
    | some v => have he := (hh v).mpr ht; rw [hs] at he; cases he

theorem observations_iff (es : List Entry) (qs : List MExp) (hc : check es qs=true) (e : MExp)
    (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar es qs) .callByValuePar (render es true e) x rest ↔
      SObs (seqGrammar es qs) .callByValueSeq (render es false e) x rest := by
  rw [←decideObsV_iff (par_firstOrder es qs) (by decide) (render_firstOrder es true e),
    ←decideObsV_iff (seq_firstOrder es qs) (by decide) (render_firstOrder es false e)]
  unfold decideObsV
  rw [stable_eq es qs hc e x]

theorem undefined_iff (es : List Entry) (qs : List MExp) (hc : check es qs=true) (e : MExp) (x : List Char) :
    (∀ k, evV (parGrammar es qs) x .callByValuePar (sourceTable es qs x k) [] (render es true e) x.length=none) ↔
      ∀ k, evV (seqGrammar es qs) x .callByValueSeq (targetTable es qs x k) [] (render es false e) x.length=none :=
  BoundedBodyRewrite.undefined_of_observations _ _ (par_firstOrder es qs) (seq_firstOrder es qs) _ _ (by decide) (by decide)
    _ _ (render_firstOrder _ _ _) (render_firstOrder _ _ _) x (fun rest => observations_iff es qs hc e x rest)

end Shallot.MacroPeg.CBV.GuardedPairCorrespondence
