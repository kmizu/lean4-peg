import MacroPeg.CBV.SequentialResultZero
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.SequentialResultCompiler
open SequentialResultSyntax SequentialResultNormal SequentialResultZero
open EmptyResultObservation (project gate)

theorem physical_rows (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (k : Nat) :
    Rows g x (tblV g x .callByValueSeq k) (tblV (target g) x .callByValueSeq k) := by
  induction k with
  | zero => constructor <;> intros <;> rfl
  | succ k ih =>
    constructor
    · intro i r hr W p hp
      have hn := target_rule g i false
      simp only [Bool.false_eq_true,if_false,Nat.add_zero,hr,Option.map_some] at hn
      rw [valAt_tblV_succ hn W hp,valAt_tblV_succ hr W hp]
      exact normal_eval g x _ _ ih (tblV_ok _ _ _ k) (SequentialClock.table_descending g x k) W r.body
        (hg r (ruleAtM_mem hr)) p hp
    · intro i r hr p hp
      have hz := target_rule g i true
      simp only [if_true,hr,Option.map_some] at hz
      rw [valAt_tblV_succ hz [] hp,valAt_tblV_succ hr (List.replicate r.arity []) hp]
      rw [zero_eval g x _ _ ih (tblV_ok _ _ _ k) (SequentialClock.table_descending g x k) [] (emptyBody r)
        (emptyBody_firstOrder r (hg r (ruleAtM_mem hr))) p hp]
      have hs : evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] (emptyBody r) p=
          evV g x .callByValueSeq (tblV g x .callByValueSeq k) (List.replicate r.arity []) r.body p := by
        simpa only [emptyBody,List.map_replicate] using evV_subst
          (g:=g) (x:=x) (s:=.callByValueSeq) (T:=tblV g x .callByValueSeq k) (E:=[])
          (List.replicate r.arity []) r.body (hg r (ruleAtM_mem hr)) p
      rw [hs]

/-- A fixed finite grammar, with two rows per source row, preserves ordinary
evaluation and observes exactly the zero-result successes. No anchor, alphabet,
capture-length, arity, call-graph or termination restriction is imposed. -/
theorem physical (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (k p : Nat) (hp : p≤x.length) :
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) E (normal e) p=
      evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p ∧
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) E (SequentialResultSyntax.zero e) p=
      project p (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p) :=
  ⟨normal_eval g x _ _ (physical_rows g hg x k) (tblV_ok _ _ _ k) (SequentialClock.table_descending g x k) E e he p hp,
    zero_eval g x _ _ (physical_rows g hg x k) (tblV_ok _ _ _ k) (SequentialClock.table_descending g x k) E e he p hp⟩

def positive (e : MExp) : MExp := gate (normal e) (.seq (.notP (SequentialResultSyntax.zero e)) (normal e))
def failure (e : MExp) : MExp := .notP (normal e)
def positiveProject (p : Nat) : Res → Res
  | none => none
  | some none => some none
  | some (some q) => if q=p then some none else some (some q)
def failureProject (p : Nat) : Res → Res
  | none => none
  | some none => some (some p)
  | some (some _) => some none

theorem positive_firstOrder (e : MExp) (he : e.FirstOrder) : (positive e).FirstOrder :=
  ⟨normal_firstOrder e he,zero_firstOrder e he,normal_firstOrder e he⟩

theorem positive_physical (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (k p : Nat) (hp : p≤x.length) :
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) E (positive e) p=
      positiveProject p (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p) := by
  obtain ⟨hn,hz⟩ := physical g hg x E e he k p hp
  unfold positive gate
  cases hv : evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p with
  | none => rw [evV_seq_none (by rw [CallLookahead.evV_peek,hn,hv]; rfl)]; rfl
  | some v => cases v with
    | none => rw [evV_seq_fail (by rw [CallLookahead.evV_peek,hn,hv]; rfl)]; rfl
    | some q =>
      rw [evV_seq_ok (by rw [CallLookahead.evV_peek,hn,hv]; rfl)]
      rw [hv] at hn hz
      by_cases hq : q=p
      · simp only [project,if_pos hq] at hz
        rw [evV_seq_fail (evV_not_ok hz)]
        simp [positiveProject,hq]
      · simp only [project,if_neg hq] at hz
        rw [evV_seq_ok (evV_not_fail hz),hn]
        simp [positiveProject,hq]

theorem failure_physical (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (k p : Nat) (hp : p≤x.length) :
    evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) E (failure e) p=
      failureProject p (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p) := by
  simp only [failure,evV]
  rw [(physical g hg x E e he k p hp).1]
  cases evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p with
  | none => rfl
  | some v => cases v <;> rfl

theorem positive_success_strict (g : MGrammar) (hg : g.FirstOrder) (x : List Char) (E : List (List Char))
    (e : MExp) (he : e.FirstOrder) (k p q : Nat) (hp : p≤x.length)
    (hv : evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) E (positive e) p=some (some q)) :
    q<p := by
  rw [positive_physical g hg x E e he k p hp] at hv
  cases hs : evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p with
  | none => simp [hs,positiveProject] at hv
  | some v => cases v with
    | none => simp [hs,positiveProject] at hv
    | some r =>
      by_cases hr : r=p
      · simp [hs,positiveProject,hr] at hv
      · have heq : r=q := by simpa [hs,positiveProject,hr] using hv
        have hd := SequentialClock.expression_descending (SequentialClock.table_descending g x k) E e p r hs
        omega

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    SObs g .callByValueSeq e x rest ↔ SObs (target g) .callByValueSeq (normal e) x rest := by
  rw [←decideObsV_iff hg (by decide) he,
    ←decideObsV_iff (target_firstOrder g hg) (by decide) (normal_firstOrder e he)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq g (target g) x .callByValueSeq .callByValueSeq e (normal e)
    (fun k => (physical g hg x [] e he k _ (Nat.le_refl _)).1.symm)]

theorem language_translation (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) :
    (fun x => SObs g .callByValueSeq e x (some []))=
      (fun x => SObs (target g) .callByValueSeq (normal e) x (some [])) := by
  funext x; exact propext (observations_iff g hg e he x (some []))

theorem finite_success_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (q : Nat) (hq : q≤x.length) :
    (∃ k, evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] e x.length=some (some q)) ↔
      SObs g .callByValueSeq e x (some (sfx x q)) := by
  constructor
  · intro h
    have hs := (tblV_stable g x .callByValueSeq (Nat.le_refl _)).mp h
    apply (decideObsV_iff hg (by decide) he x _).mp
    simp only [decideObsV,hs]
  · rintro ⟨o,hd,ho⟩
    cases o with
    | fail => simp [MOutcome.restOf] at ho
    | ok tree rest =>
      have hr : rest=sfx x q := by simpa only [MOutcome.restOf,Option.some.injEq] using ho
      subst rest
      obtain ⟨k,hk⟩ := derivesV_ev (x:=x) hg (by decide) hd he ⟨[],rfl⟩
      exact ⟨k,by simpa only [sfx_self,obsR,length_sfx x hq] using hk⟩

def recognizeZero (e : MExp) : MExp := .seq (SequentialResultSyntax.zero e) (.star .any)

/-- The zero-success predicate of any first-order Seq program is itself a
fixed Seq language over exactly the original input strings. Undefinedness is
not changed into failure; this does not yet totalize arbitrary programs. -/
theorem zero_success_language (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) :
    SObs g .callByValueSeq e x (some x) ↔ SObs (target g) .callByValueSeq (recognizeZero e) x (some []) := by
  have hroot : (recognizeZero e).FirstOrder := ⟨zero_firstOrder e he,True.intro⟩
  have hsrc := finite_success_iff g hg e he x x.length (Nat.le_refl _)
  rw [sfx_self] at hsrc
  have hdst := finite_success_iff (target g) (target_firstOrder g hg) (recognizeZero e) hroot x 0 (by omega)
  have h0 : sfx x 0=[] := by simp [sfx]
  rw [h0] at hdst
  rw [←hsrc,←hdst]
  constructor
  · rintro ⟨k,hk⟩
    have hz := (physical g hg x [] e he k x.length (Nat.le_refl _)).2
    rw [hk] at hz
    have hz' : evV (target g) x .callByValueSeq (tblV (target g) x .callByValueSeq k) [] (SequentialResultSyntax.zero e) x.length=some (some x.length) := by simpa only [project,↓reduceIte] using hz
    refine ⟨k,?_⟩
    rw [recognizeZero,evV_seq_ok hz',any_star_eval _ _ _ _ _ _ (Nat.le_refl _)]
  · rintro ⟨k,hk⟩
    have hz := (physical g hg x [] e he k x.length (Nat.le_refl _)).2
    cases hs : evV g x .callByValueSeq (tblV g x .callByValueSeq k) [] e x.length with
    | none => rw [hs] at hz; rw [recognizeZero,evV_seq_none hz] at hk; cases hk
    | some v => cases v with
      | none => rw [hs] at hz; rw [recognizeZero,evV_seq_fail hz] at hk; cases hk
      | some q =>
        by_cases hq : q=x.length
        · exact ⟨k,by simpa only [hq] using hs⟩
        · rw [hs] at hz
          simp only [project,if_neg hq] at hz
          rw [recognizeZero,evV_seq_fail hz] at hk
          cases hk

end Shallot.MacroPeg.CBV.SequentialResultCompiler
