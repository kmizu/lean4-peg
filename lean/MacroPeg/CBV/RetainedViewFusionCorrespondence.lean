import MacroPeg.CBV.RetainedViewFusionEvaluation
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.RetainedViewFusionCorrespondence
open RetainedViewFusionSyntax RetainedViewFusionDeclarations RetainedViewFusionDispatch RetainedViewFusionAtoms RetainedViewFusionEvaluation
open RegularCaptureProduct (run filtered)
open ExactWordCaptureMachine (machine)
open FiniteSuffixReplay (views palette)
open SubstringCaptureView (region)
open ClockFreezing (Table)

theorem mode_evaluation (seeds : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table)
    (rows : Rows (region seeds) rs x T U) (ht : OkTV x.length T)
    (hu : SoundTV (intermediate (region seeds) rs) x .callByValuePar U)
    (e : Term) (E : List (List Char)) (p : Nat) (hp : p≤x.length) (m : Mode) (hm : m∈modes (region seeds)) :
    evV (intermediate (region seeds) rs) x .callByValuePar U (payload E) (emit (region seeds) rs (views (region seeds) E) m e) p=
      project m x p (evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) e) p) := by
  have hh := evaluation seeds rs x T U rows ht hu e E p hp
  cases m with
  | none => exact hh.1
  | some v =>
    rcases v with ⟨u,q,r⟩
    obtain ⟨hmem,hq,hr⟩ := (mode_mem (region seeds) u q r).mp hm
    exact hh.2 u hmem q r hq hr

/-- Once the unbounded leading word has been consumed, its exact substring
view advances the observer; the real word remains in the unary payload. -/
theorem prefix_project (seeds : List (List Char)) (rs : List Spec) (x : List Char) (T : Table)
    (ht : SoundTV (source (region seeds) rs) x .callByValuePar T)
    (r : Spec) (E : List (List Char)) (he : E.length=r.arity)
    (p z : Nat) (hp : p≤x.length) (hz : z≤x.length)
    (hh : evV (source (region seeds) rs) x .callByValuePar T E (head r) p=some (some z))
    (m : Mode) (hm : m∈modes (region seeds)) :
    project (advance (views (region seeds) E) m) x z
        (evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) r.body) z)=
      project m x p (evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) r.body) z) := by
  cases m with
  | none => rfl
  | some v =>
    rcases v with ⟨u,q,t⟩
    obtain ⟨hu,hq,hr⟩ := (mode_mem (region seeds) u q t).mp hm
    have hhead : (head r).FirstOrder := by simp only [head]; split <;> trivial
    have hpref := ReplayFusion.success_prefix ht E (head r) hhead p z hp hh
    have hh' := (head_eval (source (region seeds) rs) (source (region seeds) rs) x T T (region seeds) E r he p hp).trans hh
    have hw := WordArguments.value_of_success (source (region seeds) rs) x .callByValuePar T (payload E) (.param 0) True.intro p z hp hh'
    have hword : main E=pre x p z := by simpa [WordArguments.value,payload] using Option.some.inj hw
    change filtered (machine u) x (state u q (views (region seeds) E)) t z _=filtered (machine u) x q t p _
    rw [state_views seeds u hu E q hq,hword]
    cases hv : evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) r.body) z with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some j =>
        have hj := ReplayFusion.success_prefix ht E (original (region seeds) r.body) (render_firstOrder _ _) z j hz hv
        have hc := SequenceArguments.pre_concat hp hj.1 hpref.2 hj.2
        simp only [filtered,hc,RegularCaptureProduct.run_append]

theorem tables_related (seeds : List (List Char)) (rs : List Spec) (x : List Char) (k : Nat) :
    Rows (region seeds) rs x (tblV (source (region seeds) rs) x .callByValuePar k)
      (tblV (intermediate (region seeds) rs) x .callByValuePar k) := by
  induction k with
  | zero => intro i r hr E hE p hp m hm; cases m <;> rfl
  | succ k ih =>
    intro i r hr E hE p hp m hm
    have hs := source_rule (region seeds) rs i r hr
    have hi := intermediate_rule (region seeds) rs i r hr E hE m hm
    rw [valAt_tblV_succ hs E hp,valAt_tblV_succ hi (payload E) hp]
    have hh := head_eval (source (region seeds) rs) (intermediate (region seeds) rs) x
      (tblV (source (region seeds) rs) x .callByValuePar k) (tblV (intermediate (region seeds) rs) x .callByValuePar k)
      (region seeds) E r hE p hp
    cases hhead : evV (source (region seeds) rs) x .callByValuePar (tblV (source (region seeds) rs) x .callByValuePar k) E (head r) p with
    | none =>
      rw [evV_seq_none hhead,evV_seq_none (hh.trans hhead)]
      cases m <;> rfl
    | some v => cases v with
      | none =>
        rw [evV_seq_fail hhead,evV_seq_fail (hh.trans hhead)]
        cases m <;> rfl
      | some z =>
        rw [evV_seq_ok hhead,evV_seq_ok (hh.trans hhead)]
        have hz := evV_ok (tblV_ok _ _ _ k) (head r) p hp z hhead
        rw [mode_evaluation seeds rs x _ _ ih (tblV_ok _ _ _ k) (tblV_sound (intermediate_firstOrder _ _) (by decide) k)
          r.body E z hz (advance (views (region seeds) E) m) (advance_mem seeds E m hm)]
        exact prefix_project seeds rs x _ (tblV_sound (source_firstOrder _ _) (by decide) k) r E hE p z hp hz hhead m hm

def root (seeds : List (List Char)) (rs : List Spec) (e : Term) :=
  MExp.subst [.lit []] (emit (region seeds) rs [] none e)

theorem root_firstOrder (seeds : List (List Char)) (rs : List Spec) (e : Term) : (root seeds rs e).FirstOrder :=
  firstOrder_subst (firstOrderArgs_lits [[]]) _ (emit_firstOrder _ _ _ _ _)

/-- Erase the other captures into metadata, retain the actual first word,
then compose the existing unary leading-replay fusion without input coding. -/
theorem physical (seeds : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) (k : Nat) :
    evV (source (region seeds) rs) x .callByValuePar (tblV (source (region seeds) rs) x .callByValuePar k) [] (original (region seeds) e) x.length=
      evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (root seeds rs e) x.length := by
  have he := (evaluation seeds rs x _ _ (tables_related seeds rs x k) (tblV_ok _ _ _ k)
    (tblV_sound (intermediate_firstOrder _ _) (by decide) k) e [] x.length (Nat.le_refl _)).1.symm
  rw [he]
  simp only [intermediate,views,List.map_nil]
  rw [ReplayFusion.evaluator_eq (tails_firstOrder (region seeds) rs) x k (payload [])
    (emit (region seeds) rs [] none e) (emit_firstOrder (region seeds) rs [] none e) x.length (Nat.le_refl _)]
  exact (evV_subst (g := target (region seeds) rs) (x := x) (s := .callByValueSeq)
    (T := tblV (target (region seeds) rs) x .callByValueSeq k) (E := []) (payload []) _ (emit_firstOrder _ _ _ _ _) x.length).symm

theorem observations_iff (seeds : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) (rest : Option (List Char)) :
    SObs (source (region seeds) rs) .callByValuePar (original (region seeds) e) x rest ↔
      SObs (target (region seeds) rs) .callByValueSeq (root seeds rs e) x rest := by
  rw [←decideObsV_iff (source_firstOrder _ _) (by decide) (render_firstOrder _ _),
    ←decideObsV_iff (target_firstOrder _ _) (by decide) (root_firstOrder _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical seeds rs e x k)]

theorem language_translation (seeds : List (List Char)) (rs : List Spec) (e : Term) :
    (fun x => SObs (source (region seeds) rs) .callByValuePar (original (region seeds) e) x (some []))=
      (fun x => SObs (target (region seeds) rs) .callByValueSeq (root seeds rs e) x (some [])) := by
  funext x
  exact propext (observations_iff seeds rs e x (some []))

theorem defined_iff (seeds : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) (v : Option Nat) :
    (∃ k, evV (source (region seeds) rs) x .callByValuePar (tblV (source (region seeds) rs) x .callByValuePar k) [] (original (region seeds) e) x.length=some v) ↔
      ∃ k, evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (root seeds rs e) x.length=some v := by
  constructor
  · rintro ⟨k,hk⟩; exact ⟨k,(physical seeds rs e x k).symm.trans hk⟩
  · rintro ⟨k,hk⟩; exact ⟨k,(physical seeds rs e x k).trans hk⟩

theorem undefined_iff (seeds : List (List Char)) (rs : List Spec) (e : Term) (x : List Char) :
    (∀ k, evV (source (region seeds) rs) x .callByValuePar (tblV (source (region seeds) rs) x .callByValuePar k) [] (original (region seeds) e) x.length=none) ↔
      ∀ k, evV (target (region seeds) rs) x .callByValueSeq (tblV (target (region seeds) rs) x .callByValueSeq k) [] (root seeds rs e) x.length=none := by
  constructor
  · intro h k; rw [←physical seeds rs e x k]; exact h k
  · intro h k; rw [physical seeds rs e x k]; exact h k

end Shallot.MacroPeg.CBV.RetainedViewFusionCorrespondence
