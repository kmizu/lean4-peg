import MacroPeg.CBV.FiniteSuffixObservedDispatch

namespace Shallot.MacroPeg.CBV.FiniteSuffixObservedEvaluation
open FiniteSuffixObservedSyntax FiniteSuffixObservedDeclarations FiniteSuffixObservedDispatch FiniteSuffixObservedAtoms
open RegularCaptureProduct (filtered)
open ExactWordCaptureMachine (machine)
open FiniteSuffixReplay (palette views)
open ClockFreezing (Table)

def Rows (R : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ E, E.length=r.arity → ∀ p, p≤x.length → ∀ m, m∈modes R →
    valAt (U (address R rs i (views R E) m) []) p=project m x p (valAt (T i E) p)

theorem call_eval (R : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table)
    (rows : Rows R rs x T U) (E : List (List Char)) (i : Nat) (args : List Term) (m : Mode) (hm : m∈modes R)
    (p : Nat) (hp : p≤x.length) (rel : ∀ a∈args, ArgRel (source R rs) (target R rs) x T U E R rs a p) :
    evV (target R rs) x .callByValueSeq U [] (emit R rs (views R E) m (.call i args)) p=
      project m x p (evV (source R rs) x .callByValuePar T E (original R (.call i args)) p) := by
  cases hr : rs[i]? with
  | none =>
    have hs : ruleAtM (source R rs).rules i=none := by simp [source,FiniteSuffixDependentView.source,ruleAtM_eq_getElem?,List.getElem?_map,hr]
    cases m <;> simp [emit,hr,original,FiniteSuffixDependentView.render,evV,hs,project,filtered,MExp.failAlways]
  | some r =>
    have hs := FiniteSuffixDependentView.source_rule R rs i r hr
    by_cases ha : r.arity=args.length
    · simp only [emit,hr,if_pos ha]
      rw [gather_eval (source R rs) (target R rs) x T U E R rs args p rel]
      rw [show original R (.call i args)=.call i (FiniteSuffixDependentView.renderArgs R none args) from rfl,
        evV_call_par hs (by simpa only [FiniteSuffixDependentView.renderArgs_length] using ha) (by decide)]
      cases hw : evParArgs (source R rs) x .callByValuePar T E (FiniteSuffixDependentView.renderArgs R none args) p with
      | none => cases m <;> rfl
      | some v => cases v with
        | none => cases m <;> rfl
        | some W =>
          have hl : W.length=r.arity := by simpa only [FiniteSuffixDependentView.renderArgs_length,ha] using evPar_length _ W hw
          dsimp only []
          rw [evV_call_seq (target_rule R rs i r hr W hl m hm) (args := []) rfl]
          exact rows i r hr W hl p hp m hm
    · have hn : r.arity≠(FiniteSuffixDependentView.renderArgs R none args).length := by simpa [FiniteSuffixDependentView.renderArgs_length] using ha
      cases m <;> simp [emit,hr,ha,original,FiniteSuffixDependentView.render,evV,hs,hn,project,filtered,MExp.failAlways]

/-- Ordinary and output-filtered expressions close together. The target
soundness premise is discharged by its actual physical table in Correspondence. -/
theorem evaluation (R : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table)
    (rows : Rows R rs x T U) (ht : OkTV x.length T)
    (hu : SoundTV (target R rs) x .callByValueSeq U) : ∀ (e : Term) E p, p≤x.length →
    ArgRel (source R rs) (target R rs) x T U E R rs e p
  | .call i args,E,p,hp => by
    refine ⟨call_eval R rs x T U rows E i args none (by simp [modes]) p hp ?_,?_⟩
    · intro a ha; exact evaluation R rs x T U rows ht hu a E p hp
    · intro u hmem q r hq hr
      exact call_eval R rs x T U rows E i args (some (u,q,r)) ((mode_mem R u q r).mpr ⟨hmem,hq,hr⟩) p hp
        (by intro a ha; exact evaluation R rs x T U rows ht hu a E p hp)
  | .eps,E,p,hp => by
    refine ⟨rfl,?_⟩
    intro u hm q r hq hr
    exact atom_correct _ x _ U [] _ .eps [] p (by
      intro j hj
      have he : p=j := by simpa [evV] using hj
      simp [pre,he])
  | .lit w,E,p,hp => by
    refine ⟨rfl,?_⟩
    intro u hm q r hq hr
    exact atom_correct _ x _ U [] _ (.lit w) w p (by
      intro j hj
      exact (Option.some.inj (WordArguments.value_of_success _ x _ U [] (.lit w) True.intro p j hp hj)).symm)
  | .any,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => character_correct _ x _ U [] _ .any p hp (Or.inl rfl)⟩
  | .chr c,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => character_correct _ x _ U [] _ (.chr c) p hp (Or.inr (Or.inl ⟨c,rfl⟩))⟩
  | .range a b,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => character_correct _ x _ U [] _ (.range a b) p hp (Or.inr (Or.inr ⟨a,b,rfl⟩))⟩
  | .replay i,E,p,hp => by
    have hn := (FiniteSuffixReplay.replay_eval (source R rs) (target R rs) x .callByValuePar .callByValueSeq T U E R i p hp).symm
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    exact (atom_correct _ x _ U [] _ _ _ p (replay_word _ x _ U R (views R E) i p hp)).trans (congrArg (filtered (machine u) x q r p) hn)
  | .seq a b,E,p,hp => by
    have ha := (evaluation R rs x T U rows ht hu a E p hp).1
    have hn : evV (target R rs) x .callByValueSeq U [] (emit R rs (views R E) none (.seq a b)) p=
        evV (source R rs) x .callByValuePar T E (original R (.seq a b)) p := by
      cases he : evV (source R rs) x .callByValuePar T E (original R a) p with
      | none => simp only [emit,original,FiniteSuffixDependentView.render,evV_seq_none he,evV_seq_none (ha.trans he)]
      | some v => cases v with
        | none => simp only [emit,original,FiniteSuffixDependentView.render,evV_seq_fail he,evV_seq_fail (ha.trans he)]
        | some j =>
          simp only [emit,original,FiniteSuffixDependentView.render,evV_seq_ok he,evV_seq_ok (ha.trans he)]
          exact (evaluation R rs x T U rows ht hu b E j (evV_ok ht _ p hp j he)).1
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    have hf := ControlFilter.seq_correct (machine u) (ExactWordCaptureMachine.valid u) (target R rs) x .callByValueSeq (by decide) U hu []
      (emit R rs (views R E) none a) (emit R rs (views R E) none b)
      (emit_firstOrder _ _ _ _ _) (emit_firstOrder _ _ _ _ _)
      (fun q r => emit R rs (views R E) (some (u,q,r)) a) (fun q r => emit R rs (views R E) (some (u,q,r)) b) p hp
      (by intro q r hq hr; rw [(evaluation R rs x T U rows ht hu a E p hp).1]; exact (evaluation R rs x T U rows ht hu a E p hp).2 u hm q r hq hr)
      (by intro z hz q r hq hr; rw [(evaluation R rs x T U rows ht hu b E z hz).1]; exact (evaluation R rs x T U rows ht hu b E z hz).2 u hm q r hq hr) q r hq hr
    exact hf.trans (congrArg (filtered (machine u) x q r p) hn)
  | .alt a b,E,p,hp => by
    have ha := (evaluation R rs x T U rows ht hu a E p hp).1
    have hb := (evaluation R rs x T U rows ht hu b E p hp).1
    have hn : evV (target R rs) x .callByValueSeq U [] (emit R rs (views R E) none (.alt a b)) p=
        evV (source R rs) x .callByValuePar T E (original R (.alt a b)) p := by
      change (match evV _ _ _ _ [] (emit R rs (views R E) none a) p with
        | some none => evV _ _ _ _ [] (emit R rs (views R E) none b) p | other => other)=_
      rw [ha,hb]; rfl
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    rw [emit,ChoiceArguments.branch_eval,ha]
    cases hv : evV (source R rs) x .callByValuePar T E (original R a) p with
    | none => rw [show original R (.alt a b)=.alt (original R a) (original R b) from rfl,evV_alt_none hv]; rfl
    | some v => cases v with
      | none =>
        rw [show original R (.alt a b)=.alt (original R a) (original R b) from rfl,evV_alt_fail hv]
        exact (evaluation R rs x T U rows ht hu b E p hp).2 u hm q r hq hr
      | some j =>
        rw [show original R (.alt a b)=.alt (original R a) (original R b) from rfl,evV_alt_ok hv]
        exact ((evaluation R rs x T U rows ht hu a E p hp).2 u hm q r hq hr).trans (by rw [hv])
  | .notP a,E,p,hp => by
    have hn : evV (target R rs) x .callByValueSeq U [] (emit R rs (views R E) none (.notP a)) p=
        evV (source R rs) x .callByValuePar T E (original R (.notP a)) p := by
      simp only [emit,atom,original,FiniteSuffixDependentView.render,evV,(evaluation R rs x T U rows ht hu a E p hp).1]
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    exact (atom_correct _ x _ U [] _ _ [] p (not_word _ x _ U _ p)).trans (congrArg (filtered (machine u) x q r p) hn)
  | .star a,E,p,hp => by
    have hn : evV (target R rs) x .callByValueSeq U [] (emit R rs (views R E) none (.star a)) p=
        evV (source R rs) x .callByValuePar T E (original R (.star a)) p := by
      simp only [emit,original,FiniteSuffixDependentView.render,evV_star]
      exact evStar_congr p (fun z hz => (evaluation R rs x T U rows ht hu a E z (by omega)).1)
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    have hf := GeneralStarFilter.correct (machine u) (ExactWordCaptureMachine.valid u) (target R rs) x .callByValueSeq (by decide) U hu []
      (emit R rs (views R E) none a) (emit_firstOrder _ _ _ _ _) (fun q r => emit R rs (views R E) (some (u,q,r)) a)
      (by intro q r z hq hr hz; rw [(evaluation R rs x T U rows ht hu a E z hz).1]; exact (evaluation R rs x T U rows ht hu a E z hz).2 u hm q r hq hr)
      q r p hq hp
    exact hf.trans (congrArg (filtered (machine u) x q r p) hn)
termination_by e E p hp => sizeOf e

end Shallot.MacroPeg.CBV.FiniteSuffixObservedEvaluation
