import MacroPeg.CBV.RetainedViewFusionDispatch

namespace Shallot.MacroPeg.CBV.RetainedViewFusionEvaluation
open RetainedViewFusionSyntax RetainedViewFusionDeclarations RetainedViewFusionDispatch RetainedViewFusionAtoms
open RegularCaptureProduct (filtered)
open ExactWordCaptureMachine (machine)
open FiniteSuffixReplay (palette views)
open ClockFreezing (Table)
open SubstringCaptureView (region)

def Rows (R : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ E, E.length=r.arity → ∀ p, p≤x.length → ∀ m, m∈modes R →
    valAt (U (address R rs i (views R E) m) (payload E)) p=project m x p (valAt (T i E) p)

theorem first_capture (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (R : List (List Char)) (rs : List Spec) (args : List Term) (p : Nat) (W : List (List Char))
    (hw : evParArgs g x .callByValuePar T E (originalArgs R args) p=some (some W))
    (rel : ∀ a∈args, ArgRel g h x T U E R rs a p) :
    ∃ q, evV h x .callByValuePar U (payload E) (first R rs (views R E) args) p=some (some q) ∧ payload W=[pre x p q] := by
  cases args with
  | nil =>
    have he : W=[] := by simpa only [originalArgs,evPar_nil,Option.some.injEq] using hw.symm
    subst W
    exact ⟨p,rfl,by simp [payload,main,pre]⟩
  | cons a args =>
    cases hv : evV g x .callByValuePar T E (original R a) p with
    | none => simp [originalArgs,evParArgs,hv] at hw
    | some v => cases v with
      | none => simp [originalArgs,evParArgs,hv] at hw
      | some q =>
        cases ht : evParArgs g x .callByValuePar T E (originalArgs R args) p with
        | none => simp [originalArgs,evParArgs,hv,ht] at hw
        | some v => cases v with
          | none => simp [originalArgs,evParArgs,hv,ht] at hw
          | some words =>
            have he : W=pre x p q::words := by simpa only [originalArgs,evParArgs,hv,ht,Option.some.injEq] using hw.symm
            subst W
            exact ⟨q,(rel a (by simp)).1.trans hv,rfl⟩

theorem call_eval (R : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table)
    (rows : Rows R rs x T U) (E : List (List Char)) (i : Nat) (args : List Term) (m : Mode) (hm : m∈modes R)
    (p : Nat) (hp : p≤x.length) (rel : ∀ a∈args, ArgRel (source R rs) (intermediate R rs) x T U E R rs a p) :
    evV (intermediate R rs) x .callByValuePar U (payload E) (emit R rs (views R E) m (.call i args)) p=
      project m x p (evV (source R rs) x .callByValuePar T E (original R (.call i args)) p) := by
  cases hr : rs[i]? with
  | none =>
    have hs : ruleAtM (source R rs).rules i=none := by simp [source,ruleAtM_eq_getElem?,List.getElem?_map,hr]
    cases m <;> simp [emit,hr,original,evV,hs,project,FiniteSuffixObservedAtoms.project,filtered,MExp.failAlways]
  | some r =>
    have hs := source_rule R rs i r hr
    by_cases ha : r.arity=args.length
    · simp only [emit,hr,if_pos ha]
      rw [gather_eval (source R rs) (intermediate R rs) x T U E R rs args p rel]
      rw [show original R (.call i args)=.call i (originalArgs R args) from rfl,
        evV_call_par hs (by simpa only [originalArgs_length] using ha) (by decide)]
      cases hw : evParArgs (source R rs) x .callByValuePar T E (originalArgs R args) p with
      | none => cases m <;> rfl
      | some v => cases v with
        | none => cases m <;> rfl
        | some W =>
          have hl : W.length=r.arity := by simpa only [originalArgs_length,ha] using evPar_length _ W hw
          obtain ⟨q,hq,hW⟩ := first_capture (source R rs) (intermediate R rs) x T U E R rs args p W hw rel
          dsimp only []
          rw [evV_call_par (intermediate_rule R rs i r hr W hl m hm) (args := [first R rs (views R E) args]) rfl (by decide),evPar_cons_ok hq,evPar_nil]
          dsimp only []
          rw [←hW]
          exact rows i r hr W hl p hp m hm
    · have hn : r.arity≠(originalArgs R args).length := by simpa [originalArgs_length] using ha
      cases m <;> simp [emit,hr,ha,original,evV,hs,hn,project,FiniteSuffixObservedAtoms.project,filtered,MExp.failAlways]

/-- Ordinary and output-filtered expressions close together. The target
soundness premise is discharged by its actual physical table in Correspondence. -/
theorem evaluation (seeds : List (List Char)) (rs : List Spec) (x : List Char) (T U : Table)
    (rows : Rows (region seeds) rs x T U) (ht : OkTV x.length T)
    (hu : SoundTV (intermediate (region seeds) rs) x .callByValuePar U) : ∀ (e : Term) E p, p≤x.length →
    ArgRel (source (region seeds) rs) (intermediate (region seeds) rs) x T U E (region seeds) rs e p
  | .call i args,E,p,hp => by
    refine ⟨call_eval (region seeds) rs x T U rows E i args none (by simp [modes]) p hp ?_,?_⟩
    · intro a ha; exact evaluation seeds rs x T U rows ht hu a E p hp
    · intro u hmem q r hq hr
      exact call_eval (region seeds) rs x T U rows E i args (some (u,q,r)) ((mode_mem (region seeds) u q r).mpr ⟨hmem,hq,hr⟩) p hp
        (by intro a ha; exact evaluation seeds rs x T U rows ht hu a E p hp)
  | .retained,E,p,hp => by
    refine ⟨retained_eval _ _ x T U (region seeds) E p,?_⟩
    intro u hm q r hq hr
    exact retained_correct _ _ x T U seeds E p hp u hm q r hq
  | .eps,E,p,hp => by
    refine ⟨rfl,?_⟩
    intro u hm q r hq hr
    exact FiniteSuffixObservedAtoms.atom_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) .eps [] p (by
      intro j hj
      have he : p=j := by simpa [evV] using hj
      simp [pre,he])
  | .lit w,E,p,hp => by
    refine ⟨rfl,?_⟩
    intro u hm q r hq hr
    exact FiniteSuffixObservedAtoms.atom_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) (.lit w) w p (by
      intro j hj
      exact (Option.some.inj (WordArguments.value_of_success _ x _ U (payload E) (.lit w) True.intro p j hp hj)).symm)
  | .any,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => FiniteSuffixObservedAtoms.character_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) .any p hp (Or.inl rfl)⟩
  | .chr c,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => FiniteSuffixObservedAtoms.character_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) (.chr c) p hp (Or.inr (Or.inl ⟨c,rfl⟩))⟩
  | .range a b,E,p,hp => by
    exact ⟨rfl,fun u hm q r hq hr => FiniteSuffixObservedAtoms.character_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) (.range a b) p hp (Or.inr (Or.inr ⟨a,b,rfl⟩))⟩
  | .replay i,E,p,hp => by
    have hn : evV (intermediate (region seeds) rs) x .callByValuePar U (payload E)
        (.seq (FiniteSuffixReplay.guard (region seeds)) (FiniteSuffixReplay.literal (views (region seeds) E) i)) p=
        evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) (.replay i)) p := by
      rw [retainedReplay_eval _ x U (payload E) (region seeds) (views (region seeds) E) i p hp]
      exact (FiniteSuffixReplay.replay_eval _ _ x .callByValuePar .callByValuePar T U E (region seeds) i p hp).symm
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    exact (FiniteSuffixObservedAtoms.atom_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) _ _ p (replay_word _ x U (payload E) (region seeds) (views (region seeds) E) i p hp)).trans (congrArg (filtered (machine u) x q r p) hn)
  | .seq a b,E,p,hp => by
    have ha := (evaluation seeds rs x T U rows ht hu a E p hp).1
    have hn : evV (intermediate (region seeds) rs) x .callByValuePar U (payload E) (emit (region seeds) rs (views (region seeds) E) none (.seq a b)) p=
        evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) (.seq a b)) p := by
      cases he : evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) a) p with
      | none => simp only [emit,original,original,evV_seq_none he,evV_seq_none (ha.trans he)]
      | some v => cases v with
        | none => simp only [emit,original,original,evV_seq_fail he,evV_seq_fail (ha.trans he)]
        | some j =>
          simp only [emit,original,original,evV_seq_ok he,evV_seq_ok (ha.trans he)]
          exact (evaluation seeds rs x T U rows ht hu b E j (evV_ok ht _ p hp j he)).1
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    have hf := ControlFilter.seq_correct (machine u) (ExactWordCaptureMachine.valid u) (intermediate (region seeds) rs) x .callByValuePar (by decide) U hu (payload E)
      (emit (region seeds) rs (views (region seeds) E) none a) (emit (region seeds) rs (views (region seeds) E) none b)
      (emit_firstOrder _ _ _ _ _) (emit_firstOrder _ _ _ _ _)
      (fun q r => emit (region seeds) rs (views (region seeds) E) (some (u,q,r)) a) (fun q r => emit (region seeds) rs (views (region seeds) E) (some (u,q,r)) b) p hp
      (by intro q r hq hr; rw [(evaluation seeds rs x T U rows ht hu a E p hp).1]; exact (evaluation seeds rs x T U rows ht hu a E p hp).2 u hm q r hq hr)
      (by intro z hz q r hq hr; rw [(evaluation seeds rs x T U rows ht hu b E z hz).1]; exact (evaluation seeds rs x T U rows ht hu b E z hz).2 u hm q r hq hr) q r hq hr
    exact hf.trans (congrArg (filtered (machine u) x q r p) hn)
  | .alt a b,E,p,hp => by
    have ha := (evaluation seeds rs x T U rows ht hu a E p hp).1
    have hb := (evaluation seeds rs x T U rows ht hu b E p hp).1
    have hn : evV (intermediate (region seeds) rs) x .callByValuePar U (payload E) (emit (region seeds) rs (views (region seeds) E) none (.alt a b)) p=
        evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) (.alt a b)) p := by
      change (match evV _ _ _ _ (payload E) (emit (region seeds) rs (views (region seeds) E) none a) p with
        | some none => evV _ _ _ _ (payload E) (emit (region seeds) rs (views (region seeds) E) none b) p | other => other)=_
      rw [ha,hb]; rfl
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    rw [emit,ChoiceArguments.branch_eval,ha]
    cases hv : evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) a) p with
    | none => rw [show original (region seeds) (.alt a b)=.alt (original (region seeds) a) (original (region seeds) b) from rfl,evV_alt_none hv]; rfl
    | some v => cases v with
      | none =>
        rw [show original (region seeds) (.alt a b)=.alt (original (region seeds) a) (original (region seeds) b) from rfl,evV_alt_fail hv]
        exact (evaluation seeds rs x T U rows ht hu b E p hp).2 u hm q r hq hr
      | some j =>
        rw [show original (region seeds) (.alt a b)=.alt (original (region seeds) a) (original (region seeds) b) from rfl,evV_alt_ok hv]
        exact ((evaluation seeds rs x T U rows ht hu a E p hp).2 u hm q r hq hr).trans (by rw [hv])
  | .notP a,E,p,hp => by
    have hn : evV (intermediate (region seeds) rs) x .callByValuePar U (payload E) (emit (region seeds) rs (views (region seeds) E) none (.notP a)) p=
        evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) (.notP a)) p := by
      simp only [emit,atom,FiniteSuffixObservedSyntax.atom,original,evV,(evaluation seeds rs x T U rows ht hu a E p hp).1]
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    exact (FiniteSuffixObservedAtoms.atom_correct (intermediate (region seeds) rs) x .callByValuePar U (payload E) (some (u,q,r)) _ [] p (not_word _ x U (payload E) _ p)).trans (congrArg (filtered (machine u) x q r p) hn)
  | .star a,E,p,hp => by
    have hn : evV (intermediate (region seeds) rs) x .callByValuePar U (payload E) (emit (region seeds) rs (views (region seeds) E) none (.star a)) p=
        evV (source (region seeds) rs) x .callByValuePar T E (original (region seeds) (.star a)) p := by
      simp only [emit,original,original,evV_star]
      exact evStar_congr p (fun z hz => (evaluation seeds rs x T U rows ht hu a E z (by omega)).1)
    refine ⟨hn,?_⟩
    intro u hm q r hq hr
    have hf := GeneralStarFilter.correct (machine u) (ExactWordCaptureMachine.valid u) (intermediate (region seeds) rs) x .callByValuePar (by decide) U hu (payload E)
      (emit (region seeds) rs (views (region seeds) E) none a) (emit_firstOrder _ _ _ _ _) (fun q r => emit (region seeds) rs (views (region seeds) E) (some (u,q,r)) a)
      (by intro q r z hq hr hz; rw [(evaluation seeds rs x T U rows ht hu a E z hz).1]; exact (evaluation seeds rs x T U rows ht hu a E z hz).2 u hm q r hq hr)
      q r p hq hp
    exact hf.trans (congrArg (filtered (machine u) x q r p) hn)
termination_by e E p hp => sizeOf e

end Shallot.MacroPeg.CBV.RetainedViewFusionEvaluation
