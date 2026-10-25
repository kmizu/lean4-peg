import MacroPeg.CBV.EmptyObservedDispatch

namespace Shallot.MacroPeg.CBV.EmptyObservedEvaluation
open EmptyObservedSyntax EmptyObservedDispatch
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule
open EmptyResultObservation (project gate star_empty_test)
open ClockFreezing (Table)

def view (E : List (List Char)) := E.map List.isEmpty

def Rows (rs : List Spec) (x : List Char) (T U : Table) : Prop :=
  ∀ i r, rs[i]?=some r → ∀ E, E.length=r.arity → ∀ p, p≤x.length → ∀ zero,
    valAt (U (address rs i (view E) zero) []) p=
      if zero then project p (valAt (T i E) p) else valAt (T i E) p

def Down (rs : List Spec) (x : List Char) (T : Table) : Prop :=
  ∀ e E p q, p≤x.length → evV (source rs) x .callByValuePar T E (original e) p=some (some q) → q≤p

theorem atEnd_eval (rs : List Spec) (x : List Char) (T U : Table) (E : List (List Char)) (i p : Nat) (hp : p≤x.length) :
    evV (target rs) x .callByValueSeq U [] (emit rs (view E) false (.atEnd i)) p=
      evV (source rs) x .callByValuePar T E (original (.atEnd i)) p ∧
    project p (evV (source rs) x .callByValuePar T E (original (.atEnd i)) p)=
      evV (source rs) x .callByValuePar T E (original (.atEnd i)) p := by
  have hl := length_sfx x hp
  cases hx : sfx x p with
  | nil =>
    rw [hx] at hl
    have hp0 : p=0 := by simpa using hl.symm
    subst p
    cases he : E[i]? with
    | none => simp [emit,view,original,evV,List.getElem?_map,he,hx,sfx,project,MExp.failAlways]
    | some w => cases w <;> simp [emit,view,original,evV,List.getElem?_map,he,hx,sfx,project,MExp.failAlways,Shallot.stripPrefix?]
  | cons c rest =>
    cases he : E[i]? with
    | none => simp [emit,view,original,evV,List.getElem?_map,he,hx,project,MExp.failAlways]
    | some w => cases w <;> simp [emit,view,original,evV,List.getElem?_map,he,hx,project,MExp.failAlways]

theorem gate_project_env (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (a b c : MExp) (p : Nat)
    (hn : evV h x .callByValueSeq U [] b p=evV g x .callByValuePar T E a p)
    (hc : ∀ q, evV g x .callByValuePar T E a p=some (some q) →
      evV h x .callByValueSeq U [] c p=project p (some (some q))) :
    evV h x .callByValueSeq U [] (gate b c) p=project p (evV g x .callByValuePar T E a p) := by
  unfold gate
  change (match evV h x .callByValueSeq U [] (.andP b) p with
    | some (some j) => evV h x .callByValueSeq U [] c j | other => other)=_
  rw [CallLookahead.evV_peek,hn]
  cases ha : evV g x .callByValuePar T E a p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some q => exact hc q ha

/-- An arbitrary-arity call dispatches to a fixed nullary row. Its actuals
may themselves depend on the parent's finite view and invoke user rules. -/
theorem call_eval (rs : List Spec) (x : List Char) (T U : Table) (E : List (List Char))
    (rows : Rows rs x T U) (down : Down rs x T) (i : Nat) (args : List Term)
    (p : Nat) (hp : p≤x.length)
    (rel : ∀ a∈args, ∀ q, q≤x.length → ArgRel (source rs) (target rs) x T U E
      (fun a => (emit rs (view E) false a,emit rs (view E) true a)) a q) (zero : Bool) :
    evV (target rs) x .callByValueSeq U [] (emit rs (view E) zero (.call i args)) p=
      if zero then project p (evV (source rs) x .callByValuePar T E (original (.call i args)) p)
      else evV (source rs) x .callByValuePar T E (original (.call i args)) p := by
  cases hr : rs[i]? with
  | none => simp [emit,original,originalArgs_eq_map,evV,source_rule,hr,MExp.failAlways,project]
  | some r =>
    have hs : ruleAtM (source rs).rules i=some ⟨r.arity,original r.body⟩ := by rw [source_rule,hr]; rfl
    by_cases ha : r.arity=args.length
    · simp only [emit,hr,if_pos ha,original,originalArgs_eq_map,emitArgs_eq_map]
      rw [evV_call_par hs (by simpa using ha) (by decide),
        dispatch_eval (source rs) (target rs) x T U E _ args p hp
          (by intro a hm; exact rel a hm p hp) (by intro a hm q hh; exact down a E p q hp hh)]
      cases hw : evParArgs (source rs) x .callByValuePar T E (args.map original) p with
      | none => cases zero <;> rfl
      | some v => cases v with
        | none => cases zero <;> rfl
        | some W =>
          have hl : W.length=r.arity := by simpa only [List.length_map,ha] using evPar_length (args.map original) W hw
          have ht := target_rule rs i r hr (view W) (by simpa [view] using hl) zero
          simp only [view] at ht
          dsimp only []
          rw [evV_call_seq ht (args := []) rfl]
          exact rows i r hr W hl p hp zero
    · simp [emit,hr,ha,original,originalArgs_eq_map,evV,hs,List.length_map,MExp.failAlways,project]


theorem evaluation (rs : List Spec) (x : List Char) (T U : Table) (rows : Rows rs x T U)
    (ht : OkTV x.length T) (down : Down rs x T) : ∀ (e : Term) E p, p≤x.length →
    evV (target rs) x .callByValueSeq U [] (emit rs (view E) false e) p=
      evV (source rs) x .callByValuePar T E (original e) p ∧
    evV (target rs) x .callByValueSeq U [] (emit rs (view E) true e) p=
      project p (evV (source rs) x .callByValuePar T E (original e) p)
  | .call i args,E,p,hp => by
    have hh (z : Bool) := call_eval rs x T U E rows down i args p hp
      (by intro a hm q hq; exact evaluation rs x T U rows ht down a E q hq) z
    exact ⟨by simpa only [Bool.false_eq_true,if_false] using hh false,by simpa only [if_true] using hh true⟩
  | .atEnd i,E,p,hp => by
    have hh := atEnd_eval rs x T U E i p hp
    refine ⟨hh.1,?_⟩
    simpa only [emit] using hh.1.trans hh.2.symm
  | .seq a b,E,p,hp => by
    have hn : evV (target rs) x .callByValueSeq U [] (emit rs (view E) false (.seq a b)) p=
        evV (source rs) x .callByValuePar T E (original (.seq a b)) p := by
      have ha := (evaluation rs x T U rows ht down a E p hp).1
      cases he : evV (source rs) x .callByValuePar T E (original a) p with
      | none => simp only [emit,original,evV_seq_none he,evV_seq_none (ha.trans he)]
      | some v => cases v with
        | none => simp only [emit,original,evV_seq_fail he,evV_seq_fail (ha.trans he)]
        | some j =>
          simp only [emit,original,evV_seq_ok he,evV_seq_ok (ha.trans he)]
          exact (evaluation rs x T U rows ht down b E j (evV_ok ht _ p hp j he)).1
    refine ⟨hn,?_⟩
    rw [emit]
    apply gate_project_env _ _ x T U E _ _ _ p hn
    intro q hq
    cases ha : evV (source rs) x .callByValuePar T E (original a) p with
    | none => rw [original,evV_seq_none ha] at hq; cases hq
    | some v => cases v with
      | none => rw [original,evV_seq_fail ha] at hq; cases hq
      | some j =>
        rw [original,evV_seq_ok ha] at hq
        have hj := evV_ok ht _ p hp j ha
        have hd := down b E j q hj hq
        have hz := (evaluation rs x T U rows ht down a E p hp).2
        rw [ha] at hz
        by_cases he : j=p
        · subst j
          simp only [project,if_true] at hz
          rw [evV_seq_ok hz,(evaluation rs x T U rows ht down b E p hp).2,hq]
        · simp only [project,if_neg he] at hz
          rw [evV_seq_fail hz]
          simp [project,show q≠p from by have := down a E p j hp ha; omega]
  | .alt a b,E,p,hp => by
    have hn : evV (target rs) x .callByValueSeq U [] (emit rs (view E) false (.alt a b)) p=
        evV (source rs) x .callByValuePar T E (original (.alt a b)) p := by
      have ha := (evaluation rs x T U rows ht down a E p hp).1
      cases he : evV (source rs) x .callByValuePar T E (original a) p with
      | none => simp only [emit,original,evV_alt_none he,evV_alt_none (ha.trans he)]
      | some v => cases v with
        | none =>
          simp only [emit,original,evV_alt_fail he,evV_alt_fail (ha.trans he)]
          exact (evaluation rs x T U rows ht down b E p hp).1
        | some j => simp only [emit,original,evV_alt_ok he,evV_alt_ok (ha.trans he)]
    refine ⟨hn,?_⟩
    rw [emit]
    apply gate_project_env _ _ x T U E _ _ _ p hn
    intro q hq
    have hz := (evaluation rs x T U rows ht down a E p hp).2
    have ha := (evaluation rs x T U rows ht down a E p hp).1
    cases he : evV (source rs) x .callByValuePar T E (original a) p with
    | none => rw [original,evV_alt_none he] at hq; cases hq
    | some v => cases v with
      | none =>
        rw [original,evV_alt_fail he] at hq
        rw [he] at hz ha
        rw [evV_alt_fail hz,evV_seq_ok (evV_not_fail ha),(evaluation rs x T U rows ht down b E p hp).2,hq]
      | some j =>
        rw [original,evV_alt_ok he] at hq
        have hj : j=q := by simpa only [Option.some.injEq] using hq
        subst j
        rw [he] at hz ha
        by_cases hh : q=p
        · simp only [project,if_pos hh] at hz
          rw [evV_alt_ok hz]; simp [project,hh]
        · simp only [project,if_neg hh] at hz
          rw [evV_alt_fail hz,evV_seq_fail (evV_not_ok ha)]; simp [project,hh]
  | .notP a,E,p,hp => by
    have hn : evV (target rs) x .callByValueSeq U [] (emit rs (view E) false (.notP a)) p=
        evV (source rs) x .callByValuePar T E (original (.notP a)) p := by
      simp only [emit,original,evV,(evaluation rs x T U rows ht down a E p hp).1]
    refine ⟨hn,?_⟩
    have ht' : emit rs (view E) true (.notP a)=emit rs (view E) false (.notP a) := by simp only [emit]
    rw [ht',hn]
    cases ha : evV (source rs) x .callByValuePar T E (original a) p with
    | none => simp [original,evV,ha,project]
    | some v => cases v <;> simp [original,evV,ha,project]
  | .star a,E,p,hp => by
    have hn : evV (target rs) x .callByValueSeq U [] (emit rs (view E) false (.star a)) p=
        evV (source rs) x .callByValuePar T E (original (.star a)) p := by
      simp only [emit,original,evV_star]
      exact evStar_congr p (fun q hq => (evaluation rs x T U rows ht down a E q (by omega)).1)
    refine ⟨hn,?_⟩
    rw [emit]
    apply gate_project_env _ _ x T U E _ _ _ p hn
    intro q hq
    rw [original,evV_star] at hq
    simp only [evV,(evaluation rs x T U rows ht down a E p hp).1]
    have hh := star_empty_test _ p q hq
    cases hv : evV (source rs) x .callByValuePar T E (original a) p with
    | none => simpa [hv] using hh
    | some v => cases v <;> simpa [hv] using hh
  | .eps,E,p,hp => by simp [emit,original,evV,project]
  | .any,E,p,hp => by
    constructor
    · simp only [emit,original,evV]
    · have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [emit,original,evV,hx,project,MExp.failAlways]
      | cons c rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        simp [emit,original,evV,hx,project,hn,MExp.failAlways]
  | .chr c,E,p,hp => by
    constructor
    · simp only [emit,original,evV]
    · have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [emit,original,evV,hx,project,MExp.failAlways]
      | cons d rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        cases hc : Shallot.beqChar c d <;> simp [emit,original,evV,hx,hc,project,hn,MExp.failAlways]
  | .range a b,E,p,hp => by
    constructor
    · simp only [emit,original,evV]
    · have hl := length_sfx x hp
      cases hx : sfx x p with
      | nil => simp [emit,original,evV,hx,project,MExp.failAlways]
      | cons d rest =>
        rw [hx] at hl
        have hn : rest.length≠p := by simp only [List.length_cons] at hl; omega
        cases hc : (Shallot.leChar a d && Shallot.leChar d b) <;> simp [emit,original,evV,hx,hc,project,hn,MExp.failAlways]
  | .lit w,E,p,hp => by
    constructor
    · simp only [emit,original,evV]
    · by_cases hw : w=[]
      · subst w; simp [emit,original,evV,Shallot.stripPrefix?,length_sfx x hp,project]
      · simp only [emit,if_neg hw,MExp.failAlways,original,evV]
        cases hh : Shallot.stripPrefix? w (sfx x p) with
        | none => rfl
        | some rest =>
          have hs := (CBVtoCBN.stripPrefix_exact _ _ _).mp hh
          have hl := congrArg List.length hs
          rw [List.length_append,length_sfx x hp] at hl
          simp [project,show rest.length≠p from by have := List.length_pos_iff.mpr hw; omega]
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem hm) (by omega)

end Shallot.MacroPeg.CBV.EmptyObservedEvaluation
