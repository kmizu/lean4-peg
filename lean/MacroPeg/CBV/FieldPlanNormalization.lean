import MacroPeg.CBV.FieldPlanSyntax

namespace Shallot.MacroPeg.CBV.FieldPlanNormalization
open FieldPlanSyntax
open ReplayControlFusion (Plan)
open ClockFreezing (Table)
open DelimitedPatternEvaluation (preflight gate)

theorem preflight_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (args : List MExp) (p : Nat) :
    evV g x s T E (preflight args) p=gate p (evParArgs g x s T E args p) := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    change (match evV g x s T E (.andP a) p with
      | some (some q) => evV g x s T E (preflight args) q | other => other)=_
    rw [CallLookahead.evV_peek]
    cases ha : evV g x s T E a p with
    | none => simp [CallLookahead.peek,gate,evParArgs,ha]
    | some v => cases v with
      | none => simp [CallLookahead.peek,gate,evParArgs,ha]
      | some q =>
        simp only [CallLookahead.peek,ih,evParArgs,ha]
        cases ht : evParArgs g x s T E args p with
        | none => rfl
        | some v => cases v <;> rfl

def EarlierBodies (parts : List TypedFieldSyntax.Header) (specs : List Spec) (x : List Char) (k : Nat) : Prop :=
  ∀ m, m<k → ∀ r∈parts, ∀ W p, p≤x.length →
    evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar m) W r.body p=
      evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar m) W
        (render parts specs r.body) p

theorem leaf_of_bodies (parts : List TypedFieldSyntax.Header) (specs : List Spec) (x : List Char) (k : Nat)
    (hb : EarlierBodies parts specs x k) (m : Nat) (hm : m<k)
    (r : TypedFieldSyntax.Header) (hr : r∈parts) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar m) W
      (TupleFieldTransfer.sourceBody r.delimiter r.pattern r.body) p=
    evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar m) W
      (TupleFieldTransfer.sourceBody r.delimiter r.pattern (render parts specs r.body)) p := by
  have hc : evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar m) W
      (DelimiterTemplate.compile r.delimiter (DelimitedWordPattern.sourceParts r.delimiter r.pattern)) p=
    evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar m) W
      (DelimiterTemplate.compile r.delimiter (DelimitedWordPattern.sourceParts r.delimiter r.pattern)) p := by
    rw [DelimiterTemplate.compile_eval _ _ _ _ _ _ _ _ hp,DelimiterTemplate.compile_eval _ _ _ _ _ _ _ _ hp]
  unfold TupleFieldTransfer.sourceBody
  cases he : evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar m) W
      (DelimiterTemplate.compile r.delimiter (DelimitedWordPattern.sourceParts r.delimiter r.pattern)) p with
  | none => rw [evV_seq_none he,evV_seq_none (hc.symm.trans he)]
  | some v => cases v with
    | none => rw [evV_seq_fail he,evV_seq_fail (hc.symm.trans he)]
    | some q =>
      rw [evV_seq_ok he,evV_seq_ok (hc.symm.trans he)]
      exact hb m hm r hr W q (evV_ok (tblV_ok _ _ _ m) _ p hp q he)

theorem dispatch (parts : List TypedFieldSyntax.Header) (specs : List Spec) (x : List Char) (k : Nat)
    (s : Spec) (hplan : ValidPlan parts s) (args : List MExp) (hlen : s.arity=args.length)
    (E W : List (List Char)) (p : Nat)
    (ha : evParArgs (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k)
      E args p=some (some W)) :
    evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k) E
      (s.plan.exp (fun j => .call j args)) p=
      s.plan.eval (fun j => valAt (tblV (expanded parts specs) x .callByValuePar k j W) p) p := by
  rw [Plan.exp_eval]
  apply Plan.eval_congr
  apply Plan.all_imp _ s.plan hplan
  intro j hj
  obtain ⟨r,hr,hl⟩ := hj
  rw [evV_call_par (expanded_row parts specs j r hr) (hl.trans hlen) (by decide),ha]

mutual
  theorem expression_of_bodies (parts : List TypedFieldSyntax.Header) (specs : List Spec)
      (hv : Valid parts specs) (x : List Char) (k : Nat) (hb : EarlierBodies parts specs x k) :
      ∀ e, e.FirstOrder → ∀ E p, p≤x.length →
      evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E e p=
        evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k) E (render parts specs e) p
    | .eps,_,_,_,_ | .any,_,_,_,_ | .chr _,_,_,_,_ | .range _ _,_,_,_,_
    | .lit _,_,_,_,_ | .param _,_,_,_,_ => rfl
    | .call i args,he,E,p,hp => by
      cases hs : specs[i]? with
      | none => simp [evV,source,ruleAtM_eq_getElem?,List.getElem?_map,hs,render,MExp.failAlways]
      | some s =>
        by_cases hn : s.arity=args.length
        · have ha := arguments_of_bodies parts specs hv x k hb args he E p hp
          rw [evV_call_par (source_row parts specs i s hs) hn (by decide)]
          simp only [render,hs,if_pos hn]
          change _=(match evV (expanded parts specs) x .callByValuePar _ E (preflight (renderArgs parts specs args)) p with
            | some (some q) => evV (expanded parts specs) x .callByValuePar _ E
                (s.plan.exp (fun j => .call j (renderArgs parts specs args))) q | other => other)
          rw [preflight_eval,←ha]
          cases hargs : evParArgs (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E args p with
          | none => rfl
          | some v => cases v with
            | none => rfl
            | some W =>
              change valAt (tblV (source parts specs) x .callByValuePar k i W) p=
                evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k) E
                  (s.plan.exp (fun j => .call j (renderArgs parts specs args))) p
              rw [dispatch parts specs x k s (hv.specs s (List.mem_of_getElem? hs)) _
                (by rw [renderArgs_length]; exact hn) E W p (ha.symm.trans hargs)]
              cases k with
              | zero =>
                exact (Plan.eval_none s.plan (Plan.all_of_forall (fun _ => rfl) s.plan)).symm
              | succ k =>
                rw [valAt_tblV_succ (source_row parts specs i s hs) W hp,Plan.exp_eval]
                apply Plan.eval_congr
                apply Plan.all_imp _ s.plan (hv.specs s (List.mem_of_getElem? hs))
                intro j hj
                obtain ⟨r,hr,hl⟩ := hj
                rw [valAt_tblV_succ (expanded_row parts specs j r hr) W hp]
                change evV (source parts specs) x .callByValuePar _ W (sourceLeaf parts j) p=_
                simp only [sourceLeaf,hr]
                exact leaf_of_bodies parts specs x (k+1) hb k (by omega) r (List.mem_of_getElem? hr) W p hp
        · have hr := source_row parts specs i s hs
          simp only [render,hs,if_neg hn,evV,hr,MExp.failAlways]
    | .seq a b,he,E,p,hp => by
      have ha := expression_of_bodies parts specs hv x k hb a he.1 E p hp
      simp only [render]
      cases h : evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E a p with
      | none => rw [evV_seq_none h,evV_seq_none (ha.symm.trans h)]
      | some v => cases v with
        | none => rw [evV_seq_fail h,evV_seq_fail (ha.symm.trans h)]
        | some q =>
          rw [evV_seq_ok h,evV_seq_ok (ha.symm.trans h)]
          exact expression_of_bodies parts specs hv x k hb b he.2 E q (evV_ok (tblV_ok _ _ _ k) _ p hp q h)
    | .alt a b,he,E,p,hp => by
      have ha := expression_of_bodies parts specs hv x k hb a he.1 E p hp
      simp only [render]
      cases h : evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E a p with
      | none => rw [evV_alt_none h,evV_alt_none (ha.symm.trans h)]
      | some v => cases v with
        | none =>
          rw [evV_alt_fail h,evV_alt_fail (ha.symm.trans h)]
          exact expression_of_bodies parts specs hv x k hb b he.2 E p hp
        | some q => rw [evV_alt_ok h,evV_alt_ok (ha.symm.trans h)]
    | .notP a,he,E,p,hp => by
      simp only [render,evV,expression_of_bodies parts specs hv x k hb a he E p hp]
    | .star a,he,E,p,hp => by
      rw [render,evV_star,evV_star]
      exact evStar_congr p (fun q hq => expression_of_bodies parts specs hv x k hb a he E q (by omega))
    | .dbg _,he,_,_,_ | .lam _ _,he,_,_,_ | .callParam _ _,he,_,_,_ | .invoke _ _ _,he,_,_,_ => by cases he

  theorem arguments_of_bodies (parts : List TypedFieldSyntax.Header) (specs : List Spec)
      (hv : Valid parts specs) (x : List Char) (k : Nat) (hb : EarlierBodies parts specs x k) :
      ∀ args, MExp.FirstOrderArgs args → ∀ E p, p≤x.length →
      evParArgs (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E args p=
        evParArgs (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k) E
          (renderArgs parts specs args) p
    | [],_,_,_,_ => rfl
    | a::args,he,E,p,hp => by
      simp only [renderArgs,evParArgs,expression_of_bodies parts specs hv x k hb a he.1 E p hp,
        arguments_of_bodies parts specs hv x k hb args he.2 E p hp]
end

theorem physical (parts : List TypedFieldSyntax.Header) (specs : List Spec) (hv : Valid parts specs)
    (x : List Char) (k : Nat) : ∀ e, e.FirstOrder → ∀ E p, p≤x.length →
    evV (source parts specs) x .callByValuePar (tblV (source parts specs) x .callByValuePar k) E e p=
      evV (expanded parts specs) x .callByValuePar (tblV (expanded parts specs) x .callByValuePar k) E (render parts specs e) p := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    apply expression_of_bodies parts specs hv x k
    intro m hm r hr W p hp
    exact ih m hm r.body (hv.parts r hr) W p hp

end Shallot.MacroPeg.CBV.FieldPlanNormalization
