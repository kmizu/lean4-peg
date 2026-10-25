import MacroPeg.CBV.EmptyObservedSyntax

namespace Shallot.MacroPeg.CBV.EmptyObservedDispatch
open EmptyObservedSyntax
abbrev Term := EmptyObservedSyntax.Expr
abbrev Spec := EmptyObservedSyntax.Rule
open ClockFreezing (Table)
open EmptyResultObservation (project)

/-- Normal/zero channels are semantic invariants of the actual current
finite tables, not a termination certificate supplied to the compiler. -/
def ArgRel (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (P : Term → MExp × MExp) (a : Term) (p : Nat) : Prop :=
  evV h x .callByValueSeq U [] (P a).1 p=evV g x .callByValuePar T E (original a) p ∧
  evV h x .callByValueSeq U [] (P a).2 p=project p (evV g x .callByValuePar T E (original a) p)

theorem preflight_eval (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (P : Term → MExp × MExp) (args : List Term) (p : Nat)
    (rel : ∀ a∈args, ArgRel g h x T U E P a p) :
    evV h x .callByValueSeq U [] (preflight (args.map P)) p=
      EmptyCaptureDecision.gateArgs p (evParArgs g x .callByValuePar T E (args.map original) p) := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    have ha := (rel a (by simp)).1
    change (match evV h x .callByValueSeq U [] (.andP (P a).1) p with
      | some (some j) => evV h x .callByValueSeq U [] (preflight (args.map P)) j | other => other)=_
    rw [CallLookahead.evV_peek,ha]
    simp only [List.map_cons,evParArgs]
    cases he : evV g x .callByValuePar T E (original a) p with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some q =>
        simp only [CallLookahead.peek,ih (by intro b hb; exact rel b (by simp [hb]))]
        cases evParArgs g x .callByValuePar T E (args.map original) p with
        | none => rfl
        | some v => cases v <;> rfl

theorem capture_empty (x : List Char) (p q : Nat) (hp : p≤x.length) (hq : q≤p) :
    (pre x p q).isEmpty=true ↔ q=p := by
  have hl : (pre x p q).length=p-q := by simp [pre,List.length_take,length_sfx x hp,Nat.min_eq_left (Nat.sub_le _ _)]
  constructor
  · intro he
    have he := List.isEmpty_iff.mp he
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  · intro he; simp [pre,he]

theorem decision_eval (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (P : Term → MExp × MExp) (args : List Term) (W : List (List Char)) (p : Nat) (hp : p≤x.length)
    (rel : ∀ a∈args, ArgRel g h x T U E P a p)
    (down : ∀ a∈args, ∀ q, evV g x .callByValuePar T E (original a) p=some (some q) → q≤p)
    (hargs : evParArgs g x .callByValuePar T E (args.map original) p=some (some W))
    (f : List Bool → MExp) :
    evV h x .callByValueSeq U [] (decision (args.map P) f) p=
      evV h x .callByValueSeq U [] (f (W.map List.isEmpty)) p := by
  induction args generalizing W f with
  | nil => simp only [List.map_nil,evParArgs,Option.some.injEq] at hargs; subst W; rfl
  | cons a args ih =>
    simp only [List.map_cons] at hargs
    cases ha : evV g x .callByValuePar T E (original a) p with
    | none => simp [evParArgs,ha] at hargs
    | some v => cases v with
      | none => simp [evParArgs,ha] at hargs
      | some q =>
        cases ht : evParArgs g x .callByValuePar T E (args.map original) p with
        | none => simp [evParArgs,ha,ht] at hargs
        | some v => cases v with
          | none => simp [evParArgs,ha,ht] at hargs
          | some words =>
            simp only [evParArgs,ha,ht,Option.some.injEq] at hargs
            subst W
            have hz := (rel a (by simp)).2
            rw [ha] at hz
            have he : evV h x .callByValueSeq U [] (P a).2 p=
                if (pre x p q).isEmpty then some (some p) else some none := by
              rw [hz]
              by_cases hh : q=p
              · simp [project,hh,pre]
              · have hn : (pre x p q).isEmpty=false := Bool.eq_false_iff.mpr (fun hh' => hh ((capture_empty x p q hp (down a (by simp) q ha)).mp hh'))
                simp [project,hh,hn]
            rw [List.map_cons,decision,ScannerFrontier.branch_eval _ _ _ p _ he]
            have ir := ih words (by intro b hb; exact rel b (by simp [hb])) (by intro b hb; exact down b (by simp [hb])) ht
            cases hw : (pre x p q).isEmpty <;> simp only [List.map_cons,hw,if_true,Bool.false_eq_true,if_false]
            · exact ir (fun bits => f (false::bits))
            · exact ir (fun bits => f (true::bits))

theorem dispatch_eval (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char))
    (P : Term → MExp × MExp) (args : List Term) (p : Nat) (hp : p≤x.length)
    (rel : ∀ a∈args, ArgRel g h x T U E P a p)
    (down : ∀ a∈args, ∀ q, evV g x .callByValuePar T E (original a) p=some (some q) → q≤p)
    (f : List Bool → MExp) :
    evV h x .callByValueSeq U [] (dispatch (args.map P) f) p=
      match evParArgs g x .callByValuePar T E (args.map original) p with
      | none => none | some none => some none
      | some (some W) => evV h x .callByValueSeq U [] (f (W.map List.isEmpty)) p := by
  have hh := preflight_eval g h x T U E P args p rel
  cases ha : evParArgs g x .callByValuePar T E (args.map original) p with
  | none => rw [ha] at hh; exact evV_seq_none hh
  | some v => cases v with
    | none => rw [ha] at hh; exact evV_seq_fail hh
    | some W =>
      rw [ha] at hh
      rw [dispatch,evV_seq_ok hh]
      exact decision_eval g h x T U E P args W p hp rel down ha f

end Shallot.MacroPeg.CBV.EmptyObservedDispatch
