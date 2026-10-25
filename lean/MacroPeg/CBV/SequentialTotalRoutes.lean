import MacroPeg.CBV.SequentialTotalArguments

/-! The finite family of first-positive-argument routes has exactly the
source consuming captures. It is safe under any callee continuation,
including one which fails or is undefined: rejected routes never invent
an alternative tuple. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalRoutes
open SequentialTotalSyntax SequentialTotalControl SequentialTotalArguments

def feed (r : ArgResult) (C : List (List Char) → Nat → Res) : Res :=
  match r with
  | none => none | some none => some none | some (some (W,q)) => C W q
def positiveFeed (p : Nat) (r : ArgResult) (C : List (List Char) → Nat → Res) : Res :=
  match r with
  | some (some (W,q)) => if q=p then some none else C W q
  | _ => some none

def run (g : MGrammar) (x : List Char) (T : SequentialClock.Table) (E : List (List Char))
    (p : Nat) (C : List (List Char) → Nat → Res) : List (List MExp) → Res
  | [] => some none
  | as::rest => altResult (feed (evSeqArgs g x .callByValueSeq T E as p) C) (run g x T E p C rest)

theorem alt_right_failure (r : Res) : altResult r (some none)=r := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

theorem feed_prefix (w : List Char) (r : ArgResult) (C : List (List Char) → Nat → Res) :
    feed (match r with
      | some (some (W,q)) => some (some (w::W,q)) | other => other) C=
      feed r (fun W q => C (w::W) q) := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

variable {g h : MGrammar} {x : List Char} {T U : SequentialClock.Table}
  {E : List (List Char)}

theorem prefix_failure (a : MExp) (routes : List (List MExp)) (p : Nat)
    (C : List (List Char) → Nat → Res)
    (ha : evV h x .callByValueSeq U E a p=some none) :
    run h x U E p C (routes.map (fun bs => a::bs))=some none := by
  induction routes with
  | nil => rfl
  | cons bs routes ih => simp only [List.map_cons,run,evSeq_cons_fail ha,feed,altResult,ih]

theorem prefix_success (a : MExp) (routes : List (List MExp)) (p q : Nat)
    (C : List (List Char) → Nat → Res)
    (ha : evV h x .callByValueSeq U E a p=some (some q)) :
    run h x U E p C (routes.map (fun bs => a::bs))=
      run h x U E q (fun W j => C (pre x p q::W) j) routes := by
  induction routes with
  | nil => rfl
  | cons bs routes ih =>
    simp only [List.map_cons,run,evSeq_cons_ok ha,ih]
    cases evSeqArgs h x .callByValueSeq U E bs q with
    | none => rfl
    | some v => cases v <;> rfl

/-- Route selection preserves the ordered words and remaining position for
all source actual lists and every callee continuation. Unknown source
argument evaluation finitely rejects all routes. -/
theorem routes_correct (hd : SequentialClock.Descending T) :
    ∀ {args : List MExp} {as : List (Forms × Forms)} {p : Nat},
    Entries g h x T U E p args as → ∀ C,
    run h x U E p C (positiveRoutes as)=
      positiveFeed p (evSeqArgs g x .callByValueSeq T E args p) C := by
  intro args
  induction args with
  | nil => intro as p hs C; cases hs; simp [positiveRoutes,run,positiveFeed,evSeqArgs]
  | cons a args ih =>
    intro as p hs C
    cases hs with
    | @cons _ f _ as he hs =>
      obtain ⟨az,ap,af⟩ := he.1
      simp only [positiveRoutes,run]
      cases hv : evV g x .callByValueSeq T E a p with
      | none =>
        have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by rw [az,hv]; rfl
        have hp : evV h x .callByValueSeq U E f.1.positive p=some none := by rw [ap,hv]; rfl
        rw [evSeq_cons_fail hp,prefix_failure _ _ _ _ hz,evSeq_cons_none hv]; rfl
      | some v => cases v with
        | none =>
          have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by rw [az,hv]; rfl
          have hp : evV h x .callByValueSeq U E f.1.positive p=some none := by rw [ap,hv]; rfl
          rw [evSeq_cons_fail hp,prefix_failure _ _ _ _ hz,evSeq_cons_fail hv]; rfl
        | some q =>
          have hq := SequentialClock.expression_descending hd E a p q hv
          by_cases hqp : q=p
          · subst q
            have hz : evV h x .callByValueSeq U E f.1.zero p=some (some p) := by simp [az,hv,zeroResult]
            have hp : evV h x .callByValueSeq U E f.1.positive p=some none := by simp [ap,hv,positiveResult]
            rw [evSeq_cons_fail hp,prefix_success _ _ _ _ _ hz,ih hs,evSeq_cons_ok hv]
            cases evSeqArgs g x .callByValueSeq T E args p with
            | none => rfl
            | some v => cases v <;> rfl
          · have hqp' : q<p := by omega
            have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by simp [az,hv,zeroResult,hqp]
            have hp : evV h x .callByValueSeq U E f.1.positive p=some (some q) := by simp [ap,hv,positiveResult,hqp]
            rw [evSeq_cons_ok hp,prefix_failure _ _ _ _ hz,alt_right_failure,
              full_success hd (entries_lower hs) q hqp',evSeq_cons_ok hv]
            cases ht : evSeqArgs g x .callByValueSeq T E args q with
            | none => rfl
            | some v => cases v with
              | none => rfl
              | some pair =>
                obtain ⟨W,j⟩ := pair
                have hj := (SequentialClock.arguments_metadata hd E args q W j ht).1
                simp [totalArgs,feed,positiveFeed,show j≠p by omega]

theorem choices_eval (as : List MExp) (p : Nat) :
    evV h x .callByValueSeq U E (choices as) p=
      as.foldr (fun a rest => altResult (evV h x .callByValueSeq U E a p) rest) (some none) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [choices,evV,List.foldr_cons,ih]; rfl

theorem calls_eval (routes : List (List MExp)) (p i : Nat) (r : MRule)
    (hr : ruleAtM h.rules i=some r) (ha : ∀ bs∈routes, r.arity=bs.length) :
    evV h x .callByValueSeq U E (choices (routes.map (MExp.call i))) p=
      run h x U E p (fun W q => valAt (U i W) q) routes := by
  induction routes with
  | nil => rfl
  | cons bs routes ih =>
    simp only [List.map_cons,choices,run]
    rw [show evV h x .callByValueSeq U E (.alt (.call i bs) (choices (routes.map (MExp.call i)))) p=
      altResult (feed (evSeqArgs h x .callByValueSeq U E bs p) (fun W q => valAt (U i W) q))
        (evV h x .callByValueSeq U E (choices (routes.map (MExp.call i))) p) by
      simp only [evV,hr,if_pos (ha bs (by simp)),feed,altResult]
      cases evSeqArgs h x .callByValueSeq U E bs p with
      | none => rfl
      | some v => cases v <;> rfl]
    rw [ih (by intro cs hcs; exact ha cs (by simp [hcs]))]

theorem peek_feed (p : Nat) (r : ArgResult) (C : List (List Char) → Nat → Res) :
    CallLookahead.peek p (feed r C)=feed r (fun W q => CallLookahead.peek p (C W q)) := by
  cases r with
  | none => rfl
  | some v => cases v <;> rfl

theorem lookahead_calls_eval (routes : List (List MExp)) (p i : Nat) (r : MRule)
    (hr : ruleAtM h.rules i=some r) (ha : ∀ bs∈routes, r.arity=bs.length) :
    evV h x .callByValueSeq U E (choices (routes.map (fun bs => .andP (.call i bs)))) p=
      run h x U E p (fun W q => CallLookahead.peek p (valAt (U i W) q)) routes := by
  induction routes with
  | nil => rfl
  | cons bs routes ih =>
    have hc : evV h x .callByValueSeq U E (.call i bs) p=
        feed (evSeqArgs h x .callByValueSeq U E bs p) (fun W q => valAt (U i W) q) := by
      rw [evV_call_seq hr (ha bs (by simp))]
      cases evSeqArgs h x .callByValueSeq U E bs p with
      | none => rfl
      | some v => cases v <;> rfl
    change altResult (evV h x .callByValueSeq U E (.andP (.call i bs)) p)
      (evV h x .callByValueSeq U E (choices (routes.map (fun cs => .andP (.call i cs)))) p)=_
    rw [CallLookahead.evV_peek,hc,peek_feed,ih (by intro cs hcs; exact ha cs (by simp [hcs]))]
    rfl

end Shallot.MacroPeg.CBV.SequentialTotalRoutes
