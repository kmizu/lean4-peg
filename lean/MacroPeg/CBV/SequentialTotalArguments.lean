import MacroPeg.CBV.SequentialTotalControl

/-! Mixed-stage Seq actuals. Each current-stage flag is correct at the
entry position, and each full-stage flag is correct strictly below it.
Successful argument evaluation preserves the entire ordered capture tuple. -/
namespace Shallot.MacroPeg.CBV.SequentialTotalArguments
open SequentialTotalSyntax SequentialTotalControl
abbrev ArgResult := Option (Option (List (List Char) × Nat))

inductive Related {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Related R [] []
  | cons {a b as bs} : R a b → Related R as bs → Related R (a::as) (b::bs)

def totalArgs : ArgResult → ArgResult
  | none => some none
  | other => other
def zeroArgsResult (p : Nat) : ArgResult → Res
  | some (some (_,q)) => if q=p then some (some p) else some none
  | _ => some none
def failureArgsResult (p : Nat) : ArgResult → Res
  | some none => some (some p)
  | _ => some none

def Entries (g h : MGrammar) (x : List Char) (T U : SequentialClock.Table)
    (E : List (List Char)) (p : Nat) (args : List MExp) (as : List (Forms × Forms)) : Prop :=
  Related (fun e a =>
    Realizes h x U E a.1 p (evV g x .callByValueSeq T E e p) ∧
    ∀ q, q<p → Realizes h x U E a.2 q (evV g x .callByValueSeq T E e q)) args as

variable {g h : MGrammar} {x : List Char} {T U : SequentialClock.Table}
  {E : List (List Char)}

theorem entries_length {p : Nat} {args : List MExp} {as : List (Forms × Forms)}
    (hs : Entries g h x T U E p args as) : args.length=as.length := by
  induction hs with
  | nil => rfl
  | cons he hs ih => simp only [List.length_cons,ih]

theorem entries_reset {p q : Nat} {args : List MExp} {as : List (Forms × Forms)}
    (hs : Entries g h x T U E p args as) (hq : q<p) :
    Entries g h x T U E q args (as.map (fun a => (a.2,a.2))) := by
  induction hs with
  | nil => exact .nil
  | cons he hs ih => exact .cons ⟨he.2 q hq,by intro j hj; exact he.2 j (by omega)⟩ ih

theorem entries_lower {p : Nat} {args : List MExp} {as : List (Forms × Forms)}
    (hs : Entries g h x T U E p args as) :
    Related (fun e a => ∀ q, q<p →
      Realizes h x U E a.2 q (evV g x .callByValueSeq T E e q)) args as := by
  induction hs with
  | nil => exact .nil
  | cons he hs ih => exact .cons he.2 ih

/-- Once positive progress has occurred, all remaining actuals use their
full-stage success parser. Unknown source arguments finitely reject the
route; successful source arguments keep every capture and final position. -/
theorem full_success {bound : Nat} (hd : SequentialClock.Descending T) :
    ∀ {args : List MExp} {as : List (Forms × Forms)},
    Related (fun e a => ∀ q, q<bound →
      Realizes h x U E a.2 q (evV g x .callByValueSeq T E e q)) args as →
    ∀ p, p<bound →
    evSeqArgs h x .callByValueSeq U E (as.map (fun a => a.2.success)) p=
      totalArgs (evSeqArgs g x .callByValueSeq T E args p) := by
  intro args as hs
  induction hs with
  | nil => intro p hp; rfl
  | @cons a f args as he hs ih =>
    intro p hp
    have ha := success_correct f.2 _ (he p hp)
    simp only [List.map_cons]
    cases hv : evV g x .callByValueSeq T E a p with
    | none =>
      have hv' : evV h x .callByValueSeq U E f.2.success p=some none := by rw [ha,hv]; rfl
      rw [evSeq_cons_fail hv',evSeq_cons_none hv]; rfl
    | some v => cases v with
      | none =>
        have hv' : evV h x .callByValueSeq U E f.2.success p=some none := by rw [ha,hv]; rfl
        rw [evSeq_cons_fail hv',evSeq_cons_fail hv]; rfl
      | some q =>
        have hv' : evV h x .callByValueSeq U E f.2.success p=some (some q) := by rw [ha,hv]; rfl
        have hq := SequentialClock.expression_descending hd E a p q hv
        rw [evSeq_cons_ok hv',evSeq_cons_ok hv,ih q (by omega)]
        cases evSeqArgs g x .callByValueSeq T E args q with
        | none => rfl
        | some v => cases v <;> rfl

theorem zero_correct (hd : SequentialClock.Descending T) :
    ∀ {args : List MExp} {as : List (Forms × Forms)} {p : Nat},
    Entries g h x T U E p args as →
    evV h x .callByValueSeq U E (zeroArgs as) p=
      zeroArgsResult p (evSeqArgs g x .callByValueSeq T E args p) := by
  intro args
  induction args with
  | nil => intro as p hs; cases hs; simp [zeroArgs,evSeqArgs,zeroArgsResult,evV]
  | cons a args ih =>
    intro as p hs
    cases hs with
    | @cons _ f _ as he hs =>
      obtain ⟨az,ap,af⟩ := he.1
      change evV h x .callByValueSeq U E (.seq f.1.zero (zeroArgs as)) p=_
      cases hv : evV g x .callByValueSeq T E a p with
      | none =>
        have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by rw [az,hv]; rfl
        rw [evV_seq_fail hz,evSeq_cons_none hv]; rfl
      | some v => cases v with
        | none =>
          have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by rw [az,hv]; rfl
          rw [evV_seq_fail hz,evSeq_cons_fail hv]; rfl
        | some q =>
          have hq := SequentialClock.expression_descending hd E a p q hv
          by_cases hqp : q=p
          · subst q
            have hz : evV h x .callByValueSeq U E f.1.zero p=some (some p) := by simp [az,hv,zeroResult]
            rw [evV_seq_ok hz,ih hs,evSeq_cons_ok hv]
            cases evSeqArgs g x .callByValueSeq T E args p with
            | none => rfl
            | some v => cases v <;> rfl
          · have hz : evV h x .callByValueSeq U E f.1.zero p=some none := by simp [az,hv,zeroResult,hqp]
            rw [evV_seq_fail hz,evSeq_cons_ok hv]
            cases ht : evSeqArgs g x .callByValueSeq T E args q with
            | none => rfl
            | some v => cases v with
              | none => rfl
              | some pair =>
                obtain ⟨W,j⟩ := pair
                have hj := (SequentialClock.arguments_metadata hd E args q W j ht).1
                simp [zeroArgsResult,show j≠p by omega]

theorem failure_correct (hd : SequentialClock.Descending T) :
    ∀ {args : List MExp} {as : List (Forms × Forms)} {p : Nat},
    Entries g h x T U E p args as →
    evV h x .callByValueSeq U E (failureArgs as) p=
      failureArgsResult p (evSeqArgs g x .callByValueSeq T E args p) := by
  intro args
  induction args with
  | nil => intro as p hs; cases hs; rw [failureArgs]; rfl
  | cons a args ih =>
    intro as p hs
    cases hs with
    | @cons _ f _ as he hs =>
      obtain ⟨az,ap,af⟩ := he.1
      rw [failureArgs]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => simp [evV,az,ap,af,hv,zeroResult,positiveResult,failureResult,
          evSeqArgs,failureArgsResult,MExp.andP]
      | some v => cases v with
        | none => simp [evV,af,hv,failureResult,evSeqArgs,failureArgsResult]
        | some q =>
          have hq := SequentialClock.expression_descending hd E a p q hv
          by_cases hqp : q=p
          · subst q
            have ht := ih hs
            cases hr : evSeqArgs g x .callByValueSeq T E args p with
            | none => simp [evV,az,ap,af,hv,zeroResult,positiveResult,failureResult,
                MExp.andP,ht,hr,evSeqArgs,failureArgsResult]
            | some v => cases v <;>
                simp [evV,az,ap,af,hv,zeroResult,positiveResult,failureResult,
                  MExp.andP,ht,hr,evSeqArgs,failureArgsResult]
          · have hqp' : q<p := by omega
            have ht := ih (entries_reset hs hqp')
            simp only [evV,az,ap,af,hv,zeroResult,positiveResult,failureResult,if_neg hqp,
              MExp.andP]
            rw [ht]
            rw [evSeq_cons_ok hv]
            cases evSeqArgs g x .callByValueSeq T E args q with
            | none => rfl
            | some v => cases v <;> rfl

end Shallot.MacroPeg.CBV.SequentialTotalArguments
