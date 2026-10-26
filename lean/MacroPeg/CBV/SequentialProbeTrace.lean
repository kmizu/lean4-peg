import MacroPeg.CBV.SequentialSpanRecompute

/-! Record the rule queries made by the finite-clock Seq evaluator, including
queries under predicates and failed final repetition attempts. Erasing the
record gives exactly the existing span evaluator, without restricting grammar,
raw expressions, or incoming span environments. The trace does not charge for
input accesses, matching, address arithmetic, or table construction. -/
namespace Shallot.MacroPeg.CBV.SequentialProbeTrace

structure Request where
  rule : Nat
  env : SequentialSpanRecompute.Env
  cursor : Nat
  deriving DecidableEq, Repr

abbrev Logged (α : Type) := α × List Request
abbrev Query := Nat → SequentialSpanRecompute.Env → Nat → Logged Res

def erase (Q : Query) : SequentialSpanRecompute.Query := fun i E p => (Q i E p).1

def star (f : Nat → Logged Res) (p : Nat) : Logged Res :=
  let head := f p
  match head.1 with
  | none => (none, head.2)
  | some none => (some (some p), head.2)
  | some (some q) =>
    if q < p then
      let tail := star f q
      (tail.1, head.2 ++ tail.2)
    else (none, head.2)
termination_by p
decreasing_by omega

theorem star_step {f : Nat → Logged Res} {p q : Nat} {log : List Request}
    (h : f p = (some (some q), log)) (hq : q < p) :
    star f p = ((star f q).1, log ++ (star f q).2) := by
  rw [star, h]
  simp only [if_pos hq]

theorem star_fail {f : Nat → Logged Res} {p : Nat} {log : List Request}
    (h : f p = (some none, log)) : star f p = (some (some p), log) := by
  rw [star, h]

theorem star_erase (f : Nat → Logged Res) (p : Nat) :
    (star f p).1 = evStar (fun q => (f q).1) p := by
  rw [star, evStar]
  cases hv : (f p).1 with
  | none => rfl
  | some result =>
    cases result with
    | none => rfl
    | some q =>
      by_cases hq : q < p
      · simp only [if_pos hq]
        exact star_erase f q
      · simp only [if_neg hq]
termination_by p

mutual
  def eval (g : MGrammar) (x : List Char) (Q : Query) (E : SequentialSpanRecompute.Env) :
      MExp → Nat → Logged Res
    | .call i args, p =>
      match ruleAtM g.rules i with
      | none => (some none, [])
      | some r =>
        if r.arity = args.length then
          let actuals := evalArgs g x Q E args p
          match actuals.1 with
          | none => (none, actuals.2)
          | some none => (some none, actuals.2)
          | some (some (W,q)) =>
            let body := Q i W q
            (body.1, actuals.2 ++ (⟨i,W,q⟩ :: body.2))
        else (some none, [])
    | .seq a b, p =>
      let left := eval g x Q E a p
      match left.1 with
      | some (some q) =>
        let right := eval g x Q E b q
        (right.1, left.2 ++ right.2)
      | _ => left
    | .alt a b, p =>
      let left := eval g x Q E a p
      match left.1 with
      | some none =>
        let right := eval g x Q E b p
        (right.1, left.2 ++ right.2)
      | _ => left
    | .notP a, p =>
      let body := eval g x Q E a p
      (match body.1 with
        | none => none
        | some none => some (some p)
        | some (some _) => some none, body.2)
    | .star a, p => star (fun q => eval g x Q E a q) p
    | e, p => (SequentialSpanRecompute.eval g x (erase Q) E e p, [])

  def evalArgs (g : MGrammar) (x : List Char) (Q : Query) (E : SequentialSpanRecompute.Env) :
      List MExp → Nat → Logged (Option (Option (SequentialSpanRecompute.Env × Nat)))
    | [], p => (some (some ([],p)), [])
    | a :: args, p =>
      let head := eval g x Q E a p
      match head.1 with
      | none => (none, head.2)
      | some none => (some none, head.2)
      | some (some q) =>
        let tail := evalArgs g x Q E args q
        (match tail.1 with
          | none => none
          | some none => some none
          | some (some (W,r)) => some (some ((p,min q p)::W,r)), head.2 ++ tail.2)
end

mutual
  theorem eval_erase (g : MGrammar) (x : List Char) (Q : Query) (E : SequentialSpanRecompute.Env) :
      ∀ e p, (eval g x Q E e p).1 = SequentialSpanRecompute.eval g x (erase Q) E e p
    | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _
    | .dbg _, _ | .lam _ _, _ | .callParam _ _, _ | .invoke _ _ _, _ => rfl
    | .call i args, p => by
      simp only [eval, SequentialSpanRecompute.eval]
      cases hr : ruleAtM g.rules i with
      | none => rfl
      | some r =>
        by_cases ha : r.arity = args.length
        · simp only [if_pos ha, ← args_erase g x Q E args p]
          cases hv : (evalArgs g x Q E args p).1 with
          | none => rfl
          | some result => cases result <;> rfl
        · simp only [if_neg ha]
    | .seq a b, p => by
      simp only [eval, SequentialSpanRecompute.eval, ← eval_erase g x Q E a p]
      cases hv : (eval g x Q E a p).1 with
      | none => exact hv
      | some result =>
        cases result with
        | none => exact hv
        | some q => exact eval_erase g x Q E b q
    | .alt a b, p => by
      simp only [eval, SequentialSpanRecompute.eval, ← eval_erase g x Q E a p]
      cases hv : (eval g x Q E a p).1 with
      | none => exact hv
      | some result =>
        cases result with
        | none => exact eval_erase g x Q E b p
        | some q => exact hv
    | .notP a, p => by
      simp only [eval, SequentialSpanRecompute.eval, ← eval_erase g x Q E a p]
      cases (eval g x Q E a p).1 with
      | none => rfl
      | some result => cases result <;> rfl
    | .star a, p => by
      simp only [eval, SequentialSpanRecompute.eval]
      rw [star_erase]
      exact evStar_congr p (fun q _ => eval_erase g x Q E a q)

  theorem args_erase (g : MGrammar) (x : List Char) (Q : Query) (E : SequentialSpanRecompute.Env) :
      ∀ args p, (evalArgs g x Q E args p).1 = SequentialSpanRecompute.evalArgs g x (erase Q) E args p
    | [], _ => rfl
    | a :: args, p => by
      simp only [evalArgs, SequentialSpanRecompute.evalArgs, ← eval_erase g x Q E a p]
      cases hv : (eval g x Q E a p).1 with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          simp only []
          rw [← args_erase g x Q E args q]
          cases (evalArgs g x Q E args q).1 with
          | none => rfl
          | some result => cases result <;> rfl
end

def query (g : MGrammar) (x : List Char) : Nat → Query
  | 0 => fun _ _ _ => (none, [])
  | m + 1 => fun i E p =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | none => (none, [])
      | some r => eval g x (query g x m) E r.body p
    else (none, [])

theorem query_erase (g : MGrammar) (x : List Char) : ∀ m,
    erase (query g x m) = SequentialSpanRecompute.query g x m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    funext i E p
    simp only [erase, query, SequentialSpanRecompute.query]
    by_cases hp : p ≤ x.length
    · simp only [if_pos hp]
      cases ruleAtM g.rules i with
      | none => rfl
      | some r => simpa only [ih] using eval_erase g x (query g x m) E r.body p
    · simp only [if_neg hp]

def run (g : MGrammar) (x : List Char) (m : Nat) (e : MExp) : Logged Res :=
  eval g x (query g x m) [] e x.length

theorem run_correct (g : MGrammar) (x : List Char) (m : Nat) (e : MExp) :
    (run g x m e).1 = evV g x .callByValueSeq (tblV g x .callByValueSeq m) [] e x.length := by
  rw [run, eval_erase, query_erase]
  exact SequentialSpanRecompute.eval_at_clock g x m [] (by intro span hs; cases hs) e _ (Nat.le_refl _)

end Shallot.MacroPeg.CBV.SequentialProbeTrace
