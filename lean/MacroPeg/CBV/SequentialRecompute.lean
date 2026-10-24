import MacroPeg.CBV.SequentialClock

namespace Shallot.MacroPeg.CBV.SequentialRecompute

open Shallot (beqChar leChar stripPrefix?)

/-! Recompute individual rule queries instead of constructing table rows.
The linear clock comes from SequentialClock; no memo table is retained.
This module proves semantic equivalence, not a Turing-machine space bound. -/

abbrev Query := Nat → List (List Char) → Nat → Res

mutual
  def eval (g : MGrammar) (x : List Char) (Q : Query) (E : List (List Char)) : MExp → Nat → Res
    | .eps, p => some (some p)
    | .any, p =>
      match sfx x p with
      | _ :: rest => some (some rest.length)
      | [] => some none
    | .chr c, p =>
      match sfx x p with
      | d :: rest => if beqChar c d then some (some rest.length) else some none
      | [] => some none
    | .range lo hi, p =>
      match sfx x p with
      | d :: rest => if leChar lo d && leChar d hi then some (some rest.length) else some none
      | [] => some none
    | .lit w, p =>
      match stripPrefix? w (sfx x p) with
      | some rest => some (some rest.length)
      | none => some none
    | .param k, p =>
      match E[k]? with
      | some w =>
        match stripPrefix? w (sfx x p) with
        | some rest => some (some rest.length)
        | none => some none
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some rule =>
        if rule.arity = args.length then
          match evalArgs g x Q E args p with
          | some (some (W, q)) => Q i W q
          | some none => some none
          | none => none
        else some none
      | none => some none
    | .seq a b, p =>
      match eval g x Q E a p with
      | some (some q) => eval g x Q E b q
      | result => result
    | .alt a b, p =>
      match eval g x Q E a p with
      | some none => eval g x Q E b p
      | result => result
    | .star a, p => evStar (fun q => eval g x Q E a q) p
    | .notP a, p =>
      match eval g x Q E a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  def evalArgs (g : MGrammar) (x : List Char) (Q : Query) (E : List (List Char)) :
      List MExp → Nat → Option (Option (List (List Char) × Nat))
    | [], p => some (some ([], p))
    | a :: args, p =>
      match eval g x Q E a p with
      | some (some q) =>
        match evalArgs g x Q E args q with
        | some (some (W, r)) => some (some (pre x p q :: W, r))
        | result => result
      | some none => some none
      | none => none
end

mutual
  theorem eval_eq {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W p, p ≤ x.length → Q i W p = valAt (T i W) p) (E : List (List Char)) :
      ∀ e p, p ≤ x.length → eval g x Q E e p = evV g x .callByValueSeq T E e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .param _, _, _ | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _
    | .invoke _ _ _, _, _ => rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [eval, evV, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [eval, evV, hr, if_pos ha]
          rw [args_eq hT hQ E args p hp]
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              exact hQ i W q (evSeq_mem hT args p W q hp hv).2
        · simp only [eval, evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E a p hp]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q => exact eval_eq hT hQ E b q (evV_ok hT a p hp q hv)
    | .alt a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E a p hp]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => exact eval_eq hT hQ E b p hp
        | some q => rfl
    | .notP a, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E a p hp]
      rfl
    | .star a, p, hp => by
      simp only [eval, evV_star]
      exact evStar_congr p (fun q hq => eval_eq hT hQ E a q (by omega))

  theorem args_eq {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W p, p ≤ x.length → Q i W p = valAt (T i W) p) (E : List (List Char)) :
      ∀ args p, p ≤ x.length →
        evalArgs g x Q E args p = evSeqArgs g x .callByValueSeq T E args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      simp only [evalArgs, evSeqArgs]
      rw [eval_eq hT hQ E a p hp]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          simp only []
          rw [args_eq hT hQ E args q (evV_ok hT a p hp q hv)]
          rfl
end

/-- Each body query spends one clock unit. No list of table entries is built. -/
def query (g : MGrammar) (x : List Char) : Nat → Query
  | 0 => fun _ _ _ => none
  | m + 1 => fun i E p =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | some rule => eval g x (query g x m) E rule.body p
      | none => none
    else none

theorem query_eq (g : MGrammar) (x : List Char) : ∀ m i E p,
    query g x m i E p = valAt (tblV g x .callByValueSeq m i E) p
  | 0, _, _, _ => by simp [query, tblV, valAt_nil]
  | m + 1, i, E, p => by
    by_cases hp : p ≤ x.length
    · cases hr : ruleAtM g.rules i with
      | none => simp [query, hp, hr, tblV, valAt_nil]
      | some rule =>
        rw [valAt_tblV_succ hr E hp]
        simp only [query, if_pos hp, hr]
        exact eval_eq (tblV_ok g x .callByValueSeq m) (fun i E p _ => query_eq g x m i E p) E rule.body p hp
    · cases hr : ruleAtM g.rules i with
      | none => simp [query, hp, tblV, hr, valAt_nil]
      | some rule => simp [query, hp, tblV, hr, valAt_rangeMap]

theorem eval_at_clock (g : MGrammar) (x : List Char) (m : Nat) (E : List (List Char))
    (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    eval g x (query g x m) E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) E e p :=
  eval_eq (tblV_ok g x .callByValueSeq m) (fun i E p _ => query_eq g x m i E p) E e p hp

def run (g : MGrammar) (x : List Char) (e : MExp) : Res :=
  eval g x (query g x (SequentialClock.positionClock g x.length)) [] e x.length

def observation (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x e with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem observation_eq (g : MGrammar) (x : List Char) (e : MExp) :
    observation g x e = SequentialClock.decide g x e := by
  unfold observation run SequentialClock.decide
  rw [eval_at_clock g x _ [] e x.length (Nat.le_refl _)]
  rfl

theorem observation_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) (r : Option (List Char)) :
    observation g x e = some r ↔ SObs g .callByValueSeq e x r := by
  rw [observation_eq]
  exact SequentialClock.decide_iff hg he x r

theorem observation_none_iff {g : MGrammar} (hg : g.FirstOrder) {e : MExp} (he : e.FirstOrder)
    (x : List Char) : observation g x e = none ↔ ∀ r, ¬ SObs g .callByValueSeq e x r := by
  rw [observation_eq]
  exact SequentialClock.decide_none_iff hg he x

end Shallot.MacroPeg.CBV.SequentialRecompute
