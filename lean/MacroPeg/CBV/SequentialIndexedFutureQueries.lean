import MacroPeg.CBV.SequentialIndexedReplay

namespace Shallot.MacroPeg.CBV.SequentialIndexedFutureQueries

open RightmostCaptureIndex (table)
open SequentialSpanRecompute (ValidEnv decodeEnv)

/-- Build the quadratic whole-input index once, outside the recursive parser.
Every parameter replay then selects a future source through one metadata cell.
Matching the selected word still takes character comparisons. -/
def query (g : MGrammar) (x : List Char) (A : Array (Option FutureSpanRepresentatives.Span)) : Nat → SequentialSpanRecompute.Query
  | 0 => fun _ _ _ => none
  | m + 1 => fun i E p =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | none => none
      | some r => SequentialIndexedReplay.eval g x A (query g x A m) E r.body p
    else none

theorem query_eq (g : MGrammar) (x : List Char) : ∀ m i E, ValidEnv x.length E → ∀ p,
    query g x (table x) m i E p = valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p := by
  intro m
  induction m with
  | zero => intro i E hE p; simp [query, tblV, valAt_nil]
  | succ m ih =>
    intro i E hE p
    by_cases hp : p ≤ x.length
    · cases hr : ruleAtM g.rules i with
      | none => simp [query, hp, hr, tblV, valAt_nil]
      | some r =>
        rw [valAt_tblV_succ hr _ hp]
        simp only [query, if_pos hp, hr]
        exact SequentialIndexedReplay.eval_eq (g := g) (tblV_ok g x .callByValueSeq m)
          (fun i E hE p _ => ih i E hE p) E hE r.body p hp
    · cases hr : ruleAtM g.rules i <;> simp [query, hp, hr, tblV, valAt_nil, valAt_rangeMap]

def run (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (e : MExp) (p : Nat) : Res :=
  let A := table x
  SequentialIndexedReplay.eval g x A (query g x A m) E e p

theorem run_correct (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (hE : ValidEnv x.length E) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    run g x m E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p :=
  SequentialIndexedReplay.eval_eq (tblV_ok g x .callByValueSeq m)
    (fun i E hE p _ => query_eq g x m i E hE p) E hE e p hp

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x (SequentialClock.positionClock g x.length) [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard (g : MGrammar) (x : List Char) (e : MExp) :
    decide g x e = decideObsV .callByValueSeq g x e := by
  unfold decide
  rw [run_correct g x _ [] (by intro span hs; cases hs) e _ (Nat.le_refl _)]
  exact SequentialClock.decide_eq_standard g x e

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    decide g x e = some rest ↔ SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_iff hg (by decide) he x rest

theorem undefined_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) : decide g x e = none ↔ ∀ rest, ¬SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_none_iff hg (by decide) he x


end Shallot.MacroPeg.CBV.SequentialIndexedFutureQueries
