import MacroPeg.CBV.CaptureReadSupport

namespace Shallot.MacroPeg.CBV.SequentialCanonicalQueries

open CaptureReadSupport (canonical)
open SequentialSpanRecompute (ValidEnv decodeEnv)

/-- Preserve the complete argument evaluator. Only after entering a rule,
replace the spans of parameters absent from its body by empty spans. -/
def query (g : MGrammar) (x : List Char) : Nat → SequentialSpanRecompute.Query
  | 0 => fun _ _ _ => none
  | m + 1 => fun i E p =>
    if p ≤ x.length then
      match ruleAtM g.rules i with
      | none => none
      | some r => SequentialSpanRecompute.eval g x (query g x m) (canonical r.body E) r.body p
    else none

theorem query_eq (g : MGrammar) (x : List Char) : ∀ m i E, ValidEnv x.length E → ∀ p,
    query g x m i E p = valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p := by
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
        have he := SequentialSpanRecompute.eval_eq (g := g) (tblV_ok g x .callByValueSeq m)
          (fun i E hE p _ => ih i E hE p) (canonical r.body E)
          (CaptureReadSupport.canonical_valid r.body hE) r.body p hp
        exact he.trans (CaptureReadSupport.canonical_body g x .callByValueSeq _ r.body E p)
    · cases hr : ruleAtM g.rules i <;> simp [query, hp, hr, tblV, valAt_nil, valAt_rangeMap]

def run (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (e : MExp) (p : Nat) : Res :=
  SequentialSpanRecompute.eval g x (query g x m) E e p

theorem run_correct (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (hE : ValidEnv x.length E) (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    run g x m E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p :=
  SequentialSpanRecompute.eval_eq (tblV_ok g x .callByValueSeq m)
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

/-- A row key is shared only within one physical table layer. -/
def key (g : MGrammar) (i : Nat) (E : SequentialSpanRecompute.Env) (p : Nat) :
    Nat × SequentialSpanRecompute.Env × Nat :=
  (i, match ruleAtM g.rules i with
    | some r => canonical r.body E
    | none => E, p)

theorem key_sound {g : MGrammar} {x : List Char} {i j p q : Nat}
    {E F : SequentialSpanRecompute.Env}
    (he : key g i E p = key g j F q) (m : Nat) :
    valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p =
      valAt (tblV g x .callByValueSeq m j (decodeEnv x F)) q := by
  have hi : i=j := congrArg Prod.fst he
  subst j
  have hp : p=q := congrArg (fun k => k.2.2) he
  subst q
  cases hr : ruleAtM g.rules i with
  | none => cases m <;> simp [tblV, hr, valAt_nil]
  | some r =>
    have henv : canonical r.body E = canonical r.body F := by
      simpa only [key, hr] using congrArg (fun k => k.2.1) he
    rw [← CaptureReadSupport.row_canonical g x .callByValueSeq m i r hr E p,
      ← CaptureReadSupport.row_canonical g x .callByValueSeq m i r hr F p, henv]

theorem query_key_agree {g : MGrammar} {x : List Char} {i j p q : Nat}
    {E F : SequentialSpanRecompute.Env} (hE : ValidEnv x.length E) (hF : ValidEnv x.length F)
    (he : key g i E p = key g j F q) (m : Nat) :
    query g x m i E p = query g x m j F q := by
  rw [query_eq g x m i E hE p, query_eq g x m j F hF q]
  exact key_sound he m

end Shallot.MacroPeg.CBV.SequentialCanonicalQueries
