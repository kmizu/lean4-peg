import MacroPeg.CBV.FutureSpanRepresentatives

namespace Shallot.MacroPeg.CBV.SequentialFutureQueries

open SequentialSpanRecompute (ValidEnv decodeEnv)
open FutureSpanRepresentatives (normalize environment views)

/-- Keep the cursor fixed. Rewrite the body using a finite live/dead mask and
replace live values by copies wholly inside the remaining input. Searching for
those copies is an explicit meta-level operation, not an ordinary Seq rule. -/
def prepared (g : MGrammar) (x : List Char) (Q : SequentialSpanRecompute.Query)
    (E : SequentialSpanRecompute.Env) (e : MExp) (p : Nat) : Res :=
  let slots := normalize x p E
  SequentialSpanRecompute.eval g x Q (environment slots) (MExp.subst (views slots) e) p

theorem prepared_eq {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (m : Nat)
    (Q : SequentialSpanRecompute.Query)
    (hQ : ∀ i E, ValidEnv x.length E → ∀ p, p≤x.length →
      Q i E p = valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p)
    (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E)
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    prepared g x Q E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p := by
  have hv := FutureSpanRepresentatives.environment_valid hp hE
  have hv' : ValidEnv x.length (environment (normalize x p E)) :=
    fun span hs => ⟨(hv span hs).1, Nat.le_trans (hv span hs).2 hp⟩
  unfold prepared
  rw [SequentialSpanRecompute.eval_eq (g := g) (tblV_ok g x .callByValueSeq m) hQ _ hv' _ p hp]
  exact FutureSpanRepresentatives.expression (by decide) (tblV_sound hg (by decide) m)
    hp E hE e he p (Nat.le_refl _)

def query (g : MGrammar) (x : List Char) : Nat → SequentialSpanRecompute.Query
  | 0 => fun _ _ _ => none
  | m+1 => fun i E p =>
    if p≤x.length then
      match ruleAtM g.rules i with
      | none => none
      | some r => prepared g x (query g x m) E r.body p
    else none

theorem query_eq {g : MGrammar} (hg : g.FirstOrder) (x : List Char) : ∀ m i E,
    ValidEnv x.length E → ∀ p,
    query g x m i E p = valAt (tblV g x .callByValueSeq m i (decodeEnv x E)) p := by
  intro m
  induction m with
  | zero => intro i E hE p; simp [query,tblV,valAt_nil]
  | succ m ih =>
    intro i E hE p
    by_cases hp : p≤x.length
    · cases hr : ruleAtM g.rules i with
      | none => simp [query,hp,hr,tblV,valAt_nil]
      | some r =>
        rw [valAt_tblV_succ hr _ hp]
        simp only [query,if_pos hp,hr]
        exact prepared_eq hg x m _ (fun i E hE p _ => ih i E hE p)
          E hE r.body (hg r (ruleAtM_mem hr)) p hp
    · cases hr : ruleAtM g.rules i <;> simp [query,hp,hr,tblV,valAt_nil,valAt_rangeMap]

def run (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (e : MExp) (p : Nat) : Res := prepared g x (query g x m) E e p

theorem run_correct {g : MGrammar} (hg : g.FirstOrder) (x : List Char) (m : Nat)
    (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E)
    (e : MExp) (he : e.FirstOrder) (p : Nat) (hp : p≤x.length) :
    run g x m E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p :=
  prepared_eq hg x m _ (fun i E hE p _ => query_eq hg x m i E hE p) E hE e he p hp

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x (SequentialClock.positionClock g x.length) [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard {g : MGrammar} (hg : g.FirstOrder) (x : List Char)
    (e : MExp) (he : e.FirstOrder) : decide g x e = decideObsV .callByValueSeq g x e := by
  unfold decide
  rw [run_correct hg x _ [] (by intro span hs; cases hs) e he _ (Nat.le_refl _)]
  exact SequentialClock.decide_eq_standard g x e

theorem observations_iff {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    decide g x e = some rest ↔ SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard hg x e he]
  exact decideObsV_iff hg (by decide) he x rest

theorem undefined_iff {g : MGrammar} (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) : decide g x e = none ↔ ∀ rest, ¬SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard hg x e he]
  exact decideObsV_none_iff hg (by decide) he x

end Shallot.MacroPeg.CBV.SequentialFutureQueries
