import MacroPeg.CBV.SequentialAddressedEvaluator
import MacroPeg.CBV.SequentialPositionEvaluator

/-! Fill numeric Seq rows by remaining-input position. Only the finite vector
of empty-environment calls is iterated at a position. General rows are then
computed once at that position, using the already filled smaller positions.
The array traversal and arity-dependent row count remain explicit; no common
polynomial degree, grammar translation or language separation is claimed. -/
namespace Shallot.MacroPeg.CBV.SequentialPositionRows

open SequentialAddressedEvaluator (spans origin)
open SequentialRowAddress (address)
open SequentialTupleKeys (Key keys values cursor cuts)
open SequentialSpanRecompute (decodeEnv ValidEnv)
open SequentialCaptureRegions (Window)
open SequentialLocalCorrectness (canonical)

abbrev Vector (g : MGrammar) := FiniteResultClosure.Vector g.rules.length

def Below (g : MGrammar) (x : List Char) (b : Nat) (A : Array Res) : Prop :=
  ∀ i r path, ruleAtM g.rules i=some r → path.length=r.arity+1 →
    (∀ j∈path,j≤x.length) → ValidEnv x.length (spans path) → cursor path≤x.length →
    cursor path<b → A[address g x.length i path]? =
      some (valAt (canonical g x i (values x path)) (cursor path))

private theorem lower_query {g : MGrammar} {x : List Char} {b : Nat} {A : Array Res}
    (hA : Below g x b A) {i : Nat} {r : MRule} {p q : Nat}
    {W : SequentialSpanRecompute.Env} (hr : ruleAtM g.rules i=some r)
    (hlen : r.arity=W.length) (hp : p≤x.length) (hw : Window p q W) (hq : q<b) :
    SequentialAddressedEvaluator.query g x.length A i W q =
      valAt (canonical g x i (decodeEnv x W)) q := by
  have he := hA i r (cuts p W) hr (by simp [cuts]; omega)
    (SequentialTupleKeys.window_cuts_bounded hw hp)
    (by rw [SequentialAddressedEvaluator.spans_cuts hw]; exact hw.valid hp)
    (by rw [SequentialTupleKeys.window_cursor hw]; exact Nat.le_trans hw.descending hp)
    (by rw [SequentialTupleKeys.window_cursor hw]; exact hq)
  simp only [SequentialTupleKeys.window_values hw x,SequentialTupleKeys.window_cursor hw] at he
  simp only [SequentialAddressedEvaluator.query,SequentialAddressedEvaluator.window_origin hw,
    he,Option.getD_some]

def localQuery (g : MGrammar) (x : List Char) (b : Nat) (A : Array Res) (V : Vector g) :
    SequentialSpanRecompute.Query := fun i W q =>
  if q<b then SequentialAddressedEvaluator.query g x.length A i W q else
  if q=b then if hi : i<g.rules.length then V ⟨i,hi⟩ else none else none

private theorem localQuery_agree {g : MGrammar} {x : List Char} {b : Nat} {A : Array Res}
    (hA : Below g x b A) (V : Vector g) :
    SequentialSpanWindows.Agree g x (localQuery g x b A V)
      (SequentialLocalClosure.overlay g x b (canonical g x) V) := by
  intro i r p q W hr hlen hp hw
  have hq := Nat.le_trans hw.descending hp
  by_cases hqb : q<b
  · rw [SequentialLocalClosure.overlay_lower g x b _ V i _ q hq hqb]
    simp only [localQuery,if_pos hqb]
    exact lower_query hA hr hlen hp hw hqb
  · by_cases he : q=b
    · subst q
      rw [SequentialLocalClosure.overlay_here g x b _ V ⟨i,ruleAtM_lt hr⟩ _ hq]
      simp [localQuery,ruleAtM_lt hr]
    · simp [localQuery,hqb,he,SequentialLocalClosure.overlay,valAt_rangeMap,hq]

def emptyEnv (p arity : Nat) : SequentialSpanRecompute.Env := List.replicate arity (p,p)

/-- Materialize each finite vector before exposing its indexed getter. -/
def freeze {g : MGrammar} (V : Vector g) : Vector g :=
  let A := Array.ofFn V
  fun i => A[i.val]'(by simp [A])

private theorem freeze_eq {g : MGrammar} (V : Vector g) : freeze V=V := by
  funext i
  simp [freeze]

def localRounds (g : MGrammar) (x : List Char) (p : Nat) (A : Array Res) : Nat → Vector g
  | 0 => freeze (fun _ => none)
  | k+1 =>
    let previous := localRounds g x p A k
    freeze (fun i => SequentialSpanRecompute.eval g x
      (localQuery g x p A previous) (emptyEnv p g.rules[i].arity) g.rules[i].body p)

private theorem emptyEnv_valid {x : List Char} {p : Nat} (hp : p≤x.length) (arity : Nat) :
    ValidEnv x.length (emptyEnv p arity) := by
  intro span hs
  have he : span=(p,p) := (List.mem_replicate.mp hs).2
  subst span
  exact ⟨Nat.le_refl _,hp⟩

theorem localRounds_eq {g : MGrammar} {x : List Char} {p : Nat} {A : Array Res}
    (hA : Below g x p A) (hp : p≤x.length) : ∀ k,
    localRounds g x p A k = SequentialLocalClosure.rounds g x p (canonical g x) k := by
  intro k
  induction k with
  | zero => rw [localRounds,freeze_eq]; rfl
  | succ k ih =>
    rw [localRounds,freeze_eq]
    funext i
    change SequentialSpanRecompute.eval g x (localQuery g x p A (localRounds g x p A k)) _ _ p =
      evV g x .callByValueSeq
        (SequentialLocalClosure.overlay g x p (canonical g x)
          (SequentialLocalClosure.rounds g x p (canonical g x) k)) _ _ p
    rw [ih]
    have hd := SequentialLocalClosure.overlay_descending g x p (canonical g x)
      (SequentialClock.table_descending g x _) _
      (SequentialLocalClosure.rounds_descending g x p (canonical g x)
        (SequentialClock.table_descending g x _) k)
    have he := SequentialSpanWindows.eval_eq hd (localQuery_agree hA _)
      (emptyEnv p g.rules[i].arity) (emptyEnv_valid hp _) g.rules[i].body p hp
    simpa [emptyEnv,decodeEnv,pre] using he

def evaluate (g : MGrammar) (x : List Char) (p : Nat) (A : Array Res)
    (E : SequentialSpanRecompute.Env) (e : MExp) : Res :=
  SequentialSpanRecompute.eval g x (localQuery g x p A (localRounds g x p A g.rules.length)) E e p

theorem evaluate_correct {g : MGrammar} {x : List Char} {p : Nat} {A : Array Res}
    (hA : Below g x p A) (hp : p≤x.length) (E : SequentialSpanRecompute.Env)
    (hE : ValidEnv x.length E) (e : MExp) :
    evaluate g x p A E e = evV g x .callByValueSeq (canonical g x) (decodeEnv x E) e p := by
  unfold evaluate
  rw [localRounds_eq hA hp]
  have hd := SequentialLocalClosure.overlay_descending g x p (canonical g x)
    (SequentialClock.table_descending g x _) _
    (SequentialLocalClosure.rounds_descending g x p (canonical g x)
      (SequentialClock.table_descending g x _) g.rules.length)
  exact (SequentialSpanWindows.eval_eq hd (localQuery_agree hA _) E hE e p hp).trans
    (SequentialLocalCorrectness.expression_eq_source g x p hp (decodeEnv x E) e)

private instance (n : Nat) (E : SequentialSpanRecompute.Env) : Decidable (ValidEnv n E) := by
  unfold ValidEnv
  infer_instance

private theorem values_length (x : List Char) : ∀ path : List Nat,
    (values x path).length=path.length-1
  | [] => rfl
  | [_] => rfl
  | a::b::rest => by
    simp only [values,List.length_cons]
    rw [values_length x (b::rest)]
    simp

def fill (g : MGrammar) (x : List Char) (p : Nat) (previous : Array Res) : Array Res :=
  let V := localRounds g x p previous g.rules.length
  ((keys g x.length).map (fun key =>
    if cursor key.path=p then
      if ValidEnv x.length (spans key.path) then
        match ruleAtM g.rules key.rule with
        | none => none
        | some r => SequentialSpanRecompute.eval g x (localQuery g x p previous V)
            (spans key.path) r.body p
      else none
    else (previous[address g x.length key.rule key.path]?).getD none)).toArray

def rows (g : MGrammar) (x : List Char) : Nat → Array Res
  | 0 => ((keys g x.length).map (fun _ => (none : Res))).toArray
  | p+1 => fill g x p (rows g x p)

theorem rows_correct (g : MGrammar) (x : List Char) : ∀ p, p≤x.length+1 →
    Below g x p (rows g x p) := by
  intro p
  induction p with
  | zero => intro hp i r path hr hlen hb hv hq hlt; omega
  | succ p ih =>
    intro hp
    have hprev := ih (by omega)
    intro i r path hr hlen hb hv hq hlt
    simp only [rows,fill,List.getElem?_toArray,List.getElem?_map,
      SequentialRowAddress.keys_get_address hr hlen hb,Option.map_some]
    congr 1
    by_cases he : cursor path=p
    · simp only [if_pos he,if_pos hv,hr]
      change evaluate g x p (rows g x p) (spans path) r.body = _
      rw [evaluate_correct hprev (by omega) (spans path) hv r.body,
        SequentialAddressedEvaluator.decode_spans]
      rw [he]
      exact (SequentialLocalCorrectness.canonical_unfold g x i r hr _
        (by have hh := values_length x path; omega) p (by omega)).symm
    · have hc := hprev i r path hr hlen hb hv hq (by omega)
      simp [he,hc]

def run (g : MGrammar) (x : List Char) (E : SequentialSpanRecompute.Env) (e : MExp) (p : Nat) : Res :=
  SequentialSpanRecompute.eval g x
    (SequentialAddressedEvaluator.query g x.length (rows g x (x.length+1))) E e p

theorem run_correct (g : MGrammar) (x : List Char) (E : SequentialSpanRecompute.Env)
    (hE : ValidEnv x.length E) (e : MExp) (p : Nat) (hp : p≤x.length) :
    run g x E e p = evV g x .callByValueSeq (canonical g x) (decodeEnv x E) e p := by
  refine SequentialSpanWindows.eval_eq (SequentialClock.table_descending g x _) ?_ E hE e p hp
  apply SequentialAddressedEvaluator.query_agree
  intro i r path hr hlen hb hv hq
  exact rows_correct g x (x.length+1) (Nat.le_refl _) i r path hr hlen hb hv hq (by omega)
theorem rows_size (g : MGrammar) (x : List Char) (p : Nat) :
    (rows g x p).size=(keys g x.length).length := by
  cases p <;> simp [rows,fill]

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard (g : MGrammar) (x : List Char) (e : MExp) :
    decide g x e=decideObsV .callByValueSeq g x e := by
  unfold decide
  rw [run_correct g x [] (by intro span hs; cases hs) e _ (Nat.le_refl _)]
  exact SequentialClock.decide_eq_standard g x e

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    decide g x e=some rest ↔ SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_iff hg (by decide) he x rest

theorem undefined_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) : decide g x e=none ↔ ∀ rest, ¬SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard]
  exact decideObsV_none_iff hg (by decide) he x

end Shallot.MacroPeg.CBV.SequentialPositionRows
