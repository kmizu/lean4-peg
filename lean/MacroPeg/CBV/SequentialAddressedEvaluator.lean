import MacroPeg.CBV.SequentialRowAddress
import MacroPeg.CBV.SequentialSpanWindows

/-! Dense numeric Seq rows. A call computes one address from its actual
capture endpoints and performs one array lookup. This counts the row read,
not the cost of evaluating an expression, matching a parameter, constructing
the table, or implementing the address arithmetic on a Turing machine. -/
namespace Shallot.MacroPeg.CBV.SequentialAddressedEvaluator

open SequentialTupleKeys (Key keys values cursor cuts)
open SequentialRowAddress (address)
open SequentialSpanRecompute (ValidEnv decodeEnv)
open SequentialCaptureRegions (Window)

def spans : List Nat → SequentialSpanRecompute.Env
  | a :: b :: rest => (a,b) :: spans (b :: rest)
  | _ => []

theorem decode_spans (x : List Char) : ∀ path, decodeEnv x (spans path) = values x path
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simpa only [spans, decodeEnv, List.map_cons, values] using
      congrArg (List.cons (pre x a b)) (decode_spans x (b :: rest))

theorem spans_cuts {p q : Nat} {W : SequentialSpanRecompute.Env} (h : Window p q W) :
    spans (cuts p W) = W := by
  induction h with
  | nil => rfl
  | cons hj ht ih =>
    simpa only [cuts, List.map_cons, spans, List.cons.injEq, true_and] using ih

def origin (W : SequentialSpanRecompute.Env) (q : Nat) : Nat :=
  match W with
  | [] => q
  | (p,_) :: _ => p

theorem window_origin {p q : Nat} {W : SequentialSpanRecompute.Env} (h : Window p q W) :
    origin W q = p := by cases h <;> rfl

/-- The implementation has exactly one array read, with a numeric address.
Only actual call tuples are required to denote meaningful rows. -/
def query (g : MGrammar) (n : Nat) (rows : Array Res) : SequentialSpanRecompute.Query :=
  fun i W q => (rows[address g n i (cuts (origin W q) W)]?).getD none

def Correct (g : MGrammar) (x : List Char) (T : SequentialClock.Table) (rows : Array Res) : Prop :=
  ∀ i r path, ruleAtM g.rules i = some r → path.length = r.arity + 1 →
    (∀ j ∈ path, j ≤ x.length) → ValidEnv x.length (spans path) → cursor path ≤ x.length →
    rows[address g x.length i path]? = some (valAt (T i (values x path)) (cursor path))

theorem query_agree {g : MGrammar} {x : List Char} {T : SequentialClock.Table}
    {rows : Array Res} (hc : Correct g x T rows) :
    SequentialSpanWindows.Agree g x (query g x.length rows) T := by
  intro i r p q W hr hlen hp hw
  have hl : (cuts p W).length = r.arity + 1 := by simp [cuts]; omega
  have he := hc i r (cuts p W) hr hl (SequentialTupleKeys.window_cuts_bounded hw hp)
    (by rw [spans_cuts hw]; exact hw.valid hp)
    (by rw [SequentialTupleKeys.window_cursor hw]; exact Nat.le_trans hw.descending hp)
  simp only [SequentialTupleKeys.window_values hw x, SequentialTupleKeys.window_cursor hw] at he
  simp only [query, window_origin hw, he, Option.getD_some]

private instance (n : Nat) (E : SequentialSpanRecompute.Env) : Decidable (ValidEnv n E) := by
  unfold ValidEnv
  infer_instance

def compute (g : MGrammar) (x : List Char) (previous : Array Res) (key : Key) : Res :=
  if ValidEnv x.length (spans key.path) then
    if cursor key.path ≤ x.length then
      match ruleAtM g.rules key.rule with
      | none => none
      | some r => SequentialSpanRecompute.eval g x (query g x.length previous)
          (spans key.path) r.body (cursor key.path)
    else none
  else none

def rows (g : MGrammar) (x : List Char) : Nat → Array Res
  | 0 => ((keys g x.length).map (fun _ => (none : Res))).toArray
  | m + 1 => ((keys g x.length).map (compute g x (rows g x m))).toArray

theorem rows_correct (g : MGrammar) (x : List Char) : ∀ m,
    Correct g x (tblV g x .callByValueSeq m) (rows g x m) := by
  intro m
  induction m with
  | zero =>
    intro i r path hr hlen hb _ _
    simp [rows, SequentialRowAddress.keys_get_address hr hlen hb, tblV, valAt_nil]
  | succ m ih =>
    intro i r path hr hlen hb hvalid hp
    simp only [rows, List.getElem?_toArray, List.getElem?_map,
      SequentialRowAddress.keys_get_address hr hlen hb, Option.map_some]
    congr 1
    simp only [compute, if_pos hvalid, if_pos hp, hr]
    rw [valAt_tblV_succ hr _ hp]
    have he := SequentialSpanWindows.eval_eq (SequentialClock.table_descending g x m)
      (query_agree ih) (spans path) hvalid r.body (cursor path) hp
    simpa only [decode_spans] using he

def run (g : MGrammar) (x : List Char) (m : Nat) (E : SequentialSpanRecompute.Env)
    (e : MExp) (p : Nat) : Res :=
  SequentialSpanRecompute.eval g x (query g x.length (rows g x m)) E e p

theorem run_correct (g : MGrammar) (x : List Char) (m : Nat)
    (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E)
    (e : MExp) (p : Nat) (hp : p ≤ x.length) :
    run g x m E e p = evV g x .callByValueSeq (tblV g x .callByValueSeq m) (decodeEnv x E) e p :=
  SequentialSpanWindows.eval_eq (SequentialClock.table_descending g x m)
    (query_agree (rows_correct g x m)) E hE e p hp

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

theorem rows_size (g : MGrammar) (x : List Char) (m : Nat) :
    (rows g x m).size = (keys g x.length).length := by
  cases m <;> simp [rows]

theorem query_address_lt {g : MGrammar} {x : List Char} (m : Nat)
    {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r)
    {p q : Nat} {W : SequentialSpanRecompute.Env} (hw : Window p q W)
    (hp : p ≤ x.length) (hlen : r.arity = W.length) :
    address g x.length i (cuts (origin W q) W) < (rows g x m).size := by
  rw [window_origin hw, rows_size]
  exact SequentialRowAddress.address_lt hr (by simp [cuts]; omega)
    (SequentialTupleKeys.window_cuts_bounded hw hp)

theorem rows_size_le (g : MGrammar) (x : List Char) (m : Nat) :
    (rows g x m).size ≤ g.rules.length *
      (x.length + 1) ^ (SequentialStackPayload.arityBudget g + 1) := by
  rw [rows_size]
  exact SequentialTupleKeys.keys_length_le g x.length

end Shallot.MacroPeg.CBV.SequentialAddressedEvaluator
