import Complexity.Undec.Defs
import Complexity.Univ.Growth

/-!
# One-tape tables as string rewriting systems: the construction

A configuration of a one-tape table `T` in state `q` with head `p` on the tape `t` is the word
`⊢ t₀ … t_{p-1} ⟨q⟩ t_p … ⊣` (`cword`). Tape symbols are themselves, below the bound `bnd T`; the left end `⊢` is
`bnd T`, the right end `⊣` is `bnd T + 1` and the state `q` is `bnd T + 2 + q`. The bound exceeds every number of the
table, the input symbols and the states `0, 1, 2`.

Rules (`tmSRS`), for every state `q < bnd T` other than `0` and `1` and every symbol `a < bnd T` whose row exists:
- move right: `⟨q⟩ a → b ⟨q'⟩`; stay: `⟨q⟩ a → ⟨q'⟩ b`;
- move left: `c ⟨q⟩ a → ⟨q'⟩ c b` for every symbol `c`, and `⊢ ⟨q⟩ a → ⊢ ⟨q'⟩ b` at the left end;
- the end rule `⟨q⟩ ⊣ → ⟨q⟩ 0 ⊣` (a blank past the end);
- and erasing around the accepting state: `x ⟨0⟩ → ⟨0⟩`, `⟨0⟩ x → ⟨0⟩` for every symbol `x < bnd T + 2`.
-/

namespace Complexity.Undec

open Complexity

/-- The bound on tape symbols and states: above every number of the table and above `0, 1, 2`. -/
def bnd (T : TTable) : Nat := 3 + (Univ.encRows T.rows).sum

/-- The left end marker. -/
def lbS (T : TTable) : Nat := bnd T

/-- The right end marker. -/
def rbS (T : TTable) : Nat := bnd T + 1

/-- The symbol of the state `q`. -/
def stS (T : TTable) (q : Nat) : Nat := bnd T + 2 + q

/-- The symbol a row writes. -/
def wr (r : Row) : Nat := r.2.1.headD 0

/-- The move of a row. -/
def mv (r : Row) : Move := Move.ofCode (r.2.2.headD 0)

/-- The one-tape configuration in state `q`, head `p`, tape `t`. -/
def mk (q p : Nat) (t : List Nat) : FCfg := ⟨q, [p], [t]⟩

/-- The word of the state `q` between the left part `L` and the right part `R` of the tape. -/
def zw (T : TTable) (q : Nat) (L R : List Nat) : Word := lbS T :: (L ++ stS T q :: (R ++ [rbS T]))

/-- The word of a one-tape configuration. -/
def cword (T : TTable) (c : FCfg) : Word :=
  zw T c.state ((c.tapes.headD []).take (c.pos.headD 0)) ((c.tapes.headD []).drop (c.pos.headD 0))

/-- The rules of the state `q` reading `a` with the row `r`. -/
def cellRules (T : TTable) (q a : Nat) (r : Row) : SRS :=
  match mv r with
  | .R => [([stS T q, a], [wr r, stS T r.1])]
  | .S => [([stS T q, a], [stS T r.1, wr r])]
  | .L => ([lbS T, stS T q, a], [lbS T, stS T r.1, wr r]) ::
      (List.range (bnd T)).map fun c => ([c, stS T q, a], [stS T r.1, c, wr r])

/-- The rules of the state `q` reading `a`: none for halted states or missing rows. -/
def rulesQA (T : TTable) (q a : Nat) : SRS :=
  if q = 0 ∨ q = 1 then []
  else
    match T.rows[T.idx q [a]]? with
    | none => []
    | some r => cellRules T q a r

/-- The end rule of the state `q`. -/
def endRule (T : TTable) (q : Nat) : Word × Word := ([stS T q, rbS T], [stS T q, 0, rbS T])

/-- The end rules of the states that are not halted. -/
def endRules (T : TTable) : SRS :=
  (List.range (bnd T)).flatMap fun q => if q = 0 ∨ q = 1 then [] else [endRule T q]

/-- The erasing rules around the accepting state. -/
def eraseRules (T : TTable) : SRS :=
  (List.range (bnd T + 2)).flatMap fun x => [([x, stS T 0], [stS T 0]), ([stS T 0, x], [stS T 0])]

/-- The rewriting system of a one-tape table. -/
def tmSRS (T : TTable) : SRS :=
  ((List.range (bnd T)).flatMap fun q => (List.range (bnd T)).flatMap fun a => rulesQA T q a) ++
    endRules T ++ eraseRules T

/-- The start word: the initial configuration on `w`. -/
def tmStart (T : TTable) (w : List Bool) : Word := cword T (finit 1 w)

/-- The accepting word: the accepting state alone. -/
def tmAcc (T : TTable) : Word := [stS T 0]

/-- The number of symbols. -/
def tmSyms (T : TTable) : Nat := 2 * bnd T + 2

/-! ## The bound -/

/-- The new state of a row is below the bound. -/
theorem row_state_lt {T : TTable} {r : Row} (hr : r ∈ T.rows) : r.1 < bnd T := by
  have := (Univ.row_entry_le hr).1
  unfold bnd; omega

/-- The written symbol of a row is below the bound. -/
theorem row_wr_lt {T : TTable} {r : Row} (hr : r ∈ T.rows) : wr r < bnd T := by
  have h := (Univ.row_entry_le hr).2
  unfold wr
  cases hw : r.2.1 with
  | nil => unfold bnd; simp; omega
  | cons b ws =>
    have := h b (by rw [hw]; simp)
    unfold bnd; simp; omega

/-! ## The word of a configuration -/

/-- The word of a configuration whose head splits the tape into `L` and `R`. -/
theorem cword_mk (T : TTable) (q : Nat) (L R : List Nat) : cword T (mk q L.length (L ++ R)) = zw T q L R := by
  simp [cword, mk]

/-- Every configuration with its head on the tape or just past it splits the tape at the head. -/
theorem mk_split (q p : Nat) (t : List Nat) (hp : p ≤ t.length) :
    mk q p t = mk q (t.take p).length (t.take p ++ t.drop p) := by
  simp [mk, List.length_take, Nat.min_eq_left hp]

/-! ## Membership of rules -/

/-- A rule of a state and a symbol with a row is a rule of the system. -/
theorem cell_mem {T : TTable} {q a : Nat} {r : Row} {p : Word × Word} (hq : q < bnd T) (ha : a < bnd T)
    (h0 : q ≠ 0) (h1 : q ≠ 1) (hr : T.rows[T.idx q [a]]? = some r) (hp : p ∈ cellRules T q a r) :
    p ∈ tmSRS T := by
  simp only [tmSRS, List.mem_append, List.mem_flatMap, List.mem_range]
  refine Or.inl (Or.inl ⟨q, hq, a, ha, ?_⟩)
  simp only [rulesQA, h0, h1, or_self, if_false, hr]
  exact hp

/-- The end rule of a state that is not halted is a rule of the system. -/
theorem end_mem {T : TTable} {q : Nat} (hq : q < bnd T) (h0 : q ≠ 0) (h1 : q ≠ 1) : endRule T q ∈ tmSRS T := by
  simp only [tmSRS, List.mem_append, List.mem_flatMap, List.mem_range]
  refine Or.inl (Or.inr ?_)
  simp only [endRules, List.mem_flatMap, List.mem_range]
  exact ⟨q, hq, by simp [h0, h1]⟩

/-- Erasing to the left of the accepting state is a rule. -/
theorem eraseL_mem {T : TTable} {x : Nat} (hx : x < bnd T + 2) : ([x, stS T 0], [stS T 0]) ∈ tmSRS T := by
  simp only [tmSRS, List.mem_append, List.mem_flatMap, List.mem_range]
  refine Or.inr ?_
  simp only [eraseRules, List.mem_flatMap, List.mem_range]
  exact ⟨x, hx, by simp⟩

/-- Erasing to the right of the accepting state is a rule. -/
theorem eraseR_mem {T : TTable} {x : Nat} (hx : x < bnd T + 2) : ([stS T 0, x], [stS T 0]) ∈ tmSRS T := by
  simp only [tmSRS, List.mem_append, List.mem_flatMap, List.mem_range]
  refine Or.inr ?_
  simp only [eraseRules, List.mem_flatMap, List.mem_range]
  exact ⟨x, hx, by simp⟩

/-- The kinds of rules of the system. -/
theorem mem_tmSRS {T : TTable} {p : Word × Word} (hp : p ∈ tmSRS T) :
    (∃ q a r, q < bnd T ∧ a < bnd T ∧ q ≠ 0 ∧ q ≠ 1 ∧ T.rows[T.idx q [a]]? = some r ∧ p ∈ cellRules T q a r) ∨
      (∃ q, q < bnd T ∧ q ≠ 0 ∧ q ≠ 1 ∧ p = endRule T q) ∨
      (∃ x, x < bnd T + 2 ∧ (p = ([x, stS T 0], [stS T 0]) ∨ p = ([stS T 0, x], [stS T 0]))) := by
  simp only [tmSRS, List.mem_append, List.mem_flatMap, List.mem_range] at hp
  rcases hp with (⟨q, hq, a, ha, h⟩ | h) | h
  · left
    unfold rulesQA at h
    by_cases hq01 : q = 0 ∨ q = 1
    · simp [hq01] at h
    · simp only [hq01, if_false] at h
      have h0 : q ≠ 0 := fun e => hq01 (Or.inl e)
      have h1 : q ≠ 1 := fun e => hq01 (Or.inr e)
      split at h
      · simp at h
      · rename_i r hr
        exact ⟨q, a, r, hq, ha, h0, h1, hr, h⟩
  · right; left
    simp only [endRules, List.mem_flatMap, List.mem_range] at h
    obtain ⟨q, hq, h⟩ := h
    by_cases hq01 : q = 0 ∨ q = 1
    · simp [hq01] at h
    · simp only [hq01, if_false, List.mem_singleton] at h
      exact ⟨q, hq, fun e => hq01 (Or.inl e), fun e => hq01 (Or.inr e), h⟩
  · right; right
    simp only [eraseRules, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at h
    exact h

/-- The rules of a right move. -/
theorem cellRules_R {T : TTable} {q a : Nat} {r : Row} (h : mv r = .R) :
    cellRules T q a r = [([stS T q, a], [wr r, stS T r.1])] := by
  simp [cellRules, h]

/-- The rules of a stay. -/
theorem cellRules_S {T : TTable} {q a : Nat} {r : Row} (h : mv r = .S) :
    cellRules T q a r = [([stS T q, a], [stS T r.1, wr r])] := by
  simp [cellRules, h]

/-- The rules of a left move. -/
theorem cellRules_L {T : TTable} {q a : Nat} {r : Row} (h : mv r = .L) :
    cellRules T q a r = ([lbS T, stS T q, a], [lbS T, stS T r.1, wr r]) ::
      (List.range (bnd T)).map fun c => ([c, stS T q, a], [stS T r.1, c, wr r]) := by
  simp [cellRules, h]

end Complexity.Undec
