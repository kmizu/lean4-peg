import MacroPeg.CBV.RenamedCopy

/-! A FIFO specification for the candidate and its reversal. Each input symbol
requests at most one queue insertion or removal. Lists specify queue contents;
this file does not claim constant-time implementation of List.append, nor does
it supply a multitape-TM or Seq compiler. -/
namespace Shallot.MacroPeg.CBV.RenamedCopyFIFO

open RenamedCopy (lower upper Language)

inductive State where
  | left (queue : List Bool)
  | right (queue : List Bool)
  | reject
  deriving DecidableEq, Repr

def step : State → Char → State
  | .left q, c => if c = 'a' then .left (q ++ [false]) else
      if c = 'b' then .left (q ++ [true]) else
      if c = '#' then .right q else .reject
  | .right [], _ => .reject
  | .right (b :: q), c => if c = upper b then .right q else .reject
  | .reject, _ => .reject

def runFrom (q : State) (x : List Char) : State := x.foldl step q
def accepts (x : List Char) : Prop := runFrom (.left []) x = .right []

private theorem run_append (q : State) (a b : List Char) :
    runFrom q (a ++ b) = runFrom (runFrom q a) b := List.foldl_append

private def Represents (x : List Char) : State → Prop
  | .left w => x = w.map lower
  | .right remaining => ∃ whole done : List Bool,
      whole = done ++ remaining ∧ x = whole.map lower ++ '#' :: done.map upper
  | .reject => True

private theorem step_represents (x : List Char) (q : State) (c : Char)
    (h : Represents x q) : Represents (x ++ [c]) (step q c) := by
  cases q with
  | reject => trivial
  | left w =>
    change x = w.map lower at h
    subst x
    by_cases ha : c = 'a'
    · subst c; simp [step, Represents, lower, List.map_append]
    · by_cases hb : c = 'b'
      · subst c; simp [step, Represents, lower, List.map_append]
      · by_cases hh : c = '#'
        · subst c
          simp only [step, if_neg ha, if_neg hb, if_true, Represents]
          exact ⟨w, [], by simp, by simp⟩
        · simp [step, ha, hb, hh, Represents]
  | right remaining =>
    obtain ⟨whole, done, hw, hx⟩ := h
    cases remaining with
    | nil => trivial
    | cons b remaining =>
      by_cases hc : c = upper b
      · simp only [step, if_pos hc, Represents]
        refine ⟨whole, done ++ [b], ?_, ?_⟩
        · simpa [List.append_assoc] using hw
        · simp only [hx, hc, List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append]
      · simp [step, hc, Represents]

private theorem run_represents (x : List Char) : Represents x (runFrom (.left []) x) := by
  have aux : ∀ input pre0 q, Represents pre0 q →
      Represents (pre0 ++ input) (runFrom q input) := by
    intro input
    induction input with
    | nil => intro pre0 q h; simpa [runFrom] using h
    | cons c input ih =>
      intro pre0 q h
      have ht := ih (pre0 ++ [c]) (step q c) (step_represents pre0 q c h)
      simpa [runFrom, List.append_assoc] using ht
  simpa using aux x [] (.left []) rfl

private theorem run_lower (w acc : List Bool) :
    runFrom (.left acc) (w.map lower) = .left (acc ++ w) := by
  induction w generalizing acc with
  | nil => simp [runFrom]
  | cons b w ih =>
    cases b with
    | false => simpa [runFrom, lower, step, List.append_assoc] using ih (acc ++ [false])
    | true => simpa [runFrom, lower, step, List.append_assoc] using ih (acc ++ [true])

private theorem run_upper (w : List Bool) :
    runFrom (.right w) (w.map upper) = .right [] := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simpa [runFrom, upper, step] using ih

/-- All original character inputs, including malformed inputs and empty
fields. This is a queue-model theorem, not yet a Seq-language theorem. -/
theorem accepts_iff (x : List Char) : accepts x ↔ Language x := by
  constructor
  · intro h
    have hs := run_represents x
    rw [h] at hs
    obtain ⟨whole, done, hw, hx⟩ := hs
    have he : whole = done := by simpa using hw
    exact ⟨whole, by simpa [← he] using hx⟩
  · rintro ⟨w, rfl⟩
    unfold accepts
    rw [run_append, run_lower]
    simpa only [List.nil_append, runFrom, List.foldl_cons, step,
      Char.reduceEq, if_false, if_true] using run_upper w

def swap (c : Char) : Char :=
  if c = 'a' then 'A' else if c = 'b' then 'B' else
  if c = 'A' then 'a' else if c = 'B' then 'b' else c

private theorem swap_swap (c : Char) : swap (swap c) = c := by
  by_cases ha : c = 'a'
  · subst c; decide
  · by_cases hb : c = 'b'
    · subst c; decide
    · by_cases hA : c = 'A'
      · subst c; decide
      · by_cases hB : c = 'B'
        · subst c; decide
        · simp [swap, ha, hb, hA, hB]

private theorem swap_lower (b : Bool) : swap (lower b) = upper b := by
  cases b <;> decide

private theorem swap_upper (b : Bool) : swap (upper b) = lower b := by
  cases b <;> decide

private theorem swap_hash : swap '#' = '#' := by decide

theorem reversal_iff (x : List Char) : Language x.reverse ↔ Language (x.map swap) := by
  constructor
  · rintro ⟨w, hw⟩
    have hx := congrArg List.reverse hw
    simp only [List.reverse_reverse, List.reverse_append, List.reverse_cons,
      List.append_assoc, List.singleton_append] at hx
    refine ⟨w.reverse, ?_⟩
    rw [hx]
    simp [List.map_append, List.map_map, Function.comp_def, swap_upper, swap_lower, swap_hash]
  · rintro ⟨w, hw⟩
    have hx := congrArg (List.map swap) hw
    simp only [List.map_map, Function.comp_def, swap_swap,
      List.map_append, List.map_cons, swap_hash] at hx
    have hx' : x = w.map upper ++ '#' :: w.map lower := by
      simpa [List.map_map, Function.comp_def, swap_upper, swap_lower] using hx
    refine ⟨w.reverse, ?_⟩
    rw [hx']
    simp [List.reverse_append, List.reverse_cons, List.map_reverse, List.append_assoc]

def reverseStep (q : State) (c : Char) : State := step q (swap c)
def acceptsReverse (x : List Char) : Prop := x.foldl reverseStep (.left []) = .right []

/-- The reversed language uses the same FIFO control with a finite input
letter test changed in the transition; no extra input symbols are supplied. -/
theorem acceptsReverse_iff (x : List Char) : acceptsReverse x ↔ Language x.reverse := by
  have he : acceptsReverse x ↔ accepts (x.map swap) := by
    simp only [acceptsReverse, accepts, runFrom, List.foldl_map]
    rfl
  exact he.trans ((accepts_iff _).trans (reversal_iff x).symm)

end Shallot.MacroPeg.CBV.RenamedCopyFIFO
