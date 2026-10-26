import MacroPeg.CBV.SequentialCaptureRegions
import MacroPeg.CBV.SequentialClock

namespace Shallot.MacroPeg.CBV.SequentialTupleKeys

open SequentialCaptureRegions (Window)
open SequentialClock (Descending)

def cuts (p : Nat) (W : List (Nat × Nat)) : List Nat := p :: W.map Prod.snd

def values (x : List Char) : List Nat → List (List Char)
  | a :: b :: rest => pre x a b :: values x (b :: rest)
  | _ => []

def cursor (path : List Nat) : Nat := path.getLastD 0

theorem window_values {p q : Nat} {W : List (Nat × Nat)} (h : Window p q W)
    (x : List Char) : values x (cuts p W) = SequentialSpanRecompute.decodeEnv x W := by
  induction h with
  | nil => rfl
  | cons hj ht ih =>
    simpa only [cuts, values, SequentialSpanRecompute.decodeEnv, List.map_cons]
      using congrArg (List.cons _) ih

theorem window_cursor {p q : Nat} {W : List (Nat × Nat)} (h : Window p q W) :
    cursor (cuts p W) = q := by
  induction h with
  | nil => rfl
  | cons hj ht ih => simpa [cuts, cursor] using ih

theorem window_cuts_bounded {p q n : Nat} {W : List (Nat × Nat)}
    (h : Window p q W) (hp : p ≤ n) : ∀ j ∈ cuts p W, j ≤ n := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj
  · exact hp
  · obtain ⟨span, hs, rfl⟩ := List.mem_map.mp hj
    have hb := h.valid hp span hs
    exact Nat.le_trans hb.1 hb.2

/-- The real semantic argument evaluator creates one adjacent partition,
under arbitrary incoming environments and arbitrary descending rule tables. -/
theorem arguments_window {g : MGrammar} {x : List Char} {T : SequentialClock.Table}
    (hT : Descending T) (E : List (List Char)) :
    ∀ args p W q, evSeqArgs g x .callByValueSeq T E args p = some (some (W,q)) →
      ∃ spans, Window p q spans ∧ SequentialSpanRecompute.decodeEnv x spans = W
  | [], p, W, q, h => by cases h; exact ⟨[], .nil p, rfl⟩
  | a :: args, p, W, q, h => by
    cases ha : evV g x .callByValueSeq T E a p with
    | none => simp [evSeqArgs, ha] at h
    | some result =>
      cases result with
      | none => simp [evSeqArgs, ha] at h
      | some j =>
        have hj := SequentialClock.expression_descending hT E a p j ha
        cases ht : evSeqArgs g x .callByValueSeq T E args j with
        | none => simp [evSeqArgs, ha, ht] at h
        | some result =>
          cases result with
          | none => simp [evSeqArgs, ha, ht] at h
          | some Wq =>
            obtain ⟨V, r⟩ := Wq
            simp only [evSeqArgs, ha, ht, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨spans, hs, hv⟩ := arguments_window hT E args j V r ht
            exact ⟨(p,j) :: spans, .cons hj hs, congrArg (List.cons (pre x p j)) hv⟩

def paths (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range (n + 1)).flatMap (fun j => (paths n k).map (j :: ·))

theorem mem_paths (n k : Nat) (path : List Nat) :
    path ∈ paths n k ↔ path.length = k ∧ ∀ j ∈ path, j ≤ n := by
  induction k generalizing path with
  | zero => cases path <;> simp [paths]
  | succ k ih =>
    cases path with
    | nil => simp [paths]
    | cons j path =>
      simp only [paths, List.mem_flatMap, List.mem_map, List.cons.injEq, ih,
        List.length_cons, Nat.succ.injEq, List.mem_range]
      constructor
      · rintro ⟨i, hi, tail, ⟨hlen, hb⟩, rfl, rfl⟩
        exact ⟨hlen, fun c hc => (List.mem_cons.mp hc).elim (fun he => by subst c; omega) (hb c)⟩
      · rintro ⟨hlen, hb⟩
        exact ⟨j, by have := hb j (by simp); omega, path,
          ⟨hlen, fun c hc => hb c (List.mem_cons_of_mem j hc)⟩, rfl, rfl⟩

private theorem uniform_flatMap_length {α β : Type} (xs : List α) (f : α → List β)
    (k : Nat) (h : ∀ a ∈ xs, (f a).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [h a (by simp), ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    omega

theorem paths_length (n k : Nat) : (paths n k).length = (n + 1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [paths, uniform_flatMap_length _ _ ((n + 1) ^ k) (by intro j hj; simp [ih]), List.length_range]
    exact Nat.mul_comm _ _ |>.trans (Nat.pow_succ _ _).symm

structure Key where
  rule : Nat
  path : List Nat
  deriving DecidableEq, Repr

def keys (g : MGrammar) (n : Nat) : List Key :=
  (List.finRange g.rules.length).flatMap (fun i =>
    (paths n (g.rules[i].arity + 1)).map (fun path => ⟨i.val, path⟩))

theorem keys_length (g : MGrammar) (n : Nat) :
    (keys g n).length = ((List.finRange g.rules.length).map
      (fun i => (n + 1) ^ (g.rules[i].arity + 1))).sum := by
  simp [keys, List.length_flatMap, paths_length]

theorem keys_length_le (g : MGrammar) (n : Nat) :
    (keys g n).length ≤ g.rules.length *
      (n + 1) ^ (SequentialStackPayload.arityBudget g + 1) := by
  rw [keys_length]
  have aux (is : List (Fin g.rules.length)) :
      (is.map (fun i => (n + 1) ^ (g.rules[i].arity + 1))).sum ≤
        is.length * (n + 1) ^ (SequentialStackPayload.arityBudget g + 1) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      have ha := SequentialStackPayload.arityBudget_spec g g.rules[i] (List.getElem_mem i.isLt)
      have hb := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (Nat.add_le_add_right ha 1)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  simpa using aux (List.finRange g.rules.length)

theorem covered {g : MGrammar} {x : List Char} {i : Nat} {r : MRule}
    (hr : ruleAtM g.rules i = some r) {p q : Nat} {W : List (Nat × Nat)}
    (hw : Window p q W) (hp : p ≤ x.length)
    (hlen : (SequentialSpanRecompute.decodeEnv x W).length = r.arity) :
    ∃ key ∈ keys g x.length,
      key.rule = i ∧ values x key.path = SequentialSpanRecompute.decodeEnv x W ∧
      cursor key.path = q := by
  let idx : Fin g.rules.length := ⟨i, ruleAtM_lt hr⟩
  have he : g.rules[idx] = r := by
    have hh : g.rules[i]? = some r := by simpa only [ruleAtM_eq_getElem?] using hr
    simp only [List.getElem?_eq_getElem (ruleAtM_lt hr), Option.some.injEq] at hh
    exact hh
  have hpath : cuts p W ∈ paths x.length (g.rules[idx].arity + 1) := by
    apply (mem_paths _ _ _).mpr
    refine ⟨?_, window_cuts_bounded hw hp⟩
    simpa [cuts, SequentialSpanRecompute.decodeEnv, he] using hlen
  refine ⟨⟨i, cuts p W⟩, ?_, rfl, window_values hw x, window_cursor hw⟩
  exact List.mem_flatMap.mpr ⟨idx, List.mem_finRange _, List.mem_map.mpr ⟨_, hpath, rfl⟩⟩

end Shallot.MacroPeg.CBV.SequentialTupleKeys
