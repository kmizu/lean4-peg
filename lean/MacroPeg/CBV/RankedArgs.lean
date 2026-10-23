import MacroPeg.CBV.CallFrames
import MacroPeg.CBV.EvalSpec

namespace Shallot.MacroPeg.CBV

/-- Stream argument results into their mixed-radix rank and final position. -/
def rankedArgs (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat) :
    List MExp → Nat → Nat → Option (Option (Nat × Nat))
  | [], rank, p => some (some (rank, p))
  | a :: args, rank, p =>
    match eval g x s row E a p with
    | none => none
    | some none => some none
    | some (some j) => rankedArgs g x s row E args
        (rank + spanId x.length p j * (subStrs x).length ^ args.length)
        (if s = .callByValueSeq then j else p)

theorem seqArgs_length {g : MGrammar} {x : List Char} {s : Strategy} {row E : List Nat} :
    ∀ (args : List MExp) (p : Nat) (ids : List Nat) (q : Nat),
    seqArgs g x s row E args p = some (some (ids, q)) → ids.length = args.length
  | [], p, ids, q, h => by
    have he := Option.some.inj (Option.some.inj h)
    have hi := congrArg Prod.fst he
    simpa using congrArg List.length hi.symm
  | a :: args, p, ids, q, h => by
    cases hv : eval g x s row E a p with
    | none => simp [seqArgs, hv] at h
    | some u => cases u with
      | none => simp [seqArgs, hv] at h
      | some j =>
        cases ht : seqArgs g x s row E args j with
        | none => simp [seqArgs, hv, ht] at h
        | some u => cases u with
          | none => simp [seqArgs, hv, ht] at h
          | some wq =>
            obtain ⟨js, q'⟩ := wq
            simp only [seqArgs, hv, ht, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp [seqArgs_length args j js q' ht]

theorem parArgs_length {g : MGrammar} {x : List Char} {s : Strategy} {row E : List Nat} :
    ∀ (args : List MExp) (p : Nat) (ids : List Nat),
    parArgs g x s row E args p = some (some ids) → ids.length = args.length
  | [], p, ids, h => by
    have hi := Option.some.inj (Option.some.inj h)
    simpa using congrArg List.length hi.symm
  | a :: args, p, ids, h => by
    cases hv : eval g x s row E a p with
    | none => simp [parArgs, hv] at h
    | some u => cases u with
      | none => simp [parArgs, hv] at h
      | some j =>
        cases ht : parArgs g x s row E args p with
        | none => simp [parArgs, hv, ht] at h
        | some u => cases u with
          | none => simp [parArgs, hv, ht] at h
          | some js =>
            simp only [parArgs, hv, ht, Option.some.injEq] at h
            subst ids
            simp [parArgs_length args p js ht]

/-- The streaming Seq algorithm computes the same values and position as the list-valued specification. -/
theorem rankedArgs_seq (g : MGrammar) (x : List Char) (row E : List Nat) :
    ∀ (args : List MExp) (rank p : Nat), rankedArgs g x .callByValueSeq row E args rank p =
      (seqArgs g x .callByValueSeq row E args p).map
        (Option.map (fun wq => (rank + wordRank (subStrs x).length wq.1, wq.2)))
  | [], rank, p => by simp [rankedArgs, seqArgs, wordRank]
  | a :: args, rank, p => by
    simp only [rankedArgs, seqArgs]
    cases he : eval g x .callByValueSeq row E a p with
    | none => rfl
    | some u => cases u with
      | none => rfl
      | some j =>
        simp only [if_true, rankedArgs_seq g x row E args]
        cases hs : seqArgs g x .callByValueSeq row E args j with
        | none => rfl
        | some u => cases u with
          | none => rfl
          | some wq => simp [wordRank, Nat.add_assoc, seqArgs_length args j wq.1 wq.2 hs]

/-- The streaming Par algorithm keeps the original position while accumulating the same argument tuple. -/
theorem rankedArgs_par (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (hs : s ≠ .callByValueSeq) :
    ∀ (args : List MExp) (rank p : Nat), rankedArgs g x s row E args rank p =
      (parArgs g x s row E args p).map
        (Option.map (fun ids => (rank + wordRank (subStrs x).length ids, p)))
  | [], rank, p => by simp [rankedArgs, parArgs, wordRank]
  | a :: args, rank, p => by
    simp only [rankedArgs, parArgs]
    cases he : eval g x s row E a p with
    | none => rfl
    | some u => cases u with
      | none => rfl
      | some j =>
        simp only [if_neg hs, rankedArgs_par g x s row E hs args]
        cases ht : parArgs g x s row E args p with
        | none => rfl
        | some u => cases u with
          | none => rfl
          | some ids => simp [wordRank, Nat.add_assoc, parArgs_length args p ids ht]

/-- Lookup with an already calculated scalar rank, in the same numeric table layout. -/
def rankLookup (g : MGrammar) (x : List Char) (row : List Nat) (i rank p : Nat) : Res :=
  resultDecode (row.getD (ruleOffset g x i + rank * (x.length + 1) + p) 0)

theorem rankLookup_pack {g : MGrammar} {x : List Char} {T : Nat → List (List Char) → Val}
    {i p : Nat} {rule : MRule} {ids : List Nat} (hr : ruleAtM g.rules i = some rule)
    (hw : ids ∈ words (List.range (subStrs x).length) rule.arity) (hp : p ≤ x.length) :
    rankLookup g x (pack g x T) i (wordRank (subStrs x).length ids) p =
      lookup g x (pack g x T) i ids p := by
  rw [lookup_pack_ids hr hw hp]
  exact pack_get_address hr hw hp

/-- The streaming call performs the same early exits and final lookup as numeric expression evaluation. -/
def rankedCall (g : MGrammar) (x : List Char) (s : Strategy) (row E : List Nat)
    (i : Nat) (args : List MExp) (p : Nat) : Res :=
  match rankedArgs g x s row E args 0 p with
  | none => none
  | some none => some none
  | some (some (rank, q)) => rankLookup g x row i rank q

theorem rankedCall_eval {g : MGrammar} {x : List Char} {s : Strategy}
    {T : Nat → List (List Char) → Val} {E : List Nat} (hT : OkTV x.length T)
    {i p : Nat} {rule : MRule} {args : List MExp}
    (hr : ruleAtM g.rules i = some rule) (ha : rule.arity = args.length) (hp : p ≤ x.length) :
    rankedCall g x s (pack g x T) E i args p = eval g x s (pack g x T) E (.call i args) p := by
  cases s with
  | callByValueSeq =>
    simp only [rankedCall, rankedArgs_seq, eval, hr, if_pos ha]
    cases hs : seqArgs g x .callByValueSeq (pack g x T) E args p with
    | none => rfl
    | some u => cases u with
      | none => rfl
      | some wq =>
        obtain ⟨ids, q⟩ := wq
        have hv := seqArgs_valid (pack_bound hT) args p hp ids q hs
        have hw : ids ∈ words (List.range (subStrs x).length) rule.arity :=
          (mem_words _ _ _).mpr ⟨hv.1.trans ha.symm, fun a ha => List.mem_range.mpr (hv.2.1 a ha)⟩
        simpa using rankLookup_pack hr hw hv.2.2
  | callByName | callByValuePar =>
    rw [rankedCall, rankedArgs_par _ _ _ _ _ (by decide)]
    simp only [eval, hr, if_pos ha]
    cases hs : parArgs g x _ (pack g x T) E args p with
    | none => rfl
    | some u => cases u with
      | none => rfl
      | some ids =>
        have hv := parArgs_valid args p hp ids hs
        have hw : ids ∈ words (List.range (subStrs x).length) rule.arity :=
          (mem_words _ _ _).mpr ⟨hv.1.trans ha.symm, fun a ha => List.mem_range.mpr (hv.2 a ha)⟩
        simpa using rankLookup_pack hr hw hp

end Shallot.MacroPeg.CBV
