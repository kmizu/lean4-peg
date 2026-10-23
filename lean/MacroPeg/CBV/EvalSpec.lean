import MacroPeg.CBV.Eval

namespace Shallot.MacroPeg.CBV

/-- Decode an argument list while retaining unknown and failure as separate results. -/
def decodePar (x : List Char) (r : Option (Option (List Nat))) : Option (Option (List (List Char))) :=
  r.map (fun v => v.map (List.map (literalAt x)))

def decodeSeq (x : List Char) (r : Option (Option (List Nat × Nat))) : Option (Option (List (List Char) × Nat)) :=
  r.map (fun v => v.map (fun w => (w.1.map (literalAt x), w.2)))

mutual
  /-- The numeric evaluator computes exactly the established CBV round semantics. -/
  theorem eval_correct {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E : List Nat} (hT : OkTV x.length T) :
      ∀ (e : MExp) (p : Nat), p ≤ x.length →
      eval g x s (pack g x T) E e p = evV g x s T (E.map (literalAt x)) e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .param k, p, hp => by
      cases h : E[k]? <;> simp [eval, evV, List.getElem?_map, h] <;> rfl
    | .seq a b, p, hp => by
      simp only [eval, evV, ← eval_correct (E := E) hT a p hp]
      cases h : eval g x s (pack g x T) E a p with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some j => exact eval_correct hT b j (eval_ok (pack_bound hT) a p hp j h)
    | .alt a b, p, hp => by
      simp only [eval, evV, ← eval_correct (E := E) hT a p hp]
      cases h : eval g x s (pack g x T) E a p with
      | none => rfl
      | some r => cases r with
        | none => exact eval_correct hT b p hp
        | some j => rfl
    | .notP a, p, hp => by
      simp only [eval, evV, ← eval_correct (E := E) hT a p hp]
      rfl
    | .star a, p, hp => by
      simp only [eval, evV]
      exact evStar_congr p (fun q hq => eval_correct hT a q (by omega))
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp [eval, evV, hr]
      | some r =>
        by_cases ha : r.arity = args.length
        · cases s with
          | callByValueSeq =>
            simp only [eval, evV, hr, if_pos ha]
            rw [← seqArgs_correct (E := E) hT args p hp]
            cases hv : seqArgs g x .callByValueSeq (pack g x T) E args p with
            | none => rfl
            | some v => cases v with
              | none => rfl
              | some v =>
                obtain ⟨ids, q⟩ := v
                have hs := seqArgs_valid (pack_bound hT) args p hp ids q hv
                have hm : ids ∈ words (List.range (subStrs x).length) r.arity :=
                  (mem_words _ _ _).mpr ⟨hs.1.trans ha.symm, fun j hj => List.mem_range.mpr (hs.2.1 j hj)⟩
                exact lookup_pack_ids hr hm hs.2.2
          | callByName | callByValuePar =>
            simp only [eval, evV, hr, if_pos ha]
            rw [← parArgs_correct (E := E) hT args p hp]
            cases hv : parArgs g x _ (pack g x T) E args p with
            | none => rfl
            | some v => cases v with
              | none => rfl
              | some ids =>
                have hs := parArgs_valid args p hp ids hv
                have hm : ids ∈ words (List.range (subStrs x).length) r.arity :=
                  (mem_words _ _ _).mpr ⟨hs.1.trans ha.symm, fun j hj => List.mem_range.mpr (hs.2 j hj)⟩
                exact lookup_pack_ids hr hm hp
        · simp [eval, evV, hr, ha]

  theorem parArgs_correct {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E : List Nat} (hT : OkTV x.length T) :
      ∀ (args : List MExp) (p : Nat), p ≤ x.length →
      decodePar x (parArgs g x s (pack g x T) E args p) = evParArgs g x s T (E.map (literalAt x)) args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      simp only [parArgs, evParArgs, ← eval_correct (E := E) hT a p hp]
      cases h : eval g x s (pack g x T) E a p with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some j =>
          dsimp only
          rw [← parArgs_correct (E := E) hT args p hp]
          cases hv : parArgs g x s (pack g x T) E args p with
          | none => rfl
          | some v => cases v with
            | none => rfl
            | some ids => simp [decodePar, literalAt_spanId hp]

  theorem seqArgs_correct {g : MGrammar} {x : List Char} {s : Strategy}
      {T : Nat → List (List Char) → Val} {E : List Nat} (hT : OkTV x.length T) :
      ∀ (args : List MExp) (p : Nat), p ≤ x.length →
      decodeSeq x (seqArgs g x s (pack g x T) E args p) = evSeqArgs g x s T (E.map (literalAt x)) args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      simp only [seqArgs, evSeqArgs, ← eval_correct (E := E) hT a p hp]
      cases h : eval g x s (pack g x T) E a p with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some j =>
          dsimp only
          rw [← seqArgs_correct (E := E) hT args j (eval_ok (pack_bound hT) a p hp j h)]
          cases hv : seqArgs g x s (pack g x T) E args j with
          | none => rfl
          | some v => cases v with
            | none => rfl
            | some v => obtain ⟨ids, q⟩ := v; simp [decodeSeq, literalAt_spanId hp]
end

end Shallot.MacroPeg.CBV
