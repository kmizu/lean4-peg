import MacroPeg.CBV.SequentialTupleKeys

namespace Shallot.MacroPeg.CBV.SequentialSpanWindows

open SequentialSpanRecompute (Query ValidEnv decodeEnv decodeArgs matchSpan_eq)
open SequentialCaptureRegions (Window)

/-- Only real adjacent argument tuples must be implemented by the query.
Incoming environments may be arbitrary valid spans. -/
def Agree (g : MGrammar) (x : List Char) (Q : Query) (T : SequentialClock.Table) : Prop :=
  ∀ i r p q W, ruleAtM g.rules i = some r → r.arity = W.length →
    p ≤ x.length → Window p q W → Q i W q = valAt (T i (decodeEnv x W)) q

mutual
  theorem eval_eq {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : SequentialClock.Descending T)
      (hQ : Agree g x Q T) (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E) :
      ∀ e p, p ≤ x.length → SequentialSpanRecompute.eval g x Q E e p = evV g x .callByValueSeq T (decodeEnv x E) e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .param k, p, _ => by
      cases hs : E[k]? with
      | none => simp [SequentialSpanRecompute.eval, evV, decodeEnv, hs]
      | some span =>
        obtain ⟨a, b⟩ := span
        have ha := (hE (a, b) (List.mem_of_getElem? hs)).2
        simp only [SequentialSpanRecompute.eval, evV, decodeEnv, List.getElem?_map, hs, Option.map_some]
        rw [matchSpan_eq x a b p ha]
        cases stripPrefix? (pre x a b) (sfx x p) <;> rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [SequentialSpanRecompute.eval, evV, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [SequentialSpanRecompute.eval, evV, hr, if_pos ha]
          have hargs := args_spec (g := g) hT hQ E hE args p hp
          rw [← hargs.1]
          cases hv : SequentialSpanRecompute.evalArgs g x Q E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              obtain ⟨hW, hlen⟩ := hargs.2 W q hv
              exact hQ i rule p q W hr (ha.trans hlen.symm) hp hW
        · simp only [SequentialSpanRecompute.eval, evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      simp only [SequentialSpanRecompute.eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q => exact eval_eq hT hQ E hE b q (Nat.le_trans (SequentialClock.expression_descending hT _ a p q hv) hp)
    | .alt a b, p, hp => by
      simp only [SequentialSpanRecompute.eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => exact eval_eq hT hQ E hE b p hp
        | some q => rfl
    | .notP a, p, hp => by
      simp only [SequentialSpanRecompute.eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      rfl
    | .star a, p, hp => by
      simp only [SequentialSpanRecompute.eval, evV_star]
      exact evStar_congr p (fun q hq => eval_eq hT hQ E hE a q (by omega))

  theorem args_spec {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : SequentialClock.Descending T)
      (hQ : Agree g x Q T) (E : SequentialSpanRecompute.Env) (hE : ValidEnv x.length E) :
      ∀ args p, p ≤ x.length →
        decodeArgs x (SequentialSpanRecompute.evalArgs g x Q E args p) =
          evSeqArgs g x .callByValueSeq T (decodeEnv x E) args p ∧
        ∀ W q, SequentialSpanRecompute.evalArgs g x Q E args p = some (some (W,q)) →
          Window p q W ∧ W.length = args.length
    | [], p, hp => by
      refine ⟨rfl, ?_⟩
      intro W q h
      cases h
      exact ⟨.nil p, rfl⟩
    | a :: args, p, hp => by
      have ha := eval_eq (g := g) hT hQ E hE a p hp
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none =>
        refine ⟨by simp [decodeArgs, SequentialSpanRecompute.evalArgs, ha, hv, evSeqArgs], ?_⟩
        intro W q h; simp [SequentialSpanRecompute.evalArgs, ha, hv] at h
      | some result =>
        cases result with
        | none =>
          refine ⟨by simp [decodeArgs, SequentialSpanRecompute.evalArgs, ha, hv, evSeqArgs], ?_⟩
          intro W q h; simp [SequentialSpanRecompute.evalArgs, ha, hv] at h
        | some j =>
          have hjp := SequentialClock.expression_descending hT _ a p j hv
          have hj := Nat.le_trans hjp hp
          have ht := args_spec (g := g) hT hQ E hE args j hj
          refine ⟨?_, ?_⟩
          · simp only [SequentialSpanRecompute.evalArgs, ha, hv, evSeqArgs]
            rw [← ht.1]
            cases hr : SequentialSpanRecompute.evalArgs g x Q E args j with
            | none => rfl
            | some result =>
              cases result with
              | none => rfl
              | some Wq =>
                obtain ⟨W, q⟩ := Wq
                simp [decodeArgs, decodeEnv, SequentialSpanRecompute.decode_capture]
          · intro W q h
            simp only [SequentialSpanRecompute.evalArgs, ha, hv] at h
            cases hr : SequentialSpanRecompute.evalArgs g x Q E args j with
            | none => rw [hr] at h; cases h
            | some result =>
              cases result with
              | none => rw [hr] at h; cases h
              | some Vr =>
                obtain ⟨V, r⟩ := Vr
                rw [hr] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hV, hlen⟩ := ht.2 V r hr
                rw [Nat.min_eq_left hjp]
                exact ⟨.cons hjp hV, congrArg Nat.succ hlen⟩
end

end Shallot.MacroPeg.CBV.SequentialSpanWindows
