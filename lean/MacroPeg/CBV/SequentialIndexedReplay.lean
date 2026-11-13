import MacroPeg.CBV.RightmostCaptureIndex

/-! Parameter replay selects its source through the shared whole-input index.
Every selected source is inside the current suffix; dead values fail before
matching. This is a numeric interpreter, not an ordinary Seq grammar compiler. -/
namespace Shallot.MacroPeg.CBV.SequentialIndexedReplay

open Shallot (beqChar leChar stripPrefix?)
abbrev Env := SequentialSpanRecompute.Env

open SequentialSpanRecompute (Query ValidEnv decodeEnv decodeArgs ArgsSpec
  valid_capture decode_capture matchSpan_eq)

mutual
  def eval (g : MGrammar) (x : List Char) (A : Array (Option FutureSpanRepresentatives.Span)) (Q : Query) (E : Env) : MExp → Nat → Res
    | .eps, p => some (some p)
    | .any, p =>
      match sfx x p with
      | _ :: rest => some (some rest.length)
      | [] => some none
    | .chr c, p =>
      match sfx x p with
      | d :: rest => if beqChar c d then some (some rest.length) else some none
      | [] => some none
    | .range lo hi, p =>
      match sfx x p with
      | d :: rest => if leChar lo d && leChar d hi then some (some rest.length) else some none
      | [] => some none
    | .lit w, p =>
      match stripPrefix? w (sfx x p) with
      | some rest => some (some rest.length)
      | none => some none
    | .param k, p =>
      match E[k]? with
      | some (a, b) => RightmostCaptureIndex.indexedMatch x A (a,b) p
      | none => some none
    | .call i args, p =>
      match ruleAtM g.rules i with
      | some rule =>
        if rule.arity = args.length then
          match evalArgs g x A Q E args p with
          | some (some (W, q)) => Q i W q
          | some none => some none
          | none => none
        else some none
      | none => some none
    | .seq a b, p =>
      match eval g x A Q E a p with
      | some (some q) => eval g x A Q E b q
      | result => result
    | .alt a b, p =>
      match eval g x A Q E a p with
      | some none => eval g x A Q E b p
      | result => result
    | .star a, p => evStar (fun q => eval g x A Q E a q) p
    | .notP a, p =>
      match eval g x A Q E a p with
      | some (some _) => some none
      | some none => some (some p)
      | none => none
    | .dbg _, p | .lam _ _, p => some (some p)
    | .callParam _ _, _ => some none
    | .invoke _ _ _, _ => none

  def evalArgs (g : MGrammar) (x : List Char) (A : Array (Option FutureSpanRepresentatives.Span)) (Q : Query) (E : Env) :
      List MExp → Nat → Option (Option (Env × Nat))
    | [], p => some (some ([], p))
    | a :: args, p =>
      match eval g x A Q E a p with
      | some (some q) =>
        match evalArgs g x A Q E args q with
        | some (some (W, r)) => some (some ((p, min q p) :: W, r))
        | result => result
      | some none => some none
      | none => none
end

mutual
  theorem eval_eq {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W, ValidEnv x.length W → ∀ p, p ≤ x.length →
        Q i W p = valAt (T i (decodeEnv x W)) p) (E : Env) (hE : ValidEnv x.length E) :
      ∀ e p, p ≤ x.length → eval g x (RightmostCaptureIndex.table x) Q E e p = evV g x .callByValueSeq T (decodeEnv x E) e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _ | .invoke _ _ _, _, _ => rfl
    | .param k, p, hp => by
      cases hs : E[k]? with
      | none => simp [eval, evV, decodeEnv, hs]
      | some span =>
        obtain ⟨a, b⟩ := span
        have ha := (hE (a, b) (List.mem_of_getElem? hs)).2
        simp only [eval, evV, decodeEnv, List.getElem?_map, hs, Option.map_some]
        rw [RightmostCaptureIndex.indexedMatch_eq (hE (a,b) (List.mem_of_getElem? hs)) hp,
          matchSpan_eq x a b p ha]
        cases stripPrefix? (pre x a b) (sfx x p) <;> rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [eval, evV, hr]
      | some rule =>
        by_cases ha : rule.arity = args.length
        · simp only [eval, evV, hr, if_pos ha]
          have hargs := args_spec (g := g) hT hQ E hE args p hp
          rw [← hargs.1]
          cases hv : evalArgs g x (RightmostCaptureIndex.table x) Q E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W, q⟩ := Wq
              obtain ⟨hW, hq⟩ := hargs.2 W q hv
              exact hQ i W hW q hq
        · simp only [eval, evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q => exact eval_eq hT hQ E hE b q (evV_ok hT a p hp q hv)
    | .alt a b, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none => rfl
      | some result =>
        cases result with
        | none => exact eval_eq hT hQ E hE b p hp
        | some q => rfl
    | .notP a, p, hp => by
      simp only [eval, evV]
      rw [eval_eq hT hQ E hE a p hp]
      rfl
    | .star a, p, hp => by
      simp only [eval, evV_star]
      exact evStar_congr p (fun q hq => eval_eq hT hQ E hE a q (by omega))

  theorem args_spec {g : MGrammar} {x : List Char} {Q : Query} {T : SequentialClock.Table}
      (hT : OkTV x.length T)
      (hQ : ∀ i W, ValidEnv x.length W → ∀ p, p ≤ x.length →
        Q i W p = valAt (T i (decodeEnv x W)) p) (E : Env) (hE : ValidEnv x.length E) :
      ∀ args p, p ≤ x.length → ArgsSpec x (evalArgs g x (RightmostCaptureIndex.table x) Q E args p)
        (evSeqArgs g x .callByValueSeq T (decodeEnv x E) args p)
    | [], p, hp => by
      refine ⟨rfl, ?_⟩
      intro W q h
      cases h
      refine ⟨?_, hp⟩
      intro span hm
      cases hm
    | a :: args, p, hp => by
      have ha := eval_eq (g := g) hT hQ E hE a p hp
      cases hv : evV g x .callByValueSeq T (decodeEnv x E) a p with
      | none =>
        refine ⟨by simp [decodeArgs, evalArgs, ha, hv, evSeqArgs], ?_⟩
        intro W q h; simp [evalArgs, ha, hv] at h
      | some result =>
        cases result with
        | none =>
          refine ⟨by simp [decodeArgs, evalArgs, ha, hv, evSeqArgs], ?_⟩
          intro W q h; simp [evalArgs, ha, hv] at h
        | some j =>
          have hj := evV_ok hT a p hp j hv
          have ht := args_spec (g := g) hT hQ E hE args j hj
          refine ⟨?_, ?_⟩
          · simp only [evalArgs, ha, hv, evSeqArgs]
            rw [← ht.1]
            cases hr : evalArgs g x (RightmostCaptureIndex.table x) Q E args j with
            | none => rfl
            | some result =>
              cases result with
              | none => rfl
              | some Wq =>
                obtain ⟨W, q⟩ := Wq
                simp [decodeArgs, decodeEnv, decode_capture]
          · intro W q h
            simp only [evalArgs, ha, hv] at h
            cases hr : evalArgs g x (RightmostCaptureIndex.table x) Q E args j with
            | none => rw [hr] at h; cases h
            | some result =>
              cases result with
              | none => rw [hr] at h; cases h
              | some Vr =>
                obtain ⟨V, r⟩ := Vr
                rw [hr] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨hV, hq⟩ := ht.2 V r hr
                exact ⟨valid_capture hp hV, hq⟩
end

end Shallot.MacroPeg.CBV.SequentialIndexedReplay
