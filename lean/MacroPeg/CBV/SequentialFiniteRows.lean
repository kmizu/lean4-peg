import MacroPeg.CBV.SequentialTupleKeys

namespace Shallot.MacroPeg.CBV.SequentialFiniteRows

open SequentialClock (Table Descending)
open SequentialCaptureRegions (Window)
open SequentialTupleKeys (Key keys values cursor)

def Adjacent (x : List Char) (W : List (List Char)) (q : Nat) : Prop :=
  ∃ p spans, p ≤ x.length ∧ Window p q spans ∧ SequentialSpanRecompute.decodeEnv x spans = W

def Agree (g : MGrammar) (x : List Char) (T U : Table) : Prop :=
  ∀ i r W q, ruleAtM g.rules i = some r → r.arity = W.length → Adjacent x W q →
    valAt (T i W) q = valAt (U i W) q

mutual
  theorem expression_agree {g : MGrammar} {x : List Char} {T U : Table}
      (hT : Descending T) (h : Agree g x T U) (E : List (List Char)) :
      ∀ e p, p ≤ x.length →
        evV g x .callByValueSeq T E e p = evV g x .callByValueSeq U E e p
    | .eps, _, _ | .any, _, _ | .chr _, _, _ | .range _ _, _, _ | .lit _, _, _
    | .param _, _, _ | .dbg _, _, _ | .lam _ _, _, _ | .callParam _ _, _, _
    | .invoke _ _ _, _, _ => rfl
    | .call i args, p, hp => by
      cases hr : ruleAtM g.rules i with
      | none => simp only [evV, hr]
      | some r =>
        by_cases ha : r.arity = args.length
        · rw [evV_call_seq hr ha, evV_call_seq hr ha, ← arguments_agree hT h E args p hp]
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => rfl
          | some result =>
            cases result with
            | none => rfl
            | some Wq =>
              obtain ⟨W,q⟩ := Wq
              obtain ⟨spans, hw, hd⟩ := SequentialTupleKeys.arguments_window hT E args p W q hv
              exact h i r W q hr (ha.trans (evSeq_length args p W q hv).symm) ⟨p,spans,hp,hw,hd⟩
        · simp only [evV, hr, if_neg ha]
    | .seq a b, p, hp => by
      have he := expression_agree hT h E a p hp
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_seq_none hv, evV_seq_none (he.symm.trans hv)]
      | some result =>
        cases result with
        | none => rw [evV_seq_fail hv, evV_seq_fail (he.symm.trans hv)]
        | some q =>
          rw [evV_seq_ok hv, evV_seq_ok (he.symm.trans hv)]
          exact expression_agree hT h E b q
            (Nat.le_trans (SequentialClock.expression_descending hT E a p q hv) hp)
    | .alt a b, p, hp => by
      have he := expression_agree hT h E a p hp
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rw [evV_alt_none hv, evV_alt_none (he.symm.trans hv)]
      | some result =>
        cases result with
        | none =>
          rw [evV_alt_fail hv, evV_alt_fail (he.symm.trans hv)]
          exact expression_agree hT h E b p hp
        | some q => rw [evV_alt_ok hv, evV_alt_ok (he.symm.trans hv)]
    | .notP a, p, hp => by
      simp only [evV]
      rw [expression_agree hT h E a p hp]
    | .star a, p, hp => by
      rw [evV_star, evV_star]
      exact evStar_congr p (fun q hq => expression_agree hT h E a q (by omega))

  theorem arguments_agree {g : MGrammar} {x : List Char} {T U : Table}
      (hT : Descending T) (h : Agree g x T U) (E : List (List Char)) :
      ∀ args p, p ≤ x.length →
        evSeqArgs g x .callByValueSeq T E args p = evSeqArgs g x .callByValueSeq U E args p
    | [], _, _ => rfl
    | a :: args, p, hp => by
      have he := expression_agree hT h E a p hp
      simp only [evSeqArgs]
      rw [← he]
      cases hv : evV g x .callByValueSeq T E a p with
      | none => rfl
      | some result =>
        cases result with
        | none => rfl
        | some q =>
          simp only []
          rw [arguments_agree hT h E args q
            (Nat.le_trans (SequentialClock.expression_descending hT E a p q hv) hp)]
end

structure Cell where
  key : Key
  result : Res
  deriving Repr

def keyMatches (x : List Char) (i : Nat) (W : List (List Char)) (p : Nat) (c : Cell) : Bool :=
  decide (c.key.rule = i ∧ values x c.key.path = W ∧ cursor c.key.path = p)

def lookup (x : List Char) (cells : List Cell) (i : Nat) (W : List (List Char)) (p : Nat) : Res :=
  ((cells.find? (keyMatches x i W p)).map Cell.result).getD none

def table (x : List Char) (cells : List Cell) : Table :=
  fun i W => (List.range (x.length + 1)).map (lookup x cells i W)

def Correct (x : List Char) (T : Table) (cells : List Cell) : Prop :=
  ∀ c ∈ cells, c.result = valAt (T c.key.rule (values x c.key.path)) (cursor c.key.path)

def Complete (g : MGrammar) (x : List Char) (cells : List Cell) : Prop :=
  ∀ key ∈ keys g x.length, ∃ c ∈ cells, c.key = key

/-- A finite list of cells suffices for every call the real Seq evaluator
can issue, even when the incoming environment of the expression is arbitrary. -/
theorem table_agree {g : MGrammar} {x : List Char} {T : Table} {cells : List Cell}
    (hc : Correct x T cells) (ht : Complete g x cells) : Agree g x T (table x cells) := by
  intro i r W q hr hlen hw
  obtain ⟨p,spans,hp,hs,hd⟩ := hw
  have hl : (SequentialSpanRecompute.decodeEnv x spans).length = r.arity := by rw [hd]; exact hlen.symm
  obtain ⟨key,hkey,hi,hW,hq⟩ := SequentialTupleKeys.covered hr hs hp hl
  obtain ⟨cell,hcell,hkeyeq⟩ := ht key hkey
  have hm : keyMatches x i W q cell = true := by simp [keyMatches, hkeyeq, hi, hW, hd, hq]
  have hqbound := Nat.le_trans hs.descending hp
  rw [table, valAt_rangeMap, if_pos hqbound]
  unfold lookup
  cases hf : cells.find? (keyMatches x i W q) with
  | none => exact False.elim ((List.find?_eq_none.mp hf cell hcell) hm)
  | some selected =>
    have hb := List.find?_some hf
    have he : selected.key.rule = i ∧ values x selected.key.path = W ∧ cursor selected.key.path = q :=
      by simpa only [keyMatches, decide_eq_true_eq] using hb
    have hv := hc selected (List.mem_of_find?_eq_some hf)
    simpa only [Option.map_some, Option.getD_some, he.1, he.2.1, he.2.2] using hv.symm

end Shallot.MacroPeg.CBV.SequentialFiniteRows
