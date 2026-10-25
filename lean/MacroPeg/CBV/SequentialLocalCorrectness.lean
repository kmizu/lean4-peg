import MacroPeg.CBV.SequentialLocalOrder

namespace Shallot.MacroPeg.CBV.SequentialLocalCorrectness
open SequentialClock (Table)
open SequentialLocalClosure (overlay step saturated)

def clock (g : MGrammar) (x : List Char) := SequentialClock.positionClock g x.length
def canonical (g : MGrammar) (x : List Char) : Table := tblV g x .callByValueSeq (clock g x)
def emptyValues (g : MGrammar) (x : List Char) (p : Nat) : FiniteResultClosure.Vector g.rules.length :=
  fun i => valAt (canonical g x i (List.replicate g.rules[i].arity [])) p

private theorem rule_get (g : MGrammar) (i : Nat) (r : MRule) (hr : ruleAtM g.rules i=some r) :
    g.rules[i]'(ruleAtM_lt hr)=r := by
  have h : g.rules[i]?=some r := by simpa only [ruleAtM_eq_getElem?] using hr
  simpa only [List.getElem?_eq_getElem (ruleAtM_lt hr),Option.some.injEq] using h

theorem canonical_from (g : MGrammar) (x : List Char) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (W : List (List Char)) (hlen : r.arity=W.length)
    (p : Nat) (hp : p≤x.length) : ∀ d,
    valAt (canonical g x i W) p=valAt (tblV g x .callByValueSeq (clock g x+d) i W) p := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    apply ih.trans
    apply SequentialClock.position_stable g x p hp (clock g x+d) ?_ i r W hr hlen
    have h := Nat.mul_le_mul_left (g.rules.length+1) (show p+1≤x.length+1 by omega)
    exact Nat.le_trans h (by unfold clock SequentialClock.positionClock; omega)

theorem stage_le_canonical (g : MGrammar) (x : List Char) (k i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (W : List (List Char)) (hlen : r.arity=W.length)
    (p : Nat) (hp : p≤x.length) :
    RLe (valAt (tblV g x .callByValueSeq k i W) p) (valAt (canonical g x i W) p) := by
  by_cases hk : k≤clock g x
  · exact tblV_le g x .callByValueSeq hk i W p
  · have h := canonical_from g x i r hr W hlen p hp (k-clock g x)
    rw [Nat.add_sub_cancel' (by omega)] at h
    exact Or.inr h.symm

theorem canonical_unfold (g : MGrammar) (x : List Char) (i : Nat) (r : MRule)
    (hr : ruleAtM g.rules i=some r) (W : List (List Char)) (hlen : r.arity=W.length)
    (p : Nat) (hp : p≤x.length) :
    valAt (canonical g x i W) p=evV g x .callByValueSeq (canonical g x) W r.body p := by
  have h := canonical_from g x i r hr W hlen p hp 1
  rw [valAt_tblV_succ hr W hp] at h
  exact h

theorem overlay_canonical_agrees (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) :
    SequentialClock.LocalAgree g p (overlay g x p (canonical g x) (emptyValues g x p)) (canonical g x) := by
  intro i r W hr hlen q hq hz
  by_cases he : q=p
  · subst q
    rw [SequentialLocalClosure.overlay_here g x p (canonical g x) (emptyValues g x p) ⟨i,ruleAtM_lt hr⟩ W hp]
    change valAt (canonical g x i (List.replicate (g.rules[i]'(ruleAtM_lt hr)).arity [])) p=valAt (canonical g x i W) p
    rw [rule_get g i r hr,hz rfl]
  · exact SequentialLocalClosure.overlay_lower g x p _ _ i W q (Nat.le_trans hq hp) (by omega)

theorem canonical_is_local_fixed (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) :
    step g x p (canonical g x) (emptyValues g x p)=emptyValues g x p := by
  have hv : ∀ i, OkR p (emptyValues g x p i) := by
    intro i
    exact SequentialClock.table_descending g x (clock g x) i _ p
  funext i
  have hd := SequentialLocalClosure.overlay_descending g x p (canonical g x)
    (SequentialClock.table_descending g x (clock g x)) (emptyValues g x p) hv
  have he := SequentialClock.expression_agree (x:=x) hd (overlay_canonical_agrees g x p hp)
    (List.replicate g.rules[i].arity []) g.rules[i].body p (Nat.le_refl _)
  change evV g x .callByValueSeq _ _ _ p=valAt (canonical g x i _) p
  rw [he]
  exact (canonical_unfold g x i g.rules[i] (by simp [ruleAtM_eq_getElem?,i.isLt]) _ (by simp) p hp).symm

/-- Local iteration cannot invent a source result: its least fixed point
lies below the canonical empty-environment results. -/
theorem saturated_le_source (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) :
    FiniteResultClosure.Le (saturated g x p (canonical g x)) (emptyValues g x p) :=
  SequentialLocalClosure.least g x p _ _ (canonical_is_local_fixed g x p hp)

theorem stages_le_saturated (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) :
    ∀ k (i : Fin g.rules.length), RLe (valAt (tblV g x .callByValueSeq k i (List.replicate g.rules[i].arity [])) p)
      (saturated g x p (canonical g x) i) := by
  let V := saturated g x p (canonical g x)
  let U := overlay g x p (canonical g x) V
  have hd : SequentialClock.Descending U := SequentialLocalClosure.overlay_descending g x p _
    (SequentialClock.table_descending g x (clock g x)) V
    (SequentialLocalClosure.rounds_descending g x p _ (SequentialClock.table_descending g x (clock g x)) g.rules.length)
  intro k
  induction k with
  | zero => intro i; exact Or.inl rfl
  | succ k ih =>
    intro i
    have hr : ruleAtM g.rules i=some g.rules[i] := by simp [ruleAtM_eq_getElem?,i.isLt]
    rw [valAt_tblV_succ hr _ hp]
    have hl : SequentialLocalOrder.LocalLe g p (tblV g x .callByValueSeq k) U := by
      intro j r W hr hlen q hq hz
      by_cases hsame : q=p
      · subst q
        rw [hz rfl,SequentialLocalClosure.overlay_here g x p (canonical g x) V ⟨j,ruleAtM_lt hr⟩ _ hp]
        have hj := ih ⟨j,ruleAtM_lt hr⟩
        change RLe (valAt (tblV g x .callByValueSeq k j (List.replicate (g.rules[j]'(ruleAtM_lt hr)).arity [])) p)
          (V ⟨j,ruleAtM_lt hr⟩) at hj
        rw [rule_get g j r hr] at hj
        exact hj
      · rw [SequentialLocalClosure.overlay_lower g x p (canonical g x) V j W q (Nat.le_trans hq hp) (by omega)]
        exact stage_le_canonical g x k j r hr W hlen q (Nat.le_trans hq hp)
    have he := SequentialLocalOrder.expression_mono g x p k hp U hd hl (List.replicate g.rules[i].arity []) g.rules[i].body
    have hf := SequentialLocalClosure.empty_rule_equation g x p (canonical g x) i
    rw [←hf] at he
    exact he

/-- With the source's smaller-position rows frozen, exactly |rules| rounds
recover the actual source result, including undefinedness, at this position. -/
theorem saturated_eq_source (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) :
    saturated g x p (canonical g x)=emptyValues g x p := by
  funext i
  have hu := saturated_le_source g x p hp i
  have hl := stages_le_saturated g x p hp (clock g x) i
  rcases hu with hn|he
  · rcases hl with hn'|he'
    · exact hn.trans hn'.symm
    · exact he'.symm
  · exact he

/-- After the finite local closure, arbitrary retained environments and raw
continuations agree with the original stabilized evaluator. -/
theorem expression_eq_source (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length)
    (E : List (List Char)) (e : MExp) :
    evV g x .callByValueSeq (overlay g x p (canonical g x) (saturated g x p (canonical g x))) E e p=
      evV g x .callByValueSeq (canonical g x) E e p := by
  rw [saturated_eq_source g x p hp]
  apply SequentialClock.expression_agree (x:=x) _ (overlay_canonical_agrees g x p hp) E e p (Nat.le_refl _)
  exact SequentialLocalClosure.overlay_descending g x p _ (SequentialClock.table_descending g x (clock g x)) _
    (fun i => SequentialClock.table_descending g x (clock g x) i _ p)

end Shallot.MacroPeg.CBV.SequentialLocalCorrectness
