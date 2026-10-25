import MacroPeg.CBV.FiniteResultClosure

/-! Freeze all strictly later input positions and iterate only the finite
vector of empty-environment rule results at the current position. The vector
starts at undefined, and no captured-string palette is enumerated. -/
namespace Shallot.MacroPeg.CBV.SequentialLocalClosure
open SequentialClock (Table Descending)
open FiniteResultClosure (Vector)

def overlay (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) (V : Vector g.rules.length) : Table :=
  fun i W => (List.range (x.length+1)).map (fun q =>
    if q<p then valAt (lower i W) q else
    if q=p then if hi : i<g.rules.length then V ⟨i,hi⟩ else none else none)

def step (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (V : Vector g.rules.length) : Vector g.rules.length := fun i =>
  evV g x .callByValueSeq (overlay g x p lower V) (List.replicate g.rules[i].arity []) g.rules[i].body p

def rounds (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) (k : Nat) : Vector g.rules.length :=
  FiniteResultClosure.rounds (step g x p lower) k
def saturated (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) :=
  rounds g x p lower g.rules.length

theorem overlay_lower (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) (V : Vector g.rules.length)
    (i : Nat) (W : List (List Char)) (q : Nat) (hq : q≤x.length) (hqp : q<p) :
    valAt (overlay g x p lower V i W) q=valAt (lower i W) q := by
  simp only [overlay,valAt_rangeMap,if_pos hq,if_pos hqp]

theorem overlay_here (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) (V : Vector g.rules.length)
    (i : Fin g.rules.length) (W : List (List Char)) (hp : p≤x.length) :
    valAt (overlay g x p lower V i W) p=V i := by
  simp [overlay,valAt_rangeMap,hp,i.isLt]

theorem overlay_mono (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (U V : Vector g.rules.length) (h : FiniteResultClosure.Le U V) :
    TLeV (overlay g x p lower U) (overlay g x p lower V) := by
  intro i W q
  simp only [overlay,valAt_rangeMap]
  split
  · split
    · exact RLe.refl _
    · split
      · split
        · exact h _
        · exact RLe.refl _
      · exact RLe.refl _
  · exact RLe.refl _

theorem step_mono (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) :
    FiniteResultClosure.Monotone (step g x p lower) := by
  intro U V h i
  exact evV_mono (overlay_mono g x p lower U V h) _ p

theorem fixed (g : MGrammar) (x : List Char) (p : Nat) (lower : Table) :
    step g x p lower (saturated g x p lower)=saturated g x p lower :=
  FiniteResultClosure.fixed _ (step_mono g x p lower)

theorem least (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (V : Vector g.rules.length) (hv : step g x p lower V=V) :
    FiniteResultClosure.Le (saturated g x p lower) V :=
  FiniteResultClosure.least _ (step_mono g x p lower) V hv

theorem overlay_descending (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (hl : Descending lower) (V : Vector g.rules.length) (hv : ∀ i, OkR p (V i)) :
    Descending (overlay g x p lower V) := by
  intro i W q
  simp only [overlay,valAt_rangeMap]
  split
  · split
    · exact hl i W q
    · split
      · rename_i hq
        subst q
        split
        · exact hv _
        · exact okR_none _
      · exact okR_none _
  · exact okR_none _

theorem rounds_descending (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (hl : Descending lower) : ∀ k i, OkR p (rounds g x p lower k i) := by
  intro k
  induction k with
  | zero => intro i; exact okR_none _
  | succ k ih =>
    intro i
    exact SequentialClock.expression_descending (overlay_descending g x p lower hl _ ih)
      _ g.rules[i].body p

/-- The frozen-lower-position evaluator uses precisely |rules| vector rounds,
for arbitrary arities and arbitrary retained values in those lower rows. -/
theorem empty_rule_equation (g : MGrammar) (x : List Char) (p : Nat) (lower : Table)
    (i : Fin g.rules.length) :
    saturated g x p lower i=
      evV g x .callByValueSeq (overlay g x p lower (saturated g x p lower))
        (List.replicate g.rules[i].arity []) g.rules[i].body p :=
  (congrFun (fixed g x p lower) i).symm

theorem overlay_lower_agree (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length)
    (L M : Table) (V : Vector g.rules.length)
    (h : ∀ q, q<p → SequentialClock.RowAgree g q L M) :
    SequentialClock.LocalAgree g p (overlay g x p L V) (overlay g x p M V) := by
  intro i r W hr hlen q hq hz
  by_cases he : q=p
  · subst q
    rw [overlay_here g x p L V ⟨i,ruleAtM_lt hr⟩ W hp,
      overlay_here g x p M V ⟨i,ruleAtM_lt hr⟩ W hp]
  · have hh : q<p := by omega
    rw [overlay_lower g x p L V i W q (Nat.le_trans hq hp) hh,
      overlay_lower g x p M V i W q (Nat.le_trans hq hp) hh]
    exact h q hh i r W hr hlen

/-- Only valid rows at strictly smaller positions influence this closure;
no result at the current position is read from the supplied lower table. -/
theorem rounds_lower_agree (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length)
    (L M : Table) (hl : Descending L)
    (h : ∀ q, q<p → SequentialClock.RowAgree g q L M) :
    ∀ k, rounds g x p L k=rounds g x p M k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    change evV g x .callByValueSeq (overlay g x p L (rounds g x p L k)) _ _ p=
      evV g x .callByValueSeq (overlay g x p M (rounds g x p M k)) _ _ p
    rw [←ih]
    exact SequentialClock.expression_agree (x:=x)
      (overlay_descending g x p L hl _ (rounds_descending g x p L hl k))
      (overlay_lower_agree g x p hp L M _ h) _ _ p (Nat.le_refl _)

theorem expression_lower_agree (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length)
    (L M : Table) (hl : Descending L)
    (h : ∀ q, q<p → SequentialClock.RowAgree g q L M) (E : List (List Char)) (e : MExp) :
    evV g x .callByValueSeq (overlay g x p L (saturated g x p L)) E e p=
      evV g x .callByValueSeq (overlay g x p M (saturated g x p M)) E e p := by
  have hv : saturated g x p L=saturated g x p M := rounds_lower_agree g x p hp L M hl h g.rules.length
  rw [←hv]
  exact SequentialClock.expression_agree (x:=x)
    (overlay_descending g x p L hl _ (rounds_descending g x p L hl g.rules.length))
    (overlay_lower_agree g x p hp L M _ h) E e p (Nat.le_refl _)

end Shallot.MacroPeg.CBV.SequentialLocalClosure
