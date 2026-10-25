import MacroPeg.CBV.SequentialLocalCorrectness

/-! An executable evaluator using position recursion and a finite local
empty-call closure. It never consults the original evaluator as an oracle;
the canonical source tables appear only in the correctness proof below. -/
namespace Shallot.MacroPeg.CBV.SequentialPositionEvaluator
open SequentialClock (Table Descending)
open SequentialLocalClosure (overlay saturated)
open SequentialLocalCorrectness (canonical)

def column (g : MGrammar) (x : List Char) (p : Nat) : Nat → List (List Char) → Res :=
  let lower : Table := fun i W => (List.range (x.length+1)).map (fun q =>
    if _hq : q<p then column g x q i W else none)
  let U := overlay g x p lower (saturated g x p lower)
  fun i W => match ruleAtM g.rules i with
    | none => none
    | some r => evV g x .callByValueSeq U W r.body p
termination_by p

def lower (g : MGrammar) (x : List Char) (p : Nat) : Table :=
  fun i W => (List.range (x.length+1)).map (fun q => if q<p then column g x q i W else none)

theorem column_eq (g : MGrammar) (x : List Char) (p i : Nat) (W : List (List Char)) :
    column g x p i W=match ruleAtM g.rules i with
      | none => none
      | some r => evV g x .callByValueSeq
          (overlay g x p (lower g x p) (saturated g x p (lower g x p))) W r.body p := by
  rw [column]
  rfl

theorem column_descending (g : MGrammar) (x : List Char) : ∀ p i W, OkR p (column g x p i W) := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    have hl : Descending (lower g x p) := by
      intro i W q
      simp only [lower,valAt_rangeMap]
      split
      · split
        · rename_i hq; exact ih q hq i W
        · exact okR_none _
      · exact okR_none _
    have hd := SequentialLocalClosure.overlay_descending g x p (lower g x p) hl _
      (SequentialLocalClosure.rounds_descending g x p _ hl g.rules.length)
    intro i W
    rw [column_eq]
    cases hr : ruleAtM g.rules i with
    | none => exact okR_none _
    | some r => exact SequentialClock.expression_descending hd W r.body p

theorem lower_descending (g : MGrammar) (x : List Char) (p : Nat) : Descending (lower g x p) := by
  intro i W q
  simp only [lower,valAt_rangeMap]
  split
  · split
    · exact column_descending g x q i W
    · exact okR_none _
  · exact okR_none _

/-- The position-recursive result is the real source row, for every valid
incoming environment, including newly captured words of arbitrary length. -/
theorem column_correct (g : MGrammar) (x : List Char) : ∀ p, p≤x.length → ∀ i r W,
    ruleAtM g.rules i=some r → r.arity=W.length →
    column g x p i W=valAt (canonical g x i W) p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    intro hp i r W hr hlen
    have hl : ∀ q, q<p → SequentialClock.RowAgree g q (lower g x p) (canonical g x) := by
      intro q hq j r V hr hlen
      rw [lower,valAt_rangeMap,if_pos (Nat.le_trans (Nat.le_of_lt hq) hp),if_pos hq]
      exact ih q hq (Nat.le_trans (Nat.le_of_lt hq) hp) j r V hr hlen
    rw [column_eq,hr]
    exact (SequentialLocalClosure.expression_lower_agree g x p hp (lower g x p) (canonical g x)
      (lower_descending g x p) hl W r.body).trans
      ((SequentialLocalCorrectness.expression_eq_source g x p hp W r.body).trans
        (SequentialLocalCorrectness.canonical_unfold g x i r hr W hlen p hp).symm)

def run (g : MGrammar) (x : List Char) (E : List (List Char)) (e : MExp) (p : Nat) : Res :=
  evV g x .callByValueSeq (overlay g x p (lower g x p) (saturated g x p (lower g x p))) E e p

theorem run_correct (g : MGrammar) (x : List Char) (E : List (List Char)) (e : MExp)
    (p : Nat) (hp : p≤x.length) :
    run g x E e p=evV g x .callByValueSeq (canonical g x) E e p := by
  have hl : ∀ q, q<p → SequentialClock.RowAgree g q (lower g x p) (canonical g x) := by
    intro q hq i r W hr hlen
    rw [lower,valAt_rangeMap,if_pos (Nat.le_trans (Nat.le_of_lt hq) hp),if_pos hq]
    exact column_correct g x q (Nat.le_trans (Nat.le_of_lt hq) hp) i r W hr hlen
  exact (SequentialLocalClosure.expression_lower_agree g x p hp (lower g x p) (canonical g x)
    (lower_descending g x p) hl E e).trans (SequentialLocalCorrectness.expression_eq_source g x p hp E e)

def decide (g : MGrammar) (x : List Char) (e : MExp) : Option (Option (List Char)) :=
  match run g x [] e x.length with
  | none => none
  | some none => some none
  | some (some q) => some (some (sfx x q))

theorem decide_eq_standard (g : MGrammar) (x : List Char) (e : MExp) :
    decide g x e=decideObsV .callByValueSeq g x e := by
  unfold decide
  rw [run_correct g x [] e _ (Nat.le_refl _)]
  exact SequentialClock.decide_eq_standard g x e

theorem observations_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder)
    (x : List Char) (rest : Option (List Char)) :
    decide g x e=some rest ↔ SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard g x e]
  exact decideObsV_iff hg (by decide) he x rest

theorem undefined_iff (g : MGrammar) (hg : g.FirstOrder) (e : MExp) (he : e.FirstOrder) (x : List Char) :
    decide g x e=none ↔ ∀ rest, ¬SObs g .callByValueSeq e x rest := by
  rw [decide_eq_standard g x e]
  exact decideObsV_none_iff hg (by decide) he x

end Shallot.MacroPeg.CBV.SequentialPositionEvaluator
