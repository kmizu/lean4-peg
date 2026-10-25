import MacroPeg.CBV.SequentialLocalClosure

namespace Shallot.MacroPeg.CBV.SequentialLocalOrder
open SequentialClock (Table Descending)

def LocalLe (g : MGrammar) (p : Nat) (T U : Table) : Prop :=
  ∀ i r W, ruleAtM g.rules i=some r → r.arity=W.length → ∀ q, q≤p →
    (q=p → W=List.replicate r.arity []) → RLe (valAt (T i W) q) (valAt (U i W) q)

def reachable (g : MGrammar) (p i : Nat) (W : List (List Char)) (q : Nat) : Bool :=
  match ruleAtM g.rules i with
  | none => false
  | some r => decide (r.arity=W.length ∧ q≤p ∧ (q=p → W=List.replicate r.arity []))

def mix (g : MGrammar) (x : List Char) (p : Nat) (T U : Table) : Table :=
  fun i W => (List.range (x.length+1)).map (fun q =>
    if reachable g p i W q then valAt (U i W) q else valAt (T i W) q)

theorem table_outside (g : MGrammar) (x : List Char) (k i : Nat) (W : List (List Char))
    (q : Nat) (hq : x.length<q) : valAt (tblV g x .callByValueSeq k i W) q=none := by
  cases k with
  | zero => rfl
  | succ k =>
    cases hr : ruleAtM g.rules i <;> simp [tblV,hr,valAt_nil,valAt_rangeMap,show ¬q≤x.length by omega]

theorem mix_descending (g : MGrammar) (x : List Char) (p : Nat) (T U : Table)
    (ht : Descending T) (hu : Descending U) : Descending (mix g x p T U) := by
  intro i W q
  simp only [mix,valAt_rangeMap]
  split
  · split
    · exact hu i W q
    · exact ht i W q
  · exact okR_none _

theorem table_le_mix (g : MGrammar) (x : List Char) (p k : Nat) (U : Table)
    (h : LocalLe g p (tblV g x .callByValueSeq k) U) :
    TLeV (tblV g x .callByValueSeq k) (mix g x p (tblV g x .callByValueSeq k) U) := by
  intro i W q
  simp only [mix,valAt_rangeMap]
  by_cases hq : q≤x.length
  · rw [if_pos hq]
    by_cases hc : reachable g p i W q=true
    · rw [if_pos hc]
      cases hr : ruleAtM g.rules i with
      | none => simp [reachable,hr] at hc
      | some r =>
        have hh : r.arity=W.length ∧ q≤p ∧ (q=p → W=List.replicate r.arity []) := of_decide_eq_true (by simpa only [reachable,hr] using hc)
        exact h i r W hr hh.1 q hh.2.1 hh.2.2
    · rw [if_neg hc]; exact RLe.refl _
  · rw [if_neg hq,table_outside g x k i W q (by omega)]; exact RLe.refl _

theorem mix_agrees (g : MGrammar) (x : List Char) (p : Nat) (hp : p≤x.length) (T U : Table) :
    SequentialClock.LocalAgree g p (mix g x p T U) U := by
  intro i r W hr hlen q hq hz
  have hc : reachable g p i W q=true := by
    simp only [reachable,hr]
    exact decide_eq_true ⟨hlen,hq,hz⟩
  simp only [mix,valAt_rangeMap,if_pos (Nat.le_trans hq hp),if_pos hc]

/-- A local partial order suffices: arbitrary environments are needed only
at smaller positions, and empty environments at the current position. -/
theorem expression_mono (g : MGrammar) (x : List Char) (p k : Nat) (hp : p≤x.length)
    (U : Table) (hu : Descending U) (h : LocalLe g p (tblV g x .callByValueSeq k) U)
    (E : List (List Char)) (e : MExp) :
    RLe (evV g x .callByValueSeq (tblV g x .callByValueSeq k) E e p)
      (evV g x .callByValueSeq U E e p) := by
  have hm := evV_mono (g:=g) (x:=x) (s:=.callByValueSeq) (E:=E) (table_le_mix g x p k U h) e p
  have he := SequentialClock.expression_agree (x:=x)
    (mix_descending g x p _ U (SequentialClock.table_descending g x k) hu)
    (mix_agrees g x p hp _ U) E e p (Nat.le_refl _)
  rw [he] at hm
  exact hm

end Shallot.MacroPeg.CBV.SequentialLocalOrder
