import MacroPeg.CBVtoCBN.CounterStep

namespace Shallot.MacroPeg.CBVtoCBN

theorem substArgs_append (args a b : List MExp) :
    MExp.substArgs args (a ++ b) = MExp.substArgs args a ++ MExp.substArgs args b := by
  induction a with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, MExp.substArgs, ih]

theorem subst_paramsFrom_offset (pre args : List MExp) (start n : Nat) :
    MExp.substArgs (pre ++ args) (paramsFrom (pre.length + start) n) =
      MExp.substArgs args (paramsFrom start n) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show pre.length + 1 + start = (pre.length + start) + 1 by omega,
      subst_paramsFrom_cons, ih]

theorem subst_paramsFrom_take (args tail : List MExp) :
    MExp.substArgs (args ++ tail) (paramsFrom 0 args.length) = args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    simp only [List.cons_append, List.length_cons, paramsFrom, MExp.substArgs, MExp.subst, argAt]
    rw [subst_paramsFrom_cons, ih]

theorem subst_paramsFrom_slice (pre args tail : List MExp) :
    MExp.substArgs (pre ++ (args ++ tail)) (paramsFrom pre.length args.length) = args := by
  simpa only [Nat.add_zero] using
    (subst_paramsFrom_offset pre (args ++ tail) 0 args.length).trans (subst_paramsFrom_take args tail)

theorem subst_param_at (pre : List MExp) (a : MExp) (tail : List MExp) :
    MExp.subst (pre ++ a :: tail) (.param pre.length) = a := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simpa only [List.cons_append, List.length_cons, MExp.subst, argAt] using ih

/-- Flatten pairs of counter arguments, preserving their order. -/
def pairArgs : List (MExp × MExp) → List MExp
  | [] => []
  | (a, b) :: ps => a :: b :: pairArgs ps

theorem pairArgs_length (ps : List (MExp × MExp)) : (pairArgs ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [pairArgs, List.length_cons, ih]; omega

def pairRefs (start : Nat) : Nat → List (MExp × MExp)
  | 0 => []
  | d + 1 => (.param start, .param (start + 1)) :: pairRefs (start + 2) d

def substPairs (args : List MExp) (ps : List (MExp × MExp)) : List (MExp × MExp) :=
  ps.map (fun p => (MExp.subst args p.1, MExp.subst args p.2))

theorem subst_pairArgs (args : List MExp) (ps : List (MExp × MExp)) :
    MExp.substArgs args (pairArgs ps) = pairArgs (substPairs args ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [pairArgs, MExp.substArgs, substPairs, List.map_cons] at *; exact congrArg (fun xs => MExp.subst args p.1 :: MExp.subst args p.2 :: xs) ih

theorem subst_pairRefs (pre : List MExp) (ps : List (MExp × MExp)) (tail : List MExp) :
    substPairs (pre ++ (pairArgs ps ++ tail)) (pairRefs pre.length ps.length) = ps := by
  induction ps generalizing pre with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    simp only [List.length_cons, pairRefs, substPairs, List.map_cons, pairArgs, List.cons_append]
    have ha := subst_param_at pre a (b :: pairArgs ps ++ tail)
    have hb := subst_param_at (pre ++ [a]) b (pairArgs ps ++ tail)
    have ht := ih (pre ++ [a, b])
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add] at ha hb ht
    rw [ha, hb]
    exact congrArg (List.cons (a, b)) ht

/-- A static list of repeated counter pairs, used to reset borrowed digits. -/
def repeatPair (a b : MExp) : Nat → List MExp
  | 0 => []
  | k + 1 => a :: b :: repeatPair a b k

theorem subst_repeatPair (args : List MExp) (a b : MExp) (k : Nat) :
    MExp.substArgs args (repeatPair a b k) = repeatPair (MExp.subst args a) (MExp.subst args b) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [repeatPair, MExp.substArgs, ih]

theorem firstOrderArgs_append {a b : List MExp} (ha : MExp.FirstOrderArgs a) (hb : MExp.FirstOrderArgs b) :
    MExp.FirstOrderArgs (a ++ b) := by
  induction a with
  | nil => exact hb
  | cons e es ih => exact ⟨ha.1, ih ha.2⟩

theorem repeatPair_firstOrder {a b : MExp} (ha : a.FirstOrder) (hb : b.FirstOrder) (k : Nat) :
    MExp.FirstOrderArgs (repeatPair a b k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨ha, hb, ih⟩

theorem ruleAtM_append_offset (pre tail : List MRule) (i : Nat) :
    ruleAtM (pre ++ tail) (pre.length + i) = ruleAtM tail i := by
  induction pre with
  | nil => simp
  | cons rule pre ih =>
    simp only [List.cons_append, List.length_cons]
    rw [show pre.length + 1 + i = (pre.length + i) + 1 by omega, ruleAtM, ih]

end Shallot.MacroPeg.CBVtoCBN
