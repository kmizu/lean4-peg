import MacroPeg.CBV.ParTableau.Initial
import MacroPeg.CBV.ParTableau.Position
import Complexity.TopFormula

namespace Shallot.MacroPeg.CBV.ParTableau

open PrefixCounters RootObservation
open CBVtoCBN (clockValue predClock predClock_spec)
open Complexity (TM Cfg Move)

abbrev cfg {k : Nat} (M : TM k) (x : List Char) (t : Nat) : Cfg k :=
  M.run (Complexity.initCfg k (inputBits x)) t

theorem cfg_succ {k : Nat} (M : TM k) (x : List Char) (t : Nat) :
    cfg M x (t + 1) = M.step (cfg M x t) := rfl

theorem cfg_pos_le {k : Nat} (M : TM k) (x : List Char) : ∀ t i, (cfg M x t).pos i ≤ t
  | 0, _ => Nat.le_refl 0
  | t + 1, i => by
    rw [cfg_succ, Complexity.step_pos]
    have hmove : ∀ mv : Move, mv.apply ((cfg M x t).pos i) ≤ (cfg M x t).pos i + 1 := by
      intro mv; cases mv <;> simp [Move.apply] <;> omega
    have := hmove (Complexity.moveOf M (cfg M x t).state (cfg M x t).read i)
    have := cfg_pos_le M x t i
    omega

def ValidQuery {k : Nat} (M : TM k) : Node k → Prop
  | .state q => q < M.nq
  | .head _ => True
  | .cell _ s => s < M.na
  | _ => False

theorem valid_mem {k : Nat} (M : TM k) (node : Node k) (h : ValidQuery M node) : node ∈ nodes M := by
  cases node with
  | state q => exact state_mem M q h
  | head i => exact head_mem M i
  | cell i s => exact cell_mem M i s h
  | read _ _ | incHead _ | decHead _ => cases h

theorem valid_timed {k : Nat} (M : TM k) (node : Node k) (h : ValidQuery M node) : Timed node := by
  cases node <;> trivial

def Good {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time : List Nat) (t : Nat) : Prop :=
  ∀ position, position.length = d → (∀ a ∈ position, a ≤ x.length) →
    ∀ node, ValidQuery M node →
      Test (compile M d) .callByValuePar
        (.call (address M d node) (prefixValues x (x.length :: (time ++ position)))) x
          (queryBit (cfg M x t) (clockValue x.length position) node)

/-- All predecessor-time obligations of the finite transition proof follow
from actual compiled queries, including read-symbol search and arithmetic. -/
theorem good_previous {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time : List Nat)
    (ht : time.length = d) (t : Nat) (hb : t < (x.length + 1) ^ d) (h : Good M d x time t)
    (position : List Nat) (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length) :
    Previous (compile M d) M d (prefixValues x (x.length :: (time ++ position))) x
      (cfg M x t) (clockValue x.length position) := by
  have hbound : ∀ i, (cfg M x t).pos i < (x.length + 1) ^ d := fun i => Nat.lt_of_le_of_lt (cfg_pos_le M x t i) hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact h position hp hv (.state q) hq
  · intro i s hs
    apply compiled_read_test M d x time position ht hp (cfg M x t) i s hs (hbound i)
    · intro ds hd hv; exact h ds hd hv (.head i) trivial
    · intro ds hd hv; exact h ds hd hv (.cell i s) hs
  · intro i; exact h position hp hv (.head i) trivial
  · intro i s hs; exact h position hp hv (.cell i s) hs
  · intro i mv
    exact movedHead_test M d x time position ht hp hv i (cfg M x t) (hbound i)
      (fun ds hd hv => h ds hd hv (.head i) trivial) mv

theorem nextBody_test {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time position : List Nat)
    (ht : time.length = d) (hp : position.length = d) (hv : ∀ a ∈ position, a ≤ x.length)
    (t : Nat) (hb : t < (x.length + 1) ^ d) (h : Good M d x time t)
    (node : Node k) (hn : ValidQuery M node) :
    Test (compile M d) .callByValuePar
      (MExp.subst (prefixValues x (x.length :: (time ++ position))) (nextBody M d node)) x
        (queryBit (M.step (cfg M x t)) (clockValue x.length position) node) := by
  have hl : (prefixValues x (x.length :: (time ++ position))).length = width d := by
    simp only [prefixValues_length, List.length_cons, List.length_append, ht, hp, width]; omega
  have hc := Complexity.inRange_run M (Complexity.inRange_init M (inputBits x)) t
  have hr : ∀ i, (cfg M x t).read i < M.na := fun i => hc.2 i _
  have hprev := good_previous M d x time ht t hb h position hp hv
  cases node with
  | state q => exact stateNext_test M d _ hl _ _ q hc.1 hr hprev
  | head i => exact headNext_test M d _ hl _ _ i hc.1 hr hprev
  | cell i s => exact cellNext_test M d _ hl _ _ s i hc.1 hr hn hprev
  | read _ _ | incHead _ | decHead _ => cases hn

/-- The generated first-order Par queries follow the actual multi-tape TM
at every representable time and position, on the original character input.
No simulator correctness or termination premise remains. -/
theorem tableau_sim {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time : List Nat)
    (ht : time.length = d) (hv : ∀ a ∈ time, a ≤ x.length) :
    Good M d x time (clockValue x.length time) := by
  have aux : ∀ t, ∀ time : List Nat, time.length = d → (∀ a ∈ time, a ≤ x.length) →
      clockValue x.length time = t → Good M d x time t := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro time ht hv hval position hp hpv node hn
      apply (timed_call_iff M d node (valid_mem M node hn) (valid_timed M node hn)
        x time position ht hp hv _).mpr
      have hspec := predClock_spec x.length time hv
      cases hs : predClock x.length time with
      | none =>
        simp only [hs] at hspec ⊢
        have hz : t = 0 := by omega
        subst t
        apply (par_call_iff (timed_zero_rule M d node (valid_mem M node hn) (valid_timed M node hn))
          (by simp [hp]) (prefixValues_args _ x position) _).mpr
        simpa only [Test, hspec, cfg, TM.run] using zeroBody_test M d x position hp hpv node (valid_timed M node hn)
      | some previous =>
        simp only [hs] at hspec ⊢
        have hlen : previous.length = d := hspec.1.trans ht
        have hless : clockValue x.length previous < t := by omega
        have hgood := ih (clockValue x.length previous) hless previous hlen hspec.2.1 rfl
        have hbound : clockValue x.length previous < (x.length + 1) ^ d := by
          simpa only [hlen] using clockValue_lt x.length previous hspec.2.1
        have hbody := nextBody_test M d x previous position hlen hp hpv
          (clockValue x.length previous) hbound hgood node hn
        have he : t = clockValue x.length previous + 1 := by omega
        rw [← cfg_succ, ← he] at hbody
        apply (par_call_iff (timed_next_rule M d node (valid_mem M node hn) (valid_timed M node hn))
          (by simp only [prefixValues_length, List.length_cons, List.length_append, hlen, hp, width]; omega)
            (prefixValues_args _ x (x.length :: (previous ++ position))) _).mpr
        exact hbody
  exact aux _ time ht hv rfl

theorem read_sim {k : Nat} (M : TM k) (d : Nat) (x : List Char) (time position : List Nat)
    (ht : time.length = d) (hv : ∀ a ∈ time, a ≤ x.length) (hp : position.length = d)
    (i : Fin k) (s : Nat) (hs : s < M.na) :
    Test (compile M d) .callByValuePar
      (.call (address M d (.read i s)) (prefixValues x (x.length :: (time ++ position)))) x
        ((cfg M x (clockValue x.length time)).read i == s) := by
  have hgood := tableau_sim M d x time ht hv
  have hb : (cfg M x (clockValue x.length time)).pos i < (x.length + 1) ^ d :=
    Nat.lt_of_le_of_lt (cfg_pos_le M x _ i) (by simpa only [ht] using clockValue_lt x.length time hv)
  apply compiled_read_test M d x time position ht hp _ i s hs hb
  · intro ds hd hv; exact hgood ds hd hv (.head i) trivial
  · intro ds hd hv; exact hgood ds hd hv (.cell i s) hs

end Shallot.MacroPeg.CBV.ParTableau
