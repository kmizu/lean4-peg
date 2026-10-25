import MacroPeg.CBV.ObservedScanner

namespace Shallot.MacroPeg.CBV.ObservedScannerDispatch
open StatefulScanner
open ObservedScanner (Observer machine consumed finish states)
open StatefulScannerProduct (pack left right)

/-- Every possible final scanner/observer pair has a real relocated block. -/
def rules {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) (base : Nat) : List MRule :=
  (List.ofFn (fun target : Fin (n*D.width) =>
    block (machine M D hD) (fun q => decide (q=target)) (base+target.val*(n*D.width)))).flatten

def grammar {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) : MGrammar := ⟨before++rules M D hD before.length++extra⟩

def entry {n : Nat} {D : Observer} (base : Nat) (q : Fin n) (a : Fin D.width)
    (target : Fin (n*D.width)) : MExp :=
  .call (base+target.val*(n*D.width)+(pack q a).val) []

theorem length {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) (base : Nat) :
    (rules M D hD base).length=(n*D.width)*(n*D.width) := by
  unfold rules
  rw [List.length_flatten]
  have he : (List.ofFn (fun target : Fin (n*D.width) =>
      block (machine M D hD) (fun q => decide (q=target)) (base+target.val*(n*D.width)))).map List.length =
      List.replicate (n*D.width) (n*D.width) := by
    simp only [List.map_ofFn,Function.comp_def,block_length]
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [he,List.sum_replicate_nat]

theorem rule {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) (base : Nat)
    (q target : Fin (n*D.width)) :
    ruleAtM (rules M D hD base) (target.val*(n*D.width)+q.val)=some
      ⟨0,branches (base+target.val*(n*D.width)) (terminal (decide (q=target))) ((machine M D hD).arcs q)⟩ := by
  rw [ruleAtM_eq_getElem?]
  unfold rules
  rw [StatefulScannerFamily.uniform_lookup _ (n*D.width) (by
    intro b hb
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hb
    exact block_length _ _ _) target.val q.val q.isLt]
  simp [block,target.isLt,q.isLt]

theorem installed_rule {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) (q target : Fin (n*D.width)) :
    ruleAtM (grammar M D hD before extra).rules (before.length+target.val*(n*D.width)+q.val)=some
      ⟨0,branches (before.length+target.val*(n*D.width)) (terminal (decide (q=target)))
        ((machine M D hD).arcs q)⟩ := by
  have hr := rule M D hD before.length q target
  rw [ruleAtM_eq_getElem?] at hr
  have hb := (List.getElem?_eq_some_iff.mp hr).1
  simp only [grammar,ruleAtM_eq_getElem?,List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have he : before.length+target.val*(n*D.width)+q.val-before.length=target.val*(n*D.width)+q.val := by omega
  rw [he,List.getElem?_append_left hb,hr]

theorem firstOrder {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid) (base : Nat) :
    ∀ r∈rules M D hD base, r.body.FirstOrder := by
  intro r hr
  obtain ⟨b,hb,hr⟩ := List.mem_flatten.mp hr
  obtain ⟨target,rfl⟩ := List.mem_ofFn.mp hb
  change r ∈ List.ofFn (fun q : Fin (n*D.width) =>
    ⟨0,branches (base+target.val*(n*D.width)) (terminal (decide (q=target))) ((machine M D hD).arcs q)⟩) at hr
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hr
  apply branches_firstOrder
  cases decide (q=target) <;> trivial

/-- Physical evaluation in the real surrounding grammar. No final state,
consumed word or scanner row is supplied by the caller. -/
theorem entry_eval {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) (q : Fin n) (a : Fin D.width) (target : Fin (n*D.width))
    (x : List Char) (s : Strategy) (E : List (List Char)) (p clock : Nat)
    (hp : p≤x.length) (hclock : p+1≤clock) :
    evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
      (entry before.length q a target) p =
      some (if target=pack (run M q (sfx x p)).1 (finish D hD a (consumed M q (sfx x p)))
        then some (run M q (sfx x p)).2.length else none) := by
  have hh := query_eval (machine M D hD) (fun r => decide (r=target)) (grammar M D hD before extra)
    (before.length+target.val*(n*D.width)) (fun r => installed_rule M D hD before extra r target)
    x s p hp clock hclock (pack q a)
  rw [ObservedScanner.run_observed] at hh
  simp only [decide_eq_true_eq] at hh
  have hr := installed_rule M D hD before extra (pack q a) target
  cases s <;> simpa only [entry,evV,hr,evParArgs,evSeqArgs,List.length_nil,ite_true,decide_eq_true_eq,eq_comm] using hh

/-- The actual successful scan fixes the observer continuation. A later
failure or undefined computation cannot select a different stopping point. -/
def dispatch {n : Nat} {D : Observer} (base : Nat) (q : Fin n) (a : Fin D.width)
    (K : Fin (n*D.width) → MExp) : MExp :=
  RegularCaptureProduct.choice ((states (n*D.width)).map
    (fun target => .seq (entry base q a target) (K target)))

theorem dispatch_firstOrder {n : Nat} {D : Observer} (base : Nat) (q : Fin n) (a : Fin D.width)
    (K : Fin (n*D.width) → MExp) (hK : ∀ t, (K t).FirstOrder) :
    (dispatch base q a K).FirstOrder := by
  apply RegularCaptureProduct.choice_firstOrder
  intro e he
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp he
  exact ⟨True.intro,hK t⟩

theorem dispatch_result {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) (q : Fin n) (a : Fin D.width)
    (K : Fin (n*D.width) → MExp) (x : List Char) (s : Strategy) (E : List (List Char))
    (p clock : Nat) (hp : p≤x.length) (hclock : p+1≤clock) :
    evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
      (dispatch before.length q a K) p =
      evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
        (K (pack (run M q (sfx x p)).1 (finish D hD a (consumed M q (sfx x p)))))
        (run M q (sfx x p)).2.length := by
  unfold dispatch
  rw [CaptureTransitionProfile.choice_unique
    (chosen := pack (run M q (sfx x p)).1 (finish D hD a (consumed M q (sfx x p))))]
  · rw [if_pos (by simp [states])]
  · intro target _
    have hv := entry_eval M D hD before extra q a target x s E p clock hp hclock
    by_cases ht : target=pack (run M q (sfx x p)).1 (finish D hD a (consumed M q (sfx x p)))
    · rw [if_pos ht] at hv
      rw [evV_seq_ok hv,if_pos ht,ht]
    · rw [if_neg ht] at hv
      rw [evV_seq_fail hv,if_neg ht]

theorem dispatch_product_result {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) (q : Fin n) (a : Fin D.width)
    (K : Fin (n*D.width) → MExp) (x : List Char) (s : Strategy) (E : List (List Char))
    (p clock : Nat) (hp : p≤x.length) (hclock : p+1≤clock) :
    evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
      (dispatch before.length q a K) p =
      evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
        (K (run (machine M D hD) (pack q a) (sfx x p)).1)
        (run (machine M D hD) (pack q a) (sfx x p)).2.length := by
  rw [dispatch_result M D hD before extra q a K x s E p clock hp hclock,ObservedScanner.run_observed]

/-- Across a physical captured prefix, both the scanner state and the
observer state must advance. This equality preserves arbitrary later user
computations, including their finite failures and undefined results. -/
theorem dispatch_handoff {n : Nat} (M : Machine n) (D : Observer) (hD : D.Valid)
    (before extra : List MRule) (q r : Fin n) (a : Fin D.width)
    (w x : List Char) (p j clock : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) (hstep : advance M q w=some r) (hclock : p+1≤clock)
    (s : Strategy) (E : List (List Char)) (K : Fin (n*D.width) → MExp) :
    evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
      (dispatch before.length q a K) p =
      evV (grammar M D hD before extra) x s (tblV (grammar M D hD before extra) x s clock) E
        (dispatch before.length r (finish D hD a w) K) j := by
  have hlen := congrArg List.length hcap
  rw [length_sfx x hp,List.length_append,length_sfx x hj] at hlen
  have hclockj : j+1≤clock := by omega
  rw [dispatch_product_result M D hD before extra q a K x s E p clock hp hclock,
    dispatch_product_result M D hD before extra r (finish D hD a w) K x s E j clock hj hclockj,
    hcap,ObservedScanner.residual_run M D hD q r a w (sfx x j) hstep]

end Shallot.MacroPeg.CBV.ObservedScannerDispatch
