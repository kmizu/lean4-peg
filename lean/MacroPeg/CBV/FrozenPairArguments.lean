import MacroPeg.CBV.StatefulScannerStability

/-! Exact lexical and dispatch contracts at every frozen user stage, including
stage zero. Helper evaluation consumes no user rounds; the cofinality
theorems relate this analysis back to the actual grammar. -/
namespace Shallot.MacroPeg.CBV.FrozenPairArguments
open StatefulScanner StatefulScannerProduct StatefulPairArguments
open StatefulScannerStability (frozen helpers helperCount)

private theorem call_nil (g : MGrammar) (x : List Char) (s : Strategy)
    {i : Nat} {r : MRule} (hr : ruleAtM g.rules i = some r) (ha : r.arity=0)
    (T : ClockFreezing.Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (.call i []) p = valAt (T i []) p := by
  cases s <;> simp [evV,evSeqArgs,evParArgs,hr,ha]


theorem left_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a : Fin n) (p clock : Nat)
    (hp : p ≤ x.length) :
    evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E (leftEntry (m := m) a) p =
      some (some (run A a (sfx x p)).2.length) := by
  rw [leftEntry,call_nil _ _ _ (left_rule A B hm tail a) rfl]
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ clock _ (by simp [helpers,helperCount,leftBase] <;> omega) []]
  simpa only [if_true] using query_eval A (fun _ => true) (grammar A B hm tail) (leftBase n m)
    (left_rule A B hm tail) x s p hp (x.length+1) (by omega) a


theorem right_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (b : Fin m) (p clock : Nat)
    (hp : p ≤ x.length) :
    evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E (rightEntry (n := n) b) p =
      some (some (run B b (sfx x p)).2.length) := by
  rw [rightEntry,call_nil _ _ _ (right_rule A B hm tail b) rfl]
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ clock _ (by simp [helpers,helperCount,rightBase] <;> omega) []]
  simpa only [if_true] using query_eval B (fun _ => true) (grammar A B hm tail) (rightBase n m)
    (right_rule A B hm tail) x s p hp (x.length+1) (by omega) b


theorem common_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (p clock : Nat) (hp : p ≤ x.length) :
    evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E (commonEntry a c b d) p =
      some (if (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d
        then some (common A B a b (sfx x p)).2.length else none) := by
  rw [commonEntry,StatefulScannerFamily.entry,call_nil _ _ _ (common_rule A B hm tail (pack a b) (pack c d)) rfl]
  have hi : helpers n m ((pack c d).val*(n*m)+(pack a b).val) = true := by
    simp only [helpers,helperCount,decide_eq_true_eq]
    have ht := (pack c d).isLt
    have hq := (pack a b).isLt
    have hh := Nat.mul_le_mul_right (n*m) (show (pack c d).val+1 ≤ n*m by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hh
    unfold commonSize
    omega
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ clock _ hi []]
  have hh := query_eval (product A B hm) (fun q => decide (q=pack c d))
    (grammar A B hm tail) ((pack c d).val*(n*m))
    (fun q => common_rule A B hm tail q (pack c d)) x s p hp (x.length+1) (by omega) (pack a b)
  simpa only [run_product,pack_eq_iff hm,decide_eq_true_eq] using hh


theorem arguments_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length)
    (hstate : (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d) :
    evSeqArgs (grammar A B hm tail) x s (frozen A B hm tail x s clock)
      E (arguments a c b d first) p = some (some
        ([pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b first x p)],finalPos A B a b first x p)) := by
  have hcommon : evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
      (commonEntry a c b d) p = some (some (commonPos A B a b x p)) := by
    simpa [hstate,commonPos] using common_eval A B hm tail x s E a c b d p clock hp
  have hbound := common_bound A B a b x p hp
  have hcp : commonPos A B a b x p ≤ x.length := Nat.le_trans hbound hp
  have hs : sfx x (commonPos A B a b x p) = (common A B a b (sfx x p)).2 :=
    sfx_suffix (suffix_trans (sfx_is_suffix x p)
      ⟨_,(common_prefix A B a b (sfx x p)).choose_spec.1⟩).choose_spec
  obtain ⟨hA,hB⟩ := residual_runs A B a b (sfx x p)
  rw [hstate.1] at hA
  rw [hstate.2] at hB
  have hres : evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
      (if first then rightEntry (n := n) d else leftEntry (m := m) c) (commonPos A B a b x p) =
      some (some (finalPos A B a b first x p)) := by
    cases first
    · simp only [Bool.false_eq_true,if_false,finalPos]
      rw [left_eval A B hm tail x s E c _ clock hcp,hs,← hA]
    · simp only [if_true,finalPos]
      rw [right_eval A B hm tail x s E d _ clock hcp,hs,← hB]
  rw [arguments,evSeq_cons_ok hcommon,evSeq_cons_ok hres]
  rfl

theorem caseGuard_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length) :
    evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E (caseGuard A a c b d first) p =
      if GoodCase A B a c b d first (sfx x p) then some (some p) else some none := by
  rw [caseGuard,CallLookahead.evV_peek]
  by_cases hstate : (common A B a b (sfx x p)).1.1=c ∧ (common A B a b (sfx x p)).1.2=d
  · have he : evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
        (commonEntry a c b d) p = some (some (commonPos A B a b x p)) := by
      simpa [hstate,commonPos] using common_eval A B hm tail x s E a c b d p clock hp
    rw [evV_seq_ok he,stopTest_eval,common_suffix]
    have hs : stopped (A.arcs c) (common A B a b (sfx x p)).2 = firstStops A B a b (sfx x p) := by
      rw [← hstate.1]
      rfl
    rw [hs]
    by_cases hf : firstStops A B a b (sfx x p) = first <;>
      simp only [GoodCase,hstate,hf,and_self,if_true,if_false,CallLookahead.peek,and_false]
  · have he : evV (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
        (commonEntry a c b d) p = some none := by
      simpa only [if_neg hstate] using common_eval A B hm tail x s E a c b d p clock hp
    rw [evV_seq_fail he]
    simp [GoodCase,hstate,CallLookahead.peek]

theorem independent_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (p clock : Nat) (hp : p ≤ x.length) :
    evParArgs (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
      [leftEntry (m := m) a,rightEntry (n := n) b] p =
      some (some [pre x p (run A a (sfx x p)).2.length,pre x p (run B b (sfx x p)).2.length]) := by
  rw [evPar_cons_ok (left_eval A B hm tail x s E a p clock hp),
    evPar_cons_ok (right_eval A B hm tail x s E b p clock hp)]
  rfl

theorem capture_reconstruction {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (s : Strategy) (E : List (List Char)) (a c : Fin n) (b d : Fin m)
    (first : Bool) (p clock : Nat) (hp : p ≤ x.length)
    (hgood : GoodCase A B a c b d first (sfx x p)) :
    evParArgs (grammar A B hm tail) x s (frozen A B hm tail x s clock) E
      [leftEntry (m := m) a,rightEntry (n := n) b] p = some (some
        (ScannerFrontier.restore first (pre x p (commonPos A B a b x p))
          (pre x (commonPos A B a b x p) (finalPos A B a b first x p)))) := by
  rw [independent_eval A B hm tail x s E a b p clock hp]
  have he := first_remainder A B a b (sfx x p)
  rw [hgood.2] at he
  have hpre := ScannerFrontier.pre_concat x p (commonPos A B a b x p) (finalPos A B a b first x p)
    hp (common_bound A B a b x p hp) (final_bound A B a b first x p)
  cases first with
  | true =>
    simp only [if_true] at he
    have hh : (run A a (sfx x p)).2.length = commonPos A B a b x p := congrArg List.length he
    change some (some [pre x p (run A a (sfx x p)).2.length,pre x p (run B b (sfx x p)).2.length]) = _
    have hl : finalPos A B a b true x p = (run B b (sfx x p)).2.length := rfl
    rw [hh,← hl,hpre]
    rfl
  | false =>
    simp only [Bool.false_eq_true,if_false] at he
    have hh : (run B b (sfx x p)).2.length = commonPos A B a b x p := congrArg List.length he
    have hl : finalPos A B a b false x p = (run A a (sfx x p)).2.length := rfl
    rw [hh,← hl,hpre]
    rfl


theorem dispatch_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat) (cases : List (Control n m))
    (valid : ∀ control ∈ cases, ∃ r, ruleAtM (grammar A B hm tail).rules (dest control) = some r ∧ r.arity=2)
    (p clock : Nat) (hp : p ≤ x.length)
    (hmem : actual A B a b (sfx x p) ∈ cases) :
    evV (grammar A B hm tail) x .callByValueSeq (frozen A B hm tail x .callByValueSeq clock)
      E (dispatch A a b dest cases) p =
      valAt (frozen A B hm tail x .callByValueSeq clock
        (dest (actual A B a b (sfx x p)))
        [pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p)])
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) := by
  induction cases with
  | nil => cases hmem
  | cons control rest ih =>
    obtain ⟨c,d,first⟩ := control
    rw [dispatch,ScannerFrontier.branch_eval _ _ _ p (decide (GoodCase A B a c b d first (sfx x p)))
      (by simpa only [decide_eq_true_eq] using
        caseGuard_eval A B hm tail x .callByValueSeq E a c b d first p clock hp)]
    simp only [decide_eq_true_eq]
    by_cases hg : GoodCase A B a c b d first (sfx x p)
    · rw [if_pos hg]
      obtain ⟨r,hr,hr2⟩ := valid (c,d,first) (by simp)
      rw [evV_call_seq (args := arguments a c b d first) hr (by
        cases first <;> simpa only [arguments,List.length_cons,List.length_nil] using hr2),
        arguments_eval A B hm tail x .callByValueSeq E a c b d first p clock hp hg.1]
      dsimp only []
      have heq := (goodCase_iff_eq A B a c b d first (sfx x p)).mp hg
      rw [← heq,hg.2]
    · rw [if_neg hg]
      apply ih (fun control h => valid control (by simp [h]))
      rcases List.mem_cons.mp hmem with h | h
      · exact False.elim (hg ((goodCase_iff_eq A B a c b d first (sfx x p)).mpr h.symm))
      · exact h

theorem complete_dispatch_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (dest : Control n m → Nat)
    (valid : ∀ control, ∃ r, ruleAtM (grammar A B hm tail).rules (dest control) = some r ∧ r.arity=2)
    (p clock : Nat) (hp : p ≤ x.length) :
    evV (grammar A B hm tail) x .callByValueSeq (frozen A B hm tail x .callByValueSeq clock)
      E (dispatch A a b dest (controls n m)) p =
      valAt (frozen A B hm tail x .callByValueSeq clock
        (dest (actual A B a b (sfx x p)))
        [pre x p (commonPos A B a b x p),
          pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p)])
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) :=
  dispatch_eval A B hm tail x E a b dest (controls n m) (fun control _ => valid control)
    p clock hp (controls_mem _ _ _)

theorem complete_dispatch_body_eval {n m : Nat} (A : Machine n) (B : Machine m) (hm : 0<m) (tail : List MRule)
    (x : List Char) (E : List (List Char)) (a : Fin n) (b : Fin m)
    (left right : Nat) (e : MExp) (he : e.FirstOrder)
    (hl : ruleAtM (grammar A B hm tail).rules left = some ⟨2,ScannerFrontier.body true e⟩)
    (hr : ruleAtM (grammar A B hm tail).rules right = some ⟨2,ScannerFrontier.body false e⟩)
    (p clock : Nat) (hp : p ≤ x.length)
    (hleft : helperCount n m ≤ left) (hright : helperCount n m ≤ right) :
    evV (grammar A B hm tail) x .callByValueSeq (frozen A B hm tail x .callByValueSeq (clock+1)) E
      (dispatch A a b (fun control => if control.2.2 then left else right) (controls n m)) p =
      evV (grammar A B hm tail) x .callByValueSeq (frozen A B hm tail x .callByValueSeq clock)
        (ScannerFrontier.restore (firstStops A B a b (sfx x p)) (pre x p (commonPos A B a b x p))
          (pre x (commonPos A B a b x p) (finalPos A B a b (firstStops A B a b (sfx x p)) x p))) e
        (finalPos A B a b (firstStops A B a b (sfx x p)) x p) := by
  have valid : ∀ control : Control n m, ∃ r,
      ruleAtM (grammar A B hm tail).rules (if control.2.2 then left else right) = some r ∧ r.arity=2 := by
    intro control
    cases hf : control.2.2
    · exact ⟨_,hr,rfl⟩
    · exact ⟨_,hl,rfl⟩
  rw [complete_dispatch_eval A B hm tail x E a b _ valid p (clock+1) hp]
  have hq : finalPos A B a b (firstStops A B a b (sfx x p)) x p ≤ x.length :=
    Nat.le_trans (final_bound A B a b _ x p) (Nat.le_trans (common_bound A B a b x p hp) hp)
  simp only [actual]
  by_cases hf : firstStops A B a b (sfx x p) = true
  · simp only [hf,if_true] at hq ⊢
    unfold frozen
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ clock left (by simp [helpers]; omega) _ hl _ _ hq]
    exact ScannerFrontier.body_eval _ _ _ _ true _ _ e he _
  · have hfalse : firstStops A B a b (sfx x p) = false := Bool.eq_false_iff.mpr hf
    simp only [hfalse,Bool.false_eq_true,if_false] at hq ⊢
    unfold frozen
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ clock right (by simp [helpers]; omega) _ hr _ _ hq]
    exact ScannerFrontier.body_eval _ _ _ _ false _ _ e he _

end Shallot.MacroPeg.CBV.FrozenPairArguments
