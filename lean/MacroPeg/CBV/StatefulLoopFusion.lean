import MacroPeg.CBV.LoopCaptureSafety

/-! A finite-state consuming prefix absorbs actual argument captures that
return its machine to the initial state. Held values survive the prefix. -/
namespace Shallot.MacroPeg.CBV.StatefulLoopFusion
open StatefulScanner
open LoopCaptureSafety (Loop Environment Safe)
open ClockFreezing (Table)

def Supported {n : Nat} (M : Machine n) (state : Fin n) : MExp → Prop
  | .call i [a] => n≤i ∧ Supported M state a ∧ Safe M state a
  | .seq a b | .alt a b => Supported M state a ∧ Supported M state b
  | .star a | .notP a => Supported M state a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

def grammar {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp) : MGrammar :=
  ⟨block M (fun _ => true) 0 ++ tails.map (fun e => ⟨1,.seq (.call state.val []) e⟩)⟩
def Valid {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp) : Prop :=
  ∀ e∈tails, Supported M state e

theorem supported_firstOrder {n : Nat} (M : Machine n) (state : Fin n) :
    ∀ e, Supported M state e → e.FirstOrder
  | .call _ [a], h => ⟨supported_firstOrder M state a h.2.1,True.intro⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder M state a h.1,supported_firstOrder M state b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder M state a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem helper_rule {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp) (q : Fin n) :
    ruleAtM (grammar M state tails).rules q.val=
      some ⟨0,branches 0 (terminal true) (M.arcs q)⟩ := by
  unfold grammar
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left (by simpa [block_length] using q.isLt)]
  simpa only [ruleAtM_eq_getElem?] using block_rule M (fun _ => true) 0 q

theorem user_rule {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (i : Nat) (hi : n≤i) :
    ruleAtM (grammar M state tails).rules i=
      (tails[i-n]?).map (fun e => ⟨1,.seq (.call state.val []) e⟩) := by
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simpa only [block_length] using hi),block_length,List.getElem?_map]

theorem firstOrder {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (hv : Valid M state tails) : (grammar M state tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact block_firstOrder M (fun _ => true) 0 r hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,supported_firstOrder M state e (hv e he)⟩

def helpers (n i : Nat) : Bool := decide (i<n)
abbrev frozen {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (x : List Char) (s : Strategy) (k : Nat) : Table :=
  ClockFreezing.frozen (grammar M state tails) x s (helpers n) (x.length+1) k

theorem helpers_stable {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows (grammar M state tails) x s (helpers n) (x.length+1) := by
  intro k i hi E
  have hb : i<n := by simpa only [helpers,decide_eq_true_eq] using hi
  have hh := StatefulScannerStability.rows_stable M (fun _ => true) (grammar M state tails) 0
    (fun q => by simpa only [Nat.zero_add] using helper_rule M state tails q)
    x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) ⟨i,hb⟩ E
  simpa only [Nat.zero_add] using hh

theorem scanner_eval {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M state tails) x s (frozen M state tails x s k) E (.call state.val []) p=
      some (some (run M state (sfx x p)).2.length) := by
  have hr := helper_rule M state tails state
  have hc : evV (grammar M state tails) x s (frozen M state tails x s k) E (.call state.val []) p=
      valAt (frozen M state tails x s k state.val []) p := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  rw [hc]
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ k _ (by simp [helpers,state.isLt]) []]
  simpa only [Nat.zero_add,if_true] using query_eval M (fun _ => true) (grammar M state tails) 0
    (fun q => by simpa only [Nat.zero_add] using helper_rule M state tails q)
    x s p hp (x.length+1) (by omega) state

def Shifted {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (x : List Char) (T U : Table) : Prop :=
  ∀ i e, tails[i]?=some e → ∀ w p q, p≤x.length → q≤x.length → Loop M state w →
    sfx x p=w++sfx x q → valAt (T (n+i) [w]) p=valAt (U (n+i) [w]) q

theorem evaluator_of_shift {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (x : List Char) (T U : Table) (hOk : OkTV x.length T) (hShift : Shifted M state tails x T U) :
    ∀ e, Supported M state e → ∀ E, Environment M state E → ∀ p, p≤x.length →
    evV (grammar M state tails) x .callByValuePar T E e p=
      evV (grammar M state tails) x .callByValueSeq U E e p
  | .call i [a], he, E, hE, p, hp => by
    cases hr : tails[i-n]? with
    | none => simp only [evV,user_rule M state tails i he.1,hr,Option.map_none]
    | some body =>
      have hg : ruleAtM (grammar M state tails).rules i=some ⟨1,.seq (.call state.val []) body⟩ := by
        rw [user_rule M state tails i he.1,hr]; rfl
      rw [evV_call_par hg rfl (by decide),evV_call_seq hg rfl]
      have ha := evaluator_of_shift M state tails x T U hOk hShift a he.2.1 E hE p hp
      simp only [evParArgs,evSeqArgs]
      rw [←ha]
      cases ha' : evV (grammar M state tails) x .callByValuePar T E a p with
      | none => rfl
      | some r => cases r with
        | none => rfl
        | some q =>
          have hq := evV_ok hOk a p hp q ha'
          obtain ⟨hqp,w,hw,hs⟩ := LoopCaptureSafety.suffix_shape M state _ x .callByValuePar T E hE a he.2.2 p q hp ha'
          have hpw : pre x p q=w := by
            simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) hs
          have hh := hShift (i-n) body hr w p q hp hq hw hs
          simpa only [Nat.add_sub_of_le he.1,hpw] using hh
  | .seq a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift M state tails x T U hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar M state tails) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_shift M state tails x T U hOk hShift b he.2 E hE q (evV_ok hOk a p hp q hv)
  | .alt a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift M state tails x T U hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar M state tails) x .callByValuePar T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_shift M state tails x T U hOk hShift b he.2 E hE p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, he, E, hE, p, hp =>
    evStar_congr p (fun q hq => evaluator_of_shift M state tails x T U hOk hShift a he E hE q (by omega))
  | .notP a, he, E, hE, p, hp => by
    simp only [evV]
    rw [evaluator_of_shift M state tails x T U hOk hShift a he E hE p hp]
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _ | .range _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ => rfl
  | .call _ [], h, _, _, _, _ | .call _ (_::_::_), h, _, _, _, _ | .dbg _, h, _, _, _, _
  | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem tables_shifted {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (hv : Valid M state tails) (x : List Char) : ∀ k,
    Shifted M state tails x (frozen M state tails x .callByValuePar k) (frozen M state tails x .callByValueSeq k)
  | 0 => by
    intro i e hi w p q hp hq hw hs
    simp only [frozen,ClockFreezing.frozen,helpers,show decide (n+i<n)=false from by simp,Bool.false_eq_true,ite_false,valAt_nil]
  | k+1 => by
    intro i e hi w p q hp hq hw hs
    have hr : ruleAtM (grammar M state tails).rules (n+i)=some ⟨1,.seq (.call state.val []) e⟩ := by
      rw [user_rule M state tails (n+i) (by omega),Nat.add_sub_cancel_left,hi]; rfl
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers]) _ hr [w] p hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers]) _ hr [w] q hq]
    have habs : run M state (sfx x p)=run M state (sfx x q) := by
      rw [hs,run_after_prefix M w (sfx x q) state state hw]
    rw [evV_seq_ok (scanner_eval M state tails x .callByValuePar k p [w] hp),
      evV_seq_ok (scanner_eval M state tails x .callByValueSeq k q [w] hq),habs]
    have hz : (run M state (sfx x q)).2.length≤x.length :=
      Nat.le_trans (run_length M state _) (by rw [length_sfx x hq]; exact hq)
    exact evaluator_of_shift M state tails x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
      (tables_shifted M state tails hv x k) e (hv e (List.mem_of_getElem? hi)) [w]
      (by intro v h; simp only [List.mem_singleton] at h; subst v; exact hw) _ hz

theorem evaluator_eq {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (hv : Valid M state tails) (e : MExp) (he : Supported M state e) (x : List Char) (k : Nat) :
    evV (grammar M state tails) x .callByValuePar (frozen M state tails x .callByValuePar k) [] e x.length=
    evV (grammar M state tails) x .callByValueSeq (frozen M state tails x .callByValueSeq k) [] e x.length :=
  evaluator_of_shift M state tails x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (tables_shifted M state tails hv x k) e he [] (by simp [Environment]) x.length (Nat.le_refl _)

theorem observations_iff {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (hv : Valid M state tails) (e : MExp) (he : Supported M state e) (x : List Char) (rest : Option (List Char)) :
    SObs (grammar M state tails) .callByValuePar e x rest ↔ SObs (grammar M state tails) .callByValueSeq e x rest := by
  rw [ClockFreezing.observations_iff (firstOrder M state tails hv) x .callByValuePar (by decide)
      (helpers n) (x.length+1) (helpers_stable M state tails x .callByValuePar) e (supported_firstOrder M state e he),
    ClockFreezing.observations_iff (firstOrder M state tails hv) x .callByValueSeq (by decide)
      (helpers n) (x.length+1) (helpers_stable M state tails x .callByValueSeq) e (supported_firstOrder M state e he)]
  exact exists_congr (fun k => exists_congr (fun v => by rw [evaluator_eq M state tails hv e he x k]))

theorem language_translation {n : Nat} (M : Machine n) (state : Fin n) (tails : List MExp)
    (hv : Valid M state tails) (e : MExp) (he : Supported M state e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (grammar M state tails) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨grammar M state tails,e,firstOrder M state tails hv,supported_firstOrder M state e he,
    fun x => observations_iff M state tails hv e he x (some [])⟩

end Shallot.MacroPeg.CBV.StatefulLoopFusion
