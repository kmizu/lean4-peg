import MacroPeg.CBV.CaptureActionSafety

/-! A capture action determines the target scanner resumption state.
State-changing captures retain their whole value through consuming prefixes. -/
namespace Shallot.MacroPeg.CBV.StatefulActionFusion
open StatefulScanner
open CaptureActionSafety (Profile Typed Accurate action identity)
open ClockFreezing (Table)

structure Spec (n : Nat) where
  capture : Profile n
  tail : MExp

def resume {n : Nat} (state : Fin n) (r : Spec n) : Fin n := (r.capture state).getD state
def header {n : Nat} (state : Fin n) (par : Bool) (r : Spec n) : Fin n :=
  if par then state else resume state r

def Supported {n : Nat} (M : Machine n) (specs : List (Spec n)) (parent : Profile n) : MExp → Prop
  | .call i [a] => n≤i ∧ Supported M specs parent a ∧
      (match specs[i-n]? with | none => True | some r => CaptureActionSafety.fits M parent a r.capture=true)
  | .seq a b | .alt a b => Supported M specs parent a ∧ Supported M specs parent b
  | .star a | .notP a => Supported M specs parent a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

def grammar {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n)) : MGrammar :=
  ⟨block M (fun _ => true) 0 ++ specs.map (fun r => ⟨1,.seq (.call (header state par r).val []) r.tail⟩)⟩
def Valid {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n)) : Prop :=
  ∀ r∈specs, r.capture state≠none ∧ Supported M specs r.capture r.tail

theorem supported_firstOrder {n : Nat} (M : Machine n) (specs : List (Spec n)) (parent : Profile n) :
    ∀ e, Supported M specs parent e → e.FirstOrder
  | .call _ [a], h => ⟨supported_firstOrder M specs parent a h.2.1,True.intro⟩
  | .seq a b, h | .alt a b, h => ⟨supported_firstOrder M specs parent a h.1,supported_firstOrder M specs parent b h.2⟩
  | .star a, h | .notP a, h => supported_firstOrder M specs parent a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ [], h | .call _ (_::_::_), h | .dbg _, h | .lam _ _, h
  | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem helper_rule {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n)) (q : Fin n) :
    ruleAtM (grammar M state par specs).rules q.val=
      some ⟨0,branches 0 (terminal true) (M.arcs q)⟩ := by
  unfold grammar
  rw [ruleAtM_eq_getElem?,List.getElem?_append_left (by simpa [block_length] using q.isLt)]
  simpa only [ruleAtM_eq_getElem?] using block_rule M (fun _ => true) 0 q

theorem user_rule {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n))
    (i : Nat) (hi : n≤i) :
    ruleAtM (grammar M state par specs).rules i=
      (specs[i-n]?).map (fun r => ⟨1,.seq (.call (header state par r).val []) r.tail⟩) := by
  simp only [grammar,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_right (by simpa only [block_length] using hi),block_length,List.getElem?_map]

theorem firstOrder {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n))
    (hv : Valid M state specs) : (grammar M state par specs).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact block_firstOrder M (fun _ => true) 0 r hr
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,supported_firstOrder M specs u.capture u.tail (hv u hu).2⟩

def helpers (n i : Nat) : Bool := decide (i<n)
abbrev frozen {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n))
    (x : List Char) (s : Strategy) (k : Nat) : Table :=
  ClockFreezing.frozen (grammar M state par specs) x s (helpers n) (x.length+1) k

theorem helpers_stable {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n))
    (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows (grammar M state par specs) x s (helpers n) (x.length+1) := by
  intro k i hi E
  have hb : i<n := by simpa only [helpers,decide_eq_true_eq] using hi
  have hh := StatefulScannerStability.rows_stable M (fun _ => true) (grammar M state par specs) 0
    (fun q => by simpa only [Nat.zero_add] using helper_rule M state par specs q)
    x s (x.length+1+k) (x.length+1) (by omega) (Nat.le_refl _) ⟨i,hb⟩ E
  simpa only [Nat.zero_add] using hh

theorem scanner_eval {n : Nat} (M : Machine n) (state : Fin n) (par : Bool) (specs : List (Spec n))
    (q : Fin n) (x : List Char) (s : Strategy) (k p : Nat) (E : List (List Char)) (hp : p≤x.length) :
    evV (grammar M state par specs) x s (frozen M state par specs x s k) E (.call q.val []) p=
      some (some (run M q (sfx x p)).2.length) := by
  have hr := helper_rule M state par specs q
  have hc : evV (grammar M state par specs) x s (frozen M state par specs x s k) E (.call q.val []) p=
      valAt (frozen M state par specs x s k q.val []) p := by
    cases s <;> simp [evV,hr,evParArgs,evSeqArgs]
  rw [hc]
  unfold frozen
  rw [ClockFreezing.frozen_rows _ _ _ _ _ k _ (by simp [helpers,q.isLt]) []]
  simpa only [Nat.zero_add,if_true] using query_eval M (fun _ => true) (grammar M state par specs) 0
    (fun q => by simpa only [Nat.zero_add] using helper_rule M state par specs q)
    x s p hp (x.length+1) (by omega) q

def Shifted {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n))
    (x : List Char) (T U : Table) : Prop :=
  ∀ i r, specs[i]?=some r → ∀ w p q, p≤x.length → q≤x.length → action M w=r.capture →
    sfx x p=w++sfx x q → valAt (T (n+i) [w]) p=valAt (U (n+i) [w]) q

theorem evaluator_of_shift {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n)) (parent : Profile n)
    (x : List Char) (T U : Table) (hOk : OkTV x.length T) (hShift : Shifted M state specs x T U) :
    ∀ e, Supported M specs parent e → ∀ E, Accurate M parent E → ∀ p, p≤x.length →
    evV (grammar M state true specs) x .callByValuePar T E e p=
      evV (grammar M state false specs) x .callByValueSeq U E e p
  | .call i [a], he, E, hE, p, hp => by
    cases hr : specs[i-n]? with
    | none => simp only [evV,user_rule M state true specs i he.1,user_rule M state false specs i he.1,hr,Option.map_none]
    | some r =>
      have hg (par : Bool) : ruleAtM (grammar M state par specs).rules i=
          some ⟨1,.seq (.call (header state par r).val []) r.tail⟩ := by
        rw [user_rule M state par specs i he.1,hr]; rfl
      rw [evV_call_par (hg true) rfl (by decide),evV_call_seq (hg false) rfl]
      have ha := evaluator_of_shift M state specs parent x T U hOk hShift a he.2.1 E hE p hp
      simp only [evParArgs,evSeqArgs]
      rw [←ha]
      cases ha' : evV (grammar M state true specs) x .callByValuePar T E a p with
      | none => rfl
      | some v => cases v with
        | none => rfl
        | some q =>
          have hq := evV_ok hOk a p hp q ha'
          have ht : Typed M parent a r.capture := CaptureActionSafety.fits_sound M parent a r.capture
            (by simpa only [hr] using he.2.2)
          obtain ⟨hw,hs⟩ := CaptureActionSafety.capture_action M parent _ x .callByValuePar T E hE ht p q hp ha'
          have hh := hShift (i-n) r hr (pre x p q) p q hp hq hw hs
          simpa only [Nat.add_sub_of_le he.1] using hh
  | .seq a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift M state specs parent x T U hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar M state true specs) x .callByValuePar T E a p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some r => cases r with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_shift M state specs parent x T U hOk hShift b he.2 E hE q (evV_ok hOk a p hp q hv)
  | .alt a b, he, E, hE, p, hp => by
    have ha := evaluator_of_shift M state specs parent x T U hOk hShift a he.1 E hE p hp
    cases hv : evV (grammar M state true specs) x .callByValuePar T E a p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some r => cases r with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_shift M state specs parent x T U hOk hShift b he.2 E hE p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, he, E, hE, p, hp =>
    evStar_congr p (fun q hq => evaluator_of_shift M state specs parent x T U hOk hShift a he E hE q (by omega))
  | .notP a, he, E, hE, p, hp => by
    simp only [evV]
    rw [evaluator_of_shift M state specs parent x T U hOk hShift a he E hE p hp]
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _ | .range _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ => rfl
  | .call _ [], h, _, _, _, _ | .call _ (_::_::_), h, _, _, _, _ | .dbg _, h, _, _, _, _
  | .lam _ _, h, _, _, _, _ | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => False.elim h

theorem tables_shifted {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n))
    (hv : Valid M state specs) (x : List Char) : ∀ k,
    Shifted M state specs x (frozen M state true specs x .callByValuePar k)
      (frozen M state false specs x .callByValueSeq k)
  | 0 => by
    intro i r hi w p q hp hq hw hs
    simp only [frozen,ClockFreezing.frozen,helpers,show decide (n+i<n)=false from by simp,
      Bool.false_eq_true,ite_false,valAt_nil]
  | k+1 => by
    intro i r hi w p q hp hq hw hs
    have hr (par : Bool) : ruleAtM (grammar M state par specs).rules (n+i)=
        some ⟨1,.seq (.call (header state par r).val []) r.tail⟩ := by
      rw [user_rule M state par specs (n+i) (by omega),Nat.add_sub_cancel_left,hi]; rfl
    rw [ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers]) _ (hr true) [w] p hp,
      ClockFreezing.frozen_user_step _ _ _ _ _ k _ (by simp [helpers]) _ (hr false) [w] q hq]
    have hcap : advance M state w=some (resume state r) := by
      have hh := congrFun hw state
      change advance M state w=r.capture state at hh
      rw [hh]
      cases he : r.capture state with
      | none => exact False.elim ((hv r (List.mem_of_getElem? hi)).1 he)
      | some t => simp only [resume,he,Option.getD_some]
    have habs : run M state (sfx x p)=run M (resume state r) (sfx x q) := by
      rw [hs,run_after_prefix M w (sfx x q) state (resume state r) hcap]
    simp only [header,ite_true,Bool.false_eq_true,ite_false]
    rw [evV_seq_ok (scanner_eval M state true specs state x .callByValuePar k p [w] hp),
      evV_seq_ok (scanner_eval M state false specs (resume state r) x .callByValueSeq k q [w] hq),habs]
    have hz : (run M (resume state r) (sfx x q)).2.length≤x.length :=
      Nat.le_trans (run_length M (resume state r) _) (by rw [length_sfx x hq]; exact hq)
    exact evaluator_of_shift M state specs r.capture x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
      (tables_shifted M state specs hv x k) r.tail (hv r (List.mem_of_getElem? hi)).2 [w]
      (by intro v h; have he : w=v := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using h
          subst v; exact hw) _ hz

theorem evaluator_eq {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n))
    (hv : Valid M state specs) (parent : Profile n) (e : MExp) (he : Supported M specs parent e)
    (x : List Char) (k : Nat) :
    evV (grammar M state true specs) x .callByValuePar (frozen M state true specs x .callByValuePar k) [] e x.length=
    evV (grammar M state false specs) x .callByValueSeq (frozen M state false specs x .callByValueSeq k) [] e x.length :=
  evaluator_of_shift M state specs parent x _ _ (ClockFreezing.frozen_ok _ _ _ _ _ k)
    (tables_shifted M state specs hv x k) e he [] (by intro w h; cases h) x.length (Nat.le_refl _)

theorem observations_iff {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n))
    (hv : Valid M state specs) (parent : Profile n) (e : MExp) (he : Supported M specs parent e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (grammar M state true specs) .callByValuePar e x rest ↔
      SObs (grammar M state false specs) .callByValueSeq e x rest := by
  rw [ClockFreezing.observations_iff (firstOrder M state true specs hv) x .callByValuePar (by decide)
      (helpers n) (x.length+1) (helpers_stable M state true specs x .callByValuePar) e (supported_firstOrder M specs parent e he),
    ClockFreezing.observations_iff (firstOrder M state false specs hv) x .callByValueSeq (by decide)
      (helpers n) (x.length+1) (helpers_stable M state false specs x .callByValueSeq) e (supported_firstOrder M specs parent e he)]
  exact exists_congr (fun k => exists_congr (fun v => by rw [evaluator_eq M state specs hv parent e he x k]))

theorem language_translation {n : Nat} (M : Machine n) (state : Fin n) (specs : List (Spec n))
    (hv : Valid M state specs) (parent : Profile n) (e : MExp) (he : Supported M specs parent e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
    SObs (grammar M state true specs) .callByValuePar e x (some []) ↔ SObs g .callByValueSeq start x (some []) :=
  ⟨grammar M state false specs,e,firstOrder M state false specs hv,supported_firstOrder M specs parent e he,
    fun x => observations_iff M state specs hv parent e he x (some [])⟩

end Shallot.MacroPeg.CBV.StatefulActionFusion
