import MacroPeg.CBV.RecursiveCaptureSafety
import MacroPeg.CBV.ObservedScannerDispatch

namespace Shallot.MacroPeg.CBV.ParameterizedCaptureSafety
open TotalCaptureSafety (Total Environment total_nil total_append wordCheck wordCheck_sound)
open ClockFreezing (Table)
open StatefulScanner (Machine)

/-- Every consuming argument and callee body must preserve the scanner
frontier. Queries need no termination condition. Calls may have any arity. -/
def check {n : Nat} (M : StatefulScanner.Machine n) (size : Nat) : MExp → Bool
  | .eps | .notP _ | .param _ => true
  | .lit w => wordCheck M w
  | .seq a b | .alt a b => check M size a && check M size b
  | .star a => check M size a
  | .call i args => decide (i<size) && args.attach.all (fun a => check M size a.val)
  | _ => false
termination_by e => sizeOf e
decreasing_by all_goals simp_wf; all_goals first | omega | exact Nat.lt_trans (List.sizeOf_lt_of_mem a.property) (by simp; omega)

abbrev Safe {n : Nat} (M : StatefulScanner.Machine n) (size : Nat) (e : MExp) := check M size e=true

/-- The invariant quantifies over actual retained values, including all
new argument captures; no row result is supplied to the final theorem. -/
def Rows {n : Nat} (M : StatefulScanner.Machine n) (size : Nat) (x : List Char) (T : Table) : Prop :=
  ∀ i, i<size → ∀ E, Environment M E → ∀ p q, p≤x.length →
    valAt (T i E) p=some (some q) →
    q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q

/-- Actual captured prefixes are determined by the suffix endpoints. -/
theorem capture_of_shape {n : Nat} (M : StatefulScanner.Machine n) (x : List Char)
    (p q : Nat) (hp : p≤x.length)
    (h : q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q := by
  obtain ⟨hqp,w,hw,hs⟩ := h
  have he : pre x p q=w := by
    simpa only [length_sfx x hp,length_sfx x (Nat.le_trans hqp hp)] using
      pre_eq (sfx_is_suffix x p) hs
  exact ⟨he.symm ▸ hw,he.symm ▸ hs⟩

/-- Parallel argument captures retain the same caller position. -/
theorem par_arguments {n : Nat} (M : StatefulScanner.Machine n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (args : List MExp)
    (hArgs : ∀ a∈args, ∀ p q, p≤x.length → evV g x s T E a p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q)
    (p : Nat) (hp : p≤x.length) (W : List (List Char))
    (h : evParArgs g x s T E args p=some (some W)) : Environment M W := by
  induction args generalizing W with
  | nil =>
    have he : W=[] := by simpa [evParArgs] using h.symm
    subst W
    intro w hw; cases hw
  | cons a args ih =>
    cases ha : evV g x s T E a p with
    | none => simp [evParArgs,ha] at h
    | some v => cases v with
      | none => simp [evParArgs,ha] at h
      | some j =>
        cases ht : evParArgs g x s T E args p with
        | none => simp [evParArgs,ha,ht] at h
        | some v => cases v with
          | none => simp [evParArgs,ha,ht] at h
          | some V =>
            have he : pre x p j::V=W := by simpa [evParArgs,ha,ht] using h
            subst W
            have hc := (capture_of_shape M x p j hp (hArgs a (by simp) p j hp ha)).1
            have hv := ih (fun b hb => hArgs b (by simp [hb])) V ht
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hw
            · exact hc
            · exact hv w hw

/-- Sequential captures additionally consume a safe whole prefix before
the callee starts. Every argument still evaluates in the original E. -/
theorem seq_arguments {n : Nat} (M : StatefulScanner.Machine n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char))
    (args : List MExp)
    (hArgs : ∀ a∈args, ∀ p q, p≤x.length → evV g x s T E a p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q)
    (p j : Nat) (hp : p≤x.length) (W : List (List Char))
    (h : evSeqArgs g x s T E args p=some (some (W,j))) :
    Environment M W ∧ j≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x j := by
  induction args generalizing p j W with
  | nil =>
    have he : ([],p)=(W,j) := by simpa [evSeqArgs] using h
    cases he
    refine ⟨?_, Nat.le_refl _, [],total_nil M,rfl⟩
    intro w hw; cases hw
  | cons a args ih =>
    cases ha : evV g x s T E a p with
    | none => simp [evSeqArgs,ha] at h
    | some v => cases v with
      | none => simp [evSeqArgs,ha] at h
      | some k =>
        cases ht : evSeqArgs g x s T E args k with
        | none => simp [evSeqArgs,ha,ht] at h
        | some v => cases v with
          | none => simp [evSeqArgs,ha,ht] at h
          | some pair =>
            obtain ⟨V,l⟩ := pair
            have he : (pre x p k::V,l)=(W,j) := by simpa [evSeqArgs,ha,ht] using h
            have hW := congrArg Prod.fst he
            have hj := congrArg Prod.snd he
            dsimp only [Prod.fst,Prod.snd] at hW hj
            subst W
            subst j
            have hs := hArgs a (by simp) p k hp ha
            have hc := (capture_of_shape M x p k hp hs).1
            obtain ⟨hV,hl,v,hv,hsv⟩ := ih (fun b hb => hArgs b (by simp [hb])) k l
              (Nat.le_trans hs.1 hp) V ht
            obtain ⟨hkp,u,hu,hsu⟩ := hs
            refine ⟨?_,Nat.le_trans hl hkp,u++v,total_append M u v hu hv,?_⟩
            · intro w hw
              rcases List.mem_cons.mp hw with rfl | hw
              · exact hc
              · exact hV w hw
            · rw [hsu,hsv,List.append_assoc]

private theorem literal_shape (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (w : List Char) (p q : Nat) (hp : p≤x.length)
    (hv : evV g x s T E (.lit w) p=some (some q)) :
    q≤p ∧ sfx x p=w++sfx x q := by
  cases hs : Shallot.stripPrefix? w (sfx x p) with
  | none => simp [evV,hs] at hv
  | some rest =>
    have hq : rest.length=q := by simpa only [evV,hs,Option.some.injEq] using hv
    have hh := (CBVtoCBN.stripPrefix_exact w (sfx x p) rest).mp hs
    have hr : sfx x rest.length=rest :=
      sfx_suffix (suffix_trans (sfx_is_suffix x p) ⟨w,hh⟩).choose_spec
    have hl := congrArg List.length hh
    rw [length_sfx x hp,List.length_append] at hl
    exact ⟨by omega,by rw [←hq,hr]; exact hh⟩

/-- Successful evaluation derives an actual frontier-safe captured word. -/
theorem suffix_shape {n : Nat} (M : Machine n)
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (hE : Environment M E)
    (size : Nat) (hRows : Rows M size x T) :
    ∀ e, Safe M size e → ∀ p q, p≤x.length →
      evV g x s T E e p=some (some q) →
      q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q
  | .eps, _, p, q, hp, h => by
    have hq : p=q := by simpa only [evV,if_pos hp,Option.some.injEq] using h
    subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .lit w, hw, p, q, hp, h => by
    have hw := wordCheck_sound M w (by simpa only [Safe,check] using hw)
    obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp h
    exact ⟨hq,w,hw,hs⟩
  | .param k, _, p, q, hp, h => by
    cases hw : E[k]? with
    | none => simp [evV,hw] at h
    | some w =>
      have hl : evV g x s T E (.lit w) p=some (some q) := by
        simpa only [evV,hw] using h
      obtain ⟨hq,hs⟩ := literal_shape g x s T E w p q hp hl
      exact ⟨hq,w,hE w (List.mem_of_getElem? hw),hs⟩
  | .notP a, _, p, q, hp, h => by
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | some j => simp [evV,ha] at h
      | none =>
        have hq : p=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
  | .seq a b, he, p, q, hp, h => by
    have he := Bool.and_eq_true_iff.mp (show (check M size a && check M size b)=true from by simpa only [Safe,check] using he)
    cases ha : evV g x s T E a p with
    | none => rw [evV_seq_none ha] at h; cases h
    | some v => cases v with
      | none => rw [evV_seq_fail ha] at h; cases h
      | some j =>
        rw [evV_seq_ok ha] at h
        obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE size hRows a he.1 p j hp ha
        obtain ⟨hqj,v,hv,ht⟩ := suffix_shape M g x s T E hE size hRows b he.2 j q (Nat.le_trans hjp hp) h
        exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
  | .alt a b, he, p, q, hp, h => by
    have he := Bool.and_eq_true_iff.mp (show (check M size a && check M size b)=true from by simpa only [Safe,check] using he)
    cases ha : evV g x s T E a p with
    | none => simp [evV,ha] at h
    | some v => cases v with
      | none => exact suffix_shape M g x s T E hE size hRows b he.2 p q hp (by simpa only [evV,ha] using h)
      | some j =>
        have hj : j=q := by simpa only [evV,ha,Option.some.injEq] using h
        subst q; exact suffix_shape M g x s T E hE size hRows a he.1 p j hp ha
  | .star a, he, p, q, hp, h => by
    have he : Safe M size a := by simpa only [Safe,check] using he
    have hh : ∀ p q, p≤x.length → evStar (fun z => evV g x s T E a z) p=some (some q) →
        q≤p ∧ ∃ w, Total M w ∧ sfx x p=w++sfx x q := by
      intro p
      induction p using Nat.strongRecOn with
      | ind p ih =>
        intro q hp h
        cases ha : evV g x s T E a p with
        | none => rw [evStar_none ha] at h; cases h
        | some v => cases v with
          | none =>
            rw [evStar_fail ha] at h
            have hq : p=q := by simpa using h
            subst q; exact ⟨Nat.le_refl _,[],total_nil M,rfl⟩
          | some j =>
            by_cases hj : j<p
            · rw [evStar_ok ha hj] at h
              obtain ⟨hjp,u,hu,hs⟩ := suffix_shape M g x s T E hE size hRows a he p j hp ha
              obtain ⟨hqj,v,hv,ht⟩ := ih j hj q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
            · rw [evStar_stuck ha hj] at h; cases h
    exact hh p q hp h
  | .call i args, he, p, q, hp, h => by
    have he : (decide (i<size) && args.attach.all (fun a => check M size a.val))=true := by
      simpa only [Safe,check] using he
    have hi : i<size := of_decide_eq_true (Bool.and_eq_true_iff.mp he).1
    have hArgs : ∀ a∈args, Safe M size a := by
      intro a ha
      exact (List.all_eq_true.mp (Bool.and_eq_true_iff.mp he).2) ⟨a,ha⟩ (by simp)
    have hArgShape := fun a ha => suffix_shape M g x s T E hE size hRows a (hArgs a ha)
    cases hr : ruleAtM g.rules i with
    | none => simp [evV,hr] at h
    | some r =>
      by_cases hn : r.arity=args.length
      · by_cases hs : s=.callByValueSeq
        · subst s
          rw [evV_call_seq hr hn] at h
          cases hv : evSeqArgs g x .callByValueSeq T E args p with
          | none => simp [hv] at h
          | some v => cases v with
            | none => simp [hv] at h
            | some pair =>
              obtain ⟨W,j⟩ := pair
              simp only [hv] at h
              obtain ⟨hW,hjp,u,hu,hs⟩ := seq_arguments M g x .callByValueSeq T E args hArgShape p j hp W hv
              obtain ⟨hqj,v,hv,ht⟩ := hRows i hi W hW j q (Nat.le_trans hjp hp) h
              exact ⟨Nat.le_trans hqj hjp,u++v,total_append M u v hu hv,by rw [hs,ht,List.append_assoc]⟩
        · rw [evV_call_par hr hn hs] at h
          cases hv : evParArgs g x s T E args p with
          | none => simp [hv] at h
          | some v => cases v with
            | none => simp [hv] at h
            | some W =>
              simp only [hv] at h
              exact hRows i hi W (par_arguments M g x s T E args hArgShape p hp W hv) p q hp h
      · simp [evV,hr,hn] at h
  | .chr _, h, _, _, _, _ | .any, h, _, _, _, _ | .range _ _, h, _, _, _, _
  | .dbg _, h, _, _, _, _ | .lam _ _, h, _, _, _, _
  | .callParam _ _, h, _, _, _, _ | .invoke _ _ _, h, _, _, _, _ => by simp only [Safe,check,Bool.false_eq_true] at h
termination_by e => sizeOf e

/-- Checked actual rules may be mutually recursive and have different
arities. No successful-evaluation or termination oracle is required. -/
def Checked {n : Nat} (M : StatefulScanner.Machine n) (g : MGrammar) : Prop :=
  ∀ i r, ruleAtM g.rules i=some r → Safe M g.rules.length r.body

def grammarCheck {n : Nat} (M : Machine n) (g : MGrammar) : Bool :=
  g.rules.all (fun r => check M g.rules.length r.body)

theorem grammarCheck_sound {n : Nat} (M : Machine n) (g : MGrammar)
    (h : grammarCheck M g=true) : Checked M g := by
  intro i r hr
  rw [ruleAtM_eq_getElem?] at hr
  exact (List.all_eq_true.mp h) r (List.mem_of_getElem? hr)

theorem physical_rows {n : Nat} (M : StatefulScanner.Machine n) (g : MGrammar)
    (hg : Checked M g) (x : List Char) (s : Strategy) (k : Nat) :
    Rows M g.rules.length x (tblV g x s k) := by
  induction k with
  | zero => intro i hi E hE p q hp h; simp [tblV,valAt_nil] at h
  | succ k ih =>
    intro i hi E hE p q hp h
    cases hr : ruleAtM g.rules i with
    | none => simp [tblV,hr,valAt_nil] at h
    | some r =>
      rw [valAt_tblV_succ hr E hp] at h
      exact suffix_shape M g x s _ E hE g.rules.length ih r.body (hg i r hr) p q hp h

theorem capture {n : Nat} (M : StatefulScanner.Machine n) (g : MGrammar)
    (hg : Checked M g) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (e : MExp)
    (he : Safe M g.rules.length e) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture_of_shape M x p q hp (suffix_shape M g x s _ E hE g.rules.length
    (physical_rows M g hg x s k) e he p q hp h)

/-- Frozen analysis uses only real physical rows for selected rules and
actual evaluator steps for the others, so the same capture invariant holds
without a stabilization or termination assumption. -/
theorem frozen_rows {n : Nat} (M : Machine n) (g : MGrammar)
    (hg : Checked M g) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) : Rows M g.rules.length x (ClockFreezing.frozen g x s pick floor k) := by
  induction k with
  | zero =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · simp only [ClockFreezing.frozen,hb,if_true] at h
      exact physical_rows M g hg x s floor i hi E hE p q hp h
    · simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,valAt_nil] at h
      cases h
  | succ k ih =>
    intro i hi E hE p q hp h
    by_cases hb : pick i=true
    · rw [ClockFreezing.frozen_rows g x s pick floor (k+1) i hb E] at h
      exact physical_rows M g hg x s floor i hi E hE p q hp h
    · simp only [ClockFreezing.frozen,hb,Bool.false_eq_true,if_false,ClockFreezing.step] at h
      cases hr : ruleAtM g.rules i with
      | none => simp [hr,valAt_nil] at h
      | some r =>
        simp only [hr,valAt_rangeMap,if_pos hp] at h
        exact suffix_shape M g x s _ E hE g.rules.length ih r.body (hg i r hr) p q hp h

theorem frozen_capture {n : Nat} (M : Machine n) (g : MGrammar)
    (hg : grammarCheck M g=true) (x : List Char) (s : Strategy) (pick : Nat → Bool)
    (floor k : Nat) (E : List (List Char)) (hE : Environment M E) (e : MExp)
    (he : check M g.rules.length e=true) (p q : Nat) (hp : p≤x.length)
    (h : evV g x s (ClockFreezing.frozen g x s pick floor k) E e p=some (some q)) :
    Total M (pre x p q) ∧ sfx x p=pre x p q++sfx x q :=
  capture_of_shape M x p q hp (suffix_shape M g x s _ E hE g.rules.length
    (frozen_rows M g (grammarCheck_sound M g hg) x s pick floor k) e he p q hp h)

/-- A finite actual grammar check derives safety for a parameterized
capture and advances both real scanner and total observer across it. -/
theorem observed_resumption {n : Nat} (M : Machine n) (g : MGrammar)
    (hg : grammarCheck M g=true) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (e : MExp)
    (he : check M g.rules.length e=true) (p j : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E e p=some (some j))
    (D : RegularCaptureProduct.Machine) (hD : D.Valid) (q : Fin n) (a : Fin D.width) :
    ∃ r, StatefulScanner.advance M q (pre x p j)=some r ∧
      StatefulScanner.run (ObservedScanner.machine M D hD) (StatefulScannerProduct.pack q a) (sfx x p)=
        StatefulScanner.run (ObservedScanner.machine M D hD)
          (StatefulScannerProduct.pack r (ObservedScanner.finish D hD a (pre x p j))) (sfx x j) := by
  obtain ⟨hw,hs⟩ := capture M g (grammarCheck_sound M g hg) x s k E hE e he p j hp h
  cases ht : StatefulScanner.advance M q (pre x p j) with
  | none => exact False.elim (hw q ht)
  | some r =>
    exact ⟨r,rfl,by rw [hs]; exact ObservedScanner.residual_run M D hD q r a _ _ ht⟩

/-- An actual parameterized capture in one grammar hands off to real
relocated scanner/observer rules in another grammar. The clocks, strategies,
retained environments and later continuation are independent. -/
theorem physical_dispatch_resumption {n : Nat} (M : Machine n) (g : MGrammar)
    (hg : grammarCheck M g=true) (x : List Char) (s : Strategy) (k : Nat)
    (E : List (List Char)) (hE : Environment M E) (e : MExp)
    (he : check M g.rules.length e=true) (p j : Nat) (hp : p≤x.length)
    (h : evV g x s (tblV g x s k) E e p=some (some j))
    (D : RegularCaptureProduct.Machine) (hD : D.Valid) (q : Fin n) (a : Fin D.width)
    (before extra : List MRule) (t : Strategy) (clock : Nat) (hclock : p+1≤clock)
    (F : List (List Char)) (K : Fin (n*D.width) → MExp) :
    ∃ r, StatefulScanner.advance M q (pre x p j)=some r ∧
      evV (ObservedScannerDispatch.grammar M D hD before extra) x t
        (tblV (ObservedScannerDispatch.grammar M D hD before extra) x t clock) F
        (ObservedScannerDispatch.dispatch before.length q a K) p=
      evV (ObservedScannerDispatch.grammar M D hD before extra) x t
        (tblV (ObservedScannerDispatch.grammar M D hD before extra) x t clock) F
        (ObservedScannerDispatch.dispatch before.length r (ObservedScanner.finish D hD a (pre x p j)) K) j := by
  have hshape := suffix_shape M g x s _ E hE g.rules.length
    (physical_rows M g (grammarCheck_sound M g hg) x s k) e he p j hp h
  obtain ⟨hw,hs⟩ := capture_of_shape M x p j hp hshape
  cases ht : StatefulScanner.advance M q (pre x p j) with
  | none => exact False.elim (hw q ht)
  | some r =>
    exact ⟨r,rfl,ObservedScannerDispatch.dispatch_handoff M D hD before extra q r a
      (pre x p j) x p j clock hp (Nat.le_trans hshape.1 hp) hs ht hclock t F K⟩

end Shallot.MacroPeg.CBV.ParameterizedCaptureSafety
