import MacroPeg.CBV.MultiplyingPrefixCompiler
import MacroPeg.CBV.DependentCaptureFilter
import MacroPeg.CBV.CallLookahead

namespace Shallot.MacroPeg.CBV.ForwardingPrefixCycles
open MultiplyingPrefixCompiler
open RepeatedWordArguments (copies expression)
open GuardedReplayControl (Aligned)

/-- A finite set closed under the actual, position-preserving head calls.
It may include a path feeding a cycle. Tails and fallbacks are unrestricted. -/
def Closed (rs : List Spec) (ids : List Nat) : Prop :=
  ∀ i∈ids, ∃ r, rs[i]?=some r ∧ r.factor=1 ∧ r.callee∈ids

def check (rs : List Spec) (ids : List Nat) : Bool := ids.all fun i =>
  match rs[i]? with
  | none => false
  | some r => decide (r.factor=1) && ids.contains r.callee

theorem checked_iff (rs : List Spec) (ids : List Nat) : check rs ids=true ↔ Closed rs ids := by
  simp only [check,List.all_eq_true,Closed]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  cases hr : rs[i]? with
  | none => simp
  | some r => simp

theorem argument_one (rs : List Spec) (x : List Char) (k : Nat) (w : List Char)
    (p j : Nat) (h : Aligned x w p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [w] (expression (.param 0) 1) p=some (some j) := by
  rw [WordArguments.word_eval _ _ _ _ _ _ (RepeatedWordArguments.expression_word (.param 0) True.intro 1),
    RepeatedWordArguments.expression_value _ (.param 0) w rfl]
  simpa only [WordArguments.literal,copies,List.append_nil,evV,List.getElem?_cons_zero] using
    GuardedReplayControl.aligned_replay (source rs) x w .callByValuePar (sourceTable rs x k) p j h

theorem held_call (rs : List Spec) (x : List Char) (k i : Nat) (r : Spec) (hr : rs[i]?=some r)
    (w : List Char) (p j : Nat) (h : Aligned x w p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [w]
      (.call i [expression (.param 0) 1]) p=valAt (sourceTable rs x k i [w]) p := by
  have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hr]; rfl
  have hpre : pre x p j=w := by simpa only [length_sfx x h.1,length_sfx x h.2.1] using pre_eq (sfx_is_suffix x p) h.2.2
  rw [evV_call_par hs rfl (by decide)]
  simp only [evParArgs,argument_one rs x k w p j h,hpre]

theorem rows_none (rs : List Spec) (ids : List Nat) (hc : Closed rs ids) (x : List Char) (k : Nat) :
    ∀ i∈ids, ∀ w p j, Aligned x w p j → valAt (sourceTable rs x k i [w]) p=none := by
  induction k with
  | zero => intro i hi w p j h; rfl
  | succ k ih =>
    intro i hi w p j h
    obtain ⟨r,hr,hfactor,hnext⟩ := hc i hi
    obtain ⟨child,hchild,_,_⟩ := hc r.callee hnext
    have hs : ruleAtM (source rs).rules i=some ⟨1,sourceBody r⟩ := by rw [source_rule,hr]; rfl
    rw [valAt_tblV_succ hs [w] h.1]
    have hcall : evV (source rs) x .callByValuePar (sourceTable rs x k) [w]
        (.call r.callee [expression (.param 0) r.factor]) p=none := by
      rw [hfactor,held_call rs x k r.callee child hchild w p j h,ih r.callee hnext w p j h]
    exact evV_alt_none (evV_seq_none hcall)

theorem calls_none (rs : List Spec) (ids : List Nat) (hc : Closed rs ids) (x : List Char)
    (k i : Nat) (hi : i∈ids) (w : List Char) (p j : Nat) (h : Aligned x w p j) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) [w]
      (.call i [expression (.param 0) 1]) p=none := by
  obtain ⟨r,hr,_,_⟩ := hc i hi
  rw [held_call rs x k i r hr w p j h,rows_none rs ids hc x k i hi w p j h]

def deadBody : MExp := .seq (.andP (.param 0)) (.star (.lit []))

theorem expression_one (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (E : List (List Char)) (p : Nat) :
    evV g x s T E (expression (.param 0) 1) p=evV g x s T E (.param 0) p := by
  rw [WordArguments.word_eval _ _ _ _ _ _ (RepeatedWordArguments.expression_word (.param 0) True.intro 1),
    WordArguments.word_eval g x s T E (.param 0) True.intro p]
  have hv : WordArguments.value E (expression (.param 0) 1)=WordArguments.value E (.param 0) := by
    cases E <;> simp [expression,WordArguments.value]
  rw [hv]

/-- The argument preflight is retained even for a head cycle. On a missing
or unreadable value the original body fails finitely instead of diverging. -/
theorem body_eq_dead (rs : List Spec) (ids : List Nat) (hc : Closed rs ids) (i : Nat) (hi : i∈ids)
    (r : Spec) (hr : rs[i]?=some r) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    evV (source rs) x .callByValuePar (sourceTable rs x k) E (sourceBody r) p=
      evV (source rs) x .callByValuePar (sourceTable rs x k) E deadBody p := by
  obtain ⟨s,hs,hfactor,hnext⟩ := hc i hi
  have he : s=r := by rw [hr] at hs; exact Option.some.inj hs.symm
  subst s
  obtain ⟨child,hchild,_,_⟩ := hc r.callee hnext
  have hcallee : ruleAtM (source rs).rules r.callee=some ⟨1,sourceBody child⟩ := by rw [source_rule,hchild]; rfl
  have hcall : evV (source rs) x .callByValuePar (sourceTable rs x k) E
      (.call r.callee [expression (.param 0) r.factor]) p=
      match evV (source rs) x .callByValuePar (sourceTable rs x k) E (.param 0) p with
      | some none => some none
      | _ => none := by
    rw [hfactor,evV_call_par hcallee rfl (by decide)]
    simp only [evParArgs,expression_one]
    cases E with
    | nil => rfl
    | cons w rest =>
      simp only [evV,List.getElem?_cons_zero]
      cases hm : Shallot.stripPrefix? w (sfx x p) with
      | none => rfl
      | some y =>
        have hdelta := (CBVtoCBN.stripPrefix_exact _ _ _).mp hm
        have hys := suffix_trans (sfx_is_suffix x p) ⟨w,hdelta⟩
        have hy : sfx x y.length=y := sfx_suffix hys.choose_spec
        have hq : y.length≤x.length := by
          obtain ⟨u,hu⟩ := hys
          have hl := congrArg List.length hu
          simp only [List.length_append] at hl
          omega
        have hcap : pre x p y.length=w := by simpa only [length_sfx x hp] using pre_eq (sfx_is_suffix x p) hdelta
        simp only [hcap]
        exact rows_none rs ids hc x k r.callee hnext w p y.length ⟨hp,hq,by rw [hy]; exact hdelta⟩
  have hstar : evV (source rs) x .callByValuePar (sourceTable rs x k) E (.star (.lit [])) p=none := by
    rw [evV_star]
    exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (by omega)
  have hg := CallLookahead.evV_peek (source rs) x .callByValuePar (sourceTable rs x k) E (.param 0) p
  cases hm : evV (source rs) x .callByValuePar (sourceTable rs x k) E (.param 0) p with
  | none =>
    simp only [hm,CallLookahead.peek] at hcall hg
    rw [sourceBody,evV_alt_none (evV_seq_none hcall),deadBody,evV_seq_none hg]
  | some a => cases a with
    | none =>
      simp only [hm,CallLookahead.peek] at hcall hg
      rw [sourceBody,evV_alt_fail (evV_seq_fail hcall),evV_seq_fail hm,deadBody,evV_seq_fail hg]
    | some j =>
      simp only [hm,CallLookahead.peek] at hcall hg
      rw [sourceBody,evV_alt_none (evV_seq_none hcall),deadBody,evV_seq_ok hg,hstar]

end Shallot.MacroPeg.CBV.ForwardingPrefixCycles
