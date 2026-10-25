import MacroPeg.CBV.SelectedForwardingContext

namespace Shallot.MacroPeg.CBV.SelectedForwardingCycles
open SelectedForwardingContext
open MultiplyingPrefixCompiler (Spec sourceBody)
open RepeatedWordArguments (expression)
open GuardedReplayControl (Aligned)
open ForwardingPrefixCycles (deadBody expression_one)

theorem held_call (g : MGrammar) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids)
    (i : Nat) (hi : i∈ids) (r : Spec) (hr : rs[i]?=some r) (x : List Char) (k : Nat)
    (w : List Char) (p j : Nat) (h : Aligned x w p j) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [w]
      (.call i [expression (.param 0) 1]) p=valAt (tblV g x .callByValuePar k i [w]) p := by
  have hs := hv.rule i hi r hr
  have hp0 := GuardedReplayControl.aligned_replay g x w .callByValuePar (tblV g x .callByValuePar k) p j h
  have hpre : pre x p j=w := by simpa only [length_sfx x h.1,length_sfx x h.2.1] using pre_eq (sfx_is_suffix x p) h.2.2
  rw [evV_call_par hs rfl (by decide)]
  simp only [evParArgs,expression_one,hp0,hpre]

theorem rows_none (g : MGrammar) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids)
    (cycle : List Nat) (hc : ForwardingPrefixCycles.Closed rs cycle) (hsub : cycle⊆ids) (x : List Char) (k : Nat) :
    ∀ i∈cycle, ∀ w p j, Aligned x w p j → valAt (tblV g x .callByValuePar k i [w]) p=none := by
  induction k with
  | zero => intro i hi w p j h; rfl
  | succ k ih =>
    intro i hi w p j h
    obtain ⟨r,hr,hfactor,hnext⟩ := hc i hi
    obtain ⟨child,hchild,_,_⟩ := hc r.callee hnext
    have hs : ruleAtM g.rules i=some ⟨1,sourceBody r⟩ := hv.rule i (hsub hi) r hr
    rw [valAt_tblV_succ hs [w] h.1]
    have hcall : evV g x .callByValuePar (tblV g x .callByValuePar k) [w]
        (.call r.callee [expression (.param 0) r.factor]) p=none := by
      rw [hfactor,held_call g rs ids hv r.callee (hsub hnext) child hchild x k w p j h,ih r.callee hnext w p j h]
    exact evV_alt_none (evV_seq_none hcall)


theorem body_eq_dead (g : MGrammar) (rs : List Spec) (ids : List Nat) (hv : Valid g rs ids)
    (cycle : List Nat) (hc : ForwardingPrefixCycles.Closed rs cycle) (hsub : cycle⊆ids) (i : Nat) (hi : i∈cycle)
    (r : Spec) (hr : rs[i]?=some r) (x : List Char) (k : Nat) (E : List (List Char))
    (p : Nat) (hp : p≤x.length) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (sourceBody r) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) E deadBody p := by
  obtain ⟨s,hs,hfactor,hnext⟩ := hc i hi
  have he : s=r := by rw [hr] at hs; exact Option.some.inj hs.symm
  subst s
  obtain ⟨child,hchild,_,_⟩ := hc r.callee hnext
  have hcallee : ruleAtM g.rules r.callee=some ⟨1,sourceBody child⟩ := hv.rule r.callee (hsub hnext) child hchild
  have hcall : evV g x .callByValuePar (tblV g x .callByValuePar k) E
      (.call r.callee [expression (.param 0) r.factor]) p=
      match evV g x .callByValuePar (tblV g x .callByValuePar k) E (.param 0) p with
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
        exact rows_none g rs ids hv cycle hc hsub x k r.callee hnext w p y.length ⟨hp,hq,by rw [hy]; exact hdelta⟩
  have hstar : evV g x .callByValuePar (tblV g x .callByValuePar k) E (.star (.lit [])) p=none := by
    rw [evV_star]
    exact evStar_stuck (j := p) (by simp [evV,Shallot.stripPrefix?,length_sfx x hp]) (by omega)
  have hg := CallLookahead.evV_peek g x .callByValuePar (tblV g x .callByValuePar k) E (.param 0) p
  cases hm : evV g x .callByValuePar (tblV g x .callByValuePar k) E (.param 0) p with
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

end Shallot.MacroPeg.CBV.SelectedForwardingCycles
