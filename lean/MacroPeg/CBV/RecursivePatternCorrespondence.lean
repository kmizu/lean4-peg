import MacroPeg.CBV.RecursivePatternSyntax
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.RecursivePatternCorrespondence
open RecursivePatternSyntax
abbrev Term := RecursivePatternSyntax.Expr

def Rows (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat) (x : List Char) (k : Nat) : Prop :=
  ∀ (i : Nat) (e : Term), clients[i]?=some e → ∀ p, p≤x.length →
    valAt (tblV (source clients arity d pattern) x .callByValuePar k i []) p=
      valAt (tblV (target clients arity d pattern) x .callByValueSeq k i []) p

mutual
  theorem expression_physical (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat)
      (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
      (x : List Char) (k : Nat) (rows : Rows clients arity d pattern x k) :
      ∀ e, termCheck clients arity alphabet e=true → ∀ p, p≤x.length →
      evV (source clients arity d pattern) x .callByValuePar (tblV (source clients arity d pattern) x .callByValuePar k) [] (render clients.length true e) p=
        evV (target clients arity d pattern) x .callByValueSeq (tblV (target clients arity d pattern) x .callByValueSeq k) [] (render clients.length false e) p
    | .user i,hc,p,hp => by
      have hi : i<clients.length := of_decide_eq_true (show decide (i<clients.length)=true from hc)
      have he := List.getElem?_eq_getElem hi
      rw [render,evV_call_par (source_user clients arity d pattern i clients[i] he) rfl (by decide),
        render,evV_call_seq (target_user clients arity d pattern i clients[i] he) rfl]
      exact rows i clients[i] he p hp
    | .copy args,hc,p,hp => by
      obtain ⟨hl,ha⟩ := Bool.and_eq_true_iff.mp hc
      have hl : args.length=arity := of_decide_eq_true hl
      cases pattern with
      | nil => exact False.elim (hpat rfl)
      | cons j js =>
        change evV _ _ _ _ [] (.call clients.length (renderArgs clients.length true args)) p=
          evV _ _ _ _ [] (DelimitedPatternEvaluation.targetHead clients.length (renderArgs clients.length false args)) p
        apply DelimitedPatternCallTransfer.physical _ _ clients.length d j js
          (renderArgs clients.length true args) (renderArgs clients.length false args)
          (by simp [renderArgs_length]) (by simpa [renderArgs_length,hl] using hn)
          (fun i hi => by simpa [renderArgs_length,hl] using hscope i hi)
          (by simpa [renderArgs_length,hl] using source_copy clients arity d (j::js))
          (fun i hi => target_copy clients arity d (j::js) i (by simpa [renderArgs_length,hl] using hi))
          (source_firstOrder clients arity d (j::js)) (renderArgs_firstOrder _ _ _) x k p hp
        · intro i hi
          simpa only [renderArgs_eq_map,List.getElem_map] using
            arguments_physical clients arity alphabet d (j::js) hn hpat hd hscope x k rows args ha i (by simpa [renderArgs_length] using hi) p hp
        · intro i hi q hv
          have hi : i<args.length := by simpa [renderArgs_length] using hi
          have hh := args_checked clients arity alphabet args ha i hi
          obtain ⟨hvalid,hsafe⟩ := MaskedScannerAbsorption.checked (sourceBodies clients) alphabet (render clients.length true args[i]) hh.2
          apply CaptureDelimiterSafety.captured_free (source_installed clients arity d (j::js)) (source_firstOrder clients arity d (j::js))
            _ alphabet hvalid d hd (render clients.length true args[i]) hsafe (render_firstOrder _ _ _) x .callByValuePar (by decide) k p q hp
          simpa only [renderArgs_eq_map,List.getElem_map] using hv
    | .seq a b,hc,p,hp => by
      have ha := expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows a (Bool.and_eq_true_iff.mp hc).1 p hp
      cases hv : evV (source clients arity d pattern) x .callByValuePar (tblV (source clients arity d pattern) x .callByValuePar k) [] (render clients.length true a) p with
      | none => simp only [render,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => simp only [render,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
        | some q =>
          simp only [render,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
          exact expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows b (Bool.and_eq_true_iff.mp hc).2 q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
    | .alt a b,hc,p,hp => by
      have ha := expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows a (Bool.and_eq_true_iff.mp hc).1 p hp
      cases hv : evV (source clients arity d pattern) x .callByValuePar (tblV (source clients arity d pattern) x .callByValuePar k) [] (render clients.length true a) p with
      | none => simp only [render,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
      | some v => cases v with
        | none =>
          simp only [render,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
          exact expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows b (Bool.and_eq_true_iff.mp hc).2 p hp
        | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
    | .notP a,hc,p,hp => by simp only [render,evV,expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows a hc p hp]
    | .star a,hc,p,hp => by
      simp only [render,evV_star]
      exact evStar_congr p (fun q hq => expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows a hc q (by omega))
    | .eps,_,_,_ | .any,_,_,_ | .chr _,_,_,_ | .range _ _,_,_,_ | .lit _,_,_,_ => rfl

  theorem arguments_physical (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat)
      (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
      (x : List Char) (k : Nat) (rows : Rows clients arity d pattern x k) :
      ∀ args, argsCheck clients arity alphabet args=true → ∀ i, (hi : i<args.length) → ∀ p, p≤x.length →
        evV (source clients arity d pattern) x .callByValuePar (tblV (source clients arity d pattern) x .callByValuePar k) [] (render clients.length true args[i]) p=
          evV (target clients arity d pattern) x .callByValueSeq (tblV (target clients arity d pattern) x .callByValueSeq k) [] (render clients.length false args[i]) p
    | [],_,i,hi,_,_ => by simp at hi
    | a::args,h,0,_,p,hp => expression_physical clients arity alphabet d pattern hn hpat hd hscope x k rows a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1 p hp
    | a::args,h,i+1,hi,p,hp => arguments_physical clients arity alphabet d pattern hn hpat hd hscope x k rows args
        (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi) p hp
end

/-- Actual transformed client tables close simultaneously, including calls
through nested copy actuals, without any independent-library premise. -/
theorem tables_related (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat)
    (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
    (hc : ∀ (i : Nat) (e : Term), clients[i]?=some e → termCheck clients arity alphabet e=true)
    (x : List Char) (k : Nat) : Rows clients arity d pattern x k := by
  induction k with
  | zero => intro i e hi p hp; rfl
  | succ k ih =>
    intro i e hi p hp
    rw [valAt_tblV_succ (source_user clients arity d pattern i e hi) [] hp,valAt_tblV_succ (target_user clients arity d pattern i e hi) [] hp]
    exact expression_physical clients arity alphabet d pattern hn hpat hd hscope x k ih e (hc i e hi) p hp

theorem physical (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check clients arity alphabet d pattern root=true) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source clients arity d pattern) x .callByValuePar (tblV (source clients arity d pattern) x .callByValuePar k) [] (render clients.length true root) p=
      evV (target clients arity d pattern) x .callByValueSeq (tblV (target clients arity d pattern) x .callByValueSeq k) [] (render clients.length false root) p := by
  obtain ⟨⟨hn,hpat,hd⟩,hscope,hb,he⟩ := checked clients arity alphabet d pattern root hc
  exact expression_physical clients arity alphabet d pattern hn hpat hd hscope x k
    (tables_related clients arity alphabet d pattern hn hpat hd hscope hb x k) root he p hp

theorem observations_iff (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (root : Term)
    (hc : check clients arity alphabet d pattern root=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source clients arity d pattern) .callByValuePar (render clients.length true root) x rest ↔
      SObs (target clients arity d pattern) .callByValueSeq (render clients.length false root) x rest := by
  rw [←decideObsV_iff (source_firstOrder clients arity d pattern) (by decide) (render_firstOrder _ _ _),
    ←decideObsV_iff (target_firstOrder clients arity d pattern) (by decide) (render_firstOrder _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical clients arity alphabet d pattern root hc x k _ (Nat.le_refl _))]

end Shallot.MacroPeg.CBV.RecursivePatternCorrespondence
