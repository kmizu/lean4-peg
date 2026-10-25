import MacroPeg.CBV.ConsumingPatternChecks
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.ConsumingPatternCorrespondence
open RetainedPatternSyntax
open ConsumingPatternChecks
open RetainedCaptureEffects (EnvSafe)
open MaskedScannerAbsorption (enabled)
open NestedScannerArguments (accepts)
abbrev Term := RetainedPatternSyntax.Expr

def Rows (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (pattern : List Nat) (required : List Bool) (alphabet : List Char) (x : List Char) (k : Nat) : Prop :=
  ∀ (i : Nat) (e : Term), clients[i]?=some e → ∀ w, (enabled required i=true → w.all (accepts alphabet)=true) → ∀ p q, p≤x.length → q≤x.length →
    sfx x p=w++sfx x q →
    valAt (tblV (source bodies clients arity d pattern) x .callByValuePar k (bodies.length+i) [w]) p=
      valAt (tblV (target bodies clients arity d pattern) x .callByValueSeq k (bodies.length+i) [w]) q

mutual
  theorem expression_physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (required : List Bool)
      (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
      (x : List Char) (k : Nat) (rows : Rows bodies clients arity d pattern required alphabet x k) (hasParent parentFree : Bool) :
      ∀ e, termCheck bodies clients arity alphabet required hasParent parentFree e=true → ∀ E, EnvSafe alphabet parentFree E → ∀ p, p≤x.length →
      evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true e) p=
        evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) E (render bodies.length clients.length false e) p
    | .helper i,hc,E,hE,p,hp => by
      have hi : i<bodies.length := of_decide_eq_true (show decide (i<bodies.length)=true from hc)
      have he := List.getElem?_eq_getElem hi
      rw [render,evV_call_par (source_installed bodies clients arity d pattern i bodies[i] he) rfl (by decide),evPar_nil,
        render,evV_call_seq (target_installed bodies clients arity d pattern i bodies[i] he) rfl,evSeq_nil]
      exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hb
        (source_installed bodies clients arity d pattern) (target_installed bodies clients arity d pattern) x _ _ k i hi [] [])
    | .user i a,hc,E,hE,p,hp => by
      obtain ⟨hh,hsafe⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨hi,hargCheck⟩ := Bool.and_eq_true_iff.mp hh
      have hi : i<clients.length := of_decide_eq_true hi
      have he := List.getElem?_eq_getElem hi
      have ha := expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a hargCheck E hE p hp
      rw [render,evV_call_par (source_user bodies clients arity d pattern i clients[i] he) rfl (by decide),
        render,evV_call_seq (target_user bodies clients arity d pattern i clients[i] he) rfl]
      cases hv : evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => rw [evPar_cons_none hv,evSeq_cons_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => rw [evPar_cons_fail hv,evSeq_cons_fail (ha.symm.trans hv)]
        | some q =>
          rw [evPar_cons_ok hv,evPar_nil,evSeq_cons_ok (ha.symm.trans hv),evSeq_nil]
          obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix (tblV_sound (source_firstOrder bodies clients arity d pattern hb) (by decide) k)
            E (render bodies.length clients.length true a) (render_firstOrder _ _ _ _) p q hp hv
          have hw : enabled required i=true → (pre x p q).all (accepts alphabet)=true := by
            intro hf
            have hs : RetainedCaptureEffects.safeCheck bodies clients (RetainedCaptureEffects.effects bodies clients alphabet) alphabet parentFree a=true := by simpa only [hf,Bool.not_true,Bool.false_or] using hsafe
            exact RetainedCaptureEffects.captured_alpha bodies clients arity d pattern hb alphabet hmask heff x k parentFree E hE a hs p q hp hv
          exact rows i clients[i] he (pre x p q) hw p q hp hq hs
    | .copy args,hc,E,hE,p,hp => by
      obtain ⟨hl,ha⟩ := Bool.and_eq_true_iff.mp hc
      have hl : args.length=arity := of_decide_eq_true hl
      cases pattern with
      | nil => exact False.elim (hpat rfl)
      | cons j js =>
        change evV _ _ _ _ E (.call (bodies.length+clients.length) (renderArgs bodies.length clients.length true args)) p=
          evV _ _ _ _ E (DelimitedPatternEvaluation.targetHead (bodies.length+clients.length) (renderArgs bodies.length clients.length false args)) p
        apply ParentPatternTransfer.physical _ _ (bodies.length+clients.length) d j js
          (renderArgs bodies.length clients.length true args) (renderArgs bodies.length clients.length false args)
          (by simp [renderArgs_length]) (by simpa [renderArgs_length,hl] using hn)
          (fun i hi => by simpa [renderArgs_length,hl] using hscope i hi)
          (by simpa [renderArgs_length,hl] using source_copy bodies clients arity d (j::js))
          (fun i hi => target_copy bodies clients arity d (j::js) i (by simpa [renderArgs_length,hl] using hi))
          (source_firstOrder bodies clients arity d (j::js) hb) (renderArgs_firstOrder _ _ _ _) x E k p hp
        · intro i hi
          simpa only [renderArgs_eq_map,List.getElem_map] using
            arguments_physical bodies clients arity alphabet d (j::js) required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree args ha i (by simpa [renderArgs_length] using hi) E hE p hp
        · intro i hi q hv
          have hi : i<args.length := by simpa [renderArgs_length] using hi
          have hh := args_checked bodies clients arity alphabet required hasParent parentFree args ha i hi
          have hcap := RetainedCaptureEffects.captured_alpha bodies clients arity d (j::js) hb alphabet hmask heff x k parentFree E hE args[i] hh.2 p q hp
            (by simpa only [renderArgs_eq_map,List.getElem_map] using hv)
          intro hm
          exact hd ((NestedScannerArguments.accepts_iff_mem alphabet d).mp (List.all_eq_true.mp hcap d hm))
    | .seq a b,hc,E,hE,p,hp => by
      have ha := expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a (Bool.and_eq_true_iff.mp hc).1 E hE p hp
      cases hv : evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => simp only [render,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => simp only [render,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
        | some q =>
          simp only [render,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
          exact expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree b (Bool.and_eq_true_iff.mp hc).2 E hE q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
    | .alt a b,hc,E,hE,p,hp => by
      have ha := expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a (Bool.and_eq_true_iff.mp hc).1 E hE p hp
      cases hv : evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => simp only [render,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
      | some v => cases v with
        | none =>
          simp only [render,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
          exact expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree b (Bool.and_eq_true_iff.mp hc).2 E hE p hp
        | some q => simp only [render,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
    | .notP a,hc,E,hE,p,hp => by simp only [render,evV,expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a hc E hE p hp]
    | .star a,hc,E,hE,p,hp => by
      simp only [render,evV_star]
      exact evStar_congr p (fun q hq => expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a hc E hE q (by omega))
    | .eps,_,_,_,_,_ | .any,_,_,_,_,_ | .chr _,_,_,_,_,_ | .range _ _,_,_,_,_,_ | .lit _,_,_,_,_,_ | .parent,_,_,_,_,_ => rfl
  theorem arguments_physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (required : List Bool)
      (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
      (x : List Char) (k : Nat) (rows : Rows bodies clients arity d pattern required alphabet x k) (hasParent parentFree : Bool) :
      ∀ args, argsCheck bodies clients arity alphabet required hasParent parentFree args=true → ∀ i, (hi : i<args.length) → ∀ E, EnvSafe alphabet parentFree E → ∀ p, p≤x.length →
        evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) E (render bodies.length clients.length true args[i]) p=
          evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) E (render bodies.length clients.length false args[i]) p
    | [],_,i,hi,_,_,_,_ => by simp at hi
    | a::args,h,0,_,E,hE,p,hp => expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1 E hE p hp
    | a::args,h,i+1,hi,E,hE,p,hp => arguments_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k rows hasParent parentFree args
        (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi) E hE p hp
end

theorem tables_related (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (required : List Bool)
    (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hpat : pattern≠[]) (hd : d∉alphabet) (hscope : ∀ i∈pattern, i<arity)
    (hc : ∀ (i : Nat) (e : Term), clients[i]?=some e → termCheck bodies clients arity alphabet required true (enabled required i) e=true)
    (x : List Char) (k : Nat) : Rows bodies clients arity d pattern required alphabet x k := by
  induction k with
  | zero => intro i e hi w hw p q hp hq hs; rfl
  | succ k ih =>
    intro i e hi w hw p q hp hq hs
    rw [valAt_tblV_succ (source_user bodies clients arity d pattern i e hi) [w] hp,
      valAt_tblV_succ (target_user bodies clients arity d pattern i e hi) [w] hq]
    have hfirst : evV (source bodies clients arity d pattern) x .callByValuePar
        (tblV (source bodies clients arity d pattern) x .callByValuePar k) [w] (.param 0) p=some (some q) := by
      simp [evV,(CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs,length_sfx x hq]
    rw [evV_seq_ok hfirst]
    exact expression_physical bodies clients arity alphabet d pattern required hb hmask heff hn hpat hd hscope x k ih true (enabled required i) e (hc i e hi) [w] (by
      intro hf v hv
      have hh : w=v := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hv
      subst v
      exact hw hf) q hq

theorem physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (required : List Bool) (root : Term)
    (hc : ConsumingPatternChecks.check bodies clients arity alphabet d pattern required root=true) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (source bodies clients arity d pattern) x .callByValuePar (tblV (source bodies clients arity d pattern) x .callByValuePar k) [] (render bodies.length clients.length true root) p=
      evV (target bodies clients arity d pattern) x .callByValueSeq (tblV (target bodies clients arity d pattern) x .callByValueSeq k) [] (render bodies.length clients.length false root) p := by
  have h := ConsumingPatternChecks.checked bodies clients arity alphabet d pattern required root hc
  exact expression_physical bodies clients arity alphabet d pattern required h.library h.helpers h.returns h.nonempty h.pattern_nonempty h.separator h.scope x k
    (tables_related bodies clients arity alphabet d pattern required h.library h.helpers h.returns h.nonempty h.pattern_nonempty h.separator h.scope h.client_checks x k) false false root h.root_check [] (by intro h; cases h) p hp

theorem observations_iff (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (pattern : List Nat) (required : List Bool) (root : Term)
    (hc : ConsumingPatternChecks.check bodies clients arity alphabet d pattern required root=true) (x : List Char) (rest : Option (List Char)) :
    SObs (source bodies clients arity d pattern) .callByValuePar (render bodies.length clients.length true root) x rest ↔
      SObs (target bodies clients arity d pattern) .callByValueSeq (render bodies.length clients.length false root) x rest := by
  have h := ConsumingPatternChecks.checked bodies clients arity alphabet d pattern required root hc
  rw [←decideObsV_iff (source_firstOrder bodies clients arity d pattern h.library) (by decide) (render_firstOrder _ _ _ _),
    ←decideObsV_iff (target_firstOrder bodies clients arity d pattern h.library) (by decide) (render_firstOrder _ _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical bodies clients arity alphabet d pattern required root hc x k _ (Nat.le_refl _))]

end Shallot.MacroPeg.CBV.ConsumingPatternCorrespondence
