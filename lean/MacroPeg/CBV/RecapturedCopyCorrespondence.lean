import MacroPeg.CBV.RecapturedCopySyntax
import MacroPeg.CBV.ScannerPairFusion

namespace Shallot.MacroPeg.CBV.RecapturedCopyCorrespondence
open RetainedPatternSyntax
open RecapturedCopySyntax
open ConsumingPatternChecks
open RetainedCaptureEffects (EnvSafe)
open MaskedScannerAbsorption (enabled)
open NestedScannerArguments (accepts)
abbrev Term := RetainedPatternSyntax.Expr

def Rows (bodies : List MExp) (clients : List Term) (arity : Nat) (d : Char) (body : List Nat) (required : List Bool) (alphabet : List Char) (x : List Char) (k : Nat) : Prop :=
  ∀ (i : Nat) (e : Term), clients[i]?=some e → ∀ w, (enabled required i=true → w.all (accepts alphabet)=true) → ∀ p q, p≤x.length → q≤x.length →
    sfx x p=w++sfx x q →
    valAt (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k (bodies.length+i) [w]) p=
      valAt (tblV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq k (bodies.length+i) [w]) q

mutual
  theorem expression_physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (required : List Bool)
      (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hbody : RecapturedCopySyntax.patternCheck arity body=true) (hd : d∉alphabet)
      (x : List Char) (k : Nat) (rows : Rows bodies clients arity d body required alphabet x k) (hasParent parentFree : Bool) :
      ∀ e, termCheck bodies clients arity alphabet required hasParent parentFree e=true → ∀ E, EnvSafe alphabet parentFree E → ∀ p, p≤x.length →
      evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E (render bodies.length clients.length true e) p=
        evV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq (tblV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq k) E (emit bodies.length clients.length arity d body e) p
    | .helper i,hc,E,hE,p,hp => by
      have hi : i<bodies.length := of_decide_eq_true (show decide (i<bodies.length)=true from hc)
      have he := List.getElem?_eq_getElem hi
      rw [render,evV_call_par (RecapturedCopySyntax.source_installed bodies clients arity d body i bodies[i] he) rfl (by decide),evPar_nil,
        emit,evV_call_seq (RecapturedCopySyntax.target_installed bodies clients arity d body i bodies[i] he) rfl,evSeq_nil]
      exact congrArg (fun row => valAt row p) (RecursiveParserStability.helper_rows_eq hb
        (RecapturedCopySyntax.source_installed bodies clients arity d body) (RecapturedCopySyntax.target_installed bodies clients arity d body) x _ _ k i hi [] [])
    | .user i a,hc,E,hE,p,hp => by
      obtain ⟨hh,hsafe⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨hi,hargCheck⟩ := Bool.and_eq_true_iff.mp hh
      have hi : i<clients.length := of_decide_eq_true hi
      have he := List.getElem?_eq_getElem hi
      have ha := expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a hargCheck E hE p hp
      rw [render,evV_call_par (RecapturedCopySyntax.source_user bodies clients arity d body i clients[i] he) rfl (by decide),
        emit,evV_call_seq (RecapturedCopySyntax.target_user bodies clients arity d body i clients[i] he) rfl]
      cases hv : evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => rw [evPar_cons_none hv,evSeq_cons_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => rw [evPar_cons_fail hv,evSeq_cons_fail (ha.symm.trans hv)]
        | some q =>
          rw [evPar_cons_ok hv,evPar_nil,evSeq_cons_ok (ha.symm.trans hv),evSeq_nil]
          obtain ⟨hq,hs⟩ := ReplayFusion.success_prefix (tblV_sound (RecapturedCopySyntax.source_firstOrder bodies clients arity d body hb) (by decide) k)
            E (render bodies.length clients.length true a) (render_firstOrder _ _ _ _) p q hp hv
          have hw : enabled required i=true → (pre x p q).all (accepts alphabet)=true := by
            intro hf
            have hs : RetainedCaptureEffects.safeCheck bodies clients (RetainedCaptureEffects.effects bodies clients alphabet) alphabet parentFree a=true := by simpa only [hf,Bool.not_true,Bool.false_or] using hsafe
            exact ControlledCaptureEffects.captured_alpha (RecapturedCopySyntax.source bodies clients arity d body) bodies clients
              (RecapturedCopySyntax.source_installed bodies clients arity d body) (RecapturedCopySyntax.source_user bodies clients arity d body)
              (RecapturedCopySyntax.source_firstOrder bodies clients arity d body hb) alphabet hmask heff x k parentFree E hE a hs p q hp hv
          exact rows i clients[i] he (pre x p q) hw p q hp hq hs
    | .copy args,hc,E,hE,p,hp => by
      obtain ⟨hl,ha⟩ := Bool.and_eq_true_iff.mp hc
      have hl : args.length=arity := of_decide_eq_true hl
      let originalArgs := renderArgs bodies.length clients.length true args
      let generatedArgs := emitArgs bodies.length clients.length arity d body args
      have hlen : generatedArgs.length=originalArgs.length := by simp [originalArgs,generatedArgs,renderArgs_length,emitArgs_length]
      have heq : ∀ i, (hi : i<originalArgs.length) →
          evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E originalArgs[i] p=
            evV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq (tblV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq k) E (generatedArgs[i]'(by omega)) p := by
        intro i hi
        simpa only [originalArgs,generatedArgs,renderArgs_eq_map,emitArgs_eq_map,List.getElem_map] using
          arguments_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree args ha i (by simpa [originalArgs,renderArgs_length] using hi) E hE p hp
      have hfree : ∀ i, (hi : i<originalArgs.length) → ∀ q,
          evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E originalArgs[i] p=some (some q) →
            DelimitedCopyProjection.Free d (pre x p q) := by
        intro i hi q hv
        have hi : i<args.length := by simpa [originalArgs,renderArgs_length] using hi
        have hh := ConsumingPatternChecks.args_checked bodies clients arity alphabet required hasParent parentFree args ha i hi
        have hcap := ControlledCaptureEffects.captured_alpha (RecapturedCopySyntax.source bodies clients arity d body) bodies clients
          (RecapturedCopySyntax.source_installed bodies clients arity d body) (RecapturedCopySyntax.source_user bodies clients arity d body)
          (RecapturedCopySyntax.source_firstOrder bodies clients arity d body hb) alphabet hmask heff x k parentFree E hE args[i] hh.2 p q hp
          (by simpa only [originalArgs,renderArgs_eq_map,List.getElem_map] using hv)
        intro hm
        exact hd ((NestedScannerArguments.accepts_iff_mem alphabet d).mp (List.all_eq_true.mp hcap d hm))
      obtain ⟨hpattern,hscope⟩ := RecapturedCopySyntax.pattern_checked arity body hbody
      cases body with
      | nil => exact False.elim (hpattern rfl)
      | cons j js =>
        have hi := RecapturedCopySyntax.target_copy bodies clients arity d (j::js)
        have hc := RecapturedCopyTransfer.physical (RecapturedCopySyntax.source bodies clients arity d (j::js)) (RecapturedCopySyntax.target bodies clients arity d (j::js))
          (bodies.length+clients.length) d j js originalArgs generatedArgs hlen
          (by simpa [originalArgs,renderArgs_length,hl] using hn)
          (fun i hm => by simpa [originalArgs,renderArgs_length,hl] using hscope i hm)
          (by simpa [originalArgs,renderArgs_length,hl] using RecapturedCopySyntax.source_copy bodies clients arity d (j::js))
          (by simpa [originalArgs,renderArgs_length,hl] using hi)
          (RecapturedCopySyntax.source_firstOrder bodies clients arity d (j::js) hb) (renderArgs_firstOrder _ _ _ _)
          x E k p hp heq hfree
        simpa only [originalArgs,generatedArgs,render,emit,renderArgs_length,hl,if_true] using hc
    | .seq a b,hc,E,hE,p,hp => by
      have ha := expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a (Bool.and_eq_true_iff.mp hc).1 E hE p hp
      cases hv : evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => simp only [render,emit,evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
      | some v => cases v with
        | none => simp only [render,emit,evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
        | some q =>
          simp only [render,emit,evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
          exact expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree b (Bool.and_eq_true_iff.mp hc).2 E hE q (evV_ok (tblV_ok _ _ _ k) _ p hp q hv)
    | .alt a b,hc,E,hE,p,hp => by
      have ha := expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a (Bool.and_eq_true_iff.mp hc).1 E hE p hp
      cases hv : evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E (render bodies.length clients.length true a) p with
      | none => simp only [render,emit,evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
      | some v => cases v with
        | none =>
          simp only [render,emit,evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
          exact expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree b (Bool.and_eq_true_iff.mp hc).2 E hE p hp
        | some q => simp only [render,emit,evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
    | .notP a,hc,E,hE,p,hp => by simp only [render,emit,evV,expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a hc E hE p hp]
    | .star a,hc,E,hE,p,hp => by
      simp only [render,emit,evV_star]
      exact evStar_congr p (fun q hq => expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a hc E hE q (by omega))
    | .eps,_,_,_,_,_ | .any,_,_,_,_,_ | .chr _,_,_,_,_,_ | .range _ _,_,_,_,_,_ | .lit _,_,_,_,_,_ | .parent,_,_,_,_,_ => rfl
  theorem arguments_physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (required : List Bool)
      (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hbody : RecapturedCopySyntax.patternCheck arity body=true) (hd : d∉alphabet)
      (x : List Char) (k : Nat) (rows : Rows bodies clients arity d body required alphabet x k) (hasParent parentFree : Bool) :
      ∀ args, argsCheck bodies clients arity alphabet required hasParent parentFree args=true → ∀ i, (hi : i<args.length) → ∀ E, EnvSafe alphabet parentFree E → ∀ p, p≤x.length →
        evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) E (render bodies.length clients.length true args[i]) p=
          evV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq (tblV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq k) E (emit bodies.length clients.length arity d body args[i]) p
    | [],_,i,hi,_,_,_,_ => by simp at hi
    | a::args,h,0,_,E,hE,p,hp => expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree a
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1 E hE p hp
    | a::args,h,i+1,hi,E,hE,p,hp => arguments_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k rows hasParent parentFree args
        (Bool.and_eq_true_iff.mp h).2 i (by simpa using hi) E hE p hp
end

theorem tables_related (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (required : List Bool)
    (hb : RecursiveParserStability.Valid bodies)
      (hmask : MaskedScannerAbsorption.Valid bodies (MaskedScannerAbsorption.mask bodies alphabet) alphabet)
      (heff : RetainedCaptureEffects.Valid bodies clients alphabet) (hn : 0<arity) (hbody : RecapturedCopySyntax.patternCheck arity body=true) (hd : d∉alphabet)
    (hc : ∀ (i : Nat) (e : Term), clients[i]?=some e → termCheck bodies clients arity alphabet required true (enabled required i) e=true)
    (x : List Char) (k : Nat) : Rows bodies clients arity d body required alphabet x k := by
  induction k with
  | zero => intro i e hi w hw p q hp hq hs; rfl
  | succ k ih =>
    intro i e hi w hw p q hp hq hs
    rw [valAt_tblV_succ (RecapturedCopySyntax.source_user bodies clients arity d body i e hi) [w] hp,
      valAt_tblV_succ (RecapturedCopySyntax.target_user bodies clients arity d body i e hi) [w] hq]
    have hfirst : evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar
        (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) [w] (.param 0) p=some (some q) := by
      simp [evV,(CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr hs,length_sfx x hq]
    rw [evV_seq_ok hfirst]
    exact expression_physical bodies clients arity alphabet d body required hb hmask heff hn hbody hd x k ih true (enabled required i) e (hc i e hi) [w] (by
      intro hf v hv
      have hh : w=v := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hv
      subst v
      exact hw hf) q hq

theorem physical (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (required : List Bool) (root : Term)
    (hc : RecapturedCopySyntax.check bodies clients arity alphabet d body required root=true) (x : List Char) (k p : Nat) (hp : p≤x.length) :
    evV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar (tblV (RecapturedCopySyntax.source bodies clients arity d body) x .callByValuePar k) [] (render bodies.length clients.length true root) p=
      evV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq (tblV (RecapturedCopySyntax.target bodies clients arity d body) x .callByValueSeq k) [] (emit bodies.length clients.length arity d body root) p := by
  obtain ⟨hbody,h⟩ := RecapturedCopySyntax.checked bodies clients arity alphabet d body required root hc
  exact expression_physical bodies clients arity alphabet d body required h.library h.helpers h.returns h.nonempty hbody h.separator x k
    (tables_related bodies clients arity alphabet d body required h.library h.helpers h.returns h.nonempty hbody h.separator h.client_checks x k) false false root h.root_check [] (by intro h; cases h) p hp

theorem observations_iff (bodies : List MExp) (clients : List Term) (arity : Nat) (alphabet : List Char) (d : Char) (body : List Nat) (required : List Bool) (root : Term)
    (hc : RecapturedCopySyntax.check bodies clients arity alphabet d body required root=true) (x : List Char) (rest : Option (List Char)) :
    SObs (RecapturedCopySyntax.source bodies clients arity d body) .callByValuePar (render bodies.length clients.length true root) x rest ↔
      SObs (RecapturedCopySyntax.target bodies clients arity d body) .callByValueSeq (emit bodies.length clients.length arity d body root) x rest := by
  obtain ⟨hbody,h⟩ := RecapturedCopySyntax.checked bodies clients arity alphabet d body required root hc
  rw [←decideObsV_iff (RecapturedCopySyntax.source_firstOrder bodies clients arity d body h.library) (by decide) (render_firstOrder _ _ _ _),
    ←decideObsV_iff (RecapturedCopySyntax.target_firstOrder bodies clients arity d body h.library) (by decide) (emit_firstOrder _ _ _ _ _ _)]
  unfold decideObsV
  rw [ScannerPairFusion.stable_result_eq _ _ x _ _ _ _ (fun k => physical bodies clients arity alphabet d body required root hc x k _ (Nat.le_refl _))]

end Shallot.MacroPeg.CBV.RecapturedCopyCorrespondence
