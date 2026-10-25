import MacroPeg.CBV.DelimitedPatternEvaluation

namespace Shallot.MacroPeg.CBV.ParentPatternTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedPatternPasses DelimitedPatternEvaluation
open DelimitedCopyProjection
open RecursiveParserStability (Installed)
open MaskedScannerAbsorption (Safe Valid enabled)
open ClockFreezing (Table)


theorem captured_free {bodies : List MExp} {g : MGrammar} (hg : Installed bodies g) (hFO : g.FirstOrder)
    (mask : List Bool) (A : List Char) (hmask : Valid bodies mask A)
    (d : Char) (hd : d∉A) (e : MExp) (he : Safe mask A e) (heFO : e.FirstOrder)
    (x : List Char) (E : List (List Char)) (s : Strategy) (hs : s≠.callByName) (k p q : Nat) (hp : p≤x.length)
    (hv : evV g x s (tblV g x s k) E e p=some (some q)) : Free d (pre x p q) := by
  have hi : ∀ i, enabled mask i=true → ∃ b, ruleAtM g.rules i=some ⟨0,b⟩ := by
    intro i he
    exact ⟨bodies[i]'(hmask.1 i he),hg i _ (List.getElem?_eq_getElem (hmask.1 i he))⟩
  have hdrop := MaskedScannerAbsorption.evaluator_safe mask hi A x s (tblV g x s k)
    (MaskedScannerAbsorption.physical_rows hg mask A hmask x s k) (tblV_ok g x s k) E e he p q hp hv
  have hcap := DependentCaptureFilter.success_prefix hs (tblV_sound hFO hs k) E e heFO p q hp hv
  rw [hcap.2] at hdrop
  have hall := CaptureDelimiterSafety.all_of_drop_eq A (pre x p q) (sfx x q) hdrop
  intro hm
  have hb := List.all_eq_true.mp hall d hm
  exact hd ((NestedScannerArguments.accepts_iff_mem A d).mp hb)

theorem unary_call (h : MGrammar) (n i : Nat) (d : Char) (js : List Nat)
    (hr : ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i js)⟩)
    (x : List Char) (E : List (List Char)) (k p q : Nat) (hq : q≤x.length) (a : MExp)
    (ha : evV h x .callByValueSeq (tblV h x .callByValueSeq k) E a p=some (some q)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (n+i) [a]) p=
      result k (run d [pre x p q] (afterParts d i js) (sfx x q)) := by
  rw [evV_call_seq hr rfl,evSeq_cons_ok ha,evSeq_nil]
  change valAt (tblV h x .callByValueSeq k (n+i) [pre x p q]) q=_
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [pre x p q] hq,compile_eval] <;> first | rfl | exact hq

theorem passes_eval (h : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (n : Nat) (args : List MExp)
    (p : Nat) (f : Nat → Option (List Char)) :
    ∀ is, is≠[] →
      (∀ i∈is, evV h x .callByValueSeq T E (.call (n+i) [argument args i]) p=some ((f i).map List.length)) →
      evV h x .callByValueSeq T E (passes n args is) p=some ((combine f is).map List.length)
  | [],hn,_ => False.elim (hn rfl)
  | [i],_,hc => hc i (by simp)
  | i::j::is,_,hc => by
    change (match evV h x .callByValueSeq T E (.andP (.call (n+i) [argument args i])) p with
      | some (some q) => evV h x .callByValueSeq T E (passes n args (j::is)) q | other => other)=_
    rw [CallLookahead.evV_peek,hc i (by simp)]
    cases hf : f i with
    | none => simp [CallLookahead.peek,combine,hf]
    | some rest =>
      simp only [Option.map_some,CallLookahead.peek]
      rw [passes_eval h x T E n args p f (j::is) (by simp) (fun k hk => hc k (by simp [hk]))]
      simp [combine,hf]

theorem passes_clock (h : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (n : Nat) (args : List MExp)
    (p k : Nat) (f : Nat → Option (List Char)) (is : List Nat) (hne : is≠[])
    (hc : ∀ i∈is, evV h x .callByValueSeq T E (.call (n+i) [argument args i]) p=result k (f i)) :
    evV h x .callByValueSeq T E (passes n args is) p=result k (combine f is) := by
  cases k with
  | zero =>
    cases is with
    | nil => exact False.elim (hne rfl)
    | cons i is =>
      have hh : evV h x .callByValueSeq T E (.call (n+i) [argument args i]) p=none := hc i (by simp)
      cases is with
      | nil => exact hh
      | cons j is =>
        rw [passes,evV_seq_none (by rw [CallLookahead.evV_peek,hh]; rfl)]
        rfl
  | succ k => exact passes_eval h x T E n args p f is hne hc

theorem arguments_congr (g h : MGrammar) (x : List Char) (T U : Table) (E : List (List Char)) (p : Nat) :
    ∀ (args emitted : List MExp), (hlen : emitted.length=args.length) →
      (∀ i, (hi : i<args.length) → evV g x .callByValuePar T E args[i] p=evV h x .callByValueSeq U E (emitted[i]'(by omega)) p) →
      evParArgs g x .callByValuePar T E args p=evParArgs h x .callByValueSeq U E emitted p
  | [],[],_,_ => rfl
  | [],_::_,hl,_ | _::_,[],hl,_ => by simp at hl
  | a::args,b::bs,hl,he => by
    have ha : evV g x .callByValuePar T E a p=evV h x .callByValueSeq U E b p := he 0 (by simp)
    have ht := arguments_congr g h x T U E p args bs (by simpa using hl) (fun i hi => he (i+1) (by simpa using hi))
    simp only [evParArgs,ha,ht]

theorem physical (g h : MGrammar) (n : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length) (hscope : ∀ i∈j::js, i<args.length)
    (hsrc : ruleAtM g.rules n=some ⟨args.length,compile d (sourceParts d (j::js))⟩)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i (j::js))⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call n args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (targetHead n emitted) p := by
  rw [evV_call_par hsrc rfl (by decide)]
  have heargs := arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold targetHead
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passes n emitted (List.range emitted.length)) q | other => other)
  rw [preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar k) E p args W hs
      have hwl : W.length=args.length := by simp [hw,hl]
      have hqbound (i : Nat) (hi : i<args.length) : qs[i]'(by omega)≤x.length :=
        evV_ok (tblV_ok _ _ _ k) _ p hp _ (hq i hi)
      have hwi (i : Nat) (hi : i<args.length) : W[i]'(by omega)=pre x p (qs[i]'(by omega)) := by simp [hw]
      let tails := qs.map (sfx x)
      have htl : tails.length=W.length := by simp [tails,hwl,hl]
      have hwfree (i : Nat) (hi : i<W.length) : Free d W[i] := by
        rw [hwi i (by omega)]
        exact hfree i (by omega) _ (hq i (by omega))
      have hprefix (i : Nat) (hi : i<W.length) : sfx x p=W[i]++(tails[i]'(by omega)) := by
        rw [hwi i (by omega)]
        have heFO : args[i].FirstOrder := firstOrder_get args hfo i (by omega)
        simpa [tails] using (ReplayFusion.success_prefix (tblV_sound hg (by decide) k) E args[i] heFO p _ hp (hq i (by omega))).2
      have hr := run_eq d W tails (by omega) hwfree htl (sfx x p) hprefix j js (fun i hi => by have hh := hscope i hi; omega)
      have hc (i : Nat) (hi : i∈List.range emitted.length) :
          evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (n+i) [argument emitted i]) p=
            result k (pass d W tails (j::js) i) := by
        have hi : i<args.length := by have hh := List.mem_range.mp hi; omega
        rw [argument_eq emitted i (by omega),unary_call h n i d (j::js) (hrows i hi) x E k p _ (hqbound i hi) (emitted[i]'(by omega))
          ((he i hi).symm.trans (hq i hi))]
        simp only [pass,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
        simp [tails]
      have hne : List.range emitted.length≠[] := by simpa only [hlen] using (show List.range args.length≠[] from by simpa using (Nat.ne_of_gt hn))
      have hpass := passes_clock h x (tblV h x .callByValueSeq k) E n emitted p k (pass d W tails (j::js)) _ hne hc
      change valAt (tblV g x .callByValuePar k n W) p=evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passes n emitted (List.range emitted.length)) p
      rw [source_row g n args.length d (j::js) hsrc x k W p hp]
      change result k (run d W (sourceParts d (j::js)) (sfx x p))=evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passes n emitted (List.range emitted.length)) p
      rw [hpass,hlen,←hwl,←hr]

end Shallot.MacroPeg.CBV.ParentPatternTransfer
