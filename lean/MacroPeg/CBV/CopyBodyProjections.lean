import MacroPeg.CBV.ParentPatternTransfer
import MacroPeg.CBV.CopyBodyEvaluation

namespace Shallot.MacroPeg.CBV.CopyBodyProjections
open DelimiterTemplate DelimitedWordPattern DelimitedPatternPasses DelimitedPatternEvaluation
open ParentPatternTransfer
open ClockFreezing (Table)
open DelimitedCopyProjection

theorem query_physical (g h : MGrammar) (n : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length) (hscope : ∀ i∈j::js, i<args.length)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i (j::js))⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q))
    (W : List (List Char)) (hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p=some (some W)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (targetHead n emitted) p=
      result k (CopyBodyEvaluation.partsRun d W (j::js) (sfx x p)) := by
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold targetHead
  change (match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passes n emitted (List.range emitted.length)) q | other => other)=_
  rw [preflight_eval,←heargs,hs]
  change evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passes n emitted (List.range emitted.length)) p=_
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
    rw [argument_eq emitted i (by omega),ParentPatternTransfer.unary_call h n i d (j::js) (hrows i hi) x E k p _ (hqbound i hi) (emitted[i]'(by omega))
      ((he i hi).symm.trans (hq i hi))]
    simp only [pass,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
    simp [tails]
  have hne : List.range emitted.length≠[] := by simpa only [hlen] using (show List.range args.length≠[] from by simpa using (Nat.ne_of_gt hn))
  have hpass := ParentPatternTransfer.passes_clock h x (tblV h x .callByValueSeq k) E n emitted p k (pass d W tails (j::js)) _ hne hc
  rw [hpass,hlen,←hwl,←hr]
  rfl
def passesAt (address : Nat → Nat) (args : List MExp) : List Nat → MExp
  | [] => .eps
  | [i] => .call (address i) [argument args i]
  | i::j::is => .seq (.andP (.call (address i) [argument args i])) (passesAt address args (j::is))
def headAt (address : Nat → Nat) (args : List MExp) : MExp :=
  .seq (preflight args) (passesAt address args (List.range args.length))
theorem unary_at (h : MGrammar) (address : Nat → Nat) (i : Nat) (d : Char) (js : List Nat)
    (hr : ruleAtM h.rules (address i)=some ⟨1,compile d (afterParts d i js)⟩)
    (x : List Char) (E : List (List Char)) (k p q : Nat) (hq : q≤x.length) (a : MExp)
    (ha : evV h x .callByValueSeq (tblV h x .callByValueSeq k) E a p=some (some q)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (address i) [a]) p=
      result k (run d [pre x p q] (afterParts d i js) (sfx x q)) := by
  rw [evV_call_seq hr rfl,evSeq_cons_ok ha,evSeq_nil]
  change valAt (tblV h x .callByValueSeq k (address i) [pre x p q]) q=_
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [pre x p q] hq,compile_eval] <;> first | rfl | exact hq

theorem passesAt_eval (h : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (address : Nat → Nat) (args : List MExp)
    (p : Nat) (f : Nat → Option (List Char)) :
    ∀ is, is≠[] →
      (∀ i∈is, evV h x .callByValueSeq T E (.call (address i) [argument args i]) p=some ((f i).map List.length)) →
      evV h x .callByValueSeq T E (passesAt address args is) p=some ((combine f is).map List.length)
  | [],hn,_ => False.elim (hn rfl)
  | [i],_,hc => hc i (by simp)
  | i::j::is,_,hc => by
    change (match evV h x .callByValueSeq T E (.andP (.call (address i) [argument args i])) p with
      | some (some q) => evV h x .callByValueSeq T E (passesAt address args (j::is)) q | other => other)=_
    rw [CallLookahead.evV_peek,hc i (by simp)]
    cases hf : f i with
    | none => simp [CallLookahead.peek,combine,hf]
    | some rest =>
      simp only [Option.map_some,CallLookahead.peek]
      rw [passesAt_eval h x T E address args p f (j::is) (by simp) (fun k hk => hc k (by simp [hk]))]
      simp [combine,hf]

theorem passesAt_clock (h : MGrammar) (x : List Char) (T : Table) (E : List (List Char)) (address : Nat → Nat) (args : List MExp)
    (p k : Nat) (f : Nat → Option (List Char)) (is : List Nat) (hne : is≠[])
    (hc : ∀ i∈is, evV h x .callByValueSeq T E (.call (address i) [argument args i]) p=result k (f i)) :
    evV h x .callByValueSeq T E (passesAt address args is) p=result k (combine f is) := by
  cases k with
  | zero =>
    cases is with
    | nil => exact False.elim (hne rfl)
    | cons i is =>
      have hh : evV h x .callByValueSeq T E (.call (address i) [argument args i]) p=none := hc i (by simp)
      cases is with
      | nil => exact hh
      | cons j is =>
        rw [passesAt,evV_seq_none (by rw [CallLookahead.evV_peek,hh]; rfl)]
        rfl
  | succ k => exact passesAt_eval h x T E address args p f is hne hc

theorem queryAt_physical (g h : MGrammar) (address : Nat → Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length) (hscope : ∀ i∈j::js, i<args.length)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (address i)=some ⟨1,compile d (afterParts d i (j::js))⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q))
    (W : List (List Char)) (hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p=some (some W)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (headAt address emitted) p=
      result k (CopyBodyEvaluation.partsRun d W (j::js) (sfx x p)) := by
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold headAt
  change (match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passesAt address emitted (List.range emitted.length)) q | other => other)=_
  rw [preflight_eval,←heargs,hs]
  change evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (passesAt address emitted (List.range emitted.length)) p=_
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
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call (address i) [argument emitted i]) p=
        result k (pass d W tails (j::js) i) := by
    have hi : i<args.length := by have hh := List.mem_range.mp hi; omega
    rw [argument_eq emitted i (by omega),unary_at h address i d (j::js) (hrows i hi) x E k p _ (hqbound i hi) (emitted[i]'(by omega))
      ((he i hi).symm.trans (hq i hi))]
    simp only [pass,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
    simp [tails]
  have hne : List.range emitted.length≠[] := by simpa only [hlen] using (show List.range args.length≠[] from by simpa using (Nat.ne_of_gt hn))
  have hpass := passesAt_clock h x (tblV h x .callByValueSeq k) E address emitted p k (pass d W tails (j::js)) _ hne hc
  rw [hpass,hlen,←hwl,←hr]
  rfl
end Shallot.MacroPeg.CBV.CopyBodyProjections
