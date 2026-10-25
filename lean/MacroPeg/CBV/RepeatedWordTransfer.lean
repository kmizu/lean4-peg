import MacroPeg.CBV.RepeatedWordEvaluation
import MacroPeg.CBV.CopyBodyEmission

namespace Shallot.MacroPeg.CBV.RepeatedWordTransfer
open DelimiterTemplate DelimitedWordPattern DelimitedCopyProjection
open DelimitedPatternEvaluation RepeatedWordPattern RepeatedWordEvaluation
open ClockFreezing Classical

def head (base : Nat) (args : List MExp) : MExp :=
  .seq (preflight args) (.seq (.call base [])
    (.alt (.notP .any) (passes (base+1) args (List.range args.length))))

def rules (arity : Nat) (d : Char) (js : List Nat) : List MRule :=
  ⟨0,.eps⟩::(List.range arity).map (fun i => ⟨1,afterBody d i js⟩)

structure Installed (h : MGrammar) (base arity : Nat) (d : Char) (js : List Nat) : Prop where
  gate : ruleAtM h.rules base=some ⟨0,.eps⟩
  rows : ∀ i, i<arity → ruleAtM h.rules (base+1+i)=some ⟨1,afterBody d i js⟩

theorem rules_gate (arity : Nat) (d : Char) (js : List Nat) :
    ruleAtM (rules arity d js) 0=some ⟨0,.eps⟩ := rfl

theorem rules_projection (arity : Nat) (d : Char) (js : List Nat) (i : Nat) (hi : i<arity) :
    ruleAtM (rules arity d js) (1+i)=some ⟨1,afterBody d i js⟩ := by
  simp [rules,ruleAtM_eq_getElem?,Nat.add_comm,List.getElem?_map,List.getElem?_range hi]

theorem source_firstOrder (d : Char) (js : List Nat) : (sourceBody d js).FirstOrder :=
  DelimitedRepeatEvaluation.copies_firstOrder d _

theorem after_firstOrder (d : Char) (i : Nat) (js : List Nat) : (afterBody d i js).FirstOrder :=
  ⟨compile_firstOrder d _,DelimitedRepeatEvaluation.copies_firstOrder d _⟩

theorem rules_firstOrder (arity : Nat) (d : Char) (js : List Nat) :
    ∀ r∈rules arity d js, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with hr|hr
  · subst r; trivial
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact after_firstOrder d i js

theorem head_firstOrder (base : Nat) (args : List MExp) (ha : MExp.FirstOrderArgs args) :
    (head base args).FirstOrder :=
  ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,⟨True.intro,⟨True.intro,
    DelimitedPatternCompiler.passes_firstOrder (base+1) args ha _ (fun i hi => List.mem_range.mp hi)⟩⟩⟩

theorem passes_boolean (h : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (base : Nat) (args : List MExp) (p : Nat) (P : Nat → Prop) :
    ∀ is, is≠[] →
      (∀ i∈is, evV h x .callByValueSeq T E (.call (base+i) [argument args i]) p=
        some (if P i then some 0 else none)) →
      evV h x .callByValueSeq T E (passes base args is) p=
        some (if ∀ i∈is, P i then some 0 else none)
  | [],hne,_ => False.elim (hne rfl)
  | [i],_,hc => by simpa [passes] using hc i (by simp)
  | i::j::is,_,hc => by
    have hi := hc i (by simp)
    have ht := passes_boolean h x T E base args p P (j::is) (by simp) (fun k hk => hc k (by simp [hk]))
    by_cases hp : P i
    · simp only [hp,ite_true] at hi
      rw [passes,evV_seq_ok (by rw [CallLookahead.evV_peek,hi]; rfl),ht]
      simp [hp]
    · simp only [hp,ite_false] at hi
      rw [passes,evV_seq_fail (by rw [CallLookahead.evV_peek,hi]; rfl)]
      simp [hp]

theorem eof_physical (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.notP .any) p=some (if sfx x p=[] then some 0 else none) := by
  cases hs : sfx x p with
  | nil =>
    have hz : p=0 := by have := length_sfx x hp; rw [hs] at this; simpa using this.symm
    simp [evV,sfx,hz]
  | cons c rest => simp [evV,hs]

theorem successful_actuals (g h : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (base+1+i)=some ⟨1,afterBody d i (j::js)⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) →
      evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args[i] p=some (some q) → Free d (pre x p q))
    (W : List (List Char))
    (hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar (k+1)) E args p=some (some W)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
      (.alt (.notP .any) (passes (base+1) emitted (List.range emitted.length))) p=
      evV g x .callByValuePar (tblV g x .callByValuePar k) W (sourceBody d (j::js)) p := by
  obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar (k+1)) E p args W hs
  have hwl : W.length=args.length := by simp [hw,hl]
  have hqbound (i : Nat) (hi : i<args.length) : qs[i]'(by omega)≤x.length :=
    evV_ok (tblV_ok _ _ _ (k+1)) _ p hp _ (hq i hi)
  have hwi (i : Nat) (hi : i<args.length) : W[i]'(by omega)=pre x p (qs[i]'(by omega)) := by simp [hw]
  let tails := qs.map (sfx x)
  have htl : tails.length=W.length := by simp [tails,hwl,hl]
  have hwfree (i : Nat) (hi : i<W.length) : Free d W[i] := by
    rw [hwi i (by omega)]
    exact hfree i (by omega) _ (hq i (by omega))
  have hprefix (i : Nat) (hi : i<W.length) : sfx x p=W[i]++(tails[i]'(by omega)) := by
    rw [hwi i (by omega)]
    have heFO : args[i].FirstOrder := DelimitedPatternEvaluation.firstOrder_get args hfo i (by omega)
    simpa [tails] using (ReplayFusion.success_prefix (tblV_sound hg (by decide) (k+1)) E args[i] heFO p _ hp (hq i (by omega))).2
  let P := fun i => AfterAccept d W[i]! i (j::js) tails[i]!
  have hc (i : Nat) (hi : i∈List.range emitted.length) :
      evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E
        (.call (base+1+i) [argument emitted i]) p=some (if P i then some 0 else none) := by
    have hi : i<args.length := by have := List.mem_range.mp hi; omega
    rw [argument_eq emitted i (by omega),evV_call_seq (hrows i hi) rfl,
      evSeq_cons_ok ((he i hi).symm.trans (hq i hi)),evSeq_nil]
    change valAt (tblV h x .callByValueSeq (k+1) (base+1+i) [pre x p (qs[i]'(by omega))]) (qs[i]'(by omega))=_
    rw [valAt_tblV_succ (hrows i hi) _ (hqbound i hi),
      after_physical h x .callByValueSeq _ (tblV_ok _ _ _ k) _ d (hfree i hi _ (hq i hi)) i j js _ (hqbound i hi)]
    simp only [P,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
    simp [tails]
  have hne : List.range emitted.length≠[] := by simpa [hlen] using (Nat.ne_of_gt hn)
  have hpass := passes_boolean h x (tblV h x .callByValueSeq (k+1)) E (base+1) emitted p P _ hne hc
  have hiff := RepeatedWordPattern.source_iff_after d W tails (by omega) hwfree htl (sfx x p) hprefix j js
    (fun i hi => by have := hscope i hi; omega)
  have hiff' : SourceAccept d W (j::js) (sfx x p) ↔ sfx x p=[] ∨ ∀ i∈List.range emitted.length, P i := by
    rw [hiff]
    apply or_congr_right
    simp only [List.mem_range,hlen,←hwl]
    apply forall_congr'; intro i
    apply forall_congr'; intro hi
    simp only [P,getElem!_pos W i hi,getElem!_pos tails i (show i<tails.length by omega)]
  rw [source_physical g x .callByValuePar _ (tblV_ok _ _ _ k) W d j js p hp]
  simp only [hiff']
  by_cases hx : sfx x p=[]
  · have hv : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.notP .any) p=some (some 0) := by
      rw [eof_physical h x .callByValueSeq _ E p hp]; simp [hx]
    rw [evV_alt_ok hv]
    simp [hx]
  · have hv : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.notP .any) p=some none := by
      rw [eof_physical h x .callByValueSeq _ E p hp]; simp [hx]
    rw [evV_alt_fail hv,hpass]
    simp only [hx,false_or]

theorem physical (g h : MGrammar) (base : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args emitted : List MExp) (hlen : emitted.length=args.length) (hn : 0<args.length)
    (hscope : ∀ i∈j::js, i<args.length)
    (hsource : ruleAtM g.rules base=some ⟨args.length,sourceBody d (j::js)⟩)
    (hgate : ruleAtM h.rules base=some ⟨0,.eps⟩)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (base+1+i)=some ⟨1,afterBody d i (j::js)⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (he : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call base args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base emitted) p := by
  rw [evV_call_par hsource rfl (by decide)]
  have heargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen he
  unfold head
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E
      (.seq (.call base []) (.alt (.notP .any) (passes (base+1) emitted (List.range emitted.length)))) q
    | other => other)
  rw [DelimitedPatternEvaluation.preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      change valAt (tblV g x .callByValuePar k base W) p=evV h x .callByValueSeq (tblV h x .callByValueSeq k) E
        (.seq (.call base []) (.alt (.notP .any) (passes (base+1) emitted (List.range emitted.length)))) p
      cases k with
      | zero => rw [evV_seq_none (CopyBodyEmission.initialized h base hgate x E 0 p hp)]; rfl
      | succ k =>
        rw [valAt_tblV_succ hsource W hp,
          evV_seq_ok (CopyBodyEmission.initialized h base hgate x E (k+1) p hp)]
        exact (successful_actuals g h base d j js args emitted hlen hn hscope hrows hg hfo x E k p hp he hfree W hs).symm

end Shallot.MacroPeg.CBV.RepeatedWordTransfer
