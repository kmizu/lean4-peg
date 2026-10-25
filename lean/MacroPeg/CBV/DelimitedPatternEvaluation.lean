import MacroPeg.CBV.DelimitedPatternPasses
import MacroPeg.CBV.DelimitedCopyCallTransfer

namespace Shallot.MacroPeg.CBV.DelimitedPatternEvaluation
open DelimiterTemplate DelimitedWordPattern DelimitedPatternPasses
open DelimitedCopyProjection
open ClockFreezing (Table)

abbrev result := DelimitedCopyEvaluation.result

def argument (args : List MExp) (i : Nat) := args[i]?.getD .eps

def preflight : List MExp → MExp
  | [] => .eps
  | a::args => .seq (.andP a) (preflight args)

def passes (n : Nat) (args : List MExp) : List Nat → MExp
  | [] => .eps
  | [i] => .call (n+i) [argument args i]
  | i::j::is => .seq (.andP (.call (n+i) [argument args i])) (passes n args (j::is))

def targetHead (n : Nat) (args : List MExp) : MExp :=
  .seq (preflight args) (passes n args (List.range args.length))

def gate (p : Nat) : Option (Option (List (List Char))) → Res
  | none => none | some none => some none | some (some _) => some (some p)

theorem argument_eq (args : List MExp) (i : Nat) (hi : i<args.length) : argument args i=args[i] := by
  simp [argument,List.getElem?_eq_getElem hi]

theorem preflight_eval (g : MGrammar) (x : List Char) (T : Table) (E : List (List Char))
    (args : List MExp) (p : Nat) :
    evV g x .callByValueSeq T E (preflight args) p=gate p (evParArgs g x .callByValueSeq T E args p) := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    change (match evV g x .callByValueSeq T E (.andP a) p with
      | some (some q) => evV g x .callByValueSeq T E (preflight args) q | other => other)=_
    rw [CallLookahead.evV_peek]
    cases ha : evV g x .callByValueSeq T E a p with
    | none => simp [CallLookahead.peek,gate,evParArgs,ha]
    | some v => cases v with
      | none => simp [CallLookahead.peek,gate,evParArgs,ha]
      | some q =>
        simp only [CallLookahead.peek,ih,evParArgs,ha]
        cases ht : evParArgs g x .callByValueSeq T E args p with
        | none => rfl
        | some v => cases v <;> rfl

/-- A successful Par argument list records every real endpoint. -/
theorem endpoints (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (E : List (List Char)) (p : Nat) :
    ∀ (args : List MExp) (W : List (List Char)), evParArgs g x s T E args p=some (some W) →
      ∃ qs : List Nat, ∃ hlen : qs.length=args.length, W=qs.map (pre x p) ∧
        ∀ i, (hi : i<args.length) → evV g x s T E args[i] p=some (some (qs[i]'(by omega)))
  | [],W,h => by
    have he : W=[] := by simpa [evParArgs] using h.symm
    exact ⟨[],rfl,he,fun i hi => by simp at hi⟩
  | a::args,W,h => by
    cases ha : evV g x s T E a p with
    | none => simp [evParArgs,ha] at h
    | some v => cases v with
      | none => simp [evParArgs,ha] at h
      | some q =>
        cases ht : evParArgs g x s T E args p with
        | none => simp [evParArgs,ha,ht] at h
        | some v => cases v with
          | none => simp [evParArgs,ha,ht] at h
          | some ws =>
            have he : W=pre x p q::ws := by simpa [evParArgs,ha,ht] using h.symm
            obtain ⟨qs,hl,hw,hq⟩ := endpoints g x s T E p args ws ht
            refine ⟨q::qs,by simp [hl],by simp [he,hw],?_⟩
            intro i hi
            cases i with
            | zero => exact ha
            | succ i => exact hq i (by simpa using hi)

theorem source_row (g : MGrammar) (n arity : Nat) (d : Char) (js : List Nat)
    (hr : ruleAtM g.rules n=some ⟨arity,compile d (sourceParts d js)⟩)
    (x : List Char) (k : Nat) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (tblV g x .callByValuePar k n W) p=result k (run d W (sourceParts d js) (sfx x p)) := by
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr W hp,compile_eval] <;> first | rfl | exact hp

theorem unary_call (h : MGrammar) (n i : Nat) (d : Char) (js : List Nat)
    (hr : ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i js)⟩)
    (x : List Char) (k p q : Nat) (hq : q≤x.length) (a : MExp)
    (ha : evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] a p=some (some q)) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.call (n+i) [a]) p=
      result k (run d [pre x p q] (afterParts d i js) (sfx x q)) := by
  rw [evV_call_seq hr rfl,evSeq_cons_ok ha,evSeq_nil]
  change valAt (tblV h x .callByValueSeq k (n+i) [pre x p q]) q=_
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [pre x p q] hq,compile_eval] <;> first | rfl | exact hq

theorem passes_eval (h : MGrammar) (x : List Char) (T : Table) (n : Nat) (args : List MExp)
    (p : Nat) (f : Nat → Option (List Char)) :
    ∀ is, is≠[] →
      (∀ i∈is, evV h x .callByValueSeq T [] (.call (n+i) [argument args i]) p=some ((f i).map List.length)) →
      evV h x .callByValueSeq T [] (passes n args is) p=some ((combine f is).map List.length)
  | [],hn,_ => False.elim (hn rfl)
  | [i],_,hc => hc i (by simp)
  | i::j::is,_,hc => by
    change (match evV h x .callByValueSeq T [] (.andP (.call (n+i) [argument args i])) p with
      | some (some q) => evV h x .callByValueSeq T [] (passes n args (j::is)) q | other => other)=_
    rw [CallLookahead.evV_peek,hc i (by simp)]
    cases hf : f i with
    | none => simp [CallLookahead.peek,combine,hf]
    | some rest =>
      simp only [Option.map_some,CallLookahead.peek]
      rw [passes_eval h x T n args p f (j::is) (by simp) (fun k hk => hc k (by simp [hk]))]
      simp [combine,hf]

theorem passes_clock (h : MGrammar) (x : List Char) (T : Table) (n : Nat) (args : List MExp)
    (p k : Nat) (f : Nat → Option (List Char)) (is : List Nat) (hne : is≠[])
    (hc : ∀ i∈is, evV h x .callByValueSeq T [] (.call (n+i) [argument args i]) p=result k (f i)) :
    evV h x .callByValueSeq T [] (passes n args is) p=result k (combine f is) := by
  cases k with
  | zero =>
    cases is with
    | nil => exact False.elim (hne rfl)
    | cons i is =>
      have hh : evV h x .callByValueSeq T [] (.call (n+i) [argument args i]) p=none := hc i (by simp)
      cases is with
      | nil => exact hh
      | cons j is =>
        rw [passes,evV_seq_none (by rw [CallLookahead.evV_peek,hh]; rfl)]
        rfl
  | succ k => exact passes_eval h x T n args p f is hne hc

theorem arguments_congr (g h : MGrammar) (x : List Char) (T U : Table) (p : Nat)
    (args : List MExp) (he : ∀ a∈args, evV g x .callByValuePar T [] a p=evV h x .callByValueSeq U [] a p) :
    evParArgs g x .callByValuePar T [] args p=evParArgs h x .callByValueSeq U [] args p := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    have ha := he a (by simp)
    have ht := ih (fun b hb => he b (by simp [hb]))
    simp only [evParArgs,ha,ht]

/-- Actual source and target calls, including ordered failure/divergence
of all original actuals. The target has one unary row per retained word. -/
theorem firstOrder_get : ∀ (args : List MExp), MExp.FirstOrderArgs args → ∀ i, (hi : i<args.length) → args[i].FirstOrder
  | [],_,i,hi => by simp at hi
  | a::args,ha,0,_ => ha.1
  | a::args,ha,i+1,hi => firstOrder_get args ha.2 i (by simpa using hi)

theorem physical (g h : MGrammar) (n : Nat) (d : Char) (j : Nat) (js : List Nat)
    (args : List MExp) (hn : 0<args.length) (hscope : ∀ i∈j::js, i<args.length)
    (hsrc : ruleAtM g.rules n=some ⟨args.length,compile d (sourceParts d (j::js))⟩)
    (hrows : ∀ i, i<args.length → ruleAtM h.rules (n+i)=some ⟨1,compile d (afterParts d i (j::js))⟩)
    (hg : g.FirstOrder) (hfo : MExp.FirstOrderArgs args)
    (x : List Char) (k p : Nat) (hp : p≤x.length)
    (he : ∀ a∈args, evV g x .callByValuePar (tblV g x .callByValuePar k) [] a p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] a p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) [] args[i] p=some (some q) → Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) [] (.call n args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (targetHead n args) p := by
  rw [evV_call_par hsrc rfl (by decide)]
  have heargs := arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) p args he
  unfold targetHead
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (preflight args) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n args (List.range args.length)) q | other => other)
  rw [preflight_eval,←heargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) [] args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      obtain ⟨qs,hl,hw,hq⟩ := endpoints g x .callByValuePar (tblV g x .callByValuePar k) [] p args W hs
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
        simpa [tails] using (ReplayFusion.success_prefix (tblV_sound hg (by decide) k) [] args[i] heFO p _ hp (hq i (by omega))).2
      have hr := run_eq d W tails (by omega) hwfree htl (sfx x p) hprefix j js (fun i hi => by have hh := hscope i hi; omega)
      have hc (i : Nat) (hi : i∈List.range args.length) :
          evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (.call (n+i) [argument args i]) p=
            result k (pass d W tails (j::js) i) := by
        have hi := List.mem_range.mp hi
        rw [argument_eq args i hi,unary_call h n i d (j::js) (hrows i hi) x k p _ (hqbound i hi) args[i]
          ((he args[i] (List.getElem_mem hi)).symm.trans (hq i hi))]
        simp only [pass,getElem!_pos W i (show i<W.length by omega),getElem!_pos tails i (show i<tails.length by omega),hwi i hi]
        simp [tails]
      have hne : List.range args.length≠[] := by simpa using (Nat.ne_of_gt hn)
      have hpass := passes_clock h x (tblV h x .callByValueSeq k) n args p k (pass d W tails (j::js)) _ hne hc
      change valAt (tblV g x .callByValuePar k n W) p=evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n args (List.range args.length)) p
      rw [source_row g n args.length d (j::js) hsrc x k W p hp]
      change result k (run d W (sourceParts d (j::js)) (sfx x p))=evV h x .callByValueSeq (tblV h x .callByValueSeq k) [] (passes n args (List.range args.length)) p
      rw [hpass,←hwl,←hr]


end Shallot.MacroPeg.CBV.DelimitedPatternEvaluation
