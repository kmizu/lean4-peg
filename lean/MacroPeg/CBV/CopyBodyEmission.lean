import MacroPeg.CBV.CopyBodyProjections
import MacroPeg.CBV.DelimitedPatternCompiler
import MacroPeg.CBV.ScannerFrontier

namespace Shallot.MacroPeg.CBV.CopyBodyEmission
open CopyBodyControl
open CopyBodyEvaluation (partsRun query resolve)
open ClockFreezing (Table)

def keys (arity : Nat) (e : Body) : List (List Nat × Nat) :=
  (normalized e).keys.flatMap (fun h => (List.range arity).map (fun i => (h,i)))
def address (base arity : Nat) (e : Body) (h : List Nat) (i : Nat) := base+1+(keys arity e).idxOf (h,i)
def rules (arity : Nat) (d : Char) (e : Body) : List MRule :=
  ⟨0,.eps⟩::(keys arity e).map (fun (h,i) => ⟨1,DelimiterTemplate.compile d (DelimitedWordPattern.afterParts d i h)⟩)
def emitQuery (base arity : Nat) (e : Body) (args : List MExp) (h : List Nat) : MExp :=
  if h=[] then .eps else CopyBodyProjections.headAt (address base arity e h) args

def emitPlan (base arity : Nat) (e : Body) (args : List MExp) : Plan → MExp
  | .fail => MExp.failAlways
  | .undef => .star .eps
  | .done h => emitQuery base arity e args h
  | .branch h yes no => RootObservation.branch (.andP (emitQuery base arity e args h))
      (emitPlan base arity e args yes) (emitPlan base arity e args no)
def head (base arity : Nat) (e : Body) (args : List MExp) : MExp :=
  .seq (DelimitedPatternEvaluation.preflight args) (.seq (.call base []) (emitPlan base arity e args (normalized e)))

theorem key_mem (arity : Nat) (e : Body) (h : List Nat) (hh : h∈(normalized e).keys) (i : Nat) (hi : i<arity) : (h,i)∈keys arity e :=
  List.mem_flatMap.mpr ⟨h,hh,List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩⟩

theorem rules_gate (arity : Nat) (d : Char) (e : Body) : ruleAtM (rules arity d e) 0=some ⟨0,.eps⟩ := rfl

private theorem key_lookup (xs : List (List Nat × Nat)) (key : List Nat × Nat) (hm : key∈xs) : xs[xs.idxOf key]?=some key := by
  induction xs with
  | nil => cases hm
  | cons a xs ih =>
    by_cases he : a=key
    · subst a; simp
    · have ht : key∈xs := by
        rcases List.mem_cons.mp hm with hh|ht
        · exact False.elim (he hh.symm)
        · exact ht
      simp [List.idxOf_cons,cond_eq_ite,beq_iff_eq,he,ih ht]

theorem rules_projection (arity : Nat) (d : Char) (e : Body) (h : List Nat) (hh : h∈(normalized e).keys) (i : Nat) (hi : i<arity) :
    ruleAtM (rules arity d e) (1+(keys arity e).idxOf (h,i))=some ⟨1,DelimiterTemplate.compile d (DelimitedWordPattern.afterParts d i h)⟩ := by
  have hm := key_mem arity e h hh i hi
  simp only [rules,ruleAtM_eq_getElem?,Nat.add_comm 1,List.getElem?_cons_succ,List.getElem?_map]
  rw [key_lookup _ _ hm]
  rfl

theorem rules_firstOrder (arity : Nat) (d : Char) (e : Body) : ∀ r∈rules arity d e, r.body.FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl|hr
  · exact True.intro
  · obtain ⟨⟨h,i⟩,hm,rfl⟩ := List.mem_map.mp hr
    exact DelimiterTemplate.compile_firstOrder _ _

structure Ready (g h : MGrammar) (x : List Char) (E : List (List Char)) (k p : Nat) (d : Char)
    (args emitted : List MExp) (W : List (List Char)) : Prop where
  source_fo : g.FirstOrder
  args_fo : MExp.FirstOrderArgs args
  positive : 0<args.length
  length : emitted.length=args.length
  bound : p≤x.length
  equal : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p
  free : ∀ i, (hi : i<args.length) → ∀ q,
    evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → DelimitedCopyProjection.Free d (pre x p q)
  success : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p=some (some W)

def Installed (h : MGrammar) (base arity : Nat) (d : Char) (e : Body) : Prop :=
  ruleAtM h.rules base=some ⟨0,.eps⟩ ∧ ∀ hist∈(normalized e).keys, ∀ i, i<arity →
    ruleAtM h.rules (address base arity e hist i)=some ⟨1,DelimiterTemplate.compile d (DelimitedWordPattern.afterParts d i hist)⟩
theorem passesAt_firstOrder (addr : Nat → Nat) (args : List MExp) (ha : MExp.FirstOrderArgs args) :
    ∀ is, (∀ i∈is, i<args.length) → (CopyBodyProjections.passesAt addr args is).FirstOrder
  | [],_ => True.intro
  | [i],h => by
    rw [CopyBodyProjections.passesAt,DelimitedPatternEvaluation.argument_eq args i (h i (by simp))]
    exact ⟨DelimitedPatternEvaluation.firstOrder_get args ha i (h i (by simp)),True.intro⟩
  | i::j::is,h => by
    rw [CopyBodyProjections.passesAt,DelimitedPatternEvaluation.argument_eq args i (h i (by simp))]
    exact ⟨⟨DelimitedPatternEvaluation.firstOrder_get args ha i (h i (by simp)),True.intro⟩,
      passesAt_firstOrder addr args ha (j::is) (fun k hk => h k (by simp [hk]))⟩

theorem query_firstOrder (base arity : Nat) (e : Body) (args : List MExp) (ha : MExp.FirstOrderArgs args) (hist : List Nat) :
    (emitQuery base arity e args hist).FirstOrder := by
  unfold emitQuery
  split
  · exact True.intro
  · exact ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,passesAt_firstOrder _ args ha _ (fun i hi => List.mem_range.mp hi)⟩

theorem plan_firstOrder (base arity : Nat) (e : Body) (args : List MExp) (ha : MExp.FirstOrderArgs args) :
    ∀ p, (emitPlan base arity e args p).FirstOrder
  | .fail | .undef => True.intro
  | .done h => query_firstOrder base arity e args ha h
  | .branch h a b => ⟨⟨query_firstOrder base arity e args ha h,plan_firstOrder base arity e args ha a⟩,
      query_firstOrder base arity e args ha h,plan_firstOrder base arity e args ha b⟩

theorem head_firstOrder (base arity : Nat) (e : Body) (args : List MExp) (ha : MExp.FirstOrderArgs args) : (head base arity e args).FirstOrder :=
  ⟨DelimitedPatternCompiler.preflight_firstOrder args ha,True.intro,plan_firstOrder base arity e args ha _⟩

theorem query_eval (g h : MGrammar) (base : Nat) (d : Char) (e : Body)
    (args emitted : List MExp) (he : check args.length e=true)
    (x : List Char) (E : List (List Char)) (k p : Nat) (W : List (List Char))
    (ready : Ready g h x E (k+1) p d args emitted W) (hi : Installed h base args.length d e)
    (hist : List Nat) (hh : hist∈(normalized e).keys) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (emitQuery base args.length e emitted hist) p=
      some ((partsRun d W hist (sfx x p)).map List.length) := by
  cases hist with
  | nil => simp [emitQuery,partsRun,DelimitedWordPattern.sourceParts,DelimiterTemplate.run,evV,length_sfx x ready.bound]
  | cons j js =>
    rw [emitQuery,if_neg (by simp)]
    exact CopyBodyProjections.queryAt_physical g h (address base args.length e (j::js)) d j js args emitted ready.length ready.positive
      (normalized_scope args.length e he (j::js) hh) (hi.2 (j::js) hh) ready.source_fo ready.args_fo x E (k+1) p ready.bound ready.equal ready.free W ready.success

theorem plan_eval (g h : MGrammar) (base : Nat) (d : Char) (e : Body)
    (args emitted : List MExp) (he : check args.length e=true)
    (x : List Char) (E : List (List Char)) (k p : Nat) (W : List (List Char))
    (ready : Ready g h x E (k+1) p d args emitted W) (hi : Installed h base args.length d e) :
    ∀ plan, (∀ hist∈plan.keys, hist∈(normalized e).keys) →
    evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (emitPlan base args.length e emitted plan) p=
      resolve d W (sfx x p) (plan.eval (query d W (sfx x p)))
  | .fail,_ => by simp [emitPlan,MExp.failAlways,evV,Plan.eval,resolve]
  | .undef,_ => by
    rw [emitPlan,evV_star,evStar_stuck (show evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E .eps p=some (some p) from rfl) (Nat.lt_irrefl _)]
    rfl
  | .done hist,hk => query_eval g h base d e args emitted he x E k p W ready hi hist (hk hist (by simp [Plan.keys]))
  | .branch hist a b,hk => by
    have hq := query_eval g h base d e args emitted he x E k p W ready hi hist (hk hist (by simp [Plan.keys]))
    have htest : evV h x .callByValueSeq (tblV h x .callByValueSeq (k+1)) E (.andP (emitQuery base args.length e emitted hist)) p=
        if query d W (sfx x p) hist then some (some p) else some none := by
      rw [CallLookahead.evV_peek,hq]
      cases hr : partsRun d W hist (sfx x p) <;> simp [query,hr,CallLookahead.peek]
    rw [emitPlan,ScannerFrontier.branch_eval _ _ _ p _ htest]
    have ha := plan_eval g h base d e args emitted he x E k p W ready hi a (fun hist hh => hk hist (by simp [Plan.keys,hh]))
    have hb := plan_eval g h base d e args emitted he x E k p W ready hi b (fun hist hh => hk hist (by simp [Plan.keys,hh]))
    cases hq : query d W (sfx x p) hist <;> simp [Plan.eval,hq,ha,hb]

def initial (k p : Nat) : Res := match k with | 0 => none | _+1 => some (some p)

theorem initialized (h : MGrammar) (base : Nat) (hr : ruleAtM h.rules base=some ⟨0,.eps⟩)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length) :
    evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.call base []) p=initial k p := by
  rw [evV_call_seq hr rfl,evSeq_nil]
  change valAt (tblV h x .callByValueSeq k base []) p=_
  cases k with
  | zero => rfl
  | succ k => rw [valAt_tblV_succ hr [] hp]; rfl

/-- Full actual calls preserve all three outcomes. The nullary gate keeps
clock zero undefined even when the normalized source body returns epsilon. -/
theorem physical (g h : MGrammar) (base : Nat) (d : Char) (e : Body)
    (args emitted : List MExp) (he : check args.length e=true)
    (hsource : ruleAtM g.rules base=some ⟨args.length,render d e⟩) (hi : Installed h base args.length d e)
    (hg : g.FirstOrder) (ha : MExp.FirstOrderArgs args) (hn : 0<args.length) (hlen : emitted.length=args.length)
    (x : List Char) (E : List (List Char)) (k p : Nat) (hp : p≤x.length)
    (heq : ∀ i, (hi : i<args.length) → evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (emitted[i]'(by omega)) p)
    (hfree : ∀ i, (hi : i<args.length) → ∀ q,
      evV g x .callByValuePar (tblV g x .callByValuePar k) E args[i] p=some (some q) → DelimitedCopyProjection.Free d (pre x p q)) :
    evV g x .callByValuePar (tblV g x .callByValuePar k) E (.call base args) p=
      evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (head base args.length e emitted) p := by
  rw [evV_call_par hsource rfl (by decide)]
  have hargs := ParentPatternTransfer.arguments_congr g h x (tblV g x .callByValuePar k) (tblV h x .callByValueSeq k) E p args emitted hlen heq
  unfold head
  change _=(match evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (DelimitedPatternEvaluation.preflight emitted) p with
    | some (some q) => evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.seq (.call base []) (emitPlan base args.length e emitted (normalized e))) q | other => other)
  rw [DelimitedPatternEvaluation.preflight_eval,←hargs]
  cases hs : evParArgs g x .callByValuePar (tblV g x .callByValuePar k) E args p with
  | none => rfl
  | some v => cases v with
    | none => rfl
    | some W =>
      change valAt (tblV g x .callByValuePar k base W) p=evV h x .callByValueSeq (tblV h x .callByValueSeq k) E (.seq (.call base []) (emitPlan base args.length e emitted (normalized e))) p
      cases k with
      | zero => rw [evV_seq_none (initialized h base hi.1 x E 0 p hp)]; rfl
      | succ k =>
        rw [valAt_tblV_succ hsource W hp,CopyBodyEvaluation.physical g x .callByValuePar _ (tblV_ok _ _ _ k) W d args.length e he p hp,
          evV_seq_ok (initialized h base hi.1 x E (k+1) p hp)]
        have ready : Ready g h x E (k+1) p d args emitted W := ⟨hg,ha,hn,hlen,hp,heq,hfree,hs⟩
        rw [plan_eval g h base d e args emitted he x E k p W ready hi (normalized e) (fun _ hm => hm),CopyBodyEvaluation.normalized_run]

end Shallot.MacroPeg.CBV.CopyBodyEmission
