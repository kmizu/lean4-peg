import MacroPeg.CBV.AdjacentCallsiteRecursive
import MacroPeg.CBV.ReplayFusion
import MacroPeg.CBV.CodewordControlRecursive

/-! Mix arbitrary-argument replay users with shifted codeword users in one
fixed recursive grammar.

A replay user begins with param0; its target removes that first replay and
keeps a single whole capture. Its argument may be any Body, including other
user calls under parameters, choice, predicates, sequence, and repetition.
A shifted user begins with A;param0; its target uses adjacent comparisons
and keeps two consecutive parts of its single source capture.

The row kind selects the target parameter view. Caller-side argument
compilation always uses the caller's view, including recursive calls inside
general arguments. The recursive row relation combines arbitrary prefix
traces for replay rows with codeword traces for shifted rows. Both kinds
use actual prefix seeds and the same ordinary unary comparator row.

This unifies two restricted entry shapes, not all first-order user bodies.
The shared independent Pure prefix-code A and call-free codeword controls
are needed only for shifted calls. -/
namespace Shallot.MacroPeg.CBV.MixedAdjacentRecursive
open ClockFreezing (Table)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)
open CodewordControlFilter (wholeView)
open CodewordControlRecursive (wordAt word_eval)

open AdjacentCallsiteRecursive (Header Argument rest argument checks rest_firstOrder
  argument_syntax argument_firstOrder checks_firstOrder)

def view (split : Bool) (e : MExp) : MExp := if split then wholeView e else e

theorem view_firstOrder (split : Bool) (e : MExp) (he : e.FirstOrder) :
    (view split e).FirstOrder := by
  cases split
  · exact he
  · exact CodewordControlFilter.wholeView_firstOrder e he

inductive Body (H : Header) where
  | call (rule : Nat) (argument : Argument H)
  | replay (rule : Nat) (argument : Body H)
  | seq (a b : Body H)
  | alt (a b : Body H)
  | star (a : Body H)
  | notP (a : Body H)
  | param (index : Nat)
  | eps
  | any
  | chr (c : Char)
  | range (a b : Char)
  | lit (word : List Char)

structure Spec (H : Header) where
  split : Bool
  body : Body H

def sourcePrefix (H : Header) (split : Bool) : MExp :=
  if split then .seq H.head (.param 0) else .param 0
def targetPrefix (split : Bool) : MExp := if split then .param 0 else .eps

def lexical (H : Header) (x : List Char) (p : Nat) : Res := RuntimePrefixGrammar.lexical H x p

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) : evV g x s T E H.head p=lexical H x p :=
  RuntimePrefixGrammar.head_eval H g x s T E p

def render (H : Header) (tails : List (Spec H)) (par split : Bool) : Body H → MExp
  | .call i a => match tails[i]? with
    | none => MExp.failAlways
    | some r => if r.split then
        if par then .call (i+1) [argument H a]
        else .seq (.andP (view split (argument H a))) (.seq (.andP (view split (checks H a)))
          (.call (i+1) [H.head,view split (rest H a)]))
      else MExp.failAlways
  | .replay i a => match tails[i]? with
    | none => MExp.failAlways
    | some r => if r.split then MExp.failAlways else .call (i+1) [render H tails par split a]
  | .seq a b => .seq (render H tails par split a) (render H tails par split b)
  | .alt a b => .alt (render H tails par split a) (render H tails par split b)
  | .star a => .star (render H tails par split a)
  | .notP a => .notP (render H tails par split a)
  | .param k => if par then .param k else view split (.param k)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w

def source (H : Header) (tails : List (Spec H)) : MGrammar :=
  ⟨⟨1,.param 0⟩::tails.map (fun r => ⟨1,.seq (sourcePrefix H r.split) (render H tails true r.split r.body)⟩)⟩
def target (H : Header) (tails : List (Spec H)) : MGrammar :=
  ⟨⟨1,.param 0⟩::tails.map (fun r => ⟨if r.split then 2 else 1,
    .seq (targetPrefix r.split) (render H tails false r.split r.body)⟩)⟩
def pick (i : Nat) : Bool := decide (i=0)

theorem render_firstOrder (H : Header) (tails : List (Spec H)) (par split : Bool) :
    ∀ e, (render H tails par split e).FirstOrder
  | .call i a => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some r =>
      cases hkind : r.split <;> simp only [hkind,Bool.false_eq_true,ite_false,ite_true]
      · trivial
      · cases par
        · exact ⟨view_firstOrder split _ (argument_firstOrder H a),
            view_firstOrder split _ (checks_firstOrder H a),pure_firstOrder _ H.pure,
            view_firstOrder split _ (rest_firstOrder H a),True.intro⟩
        · exact ⟨argument_firstOrder H a,True.intro⟩
  | .replay i a => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some r =>
      cases hkind : r.split <;> simp only [hkind,Bool.false_eq_true,ite_false,ite_true]
      · exact ⟨render_firstOrder H tails par split a,True.intro⟩
      · trivial
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par split a,render_firstOrder H tails par split b⟩
  | .star a | .notP a => render_firstOrder H tails par split a
  | .param k => by cases par; exact view_firstOrder split _ True.intro; trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial

theorem source_firstOrder (H : Header) (tails : List (Spec H)) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    refine ⟨?_,render_firstOrder H tails true b.split b.body⟩
    cases b.split
    · trivial
    · exact ⟨pure_firstOrder _ H.pure,True.intro⟩
theorem target_firstOrder (H : Header) (tails : List (Spec H)) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    refine ⟨?_,render_firstOrder H tails false b.split b.body⟩
    cases b.split <;> trivial

theorem source_rule (H : Header) (tails : List (Spec H)) (i : Nat) :
    ruleAtM (source H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨1,.seq (sourcePrefix H b.split) (render H tails true b.split b.body)⟩) := by
  simp [source,ruleAtM_eq_getElem?]
theorem target_rule (H : Header) (tails : List (Spec H)) (i : Nat) :
    ruleAtM (target H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨if b.split then 2 else 1,.seq (targetPrefix b.split) (render H tails false b.split b.body)⟩) := by
  simp [target,ruleAtM_eq_getElem?]

theorem comparator_stable (H : Header) (g : MGrammar)
    (hr : ruleAtM g.rules 0=some ⟨1,.param 0⟩) (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows g x s pick 1 := by
  intro k i hi W
  have he : i=0 := by simpa [pick] using hi
  subst i
  have hn : 1+k=k+1 := by omega
  rw [hn]
  simp only [tblV,hr]
  apply List.map_congr_left
  intro p hp
  rfl

abbrev sourceTable (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (source H tails) x .callByValuePar pick 1
    (SeededClock.prefixSeed (source H tails) x .callByValuePar pick 1) k
abbrev targetTable (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (target H tails) x .callByValueSeq pick 1
    (SeededClock.prefixSeed (target H tails) x .callByValueSeq pick 1) k

theorem source_ok (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) :
    OkTV x.length (sourceTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (1+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem source_sound (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) :
    SoundTV (source H tails) x .callByValuePar (sourceTable H tails x k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound (source_firstOrder H tails) (by decide) _ i rule W hr ha p hp v
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem target_ok (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) :
    OkTV x.length (targetTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (1+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem target_sound (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) :
    SoundTV (target H tails) x .callByValueSeq (targetTable H tails x k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound (target_firstOrder H tails) (by decide) _ i rule W hr ha p hp v
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)

def Parameters (H : Header) (tails : List (Spec H)) (x : List Char) (T U : Table)
    (split : Bool) (E F : List (List Char)) : Prop :=
  if split then ∀ k p,
    evV (source H tails) x .callByValuePar T E (.param k) p=
      evV (target H tails) x .callByValueSeq U F (wholeView (.param k)) p
  else E=F

theorem parameters_empty (H : Header) (tails : List (Spec H)) (x : List Char) (T U : Table) :
    Parameters H tails x T U false [] [] := rfl

theorem parameters_parts (H : Header) (tails : List (Spec H)) (x : List Char) (T U : Table)
    (u v : List Char) : Parameters H tails x T U true [u++v] [u,v] := by
  intro k p
  rw [CodewordControlFilter.wholeView_eval _ x _ U u v (.param k) True.intro p]
  cases k <;> rfl

private theorem seq_eps (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (e : MExp) (p : Nat) :
    evV g x s T E (.seq e .eps) p=evV g x s T E e p := by
  change (match evV g x s T E e p with
    | some (some z) => some (some z) | other => other)=_
  cases evV g x s T E e p with
  | none => rfl
  | some r => cases r <;> rfl

def prefixAt (H : Header) (x : List Char) (W : List (List Char)) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) W (.seq H.head (.param 0)) p

theorem prefix_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (W : List (List Char)) (p : Nat) :
    evV g x s T W (.seq H.head (.param 0)) p=prefixAt H x W p := by
  unfold prefixAt
  change (match evV g x s T W H.head p with
    | some (some j) => evV g x s T W (.param 0) j | other => other)=
    (match evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) W H.head p with
    | some (some j) => evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) W (.param 0) j | other => other)
  simp only [head_eval]
  cases lexical H x p with
  | none => rfl
  | some r => cases r <;> rfl


theorem prefix_bridge (H : Header) (x : List Char) (p j q : Nat) (ws : List (List Char))
    (hp : p≤x.length) (hq : q≤x.length) (ha : lexical H x p=some (some j))
    (hw : ∀ w∈ws, H.code w) (htrace : sfx x j=ws.flatten++sfx x q) :
    prefixAt H x [pre x p j++ws.flatten] p=
      if (pre x p j++ws.flatten).IsPrefix (sfx x j) then wordAt x (pre x p j) q else some none := by
  unfold prefixAt
  rw [evV_seq_ok ((head_eval H _ x _ _ _ p).trans ha)]
  by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
  · rw [if_pos he]
    have hu := (RuntimePrefixGrammar.lexical_success H x p j hp ha).2.2
    have hew : (pre x p j++ws.flatten).IsPrefix (ws.flatten++sfx x q) := by simpa only [htrace] using he
    have huniform := CodewordReplay.source_prefix_forces H.prefixFree (pre x p j) ws (sfx x q) hu hw hew
    have hr := CodewordControlFilter.replay_trace (⟨[]⟩ : MGrammar) x .callByValuePar (fun _ _ => [])
      H.prefixFree (pre x p j) hu ws hw j q hq htrace .eps True.intro
    rw [if_pos huniform] at hr
    simpa only [wholeView,MExp.subst,seq_eps,word_eval] using hr
  · rw [if_neg he]
    have hn : Shallot.stripPrefix? (pre x p j++ws.flatten) (sfx x j)=none := by
      cases hh : Shallot.stripPrefix? (pre x p j++ws.flatten) (sfx x j) with
      | none => rfl
      | some rest => exact False.elim (he ⟨rest,((CBVtoCBN.stripPrefix_exact _ _ _).mp hh).symm⟩)
    simp [evV,hn]

theorem prefix_positive (H : Header) (x : List Char) (p j q : Nat) (ws : List (List Char))
    (hp : p≤x.length) (hq : q≤x.length) (ha : lexical H x p=some (some j))
    (hw : ∀ w∈ws, H.code w) (htrace : sfx x j=ws.flatten++sfx x q)
    (he : (pre x p j++ws.flatten).IsPrefix (sfx x j)) :
    ∃ z, wordAt x (pre x p j) q=some (some z) := by
  obtain ⟨r,hr⟩ := he
  have he : (pre x p j++ws.flatten).IsPrefix (sfx x j) := ⟨r,hr⟩
  have hs : Shallot.stripPrefix? (pre x p j++ws.flatten) (sfx x j)=some r :=
    (CBVtoCBN.stripPrefix_exact _ _ _).mpr hr.symm
  have h := prefix_bridge H x p j q ws hp hq ha hw htrace
  rw [if_pos he] at h
  have hh : prefixAt H x [pre x p j++ws.flatten] p=some (some r.length) := by
    unfold prefixAt
    rw [evV_seq_ok ((head_eval H _ x _ _ _ p).trans ha)]
    simp [evV,hs]
  exact ⟨r.length,h.symm.trans hh⟩

theorem compare_eval (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call 0 [H.head]) p=
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq 1) E (.call 0 [H.head]) p := by
  have hr : ruleAtM (target H tails).rules 0=some ⟨1,.param 0⟩ := rfl
  rw [evV_call_seq hr rfl,evV_call_seq hr rfl]
  simp only [evSeqArgs,head_eval]
  cases ha : lexical H x p with
  | none => rfl
  | some r => cases r with
    | none => rfl
    | some j =>
      have hj := (RuntimePrefixGrammar.lexical_success H x p j hp ha).1
      dsimp only []
      unfold targetTable
      rw [SeededClock.rows _ x _ pick 1 _ (SeededClock.prefixSeed_rows _ x _ pick 1) k 0
        (by simp [pick])]

theorem compare_spec (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat)
    (E : List (List Char)) (p q : Nat) (hp : p≤x.length)
    (ha : evV (target H tails) x .callByValueSeq (targetTable H tails x k) E H.head p=some (some q)) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.andP (.call 0 [H.head])) p=
      if (pre x p q).IsPrefix (sfx x q) then some (some p) else some none := by
  rw [CallLookahead.evV_peek,compare_eval H tails x k E p hp]
  rw [←CallLookahead.evV_peek]
  apply AdjacentCodewordControl.physical_compare (target H tails) x 0 0 rfl E H.head p q hp
  rw [head_eval] at ha ⊢
  exact ha

/-- Parameter views are valid inside the caller's complete comparison
expression, including its fresh unary Seq calls. -/
theorem views_eval (H : Header) (tails : List (Spec H)) (x : List Char) (T U : Table)
    (split : Bool) (E F : List (List Char)) (hEF : Parameters H tails x T U split E F)
    (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV (target H tails) x .callByValueSeq U F (view split e) p=
      evV (target H tails) x .callByValueSeq U E e p := by
  cases split
  · change E=F at hEF
    subst F
    rfl
  · apply CaptureViews.evV_rebind [CaptureViews.prefixExpr 2] E _ e he p
    intro k q
    exact (hEF k q).symm

/-- Row correspondence depends on the actual captured word trace, not on
which parent selected that trace. The guard includes the final extra copy;
its failure must already be finite failure in the prefix-seeded source row. -/
def Shifted (H : Header) (tails : List (Spec H)) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b →
    (b.split=true → ∀ p j q (ws : List (List Char)), p≤x.length → q≤x.length →
      lexical H x p=some (some j) → (∀ w∈ws, H.code w) → sfx x j=ws.flatten++sfx x q →
      valAt (T (i+1) [pre x p j++ws.flatten]) p=
        if (pre x p j++ws.flatten).IsPrefix (sfx x j)
        then valAt (U (i+1) [pre x p j,ws.flatten]) q else some none) ∧
    (b.split=false → ∀ w p q, p≤x.length → q≤x.length → sfx x p=w++sfx x q →
      valAt (T (i+1) [w]) p=valAt (U (i+1) [w]) q)

theorem evaluator_of_shift (H : Header) (tails : List (Spec H)) (x : List Char)
    (T : Table) (hSound : SoundTV (source H tails) x .callByValuePar T) (hOk : OkTV x.length T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e split E F, Parameters H tails x T (targetTable H tails x k) split E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true split e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false split e) p
  | .call i a, split, E, F, hEF, p, hp => by
    let U := targetTable H tails x k
    have hargs := LastCodewordGrammar.syntax_eval (source H tails) (target H tails) x .callByValuePar .callByValueSeq T U hOk E
      (argument H a) (argument_syntax H a) p hp
    have hviewB := views_eval H tails x T U split E F hEF (argument H a) (argument_firstOrder H a) p
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      cases hkind : b.split with
      | false => simp only [render,hr,hkind,Bool.false_eq_true,ite_false]; rfl
      | true =>
        have hs : ruleAtM (source H tails).rules (i+1)=some
            ⟨1,.seq (.seq H.head (.param 0)) (render H tails true true b.body)⟩ := by simp only [source_rule,hr,Option.map,hkind,sourcePrefix,ite_true]
        have ht : ruleAtM (target H tails).rules (i+1)=some
            ⟨2,.seq (.param 0) (render H tails false true b.body)⟩ := by simp only [target_rule,hr,Option.map,hkind,targetPrefix,ite_true]
        simp only [render,hr,hkind,ite_true]
        rw [evV_call_par hs rfl (by decide)]
        change _=(match evV (target H tails) x .callByValueSeq U F (.andP (view split (argument H a))) p with
          | some (some z) => evV (target H tails) x .callByValueSeq U F
            (.seq (.andP (view split (checks H a))) (.call (i+1) [H.head,view split (rest H a)])) z
          | other => other)
        rw [CallLookahead.evV_peek,hviewB,←hargs]
        simp only [evParArgs]
        cases hb : evV (source H tails) x .callByValuePar T E (argument H a) p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some q =>
            have hq := evV_ok hOk (argument H a) p hp q hb
            change evV (source H tails) x .callByValuePar T E (.seq H.head (rest H a)) p=some (some q) at hb
            cases ha : lexical H x p with
            | none => simp only [evV,head_eval,ha] at hb; cases hb
            | some result => cases result with
              | none => simp only [evV,head_eval,ha] at hb; cases hb
              | some j =>
                have hj := (RuntimePrefixGrammar.lexical_success H x p j hp ha).1
                have haS := (head_eval H (source H tails) x .callByValuePar T E p).trans ha
                rw [evV_seq_ok haS] at hb
                have haH := (head_eval H (target H tails) x .callByValueSeq U E p).trans ha
                have hdH := (LastCodewordGrammar.syntax_eval (source H tails) (target H tails) x .callByValuePar .callByValueSeq
                  T U hOk E (rest H a) a.controlSyntax j hj).symm.trans hb
                obtain ⟨ws,hw,htrace,_⟩ := AdjacentCodewordControl.success (target H tails) x
                  .callByValueSeq (by decide) U (target_sound H tails x k) (target_ok H tails x k)
                  H.head (pure_firstOrder _ H.pure) H.prefixFree E (.call 0 [H.head])
                  (compare_spec H tails x k E)
                  (fun z t hz ht => H.captured _ x _ U E z t hz ht) a.control j q hj hdH
                have hpw : pre x j q=ws.flatten := by
                  simpa only [length_sfx x hj,length_sfx x hq] using pre_eq (sfx_is_suffix x j) htrace
                have hfull : sfx x p=(pre x p j++ws.flatten)++sfx x q := by
                  rw [(RuntimePrefixGrammar.lexical_success H x p j hp ha).2.1,htrace,List.append_assoc]
                have hcap : pre x p q=pre x p j++ws.flatten := by
                  simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) hfull
                have hchecks := AdjacentCodewordControl.argument_checks (target H tails) x .callByValueSeq (by decide)
                  U (target_sound H tails x k) (target_ok H tails x k) H.head (pure_firstOrder _ H.pure)
                  H.prefixFree E (.call 0 [H.head]) (compare_spec H tails x k E)
                  (fun z t hz ht => H.captured _ x _ U E z t hz ht) a.control p j q hp haH hdH
                change evV (target H tails) x .callByValueSeq U E (checks H a) p=_ at hchecks
                simp only [hpw] at hchecks
                dsimp only [CallLookahead.peek]
                rw [hcap,(hShift i b hr).1 hkind p j q ws hp hq ha hw htrace]
                change _=(match evV (target H tails) x .callByValueSeq U F (.andP (view split (checks H a))) p with
                  | some (some z) => evV (target H tails) x .callByValueSeq U F
                      (.call (i+1) [H.head,view split (rest H a)]) z | other => other)
                rw [CallLookahead.evV_peek,views_eval H tails x T U split E F hEF _ (checks_firstOrder H a) p,hchecks]
                by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
                · simp only [if_pos he, CallLookahead.peek]
                  rw [evV_call_seq ht rfl]
                  simp only [evSeqArgs,head_eval,ha]
                  rw [views_eval H tails x T U split E F hEF _ (rest_firstOrder H a) j,hdH]
                  simp only [hpw]
                  rfl
                · simp only [if_neg he, CallLookahead.peek]
  | .replay i a, split, E, F, hEF, p, hp => by
    have harg := evaluator_of_shift H tails x T hSound hOk k hShift a split E F hEF p hp
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      cases hkind : b.split with
      | true => simp only [render,hr,hkind,ite_true]; rfl
      | false =>
        have hs : ruleAtM (source H tails).rules (i+1)=some
            ⟨1,.seq (.param 0) (render H tails true false b.body)⟩ := by
          simp only [source_rule,hr,Option.map,hkind,sourcePrefix,Bool.false_eq_true,ite_false]
        have ht : ruleAtM (target H tails).rules (i+1)=some
            ⟨1,.seq .eps (render H tails false false b.body)⟩ := by
          simp only [target_rule,hr,Option.map,hkind,targetPrefix,Bool.false_eq_true,ite_false]
        simp only [render,hr,hkind,Bool.false_eq_true,ite_false]
        rw [evV_call_par hs rfl (by decide),evV_call_seq ht rfl]
        simp only [evParArgs,evSeqArgs]
        rw [←harg]
        cases hv : evV (source H tails) x .callByValuePar T E (render H tails true split a) p with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some q =>
            obtain ⟨hq,htrace⟩ := ReplayFusion.success_prefix hSound E _
              (render_firstOrder H tails true split a) p q hp hv
            exact (hShift i b hr).2 hkind (pre x p q) p q hp hq htrace
  | .seq a b, split, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hSound hOk k hShift a split E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true split a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T hSound hOk k hShift b split E F hEF q (evV_ok hOk _ p hp q hv)
  | .alt a b, split, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hSound hOk k hShift a split E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true split a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]; exact evaluator_of_shift H tails x T hSound hOk k hShift b split E F hEF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, split, E, F, hEF, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T hSound hOk k hShift a split E F hEF q (by omega))
  | .notP a, split, E, F, hEF, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T hSound hOk k hShift a split E F hEF p hp]
  | .param z, split, E, F, hEF, p, _ => by
    cases split
    · change E=F at hEF
      subst F
      rfl
    · exact hEF z p
  | .eps, _, _, _, _, _, _ | .any, _, _, _, _, _, _ | .chr _, _, _, _, _, _, _
  | .range _ _, _, _, _, _, _, _ | .lit _, _, _, _, _, _, _ => rfl

theorem source_step (H : Header) (tails : List (Spec H)) (x : List Char) (k i : Nat)
    (b : Spec H) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) (i+1) W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W
        (.seq (sourcePrefix H b.split) (render H tails true b.split b.body)) p := by
  exact SeededClock.user_step (source H tails) x .callByValuePar pick 1 _ k (i+1)
    (by simp [pick]) ⟨1,.seq (sourcePrefix H b.split) (render H tails true b.split b.body)⟩
    (by rw [source_rule,hr]; rfl) W p hp

theorem target_step (H : Header) (tails : List (Spec H)) (x : List Char) (k i : Nat)
    (b : Spec H) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable H tails x (k+1) (i+1) W) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) W
        (.seq (targetPrefix b.split) (render H tails false b.split b.body)) p := by
  exact SeededClock.user_step (target H tails) x .callByValueSeq pick 1 _ k (i+1)
    (by simp [pick]) ⟨if b.split then 2 else 1,
      .seq (targetPrefix b.split) (render H tails false b.split b.body)⟩
    (by rw [target_rule,hr]; rfl) W p hp

private theorem param_trace (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (w : List Char) (p q : Nat) (hq : q≤x.length) (ht : sfx x p=w++sfx x q) :
    evV g x s T [w] (.param 0) p=some (some q) := by
  have hh := (CBVtoCBN.stripPrefix_exact w (sfx x p) (sfx x q)).mpr ht
  simp only [evV,List.getElem?_cons_zero,hh,length_sfx x hq]

theorem tables_shifted (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr
    constructor
    · intro hkind p j q ws hp hq ha hw htrace
      have hs : ruleAtM (source H tails).rules (i+1)=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true true b.body)⟩ := by
        simp only [source_rule,hr,Option.map,hkind,sourcePrefix,ite_true]
      have ht : ruleAtM (target H tails).rules (i+1)=some
          ⟨2,.seq (.param 0) (render H tails false true b.body)⟩ := by
        simp only [target_rule,hr,Option.map,hkind,targetPrefix,ite_true]
      change valAt (SeededClock.prefixSeed _ x .callByValuePar pick 1 (i+1) [pre x p j++ws.flatten]) p=_
      rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ hs _ p hp,prefix_eval,
        prefix_bridge H x p j q ws hp hq ha hw htrace]
      by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
      · simp only [if_pos he]
        change _=valAt (SeededClock.prefixSeed _ x .callByValueSeq pick 1 (i+1) [pre x p j,ws.flatten]) q
        rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 2 _ _ ht _ q hq,word_eval]
      · simp only [if_neg he,ite_true]
    · intro hkind w p q hp hq htrace
      have hs : ruleAtM (source H tails).rules (i+1)=some
          ⟨1,.seq (.param 0) (render H tails true false b.body)⟩ := by
        simp only [source_rule,hr,Option.map,hkind,sourcePrefix,Bool.false_eq_true,ite_false]
      have ht : ruleAtM (target H tails).rules (i+1)=some
          ⟨1,.seq .eps (render H tails false false b.body)⟩ := by
        simp only [target_rule,hr,Option.map,hkind,targetPrefix,Bool.false_eq_true,ite_false]
      change valAt (SeededClock.prefixSeed _ x .callByValuePar pick 1 (i+1) [w]) p=
        valAt (SeededClock.prefixSeed _ x .callByValueSeq pick 1 (i+1) [w]) q
      rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ hs _ p hp,
        SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ ht _ q hq,
        param_trace _ x _ _ w p q hq htrace]
      rfl
  | succ k ih =>
    intro i b hr
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    constructor
    · intro hkind p j q ws hp hq ha hw htrace
      rw [source_step H tails x k i b hr _ p hp]
      simp only [hkind,sourcePrefix,ite_true]
      have hpre : evV (source H tails) x .callByValuePar T [pre x p j++ws.flatten]
          (.seq H.head (.param 0)) p=
          if (pre x p j++ws.flatten).IsPrefix (sfx x j) then wordAt x (pre x p j) q else some none :=
        (prefix_eval H _ x _ T _ p).trans (prefix_bridge H x p j q ws hp hq ha hw htrace)
      by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
      · rw [if_pos he] at hpre ⊢
        obtain ⟨z,hz⟩ := prefix_positive H x p j q ws hp hq ha hw htrace he
        rw [evV_seq_ok (hpre.trans hz),target_step H tails x k i b hr _ q hq]
        simp only [hkind,targetPrefix,ite_true]
        rw [evV_seq_ok ((word_eval (target H tails) x .callByValueSeq U (pre x p j) ws.flatten q).trans hz)]
        have hzbound := evV_ok (source_ok H tails x k) (.seq H.head (.param 0)) p hp z (hpre.trans hz)
        exact evaluator_of_shift H tails x T (source_sound H tails x k) (source_ok H tails x k) k ih
          b.body true _ _ (parameters_parts H tails x T U _ _) z hzbound
      · rw [if_neg he] at hpre ⊢
        exact evV_seq_fail hpre
    · intro hkind w p q hp hq htrace
      rw [source_step H tails x k i b hr _ p hp,target_step H tails x k i b hr _ q hq]
      simp only [hkind,sourcePrefix,targetPrefix,Bool.false_eq_true,ite_false]
      rw [evV_seq_ok (param_trace _ x _ T w p q hq htrace),
        evV_seq_ok (show evV (target H tails) x .callByValueSeq U [w] .eps q=some (some q) from rfl)]
      exact evaluator_of_shift H tails x T (source_sound H tails x k) (source_ok H tails x k) k ih
        b.body false [w] [w] rfl q hq

theorem evaluator_eq (H : Header) (tails : List (Spec H)) (x : List Char) (k : Nat)
    (e : Body H) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E (render H tails true false e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (render H tails false false e) p :=
  evaluator_of_shift H tails x _ (source_sound H tails x k) (source_ok H tails x k) k
    (tables_shifted H tails x k) e false E E rfl p hp

theorem stable_eq (H : Header) (tails : List (Spec H)) (e : Body H) (x : List Char) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
      [] (render H tails true false e) x.length=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
      [] (render H tails false false e) x.length := by
  have hsource := comparator_stable H (source H tails) rfl x .callByValuePar
  have htarget := comparator_stable H (target H tails) rfl x .callByValueSeq
  have hdefined (v : Option Nat) :
      evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
        [] (render H tails true false e) x.length=some v ↔
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
        [] (render H tails false false e) x.length=some v := by
    rw [←tblV_stable (source H tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target H tails) x .callByValueSeq (Nat.le_refl _),
      ←SeededClock.defined_iff (source H tails) x .callByValuePar pick 1 _
        (SeededClock.prefixSeed_lower _ x _ pick 1) (SeededClock.prefixSeed_upper _ x _ pick 1) hsource,
      ←SeededClock.defined_iff (target H tails) x .callByValueSeq pick 1 _
        (SeededClock.prefixSeed_lower _ x _ pick 1) (SeededClock.prefixSeed_upper _ x _ pick 1) htarget]
    exact exists_congr (fun k => by rw [evaluator_eq H tails x k e [] x.length (Nat.le_refl _)])
  cases hs : evV (source H tails) x .callByValuePar
      (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x)) [] (render H tails true false e) x.length with
  | none =>
    cases ht : evV (target H tails) x .callByValueSeq
        (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x)) [] (render H tails false false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves every finite observation on
unchanged input strings. Captures can have unbounded input-dependent word
counts, with retained parameters controlling their selection at each call. -/
theorem observations_iff (H : Header) (tails : List (Spec H)) (e : Body H)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H tails) .callByValuePar (render H tails true false e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false false e) x r := by
  rw [←decideObsV_iff (source_firstOrder H tails) (by decide) (render_firstOrder H tails true false e),
    ←decideObsV_iff (target_firstOrder H tails) (by decide) (render_firstOrder H tails false false e)]
  unfold decideObsV
  rw [stable_eq]

theorem language_translation (H : Header) (tails : List (Spec H)) (e : Body H) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source H tails) .callByValuePar (render H tails true false e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target H tails,render H tails false false e,target_firstOrder H tails,render_firstOrder H tails false false e,
    fun x => observations_iff H tails e x (some [])⟩


end Shallot.MacroPeg.CBV.MixedAdjacentRecursive
