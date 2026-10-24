import MacroPeg.CBV.AdjacentCodewordCalls
import MacroPeg.CBV.CodewordControlRecursive

/-! A fixed recursive translation for parent-dependent codeword control.

A source call captures `A;D` and its unary user row begins with `A;param0`.
The target keeps tests of D in the caller, compares adjacent A-codewords
with one ordinary unary Seq row, then captures A and D in two Seq arguments.
The target user first replays A and continues with a view of the whole value.

Unlike CodewordControlRecursive, D may inspect retained caller parameters.
User tails can call each other, sequence, choose, negate, and repeat; the
source and target are fixed grammars independent of the input. A remains
a shared Pure prefix-code header, and D is shared call-free syntax. This
is a restricted grammar family, not a general Par-to-Seq compiler. -/
namespace Shallot.MacroPeg.CBV.AdjacentCodewordRecursive
open ClockFreezing (Table)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)
open CodewordControlFilter (wholeView)
open CodewordControlRecursive (wordAt word_eval)

structure Header extends RuntimePrefixGrammar.Header where
  control : CodewordControlFilter.Expr
  controlSyntax : HelperArgument.Syntax 0 (CodewordControlFilter.render head control)

def rest (H : Header) : MExp := CodewordControlFilter.render H.head H.control
def argument (H : Header) : MExp := .seq H.head (rest H)
def checks (H : Header) : MExp :=
  AdjacentCodewordControl.filter H.head (.call 0 [H.head]) (.seq .token H.control)

theorem rest_firstOrder (H : Header) : (rest H).FirstOrder :=
  HelperArgument.firstOrder 0 _ H.controlSyntax
theorem argument_syntax (H : Header) : HelperArgument.Syntax 0 (argument H) :=
  ⟨LastCodewordGrammar.pure_syntax H.head H.pure,H.controlSyntax⟩
theorem argument_firstOrder (H : Header) : (argument H).FirstOrder :=
  ⟨pure_firstOrder _ H.pure,rest_firstOrder H⟩
theorem checks_firstOrder (H : Header) : (checks H).FirstOrder :=
  AdjacentCodewordControl.filter_firstOrder H.head (.call 0 [H.head])
    (pure_firstOrder _ H.pure) ⟨pure_firstOrder _ H.pure,True.intro⟩
    (.seq .token H.control) (argument_firstOrder H)

def lexical (H : Header) (x : List Char) (p : Nat) : Res := RuntimePrefixGrammar.lexical H.toHeader x p

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) : evV g x s T E H.head p=lexical H x p :=
  RuntimePrefixGrammar.head_eval H.toHeader g x s T E p

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call (i+1) [argument H]
      else .seq (.andP (wholeView (argument H))) (.seq (.andP (wholeView (checks H)))
        (.call (i+1) [H.head,wholeView (rest H)]))
  | .seq a b => .seq (render H tails par a) (render H tails par b)
  | .alt a b => .alt (render H tails par a) (render H tails par b)
  | .star a => .star (render H tails par a)
  | .notP a => .notP (render H tails par a)
  | .param k => if par then .param k else wholeView (.param k)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | _ => MExp.failAlways

def source (H : Header) (tails : List MExp) : MGrammar :=
  ⟨⟨1,.param 0⟩::tails.map (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨⟨1,.param 0⟩::tails.map (fun b => ⟨2,.seq (.param 0) (render H tails false b)⟩)⟩
def pick (i : Nat) : Bool := decide (i=0)

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨CodewordControlFilter.wholeView_firstOrder _ (argument_firstOrder H),
          CodewordControlFilter.wholeView_firstOrder _ (checks_firstOrder H),
          pure_firstOrder _ H.pure,CodewordControlFilter.wholeView_firstOrder _ (rest_firstOrder H),True.intro⟩
      · exact ⟨argument_firstOrder H,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par; exact CodewordControlFilter.wholeView_firstOrder _ True.intro; trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨pure_firstOrder _ H.pure,True.intro⟩,render_firstOrder H tails true b⟩
theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · trivial
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,render_firstOrder H tails false b⟩
theorem source_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (source H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩) := by
  simp [source,ruleAtM_eq_getElem?]
theorem target_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (target H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨2,.seq (.param 0) (render H tails false b)⟩) := by
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

abbrev sourceTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (source H tails) x .callByValuePar pick 1
    (SeededClock.prefixSeed (source H tails) x .callByValuePar pick 1) k
abbrev targetTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (target H tails) x .callByValueSeq pick 1
    (SeededClock.prefixSeed (target H tails) x .callByValueSeq pick 1) k

theorem source_ok (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    OkTV x.length (sourceTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (1+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem source_sound (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    SoundTV (source H tails) x .callByValuePar (sourceTable H tails x k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound (source_firstOrder H tails) (by decide) _ i rule W hr ha p hp v
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem target_ok (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    OkTV x.length (targetTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (1+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)
theorem target_sound (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    SoundTV (target H tails) x .callByValueSeq (targetTable H tails x k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound (target_firstOrder H tails) (by decide) _ i rule W hr ha p hp v
    ((SeededClock.physical_bound _ x _ pick 1 _ (SeededClock.prefixSeed_upper _ x _ pick 1) k i W p).eq_of_some hv)

def Parameters (H : Header) (tails : List MExp) (x : List Char) (T U : Table)
    (E F : List (List Char)) : Prop := ∀ k p,
  evV (source H tails) x .callByValuePar T E (.param k) p=
    evV (target H tails) x .callByValueSeq U F (wholeView (.param k)) p

theorem parameters_empty (H : Header) (tails : List MExp) (x : List Char) (T U : Table) :
    Parameters H tails x T U [] [] := by
  intro k p
  cases k <;> simp [wholeView,CaptureViews.prefixExpr,MExp.subst,argAt,evV,MExp.failAlways,Shallot.stripPrefix?]

theorem parameters_parts (H : Header) (tails : List MExp) (x : List Char) (T U : Table)
    (u v : List Char) : Parameters H tails x T U [u++v] [u,v] := by
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
    have hu := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).2.2
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

theorem compare_eval (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
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
      have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
      dsimp only []
      unfold targetTable
      rw [SeededClock.rows _ x _ pick 1 _ (SeededClock.prefixSeed_rows _ x _ pick 1) k 0
        (by simp [pick])]

theorem compare_spec (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
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
theorem views_eval (H : Header) (tails : List MExp) (x : List Char) (T U : Table)
    (E F : List (List Char)) (hEF : Parameters H tails x T U E F)
    (e : MExp) (he : e.FirstOrder) (p : Nat) :
    evV (target H tails) x .callByValueSeq U F (wholeView e) p=
      evV (target H tails) x .callByValueSeq U E e p := by
  apply CaptureViews.evV_rebind [CaptureViews.prefixExpr 2] E _ e he p
  intro k q
  exact (hEF k q).symm

/-- Row correspondence depends on the actual captured word trace, not on
which parent selected that trace. The guard includes the final extra copy;
its failure must already be finite failure in the prefix-seeded source row. -/
def Shifted (H : Header) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p j q (ws : List (List Char)), p≤x.length → q≤x.length →
    lexical H x p=some (some j) → (∀ w∈ws, H.code w) → sfx x j=ws.flatten++sfx x q →
    valAt (T (i+1) [pre x p j++ws.flatten]) p=
      if (pre x p j++ws.flatten).IsPrefix (sfx x j)
      then valAt (U (i+1) [pre x p j,ws.flatten]) q else some none

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T : Table) (hOk : OkTV x.length T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e E F, Parameters H tails x T (targetTable H tails x k) E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    let U := targetTable H tails x k
    have hargs := LastCodewordGrammar.syntax_eval (source H tails) (target H tails) x .callByValuePar .callByValueSeq T U hOk E
      (argument H) (argument_syntax H) p hp
    have hviewB := views_eval H tails x T U E F hEF (argument H) (argument_firstOrder H) p
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (i+1)=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (i+1)=some
          ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      change _=(match evV (target H tails) x .callByValueSeq U F (.andP (wholeView (argument H))) p with
        | some (some z) => evV (target H tails) x .callByValueSeq U F
          (.seq (.andP (wholeView (checks H))) (.call (i+1) [H.head,wholeView (rest H)])) z
        | other => other)
      rw [CallLookahead.evV_peek,hviewB,←hargs]
      simp only [evParArgs]
      cases hb : evV (source H tails) x .callByValuePar T E (argument H) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          have hq := evV_ok hOk (argument H) p hp q hb
          change evV (source H tails) x .callByValuePar T E (.seq H.head (rest H)) p=some (some q) at hb
          cases ha : lexical H x p with
          | none => simp only [evV,head_eval,ha] at hb; cases hb
          | some result => cases result with
            | none => simp only [evV,head_eval,ha] at hb; cases hb
            | some j =>
              have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
              have haS := (head_eval H (source H tails) x .callByValuePar T E p).trans ha
              rw [evV_seq_ok haS] at hb
              have haH := (head_eval H (target H tails) x .callByValueSeq U E p).trans ha
              have hdH := (LastCodewordGrammar.syntax_eval (source H tails) (target H tails) x .callByValuePar .callByValueSeq
                T U hOk E (rest H) H.controlSyntax j hj).symm.trans hb
              obtain ⟨ws,hw,htrace,_⟩ := AdjacentCodewordControl.success (target H tails) x
                .callByValueSeq (by decide) U (target_sound H tails x k) (target_ok H tails x k)
                H.head (pure_firstOrder _ H.pure) H.prefixFree E (.call 0 [H.head])
                (compare_spec H tails x k E)
                (fun z t hz ht => H.captured _ x _ U E z t hz ht) H.control j q hj hdH
              have hpw : pre x j q=ws.flatten := by
                simpa only [length_sfx x hj,length_sfx x hq] using pre_eq (sfx_is_suffix x j) htrace
              have hfull : sfx x p=(pre x p j++ws.flatten)++sfx x q := by
                rw [(RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).2.1,htrace,List.append_assoc]
              have hcap : pre x p q=pre x p j++ws.flatten := by
                simpa only [length_sfx x hp,length_sfx x hq] using pre_eq (sfx_is_suffix x p) hfull
              have hchecks := AdjacentCodewordControl.argument_checks (target H tails) x .callByValueSeq (by decide)
                U (target_sound H tails x k) (target_ok H tails x k) H.head (pure_firstOrder _ H.pure)
                H.prefixFree E (.call 0 [H.head]) (compare_spec H tails x k E)
                (fun z t hz ht => H.captured _ x _ U E z t hz ht) H.control p j q hp haH hdH
              change evV (target H tails) x .callByValueSeq U E (checks H) p=_ at hchecks
              simp only [hpw] at hchecks
              dsimp only [CallLookahead.peek]
              rw [hcap,hShift i b hr p j q ws hp hq ha hw htrace]
              change _=(match evV (target H tails) x .callByValueSeq U F (.andP (wholeView (checks H))) p with
                | some (some z) => evV (target H tails) x .callByValueSeq U F
                    (.call (i+1) [H.head,wholeView (rest H)]) z | other => other)
              rw [CallLookahead.evV_peek,views_eval H tails x T U E F hEF _ (checks_firstOrder H) p,hchecks]
              by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
              · simp only [if_pos he, CallLookahead.peek]
                rw [evV_call_seq ht rfl]
                simp only [evSeqArgs,head_eval,ha]
                rw [views_eval H tails x T U E F hEF _ (rest_firstOrder H) j,hdH]
                simp only [hpw]
                rfl
              · simp only [if_neg he, CallLookahead.peek]
  | .seq a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk k hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T hOk k hShift b E F hEF q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk k hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]; exact evaluator_of_shift H tails x T hOk k hShift b E F hEF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, F, hEF, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T hOk k hShift a E F hEF q (by omega))
  | .notP a, E, F, hEF, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T hOk k hShift a E F hEF p hp]
  | .param z, E, F, hEF, p, _ => hEF z p
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .call _ (_::_), _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl

theorem source_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) (i+1) W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W
        (.seq (.seq H.head (.param 0)) (render H tails true b)) p := by
  exact SeededClock.user_step (source H tails) x .callByValuePar pick 1 _ k (i+1)
    (by simp [pick]) ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩
    (by rw [source_rule,hr]; rfl) W p hp

theorem target_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable H tails x (k+1) (i+1) W) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) W
        (.seq (.param 0) (render H tails false b)) p := by
  exact SeededClock.user_step (target H tails) x .callByValueSeq pick 1 _ k (i+1)
    (by simp [pick]) ⟨2,.seq (.param 0) (render H tails false b)⟩
    (by rw [target_rule,hr]; rfl) W p hp

theorem tables_shifted (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr p j q ws hp hq ha hw htrace
    have hs : ruleAtM (source H tails).rules (i+1)=some
        ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
    have ht : ruleAtM (target H tails).rules (i+1)=some
        ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
    change valAt (SeededClock.prefixSeed _ x .callByValuePar pick 1 (i+1) [pre x p j++ws.flatten]) p=_
    rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ hs _ p hp,prefix_eval,
      prefix_bridge H x p j q ws hp hq ha hw htrace]
    by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
    · simp only [if_pos he]
      change _=valAt (SeededClock.prefixSeed _ x .callByValueSeq pick 1 (i+1) [pre x p j,ws.flatten]) q
      rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 2 _ _ ht _ q hq,word_eval]
    · simp only [if_neg he, ite_true]
  | succ k ih =>
    intro i b hr p j q ws hp hq ha hw htrace
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    rw [source_step H tails x k i b hr _ p hp]
    have hpre : evV (source H tails) x .callByValuePar T [pre x p j++ws.flatten]
        (.seq H.head (.param 0)) p=
        if (pre x p j++ws.flatten).IsPrefix (sfx x j) then wordAt x (pre x p j) q else some none :=
      (prefix_eval H _ x _ T _ p).trans (prefix_bridge H x p j q ws hp hq ha hw htrace)
    by_cases he : (pre x p j++ws.flatten).IsPrefix (sfx x j)
    · rw [if_pos he] at hpre ⊢
      obtain ⟨z,hz⟩ := prefix_positive H x p j q ws hp hq ha hw htrace he
      rw [evV_seq_ok (hpre.trans hz),target_step H tails x k i b hr _ q hq]
      rw [evV_seq_ok ((word_eval (target H tails) x .callByValueSeq U (pre x p j) ws.flatten q).trans hz)]
      have hzbound := evV_ok (source_ok H tails x k) (.seq H.head (.param 0)) p hp z (hpre.trans hz)
      exact evaluator_of_shift H tails x T (source_ok H tails x k) k ih b _ _
        (parameters_parts H tails x T U _ _) z hzbound
    · rw [if_neg he] at hpre ⊢
      exact evV_seq_fail hpre

theorem evaluator_eq (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (e : MExp) (E F : List (List Char))
    (hEF : Parameters H tails x (sourceTable H tails x k) (targetTable H tails x k) E F)
    (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false e) p :=
  evaluator_of_shift H tails x _ (source_ok H tails x k) k (tables_shifted H tails x k) e E F hEF p hp

theorem stable_eq (H : Header) (tails : List MExp) (e : MExp) (x : List Char) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
      [] (render H tails true e) x.length=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
      [] (render H tails false e) x.length := by
  have hsource := comparator_stable H (source H tails) rfl x .callByValuePar
  have htarget := comparator_stable H (target H tails) rfl x .callByValueSeq
  have hdefined (v : Option Nat) :
      evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
        [] (render H tails true e) x.length=some v ↔
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
        [] (render H tails false e) x.length=some v := by
    rw [←tblV_stable (source H tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target H tails) x .callByValueSeq (Nat.le_refl _),
      ←SeededClock.defined_iff (source H tails) x .callByValuePar pick 1 _
        (SeededClock.prefixSeed_lower _ x _ pick 1) (SeededClock.prefixSeed_upper _ x _ pick 1) hsource,
      ←SeededClock.defined_iff (target H tails) x .callByValueSeq pick 1 _
        (SeededClock.prefixSeed_lower _ x _ pick 1) (SeededClock.prefixSeed_upper _ x _ pick 1) htarget]
    exact exists_congr (fun k => by rw [evaluator_eq H tails x k e [] [] (parameters_empty H tails x _ _) x.length (Nat.le_refl _)])
  cases hs : evV (source H tails) x .callByValuePar
      (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x)) [] (render H tails true e) x.length with
  | none =>
    cases ht : evV (target H tails) x .callByValueSeq
        (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x)) [] (render H tails false e) x.length with
    | none => rfl
    | some v => have hh := (hdefined v).mpr ht; rw [hs] at hh; cases hh
  | some v => exact ((hdefined v).mp hs).symm

/-- One fixed recursive Seq grammar preserves every finite observation on
unchanged input strings. Captures can have unbounded input-dependent word
counts, with retained parameters controlling their selection at each call. -/
theorem observations_iff (H : Header) (tails : List MExp) (e : MExp)
    (x : List Char) (r : Option (List Char)) :
    SObs (source H tails) .callByValuePar (render H tails true e) x r ↔
      SObs (target H tails) .callByValueSeq (render H tails false e) x r := by
  rw [←decideObsV_iff (source_firstOrder H tails) (by decide) (render_firstOrder H tails true e),
    ←decideObsV_iff (target_firstOrder H tails) (by decide) (render_firstOrder H tails false e)]
  unfold decideObsV
  rw [stable_eq]

theorem language_translation (H : Header) (tails : List MExp) (e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧
      ∀ x, SObs (source H tails) .callByValuePar (render H tails true e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target H tails,render H tails false e,target_firstOrder H tails,render_firstOrder H tails false e,
    fun x => observations_iff H tails e x (some [])⟩


end Shallot.MacroPeg.CBV.AdjacentCodewordRecursive
