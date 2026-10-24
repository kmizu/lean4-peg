import MacroPeg.CBV.CodewordControlGrammar
import MacroPeg.CBV.SelectedCodewordRecursive

/-! Retain one source capture as two consecutive Seq arguments throughout
mutually recursive user calls. -/
namespace Shallot.MacroPeg.CBV.CodewordControlRecursive
open ClockFreezing (Table)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)
open CodewordControlFilter (wholeView)

structure Header extends RuntimePrefixGrammar.Header where
  control : CodewordControlFilter.Expr
  controlPure : CodewordControlFilter.Pure control

def rest (H : Header) : MExp := CodewordControlFilter.render H.head H.control
def argument (H : Header) : MExp := .seq H.head (rest H)
def verifier (H : Header) : MExp := CodewordControlFilter.filter H.head H.control

theorem rest_pure (H : Header) : Pure (rest H) :=
  CodewordControlFilter.render_pure H.head H.pure H.control H.controlPure
theorem argument_pure (H : Header) : Pure (argument H) := ⟨H.pure,rest_pure H⟩
theorem verifier_syntax (H : Header) : HelperArgument.Syntax 0 (verifier H) :=
  CodewordControlFilter.filter_syntax H.head H.pure H.control H.controlPure

def lexical (H : Header) (x : List Char) (p : Nat) : Res := RuntimePrefixGrammar.lexical H.toHeader x p
def restAt (H : Header) (x : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [] (rest H) p
def argumentAt (H : Header) (x : List Char) (p : Nat) : Res :=
  match lexical H x p with | some (some j) => restAt H x j | other => other
def check (H : Header) (x u : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [u] (verifier H) p

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) : evV g x s T E H.head p=lexical H x p :=
  RuntimePrefixGrammar.head_eval H.toHeader g x s T E p
theorem rest_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) : evV g x s T E (rest H) p=restAt H x p :=
  pure_eval g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) E [] _ (rest_pure H) p
theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) : evV g x s T E (argument H) p=argumentAt H x p := by
  simp only [argument,evV,head_eval,rest_eval,argumentAt]
  rfl

theorem verifier_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hOk : OkTV x.length T) (u : List Char) (p : Nat) (hp : p≤x.length) :
    evV g x s T [u] (verifier H) p=check H x u p :=
  LastCodewordGrammar.syntax_eval g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) hOk [u]
    _ (verifier_syntax H) p hp

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call (i+1) [argument H]
      else .seq (.andP (argument H)) (.seq (.andP (.call 0 [H.head])) (.call (i+1) [H.head,rest H]))
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
  ⟨⟨1,verifier H⟩::tails.map (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨⟨1,verifier H⟩::tails.map (fun b => ⟨2,.seq (.param 0) (render H tails false b)⟩)⟩
def pick (i : Nat) : Bool := decide (i=0)

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨pure_firstOrder _ (argument_pure H),⟨pure_firstOrder _ H.pure,True.intro⟩,
          pure_firstOrder _ H.pure,pure_firstOrder _ (rest_pure H),True.intro⟩
      · exact ⟨pure_firstOrder _ (argument_pure H),True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par; exact CodewordControlFilter.wholeView_firstOrder _ True.intro; trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact HelperArgument.firstOrder 0 _ (verifier_syntax H)
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨pure_firstOrder _ H.pure,True.intro⟩,render_firstOrder H tails true b⟩
theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact HelperArgument.firstOrder 0 _ (verifier_syntax H)
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

theorem verifier_stable (H : Header) (g : MGrammar)
    (hr : ruleAtM g.rules 0=some ⟨1,verifier H⟩) (x : List Char) (s : Strategy) :
    ClockFreezing.StableRows g x s pick 1 := by
  intro k i hi W
  have he : i=0 := by simpa [pick] using hi
  subst i
  have hn : 1+k=k+1 := by omega
  rw [hn]
  simp only [tblV,hr]
  apply List.map_congr_left
  intro p hp
  exact LastCodewordGrammar.syntax_eval g g x s s _ _ (tblV_ok g x s k) W
    _ (verifier_syntax H) p (by have := List.mem_range.mp hp; omega)

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

theorem verifier_call (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call 0 [H.head]) p=
      match lexical H x p with
      | some (some j) => check H x (pre x p j) j | other => other := by
  have hr : ruleAtM (target H tails).rules 0=some ⟨1,verifier H⟩ := rfl
  rw [evV_call_seq hr rfl]
  simp only [evSeqArgs,head_eval]
  cases hv : lexical H x p with
  | none => rfl
  | some rr => cases rr with
    | none => rfl
    | some j =>
      have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp hv).1
      dsimp only []
      unfold targetTable
      rw [SeededClock.rows _ x _ pick 1 _ (SeededClock.prefixSeed_rows _ x _ pick 1) k 0
        (by simp [pick]),valAt_tblV_succ hr _ hj]
      exact verifier_eval H _ x _ _ (tblV_ok _ x _ 0) _ j hj

/-- Full local entry, with arbitrary first-order recursive continuation. -/
theorem entry (H : Header) (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (hOk : OkTV x.length T)
    (p j q : Nat) (hp : p≤x.length) (ha : lexical H x p=some (some j))
    (hd : restAt H x j=some (some q)) (b : MExp) (hb : b.FirstOrder) :
    evV g x .callByValuePar T [pre x p q] (.seq (.seq H.head (.param 0)) b) p=
      match check H x (pre x p j) j with
      | some (some _) => evV g x .callByValuePar T [pre x p j,pre x j q]
          (.seq (.param 0) (wholeView b)) q
      | other => other := by
  have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
  have ha0 := (head_eval H g x .callByValuePar T [] p).trans ha
  have hd0 := (rest_eval H g x .callByValuePar T [] j).trans hd
  have hq := evV_ok hOk _ j hj q hd0
  have hc := SequenceArguments.pre_concat hp hq
    (WordStarFilter.success_prefix (by decide) hT [] H.head (pure_firstOrder _ H.pure) p j hp ha0).2
    (WordStarFilter.success_prefix (by decide) hT [] (rest H) (pure_firstOrder _ (rest_pure H)) j q hj hd0).2
  rw [LeadingReplayStar.sequence_assoc,evV_seq_ok ((head_eval H g x .callByValuePar T [pre x p q] p).trans ha),hc]
  have hh := CodewordControlFilter.replay_success g x .callByValuePar (by decide) T hT hOk
    H.head (pure_firstOrder _ H.pure) H.prefixFree (pre x p j)
    (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).2.2
    (fun z k hz hk => H.captured g x .callByValuePar T [pre x p j] z k hz hk)
    H.control j q hj ((rest_eval H g x .callByValuePar T [pre x p j] j).trans hd) b hb
  change _=(match evV g x .callByValuePar T [pre x p j] (verifier H) j with
    | some (some _) => evV g x .callByValuePar T [pre x p j,pre x j q]
        (.seq (.param 0) (wholeView b)) q
    | other => other) at hh
  rw [verifier_eval H g x .callByValuePar T hOk _ j hj] at hh
  exact hh

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

def Shifted (H : Header) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p j q, p≤x.length →
    lexical H x p=some (some j) → restAt H x j=some (some q) →
    valAt (T (i+1) [pre x p q]) p=
      match check H x (pre x p j) j with
      | some (some _) => valAt (U (i+1) [pre x p j,pre x j q]) q
      | other => other

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T : Table) (hOk : OkTV x.length T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e E F, Parameters H tails x T (targetTable H tails x k) E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (i+1)=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (i+1)=some
          ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.andP (argument H)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) F
          (.seq (.andP (.call 0 [H.head])) (.call (i+1) [H.head,rest H])) j
        | other => other)
      rw [CallLookahead.evV_peek]
      simp only [evParArgs,argument_eval,argumentAt]
      cases ha : lexical H x p with
      | none => rfl
      | some rr => cases rr with
        | none => rfl
        | some j =>
          have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
          dsimp only []
          cases hd : restAt H x j with
          | none => rfl
          | some rr => cases rr with
            | none => rfl
            | some q =>
              dsimp only [CallLookahead.peek]
              rw [hShift i b hr p j q hp ha hd]
              change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.andP (.call 0 [H.head])) p with
                | some (some z) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.call (i+1) [H.head,rest H]) z
                | other => other)
              rw [CallLookahead.evV_peek,verifier_call H tails x k F p hp,ha]
              dsimp only []
              cases check H x (pre x p j) j with
              | none => rfl
              | some rr => cases rr with
                | none => rfl
                | some z =>
                  dsimp only [CallLookahead.peek]
                  rw [evV_call_seq ht rfl]
                  simp only [evSeqArgs,head_eval,rest_eval,ha,hd]
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

def wordAt (x u : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [u] (.param 0) p

theorem word_eval (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (u v : List Char) (p : Nat) : evV g x s T [u,v] (.param 0) p=wordAt x u p := rfl

/-- The same exact prefix identity also relates the two actual failure seeds. -/
theorem prefix_identity (H : Header) (x : List Char) (p j q : Nat) (hp : p≤x.length)
    (ha : lexical H x p=some (some j)) (hd : restAt H x j=some (some q)) :
    prefixAt H x [pre x p q] p=
      match check H x (pre x p j) j with
      | some (some _) => wordAt x (pre x p j) q | other => other := by
  let g : MGrammar := ⟨[]⟩
  let T : Table := fun _ _ => []
  have hOk : OkTV x.length T := by intro i W z k hv; cases hv
  have hSound : SoundTV g x .callByValuePar T := by intro i r W hr; cases i <;> cases hr
  have he := entry H g x T hSound hOk p j q hp ha hd .eps True.intro
  simp only [wholeView,MExp.subst,seq_eps] at he
  rw [prefix_eval] at he
  simp only [word_eval] at he
  exact he

theorem seed_entry (H : Header) (x : List Char) (p j q : Nat) (hp : p≤x.length)
    (ha : lexical H x p=some (some j)) (hd : restAt H x j=some (some q)) :
    (if prefixAt H x [pre x p q] p=some none then some none else none)=
      match check H x (pre x p j) j with
      | some (some _) => if wordAt x (pre x p j) q=some none then some none else none
      | other => other := by
  rw [prefix_identity H x p j q hp ha hd]
  cases check H x (pre x p j) j with
  | none => rfl
  | some r => cases r <;> rfl

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
    intro i b hr p j q hp ha hd
    have hs : ruleAtM (source H tails).rules (i+1)=some
        ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
    have ht : ruleAtM (target H tails).rules (i+1)=some
        ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
    have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
    have hd0 := (rest_eval H (⟨[]⟩ : MGrammar) x .callByValuePar (fun _ _ => []) [] j).trans hd
    have hq := evV_ok (tblV_ok (⟨[]⟩ : MGrammar) x .callByValuePar 0) _ j hj q hd0
    change valAt (SeededClock.prefixSeed _ x .callByValuePar pick 1 (i+1) [pre x p q]) p=_
    rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ hs _ p hp,prefix_eval]
    change _=(match check H x (pre x p j) j with
      | some (some _) => valAt (SeededClock.prefixSeed _ x .callByValueSeq pick 1 (i+1) [pre x p j,pre x j q]) q
      | other => other)
    rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 2 _ _ ht _ q hq,word_eval]
    exact seed_entry H x p j q hp ha hd
  | succ k ih =>
    intro i b hr p j q hp ha hd
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    have hj := (RuntimePrefixGrammar.lexical_success H.toHeader x p j hp ha).1
    have hd0 := (rest_eval H (source H tails) x .callByValuePar T [] j).trans hd
    have hq := evV_ok (source_ok H tails x k) _ j hj q hd0
    rw [source_step H tails x k i b hr _ p hp]
    rw [entry H (source H tails) x T (source_sound H tails x k) (source_ok H tails x k)
      p j q hp ha hd _ (render_firstOrder H tails true b)]
    cases check H x (pre x p j) j with
    | none => rfl
    | some rr => cases rr with
      | none => rfl
      | some z =>
        dsimp only []
        rw [target_step H tails x k i b hr _ q hq]
        change (match evV (source H tails) x .callByValuePar T [pre x p j,pre x j q] (.param 0) q with
          | some (some z) => evV (source H tails) x .callByValuePar T [pre x p j,pre x j q]
              (wholeView (render H tails true b)) z | other => other)=
          (match evV (target H tails) x .callByValueSeq U [pre x p j,pre x j q] (.param 0) q with
          | some (some z) => evV (target H tails) x .callByValueSeq U [pre x p j,pre x j q] (render H tails false b) z
          | other => other)
        have hh : evV (source H tails) x .callByValuePar T [pre x p j,pre x j q] (.param 0) q=
            evV (target H tails) x .callByValueSeq U [pre x p j,pre x j q] (.param 0) q := rfl
        rw [hh]
        cases hz : evV (target H tails) x .callByValueSeq U [pre x p j,pre x j q] (.param 0) q with
        | none => rfl
        | some rr => cases rr with
          | none => rfl
          | some w =>
            dsimp only []
            rw [CodewordControlFilter.wholeView_eval _ x _ T _ _ _ (render_firstOrder H tails true b) w]
            have hw : w≤x.length := evV_ok (source_ok H tails x k) _ q hq w (hh.trans hz)
            exact evaluator_of_shift H tails x T (source_ok H tails x k) k ih b _ _
              (parameters_parts H tails x T U _ _) w hw

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
  have hsource := verifier_stable H (source H tails) rfl x .callByValuePar
  have htarget := verifier_stable H (target H tails) rfl x .callByValueSeq
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
unchanged input strings, despite input-dependent unbounded capture counts. -/
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

/-- Guard evaluation precedes every helper or user row query. An undefined
argument cannot become a finite negative answer in the recursive compiler. -/
theorem undefined_argument (H : Header) (tails : List MExp) (i : Nat) (b : MExp)
    (hr : tails[i]?=some b) (x : List Char) (p : Nat)
    (hb : argumentAt H x p=none) (T U : Table) (E : List (List Char)) :
    evV (source H tails) x .callByValuePar T E (render H tails true (.call i [])) p=none ∧
    evV (target H tails) x .callByValueSeq U E (render H tails false (.call i [])) p=none := by
  have hs : ruleAtM (source H tails).rules (i+1)=some
      ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
  constructor
  · simp only [render,hr,ite_true]
    rw [evV_call_par hs rfl (by decide)]
    simp only [evParArgs,argument_eval,hb]
  · simp only [render,hr]
    apply evV_seq_none
    rw [CallLookahead.evV_peek,argument_eval,hb]
    rfl

end Shallot.MacroPeg.CBV.CodewordControlRecursive
