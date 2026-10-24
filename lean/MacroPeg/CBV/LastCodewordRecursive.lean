import MacroPeg.CBV.LastCodewordGrammar
import MacroPeg.CBV.RuntimePrefixGrammar
import MacroPeg.CBV.SeededClock
import MacroPeg.CBV.LeadingReplayStar

/-! Last-preserving captures across mutually recursive user calls. -/
namespace Shallot.MacroPeg.CBV.LastCodewordRecursive
open ClockFreezing (Table)
open RuntimePrefixGrammar (Header lexical head_eval)
open ParserPrefixFusion (Pure pure_eval pure_firstOrder)

def argument (H : Header) : MExp := LastCodewordRotation.argument H.head
def argumentAt (H : Header) (x : List Char) (p : Nat) : Res :=
  evV ⟨[]⟩ x .callByValuePar (fun _ _ => []) [] (argument H) p
def probe (H : Header) (x : List Char) (p : Nat) : Res :=
  LastCodewordVerification.probe ⟨[]⟩ x .callByValuePar (fun _ _ => []) H.head p

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call (i+1) [argument H]
      else .seq (.andP (argument H)) (.seq (.andP (.call 0 [H.head])) (.call (i+1) [argument H]))
  | .seq a b => .seq (render H tails par a) (render H tails par b)
  | .alt a b => .alt (render H tails par a) (render H tails par b)
  | .star a => .star (render H tails par a)
  | .notP a => .notP (render H tails par a)
  | .param k => .param k
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range a b => .range a b
  | .lit w => .lit w
  | _ => MExp.failAlways

def source (H : Header) (tails : List MExp) : MGrammar :=
  ⟨⟨1,LastCodewordVerification.verifier H.head⟩::tails.map
    (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨⟨1,LastCodewordVerification.verifier H.head⟩::tails.map
    (fun b => ⟨1,.seq H.head (render H tails false b)⟩)⟩
def pick (i : Nat) : Bool := decide (i=0)

theorem argument_pure (H : Header) : Pure (argument H) := ⟨H.pure,H.pure⟩
theorem argument_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (E : List (List Char)) (p : Nat) :
    evV g x s T E (argument H) p=argumentAt H x p :=
  pure_eval g ⟨[]⟩ x s .callByValuePar T (fun _ _ => []) E [] _ (argument_pure H) p

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨pure_firstOrder _ (argument_pure H),⟨pure_firstOrder _ H.pure,True.intro⟩,pure_firstOrder _ (argument_pure H),True.intro⟩
      · exact ⟨pure_firstOrder _ (argument_pure H),True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨⟨pure_firstOrder _ H.pure,True.intro⟩,pure_firstOrder _ H.pure⟩
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨pure_firstOrder _ H.pure,True.intro⟩,render_firstOrder H tails true b⟩
theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨⟨pure_firstOrder _ H.pure,True.intro⟩,pure_firstOrder _ H.pure⟩
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨pure_firstOrder _ H.pure,render_firstOrder H tails false b⟩

theorem source_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (source H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩) := by
  simp [source,ruleAtM_eq_getElem?]
theorem target_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (target H tails).rules (i+1)=(tails[i]?).map
      (fun b => ⟨1,.seq H.head (render H tails false b)⟩) := by
  simp [target,ruleAtM_eq_getElem?]

/-- The verifier row is physically stable after one ordinary round. -/
theorem verifier_stable (H : Header) (g : MGrammar)
    (hr : ruleAtM g.rules 0=some ⟨1,LastCodewordVerification.verifier H.head⟩)
    (x : List Char) (s : Strategy) : ClockFreezing.StableRows g x s pick 1 := by
  intro k i hi W
  have he : i=0 := by simpa [pick] using hi
  subst i
  have hn : 1+k=k+1 := by omega
  rw [hn]
  simp only [tblV,hr]
  apply List.map_congr_left
  intro p hp
  exact LastCodewordGrammar.syntax_eval g g x s s _ _ (tblV_ok g x s k) W
    (LastCodewordVerification.verifier H.head)
    ⟨⟨LastCodewordGrammar.pure_syntax _ H.pure,True.intro⟩,LastCodewordGrammar.pure_syntax _ H.pure⟩ p
    (by have := List.mem_range.mp hp; omega)

abbrev sourceTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (source H tails) x .callByValuePar pick 1
    (SeededClock.prefixSeed (source H tails) x .callByValuePar pick 1) k
abbrev targetTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  ClockFreezing.frozen (target H tails) x .callByValueSeq pick 1 k

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

/-- The actual installed unary helper supplies the probe; no row oracle. -/
theorem verifier_call (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call 0 [H.head]) p=
      probe H x p := by
  have hr : ruleAtM (target H tails).rules 0=some ⟨1,LastCodewordVerification.verifier H.head⟩ := rfl
  rw [evV_call_seq hr rfl]
  simp only [evSeqArgs,head_eval]
  unfold probe LastCodewordVerification.probe
  rw [head_eval]
  cases hv : lexical H x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := (RuntimePrefixGrammar.lexical_success H x p j hp hv).1
      simp only []
      unfold targetTable
      rw [ClockFreezing.frozen_rows _ x _ pick 1 k 0 (by simp [pick]),valAt_tblV_succ hr _ hj]
      exact LastCodewordGrammar.syntax_eval _ _ x _ _ _ _ (tblV_ok _ x _ 0) [pre x p j]
        (LastCodewordVerification.verifier H.head)
        ⟨⟨LastCodewordGrammar.pure_syntax _ H.pure,True.intro⟩,LastCodewordGrammar.pure_syntax _ H.pure⟩ j hj

/-- A table-local probe is the same actual closed-header computation. -/
theorem probe_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hOk : OkTV x.length T) (p : Nat) (hp : p≤x.length) :
    LastCodewordVerification.probe g x s T H.head p=probe H x p := by
  unfold probe
  unfold LastCodewordVerification.probe
  simp only [head_eval]
  cases hv : lexical H x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := (RuntimePrefixGrammar.lexical_success H x p j hp hv).1
      exact LastCodewordGrammar.syntax_eval _ _ x _ _ _ _ hOk [pre x p j]
        (LastCodewordVerification.verifier H.head)
        ⟨⟨LastCodewordGrammar.pure_syntax _ H.pure,True.intro⟩,LastCodewordGrammar.pure_syntax _ H.pure⟩ j hj

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
  | some result => cases result <;> rfl

/-- The source seed computes only actual prefix failures. With a successful
B these coincide precisely with rejection by the installed verifier. -/
theorem seed_entry (H : Header) (x : List Char) (p q : Nat) (hp : p≤x.length)
    (hb : argumentAt H x p=some (some q)) :
    (if prefixAt H x [pre x p q] p=some none then some none else none)=
      match probe H x p with | some (some _) => none | other => other := by
  let g : MGrammar := ⟨[]⟩
  let T : Table := fun _ _ => []
  let loop : MExp := .star (.lit [])
  have hOk : OkTV x.length T := by intro i W z j hv; cases hv
  have hSound : SoundTV g x .callByValuePar T := by intro i r W hr; cases i <;> cases hr
  have hloop (W : List (List Char)) (z : Nat) (hz : z≤x.length) :
      evV g x .callByValuePar T W loop z=none := by
    rw [show loop=.star (.lit []) from rfl,evV_star]
    apply evStar_stuck (j:=z)
    · simp [evV,Shallot.stripPrefix?,length_sfx x hz]
    · omega
  have hl := LastCodewordVerification.actual_entry g x .callByValuePar (by decide) T hSound
    H.head (pure_firstOrder _ H.pure)
    (fun E z => pure_eval g g x _ _ T T E [] H.head H.pure z) H.prefixFree
    (fun z j hz he => H.captured g x _ T [] z j hz he) p q hp hb loop
  rw [←LeadingReplayStar.sequence_assoc] at hl
  have hleft : evV g x .callByValuePar T [pre x p q]
      (.seq (.seq H.head (.param 0)) loop) p=
      if prefixAt H x [pre x p q] p=some none then some none else none := by
    change (match evV g x .callByValuePar T [pre x p q] (.seq H.head (.param 0)) p with
      | some (some z) => evV g x .callByValuePar T [pre x p q] loop z | other => other)=_
    cases hv : evV g x .callByValuePar T [pre x p q] (.seq H.head (.param 0)) p with
    | none => simp only [←prefix_eval H g x .callByValuePar T _ p,hv]; rfl
    | some result => cases result with
      | none => simp only [←prefix_eval H g x .callByValuePar T _ p,hv]; rfl
      | some z =>
        dsimp only []
        rw [hloop _ z (evV_ok hOk _ p hp z hv)]
        simp only [←prefix_eval H g x .callByValuePar T _ p,hv]; rfl
  rw [hleft] at hl
  change _=(match probe H x p with
    | some (some _) => evV g x .callByValuePar T [pre x p q] (.seq H.head loop) q | other => other) at hl
  rw [hl]
  have hq : q≤x.length := evV_ok hOk (argument H) p hp q hb
  have hb' := hb
  change evV g x .callByValuePar T [] (LastCodewordRotation.argument H.head) p=some (some q) at hb'
  rw [LastCodewordRotation.argument_eval] at hb'
  rcases LastCodewordRotation.capture_endpoint _ p q hb' with ⟨he,hfail⟩ | ⟨r,hr,hend⟩
  · subst q
    have hprobe : probe H x p=some none := by
      unfold probe LastCodewordVerification.probe
      rw [hfail]
    rw [hprobe]
  · have he : evV g x .callByValuePar T [pre x p q] H.head q=some (some r) :=
      (pure_eval g g x _ _ T T [pre x p q] [] H.head H.pure q).trans hr
    rw [evV_seq_ok he,hloop _ r (evV_ok hOk _ q hq r he)]

def Shifted (H : Header) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p q, p≤x.length → argumentAt H x p=some (some q) →
    valAt (T (i+1) [pre x p q]) p=
      match probe H x p with
      | some (some _) => valAt (U (i+1) [pre x p q]) q
      | other => other

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T : Table) (hOk : OkTV x.length T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e E p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (render H tails false e) p
  | .call i [], E, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (i+1)=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (i+1)=some
          ⟨1,.seq H.head (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.andP (argument H)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) E
          (.seq (.andP (.call 0 [H.head])) (.call (i+1) [argument H])) j
        | other => other)
      rw [CallLookahead.evV_peek]
      simp only [evParArgs,argument_eval]
      cases ha : argumentAt H x p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only [CallLookahead.peek]
          change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.andP (.call 0 [H.head])) p with
            | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call (i+1) [argument H]) j
            | other => other)
          rw [CallLookahead.evV_peek,verifier_call H tails x k E p hp,hShift i b hr p q hp ha]
          cases hv : probe H x p with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some j =>
              dsimp only [CallLookahead.peek]
              rw [evV_call_seq ht rfl]
              simp only [evSeqArgs,argument_eval,ha]
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk k hShift a E p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T hOk k hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk k hShift a E p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]; exact evaluator_of_shift H tails x T hOk k hShift b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T hOk k hShift a E q (by omega))
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T hOk k hShift a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

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
        (.seq H.head (render H tails false b)) p := by
  exact ClockFreezing.frozen_user_step (target H tails) x .callByValueSeq pick 1 k (i+1)
    (by simp [pick]) ⟨1,.seq H.head (render H tails false b)⟩
    (by rw [target_rule,hr]; rfl) W p hp

theorem tables_shifted (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr p q hp hb
    have hs : ruleAtM (source H tails).rules (i+1)=some
        ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
    change valAt (SeededClock.prefixSeed _ x .callByValuePar pick 1 (i+1) [pre x p q]) p=_
    rw [SeededClock.prefixSeed_query _ x _ pick 1 (i+1) (by simp [pick]) 1 _ _ hs _ p hp,prefix_eval]
    have hn : valAt (targetTable H tails x 0 (i+1) [pre x p q]) q=none := by
      simp [targetTable,ClockFreezing.frozen,pick,valAt_nil]
    rw [hn]
    exact seed_entry H x p q hp hb
  | succ k ih =>
    intro i b hr p q hp hb
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    have hq : q≤x.length := evV_ok (tblV_ok (⟨[]⟩ : MGrammar) x .callByValuePar 0) (argument H) p hp q hb
    rw [source_step H tails x k i b hr _ p hp,LeadingReplayStar.sequence_assoc]
    have hl := LastCodewordVerification.actual_entry (source H tails) x .callByValuePar (by decide) T
      (source_sound H tails x k) H.head (pure_firstOrder _ H.pure)
      (fun E z => pure_eval _ _ x _ _ T T E [] H.head H.pure z) H.prefixFree
      (fun z j hz he => H.captured _ x _ T [] z j hz he) p q hp
      ((argument_eval H _ x _ T [] p).trans hb) (render H tails true b)
    rw [probe_eval H _ x _ T (source_ok H tails x k) p hp] at hl
    rw [hl]
    cases hv : probe H x p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        rw [target_step H tails x k i b hr _ q hq]
        have hhead := head_eval H (source H tails) x .callByValuePar T [pre x p q] q
        have hhead' := head_eval H (target H tails) x .callByValueSeq U [pre x p q] q
        change (match evV (source H tails) x .callByValuePar T [pre x p q] H.head q with
          | some (some z) => evV (source H tails) x .callByValuePar T [pre x p q] (render H tails true b) z
          | other => other)=
          (match evV (target H tails) x .callByValueSeq U [pre x p q] H.head q with
          | some (some z) => evV (target H tails) x .callByValueSeq U [pre x p q] (render H tails false b) z
          | other => other)
        rw [hhead,hhead']
        cases hz : lexical H x q with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some z =>
            exact evaluator_of_shift H tails x T (source_ok H tails x k) k ih b [pre x p q] z
              (RuntimePrefixGrammar.lexical_success H x q z hq hz).1

theorem evaluator_eq (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (render H tails false e) p :=
  evaluator_of_shift H tails x _ (source_ok H tails x k) k (tables_shifted H tails x k) e E p hp

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
      ←ClockFreezing.defined_iff (target H tails) x .callByValueSeq pick 1 htarget]
    exact exists_congr (fun k => by rw [evaluator_eq H tails x k e [] x.length (Nat.le_refl _)])
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

end Shallot.MacroPeg.CBV.LastCodewordRecursive
