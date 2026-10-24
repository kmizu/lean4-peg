import MacroPeg.CBV.LastCodewordHelpers

/-! Retain unbounded last-header captures through user recursion while the
header itself uses an independent mutually recursive helper component. -/
namespace Shallot.MacroPeg.CBV.LastCodewordHelperGrammar
open ClockFreezing (Table)
open RecursiveCodeGrammar (Header canonical lexical LexicalTable)
open RecursiveParserStability (Installed)
open LastCodewordHelpers (argument argumentAt probe prefixAt pick floor lexical_environment lexical_syntax)

theorem head_firstOrder (H : Header) : H.head.FirstOrder :=
  RecursiveParserStability.lexical_firstOrder _ H.head H.lexical

theorem head_eval (H : Header) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : Table) (hLex : LexicalTable H g x s T) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV g x s T E H.head p=lexical H H.head x p := hLex E _ H.lexical p hp

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call (H.bodies.length+(i+1)) [argument H]
      else .seq (.andP (argument H)) (.seq (.andP (.call H.bodies.length [H.head])) (.call (H.bodies.length+(i+1)) [argument H]))
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
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++⟨1,LastCodewordVerification.verifier H.head⟩::tails.map
    (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++⟨1,LastCodewordVerification.verifier H.head⟩::tails.map
    (fun b => ⟨1,.seq H.head (render H tails false b)⟩)⟩
theorem argument_firstOrder (H : Header) : (argument H).FirstOrder :=
  RecursiveParserStability.lexical_firstOrder _ _ (LastCodewordHelpers.argument_lexical H)

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨argument_firstOrder H,⟨head_firstOrder H,True.intro⟩,argument_firstOrder H,True.intro⟩
      · exact ⟨argument_firstOrder H,True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param _ | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_installed (H : Header) (tails : List MExp) : Installed H.bodies (source H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem source_verifier (H : Header) (tails : List MExp) :
    ruleAtM (source H tails).rules H.bodies.length=some ⟨1,LastCodewordVerification.verifier H.head⟩ := by
  simp [source,ruleAtM_eq_getElem?]

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨⟨head_firstOrder H,True.intro⟩,head_firstOrder H⟩
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨⟨head_firstOrder H,True.intro⟩,render_firstOrder H tails true b⟩

theorem target_installed (H : Header) (tails : List MExp) : Installed H.bodies (target H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem target_verifier (H : Header) (tails : List MExp) :
    ruleAtM (target H tails).rules H.bodies.length=some ⟨1,LastCodewordVerification.verifier H.head⟩ := by
  simp [target,ruleAtM_eq_getElem?]

theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨⟨head_firstOrder H,True.intro⟩,head_firstOrder H⟩
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨head_firstOrder H,render_firstOrder H tails false b⟩

theorem source_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (source H tails).rules (H.bodies.length+(i+1))=(tails[i]?).map
      (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩) := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right]
theorem target_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (target H tails).rules (H.bodies.length+(i+1))=(tails[i]?).map
      (fun b => ⟨1,.seq H.head (render H tails false b)⟩) := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right]

abbrev sourceTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (source H tails) x .callByValuePar (pick H) (floor H x)
    (SeededClock.prefixSeed (source H tails) x .callByValuePar (pick H) (floor H x)) k
abbrev targetTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  ClockFreezing.frozen (target H tails) x .callByValueSeq (pick H) (floor H x) k

theorem source_ok (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    OkTV x.length (sourceTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (floor H x+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ (pick H) (floor H x) _ (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) k i W p).eq_of_some hv)

theorem source_sound (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    SoundTV (source H tails) x .callByValuePar (sourceTable H tails x k) := by
  intro i rule W hr ha p hp v hv
  exact tblV_sound (source_firstOrder H tails) (by decide) _ i rule W hr ha p hp v
    ((SeededClock.physical_bound _ x _ (pick H) (floor H x) _ (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) k i W p).eq_of_some hv)

theorem source_lexical (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    LexicalTable H (source H tails) x .callByValuePar (sourceTable H tails x k) := by
  apply LastCodewordHelpers.lexical_table H _ (source_installed H tails) x _ _ (source_ok H tails x k)
  intro i hi
  exact SeededClock.rows _ x _ (pick H) (floor H x) _
    (SeededClock.prefixSeed_rows _ x _ (pick H) (floor H x)) k i (by simp [pick]; omega) []

theorem target_lexical (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    LexicalTable H (target H tails) x .callByValueSeq (targetTable H tails x k) := by
  apply LastCodewordHelpers.lexical_table H _ (target_installed H tails) x _ _ (ClockFreezing.frozen_ok _ x _ _ _ k)
  intro i hi
  exact ClockFreezing.frozen_rows _ x _ (pick H) (floor H x) k i (by simp [pick]; omega) []

/-- The installed verifier uses only actual stabilized recursive helpers. -/
theorem verifier_call (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call H.bodies.length [H.head]) p=
      probe H x p := by
  have hr := target_verifier H tails
  rw [evV_call_seq hr rfl]
  simp only [evSeqArgs,head_eval H _ x _ _ (target_lexical H tails x k) E p hp]
  unfold probe LastCodewordVerification.probe
  change _=
    (match lexical H H.head x p with
    | some (some j) => evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
      (canonical H.bodies x) [pre x p j] (LastCodewordVerification.verifier H.head) j | other => other)
  cases hv : lexical H H.head x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := (RecursiveCodeGrammar.lexical_success H H.head H.lexical x p j hp hv).1
      dsimp only []
      unfold targetTable
      rw [ClockFreezing.frozen_rows _ x _ (pick H) (floor H x) k H.bodies.length (by simp [pick]),
        show floor H x=RecursiveParserStability.floor H.bodies x+1 from rfl,valAt_tblV_succ hr _ hj]
      exact LastCodewordHelpers.syntax_eval H _ (target_installed H tails) x _ _ (tblV_ok _ x _ _)
        (LastCodewordHelpers.physical_lexical H _ (target_installed H tails) x .callByValueSeq)
        [pre x p j] (LastCodewordVerification.verifier H.head)
        ⟨⟨lexical_syntax _ H.head H.lexical,True.intro⟩,lexical_syntax _ H.head H.lexical⟩ j hj

/-- The source seed computes only actual prefix failures. With a successful
B these coincide precisely with rejection by the installed verifier. -/
theorem seed_entry (H : Header) (x : List Char) (p q : Nat) (hp : p≤x.length)
    (hb : argumentAt H x p=some (some q)) :
    (if prefixAt H x [pre x p q] p=some none then some none else none)=
      match probe H x p with | some (some _) => none | other => other := by
  let g := RecursiveParserStability.grammar H.bodies
  let T := canonical H.bodies x
  let loop : MExp := .star (.lit [])
  have hOk : OkTV x.length T := tblV_ok g x .callByValuePar _
  have hSound : SoundTV g x .callByValuePar T := tblV_sound (RecursiveCodeGrammar.helpers_firstOrder H) (by decide) _
  have hloop (W : List (List Char)) (z : Nat) (hz : z≤x.length) :
      evV g x .callByValuePar T W loop z=none := by
    rw [show loop=.star (.lit []) from rfl,evV_star]
    apply evStar_stuck (j:=z)
    · simp [evV,Shallot.stripPrefix?,length_sfx x hz]
    · omega
  have hl := LastCodewordVerification.actual_entry g x .callByValuePar (by decide) T hSound
    H.head (head_firstOrder H)
    (fun E z => lexical_environment g x .callByValuePar T E [] _ H.head H.lexical z) H.prefixFree
    (fun z j hz he => H.captured x z j hz he) p q hp hb loop
  rw [←LeadingReplayStar.sequence_assoc] at hl
  have hpref : evV g x .callByValuePar T [pre x p q] (.seq H.head (.param 0)) p=prefixAt H x [pre x p q] p := rfl
  have hleft : evV g x .callByValuePar T [pre x p q]
      (.seq (.seq H.head (.param 0)) loop) p=
      if prefixAt H x [pre x p q] p=some none then some none else none := by
    change (match evV g x .callByValuePar T [pre x p q] (.seq H.head (.param 0)) p with
      | some (some z) => evV g x .callByValuePar T [pre x p q] loop z | other => other)=_
    cases hv : evV g x .callByValuePar T [pre x p q] (.seq H.head (.param 0)) p with
    | none => simp only [←hpref,hv]; rfl
    | some result => cases result with
      | none => simp only [←hpref,hv]; rfl
      | some z =>
        dsimp only []
        rw [hloop _ z (evV_ok hOk _ p hp z hv)]
        simp only [←hpref,hv]; rfl
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
      (lexical_environment g x .callByValuePar T [pre x p q] [] _ H.head H.lexical q).trans hr
    rw [evV_seq_ok he,hloop _ r (evV_ok hOk _ q hq r he)]

def Shifted (H : Header) (tails : List MExp) (x : List Char) (T U : Table) : Prop :=
  ∀ i b, tails[i]?=some b → ∀ p q, p≤x.length → argumentAt H x p=some (some q) →
    valAt (T (H.bodies.length+(i+1)) [pre x p q]) p=
      match probe H x p with
      | some (some _) => valAt (U (H.bodies.length+(i+1)) [pre x p q]) q
      | other => other

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T : Table) (hOk : OkTV x.length T) (hLex : LexicalTable H (source H tails) x .callByValuePar T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e E p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (render H tails false e) p
  | .call i [], E, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (H.bodies.length+(i+1))=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (H.bodies.length+(i+1))=some
          ⟨1,.seq H.head (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.andP (argument H)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) E
          (.seq (.andP (.call H.bodies.length [H.head])) (.call (H.bodies.length+(i+1)) [argument H])) j
        | other => other)
      rw [CallLookahead.evV_peek]
      simp only [evParArgs]
      have hargS := LastCodewordHelpers.argument_eval H _ x .callByValuePar T hLex E p hp
      have hargT := LastCodewordHelpers.argument_eval H _ x .callByValueSeq _ (target_lexical H tails x k) E p hp
      rw [hargS,hargT]
      cases ha : argumentAt H x p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some q =>
          dsimp only [CallLookahead.peek]
          change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.andP (.call H.bodies.length [H.head])) p with
            | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call (H.bodies.length+(i+1)) [argument H]) j
            | other => other)
          rw [CallLookahead.evV_peek,verifier_call H tails x k E p hp,hShift i b hr p q hp ha]
          cases hv : probe H x p with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some j =>
              dsimp only [CallLookahead.peek]
              rw [evV_call_seq ht rfl]
              simp only [evSeqArgs]
              rw [hargT,ha]
  | .seq a b, E, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk hLex k hShift a E p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T hOk hLex k hShift b E q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk hLex k hShift a E p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]; exact evaluator_of_shift H tails x T hOk hLex k hShift b E p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T hOk hLex k hShift a E q (by omega))
  | .notP a, E, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T hOk hLex k hShift a E p hp]
  | .param _, _, _, _ | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _
  | .range _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .call _ (_::_), _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

theorem source_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) (H.bodies.length+(i+1)) W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W
        (.seq (.seq H.head (.param 0)) (render H tails true b)) p := by
  exact SeededClock.user_step (source H tails) x .callByValuePar (pick H) (floor H x) _ k (H.bodies.length+(i+1))
    (by simp [pick]) ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩
    (by rw [source_rule,hr]; rfl) W p hp

theorem target_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable H tails x (k+1) (H.bodies.length+(i+1)) W) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) W
        (.seq H.head (render H tails false b)) p := by
  exact ClockFreezing.frozen_user_step (target H tails) x .callByValueSeq (pick H) (floor H x) k (H.bodies.length+(i+1))
    (by simp [pick]) ⟨1,.seq H.head (render H tails false b)⟩
    (by rw [target_rule,hr]; rfl) W p hp

theorem tables_shifted (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr p q hp hb
    have hs : ruleAtM (source H tails).rules (H.bodies.length+(i+1))=some
        ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
    change valAt (SeededClock.prefixSeed _ x .callByValuePar (pick H) (floor H x) (H.bodies.length+(i+1)) [pre x p q]) p=_
    rw [SeededClock.prefixSeed_query _ x _ (pick H) (floor H x) (H.bodies.length+(i+1)) (by simp [pick]) 1 _ _ hs _ p hp]
    have hlex0 : LexicalTable H (source H tails) x .callByValuePar
        (ClockFreezing.frozen (source H tails) x .callByValuePar (pick H) (floor H x) 0) := by
      apply LastCodewordHelpers.lexical_table H _ (source_installed H tails) x _ _ (ClockFreezing.frozen_ok _ x _ _ _ 0)
      intro j hj
      exact ClockFreezing.frozen_rows _ x _ (pick H) (floor H x) 0 j (by simp [pick]; omega) []
    rw [LastCodewordHelpers.prefix_eval H _ (source_installed H tails) x _ _
      (ClockFreezing.frozen_ok _ x _ _ _ 0) hlex0 _ p hp]
    have hn : valAt (targetTable H tails x 0 (H.bodies.length+(i+1)) [pre x p q]) q=none := by
      have hgt : ¬H.bodies.length+(i+1)≤H.bodies.length := by omega
      simp [targetTable,ClockFreezing.frozen,pick,hgt,valAt_nil]
    rw [hn]
    exact seed_entry H x p q hp hb
  | succ k ih =>
    intro i b hr p q hp hb
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    have hq : q≤x.length := evV_ok (tblV_ok (RecursiveParserStability.grammar H.bodies) x .callByValuePar (RecursiveParserStability.floor H.bodies x)) (argument H) p hp q hb
    rw [source_step H tails x k i b hr _ p hp,LeadingReplayStar.sequence_assoc]
    have hl := LastCodewordVerification.actual_entry (source H tails) x .callByValuePar (by decide) T
      (source_sound H tails x k) H.head (head_firstOrder H)
      (fun E z => lexical_environment _ x .callByValuePar T E [] _ H.head H.lexical z) H.prefixFree
      (fun z j hz he => H.captured x z j hz ((source_lexical H tails x k [] H.head H.lexical z hz).symm.trans he)) p q hp
      ((LastCodewordHelpers.argument_eval H _ x _ T (source_lexical H tails x k) [] p hp).trans hb) (render H tails true b)
    rw [LastCodewordHelpers.probe_eval H _ (source_installed H tails) x _ T (source_ok H tails x k) (source_lexical H tails x k) p hp] at hl
    rw [hl]
    cases hv : probe H x p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        dsimp only []
        rw [target_step H tails x k i b hr _ q hq]
        have hhead := head_eval H (source H tails) x .callByValuePar T (source_lexical H tails x k) [pre x p q] q hq
        have hhead' := head_eval H (target H tails) x .callByValueSeq U (target_lexical H tails x k) [pre x p q] q hq
        change (match evV (source H tails) x .callByValuePar T [pre x p q] H.head q with
          | some (some z) => evV (source H tails) x .callByValuePar T [pre x p q] (render H tails true b) z
          | other => other)=
          (match evV (target H tails) x .callByValueSeq U [pre x p q] H.head q with
          | some (some z) => evV (target H tails) x .callByValueSeq U [pre x p q] (render H tails false b) z
          | other => other)
        rw [hhead,hhead']
        cases hz : lexical H H.head x q with
        | none => rfl
        | some result => cases result with
          | none => rfl
          | some z =>
            exact evaluator_of_shift H tails x T (source_ok H tails x k) (source_lexical H tails x k) k ih b [pre x p q] z
              (RecursiveCodeGrammar.lexical_success H H.head H.lexical x q z hq hz).1

theorem evaluator_eq (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (render H tails false e) p :=
  evaluator_of_shift H tails x _ (source_ok H tails x k) (source_lexical H tails x k) k (tables_shifted H tails x k) e E p hp

theorem stable_eq (H : Header) (tails : List MExp) (e : MExp) (x : List Char) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
      [] (render H tails true e) x.length=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
      [] (render H tails false e) x.length := by
  have hsource := LastCodewordHelpers.stable H (source H tails) (source_installed H tails) (source_verifier H tails) x .callByValuePar
  have htarget := LastCodewordHelpers.stable H (target H tails) (target_installed H tails) (target_verifier H tails) x .callByValueSeq
  have hdefined (v : Option Nat) :
      evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
        [] (render H tails true e) x.length=some v ↔
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
        [] (render H tails false e) x.length=some v := by
    rw [←tblV_stable (source H tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target H tails) x .callByValueSeq (Nat.le_refl _),
      ←SeededClock.defined_iff (source H tails) x .callByValuePar (pick H) (floor H x) _
        (SeededClock.prefixSeed_lower _ x _ (pick H) (floor H x)) (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) hsource,
      ←ClockFreezing.defined_iff (target H tails) x .callByValueSeq (pick H) (floor H x) htarget]
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

end Shallot.MacroPeg.CBV.LastCodewordHelperGrammar
