import MacroPeg.CBV.CodewordControlHelpers

/-! Combine independent recursive header/test helpers with mutually
recursive users retaining the original capture in two Seq values. -/
namespace Shallot.MacroPeg.CBV.CodewordControlHelperGrammar
open ClockFreezing (Table)
open RecursiveCodeGrammar (canonical)
open RecursiveParserStability (Installed)
open LastCodewordHelpers (lexical_environment lexical_syntax)
open CodewordControlFilter (wholeView)
open CodewordControlHelpers (Header lexical LexicalTable rest rest_lexical rest_firstOrder
  argument argumentAt verifier verifier_allowed check head_firstOrder head_eval rest_eval argument_eval
  pick floor prefixAt prefix_eval entry seed_entry)
open CodewordControlRecursive (wordAt word_eval)

theorem argumentAt_eq (H : Header) (x : List Char) (p : Nat) :
    argumentAt H x p=match lexical H H.head x p with
    | some (some j) => lexical H (rest H) x j | other => other := rfl

def render (H : Header) (tails : List MExp) (par : Bool) : MExp → MExp
  | .call i [] => match tails[i]? with
    | none => MExp.failAlways
    | some _ => if par then .call (H.bodies.length+(i+1)) [argument H]
      else .seq (.andP (argument H)) (.seq (.andP (.call H.bodies.length [H.head])) (.call (H.bodies.length+(i+1)) [H.head,rest H]))
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
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++⟨1,verifier H⟩::tails.map (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩)⟩
def target (H : Header) (tails : List MExp) : MGrammar :=
  ⟨H.bodies.map (fun e => ⟨0,e⟩)++⟨1,verifier H⟩::tails.map (fun b => ⟨2,.seq (.param 0) (render H tails false b)⟩)⟩

theorem render_firstOrder (H : Header) (tails : List MExp) (par : Bool) :
    ∀ e, (render H tails par e).FirstOrder
  | .call i [] => by
    simp only [render]
    cases tails[i]? with
    | none => trivial
    | some b =>
      cases par
      · exact ⟨RecursiveParserStability.lexical_firstOrder _ _ (CodewordControlHelpers.argument_lexical H),⟨head_firstOrder H,True.intro⟩,
          head_firstOrder H,rest_firstOrder H,True.intro⟩
      · exact ⟨RecursiveParserStability.lexical_firstOrder _ _ (CodewordControlHelpers.argument_lexical H),True.intro⟩
  | .seq a b | .alt a b => ⟨render_firstOrder H tails par a,render_firstOrder H tails par b⟩
  | .star a | .notP a => render_firstOrder H tails par a
  | .param k => by cases par; exact CodewordControlFilter.wholeView_firstOrder _ True.intro; trivial
  | .eps | .any | .chr _ | .range _ _ | .lit _ => trivial
  | .call _ (_::_) | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

theorem source_installed (H : Header) (tails : List MExp) : Installed H.bodies (source H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [source,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem source_verifier (H : Header) (tails : List MExp) :
    ruleAtM (source H tails).rules H.bodies.length=some ⟨1,verifier H⟩ := by
  simp [source,ruleAtM_eq_getElem?]

theorem source_firstOrder (H : Header) (tails : List MExp) : (source H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact HelperArgument.firstOrder _ (verifier H) (verifier_allowed H)
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨⟨head_firstOrder H,True.intro⟩,render_firstOrder H tails true b⟩

theorem target_installed (H : Header) (tails : List MExp) : Installed H.bodies (target H tails) := by
  intro i e hi
  have hb := (List.getElem?_eq_some_iff.mp hi).1
  simp only [target,ruleAtM_eq_getElem?]
  rw [List.getElem?_append_left (by simpa using hb)]
  simp [hi]

theorem target_verifier (H : Header) (tails : List MExp) :
    ruleAtM (target H tails).rules H.bodies.length=some ⟨1,verifier H⟩ := by
  simp [target,ruleAtM_eq_getElem?]

theorem target_firstOrder (H : Header) (tails : List MExp) : (target H tails).FirstOrder := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact RecursiveParserStability.lexical_firstOrder _ e (H.valid e he)
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact HelperArgument.firstOrder _ (verifier H) (verifier_allowed H)
    · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨True.intro,render_firstOrder H tails false b⟩

theorem source_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (source H tails).rules (H.bodies.length+(i+1))=(tails[i]?).map
      (fun b => ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩) := by
  simp [source,ruleAtM_eq_getElem?,List.getElem?_append_right]
theorem target_rule (H : Header) (tails : List MExp) (i : Nat) :
    ruleAtM (target H tails).rules (H.bodies.length+(i+1))=(tails[i]?).map
      (fun b => ⟨2,.seq (.param 0) (render H tails false b)⟩) := by
  simp [target,ruleAtM_eq_getElem?,List.getElem?_append_right]

abbrev sourceTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (source H tails) x .callByValuePar (pick H) (floor H x)
    (SeededClock.prefixSeed (source H tails) x .callByValuePar (pick H) (floor H x)) k
abbrev targetTable (H : Header) (tails : List MExp) (x : List Char) (k : Nat) : Table :=
  SeededClock.table (target H tails) x .callByValueSeq (pick H) (floor H x)
    (SeededClock.prefixSeed (target H tails) x .callByValueSeq (pick H) (floor H x)) k

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
  apply CodewordControlHelpers.lexical_table H _ (source_installed H tails) x _ _ (source_ok H tails x k)
  intro i hi
  exact SeededClock.rows _ x _ (pick H) (floor H x) _
    (SeededClock.prefixSeed_rows _ x _ (pick H) (floor H x)) k i (by simp [pick,LastCodewordHelpers.pick]; omega) []

theorem target_ok (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    OkTV x.length (targetTable H tails x k) := by
  intro i W p j hv
  exact tblV_ok _ x _ (floor H x+(k+1)) i W p j
    ((SeededClock.physical_bound _ x _ (pick H) (floor H x) _
      (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) k i W p).eq_of_some hv)

theorem target_lexical (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    LexicalTable H (target H tails) x .callByValueSeq (targetTable H tails x k) := by
  apply CodewordControlHelpers.lexical_table H _ (target_installed H tails) x _ _ (target_ok H tails x k)
  intro i hi
  exact SeededClock.rows _ x _ (pick H) (floor H x) _
    (SeededClock.prefixSeed_rows _ x _ (pick H) (floor H x)) k i (by simp [pick,LastCodewordHelpers.pick]; omega) []

/-- The installed verifier uses only actual stabilized recursive helpers. -/
theorem verifier_call (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (target H tails) x .callByValueSeq (targetTable H tails x k) E (.call H.bodies.length [H.head]) p=
      (match lexical H H.head x p with
      | some (some j) => check H x (pre x p j) j | other => other) := by
  have hr := target_verifier H tails
  rw [evV_call_seq hr rfl]
  simp only [evSeqArgs,head_eval H _ x _ _ (target_lexical H tails x k) E p hp]
  change _=
    (match lexical H H.head x p with
    | some (some j) => evV (RecursiveParserStability.grammar H.bodies) x .callByValuePar
      (canonical H.bodies x) [pre x p j] (verifier H) j | other => other)
  cases hv : lexical H H.head x p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp hv).1
      dsimp only []
      unfold targetTable
      rw [SeededClock.rows _ x _ (pick H) (floor H x) _
        (SeededClock.prefixSeed_rows _ x _ (pick H) (floor H x)) k H.bodies.length (by simp [pick,LastCodewordHelpers.pick]),
        show floor H x=RecursiveParserStability.floor H.bodies x+1 from rfl,valAt_tblV_succ hr _ hj]
      exact CodewordControlHelpers.syntax_eval H _ (target_installed H tails) x _ _ (tblV_ok _ x _ _)
        (CodewordControlHelpers.physical_lexical H _ (target_installed H tails) x .callByValueSeq)
        [pre x p j] (verifier H)
        (verifier_allowed H) j hj

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
    lexical H H.head x p=some (some j) → lexical H (rest H) x j=some (some q) →
    valAt (T (H.bodies.length+(i+1)) [pre x p q]) p=
      match check H x (pre x p j) j with
      | some (some _) => valAt (U (H.bodies.length+(i+1)) [pre x p j,pre x j q]) q
      | other => other

theorem evaluator_of_shift (H : Header) (tails : List MExp) (x : List Char)
    (T : Table) (hOk : OkTV x.length T) (hLexT : LexicalTable H (source H tails) x .callByValuePar T) (k : Nat)
    (hShift : Shifted H tails x T (targetTable H tails x k)) :
    ∀ e E F, Parameters H tails x T (targetTable H tails x k) E F → ∀ p, p≤x.length →
      evV (source H tails) x .callByValuePar T E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false e) p
  | .call i [], E, F, hEF, p, hp => by
    cases hr : tails[i]? with
    | none => simp only [render,hr]; rfl
    | some b =>
      have hs : ruleAtM (source H tails).rules (H.bodies.length+(i+1))=some
          ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
      have ht : ruleAtM (target H tails).rules (H.bodies.length+(i+1))=some
          ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
      simp only [render,hr,ite_true]
      rw [evV_call_par hs rfl (by decide)]
      change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.andP (argument H)) p with
        | some (some j) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) F
          (.seq (.andP (.call H.bodies.length [H.head])) (.call (H.bodies.length+(i+1)) [H.head,rest H])) j
        | other => other)
      rw [CallLookahead.evV_peek]
      simp only [evParArgs,argument_eval H _ x _ T hLexT E p hp,
        argument_eval H _ x _ _ (target_lexical H tails x k) F p hp,argumentAt_eq]
      cases ha : lexical H H.head x p with
      | none => rfl
      | some rr => cases rr with
        | none => rfl
        | some j =>
          have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha).1
          dsimp only []
          cases hd : lexical H (rest H) x j with
          | none => rfl
          | some rr => cases rr with
            | none => rfl
            | some q =>
              dsimp only [CallLookahead.peek]
              rw [hShift i b hr p j q hp ha hd]
              change _=(match evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.andP (.call H.bodies.length [H.head])) p with
                | some (some z) => evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (.call (H.bodies.length+(i+1)) [H.head,rest H]) z
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
                  simp only [evSeqArgs,head_eval H _ x _ _ (target_lexical H tails x k) F p hp,ha]
                  rw [rest_eval H _ x _ _ (target_lexical H tails x k) F j hj,hd]
  | .seq a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk hLexT k hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (hh.symm.trans hv)]
      | some q =>
        rw [evV_seq_ok hv,evV_seq_ok (hh.symm.trans hv)]
        exact evaluator_of_shift H tails x T hOk hLexT k hShift b E F hEF q (evV_ok hOk _ p hp q hv)
  | .alt a b, E, F, hEF, p, hp => by
    have hh := evaluator_of_shift H tails x T hOk hLexT k hShift a E F hEF p hp
    simp only [render]
    cases hv : evV (source H tails) x .callByValuePar T E (render H tails true a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (hh.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_alt_fail hv,evV_alt_fail (hh.symm.trans hv)]; exact evaluator_of_shift H tails x T hOk hLexT k hShift b E F hEF p hp
      | some q => rw [evV_alt_ok hv,evV_alt_ok (hh.symm.trans hv)]
  | .star a, E, F, hEF, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun q hq => evaluator_of_shift H tails x T hOk hLexT k hShift a E F hEF q (by omega))
  | .notP a, E, F, hEF, p, hp => by
    simp only [render,evV]
    rw [evaluator_of_shift H tails x T hOk hLexT k hShift a E F hEF p hp]
  | .param z, E, F, hEF, p, _ => hEF z p
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _
  | .range _ _, _, _, _, _, _ | .lit _, _, _, _, _, _ => rfl
  | .call _ (_::_), _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl

theorem source_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (sourceTable H tails x (k+1) (H.bodies.length+(i+1)) W) p=
      evV (source H tails) x .callByValuePar (sourceTable H tails x k) W
        (.seq (.seq H.head (.param 0)) (render H tails true b)) p := by
  exact SeededClock.user_step (source H tails) x .callByValuePar (pick H) (floor H x) _ k (H.bodies.length+(i+1))
    (by simp [pick,LastCodewordHelpers.pick]) ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩
    (by rw [source_rule,hr]; rfl) W p hp

theorem target_step (H : Header) (tails : List MExp) (x : List Char) (k i : Nat)
    (b : MExp) (hr : tails[i]?=some b) (W : List (List Char)) (p : Nat) (hp : p≤x.length) :
    valAt (targetTable H tails x (k+1) (H.bodies.length+(i+1)) W) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) W
        (.seq (.param 0) (render H tails false b)) p := by
  exact SeededClock.user_step (target H tails) x .callByValueSeq (pick H) (floor H x) _ k (H.bodies.length+(i+1))
    (by simp [pick,LastCodewordHelpers.pick]) ⟨2,.seq (.param 0) (render H tails false b)⟩
    (by rw [target_rule,hr]; rfl) W p hp

theorem tables_shifted (H : Header) (tails : List MExp) (x : List Char) (k : Nat) :
    Shifted H tails x (sourceTable H tails x k) (targetTable H tails x k) := by
  induction k with
  | zero =>
    intro i b hr p j q hp ha hd
    have hs : ruleAtM (source H tails).rules (H.bodies.length+(i+1))=some
        ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
    have ht : ruleAtM (target H tails).rules (H.bodies.length+(i+1))=some
        ⟨2,.seq (.param 0) (render H tails false b)⟩ := by rw [target_rule,hr]; rfl
    have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha).1
    have hq := (RecursiveCodeGrammar.lexical_success H.toHeader (rest H) (rest_lexical H) x j q hj hd).1
    change valAt (SeededClock.prefixSeed _ x .callByValuePar (pick H) (floor H x) (H.bodies.length+(i+1)) [pre x p q]) p=_
    rw [SeededClock.prefixSeed_query _ x _ (pick H) (floor H x) (H.bodies.length+(i+1)) (by simp [pick,LastCodewordHelpers.pick]) 1 _ _ hs _ p hp]
    have hlex : LexicalTable H (source H tails) x .callByValuePar
        (ClockFreezing.frozen (source H tails) x .callByValuePar (pick H) (floor H x) 0) := by
      apply CodewordControlHelpers.lexical_table H _ (source_installed H tails) x _ _
        (ClockFreezing.frozen_ok _ x _ (pick H) (floor H x) 0)
      intro a ha
      exact ClockFreezing.frozen_rows _ x _ (pick H) (floor H x) 0 a
        (by simp [pick,LastCodewordHelpers.pick]; omega) []
    rw [prefix_eval H _ (source_installed H tails) x _ _
      (ClockFreezing.frozen_ok _ x _ (pick H) (floor H x) 0) hlex _ p hp]
    change _=(match check H x (pre x p j) j with
      | some (some _) => valAt (SeededClock.prefixSeed _ x .callByValueSeq (pick H) (floor H x) (H.bodies.length+(i+1)) [pre x p j,pre x j q]) q
      | other => other)
    rw [SeededClock.prefixSeed_query _ x _ (pick H) (floor H x) (H.bodies.length+(i+1)) (by simp [pick,LastCodewordHelpers.pick]) 2 _ _ ht _ q hq,word_eval]
    exact seed_entry H x p j q hp ha hd
  | succ k ih =>
    intro i b hr p j q hp ha hd
    let T := sourceTable H tails x k
    let U := targetTable H tails x k
    have hj := (RecursiveCodeGrammar.lexical_success H.toHeader H.head H.lexical x p j hp ha).1
    have hd0 := (rest_eval H (source H tails) x .callByValuePar T (source_lexical H tails x k) [] j hj).trans hd
    have hq := evV_ok (source_ok H tails x k) _ j hj q hd0
    rw [source_step H tails x k i b hr _ p hp]
    rw [entry H (source H tails) (source_installed H tails) x T (source_sound H tails x k) (source_ok H tails x k) (source_lexical H tails x k)
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
            exact evaluator_of_shift H tails x T (source_ok H tails x k) (source_lexical H tails x k) k ih b _ _
              (parameters_parts H tails x T U _ _) w hw

theorem evaluator_eq (H : Header) (tails : List MExp) (x : List Char) (k : Nat)
    (e : MExp) (E F : List (List Char))
    (hEF : Parameters H tails x (sourceTable H tails x k) (targetTable H tails x k) E F)
    (p : Nat) (hp : p≤x.length) :
    evV (source H tails) x .callByValuePar (sourceTable H tails x k) E (render H tails true e) p=
      evV (target H tails) x .callByValueSeq (targetTable H tails x k) F (render H tails false e) p :=
  evaluator_of_shift H tails x _ (source_ok H tails x k) (source_lexical H tails x k) k (tables_shifted H tails x k) e E F hEF p hp

theorem stable_eq (H : Header) (tails : List MExp) (e : MExp) (x : List Char) :
    evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
      [] (render H tails true e) x.length=
    evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
      [] (render H tails false e) x.length := by
  have hsource := CodewordControlHelpers.stable H (source H tails) (source_installed H tails) (source_verifier H tails) x .callByValuePar
  have htarget := CodewordControlHelpers.stable H (target H tails) (target_installed H tails) (target_verifier H tails) x .callByValueSeq
  have hdefined (v : Option Nat) :
      evV (source H tails) x .callByValuePar (tblV (source H tails) x .callByValuePar (iterBoundV (source H tails) x))
        [] (render H tails true e) x.length=some v ↔
      evV (target H tails) x .callByValueSeq (tblV (target H tails) x .callByValueSeq (iterBoundV (target H tails) x))
        [] (render H tails false e) x.length=some v := by
    rw [←tblV_stable (source H tails) x .callByValuePar (Nat.le_refl _),
      ←tblV_stable (target H tails) x .callByValueSeq (Nat.le_refl _),
      ←SeededClock.defined_iff (source H tails) x .callByValuePar (pick H) (floor H x) _
        (SeededClock.prefixSeed_lower _ x _ (pick H) (floor H x)) (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) hsource,
      ←SeededClock.defined_iff (target H tails) x .callByValueSeq (pick H) (floor H x) _
        (SeededClock.prefixSeed_lower _ x _ (pick H) (floor H x)) (SeededClock.prefixSeed_upper _ x _ (pick H) (floor H x)) htarget]
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

/-- An undefined actual argument is checked before any user-row query
on either side, including before a failed codeword comparison. -/
theorem undefined_argument (H : Header) (tails : List MExp) (i : Nat) (b : MExp)
    (hr : tails[i]?=some b) (x : List Char) (p : Nat) (T U : Table) (E F : List (List Char))
    (ha : evV (source H tails) x .callByValuePar T E (argument H) p=none)
    (hb : evV (target H tails) x .callByValueSeq U F (argument H) p=none) :
    evV (source H tails) x .callByValuePar T E (render H tails true (.call i [])) p=none ∧
    evV (target H tails) x .callByValueSeq U F (render H tails false (.call i [])) p=none := by
  have hs : ruleAtM (source H tails).rules (H.bodies.length+(i+1))=some
      ⟨1,.seq (.seq H.head (.param 0)) (render H tails true b)⟩ := by rw [source_rule,hr]; rfl
  constructor
  · simp only [render,hr,ite_true]
    rw [evV_call_par hs rfl (by decide)]
    simp only [evParArgs,ha]
  · simp only [render,hr]
    apply evV_seq_none
    rw [CallLookahead.evV_peek,hb]
    rfl

end Shallot.MacroPeg.CBV.CodewordControlHelperGrammar
