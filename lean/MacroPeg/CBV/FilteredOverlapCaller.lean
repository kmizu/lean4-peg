import MacroPeg.CBV.CaptureProductExtension

/-! Shifted replay with an arbitrary independent recursive capture parser.
The target selects a generated state-filtered argument and retains the full
captured value in an actual unary call. -/
namespace Shallot.MacroPeg.CBV.FilteredOverlapCaller
open RegularCaptureProduct
open PeriodicCaptureMachine (phase machine)
open ClockFreezing (Table)

/-- Continuations may inspect and replay captured parameters and invoke the
independent recursive helper component at arbitrary positions. -/
def Tail (n : Nat) : MExp → Prop
  | .seq a b | .alt a b => Tail n a ∧ Tail n b
  | .star a | .notP a => Tail n a
  | .call i [] => i<n
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True
  | _ => False

theorem tail_firstOrder (n : Nat) : ∀ e, Tail n e → e.FirstOrder
  | .seq a b, he | .alt a b, he => ⟨tail_firstOrder n a he.1,tail_firstOrder n b he.2⟩
  | .star a, he | .notP a, he => tail_firstOrder n a he
  | .call _ [], _ | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ | .param _, _ => trivial
  | .call _ (_::_), he | .dbg _, he | .lam _ _, he | .callParam _ _, he | .invoke _ _ _, he => False.elim he

def extend (nodes : List Node) (D : Machine) (extra : List MRule) : MGrammar :=
  ⟨(grammar nodes D).rules++extra⟩

def table (g : MGrammar) (x : List Char) (s : Strategy) : Table := tblV g x s (iterBoundV g x)

theorem tail_eval (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : 0<D.width)
    (left right : List MRule) (x : List Char) (E : List (List Char)) :
    ∀ e, Tail (grammar nodes D).rules.length e → ∀ p, p≤x.length →
      evV (extend nodes D left) x .callByValuePar (table (extend nodes D left) x .callByValuePar) E e p =
        evV (extend nodes D right) x .callByValueSeq (table (extend nodes D right) x .callByValueSeq) E e p
  | .call i [], hi, p, hp => by
    exact (extension_call_eq nodes hNodes D hD left x .callByValuePar .callByValueSeq i p hi hp E []).trans
      (extension_call_eq nodes hNodes D hD right x .callByValueSeq .callByValueSeq i p hi hp E []).symm
  | .seq a b, he, p, hp => by
    have ha := tail_eval nodes hNodes D hD left right x E a he.1 p hp
    change (match evV _ _ _ _ _ a p with | some (some z) => evV _ _ _ _ _ b z | other => other)=_
    rw [ha]
    cases hv : evV (extend nodes D right) x .callByValueSeq (table _ x .callByValueSeq) E a p with
    | none => rw [evV_seq_none hv]
    | some result => cases result with
      | none => rw [evV_seq_fail hv]
      | some z =>
        dsimp only []
        rw [evV_seq_ok hv]
        exact tail_eval nodes hNodes D hD left right x E b he.2 z (evV_ok (tblV_ok _ _ _ _) a p hp z hv)
  | .alt a b, he, p, hp => by
    have ha := tail_eval nodes hNodes D hD left right x E a he.1 p hp
    change (match evV _ _ _ _ _ a p with | some none => evV _ _ _ _ _ b p | other => other)=_
    rw [ha]
    cases hv : evV (extend nodes D right) x .callByValueSeq (table _ x .callByValueSeq) E a p with
    | none => rw [evV_alt_none hv]
    | some result => cases result with
      | none =>
        dsimp only []
        rw [evV_alt_fail hv]
        exact tail_eval nodes hNodes D hD left right x E b he.2 p hp
      | some z => rw [evV_alt_ok hv]
  | .star a, he, p, hp => by
    rw [evV_star,evV_star]
    exact evStar_congr p (fun z hz => tail_eval nodes hNodes D hD left right x E a he z (by omega))
  | .notP a, he, p, hp => by
    change (match evV _ _ _ _ _ a p with | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [tail_eval nodes hNodes D hD left right x E a he p hp]
    rfl
  | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _
  | .lit _, _, _, _ | .param _, _, _, _ => rfl
  | .call _ (_::_), he, _, _ | .dbg _, he, _, _ | .lam _ _, he, _, _
  | .callParam _ _, he, _, _ | .invoke _ _ _, he, _, _ => False.elim he

def sourceRules (u : List Char) (B : MExp) : List MRule :=
  [⟨1,.seq (.seq (.lit u) (.param 0)) B⟩]

def targetRules (u : List Char) (B : MExp) : List MRule :=
  (List.range u.length).map (fun r => ⟨1,.seq (.lit (phase u r)) B⟩)

def source (nodes : List Node) (u : List Char) (B : MExp) : MGrammar :=
  extend nodes (machine u) (sourceRules u B)

def target (nodes : List Node) (u : List Char) (B : MExp) : MGrammar :=
  extend nodes (machine u) (targetRules u B)

def sourceStart (nodes : List Node) (u : List Char) (i : Nat) : MExp :=
  .call (grammar nodes (machine u)).rules.length [.call i []]

def targetStart (nodes : List Node) (u : List Char) (i : Nat) : MExp :=
  choice ((List.range u.length).map (fun r =>
    .call ((grammar nodes (machine u)).rules.length+r) [call nodes (machine u) i 0 r]))

theorem source_rule (nodes : List Node) (u : List Char) (B : MExp) :
    ruleAtM (source nodes u B).rules (grammar nodes (machine u)).rules.length =
      some ⟨1,.seq (.seq (.lit u) (.param 0)) B⟩ := by
  simp [source,extend,sourceRules,ruleAtM_eq_getElem?]

theorem target_rule (nodes : List Node) (u : List Char) (B : MExp) (r : Nat) (hr : r<u.length) :
    ruleAtM (target nodes u B).rules ((grammar nodes (machine u)).rules.length+r) =
      some ⟨1,.seq (.lit (phase u r)) B⟩ := by
  simp [target,extend,targetRules,ruleAtM_eq_getElem?,hr]

/-- Parameter-bearing rows also obey their real body equations at the
canonical bound when their arguments are actual input substrings. -/
theorem canonical_row (g : MGrammar) (x : List Char) (s : Strategy) (i : Nat) (rule : MRule)
    (hr : ruleAtM g.rules i=some rule) (W : List (List Char)) (hW : W∈words (subStrs x) rule.arity)
    (p : Nat) (hp : p≤x.length) :
    valAt (table g x s i W) p=evV g x s (table g x s) W rule.body p := by
  unfold table
  rw [(bound_fixed g x s) i rule W hr hW p hp]
  exact valAt_tblV_succ hr W hp

theorem source_firstOrder (nodes : List Node) (u : List Char) (B : MExp) (hB : B.FirstOrder) :
    (source nodes u B).FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact grammar_firstOrder nodes (machine u) rule hr
  · simp only [sourceRules,List.mem_singleton] at hr
    subst rule
    exact ⟨⟨True.intro,True.intro⟩,hB⟩

theorem target_firstOrder (nodes : List Node) (u : List Char) (B : MExp) (hB : B.FirstOrder) :
    (target nodes u B).FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact grammar_firstOrder nodes (machine u) rule hr
  · obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨True.intro,hB⟩

theorem targetStart_firstOrder (nodes : List Node) (u : List Char) (i : Nat) :
    (targetStart nodes u i).FirstOrder := by
  apply choice_firstOrder
  intro e he
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp he
  exact ⟨True.intro,True.intro⟩

theorem choice_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (p : Nat) (R : Nat → MExp) (states : List Nat) (hne : states≠[])
    (h : ∀ r∈states, evV g x s T [] (R r) p=none) :
    evV g x s T [] (choice (states.map R)) p=none := by
  cases states with
  | nil => contradiction
  | cons r states => exact evV_alt_none (h r (by simp))

theorem choice_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (p : Nat) (R : Nat → MExp) : ∀ (states : List Nat),
    (∀ r∈states, evV g x s T [] (R r) p=some none) →
    evV g x s T [] (choice (states.map R)) p=some none
  | [], _ => rfl
  | r::states, h => by
    rw [List.map_cons,choice,evV_alt_fail (h r (by simp))]
    exact choice_fail g x s T p R states (fun r hr => h r (by simp [hr]))

/-- For a successful capture, the selected nonsink phase makes shifted
source replay and the target literal agree as complete partial results. -/
theorem replay_rotation (g h : MGrammar) (x : List Char) (T U : Table)
    (u : List Char) (hu : u≠[]) (p j : Nat) (_hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=pre x p j++sfx x j)
    (hphase : run (machine u) 0 (pre x p j)<u.length) :
    evV g x .callByValuePar T [pre x p j] (.seq (.lit u) (.param 0)) p =
      evV h x .callByValueSeq U [pre x p j]
        (.lit (phase u (run (machine u) 0 (pre x p j)))) j := by
  have hr := PeriodicCaptureMachine.run_rotation u hu (pre x p j) 0 (List.length_pos_iff.mpr hu) hphase
  simp only [phase,List.drop_zero,List.take_zero,List.append_nil] at hr
  have hparam : evV g x .callByValuePar T [pre x p j] (.param 0) p=some (some j) := by
    simp only [evV,List.getElem?_cons_zero,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hcap,length_sfx x hj]
  rw [BlockCapture.prefix_rotate g x .callByValuePar T _ u _ hr p,evV_seq_ok hparam]
  rfl

theorem nonperiodic_replay_fail (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (hu : u≠[]) (p j : Nat) (hp : p≤x.length)
    (hv : evV g x .callByValuePar T [] a p=some (some j))
    (hsink : ¬run (machine u) 0 (pre x p j)<u.length) :
    evV g x .callByValuePar T [pre x p j] (.seq (.lit u) (.param 0)) p=some none := by
  cases hr : evV g x .callByValuePar T [pre x p j] (.seq (.lit u) (.param 0)) p with
  | none =>
    have hh := WordArguments.word_eval g x .callByValuePar T [pre x p j]
      (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p
    rw [hr] at hh
    simp only [WordArguments.value,List.getElem?_cons_zero,Option.bind_some,Option.map_some,
      WordArguments.literal,evV] at hh
    split at hh <;> contradiction
  | some result => cases result with
    | none => rfl
    | some z =>
      obtain ⟨v,_,he⟩ := OverlapNecessity.actual_capture_rotation g x T hT [] a ha u p j z hp hv hr
      exact False.elim (hsink (PeriodicCaptureMachine.prefix_run u (pre x p j) hu ⟨v,he.symm⟩))

/-- A fixed source/target grammar pair preserves the complete partial result
for every input. The selected argument is the actual captured string. -/
theorem evaluator_eq (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (B : MExp) (hB : Tail (grammar nodes (machine u)).rules.length B)
    (i p : Nat) (hi : i<nodes.length) (x : List Char) (hp : p≤x.length) :
    evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar) []
        (sourceStart nodes u i) p =
      evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq) []
        (targetStart nodes u i) p := by
  have hu' := List.length_pos_iff.mpr hu
  have hD := PeriodicCaptureMachine.valid u hu
  have hq : 0<(machine u).width := hD.1
  have hzero : 0<(machine u).width := hD.1
  have hi' : i<(grammar nodes (machine u)).rules.length := Nat.lt_of_lt_of_le hi (by simp [grammar])
  have hhead : evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar) [] (.call i []) p =
      evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq) [] (.call i []) p := by
    exact (extension_call_eq nodes hNodes (machine u) hq (sourceRules u B) x
      .callByValuePar .callByValueSeq i p hi' hp [] []).trans
        (extension_call_eq nodes hNodes (machine u) hq (targetRules u B) x
          .callByValueSeq .callByValueSeq i p hi' hp [] []).symm
  have hfilter (r : Nat) (hr : r<u.length) :
      evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq) []
        (call nodes (machine u) i 0 r) p =
      filtered (machine u) x 0 r p
        (evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar) [] (.call i []) p) := by
    rw [hhead]
    exact extension_product_correct nodes hNodes (machine u) hD (targetRules u B) x i 0 r p hi
      hzero (by change r<u.length+1; omega) hp
  unfold sourceStart
  rw [evV_call_par (source_rule nodes u B) rfl (by decide)]
  simp only [evParArgs]
  cases hv : evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar) [] (.call i []) p with
  | none =>
    dsimp only []
    symm
    apply choice_none
    · simpa using hu
    · intro r hr
      rw [evV_call_seq (target_rule nodes u B r (List.mem_range.mp hr)) rfl]
      simp only [evSeqArgs,hfilter r (List.mem_range.mp hr),hv,filtered]
  | some result => cases result with
    | none =>
      dsimp only []
      symm
      apply choice_fail
      intro r hr
      rw [evV_call_seq (target_rule nodes u B r (List.mem_range.mp hr)) rfl]
      simp only [evSeqArgs,hfilter r (List.mem_range.mp hr),hv,filtered]
    | some j =>
      dsimp only []
      have hSound := tblV_sound (x := x) (s := .callByValuePar) (source_firstOrder nodes u B (tail_firstOrder _ B hB)) (by decide)
        (iterBoundV (source nodes u B) x)
      have hj := ReplayFusion.success_prefix hSound [] (.call i []) True.intro p j hp hv
      have hW : [pre x p j]∈words (subStrs x) 1 :=
        (mem_words _ _ _).mpr ⟨rfl,by intro w hw; simp only [List.mem_singleton] at hw; subst w; exact pre_mem hp j⟩
      rw [canonical_row _ x .callByValuePar _ _ (source_rule nodes u B) [pre x p j] hW p hp]
      let t := run (machine u) 0 (pre x p j)
      let v := evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar)
        [pre x p j] (.seq (.seq (.lit u) (.param 0)) B) p
      have hbody (ht : t<u.length) : v =
          evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq)
            [pre x p j] (.seq (.lit (phase u t)) B) j := by
        have hrot := replay_rotation (source nodes u B) (target nodes u B) x
          (table (source nodes u B) x .callByValuePar) (table (target nodes u B) x .callByValueSeq)
          u hu p j hp hj.1 hj.2 ht
        change (match evV (source nodes u B) x .callByValuePar (table (source nodes u B) x .callByValuePar)
          [pre x p j] (.seq (.lit u) (.param 0)) p with
          | some (some z) => evV (source nodes u B) x .callByValuePar
              (table (source nodes u B) x .callByValuePar) [pre x p j] B z
          | other => other)=_
        rw [hrot]
        cases hz : evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq)
            [pre x p j] (.lit (phase u t)) j with
        | none => rw [evV_seq_none hz]
        | some result => cases result with
          | none => rw [evV_seq_fail hz]
          | some z =>
            dsimp only []
            rw [evV_seq_ok hz]
            exact tail_eval nodes hNodes (machine u) hD.1 (sourceRules u B) (targetRules u B)
              x [pre x p j] B hB z (evV_ok (tblV_ok _ _ _ _) (.lit (phase u t)) j hj.1 z hz)
      have hbranches (r : Nat) (hr : r<u.length) :
          evV (target nodes u B) x .callByValueSeq (table (target nodes u B) x .callByValueSeq) []
            (.call ((grammar nodes (machine u)).rules.length+r) [call nodes (machine u) i 0 r]) p =
              if r=t then v else some none := by
        rw [evV_call_seq (target_rule nodes u B r hr) rfl]
        simp only [evSeqArgs,hfilter r hr,hv,filtered]
        by_cases he : r=t
        · subst r
          rw [if_pos rfl]
          dsimp only []
          rw [canonical_row _ x .callByValueSeq _ _ (target_rule nodes u B _ hr) [pre x p j] hW j hj.1]
          simpa only [ite_true] using (hbody hr).symm
        · rw [if_neg (Ne.symm he)]
          simp only [if_neg he]
      change v=evV _ _ _ _ _ (choice ((List.range u.length).map _)) p
      rw [choice_eval_unique (chosen := t) (v := v)]
      · by_cases ht : t<u.length
        · simp [List.mem_range,ht]
        · rw [if_neg (by simpa only [List.mem_range] using ht)]
          exact evV_seq_fail (nonperiodic_replay_fail (source nodes u B) x _ hSound (.call i [])
            True.intro u hu p j hp hv ht)
      · intro r hr
        exact hbranches r (List.mem_range.mp hr)

theorem decide_eq (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (B : MExp) (hB : Tail (grammar nodes (machine u)).rules.length B)
    (i : Nat) (hi : i<nodes.length) (x : List Char) :
    decideObsV .callByValuePar (source nodes u B) x (sourceStart nodes u i) =
      decideObsV .callByValueSeq (target nodes u B) x (targetStart nodes u i) := by
  unfold decideObsV
  have he := evaluator_eq nodes hNodes u hu B hB i x.length hi x (by omega)
  unfold table at he
  rw [he]

theorem observations_iff (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (B : MExp) (hB : Tail (grammar nodes (machine u)).rules.length B)
    (i : Nat) (hi : i<nodes.length) (x : List Char) (rest : Option (List Char)) :
    SObs (source nodes u B) .callByValuePar (sourceStart nodes u i) x rest ↔
      SObs (target nodes u B) .callByValueSeq (targetStart nodes u i) x rest := by
  rw [←decideObsV_iff (e := sourceStart nodes u i)
      (source_firstOrder nodes u B (tail_firstOrder _ B hB)) (by decide) ⟨True.intro,True.intro⟩,
    ←decideObsV_iff (e := targetStart nodes u i)
      (target_firstOrder nodes u B (tail_firstOrder _ B hB)) (by decide) (targetStart_firstOrder nodes u i),
    decide_eq nodes hNodes u hu B hB i hi x]

/-- One fixed target grammar and start expression work for all unchanged
original strings; successful capture length is unbounded. -/
theorem language_translation (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (B : MExp) (hB : Tail (grammar nodes (machine u)).rules.length B)
    (i : Nat) (hi : i<nodes.length) :
    ∃ g start, g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (source nodes u B) .callByValuePar (sourceStart nodes u i) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨target nodes u B,targetStart nodes u i,target_firstOrder nodes u B (tail_firstOrder _ B hB),
    targetStart_firstOrder nodes u i,fun x => observations_iff nodes hNodes u hu B hB i hi x (some [])⟩

/-- Three-character shift with a graph argument chosen at runtime:
phase one selects bca and the full abca capture is reused after #. A winning
nonperiodic abcx capture is rejected. -/
theorem retained_capture_execution :
    let nodes : List Node := [.alt 1 2,.lit "abcx".toList,.lit "abca".toList]
    let u := "abc".toList
    let B := MExp.seq (.lit ['#']) (.seq (.param 0) (.notP .any))
    let gp := source nodes u B
    let gs := target nodes u B
    let good := "abcabca#abca".toList
    let bad := "abcxabc#abcx".toList
    evV gp good .callByValuePar (tblV gp good .callByValuePar 12) [] (sourceStart nodes u 0) good.length=some (some 0) ∧
    evV gs good .callByValueSeq (tblV gs good .callByValueSeq 12) [] (targetStart nodes u 0) good.length=some (some 0) ∧
    evV gp bad .callByValuePar (tblV gp bad .callByValuePar 12) [] (sourceStart nodes u 0) bad.length=some none ∧
    evV gs bad .callByValueSeq (tblV gs bad .callByValueSeq 12) [] (targetStart nodes u 0) bad.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.FilteredOverlapCaller
