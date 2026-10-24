import MacroPeg.CBV.SeededClock

/-! Recapture through recursive user control, with actual phase-filtered
arguments. Prefix-failure seeds synchronize early argument rejection. -/
namespace Shallot.MacroPeg.CBV.RecursiveFilteredOverlap
open RegularCaptureProduct
open PeriodicCaptureMachine (machine phase)
open ClockFreezing (Table)
open FilteredOverlapCaller (sourceStart targetStart)

/-- Raw call zero recaptures; raw call j+1 invokes independent helper j.
The full current capture remains available in parameters around either call. -/
def render (seq : Bool) (nodes : List Node) (u : List Char) (i : Nat) : MExp → MExp
  | .call 0 [] => if seq then targetStart nodes u i else sourceStart nodes u i
  | .call (j+1) [] => if j<(grammar nodes (machine u)).rules.length then .call j [] else MExp.failAlways
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (render seq nodes u i a) (render seq nodes u i b)
  | .alt a b => .alt (render seq nodes u i a) (render seq nodes u i b)
  | .star a => .star (render seq nodes u i a)
  | .notP a => .notP (render seq nodes u i a)
  | .eps => .eps
  | .any => .any
  | .chr c => .chr c
  | .range lo hi => .range lo hi
  | .lit w => .lit w
  | .param j => .param j
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

theorem render_firstOrder (seq : Bool) (nodes : List Node) (u : List Char) (i : Nat) :
    ∀ e, (render seq nodes u i e).FirstOrder
  | .call 0 [] => by cases seq <;> simp only [render,Bool.false_eq_true,ite_false,ite_true]; exact ⟨True.intro,True.intro⟩; exact FilteredOverlapCaller.targetStart_firstOrder nodes u i
  | .call (j+1) [] => by simp only [render]; split <;> trivial
  | .call j (_::_) => by cases j <;> trivial
  | .seq a b | .alt a b => ⟨render_firstOrder seq nodes u i a,render_firstOrder seq nodes u i b⟩
  | .star a | .notP a => render_firstOrder seq nodes u i a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => trivial
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => trivial

abbrev parGrammar (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) : MGrammar :=
  FilteredOverlapCaller.source nodes u (render false nodes u i B)

abbrev seqGrammar (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) : MGrammar :=
  FilteredOverlapCaller.target nodes u (render true nodes u i B)

abbrev helpers (nodes : List Node) (u : List Char) := component nodes (machine u)
abbrev parTable (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (parGrammar nodes u i B) x .callByValuePar k
abbrev seqTable (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (seqGrammar nodes u i B) x .callByValueSeq k

theorem par_installed (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) :
    RecursiveParserStability.Installed (helpers nodes u) (parGrammar nodes u i B) := component_installed _ _ _
theorem seq_installed (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) :
    RecursiveParserStability.Installed (helpers nodes u) (seqGrammar nodes u i B) := component_installed _ _ _

theorem par_firstOrder (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) :
    (parGrammar nodes u i B).FirstOrder := FilteredOverlapCaller.source_firstOrder _ _ _ (render_firstOrder false _ _ _ B)
theorem seq_firstOrder (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) :
    (seqGrammar nodes u i B).FirstOrder := FilteredOverlapCaller.target_firstOrder _ _ _ (render_firstOrder true _ _ _ B)

/-- Frozen independent queries at every seeded user stage are the original
canonical physical queries, not supplied information about captures. -/
theorem query_eq (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : 0<D.width)
    (extra : List MRule) (x : List Char) (s : Strategy) (k j p : Nat)
    (hj : j<(grammar nodes D).rules.length) (hp : p≤x.length) (E : List (List Char)) :
    let g := FilteredOverlapCaller.extend nodes D extra
    evV g x s (SeededClock.rounds (component nodes D) g x s k) E (.call j []) p =
      evV (grammar nodes D) x .callByValueSeq
        (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) [] (.call j []) p := by
  dsimp only []
  unfold FilteredOverlapCaller.extend
  rw [SeededClock.rounds_lexical (component_valid nodes hNodes D hD) (component_installed nodes D extra)
    x s k E [] (.call j []) (by simpa [component,RecursiveParserStability.Lexical] using hj) p hp]
  exact extension_call_eq nodes hNodes D hD extra x s .callByValueSeq j p hj hp [] []

def Shifted (nodes : List Node) (u : List Char) (i : Nat) (B : MExp) (x : List Char) (k : Nat) : Prop :=
  ∀ p j, p≤x.length → j≤x.length →
    evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) [] (.call i []) p=some (some j) →
    ∀ r, r<u.length → r=run (machine u) 0 (pre x p j) →
      valAt (parTable nodes u i B x k (grammar nodes (machine u)).rules.length [pre x p j]) p =
        valAt (seqTable nodes u i B x k ((grammar nodes (machine u)).rules.length+r) [pre x p j]) j

theorem choice_none (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {E : List (List Char)} (p : Nat) (R : Nat → MExp) (states : List Nat) (hne : states≠[])
    (h : ∀ r∈states, evV g x s T E (R r) p=none) :
    evV g x s T E (choice (states.map R)) p=none := by
  cases states with
  | nil => contradiction
  | cons r states => exact evV_alt_none (h r (by simp))

theorem choice_fail (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    {E : List (List Char)} (p : Nat) (R : Nat → MExp) : ∀ (states : List Nat),
    (∀ r∈states, evV g x s T E (R r) p=some none) →
    evV g x s T E (choice (states.map R)) p=some none
  | [], _ => rfl
  | r::states, h => by
    rw [List.map_cons,choice,evV_alt_fail (h r (by simp))]
    exact choice_fail g x s T p R states (fun r hr => h r (by simp [hr]))

theorem entry_eq (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B : MExp) (x : List Char) (k : Nat)
    (hRows : Shifted nodes u i B x k) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (sourceStart nodes u i) p =
      evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E (targetStart nodes u i) p := by
  have hu' := List.length_pos_iff.mpr hu
  have hD := PeriodicCaptureMachine.valid u hu
  have hi' : i<(grammar nodes (machine u)).rules.length := Nat.lt_of_lt_of_le hi (by simp [grammar])
  have hhead : evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (.call i []) p =
      evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) [] (.call i []) p :=
    (query_eq nodes hNodes (machine u) hD.1 _ x .callByValuePar k i p hi' hp E).trans
      (query_eq nodes hNodes (machine u) hD.1 _ x .callByValuePar k i p hi' hp []).symm
  have hfilter (r : Nat) (hr : r<u.length) :
      evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E (call nodes (machine u) i 0 r) p =
        filtered (machine u) x 0 r p
          (evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) [] (.call i []) p) := by
    have hl : evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E
        (call nodes (machine u) i 0 r) p =
      evV (grammar nodes (machine u)) x .callByValueSeq
        (tblV (grammar nodes (machine u)) x .callByValueSeq (iterBoundV (grammar nodes (machine u)) x)) [] (.call (key nodes (machine u) i 0 r) []) p :=
      query_eq nodes hNodes (machine u) hD.1 _ x .callByValueSeq k _ p
        (key_bound nodes (machine u) hD.1 i 0 r hi hD.1 (by change r<u.length+1; omega)) hp E
    have hc := product_correct nodes hNodes (machine u) hD x i 0 r p hi hD.1 (by change r<u.length+1; omega) hp
    dsimp only [call] at hc
    rw [hl,hc]
    congr 1
    exact (query_eq nodes hNodes (machine u) hD.1 _ x .callByValuePar k i p hi' hp []).symm
  unfold sourceStart
  rw [evV_call_par (FilteredOverlapCaller.source_rule nodes u (render false nodes u i B)) rfl (by decide)]
  simp only [evParArgs,hhead]
  cases hv : evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) [] (.call i []) p with
  | none =>
    dsimp only []
    symm
    apply choice_none
    · simpa using hu
    · intro r hr
      rw [evV_call_seq (FilteredOverlapCaller.target_rule nodes u (render true nodes u i B) r (List.mem_range.mp hr)) rfl]
      simp only [evSeqArgs,hfilter r (List.mem_range.mp hr),hv,filtered]
  | some result => cases result with
    | none =>
      dsimp only []
      symm
      apply choice_fail
      intro r hr
      rw [evV_call_seq (FilteredOverlapCaller.target_rule nodes u (render true nodes u i B) r (List.mem_range.mp hr)) rfl]
      simp only [evSeqArgs,hfilter r (List.mem_range.mp hr),hv,filtered]
    | some j =>
      dsimp only []
      have hSound := SeededClock.rounds_sound (par_firstOrder nodes u i B) (helpers nodes u) x .callByValuePar (by decide) k
      have hj := ReplayFusion.success_prefix hSound [] (.call i []) True.intro p j hp hv
      let t := run (machine u) 0 (pre x p j)
      let v := valAt (parTable nodes u i B x k (grammar nodes (machine u)).rules.length [pre x p j]) p
      have hbranches (r : Nat) (hr : r<u.length) :
          evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E
            (.call ((grammar nodes (machine u)).rules.length+r) [call nodes (machine u) i 0 r]) p =
              if r=t then v else some none := by
        rw [evV_call_seq (FilteredOverlapCaller.target_rule nodes u (render true nodes u i B) r hr) rfl]
        simp only [evSeqArgs,hfilter r hr,hv,filtered]
        by_cases he : r=t
        · subst r
          rw [if_pos rfl]
          dsimp only []
          simpa only [ite_true] using (hRows p j hp hj.1 hv t hr rfl).symm
        · rw [if_neg (Ne.symm he)]
          simp only [if_neg he]
      change v=evV _ _ _ _ _ (choice ((List.range u.length).map _)) p
      rw [choice_eval_unique (chosen := t) (v := v)]
      · by_cases ht : t<u.length
        · simp [List.mem_range,ht]
        · rw [if_neg (by simpa only [List.mem_range] using ht)]
          exact SeededClock.rounds_failed_prefix (helpers nodes u) (parGrammar nodes u i B) x .callByValuePar
            _ 1 (by simp [RecursiveParserStability.pick,helpers,component])
            (.seq (.lit u) (.param 0)) (render false nodes u i B)
            (FilteredOverlapCaller.source_rule nodes u _) ⟨True.intro,True.intro⟩ [pre x p j] _ p hp
            (FilteredOverlapCaller.nonperiodic_replay_fail _ x _ hSound (.call i []) True.intro u hu p j hp hv ht) k
      · intro r hr
        exact hbranches r (List.mem_range.mp hr)

theorem evaluator_of_rows (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B : MExp) (x : List Char) (k : Nat)
    (hRows : Shifted nodes u i B x k) :
    ∀ e E p, p≤x.length →
      evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (render false nodes u i e) p =
        evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E (render true nodes u i e) p
  | .call 0 [], E, p, hp => entry_eq nodes hNodes u hu i hi B x k hRows E p hp
  | .call (j+1) [], E, p, hp => by
    simp only [render]
    split
    · rename_i hj
      exact (query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1 _ x .callByValuePar k j p hj hp E).trans
        (query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1 _ x .callByValueSeq k j p hj hp E).symm
    · rfl
  | .call j (_::_), _, _, _ => by cases j <;> rfl
  | .seq a b, E, p, hp => by
    have ha := evaluator_of_rows nodes hNodes u hu i hi B x k hRows a E p hp
    simp only [render]
    cases hv : evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (render false nodes u i a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (ha.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (ha.symm.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (ha.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu i hi B x k hRows b E z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp z hv)
  | .alt a b, E, p, hp => by
    have ha := evaluator_of_rows nodes hNodes u hu i hi B x k hRows a E p hp
    simp only [render]
    cases hv : evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (render false nodes u i a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (ha.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (ha.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu i hi B x k hRows b E p hp
      | some z => rw [evV_alt_ok hv,evV_alt_ok (ha.symm.trans hv)]
  | .star a, E, p, hp => by
    simp only [render,evV_star]
    exact evStar_congr p (fun z hz => evaluator_of_rows nodes hNodes u hu i hi B x k hRows a E z (by omega))
  | .notP a, E, p, hp => by
    have ha := evaluator_of_rows nodes hNodes u hu i hi B x k hRows a E p hp
    change (match evV _ _ _ _ E (render false nodes u i a) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [ha]
    rfl
  | .eps, _, _, _ | .any, _, _, _ | .chr _, _, _, _ | .range _ _, _, _, _
  | .lit _, _, _, _ | .param _, _, _, _ | .dbg _, _, _, _ | .lam _ _, _, _, _
  | .callParam _ _, _, _, _ | .invoke _ _ _, _, _, _ => rfl

/-- Fresh capture can recur through the same fixed body. Prefix seeds make
early Seq argument rejection agree even at the bottom user approximation. -/
theorem tables_shifted (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B : MExp) (x : List Char) :
    ∀ k, Shifted nodes u i B x k := by
  have hD := PeriodicCaptureMachine.valid u hu
  have hpar := FilteredOverlapCaller.source_rule nodes u (render false nodes u i B)
  have hseq (r : Nat) (hr : r<u.length) := FilteredOverlapCaller.target_rule nodes u (render true nodes u i B) r hr
  have huser : RecursiveParserStability.pick (helpers nodes u) (grammar nodes (machine u)).rules.length=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser (r : Nat) : RecursiveParserStability.pick (helpers nodes u) ((grammar nodes (machine u)).rules.length+r)=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  intro k
  induction k with
  | zero =>
    intro p j hp hj hv r hr he
    have hcap := ReplayFusion.success_prefix
      (SeededClock.rounds_sound (par_firstOrder nodes u i B) (helpers nodes u) x .callByValuePar (by decide) 0)
      [] (.call i []) True.intro p j hp hv
    have hrot := FilteredOverlapCaller.replay_rotation (parGrammar nodes u i B) (seqGrammar nodes u i B) x
      (ClockFreezing.frozen (parGrammar nodes u i B) x .callByValuePar (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      (ClockFreezing.frozen (seqGrammar nodes u i B) x .callByValueSeq (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      u hu p j hp hj hcap.2 (by omega)
    subst r
    change valAt (SeededClock.prefixSeed _ x .callByValuePar _ _ _ [pre x p j]) p =
      valAt (SeededClock.prefixSeed _ x .callByValueSeq _ _ _ [pre x p j]) j
    rw [SeededClock.prefixSeed_query _ x .callByValuePar _ _ _ huser 1 _ _ hpar _ p hp,
      SeededClock.prefixSeed_query _ x .callByValueSeq _ _ _ (htuser _) 1 _ _ (hseq _ hr) _ j hj,hrot]
  | succ k ih =>
    intro p j hp hj hv r hr he
    have hcap := ReplayFusion.success_prefix
      (SeededClock.rounds_sound (par_firstOrder nodes u i B) (helpers nodes u) x .callByValuePar (by decide) (k+1))
      [] (.call i []) True.intro p j hp hv
    have hrot := FilteredOverlapCaller.replay_rotation (parGrammar nodes u i B) (seqGrammar nodes u i B) x
      (parTable nodes u i B x k) (seqTable nodes u i B x k) u hu p j hp hj hcap.2 (by omega)
    subst r
    rw [SeededClock.user_step _ x .callByValuePar _ _ _ k _ huser _ hpar _ p hp,
      SeededClock.user_step _ x .callByValueSeq _ _ _ k _ (htuser _) _ (hseq _ hr) _ j hj]
    change (match evV _ _ _ _ [pre x p j] (.seq (.lit u) (.param 0)) p with
      | some (some z) => evV _ _ _ _ [pre x p j] (render false nodes u i B) z
      | other => other)=_
    rw [hrot]
    cases hz : evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k)
        [pre x p j] (.lit (phase u (run (machine u) 0 (pre x p j)))) j with
    | none => rw [evV_seq_none hz]
    | some result => cases result with
      | none => rw [evV_seq_fail hz]
      | some z =>
        dsimp only []
        rw [evV_seq_ok hz]
        exact evaluator_of_rows nodes hNodes u hu i hi B x k ih B [pre x p j] z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ j hj z hz)

theorem evaluator_eq (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B : MExp) (x : List Char) (k : Nat)
    (e : MExp) (E : List (List Char)) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u i B) x .callByValuePar (parTable nodes u i B x k) E (render false nodes u i e) p =
      evV (seqGrammar nodes u i B) x .callByValueSeq (seqTable nodes u i B x k) E (render true nodes u i e) p :=
  evaluator_of_rows nodes hNodes u hu i hi B x k (tables_shifted nodes hNodes u hu i hi B x k) e E p hp

/-- Prefix seeds are removed: these are finite observations of the actual
first-order grammars on the same original character strings. -/
theorem observations_iff (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B e : MExp) (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar nodes u i B) .callByValuePar (render false nodes u i e) x rest ↔
      SObs (seqGrammar nodes u i B) .callByValueSeq (render true nodes u i e) x rest := by
  have hb := component_valid nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1
  rw [SeededClock.observations_iff hb (par_installed nodes u i B) (par_firstOrder nodes u i B)
      x .callByValuePar (by decide) _ (render_firstOrder false nodes u i e) rest,
    SeededClock.observations_iff hb (seq_installed nodes u i B) (seq_firstOrder nodes u i B)
      x .callByValueSeq (by decide) _ (render_firstOrder true nodes u i e) rest]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu i hi B x k e [] x.length (Nat.le_refl _)).symm.trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu i hi B x k e [] x.length (Nat.le_refl _)).trans hv,hr⟩

theorem language_translation (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (i : Nat) (hi : i<nodes.length) (B e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (parGrammar nodes u i B) .callByValuePar (render false nodes u i e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar nodes u i B,render true nodes u i e,seq_firstOrder nodes u i B,
    render_firstOrder true nodes u i e,fun x => observations_iff nodes hNodes u hu i hi B e x (some [])⟩

/-- The parent captures ababa, the child captures aba, and the parent then
uses its original ababa again after the child's return. -/
theorem recursive_capture_execution :
    let nodes : List Node := [.alt 1 2,.seq 3 4,.lit "aba".toList,.lit "ababa".toList,.notP 5,.lit ['#']]
    let u := "ab".toList
    let B := MExp.seq (.lit ['#']) (.seq (.param 0)
      (.alt (.seq (.lit ['!']) (.seq (.call 0 []) (.seq (.lit ['?']) (.param 0)))) .eps))
    let gp := parGrammar nodes u 0 B
    let gs := seqGrammar nodes u 0 B
    let e := MExp.seq (.call 0 []) (.notP .any)
    let x := "abababa#ababa!ababa#aba?ababa".toList
    let child := "ababa#aba?ababa".toList.length
    let bad := "abababa#ababa!ababa#aba?aba".toList
    evV gp x .callByValuePar (tblV gp x .callByValuePar 18) [] (.call 0 []) x.length=some (some (x.length-5)) ∧
    evV gp x .callByValuePar (tblV gp x .callByValuePar 18) [] (.call 0 []) child=some (some (child-3)) ∧
    evV gp x .callByValuePar (tblV gp x .callByValuePar 18) [] (render false nodes u 0 e) x.length=some (some 0) ∧
      evV gs x .callByValueSeq (tblV gs x .callByValueSeq 18) [] (render true nodes u 0 e) x.length=some (some 0) ∧
    evV gp bad .callByValuePar (tblV gp bad .callByValuePar 18) [] (render false nodes u 0 e) bad.length=some none ∧
    evV gs bad .callByValueSeq (tblV gs bad .callByValueSeq 18) [] (render true nodes u 0 e) bad.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.RecursiveFilteredOverlap
