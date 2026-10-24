import MacroPeg.CBV.RecursiveArgumentCompiler
import MacroPeg.CBV.ControlFilter

/-! Simultaneous plain/product correspondence for explicit recursive arguments. -/
namespace Shallot.MacroPeg.CBV.RecursiveArgumentCorrespondence
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)
open RecursiveArgumentCompiler
abbrev Arg := RecursiveArgumentCompiler.Expr

/-- All incoming physical prefixes, independently of capture stage. -/
def Rows (nodes : List Node) (users : List User) (x : List Char) (k : Nat) : Prop :=
  ∀ i r, users[i]?=some r → ∀ w p j, p≤x.length → j≤x.length → sfx x p=w++sfx x j →
    (valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [w]) p =
      valAt (seqTable nodes users x k (address nodes users i (profile (machine users) w) none) [w]) j) ∧
    (∀ q t, q<(machine users).width → t<(machine users).width →
      valAt (seqTable nodes users x k (address nodes users i (profile (machine users) w) (some (q,t))) [w]) j =
        filtered (machine users) x q t p
          (valAt (parTable nodes users x k ((grammar nodes (machine users)).rules.length+i) [w]) p))

/-- Selection checks the actual recursively translated argument and its
actual product expressions, before passing its unchanged capture to a row. -/
theorem selected_call (nodes : List Node) (users : List User) (x : List Char) (k : Nat)
    (i : Nat) (r : User) (hi : users[i]?=some r) (a : Arg) (S : List (List Nat)) (E : List (List Char))
    (p : Nat) (m : Mode) (hm : m∈modes (machine users))
    (hplain : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p =
      evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p)
    (hfilter : ∀ q t, q<(machine users).width → t<(machine users).width →
      evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (filter nodes users S a q t) p =
        filtered (machine users) x q t p
          (evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p)) :
    evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E
        (ProfileControl.select (machine users) (plain nodes users S a) (fun q t => filter nodes users S a q t)
          (fun P => .call (address nodes users i P m) [plain nodes users S a])) p =
      match evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
      | some (some j) => valAt (seqTable nodes users x k (address nodes users i (profile (machine users) (pre x p j)) m) [pre x p j]) j
      | other => other := by
  have hD := CaptureMachineFamily.valid (shifts users)
  rw [ProfileControl.select_correct (machine users) hD _ x .callByValueSeq _ E _ _ p hfilter,hplain]
  cases hv : evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      rw [evV_call_seq (target_rule nodes users i r hi _ (CaptureTransitionProfile.profile_mem (machine users) hD _) m hm) rfl]
      simp only [evSeqArgs,hplain,hv]

/-- The user-call case consumes its argument recursively at the same stage;
row correspondence handles the already captured value at either entry. -/
theorem user_correct (nodes : List Node) (users : List User) (x : List Char) (k : Nat)
    (hRows : Rows nodes users x k) (i : Nat) (r : User) (hi : users[i]?=some r)
    (a : Arg) (S : List (List Nat)) (E : List (List Char)) (p : Nat) (hp : p≤x.length)
    (hplain : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p =
      evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p)
    (hfilter : ∀ q t, q<(machine users).width → t<(machine users).width →
      evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (filter nodes users S a q t) p =
        filtered (machine users) x q t p
          (evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p)) :
    (evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S (.user i a)) p =
      evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.user i a)) p) ∧
    (∀ q t, q<(machine users).width → t<(machine users).width →
      evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (filter nodes users S (.user i a) q t) p =
        filtered (machine users) x q t p
          (evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.user i a)) p)) := by
  have hib := (List.getElem?_eq_some_iff.mp hi).1
  have harg := WordStarFilter.success_prefix (g := parGrammar nodes users) (x := x)
    (by decide) (SeededClock.rounds_sound (par_firstOrder nodes users) (helpers nodes users) x .callByValuePar (by decide) k)
    E (parRender nodes users a) (parRender_firstOrder nodes users a) p
  constructor
  · simp only [plain,parRender,if_pos hib]
    rw [selected_call nodes users x k i r hi a S E p none (mode_plain_mem _) hplain hfilter,
      evV_call_par (source_rule nodes users i r hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        exact (hRows i r hi _ p j hp hj hcap).1.symm
  · intro q t hq ht
    simp only [filter,parRender,if_pos hib]
    rw [selected_call nodes users x k i r hi a S E p (some (q,t)) (mode_filter_mem _ q t hq ht) hplain hfilter,
      evV_call_par (source_rule nodes users i r hi) rfl (by decide)]
    simp only [evParArgs]
    cases hv : evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some j =>
        obtain ⟨hj,hcap⟩ := harg j hp hv
        exact (hRows i r hi _ p j hp hj hcap).2 q t hq ht

/-- Structural argument nesting and recursive row queries are handled by
separate inductions. The row premise is discharged by the round induction. -/
theorem evaluator_of_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (x : List Char) (k : Nat) (hRows : Rows nodes users x k) :
    ∀ e, Valid nodes users e → ∀ S E, DependentCaptureFilter.Accurate (machine users) S E →
    ∀ p, p≤x.length →
    (evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S e) p =
      evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users e) p) ∧
    (∀ q t, q<(machine users).width → t<(machine users).width →
      evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (filter nodes users S e q t) p =
        filtered (machine users) x q t p
          (evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users e) p))
  | .lit w, _, S, E, hS, p, hp => by
    refine ⟨rfl,?_⟩
    intro q t hq ht
    exact ParametricHelperControl.filter_correct nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users))
      (sourceRules nodes users) (targetRules nodes users) x k k S E hS (.lit w) True.intro p hp q t hq ht
  | .param i, _, S, E, hS, p, hp => by
    refine ⟨rfl,?_⟩
    intro q t hq ht
    exact ParametricHelperControl.filter_correct nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users))
      (sourceRules nodes users) (targetRules nodes users) x k k S E hS (.param i) True.intro p hp q t hq ht
  | .helper i, hi, S, E, hS, p, hp => by
    constructor
    · exact (ParametricHelperControl.rounds_base nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users)).1
        (targetRules nodes users) x .callByValueSeq k E _ (ParametricHelperControl.render_safe nodes (machine users) (.helper i) hi) p hp).trans
        (ParametricHelperControl.rounds_base nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users)).1
        (sourceRules nodes users) x .callByValuePar k E _ (ParametricHelperControl.render_safe nodes (machine users) (.helper i) hi) p hp).symm
    · intro q t hq ht
      exact ParametricHelperControl.filter_correct nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users))
        (sourceRules nodes users) (targetRules nodes users) x k k S E hS (.helper i) hi p hp q t hq ht
  | .user i a, ha, S, E, hS, p, hp => by
    have hib : i<users.length := ha.1
    have hr : users[i]?=some users[i] := List.getElem?_eq_getElem hib
    have ih := evaluator_of_rows nodes hNodes users x k hRows a ha.2 S E hS p hp
    apply user_correct nodes users x k hRows i users[i] hr a S E p hp ih.1
    intro q t hq ht
    rw [ih.1]
    exact ih.2 q t hq ht
  | .seq a b, ha, S, E, hS, p, hp => by
    have hA := evaluator_of_rows nodes hNodes users x k hRows a ha.1 S E hS p hp
    have he : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S (.seq a b)) p =
        evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.seq a b)) p := by
      change (match evV _ _ _ _ E (plain nodes users S a) p with
        | some (some z) => evV _ _ _ _ E (plain nodes users S b) z | other => other)=
        (match evV _ _ _ _ E (parRender nodes users a) p with
        | some (some z) => evV _ _ _ _ E (parRender nodes users b) z | other => other)
      rw [hA.1]
      cases hv : evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
      | none => rfl
      | some result => cases result with
        | none => rfl
        | some z =>
          exact (evaluator_of_rows nodes hNodes users x k hRows b ha.2 S E hS z
            (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp z hv)).1
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact ControlFilter.seq_correct (machine users) (CaptureMachineFamily.valid (shifts users)) _ x .callByValueSeq (by decide) _
      (SeededClock.rounds_sound (seq_firstOrder nodes users) (helpers nodes users) x .callByValueSeq (by decide) k)
      E (plain nodes users S a) (plain nodes users S b) (plain_firstOrder nodes users S a) (plain_firstOrder nodes users S b)
      _ _ p hp (by intro q t hq ht; rw [hA.1]; exact hA.2 q t hq ht)
      (by
        intro z hz q t hq ht
        have hB := evaluator_of_rows nodes hNodes users x k hRows b ha.2 S E hS z hz
        rw [hB.1]
        exact hB.2 q t hq ht) q t hq ht
  | .alt a b, ha, S, E, hS, p, hp => by
    have hA := evaluator_of_rows nodes hNodes users x k hRows a ha.1 S E hS p hp
    have hB := evaluator_of_rows nodes hNodes users x k hRows b ha.2 S E hS p hp
    have he : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S (.alt a b)) p =
        evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.alt a b)) p := by
      change (match evV _ _ _ _ E (plain nodes users S a) p with
        | some none => evV _ _ _ _ E (plain nodes users S b) p | other => other)=
        (match evV _ _ _ _ E (parRender nodes users a) p with
        | some none => evV _ _ _ _ E (parRender nodes users b) p | other => other)
      rw [hA.1]
      cases hv : evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users a) p with
      | none => rfl
      | some result => cases result with
        | none => exact hB.1
        | some z => rfl
    refine ⟨he,?_⟩
    intro q t hq ht
    change evV _ _ _ _ E (RootObservation.branch (.andP (plain nodes users S a)) _ _) p=_
    rw [ChoiceArguments.branch_eval]
    cases hv : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p with
    | none =>
      have hs := hA.1.symm.trans hv
      rw [show parRender nodes users (.alt a b)=.alt (parRender nodes users a) (parRender nodes users b) from rfl,
        evV_alt_none hs]
      rfl
    | some result => cases result with
      | none =>
        have hs := hA.1.symm.trans hv
        rw [show parRender nodes users (.alt a b)=.alt (parRender nodes users a) (parRender nodes users b) from rfl,
          evV_alt_fail hs]
        exact hB.2 q t hq ht
      | some z =>
        have hs := hA.1.symm.trans hv
        rw [show parRender nodes users (.alt a b)=.alt (parRender nodes users a) (parRender nodes users b) from rfl,
          evV_alt_ok hs]
        simpa only [hs] using hA.2 q t hq ht
  | .star a, ha, S, E, hS, p, hp => by
    have he : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S (.star a)) p =
        evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.star a)) p :=
      evStar_congr p (fun z hz => (evaluator_of_rows nodes hNodes users x k hRows a ha S E hS z (by omega)).1)
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    exact GeneralStarFilter.correct (machine users) (CaptureMachineFamily.valid (shifts users)) _ x .callByValueSeq (by decide) _
      (SeededClock.rounds_sound (seq_firstOrder nodes users) (helpers nodes users) x .callByValueSeq (by decide) k)
      E _ (plain_firstOrder nodes users S a) _
      (by
        intro q t z hq ht hz
        have hA := evaluator_of_rows nodes hNodes users x k hRows a ha S E hS z hz
        rw [hA.1]
        exact hA.2 q t hq ht) q t p hq hp
  | .notP a, ha, S, E, hS, p, hp => by
    have hA := evaluator_of_rows nodes hNodes users x k hRows a ha S E hS p hp
    have he : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S (.notP a)) p =
        evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users (.notP a)) p := by
      simp only [plain,parRender,evV,hA.1]
    refine ⟨he,?_⟩
    intro q t hq ht
    rw [←he]
    apply DependentCaptureFilter.atom_correct (state := some q)
    intro j hv
    cases hz : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S a) p with
    | none => simp [evV,hz] at hv
    | some result => cases result with
      | some z => simp [evV,hz] at hv
      | none =>
        have hj : p=j := by simpa only [plain,evV,hz,Option.some.injEq] using hv
        subst j
        simp [pre,run]

theorem tailPrefix_actual (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r) (hu : r.shift≠[]) (w : List Char) :
    tailPrefix users i (profile (machine users) w) r =
      ProfiledDependentRecursion.tailPrefix r.shift (profile (PeriodicCaptureMachine.machine r.shift) w) := by
  have hi : (shifts users)[i]?=some r.shift := by simp [shifts,hr]
  simp only [tailPrefix,if_neg hu,phase,CaptureMachineFamily.phase_profile (shifts users) i r.shift hi w,
    ProfiledDependentRecursion.tailPrefix,CaptureTransitionProfile.profile_get _ _ 0 (CaptureMachineFamily.phase_valid r.shift).1,
    Option.getD_some]

theorem prefix_eq (g h : MGrammar) (x : List Char) (T U : ClockFreezing.Table)
    (users : List User) (i : Nat) (r : User) (hr : users[i]?=some r)
    (w : List Char) (p j : Nat) (hp : p≤x.length) (hj : j≤x.length)
    (hcap : sfx x p=w++sfx x j) :
    evV g x .callByValuePar T [w] (.seq (.lit r.shift) (.param 0)) p =
      evV h x .callByValueSeq U [w] (tailPrefix users i (profile (machine users) w) r) j := by
  by_cases hu : r.shift=[]
  · have hl : evV g x .callByValuePar T [w] (.lit r.shift) p=some (some p) := by
      simp only [hu,evV,(CBVtoCBN.stripPrefix_exact [] (sfx x p) (sfx x p)).mpr (by simp),length_sfx x hp]
    rw [evV_seq_ok hl]
    simp only [tailPrefix,if_pos hu,evV,List.getElem?_cons_zero,
      (CBVtoCBN.stripPrefix_exact _ _ _).mpr hcap,
      (CBVtoCBN.stripPrefix_exact [] (sfx x j) (sfx x j)).mpr (by simp),length_sfx x hj]
  ·
    let empty : MGrammar := ⟨[]⟩
    let V : ClockFreezing.Table := fun _ _ => []
    have hs : SoundTV empty x .callByValuePar V := by
      intro n rule W hn
      cases n <;> cases hn
    have hv : evV empty x .callByValuePar V [] (.lit w) p=some (some j) := by
      simp only [evV,(CBVtoCBN.stripPrefix_exact _ _ _).mpr hcap,length_sfx x hj]
    have he := ProfiledDependentRecursion.prefix_eq empty h x V V U hs [] (.lit w)
      True.intro r.shift hu p j hp hv
    rw [CapturePrefixRows.captured_word x w p j hp hj hcap] at he
    rw [tailPrefix_actual users i r hr hu]
    exact (SeededClock.word_eval_eq g empty x .callByValuePar .callByValuePar T V [w]
      (.seq (.lit r.shift) (.param 0)) ⟨True.intro,True.intro⟩ p).trans he

theorem tail_success (g : MGrammar) (x : List Char) (s : Strategy) (T : ClockFreezing.Table)
    (users : List User) (i : Nat) (P : List Nat) (r : User) (E : List (List Char)) (j z : Nat)
    (hj : j≤x.length) (hv : evV g x s T E (tailPrefix users i P r) j=some (some z)) :
    z≤x.length ∧ sfx x j=PeriodicCaptureMachine.phase r.shift (phase users i P)++sfx x z := by
  have hl : tailPrefix users i P r=.lit (PeriodicCaptureMachine.phase r.shift (phase users i P)) := by
    by_cases he : r.shift=[]
    · simp [tailPrefix,he,PeriodicCaptureMachine.phase]
    · simp only [tailPrefix,if_neg he] at hv ⊢
      split at hv
      · rename_i hphase
        rw [if_pos hphase]
      · simp [MExp.failAlways,evV] at hv
  rw [hl] at hv
  have hz := SequenceArguments.success_prefix g x s T E (.lit (PeriodicCaptureMachine.phase r.shift (phase users i P))) True.intro j z hj hv
  have hw := WordArguments.value_of_success g x s T E (.lit (PeriodicCaptureMachine.phase r.shift (phase users i P))) True.intro j z hj hv
  have he : PeriodicCaptureMachine.phase r.shift (phase users i P)=pre x j z := by
    simpa only [WordArguments.value,Option.some.injEq] using hw
  exact ⟨hz.1,he ▸ hz.2⟩

def modeResult (D : Machine) (x : List Char) (p : Nat) (m : Mode) (R : Res) : Res :=
  match m with | none => R | some (q,t) => filtered D x q t p R

theorem row_zero (nodes : List Node) (users : List User) (x : List Char)
    (i : Nat) (r : User) (hr : users[i]?=some r)
    (w : List Char) (p j : Nat) (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (m : Mode) (hm : m∈modes (machine users)) :
    valAt (seqTable nodes users x 0 (address nodes users i (profile (machine users) w) m) [w]) j =
      modeResult (machine users) x p m
        (valAt (parTable nodes users x 0 ((grammar nodes (machine users)).rules.length+i) [w]) p) := by
  have hD := CaptureMachineFamily.valid (shifts users)
  have huser : RecursiveParserStability.pick (helpers nodes users) ((grammar nodes (machine users)).rules.length+i)=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser : RecursiveParserStability.pick (helpers nodes users) (address nodes users i (profile (machine users) w) m)=false := by
    simp [RecursiveParserStability.pick,helpers,component,address]
  have hrot := prefix_eq (parGrammar nodes users) (seqGrammar nodes users) x
    (ClockFreezing.frozen (parGrammar nodes users) x .callByValuePar (RecursiveParserStability.pick (helpers nodes users)) (RecursiveParserStability.floor (helpers nodes users) x) 0)
    (ClockFreezing.frozen (seqGrammar nodes users) x .callByValueSeq (RecursiveParserStability.pick (helpers nodes users)) (RecursiveParserStability.floor (helpers nodes users) x) 0)
    users i r hr w p j hp hj hcap
  change valAt (SeededClock.prefixSeed _ x .callByValueSeq _ _ _ [w]) j =
    modeResult _ _ _ _ (valAt (SeededClock.prefixSeed _ x .callByValuePar _ _ _ [w]) p)
  rw [SeededClock.prefixSeed_query _ x .callByValuePar _ _ _ huser 1 _ _ (source_rule nodes users i r hr) _ p hp,
    SeededClock.prefixSeed_query _ x .callByValueSeq _ _ _ htuser 1 _ _
      (target_rule nodes users i r hr _ (CaptureTransitionProfile.profile_mem (machine users) hD w) m hm) _ j hj,hrot]
  cases m with
  | none => rfl
  | some pair =>
    dsimp only [modeResult]
    split <;> rfl

theorem row_step (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (x : List Char) (k : Nat)
    (ih : Rows nodes users x k) (i : Nat) (r : User) (hr : users[i]?=some r)
    (w : List Char) (p j : Nat) (hp : p≤x.length) (hj : j≤x.length) (hcap : sfx x p=w++sfx x j)
    (m : Mode) (hm : m∈modes (machine users)) :
    valAt (seqTable nodes users x (k+1) (address nodes users i (profile (machine users) w) m) [w]) j =
      modeResult (machine users) x p m
        (valAt (parTable nodes users x (k+1) ((grammar nodes (machine users)).rules.length+i) [w]) p) := by
  have hD := CaptureMachineFamily.valid (shifts users)
  have hvalid := hUsers r (List.mem_of_getElem? hr)
  have huser : RecursiveParserStability.pick (helpers nodes users) ((grammar nodes (machine users)).rules.length+i)=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser : RecursiveParserStability.pick (helpers nodes users) (address nodes users i (profile (machine users) w) m)=false := by
    simp [RecursiveParserStability.pick,helpers,component,address]
  have hrot := prefix_eq (parGrammar nodes users) (seqGrammar nodes users) x
    (parTable nodes users x k) (seqTable nodes users x k) users i r hr w p j hp hj hcap
  rw [SeededClock.user_step _ x .callByValuePar _ _ _ k _ huser _ (source_rule nodes users i r hr) _ p hp,
    SeededClock.user_step _ x .callByValueSeq _ _ _ k _ htuser _
      (target_rule nodes users i r hr _ (CaptureTransitionProfile.profile_mem (machine users) hD w) m hm) _ j hj]
  change (match evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) [w]
      (tailPrefix users i (profile (machine users) w) r) j with
    | some (some z) => evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) [w] ((fun mode : Mode => match mode with
        | none => plain nodes users [profile (machine users) w] r.body
        | some (q,t) => filter nodes users [profile (machine users) w] r.body
            (run (machine users) ((profile (machine users) w)[q]?.getD 0)
              (PeriodicCaptureMachine.phase r.shift (phase users i (profile (machine users) w)))) t) m) z
    | other => other)=modeResult _ _ _ _
      (match evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) [w] (.seq (.lit r.shift) (.param 0)) p with
      | some (some z) => evV _ _ _ _ [w] (parRender nodes users r.body) z | other => other)
  rw [hrot]
  cases hv : evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) [w]
      (tailPrefix users i (profile (machine users) w) r) j with
  | none => cases m <;> rfl
  | some result => cases result with
    | none => cases m <;> rfl
    | some z =>
      have hzcap := tail_success (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k)
        users i (profile (machine users) w) r [w] j z hj hv
      have hbody := evaluator_of_rows nodes hNodes users x k ih r.body hvalid
        [profile (machine users) w] [w] (DependentCaptureFilter.environment_accurate (machine users) [w]) z hzcap.1
      cases m with
      | none => exact hbody.1
      | some pair =>
        obtain ⟨q,t⟩ := pair
        have hqt : q<(machine users).width ∧ t<(machine users).width := by simpa [modes] using hm
        have hstart := run_bound hD (run (machine users) q w) (run_bound hD q hqt.1 w)
          (PeriodicCaptureMachine.phase r.shift (phase users i (profile (machine users) w)))
        simp only [CaptureTransitionProfile.profile_get (machine users) w q hqt.1,Option.getD_some] at *
        rw [hbody.2 _ t hstart hqt.2]
        have hwhole : sfx x p=(w++PeriodicCaptureMachine.phase r.shift (phase users i (profile (machine users) w)))++sfx x z := by
          rw [hcap,hzcap.2,List.append_assoc]
        have hfilter := CapturePrefixRows.filter_prefix (machine users) x
          (w++PeriodicCaptureMachine.phase r.shift (phase users i (profile (machine users) w))) p z q t hp hzcap.1 hwhole
          (evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) [w] (parRender nodes users r.body) z)
          (fun endpos he => WordStarFilter.success_prefix (by decide)
            (SeededClock.rounds_sound (par_firstOrder nodes users) (helpers nodes users) x .callByValuePar (by decide) k)
            [w] (parRender nodes users r.body) (parRender_firstOrder nodes users r.body) z endpos hzcap.1 he)
        exact (by simpa only [modeResult,run_append] using hfilter.symm)

/-- Real installed plain and product rows satisfy the simultaneous invariant
at every seeded stage. There is no supplied semantic row oracle. -/
theorem tables_rows (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (x : List Char) :
    ∀ k, Rows nodes users x k := by
  intro k
  induction k with
  | zero =>
    intro i r hr w p j hp hj hcap
    constructor
    · exact (row_zero nodes users x i r hr w p j hp hj hcap none (mode_plain_mem _)).symm
    · intro q t hq ht
      exact row_zero nodes users x i r hr w p j hp hj hcap _ (mode_filter_mem _ q t hq ht)
  | succ k ih =>
    intro i r hr w p j hp hj hcap
    constructor
    · exact (row_step nodes hNodes users hUsers x k ih i r hr w p j hp hj hcap none (mode_plain_mem _)).symm
    · intro q t hq ht
      exact row_step nodes hNodes users hUsers x k ih i r hr w p j hp hj hcap _ (mode_filter_mem _ q t hq ht)

theorem evaluator_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (x : List Char) (k : Nat)
    (e : Arg) (he : Valid nodes users e) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (machine users) S E) (p : Nat) (hp : p≤x.length) :
    evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (plain nodes users S e) p =
      evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users e) p :=
  (evaluator_of_rows nodes hNodes users x k (tables_rows nodes hNodes users hUsers x k) e he S E hS p hp).1

theorem filter_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (x : List Char) (k : Nat)
    (e : Arg) (he : Valid nodes users e) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (machine users) S E) (p : Nat) (hp : p≤x.length)
    (q t : Nat) (hq : q<(machine users).width) (ht : t<(machine users).width) :
    evV (seqGrammar nodes users) x .callByValueSeq (seqTable nodes users x k) E (filter nodes users S e q t) p =
      filtered (machine users) x q t p
        (evV (parGrammar nodes users) x .callByValuePar (parTable nodes users x k) E (parRender nodes users e) p) :=
  (evaluator_of_rows nodes hNodes users x k (tables_rows nodes hNodes users hUsers x k) e he S E hS p hp).2 q t hq ht

/-- Removing the seeded stages gives full finite observations on the same
original strings, including arguments that themselves call recursive users. -/
theorem observations_iff (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (e : Arg) (he : Valid nodes users e)
    (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar nodes users) .callByValuePar (parRender nodes users e) x rest ↔
      SObs (seqGrammar nodes users) .callByValueSeq (plain nodes users [] e) x rest := by
  have hb := component_valid nodes hNodes (machine users) (CaptureMachineFamily.valid (shifts users)).1
  rw [SeededClock.observations_iff hb (par_installed nodes users) (par_firstOrder nodes users)
      x .callByValuePar (by decide) _ (parRender_firstOrder nodes users e) rest,
    SeededClock.observations_iff hb (seq_installed nodes users) (seq_firstOrder nodes users)
      x .callByValueSeq (by decide) _ (plain_firstOrder nodes users [] e) rest]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes users hUsers x k e he [] [] (DependentCaptureFilter.environment_accurate (machine users) []) x.length (Nat.le_refl _)).trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes users hUsers x k e he [] [] (DependentCaptureFilter.environment_accurate (machine users) []) x.length (Nat.le_refl _)).symm.trans hv,hr⟩

theorem language_translation (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (users : List User) (hUsers : UsersValid nodes users) (e : Arg) (he : Valid nodes users e) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (parGrammar nodes users) .callByValuePar (parRender nodes users e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar nodes users,plain nodes users [] e,seq_firstOrder nodes users,
    plain_firstOrder nodes users [] e,fun x => observations_iff nodes hNodes users hUsers e he x (some [])⟩

end Shallot.MacroPeg.CBV.RecursiveArgumentCorrespondence
