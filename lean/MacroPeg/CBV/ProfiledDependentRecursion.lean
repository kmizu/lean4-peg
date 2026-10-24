import MacroPeg.CBV.DependentProfileCall
import MacroPeg.CBV.RecursiveFilteredOverlap

/-! Recursive fresh arguments may depend on the retained capture. Finite
transition profiles specialize the target user rows without losing the value. -/
namespace Shallot.MacroPeg.CBV.ProfiledDependentRecursion
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)
open PeriodicCaptureMachine (machine phase)
open ClockFreezing (Table)
abbrev Arg := DependentCaptureFilter.Expr

/-- Raw call zero captures A in the current retained environment; other
zero-argument calls address the independent helper component. -/
def parRender (nodes : List Node) (u : List Char) (A : Arg) : MExp → MExp
  | .call 0 [] => .call (grammar nodes (machine u)).rules.length [DependentCaptureFilter.render A]
  | .call (j+1) [] => if j<(grammar nodes (machine u)).rules.length then .call j [] else MExp.failAlways
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (parRender nodes u A a) (parRender nodes u A b)
  | .alt a b => .alt (parRender nodes u A a) (parRender nodes u A b)
  | .star a => .star (parRender nodes u A a)
  | .notP a => .notP (parRender nodes u A a)
  | .eps => .eps | .any => .any | .chr c => .chr c | .range lo hi => .range lo hi
  | .lit w => .lit w | .param k => .param k
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def seqRender (nodes : List Node) (u : List Char) (A : Arg) (S : List (List Nat)) : MExp → MExp
  | .call 0 [] => DependentProfileCall.entry nodes (machine u) S A
  | .call (j+1) [] => if j<(grammar nodes (machine u)).rules.length then .call j [] else MExp.failAlways
  | .call _ (_::_) => MExp.failAlways
  | .seq a b => .seq (seqRender nodes u A S a) (seqRender nodes u A S b)
  | .alt a b => .alt (seqRender nodes u A S a) (seqRender nodes u A S b)
  | .star a => .star (seqRender nodes u A S a)
  | .notP a => .notP (seqRender nodes u A S a)
  | .eps => .eps | .any => .any | .chr c => .chr c | .range lo hi => .range lo hi
  | .lit w => .lit w | .param k => .param k
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => MExp.failAlways

def tailPrefix (u : List Char) (P : List Nat) : MExp :=
  if P[0]?.getD 0<u.length then .lit (phase u (P[0]?.getD 0)) else MExp.failAlways

def targetBody (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) (P : List Nat) : MExp :=
  .seq (tailPrefix u P) (seqRender nodes u A [P] B)

abbrev parGrammar (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :=
  FilteredOverlapCaller.source nodes u (parRender nodes u A B)
abbrev seqGrammar (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :=
  DependentProfileCall.specialized nodes (machine u) (targetBody nodes u A B)
abbrev helpers (nodes : List Node) (u : List Char) := component nodes (machine u)
abbrev parTable (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (parGrammar nodes u A B) x .callByValuePar k
abbrev seqTable (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) (x : List Char) (k : Nat) :=
  SeededClock.rounds (helpers nodes u) (seqGrammar nodes u A B) x .callByValueSeq k

theorem parRender_firstOrder (nodes : List Node) (u : List Char) (A : Arg) : ∀ e, (parRender nodes u A e).FirstOrder
  | .call 0 [] => ⟨DependentCaptureFilter.render_firstOrder A,True.intro⟩
  | .call (j+1) [] => by simp only [parRender]; split <;> trivial
  | .call j (_::_) => by cases j <;> trivial
  | .seq a b | .alt a b => ⟨parRender_firstOrder nodes u A a,parRender_firstOrder nodes u A b⟩
  | .star a | .notP a => parRender_firstOrder nodes u A a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True.intro
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => True.intro

theorem seqRender_firstOrder (nodes : List Node) (u : List Char) (A : Arg) (S : List (List Nat)) :
    ∀ e, (seqRender nodes u A S e).FirstOrder
  | .call 0 [] => DependentProfileCall.entry_firstOrder nodes (machine u) S A
  | .call (j+1) [] => by simp only [seqRender]; split <;> trivial
  | .call j (_::_) => by cases j <;> trivial
  | .seq a b | .alt a b => ⟨seqRender_firstOrder nodes u A S a,seqRender_firstOrder nodes u A S b⟩
  | .star a | .notP a => seqRender_firstOrder nodes u A S a
  | .eps | .any | .chr _ | .range _ _ | .lit _ | .param _ => True.intro
  | .dbg _ | .lam _ _ | .callParam _ _ | .invoke _ _ _ => True.intro

theorem par_firstOrder (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :
    (parGrammar nodes u A B).FirstOrder := FilteredOverlapCaller.source_firstOrder _ _ _ (parRender_firstOrder _ _ _ B)
theorem seq_firstOrder (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :
    (seqGrammar nodes u A B).FirstOrder := by
  apply DependentProfileCall.specialized_firstOrder
  intro P _
  refine ⟨?_,seqRender_firstOrder _ _ _ _ B⟩
  unfold tailPrefix
  split <;> trivial

theorem par_installed (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :
    RecursiveParserStability.Installed (helpers nodes u) (parGrammar nodes u A B) := component_installed _ _ _
theorem seq_installed (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) :
    RecursiveParserStability.Installed (helpers nodes u) (seqGrammar nodes u A B) := component_installed _ _ _

def Shifted (nodes : List Node) (u : List Char) (A : Arg) (B : MExp) (x : List Char) (k : Nat) : Prop :=
  ∀ E p j, p≤x.length → j≤x.length →
    evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (DependentCaptureFilter.render A) p=some (some j) →
      valAt (parTable nodes u A B x k (grammar nodes (machine u)).rules.length [pre x p j]) p =
        valAt (seqTable nodes u A B x k (DependentProfileCall.address nodes (machine u) (profile (machine u) (pre x p j))) [pre x p j]) j

/-- Both continuation tables are genuine user stages; profile selection
hands them exactly the original source argument value and endpoint. -/
theorem entry_eq (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B : MExp) (x : List Char) (k : Nat)
    (hRows : Shifted nodes u A B x k) (S : List (List Nat)) (E : List (List Char))
    (hS : DependentCaptureFilter.Accurate (machine u) S E) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (parRender nodes u A (.call 0 [])) p =
      evV (seqGrammar nodes u A B) x .callByValueSeq (seqTable nodes u A B x k) E (seqRender nodes u A S (.call 0 [])) p := by
  have hd := PeriodicCaptureMachine.valid u hu
  have ht := DependentProfileCall.entry_par_correct nodes hNodes (machine u) hd
    (FilteredOverlapCaller.sourceRules u (parRender nodes u A B)) (targetBody nodes u A B) x k k S E hS A ha p hp
  change evV (seqGrammar nodes u A B) x .callByValueSeq (seqTable nodes u A B x k) E
      (DependentProfileCall.entry nodes (machine u) S A) p =
    (match evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (DependentCaptureFilter.render A) p with
    | some (some j) => valAt (seqTable nodes u A B x k (DependentProfileCall.address nodes (machine u) (profile (machine u) (pre x p j))) [pre x p j]) j
    | other => other) at ht
  change evV _ _ _ _ E (.call _ [DependentCaptureFilter.render A]) p=evV _ _ _ _ E (DependentProfileCall.entry nodes (machine u) S A) p
  rw [ht,evV_call_par (FilteredOverlapCaller.source_rule nodes u (parRender nodes u A B)) rfl (by decide)]
  simp only [evParArgs]
  cases hv : evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (DependentCaptureFilter.render A) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      exact hRows E p j hp (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp j hv) hv

theorem evaluator_of_rows (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B : MExp) (x : List Char) (k : Nat)
    (hRows : Shifted nodes u A B x k) :
    ∀ e S E, DependentCaptureFilter.Accurate (machine u) S E → ∀ p, p≤x.length →
      evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (parRender nodes u A e) p =
        evV (seqGrammar nodes u A B) x .callByValueSeq (seqTable nodes u A B x k) E (seqRender nodes u A S e) p
  | .call 0 [], S, E, hS, p, hp => entry_eq nodes hNodes u hu A ha B x k hRows S E hS p hp
  | .call (j+1) [], S, E, hS, p, hp => by
    simp only [parRender,seqRender]
    split
    · rename_i hj
      exact (RecursiveFilteredOverlap.query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1 _ x .callByValuePar k j p hj hp E).trans
        (RecursiveFilteredOverlap.query_eq nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1 _ x .callByValueSeq k j p hj hp E).symm
    · rfl
  | .call j (_::_), _, _, _, _, _ => by cases j <;> rfl
  | .seq a b, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu A ha B x k hRows a S E hS p hp
    simp only [parRender,seqRender]
    cases hv : evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (parRender nodes u A a) p with
    | none => rw [evV_seq_none hv,evV_seq_none (heq.symm.trans hv)]
    | some result => cases result with
      | none => rw [evV_seq_fail hv,evV_seq_fail (heq.symm.trans hv)]
      | some z =>
        rw [evV_seq_ok hv,evV_seq_ok (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu A ha B x k hRows b S E hS z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ p hp z hv)
  | .alt a b, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu A ha B x k hRows a S E hS p hp
    simp only [parRender,seqRender]
    cases hv : evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (parRender nodes u A a) p with
    | none => rw [evV_alt_none hv,evV_alt_none (heq.symm.trans hv)]
    | some result => cases result with
      | none =>
        rw [evV_alt_fail hv,evV_alt_fail (heq.symm.trans hv)]
        exact evaluator_of_rows nodes hNodes u hu A ha B x k hRows b S E hS p hp
      | some z => rw [evV_alt_ok hv,evV_alt_ok (heq.symm.trans hv)]
  | .star a, S, E, hS, p, hp => by
    simp only [parRender,seqRender,evV_star]
    exact evStar_congr p (fun z hz => evaluator_of_rows nodes hNodes u hu A ha B x k hRows a S E hS z (by omega))
  | .notP a, S, E, hS, p, hp => by
    have heq := evaluator_of_rows nodes hNodes u hu A ha B x k hRows a S E hS p hp
    change (match evV _ _ _ _ E (parRender nodes u A a) p with
      | some (some _) => some none | some none => some (some p) | none => none)=_
    rw [heq]
    rfl
  | .eps, _, _, _, _, _ | .any, _, _, _, _, _ | .chr _, _, _, _, _, _ | .range _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ | .param _, _, _, _, _, _ | .dbg _, _, _, _, _, _ | .lam _ _, _, _, _, _, _
  | .callParam _ _, _, _, _, _, _ | .invoke _ _ _, _, _, _, _, _ => rfl


theorem nonperiodic_replay_fail (g : MGrammar) (x : List Char) (T : Table)
    (hT : SoundTV g x .callByValuePar T) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (hu : u≠[]) (p j : Nat) (hp : p≤x.length)
    (hv : evV g x .callByValuePar T E a p=some (some j))
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
      obtain ⟨v,_,he⟩ := OverlapNecessity.actual_capture_rotation g x T hT E a ha u p j z hp hv hr
      exact False.elim (hsink (PeriodicCaptureMachine.prefix_run u (pre x p j) hu ⟨v,he.symm⟩))

theorem prefix_eq (g h : MGrammar) (x : List Char) (Tcap T U : Table)
    (hT : SoundTV g x .callByValuePar Tcap) (E : List (List Char)) (a : MExp) (ha : a.FirstOrder)
    (u : List Char) (hu : u≠[]) (p j : Nat) (hp : p≤x.length)
    (hv : evV g x .callByValuePar Tcap E a p=some (some j)) :
    evV g x .callByValuePar T [pre x p j] (.seq (.lit u) (.param 0)) p =
      evV h x .callByValueSeq U [pre x p j] (tailPrefix u (profile (machine u) (pre x p j))) j := by
  have hcap := DependentCaptureFilter.success_prefix (by decide) hT E a ha p j hp hv
  simp only [tailPrefix,CaptureTransitionProfile.profile_get (machine u) (pre x p j) 0
    (PeriodicCaptureMachine.valid u hu).1,Option.getD_some]
  split
  · rename_i hphase
    exact FilteredOverlapCaller.replay_rotation g h x T U u hu p j hp hcap.1 hcap.2 hphase
  · rename_i hsink
    have hf := nonperiodic_replay_fail g x Tcap hT E a ha u hu p j hp hv hsink
    exact (SeededClock.word_eval_eq g g x .callByValuePar .callByValuePar T Tcap [pre x p j]
      (.seq (.lit u) (.param 0)) ⟨True.intro,True.intro⟩ p).trans hf

/-- All transition profiles, including a sink profile, are threaded through
actual recursive user rows. -/
theorem tables_shifted (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B : MExp) (x : List Char) :
    ∀ k, Shifted nodes u A B x k := by
  have hD := PeriodicCaptureMachine.valid u hu
  have hpar := FilteredOverlapCaller.source_rule nodes u (parRender nodes u A B)
  have hseq (P : List Nat) (hP : P∈profiles (machine u)) :=
    DependentProfileCall.specialized_rule nodes (machine u) (targetBody nodes u A B) P hP
  have huser : RecursiveParserStability.pick (helpers nodes u) (grammar nodes (machine u)).rules.length=false := by
    simp [RecursiveParserStability.pick,helpers,component]
  have htuser (P : List Nat) : RecursiveParserStability.pick (helpers nodes u) (DependentProfileCall.address nodes (machine u) P)=false := by
    simp [RecursiveParserStability.pick,helpers,component,DependentProfileCall.address]
  intro k
  induction k with
  | zero =>
    intro E p j hp hj hv
    have hrot := prefix_eq (parGrammar nodes u A B) (seqGrammar nodes u A B) x
      (parTable nodes u A B x 0)
      (ClockFreezing.frozen (parGrammar nodes u A B) x .callByValuePar (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      (ClockFreezing.frozen (seqGrammar nodes u A B) x .callByValueSeq (RecursiveParserStability.pick (helpers nodes u)) (RecursiveParserStability.floor (helpers nodes u) x) 0)
      (SeededClock.rounds_sound (par_firstOrder nodes u A B) (helpers nodes u) x .callByValuePar (by decide) 0)
      E (DependentCaptureFilter.render A) (DependentCaptureFilter.render_firstOrder A) u hu p j hp hv
    change valAt (SeededClock.prefixSeed _ x .callByValuePar _ _ _ [pre x p j]) p =
      valAt (SeededClock.prefixSeed _ x .callByValueSeq _ _ _ [pre x p j]) j
    rw [SeededClock.prefixSeed_query _ x .callByValuePar _ _ _ huser 1 _ _ hpar _ p hp,
      SeededClock.prefixSeed_query _ x .callByValueSeq _ _ _ (htuser _) 1 _ _
        (hseq _ (CaptureTransitionProfile.profile_mem (machine u) hD _)) _ j hj,hrot]
  | succ k ih =>
    intro E p j hp hj hv
    have hrot := prefix_eq (parGrammar nodes u A B) (seqGrammar nodes u A B) x
      (parTable nodes u A B x (k+1)) (parTable nodes u A B x k) (seqTable nodes u A B x k)
      (SeededClock.rounds_sound (par_firstOrder nodes u A B) (helpers nodes u) x .callByValuePar (by decide) (k+1))
      E (DependentCaptureFilter.render A) (DependentCaptureFilter.render_firstOrder A) u hu p j hp hv
    rw [SeededClock.user_step _ x .callByValuePar _ _ _ k _ huser _ hpar _ p hp,
      SeededClock.user_step _ x .callByValueSeq _ _ _ k _ (htuser _) _
        (hseq _ (CaptureTransitionProfile.profile_mem (machine u) hD _)) _ j hj]
    change (match evV _ _ _ _ [pre x p j] (.seq (.lit u) (.param 0)) p with
      | some (some z) => evV _ _ _ _ [pre x p j] (parRender nodes u A B) z
      | other => other)=_
    rw [hrot]
    dsimp only [targetBody]
    cases hz : evV (seqGrammar nodes u A B) x .callByValueSeq (seqTable nodes u A B x k)
        [pre x p j] (tailPrefix u (profile (machine u) (pre x p j))) j with
    | none => rw [evV_seq_none hz]
    | some result => cases result with
      | none => rw [evV_seq_fail hz]
      | some z =>
        dsimp only []
        rw [evV_seq_ok hz]
        exact evaluator_of_rows nodes hNodes u hu A ha B x k ih B [profile (machine u) (pre x p j)] [pre x p j]
          (DependentCaptureFilter.environment_accurate (machine u) [pre x p j]) z
          (evV_ok (SeededClock.rounds_ok _ _ _ _ _) _ j hj z hz)

theorem evaluator_eq (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B : MExp) (x : List Char) (k : Nat)
    (e : MExp) (S : List (List Nat)) (E : List (List Char)) (hS : DependentCaptureFilter.Accurate (machine u) S E) (p : Nat) (hp : p≤x.length) :
    evV (parGrammar nodes u A B) x .callByValuePar (parTable nodes u A B x k) E (parRender nodes u A e) p =
      evV (seqGrammar nodes u A B) x .callByValueSeq (seqTable nodes u A B x k) E (seqRender nodes u A S e) p :=
  evaluator_of_rows nodes hNodes u hu A ha B x k (tables_shifted nodes hNodes u hu A ha B x k) e S E hS p hp

/-- Prefix seeds are removed: these are finite observations of the actual
first-order grammars on the same original character strings. -/
theorem observations_iff (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B e : MExp) (x : List Char) (rest : Option (List Char)) :
    SObs (parGrammar nodes u A B) .callByValuePar (parRender nodes u A e) x rest ↔
      SObs (seqGrammar nodes u A B) .callByValueSeq (seqRender nodes u A [] e) x rest := by
  have hb := component_valid nodes hNodes (machine u) (PeriodicCaptureMachine.valid u hu).1
  rw [SeededClock.observations_iff hb (par_installed nodes u A B) (par_firstOrder nodes u A B)
      x .callByValuePar (by decide) _ (parRender_firstOrder nodes u A e) rest,
    SeededClock.observations_iff hb (seq_installed nodes u A B) (seq_firstOrder nodes u A B)
      x .callByValueSeq (by decide) _ (seqRender_firstOrder nodes u A [] e) rest]
  constructor
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu A ha B x k e [] [] (DependentCaptureFilter.environment_accurate (machine u) []) x.length (Nat.le_refl _)).symm.trans hv,hr⟩
  · rintro ⟨k,v,hv,hr⟩
    exact ⟨k,v,(evaluator_eq nodes hNodes u hu A ha B x k e [] [] (DependentCaptureFilter.environment_accurate (machine u) []) x.length (Nat.le_refl _)).trans hv,hr⟩

theorem language_translation (nodes : List Node) (hNodes : Valid nodes) (u : List Char) (hu : u≠[])
    (A : Arg) (ha : DependentCaptureFilter.Valid nodes A) (B e : MExp) :
    ∃ (g : MGrammar) (start : MExp), g.FirstOrder ∧ start.FirstOrder ∧ ∀ x,
      SObs (parGrammar nodes u A B) .callByValuePar (parRender nodes u A e) x (some []) ↔
        SObs g .callByValueSeq start x (some []) :=
  ⟨seqGrammar nodes u A B,seqRender nodes u A [] e,seq_firstOrder nodes u A B,
    seqRender_firstOrder nodes u A [] e,fun x => observations_iff nodes hNodes u hu A ha B e x (some [])⟩


/-- The child appends a new ba capture to the retained aba, yielding ababa.
After it returns, the parent still replays its original aba. -/
theorem dependent_recursive_execution :
    let nodes : List Node := [.lit "aba".toList,.lit "ba".toList]
    let u := "ab".toList
    let A : Arg := .alt (.seq (.param 0) (.helper 1)) (.helper 0)
    let B := MExp.seq (.lit ['#']) (.seq (.param 0)
      (.alt (.seq (.lit ['!']) (.seq (.call 0 []) (.seq (.lit ['?']) (.param 0)))) .eps))
    let gp := parGrammar nodes u A B
    let gs := seqGrammar nodes u A B
    let e := MExp.seq (.call 0 []) (.notP .any)
    let x := "ababa#aba!abababa#ababa?aba".toList
    let bad := "ababa#aba!abababa#ababa?ababa".toList
    evV gp x .callByValuePar (tblV gp x .callByValuePar 18) [] (parRender nodes u A e) x.length=some (some 0) ∧
      evV gs x .callByValueSeq (tblV gs x .callByValueSeq 18) [] (seqRender nodes u A [] e) x.length=some (some 0) ∧
    evV gp bad .callByValuePar (tblV gp bad .callByValuePar 18) [] (parRender nodes u A e) bad.length=some none ∧
    evV gs bad .callByValueSeq (tblV gs bad .callByValueSeq 18) [] (seqRender nodes u A [] e) bad.length=some none := by
  decide +kernel

end Shallot.MacroPeg.CBV.ProfiledDependentRecursion
