import MacroPeg.CBV.ParametricHelperControl

/-! Finite profile selection for a retained-value-dependent fresh argument,
and its actual handoff to a profile-specialized unary Seq rule. -/
namespace Shallot.MacroPeg.CBV.DependentProfileCall
open RegularCaptureProduct
open DependentCaptureFilter (Accurate render filter)
open CaptureTransitionProfile (profile profiles)
abbrev Arg := DependentCaptureFilter.Expr

abbrev caller (nodes : List Node) (D : Machine) (extra : List MRule) :=
  FilteredOverlapCaller.extend nodes D extra
abbrev rounds (nodes : List Node) (D : Machine) (extra : List MRule) (x : List Char) (k : Nat) :=
  SeededClock.rounds (component nodes D) (caller nodes D extra) x .callByValueSeq k

def checks (nodes : List Node) (D : Machine) (S : List (List Nat))
    (a : Arg) (P : List Nat) : List Nat → MExp
  | [] => .eps
  | q::qs => .seq (.andP (filter nodes D S a q (P[q]?.getD 0))) (checks nodes D S a P qs)

def guard (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) (P : List Nat) : MExp :=
  .seq (.andP (render a)) (checks nodes D S a P (List.range D.width))

def select (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) (K : List Nat → MExp) : MExp :=
  choice ((profiles D).map (fun P => .seq (guard nodes D S a P) (K P)))

theorem checks_firstOrder (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) (P : List Nat) :
    ∀ qs, (checks nodes D S a P qs).FirstOrder
  | [] => True.intro
  | q::qs => ⟨DependentCaptureFilter.filter_firstOrder nodes D S a q _,checks_firstOrder nodes D S a P qs⟩

theorem guard_firstOrder (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) (P : List Nat) :
    (guard nodes D S a P).FirstOrder := ⟨DependentCaptureFilter.render_firstOrder a,checks_firstOrder nodes D S a P _⟩

theorem select_firstOrder (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg)
    (K : List Nat → MExp) (hK : ∀ P∈profiles D, (K P).FirstOrder) :
    (select nodes D S a K).FirstOrder := by
  apply choice_firstOrder
  intro e he
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp he
  exact ⟨guard_firstOrder nodes D S a P,hK P hP⟩

theorem filter_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (extra : List MRule) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (filter nodes D S a q r) p =
      filtered D x q r p (evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p) := by
  rw [ParametricHelperControl.rounds_base nodes hNodes D hD.1 extra x .callByValueSeq k E _
      (ParametricHelperControl.filter_safe nodes D hD.1 S a ha q r hq hr) p hp,
    ParametricHelperControl.rounds_base nodes hNodes D hD.1 extra x .callByValueSeq k E _
      (ParametricHelperControl.render_safe nodes D a ha) p hp]
  exact DependentCaptureFilter.correct nodes hNodes D hD x S E hS a ha p hp q r hq hr

theorem checks_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (extra : List MRule) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p j : Nat) (hp : p≤x.length)
    (hv : evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p=some (some j))
    (P : List Nat) (hP : P∈profiles D) :
    ∀ qs, (∀ q∈qs, q<D.width) →
      evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (checks nodes D S a P qs) p =
        if qs.all (fun q => run D q (pre x p j)==P[q]?.getD 0) then some (some p) else some none
  | [], _ => rfl
  | q::qs, hqs => by
    have hq := hqs q (by simp)
    have hc := filter_correct nodes hNodes D hD extra x k S E hS a ha p hp q (P[q]?.getD 0)
      hq (CaptureTransitionProfile.member_bound D P hP q hq)
    rw [hv] at hc
    change (match evV _ _ _ _ E (.andP (filter nodes D S a q (P[q]?.getD 0))) p with
      | some (some z) => evV _ _ _ _ E (checks nodes D S a P qs) z | other => other)=_
    rw [CallLookahead.evV_peek,hc]
    simp only [filtered]
    by_cases he : run D q (pre x p j)=P[q]?.getD 0
    · rw [if_pos he]
      dsimp only [CallLookahead.peek]
      rw [checks_correct nodes hNodes D hD extra x k S E hS a ha p j hp hv P hP qs
        (fun q hq => hqs q (by simp [hq]))]
      simp [he]
    · rw [if_neg he]
      simp [CallLookahead.peek,he]

/-- Every profile query follows the selected parameter-dependent argument,
including newly captured helper strings and retained parameter values. -/
theorem guard_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (extra : List MRule) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length)
    (P : List Nat) (hP : P∈profiles D) :
    evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (guard nodes D S a P) p =
      match evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p with
      | some (some j) => if P=profile D (pre x p j) then some (some p) else some none
      | other => other := by
  change (match evV _ _ _ _ E (.andP (render a)) p with
    | some (some z) => evV _ _ _ _ E (checks nodes D S a P (List.range D.width)) z | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only [CallLookahead.peek]
      rw [checks_correct nodes hNodes D hD extra x k S E hS a ha p j hp hv P hP _ (fun _ h => List.mem_range.mp h)]
      by_cases he : P=profile D (pre x p j)
      · rw [if_pos he,if_pos ((CaptureTransitionProfile.checks_iff_profile D P hP _).mpr he)]
      · rw [if_neg he,if_neg (fun h => he ((CaptureTransitionProfile.checks_iff_profile D P hP _).mp h))]

/-- Profile discrimination is before the actual call. Later failure cannot
change the captured word or try a different metadata value for it. -/
theorem select_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (extra : List MRule) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length)
    (K : List Nat → MExp) :
    evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (select nodes D S a K) p =
      match evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p with
      | some (some j) => evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (K (profile D (pre x p j))) p
      | other => other := by
  cases hv : evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (render a) p with
  | none =>
    have hne : profiles D≠[] := by
      intro hn
      have hm := CaptureTransitionProfile.profile_mem D hD []
      rw [hn] at hm
      contradiction
    cases hs : profiles D with
    | nil => exact False.elim (hne hs)
    | cons P Ps =>
      have hg := guard_correct nodes hNodes D hD extra x k S E hS a ha p hp P (by rw [hs]; simp)
      rw [hv] at hg
      unfold select
      rw [hs,List.map_cons,choice]
      exact evV_alt_none (evV_seq_none hg)
  | some result => cases result with
    | none =>
      apply CaptureTransitionProfile.choice_failed
      intro P hP
      have hg := guard_correct nodes hNodes D hD extra x k S E hS a ha p hp P hP
      rw [hv] at hg
      exact evV_seq_fail hg
    | some j =>
      unfold select
      rw [CaptureTransitionProfile.choice_unique (chosen := profile D (pre x p j))
        (v := evV (caller nodes D extra) x .callByValueSeq (rounds nodes D extra x k) E (K (profile D (pre x p j))) p)]
      · rw [if_pos (CaptureTransitionProfile.profile_mem D hD _)]
      · intro P hP
        have hg := guard_correct nodes hNodes D hD extra x k S E hS a ha p hp P hP
        rw [hv] at hg
        dsimp only [] at hg
        by_cases he : P=profile D (pre x p j)
        · rw [if_pos he] at hg
          rw [evV_seq_ok hg,if_pos he,he]
        · rw [if_neg he] at hg
          rw [evV_seq_fail hg,if_neg he]

theorem index_correct {α : Type} [BEq α] [LawfulBEq α] (a : α) :
    ∀ xs : List α, a∈xs → xs[xs.idxOf a]?=some a
  | [], h => by contradiction
  | b::xs, h => by
    by_cases he : b=a
    · subst b; simp
    · have ht : a∈xs := by
        rcases List.mem_cons.mp h with h | h
        · exact False.elim (he h.symm)
        · exact h
      have hb : (b==a)=false := beq_eq_false_iff_ne.mpr he
      simpa [List.idxOf_cons,hb] using index_correct a xs ht

def address (nodes : List Node) (D : Machine) (P : List Nat) : Nat :=
  (grammar nodes D).rules.length+(profiles D).idxOf P

def rules (D : Machine) (B : List Nat → MExp) : List MRule :=
  (profiles D).map (fun P => ⟨1,B P⟩)

abbrev specialized (nodes : List Node) (D : Machine) (B : List Nat → MExp) := caller nodes D (rules D B)

def entry (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) : MExp :=
  select nodes D S a (fun P => .call (address nodes D P) [render a])

theorem specialized_rule (nodes : List Node) (D : Machine) (B : List Nat → MExp)
    (P : List Nat) (hP : P∈profiles D) :
    ruleAtM (specialized nodes D B).rules (address nodes D P)=some ⟨1,B P⟩ := by
  change ruleAtM ((grammar nodes D).rules++rules D B) (address nodes D P)=some ⟨1,B P⟩
  rw [ruleAtM_eq_getElem?,address,List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left,rules,List.getElem?_map,index_correct P _ hP,Option.map_some]

theorem specialized_firstOrder (nodes : List Node) (D : Machine) (B : List Nat → MExp)
    (hB : ∀ P∈profiles D, (B P).FirstOrder) : (specialized nodes D B).FirstOrder := by
  intro rule hr
  rcases List.mem_append.mp hr with hr | hr
  · exact grammar_firstOrder nodes D rule hr
  · obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hr
    exact hB P hP

theorem entry_firstOrder (nodes : List Node) (D : Machine) (S : List (List Nat)) (a : Arg) :
    (entry nodes D S a).FirstOrder :=
  select_firstOrder nodes D S a _ (fun _ _ => ⟨DependentCaptureFilter.render_firstOrder a,True.intro⟩)

/-- The chosen metadata is the real callee address, and the new captured
string is the real unary argument at its consumed endpoint. This concerns
actual installed rows, not a continuation supplied with an unknown word. -/
theorem entry_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (B : List Nat → MExp) (x : List Char) (k : Nat)
    (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length) :
    let T := rounds nodes D (rules D B) x k
    evV (specialized nodes D B) x .callByValueSeq T E (entry nodes D S a) p =
      match evV (specialized nodes D B) x .callByValueSeq T E (render a) p with
      | some (some j) => valAt (T (address nodes D (profile D (pre x p j))) [pre x p j]) j
      | other => other := by
  dsimp only []
  unfold entry
  rw [select_correct nodes hNodes D hD (rules D B) x k S E hS a ha p hp]
  cases hv : evV (specialized nodes D B) x .callByValueSeq (rounds nodes D (rules D B) x k) E (render a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only []
      rw [evV_call_seq (specialized_rule nodes D B _ (CaptureTransitionProfile.profile_mem D hD _)) rfl]
      simp only [evSeqArgs,hv]

/-- Source argument evaluation and the metadata-specialized Seq call may
use different real user grammars and different seeded stages. The new
value's full profile and endpoint are nevertheless the original Par ones. -/
theorem entry_par_correct (nodes : List Node) (hNodes : RegularCaptureProduct.Valid nodes)
    (D : Machine) (hD : D.Valid) (left : List MRule) (B : List Nat → MExp)
    (x : List Char) (k l : Nat) (S : List (List Nat)) (E : List (List Char)) (hS : Accurate D S E)
    (a : Arg) (ha : DependentCaptureFilter.Valid nodes a) (p : Nat) (hp : p≤x.length) :
    let T := rounds nodes D (rules D B) x l
    evV (specialized nodes D B) x .callByValueSeq T E (entry nodes D S a) p =
      match evV (caller nodes D left) x .callByValuePar
        (SeededClock.rounds (component nodes D) (caller nodes D left) x .callByValuePar k) E (render a) p with
      | some (some j) => valAt (T (address nodes D (profile D (pre x p j))) [pre x p j]) j
      | other => other := by
  dsimp only []
  rw [entry_correct nodes hNodes D hD B x l S E hS a ha p hp]
  have he : evV (specialized nodes D B) x .callByValueSeq (rounds nodes D (rules D B) x l) E (render a) p =
      evV (caller nodes D left) x .callByValuePar
        (SeededClock.rounds (component nodes D) (caller nodes D left) x .callByValuePar k) E (render a) p := by
    rw [ParametricHelperControl.rounds_base nodes hNodes D hD.1 (rules D B) x .callByValueSeq l E _
        (ParametricHelperControl.render_safe nodes D a ha) p hp,
      ParametricHelperControl.rounds_base nodes hNodes D hD.1 left x .callByValuePar k E _
        (ParametricHelperControl.render_safe nodes D a ha) p hp]
  rw [he]

end Shallot.MacroPeg.CBV.DependentProfileCall
