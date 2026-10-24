import MacroPeg.CBV.RecursiveFilteredOverlap

/-! A captured value has a finite transition profile, even when its length
is unbounded. Actual generated filter queries can select that whole profile. -/
namespace Shallot.MacroPeg.CBV.CaptureTransitionProfile
open RegularCaptureProduct
open ClockFreezing (Table)

def profile (D : Machine) (w : List Char) : List Nat :=
  (List.range D.width).map (fun q => run D q w)

def profiles (D : Machine) : List (List Nat) := words (List.range D.width) D.width

theorem profile_length (D : Machine) (w : List Char) : (profile D w).length=D.width := by simp [profile]

theorem profile_get (D : Machine) (w : List Char) (q : Nat) (hq : q<D.width) :
    (profile D w)[q]?=some (run D q w) := by simp [profile,hq]

theorem profile_mem (D : Machine) (hD : D.Valid) (w : List Char) : profile D w∈profiles D := by
  apply (mem_words _ _ _).mpr
  refine ⟨profile_length D w,?_⟩
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  exact List.mem_range.mpr (run_bound hD q (List.mem_range.mp hq) w)

theorem profiles_length (D : Machine) : (profiles D).length=D.width^D.width := by
  simp only [profiles,length_words,List.length_range]

theorem member_length (D : Machine) (P : List Nat) (hP : P∈profiles D) : P.length=D.width :=
  ((mem_words _ _ _).mp hP).1

theorem member_bound (D : Machine) (P : List Nat) (hP : P∈profiles D) (q : Nat) (hq : q<D.width) :
    P[q]?.getD 0<D.width := by
  have hq' : q<P.length := by rw [member_length D P hP]; exact hq
  rw [List.getElem?_eq_getElem hq',Option.getD_some]
  exact List.mem_range.mp (((mem_words _ _ _).mp hP).2 _ (List.getElem_mem hq'))

/-- Concatenation acts by composing the two finite profiles. -/
theorem profile_append (D : Machine) (u v : List Char) :
    profile D (u++v)=(profile D u).map (fun q => run D q v) := by
  simp only [profile,List.map_map,run_append,Function.comp_def]

def compose (P Q : List Nat) : List Nat := P.map (fun q => Q[q]?.getD 0)

/-- Metadata for concatenated retained values is computed solely from the
two finite arrays, without inspecting either retained string. -/
theorem compose_correct (D : Machine) (hD : D.Valid) (u v : List Char) :
    compose (profile D u) (profile D v)=profile D (u++v) := by
  rw [profile_append]
  apply List.map_congr_left
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  have hbound := run_bound hD r (List.mem_range.mp hr) u
  simp only [profile_get D v _ hbound,Option.getD_some]

/-- A single ending phase need not determine the behavior of the same
captured value when replayed after a different prefix. -/
theorem single_phase_insufficient :
    let D := PeriodicCaptureMachine.machine "aab".toList
    run D 0 "a".toList=1 ∧ run D 0 "aaba".toList=1 ∧
      run D 1 "a".toList=2 ∧ run D 1 "aaba".toList=3 ∧
        profile D "a".toList≠profile D "aaba".toList := by decide +kernel

def checks (nodes : List Node) (D : Machine) (i : Nat) (P : List Nat) : List Nat → MExp
  | [] => .eps
  | q::qs => .seq (.andP (call nodes D i q (P[q]?.getD 0))) (checks nodes D i P qs)

def guard (nodes : List Node) (D : Machine) (i : Nat) (P : List Nat) : MExp :=
  .seq (.andP (.call i [])) (checks nodes D i P (List.range D.width))

theorem checks_firstOrder (nodes : List Node) (D : Machine) (i : Nat) (P : List Nat) :
    ∀ qs, (checks nodes D i P qs).FirstOrder
  | [] => True.intro
  | _::qs => ⟨True.intro,checks_firstOrder nodes D i P qs⟩

theorem guard_firstOrder (nodes : List Node) (D : Machine) (i : Nat) (P : List Nat) :
    (guard nodes D i P).FirstOrder := ⟨True.intro,checks_firstOrder nodes D i P _⟩

/-- Every probe concerns the same committed original capture and is a
lookahead, so gathering its profile does not advance the caller position. -/
theorem checks_eval (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : D.Valid)
    (x : List Char) (i p j : Nat) (hi : i<nodes.length) (hp : p≤x.length)
    (hv : evV (grammar nodes D) x .callByValueSeq
      (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) [] (.call i []) p=some (some j))
    (P : List Nat) (hP : P∈profiles D) :
    ∀ qs, (∀ q∈qs, q<D.width) →
      evV (grammar nodes D) x .callByValueSeq
        (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) [] (checks nodes D i P qs) p =
          if qs.all (fun q => run D q (pre x p j)==P[q]?.getD 0) then some (some p) else some none
  | [], _ => rfl
  | q::qs, hqs => by
    have hq := hqs q (by simp)
    have hc := product_correct nodes hNodes D hD x i q (P[q]?.getD 0) p hi hq (member_bound D P hP q hq) hp
    dsimp only [] at hc
    rw [hv] at hc
    simp only [checks]
    change (match evV _ _ _ _ [] (.andP (call nodes D i q (P[q]?.getD 0))) p with
      | some (some z) => evV _ _ _ _ [] (checks nodes D i P qs) z | other => other)=_
    rw [CallLookahead.evV_peek,hc]
    simp only [filtered]
    by_cases he : run D q (pre x p j)=P[q]?.getD 0
    · rw [if_pos he]
      dsimp only [CallLookahead.peek]
      rw [checks_eval nodes hNodes D hD x i p j hi hp hv P hP qs (fun q hq => hqs q (by simp [hq]))]
      simp [he]
    · rw [if_neg he]
      simp [CallLookahead.peek,he]

theorem checks_iff_profile (D : Machine) (P : List Nat) (hP : P∈profiles D) (w : List Char) :
    ((List.range D.width).all (fun q => run D q w==P[q]?.getD 0))=true ↔ P=profile D w := by
  constructor
  · intro h
    apply List.ext_getElem
    · rw [member_length D P hP,profile_length]
    · intro q hq hq'
      have hqD : q<D.width := by rw [←member_length D P hP]; exact hq
      have hs := (List.all_eq_true.mp h) q (List.mem_range.mpr hqD)
      have he : run D q w=P[q] := by
        simpa only [List.getElem?_eq_getElem hq,Option.getD_some,beq_iff_eq] using hs
      have hf := congrArg (fun o => o.getD 0) (profile_get D w q hqD)
      have hf' : (profile D w)[q]=run D q w := by
        simpa only [List.getElem?_eq_getElem hq',Option.getD_some] using hf
      exact he.symm.trans hf'.symm
  · intro he
    subst P
    apply List.all_eq_true.mpr
    intro q hq
    simp only [profile_get D w q (List.mem_range.mp hq),Option.getD_some,beq_self_eq_true]

/-- A real profile guard preserves undefined and failed source queries and
succeeds at the original position exactly for the captured value's full
profile. No guessed capture or semantic profile oracle is supplied. -/
theorem guard_correct (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : D.Valid)
    (x : List Char) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length)
    (P : List Nat) (hP : P∈profiles D) :
    let T := tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)
    evV (grammar nodes D) x .callByValueSeq T [] (guard nodes D i P) p =
      match evV (grammar nodes D) x .callByValueSeq T [] (.call i []) p with
      | some (some j) => if P=profile D (pre x p j) then some (some p) else some none
      | other => other := by
  dsimp only []
  change (match evV _ _ _ _ [] (.andP (.call i [])) p with
    | some (some z) => evV _ _ _ _ [] (checks nodes D i P (List.range D.width)) z
    | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV (grammar nodes D) x .callByValueSeq
      (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) [] (.call i []) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only [CallLookahead.peek]
      rw [checks_eval nodes hNodes D hD x i p j hi hp hv P hP _ (fun _ h => List.mem_range.mp h)]
      by_cases he : P=profile D (pre x p j)
      · rw [if_pos he,if_pos ((checks_iff_profile D P hP _).mpr he)]
      · rw [if_neg he,if_neg (fun h => he ((checks_iff_profile D P hP _).mp h))]

theorem choice_unique {α : Type} [DecidableEq α] (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (chosen : α) (v : Res) (R : α → MExp) :
    ∀ states : List α, (∀ t∈states, evV g x s T E (R t) p=if t=chosen then v else some none) →
      evV g x s T E (choice (states.map R)) p=if chosen∈states then v else some none
  | [], _ => by simp [choice,MExp.failAlways,evV]
  | t::states, h => by
    have ht := h t (by simp)
    have ih := choice_unique g x s T E p chosen v R states (fun t ht => h t (by simp [ht]))
    simp only [List.map_cons,choice]
    by_cases hc : t=chosen
    · rw [if_pos hc] at ht
      cases v with
      | none => rw [evV_alt_none ht]; simp [hc]
      | some result => cases result with
        | none => rw [evV_alt_fail ht,ih]; simp [hc]
        | some j => rw [evV_alt_ok ht]; simp [hc]
    · rw [if_neg hc] at ht
      rw [evV_alt_fail ht,ih]
      simp only [List.mem_cons,eq_comm (a := chosen) (b := t),hc,false_or]

theorem choice_failed {α : Type} (g : MGrammar) (x : List Char) (s : Strategy) (T : Table)
    (E : List (List Char)) (p : Nat) (R : α → MExp) : ∀ states : List α,
    (∀ t∈states, evV g x s T E (R t) p=some none) →
      evV g x s T E (choice (states.map R)) p=some none
  | [], _ => rfl
  | t::states, h => by
    rw [List.map_cons,choice,evV_alt_fail (h t (by simp))]
    exact choice_failed g x s T E p R states (fun t ht => h t (by simp [ht]))

def select (nodes : List Node) (D : Machine) (i : Nat) (K : List Nat → MExp) : MExp :=
  choice ((profiles D).map (fun P => .seq (guard nodes D i P) (K P)))

theorem select_firstOrder (nodes : List Node) (D : Machine) (i : Nat) (K : List Nat → MExp)
    (hK : ∀ P∈profiles D, (K P).FirstOrder) : (select nodes D i K).FirstOrder := by
  apply choice_firstOrder
  intro e he
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp he
  exact ⟨guard_firstOrder nodes D i P,hK P hP⟩

/-- Full profiles are selected before a continuation, with the original
capture fixed. Continuation failure cannot choose a different capture or
profile; undefinedness and finite failure are preserved. -/
theorem select_correct (nodes : List Node) (hNodes : Valid nodes) (D : Machine) (hD : D.Valid)
    (x : List Char) (i p : Nat) (hi : i<nodes.length) (hp : p≤x.length) (K : List Nat → MExp) :
    let T := tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)
    evV (grammar nodes D) x .callByValueSeq T [] (select nodes D i K) p =
      match evV (grammar nodes D) x .callByValueSeq T [] (.call i []) p with
      | some (some j) => evV (grammar nodes D) x .callByValueSeq T [] (K (profile D (pre x p j))) p
      | other => other := by
  dsimp only []
  cases hv : evV (grammar nodes D) x .callByValueSeq
      (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) [] (.call i []) p with
  | none =>
    have hne : profiles D≠[] := by
      intro hn
      have hmem := profile_mem D hD []
      rw [hn] at hmem
      contradiction
    cases hs : profiles D with
    | nil => exact False.elim (hne hs)
    | cons P Ps =>
      have hP : P∈profiles D := by rw [hs]; simp
      have hg := guard_correct nodes hNodes D hD x i p hi hp P hP
      dsimp only [] at hg
      rw [hv] at hg
      unfold select
      rw [hs,List.map_cons,choice]
      exact evV_alt_none (evV_seq_none hg)
  | some result => cases result with
    | none =>
      apply choice_failed
      intro P hP
      have hg := guard_correct nodes hNodes D hD x i p hi hp P hP
      dsimp only [] at hg
      rw [hv] at hg
      exact evV_seq_fail hg
    | some j =>
      unfold select
      rw [choice_unique (chosen := profile D (pre x p j))
        (v := evV (grammar nodes D) x .callByValueSeq
          (tblV (grammar nodes D) x .callByValueSeq (iterBoundV (grammar nodes D) x)) []
          (K (profile D (pre x p j))) p)]
      · rw [if_pos (profile_mem D hD _)]
      · intro P hP
        have hg := guard_correct nodes hNodes D hD x i p hi hp P hP
        dsimp only [] at hg
        rw [hv] at hg
        dsimp only [] at hg
        by_cases he : P=profile D (pre x p j)
        · rw [if_pos he] at hg
          rw [evV_seq_ok hg,if_pos he,he]
        · rw [if_neg he] at hg
          rw [evV_seq_fail hg,if_neg he]

end Shallot.MacroPeg.CBV.CaptureTransitionProfile
