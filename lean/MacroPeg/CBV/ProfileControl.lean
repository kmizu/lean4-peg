import MacroPeg.CBV.CapturePrefixRows

/-! Profile discrimination parameterized by actual plain and filtered argument
expressions. Recursive compilers discharge the one-step filter premise. -/
namespace Shallot.MacroPeg.CBV.ProfileControl
open RegularCaptureProduct
open CaptureTransitionProfile (profile profiles)

def checks (D : Machine) (a : MExp) (F : Nat → Nat → MExp) (P : List Nat) : List Nat → MExp
  | [] => .eps
  | q::qs => .seq (.andP (F q (P[q]?.getD 0))) (checks D a F P qs)

def guard (D : Machine) (a : MExp) (F : Nat → Nat → MExp) (P : List Nat) : MExp :=
  .seq (.andP (a)) (checks D a F P (List.range D.width))

def select (D : Machine) (a : MExp) (F : Nat → Nat → MExp) (K : List Nat → MExp) : MExp :=
  choice ((profiles D).map (fun P => .seq (guard D a F P) (K P)))

theorem checks_firstOrder (D : Machine) (a : MExp) (F : Nat → Nat → MExp) (hF : ∀ q r, (F q r).FirstOrder) (P : List Nat) :
    ∀ qs, (checks D a F P qs).FirstOrder
  | [] => True.intro
  | q::qs => ⟨hF q _,checks_firstOrder D a F hF P qs⟩

theorem guard_firstOrder (D : Machine) (a : MExp) (F : Nat → Nat → MExp) (ha : a.FirstOrder) (hF : ∀ q r, (F q r).FirstOrder) (P : List Nat) :
    (guard D a F P).FirstOrder := ⟨ha,checks_firstOrder D a F hF P _⟩

theorem select_firstOrder (D : Machine) (a : MExp) (F : Nat → Nat → MExp)
    (ha : a.FirstOrder) (hF : ∀ q r, (F q r).FirstOrder)
    (K : List Nat → MExp) (hK : ∀ P∈profiles D, (K P).FirstOrder) :
    (select D a F K).FirstOrder := by
  apply choice_firstOrder
  intro e he
  obtain ⟨P,hP,rfl⟩ := List.mem_map.mp he
  exact ⟨guard_firstOrder D a F ha hF P,hK P hP⟩

theorem checks_correct (D : Machine) (hD : D.Valid) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (a : MExp) (F : Nat → Nat → MExp) (p j : Nat)
    (hF : ∀ q r, q<D.width → r<D.width → evV g x s T E (F q r) p=filtered D x q r p (evV g x s T E a p))
    (hv : evV g x s T E (a) p=some (some j))
    (P : List Nat) (hP : P∈profiles D) :
    ∀ qs, (∀ q∈qs, q<D.width) →
      evV g x s T E (checks D a F P qs) p =
        if qs.all (fun q => run D q (pre x p j)==P[q]?.getD 0) then some (some p) else some none
  | [], _ => rfl
  | q::qs, hqs => by
    have hq := hqs q (by simp)
    have hc := hF q (P[q]?.getD 0)
      hq (CaptureTransitionProfile.member_bound D P hP q hq)
    rw [hv] at hc
    change (match evV _ _ _ _ E (.andP (F q (P[q]?.getD 0))) p with
      | some (some z) => evV _ _ _ _ E (checks D a F P qs) z | other => other)=_
    rw [CallLookahead.evV_peek,hc]
    simp only [filtered]
    by_cases he : run D q (pre x p j)=P[q]?.getD 0
    · rw [if_pos he]
      dsimp only [CallLookahead.peek]
      rw [checks_correct D hD g x s T E a F p j hF hv P hP qs
        (fun q hq => hqs q (by simp [hq]))]
      simp [he]
    · rw [if_neg he]
      simp [CallLookahead.peek,he]

/-- Every profile query follows the selected parameter-dependent argument,
without restricting the syntax or recursion of the argument. -/
theorem guard_correct (D : Machine) (hD : D.Valid) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (a : MExp) (F : Nat → Nat → MExp) (p : Nat)
    (hF : ∀ q r, q<D.width → r<D.width → evV g x s T E (F q r) p=filtered D x q r p (evV g x s T E a p))
    (P : List Nat) (hP : P∈profiles D) :
    evV g x s T E (guard D a F P) p =
      match evV g x s T E (a) p with
      | some (some j) => if P=profile D (pre x p j) then some (some p) else some none
      | other => other := by
  change (match evV _ _ _ _ E (.andP (a)) p with
    | some (some z) => evV _ _ _ _ E (checks D a F P (List.range D.width)) z | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV g x s T E (a) p with
  | none => rfl
  | some result => cases result with
    | none => rfl
    | some j =>
      dsimp only [CallLookahead.peek]
      rw [checks_correct D hD g x s T E a F p j hF hv P hP _ (fun _ h => List.mem_range.mp h)]
      by_cases he : P=profile D (pre x p j)
      · rw [if_pos he,if_pos ((CaptureTransitionProfile.checks_iff_profile D P hP _).mpr he)]
      · rw [if_neg he,if_neg (fun h => he ((CaptureTransitionProfile.checks_iff_profile D P hP _).mp h))]

/-- Profile discrimination is before the actual call. Later failure cannot
change the captured word or try a different metadata value for it. -/
theorem select_correct (D : Machine) (hD : D.Valid) (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (a : MExp) (F : Nat → Nat → MExp) (p : Nat)
    (hF : ∀ q r, q<D.width → r<D.width → evV g x s T E (F q r) p=filtered D x q r p (evV g x s T E a p))
    (K : List Nat → MExp) :
    evV g x s T E (select D a F K) p =
      match evV g x s T E (a) p with
      | some (some j) => evV g x s T E (K (profile D (pre x p j))) p
      | other => other := by
  cases hv : evV g x s T E (a) p with
  | none =>
    have hne : profiles D≠[] := by
      intro hn
      have hm := CaptureTransitionProfile.profile_mem D hD []
      rw [hn] at hm
      contradiction
    cases hs : profiles D with
    | nil => exact False.elim (hne hs)
    | cons P Ps =>
      have hg := guard_correct D hD g x s T E a F p hF P (by rw [hs]; simp)
      rw [hv] at hg
      unfold select
      rw [hs,List.map_cons,choice]
      exact evV_alt_none (evV_seq_none hg)
  | some result => cases result with
    | none =>
      apply CaptureTransitionProfile.choice_failed
      intro P hP
      have hg := guard_correct D hD g x s T E a F p hF P hP
      rw [hv] at hg
      exact evV_seq_fail hg
    | some j =>
      unfold select
      rw [CaptureTransitionProfile.choice_unique (chosen := profile D (pre x p j))
        (v := evV g x s T E (K (profile D (pre x p j))) p)]
      · rw [if_pos (CaptureTransitionProfile.profile_mem D hD _)]
      · intro P hP
        have hg := guard_correct D hD g x s T E a F p hF P hP
        rw [hv] at hg
        dsimp only [] at hg
        by_cases he : P=profile D (pre x p j)
        · rw [if_pos he] at hg
          rw [evV_seq_ok hg,if_pos he,he]
        · rw [if_neg he] at hg
          rw [evV_seq_fail hg,if_neg he]


end Shallot.MacroPeg.CBV.ProfileControl
