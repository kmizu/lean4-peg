import MacroPeg.CBV.ProfileControl

/-! Compositional control laws for actual inline state-filter expressions. -/
namespace Shallot.MacroPeg.CBV.ControlFilter
open RegularCaptureProduct

theorem seq_correct (D : Machine) (hD : D.Valid) (g : MGrammar) (x : List Char)
    (s : Strategy) (hs : s≠.callByName) (T : ClockFreezing.Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (a b : MExp) (ha : a.FirstOrder) (hFOB : b.FirstOrder)
    (A B : Nat → Nat → MExp) (p : Nat) (hp : p≤x.length)
    (hA : ∀ q r, q<D.width → r<D.width → evV g x s T E (A q r) p=filtered D x q r p (evV g x s T E a p))
    (hB : ∀ z, z≤x.length → ∀ q r, q<D.width → r<D.width → evV g x s T E (B q r) z=filtered D x q r z (evV g x s T E b z))
    (q r : Nat) (hq : q<D.width) (hr : r<D.width) :
    evV g x s T E (choice ((List.range D.width).map (fun t => .seq (A q t) (B t r)))) p =
      filtered D x q r p (evV g x s T E (.seq a b) p) := by
    cases hv : evV g x s T E a p with
    | none =>
      rw [evV_seq_none hv]
      apply RecursiveFilteredOverlap.choice_none
      · intro hn
        have hl := congrArg List.length hn
        simp only [List.length_range,List.length_nil] at hl
        omega
      · intro t ht
        have he := hA q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_none he
    | some result => cases result with
      | none =>
        rw [evV_seq_fail hv]
        apply CaptureTransitionProfile.choice_failed
        intro t ht
        have he := hA q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_fail he
      | some z =>
        have hz := WordStarFilter.success_prefix hs hT E a ha p z hp hv
        have ht := run_bound hD q hq (pre x p z)
        rw [CaptureTransitionProfile.choice_unique (chosen := run D q (pre x p z))
          (v := filtered D x (run D q (pre x p z)) r z
            (evV g x s T E b z))]
        · rw [if_pos (List.mem_range.mpr ht),evV_seq_ok hv]
          cases hb : evV g x s T E b z with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some j =>
              have hj := WordStarFilter.success_prefix hs hT E b hFOB z j hz.1 hb
              have he := SequenceArguments.pre_concat hp hj.1 hz.2 hj.2
              simp only [filtered,he,run_append]
        · intro t hmem
          have he := hA q t hq (List.mem_range.mp hmem)
          rw [hv] at he
          simp only [filtered] at he
          by_cases ht' : t=run D q (pre x p z)
          · subst t
            rw [if_pos rfl] at he
            rw [evV_seq_ok he,if_pos rfl]
            exact hB z hz.1 _ r ht hr
          · rw [if_neg (Ne.symm ht')] at he
            rw [evV_seq_fail he,if_neg ht']

theorem seq_transfer (D : Machine) (hD : D.Valid) (g h : MGrammar) (x : List Char)
    (s t : Strategy) (hs : s≠.callByName) (T U : ClockFreezing.Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (a b : MExp) (ha : a.FirstOrder) (hFOB : b.FirstOrder)
    (A B : Nat → Nat → MExp) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) (hr : r<D.width)
    (hA : ∀ q r, q<D.width → r<D.width → evV h x t U E (A q r) p=filtered D x q r p (evV g x s T E a p))
    (hB : ∀ z, z≤x.length → ∀ q, q<D.width → evV h x t U E (B q r) z=filtered D x q r z (evV g x s T E b z))
    :
    evV h x t U E (choice ((List.range D.width).map (fun t => .seq (A q t) (B t r)))) p =
      filtered D x q r p (evV g x s T E (.seq a b) p) := by
    cases hv : evV g x s T E a p with
    | none =>
      rw [evV_seq_none hv]
      apply RecursiveFilteredOverlap.choice_none
      · intro hn
        have hl := congrArg List.length hn
        simp only [List.length_range,List.length_nil] at hl
        omega
      · intro t ht
        have he := hA q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_none he
    | some result => cases result with
      | none =>
        rw [evV_seq_fail hv]
        apply CaptureTransitionProfile.choice_failed
        intro t ht
        have he := hA q t hq (List.mem_range.mp ht)
        rw [hv] at he
        exact evV_seq_fail he
      | some z =>
        have hz := WordStarFilter.success_prefix hs hT E a ha p z hp hv
        have ht := run_bound hD q hq (pre x p z)
        rw [CaptureTransitionProfile.choice_unique (chosen := run D q (pre x p z))
          (v := filtered D x (run D q (pre x p z)) r z
            (evV g x s T E b z))]
        · rw [if_pos (List.mem_range.mpr ht),evV_seq_ok hv]
          cases hb : evV g x s T E b z with
          | none => rfl
          | some result => cases result with
            | none => rfl
            | some j =>
              have hj := WordStarFilter.success_prefix hs hT E b hFOB z j hz.1 hb
              have he := SequenceArguments.pre_concat hp hj.1 hz.2 hj.2
              simp only [filtered,he,run_append]
        · intro t hmem
          have he := hA q t hq (List.mem_range.mp hmem)
          rw [hv] at he
          simp only [filtered] at he
          by_cases ht' : t=run D q (pre x p z)
          · subst t
            rw [if_pos rfl] at he
            rw [evV_seq_ok he,if_pos rfl]
            exact hB z hz.1 _ ht
          · rw [if_neg (Ne.symm ht')] at he
            rw [evV_seq_fail he,if_neg ht']

end Shallot.MacroPeg.CBV.ControlFilter
