import MacroPeg.CBV.ForwardingPrefixCycles

namespace Shallot.MacroPeg.CBV.ForwardingPrefixTrace
open MultiplyingPrefixCompiler
open ForwardingPrefixCycles (Closed)

inductive Result where
  | terminal (index : Nat) (seen : List Nat)
  | cycle (ids : List Nat)
  | exhausted
  deriving DecidableEq

/-- Only the unique factor-1 head edge is followed. Continuations are
retained for later inlining and do not affect this head classification. -/
def trace (rs : List Spec) : Nat → Nat → List Nat → Result
  | 0,_,_ => .exhausted
  | fuel+1,i,seen =>
    if i∈seen then .cycle seen else
    match rs[i]? with
    | none => .terminal i seen
    | some r => if r.factor=1 then trace rs fuel r.callee (i::seen) else .terminal i seen

def classify (rs : List Spec) (i : Nat) := trace rs (rs.length+1) i []

def Trail (rs : List Spec) (seen : List Nat) (frontier : Nat) : Prop :=
  ∀ i∈seen, ∃ r, rs[i]?=some r ∧ r.factor=1 ∧ (r.callee∈seen ∨ r.callee=frontier)

theorem trail_push (rs : List Spec) (seen : List Nat) (i : Nat) (r : Spec)
    (ht : Trail rs seen i) (hr : rs[i]?=some r) (hf : r.factor=1) : Trail rs (i::seen) r.callee := by
  intro a ha
  rcases List.mem_cons.mp ha with he|ha
  · subst a
    exact ⟨r,hr,hf,Or.inr rfl⟩
  · obtain ⟨s,hs,hf,hn⟩ := ht a ha
    refine ⟨s,hs,hf,Or.inl ?_⟩
    rcases hn with hn|hn
    · exact List.mem_cons_of_mem _ hn
    · exact List.mem_cons.mpr (Or.inl hn)

theorem trail_closed (rs : List Spec) (seen : List Nat) (i : Nat) (ht : Trail rs seen i)
    (hi : i∈seen) : ForwardingPrefixCycles.Closed rs seen := by
  intro a ha
  obtain ⟨s,hs,hf,hn⟩ := ht a ha
  exact ⟨s,hs,hf,hn.elim id (fun he => he.symm ▸ hi)⟩

theorem cycle_sound (rs : List Spec) (fuel i : Nat) (seen ids : List Nat)
    (ht : Trail rs seen i) (hc : trace rs fuel i seen=.cycle ids) :
    ForwardingPrefixCycles.Closed rs ids ∧ i∈ids ∧ seen⊆ids := by
  induction fuel generalizing i seen with
  | zero => cases hc
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp only [trace,if_pos hi,Result.cycle.injEq] at hc
      subst ids
      exact ⟨trail_closed rs seen i ht hi,hi,fun _ h => h⟩
    · cases hr : rs[i]? with
      | none => simp [trace,hi,hr] at hc
      | some r =>
        by_cases hf : r.factor=1
        · simp only [trace,if_neg hi,hr,if_pos hf] at hc
          obtain ⟨hclosed,_,hsub⟩ := ih r.callee (i::seen) (trail_push rs seen i r ht hr hf) hc
          exact ⟨hclosed,hsub (by simp),fun _ ha => hsub (List.mem_cons_of_mem _ ha)⟩
        · simp [trace,hi,hr,hf] at hc

private theorem nodup_subset_length (xs ys : List Nat) (hn : xs.Nodup) (hs : xs⊆ys) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ha : a∈ys := hs (by simp)
    have hxs : xs⊆ys.erase a := by
      intro b hb
      have hba : b≠a := by intro he; subst b; exact (List.nodup_cons.mp hn).1 hb
      exact (List.mem_erase_of_ne hba).mpr (hs (by simp [hb]))
    have he := ih (ys.erase a) (List.nodup_cons.mp hn).2 hxs
    rw [List.length_erase_of_mem ha] at he
    have hp : 0<ys.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem trace_not_exhausted (rs : List Spec) (fuel i : Nat) (seen : List Nat)
    (hn : seen.Nodup) (hb : ∀ a∈seen, a<rs.length) (hf : rs.length<seen.length+fuel) :
    trace rs fuel i seen≠.exhausted := by
  induction fuel generalizing i seen with
  | zero =>
    have hle : seen.length≤rs.length := by
      have := nodup_subset_length seen (List.range rs.length) hn (fun _ ha => List.mem_range.mpr (hb _ ha))
      simpa only [List.length_range] using this
    omega
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp [trace,hi]
    · cases hr : rs[i]? with
      | none => simp [trace,hi,hr]
      | some r =>
        by_cases hm : r.factor=1
        · simp only [trace,if_neg hi,hr,if_pos hm]
          apply ih r.callee (i::seen) (List.nodup_cons.mpr ⟨hi,hn⟩)
          · intro a ha
            rcases List.mem_cons.mp ha with he|ha
            · subst a; exact (List.getElem?_eq_some_iff.mp hr).1
            · exact hb a ha
          · simp only [List.length_cons]; omega
        · simp [trace,hi,hr,hm]

theorem classify_total (rs : List Spec) (i : Nat) : classify rs i≠.exhausted :=
  trace_not_exhausted rs (rs.length+1) i [] (by simp) (by simp) (by simp)

theorem classify_cycle (rs : List Spec) (i : Nat) (ids : List Nat) (h : classify rs i=.cycle ids) :
    ForwardingPrefixCycles.check rs ids=true ∧ i∈ids := by
  obtain ⟨hc,hi,_⟩ := cycle_sound rs (rs.length+1) i [] ids (by simp [Trail]) h
  exact ⟨(ForwardingPrefixCycles.checked_iff rs ids).mpr hc,hi⟩

theorem terminal_sound (rs : List Spec) (fuel i : Nat) (seen : List Nat) (j : Nat) (path : List Nat)
    (h : trace rs fuel i seen=.terminal j path) :
    rs[j]?=none ∨ ∃ r, rs[j]?=some r ∧ r.factor≠1 := by
  induction fuel generalizing i seen with
  | zero => cases h
  | succ fuel ih =>
    by_cases hi : i∈seen
    · simp [trace,hi] at h
    · cases hr : rs[i]? with
      | none =>
        simp only [trace,if_neg hi,hr,Result.terminal.injEq] at h
        exact Or.inl (h.1 ▸ hr)
      | some r =>
        by_cases hf : r.factor=1
        · simp only [trace,if_neg hi,hr,if_pos hf] at h
          exact ih r.callee (i::seen) h
        · simp only [trace,if_neg hi,hr,if_neg hf,Result.terminal.injEq] at h
          exact Or.inr ⟨r,h.1 ▸ hr,hf⟩

theorem closed_no_terminal (rs : List Spec) (ids : List Nat) (hc : ForwardingPrefixCycles.Closed rs ids)
    (fuel i : Nat) (hi : i∈ids) (seen : List Nat) (j : Nat) (path : List Nat) :
    trace rs fuel i seen≠.terminal j path := by
  induction fuel generalizing i seen with
  | zero => simp [trace]
  | succ fuel ih =>
    by_cases hs : i∈seen
    · simp [trace,hs]
    · obtain ⟨r,hr,hfactor,hnext⟩ := hc i hi
      simp only [trace,if_neg hs,hr,if_pos hfactor]
      exact ih r.callee hnext (i::seen)

/-- Every finitely certified closed forwarding component is recognized
automatically, including paths feeding its cycle. -/
theorem closed_classifies_cycle (rs : List Spec) (ids : List Nat) (hc : ForwardingPrefixCycles.Closed rs ids)
    (i : Nat) (hi : i∈ids) : ∃ out, classify rs i=.cycle out := by
  cases h : classify rs i with
  | cycle out => exact ⟨out,rfl⟩
  | exhausted => exact False.elim (classify_total rs i h)
  | terminal j path => exact False.elim (closed_no_terminal rs ids hc (rs.length+1) i hi [] j path h)

end Shallot.MacroPeg.CBV.ForwardingPrefixTrace
