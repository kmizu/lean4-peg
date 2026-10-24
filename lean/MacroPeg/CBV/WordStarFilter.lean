import MacroPeg.CBV.InlineRepeat

/-! Filter a repeated retained Word expression without a parameter-bearing
helper call, preserving its greedy endpoint and partial results. -/
namespace Shallot.MacroPeg.CBV.WordStarFilter
open RegularCaptureProduct
open CaptureTransitionProfile (profile)
open ClockFreezing (Table)

def summary (D : Machine) (S : List (List Nat)) : MExp → Option (List Nat)
  | .lit w => some (profile D w)
  | .param k => S[k]?
  | .seq a b => (summary D S a).bind (fun P => (summary D S b).map (CaptureTransitionProfile.compose P))
  | _ => none

def transition (D : Machine) (S : List (List Nat)) (e : MExp) (q : Nat) : Nat :=
  ((summary D S e).bind (fun P => P[q]?)).getD 0 % D.width

def filter (D : Machine) (S : List (List Nat)) (e : MExp) (q r : Nat) : MExp :=
  .seq (.andP (.star e)) (choice ((CaptureOrbit.descriptors (transition D S e) D.width q r).map
    (fun (k,l) => InlineRepeat.pattern e k l)))

theorem transition_bound (D : Machine) (hD : 0<D.width) (S : List (List Nat)) (e : MExp) (q : Nat) :
    transition D S e q<D.width := Nat.mod_lt _ hD

theorem summary_correct (D : Machine) (hD : D.Valid) (S : List (List Nat)) (E : List (List Char))
    (hS : ∀ (k : Nat) (w : List Char), E[k]?=some w → S[k]?=some (profile D w)) :
    ∀ e, WordArguments.Word e → ∀ w, WordArguments.value E e=some w → summary D S e=some (profile D w)
  | .lit u, _, w, hv => by cases hv; rfl
  | .param k, _, w, hv => hS k w hv
  | .seq a b, he, w, hv => by
    cases ha : WordArguments.value E a with
    | none => simp [WordArguments.value,ha] at hv
    | some u => cases hb : WordArguments.value E b with
      | none => simp [WordArguments.value,ha,hb] at hv
      | some v =>
        have hw : u++v=w := by simpa only [WordArguments.value,ha,hb,Option.bind_some,Option.map_some,Option.some.injEq] using hv
        rw [summary,summary_correct D hD S E hS a he.1 u ha,summary_correct D hD S E hS b he.2 v hb]
        simp only [Option.bind_some,Option.map_some,CaptureTransitionProfile.compose_correct D hD u v,hw]
  | .eps, he, _, _ | .any, he, _, _ | .chr _, he, _, _ | .range _ _, he, _, _ | .call _ _, he, _, _
  | .alt _ _, he, _, _ | .star _, he, _, _ | .notP _, he, _, _ | .dbg _, he, _, _ | .lam _ _, he, _, _
  | .callParam _ _, he, _, _ | .invoke _ _ _, he, _, _ => False.elim he

theorem step_correct (D : Machine) (hD : D.Valid) (S : List (List Nat)) (E : List (List Char))
    (hS : ∀ (k : Nat) (w : List Char), E[k]?=some w → S[k]?=some (profile D w))
    (g : MGrammar) (x : List Char) (s : Strategy) (T : Table) (e : MExp) (he : WordArguments.Word e)
    (q p j : Nat) (hq : q<D.width) (hp : p≤x.length) (hv : evV g x s T E e p=some (some j)) :
    transition D S e q=run D q (pre x p j) := by
  have hw := WordArguments.value_of_success g x s T E e he p j hp hv
  simp only [transition,summary_correct D hD S E hS e he _ hw,Option.bind_some,
    CaptureTransitionProfile.profile_get D _ q hq,Option.getD_some]
  exact Nat.mod_eq_of_lt (run_bound hD q hq _)

theorem success_prefix {g : MGrammar} {x : List Char} {s : Strategy} {T : Table}
    (hs : s≠.callByName) (hT : SoundTV g x s T) (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (p j : Nat) (hp : p≤x.length) (hv : evV g x s T E e p=some (some j)) :
    j≤x.length ∧ sfx x p=pre x p j++sfx x j := by
  have hf : (MExp.subst (E.map MExp.lit) e).FirstOrder := firstOrder_subst (firstOrderArgs_lits E) e he
  have hv' : evV g x s T [] (MExp.subst (E.map MExp.lit) e) p=some (some j) := by
    rw [evV_subst E e he]; exact hv
  obtain ⟨o,hd,ho⟩ := evV_sound hs hT _ hf p hp _ hv'
  obtain ⟨t,rest,rfl,hj⟩ := obsR_ok ho
  have hpre := mderives_suffix hd _ _ rfl
  have hr := rest_eq_sfx' hd
  rw [hj] at hr
  have hlen : j≤x.length := by
    obtain ⟨w,hw⟩ := hpre
    have hl := congrArg List.length hw
    rw [List.length_append,length_sfx x hp,hj] at hl
    omega
  refine ⟨hlen,?_⟩
  rw [hr]
  simpa [hj] using pre_split hp hpre

theorem trace_run (D : Machine) (_hD : D.Valid) (f : Nat → Nat)
    (hf : ∀ q, q<D.width → f q<D.width)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder)
    (hstep : ∀ q p j, q<D.width → p≤x.length → evV g x s T E e p=some (some j) → f q=run D q (pre x p j))
    {p n j : Nat} (ht : InlineRepeat.Trace (fun z => evV g x s T E e z) p n j)
    (hend : evV g x s T E e j=some none) :
    ∀ q, q<D.width → p≤x.length → run D q (pre x p j)=CaptureOrbit.orbit f q n := by
  induction ht with
  | zero p => intro q _ _; simp [pre,CaptureOrbit.orbit,run]
  | @succ p z n j hv hz tail ih =>
    intro q hq hp
    have hz' := success_prefix hs hT E e he p z hp hv
    have hj := success_prefix hs hT E (.star e) he z j hz'.1 (InlineRepeat.trace_star tail hend)
    rw [SequenceArguments.pre_concat hp hj.1 hz'.2 hj.2,run_append,←hstep q p z hq hp hv,
      ih hend (f q) (hf q hq) hz'.1]
    have hh := CaptureOrbit.orbit_add f q 1 n
    simpa only [CaptureOrbit.orbit,Nat.add_comm] using hh.symm

theorem filter_firstOrder (D : Machine) (S : List (List Nat)) (e : MExp) (he : e.FirstOrder) (q r : Nat) :
    (filter D S e q r).FirstOrder := by
  refine ⟨he,?_⟩
  apply choice_firstOrder
  intro a ha
  obtain ⟨⟨k,l⟩,_,rfl⟩ := List.mem_map.mp ha
  exact InlineRepeat.pattern_firstOrder e he k l

/-- Complete filtered results for retained Word repetition. The only state
information used by the generated syntax is finite incoming metadata. -/
theorem correct (D : Machine) (hD : D.Valid) (S : List (List Nat)) (E : List (List Char))
    (hS : ∀ (k : Nat) (w : List Char), E[k]?=some w → S[k]?=some (profile D w))
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (e : MExp) (he : WordArguments.Word e) (p : Nat) (hp : p≤x.length)
    (q r : Nat) (hq : q<D.width) :
    evV g x s T E (filter D S e q r) p=filtered D x q r p (evV g x s T E (.star e) p) := by
  change (match evV g x s T E (.andP (.star e)) p with
    | some (some z) => evV g x s T E (choice _) z | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV g x s T E (.star e) p with
  | none => rfl
  | some result => cases result with
    | none => exact False.elim (evStar_ne_fail p hv)
    | some j =>
      dsimp only [CallLookahead.peek]
      obtain ⟨n,ht,hend⟩ := InlineRepeat.star_trace (fun z => evV g x s T E e z) p j hv
      have hb := fun q (_ : q<D.width) => transition_bound D hD.1 S e q
      have hrun := trace_run D hD (transition D S e) hb g x s hs T hT E e (WordArguments.word_firstOrder e he)
        (fun q p j hq hp hv => step_correct D hD S E hS g x s T e he q p j hq hp hv) ht hend q hq hp
      simp only [filtered,hrun]
      by_cases hr : CaptureOrbit.orbit (transition D S e) q n=r
      · rw [if_pos hr]
        apply InlineRepeat.choice_success g x s T E e p n j ht hend
        rw [←hr]
        exact CaptureOrbit.descriptors_complete _ _ hb q hq n
      · rw [if_neg hr]
        apply CaptureTransitionProfile.choice_failed
        intro kl hkl
        apply InlineRepeat.pattern_fail g x s T E e kl.1 kl.2 p n j ht hend
        intro hn
        exact hr (CaptureOrbit.descriptors_sound _ _ q r kl.1 kl.2 n hkl hn)

theorem word_safe (n : Nat) : ∀ e, WordArguments.Word e → FilteredOverlapCaller.Tail n e
  | .lit _, _ | .param _, _ => True.intro
  | .seq a b, h => ⟨word_safe n a h.1,word_safe n b h.2⟩
  | .eps, h | .any, h | .chr _, h | .range _ _, h | .call _ _, h | .alt _ _, h | .star _, h | .notP _, h
  | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => False.elim h

theorem copies_safe (n : Nat) (e : MExp) (he : FilteredOverlapCaller.Tail n e) :
    ∀ k, FilteredOverlapCaller.Tail n (InlineRepeat.copies e k)
  | 0 => True.intro
  | k+1 => ⟨he,copies_safe n e he k⟩

theorem pattern_safe (n : Nat) (e : MExp) (he : FilteredOverlapCaller.Tail n e) (k l : Nat) :
    FilteredOverlapCaller.Tail n (InlineRepeat.pattern e k l) := by
  refine ⟨copies_safe n e he k,?_,he⟩
  split
  · trivial
  · exact copies_safe n e he l

theorem choice_safe (n : Nat) : ∀ es, (∀ e∈es, FilteredOverlapCaller.Tail n e) → FilteredOverlapCaller.Tail n (choice es)
  | [], _ => True.intro
  | e::es, h => ⟨h e (by simp),choice_safe n es (fun e he => h e (by simp [he]))⟩

theorem filter_safe (n : Nat) (D : Machine) (S : List (List Nat)) (e : MExp)
    (he : FilteredOverlapCaller.Tail n e) (q r : Nat) : FilteredOverlapCaller.Tail n (filter D S e q r) := by
  refine ⟨he,?_⟩
  apply choice_safe
  intro a ha
  obtain ⟨⟨k,l⟩,_,rfl⟩ := List.mem_map.mp ha
  exact pattern_safe n e he k l

end Shallot.MacroPeg.CBV.WordStarFilter
