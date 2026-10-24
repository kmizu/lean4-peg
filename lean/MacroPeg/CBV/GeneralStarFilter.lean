import MacroPeg.CBV.FirstReturn

/-! State filtering of arbitrary partial PEG repetition. Every original
iteration may consume a different word; no captured parameter is transferred. -/
namespace Shallot.MacroPeg.CBV.GeneralStarFilter
open RegularCaptureProduct
open ClockFreezing (Table)

def filter (W : Nat) (e : MExp) (F : Nat → Nat → MExp) (q r : Nat) : MExp :=
  .seq (.andP (.star e)) (FirstReturn.finished W F e q r)

theorem lift_trace (D : Machine) (hD : D.Valid)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (F : Nat → Nat → MExp)
    (hF : ∀ q r p, q<D.width → r<D.width → p≤x.length →
      evV g x s T E (F q r) p=filtered D x q r p (evV g x s T E e p))
    {p n j : Nat} (ht : InlineRepeat.Trace (fun p => evV g x s T E e p) p n j)
    (hend : evV g x s T E e j=some none) :
    ∀ q, q<D.width → p≤x.length → ∃ tail,
      FirstReturn.Run (fun q r p => evV g x s T E (F q r) p) D.width ((q,p)::tail) ∧
      FirstReturn.Source (fun p => evV g x s T E e p) ((q,p)::tail) ∧
      FirstReturn.Ends ((q,p)::tail) (run D q (pre x p j)) j := by
  induction ht with
  | zero p =>
    intro q hq hp
    refine ⟨[],.last q p hq ?_,hend,?_⟩
    · intro r hr
      rw [hF q r p hq hr hp,hend]
      rfl
    · simp [FirstReturn.Ends,pre,run]
  | @succ p z n j hv hz tail ih =>
    intro q hq hp
    have hz' := WordStarFilter.success_prefix hs hT E e he p z hp hv
    have hj := WordStarFilter.success_prefix hs hT E (.star e) he z j hz'.1 (InlineRepeat.trace_star tail hend)
    let t := run D q (pre x p z)
    have ht : t<D.width := run_bound hD q hq _
    obtain ⟨rest,hRun,hSource,hEnd⟩ := ih hend t ht hz'.1
    refine ⟨(t,z)::rest,.cons q p t z rest hq hz ?_ hRun,⟨hv,hSource⟩,?_⟩
    · intro r hr
      rw [hF q r p hq hr hp,hv]
      change (if t=r then some (some z) else some none)=(if r=t then some (some z) else some none)
      by_cases he : r=t
      · simp only [he,ite_true]
      · simp only [if_neg he,if_neg (Ne.symm he)]
    · change FirstReturn.Ends ((t,z)::rest) (run D q (pre x p j)) j
      rw [SequenceArguments.pre_concat hp hj.1 hz'.2 hj.2,run_append]
      exact hEnd

/-- Complete partial-result correctness for star follows from correctness
of the one-step filters, with no uniform-word or non-nullability premise. -/
theorem correct (D : Machine) (hD : D.Valid)
    (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName) (T : Table) (hT : SoundTV g x s T)
    (E : List (List Char)) (e : MExp) (he : e.FirstOrder) (F : Nat → Nat → MExp)
    (hF : ∀ q r p, q<D.width → r<D.width → p≤x.length →
      evV g x s T E (F q r) p=filtered D x q r p (evV g x s T E e p))
    (q r p : Nat) (hq : q<D.width) (hp : p≤x.length) :
    evV g x s T E (filter D.width e F q r) p=filtered D x q r p (evV g x s T E (.star e) p) := by
  change (match evV g x s T E (.andP (.star e)) p with
    | some (some j) => evV g x s T E (FirstReturn.finished D.width F e q r) j | other => other)=_
  rw [CallLookahead.evV_peek]
  cases hv : evV g x s T E (.star e) p with
  | none => rfl
  | some result => cases result with
    | none => exact False.elim (evStar_ne_fail p hv)
    | some j =>
      dsimp only [CallLookahead.peek]
      obtain ⟨n,ht,hend⟩ := InlineRepeat.star_trace (fun p => evV g x s T E e p) p j hv
      obtain ⟨tail,hRun,hSource,hEnd⟩ := lift_trace D hD g x s hs T hT E e he F hF ht hend q hq hp
      exact FirstReturn.finished_correct g x s T E D.width F e q r p tail hRun hSource _ j hEnd

theorem filter_firstOrder (W : Nat) (e : MExp) (he : e.FirstOrder) (F : Nat → Nat → MExp)
    (hF : ∀ q r, (F q r).FirstOrder) (q r : Nat) : (filter W e F q r).FirstOrder :=
  ⟨he,FirstReturn.finished_firstOrder W F hF e he q r⟩

theorem filter_safe (n W : Nat) (e : MExp) (he : FilteredOverlapCaller.Tail n e) (F : Nat → Nat → MExp)
    (hF : ∀ q r, q<W → r<W → FilteredOverlapCaller.Tail n (F q r)) (q r : Nat) (hq : q<W) (hr : r<W) :
    FilteredOverlapCaller.Tail n (filter W e F q r) :=
  ⟨he,FirstReturn.finished_safe n W F hF e he q r hq hr⟩

end Shallot.MacroPeg.CBV.GeneralStarFilter
