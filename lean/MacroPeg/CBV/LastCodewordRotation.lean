import MacroPeg.CBV.GreedyRotation
import MacroPeg.CBV.CallLookahead
import MacroPeg.CBV.InlineRepeat

/-! Leave the last successful header outside a greedy capture. The capture
may contain an input-dependent number of headers, including zero. -/
namespace Shallot.MacroPeg.CBV.LastCodewordRotation
open ContinuationPlan (sequence)
open GreedyRotation (negative Decreasing)
open CallLookahead (peek)

def step (A : Nat → Res) : Nat → Res := sequence A (fun q => peek q (A q))

def argument (A : MExp) : MExp := .star (.seq A (.andP A))

theorem star_stop_test (A : Nat → Res) : ∀ p,
    sequence (evStar A) (negative A) p=evStar A p := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
    cases ha : A p with
    | none => simp only [sequence,evStar_none ha]
    | some result => cases result with
      | none => simp only [sequence,evStar_fail ha,negative,ha]
      | some j =>
        by_cases hj : j<p
        · change (match evStar A p with | some (some z) => negative A z | other => other)=_
          rw [evStar_ok ha hj]
          exact ih j hj
        · simp only [sequence,evStar_stuck ha hj]

/-- `(A &A)* A = A A*` with full partial results. Empty successes still
loop, and a later undefined header is never turned into a finite stop. -/
theorem rotate (n : Nat) (A : Nat → Res) (hA : Decreasing n A) (p : Nat) (hp : p≤n) :
    sequence (evStar (step A)) A p=sequence A (evStar A) p := by
  have hpeek : Decreasing n (fun q => peek q (A q)) := by
    intro q hq j hj
    cases ha : A q with
    | none => simp [peek,ha] at hj
    | some result => cases result with
      | none => simp [peek,ha] at hj
      | some k =>
        have he : q=j := by simpa [peek,ha] using hj
        omega
  have hbefore : sequence (fun q => peek q (A q)) A=A := by
    funext q
    cases ha : A q with
    | none => simp [sequence,peek,ha]
    | some result => cases result <;> simp [sequence,peek,ha]
  have hnot : negative (fun q => peek q (A q))=negative A := by
    funext q
    cases ha : A q with
    | none => simp [negative,peek,ha]
    | some result => cases result <;> simp [negative,peek,ha]
  have hh := GreedyRotation.rotate n A (fun q => peek q (A q)) hA hpeek p hp
  rw [hbefore,hnot] at hh
  change sequence (evStar (step A)) A p=_ at hh
  rw [hh]
  have hs : sequence (evStar A) (negative A)=evStar A := funext (star_stop_test A)
  rw [hs]

theorem expression_rotation (g : MGrammar) (x : List Char) (s : Strategy) (hs : s≠.callByName)
    (T : ClockFreezing.Table) (hT : SoundTV g x s T) (E : List (List Char))
    (A : MExp) (hA : A.FirstOrder) (p : Nat) (hp : p≤x.length) :
    evV g x s T E (.seq (argument A) A) p=
      evV g x s T E (.seq A (.star A)) p := by
  have he : (fun q => evV g x s T E (.seq A (.andP A)) q)=
      step (fun q => evV g x s T E A q) := by
    funext q
    change (match evV g x s T E A q with
      | some (some j) => evV g x s T E (.andP A) j | other => other)=_
    simp only [CallLookahead.evV_peek,step,sequence]
    rfl
  change sequence (evStar (fun q => evV g x s T E (.seq A (.andP A)) q))
      (fun q => evV g x s T E A q) p=_
  rw [he]
  exact rotate x.length _ (GreedyRotation.evaluator_decreasing g x s hs T hT E A hA) p hp

theorem argument_eval (g : MGrammar) (x : List Char) (s : Strategy)
    (T : ClockFreezing.Table) (E : List (List Char)) (A : MExp) (p : Nat) :
    evV g x s T E (argument A) p=evStar (step (fun q => evV g x s T E A q)) p := by
  apply evStar_congr p
  intro q hq
  change (match evV g x s T E A q with
    | some (some j) => evV g x s T E (.andP A) j | other => other)=_
  simp only [CallLookahead.evV_peek,step,sequence]
  rfl

theorem step_success (A : Nat → Res) (p q : Nat) (h : step A p=some (some q)) :
    A p=some (some q) := by
  cases ha : A p with
  | none => simp [step,sequence,ha] at h
  | some result => cases result with
    | none => simp [step,sequence,ha] at h
    | some j =>
      cases hb : A j with
      | none => simp [step,sequence,ha,hb,peek] at h
      | some result => cases result with
        | none => simp [step,sequence,ha,hb,peek] at h
        | some k => have he : j=q := by simpa [step,sequence,ha,hb,peek] using h
                    rw [he]

theorem step_trace {A : Nat → Res} {p n q : Nat} (h : InlineRepeat.Trace (step A) p n q) :
    InlineRepeat.Trace A p n q := by
  induction h with
  | zero p => exact .zero p
  | succ hv hz tail ih => exact .succ (step_success A _ _ hv) hz ih

/-- A successful last-preserving capture ends where the header is defined.
If there is no final header, the capture is empty and the first header
itself finitely fails. Otherwise the final header is followed by failure. -/
theorem capture_endpoint (A : Nat → Res) (p q : Nat)
    (h : evStar (step A) p=some (some q)) :
    (q=p ∧ A q=some none) ∨ ∃ r, A q=some (some r) ∧ A r=some none := by
  obtain ⟨n,ht,hstop⟩ := InlineRepeat.star_trace (step A) p q h
  have hend : A q=some none ∨ ∃ r, A q=some (some r) ∧ A r=some none := by
    cases ha : A q with
    | none => simp [step,sequence,ha] at hstop
    | some result => cases result with
      | none => exact Or.inl rfl
      | some r =>
        have hr : A r=some none := by
          cases hb : A r with
          | none => simp [step,sequence,peek,ha,hb] at hstop
          | some result => cases result with
            | none => rfl
            | some j => simp [step,sequence,peek,ha,hb] at hstop
        exact Or.inr ⟨r,rfl,hr⟩
  rcases hend with hend | hend
  · have hzero : q=p := by
      revert hend
      induction ht with
      | zero => intro _; rfl
      | @succ p z n q hv hz tail ih =>
        intro hend
        have hzq := ih (InlineRepeat.trace_star tail hstop) hstop hend
        have hz' : A z=some none := hzq ▸ hend
        cases ha : A p with
        | none => simp [step,sequence,ha] at hv
        | some result => cases result with
          | none => simp [step,sequence,ha] at hv
          | some j =>
            cases hb : A j with
            | none => simp [step,sequence,ha,hb,peek] at hv
            | some result => cases result with
              | none => simp [step,sequence,ha,hb,peek] at hv
              | some k =>
                have hj : j=z := by simpa [step,sequence,ha,hb,peek] using hv
                subst j
                rw [hz'] at hb
                cases hb
    exact Or.inl ⟨hzero,hend⟩
  · exact Or.inr hend


/-- Every finite maximal nonempty header run has a last-preserving
capture with exactly one fewer iterations. The iteration count is not a
parameter of either parser. -/
theorem last_trace (A : Nat → Res) : ∀ n p r,
    InlineRepeat.Trace A p (n+1) r → A r=some none →
    ∃ q, InlineRepeat.Trace (step A) p n q ∧ A q=some (some r) ∧
      evStar (step A) p=some (some q) := by
  intro n
  induction n with
  | zero =>
    intro p r ht hend
    cases ht with
    | succ hv hz tail =>
      cases tail
      have hh : step A p=some none := by simp [step,sequence,hv,hend,peek]
      exact ⟨p,.zero p,hv,evStar_fail hh⟩
  | succ n ih =>
    intro p r ht hend
    cases ht with
    | @succ _ z _ _ hv hz tail =>
      obtain ⟨q,htrace,hq,hstar⟩ := ih z r tail hend
      have hdefined : ∃ j, A z=some (some j) := by cases tail with | succ h _ _ => exact ⟨_,h⟩
      obtain ⟨j,hj⟩ := hdefined
      have hh : step A p=some (some z) := by simp [step,sequence,hv,hj,peek]
      exact ⟨q,.succ hh hz htrace,hq,(evStar_ok hh hz).trans hstar⟩

end Shallot.MacroPeg.CBV.LastCodewordRotation
