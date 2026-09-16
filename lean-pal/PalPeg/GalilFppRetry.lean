import PalPeg.GalilFppCompare
import PalPeg.GalilFppDeltaTape
import PalPeg.GalilFppFailure

set_option autoImplicit false
namespace PalPeg.GalilFppRetry
open GalilFppInstruction GalilFppCode GalilFppMaterialize GalilFppFallbackBits
open GalilFppDelta GalilFppDeltaTape GalilFppCompare
variable {α : Type} [DecidableEq α]

/-- Reusable data invariant at a comparison retry; PC is kept separate. -/
def Ready (w : List α) (p : ℕ) (x : Config) : Prop :=
  x.pos 0 = p ∧ StackAt (x.tape 4) (x.pos 4) [] ∧
  x.pos 3 = p-failure w p ∧ Unary (x.tape 3) (x.pos 3) ∧
  x.pos 2 = position (failure w) p ∧ Tape (x.tape 2) (failure w) p

/-- One failed non-leftmost comparison, including the real fallback,
returns to retry with the same invariant at the strictly smaller candidate. -/
theorem miss_retry (j : Fin 4) (a : Fin 5) (old : Fin 4) (w : List α)
    (p : ℕ) (x : Config) (q : List (Fin 2)) (hp : x.pc = 68+offset j)
    (hpos : 0 < p) (ha : a.val ≠ j.val)
    (hc : x.tape 0 (x.pos 0+1) = symbol a)
    (hold : x.tape 0 (x.pos 0) = previousSymbol (some old))
    (hr : Ready w p x) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length ≤ 20*(p-failure w p)+9 ∧
      y.pc = 68+offset j ∧ Ready w (failure w p) y ∧
      QueueAt y (q ++ List.replicate (p-failure w p) 1) ∧
      y.tape 0 = x.tape 0 ∧ y.tape 1 = x.tape 1 ∧ failure w p < p ∧ y.tape 2 = x.tape 2 ∧
      y.pos 1 = x.pos 1 := by
  obtain ⟨hA, hT, hS, hu, hC, hTape⟩ := hr
  let z : Config := { x with pc := 97+offset j }
  have hm : Steps code x [68+offset j,67+offset j,106+offset j,105+offset j] z :=
    retry_mismatch j a (some old) x hp ha hc hold
  have hus : Unary (x.tape 3) (p-failure w p) := by simpa [hS] using hu
  obtain ⟨y, qs, hs, hl, hpc, hyA, hyS, hyC, hyCt, hyT, hyq, hyu, hyTape, hyB⟩ :=
    fallback_failure j w p z q rfl hA hT hS hus.1 hus.2.2 hus.2.1 hC hTape hq
  have hall := GalilFppCopy.steps_append hm hs
  obtain ⟨htA, htB⟩ := input_tapes hall
  have hf := failure_le w p
  refine ⟨y, [68+offset j,67+offset j,106+offset j,105+offset j] ++ qs,
    hall, ?_, hpc, ⟨hyA, hyT, hyS, hyu, hyC, hyTape⟩, hyq, htA, htB, by omega, hyCt, hyB⟩
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

def letter (j : Fin 4) : Fin 9 := ⟨j.val, by omega⟩

/-- The finite input alphabet and left-end layout at candidate positions. -/
def ValidInput (t : ℕ → Fin 9) (p : ℕ) : Prop :=
  (∀ k, k ≤ p → ∃ a : Fin 5, t (k+1) = symbol a) ∧
  (∀ k, 0 < k → k ≤ p → ∃ a : Fin 4, t k = previousSymbol (some a))

theorem symbol_letter (a : Fin 5) (j : Fin 4) : symbol a = letter j ↔ a.val = j.val := by
  fin_cases a <;> fin_cases j <;> decide

inductive Skipped (w : List α) (j : Fin 4) (t : ℕ → Fin 9) : ℕ → ℕ → Prop
  | refl (p : ℕ) : Skipped w j t p p
  | step (p r : ℕ) (hp : 0 < p) (hm : t (p+1) ≠ letter j)
      (rest : Skipped w j t (failure w p) r) : Skipped w j t p r

/-- All failed retries compose to a finite actual execution. The total
cost is linear in the distance traversed, not in an assumed trace length.
The final candidate is either zero or has the required next character. -/
theorem search (j : Fin 4) (w : List α) (p : ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 68+offset j) (hr : Ready w p x) (hq : QueueAt x q)
    (hv : ValidInput (x.tape 0) p) :
    ∃ r y qs, r ≤ p ∧ Steps code x qs y ∧ qs.length ≤ 29*(p-r) ∧
      y.pc = 68+offset j ∧ Ready w r y ∧
      QueueAt y (q ++ List.replicate (p-r) 1) ∧
      (r = 0 ∨ y.tape 0 (r+1) = letter j) ∧ Skipped w j (x.tape 0) p r ∧ y.tape 2 = x.tape 2 ∧
      y.pos 1 = x.pos 1 := by
  induction p using Nat.strong_induction_on generalizing x q with
  | h p ih =>
    by_cases hstop : p = 0 ∨ x.tape 0 (p+1) = letter j
    · exact ⟨p, x, [], le_refl _, .nil _, by simp, hp, hr, by simpa using hq, hstop, .refl p, rfl, rfl⟩
    · have hpos : 0 < p := by omega
      have hmiss : x.tape 0 (p+1) ≠ letter j := by tauto
      obtain ⟨a, ha⟩ := hv.1 p (le_refl _)
      obtain ⟨old, hold⟩ := hv.2 p hpos (le_refl _)
      have hneq : a.val ≠ j.val := by
        intro he
        exact hmiss (ha.trans ((symbol_letter a j).mpr he))
      obtain ⟨z, qs, hs, hl, hzpc, hzr, hzq, hAt, _, hlt, hCt, hzB⟩ :=
        miss_retry j a old w p x q hp hpos hneq (by simpa [hr.1] using ha)
          (by simpa [hr.1] using hold) hr hq
      have hzv : ValidInput (z.tape 0) (failure w p) := by
        rw [hAt]
        exact ⟨fun k hk => hv.1 k (by omega), fun k hk hk' => hv.2 k hk (by omega)⟩
      obtain ⟨r, y, rs, hrp, hrun, hlen, hypc, hyr, hyq, hterminal, hpath, hCt', hyB⟩ :=
        ih (failure w p) hlt z (q ++ List.replicate (p-failure w p) 1) hzpc hzr hzq hzv
      refine ⟨r, y, qs ++ rs, by omega, GalilFppCopy.steps_append hs hrun,
        ?_, hypc, hyr, ?_, hterminal, .step p r hpos hmiss (by simpa [hAt] using hpath),
        hCt'.trans hCt, hyB.trans hzB⟩
      · simp only [List.length_append]
        omega
      · have hd : p-failure w p + (failure w p-r) = p-r := by omega
        simpa [List.append_assoc, ← List.replicate_add, hd] using hyq

/-- Left-end mismatch completes the input's generation branch: the actual
comparison and two pushes append 10 and return to the B-advance PC. -/
theorem zero_miss (j : Fin 4) (a : Fin 5) (w : List α) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 68+offset j) (ha : a.val ≠ j.val)
    (hc : x.tape 0 1 = symbol a) (hleft : x.tape 0 0 = 4)
    (hr : Ready w 0 x) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 8 ∧ y.pc = 38 ∧ Ready w 0 y ∧
      QueueAt y (q ++ [1,0]) ∧ y.tape 0 = x.tape 0 ∧ y.tape 1 = x.tape 1 ∧
      y.tape 2 = x.tape 2 ∧ y.pos 1 = x.pos 1 := by
  let z : Config := { x with pc := 66 }
  let u := GalilFppEnqueue.pushed 1 64 z
  let v := GalilFppEnqueue.pushed 0 38 u
  have hm : Steps code x [68+offset j,67+offset j,106+offset j,105+offset j] z :=
    retry_mismatch j a none x hp ha (by simpa [hr.1] using hc)
      (by simpa [hr.1, previousSymbol] using hleft)
  have h₁ : Steps code z [66,65] u := GalilFppEnqueue.push_steps 2 z rfl
  have h₂ : Steps code u [64,63] v := GalilFppEnqueue.push_steps 1 u rfl
  have hqz : QueueAt z q := hq
  have hqu : QueueAt u (q ++ [1]) := GalilFppEnqueue.pushed_queue 1 64 z q hqz
  have hqv : QueueAt v ((q ++ [1]) ++ [0]) := GalilFppEnqueue.pushed_queue 0 38 u _ hqu
  have hall := GalilFppCopy.steps_append (GalilFppCopy.steps_append hm h₁) h₂
  obtain ⟨htA, htB⟩ := input_tapes hall
  refine ⟨v, _, hall, rfl, rfl, ?_, ?_, htA, htB, ?_, ?_⟩
  · simpa [Ready, v, u, z, GalilFppEnqueue.pushed] using hr
  · simpa [List.append_assoc] using hqv
  · simp [v, u, z, GalilFppEnqueue.pushed]
  · simp [v, u, z, GalilFppEnqueue.pushed]

/-- Search and terminal dispatch together: reach either the matched
branch with an advanced A head, or complete a left-end failure. -/
theorem search_dispatch (j : Fin 4) (w : List α) (p : ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 68+offset j) (hr : Ready w p x) (hq : QueueAt x q)
    (hv : ValidInput (x.tape 0) p) (hleft : x.tape 0 0 = 4) :
    ∃ r y qs, r ≤ p ∧ Steps code x qs y ∧ qs.length ≤ 29*(p-r)+8 ∧
      ((y.pc = 62 ∧ y.pos 0 = r+1 ∧
        Ready w r { y with pos := Function.update y.pos 0 r } ∧
        QueueAt y (q ++ List.replicate (p-r) 1)) ∨
       (r = 0 ∧ y.pc = 38 ∧ Ready w 0 y ∧
        QueueAt y ((q ++ List.replicate p 1) ++ [1,0]))) := by
  obtain ⟨r, z, qs, hrp, hs, hl, hzpc, hzr, hzq, hstop, _⟩ := search j w p x q hp hr hq hv
  by_cases hhit : z.tape 0 (r+1) = letter j
  · let y : Config := { z with pc := 62, pos := Function.update z.pos 0 (z.pos 0+1) }
    have hh : Steps code z [68+offset j,67+offset j] y :=
      retry_hit j z hzpc (by simpa [hzr.1, letter] using hhit)
    refine ⟨r, y, qs ++ [68+offset j,67+offset j], hrp, GalilFppCopy.steps_append hs hh,
      ?_, Or.inl ⟨rfl, ?_, ?_, ?_⟩⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp [y, hzr.1]
    · simpa [Ready, y, hzr.1] using hzr
    · simpa [QueueAt, y] using hzq
  · have hrzero : r = 0 := hstop.resolve_right hhit
    subst r
    obtain ⟨hAt, _⟩ := input_tapes hs
    obtain ⟨a, ha⟩ := hv.1 0 (by omega)
    have hchar : z.tape 0 1 = symbol a := by rw [hAt]; simpa using ha
    have hneq : a.val ≠ j.val := by
      intro he
      exact hhit (hchar.trans ((symbol_letter a j).mpr he))
    obtain ⟨y, rs, hrun, hlen, hypc, hyr, hyq, _, _⟩ :=
      zero_miss j a w z (q ++ List.replicate (p-0) 1) hzpc hneq hchar
        (by rw [hAt]; exact hleft) hzr hzq
    refine ⟨0, y, qs ++ rs, by omega, GalilFppCopy.steps_append hs hrun,
      ?_, Or.inr ⟨rfl, hypc, hyr, ?_⟩⟩
    · simp only [List.length_append]; omega
    · simpa using hyq

/-- A real skipped-candidate trace preserves the reference seek result
when the input tape's comparisons agree with the reference word. -/
theorem skipped_seek (w : List α) (a : α) (j : Fin 4) (t : ℕ → Fin 9) (p r : ℕ)
    (hs : Skipped w j t p r)
    (hc : ∀ k, k ≤ p → (t (k+1) = letter j ↔ w[k]? = some a)) :
    GalilFppFailure.seek w a p = GalilFppFailure.seek w a r := by
  induction hs with
  | refl => rfl
  | step p r hp hm hs ih =>
    have hn : w[p]? ≠ some a := fun h => hm ((hc p (le_refl _)).mpr h)
    rw [GalilFppFailure.seek, if_neg hn, if_neg (show p ≠ 0 by omega)]
    apply ih
    intro k hk
    have hf := failure_le w p
    exact hc k (by omega)

/-- The semantic result at the actual search endpoint: the next failure
length is r+1 on a hit, and zero on the left-end miss. -/
theorem endpoint_failure (w : List α) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
    (j : Fin 4) (t : ℕ → Fin 9) (r : ℕ) (hr : r ≤ failure w N)
    (hpath : Skipped w j t (failure w N) r)
    (hstop : r = 0 ∨ t (r+1) = letter j)
    (hc : ∀ k, k ≤ failure w N → (t (k+1) = letter j ↔ w[k]? = some w[N])) :
    failure w (N+1) = if t (r+1) = letter j then r+1 else 0 := by
  have hs := skipped_seek w w[N] j t (failure w N) r hpath hc
  rw [GalilFppFailure.failure_step w N hN hw] at hs
  rw [hs, GalilFppFailure.seek]
  by_cases hh : t (r+1) = letter j
  · simp [hh, (hc r hr).mp hh]
  · have hz : r = 0 := hstop.resolve_right hh
    have hn : w[r]? ≠ some w[N] := fun h => hh ((hc r hr).mpr h)
    simp only [if_neg hn, if_neg hh, if_pos hz]

#print axioms endpoint_failure
#print axioms search_dispatch
#print axioms zero_miss
#print axioms search
#print axioms miss_retry
end PalPeg.GalilFppRetry
