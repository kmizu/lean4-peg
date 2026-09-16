import PalPeg.GalilFppFallbackBits
import PalPeg.GalilFppCopyInstances

set_option autoImplicit false
namespace PalPeg.GalilFppFallbackLoop
open GalilFppInstruction GalilFppCode GalilFppCopy GalilFppMaterialize GalilFppEnqueue GalilFppFallbackBits

def beginScan (j : Fin 4) (x : Config) : Config :=
  { x with pc := 70+offset j, pos := Function.update x.pos 2 (x.pos 2 - 1) }

theorem enter_scan (j : Fin 4) (x : Config) (hp : x.pc = 69+offset j)
    (hT : x.tape 4 (x.pos 4) = 8) (hC : 0 < x.pos 2) :
    Steps code x [69+offset j,96+offset j] (beginScan j x) := by
  let y : Config := { x with pc := 96+offset j }
  have hi : code[x.pc]? = some (.read 4 [(4,68+offset j),(8,96+offset j)]) := by
    rw [hp]; fin_cases j <;> rfl
  have he : Execute (.read 4 [(4,68+offset j),(8,96+offset j)]) x y :=
    .read _ _ _ _ (by simp [hT])
  have hi' : code[y.pc]? = some (.move 2 false (70+offset j)) := by fin_cases j <;> rfl
  simpa only [hp] using Steps.step x y _ _ _ hi he
    (.step y (beginScan j x) _ _ [] hi' (.left _ _ _ hC) (.nil _))

theorem exit_scan (j : Fin 4) (x : Config) (hp : x.pc = 69+offset j)
    (hT : StackAt (x.tape 4) (x.pos 4) []) :
    Steps code x [69+offset j] { x with pc := 68+offset j } := by
  have hm : x.tape 4 (x.pos 4) = 4 := by rw [hT.1]; exact hT.2
  have hi : code[x.pc]? = some (.read 4 [(4,68+offset j),(8,96+offset j)]) := by
    rw [hp]; fin_cases j <;> rfl
  simpa only [hp] using Steps.step x { x with pc := 68+offset j } _ _ [] hi
    (.read _ _ _ _ (by simp [hm])) (.nil _)

theorem zero_stack (j : Fin 4) (x : Config) (ts : List (Fin 2))
    (hT : StackAt (x.tape 4) (x.pos 4) (1 :: ts)) :
    StackAt ((afterZero j x).tape 4) ((afterZero j x).pos 4) ts := by
  simp only [afterZero, pushed, Function.update_self,
    Function.update_of_ne (by decide : (4 : Fin 7) ≠ 5)]
  apply stack_congr hT.2.2
  intro k hk
  have hn : k ≠ x.pos 4 := by have := hT.1; omega
  simp [Function.update_of_ne hn]

/-- One complete fallback iteration crosses n ones and one delimiter.
It advances the outer loop, pops exactly one T cell, moves A once, and
appends exactly one FIFO distance bit. All four Scala instances are covered. -/
theorem iteration (j : Fin 4) (n : ℕ) (x : Config) (q ts : List (Fin 2))
    (hp : x.pc = 69+offset j) (hA : 0 < x.pos 0)
    (hT : StackAt (x.tape 4) (x.pos 4) (1 :: ts))
    (hS : n ≤ x.pos 3) (hC : n+1 ≤ x.pos 2)
    (hones : ∀ k, k < n → x.tape 2 (x.pos 2 - (k+1)) = 8)
    (hzero : x.tape 2 (x.pos 2 - (n+1)) = 7) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*n+9 ∧ y.pc = 69+offset j ∧
      y.pos 0 = x.pos 0 - 1 ∧ y.pos 3 = x.pos 3 - n ∧
      y.pos 2 = x.pos 2 - (n+1) ∧ y.tape 2 = x.tape 2 ∧
      StackAt (y.tape 4) (y.pos 4) ts ∧ QueueAt y (q ++ [1]) ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) ∧ y.pos 1 = x.pos 1 := by
  have he := enter_scan j x hp hT.2.1 (by omega)
  have hc : ∀ k, k < n → (beginScan j x).tape 2 ((beginScan j x).pos 2 - k) = 8 := by
    intro k hk
    have hh := hones k hk
    have heq : x.pos 2 - 1 - k = x.pos 2 - (k+1) := by omega
    simpa [beginScan, heq] using hh
  have hq' : QueueAt (beginScan j x) q := by simpa [QueueAt, beginScan] using hq
  obtain ⟨z, qs, hs, hl, hpc, hzs, hzc, hct, hzq, hframe, hunary⟩ :=
    ones_steps j n (beginScan j x) q rfl (by simpa [beginScan] using hS)
      (by simp [beginScan]; omega) hc hq'
  have hzA : z.pos 0 = x.pos 0 := by simpa [beginScan] using (hframe 0 (by decide) (by decide)).1
  have hzT : StackAt (z.tape 4) (z.pos 4) (1 :: ts) := by
    obtain ⟨htp, htt⟩ := hframe 4 (by decide) (by decide)
    simpa [htp, htt, beginScan] using hT
  have hzC : z.pos 2 = x.pos 2 - (n+1) := by simp [beginScan] at hzc; omega
  have hzbit : z.tape 2 (z.pos 2) = 7 := by rw [hct, hzC]; exact hzero
  have hz := zero_steps j z hpc hzbit (by omega) hzT.1
  refine ⟨afterZero j z,
    ([69+offset j,96+offset j] ++ qs) ++
      [70+offset j,95+offset j,75+offset j,74+offset j,73+offset j,72+offset j,71+offset j],
    steps_append (steps_append he hs) hz, ?_, rfl, ?_, ?_, ?_, ?_, zero_stack j z ts hzT, zero_queue j z q hzq, ?_, ?_⟩
  · simp [hl]
  · simpa [afterZero, pushed] using congrArg (fun k => k-1) hzA
  · simpa [afterZero, pushed, beginScan] using hzs
  · simpa [afterZero, pushed] using hzC
  · simpa [afterZero, pushed, beginScan] using hct
  · intro hu
    exact zero_unary j z (hunary (by simpa [beginScan] using hu))
  · simpa [afterZero, pushed, beginScan] using (hframe 1 (by decide) (by decide)).1

/-- Successive leftward groups of delta ones, each ending in a zero. -/
def Blocks (t : ℕ → Fin 9) : ℕ → List ℕ → Prop
  | _, [] => True
  | p, d :: ds => d+1 ≤ p ∧ (∀ k, k < d → t (p-(k+1)) = 8) ∧
      t (p-(d+1)) = 7 ∧ Blocks t (p-(d+1)) ds

/-- Complete actual append-distance fallback loop, from copied T to its
empty marker. It terminates after exactly 5Σd+9k+1 instructions and appends
exactly k ones. No eventual-termination premise is used. -/
theorem loop (j : Fin 4) (ds : List ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 69+offset j) (hA : ds.length ≤ x.pos 0)
    (hT : StackAt (x.tape 4) (x.pos 4) (List.replicate ds.length 1))
    (hS : ds.sum ≤ x.pos 3) (hC : Blocks (x.tape 2) (x.pos 2) ds) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*ds.sum+9*ds.length+1 ∧ y.pc = 68+offset j ∧
      y.pos 0 = x.pos 0 - ds.length ∧ y.pos 3 = x.pos 3 - ds.sum ∧
      y.pos 2 = x.pos 2 - (ds.sum+ds.length) ∧ y.tape 2 = x.tape 2 ∧
      StackAt (y.tape 4) (y.pos 4) [] ∧ QueueAt y (q ++ List.replicate ds.length 1) ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) ∧ y.pos 1 = x.pos 1 := by
  induction ds generalizing x q with
  | nil =>
    refine ⟨{ x with pc := 68+offset j }, [69+offset j], exit_scan j x hp hT,
      by simp, rfl, by simp, by simp, by simp, rfl, hT, ?_, id, rfl⟩
    simpa [QueueAt] using hq
  | cons d ds ih =>
    have hT' : StackAt (x.tape 4) (x.pos 4) (1 :: List.replicate ds.length 1) := by
      simpa [List.replicate_succ] using hT
    obtain ⟨z, qs, hs, hl, hzpc, hzA, hzS, hzC, hzt, hzT, hzq, hzu, hzB⟩ :=
      iteration j d x q (List.replicate ds.length 1) hp
        (by simp only [List.length_cons] at hA; omega) hT'
        (by simp only [List.sum_cons] at hS; omega) hC.1 hC.2.1 hC.2.2.1 hq
    have hAc : ds.length ≤ z.pos 0 := by simp only [List.length_cons] at hA; omega
    have hSc : ds.sum ≤ z.pos 3 := by simp only [List.sum_cons] at hS; omega
    have hCc : Blocks (z.tape 2) (z.pos 2) ds := by rw [hzt, hzC]; exact hC.2.2.2
    obtain ⟨y, rs, hr, hrl, hypc, hyA, hyS, hyC, hyt, hyT, hyq, hyu, hyB⟩ := ih z (q ++ [1]) hzpc hAc hzT hSc hCc hzq
    refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, ?_, ?_, ?_, hyt.trans hzt, hyT, ?_, hyu ∘ hzu, hyB.trans hzB⟩
    · simp only [List.length_append, List.sum_cons, List.length_cons]
      omega
    · simp only [List.length_cons]; omega
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons, List.length_cons]; omega
    · simpa [List.replicate_succ, List.append_assoc] using hyq

theorem stack_ones (t : ℕ → Fin 9) (n : ℕ) (hleft : t 0 = 4)
    (hones : ∀ k, 1 ≤ k → k ≤ n → t k = 8) :
    StackAt t n (List.replicate n 1) := by
  induction n with
  | zero => exact ⟨rfl, hleft⟩
  | succ n ih =>
    rw [List.replicate_succ]
    refine ⟨by omega, hones _ (by omega) (by omega), ?_⟩
    simpa using ih (fun k hk hn => hones k hk (by omega))

/-- Whole append-distance fallback, starting before copySToT with empty T.
The copied-T precondition is discharged by the actual copy instructions. -/
theorem fallback (j : Fin 4) (ds : List ℕ) (x : Config) (q : List (Fin 2))
    (hp : x.pc = 97+offset j) (hA : ds.length ≤ x.pos 0)
    (hT : StackAt (x.tape 4) (x.pos 4) [])
    (hS : x.pos 3 = ds.length) (hsleft : x.tape 3 0 = 4)
    (hsend : ∀ k, ds.length < k → x.tape 3 k = 6)
    (hsones : ∀ k, 1 ≤ k → k ≤ ds.length → x.tape 3 k = 8)
    (hsum : ds.sum ≤ ds.length) (hC : Blocks (x.tape 2) (x.pos 2) ds) (hq : QueueAt x q) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*ds.sum+15*ds.length+5 ∧ y.pc = 68+offset j ∧
      y.pos 0 = x.pos 0 - ds.length ∧ y.pos 3 = ds.length - ds.sum ∧
      y.pos 2 = x.pos 2 - (ds.sum+ds.length) ∧ y.tape 2 = x.tape 2 ∧
      StackAt (y.tape 4) (y.pos 4) [] ∧ QueueAt y (q ++ List.replicate ds.length 1) ∧
      Unary (y.tape 3) (y.pos 3) ∧ y.pos 1 = x.pos 1 := by
  let j' : Fin 5 := ⟨j.val+1, by omega⟩
  have he : GalilFppCopyInstances.entry j' = 97+offset j := by fin_cases j <;> rfl
  have hex : GalilFppCopyInstances.exitPC j' = 69+offset j := by fin_cases j <;> rfl
  obtain ⟨z, qs, hs, hl, hzpc, hzS, hzT, hzst, hzbelow, hzabove, hframe⟩ :=
    GalilFppCopyInstances.copy_restore_all j' ds.length x (hp.trans he.symm) hS hsleft
      (hsend (ds.length+1) (by omega)) hsones
  rw [hex] at hzpc
  have hzTpos : z.pos 4 = ds.length := by rw [hT.1] at hzT; simpa using hzT
  have hzstack : StackAt (z.tape 4) (z.pos 4) (List.replicate ds.length 1) := by
    rw [hzTpos]
    apply stack_ones
    · rw [hzbelow 0 (by omega)]; exact hT.2
    · intro k hk hkn
      apply hzabove k <;> have := hT.1 <;> omega
  obtain ⟨hAp, _⟩ := hframe 0 (by decide) (by decide)
  obtain ⟨hCp, hCt⟩ := hframe 2 (by decide) (by decide)
  obtain ⟨hBp, hBt⟩ := hframe 5 (by decide) (by decide)
  obtain ⟨hFp, hFt⟩ := hframe 6 (by decide) (by decide)
  have hzq : QueueAt z q := by simpa [QueueAt, hBp, hBt, hFp, hFt] using hq
  have hzc : Blocks (z.tape 2) (z.pos 2) ds := by simpa [hCp, hCt] using hC
  obtain ⟨y, rs, hr, hrl, hypc, hyA, hyS, hyC, hyt, hyT, hyq, hyu, hyB⟩ :=
    loop j ds z q hzpc (by simpa [hAp] using hA) hzstack (by simpa [hzS] using hsum) hzc hzq
  refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, ?_, ?_, ?_, hyt.trans hCt, hyT, hyq, ?_,
    hyB.trans (hframe 1 (by decide) (by decide)).1⟩
  · simp only [List.length_append]; omega
  · simpa [hAp] using hyA
  · simpa [hzS] using hyS
  · simpa [hCp] using hyC
  · apply hyu
    rw [hzS, hzst]
    exact ⟨hsleft, hsones, hsend⟩

#print axioms fallback
#print axioms loop
#print axioms iteration
end PalPeg.GalilFppFallbackLoop
