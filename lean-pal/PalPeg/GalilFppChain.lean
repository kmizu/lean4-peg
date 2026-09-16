import PalPeg.GalilFppGeneration

set_option autoImplicit false
namespace PalPeg.GalilFppChain
open GalilFppInstruction GalilFppCode GalilFppCopy GalilFppFallbackBits

def popOne (x : Config) : Config :=
  { x with
    pc := 3
    pos := Function.update (Function.update x.pos 3 (x.pos 3-1)) 2 (x.pos 2-1)
    tape := Function.update x.tape 3 (Function.update (x.tape 3) (x.pos 3) 6) }

/-- The output-only fallback reads cached delta bits; unlike the input
fallback it does not append distance bits to BACK. -/
theorem one (x : Config) (hp : x.pc = 3) (hc : x.tape 2 (x.pos 2) = 8)
    (hS : 0 < x.pos 3) (hC : 0 < x.pos 2) :
    Steps code x [3,26,9,8,7] (popOne x) := by
  let a : Config := { x with pc := 26 }
  let b : Config := { x with pc := 9 }
  let c : Config := { b with
    pc := 8
    tape := Function.update b.tape 3 (Function.update (b.tape 3) (b.pos 3) 6) }
  let d : Config := { c with pc := 7, pos := Function.update c.pos 3 (c.pos 3-1) }
  have hlast : Execute (.move 2 false 3) d (popOne x) := by
    simpa [d, c, b, popOne] using Execute.left d 2 3 (by simpa [d, c, b] using hC)
  simpa only [hp] using
    (Steps.step x a _ _ _ (by rw [hp]; rfl) (.read _ _ _ _ (by simp [hc]))
      (.step a b _ _ _ rfl (.read _ _ _ _ (by simp [a, hc]))
        (.step b c _ _ _ rfl (.write _ _ _ _)
          (.step c d _ _ _ rfl (.left _ _ _ hS)
            (.step d _ _ _ [] rfl hlast (.nil _))))))

theorem ones (n : ℕ) (x : Config) (hp : x.pc = 3)
    (hS : n ≤ x.pos 3) (hC : n ≤ x.pos 2)
    (hc : ∀ k, k < n → x.tape 2 (x.pos 2-k) = 8) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*n ∧ y.pc = 3 ∧
      y.pos 3 = x.pos 3-n ∧ y.pos 2 = x.pos 2-n ∧ y.tape 2 = x.tape 2 ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) ∧
      (∀ t, t ≠ 2 → t ≠ 3 → y.pos t = x.pos t ∧ y.tape t = x.tape t) ∧
      y.output = x.output := by
  induction n generalizing x with
  | zero => exact ⟨x, [], .nil _, rfl, hp, by simp, by simp, rfl, id,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl⟩
  | succ n ih =>
    have hs := one x hp (by simpa using hc 0 (by omega)) (by omega) (by omega)
    have hbits : ∀ k, k < n → (popOne x).tape 2 ((popOne x).pos 2-k) = 8 := by
      intro k hk
      have he : x.pos 2-1-k = x.pos 2-(k+1) := by omega
      simpa [popOne, he] using hc (k+1) (by omega)
    obtain ⟨y, qs, hr, hl, hyp, hyS, hyC, hyCt, hyU, hf, hout⟩ :=
      ih (popOne x) rfl (by simp [popOne]; omega) (by simp [popOne]; omega) hbits
    refine ⟨y, [3,26,9,8,7] ++ qs, steps_append hs hr, ?_, hyp, ?_, ?_, ?_, ?_, ?_, hout⟩
    · simp [hl]; omega
    · simp [popOne] at hyS; omega
    · simp [popOne] at hyC; omega
    · simpa [popOne] using hyCt
    · intro hu
      apply hyU
      simpa [popOne] using unary_pop (x.tape 3) (x.pos 3) (by omega) hu
    · intro t h2 h3
      simpa [popOne, h2, h3] using hf t h2 h3

def popZero (x : Config) : Config :=
  { x with
    pc := 2
    pos := Function.update (Function.update x.pos 0 (x.pos 0-1)) 4 (x.pos 4-1)
    tape := Function.update x.tape 4 (Function.update (x.tape 4) (x.pos 4) 6) }

/-- Crossing a zero in the output fallback consumes T and moves A left,
without enqueueing anything or emitting another answer. -/
theorem zero (x : Config) (hp : x.pc = 3) (hc : x.tape 2 (x.pos 2) = 7)
    (hA : 0 < x.pos 0) (hT : 0 < x.pos 4) :
    Steps code x [3,26,6,5,4] (popZero x) := by
  let a : Config := { x with pc := 26 }
  let b : Config := { x with pc := 6 }
  let c : Config := { b with pc := 5, pos := Function.update b.pos 0 (b.pos 0-1) }
  let d : Config := { c with
    pc := 4
    tape := Function.update c.tape 4 (Function.update (c.tape 4) (c.pos 4) 6) }
  have hlast : Execute (.move 4 false 2) d (popZero x) := by
    simpa [d, c, b, popZero] using Execute.left d 4 2 (by simpa [d, c, b] using hT)
  simpa only [hp] using
    (Steps.step x a _ _ _ (by rw [hp]; rfl) (.read _ _ _ _ (by simp [hc]))
      (.step a b _ _ _ rfl (.read _ _ _ _ (by simp [a, hc]))
        (.step b c _ _ _ rfl (.left _ _ _ hA)
          (.step c d _ _ _ rfl (.write _ _ _ _)
            (.step d _ _ _ [] rfl hlast (.nil _))))))

def begin (x : Config) : Config :=
  { x with pc := 3, pos := Function.update x.pos 2 (x.pos 2-1) }

theorem enter (x : Config) (hp : x.pc = 2) (ht : x.tape 4 (x.pos 4) = 8)
    (hc : 0 < x.pos 2) : Steps code x [2,27] (begin x) := by
  let y : Config := { x with pc := 27 }
  simpa only [hp, y, begin] using
    (Steps.step x y _ _ _ (by rw [hp]; rfl) (.read _ _ _ _ (by simp [ht]))
      (.step y _ _ _ [] rfl (.left _ _ _ hc) (.nil _)))

/-- A complete output-fallback group: leave the current delimiter, cross
the ones, then pop one T cell at the preceding delimiter. -/
theorem iteration (n : ℕ) (x : Config) (ts : List (Fin 2))
    (hp : x.pc = 2) (hA : 0 < x.pos 0)
    (hT : GalilFppMaterialize.StackAt (x.tape 4) (x.pos 4) (1 :: ts))
    (hS : n ≤ x.pos 3) (hC : n+1 ≤ x.pos 2)
    (hones : ∀ k, k < n → x.tape 2 (x.pos 2-(k+1)) = 8)
    (hzero : x.tape 2 (x.pos 2-(n+1)) = 7) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*n+7 ∧ y.pc = 2 ∧
      y.pos 0 = x.pos 0-1 ∧ y.pos 3 = x.pos 3-n ∧
      y.pos 2 = x.pos 2-(n+1) ∧ y.tape 2 = x.tape 2 ∧
      GalilFppMaterialize.StackAt (y.tape 4) (y.pos 4) ts ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) ∧
      y.output = x.output := by
  have he := enter x hp hT.2.1 (by omega)
  have hbits : ∀ k, k < n → (begin x).tape 2 ((begin x).pos 2-k) = 8 := by
    intro k hk
    have hh : x.pos 2-1-k = x.pos 2-(k+1) := by omega
    simpa [begin, hh] using hones k hk
  obtain ⟨z, qs, hs, hl, hzpc, hzS, hzC, hzCt, hzU, hf, hout⟩ :=
    ones n (begin x) rfl (by simpa [begin] using hS) (by simp [begin]; omega) hbits
  have hzA : z.pos 0 = x.pos 0 := by simpa [begin] using (hf 0 (by decide) (by decide)).1
  have hzT : GalilFppMaterialize.StackAt (z.tape 4) (z.pos 4) (1 :: ts) := by
    obtain ⟨htp, htt⟩ := hf 4 (by decide) (by decide)
    simpa [htp, htt, begin] using hT
  have hzC' : z.pos 2 = x.pos 2-(n+1) := by simp [begin] at hzC; omega
  have hzbit : z.tape 2 (z.pos 2) = 7 := by rw [hzCt, hzC']; exact hzero
  have hz := zero z hzpc hzbit (by omega) hzT.1
  have hstack : GalilFppMaterialize.StackAt ((popZero z).tape 4) ((popZero z).pos 4) ts := by
    simp only [popZero, Function.update_self]
    apply GalilFppMaterialize.stack_congr hzT.2.2
    intro k hk
    have hn : k ≠ z.pos 4 := by have := hzT.1; omega
    simp [Function.update_of_ne hn]
  refine ⟨popZero z, [2,27] ++ qs ++ [3,26,6,5,4],
    steps_append (steps_append he hs) hz, ?_, rfl, ?_, ?_, ?_, ?_, hstack, ?_, hout⟩
  · simp [hl]
  · simp [popZero, hzA]
  · simpa [popZero, begin] using hzS
  · simpa [popZero] using hzC'
  · simpa [popZero, begin] using hzCt
  · intro hu
    simpa [popZero] using hzU (by simpa [begin] using hu)

/-- Complete output-only scan after S has been copied into T. -/
theorem loop (ds : List ℕ) (x : Config) (hp : x.pc = 2)
    (hA : ds.length ≤ x.pos 0)
    (hT : GalilFppMaterialize.StackAt (x.tape 4) (x.pos 4) (List.replicate ds.length 1))
    (hS : ds.sum ≤ x.pos 3)
    (hC : GalilFppFallbackLoop.Blocks (x.tape 2) (x.pos 2) ds) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*ds.sum+7*ds.length+1 ∧ y.pc = 1 ∧
      y.pos 0 = x.pos 0-ds.length ∧ y.pos 3 = x.pos 3-ds.sum ∧
      y.pos 2 = x.pos 2-(ds.sum+ds.length) ∧ y.tape 2 = x.tape 2 ∧
      GalilFppMaterialize.StackAt (y.tape 4) (y.pos 4) [] ∧
      (Unary (x.tape 3) (x.pos 3) → Unary (y.tape 3) (y.pos 3)) ∧
      y.output = x.output := by
  induction ds generalizing x with
  | nil =>
    have hm : x.tape 4 (x.pos 4) = 4 := by rw [hT.1]; exact hT.2
    have hs : Steps code x [2] { x with pc := 1 } := by
      simpa only [hp] using
        (Steps.step x { x with pc := 1 } _ _ [] (by rw [hp]; rfl)
          (.read _ _ _ _ (by simp [hm])) (.nil _))
    exact ⟨_, [2], hs, by simp, rfl, by simp, by simp, by simp, rfl, hT, id, rfl⟩
  | cons d ds ih =>
    have hT' : GalilFppMaterialize.StackAt (x.tape 4) (x.pos 4)
        (1 :: List.replicate ds.length 1) := by simpa [List.replicate_succ] using hT
    obtain ⟨z, qs, hs, hl, hzpc, hzA, hzS, hzC, hzCt, hzT, hzU, hzout⟩ :=
      iteration d x _ hp (by simp only [List.length_cons] at hA; omega) hT'
        (by simp only [List.sum_cons] at hS; omega) hC.1 hC.2.1 hC.2.2.1
    have hzblocks : GalilFppFallbackLoop.Blocks (z.tape 2) (z.pos 2) ds := by
      rw [hzCt, hzC]; exact hC.2.2.2
    obtain ⟨y, rs, hr, hrl, hypc, hyA, hyS, hyC, hyCt, hyT, hyU, hyout⟩ :=
      ih z hzpc (by simp only [List.length_cons] at hA; omega) hzT
        (by simp only [List.sum_cons] at hS; omega) hzblocks
    refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, ?_, ?_, ?_,
      hyCt.trans hzCt, hyT, hyU ∘ hzU, hyout.trans hzout⟩
    · simp only [List.length_append, List.sum_cons, List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons, List.length_cons]; omega

def silent : Instruction → Bool
  | .emit _ => false
  | _ => true

theorem copy_silent : ∀ q : Fin 8, (code[q.val+28]?).map silent = some true := by decide

theorem copy_output {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (hin : Inside qs) : y.output = x.output := by
  induction hs with
  | nil => rfl
  | step x y z i qs hi he hs ih =>
    have hb := of_decide_eq_true (List.all_eq_true.mp hin x.pc (by simp))
    have hc := copy_silent ⟨x.pc-28, by omega⟩
    have hn : x.pc-28+28 = x.pc := by omega
    simp only [hn, hi, Option.map_some, Option.some.injEq] at hc
    have ho : y.output = x.output := by cases he <;> simp_all [silent]
    have ht : Inside qs := List.all_eq_true.mpr
      (fun q hq => List.all_eq_true.mp hin q (by simp [hq]))
    exact (ih ht).trans ho

/-- Full output fallback, including the actual S-to-T copy. -/
theorem fallback (ds : List ℕ) (x : Config) (hp : x.pc = 28)
    (hA : ds.length ≤ x.pos 0)
    (hT : GalilFppMaterialize.StackAt (x.tape 4) (x.pos 4) [])
    (hS : x.pos 3 = ds.length) (hu : Unary (x.tape 3) (x.pos 3))
    (hsum : ds.sum ≤ ds.length)
    (hC : GalilFppFallbackLoop.Blocks (x.tape 2) (x.pos 2) ds) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 5*ds.sum+13*ds.length+5 ∧ y.pc = 1 ∧
      y.pos 0 = x.pos 0-ds.length ∧ y.pos 3 = ds.length-ds.sum ∧
      y.pos 2 = x.pos 2-(ds.sum+ds.length) ∧ y.tape 2 = x.tape 2 ∧
      GalilFppMaterialize.StackAt (y.tape 4) (y.pos 4) [] ∧
      Unary (y.tape 3) (y.pos 3) ∧ y.output = x.output := by
  have hu' : Unary (x.tape 3) ds.length := by simpa [hS] using hu
  obtain ⟨z, qs, hs, hl, hzpc, hzS, hzT, hzst, hzbelow, hzabove, hin⟩ :=
    copy_restore ds.length x hp hS hu'.1 (hu'.2.2 _ (by omega)) hu'.2.1
  have hf := GalilFppCopyInstances.copy_frame hs hin
  have hTp : z.pos 4 = ds.length := by rw [hT.1] at hzT; simpa using hzT
  have hzstack : GalilFppMaterialize.StackAt (z.tape 4) (z.pos 4)
      (List.replicate ds.length 1) := by
    rw [hTp]
    apply GalilFppFallbackLoop.stack_ones
    · rw [hzbelow 0 (by omega)]; exact hT.2
    · intro k hk hkn
      apply hzabove k <;> have := hT.1 <;> omega
  obtain ⟨hAp, _⟩ := hf 0 (by decide) (by decide)
  obtain ⟨hCp, hCt⟩ := hf 2 (by decide) (by decide)
  have hzc : GalilFppFallbackLoop.Blocks (z.tape 2) (z.pos 2) ds := by
    simpa [hCp, hCt] using hC
  obtain ⟨y, rs, hr, hrl, hypc, hyA, hyS, hyC, hyCt, hyT, hyU, hyout⟩ :=
    loop ds z hzpc (by simpa [hAp] using hA) hzstack (by simpa [hzS] using hsum) hzc
  refine ⟨y, qs ++ rs, steps_append hs hr, ?_, hypc, ?_, ?_, ?_, hyCt.trans hCt,
    hyT, ?_, hyout.trans (copy_output hs hin)⟩
  · simp only [List.length_append]; omega
  · simpa [hAp] using hyA
  · simpa [hzS] using hyS
  · simpa [hCp] using hyC
  · apply hyU
    simpa [hzS, hzst] using hu'

open GalilFppDelta GalilFppDeltaTape GalilFppRetry

/-- The output fallback restores precisely the next proper-border state. -/
theorem fallback_ready (w : List (Fin 4)) (p : ℕ) (x : Config)
    (hp : x.pc = 28) (hr : Ready w p x) :
    ∃ y qs, Steps code x qs y ∧ qs.length ≤ 18*(p-failure w p)+5 ∧
      y.pc = 1 ∧ Ready w (failure w p) y ∧ y.output = x.output := by
  obtain ⟨hA, hT, hS, hu, hC, htape⟩ := hr
  let ds := backwards (failure w) (failure w p) (p-failure w p)
  have hlen : ds.length = p-failure w p := backwards_length _ _ _
  have hsum : ds.sum = deltaSum (failure w) (failure w p) (p-failure w p) := backwards_sum _ _ _
  have hf := failure_le w p
  have hjoin : failure w p+(p-failure w p) = p := by omega
  have hbits : GalilFppFallbackLoop.Blocks (x.tape 2) (x.pos 2) ds := by
    rw [hC]
    have hh := tape_blocks (x.tape 2) (failure w) p (failure w p) (p-failure w p)
      htape (by omega)
    simpa only [hjoin] using hh
  have hbound : ds.sum ≤ ds.length := by rw [hsum, hlen]; exact crossed_ones_le w p
  obtain ⟨y, qs, hs, hl, hypc, hyA, hyS, hyC, hyCt, hyT, hyU, hyout⟩ :=
    fallback ds x hp (by rw [hlen, hA]; omega) hT (by simpa [hlen] using hS) hu hbound hbits
  have hgap := fallback_gap w p
  have hspan := position_span (failure w) (failure w p) (p-failure w p)
  rw [hjoin] at hspan
  have hA' : y.pos 0 = failure w p := by rw [hA, hlen] at hyA; omega
  have hS' : y.pos 3 = failure w p-failure w (failure w p) := by
    rw [hlen, hsum] at hyS; omega
  have hC' : y.pos 2 = position (failure w) (failure w p) := by
    rw [hC, hlen] at hyC
    change position (failure w) p = position (failure w) (failure w p)+ds.sum+(p-failure w p) at hspan
    omega
  refine ⟨y, qs, hs, ?_, hypc, ⟨hA', hyT, hS', hyU, hC', ?_⟩, hyout⟩
  · rw [hlen] at hl hbound; omega
  · rw [hyCt]
    exact tape_mono htape (by omega)

/-- Emit the current nonzero border exactly once and return to the output
entry with the strictly smaller next border. -/
theorem emit_next (w : List (Fin 4)) (p : ℕ) (x : Config)
    (hp : x.pc = 1) (hpos : 0 < p) (hword : p ≤ w.length)
    (ht : x.tape 0 = GalilFppInputWord.inputTape w) (hr : Ready w p x) :
    ∃ y qs, Steps code x qs y ∧ qs.length ≤ 18*(p-failure w p)+7 ∧
      y.pc = 1 ∧ Ready w (failure w p) y ∧ y.output = x.output ++ [p] ∧
      y.tape 0 = GalilFppInputWord.inputTape w ∧ failure w p < p := by
  let a : Config := { x with pc := 36 }
  let z : Config := { a with pc := 28, output := a.output ++ [a.pos 0] }
  have hc : x.tape 0 (x.pos 0) = letter w[p-1] := by
    have hi := GalilFppInputWord.input_next w (p-1) (by omega)
    rw [hr.1, ht]
    simpa [show p-1+1 = p by omega] using hi
  have hm : (x.tape 0 (x.pos 0), 36) ∈
      ([(4,0),(0,36),(1,36),(2,36),(3,36)] : List (Fin 9 × ℕ)) := by
    rw [hc]
    generalize w[p-1] = b
    fin_cases b <;> decide
  have hs : Steps code x [1,36] z := by
    simpa only [hp] using
      (Steps.step x a _ _ _ (by rw [hp]; rfl) (.read _ _ _ _ hm)
        (.step a z _ _ [] rfl (.emit _ _) (.nil _)))
  obtain ⟨y, qs, hrun, hl, hypc, hyr, hyout⟩ := fallback_ready w p z rfl hr
  have hall := steps_append hs hrun
  refine ⟨y, [1,36] ++ qs, hall, ?_, hypc, hyr, ?_,
    GalilFppInputWord.preserves_input hall w ht, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · simpa [z, a, hr.1] using hyout
  · have := failure_le w p; omega

def borderValues (w : List (Fin 4)) (p : ℕ) : List ℕ :=
  if p = 0 then [] else p :: borderValues w (failure w p)
termination_by p
decreasing_by have := failure_le w p; omega

theorem steps_completed {x y z : Config} {qs rs : List ℕ}
    (hs : Steps code x qs y) (hr : Completed code y rs z) :
    Completed code x (qs ++ rs) z := by
  induction hs with
  | nil => exact hr
  | step x y z i qs hi he hs ih => exact .step _ _ _ _ _ hi he (ih hr)

/-- The entire output loop terminates and appends exactly the decreasing
proper-border chain to the output present on entry. -/
theorem completed (w : List (Fin 4)) (p : ℕ) (x : Config)
    (hp : x.pc = 1) (hw : p ≤ w.length)
    (ht : x.tape 0 = GalilFppInputWord.inputTape w) (hr : Ready w p x) :
    ∃ y qs, Completed code x qs y ∧ qs.length ≤ 25*p+2 ∧
      y.output = x.output ++ borderValues w p ∧ y.pos 0 = 0 ∧ y.pc = 0 := by
  induction p using Nat.strong_induction_on generalizing x with
  | h p ih =>
    by_cases hz : p = 0
    · subst p
      let y : Config := { x with pc := 0 }
      have hc : x.tape 0 (x.pos 0) = 4 := by
        rw [hr.1, ht]; exact GalilFppInputWord.input_left w
      have hs : Completed code x [1,0] y := by
        simpa only [hp] using
          (Completed.step x y y _ _ (by rw [hp]; rfl)
            (.read _ _ _ _ (by simp [hc])) (.halt y rfl))
      exact ⟨y, [1,0], hs, by simp, by simp [y, borderValues], hr.1, rfl⟩
    · obtain ⟨z, qs, hs, hl, hzpc, hzr, hzout, hzt, hlt⟩ :=
        emit_next w p x hp (by omega) hw ht hr
      obtain ⟨y, rs, hrun, hrl, hyout, hypos, hypc⟩ := ih (failure w p) hlt z hzpc (by omega) hzt hzr
      refine ⟨y, qs ++ rs, steps_completed hs hrun, ?_, ?_, hypos, hypc⟩
      · simp only [List.length_append]; omega
      · rw [hyout, hzout]
        conv_rhs => rw [borderValues, if_neg hz]
        simp only [List.append_assoc, List.singleton_append]

/-- The concrete Scala FPP kernel terminates on every input and its entire
output is exactly the decreasing proper-border chain, with no earlier emits. -/
theorem initial_completed (w : List (Fin 4)) :
    ∃ y qs, Completed code (GalilFppGeneration.initial w) qs y ∧
      y.output = borderValues w (failure w w.length) ∧ y.pos 0 = 0 ∧ y.pc = 0 := by
  by_cases hw : w.length = 0
  · have he : w = [] := by cases w <;> simp_all
    subst w
    obtain ⟨y, hs, hout, hpos, hpc⟩ := GalilFppGeneration.empty_completed
    exact ⟨y, _, hs, by simpa [failure_zero, borderValues] using hout, hpos, hpc⟩
  · obtain ⟨x, qs, n, q, hs, hp, _, hr, _, _, ht, _, hout⟩ :=
      GalilFppGeneration.process_all w (by omega)
    have hf := failure_le w w.length
    obtain ⟨y, rs, hrun, _, hyout, hypos, hypc⟩ := completed w (failure w w.length) x hp (by omega) ht hr
    exact ⟨y, _, steps_completed hs hrun, by simpa [hout] using hyout, hypos, hypc⟩

/-- Following failure links enumerates every positive match below the
current matching prefix, not just a subset of its borders. -/
theorem mem_borderValues (w T : List (Fin 4)) (p b : ℕ) (hm : MatchAt w T p) :
    b ∈ borderValues w p ↔ 0 < b ∧ b ≤ p ∧ MatchAt w T b := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hz : p = 0
    · subst p
      rw [borderValues, if_pos rfl]
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hb hbp
      omega
    · have hpos : 0 < p := by omega
      have hf : failure w p < p := by have := failure_le w p; omega
      obtain ⟨hfm, hmax⟩ := GalilFppFailure.fallback_complete w T p hm hpos
      rw [borderValues, if_neg hz, List.mem_cons, ih (failure w p) hf hfm]
      constructor
      · rintro (he | ⟨hb, hbf, hbm⟩)
        · subst b; exact ⟨hpos, le_refl _, hm⟩
        · exact ⟨hb, by omega, hbm⟩
      · rintro ⟨hb, hbp, hbm⟩
        by_cases he : b = p
        · exact Or.inl he
        · exact Or.inr ⟨hb, hmax b (by omega) hbm, hbm⟩

/-- The whole-kernel output contains exactly the nonempty proper borders. -/
theorem mem_initial_output (w : List (Fin 4)) (b : ℕ) :
    b ∈ borderValues w (failure w w.length) ↔
      0 < b ∧ b < w.length ∧ IsBorder w b := by
  have hm : MatchAt w ((w.take w.length).drop 1) (failure w w.length) := matchState_spec _ _
  rw [mem_borderValues w _ _ b hm]
  constructor
  · rintro ⟨hb, hbf, hbm⟩
    have hf := failure_le w w.length
    have hbl : b < w.length := by omega
    refine ⟨hb, hbl, ?_⟩
    simpa using (GalilFppFailure.proper_iff w w.length b (le_refl _) hbl).mp hbm
  · rintro ⟨hb, hbl, hborder⟩
    have hbt : IsBorder (w.take w.length) b := by simpa using hborder
    exact ⟨hb, GalilFppFailure.proper_le_failure w w.length b (le_refl _) hbl hbt,
      (GalilFppFailure.proper_iff w w.length b (le_refl _) hbl).mpr hbt⟩

#print axioms mem_initial_output
#print axioms initial_completed
#print axioms completed
#print axioms emit_next
#print axioms fallback_ready
#print axioms fallback
#print axioms loop
#print axioms iteration
#print axioms ones
#print axioms zero
end PalPeg.GalilFppChain
