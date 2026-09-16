import PalPeg.GalilFppInputWord
import PalPeg.GalilFppSupply

set_option autoImplicit false
namespace PalPeg.GalilFppGeneration
open GalilFppInstruction GalilFppCode GalilFppDelta GalilFppDeltaTape GalilFppRetry
open GalilFppInputWord GalilFppSupply GalilFppLazyForward GalilFppCache GalilFppFallbackBits

/-- Actual comparison search preserves reference-aligned supply. Its
emitted ones are validated from the proved next-border result, not assumed
correct separately at each failed comparison. -/
theorem search_supply (w : List (Fin 4)) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 68+offset w[N]) (hr : Ready w (failure w N) x)
    (ht : x.tape 0 = inputTape w) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1)) (hgen : n+q.length = position (failure w) N+1) :
    ∃ r y qs, r ≤ failure w N ∧ Steps code x qs y ∧
      qs.length ≤ 29*(failure w N-r) ∧ y.pc = 68+offset w[N] ∧ Ready w r y ∧
      Supply y s n (q ++ List.replicate (failure w N-r) 1) ∧
      n+(q ++ List.replicate (failure w N-r) 1).length = generatedPosition (failure w) N r ∧
      (r = 0 ∨ y.tape 0 (r+1) = letter w[N]) ∧
      failure w (N+1) = (if y.tape 0 (r+1) = letter w[N] then r+1 else 0) ∧
      y.pos 1 = x.pos 1 := by
  obtain ⟨r, y, qs, hrp, hrun, hl, hypc, hyr, hyq, hstop, hnext, hCt, hB⟩ :=
    search_word w N hN hw x q hp hr hs.2.1 ht
  have hbound : failure w (N+1) ≤ r+1 := by
    rw [hnext]
    split <;> omega
  have hbits : Aligned s (n+q.length) (List.replicate (failure w N-r) 1) := by
    rw [hgen]
    apply aligned_ones
    intro k hk
    have hd : k < delta (failure w) N := by unfold delta; omega
    exact he.2 N (by omega) k hd
  have hsy : Supply y s n (q ++ List.replicate (failure w N-r) 1) := by
    refine ⟨?_, hyq, aligned_append s n q _ hs.2.2 hbits⟩
    unfold CacheAt
    rw [hCt]
    exact hs.1
  refine ⟨r, y, qs, hrp, hrun, hl, hypc, hyr, hsy, ?_, hstop, hnext, hB⟩
  simp only [List.length_append, List.length_replicate]
  unfold generatedPosition
  omega

/-- The actual left-end failure completes the next delta block, including
its delimiter, without assuming the correctness of the two appended bits. -/
theorem zero_miss_supply (w : List (Fin 4)) (N : ℕ) (j : Fin 4) (a : Fin 5)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 68+offset j) (ha : a.val ≠ j.val)
    (hc : x.tape 0 1 = GalilFppCompare.symbol a) (hleft : x.tape 0 0 = 4)
    (hr : Ready w 0 x) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1))
    (hgen : n+q.length = generatedPosition (failure w) N 0)
    (hnext : failure w (N+1) = 0) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 8 ∧ y.pc = 38 ∧ Ready w 0 y ∧
      Supply y s n (q ++ [1,0]) ∧
      n+(q ++ [1,0]).length = position (failure w) (N+1)+1 ∧ y.pos 1 = x.pos 1 := by
  obtain ⟨y, qs, hrun, hl, hypc, hyr, hyq, _, _, hCt, hB⟩ :=
    zero_miss j a w x q hp ha hc hleft hr hs.2.1
  have hd : delta (failure w) N = failure w N+1 := by
    simp [delta, hnext, Nat.add_comm]
  have hg : n+q.length = position (failure w) N+1+failure w N := by
    simpa [generatedPosition] using hgen
  have hz : n+q.length+1 = position (failure w) (N+1) := by
    rw [position_step, hd]
    omega
  have hb : Aligned s (n+q.length) [1,0] := by
    refine ⟨?_, ?_, trivial⟩
    · rw [hg]
      exact (he.2 N (by omega) (failure w N) (by omega)).symm
    · rw [hz]
      exact (he.1 (N+1) (by omega)).symm
  refine ⟨y, qs, hrun, hl, hypc, hyr, ⟨?_, hyq,
    aligned_append s n q [1,0] hs.2.2 hb⟩, ?_, hB⟩
  · unfold CacheAt
    rw [hCt]
    exact hs.1
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- A materialized delimiter implies the entire preceding encoded tape
is present, not merely the bit currently under the head. -/
theorem cache_tape (x : Config) (s : ℕ → Fin 2) (n p : ℕ) (f : ℕ → ℕ)
    (hc : CacheAt x s n) (he : Encoded s f p) (hh : position f p < n) :
    Tape (x.tape 2) f p := by
  constructor
  · intro k hk
    have hm := position_mono f hk
    rw [hc.1 _ (by omega), he.1 k hk]
    rfl
  · intro k hk i hi
    have hm := position_mono f (show k+1 ≤ p by omega)
    have hp := position_step f k
    rw [hc.1 _ (by omega), he.2 k hk i hi]
    rfl

/-- A successful actual comparison and its lazy delta scan restore the
full retry data invariant at the next failure value. -/
theorem hit_ready (w : List (Fin 4)) (N p : ℕ) (j : Fin 4)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hN : 0 < N) (hp : p ≤ failure w N) (hpc : x.pc = 68+offset j)
    (hhit : x.tape 0 (p+1) = letter j) (hr : Ready w p x)
    (hs : Supply x s n q) (he : Encoded s (failure w) (N+1))
    (hgen : n+q.length = generatedPosition (failure w) N p)
    (hnext : failure w (N+1) = p+1) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ Ready w (failure w (N+1)) y ∧
      Supply y s m r ∧ n ≤ m ∧ m+r.length = position (failure w) (N+1)+1 ∧
      y.pos 1 = x.pos 1 := by
  let z : Config := { x with pc := 62, pos := Function.update x.pos 0 (x.pos 0+1) }
  have hcmp : Steps code x [68+offset j,67+offset j] z :=
    GalilFppCompare.retry_hit j x hpc (by simpa [hr.1, letter] using hhit)
  have hsz : Supply z s n q := by
    simpa [z, Supply, CacheAt, GalilFppMaterialize.QueueAt] using hs
  have hc : z.tape 2 (z.pos 2) = 7 := by
    simpa [z, hr.2.2.2.2.1] using hr.2.2.2.2.2.1 p (by omega)
  obtain ⟨y, qs, m, r, hrun, hypc, hyC, hyS, hyu, hys, hnm, htotal, hlt, hframe⟩ :=
    matched_generated w N p z s n q hN hp rfl
      (by simpa [z] using hr.2.2.2.2.1) (by simpa [z] using hr.2.2.1)
      hc hsz he hgen hnext (by simpa [z] using hr.2.2.2.1)
  have hA := (hframe 0 (by decide) (by decide) (by decide) (by decide)).1
  obtain ⟨hTp, hTt⟩ := hframe 4 (by decide) (by decide) (by decide) (by decide)
  have hbound := failure_le w N
  have he' : Encoded s (failure w) (p+1) :=
    ⟨fun k hk => he.1 k (by omega), fun k hk => he.2 k (by omega)⟩
  have hyt := cache_tape y s m (p+1) (failure w) hys.1 he' (by omega)
  refine ⟨y, _, m, r, GalilFppCopy.steps_append hcmp hrun, hypc, ?_, hys, hnm, htotal,
    by simpa [z] using (hframe 1 (by decide) (by decide) (by decide) (by decide)).1⟩
  rw [hnext]
  refine ⟨?_, ?_, hyS, hyu, hyC, hyt⟩
  · simpa [z, hr.1] using hA
  · simpa [hTp, hTt, z] using hr.2.1

/-- Complete processing of one input character from the retry entry:
search, terminal comparison, generation and lazy materialization. Both
branches reestablish the same invariant for the next input prefix. -/
theorem input_step (w : List (Fin 4)) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 68+offset w[N]) (hr : Ready w (failure w N) x)
    (ht : x.tape 0 = inputTape w) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1)) (hgen : n+q.length = position (failure w) N+1) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ Ready w (failure w (N+1)) y ∧
      Supply y s m r ∧ n ≤ m ∧ m+r.length = position (failure w) (N+1)+1 ∧
      y.tape 0 = inputTape w ∧ y.pos 1 = x.pos 1 := by
  obtain ⟨p, z, qs, hpn, hsearch, _, hzpc, hzr, hzs, hzg, hstop, hnext, hzB⟩ :=
    search_supply w N hN hw x s n q hp hr ht hs he hgen
  by_cases hhit : z.tape 0 (p+1) = letter w[N]
  · have hn : failure w (N+1) = p+1 := by simpa [hhit] using hnext
    obtain ⟨y, rs, m, r, hrun, hypc, hyr, hys, hnm, htotal, hyB⟩ :=
      hit_ready w N p w[N] z s n _ hN hpn hzpc hhit hzr hzs he hzg hn
    have hall := GalilFppCopy.steps_append hsearch hrun
    exact ⟨y, _, m, r, hall, hypc, hyr, hys, hnm, htotal, preserves_input hall w ht, hyB.trans hzB⟩
  · have hp0 : p = 0 := hstop.resolve_right hhit
    subst p
    have hn : failure w (N+1) = 0 := by simpa [hhit] using hnext
    have hzt := preserves_input hsearch w ht
    obtain ⟨a, ha⟩ := (valid_input w 0 (by omega)).1 0 (by omega)
    have hchar : z.tape 0 1 = GalilFppCompare.symbol a := by rw [hzt]; exact ha
    have hneq : a.val ≠ (w[N]).val := by
      intro h
      exact hhit (hchar.trans ((symbol_letter a w[N]).mpr h))
    obtain ⟨y, rs, hrun, _, hypc, hyr, hys, htotal, hyB⟩ :=
      zero_miss_supply w N w[N] a z s n _ hzpc hneq hchar
        (by rw [hzt]; exact input_left w) hzr hzs he hzg hn
    have hall := GalilFppCopy.steps_append hsearch hrun
    exact ⟨y, _, n, _, hall, hypc, by simpa [hn] using hyr,
      hys, le_refl _, htotal, preserves_input hall w ht, hyB.trans hzB⟩

/-- Actual B advance and dispatch, between completed input processing and
the next retry entry. No abstract jump replaces these two instructions. -/
theorem advance_input (w : List (Fin 4)) (N : ℕ) (hw : N < w.length)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hpc : x.pc = 38) (hB : x.pos 1 = N) (ht : x.tape 1 = inputTape w)
    (hr : Ready w (failure w N) x) (hs : Supply x s n q) :
    ∃ y, Steps code x [38,37] y ∧ y.pc = 68+offset w[N] ∧
      y.pos 1 = N+1 ∧ Ready w (failure w N) y ∧ Supply y s n q ∧
      y.tape = x.tape := by
  let z : Config := { x with pc := 37, pos := Function.update x.pos 1 (x.pos 1+1) }
  let y : Config := { z with pc := 68+offset w[N] }
  have hc : z.tape 1 (z.pos 1) = letter w[N] := by
    simpa [z, hB, ht] using input_next w N hw
  have hm : (z.tape 1 (z.pos 1), 68+offset w[N]) ∈
      ([(5,1),(0,68),(1,108),(2,148),(3,188)] : List (Fin 9 × ℕ)) := by
    rw [hc]
    generalize w[N] = a
    fin_cases a <;> decide
  have hread : Steps code z [37] y :=
    .step _ _ _ _ [] rfl (.read _ _ _ _ hm) (.nil _)
  have hmove : Steps code x [38] z :=
    by simpa only [hpc] using
      (Steps.step x z z (.move 1 true 37) [] (by rw [hpc]; rfl)
        (.right _ _ _) (.nil _))
  refine ⟨y, GalilFppCopy.steps_append hmove hread, rfl, ?_, ?_, ?_, rfl⟩
  · simp [y, z, hB]
  · simpa [Ready, y, z] using hr
  · simpa [Supply, CacheAt, GalilFppMaterialize.QueueAt, y, z] using hs

/-- Exact preload used by Scala FppFinite.Program.run. -/
def initial (w : List (Fin 4)) : Config where
  pc := 227
  tape := fun t => if t = 0 ∨ t = 1 then inputTape w
    else if t = 2 then GalilFppFrontier.initialC
    else fun i => if i = 0 then 4 else 6
  pos := fun t => if t = 1 then 1 else 0
  output := []

theorem initial_ready (w : List (Fin 4)) : Ready w (failure w 1) (initial w) := by
  have hf : failure w 1 = 0 := by have := failure_le w 1; omega
  rw [hf]
  refine ⟨rfl, ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [initial, failure_zero]
  · refine ⟨rfl, ?_, ?_⟩
    · intro k hk hn
      change k ≤ 0 at hn
      omega
    · intro k hk
      change 0 < k at hk
      simp [initial, show k ≠ 0 by omega]
  · simp [initial, position, deltaSum]
  · exact tape_mono (initial_tape w) (by omega)

theorem initial_supply (w : List (Fin 4)) :
    Supply (initial w) (referenceStream (failure w)) 3 [] := by
  let s := referenceStream (failure w)
  have he := reference_encoded (failure w) 1
  have h0 : s 0 = 0 := by simpa [position, deltaSum] using he.1 0 (by omega)
  have h1 : s 1 = 1 := by
    simpa [position, deltaSum] using he.2 0 (by omega) 0 (by rw [delta_zero]; omega)
  have h2 : s 2 = 0 := by
    simpa [position, deltaSum, delta_zero] using he.1 1 (by omega)
  refine ⟨⟨?_, ?_⟩, ?_, trivial⟩
  · intro i hi
    change GalilFppFrontier.initialC i = GalilFppMaterialize.bitSymbol (s i)
    interval_cases i <;> simp [GalilFppFrontier.initialC, h0, h1, h2,
      GalilFppMaterialize.bitSymbol]
  · intro i hi
    simp [initial, GalilFppFrontier.initialC, show i ≠ 1 by omega, show ¬ i < 3 by omega]
  · exact ⟨[], [], ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩

/-- For a nonempty word the actual start instruction skips its first
letter, whose proper-border value is zero, and reaches the input boundary. -/
theorem initial_start (w : List (Fin 4)) (hw : 0 < w.length) :
    ∃ y, Steps code (initial w) [227] y ∧ y.pc = 38 ∧ y.pos 1 = 1 ∧
      Ready w (failure w 1) y ∧ Supply y (referenceStream (failure w)) 3 [] ∧
      y.tape 0 = inputTape w ∧ y.tape 1 = inputTape w ∧
      3+([] : List (Fin 2)).length = position (failure w) 1+1 := by
  let x := initial w
  let y : Config := { x with pc := 38 }
  have hc : x.tape 1 (x.pos 1) = letter w[0] := by
    simpa [x, initial] using input_next w 0 hw
  have hm : (x.tape 1 (x.pos 1), 38) ∈
      ([(5,0),(0,38),(1,38),(2,38),(3,38)] : List (Fin 9 × ℕ)) := by
    rw [hc]
    generalize w[0] = a
    fin_cases a <;> decide
  have hrun : Steps code x [227] y :=
    .step _ _ _ _ [] rfl (.read _ _ _ _ hm) (.nil _)
  refine ⟨y, hrun, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · exact initial_ready w
  · exact initial_supply w
  · simp [position, deltaSum, delta_zero]

/-- Every nonempty input prefix is processed by the actual finite program.
Initialization, B dispatch and both comparison outcomes are included;
there is no assumed reference stream or per-character execution oracle. -/
theorem process_prefix (w : List (Fin 4)) (k : ℕ) (hk : 1 ≤ k) (hw : k ≤ w.length) :
    ∃ y qs n q, Steps code (initial w) qs y ∧ y.pc = 38 ∧ y.pos 1 = k ∧
      Ready w (failure w k) y ∧ Supply y (referenceStream (failure w)) n q ∧
      n+q.length = position (failure w) k+1 ∧
      y.tape 0 = inputTape w ∧ y.tape 1 = inputTape w := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      obtain ⟨y, hs, hp, hB, hr, hsup, htA, htB, htotal⟩ := initial_start w (by omega)
      exact ⟨y, [227], 3, [], hs, hp, hB, hr, hsup, htotal, htA, htB⟩
    · obtain ⟨x, qs, n, q, hrun, hpc, hB, hr, hsup, htotal, htA, htB⟩ :=
        ih (by omega) (by omega)
      obtain ⟨z, hadv, hzpc, hzB, hzr, hzs, hzt⟩ :=
        advance_input w k (by omega) x _ n q hpc hB htB hr hsup
      have hzA : z.tape 0 = inputTape w := by rw [hzt]; exact htA
      obtain ⟨y, rs, m, r, hstep, hypc, hyr, hys, _, hytotal, hyA, hyB⟩ :=
        input_step w k (by omega) (by omega) z _ n q hzpc hzr hzA hzs
          (reference_encoded _ _) htotal
      have hrest := GalilFppCopy.steps_append hadv hstep
      have hall := GalilFppCopy.steps_append hrun hrest
      have hyBt : y.tape 1 = inputTape w :=
        (GalilFppCompare.input_tapes hrest).2.trans htB
      exact ⟨y, _, m, r, hall, hypc, hyB.trans hzB, hyr, hys, hytotal, hyA, hyBt⟩

set_option maxRecDepth 10000

theorem output_region_code : ∀ q : Fin 37,
    (code[q.val]?).map (fun i => (successors i).all (fun k => decide (k ≤ 36))) = some true := by decide

theorem output_region {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (hp : x.pc ≤ 36) : y.pc ≤ 36 := by
  induction hs with
  | nil => exact hp
  | step x y z i qs hi he hs ih =>
    have hc := output_region_code ⟨x.pc, by omega⟩
    simp only [hi, Option.map_some, Option.some.injEq] at hc
    exact ih (of_decide_eq_true (List.all_eq_true.mp hc y.pc (execute_successor he)))

theorem emit_location : ∀ q : Fin 228,
    (code[q.val]?).map (fun i => match i with | .emit _ => q.val == 36 | _ => true) = some true := by decide

/-- No execution ending in the generation region can have emitted:
the only emit is in the closed output region. -/
theorem generation_output {x y : Config} {qs : List ℕ} (hs : Steps code x qs y)
    (hp : 37 ≤ y.pc) : y.output = x.output := by
  induction hs with
  | nil => rfl
  | step x y z i qs hi he hs ih =>
    have hx : ¬ x.pc ≤ 36 := fun h => by
      have hz := output_region (.step x y z i qs hi he hs) h
      omega
    obtain ⟨hq, _⟩ := List.getElem?_eq_some_iff.mp hi
    have hb : x.pc < 228 := by simpa [code] using hq
    have hc := emit_location ⟨x.pc, hb⟩
    simp only [hi, Option.map_some, Option.some.injEq] at hc
    have ho : y.output = x.output := by
      cases he <;> try rfl
      have h36 : x.pc = 36 := by simpa using hc
      omega
    exact (ih hp).trans ho

/-- After the entire nonempty input, dispatch the real right marker to
the border-chain output entry. This does not yet execute that output loop. -/
theorem process_all (w : List (Fin 4)) (hw : 0 < w.length) :
    ∃ y qs n q, Steps code (initial w) qs y ∧ y.pc = 1 ∧ y.pos 1 = w.length+1 ∧
      Ready w (failure w w.length) y ∧ Supply y (referenceStream (failure w)) n q ∧
      n+q.length = position (failure w) w.length+1 ∧
      y.tape 0 = inputTape w ∧ y.tape 1 = inputTape w ∧ y.output = [] := by
  obtain ⟨x, qs, n, q, hrun, hpc, hB, hr, hs, htotal, htA, htB⟩ :=
    process_prefix w w.length (by omega) (le_refl _)
  let z : Config := { x with pc := 37, pos := Function.update x.pos 1 (x.pos 1+1) }
  let y : Config := { z with pc := 1 }
  have hc : z.tape 1 (z.pos 1) = 5 := by
    simpa [z, hB, htB] using input_end w
  have hm : (z.tape 1 (z.pos 1), 1) ∈
      ([(5,1),(0,68),(1,108),(2,148),(3,188)] : List (Fin 9 × ℕ)) := by
    rw [hc]; simp
  have hread : Steps code z [37] y :=
    .step _ _ _ _ [] rfl (.read _ _ _ _ hm) (.nil _)
  have hmove : Steps code x [38] z := by
    simpa only [hpc] using
      (Steps.step x z z (.move 1 true 37) [] (by rw [hpc]; rfl)
        (.right _ _ _) (.nil _))
  refine ⟨y, _, n, q, GalilFppCopy.steps_append hrun
    (GalilFppCopy.steps_append hmove hread), rfl, ?_, ?_, ?_, htotal, htA, htB, ?_⟩
  · simp [y, z, hB]
  · simpa [Ready, y, z] using hr
  · simpa [Supply, CacheAt, GalilFppMaterialize.QueueAt, y, z] using hs
  · exact generation_output hrun (by omega)

/-- Empty input takes the explicit start-to-halt branch, emitting nothing. -/
theorem empty_completed :
    ∃ y, Completed code (initial []) [227,0] y ∧ y.output = [] ∧ y.pos 0 = 0 ∧ y.pc = 0 := by
  let x := initial []
  let y : Config := { x with pc := 0 }
  have hm : (x.tape 1 (x.pos 1), 0) ∈
      ([(5,0),(0,38),(1,38),(2,38),(3,38)] : List (Fin 9 × ℕ)) := by
    simp [x, initial, inputTape]
  exact ⟨y, .step _ _ _ _ _ rfl (.read _ _ _ _ hm) (.halt _ rfl), rfl, rfl, rfl⟩

#print axioms empty_completed
#print axioms generation_output
#print axioms process_all
#print axioms process_prefix
#print axioms initial_start
#print axioms initial_supply
#print axioms initial_ready
#print axioms reference_encoded
#print axioms advance_input
#print axioms input_step
#print axioms hit_ready
#print axioms cache_tape
#print axioms zero_miss_supply
#print axioms search_supply
end PalPeg.GalilFppGeneration
