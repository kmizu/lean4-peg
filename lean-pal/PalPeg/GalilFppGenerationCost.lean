import PalPeg.GalilFppSupplyCost
import PalPeg.GalilFppGeneration
import PalPeg.GalilFppChain

set_option autoImplicit false
namespace PalPeg.GalilFppGenerationCost
open GalilFppInstruction GalilFppCode GalilFppDelta GalilFppDeltaTape GalilFppRetry
open GalilFppInputWord GalilFppSupply GalilFppLazyForward GalilFppCache GalilFppFallbackBits
open GalilFppGeneration

/-- A single real instruction increases the BACK/S potential by at most eleven. -/
theorem execute_potential {i : Instruction} {x y : Config} (h : Execute i x y) :
    5*y.pos 5 + 11*x.pos 3 ≤ 11 + 5*x.pos 5 + 11*y.pos 3 := by
  cases h with
  | right x t n =>
    by_cases h5 : t = 5 <;> by_cases h3 : t = 3 <;>
      simp_all [Function.update_apply, eq_comm] <;> omega
  | left x t n hp =>
    by_cases h5 : t = 5 <;> by_cases h3 : t = 3 <;>
      simp_all [Function.update_apply, eq_comm] <;> omega
  | emit => simp
  | write => simp
  | read => simp

theorem steps_potential {program : List Instruction} {x y : Config} {qs : List ℕ}
    (h : Steps program x qs y) :
    qs.length + 5*y.pos 5 + 11*x.pos 3 ≤
      12*qs.length + 5*x.pos 5 + 11*y.pos 3 := by
  induction h with
  | nil => simp
  | step x y z i qs hi hs hr ih =>
    have hm := execute_potential hs
    simp only [List.length_cons]
    omega

theorem search_supply_cost (w : List (Fin 4)) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
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
      y.pos 1 = x.pos 1 ∧
      qs.length + 5*y.pos 5 + 11*x.pos 3 ≤
        348*(failure w N-r) + 5*x.pos 5 + 11*y.pos 3 := by
  obtain ⟨r,y,qs,hrp,hrun,hl,hpc,hready,hsupply,hpos,hstop,hnext,hB⟩ :=
    search_supply w N hN hw x s n q hp hr ht hs he hgen
  refine ⟨r,y,qs,hrp,hrun,hl,hpc,hready,hsupply,hpos,hstop,hnext,hB,?_⟩
  have hh := steps_potential hrun
  omega

/-- Cost-aware Ready restoration. The S-height form avoids summing delta(p)
as though the retry candidate p were the input index N. -/
theorem hit_ready_cost (w : List (Fin 4)) (N p : ℕ) (j : Fin 4)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hN : 0 < N) (hp : p ≤ failure w N) (hpc : x.pc = 68+offset j)
    (hhit : x.tape 0 (p+1) = letter j) (hr : Ready w p x)
    (hs : Supply x s n q) (he : Encoded s (failure w) (N+1))
    (hgen : n+q.length = generatedPosition (failure w) N p)
    (hnext : failure w (N+1) = p+1) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ Ready w (failure w (N+1)) y ∧
      Supply y s m r ∧ n ≤ m ∧ m+r.length = position (failure w) (N+1)+1 ∧
      y.pos 1 = x.pos 1 ∧
      qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 18 + 5*x.pos 5 + 11*y.pos 3 := by
  let z : Config := {x with pc := 62,pos := Function.update x.pos 0 (x.pos 0+1)}
  have hcmp : Steps code x [68+offset j,67+offset j] z :=
    GalilFppCompare.retry_hit j x hpc (by simpa [hr.1,letter] using hhit)
  have hsz : Supply z s n q := by
    simpa [z,Supply,CacheAt,GalilFppMaterialize.QueueAt] using hs
  have hc : z.tape 2 (z.pos 2) = 7 := by
    simpa [z,hr.2.2.2.2.1] using hr.2.2.2.2.2.1 p (by omega)
  obtain ⟨y,qs,m,r,hrun,hypc,hyC,hyS,hyu,hys,hnm,htotal,hlt,hframe,hcost⟩ :=
    GalilFppSupplyCost.matched_generated_cost w N p z s n q hN hp rfl
      (by simpa [z] using hr.2.2.2.2.1) (by simpa [z] using hr.2.2.1)
      hc hsz he hgen hnext (by simpa [z] using hr.2.2.2.1)
  have hA := (hframe 0 (by decide) (by decide) (by decide) (by decide)).1
  obtain ⟨hTp,hTt⟩ := hframe 4 (by decide) (by decide) (by decide) (by decide)
  have hbound := failure_le w N
  have he' : Encoded s (failure w) (p+1) :=
    ⟨fun k hk => he.1 k (by omega),fun k hk => he.2 k (by omega)⟩
  have hyt := cache_tape y s m (p+1) (failure w) hys.1 he' (by omega)
  refine ⟨y,_,m,r,GalilFppCopy.steps_append hcmp hrun,hypc,?_,hys,hnm,htotal,
    by simpa [z] using (hframe 1 (by decide) (by decide) (by decide) (by decide)).1,?_⟩
  · rw [hnext]
    refine ⟨?_,?_,hyS,hyu,hyC,hyt⟩
    · simpa [z,hr.1] using hA
    · simpa [hTp,hTt,z] using hr.2.1
  · have hfl := failure_le w p
    have hfg := failure_grows w p
    have hS := hr.2.2.1
    have hd : x.pos 3 + delta (failure w) p = y.pos 3 := by
      unfold delta
      omega
    have hB : z.pos 5 = x.pos 5 := by simp [z]
    rw [hB] at hcost
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem zero_miss_supply_cost (w : List (Fin 4)) (N : ℕ) (j : Fin 4) (a : Fin 5)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 68+offset j) (ha : a.val ≠ j.val)
    (hc : x.tape 0 1 = GalilFppCompare.symbol a) (hleft : x.tape 0 0 = 4)
    (hr : Ready w 0 x) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1))
    (hgen : n+q.length = generatedPosition (failure w) N 0)
    (hnext : failure w (N+1) = 0) :
    ∃ y qs, Steps code x qs y ∧ qs.length = 8 ∧ y.pc = 38 ∧ Ready w 0 y ∧
      Supply y s n (q ++ [1,0]) ∧
      n+(q ++ [1,0]).length = position (failure w) (N+1)+1 ∧ y.pos 1 = x.pos 1 ∧
      qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 18+5*x.pos 5+11*y.pos 3 := by
  let z : Config := {x with pc := 66}
  let u := GalilFppEnqueue.pushed 1 64 z
  let v := GalilFppEnqueue.pushed 0 38 u
  have hm : Steps code x [68+offset j,67+offset j,106+offset j,105+offset j] z :=
    GalilFppCompare.retry_mismatch j a none x hp ha (by simpa [hr.1] using hc)
      (by simpa [hr.1,GalilFppCompare.previousSymbol] using hleft)
  have hd : delta (failure w) N = failure w N+1 := by simp [delta,hnext,Nat.add_comm]
  have hg : n+q.length = position (failure w) N+1+failure w N := by
    simpa [generatedPosition] using hgen
  have hz : n+q.length+1 = position (failure w) (N+1) := by
    rw [position_step,hd]; omega
  have hb₁ : (1 : Fin 2) = s (n+q.length) := by
    rw [hg]
    exact (he.2 N (by omega) (failure w N) (by omega)).symm
  have hb₀ : (0 : Fin 2) = s (n+(q ++ [1]).length) := by
    have hlen : n+(q ++ [1]).length = position (failure w) (N+1) := by simp; omega
    rw [hlen]
    exact (he.1 (N+1) (by omega)).symm
  have hsz : Supply z s n q := hs
  obtain ⟨h₁,hsu,_⟩ := enqueue_supply 2 z s n q rfl hsz hb₁
  change Supply u s n (q ++ [1]) at hsu
  obtain ⟨h₂,hsv,_⟩ := enqueue_supply 1 u s n (q ++ [1]) rfl hsu hb₀
  have hall := GalilFppCopy.steps_append (GalilFppCopy.steps_append hm h₁) h₂
  refine ⟨v,_,hall,rfl,rfl,?_,?_,?_,?_,?_⟩
  · simpa [Ready,v,u,z,GalilFppEnqueue.pushed] using hr
  · change Supply v s n ((q ++ [1]) ++ [0]) at hsv
    simpa [List.append_assoc] using hsv
  · simp only [List.length_append,List.length_cons,List.length_nil]; omega
  · simp [v,u,z,GalilFppEnqueue.pushed]
  · simp [v,u,z,GalilFppEnqueue.pushed]
    <;> omega

/-- One input symbol, including all retries. Failure and head potentials
are retained so consecutive input steps can telescope. -/
theorem input_step_cost (w : List (Fin 4)) (N : ℕ) (hN : 0 < N) (hw : N < w.length)
    (x : Config) (s : ℕ → Fin 2) (n : ℕ) (q : List (Fin 2))
    (hp : x.pc = 68+offset w[N]) (hr : Ready w (failure w N) x)
    (ht : x.tape 0 = inputTape w) (hs : Supply x s n q)
    (he : Encoded s (failure w) (N+1)) (hgen : n+q.length = position (failure w) N+1) :
    ∃ y qs m r, Steps code x qs y ∧ y.pc = 38 ∧ Ready w (failure w (N+1)) y ∧
      Supply y s m r ∧ n ≤ m ∧ m+r.length = position (failure w) (N+1)+1 ∧
      y.tape 0 = inputTape w ∧ y.pos 1 = x.pos 1 ∧
      qs.length + 5*y.pos 5 + 11*x.pos 3 + 348*failure w (N+1) ≤
        366 + 5*x.pos 5 + 11*y.pos 3 + 348*failure w N := by
  obtain ⟨p,z,qs,hpn,hsearch,_,hzpc,hzr,hzs,hzg,hstop,hnext,hzB,hsc⟩ :=
    search_supply_cost w N hN hw x s n q hp hr ht hs he hgen
  by_cases hhit : z.tape 0 (p+1) = letter w[N]
  · have hn : failure w (N+1) = p+1 := by simpa [hhit] using hnext
    obtain ⟨y,rs,m,r,hrun,hypc,hyr,hys,hnm,htotal,hyB,hc⟩ :=
      hit_ready_cost w N p w[N] z s n _ hN hpn hzpc hhit hzr hzs he hzg hn
    have hall := GalilFppCopy.steps_append hsearch hrun
    refine ⟨y,_,m,r,hall,hypc,hyr,hys,hnm,htotal,preserves_input hall w ht,
      hyB.trans hzB,?_⟩
    simp only [List.length_append]
    omega
  · have hp0 : p = 0 := hstop.resolve_right hhit
    subst p
    have hn : failure w (N+1) = 0 := by simpa [hhit] using hnext
    have hzt := preserves_input hsearch w ht
    obtain ⟨a,ha⟩ := (valid_input w 0 (by omega)).1 0 (by omega)
    have hchar : z.tape 0 1 = GalilFppCompare.symbol a := by rw [hzt]; exact ha
    have hneq : a.val ≠ (w[N]).val := by
      intro h
      exact hhit (hchar.trans ((symbol_letter a w[N]).mpr h))
    obtain ⟨y,rs,hrun,_,hypc,hyr,hys,htotal,hyB,hc⟩ :=
      zero_miss_supply_cost w N w[N] a z s n _ hzpc hneq hchar
        (by rw [hzt]; exact input_left w) hzr hzs he hzg hn
    have hall := GalilFppCopy.steps_append hsearch hrun
    refine ⟨y,_,n,_,hall,hypc,by simpa [hn] using hyr,hys,le_refl _,htotal,
      preserves_input hall w ht,hyB.trans hzB,?_⟩
    simp only [List.length_append]
    omega

/-- Whole-prefix bound for the actual program, retaining potential for composition. -/
theorem process_prefix_cost (w : List (Fin 4)) (k : ℕ) (hk : 1 ≤ k) (hw : k ≤ w.length) :
    ∃ y qs n q, Steps code (initial w) qs y ∧ y.pc = 38 ∧ y.pos 1 = k ∧
      Ready w (failure w k) y ∧ Supply y (referenceStream (failure w)) n q ∧
      n+q.length = position (failure w) k+1 ∧
      y.tape 0 = inputTape w ∧ y.tape 1 = inputTape w ∧
      qs.length + 5*y.pos 5 + 348*failure w k ≤ 390*k + 11*y.pos 3 := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      obtain ⟨y,hs,hp,hB,hr,hsup,htA,htB,htotal⟩ := initial_start w (by omega)
      refine ⟨y,[227],3,[],hs,hp,hB,hr,hsup,htotal,htA,htB,?_⟩
      have hc := steps_potential hs
      have hf : failure w 1 = 0 := by have := failure_le w 1; omega
      simp [initial,hf] at hc ⊢
      omega
    · obtain ⟨x,qs,n,q,hrun,hpc,hB,hr,hsup,htotal,htA,htB,hcost⟩ :=
        ih (by omega) (by omega)
      obtain ⟨z,hadv,hzpc,hzB,hzr,hzs,hzt⟩ :=
        advance_input w k (by omega) x _ n q hpc hB htB hr hsup
      have hzA : z.tape 0 = inputTape w := by rw [hzt]; exact htA
      obtain ⟨y,rs,m,r,hstep,hypc,hyr,hys,_,hytotal,hyA,hyB,hstepcost⟩ :=
        input_step_cost w k (by omega) (by omega) z _ n q hzpc hzr hzA hzs
          (reference_encoded _ _) htotal
      have hrest := GalilFppCopy.steps_append hadv hstep
      have hall := GalilFppCopy.steps_append hrun hrest
      have hyBt : y.tape 1 = inputTape w :=
        (GalilFppCompare.input_tapes hrest).2.trans htB
      refine ⟨y,_,m,r,hall,hypc,hyB.trans hzB,hyr,hys,hytotal,hyA,hyBt,?_⟩
      have hac := steps_potential hadv
      simp only [List.length_append,List.length_cons,List.length_nil] at hac ⊢
      omega

/-- Generation leaves enough potential to pay for the entire border output. -/
theorem process_all_cost (w : List (Fin 4)) (hw : 0 < w.length) :
    ∃ y qs, Steps code (initial w) qs y ∧ y.pc = 1 ∧
      Ready w (failure w w.length) y ∧ y.tape 0 = inputTape w ∧ y.output = [] ∧
      qs.length + 25*failure w w.length ≤ 390*w.length+2 := by
  obtain ⟨x,qs,n,q,hrun,hpc,hB,hr,hs,htotal,htA,htB,hcost⟩ :=
    process_prefix_cost w w.length (by omega) (le_refl _)
  let z : Config := {x with pc := 37,pos := Function.update x.pos 1 (x.pos 1+1)}
  let y : Config := {z with pc := 1}
  have hc : z.tape 1 (z.pos 1) = 5 := by
    simpa [z,hB,htB] using input_end w
  have hm : (z.tape 1 (z.pos 1),1) ∈
      ([(5,1),(0,68),(1,108),(2,148),(3,188)] : List (Fin 9 × ℕ)) := by
    rw [hc]; simp
  have hread : Steps code z [37] y :=
    .step _ _ _ _ [] rfl (.read _ _ _ _ hm) (.nil _)
  have hmove : Steps code x [38] z := by
    simpa only [hpc] using
      (Steps.step x z z (.move 1 true 37) [] (by rw [hpc]; rfl)
        (.right _ _ _) (.nil _))
  refine ⟨y,_,GalilFppCopy.steps_append hrun
    (GalilFppCopy.steps_append hmove hread),rfl,?_,htA,?_,?_⟩
  · simpa [Ready,y,z] using hr
  · exact generation_output hrun (by omega)
  · have hS := hr.2.2.1
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

/-- A conservative linear bound for every actual FPP execution constructed here,
including initialization, all retries, output, and halt. -/
theorem initial_completed_cost (w : List (Fin 4)) :
    ∃ y qs, Completed code (initial w) qs y ∧
      y.output = GalilFppChain.borderValues w (failure w w.length) ∧
      y.pos 0 = 0 ∧ y.pc = 0 ∧ qs.length ≤ 390*w.length+4 := by
  by_cases hw : w.length = 0
  · have he : w = [] := by cases w <;> simp_all
    subst w
    obtain ⟨y,hs,hout,hpos,hpc⟩ := empty_completed
    exact ⟨y,_,hs,by simpa [failure_zero,GalilFppChain.borderValues] using hout,
      hpos,hpc,by simp⟩
  · obtain ⟨x,qs,hs,hp,hr,ht,hout,hcost⟩ := process_all_cost w (by omega)
    have hf := failure_le w w.length
    obtain ⟨y,rs,hrun,hl,hyout,hypos,hypc⟩ :=
      GalilFppChain.completed w (failure w w.length) x hp (by omega) ht hr
    refine ⟨y,_,GalilFppChain.steps_completed hs hrun,by simpa [hout] using hyout,
      hypos,hypc,?_⟩
    simp only [List.length_append]
    omega

#print axioms initial_completed_cost
#print axioms process_all_cost
#print axioms process_prefix_cost
#print axioms input_step_cost
#print axioms zero_miss_supply_cost
#print axioms hit_ready_cost
#print axioms search_supply_cost
end PalPeg.GalilFppGenerationCost
