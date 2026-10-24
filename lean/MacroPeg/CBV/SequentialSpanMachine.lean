import MacroPeg.CBV.SequentialInputPair

/-! Scan a captured interval by rereading the original input at two cursors.
Only the original input and a fixed number of numeric registers are retained. -/
namespace Shallot.MacroPeg.CBV.SequentialSpanMachine
open Complexity Complexity.NBoundedTransfer
open SequentialInputRead (codes result)
variable {B : Nat}

/-- Registers 0--6 belong to character comparison; 7,8,9 hold the persistent
source cursor, target cursor, and remaining count (empty denotes failure). -/
def state (L : Lists 7) (a p : Nat) (C : List Nat) : Lists 10 := fun i =>
  if i=0 then L 0 else if i=1 then L 1 else if i=2 then L 2 else
  if i=3 then L 3 else if i=4 then L 4 else if i=5 then L 5 else
  if i=6 then L 6 else if i=7 then [a] else if i=8 then [p] else C

def reg (i : Fin 7) : Fin 10 := ⟨i.val,by omega⟩
theorem reg_injective : Function.Injective reg := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 10 => i.val) h

private theorem frame (L : Lists 7) (a p : Nat) (C : List Nat) (L' : Lists 7) :
    L'.frame reg (state L a p C) = state L' a p C := by
  funext j
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Lists.frame_get reg_injective _ _ 0
    | exact Lists.frame_get reg_injective _ _ 1
    | exact Lists.frame_get reg_injective _ _ 2
    | exact Lists.frame_get reg_injective _ _ 3
    | exact Lists.frame_get reg_injective _ _ 4
    | exact Lists.frame_get reg_injective _ _ 5
    | exact Lists.frame_get reg_injective _ _ 6
    | exact Lists.frame_outside _ _ _ (by intro ⟨i,hi⟩; have := congrArg Fin.val hi; simp [reg] at this; omega)

def blank (x : List Char) : Lists 7 := SequentialInputPair.state (codes x) [] [] [] []
def start (x : List Char) (a p k : Nat) : Lists 10 := state (blank x) a p [k]

def prepare : NProg 10 := .seq (.prim (.dup 7 2 (by decide))) (.prim (.dup 8 5 (by decide)))
def cleanup : NProg 10 := .seq (.prim (.pop 3)) (.prim (.pop 6))
def advance : NProg 10 := .seq (.prim (.dec 7)) (.seq (.prim (.dec 8)) (.prim (.dec 9)))
def guard : NProg 10 := .ite 3 .zero (.ite 6 .zero advance (.prim (.pop 9))) (.prim (.pop 9))
def body : NProg 10 := .seq prepare (.seq (SequentialInputPair.compare.rename reg reg_injective)
  (.seq guard cleanup))
def program : NProg 10 := .loop 9 .pos body

/-- A pure description of final cursor values, including the stopping position
on failure. It is related below to the existing capture matcher. -/
def scan (x : List Char) : Nat → Nat → Nat → Nat × Nat × Bool
  | 0,a,p => (a,p,true)
  | k+1,a,p => if result x a = result x p then scan x k (a-1) (p-1) else (a,p,false)

def output (x : List Char) (v : Nat × Nat × Bool) : Lists 10 :=
  state (blank x) v.1 v.2.1 (if v.2.2 then [0] else [])

def space (x : List Char) : Nat := SequentialInputRead.space x.length

private theorem state_fits (x : List Char) (L : Lists 7) (a p : Nat) (C : List Nat)
    (hL : NFits (space x) L) (ha : a ≤ x.length) (hp : p ≤ x.length)
    (hC : (Complexity.encS C).length+2 ≤ space x) : NFits (space x) (state L a p C) := by
  refine ⟨hL.1,fun i => ?_⟩
  have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hL.2 0
    | exact hL.2 1
    | exact hL.2 2
    | exact hL.2 3
    | exact hL.2 4
    | exact hL.2 5
    | exact hL.2 6
    | exact hC
    | (simp [state,Complexity.encS,encN]; unfold space SequentialInputRead.space; omega)

private theorem blank_fits (x : List Char) : NFits (space x) (blank x) := by
  have hh := SequentialInputRead.encoded_length x
  refine ⟨by unfold space SequentialInputRead.space; omega,fun i => ?_⟩
  by_cases hi : i=0
  · subst i
    change (Complexity.encS (codes x)).length+2 ≤ space x
    unfold space SequentialInputRead.space
    omega
  · simp [blank,SequentialInputPair.state,hi,Complexity.encS]
    unfold space SequentialInputRead.space
    omega

private theorem start_fits (x : List Char) (a p k : Nat)
    (ha : a ≤ x.length) (hp : p ≤ x.length) (hk : k ≤ a) : NFits (space x) (start x a p k) := by
  apply state_fits x _ a p [k] (blank_fits x) ha hp
  simp [Complexity.encS,encN]
  unfold space SequentialInputRead.space
  omega

private theorem dec_run (S : Lists 10) (i : Fin 10) (hS : NFits B S) :
    FitsRuns B (.prim (.dec i)) S ((NPrim.dec i).apply S) 1 :=
  ⟨1,Nat.le_refl _,.prim hS (NShrinkingCompare.fits_dec hS i)⟩

private theorem pop_run (S : Lists 10) (i : Fin 10) (hS : NFits B S) :
    FitsRuns B (.prim (.pop i)) S ((NPrim.pop i).apply S) 1 :=
  ⟨1,Nat.le_refl _,.prim hS (NShrinkingCompare.fits_pop hS i)⟩

private theorem prepare_runs (x : List Char) (a p k : Nat)
    (hS : NFits (space x) (start x a p k)) :
    FitsRuns (space x) prepare (start x a p k)
      (state (SequentialInputPair.state (codes x) [a] [] [p] []) a p [k]) 2 := by
  let S := start x a p k
  let A := (NPrim.dup (K := 10) 7 2 (by decide)).apply S
  let D := (NPrim.dup (K := 10) 8 5 (by decide)).apply A
  have hA : NFits (space x) A := by
    have hh := replace hS 2 [a] (hS.2 7)
    simpa [A,S,start,state,blank,SequentialInputPair.state,NPrim.apply] using hh
  have hD : NFits (space x) D := by
    have hh := replace hA 5 [p] (by simpa [A,S,start,state,NPrim.apply,Lists.set] using hS.2 8)
    simpa [D,A,S,start,state,blank,SequentialInputPair.state,NPrim.apply,Lists.set] using hh
  have heD : D = state (SequentialInputPair.state (codes x) [a] [] [p] []) a p [k] := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [D,A,S,start,state,blank,SequentialInputPair.state,NPrim.apply,Lists.set]
  rw [← heD]
  exact ⟨2,by omega,.seqC (.prim hS hA) (.prim hA hD)⟩

private theorem advance_runs (L : Lists 7) (a p k : Nat)
    (hS : NFits B (state L a p [k+1])) :
    FitsRuns B advance (state L a p [k+1]) (state L (a-1) (p-1) [k]) 3 := by
  let S := state L a p [k+1]
  have h₁ := dec_run S 7 hS
  have h₂ := dec_run _ 8 (NShrinkingCompare.fits_dec hS 7)
  have h₃ := dec_run _ 9 (NShrinkingCompare.fits_dec (NShrinkingCompare.fits_dec hS 7) 8)
  have he : (NPrim.dec 9).apply ((NPrim.dec 8).apply ((NPrim.dec 7).apply S)) =
      state L (a-1) (p-1) [k] := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S,state,NPrim.apply,Lists.set,mapTop]
  have hh := h₁.seq (h₂.seq h₃)
  rw [he] at hh
  exact hh

private theorem cleanup_runs (x : List Char) (a p u v : Nat) (C : List Nat)
    (hS : NFits B (state (SequentialInputPair.compared x a p) u v C)) :
    FitsRuns B cleanup (state (SequentialInputPair.compared x a p) u v C)
      (state (blank x) u v C) 2 := by
  let S := state (SequentialInputPair.compared x a p) u v C
  have h₁ := pop_run S 3 hS
  have h₂ := pop_run _ 6 (NShrinkingCompare.fits_pop hS 3)
  have he : (NPrim.pop 6).apply ((NPrim.pop 3).apply S) = state (blank x) u v C := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals by_cases h : result x a ≤ result x p <;>
      simp [S,state,blank,SequentialInputPair.compared,NShrinkingCompare.result,
        SequentialInputPair.state,NPrim.apply,Lists.set,h]
  have hh := h₁.seq h₂
  rw [he] at hh
  exact hh

def next (x : List Char) (a p k : Nat) : Lists 10 :=
  if result x a = result x p then state (blank x) (a-1) (p-1) [k]
  else state (blank x) a p []

private theorem guard_runs (x : List Char) (a p k : Nat)
    (hS : NFits B (state (SequentialInputPair.compared x a p) a p [k+1])) :
    FitsRuns B guard (state (SequentialInputPair.compared x a p) a p [k+1])
      (if result x a = result x p then state (SequentialInputPair.compared x a p) (a-1) (p-1) [k]
       else state (SequentialInputPair.compared x a p) a p []) 5 := by
  let S := state (SequentialInputPair.compared x a p) a p [k+1]
  have hz : (NTest.zero.eval (S 3) && NTest.zero.eval (S 6)) = decide (result x a = result x p) :=
    SequentialInputPair.equalTest_compared x a p
  by_cases heq : result x a = result x p
  · simp only [if_pos heq]
    have hz' : NTest.zero.eval (S 3) = true ∧ NTest.zero.eval (S 6) = true := by simpa [heq] using hz
    obtain ⟨h3,h6⟩ := hz'
    obtain ⟨t,ht,he⟩ := advance_runs _ a p k hS
    exact ⟨t+1+1,by omega,.iteT hS h3 (.iteT hS h6 he)⟩
  · simp only [if_neg heq]
    have hf : (NPrim.pop (K := 10) 9).apply S = state (SequentialInputPair.compared x a p) a p [] := by
      funext i
      by_cases hi : i=9
      · subst i; simp [S,state,NPrim.apply,Lists.set]
      · have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
        rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [S,state,NPrim.apply,Lists.set]
    obtain ⟨t,ht,he⟩ := pop_run S 9 hS
    rw [hf] at he
    cases h3 : NTest.zero.eval (S 3) with
    | false => exact ⟨t+1,by omega,.iteF hS h3 he⟩
    | true =>
      have h6 : NTest.zero.eval (S 6) = false := by simpa [heq,h3] using hz
      exact ⟨t+1+1,by omega,.iteT hS h3 (.iteF hS h6 he)⟩

theorem body_runs (x : List Char) (a p k : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length)
    (hk : k+1 ≤ a) :
    FitsRuns (space x) body (start x a p (k+1)) (next x a p k)
      (8*a+8*p+4*result x a+30) := by
  have hS := start_fits x a p (k+1) ha hp hk
  have hprep := prepare_runs x a p (k+1) hS
  have hD : NFits (space x) (state (SequentialInputPair.state (codes x) [a] [] [p] []) a p [k+1]) := by
    obtain ⟨_,_,he⟩ := hprep
    exact he.post
  have hcmp := (SequentialInputPair.compare_runs x a p ha hp).rename_frame reg_injective _ hD
  rw [frame,frame] at hcmp
  have hQ : NFits (space x) (state (SequentialInputPair.compared x a p) a p [k+1]) := by
    obtain ⟨_,_,he⟩ := hcmp
    exact he.post
  have hg := guard_runs x a p k hQ
  have hclean : FitsRuns (space x) cleanup
      (if result x a = result x p then state (SequentialInputPair.compared x a p) (a-1) (p-1) [k]
       else state (SequentialInputPair.compared x a p) a p []) (next x a p k) 2 := by
    have hh : NFits (space x) (if result x a = result x p then state (SequentialInputPair.compared x a p) (a-1) (p-1) [k]
        else state (SequentialInputPair.compared x a p) a p []) := by
      obtain ⟨_,_,he⟩ := hg
      exact he.post
    by_cases heq : result x a = result x p
    · simp only [if_pos heq] at hh ⊢
      simpa only [next,if_pos heq] using cleanup_runs x a p (a-1) (p-1) [k] hh
    · simp only [if_neg heq] at hh ⊢
      simpa only [next,if_neg heq] using cleanup_runs x a p a p [] hh
  obtain ⟨t,ht,he⟩ := hprep.seq (hcmp.seq (hg.seq hclean))
  exact ⟨t,by omega,he⟩

def stepTime (x : List Char) : Nat := 16*x.length+4*2^32+31

private theorem result_bound (x : List Char) (a : Nat) : result x a ≤ 2^32 := by
  cases hs : sfx x a with
  | nil => simp [result,hs]
  | cons c cs => simpa only [result,hs] using SequentialInputRead.code_bound c

/-- The complete loop is compiled once; the capture length is only runtime
data. No substring and no input-dependent program unrolling is used. -/
theorem loop_runs (x : List Char) (k a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length)
    (hk : k ≤ a) :
    FitsRuns (space x) program (start x a p k) (output x (scan x k a p))
      (k*stepTime x+1) := by
  induction k generalizing a p with
  | zero =>
    have hS := start_fits x a p 0 ha hp hk
    exact ⟨1,by simp,.loopF hS (by simp [start,state,NTest.eval])⟩
  | succ k ih =>
    have hS := start_fits x a p (k+1) ha hp hk
    have hb := body_runs x a p k ha hp hk
    have hc : 8*a+8*p+4*result x a+31 ≤ stepTime x := by
      have hh := result_bound x a
      unfold stepTime
      omega
    by_cases heq : result x a = result x p
    · have hr := ih (a-1) (p-1) (by omega) (by omega) (by omega)
      simp only [next,if_pos heq] at hb
      obtain ⟨t,ht,he⟩ := hb
      obtain ⟨u,hu,huE⟩ := hr
      refine ⟨t+1+u,?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · simpa only [program,scan,if_pos heq] using
          (NExec.loopC hS (by simp [start,state,NTest.eval]) he huE)
    · have hF : NFits (space x) (state (blank x) a p []) := by
        obtain ⟨_,_,he⟩ := hb
        have hh : NFits (space x) (next x a p k) := he.post
        simpa only [next,if_neg heq] using hh
      simp only [next,if_neg heq] at hb
      obtain ⟨t,ht,he⟩ := hb
      refine ⟨t+1+1,?_,?_⟩
      · rw [Nat.succ_mul]
        omega
      · simpa only [program,scan,if_neg heq,output,Bool.false_eq_true,if_false] using
          (NExec.loopC hS (by simp [start,state,NTest.eval]) he
            (NExec.loopF hF (by simp [state,NTest.eval])))

/-- The runtime loop computes exactly the original capture matcher. -/
theorem scan_correct (x : List Char) (k a p : Nat) (ha : a ≤ x.length) (hp : p ≤ x.length)
    (hk : k ≤ a) :
    (if (scan x k a p).2.2 then some (scan x k a p).2.1 else none) =
      SequentialSpanRecompute.matchCount k (sfx x a) (sfx x p) := by
  induction k generalizing a p with
  | zero => simp [scan,SequentialSpanRecompute.matchCount,length_sfx x hp]
  | succ k ih =>
    rw [SequentialInputPair.matchCount_step x a p k ha hp hk,SequentialInputPair.equalTest_compared]
    by_cases heq : result x a = result x p
    · simpa [scan,heq] using
        ih (a-1) (p-1) (by omega) (by omega) (by omega)
    · simp [scan,heq]

/-- Convert the stored interval endpoint b into the remaining count a-b. -/
def setup : NProg 10 := .seq (.prim (.dup 9 2 (by decide)))
  (.seq (.prim (.pop 9)) (.seq (.prim (.dup 7 9 (by decide)))
    (.seq (NShrinkingCompare.program 2 9) (.prim (.pop 2)))))

theorem setup_runs (x : List Char) (a b p : Nat) (hb : b ≤ a)
    (ha : a ≤ x.length) (hp : p ≤ x.length) :
    FitsRuns (space x) setup (start x a p b) (start x a p (a-b)) (4*b+5) := by
  let S := start x a p b
  let A := S.set 2 [b]
  let D := A.set 9 []
  let E := D.set 9 [a]
  have hS := start_fits x a p b ha hp hb
  have hA : NFits (space x) A := replace hS 2 [b] (hS.2 9)
  have hD : NFits (space x) D := by
    have hh := NShrinkingCompare.fits_pop hA 9
    simpa [NPrim.apply,A,S,start,state,Lists.set,D] using hh
  have hE : NFits (space x) E := replace hD 9 [a] (hS.2 7)
  have h₁ : FitsRuns (space x) (.prim (.dup 9 2 (by decide))) S A 1 := by
    have hh : (NPrim.dup (K := 10) 9 2 (by decide)).apply S = A := by
      simp [NPrim.apply,S,start,state,blank,SequentialInputPair.state,A]
    refine ⟨1,by omega,?_⟩
    rw [← hh]
    exact .prim hS (by rwa [hh])
  have h₂ : FitsRuns (space x) (.prim (.pop 9)) A D 1 := by
    simpa [NPrim.apply,A,S,start,state,Lists.set,D] using pop_run A 9 hA
  have h₃ : FitsRuns (space x) (.prim (.dup 7 9 (by decide))) D E 1 := by
    have hh : (NPrim.dup (K := 10) 7 9 (by decide)).apply D = E := by
      simp [NPrim.apply,D,A,S,start,state,Lists.set,E]
    refine ⟨1,by omega,?_⟩
    rw [← hh]
    exact .prim hD (by rwa [hh])
  have hcmp : FitsRuns (space x) (NShrinkingCompare.program 2 9) E
      (NShrinkingCompare.result E 2 9 [] b a) (4*b+1) :=
    NShrinkingCompare.exec (K := 10) 2 9 (by decide) b a E []
    (by simp [E,D,A,Lists.set]) (by simp [E]) hE
  let F := NShrinkingCompare.result E 2 9 [] b a
  have hF : NFits (space x) F := by obtain ⟨_,_,he⟩ := hcmp; exact he.post
  have h₄ := pop_run F 2 hF
  have he : (NPrim.pop 2).apply F = start x a p (a-b) := by
    funext i
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [F,E,D,A,S,start,state,blank,SequentialInputPair.state,
        NShrinkingCompare.result,Lists.set,NPrim.apply,hb]
  rw [he] at h₄
  obtain ⟨t,ht,he⟩ := h₁.seq (h₂.seq (h₃.seq (hcmp.seq h₄)))
  exact ⟨t,by omega,he⟩

def spanProgram : NProg 10 := .seq setup program

def value (S : Lists 10) : Option Nat :=
  if NTest.zero.eval (S 9) then (S 8).getLast? else none

theorem value_output (x : List Char) (v : Nat × Nat × Bool) :
    value (output x v) = if v.2.2 then some v.2.1 else none := by
  obtain ⟨a,p,b⟩ := v
  cases b <;> simp [value,output,state,NTest.eval]

theorem span_runs (x : List Char) (a b p : Nat) (hb : b ≤ a)
    (ha : a ≤ x.length) (hp : p ≤ x.length) :
    FitsRuns (space x) spanProgram (start x a p b) (output x (scan x (a-b) a p))
      (4*b+5+((a-b)*stepTime x+1)) :=
  (setup_runs x a b p hb ha hp).seq (loop_runs x (a-b) a p ha hp (by omega))

theorem span_value (x : List Char) (a b p : Nat)
    (ha : a ≤ x.length) (hp : p ≤ x.length) :
    some (value (output x (scan x (a-b) a p))) = SequentialSpanRecompute.matchSpan x a b p := by
  rw [value_output,scan_correct x (a-b) a p ha hp (by omega)]
  rfl

theorem compiled_span (x : List Char) (a b p : Nat) (hb : b ≤ a)
    (ha : a ≤ x.length) (hp : p ≤ x.length) :
    Runs (LenOK (space x)) spanProgram.compile (encL (start x a p b))
      (encL (output x (scan x (a-b) a p)))
      ((4*b+5+((a-b)*stepTime x+1))*ncost (space x)) := by
  obtain ⟨t,ht,he⟩ := span_runs x a b p hb ha hp
  obtain ⟨u,hu,h⟩ := nexec_compile (fun _ h => h) he
  exact ⟨u,Nat.le_trans hu (Nat.mul_le_mul_right _ ht),h⟩

theorem span_tape (x : List Char) (a b p : Nat) (hb : b ≤ a)
    (ha : a ≤ x.length) (hp : p ≤ x.length) (τ : Tapes 11)
    (hτ : Rep (encL (start x a p b)) τ) :
    ∃ t τ', Exec (TFits (space x)) spanProgram.compile.compile τ t (.cont τ') ∧
      Rep (encL (output x (scan x (a-b) a p))) τ' ∧
      some (value (output x (scan x (a-b) a p))) = SequentialSpanRecompute.matchSpan x a b p := by
  obtain ⟨t,τ',_,he,hr⟩ := Complexity.BinaryWord.runs_tape (compiled_span x a b p hb ha hp) τ hτ
  exact ⟨t,τ',he,hr,span_value x a b p ha hp⟩

end Shallot.MacroPeg.CBV.SequentialSpanMachine
