import PalPeg.GalilScaffoldTopFpp

/-!
# Quantum existence for the marked FPP program

`GalilTickFun3.FppEnabled q s` assumes

```
∃ p, GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program
        (List.replicate q true) p
```

i.e. that a whole quantum of `q` *enabled* control ticks can actually be
taken.  This is not free: `GalilScaffoldControl.Tick code true` refuses to
step unless the program counter is in range *and* the instruction found
there is executable (`Execute` blocks on a left move at the left tape edge
and on a `read` whose focus symbol is not covered by the choice table).
Only a machine that is already `done` can idle through an enabled tick.

This module reduces the quantum-existence assumption to a *local safety
invariant* on the reachable set, and then splits that invariant into two
independent obligations:

* a program-counter obligation, which is fully discharged here from a single
  initial condition by `reach_pc_lt` plus the decidable fact
  `marked_targets_lt` (every jump target of the marked code is in range), and
* an instruction-legality obligation (`Legal`), which is *not* discharged
  here and is the residual gap.
-/

set_option autoImplicit false
namespace PalPeg.GalilFppQuantum
open GalilFppWide (Instruction)
open GalilScaffoldProgram
open GalilScaffoldControl

variable {n : ℕ}

/-! ## Local steppability -/

/-- The successor program counters an instruction can jump to. -/
def targets : Instruction n → List ℕ
  | .halt => []
  | .move _ _ pc => [pc]
  | .write _ _ pc => [pc]
  | .read _ cs => cs.map Prod.snd

/-- The side condition under which the instruction `i` is executable in the
configuration `x`.  `halt` and `write` are unconditional, a right move is
unconditional, a left move needs a non-empty left stack, and a `read` needs
its choice table to cover the focused symbol. -/
def Legal (x : Config n) : Instruction n → Prop
  | .halt => True
  | .move t right _ => right = true ∨ (x.tapes t).left ≠ []
  | .write _ _ _ => True
  | .read t cs => ∃ pc, ((x.tapes t).focus, pc) ∈ cs

/-- A configuration from which some enabled tick is possible. -/
def CanStep (code : List (Instruction n)) (x : Config n) : Prop :=
  code[x.pc]? = some .halt ∨ ∃ i y, code[x.pc]? = some i ∧ Execute i x y

/-- A machine state that cannot block on an enabled tick: either it is
already `done` (and idles), or its current instruction can fire. -/
def Safe (code : List (Instruction n)) (m : Machine n) : Prop :=
  m.done = true ∨ CanStep code m.config

theorem canStep_of_legal {code : List (Instruction n)} {x : Config n} {i : Instruction n}
    (hi : code[x.pc]? = some i) (h : Legal x i) : CanStep code x := by
  cases i with
  | halt => exact Or.inl hi
  | move t r pc =>
    cases r with
    | true => exact Or.inr ⟨_, _, hi, .right x t pc⟩
    | false =>
      have hl : (x.tapes t).left ≠ [] := by
        rcases h with h | h
        · exact absurd h (by simp)
        · exact h
      exact Or.inr ⟨_, _, hi, .left x t pc hl⟩
  | write t s pc => exact Or.inr ⟨_, _, hi, .write x t s pc⟩
  | read t cs =>
    obtain ⟨pc, hm⟩ := h
    exact Or.inr ⟨_, _, hi, .read x t cs pc hm⟩

theorem tick_of_safe {code : List (Instruction n)} {m : Machine n} (h : Safe code m) :
    ∃ p, Tick code true m p := by
  obtain ⟨x, d⟩ := m
  cases d with
  | true => exact ⟨⟨x, true⟩, .idle _ true (Or.inr rfl)⟩
  | false =>
    rcases h with h | h
    · exact absurd h (by simp)
    · rcases h with h | ⟨i, y, hi, he⟩
      · exact ⟨⟨x, true⟩, .halt x h⟩
      · exact ⟨⟨y, false⟩, .execute x y i hi he⟩

/-! ## Reachability under enabled ticks -/

inductive Reach (code : List (Instruction n)) (m : Machine n) : Machine n → Prop
  | refl : Reach code m m
  | step {x y : Machine n} : Reach code m x → Tick code true x y → Reach code m y

/-- **The reduction.**  If every state reachable by enabled ticks is safe,
then runs of every length exist. -/
theorem run_exists_of_reachSafe {code : List (Instruction n)} {m : Machine n}
    (hsafe : ∀ x, Reach code m x → Safe code x) (q : ℕ) :
    ∃ p, Run code m (List.replicate q true) p ∧ Reach code m p := by
  induction q with
  | zero => exact ⟨m, .nil m, .refl⟩
  | succ q ih =>
    obtain ⟨p, hrun, hre⟩ := ih
    obtain ⟨p', ht⟩ := tick_of_safe (hsafe p hre)
    refine ⟨p', ?_, .step hre ht⟩
    have hrep : List.replicate (q + 1) true = List.replicate q true ++ [true] := by
      simp [List.replicate_succ']
    rw [hrep]
    exact run_append hrun (.cons p p' p' true [] ht (.nil p'))

/-! ## The program-counter obligation is dischargeable -/

theorem execute_target {i : Instruction n} {x y : Config n} (he : Execute i x y) :
    y.pc ∈ targets i := by
  cases he with
  | right x t pc => simp [targets, changed]
  | left x t pc h => simp [targets, changed]
  | write x t s pc => simp [targets, changed]
  | read x t cs pc hm =>
    simp only [targets, List.mem_map]
    exact ⟨((x.tapes t).focus, pc), hm, rfl⟩

theorem tick_pc_lt {code : List (Instruction n)}
    (hin : ∀ i ∈ code, ∀ pc ∈ targets i, pc < code.length)
    {x y : Machine n} (ht : Tick code true x y)
    (hx : x.done = true ∨ x.config.pc < code.length) :
    y.done = true ∨ y.config.pc < code.length := by
  cases ht with
  | idle x e h => exact hx
  | halt x hi => exact Or.inl rfl
  | execute x y i hi he =>
    exact Or.inr (hin i (List.mem_of_getElem? hi) y.pc (execute_target he))

/-- Reachable states never fall off the end of the code, given that the
initial state does not. -/
theorem reach_pc_lt {code : List (Instruction n)} {m : Machine n}
    (hin : ∀ i ∈ code, ∀ pc ∈ targets i, pc < code.length)
    (hm : m.done = true ∨ m.config.pc < code.length) :
    ∀ x, Reach code m x → x.done = true ∨ x.config.pc < code.length := by
  intro x hx
  induction hx with
  | refl => exact hm
  | step hr ht ih => exact tick_pc_lt hin ht ih

/-- Splitting the safety invariant: the pc obligation (already dischargeable)
and the legality obligation (the residual gap). -/
theorem reachSafe_of_legal {code : List (Instruction n)} {m : Machine n}
    (hpc : ∀ x, Reach code m x → x.done = true ∨ x.config.pc < code.length)
    (hlegal : ∀ x, Reach code m x → x.done = false →
      ∀ i, code[x.config.pc]? = some i → Legal x.config i) :
    ∀ x, Reach code m x → Safe code x := by
  intro x hx
  cases hd : x.done with
  | true => exact Or.inl hd
  | false =>
    rcases hpc x hx with h | h
    · rw [hd] at h; exact absurd h (by simp)
    · obtain ⟨i, hi⟩ : ∃ i, code[x.config.pc]? = some i :=
        ⟨code[x.config.pc]'h, List.getElem?_eq_getElem h⟩
      exact Or.inr (canStep_of_legal hi (hlegal x hx hd i hi))

/-! ## The marked FPP program -/

set_option maxRecDepth 100000 in
theorem marked_length : GalilFppMarkedCode.code.length = 321 := by rfl

set_option maxRecDepth 100000 in
theorem marked_targets_lt :
    ∀ i ∈ GalilFppMarkedCode.code, ∀ pc ∈ targets i, pc < GalilFppMarkedCode.code.length := by
  decide

/-- The published entry point is in range, so the pc side condition holds at
the start of the program. -/
theorem marked_start_lt : GalilFppMarkedCode.start < GalilFppMarkedCode.code.length := by
  rw [marked_length]; exact Nat.lt_succ_self 320

/-- **The requested lemma.**  Quantum existence for the marked FPP code,
under the reachable-state safety invariant. -/
theorem fpp_run_exists (m : Machine 9)
    (hreach : ∀ x, Reach GalilFppMarkedCode.code m x → Safe GalilFppMarkedCode.code x)
    (q : ℕ) :
    ∃ p, Run GalilFppMarkedCode.code m (List.replicate q true) p := by
  obtain ⟨p, hp, _⟩ := run_exists_of_reachSafe hreach q
  exact ⟨p, hp⟩

/-- The same, with the invariant split: the pc side is discharged from the
single initial condition `m.config.pc < 321`, so only `Legal` remains. -/
theorem fpp_run_exists_of_legal (m : Machine 9)
    (hm : m.done = true ∨ m.config.pc < 321)
    (hlegal : ∀ x, Reach GalilFppMarkedCode.code m x → x.done = false →
      ∀ i, GalilFppMarkedCode.code[x.config.pc]? = some i → Legal x.config i)
    (q : ℕ) :
    ∃ p, Run GalilFppMarkedCode.code m (List.replicate q true) p := by
  refine fpp_run_exists m (reachSafe_of_legal ?_ hlegal) q
  exact reach_pc_lt marked_targets_lt (by rw [marked_length]; exact hm)

#print axioms canStep_of_legal
#print axioms tick_of_safe
#print axioms run_exists_of_reachSafe
#print axioms execute_target
#print axioms reach_pc_lt
#print axioms reachSafe_of_legal
#print axioms marked_length
#print axioms marked_targets_lt
#print axioms marked_start_lt
#print axioms fpp_run_exists
#print axioms fpp_run_exists_of_legal
end PalPeg.GalilFppQuantum
