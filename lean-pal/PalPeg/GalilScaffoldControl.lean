import PalPeg.GalilScaffoldProgram
import PalPeg.GalilDpCorrect

set_option autoImplicit false
namespace PalPeg.GalilScaffoldControl
open GalilFppWide (Instruction)
open GalilScaffoldProgram

structure Machine (n : ℕ) where
  config : Config n
  done : Bool

def start {n : ℕ} (entry : ℕ) (x : Machine n) : Machine n :=
  ⟨{ x.config with pc := entry }, false⟩

def reset {n : ℕ} (entry : ℕ) (_x : Machine n) : Machine n :=
  ⟨⟨entry, fun _ => GalilScaffoldTape.reset⟩, true⟩

/-- The enabled/done control protocol of raw instructionStep, over logical
stacks. Predicated expression evaluation and heap refinement remain separate. -/
inductive Tick {n : ℕ} (code : List (Instruction n)) : Bool → Machine n → Machine n → Prop
  | idle (x : Machine n) (enabled : Bool) (h : enabled = false ∨ x.done = true) : Tick code enabled x x
  | halt (x : Config n) (hi : code[x.pc]? = some .halt) : Tick code true ⟨x,false⟩ ⟨x,true⟩
  | execute (x y : Config n) (i : Instruction n)
      (hi : code[x.pc]? = some i) (he : Execute i x y) : Tick code true ⟨x,false⟩ ⟨y,false⟩

inductive Run {n : ℕ} (code : List (Instruction n)) : Machine n → List Bool → Machine n → Prop
  | nil (x : Machine n) : Run code x [] x
  | cons (x y z : Machine n) (b : Bool) (bs : List Bool)
      (hs : Tick code b x y) (hr : Run code y bs z) : Run code x (b :: bs) z

theorem run_append {n : ℕ} {code : List (Instruction n)} {x y z : Machine n}
    {bs cs : List Bool} (hb : Run code x bs y) (hc : Run code y cs z) :
    Run code x (bs ++ cs) z := by
  induction hb with
  | nil => exact hc
  | cons x y z b bs hs hr ih => exact .cons _ _ _ _ _ hs (ih hc)

theorem done_tick {n : ℕ} {code : List (Instruction n)} {b : Bool}
    {x y : Machine n} (hx : x.done = true) (hs : Tick code b x y) : y = x := by
  cases hs with
  | idle => rfl
  | halt => contradiction
  | execute => contradiction

theorem done_run {n : ℕ} (code : List (Instruction n)) (x : Machine n)
    (hx : x.done = true) (bs : List Bool) : Run code x bs x := by
  induction bs with
  | nil => exact .nil _
  | cons b bs ih => exact .cons _ _ _ _ _ (.idle x b (Or.inr hx)) ih

theorem pause_run {n : ℕ} (code : List (Instruction n)) (x : Machine n) (k : ℕ) :
    Run code x (List.replicate k false) x := by
  induction k with
  | zero => exact .nil _
  | succ k ih => simpa [List.replicate_succ] using Run.cons x x x false _ (.idle x false (Or.inl rfl)) ih

/-- A completed instruction trace sets done on its final halt, preserves
that halt PC, and consumes exactly one enabled tick per instruction. -/
theorem completed_run {n : ℕ} {code : List (Instruction n)}
    {x y : Config n} {qs : List ℕ} (hr : Completed code x qs y) :
    Run code ⟨x,false⟩ (List.replicate qs.length true) ⟨y,true⟩ := by
  induction hr with
  | halt x hi => exact .cons _ _ _ true [] (.halt x hi) (.nil _)
  | step x y z i qs hi he hr ih =>
    simpa [List.replicate_succ] using Run.cons ⟨x,false⟩ ⟨y,false⟩ ⟨z,true⟩ true _ (.execute x y i hi he) ih

/-- Extra calls after completion are harmless, whether enabled or paused. -/
theorem completed_padded {n : ℕ} {code : List (Instruction n)}
    {x y : Config n} {qs : List ℕ} (hr : Completed code x qs y) (bs : List Bool) :
    Run code ⟨x,false⟩ (List.replicate qs.length true ++ bs) ⟨y,true⟩ :=
  run_append (completed_run hr) (done_run code ⟨y,true⟩ rfl bs)

/-- Arbitrary pauses and post-halt ticks preserve the result. The caller
only needs to supply enough enabled ticks, counted in the real schedule. -/
theorem scheduled_completed {n : ℕ} {code : List (Instruction n)}
    {x y : Config n} {qs : List ℕ} (hr : Completed code x qs y)
    (bs : List Bool) (hc : qs.length ≤ bs.count true) :
    Run code ⟨x,false⟩ bs ⟨y,true⟩ := by
  induction bs generalizing x qs with
  | nil =>
    have hp : 0 < qs.length := by cases hr <;> simp
    have hz : qs.length = 0 := Nat.eq_zero_of_le_zero hc
    omega
  | cons b bs ih =>
    cases b with
    | false =>
      have hc' : qs.length ≤ bs.count true := by simpa using hc
      exact .cons _ _ _ false _ (.idle _ false (Or.inl rfl)) (ih hr hc')
    | true =>
      cases hr with
      | halt z hi =>
        exact .cons _ _ _ true _ (.halt _ hi) (done_run code ⟨y,true⟩ rfl bs)
      | step x v y i qs hi he hr =>
        have hc' : qs.length ≤ bs.count true := by simpa using hc
        exact .cons _ _ _ true _ (.execute x v i hi he) (ih hr hc')

theorem reset_denote {n : ℕ} (entry : ℕ) (x : Machine n) :
    denote (reset entry x).config =
      (⟨entry, fun _ _ => 6, fun _ => 0⟩ : GalilFppWide.Config n) := by
  apply wide_ext
  · rfl
  · funext t; exact GalilScaffoldTape.reset_blank
  · rfl

/-- DP correctness survives the logical-stack representation and any
schedule with enough enabled ticks. The initial representation equality
is explicit; physical loading and StackPool refinement are not assumed proved. -/
theorem dp_scheduled (w : List (Fin 3)) (lower : ℕ) (u : Config 12)
    (hu : denote u = GalilDpPrepared.initial w lower) :
    ∃ v qs, Completed GalilDpCode.code u qs v ∧
      GalilDpCorrect.Result w lower 0 (denote v) ∧
      ∀ bs : List Bool, qs.length ≤ bs.count true →
        Run GalilDpCode.code ⟨u,false⟩ bs ⟨v,true⟩ := by
  obtain ⟨y, qs, hr, hy⟩ := GalilDpCorrect.initial_correct w lower
  obtain ⟨v, hv, he⟩ := realize_completed hr u hu
  refine ⟨v, qs, hv, ?_, ?_⟩
  · rw [he]; exact hy
  · intro bs hb; exact scheduled_completed hv bs hb

#print axioms completed_run
#print axioms completed_padded
#print axioms reset_denote
#print axioms scheduled_completed
#print axioms dp_scheduled
end PalPeg.GalilScaffoldControl
