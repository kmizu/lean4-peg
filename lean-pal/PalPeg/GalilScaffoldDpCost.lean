import PalPeg.GalilDpCost
import PalPeg.GalilScaffoldPreload

set_option autoImplicit false
namespace PalPeg.GalilScaffoldDpCost
open GalilScaffoldProgram GalilScaffoldControl

/-- A concrete enabled-tick budget, rather than an existential trace length. -/
theorem scheduled_correct (w : List (Fin 3)) (lower : ℕ) :
    ∃ v, GalilDpCorrect.Result w lower 0 (denote v) ∧
      ∀ bs : List Bool, 3186*w.length+1683 ≤ bs.count true →
        Run GalilDpCode.code ⟨GalilScaffoldPreload.initial w lower,false⟩ bs ⟨v,true⟩ := by
  obtain ⟨y,qs,hr,hy,hcost⟩ := GalilDpCost.initial_correct_cost w lower
  obtain ⟨v,hv,he⟩ := realize_completed hr (GalilScaffoldPreload.initial w lower)
    (GalilScaffoldPreload.initial_denote w lower)
  refine ⟨v,?_,?_⟩
  · rw [he]; exact hy
  · intro bs hb
    exact scheduled_completed hv bs (hcost.trans hb)

/-- Requested instruction opportunities, with calls suppressed after halt.
This isolates the done-sensitive part of Search's run-mode guard. -/
inductive GuardedRun {n : ℕ} (code : List (GalilFppWide.Instruction n)) :
    Machine n → List Bool → Machine n → Prop
  | nil (x : Machine n) : GuardedRun code x [] x
  | cons (x y z : Machine n) (b : Bool) (bs : List Bool)
      (hs : Tick code (b && !x.done) x y) (hr : GuardedRun code y bs z) :
      GuardedRun code x (b :: bs) z

theorem guard_run {n : ℕ} {code : List (GalilFppWide.Instruction n)}
    {x y : Machine n} {bs : List Bool} (hr : Run code x bs y) :
    GuardedRun code x bs y := by
  induction hr with
  | nil => exact .nil _
  | cons x y z b bs hs hr ih =>
    refine .cons x y z b bs ?_ ih
    cases hs with
    | idle x b h =>
      apply Tick.idle
      rcases h with h | h
      · simp [h]
      · exact Or.inr h
    | halt x hi => exact .halt x hi
    | execute x y i hi he => exact .execute x y i hi he

/-- With quantum 64, this many requested slots suffice even when calls
after completion are suppressed. Actual Search mode scheduling is separate. -/
theorem quantum64_correct (w : List (Fin 3)) (lower : ℕ) :
    ∃ v, GalilDpCorrect.Result w lower 0 (denote v) ∧
      GuardedRun GalilDpCode.code ⟨GalilScaffoldPreload.initial w lower,false⟩
        (List.replicate (64*(50*w.length+27)) true) ⟨v,true⟩ := by
  obtain ⟨v,hv,hr⟩ := scheduled_correct w lower
  refine ⟨v,hv,guard_run (hr _ ?_)⟩
  simp
  omega

#print axioms quantum64_correct
#print axioms scheduled_correct
end PalPeg.GalilScaffoldDpCost
