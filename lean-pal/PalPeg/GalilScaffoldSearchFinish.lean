import PalPeg.GalilScaffoldRawSchedule

set_option autoImplicit false
namespace PalPeg.GalilScaffoldSearchFinish
open GalilScaffoldCounter (Counter)

inductive Mode
  | idle | grow | lower | lowerHome | copy | home | run | found | missed | wait | double
  deriving DecidableEq

structure State where
  mode : Mode
  finalStage : Bool
  span : Counter
  work : Counter
  debt : Counter
  quarter : Fin 4

/-- Post-program-step portion of Scala Search.runStep, including double's
counter copies/reset. The program execution itself has already occurred. -/
def finish (s : State) (enabled done : Bool) (pc : ℕ) : State :=
  if enabled && done then
    if pc = 346 then {s with mode := .found}
    else if s.finalStage then {s with mode := .missed}
    else if GalilScaffoldCounter.zero s.debt then
      {s with mode := .double,work := s.span,span := GalilScaffoldCounter.reset,quarter := 0}
    else {s with mode := .wait}
  else s

theorem idle (s : State) (enabled done : Bool) (pc : ℕ)
    (hi : enabled = false ∨ done = false) : finish s enabled done pc = s := by
  rcases hi with hi | hi <;> simp [finish,hi]

theorem found_iff (s : State) (pc : ℕ) : (finish s true true pc).mode = .found ↔ pc = 346 := by
  by_cases hp : pc = 346
  · simp [finish,hp]
  · cases hf : s.finalStage <;> cases hz : GalilScaffoldCounter.zero s.debt <;> simp [finish,hp,hf,hz]

theorem debt_guard (s : State) (hc : GalilScaffoldCounter.Canonical s.debt)
    (hn : 0 ≤ GalilScaffoldCounter.value s.debt) : GalilScaffoldCounter.negative s.debt ≠ true := by
  intro he
  have hv := (GalilScaffoldCounter.negative_iff s.debt hc).mp he
  omega

theorem result_found {w : List (Fin 3)} {lower first : ℕ} {y : GalilFppWide.Config 12}
    (hr : GalilDpCorrect.Result w lower first y) (s : State) :
    (finish s true true y.pc).mode = .found ↔
      ∃ k, first ≤ k ∧ GalilDpCorrect.Candidate w lower k := by
  rw [found_iff]
  rcases hr with ⟨k,hk,hc,hmin,hp,ho⟩ | ⟨hp,hn⟩
  · exact ⟨fun _ => ⟨k,hk,hc⟩,fun _ => hp⟩
  · constructor
    · intro he; omega
    · rintro ⟨k,hk,hc⟩; exact False.elim (hn k hk hc)

theorem failed_branches (s : State) :
    finish s true true 347 =
      if s.finalStage then {s with mode := .missed}
      else if GalilScaffoldCounter.zero s.debt then
        {s with mode := .double,work := s.span,span := GalilScaffoldCounter.reset,quarter := 0}
      else {s with mode := .wait} := by simp [finish]

theorem failed_no_candidate {w : List (Fin 3)} {lower first : ℕ} {y : GalilFppWide.Config 12}
    (hr : GalilDpCorrect.Result w lower first y) (hp : y.pc = 347) :
    ∀ k, first ≤ k → ¬ GalilDpCorrect.Candidate w lower k := by
  rcases hr with ⟨k,hk,hc,hmin,he,ho⟩ | ⟨_,hn⟩
  · omega
  · exact hn

/-- Search.start swaps the radius counter's roots; debt is initially -radius,
so global debt nonnegativity is not a valid invariant. -/
def initialDebt (radius : Counter) : Counter := ⟨radius.neg,radius.pos⟩

/-- Search.start's scheduling-state projection. The lower root is also
aliased separately and the program reset is a separate machine operation. -/
def begin (lower radius : Counter) : State :=
  ⟨.grow,false,GalilScaffoldCounter.reset,
    if GalilScaffoldCounter.zero lower then GalilScaffoldCounter.inc lower else lower,
    initialDebt radius,0⟩

theorem begin_positive (lower radius : Counter)
    (hp : GalilScaffoldCounter.positive lower = true) :
    (begin lower radius).mode = .grow ∧ (begin lower radius).work = lower ∧
      (begin lower radius).span = GalilScaffoldCounter.reset ∧
      (begin lower radius).debt = initialDebt radius ∧
      (begin lower radius).finalStage = false ∧ (begin lower radius).quarter = 0 := by
  have hz : GalilScaffoldCounter.zero lower = false := by
    cases he : lower.pos.isEmpty <;>
      simp_all [GalilScaffoldCounter.positive,GalilScaffoldCounter.zero]
  simp [begin,hz]

theorem initial_balance (radius : Counter) :
    GalilScaffoldCounter.value (initialDebt radius) + GalilScaffoldCounter.value radius = 0 := by
  simp only [initialDebt,GalilScaffoldCounter.value]
  omega

/-- Search.start's program, lower root value, and scheduler projection.
Counter values model root copies; physical alias encoding is separate. -/
structure SearchState (n slots : ℕ) where
  program : GalilScaffoldRawTick.Machine n slots
  lower : Counter
  scheduler : State

def startSearch {n slots : ℕ} (entry : ℕ) (lower radius : Counter)
    (s : SearchState n slots) : SearchState n slots :=
  ⟨GalilScaffoldRawTick.reset entry s.program,lower,begin lower radius⟩

theorem startSearch_positive {n slots : ℕ} (entry : ℕ) (lower radius : Counter)
    (s : SearchState n slots) (hp : GalilScaffoldCounter.positive lower = true) :
    let t := startSearch entry lower radius s
    GalilScaffoldRawTick.Represents t.program
      ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ ∧
    t.program.config.heap = s.program.config.heap ∧
    t.lower = lower ∧ t.scheduler.mode = .grow ∧ t.scheduler.work = t.lower ∧
    t.scheduler.span = GalilScaffoldCounter.reset ∧
    GalilScaffoldCounter.value t.scheduler.debt + GalilScaffoldCounter.value radius = 0 ∧
    t.scheduler.finalStage = false ∧ t.scheduler.quarter = 0 := by
  obtain ⟨hm,hw,hs,hd,hf,hq⟩ := begin_positive lower radius hp
  exact ⟨GalilScaffoldRawTick.reset_represents entry s.program,rfl,rfl,hm,hw,hs,
    hd ▸ initial_balance radius,hf,hq⟩

#print axioms startSearch_positive

theorem advance_balance (radius debt : Counter) :
    GalilScaffoldCounter.value (GalilScaffoldCounter.dec debt) +
      GalilScaffoldCounter.value (GalilScaffoldCounter.inc radius) =
    GalilScaffoldCounter.value debt + GalilScaffoldCounter.value radius := by
  rw [GalilScaffoldCounter.dec_value,GalilScaffoldCounter.inc_value]
  omega

theorem grow_balance (radius debt : Counter) :
    GalilScaffoldCounter.value (GalilScaffoldCounter.inc (GalilScaffoldCounter.inc debt)) +
      GalilScaffoldCounter.value radius =
    GalilScaffoldCounter.value debt + GalilScaffoldCounter.value radius + 2 := by
  rw [GalilScaffoldCounter.inc_value,GalilScaffoldCounter.inc_value]
  omega

theorem quarter_balance (radius debt : Counter) :
    GalilScaffoldCounter.value (GalilScaffoldCounter.inc debt) + GalilScaffoldCounter.value radius =
    GalilScaffoldCounter.value debt + GalilScaffoldCounter.value radius + 1 := by
  rw [GalilScaffoldCounter.inc_value]
  omega

/-- At a guarded boundary, the exact remaining scheduling obligation is
radius <= accumulated grow/doubling credits. This bound is not assumed globally. -/
theorem boundary_guard (s : State) (radius : Counter) (credits : ℤ)
    (hc : GalilScaffoldCounter.Canonical s.debt)
    (hb : GalilScaffoldCounter.value s.debt + GalilScaffoldCounter.value radius = credits)
    (hs : GalilScaffoldCounter.value radius ≤ credits) :
    GalilScaffoldCounter.negative s.debt ≠ true := by
  apply debt_guard s hc
  omega

#print axioms initial_balance
#print axioms advance_balance
#print axioms boundary_guard
#print axioms result_found
#print axioms debt_guard
#print axioms failed_no_candidate
end PalPeg.GalilScaffoldSearchFinish
