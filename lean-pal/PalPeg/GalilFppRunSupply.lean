import PalPeg.GalilFppQuantum
import PalPeg.GalilTickFun3

/-!
# Quantum existence for the marked FPP program, from its correctness run

`GalilTickFun3.FppEnabled q s` asks for

```
∃ p, GalilScaffoldControl.Run GalilFppMarkedCode.code s.fpp.program
       (List.replicate q true) p
```

`GalilFppQuantum` reduced this to a `Legal`/`Safe` reachability invariant and
left the legality half open.  This module closes the gap *without* that
invariant, by reusing the halting run that the marked-FPP correctness theorem
already builds: `fpp_scheduled` produces, for the fallback window `w`, a run

```
Run GalilFppMarkedCode.code ⟨fppInitial w, false⟩ (List.replicate N true) ⟨v, true⟩
```

with `N = 1584·|w| + 830`.  A shorter quantum is a *prefix* of that run
(`run_prefix`), and a longer one is that run extended by `idle` ticks, which
are always available once `done = true` (`run_idle_after_done`).  Hence every
`q` is served (`Supplies`).  The intermediate machines the controller visits
along the fpp phase (one `fpp_slice` tick consumes `q` enabled events) are
reached by a run from the entry machine, so they inherit the property
(`run_split` / `supplies_run`), by determinism of enabled control ticks.
-/

set_option autoImplicit false
namespace PalPeg.GalilFppRunSupply
open GalilFppWide (Instruction)
open GalilScaffoldControl
open PalPeg.GalilScaffoldChainInputSupply

variable {n : ℕ}

/-! ## The supply property -/

/-- A machine that can serve a quantum of *any* size: for every `q` there is
a run of `q` enabled control ticks out of it. -/
def Supplies (code : List (Instruction n)) (m : Machine n) : Prop :=
  ∀ q : ℕ, ∃ p, Run code m (List.replicate q true) p

/-! ## The two halves -/

/-- **Prefix.** Any initial segment of a run is itself a run. -/
theorem run_prefix {code : List (Instruction n)} :
    ∀ {as bs : List Bool} {m p : Machine n},
      Run code m (as ++ bs) p → ∃ m', Run code m as m' := by
  intro as
  induction as with
  | nil => intro bs m p _; exact ⟨m, .nil m⟩
  | cons a as ih =>
    intro bs m p h
    rw [List.cons_append] at h
    cases h with
    | cons _ y _ _ _ ht hr =>
      obtain ⟨m', hm'⟩ := ih hr
      exact ⟨m', .cons _ _ _ _ _ ht hm'⟩

/-- **Idle extension.** A halted machine idles through enabled ticks, so it
serves every quantum at no cost. -/
theorem run_idle_after_done {code : List (Instruction n)} {m : Machine n}
    (hd : m.done = true) (q : ℕ) : Run code m (List.replicate q true) m :=
  done_run code m hd _

theorem supplies_of_done {code : List (Instruction n)} {m : Machine n}
    (hd : m.done = true) : Supplies code m :=
  fun q => ⟨m, run_idle_after_done hd q⟩

/-- **The construction.** A machine with a halting run of *some* length
serves every quantum: shorter quanta by `run_prefix`, longer ones by
`run_idle_after_done` past the halt. -/
theorem supplies_of_halting {code : List (Instruction n)} {m f : Machine n} {N : ℕ}
    (hrun : Run code m (List.replicate N true) f) (hdone : f.done = true) :
    Supplies code m := by
  intro q
  rcases Nat.le_total q N with h | h
  · have hsplit : List.replicate N true
        = List.replicate q true ++ List.replicate (N - q) true := by
      rw [← List.replicate_add]; congr 1; omega
    rw [hsplit] at hrun
    exact run_prefix hrun
  · refine ⟨f, ?_⟩
    have hsplit : List.replicate q true
        = List.replicate N true ++ List.replicate (q - N) true := by
      rw [← List.replicate_add]; congr 1; omega
    rw [hsplit]
    exact run_append hrun (run_idle_after_done hdone _)

/-! ## Stability along the phase -/

/-- **Splitting.** A run out of `m` of length `k + q` factors through the
unique machine reached after `k` enabled ticks. -/
theorem run_split {code : List (Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i)
    {m m' p : Machine n} {k q : ℕ}
    (hstep : Run code m (List.replicate k true) m')
    (hbig : Run code m (List.replicate (k + q) true) p) :
    Run code m' (List.replicate q true) p := by
  rw [List.replicate_add] at hbig
  obtain ⟨y, h1, h2⟩ := control_run_split hbig
  have hy : y = m' := control_run_unique hw h1 hstep
  exact hy ▸ h2

/-- The intermediate machines of the fpp phase stay of this form: whatever the
controller reaches by enabled ticks still serves every quantum. -/
theorem supplies_run {code : List (Instruction n)}
    (hw : ∀ i ∈ code, GalilScaffoldNextPc.WellFormed i)
    {m m' : Machine n} {k : ℕ} (hs : Supplies code m)
    (hstep : Run code m (List.replicate k true) m') :
    Supplies code m' := by
  intro q
  obtain ⟨p, hp⟩ := hs (k + q)
  exact ⟨p, run_split hw hstep hp⟩

/-! ## The marked FPP code -/

theorem marked_supplies_run {m m' : Machine 9} {k : ℕ}
    (hs : Supplies GalilFppMarkedCode.code m)
    (hstep : Run GalilFppMarkedCode.code m (List.replicate k true) m') :
    Supplies GalilFppMarkedCode.code m' :=
  supplies_run marked_wellFormed hs hstep

/-- **The main lemma.**  The entry machine of the fpp phase — the one
`FppControl.beginFallback old p length` reaches after the copy and home
phases, i.e. exactly the machine `fallback_prepared` produces and
`fpp_scheduled` is stated about — serves every quantum. -/
theorem fppEnabled_of_correct (w : List (Fin 3)) :
    Supplies GalilFppMarkedCode.code ⟨fppInitial w, false⟩ := by
  obtain ⟨v, _, _, _, _, hsched⟩ := fpp_scheduled w
  refine supplies_of_halting (N := 1584 * w.length + 830) (f := ⟨v, true⟩) ?_ rfl
  apply hsched
  rw [count_true_replicate]

/-- The same, phrased on the controller state reached by `beginFallback`
after copy/home: `fallback_prepared` gives `t.mode = .run` and
`t.program = ⟨fppInitial w, false⟩`, which is precisely this hypothesis pair. -/
theorem fppEnabled_of_prepared (q : ℕ) (s : GalilVM) (w : List (Fin 3))
    (hm : s.fpp.mode = .run) (hp : s.fpp.program = ⟨fppInitial w, false⟩) :
    GalilTickFun3.FppEnabled q s := by
  refine ⟨hm, ?_⟩
  rw [hp]
  exact fppEnabled_of_correct w q

/-- And on any machine that supplies quanta, which by `marked_supplies_run` is
preserved by the `fpp_slice` ticks of the phase. -/
theorem fppEnabled_of_supplies (q : ℕ) (s : GalilVM)
    (hm : s.fpp.mode = .run) (hs : Supplies GalilFppMarkedCode.code s.fpp.program) :
    GalilTickFun3.FppEnabled q s :=
  ⟨hm, hs q⟩

/-- Stability of the enabling condition along one `fpp_slice`: the slice
consumes `q` enabled events, and the successor still supplies. -/
theorem supplies_slice (q : ℕ) {s s' : GalilVM}
    (hs : Supplies GalilFppMarkedCode.code s.fpp.program)
    (hstep : Run GalilFppMarkedCode.code s.fpp.program (List.replicate q true) s'.fpp.program) :
    Supplies GalilFppMarkedCode.code s'.fpp.program :=
  marked_supplies_run hs hstep

/-- Everything the phase visits, starting from the prepared entry machine,
still enables the fpp tick. -/
theorem fppEnabled_along_phase (q k : ℕ) (s s' : GalilVM) (w : List (Fin 3))
    (hp : s.fpp.program = ⟨fppInitial w, false⟩)
    (hm' : s'.fpp.mode = .run)
    (hstep : Run GalilFppMarkedCode.code s.fpp.program (List.replicate k true) s'.fpp.program) :
    GalilTickFun3.FppEnabled q s' := by
  refine fppEnabled_of_supplies q s' hm' ?_
  refine marked_supplies_run ?_ hstep
  rw [hp]
  exact fppEnabled_of_correct w

#print axioms run_prefix
#print axioms run_idle_after_done
#print axioms supplies_of_done
#print axioms supplies_of_halting
#print axioms run_split
#print axioms supplies_run
#print axioms marked_supplies_run
#print axioms fppEnabled_of_correct
#print axioms fppEnabled_of_prepared
#print axioms fppEnabled_of_supplies
#print axioms supplies_slice
#print axioms fppEnabled_along_phase

end PalPeg.GalilFppRunSupply
