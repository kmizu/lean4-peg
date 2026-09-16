import PalPeg.GalilScaffoldNextPc

set_option autoImplicit false
namespace PalPeg.GalilScaffoldRawTick
open GalilFppWide (Instruction)

structure Machine (n slots : ℕ) where
  config : GalilScaffoldHeapProgram.Config n slots
  done : Bool

def Represents {n slots : ℕ} (x : Machine n slots) (u : GalilScaffoldControl.Machine n) : Prop :=
  GalilScaffoldHeapProgram.Represents x.config u.config ∧ x.done = u.done

/-- Scala ProgramView.reset drops only the private tape roots. Retained
heap cells are untouched, and instruction execution stays halted. -/
def reset {n slots : ℕ} (entry : ℕ) (x : Machine n slots) : Machine n slots :=
  ⟨⟨x.config.heap,entry,fun _ => ⟨none,6,none⟩⟩,true⟩

theorem reset_represents {n slots : ℕ} (entry : ℕ) (x : Machine n slots) :
    Represents (reset entry x)
      ⟨⟨entry,fun _ => GalilScaffoldTape.reset⟩,true⟩ := by
  refine ⟨⟨rfl,?_⟩,rfl⟩
  intro k
  exact ⟨.empty,rfl,.empty⟩

theorem reset_heap {n slots : ℕ} (entry : ℕ) (x : Machine n slots) :
    (reset entry x).config.heap = x.config.heap := rfl

#print axioms reset_represents

/-- Decoded raw tick. None records a missing PC/read target. Allocation
freshness and legal-left requirements are discharged by the refinement theorem;
this function does not validate the actual circuit's field encodings. -/
def tick {n slots : ℕ} (code : List (Instruction n)) (enabled : Bool)
    (a : GalilScaffoldHeap.Address slots) (x : Machine n slots) : Option (Machine n slots) :=
  if !enabled || x.done then some x else
    (code[x.config.pc]?).bind (fun i =>
      if i = .halt then some {x with done := true} else
      (GalilScaffoldNextPc.next i (fun t => (x.config.tapes t).focus)).map (fun pc =>
        ⟨{GalilScaffoldRawTapes.loop i true a x.config with pc := pc},false⟩))

theorem tick_idle {n slots : ℕ} (code : List (Instruction n)) (enabled : Bool)
    (a : GalilScaffoldHeap.Address slots) (x : Machine n slots)
    (hi : enabled = false ∨ x.done = true) : tick code enabled a x = some x := by
  rcases hi with hi | hi <;> simp [tick,hi]

theorem tick_execute {n slots : ℕ} {code : List (Instruction n)} {i : Instruction n}
    {u v : GalilScaffoldProgram.Config n} (he : GalilScaffoldProgram.Execute i u v)
    (hi : code[u.pc]? = some i) (hw : GalilScaffoldNextPc.WellFormed i)
    (x : GalilScaffoldHeapProgram.Config n slots) (hr : GalilScaffoldHeapProgram.Represents x u)
    (a : GalilScaffoldHeap.Address slots) (hf : x.heap a = none) :
    ∃ y, tick code true a ⟨x,false⟩ = some y ∧ Represents y ⟨v,false⟩ := by
  obtain ⟨pc,hp,hm⟩ := GalilScaffoldNextPc.realize_next he hw x hr a hf
  have hn : i ≠ .halt := by cases he <;> simp
  refine ⟨⟨{GalilScaffoldRawTapes.loop i true a x with pc := pc},false⟩,?_,hm,rfl⟩
  simp [tick,hr.1,hi,hn,hp]

theorem realize_tick {n slots : ℕ} {code : List (Instruction n)} {enabled : Bool}
    {u v : GalilScaffoldControl.Machine n} (ht : GalilScaffoldControl.Tick code enabled u v)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (x : Machine n slots) (hr : Represents x u) (a : GalilScaffoldHeap.Address slots)
    (hf : x.config.heap a = none) :
    ∃ y, tick code enabled a x = some y ∧ Represents y v := by
  cases ht with
  | idle u enabled hu =>
    refine ⟨x,tick_idle code enabled a x ?_,hr⟩
    rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (hr.2.trans hu)
  | halt u hi =>
    refine ⟨{x with done := true},?_,hr.1,rfl⟩
    have hd : x.done = false := hr.2
    simp [tick,hd,hr.1.1,hi]
  | execute u v i hi he =>
    have hd : x.done = false := hr.2
    obtain ⟨y,hy,hry⟩ := tick_execute he hi (hw u.pc i hi) x.config hr.1 a hf
    refine ⟨y,?_,hry⟩
    have hx : x = ⟨x.config,false⟩ := by cases x; simp_all
    rw [hx]
    exact hy

theorem loop_finite {n slots : ℕ} (i : Instruction n) (active : Bool)
    (a : GalilScaffoldHeap.Address slots) (x : GalilScaffoldHeapProgram.Config n slots)
    (hh : GalilScaffoldHeapProgram.FiniteHeap x.heap) :
    GalilScaffoldHeapProgram.FiniteHeap (GalilScaffoldRawTapes.loop i active a x).heap := by
  cases active with
  | false => simpa [GalilScaffoldRawTapes.loop_inactive] using hh
  | true =>
    cases i with
    | halt => simpa [GalilScaffoldRawTapes.loop_halt] using hh
    | read => simpa [GalilScaffoldRawTapes.loop_read] using hh
    | write => simpa [GalilScaffoldRawTapes.loop_write,GalilScaffoldHeapProgram.written] using hh
    | move t d pc =>
      rw [GalilScaffoldRawTapes.loop_move]
      cases d <;> exact GalilScaffoldHeapProgram.put_finite hh a _

theorem tick_finite {n slots : ℕ} {code : List (Instruction n)} {enabled : Bool}
    {a : GalilScaffoldHeap.Address slots} {x y : Machine n slots}
    (ht : tick code enabled a x = some y) (hh : GalilScaffoldHeapProgram.FiniteHeap x.config.heap) :
    GalilScaffoldHeapProgram.FiniteHeap y.config.heap := by
  unfold tick at ht
  split at ht
  · cases Option.some.inj ht; exact hh
  · cases hi : code[x.config.pc]? with
    | none => simp [hi] at ht
    | some i =>
      simp only [hi,Option.bind_some] at ht
      split at ht
      · cases Option.some.inj ht; exact hh
      · cases hp : GalilScaffoldNextPc.next i (fun t => (x.config.tapes t).focus) with
        | none => simp [hp] at ht
        | some pc =>
          simp only [hp,Option.map_some] at ht
          cases Option.some.inj ht
          exact loop_finite i true a x.config hh

inductive Run {n slots : ℕ} (code : List (Instruction n)) :
    Machine n slots → List Bool → Machine n slots → Prop
  | nil (x : Machine n slots) : Run code x [] x
  | cons (x y z : Machine n slots) (b : Bool) (bs : List Bool)
      (a : GalilScaffoldHeap.Address slots) (ht : tick code b a x = some y)
      (hr : Run code y bs z) : Run code x (b :: bs) z

theorem realize_run {n slots : ℕ} {code : List (Instruction n)}
    {u v : GalilScaffoldControl.Machine n} {bs : List Bool}
    (hu : GalilScaffoldControl.Run code u bs v)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (hs : 0 < slots) (x : Machine n slots) (hr : Represents x u)
    (hh : GalilScaffoldHeapProgram.FiniteHeap x.config.heap) :
    ∃ y, Run code x bs y ∧ Represents y v ∧ GalilScaffoldHeapProgram.FiniteHeap y.config.heap := by
  induction hu generalizing x with
  | nil u => exact ⟨x,.nil x,hr,hh⟩
  | cons u v w b bs ht hu ih =>
    obtain ⟨bound,hb⟩ := hh
    let a : GalilScaffoldHeap.Address slots := (bound,⟨0,hs⟩)
    obtain ⟨y,hy,hry⟩ := realize_tick ht hw x hr a (hb a (Nat.le_refl bound))
    have hfy := tick_finite hy ⟨bound,hb⟩
    obtain ⟨z,hz,hrz,hfz⟩ := ih y hry hfy
    exact ⟨z,.cons x y z b bs a hy hz,hrz,hfz⟩

theorem scheduled_completed {n slots : ℕ} {code : List (Instruction n)}
    {u v : GalilScaffoldProgram.Config n} {qs : List ℕ}
    (hc : GalilScaffoldProgram.Completed code u qs v)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (hs : 0 < slots) (x : GalilScaffoldHeapProgram.Config n slots)
    (hr : GalilScaffoldHeapProgram.Represents x u) (hh : GalilScaffoldHeapProgram.FiniteHeap x.heap)
    (bs : List Bool) (hb : qs.length ≤ bs.count true) :
    ∃ y, Run code ⟨x,false⟩ bs y ∧ y.done = true ∧
      GalilScaffoldHeapProgram.Represents y.config v ∧ GalilScaffoldHeapProgram.FiniteHeap y.config.heap := by
  obtain ⟨y,hy,hry,hfy⟩ := realize_run (GalilScaffoldControl.scheduled_completed hc bs hb)
    hw hs ⟨x,false⟩ ⟨hr,rfl⟩ hh
  exact ⟨y,hy,hry.2,hry.1,hfy⟩

#print axioms scheduled_completed
#print axioms realize_run
#print axioms tick_finite
#print axioms tick_execute
#print axioms realize_tick
end PalPeg.GalilScaffoldRawTick
