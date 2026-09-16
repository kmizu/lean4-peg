import PalPeg.GalilScaffoldSourceReady
import PalPeg.GalilScaffoldSearchFinish

set_option autoImplicit false
namespace PalPeg.GalilScaffoldPrepareControl
open GalilScaffoldCounter (Counter)
open GalilScaffoldTape
open GalilScaffoldSearchFinish (Mode)

/-- Shared decoded controller state for lower/lower_home/copy/home.
No separate hypothetical tape is substituted at a mode boundary. -/
structure State where
  mode : Mode
  program : GalilScaffoldControl.Machine 12
  work : Counter
  span : Counter
  debt : Counter
  walker : GalilScaffoldPlace.Place
  finalStage : Bool

def tape (x : State) (i : Fin 12) (f : Tape → Tape) : GalilScaffoldControl.Machine 12 :=
  {x.program with config := GalilScaffoldLoading.put x.program.config i (f (x.program.config.tapes i))}

/-- A successful enabled preparation tick, in Scala dispatch order.
The left-end guards are explicit; disabled ticks are identity. -/
inductive Tick : Bool → State → State → Prop
  | idle (x : State) : Tick false x x
  | lowerBit (x : State) (hm : x.mode = .lower)
      (hp : GalilScaffoldCounter.positive x.work = true) :
      Tick true x {x with program := tape x 10 (fun t => moveRight (write t 8)), work := GalilScaffoldCounter.dec x.work}
  | lowerEnd (x : State) (hm : x.mode = .lower)
      (hp : GalilScaffoldCounter.positive x.work = false) :
      Tick true x {x with program := tape x 10 (fun t => write t 5),mode := .lowerHome}
  | lowerLeft (x : State) (hm : x.mode = .lowerHome)
      (hf : (x.program.config.tapes 10).focus ≠ 4) (hl : (x.program.config.tapes 10).left ≠ []) :
      Tick true x {x with program := tape x 10 moveLeft}
  | beginCopy (x : State) (hm : x.mode = .lowerHome)
      (hf : (x.program.config.tapes 10).focus = 4) :
      Tick true x {x with program := tape x 7 (fun t => moveRight (write t 4)), work := GalilScaffoldCounter.inc x.span,mode := .copy}
  | copyBit (x : State) (a : Fin 3) (hm : x.mode = .copy)
      (ha : GalilScaffoldPlace.read x.walker = some a)
      (hw : GalilScaffoldCounter.zero x.work = false) :
      Tick true x {x with program := tape x 7 (fun t => moveRight (write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec x.work,walker := GalilScaffoldPlace.left x.walker}
  | copyEnd (x : State) (hm : x.mode = .copy)
      (he : GalilScaffoldPlace.read x.walker = none ∨ GalilScaffoldCounter.zero x.work = true) :
      Tick true x {x with program := tape x 7 (fun t => write t 5),mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}
  | sourceLeft (x : State) (hm : x.mode = .home)
      (hf : (x.program.config.tapes 7).focus ≠ 4) (hl : (x.program.config.tapes 7).left ≠ []) :
      Tick true x {x with program := tape x 7 moveLeft}
  | startRun (x : State) (hm : x.mode = .home)
      (hf : (x.program.config.tapes 7).focus = 4) :
      Tick true x {x with program := GalilScaffoldControl.start 320 x.program,mode := .run}

theorem tick_debt {x y : State} {b : Bool} (ht : Tick b x y) : y.debt = x.debt := by
  cases ht <;> rfl

theorem tick_frame {x y : State} {b : Bool} (ht : Tick b x y)
    (i : Fin 12) (h7 : i ≠ 7) (h10 : i ≠ 10) :
    y.program.config.tapes i = x.program.config.tapes i := by
  cases ht <;> simp [tape,GalilScaffoldLoading.put,GalilScaffoldControl.start,h7,h10]

inductive Run : State → List Bool → State → Prop
  | nil (x : State) : Run x [] x
  | cons (x y z : State) (b : Bool) (bs : List Bool)
      (ht : Tick b x y) (hr : Run y bs z) : Run x (b :: bs) z

theorem run_debt {x y : State} {bs : List Bool} (hr : Run x bs y) : y.debt = x.debt := by
  induction hr with
  | nil => rfl
  | cons x y z b bs ht hr ih => exact ih.trans (tick_debt ht)

theorem run_frame {x y : State} {bs : List Bool} (hr : Run x bs y)
    (i : Fin 12) (h7 : i ≠ 7) (h10 : i ≠ 10) :
    y.program.config.tapes i = x.program.config.tapes i := by
  induction hr with
  | nil => rfl
  | cons x y z b bs ht hr ih => exact ih.trans (tick_frame ht i h7 h10)

theorem lower_load {x y : GalilScaffoldLower.Cursor} {n : ℕ}
    (hr : GalilScaffoldLower.Load x n y) (s : State) (hm : s.mode = .lower)
    (hw : s.work = x.work) (ht : s.program.config.tapes 10 = x.tape) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .lowerHome ∧
      t.work = y.work ∧ t.program.config.tapes 10 = y.tape ∧
      t.walker = s.walker ∧ t.program.config.tapes 7 = s.program.config.tapes 7 := by
  induction hr generalizing s with
  | stop x hp =>
    let t : State := {s with program := tape s 10 (fun t => write t 5),mode := .lowerHome}
    have hs : Tick true s t := .lowerEnd s hm (by simpa [hw] using hp)
    refine ⟨t,.cons s t t true [] hs (.nil t),rfl,hw,?_,rfl,?_⟩ <;>
      simp [t,tape,GalilScaffoldLoading.put,ht]
  | next x y n hp hr ih =>
    let u : State := {s with program := tape s 10 (fun t => moveRight (write t 8)),work := GalilScaffoldCounter.dec s.work}
    have hs : Tick true s u := .lowerBit s hm (by simpa [hw] using hp)
    obtain ⟨t,hrt,hmode,hwork,htape,hwalker,h7⟩ := ih u hm
      (by simp [u,hw]) (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,hwork,htape,hwalker,?_⟩
    · simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt
    · simpa [u,tape,GalilScaffoldLoading.put] using h7

theorem lower_home {x y : Tape} {n : ℕ} (hr : GalilScaffoldLower.Rewind x n y)
    (s : State) (hm : s.mode = .lowerHome) (ht : s.program.config.tapes 10 = x) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .copy ∧
      t.program.config.tapes 10 = y ∧ t.work = GalilScaffoldCounter.inc s.span ∧
      t.program.config.tapes 7 = moveRight (write (s.program.config.tapes 7) 4) ∧ t.walker = s.walker := by
  induction hr generalizing s with
  | done x hf =>
    let t : State := {s with program := tape s 7 (fun t => moveRight (write t 4)),work := GalilScaffoldCounter.inc s.span,mode := .copy}
    have hs : Tick true s t := .beginCopy s hm (by simpa [ht] using hf)
    refine ⟨t,.cons s t t true [] hs (.nil t),rfl,?_,rfl,?_,rfl⟩
    · simpa [t,tape,GalilScaffoldLoading.put] using ht
    · simp [t,tape,GalilScaffoldLoading.put]
  | left x y n hf hl hr ih =>
    let u : State := {s with program := tape s 10 moveLeft}
    have hs : Tick true s u := .lowerLeft s hm (by simpa [ht] using hf) (by simpa [ht] using hl)
    obtain ⟨t,hrt,hmode,h10,hwork,h7,hwalker⟩ := ih u hm (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,h10,hwork,?_,hwalker⟩
    · simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt
    · simpa [u,tape,GalilScaffoldLoading.put] using h7

theorem source_copy {x y : GalilScaffoldPlace.Cursor} {n : ℕ} {final : Bool}
    (hr : GalilScaffoldPlace.Copy x n y final) (s : State) (hm : s.mode = .copy)
    (hw : s.work = GalilScaffoldCounter.ofNat x.work) (hp : s.walker = x.place)
    (ht : s.program.config.tapes 7 = x.tape) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .home ∧
      t.work = GalilScaffoldCounter.ofNat y.work ∧ t.walker = y.place ∧
      t.program.config.tapes 7 = y.tape ∧ t.finalStage = final := by
  induction hr generalizing s with
  | stop x he =>
    let t : State := {s with program := tape s 7 (fun t => write t 5),mode := .home,finalStage := (GalilScaffoldPlace.read s.walker).isNone}
    have hs : Tick true s t := .copyEnd s hm (by
      rcases he with he | he
      · exact Or.inl (by simpa [hp] using he)
      · right; simp [hw,he,GalilScaffoldCounter.ofNat,GalilScaffoldCounter.zero])
    refine ⟨t,.cons s t t true [] hs (.nil t),rfl,hw,hp,?_,?_⟩
    · simp [t,tape,GalilScaffoldLoading.put,ht]
    · simp [t,hp]
  | next p k tape0 a ha n y final hr ih =>
    let u : State := {s with program := tape s 7 (fun t => moveRight (write t (GalilFppPreparation.symbol a))),work := GalilScaffoldCounter.dec s.work,walker := GalilScaffoldPlace.left s.walker}
    have hs : Tick true s u := .copyBit s a hm (by simpa [hp] using ha)
      (by simp [hw,GalilScaffoldCounter.zero,GalilScaffoldCounter.ofNat,List.replicate_succ])
    obtain ⟨t,hrt,hmode,hwork,hplace,htape,hfinal⟩ := ih u hm
      (by simp [u,hw,GalilScaffoldCounter.dec_ofNat_succ])
      (by simp [u,hp]) (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,hwork,hplace,htape,hfinal⟩
    simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt

theorem source_home {x y : Tape} {n : ℕ} (hr : GalilScaffoldLower.Rewind x n y)
    (s : State) (hm : s.mode = .home) (ht : s.program.config.tapes 7 = x) :
    ∃ t, Run s (List.replicate n true) t ∧ t.mode = .run ∧
      t.program.config.tapes 7 = y ∧ t.program.config.pc = 320 ∧ t.program.done = false ∧
      t.finalStage = s.finalStage := by
  induction hr generalizing s with
  | done x hf =>
    let t : State := {s with program := GalilScaffoldControl.start 320 s.program,mode := .run}
    have hs : Tick true s t := .startRun s hm (by simpa [ht] using hf)
    exact ⟨t,.cons s t t true [] hs (.nil t),rfl,ht,rfl,rfl,rfl⟩
  | left x y n hf hl hr ih =>
    let u : State := {s with program := tape s 7 moveLeft}
    have hs : Tick true s u := .sourceLeft s hm (by simpa [ht] using hf) (by simpa [ht] using hl)
    obtain ⟨t,hrt,hmode,htape,hpc,hdone,hfinal⟩ := ih u hm
      (by simp [u,tape,GalilScaffoldLoading.put,ht])
    refine ⟨t,?_,hmode,htape,hpc,hdone,hfinal⟩
    simpa [List.replicate_succ] using Run.cons s u t true _ hs hrt

theorem run_append {x y z : State} {bs cs : List Bool} (hb : Run x bs y) (hc : Run y cs z) :
    Run x (bs ++ cs) z := by
  induction hb with
  | nil => exact hc
  | cons x y z b bs ht hr ih => exact .cons _ _ _ _ _ ht (ih hc)

theorem run_span {x y : State} {bs : List Bool} (hr : Run x bs y) : y.span = x.span := by
  induction hr with
  | nil => rfl
  | cons x y z b bs ht hr ih => cases ht <;> exact ih

def SourcePhase (s : State) : Prop := s.mode = .copy ∨ s.mode = .home ∨ s.mode = .run

theorem source_tick_frame {x y : State} {b : Bool} (ht : Tick b x y) (hx : SourcePhase x) :
    SourcePhase y ∧ y.program.config.tapes 10 = x.program.config.tapes 10 := by
  cases ht <;> simp_all [SourcePhase,tape,GalilScaffoldLoading.put,GalilScaffoldControl.start]

theorem source_run_frame {x y : State} {bs : List Bool} (hr : Run x bs y) (hx : SourcePhase x) :
    y.program.config.tapes 10 = x.program.config.tapes 10 := by
  induction hr with
  | nil => rfl
  | cons x y z b bs ht hr ih =>
    obtain ⟨hy,hframe⟩ := source_tick_frame ht hx
    exact (ih hy).trans hframe

/-- All four preparation phases on one shared controller state. The initial
prepare tick (reset, LEFT/right on LOWER) has already happened. -/
theorem prepared_run (s : State) (lower span : ℕ)
    (hm : s.mode = .lower) (hw : s.work = GalilScaffoldCounter.ofNat lower)
    (hspan : s.span = GalilScaffoldCounter.ofNat span)
    (h10 : s.program.config.tapes 10 = moveRight (write reset 4))
    (h7 : s.program.config.tapes 7 = reset)
    (hother : ∀ i : Fin 12, i ≠ 7 → i ≠ 10 → s.program.config.tapes i = reset) :
    let w := (GalilScaffoldPlace.stream s.walker).take (span+1)
    ∃ t, Run s (List.replicate (2*lower+2*w.length+6) true) t ∧
      t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w lower ∧
      t.program.done = false ∧ t.debt = s.debt ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream s.walker).length ≤ span+1) := by
  dsimp
  obtain ⟨lt,hl,hh⟩ := GalilScaffoldLower.lower_ready lower
  obtain ⟨a,ha,ham,haw,hat,hawalker,ha7⟩ := lower_load hl s hm hw h10
  obtain ⟨b,hb,hbm,hbt,hbw,hb7,hbwalker⟩ := lower_home hh a ham hat
  have hbwork : b.work = GalilScaffoldCounter.ofNat (span+1) := by
    rw [hbw,run_span ha,hspan,GalilScaffoldCounter.inc_ofNat]
  have hbplace : b.walker = s.walker := hbwalker.trans hawalker
  have hbsource : b.program.config.tapes 7 = moveRight (write reset 4) := by
    rw [hb7,ha7,h7]
  obtain ⟨cursor,final,hcopy,hhome,hfinal⟩ := GalilScaffoldSourceReady.place_ready s.walker span
  obtain ⟨c,hc,hcm,hcw,hcp,hct,hcf⟩ := source_copy hcopy b hbm hbwork hbplace hbsource
  obtain ⟨t,ht,htm,htt,htpc,htdone,htfinal⟩ := source_home hhome c hcm hct
  have hsource := run_append hc ht
  have hall := run_append (run_append ha hb) hsource
  have hten : t.program.config.tapes 10 =
      GalilScaffoldPreload.bounded (List.replicate lower 8) :=
    (source_run_frame hsource (Or.inl hbm)).trans hbt
  refine ⟨t,?_,htm,?_,htdone,run_debt hall,?_⟩
  · simp only [← List.replicate_add] at hall
    convert hall using 1 <;> congr 1 <;> omega
  · apply GalilScaffoldLoading.config_ext htpc
    funext i
    by_cases hi7 : i = 7
    · subst i; simpa [GalilScaffoldPreload.initial] using htt
    · by_cases hi10 : i = 10
      · subst i; simpa [GalilScaffoldPreload.initial] using hten
      · simpa [GalilScaffoldPreload.initial,hi7,hi10] using
          (run_frame hall i hi7 hi10).trans (hother i hi7 hi10)
  · rw [htfinal,hcf]
    exact hfinal

/-- Scala Search.prepare on decoded program/counter/place representations.
The caller supplies the persistent lower counter and center reference. -/
def prepare (s : State) (lower : Counter) (center : GalilScaffoldPlace.Place) : State :=
  let p := GalilScaffoldControl.reset 320 s.program
  let c := GalilScaffoldLoading.put p.config 10 (moveRight (write reset 4))
  {s with mode := .lower,program := {p with config := c},work := lower,walker := center,finalStage := false}

/-- The single prepare dispatch is counted separately from its four-mode body. -/
inductive PreparedRun (lower : Counter) (center : GalilScaffoldPlace.Place) :
    State → ℕ → State → Prop
  | intro (s t : State) (n : ℕ)
      (hr : Run (prepare s lower center) (List.replicate n true) t) :
      PreparedRun lower center s (n+1) t

theorem prepare_complete (s : State) (lower span : ℕ) (center : GalilScaffoldPlace.Place)
    (hs : s.span = GalilScaffoldCounter.ofNat span) :
    let w := (GalilScaffoldPlace.stream center).take (span+1)
    ∃ t, PreparedRun (GalilScaffoldCounter.ofNat lower) center s (2*lower+2*w.length+7) t ∧
      t.mode = .run ∧ t.program.config = GalilScaffoldPreload.initial w lower ∧
      t.program.done = false ∧ t.debt = s.debt ∧
      (t.finalStage = true ↔ (GalilScaffoldPlace.stream center).length ≤ span+1) := by
  obtain ⟨t,hr,hm,hp,hd,hdebt,hf⟩ := prepared_run
    (prepare s (GalilScaffoldCounter.ofNat lower) center) lower span rfl rfl hs
    (by simp [prepare,GalilScaffoldLoading.put])
    (by simp [prepare,GalilScaffoldLoading.put,GalilScaffoldControl.reset])
    (by intro i hi7 hi10; simp [prepare,GalilScaffoldLoading.put,GalilScaffoldControl.reset,hi10])
  refine ⟨t,?_,hm,hp,hd,hdebt,hf⟩
  exact PreparedRun.intro s t _ hr

#print axioms prepare_complete
#print axioms prepared_run
#print axioms source_run_frame
#print axioms source_home
#print axioms source_copy
#print axioms lower_home
#print axioms lower_load
#print axioms run_debt
#print axioms run_frame
end PalPeg.GalilScaffoldPrepareControl
