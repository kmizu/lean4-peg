import PalPeg.ProgLangPersist2

/-!
# A finite bank of independently suspended program controls

Each slot owns its continuation in finite control, not on an unbounded program
counter tape.  Programs may share a tape bundle: the selected interpretation
determines which tapes are touched.  Tape noninterference is therefore a
separate obligation, whereas continuation noninterference holds unconditionally.
-/

set_option autoImplicit false

namespace PalPeg.ProgLangBank

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2

variable {A C Terminal Γ : Type} {n t B : ℕ}

abbrev Bank (progs : Fin n → Prog A C) := (i : Fin n) → CtrlS (progs i)

def initialBank (progs : Fin n → Prog A C) : Bank progs :=
  fun i => startCtrlS (progs i)

/-- Resume one continuation for one microstep. Other continuations are frozen. -/
def tick (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (blank : Γ) (i : Fin n) (a : Option Terminal)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (Bank progs × Bool) × (Fin t → STape Γ) :=
  let ev := evalConds (I i).toInterp (fun j => (x.2 j).focus)
  ((Function.update x.1.1 i (stepCtrlS (progs i) ev (x.1.1 i)),
      updFlag (I i) x.1.2 (stepStack ev (x.1.1 i).val).2),
    (microStep (I i).toInterp blank a ((x.1.1 i).val, x.2)).2)

@[simp] theorem tick_other (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ)
    (i j : Fin n) (h : j ≠ i) (a : Option Terminal)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (tick progs I blank i a x).1.1 j = x.1.1 j := by
  simp [tick, h]

@[simp] theorem tick_selected (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ)
    (i : Fin n) (a : Option Terminal)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    ((tick progs I blank i a x).1.1 i |>.val,
        (tick progs I blank i a x).2) =
      microStep (I i).toInterp blank a ((x.1.1 i).val, x.2) := by
  simp [tick, microStep]

/-- A fixed finite phase schedule can interleave arbitrary finite programs. -/
noncomputable def bankBody [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (slot : Fin B → Fin n) :
    PhaseBody Terminal (Bank progs × Bool) Γ t B :=
  fun c a ph σ =>
    let i := slot ph
    let r := roundBodyPA (I i) (progs i) arr hB (c.1 i, c.2) a ph σ
    ((Function.update c.1 i r.1.1, r.1.2), r.2)

noncomputable def bankMachine [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (ht : 0 < t) (hB : 0 < B)
    (slot : Fin B → Fin n) (blank : Γ) (initialFlag : Bool) :
    StructuredMachine Terminal ((Bank progs × Bool) × Fin B) Γ t B :=
  ofPhases ht hB blank (initialBank progs, initialFlag) Prod.snd
    (bankBody progs I arr hB slot)

theorem bankBody_zero [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (slot : Fin B → Fin n)
    (blank : Γ) (a : Option Terminal) (c : Bank progs × Bool)
    (T : Fin t → STape Γ) :
    bodyStep blank (bankBody progs I arr hB slot) ⟨0, hB⟩ a (c, T) =
      (c, arriveA blank arr a T) := by
  simpa [bodyStep, bankBody, roundBodyPA] using
    (show (fun j => (T j).applyAction blank (arr a (fun j => (T j).focus) j)) =
      arriveA blank arr a T from rfl)

theorem bankBody_ne [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (slot : Fin B → Fin n)
    (blank : Γ) (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩)
    (a : Option Terminal) (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    bodyStep blank (bankBody progs I arr hB slot) ph a x =
      tick progs I blank (slot ph) a x := by
  apply Prod.ext
  · simp [bodyStep, bankBody, roundBodyPA, hph, tick]
  · have h := congrArg Prod.snd
      (bodyStepPA_ne (I (slot ph)) (progs (slot ph)) arr hB blank ph hph a
        (x.1.1 (slot ph), x.1.2) x.2)
    simpa only [bodyStep, bankBody, tick] using h

/-- Execute a finite chunk without resetting the selected program. -/
def runChunk (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (blank : Γ) (i : Fin n) : List (Option Terminal) →
      ((Bank progs × Bool) × (Fin t → STape Γ)) →
      ((Bank progs × Bool) × (Fin t → STape Γ))
  | [], x => x
  | a :: l, x => runChunk progs I blank i l (tick progs I blank i a x)

theorem runChunk_selected (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    ((runChunk progs I blank i l x).1.1 i |>.val,
        (runChunk progs I blank i l x).2) =
      runInputs (I i).toInterp blank l ((x.1.1 i).val, x.2) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
      simp only [runChunk, runInputs_cons, ih, tick_selected]

theorem runChunk_other (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ)
    (i j : Fin n) (h : j ≠ i) (l : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    (runChunk progs I blank i l x).1.1 j = x.1.1 j := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => simp only [runChunk, ih, tick_other progs I blank i j h]

theorem runChunk_append (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l r : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    runChunk progs I blank i (l ++ r) x =
      runChunk progs I blank i r (runChunk progs I blank i l x) := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => exact ih _

/-- Existing `Exec` proofs transfer to the bank without a PC-tape compiler. -/
theorem runChunk_exec (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (blank : Γ) (i : Fin n)
    (l : List (Option Terminal))
    (x : (Bank progs × Bool) × (Fin t → STape Γ))
    (acts : List (Fin t → Γ × Move))
    (hstart : (x.1.1 i).val = [progs i])
    (he : Exec (I i).toInterp blank (progs i) x.2 acts)
    (hlen : l.length = acts.length) :
    (runChunk progs I blank i l x).2 = applyTrace blank x.2 acts ∧
      SEqAt (I i).toInterp (applyTrace blank x.2 acts)
        ((runChunk progs I blank i l x).1.1 i).val [] := by
  obtain ⟨_, s, hs, heq⟩ := he [] l hlen
  have h := runChunk_selected progs I blank i l x
  rw [hstart] at h
  simp only [List.append_nil] at hs
  rw [hs] at h
  refine ⟨congrArg Prod.snd h, ?_⟩
  have hc := congrArg Prod.fst h
  change ((runChunk progs I blank i l x).1.1 i).val = s at hc
  rw [hc]
  exact heq

/-- Operational schedule: input arrival at phase zero, one selected tick otherwise. -/
def scheduledRun (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t) (arr : ArriveAct Terminal Γ t)
    (hB : 0 < B) (slot : Fin B → Fin n) (blank : Γ) :
    List (Option Terminal) → Fin B →
      ((Bank progs × Bool) × (Fin t → STape Γ)) →
      ((Bank progs × Bool) × (Fin t → STape Γ))
  | [], _, x => x
  | a :: l, ph, x =>
      scheduledRun progs I arr hB slot blank l (nextPhase ph)
        (if ph = ⟨0, hB⟩ then (x.1, arriveA blank arr a x.2)
          else tick progs I blank (slot ph) a x)

theorem phaseRun_bank [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (hB : 0 < B) (slot : Fin B → Fin n)
    (blank : Γ) (l : List (Option Terminal)) (ph : Fin B)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    phaseRun blank (bankBody progs I arr hB slot) l ph x =
      scheduledRun progs I arr hB slot blank l ph x := by
  induction l generalizing ph x with
  | nil => rfl
  | cons a l ih =>
      simp only [phaseRun_cons, scheduledRun]
      by_cases h : ph = ⟨0, hB⟩
      · subst ph
        rw [if_pos rfl, bankBody_zero, ih]
      · rw [if_neg h, bankBody_ne progs I arr hB slot blank ph h, ih]

theorem bankMachine_round [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (arr : ArriveAct Terminal Γ t) (ht : 0 < t) (hB : 0 < B)
    (slot : Fin B → Fin n) (blank : Γ) (initialFlag : Bool) (a : Terminal)
    (c : Bank progs × Bool) (T : Fin t → STape Γ) :
    (bankMachine progs I arr ht hB slot blank initialFlag).sRound
      { state := (c, ⟨0, hB⟩), tape := T } a =
      let y := scheduledRun progs I arr hB slot blank
        (PalPeg.Speedup.MultiStepMachine.roundInputs B a) ⟨0, hB⟩ (c, T)
      { state := (y.1, ⟨0, hB⟩), tape := y.2 } := by
  simpa only [bankMachine, phaseRun_bank] using
    (ofPhases_round ht hB blank (initialBank progs, initialFlag) Prod.snd
      (bankBody progs I arr hB slot) c T a)

/-- info: 'PalPeg.ProgLangBank.bankMachine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bankMachine_round

end PalPeg.ProgLangBank
