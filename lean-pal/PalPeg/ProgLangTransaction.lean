import PalPeg.ProgLangBudget

/-! Restarting a completed bank entry is a finite-control phase, not an
unbounded tape operation. Remaining phases are ordinary bank microsteps. -/
set_option autoImplicit false

namespace PalPeg.ProgLangBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2

variable {A C Terminal Γ : Type} {n t B : ℕ}

noncomputable def transactionBody [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (hB : 0 < B) (i : Fin n) : PhaseBody Terminal (Bank progs × Bool) Γ t B := by
  classical
  exact fun c a ph σ =>
    if ph = ⟨0, hB⟩ then
      ((if (c.1 i).val = [] then Function.update c.1 i (startCtrlS (progs i)) else c.1,
        c.2), fun j => (σ j, Move.stay))
    else bankBody progs I (fun _ σ j => (σ j, Move.stay)) hB (fun _ => i) c a ph σ

theorem transactionBody_zero [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (hB : 0 < B) (i : Fin n) (blank : Γ) (a : Option Terminal)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    bodyStep blank (transactionBody progs I hB i) ⟨0, hB⟩ a x =
      restartDone progs i x := by
  classical
  by_cases h : (x.1.1 i).val = []
  · simp [bodyStep, transactionBody, restartDone, h, STape.applyAction]
  · simp [bodyStep, transactionBody, restartDone, h, STape.applyAction]

theorem transactionBody_ne [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (hB : 0 < B) (i : Fin n) (blank : Γ) (a : Option Terminal)
    (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    bodyStep blank (transactionBody progs I hB i) ph a x = tick progs I blank i a x := by
  classical
  simpa only [bodyStep, transactionBody, if_neg hph] using
    bankBody_ne progs I (fun _ σ j => (σ j, Move.stay)) hB (fun _ => i)
      blank ph hph a x

theorem transactionBody_tail [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (hB : 0 < B) (i : Fin n) (blank : Γ)
    (l : List (Option Terminal)) (ph : Fin B)
    (x : (Bank progs × Bool) × (Fin t → STape Γ))
    (hlen : ph.val + l.length ≤ B) (hpos : 0 < ph.val) :
    phaseRun blank (transactionBody progs I hB i) l ph x =
      runChunk progs I blank i l x := by
  induction l generalizing ph x with
  | nil => rfl
  | cons a l ih =>
    have hne : ph ≠ ⟨0, hB⟩ := by intro h; subst ph; simp at hpos
    rw [phaseRun_cons, transactionBody_ne progs I hB i blank a ph hne, runChunk]
    by_cases hl : l = []
    · subst l; rfl
    · have hll : 0 < l.length := List.length_pos_iff.mpr hl
      have hb : ph.val + 1 < B := by simp only [List.length_cons] at hlen; omega
      apply ih
      · simp only [nextPhase, dif_pos hb]
        simp only [List.length_cons] at hlen
        omega
      · simp only [nextPhase, dif_pos hb]; omega

/-- A reset tick followed by exactly H ordinary ticks. No arrival hook is
included: this is an internal transaction block, not an input scheduler. -/
theorem transactionBody_block [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (H : ℕ) (i : Fin n) (blank : Γ)
    (x : (Bank progs × Bool) × (Fin t → STape Γ)) :
    phaseRun blank (transactionBody progs I (Nat.zero_lt_succ H) i)
      (none :: List.replicate H none) ⟨0, Nat.zero_lt_succ H⟩ x =
      runChunk progs I blank i (List.replicate H none) (restartDone progs i x) := by
  rw [phaseRun_cons, transactionBody_zero]
  cases H with
  | zero => rfl
  | succ H =>
    apply transactionBody_tail
    · simp [nextPhase, List.length_replicate]; omega
    · simp [nextPhase]

/-- The block has a finite phase counter and uses the existing structured
machine construction; its duration is H+1 actual microsteps. -/
noncomputable def transactionMachine [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (H : ℕ) (i : Fin n) (blank : Γ) (ht : 0 < t) :
    StructuredMachine Terminal ((Bank progs × Bool) × Fin (H + 1)) Γ t (H + 1) :=
  ofPhases ht (Nat.zero_lt_succ H) blank (initialBank progs, false) Prod.snd
    (transactionBody progs I (Nat.zero_lt_succ H) i)

/-- info: 'PalPeg.ProgLangBank.transactionBody_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transactionBody_block

end PalPeg.ProgLangBank
