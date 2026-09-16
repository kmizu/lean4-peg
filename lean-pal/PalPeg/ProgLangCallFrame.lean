import PalPeg.ProgLangCalls
import PalPeg.ProgramFrame

/-! A real-time input frame containing a fixed number of complete calls.
The clock bound is 1 + R*(H+1), with one actual arrival, no input repetition,
and a call boundary at both ends of every frame. -/
set_option autoImplicit false

namespace PalPeg.ProgLangBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2

variable {A C D Terminal Γ : Type} {n t : ℕ}
  [DecidableEq A] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype Γ] [DecidableEq Γ]

theorem callMachine_noneBlocks
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n) (R : ℕ)
    (x : CallCtrl progs D × (Fin t → STape Γ)) :
    (List.replicate (R * (H + 1)) none).foldl
      (callMachine progs I choose H blank ht initialOuter initialIndex).sMicroStep
      { state := (x.1, ⟨0, Nat.zero_lt_succ H⟩), tape := x.2 } =
      let y := (callRun progs I choose H blank)^[R] x
      { state := (y.1, ⟨0, Nat.zero_lt_succ H⟩), tape := y.2 } := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Nat.succ_mul, List.replicate_add, List.foldl_append, ih,
      callMachine_noneBlock]
    rw [Function.iterate_succ_apply']

noncomputable def callFrameMachine
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H R : ℕ) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n)
    (arr : ArriveAct Terminal Γ t) :
    StructuredMachine Terminal
      ((CallCtrl progs D × Fin (H + 1)) × Fin (R * (H + 1) + 1)) Γ t
      (R * (H + 1) + 1) :=
  frameMachine (callMachine progs I choose H blank ht initialOuter initialIndex)
    arr (R * (H + 1))

/-- End-to-end equality for an actual input round of the finite machine.
This is a clock/scheduling theorem; semantic bounds for each selected low
program are supplied separately by callRun_exec or its queue instance. -/
theorem callFrameMachine_round
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H R : ℕ) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n)
    (arr : ArriveAct Terminal Γ t) (a : Terminal)
    (c : CallCtrl progs D) (T : Fin t → STape Γ) :
    (callFrameMachine progs I choose H R blank ht initialOuter initialIndex arr).sRound
      { state := ((c, ⟨0, Nat.zero_lt_succ H⟩), ⟨0, Nat.zero_lt_succ _⟩), tape := T } a =
      let y := (callRun progs I choose H blank)^[R]
        (c, arriveA blank arr (some a) T)
      { state := ((y.1, ⟨0, Nat.zero_lt_succ H⟩), ⟨0, Nat.zero_lt_succ _⟩), tape := y.2 } := by
  rw [callFrameMachine, frameMachine_round]
  have hblank : (callMachine progs I choose H blank ht initialOuter initialIndex).blank =
      blank := rfl
  rw [hblank]
  rw [callMachine_noneBlocks progs I choose H blank ht initialOuter initialIndex R
    (c, arriveA blank arr (some a) T)]

/-- info: 'PalPeg.ProgLangBank.callFrameMachine_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callFrameMachine_round

end PalPeg.ProgLangBank
