import PalPeg.ProgLangTransaction

/-! A finite outer controller can call bounded low-level programs. The call
index is selected once from the visible tape symbols, then held throughout
the block. No unbounded queue state is consulted by the controller. -/
set_option autoImplicit false

namespace PalPeg.ProgLangBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist PalPeg.ProgLangPersist2

variable {A C D Terminal Γ : Type} {n t B : ℕ}

abbrev CallCtrl (progs : Fin n → Prog A C) (D : Type) :=
  D × Fin n × (Bank progs × Bool)

noncomputable instance [DecidableEq A] [DecidableEq C] [DecidableEq D]
    (progs : Fin n → Prog A C) : DecidableEq (CallCtrl progs D) := Classical.decEq _

/-- The outer control and call index are changed only at phase zero.
Selection sees head symbols, not whole tapes. -/
noncomputable def callBody [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (hB : 0 < B) :
    PhaseBody Terminal (CallCtrl progs D) Γ t B := fun c a ph σ =>
  let di := if ph = ⟨0, hB⟩ then choose c.1 σ else (c.1, c.2.1)
  let r := transactionBody progs I hB di.2 c.2.2 a ph σ
  ((di.1, di.2, r.1), r.2)

theorem callBody_zero [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (hB : 0 < B)
    (blank : Γ) (a : Option Terminal) (x : CallCtrl progs D × (Fin t → STape Γ)) :
    bodyStep blank (callBody progs I choose hB) ⟨0, hB⟩ a x =
      let di := choose x.1.1 (fun j => (x.2 j).focus)
      let y := restartDone progs di.2 (x.1.2.2, x.2)
      ((di.1, di.2, y.1), y.2) := by
  have hh := transactionBody_zero progs I hB
    (choose x.1.1 (fun j => (x.2 j).focus)).2 blank a (x.1.2.2, x.2)
  exact congrArg (fun y => (((choose x.1.1 (fun j => (x.2 j).focus)).1,
    (choose x.1.1 (fun j => (x.2 j).focus)).2, y.1), y.2)) hh

theorem callBody_ne [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (hB : 0 < B)
    (blank : Γ) (a : Option Terminal) (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩)
    (x : CallCtrl progs D × (Fin t → STape Γ)) :
    bodyStep blank (callBody progs I choose hB) ph a x =
      let y := tick progs I blank x.1.2.1 a (x.1.2.2, x.2)
      ((x.1.1, x.1.2.1, y.1), y.2) := by
  have hh := transactionBody_ne progs I hB x.1.2.1 blank a ph hph (x.1.2.2, x.2)
  simpa only [bodyStep, callBody, if_neg hph] using
    congrArg (fun y => ((x.1.1, x.1.2.1, y.1), y.2)) hh

theorem callBody_tail [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (hB : 0 < B)
    (blank : Γ) (l : List (Option Terminal)) (ph : Fin B)
    (x : CallCtrl progs D × (Fin t → STape Γ))
    (hlen : ph.val + l.length ≤ B) (hpos : 0 < ph.val) :
    phaseRun blank (callBody progs I choose hB) l ph x =
      let y := runChunk progs I blank x.1.2.1 l (x.1.2.2, x.2)
      ((x.1.1, x.1.2.1, y.1), y.2) := by
  induction l generalizing ph x with
  | nil => rfl
  | cons a l ih =>
    have hne : ph ≠ ⟨0, hB⟩ := by intro h; subst ph; simp at hpos
    rw [phaseRun_cons, callBody_ne progs I choose hB blank a ph hne]
    by_cases hl : l = []
    · subst l; rfl
    · have hll : 0 < l.length := List.length_pos_iff.mpr hl
      have hb : ph.val + 1 < B := by simp only [List.length_cons] at hlen; omega
      apply ih
      · simp only [nextPhase, dif_pos hb]
        simp only [List.length_cons] at hlen
        omega
      · simp only [nextPhase, dif_pos hb]; omega

noncomputable def callRun (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (x : CallCtrl progs D × (Fin t → STape Γ)) :
    CallCtrl progs D × (Fin t → STape Γ) :=
  let di := choose x.1.1 (fun j => (x.2 j).focus)
  let y := runChunk progs I blank di.2 (List.replicate H none)
    (restartDone progs di.2 (x.1.2.2, x.2))
  ((di.1, di.2, y.1), y.2)

/-- Selection and outer advancement happen exactly once, even when the low
program changes symbols used by the outer conditions during the call. -/
theorem callBody_block [DecidableEq A] [DecidableEq C]
    [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (x : CallCtrl progs D × (Fin t → STape Γ)) :
    phaseRun blank (callBody progs I choose (Nat.zero_lt_succ H))
      (none :: List.replicate H none) ⟨0, Nat.zero_lt_succ H⟩ x =
      callRun progs I choose H blank x := by
  rw [phaseRun_cons, callBody_zero]
  cases H with
  | zero => rfl
  | succ H =>
    apply callBody_tail
    · simp [nextPhase, List.length_replicate]; omega
    · simp [nextPhase]

noncomputable def callMachine [DecidableEq A] [DecidableEq C]
    [Fintype D] [DecidableEq D] [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n) :
    StructuredMachine Terminal (CallCtrl progs D × Fin (H + 1)) Γ t (H + 1) :=
  ofPhases ht (Nat.zero_lt_succ H) blank
    (initialOuter, initialIndex, initialBank progs, false) (fun c => c.2.2.2)
    (callBody progs I choose (Nat.zero_lt_succ H))

/-- The internal machine executes a call in H+1 physical microsteps and
returns its local phase counter to zero. These are absent micro-inputs,
not H+1 repetitions of an external input symbol. -/
theorem callMachine_noneBlock [DecidableEq A] [DecidableEq C]
    [Fintype D] [DecidableEq D] [Fintype Γ] [DecidableEq Γ]
    (progs : Fin n → Prog A C) (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (ht : 0 < t) (initialOuter : D) (initialIndex : Fin n)
    (x : CallCtrl progs D × (Fin t → STape Γ)) :
    (List.replicate (H + 1) none).foldl
      (callMachine progs I choose H blank ht initialOuter initialIndex).sMicroStep
      { state := (x.1, ⟨0, Nat.zero_lt_succ H⟩), tape := x.2 } =
      let y := callRun progs I choose H blank x
      { state := (y.1, ⟨0, Nat.zero_lt_succ H⟩), tape := y.2 } := by
  simp only [callMachine, ofPhases_foldl, List.length_replicate,
    nextPhase_iterate_round (Nat.zero_lt_succ H)]
  rw [List.replicate_succ, callBody_block]

-- Avoid unfolding an entire fixed execution window in control equalities.
attribute [local irreducible] runChunk

/-- The chosen bounded program really reaches its Exec endpoint, and all
bank entries are again at safe call boundaries. The strict bound accounts
for the final normalization tick. -/
theorem callRun_exec (progs : Fin n → Prog A C)
    (I : Fin n → InterpF Terminal A C Γ t)
    (choose : D → (Fin t → Γ) → D × Fin n) (H : ℕ) (blank : Γ)
    (x : CallCtrl progs D × (Fin t → STape Γ))
    (hb : AtBoundary progs x.1.2.2.1)
    (tr : List (Fin t → Γ × Move))
    (he : Exec (I (choose x.1.1 (fun j => (x.2 j).focus)).2).toInterp blank
      (progs (choose x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr)
    (hlen : tr.length < H) :
    let y := callRun progs I choose H blank x
    y.2 = applyTrace blank x.2 tr ∧ AtBoundary progs y.1.2.2.1 ∧
      (y.1.2.2.1 (choose x.1.1 (fun j => (x.2 j).focus)).2).val = [] ∧
      (∀ j, j ≠ (choose x.1.1 (fun j => (x.2 j).focus)).2 →
        y.1.2.2.1 j = x.1.2.2.1 j) := by
  let i := (choose x.1.1 (fun j => (x.2 j).focus)).2
  let x1 := restartDone progs i (x.1.2.2, x.2)
  have hf : (x1.1.1 i).val = [progs i] := restartDone_fresh progs i _ (hb i)
  have ht : x1.2 = x.2 := restartDone_tapes progs i _
  have hex : Exec (I i).toInterp blank (progs i) x1.2 tr := by rw [ht]; exact he
  obtain ⟨hout, hempty⟩ := runChunk_exec_lt progs I blank i (List.replicate H none)
    x1 tr hf hex (by simpa using hlen)
  have hother : ∀ j, j ≠ i →
      (runChunk progs I blank i (List.replicate H none) x1).1.1 j = x.1.2.2.1 j := by
    intro j hj
    rw [runChunk_other progs I blank i j hj]
    exact restartDone_other progs i j hj _
  refine ⟨?_, ?_, hempty, hother⟩
  · change (runChunk progs I blank i (List.replicate H none) x1).2 = _
    rw [hout, ht]
  · intro j
    by_cases hj : j = i
    · subst j; exact Or.inl hempty
    · change ((runChunk progs I blank i (List.replicate H none) x1).1.1 j).val = [] ∨
        ((runChunk progs I blank i (List.replicate H none) x1).1.1 j).val = [progs j]
      rw [hother j hj]
      exact hb j

/-- Structured programs provide one concrete finite outer controller. The
idle label is used when no action is pending (its low program must be a no-op
where a semantic no-op is required). -/
def programChoice {C₀ : Type} (p : Prog (Fin n) C₀)
    (cond : C₀ → (Fin t → Γ) → Bool) (idle : Fin n)
    (c : CtrlS p) (σ : Fin t → Γ) : CtrlS p × Fin n :=
  (stepCtrlS p (fun q => cond q σ) c,
    (stepStack (fun q => cond q σ) c.val).2.getD idle)

/-- info: 'PalPeg.ProgLangBank.callBody_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callBody_block

/-- info: 'PalPeg.ProgLangBank.callRun_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms callRun_exec

end PalPeg.ProgLangBank
