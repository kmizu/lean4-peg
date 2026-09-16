import Mathlib
import PegSeparation.Common.Compiler.RealTimeTM.Model
import PalPeg.Speedup

/-!
# Structured ("program-level") multi-step real-time machines

`PalPeg.Speedup.MultiStepMachine` is stated with `Fin s` states and `Fin k` tape
symbols, which is convenient for the compression proof but painful to program in.
This file provides `StructuredMachine`, the same model over arbitrary finite
control and alphabet types `Q`, `Γ`, together with

* its own operational semantics (`sMicroStep`, `sRound`, `srun`, `SAccepts`) on
  structured configurations built from a `Γ`-zipper tape `STape Γ`;
* a transport `toMulti` into `MultiStepMachine` through `Fintype.equivFin`;
* the simulation lemma `srun_eq` / `sAccepts_iff`, so that users may reason
  entirely with `Q` and `Γ`;
* the corollary `structured_recognizedBy`, which chains through
  `PalPeg.Speedup.multiStep_recognizedBy`;
* a *program-notation layer* `ofPhases`, which builds the control type
  `Ctrl × Fin B` (control state + phase counter) automatically, so a `B`-phase
  round is written as a single `body` function of the phase index.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.Program

open PegSeparation.RealTimeTM
open PalPeg.Speedup

/-! ## Structured tapes -/

/-- A two-way infinite tape over an arbitrary symbol type, as a zipper.  This
mirrors the artifact's `TapeConfiguration` with `Fin k` replaced by `Γ`. -/
structure STape (Γ : Type) where
  left : List Γ
  focus : Γ
  right : List Γ

namespace STape

variable {Γ : Type}

/-- All-blank tape, head at the left edge. -/
def blankTape (blank : Γ) : STape Γ := ⟨[], blank, []⟩

/-- Write a symbol and move, exactly as `TapeConfiguration.applyAction`. -/
def applyAction (blank : Γ) (T : STape Γ) (wa : Γ × Move) : STape Γ :=
  match wa.2 with
  | .stay => { T with focus := wa.1 }
  | .right =>
      match T.right with
      | [] => { left := wa.1 :: T.left, focus := blank, right := [] }
      | n :: r => { left := wa.1 :: T.left, focus := n, right := r }
  | .left =>
      match T.left with
      | [] => { left := [], focus := wa.1, right := T.right }
      | n :: l => { left := l, focus := n, right := wa.1 :: T.right }

/-- Symbolwise encoding of a structured tape as an artifact tape. -/
def enc {k : ℕ} (e : Γ ≃ Fin k) (T : STape Γ) : TapeConfiguration k where
  left := T.left.map e
  focus := e T.focus
  right := T.right.map e

@[simp] theorem enc_blankTape {k : ℕ} (e : Γ ≃ Fin k) (blank : Γ) :
    enc e (blankTape blank) = { left := [], focus := e blank, right := [] } := rfl

theorem enc_applyAction {k : ℕ} (e : Γ ≃ Fin k) (blank : Γ) (T : STape Γ)
    (wa : Γ × Move) :
    enc e (T.applyAction blank wa) =
      (enc e T).applyAction (e blank) { write := e wa.1, move := wa.2 } := by
  obtain ⟨w, m⟩ := wa
  obtain ⟨L, f, R⟩ := T
  cases m <;> cases L <;> cases R <;> rfl

end STape

/-! ## Structured machines -/

/-- A strictly real-time machine performing `B` micro-transitions per input
symbol, with a *structured* control type `Q` and *structured* tape alphabet `Γ`.
Each micro-transition reads the symbol under every head and writes/moves on every
tape; the input symbol is available only during the first micro-step of a round
(this is enforced by `sRound` via `MultiStepMachine.roundInputs`). -/
structure StructuredMachine (Terminal : Type) (Q : Type) [Fintype Q] [DecidableEq Q]
    (Γ : Type) [Fintype Γ] [DecidableEq Γ] (tapeCount B : ℕ) where
  tapeCount_pos : 0 < tapeCount
  blank : Γ
  initial : Q
  accepting : Q → Bool
  micro : Q → Option Terminal → (Fin tapeCount → Γ) → Q × (Fin tapeCount → Γ × Move)

/-- A structured configuration: a control state and one `Γ`-tape per tape index. -/
structure SConfig (Q Γ : Type) (t : ℕ) where
  state : Q
  tape : Fin t → STape Γ

/-- Symbolwise encoding of a structured configuration as an artifact configuration. -/
noncomputable def encodeConfig {Q Γ : Type} [Fintype Q] [DecidableEq Q]
    [Fintype Γ] [DecidableEq Γ] {t : ℕ} (c : SConfig Q Γ t) :
    Configuration t (Fintype.card Q) (Fintype.card Γ) where
  state := Fintype.equivFin Q c.state
  tape := fun j => STape.enc (Fintype.equivFin Γ) (c.tape j)

namespace StructuredMachine

variable {Terminal Q Γ : Type} [Fintype Q] [DecidableEq Q] [Fintype Γ] [DecidableEq Γ]
  {t B : ℕ}

/-! ### Structured operational semantics -/

/-- All tapes blank, head at the left edge, control in `M.initial`. -/
def sInit (M : StructuredMachine Terminal Q Γ t B) : SConfig Q Γ t where
  state := M.initial
  tape := fun _ => STape.blankTape M.blank

/-- One micro-transition on a structured configuration. -/
def sMicroStep (M : StructuredMachine Terminal Q Γ t B) (c : SConfig Q Γ t)
    (a : Option Terminal) : SConfig Q Γ t :=
  let r := M.micro c.state a (fun j => (c.tape j).focus)
  { state := r.1
    tape := fun j => (c.tape j).applyAction M.blank (r.2 j) }

/-- One round: `B` micro-transitions triggered by one input symbol, the symbol
being visible only in the first of them. -/
def sRound (M : StructuredMachine Terminal Q Γ t B) (c : SConfig Q Γ t)
    (a : Terminal) : SConfig Q Γ t :=
  (MultiStepMachine.roundInputs B a).foldl M.sMicroStep c

/-- The structured run on a whole input word. -/
def srun (M : StructuredMachine Terminal Q Γ t B) (input : List Terminal) :
    SConfig Q Γ t :=
  input.foldl M.sRound M.sInit

/-- Structured acceptance. -/
def SAccepts (M : StructuredMachine Terminal Q Γ t B) (input : List Terminal) : Prop :=
  M.accepting (M.srun input).state = true

@[simp] theorem srun_nil (M : StructuredMachine Terminal Q Γ t B) :
    M.srun [] = M.sInit := rfl

@[simp] theorem srun_append_singleton (M : StructuredMachine Terminal Q Γ t B)
    (input : List Terminal) (a : Terminal) :
    M.srun (input ++ [a]) = M.sRound (M.srun input) a := by
  simp [srun, List.foldl_append]

/-! ### Transport into `MultiStepMachine` -/

/-- The index-based machine obtained by transporting `Q` and `Γ` through
`Fintype.equivFin`. -/
noncomputable def toMulti (M : StructuredMachine Terminal Q Γ t B) :
    MultiStepMachine Terminal t (Fintype.card Q) (Fintype.card Γ) B where
  tapeCount_pos := M.tapeCount_pos
  blank := Fintype.equivFin Γ M.blank
  initialState := Fintype.equivFin Q M.initial
  accepting := Finset.univ.filter fun i => M.accepting ((Fintype.equivFin Q).symm i) = true
  micro := fun q a f =>
    let r := M.micro ((Fintype.equivFin Q).symm q) a
      (fun j => (Fintype.equivFin Γ).symm (f j))
    (Fintype.equivFin Q r.1,
      fun j => { write := Fintype.equivFin Γ (r.2 j).1, move := (r.2 j).2 })

theorem toMulti_blank (M : StructuredMachine Terminal Q Γ t B) :
    M.toMulti.blank = Fintype.equivFin Γ M.blank := rfl

theorem toMulti_micro (M : StructuredMachine Terminal Q Γ t B) (q : Q)
    (a : Option Terminal) (s : Fin t → Γ) :
    M.toMulti.micro (Fintype.equivFin Q q) a (fun j => Fintype.equivFin Γ (s j)) =
      (Fintype.equivFin Q (M.micro q a s).1,
        fun j => { write := Fintype.equivFin Γ ((M.micro q a s).2 j).1,
                   move := ((M.micro q a s).2 j).2 }) := by
  simp [toMulti]

/-! ### Simulation -/

theorem encode_sInit (M : StructuredMachine Terminal Q Γ t B) :
    encodeConfig M.sInit = M.toMulti.initialConfiguration := rfl

theorem encode_sMicroStep (M : StructuredMachine Terminal Q Γ t B)
    (c : SConfig Q Γ t) (a : Option Terminal) :
    encodeConfig (M.sMicroStep c a) = M.toMulti.microStep (encodeConfig c) a := by
  obtain ⟨q, T⟩ := c
  have hfocus : (fun j => ((encodeConfig (SConfig.mk q T)).tape j).focus)
      = fun j => Fintype.equivFin Γ ((T j).focus) := rfl
  have hstate : (encodeConfig (SConfig.mk q T)).state = Fintype.equivFin Q q := rfl
  simp only [MultiStepMachine.microStep, hfocus, hstate, toMulti_micro]
  simp only [sMicroStep, encodeConfig, toMulti_blank, STape.enc_applyAction]

theorem encode_foldl (M : StructuredMachine Terminal Q Γ t B)
    (l : List (Option Terminal)) (c : SConfig Q Γ t) :
    encodeConfig (l.foldl M.sMicroStep c) =
      l.foldl M.toMulti.microStep (encodeConfig c) := by
  induction l generalizing c with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.foldl_cons, ih, encode_sMicroStep]

theorem encode_sRound (M : StructuredMachine Terminal Q Γ t B) (c : SConfig Q Γ t)
    (a : Terminal) :
    encodeConfig (M.sRound c a) = M.toMulti.round (encodeConfig c) a :=
  encode_foldl M _ c

/-- **Structured simulation.**  The structured run and the transported
index-based run agree, symbolwise. -/
theorem srun_eq (M : StructuredMachine Terminal Q Γ t B) (w : List Terminal) :
    encodeConfig (M.srun w) = M.toMulti.run w := by
  have h : ∀ (v : List Terminal) (c : SConfig Q Γ t),
      encodeConfig (v.foldl M.sRound c) = v.foldl M.toMulti.round (encodeConfig c) := by
    intro v
    induction v with
    | nil => intro c; rfl
    | cons a rest ih =>
        intro c
        simp only [List.foldl_cons, ih, encode_sRound]
  have := h w M.sInit
  rwa [encode_sInit] at this

/-- Structured acceptance agrees with the transported machine's acceptance. -/
theorem sAccepts_iff (M : StructuredMachine Terminal Q Γ t B) (w : List Terminal) :
    M.SAccepts w ↔ M.toMulti.Accepts w := by
  unfold SAccepts MultiStepMachine.Accepts
  rw [← srun_eq]
  simp [encodeConfig, toMulti]

/-! ### The main corollary -/

/-- **A structured multi-step machine defines a strictly real-time language.**
Chains `sAccepts_iff` with `PalPeg.Speedup.multiStep_recognizedBy`. -/
theorem structured_recognizedBy [DecidableEq Terminal] (hB : 0 < B)
    (M : StructuredMachine Terminal Q Γ t B) :
    RecognizedBy { w | M.SAccepts w } := by
  obtain ⟨s', k', M', hM'⟩ := PalPeg.Speedup.multiStep_recognizedBy hB M.toMulti
  exact ⟨t, s', k', M', fun w => (hM' w).trans (M.sAccepts_iff w).symm⟩

end StructuredMachine

/-! ## Program-notation layer: multi-phase rounds

A `B`-phase round is written by giving a single `body` which, in addition to the
control state, the (possibly absent) input symbol and the scanned symbols, sees
the *phase index* `Fin B`.  `ofPhases` builds the control type `Ctrl × Fin B`
and maintains the phase counter automatically: it increments on every
micro-step and wraps back to `0` exactly at the round boundary. -/

section Phases

variable {Terminal Ctrl Γ : Type} [Fintype Ctrl] [DecidableEq Ctrl]
  [Fintype Γ] [DecidableEq Γ] {t B : ℕ}

/-- Cyclic successor on phase indices. -/
def nextPhase (p : Fin B) : Fin B :=
  if h : (p : ℕ) + 1 < B then ⟨(p : ℕ) + 1, h⟩ else ⟨0, Nat.zero_lt_of_lt p.isLt⟩

/-- The per-phase transition supplied by the programmer. -/
abbrev PhaseBody (Terminal Ctrl Γ : Type) (t B : ℕ) : Type :=
  Ctrl → Option Terminal → Fin B → (Fin t → Γ) → Ctrl × (Fin t → Γ × Move)

/-- The structured machine described by a phase body. -/
def ofPhases (htape : 0 < t) (hB : 0 < B) (blank : Γ) (init : Ctrl)
    (acc : Ctrl → Bool) (body : PhaseBody Terminal Ctrl Γ t B) :
    StructuredMachine Terminal (Ctrl × Fin B) Γ t B where
  tapeCount_pos := htape
  blank := blank
  initial := (init, ⟨0, hB⟩)
  accepting := fun q => acc q.1
  micro := fun q a s =>
    let r := body q.1 a q.2 s
    ((r.1, nextPhase q.2), r.2)

/-- One application of the phase body, with the phase bookkeeping stripped away. -/
def bodyStep (blank : Γ) (body : PhaseBody Terminal Ctrl Γ t B) (p : Fin B)
    (a : Option Terminal) (x : Ctrl × (Fin t → STape Γ)) :
    Ctrl × (Fin t → STape Γ) :=
  let r := body x.1 a p (fun j => (x.2 j).focus)
  (r.1, fun j => (x.2 j).applyAction blank (r.2 j))

/-- `phaseRun blank body l p x` runs the body once per element of `l`, starting
at phase `p` and advancing the phase cyclically. -/
def phaseRun (blank : Γ) (body : PhaseBody Terminal Ctrl Γ t B) :
    List (Option Terminal) → Fin B → (Ctrl × (Fin t → STape Γ)) →
      Ctrl × (Fin t → STape Γ)
  | [], _, x => x
  | a :: rest, p, x => phaseRun blank body rest (nextPhase p) (bodyStep blank body p a x)

omit [Fintype Ctrl] [DecidableEq Ctrl] [Fintype Γ] [DecidableEq Γ] in
@[simp] theorem phaseRun_nil (blank : Γ) (body : PhaseBody Terminal Ctrl Γ t B)
    (p : Fin B) (x : Ctrl × (Fin t → STape Γ)) : phaseRun blank body [] p x = x := rfl

omit [Fintype Ctrl] [DecidableEq Ctrl] [Fintype Γ] [DecidableEq Γ] in
@[simp] theorem phaseRun_cons (blank : Γ) (body : PhaseBody Terminal Ctrl Γ t B)
    (a : Option Terminal) (l : List (Option Terminal)) (p : Fin B)
    (x : Ctrl × (Fin t → STape Γ)) :
    phaseRun blank body (a :: l) p x =
      phaseRun blank body l (nextPhase p) (bodyStep blank body p a x) := rfl

/-- Any block of micro-steps of `ofPhases` is the corresponding `phaseRun`, with
the phase counter advanced by iterated `nextPhase`. -/
theorem ofPhases_foldl (htape : 0 < t) (hB : 0 < B) (blank : Γ) (init : Ctrl)
    (acc : Ctrl → Bool) (body : PhaseBody Terminal Ctrl Γ t B)
    (l : List (Option Terminal)) (p : Fin B) (c : Ctrl) (T : Fin t → STape Γ) :
    l.foldl (ofPhases htape hB blank init acc body).sMicroStep
        { state := (c, p), tape := T } =
      { state := ((phaseRun blank body l p (c, T)).1, nextPhase^[l.length] p)
        tape := (phaseRun blank body l p (c, T)).2 } := by
  induction l generalizing p c T with
  | nil => rfl
  | cons a rest ih =>
      have hstep :
          (ofPhases htape hB blank init acc body).sMicroStep
              { state := (c, p), tape := T } a =
            { state := ((bodyStep blank body p a (c, T)).1, nextPhase p)
              tape := (bodyStep blank body p a (c, T)).2 } := rfl
      simp only [List.foldl_cons, hstep, ih, List.length_cons, phaseRun_cons,
        Function.iterate_succ_apply]

theorem nextPhase_iterate (hB : 0 < B) :
    ∀ (i : ℕ) (hi : i < B), nextPhase^[i] (⟨0, hB⟩ : Fin B) = ⟨i, hi⟩ := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ n ih =>
      intro hi
      have hn : n < B := by omega
      have hlt : ((⟨n, hn⟩ : Fin B) : ℕ) + 1 < B := hi
      rw [Function.iterate_succ_apply', ih hn]
      simp [nextPhase, hlt]

/-- After a full round of `B` micro-steps the phase counter is back to `0`. -/
theorem nextPhase_iterate_round (hB : 0 < B) :
    nextPhase^[B] (⟨0, hB⟩ : Fin B) = ⟨0, hB⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
  rw [Function.iterate_succ_apply', nextPhase_iterate hB m (by omega)]
  simp [nextPhase]

/-- **One round of `ofPhases` is the `B`-fold composition of the phase body**,
run at phases `0, 1, …, B-1` on the micro-inputs
`some a, none, …, none`, and it returns the phase counter to `0`. -/
theorem ofPhases_round (htape : 0 < t) (hB : 0 < B) (blank : Γ) (init : Ctrl)
    (acc : Ctrl → Bool) (body : PhaseBody Terminal Ctrl Γ t B)
    (c : Ctrl) (T : Fin t → STape Γ) (a : Terminal) :
    (ofPhases htape hB blank init acc body).sRound
        { state := (c, ⟨0, hB⟩), tape := T } a =
      { state :=
          ((phaseRun blank body (MultiStepMachine.roundInputs B a) ⟨0, hB⟩ (c, T)).1,
            ⟨0, hB⟩)
        tape :=
          (phaseRun blank body (MultiStepMachine.roundInputs B a) ⟨0, hB⟩ (c, T)).2 } := by
  rw [StructuredMachine.sRound, ofPhases_foldl]
  rw [MultiStepMachine.length_roundInputs B hB a, nextPhase_iterate_round hB]

/-- The initial configuration of `ofPhases` is at phase `0`, so `ofPhases_round`
applies at every round boundary of a run. -/
theorem ofPhases_sInit (htape : 0 < t) (hB : 0 < B) (blank : Γ) (init : Ctrl)
    (acc : Ctrl → Bool) (body : PhaseBody Terminal Ctrl Γ t B) :
    (ofPhases htape hB blank init acc body).sInit =
      { state := (init, ⟨0, hB⟩), tape := fun _ => STape.blankTape blank } := rfl

end Phases

end PalPeg.Program
