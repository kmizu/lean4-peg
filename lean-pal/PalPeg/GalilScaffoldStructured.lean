import PalPeg.GalilScaffoldControl
import PalPeg.GalilScaffoldNextPc
import PalPeg.ProgramMachine

/-!
# Scaffold programs as structured machines

`GalilScaffoldControl.Tick code true` executes one instruction of a scaffold
program per tick. This module packages such a program as a
`StructuredMachine` with one micro-step per input symbol (`B = 1`), finite
control `Fin (code.length+1) × Bool` (clamped program counter and the done
flag), tape alphabet `Fin 9` with blank `6`, and proves the forward
simulation: every `Tick` is matched by `sMicroStep` on the encoded
configuration, hence every `Run` on `replicate m true` is matched by `srun`.
The input symbol is ignored by the control; it only paces the ticks.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldStructured
open GalilFppWide (Instruction)
open PalPeg.Program (StructuredMachine STape SConfig)
open PalPeg.Speedup (MultiStepMachine)
open PegSeparation.RealTimeTM (Move)

abbrev Control (m : ℕ) := Fin (m+1) × Bool

def clamp (m pc : ℕ) : Fin (m+1) := ⟨min pc m, by omega⟩

theorem clamp_val {n : ℕ} {code : List (Instruction n)} {pc : ℕ} {i : Instruction n}
    (hi : code[pc]? = some i) : (clamp code.length pc).val = pc := by
  obtain ⟨h,_⟩ := List.getElem?_eq_some_iff.1 hi
  simp only [clamp]; omega

def stays {n : ℕ} (focus : Fin n → Fin 9) : Fin n → Fin 9 × Move := fun k => (focus k, .stay)

def action {n : ℕ} (i : Instruction n) (focus : Fin n → Fin 9) : Fin n → Fin 9 × Move :=
  match i with
  | .write t v _ => fun k => if k = t then (v, .stay) else (focus k, .stay)
  | .move t d _ => fun k => if k = t then (focus k, if d then .right else .left) else (focus k, .stay)
  | _ => stays focus

def step {n : ℕ} (code : List (Instruction n)) (q : Control code.length) (focus : Fin n → Fin 9) :
    Control code.length × (Fin n → Fin 9 × Move) :=
  if q.2 then (q, stays focus) else
  match code[q.1.val]? with
  | none => (q, stays focus)
  | some i =>
    if i = .halt then ((q.1, true), stays focus) else
    match GalilScaffoldNextPc.next i focus with
    | none => (q, stays focus)
    | some pc => ((clamp code.length pc, false), action i focus)

def machine {n : ℕ} (hn : 0 < n) (code : List (Instruction n)) (entry : ℕ) :
    StructuredMachine Unit (Control code.length) (Fin 9) n 1 where
  tapeCount_pos := hn
  blank := 6
  initial := (clamp code.length entry, false)
  accepting := fun q => q.2
  micro := fun q _ focus => step code q focus

def encodeTape (t : GalilScaffoldTape.Tape) : STape (Fin 9) := ⟨t.left, t.focus, t.right⟩

def encode {n : ℕ} (m : ℕ) (x : GalilScaffoldControl.Machine n) :
    SConfig (Control m) (Fin 9) n :=
  ⟨(clamp m x.config.pc, x.done), fun k => encodeTape (x.config.tapes k)⟩

theorem apply_stay (T : STape (Fin 9)) : T.applyAction 6 (T.focus, .stay) = T := by
  cases T; rfl

theorem apply_stays {n : ℕ} (x : GalilScaffoldControl.Machine n) (k : Fin n) :
    (encodeTape (x.config.tapes k)).applyAction 6
      (stays (fun j => (encodeTape (x.config.tapes j)).focus) k) = encodeTape (x.config.tapes k) :=
  apply_stay _

theorem apply_right (t : GalilScaffoldTape.Tape) :
    (encodeTape t).applyAction 6 (t.focus, .right) = encodeTape (GalilScaffoldTape.moveRight t) := by
  cases t with
  | mk l f r => cases r <;> rfl

theorem apply_left (t : GalilScaffoldTape.Tape) (h : t.left ≠ []) :
    (encodeTape t).applyAction 6 (t.focus, .left) = encodeTape (GalilScaffoldTape.moveLeft t) := by
  cases t with
  | mk l f r =>
    cases l with
    | nil => exact absurd rfl h
    | cons a ls => rfl

theorem apply_write (t : GalilScaffoldTape.Tape) (s : Fin 9) :
    (encodeTape t).applyAction 6 (s, .stay) = encodeTape (GalilScaffoldTape.write t s) := rfl

/-- One tick of the control protocol is one micro-step of the structured
machine, for any input symbol (the control ignores it). -/
theorem tick_sim {n : ℕ} (hn : 0 < n) {code : List (Instruction n)} (entry : ℕ)
    {x y : GalilScaffoldControl.Machine n} (ht : GalilScaffoldControl.Tick code true x y)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (a : Option Unit) :
    (machine hn code entry).sMicroStep (encode code.length x) a = encode code.length y := by
  cases ht with
  | idle x enabled h =>
    have hd : x.done = true := by
      rcases h with h | h
      · cases h
      · exact h
    simp only [StructuredMachine.sMicroStep, machine, encode, step, hd, ite_true]
    congr 1
  | halt x hi =>
    have hc := clamp_val hi
    simp only [StructuredMachine.sMicroStep, machine, encode, step, Bool.false_eq_true, ite_false,
      hc, hi, ite_true]
    congr 1
  | execute x y i hi he =>
    have hc := clamp_val hi
    have hnext := GalilScaffoldNextPc.next_execute he (hw _ _ hi)
    have hn' : i ≠ .halt := by cases he <;> simp
    simp only [StructuredMachine.sMicroStep, machine, encode, step, Bool.false_eq_true, ite_false,
      hc, hi, hn']
    have hfocus : (fun j => (encodeTape (x.tapes j)).focus) = fun t => (x.tapes t).focus := rfl
    rw [hfocus, hnext]
    simp only
    congr 1
    funext k
    cases he with
    | right x t pc =>
      simp only [action, GalilScaffoldProgram.changed]
      by_cases hk : k = t
      · subst hk
        simp only [ite_true, Function.update_self]
        exact apply_right _
      · simp only [hk, ite_false, Function.update_of_ne hk]
        exact apply_stay _
    | left x t pc h =>
      simp only [action, GalilScaffoldProgram.changed]
      by_cases hk : k = t
      · subst hk
        simp only [ite_true, Function.update_self]
        exact apply_left _ h
      · simp only [hk, ite_false, Function.update_of_ne hk]
        exact apply_stay _
    | write x t s pc =>
      simp only [action, GalilScaffoldProgram.changed]
      by_cases hk : k = t
      · subst hk
        simp only [ite_true, Function.update_self]
        rfl
      · simp only [hk, ite_false, Function.update_of_ne hk]
        exact apply_stay _
    | read x t cs pc h =>
      simp only [action]
      exact apply_stay _

#print axioms tick_sim

theorem round_sim {n : ℕ} (hn : 0 < n) {code : List (Instruction n)} (entry : ℕ)
    {x y : GalilScaffoldControl.Machine n} (ht : GalilScaffoldControl.Tick code true x y)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i) :
    (machine hn code entry).sRound (encode code.length x) () = encode code.length y := by
  simp only [StructuredMachine.sRound, MultiStepMachine.roundInputs, Nat.sub_self,
    List.replicate_zero, List.foldl_cons, List.foldl_nil]
  exact tick_sim hn entry ht hw _

/-- A run of `m` enabled ticks is the structured run on `m` input symbols. -/
theorem run_sim {n : ℕ} (hn : 0 < n) {code : List (Instruction n)} (entry : ℕ)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (m : ℕ) : ∀ {x y : GalilScaffoldControl.Machine n},
    GalilScaffoldControl.Run code x (List.replicate m true) y →
    (List.replicate m ()).foldl (machine hn code entry).sRound (encode code.length x) =
      encode code.length y := by
  induction m with
  | zero =>
    intro x y hr
    cases hr
    rfl
  | succ m ih =>
    intro x y hr
    cases hr with
    | cons _ z _ _ _ hs hr' =>
      simp only [List.replicate_succ, List.foldl_cons]
      rw [round_sim hn entry hs hw]
      exact ih hr'

theorem encode_init {n : ℕ} (hn : 0 < n) (code : List (Instruction n)) (entry : ℕ) :
    (machine hn code entry).sInit =
      encode code.length (n := n) ⟨⟨entry, fun _ => GalilScaffoldTape.reset⟩, false⟩ := rfl

/-- Acceptance of the structured machine on `m` symbols is the done flag of the
control run of `m` enabled ticks from the reset configuration at `entry`. -/
theorem saccepts_iff {n : ℕ} (hn : 0 < n) {code : List (Instruction n)} (entry : ℕ)
    (hw : ∀ (pc : ℕ) (i : Instruction n), code[pc]? = some i → GalilScaffoldNextPc.WellFormed i)
    (m : ℕ) {y : GalilScaffoldControl.Machine n}
    (hr : GalilScaffoldControl.Run code (n := n) ⟨⟨entry, fun _ => GalilScaffoldTape.reset⟩, false⟩
      (List.replicate m true) y) :
    (machine hn code entry).SAccepts (List.replicate m ()) ↔ y.done = true := by
  simp only [StructuredMachine.SAccepts, StructuredMachine.srun, encode_init]
  rw [run_sim hn entry hw m hr]
  rfl

#print axioms saccepts_iff

end PalPeg.GalilScaffoldStructured
