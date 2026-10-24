import MacroPeg.CBV.SequentialCursorEditMachine

/-! Connect the direct cursor subroutine to actual structural Seq entries.
The other streams of the complete packed state stay on their tapes. This
updates the cursor component only, not the control or word components. -/
namespace Shallot.MacroPeg.CBV.SequentialCursorEntryMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialSharedStateCodec (Packed encode)

private def wordSymbol : Option Char → Nat
  | none => 0
  | some c => c.toNat + 1

/-- Tape 0 is the cursor stream; 1 and 5 are empty scratch. The remaining
tapes hold the control, shared clock, and captured words without modification. -/
def layout (packed : Packed) : Lists 6 := fun i =>
  if i=0 then bits packed.cursors else if i=2 then bits packed.control
  else if i=3 then bits packed.clock else if i=4 then (packed.words.map wordSymbol).reverse else []

theorem layout_fits (packed : Packed) {B : Nat} (h : packed.length+2 ≤ B) : LenOK B (layout packed) := by
  intro i
  unfold Packed.length at h
  by_cases h0 : i=0 <;> by_cases h2 : i=2 <;> by_cases h3 : i=3 <;> by_cases h4 : i=4 <;>
    simp_all [layout,bits_length] <;> omega

theorem layout_cursors (ns : List CBVtoCBN.CompileNode) (c : Config) :
    layout (encode ns c) 0 = cursors (SequentialSharedCursors.positions c) := by
  simp [layout,encode,SequentialSharedStateCodec.write_cursors,cursors]

theorem layout_cursor_length (packed : Packed) : (layout packed 0).length ≤ packed.length := by
  simp only [layout,ite_true,bits_length]
  unfold Packed.length
  omega

inductive Entry where
  | alt (a b : MExp)
  | notP (a : MExp)
  | star (a : MExp)
  | args (a : MExp) (tail : List MExp)

def before (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,match entry with
    | .alt a b => .expr (.alt a b) p
    | .notP a => .expr (.notP a) p
    | .star a => .expr (.star a) p
    | .args a es => .args (a :: es) p,E,K⟩

def after (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) : Config :=
  match entry with
  | .alt a b => ⟨m,.expr a p,E,.alt b p :: K⟩
  | .notP a => ⟨m,.expr a p,E,.notP p :: K⟩
  | .star a => ⟨m,.expr a p,E,.star a p :: K⟩
  | .args a es => ⟨m,.expr a p,E,.argHead es p :: K⟩

theorem actual_step (g : MGrammar) (x : List Char) (entry : Entry) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame) :
    SequentialSharedWords.step g x (before entry m E p K) = some (after entry m E p K) := by
  cases entry <;> rfl

theorem before_positions (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    SequentialSharedCursors.positions (before entry m E p K) =
      p :: K.filterMap SequentialSharedCursors.frameCursor := by cases entry <;> rfl

theorem after_positions (entry : Entry) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) :
    SequentialSharedCursors.positions (after entry m E p K) =
      p :: p :: K.filterMap SequentialSharedCursors.frameCursor := by cases entry <;> rfl

/-- An initialized reachable state's cursor component is updated by an actual
list program with a linear capacity, while the other full-state streams survive. -/
theorem cursor_update (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) :
    ∃ T, Complexity.Runs
      (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1) + 3))
      (duplicate (0 : Fin 6) 1)
      (layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K)))
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after entry m E p K)))) T := by
  let packed := encode (CBVtoCBN.compilerNodes g e) (before entry m E p K)
  have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
  change packed.length ≤ _ at hb
  have hc := layout_cursor_length packed
  have hL := layout_fits packed (B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+3)
    (by omega)
  have hs : layout packed 0 = cursors (p :: K.filterMap SequentialSharedCursors.frameCursor) := by
    rw [layout_cursors,before_positions]
  have ht : layout packed 1 = [] := rfl
  have hr := duplicate_current_runs (src := (0 : Fin 6)) (tmp := 1) (by decide) p
    (K.filterMap SequentialSharedCursors.frameCursor) (layout packed) hs ht hL (by omega)
  simpa only [after_positions] using hr

/-- Compiled tape execution of that component update. The bound includes all
intermediate tape positions and writes, not merely the packed endpoints. -/
theorem cursor_update_tape (g : MGrammar) (x : List Char) (e : MExp) (entry : Entry) (m : Nat)
    (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before entry m E p K)) (τ : Tapes 6)
    (hrep : Rep (layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K))) τ) :
    ∃ t τ', Exec (TFits (SequentialSharedStateBound.linearFactor g e * (x.length+1)+3))
      (duplicate (0 : Fin 6) 1).compile τ t (.cont τ') ∧
      Rep ((layout (encode (CBVtoCBN.compilerNodes g e) (before entry m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after entry m E p K)))) τ' := by
  obtain ⟨T,hr⟩ := cursor_update g x e entry m E p K h
  exact tape_runs hr τ hrep

end Shallot.MacroPeg.CBV.SequentialCursorEntryMachine
