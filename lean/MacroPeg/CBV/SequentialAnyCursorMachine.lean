import MacroPeg.CBV.SequentialCursorDecreaseMachine

/-! Input-independent cursor handling for the actual `any` atom. The unary
head itself selects success or empty-input failure, with no supplied result
position or consumed-character counter. Other packed streams remain held. -/
namespace Shallot.MacroPeg.CBV.SequentialAnyCursorMachine
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialCursorDecreaseMachine
open SequentialSharedWords (Config CaptureEnv Runs initial)
open SequentialCursorEntryMachine (layout layout_fits layout_cursors)
open SequentialSharedStateCodec (encode)

/-- A positive current cursor ends in 1; cursor zero ends in the delimiter 0. -/
def program : LProg 6 := .ite 0 (symIs 1) (decrement 0 1) (dropBlock 0 1)

def before (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.expr .any p,E,K⟩

def after (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) : Config :=
  ⟨m,.value (.expr (match p with
    | 0 => some none
    | q+1 => some (some q))),E,K⟩

theorem actual_step (g : MGrammar) (x : List Char) (m : Nat) (E : CaptureEnv) (p : Nat)
    (K : List SequentialSharedWords.Frame) (hp : p ≤ x.length) :
    SequentialSharedWords.step g x (before m E p K) = some (after m E p K) := by
  cases p with
  | zero => simp [before,after,SequentialSharedWords.step,SequentialSharedWords.atom,sfx]
  | succ p =>
    have hl := length_sfx x hp
    cases hs : sfx x (p+1) with
    | nil => simp [hs] at hl
    | cons c rest =>
      rw [hs] at hl
      have he : rest.length = p := by simp at hl; omega
      simp only [before,after,SequentialSharedWords.step,SequentialSharedWords.atom,hs,he]

theorem before_positions (m : Nat) (E : CaptureEnv) (p : Nat) (K : List SequentialSharedWords.Frame) :
    SequentialSharedCursors.positions (before m E p K) =
      p :: K.filterMap SequentialSharedCursors.frameCursor := rfl

/-- Both branches of the actual atom's cursor update execute with linear
capacity, including all instruction states, and leave no scratch behind. -/
theorem cursor_update (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E p K)) :
    SequentialSharedWords.step g x (before m E p K) = some (after m E p K) ∧
    ∃ T, Complexity.Runs
      (LenOK (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2)) program
      (layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K)))
      ((layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after m E p K)))) T := by
  have hchain := SequentialSharedCursors.reachable_chain g x e (before m E p K) h
  rw [before_positions] at hchain
  cases hchain with
  | cons hz ht =>
    refine ⟨actual_step g x m E p K ht.bound,?_⟩
    let packed := encode (CBVtoCBN.compilerNodes g e) (before m E p K)
    have hb := SequentialSharedStateBound.encoded_state_linear g x e _ h
    change packed.length ≤ _ at hb
    have hL := layout_fits packed
      (B := SequentialSharedStateBound.linearFactor g e * (x.length+1)+2) (by omega)
    have hs : layout packed 0 = cursors (p :: K.filterMap SequentialSharedCursors.frameCursor) := by
      rw [layout_cursors,before_positions]
    have htmp : layout packed 1 = [] := rfl
    cases p with
    | zero =>
      obtain ⟨T,hr⟩ := drop_current_runs (src := (0 : Fin 6)) (tmp := 1) (by decide)
        ht (layout packed) hs htmp hL
      have hc : symIs 1 (lastSym (layout packed 0)) = false := by
        simp [hs,cursors_cons,lastSym_append,symIs]
      exact ⟨T+1,hr.iteF hL hc⟩
    | succ p =>
      obtain ⟨T,hr⟩ := decrement_current_runs (src := (0 : Fin 6)) (tmp := 1) (by decide)
        ht (layout packed) hs htmp hL
      have hc : symIs 1 (lastSym (layout packed 0)) = true := by
        have he : unary (p+1) = unary p ++ [1] := List.replicate_succ'
        rw [hs,cursors_cons,he,← List.append_assoc,lastSym_append]
        decide
      exact ⟨T+1,hr.iteT hL hc⟩

/-- This is the cursor component of an atom transition, not an updated full
packed successor. Its other streams still contain the source-state fields. -/
theorem cursor_update_tape (g : MGrammar) (x : List Char) (e : MExp) (m : Nat) (E : CaptureEnv)
    (p : Nat) (K : List SequentialSharedWords.Frame)
    (h : Runs g x (initial g x e) (before m E p K)) (τ : Tapes 6)
    (hrep : Rep (layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))) τ) :
    ∃ t τ', Exec (TFits (SequentialSharedStateBound.linearFactor g e * (x.length+1)+2))
      program.compile τ t (.cont τ') ∧
      Rep ((layout (encode (CBVtoCBN.compilerNodes g e) (before m E p K))).set 0
        (cursors (SequentialSharedCursors.positions (after m E p K)))) τ' := by
  obtain ⟨hs,T,hr⟩ := cursor_update g x e m E p K h
  exact tape_runs hr τ hrep


/-- The cursor subroutine's compiled actions respect any fixed alphabet
large enough for its two pushed bit symbols and the tape markers. -/
theorem finite_alphabet (E : Nat) (hE : 2 ≤ E) : program.compile.SymOK (E+4) := by
  apply compile_symOK E
  refine ⟨decrement_constOK hE _ _,?_⟩
  simp [dropBlock,scan,moveTop,moveAll,clearP,LProg.ConstOK]

end Shallot.MacroPeg.CBV.SequentialAnyCursorMachine
