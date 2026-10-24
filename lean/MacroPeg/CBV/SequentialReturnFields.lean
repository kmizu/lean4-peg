import MacroPeg.CBV.SequentialRefReturnDispatchMachine

/-! Control-field layout shared by expression and argument-value returns. -/
namespace Shallot.MacroPeg.CBV.SequentialReturnFields
open Complexity SequentialCursorEdit SequentialCursorEditMachine SequentialControlEditMachine
open SequentialSharedWords (Config CaptureEnv)
abbrev ReturnValue := SequentialSharedWords.Value
abbrev ReturnFrame := SequentialSharedWords.Frame
open SequentialSharedStateCodec (encode write writeTask writeFrame writeFrames Input)
open SequentialCaptureCopyMachine (withInput)
open SequentialScopeWordMachine (resultFields)

def before (m : Nat) (E : CaptureEnv) (v : ReturnValue) (f : ReturnFrame) (K : List ReturnFrame) : Config :=
  ⟨m,.value v,E,f :: K⟩

def frameTag : ReturnFrame → Nat
  | .seq _ => 0
  | .alt _ _ => 1
  | .notP _ => 2
  | .star _ _ => 3
  | .argHead _ _ => 4
  | .argCons _ => 5
  | .call _ => 6
  | .scope _ => 7

def payload (ns : List CBVtoCBN.CompileNode) (f : ReturnFrame) : List Nat := (writeFrame ns f).control.tail

theorem frame_fields (ns : List CBVtoCBN.CompileNode) (f : ReturnFrame) :
    (writeFrame ns f).control=frameTag f :: payload ns f := by cases f <;> rfl

theorem frame_tag_bound (f : ReturnFrame) : frameTag f ≤ 7 := by cases f <;> simp [frameTag]

theorem value_fields (ns : List CBVtoCBN.CompileNode) (v : ReturnValue) :
    (writeTask ns (.value v)).control=resultFields v := by
  cases v with
  | expr r => cases r with
    | none => rfl
    | some v => cases v <;> rfl
  | args r => cases r with
    | none => rfl
    | some v => cases v with
      | none => rfl
      | some Wq => cases Wq; rfl

theorem before_control (ns : List CBVtoCBN.CompileNode) (x : List Char) (m : Nat)
    (E : CaptureEnv) (v : ReturnValue) (f : ReturnFrame) (K : List ReturnFrame) :
    withInput (encode ns (before m E v f K)) x 2=blocks (writeFrames ns K).control ++
      blocks (frameTag f :: payload ns f) ++ blocks ([E.length,K.length+1] ++ resultFields v) := by
  change SequentialCursorEntryMachine.layout (encode ns (before m E v f K)) 2 = _
  rw [SequentialAnyPackedMachine.layout_control]
  have he : (write ns (before m E v f K)).control=[E.length,K.length+1] ++ resultFields v ++
      (writeFrame ns f).control ++ (writeFrames ns K).control := by
    simp [write,before,writeFrames,Input.append,SequentialSharedStateCodec.putControl,
      SequentialSharedStateCodec.putWords,value_fields,List.append_assoc]
  rw [he,frame_fields]
  simp only [blocks_append,List.append_assoc]

def program (saved : Nat) (next : Nat → LProg 8) : LProg 8 :=
  SequentialTagDispatchMachine.program 2 1 saved 7 next

theorem dispatch_runs (next : Nat → LProg 8) (tag : Nat) (htag : tag ≤ 7)
    (header fields tail : List Nat) (L M : Lists 8) {B T : Nat}
    (hctrl : L 2=tail ++ blocks (tag :: fields) ++ blocks header) (h1 : L 1=[]) (hL : LenOK B L)
    (hp : Runs (LenOK B) (next tag) L M T) :
    ∃ U, Runs (LenOK B) (program header.length next) L M U := by
  let C := (tail ++ blocks fields) ++ [0]
  have hsrc : L 2=C ++ unary tag ++ blocks header := by rw [hctrl,blocks_cons]; simp only [C,List.append_assoc]
  exact SequentialTagDispatchMachine.dispatch_runs (src := (2 : Fin 8)) (tmp := 1) (by decide) header 7 tag htag C
    next L M hsrc (by rw [lastSym_append]; rfl) h1 hL hp

end Shallot.MacroPeg.CBV.SequentialReturnFields
