import MacroPeg.CBV.SequentialSharedPool

/-! A whole-state codec for the word machine. Three logical streams retain
control, ordered cursors, and ordered words; the packed representation encodes
all three and the shared clock over fixed symbol alphabets. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedStateCodec
open SequentialSharedWords
open SequentialSharedPool (TaskOK FrameOK ConfigOK)
open SequentialStackPool (ExprOK ArgsOK)
open CBVtoCBN (CompileNode compilerNodes)

structure Input where
  control : List Nat
  cursors : List Nat
  words : CaptureEnv
  deriving Repr

def Input.empty : Input := ⟨[],[],[]⟩
def Input.append (a b : Input) : Input :=
  ⟨a.control ++ b.control,a.cursors ++ b.cursors,a.words ++ b.words⟩

infixr:65 " +++ " => Input.append

theorem Input.append_assoc (a b c : Input) : (a +++ b) +++ c = a +++ (b +++ c) := by
  cases a; cases b; cases c
  simp only [Input.append,List.append_assoc]

def putControl (n : Nat) : Input := ⟨[n],[],[]⟩
def putCursor (p : Nat) : Input := ⟨[],[p],[]⟩
def putWords (W : CaptureEnv) : Input := ⟨[],[],W⟩
def putExpr (ns : List CompileNode) (e : MExp) : Input :=
  ⟨SequentialStackCodec.writeExpr ns e,[],[]⟩
def putExprs (ns : List CompileNode) (es : List MExp) : Input :=
  ⟨SequentialStackCodec.writeExprs ns es,[],[]⟩

abbrev Reader (α : Type) := StateT Input Option α

theorem bind_apply {α β : Type} (reader : Reader α) (next : α → Reader β) (input : Input) :
    (reader >>= next) input = (reader input).bind (fun result => next result.1 result.2) := rfl

theorem pure_apply {α : Type} (a : α) (input : Input) :
    (pure a : Reader α) input = some (a,input) := rfl

theorem option_bind_some {α β : Type} (a : α) (next : α → Option β) :
    (some a >>= next) = next a := rfl

def liftControl {α : Type} (reader : SequentialStackCodec.Reader α) : Reader α := fun input => do
  let (a,rest) ← reader input.control
  pure (a,{input with control := rest})

def readControl : Reader Nat := liftControl fun
  | n :: rest => some (n,rest)
  | [] => none

def readCursor : Reader Nat := fun input =>
  match input.cursors with
  | p :: rest => some (p,{input with cursors := rest})
  | [] => none

def readWord : Reader (List Char) := fun input =>
  match input.words with
  | w :: rest => some (w,{input with words := rest})
  | [] => none

def readMany {α : Type} (reader : Reader α) : Nat → Reader (List α)
  | 0 => pure []
  | k + 1 => do
    let a ← reader
    let tail ← readMany reader k
    pure (a :: tail)

def readEnv (k : Nat) : Reader CaptureEnv := readMany readWord k
def readExpr (ns : List CompileNode) : Reader MExp := liftControl (SequentialStackCodec.readExpr ns)
def readExprs (ns : List CompileNode) : Reader (List MExp) := liftControl (SequentialStackCodec.readExprs ns)

theorem readControl_put (n : Nat) (tail : Input) :
    readControl (putControl n +++ tail) = some (n,tail) := rfl

theorem readCursor_put (p : Nat) (tail : Input) :
    readCursor (putCursor p +++ tail) = some (p,tail) := rfl

theorem readWord_put (w : List Char) (tail : Input) :
    readWord (putWords [w] +++ tail) = some (w,tail) := rfl

theorem readEnv_put (W : CaptureEnv) (tail : Input) :
    readEnv W.length (putWords W +++ tail) = some (W,tail) := by
  induction W generalizing tail with
  | nil => rfl
  | cons w W ih =>
    change ((readEnv W.length (putWords W +++ tail)).bind
      (fun result => some (w :: result.1,result.2))) = _
    rw [ih]
    rfl

theorem readExpr_put {ns : List CompileNode} {e : MExp} (h : ExprOK ns e) (tail : Input) :
    readExpr ns (putExpr ns e +++ tail) = some (e,tail) := by
  simp only [readExpr,liftControl,putExpr,Input.append]
  rw [SequentialStackCodec.readExpr_write h]
  rfl

theorem readExprs_put {ns : List CompileNode} {es : List MExp} (h : ArgsOK ns es) (tail : Input) :
    readExprs ns (putExprs ns es +++ tail) = some (es,tail) := by
  simp only [readExprs,liftControl,putExprs,Input.append]
  rw [SequentialStackCodec.readExprs_write h]
  rfl

def writeTask (ns : List CompileNode) : Task → Input
  | .expr e p => putControl 0 +++ putExpr ns e +++ putCursor p
  | .args es p => putControl 1 +++ putExprs ns es +++ putCursor p
  | .query i W p => putControl 2 +++ putControl i +++ putControl W.length +++ putWords W +++ putCursor p
  | .value (.expr none) => putControl 3 +++ putControl 0
  | .value (.expr (some none)) => putControl 3 +++ putControl 1
  | .value (.expr (some (some p))) => putControl 3 +++ putControl 2 +++ putCursor p
  | .value (.args none) => putControl 4 +++ putControl 0
  | .value (.args (some none)) => putControl 4 +++ putControl 1
  | .value (.args (some (some (W,p)))) =>
      putControl 4 +++ putControl 2 +++ putControl W.length +++ putWords W +++ putCursor p

def readTask (ns : List CompileNode) : Reader Task := do
  let tag ← readControl
  match tag with
  | 0 => let e ← readExpr ns; let p ← readCursor; pure (.expr e p)
  | 1 => let es ← readExprs ns; let p ← readCursor; pure (.args es p)
  | 2 =>
    let i ← readControl
    let k ← readControl
    let W ← readEnv k
    let p ← readCursor
    pure (.query i W p)
  | 3 =>
    let tag ← readControl
    match tag with
    | 0 => pure (.value (.expr none))
    | 1 => pure (.value (.expr (some none)))
    | 2 => let p ← readCursor; pure (.value (.expr (some (some p))))
    | _ => failure
  | 4 =>
    let tag ← readControl
    match tag with
    | 0 => pure (.value (.args none))
    | 1 => pure (.value (.args (some none)))
    | 2 =>
      let k ← readControl
      let W ← readEnv k
      let p ← readCursor
      pure (.value (.args (some (some (W,p)))))
    | _ => failure
  | _ => failure

def writeFrame (ns : List CompileNode) : Frame → Input
  | .seq b => putControl 0 +++ putExpr ns b
  | .alt b p => putControl 1 +++ putExpr ns b +++ putCursor p
  | .notP p => putControl 2 +++ putCursor p
  | .star a p => putControl 3 +++ putExpr ns a +++ putCursor p
  | .argHead es p => putControl 4 +++ putExprs ns es +++ putCursor p
  | .argCons w => putControl 5 +++ putWords [w]
  | .call i => putControl 6 +++ putControl i
  | .scope E => putControl 7 +++ putControl E.length +++ putWords E

def readFrame (ns : List CompileNode) : Reader Frame := do
  let tag ← readControl
  match tag with
  | 0 => let b ← readExpr ns; pure (.seq b)
  | 1 => let b ← readExpr ns; let p ← readCursor; pure (.alt b p)
  | 2 => let p ← readCursor; pure (.notP p)
  | 3 => let a ← readExpr ns; let p ← readCursor; pure (.star a p)
  | 4 => let es ← readExprs ns; let p ← readCursor; pure (.argHead es p)
  | 5 => let w ← readWord; pure (.argCons w)
  | 6 => let i ← readControl; pure (.call i)
  | 7 => let k ← readControl; let E ← readEnv k; pure (.scope E)
  | _ => failure

theorem readTask_write {ns : List CompileNode} {t : Task} (h : TaskOK ns t) (tail : Input) :
    readTask ns (writeTask ns t +++ tail) = some (t,tail) := by
  cases t with
  | expr e p =>
    simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
      readControl_put,readExpr_put h,readCursor_put,Option.bind_some]
  | args es p =>
    simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
      readControl_put,readExprs_put h,readCursor_put,Option.bind_some]
  | query i W p =>
    simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
      readControl_put,readEnv_put,readCursor_put,Option.bind_some]
  | value v =>
    cases v <;> rename_i r
    all_goals cases r with
    | none =>
      simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
        readControl_put,Option.bind_some]
    | some result =>
      cases result with
      | none =>
        simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
          readControl_put,Option.bind_some]
      | some val =>
        first
        | solve | simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
            readControl_put,readCursor_put,Option.bind_some]
        | obtain ⟨W,p⟩ := val
          simp only [writeTask,Input.append_assoc,readTask,bind_apply,pure_apply,
            readControl_put,readEnv_put,readCursor_put,Option.bind_some]

theorem readFrame_write {ns : List CompileNode} {f : Frame} (h : FrameOK ns f) (tail : Input) :
    readFrame ns (writeFrame ns f +++ tail) = some (f,tail) := by
  cases f with
  | seq b | alt b p =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readExpr_put h,readCursor_put,Option.bind_some]
  | notP p =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readCursor_put,Option.bind_some]
  | star a p =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readExpr_put h.star,readCursor_put,Option.bind_some]
  | argHead es p =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readExprs_put h,readCursor_put,Option.bind_some]
  | argCons w =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readWord_put,Option.bind_some]
  | call i =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,Option.bind_some]
  | scope E =>
    simp only [writeFrame,Input.append_assoc,readFrame,bind_apply,pure_apply,
      readControl_put,readEnv_put,Option.bind_some]

def writeFrames (ns : List CompileNode) : List Frame → Input
  | [] => Input.empty
  | f :: K => writeFrame ns f +++ writeFrames ns K

theorem readFrames_write {ns : List CompileNode} (K : List Frame)
    (h : ∀ f ∈ K, FrameOK ns f) (tail : Input) :
    readMany (readFrame ns) K.length (writeFrames ns K +++ tail) = some (K,tail) := by
  induction K generalizing tail with
  | nil => rfl
  | cons f K ih =>
    simp only [writeFrames,Input.append_assoc,List.length_cons,readMany,bind_apply,
      readFrame_write (h f List.mem_cons_self),Option.bind_some]
    rw [ih (fun F hF => h F (List.mem_cons_of_mem f hF))]
    rfl

def write (ns : List CompileNode) (c : Config) : Input :=
  putControl c.env.length +++ putControl c.stack.length +++ writeTask ns c.task +++
    putWords c.env +++ writeFrames ns c.stack

def read (ns : List CompileNode) (clock : Nat) : Reader Config := do
  let envLength ← readControl
  let stackLength ← readControl
  let task ← readTask ns
  let E ← readEnv envLength
  let K ← readMany (readFrame ns) stackLength
  pure ⟨clock,task,E,K⟩

/-- Environment counts and frame tags assign each word and cursor to its
original field; the theorem leaves all three arbitrary tail streams intact. -/
theorem read_write {ns : List CompileNode} {c : Config} (h : ConfigOK ns c) (tail : Input) :
    read ns c.clock (write ns c +++ tail) = some (c,tail) := by
  simp only [write,Input.append_assoc,read,bind_apply,pure_apply,readControl_put,
    readTask_write h.1,readEnv_put,readFrames_write _ h.2,Option.bind_some]

theorem task_cursors (ns : List CompileNode) (t : Task) :
    (writeTask ns t).cursors = (SequentialSharedCursors.taskCursor t).toList := by
  cases t with
  | expr _ _ | args _ _ | query _ _ _ => rfl
  | value v =>
    cases v <;> rename_i r
    all_goals cases r with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some val => first | rfl | obtain ⟨W,p⟩ := val; rfl

theorem task_words (ns : List CompileNode) (t : Task) :
    (writeTask ns t).words = SequentialSharedWordSpace.taskWords t := by
  cases t with
  | expr _ _ | args _ _ => rfl
  | query _ _ _ => simp [writeTask,Input.append,putControl,putWords,putCursor,
      SequentialSharedWordSpace.taskWords]
  | value v =>
    cases v <;> rename_i r
    all_goals cases r with
    | none => rfl
    | some result => cases result with
      | none => rfl
      | some val =>
        first
        | rfl
        | obtain ⟨W,p⟩ := val
          simp [writeTask,Input.append,putControl,putWords,putCursor,
            SequentialSharedWordSpace.taskWords]

theorem frame_cursors (ns : List CompileNode) (f : Frame) :
    (writeFrame ns f).cursors = (SequentialSharedCursors.frameCursor f).toList := by
  cases f <;> rfl

theorem frame_words (ns : List CompileNode) (f : Frame) :
    (writeFrame ns f).words = SequentialSharedWordSpace.frameWords f := by
  cases f <;> rfl

theorem frames_cursors (ns : List CompileNode) (K : List Frame) :
    (writeFrames ns K).cursors = K.filterMap SequentialSharedCursors.frameCursor := by
  induction K with
  | nil => rfl
  | cons f K ih =>
    simp only [writeFrames,Input.append,frame_cursors,ih,List.filterMap_cons]
    cases SequentialSharedCursors.frameCursor f <;> rfl

theorem frames_words (ns : List CompileNode) (K : List Frame) :
    (writeFrames ns K).words = K.flatMap SequentialSharedWordSpace.frameWords := by
  induction K with
  | nil => rfl
  | cons f K ih => simp only [writeFrames,Input.append,frame_words,ih,List.flatMap_cons]

theorem write_cursors (ns : List CompileNode) (c : Config) :
    (write ns c).cursors = SequentialSharedCursors.positions c := by
  simp only [write,Input.append,putControl,putWords,task_cursors,frames_cursors,
    List.nil_append,SequentialSharedCursors.positions]

theorem write_words (ns : List CompileNode) (c : Config) :
    (write ns c).words = SequentialSharedWordSpace.retainedWords c := by
  simp only [write,Input.append,putControl,putWords,task_words,frames_words,
    List.nil_append,SequentialSharedWordSpace.retainedWords,List.append_assoc]

/-- The whole representation consists of binary clock/control/position
streams and tagged characters. No stream has input-sized alphabet symbols. -/
structure Packed where
  clock : List Bool
  control : List Bool
  cursors : List Bool
  words : List (Option Char)
  deriving Repr

def encode (ns : List CompileNode) (c : Config) : Packed :=
  let streams := write ns c
  ⟨SequentialCursorChain.encodeDeltas [c.clock],
    SequentialCursorChain.encodeDeltas streams.control,
    SequentialCursorChain.encode streams.cursors,
    SequentialSharedWordSpace.encodeWords streams.words⟩

def decode (ns : List CompileNode) (packed : Packed) : Option Config := do
  let clocks ← SequentialCursorChain.decodeDeltas packed.clock
  let clock ← match clocks with
    | [m] => some m
    | _ => none
  let control ← SequentialCursorChain.decodeDeltas packed.control
  let cursors ← SequentialCursorChain.decode packed.cursors
  let words ← SequentialSharedWordSpace.decodeWords packed.words
  match read ns clock ⟨control,cursors,words⟩ with
  | some (c,⟨[],[],[]⟩) => some c
  | _ => none

/-- Exact recovery of every field, not just of ungrouped word/cursor lists. -/
theorem decode_encode {ns : List CompileNode} {c : Config} {n : Nat}
    (h : ConfigOK ns c) (hp : SequentialCursorChain.Chain 0 (SequentialSharedCursors.positions c) n) :
    decode ns (encode ns c) = some c := by
  have hr : read ns c.clock (write ns c) = some (c,Input.empty) := by
    simpa only [Input.append,Input.empty,List.append_nil] using read_write h Input.empty
  simp only [encode,decode,SequentialCursorChain.decodeDeltas_encodeDeltas,
    write_cursors,hp.decode_encode,SequentialSharedWordSpace.decodeWords_encodeWords,
    option_bind_some]
  rw [← write_cursors ns c]
  change (match read ns c.clock (write ns c) with
    | some (c,⟨[],[],[]⟩) => some c
    | _ => none) = some c
  rw [hr]
  rfl

theorem reachable_decode_encode (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    decode (compilerNodes g e) (encode (compilerNodes g e) c) = some c :=
  decode_encode (SequentialSharedPool.reachable_ok g x e c h)
    (SequentialSharedCursors.reachable_chain g x e c h)

theorem encode_injective {ns : List CompileNode} {c d : Config} {n m : Nat}
    (hc : ConfigOK ns c) (hd : ConfigOK ns d)
    (hp : SequentialCursorChain.Chain 0 (SequentialSharedCursors.positions c) n)
    (hq : SequentialCursorChain.Chain 0 (SequentialSharedCursors.positions d) m)
    (he : encode ns c = encode ns d) : c = d := by
  have hh := congrArg (decode ns) he
  simpa only [decode_encode hc hp,decode_encode hd hq,Option.some.injEq] using hh

/-- Semantic execution through the representation. This implementation
materializes decoded states; its workspace is not asserted to be linear. -/
def packedStep (ns : List CompileNode) (g : MGrammar) (x : List Char) (packed : Packed) :
    Option Packed := do
  let c ← decode ns packed
  let next ← step g x c
  pure (encode ns next)

theorem reachable_step_commutes (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    packedStep (compilerNodes g e) g x (encode (compilerNodes g e) c) =
      (step g x c).map (encode (compilerNodes g e)) := by
  simp only [packedStep,reachable_decode_encode g x e c h,option_bind_some]
  cases step g x c <;> rfl

def Packed.length (packed : Packed) : Nat :=
  packed.clock.length + packed.control.length + packed.cursors.length + packed.words.length

theorem encode_length (ns : List CompileNode) (c : Config) :
    (encode ns c).length = c.clock + 1 +
      ((write ns c).control.sum + (write ns c).control.length) +
      (SequentialCursorChain.encode (SequentialSharedCursors.positions c)).length +
      (SequentialSharedWordSpace.encodeWords (SequentialSharedWordSpace.retainedWords c)).length := by
  simp only [Packed.length,encode,SequentialCursorChain.encodeDeltas_length,
    List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,Nat.add_zero,
    write_cursors,write_words]

end Shallot.MacroPeg.CBV.SequentialSharedStateCodec
