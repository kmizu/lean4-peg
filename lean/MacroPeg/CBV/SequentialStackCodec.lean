import MacroPeg.CBV.SequentialStackPool

namespace Shallot.MacroPeg.CBV.SequentialStackCodec

open SequentialStack SequentialStackPool CBVtoCBN

abbrev Reader (α : Type) := List Nat → Option (α × List Nat)

def readMany {α : Type} (reader : Reader α) : Nat → Reader (List α)
  | 0, rest => some ([], rest)
  | n + 1, input => do
    let (a, rest) ← reader input
    let (as, rest) ← readMany reader n rest
    pure (a :: as, rest)

def writeList {α : Type} (writer : α → List Nat) (as : List α) : List Nat :=
  as.length :: as.flatMap writer

def readList {α : Type} (reader : Reader α) : Reader (List α)
  | [] => none
  | n :: input => readMany reader n input

theorem readMany_write {α : Type} (reader : Reader α) (writer : α → List Nat) :
    ∀ as : List α, (∀ a ∈ as, ∀ tail, reader (writer a ++ tail) = some (a, tail)) →
      ∀ tail, readMany reader as.length (as.flatMap writer ++ tail) = some (as, tail)
  | [], _, _ => rfl
  | a :: as, h, tail => by
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany]
    rw [h a (by simp) (as.flatMap writer ++ tail)]
    change (readMany reader as.length (as.flatMap writer ++ tail)).bind
      (fun pair => some (a :: pair.1, pair.2)) = some (a :: as, tail)
    rw [readMany_write reader writer as (fun b hb => h b (by simp [hb])) tail]
    rfl

theorem readList_write {α : Type} (reader : Reader α) (writer : α → List Nat) (as : List α)
    (h : ∀ a ∈ as, ∀ tail, reader (writer a ++ tail) = some (a, tail)) (tail : List Nat) :
    readList reader (writeList writer as ++ tail) = some (as, tail) :=
  readMany_write reader writer as h tail

def writePair (span : Nat × Nat) : List Nat := [span.1, span.2]
def readPair : Reader (Nat × Nat)
  | a :: b :: rest => some ((a, b), rest)
  | _ => none

def writeEnv (E : CaptureEnv) : List Nat := writeList writePair E
def readEnv : Reader CaptureEnv := readList readPair

theorem readEnv_write (E : CaptureEnv) (tail : List Nat) :
    readEnv (writeEnv E ++ tail) = some (E, tail) :=
  readList_write readPair writePair E (fun _ _ _ => rfl) tail

def exprId (ns : List CompileNode) (e : MExp) : Nat := (exprPool ns).idxOf e
def writeExpr (ns : List CompileNode) (e : MExp) : List Nat := [exprId ns e]
def readExpr (ns : List CompileNode) : Reader MExp
  | [] => none
  | i :: rest => do
    let e ← (exprPool ns)[i]?
    pure (e, rest)

theorem readExpr_write {ns e} (h : ExprOK ns e) (tail : List Nat) :
    readExpr ns (writeExpr ns e ++ tail) = some (e, tail) := by
  simp only [writeExpr, List.singleton_append, readExpr, exprId, get_idxOf h.mem]
  rfl

def writeExprs (ns : List CompileNode) (es : List MExp) : List Nat := writeList (writeExpr ns) es
def readExprs (ns : List CompileNode) : Reader (List MExp) := readList (readExpr ns)

theorem readExprs_write {ns es} (h : ArgsOK ns es) (tail : List Nat) :
    readExprs ns (writeExprs ns es ++ tail) = some (es, tail) := by
  apply readList_write
  intro e he rest
  simp only [writeExpr, List.singleton_append, readExpr, exprId, get_idxOf (h.mem e he)]
  rfl

def writeRes : Res → List Nat
  | none => [0]
  | some none => [1]
  | some (some p) => [2, p]

def readRes : Reader Res
  | 0 :: rest => some (none, rest)
  | 1 :: rest => some (some none, rest)
  | 2 :: p :: rest => some (some (some p), rest)
  | _ => none

theorem readRes_write (r : Res) (tail : List Nat) : readRes (writeRes r ++ tail) = some (r, tail) := by
  cases r with
  | none => rfl
  | some r => cases r <;> rfl

def writeArgsRes : ArgsResult → List Nat
  | none => [0]
  | some none => [1]
  | some (some (W, p)) => [2, p] ++ writeEnv W

def readArgsRes : Reader ArgsResult
  | 0 :: rest => some (none, rest)
  | 1 :: rest => some (some none, rest)
  | 2 :: p :: rest => do
    let (W, rest) ← readEnv rest
    pure (some (some (W, p)), rest)
  | _ => none

theorem readArgsRes_write (r : ArgsResult) (tail : List Nat) :
    readArgsRes (writeArgsRes r ++ tail) = some (r, tail) := by
  cases r with
  | none => rfl
  | some r =>
    cases r with
    | none => rfl
    | some Wp =>
      obtain ⟨W, p⟩ := Wp
      simp [writeArgsRes, readArgsRes, readEnv_write]

def writeValue : SequentialStack.Value → List Nat
  | .expr r => 0 :: writeRes r
  | .args r => 1 :: writeArgsRes r

def readValue : Reader SequentialStack.Value
  | 0 :: rest => do
    let (r, rest) ← readRes rest
    pure (.expr r, rest)
  | 1 :: rest => do
    let (r, rest) ← readArgsRes rest
    pure (.args r, rest)
  | _ => none

theorem readValue_write (v : SequentialStack.Value) (tail : List Nat) :
    readValue (writeValue v ++ tail) = some (v, tail) := by
  cases v <;> simp [writeValue, readValue, readRes_write, readArgsRes_write]

def writeTask (ns : List CompileNode) : Task → List Nat
  | .expr m E e p => [0, m, p] ++ writeExpr ns e ++ writeEnv E
  | .args m E es p => [1, m, p] ++ writeEnv E ++ writeExprs ns es
  | .query m i E p => [2, m, i, p] ++ writeEnv E
  | .value v => 3 :: writeValue v

def readTask (ns : List CompileNode) : Reader Task
  | 0 :: m :: p :: rest => do
    let (e, rest) ← readExpr ns rest
    let (E, rest) ← readEnv rest
    pure (.expr m E e p, rest)
  | 1 :: m :: p :: rest => do
    let (E, rest) ← readEnv rest
    let (es, rest) ← readExprs ns rest
    pure (.args m E es p, rest)
  | 2 :: m :: i :: p :: rest => do
    let (E, rest) ← readEnv rest
    pure (.query m i E p, rest)
  | 3 :: rest => do
    let (v, rest) ← readValue rest
    pure (.value v, rest)
  | _ => none

theorem readTask_write {ns task} (h : TaskOK ns task) (tail : List Nat) :
    readTask ns (writeTask ns task ++ tail) = some (task, tail) := by
  cases task with
  | expr m E e p =>
    simp [writeTask, List.append_assoc, readTask, readExpr_write h, readEnv_write]
  | args m E es p =>
    simp [writeTask, List.append_assoc, readTask, readExprs_write h, readEnv_write]
  | query m i E p => simp [writeTask, readTask, readEnv_write]
  | value v => simp [writeTask, readTask, readValue_write]

def writeFrame (ns : List CompileNode) : Frame → List Nat
  | .seq m E b => [0, m] ++ writeExpr ns b ++ writeEnv E
  | .alt m E b p => [1, m, p] ++ writeExpr ns b ++ writeEnv E
  | .notP p => [2, p]
  | .star m E a p => [3, m, p] ++ writeExpr ns a ++ writeEnv E
  | .argHead m E es p => [4, m, p] ++ writeEnv E ++ writeExprs ns es
  | .argCons (a, b) => [5, a, b]
  | .call m i => [6, m, i]

def readFrame (ns : List CompileNode) : Reader Frame
  | 0 :: m :: rest => do
    let (b, rest) ← readExpr ns rest
    let (E, rest) ← readEnv rest
    pure (.seq m E b, rest)
  | 1 :: m :: p :: rest => do
    let (b, rest) ← readExpr ns rest
    let (E, rest) ← readEnv rest
    pure (.alt m E b p, rest)
  | 2 :: p :: rest => some (.notP p, rest)
  | 3 :: m :: p :: rest => do
    let (a, rest) ← readExpr ns rest
    let (E, rest) ← readEnv rest
    pure (.star m E a p, rest)
  | 4 :: m :: p :: rest => do
    let (E, rest) ← readEnv rest
    let (es, rest) ← readExprs ns rest
    pure (.argHead m E es p, rest)
  | 5 :: a :: b :: rest => some (.argCons (a, b), rest)
  | 6 :: m :: i :: rest => some (.call m i, rest)
  | _ => none

theorem readFrame_write {ns f} (h : FrameOK ns f) (tail : List Nat) :
    readFrame ns (writeFrame ns f ++ tail) = some (f, tail) := by
  cases f with
  | seq m E b => simp [writeFrame, List.append_assoc, readFrame, readExpr_write h, readEnv_write]
  | alt m E b p => simp [writeFrame, List.append_assoc, readFrame, readExpr_write h, readEnv_write]
  | notP p => rfl
  | star m E a p => simp [writeFrame, List.append_assoc, readFrame, readExpr_write h.star, readEnv_write]
  | argHead m E es p => simp [writeFrame, List.append_assoc, readFrame, readExprs_write h, readEnv_write]
  | argCons span => cases span; rfl
  | call m i => rfl

def encode (ns : List CompileNode) (c : Config) : List Nat :=
  writeTask ns c.task ++ writeList (writeFrame ns) c.stack

def readConfig (ns : List CompileNode) (input : List Nat) : Option (Config × List Nat) := do
  let (task, rest) ← readTask ns input
  let (K, rest) ← readList (readFrame ns) rest
  pure (⟨task, K⟩, rest)

def decode (ns : List CompileNode) (input : List Nat) : Option Config := do
  let (c, rest) ← readConfig ns input
  if rest.isEmpty then some c else none

theorem readConfig_encode {ns c} (h : ConfigOK ns c) (tail : List Nat) :
    readConfig ns (encode ns c ++ tail) = some (c, tail) := by
  obtain ⟨task, K⟩ := c
  have hframes : ∀ rest, readList (readFrame ns) (writeList (writeFrame ns) K ++ rest) = some (K, rest) :=
    fun rest => readList_write _ _ K (fun f hf tail => readFrame_write (h.2 f hf) tail) rest
  simp [encode, List.append_assoc, readConfig, readTask_write h.1, hframes]

theorem decode_encode {ns c} (h : ConfigOK ns c) : decode ns (encode ns c) = some c := by
  have hh := readConfig_encode h []
  simp only [List.append_nil] at hh
  simp [decode, hh]

/-- The fixed pool is determined by the source program. Every actual
intermediate configuration survives encoding and decoding unchanged. -/
theorem reachable_roundtrip (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    decode (compilerNodes g e) (encode (compilerNodes g e) c) = some c :=
  decode_encode (reachable_ok g x e c h)

theorem encode_injective {ns a b} (ha : ConfigOK ns a) (hb : ConfigOK ns b)
    (he : encode ns a = encode ns b) : a = b := by
  have hdec := congrArg (decode ns) he
  rw [decode_encode ha, decode_encode hb] at hdec
  exact Option.some.inj hdec

end Shallot.MacroPeg.CBV.SequentialStackCodec
