import MacroPeg.CBV.SequentialFieldFetch

/-! Tag/header-driven front scanning, without a supplied front length.
`eval` is the field-stream semantics. `compile` is an actual list program;
its control-flow refinement is proved in `SequentialFrontScanMachine`.
-/

namespace Shallot.MacroPeg.CBV.SequentialFrontScan

open Complexity Complexity.BinaryWord SequentialStack SequentialStackCodec CBVtoCBN

inductive Plan where
  | done
  | fail
  | word (next : Plan)
  | branch (zero positive : Plan)
  | many (stride : Nat) (next : Plan)

def eval : Plan → Nat → List Nat → Option (List Nat)
  | .done, _, input => some input
  | .fail, _, _ => none
  | .word _, _, [] => none
  | .word next, _, v :: rest => eval next v rest
  | .branch zero positive, n, input =>
    if n = 0 then eval zero 0 input else eval positive (n - 1) input
  | .many stride next, n, input =>
    if input.length < n * stride then none else
      eval next (SequentialFieldFetch.after n (input.take (n * stride))) (input.drop (n * stride))

def compile : Plan → LProg 11
  | .done => skipP 3
  | .fail => .halt false
  | .word next => .seq SequentialFieldFetch.fetch (compile next)
  | .branch zero positive =>
    .ite 3 nonEmpty (.seq (.pop 3) (compile positive)) (compile zero)
  | .many stride next =>
    .seq (copyLenP 3 10 7)
      (.seq (.loop 10 nonEmpty (.seq (repeatP 3 SequentialFieldFetch.fetch stride) (.pop 10)))
        (compile next))

def skipWords : Nat → Plan → Plan
  | 0, next => next
  | n + 1, next => .word (skipWords n next)

def dispatch : List Plan → Plan
  | [] => .fail
  | p :: ps => .branch p (dispatch ps)

def tagged (ps : List Plan) : Plan := .word (dispatch ps)
def env (next : Plan) : Plan := .word (.many 2 next)
def exprs (next : Plan) : Plan := .word (.many 1 next)
def res (next : Plan) : Plan := tagged [next, next, .word next]
def argsRes (next : Plan) : Plan := tagged [next, next, .word (env next)]
def val (next : Plan) : Plan := tagged [res next, argsRes next]

def task (next : Plan) : Plan := tagged [
  skipWords 3 (env next),
  skipWords 2 (env (exprs next)),
  skipWords 3 (env next),
  val next]

def frame (next : Plan) : Plan := tagged [
  skipWords 2 (env next),
  skipWords 3 (env next),
  .word next,
  skipWords 3 (env next),
  skipWords 2 (env (exprs next)),
  skipWords 2 next,
  skipWords 2 next]

/-- The stack header decides whether there is a top frame. The positive
branch ignores the decremented stack count and scans precisely one frame. -/
def parser : Plan := task (.word (.branch .done (frame .done)))
def parserProgram : LProg 11 := compile parser

theorem dispatch_eq (ps : List Plan) (i : Nat) (p : Plan) (hp : ps[i]? = some p) (input : List Nat) :
    eval (dispatch ps) i input = eval p 0 input := by
  induction ps generalizing i with
  | nil => simp at hp
  | cons q ps ih =>
    cases i with
    | zero => simp at hp; subst p; simp [dispatch, eval]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hp
      simpa [dispatch, eval] using ih i hp

theorem tagged_eq (ps : List Plan) (i : Nat) (p : Plan) (hp : ps[i]? = some p)
    (held : Nat) (input : List Nat) :
    eval (tagged ps) held (i :: input) = eval p 0 input := by
  exact dispatch_eq ps i p hp input

theorem skip_correct (vs : List Nat) (next : Plan) (held : Nat) (tail out : List Nat)
    (hn : ∀ h, eval next h tail = some out) :
    eval (skipWords vs.length next) held (vs ++ tail) = some out := by
  induction vs generalizing held with
  | nil => exact hn held
  | cons v vs ih => simpa [skipWords, eval] using ih v

theorem many_correct (stride n : Nat) (vs : List Nat) (hlen : vs.length = n * stride)
    (next : Plan) (tail out : List Nat) (hn : ∀ h, eval next h tail = some out) :
    eval (.many stride next) n (vs ++ tail) = some out := by
  have hl : ¬ (vs ++ tail).length < n * stride := by simp; omega
  simp only [eval, if_neg hl]
  rw [← hlen, List.take_left, List.drop_left]
  exact hn _

theorem env_correct (E : CaptureEnv) (next : Plan) (held : Nat) (tail out : List Nat)
    (hn : ∀ h, eval next h tail = some out) :
    eval (env next) held (writeEnv E ++ tail) = some out := by
  have hlen : (E.flatMap writePair).length = E.length * 2 := by
    induction E with
    | nil => simp
    | cons p E ih => cases p; simp [writePair, ih, Nat.add_mul]
  exact many_correct 2 E.length _ hlen next tail out hn

theorem exprs_correct (ns : List CompileNode) (es : List MExp) (next : Plan) (held : Nat)
    (tail out : List Nat) (hn : ∀ h, eval next h tail = some out) :
    eval (exprs next) held (writeExprs ns es ++ tail) = some out := by
  have hlen : (es.flatMap (writeExpr ns)).length = es.length * 1 := by
    induction es with
    | nil => simp
    | cons e es ih => simp [writeExpr, ih]
  exact many_correct 1 es.length _ hlen next tail out hn

theorem res_correct (r : Res) (next : Plan) (held : Nat) (tail out : List Nat)
    (hn : ∀ h, eval next h tail = some out) :
    eval (res next) held (writeRes r ++ tail) = some out := by
  cases r with
  | none => simpa [res, tagged, dispatch, eval, writeRes] using hn 0
  | some r =>
    cases r with
    | none => simpa [res, tagged, dispatch, eval, writeRes] using hn 0
    | some p => simpa [res, tagged, dispatch, eval, writeRes] using hn p

theorem argsRes_correct (r : ArgsResult) (next : Plan) (held : Nat) (tail out : List Nat)
    (hn : ∀ h, eval next h tail = some out) :
    eval (argsRes next) held (writeArgsRes r ++ tail) = some out := by
  cases r with
  | none => simpa [argsRes, tagged, dispatch, eval, writeArgsRes] using hn 0
  | some r =>
    cases r with
    | none => simpa [argsRes, tagged, dispatch, eval, writeArgsRes] using hn 0
    | some Wp =>
      obtain ⟨W, p⟩ := Wp
      simpa [argsRes, tagged, dispatch, eval, writeArgsRes, List.append_assoc] using
        env_correct W next p tail out hn

theorem val_correct (v : SequentialStack.Value) (next : Plan) (held : Nat) (tail out : List Nat)
    (hn : ∀ h, eval next h tail = some out) :
    eval (val next) held (writeValue v ++ tail) = some out := by
  cases v with
  | expr r =>
    simpa [val, writeValue, tagged, dispatch, eval] using res_correct r next 0 tail out hn
  | args r =>
    simpa [val, writeValue, tagged, dispatch, eval] using argsRes_correct r next 0 tail out hn

theorem task_correct (ns : List CompileNode) (t : Task) (next : Plan) (held : Nat)
    (tail out : List Nat) (hn : ∀ h, eval next h tail = some out) :
    eval (task next) held (writeTask ns t ++ tail) = some out := by
  cases t with
  | expr m E e p =>
    simpa [task, tagged, dispatch, eval, writeTask, writeExpr, List.append_assoc] using
      skip_correct [m, p, exprId ns e] (env next) 0 (writeEnv E ++ tail) out
        (fun h => env_correct E next h tail out hn)
  | args m E es p =>
    simpa [task, tagged, dispatch, eval, writeTask, List.append_assoc] using
      skip_correct [m, p] (env (exprs next)) 0 (writeEnv E ++ (writeExprs ns es ++ tail)) out
        (fun h => env_correct E (exprs next) h (writeExprs ns es ++ tail) out
          (fun h => exprs_correct ns es next h tail out hn))
  | query m i E p =>
    simpa [task, tagged, dispatch, eval, writeTask, List.append_assoc] using
      skip_correct [m, i, p] (env next) 0 (writeEnv E ++ tail) out
        (fun h => env_correct E next h tail out hn)
  | value v =>
    simpa [task, tagged, dispatch, eval, writeTask] using val_correct v next 0 tail out hn

theorem frame_correct (ns : List CompileNode) (f : SequentialStack.Frame) (next : Plan) (held : Nat)
    (tail out : List Nat) (hn : ∀ h, eval next h tail = some out) :
    eval (frame next) held (writeFrame ns f ++ tail) = some out := by
  cases f with
  | seq m E b =>
    simpa [frame, tagged, dispatch, eval, writeFrame, writeExpr, List.append_assoc] using
      skip_correct [m, exprId ns b] (env next) 0 (writeEnv E ++ tail) out
        (fun h => env_correct E next h tail out hn)
  | alt m E b p =>
    simpa [frame, tagged, dispatch, eval, writeFrame, writeExpr, List.append_assoc] using
      skip_correct [m, p, exprId ns b] (env next) 0 (writeEnv E ++ tail) out
        (fun h => env_correct E next h tail out hn)
  | notP p => simpa [frame, tagged, dispatch, eval, writeFrame] using hn p
  | star m E a p =>
    simpa [frame, tagged, dispatch, eval, writeFrame, writeExpr, List.append_assoc] using
      skip_correct [m, p, exprId ns a] (env next) 0 (writeEnv E ++ tail) out
        (fun h => env_correct E next h tail out hn)
  | argHead m E es p =>
    simpa [frame, tagged, dispatch, eval, writeFrame, List.append_assoc] using
      skip_correct [m, p] (env (exprs next)) 0 (writeEnv E ++ (writeExprs ns es ++ tail)) out
        (fun h => env_correct E (exprs next) h (writeExprs ns es ++ tail) out
          (fun h => exprs_correct ns es next h tail out hn))
  | argCons span =>
    obtain ⟨a, b⟩ := span
    simpa [frame, tagged, dispatch, eval, writeFrame] using skip_correct [a, b] next 0 tail out hn
  | call m i =>
    simpa [frame, tagged, dispatch, eval, writeFrame] using skip_correct [m, i] next 0 tail out hn

/-- The field-stream parser finds the end of precisely the task, global stack
header and optional top frame. It never receives their combined length. -/
theorem parser_correct (ns : List CompileNode) (c : Config) (rest : List Nat) (held : Nat) :
    eval parser held (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c) ++ rest) =
      some rest := by
  obtain ⟨t, K⟩ := c
  cases K with
  | nil =>
    have hh := task_correct ns t (.word (.branch .done (frame .done))) held (0 :: rest) rest
      (fun h => by simp [eval])
    simpa [parser, SequentialFront.prefixCode, SequentialFront.suffixCode,
      SequentialFront.front, SequentialFront.tail, List.append_assoc] using hh
  | cons f K =>
    have hh := task_correct ns t (.word (.branch .done (frame .done))) held
      ((K.length + 1) :: writeFrame ns f ++ rest) rest (fun h => by
        simpa [eval] using frame_correct ns f .done K.length rest rest (fun _ => rfl))
    simpa [parser, SequentialFront.prefixCode, SequentialFront.suffixCode,
      SequentialFront.front, SequentialFront.tail, Nat.add_comm, List.append_assoc] using hh

/-- This boundary is computed from the input stream, not from a `Config`. -/
def splitFront (input : List Nat) : Option (List Nat × List Nat) := do
  let rest ← eval parser 0 input
  pure (input.take (input.length - rest.length), rest)

theorem splitFront_correct (ns : List CompileNode) (c : Config) :
    splitFront (encode ns c) = some
      (SequentialFront.prefixCode ns (SequentialFront.tail c) (SequentialFront.front c),
        SequentialFront.suffixCode ns (SequentialFront.tail c)) := by
  rw [SequentialFront.encode_front]
  simp [splitFront, parser_correct]

end Shallot.MacroPeg.CBV.SequentialFrontScan
