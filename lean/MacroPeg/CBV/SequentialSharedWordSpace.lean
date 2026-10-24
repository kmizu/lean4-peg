import MacroPeg.CBV.SequentialSharedWords

/-! All-state payload bounds for the actual word machine. No origin pairs
are retained in capture environments or pending argument values. The final
codec stores word characters and delimiters; it is not a full state codec. -/
namespace Shallot.MacroPeg.CBV.SequentialSharedWordSpace
open SequentialSharedWords

def taskWords : Task → CaptureEnv
  | .query _ W _ => W
  | .value (.args (some (some (W,_)))) => W
  | _ => []

def frameWords : Frame → CaptureEnv
  | .argCons word => [word]
  | .scope E => E
  | _ => []

def retainedWords (c : Config) : CaptureEnv :=
  taskWords c.task ++ c.env ++ c.stack.flatMap frameWords

theorem decode_task_words (x : List Char) (t : SequentialSharedClock.Task) :
    taskWords (decodeTask x t) =
      SequentialSpanRecompute.decodeEnv x (SequentialSharedClock.taskCaptures t) := by
  cases t with
  | expr _ _ | args _ _ | query _ _ _ => rfl
  | value v =>
    cases v with
    | expr _ => rfl
    | args r => cases r with
      | none => rfl
      | some result => cases result <;> rfl

theorem decode_frame_words (x : List Char) (f : SequentialSharedClock.Frame) :
    frameWords (decodeFrame x f) =
      SequentialSpanRecompute.decodeEnv x (SequentialSharedClock.frameCaptures f) := by
  cases f <;> rfl

theorem decode_stack_words (x : List Char) (K : List SequentialSharedClock.Frame) :
    (K.map (decodeFrame x)).flatMap frameWords =
      SequentialSpanRecompute.decodeEnv x (K.flatMap SequentialSharedClock.frameCaptures) := by
  induction K with
  | nil => rfl
  | cons f K ih =>
    simp only [List.map_cons,List.flatMap_cons,decode_frame_words,ih,
      SequentialSpanRecompute.decodeEnv,List.map_append]

/-- Equality counts every retained copy, not just the current environment. -/
theorem decode_retained_words (x : List Char) (c : SequentialSharedClock.Config) :
    retainedWords (decode x c) =
      SequentialSpanRecompute.decodeEnv x (SequentialSharedClock.retainedCaptures c) := by
  simp only [retainedWords,decode,decode_task_words,decode_stack_words,
    SequentialSharedClock.retainedCaptures,SequentialSpanRecompute.decodeEnv,List.map_append]

theorem reachable_word_characters (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    ((retainedWords c).map List.length).sum ≤ x.length := by
  obtain ⟨d,hd,rfl⟩ := runs_lift g x e c h
  rw [decode_retained_words]
  exact SequentialSharedClock.reachable_captured_characters g x e d hd

theorem reachable_word_records (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (retainedWords c).length ≤ (c.stack.length + 2) * SequentialStackPayload.arityBudget g := by
  obtain ⟨d,hd,rfl⟩ := runs_lift g x e c h
  rw [decode_retained_words]
  simpa only [SequentialSpanRecompute.decodeEnv,List.length_map,decode] using
    SequentialSharedPayload.reachable_capture_records g x e d hd

theorem stack_linear_bound (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    c.stack.length ≤ ((g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1)) *
      (x.length + 1) + sizeOf e := by
  obtain ⟨d,hd,rfl⟩ := runs_lift g x e c h
  simpa only [decode,List.length_map] using SequentialSharedRank.stack_linear_bound g x e d hd

/-- Characters are tagged `some`; `none` terminates each word, including an
empty word. This alphabet has no input-dependent symbols. -/
def encodeWords : CaptureEnv → List (Option Char)
  | [] => []
  | w :: W => w.map some ++ none :: encodeWords W

/-- Decode from right to left. An unterminated final word is rejected. -/
def decodeWords : List (Option Char) → Option CaptureEnv
  | [] => some []
  | none :: tail => (decodeWords tail).map ([] :: ·)
  | some c :: tail =>
    match decodeWords tail with
    | some (w :: W) => some ((c :: w) :: W)
    | _ => none

theorem decodeWords_word (w : List Char) (tail : List (Option Char)) :
    decodeWords (w.map some ++ none :: tail) = (decodeWords tail).map (w :: ·) := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons,List.cons_append,decodeWords,ih]
    cases decodeWords tail <;> rfl

theorem decodeWords_encodeWords (W : CaptureEnv) : decodeWords (encodeWords W) = some W := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    simp only [encodeWords,decodeWords_word,ih,Option.map_some]

theorem encodeWords_injective : Function.Injective encodeWords := by
  intro W V he
  have hh := congrArg decodeWords he
  simpa only [decodeWords_encodeWords,Option.some.injEq] using hh

theorem encodeWords_length (W : CaptureEnv) :
    (encodeWords W).length = (W.map List.length).sum + W.length := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    simp only [encodeWords,List.length_append,List.length_map,List.length_cons,
      List.map_cons,List.sum_cons,ih]
    omega

/-- The encoded character payload and all empty-word delimiters are linear.
Saved input cursors, syntax references, and environment grouping are separate
state data; this theorem does not claim a complete machine-space bound. -/
theorem reachable_capture_stream (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encodeWords (retainedWords c)).length ≤ x.length +
      (c.stack.length + 2) * SequentialStackPayload.arityBudget g := by
  rw [encodeWords_length]
  exact Nat.add_le_add (reachable_word_characters g x e c h) (reachable_word_records g x e c h)

theorem capture_stream_linear (g : MGrammar) (x : List Char) (e : MExp) (c : Config)
    (h : Runs g x (initial g x e) c) :
    (encodeWords (retainedWords c)).length ≤ x.length +
      ((((g.rules.length + 1) * (SequentialStackRank.codeBudget g + 1)) *
        (x.length + 1) + sizeOf e) + 2) * SequentialStackPayload.arityBudget g := by
  exact Nat.le_trans (reachable_capture_stream g x e c h)
    (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (Nat.add_le_add_right (stack_linear_bound g x e c h) 2)) _)

end Shallot.MacroPeg.CBV.SequentialSharedWordSpace
