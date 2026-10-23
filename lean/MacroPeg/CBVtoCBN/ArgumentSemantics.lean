import MacroPeg.CBVtoCBN.CompiledLookup

namespace Shallot.MacroPeg.CBVtoCBN

def stageArgs (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q : Nat) : List MExp :=
  evalArgs x ds E p q ++ envArgs x.length C

def stageRest (x : List Char) (ds : List Nat) (E C : CapturedEnv) (q : Nat) : List MExp :=
  skipN q :: skipN (x.length - q) :: (evalRest x ds E ++ envArgs x.length C)

theorem stageArgs_length (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q : Nat) :
    (stageArgs x ds E C p q).length = 5 + 2 * ds.length + 4 * E.length + 4 * C.length := by
  simp only [stageArgs, List.length_append, evalArgs_length, envArgs_length]

theorem stageRest_length (x : List Char) (ds : List Nat) (E C : CapturedEnv) (q : Nat) :
    (stageRest x ds E C q).length = 3 + 2 * ds.length + 4 * E.length + 4 * C.length := by
  simp only [stageRest, List.length_cons, List.length_append, evalRest_length, envArgs_length]
  omega

theorem stageArgs_split (x : List Char) (ds : List Nat) (E C : CapturedEnv) (p q : Nat) :
    stageArgs x ds E C p q = skipN p :: skipN (x.length - p) :: stageRest x ds E C q := rfl

theorem ValidEnv.append_capture {n : Nat} {C : CapturedEnv} (hv : ValidEnv n C) {p j : Nat}
    (hp : p ≤ n) (hj : j ≤ p) : ValidEnv n (C ++ [(p, j)]) := by
  intro span hspan
  rcases List.mem_append.mp hspan with hm | hm
  · exact hv span hm
  · have he := List.mem_singleton.mp hm
    subst span
    exact ⟨hj, hp⟩

/-- Source continuation after the captured prefix, expressed directly by its literal values. -/
def argumentValue (c : CompilerConfig) (x : List Char) (ds : List Nat) (E : CapturedEnv)
    (prefixValues : List (List Char)) (callee : Nat) (remaining : List MExp) (p : Nat) : Res :=
  let T := tblV c.source x c.strategy (clockValue x.length ds)
  if c.strategy = .callByValueSeq then
    finishSeq (fun W q => valAt (T callee (prefixValues ++ W)) q)
      (evSeqArgs c.source x c.strategy T (decodeEnv x E) remaining p)
  else
    finishPar (fun W => valAt (T callee (prefixValues ++ W)) p)
      (evParArgs c.source x c.strategy T (decodeEnv x E) remaining p)

theorem argumentValue_capture (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (remaining : List MExp) (p j next : Nat) :
    argumentValue c x ds E (decodeEnv x C ++ [pre x p j]) callee remaining next =
      argumentResult c x ds E (C ++ [(p, j)]) callee remaining next := by
  simp [argumentValue, argumentResult, decodeEnv, List.map_append]

theorem argumentResult_cons (c : CompilerConfig) (x : List Char) (ds : List Nat) (E C : CapturedEnv)
    (callee : Nat) (a : MExp) (remaining : List MExp) (p : Nat) :
    argumentResult c x ds E C callee (a :: remaining) p =
      seqResult (evV c.source x c.strategy (tblV c.source x c.strategy (clockValue x.length ds)) (decodeEnv x E) a p)
        (fun j => argumentValue c x ds E (decodeEnv x C ++ [pre x p j]) callee remaining
          (if c.strategy == .callByValueSeq then j else p)) := by
  unfold argumentResult
  dsimp only
  by_cases hs : c.strategy = .callByValueSeq
  · rw [if_pos hs, finishSeq_cons]
    simp [argumentValue, hs, List.append_assoc]
  · rw [if_neg hs, finishPar_cons]
    simp [argumentValue, hs, List.append_assoc]

theorem drop_argument {actuals : List MExp} {stage : Nat} {a : MExp} (ha : actuals[stage]? = some a) :
    actuals.drop stage = a :: actuals.drop (stage + 1) := by
  rw [List.drop_eq_getElem?_toList_append, ha]
  rfl

/-- The capture fragment only needs a valid continuation when the argument actually succeeded. -/
theorem RulesAt.capture_test {g : MGrammar} {entry argument next : Nat} (thread : Bool) (rest : List MExp)
    (h : RulesAt g entry (captureBlock entry argument next thread rest.length))
    (x : List Char) (p : Nat) (v : Option Nat) (a : Res) (F : List Char → Nat → Res)
    (hl : ∀ j, j ≤ x.length → RootTest g
      (.call argument (skipN p :: skipN (x.length - p) :: skipN j :: skipN (x.length - j) :: rest)) x (a = some (some j)))
    (hn : ∀ j, j ≤ x.length → a = some (some j) → RootTest g
      (.call next (captureNextArgs thread (skipN j) (skipN (x.length - j)) (skipN p) (skipN (x.length - p)) rest)) x
      (F (pre x p j) (if thread then j else p) = some v)) :
    RootTest g (.call entry (.eps :: skipN p :: skipN (x.length - p) :: rest)) x
      (∃ j, j ≤ x.length ∧ a = some (some j) ∧ F (pre x p j) (if thread then j else p) = some v) := by
  obtain ⟨preRules, tail, hpre, hg⟩ := h.split (by simp [captureBlock, pairSearchBlock])
  have ht := captureBlock_test preRules tail argument next thread rest x p v a F
    (by simpa only [hpre, ← hg] using hl) (by simpa only [hpre, ← hg] using hn)
  simpa only [hpre, ← hg] using ht

end Shallot.MacroPeg.CBVtoCBN
