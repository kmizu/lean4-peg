import MacroPeg.CBV.LoadedProgram
import MacroPeg.CBV.MirrorBuild
import MacroPeg.CBV.SpanBuild
import Shallot.Peg.Separation.TokenInput

namespace Shallot.MacroPeg.CBV

open Complexity Shallot.Packrat.Machine Shallot.MacroPeg.Mach Shallot.MacroPeg.KExp

def emptyStacks {K : Nat} : Lists K := fun _ => []

def inputState {K : Nat} (r : EvalRegs K) (x : List Char) : Lists K :=
  ((emptyStacks.set (r.get 0) (inputRow x)).set (r.get 20) [x.length])

def preparedState {K : Nat} (r : EvalRegs K) (x : List Char) : Lists K :=
  (((emptyStacks.set (r.get 0) (mirrorRow x)).set (r.get 20) [x.length]).set
    (r.get 17) (encPairs (spans x.length))).set (r.get 19) [(spans x.length).length]

theorem preparedState_ready {K : Nat} (r : EvalRegs K) (x : List Char) :
    EvalReady r (preparedState r x) x [] [] := by
  constructor
  · simp [preparedState, Lists.set]
  · simp [preparedState, Lists.set, emptyStacks]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [preparedState, Lists.set, emptyStacks]
  · simp [preparedState, Lists.set]
  · simp [preparedState]
  · simp [preparedState, Lists.set]
  · simp [preparedState, Lists.set, emptyStacks]
  · simp [preparedState, Lists.set, emptyStacks]

def spanSlot (i : Fin 6) : Fin 32 :=
  match i.val with
  | 0 => 17
  | 1 => 19
  | 2 => 3
  | 3 => 4
  | 4 => 26
  | _ => 27

def setupSpanRegs {K : Nat} (r : EvalRegs K) : SpanBuildRegs K where
  get i := r.get (spanSlot i)
  inj i j h := (show ∀ a b : Fin 6, spanSlot a = spanSlot b → a = b from by decide) i j (r.inj _ _ h)

def setupP {K : Nat} (r : EvalRegs K) : NProg K :=
  .seq (mirrorBuildP (r.get 0) (r.get 3) (r.get 5) (r.ne (by decide)) (r.ne (by decide)) (r.ne (by decide)))
    (.seq (.prim (.dup (r.get 20) (r.get 26) (r.ne (by decide))))
      (.seq (.prim (.inc (r.get 26))) (spanBuildP (setupSpanRegs r))))

def setupCost (n : Nat) : Nat := 9 * (n + 1) + 6 + spanBuildCost n

/-- The actual setup reverses the input, builds every interval pair, and leaves all evaluator workspaces ready. -/
theorem setup_runs {K : Nat} (r : EvalRegs K) (x : List Char) :
    NRuns (setupP r) (inputState r x) (preparedState r x) (setupCost x.length) := by
  have xm := mirrorBuild_runs (r.get 0) (r.get 3) (r.get 5) (r.ne (by decide)) (r.ne (by decide))
    (r.ne (by decide)) (inputState r x) x
    (by simp [inputState, Lists.set]) (by simp [inputState, Lists.set, emptyStacks])
    (by simp [inputState, Lists.set, emptyStacks])
  let X := (inputState r x).set (r.get 0) (mirrorRow x)
  have xd := nruns_dup (r.get 20) (r.get 26) (r.ne (by decide)) X
    (l := []) (v := x.length) (by simp [X, inputState, Lists.set])
  have hx26 : X (r.get 26) = [] := by simp [X, inputState, Lists.set, emptyStacks]
  rw [hx26, List.nil_append] at xd
  let Y := X.set (r.get 26) [x.length]
  have xi := nruns_inc (r.get 26) Y (l := []) (v := x.length) (by simp [Y])
  let Z := Y.set (r.get 26) [x.length + 1]
  have xs := spanBuild_runs (setupSpanRegs r) Z x.length
    (by change Z (r.get 17) = []; simp [Z, Y, X, inputState, Lists.set, emptyStacks])
    (by change Z (r.get 19) = []; simp [Z, Y, X, inputState, Lists.set, emptyStacks])
    (by change Z (r.get 3) = []; simp [Z, Y, X, inputState, Lists.set, emptyStacks])
    (by change Z (r.get 4) = []; simp [Z, Y, X, inputState, Lists.set, emptyStacks])
    (by change Z (r.get 26) = [x.length + 1]; simp [Z])
    (by change Z (r.get 27) = []; simp [Z, Y, X, inputState, Lists.set, emptyStacks])
  change NRuns _ Z (((Z.set (r.get 17) (encPairs (spans x.length))).set (r.get 19) [(spans x.length).length]).set
    (r.get 26) []) _ at xs
  have he : (((Z.set (r.get 17) (encPairs (spans x.length))).set (r.get 19) [(spans x.length).length]).set
      (r.get 26) []) = preparedState r x := by
    funext z
    by_cases h0 : z = r.get 0
    · subst z; simp [Z, Y, X, inputState, preparedState, Lists.set]
    by_cases h17 : z = r.get 17
    · subst z; simp [Z, Y, X, inputState, preparedState, Lists.set]
    by_cases h19 : z = r.get 19
    · subst z; simp [Z, Y, X, inputState, preparedState, Lists.set]
    by_cases h20 : z = r.get 20
    · subst z; simp [Z, Y, X, inputState, preparedState, Lists.set]
    by_cases h26 : z = r.get 26
    · subst z; simp [Z, Y, X, inputState, preparedState, Lists.set, emptyStacks]
    simp [Z, Y, X, inputState, preparedState, Lists.set, emptyStacks, h0, h17, h19, h20, h26]
  rw [he] at xs
  exact (xm.seq (xd.seq (xi.seq xs))).mono (by unfold setupCost; omega)

theorem setupCost_poly : IsPoly setupCost :=
  isPoly_add (isPoly_add (isPoly_mul (isPoly_const 9) (isPoly_add isPoly_id (isPoly_const 1)))
    (isPoly_const 6)) spanBuildCost_poly

/-- A constant grammar supplies enough registers for the existing verified token loader. -/
def loaderGrammar : Shallot.Grammar := ⟨List.replicate 16 .eps, 0⟩
abbrev machineK : Nat := NK loaderGrammar

def machineRegs : EvalRegs machineK where
  get i := ⟨i.val, by
    have hi := i.isLt
    have hK : 32 ≤ machineK := by decide
    omega⟩
  inj i j h := Fin.ext (congrArg (fun k : Fin machineK => k.val) h)

/-- Free the loader's length register for the evaluator's read scratch, preserving the loaded input. -/
theorem moveLength_runs (w : List Bool) :
    NRuns (nmv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)))
      (Shallot.PegSeparation.tokenLoaded loaderGrammar w)
      (inputState machineRegs (Shallot.PegSeparation.tokenWord w)) 2 := by
  let S := Shallot.PegSeparation.tokenLoaded loaderGrammar w
  have hi0 : inpR loaderGrammar = machineRegs.get 0 := rfl
  have hi1 : lenR loaderGrammar = machineRegs.get 1 := rfl
  have hlen : S (machineRegs.get 1) = [(Shallot.PegSeparation.tokenWord w).length] := by
    simp [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1, Lists.set]
  have xm := nruns_mv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)) S
    (l := []) (v := (Shallot.PegSeparation.tokenWord w).length) hlen
  have h20 : S (machineRegs.get 20) = [] := by
    simp only [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1]
    rw [Lists.set_ne _ _ (machineRegs.ne (by decide)), Lists.set_ne _ _ (machineRegs.ne (by decide))]
    change (if 20 = 0 then _ else []) = []
    rfl
  rw [h20, List.nil_append] at xm
  have he : (S.set (machineRegs.get 20) [(Shallot.PegSeparation.tokenWord w).length]).set (machineRegs.get 1) [] =
      inputState machineRegs (Shallot.PegSeparation.tokenWord w) := by
    funext z
    by_cases h0 : z = machineRegs.get 0
    · subst z
      simp [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1, inputState, Lists.set]
    by_cases h1 : z = machineRegs.get 1
    · subst z
      simp [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1, inputState, Lists.set, emptyStacks]
    by_cases h20 : z = machineRegs.get 20
    · subst z
      simp [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1, inputState, Lists.set]
    have hz0 : z.val ≠ 0 := fun hz => h0 (Fin.ext hz)
    simp [S, Shallot.PegSeparation.tokenLoaded, hi0, hi1, inputState, Lists.set,
      h0, h1, h20, emptyStacks, nInit, hz0]
  rw [he] at xm
  exact xm

def inputProgram (g : MGrammar) (s : Strategy) (e : MExp) : NProg machineK :=
  .seq (Shallot.PegSeparation.loadTokens loaderGrammar)
    (.seq (nmv (machineRegs.get 1) (machineRegs.get 20) (machineRegs.ne (by decide)))
      (.seq (setupP machineRegs) (loadedProgram machineRegs g s e)))

/-- Complete execution starts at the actual encoded bit input, including token decoding and dictionary construction. -/
theorem inputProgram_halts (g : MGrammar) (s : Strategy) (e : MExp) (w : List Bool) :
    ∃ b S', NHalts (inputProgram g s e) (nInit machineK w) b S'
      (220 * (w.length + 1) + 2 + setupCost (Shallot.PegSeparation.tokenWord w).length +
        loadedCost g e (Shallot.PegSeparation.tokenWord w).length) ∧
      (b = true ↔ numericDecide s g (Shallot.PegSeparation.tokenWord w) e = some (some 0)) := by
  have xl := Shallot.PegSeparation.nruns_loadTokens loaderGrammar w
  have xm := moveLength_runs w
  have xs := setup_runs machineRegs (Shallot.PegSeparation.tokenWord w)
  obtain ⟨b, S', hf, hb⟩ := loadedProgram_halts machineRegs g s e (Shallot.PegSeparation.tokenWord w)
    (preparedState machineRegs _) (preparedState_ready machineRegs _)
    (by simp [preparedState, Lists.set, emptyStacks])
  exact ⟨b, S', (xl.seqH (xm.seqH (xs.seqH hf))).mono (by omega), hb⟩

end Shallot.MacroPeg.CBV
