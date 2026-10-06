import MacroPeg.HigherOrder.Mach.MainTables
import MacroPeg.HigherOrder.Mach.RowsTable
import MacroPeg.HigherOrder.Mach.ValEnvTable
import MacroPeg.HigherOrder.Mach.MainItems
import MacroPeg.HigherOrder.Mach.EvalLoop

/-!
# The second stage, second part: the value tables and the evaluation

From the stacks after the order check (`ordSt`): the rows, the value lengths and the environment counts of the small
types, then the stacks of the reading that the evaluation reuses are emptied, and the evaluation runs with the
program of every item. It halts with the answer of the tables (`evalStage_halts`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- Empty the stacks of the reading that the evaluation reuses. -/
def clearP : NProg NK :=
  .seq (nclr TY) (.seq (nclr OUT) (.seq (nclr CUR) (.seq (nclr NTT) (.seq (nclr NCT) (.seq (nclr NLT) (nclr NRT))))))

/-- The tables of the small types, the clearing and the evaluation. -/
def evalStageP (j : Nat) : NProg NK :=
  .seq (rowsTableP j) (.seq valTableP (.seq envTableP (.seq clearP (evalP itemFullP))))

/-- The steps of the clearing. -/
def clearCost (st : PSt) : Nat :=
  (2 * st.ty.length + 1) + (2 * (encItems st.out.reverse).length + 1) + 3 + 3 + 3 + 3 + 3

def evalStageCost (j cap : Nat) (st : PSt) : Nat :=
  rowsCost j cap st.x.length st.tt + valCost j cap st.x.length st.tt + envCostL j cap st.x.length st.tt st.ct +
    clearCost st + evalCost j cap st

section Stage

variable (j cap : Nat) (st : PSt)

/-- The stacks after the tables. -/
def tabSt : Lists NK :=
  (((((ordSt st cap).set CNT (cntTable j cap st.x.length st.tt)).set ROWS (rowsFlat j cap st.x.length st.tt)).set ROFF
    (roffTable j cap st.x.length st.tt)).set VALT (valTable j cap st.x.length st.tt)).set ENVT
    (envTable j cap st.x.length st.tt st.ct)

/-- The stacks when the evaluation starts. -/
def evSt : Lists NK :=
  (((((((tabSt j cap st).set TY []).set OUT []).set CUR []).set NTT []).set NCT []).set NLT []).set NRT []

end Stage

/-- Read one stack of a chain of updates of the reading stacks. -/
macro "me_get" : tactic =>
  `(tactic| (simp (config := { decide := true }) [evSt, tabSt, ordSt, baseSt, Lists.set, enc, encList]) <;> rfl)

section Run

variable (j cap : Nat) {st : PSt} {R : List HO.Ty} {bis : List (List Flat.Item)} {is : List Flat.Item}
  {x : List Char}

theorem ordSt_scratch : ScratchEmpty (ordSt st cap) :=
  scratch_set (scratch_set (scratch_set (baseSt_scratch st cap) ORD (by decide) _) SZ (by decide) _) NX
    (by decide) _

theorem evSt_scratch : ScratchEmpty (evSt j cap st) := by
  have h₀ := ordSt_scratch cap (st := st)
  unfold evSt tabSt
  repeat (first | exact h₀ | apply scratch_set _ _ (by decide))

theorem evSt_env : EvalEnv (evSt j cap st) j cap st [] where
  ct := by me_get
  lt := by me_get
  rt := by me_get
  xs := by me_get
  nx := by me_get
  ord := by me_get
  sz := by me_get
  cnt := by me_get
  rows := by me_get
  roff := by me_get
  valt := by me_get
  envt := by me_get
  rv := by me_get
  rvl := by me_get
  cap := by me_get
  scratch := evSt_scratch j cap

/-- The clearing empties the reading stacks that the evaluation reuses. -/
theorem clearP_runs : NRuns clearP (tabSt j cap st) (evSt j cap st) (clearCost st) := by
  let T₀ := tabSt j cap st
  have c₁ := nruns_clr TY T₀
  have e₁ : T₀ TY = st.ty.reverse := by simp only [T₀]; me_get
  let T₁ := T₀.set TY []
  have c₂ := nruns_clr OUT T₁
  have e₂ : T₁ OUT = encItems st.out.reverse := by simp only [T₁, T₀]; me_get
  let T₂ := T₁.set OUT []
  have c₃ := nruns_clr CUR T₂
  have e₃ : T₂ CUR = [st.cur] := by simp only [T₂, T₁, T₀]; me_get
  let T₃ := T₂.set CUR []
  have c₄ := nruns_clr NTT T₃
  have e₄ : T₃ NTT = [st.tt.length] := by simp only [T₃, T₂, T₁, T₀]; me_get
  let T₄ := T₃.set NTT []
  have c₅ := nruns_clr NCT T₄
  have e₅ : T₄ NCT = [st.ct.length] := by simp only [T₄, T₃, T₂, T₁, T₀]; me_get
  let T₅ := T₄.set NCT []
  have c₆ := nruns_clr NLT T₅
  have e₆ : T₅ NLT = [st.lt.length] := by simp only [T₅, T₄, T₃, T₂, T₁, T₀]; me_get
  let T₆ := T₅.set NLT []
  have c₇ := nruns_clr NRT T₆
  have e₇ : T₆ NRT = [st.rt.length] := by simp only [T₆, T₅, T₄, T₃, T₂, T₁, T₀]; me_get
  rw [e₁] at c₁; rw [e₂] at c₂; rw [e₃] at c₃; rw [e₄] at c₄; rw [e₅] at c₅; rw [e₆] at c₆; rw [e₇] at c₇
  refine (c₁.seq (c₂.seq (c₃.seq (c₄.seq (c₅.seq (c₆.seq c₇)))))).mono ?_
  simp only [clearCost, List.length_reverse, List.length_singleton]
  omega

/-- **The second part of the second stage halts with the answer of the tables.** -/
theorem evalStage_halts (hi : MInv st) (hr : ReadOK st R bis is x) :
    ∃ S', NHalts (evalStageP j) (ordSt st cap)
      (startCodeT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.rt st.bodies st.start == 2) S'
      (evalStageCost j cap st) := by
  have hs₀ := ordSt_scratch cap (st := st)
  -- the rows tables
  have x₁ := rowsTableP_runs j (ordSt st cap) (cap := cap) (N := st.x.length) hi.tt (by me_get) (by me_get)
    (by me_get) (by me_get) (by me_get) (by me_get) (by me_get) (by me_get) (by me_get) hs₀
  -- the value lengths
  let S₁ := (((ordSt st cap).set CNT (cntTable j cap st.x.length st.tt)).set ROWS
    (rowsFlat j cap st.x.length st.tt)).set ROFF (roffTable j cap st.x.length st.tt)
  have hs₁ : ScratchEmpty S₁ :=
    scratch_set (scratch_set (scratch_set hs₀ CNT (by decide) _) ROWS (by decide) _) ROFF (by decide) _
  have x₂ := valTableP_runs j cap st.x.length S₁ hi.tt (by simp [S₁]; me_get) (by simp [S₁]; me_get)
    (by simp [S₁]; me_get) (by simp [S₁]; me_get) (by simp [S₁]; me_get) hs₁
  -- the environment counts
  let S₂ := S₁.set VALT (valTable j cap st.x.length st.tt)
  have hs₂ : ScratchEmpty S₂ := scratch_set hs₁ VALT (by decide) _
  have x₃ := envTableP_runsL j cap st.x.length S₂ hi.ct (by simp [S₂, S₁]; me_get) (by simp [S₂, S₁]; me_get)
    (by simp [S₂, S₁]; me_get)
    (by (simp (config := { decide := true }) [S₂, S₁, ordSt, baseSt, Lists.set, enc, encList, hr.ctl]) <;> rfl) hs₂
  -- the clearing and the evaluation
  have x₄ := clearP_runs j cap (st := st)
  have htag : ∀ it ∈ st.bodies.flatten, it.tag < 13 := fun it h =>
    Nat.lt_succ_of_le (read_tags hr it (List.mem_append_left _ h)).1
  obtain ⟨S', x₅⟩ := evalP_runs itemFullP j cap st (itemFull_runs j cap hi hr) htag (evSt j cap st)
    (evSt_env j cap) (by me_get) (by me_get) (by me_get) (by me_get) (by me_get) (by me_get) (by me_get)
    (by me_get)
  exact ⟨S', (x₁.seqH (x₂.seqH (x₃.seqH (x₄.seqH x₅)))).mono (by unfold evalStageCost; omega)⟩

end Run

end Shallot.MacroPeg.Mach
