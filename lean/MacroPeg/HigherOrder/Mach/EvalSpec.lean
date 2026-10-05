import MacroPeg.HigherOrder.Mach.EvalStacks

/-!
# The evaluation stack on stacks

The evaluator's stack of packed vectors `st` (head on top) is kept on two stacks: `EV` holds the vectors one after
another, the top vector last (`evFlat`); `EVL` holds their lengths (`evLens`). The item being evaluated is on `IT`
as `[tag, a, b, ctx]` (`encItem`). The rule values (a list `Tf`, one value per rule) are on `RV` one after another.

`EvalEnv` collects what the item programs may rely on: the tables of the evaluation stage and of the reading.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-- The item being evaluated. -/
abbrev IT : Fin NK := 14

def evFlat (st : List (List Nat)) : List Nat := st.reverse.flatten
def evLens (st : List (List Nat)) : List Nat := st.reverse.map List.length

theorem evFlat_cons (v : List Nat) (st : List (List Nat)) : evFlat (v :: st) = evFlat st ++ v := by
  simp [evFlat]

theorem evLens_cons (v : List Nat) (st : List (List Nat)) : evLens (v :: st) = evLens st ++ [v.length] := by
  simp [evLens]

/-- The tables the item programs read, for the final reading state `st` (the string `xs`, codes), order bound `j`
and cap `cap`, with the rule values `Tf`. -/
structure EvalEnv (S : Lists NK) (j cap : Nat) (st : PSt) (Tf : List (List Nat)) : Prop where
  ct : S CTs = encPairs st.ct
  lt : S LTs = encLits st.lt
  rt : S RTs = st.rt
  xs : S XS = st.x
  nx : S NX = [st.x.length]
  ord : S ORD = typeTable st.tt (ordNum st.tt)
  sz : S SZ = typeTable st.tt (sizeNum cap st.tt)
  cnt : S CNT = cntTable j cap st.x.length st.tt
  rows : S ROWS = rowsFlat j cap st.x.length st.tt
  roff : S ROFF = roffTable j cap st.x.length st.tt
  valt : S VALT = valTable j cap st.x.length st.tt
  envt : S ENVT = envTable j cap st.x.length st.tt st.ct
  rv : S RV = Tf.flatten
  cap : S CAP = [cap]
  scratch : ScratchEmpty S

end Shallot.MacroPeg.Mach
