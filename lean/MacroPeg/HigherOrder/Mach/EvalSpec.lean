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
/-- The lengths of the rule values; the next round's values and their lengths. -/
abbrev RVL : Fin NK := 15
abbrev RVL2 : Fin NK := 17

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
  rvl : S RVL = Tf.map List.length
  cap : S CAP = [cap]
  scratch : ScratchEmpty S

/-- The size of what an item program sees and makes. -/
def itemZ (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat)) : Nat :=
  2 + (evFlat vs).length +
    (evFlat (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs)).length +
    (rowsFlat j cap st.x.length st.tt).length + Tf.flatten.length + Tf.length + st.ct.length + st.lt.length +
    (encLits st.lt).length + (envTable j cap st.x.length st.tt st.ct).sum +
    (valTable j cap st.x.length st.tt).sum + (cntTable j cap st.x.length st.tt).sum + it.a + it.b + it.ctx +
    st.x.length + st.tt.length +
    -- the sizes of the numbers that may be compared or counted down
    (evFlat vs).sum + (evFlat (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs)).sum + Tf.flatten.sum +
    (rowsFlat j cap st.x.length st.tt).sum + st.x.sum + (encLits st.lt).sum

/-- A bound on the steps of an item program. -/
def itemCost (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) (vs : List (List Nat)) : Nat :=
  1000 * (itemZ j cap st Tf it vs * itemZ j cap st Tf it vs * itemZ j cap st Tf it vs *
    itemZ j cap st Tf it vs * itemZ j cap st Tf it vs)

/-- An item program does the item's step on the evaluation stack. -/
def ItemRuns (p : NProg NK) (j cap : Nat) (st : PSt) (Tf : List (List Nat)) (it : MItem) : Prop :=
  ∀ (S : Lists NK) (vs : List (List Nat)), EvalEnv S j cap st Tf → S IT = encItem it → S EV = evFlat vs →
    S EVL = evLens vs →
    NRuns p S ((S.set EV (evFlat (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs))).set EVL
      (evLens (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs))) (itemCost j cap st Tf it vs)

end Shallot.MacroPeg.Mach
