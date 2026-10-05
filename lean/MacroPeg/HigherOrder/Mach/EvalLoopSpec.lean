import MacroPeg.HigherOrder.Mach.EvalSpec

/-!
# The cost of the evaluation loops

The steps of running items, of a round and of the rounds, along the actual run (`runCost`, `roundCost`,
`fixCost`): each item program within its `itemCost`, plus some steps per item and per round to move things.
-/

namespace Shallot.MacroPeg.Mach

/-! ## The cost of evaluating along the run -/

section Costs

variable (j cap : Nat) (st : PSt)

/-- The steps of running the items `l` from the stack `vs`. -/
def runCost (Tf : List (List Nat)) : List MItem → List (List Nat) → Nat
  | [], _ => 0
  | it :: l, vs =>
    itemCost j cap st Tf it vs + 500 + runCost Tf l (stepT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt Tf it vs)

/-- The steps of one round. -/
def roundCost (Tf : List (List Nat)) : Nat :=
  (st.bodies.map (fun l => runCost j cap st Tf l [] + 100 * (l.length + 1))).sum +
    100 * ((encBodies st.bodies).length + Tf.flatten.length + Tf.length + Tf.flatten.sum + 1)

/-- The steps of the rounds. -/
def fixCost : Nat → List (List Nat) → Nat
  | 0, _ => 1
  | fuel + 1, Tf =>
    roundCost j cap st Tf +
      (if roundT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies Tf = Tf then 0
        else fixCost fuel (roundT j cap (st.x.map Char.ofNat) st.tt st.ct st.lt st.bodies Tf))

end Costs

/-- The steps of the whole evaluation: preparing the rule values, the rounds, the start, the answer. -/
def evalCost (j cap : Nat) (st : PSt) : Nat :=
  let x := st.x.map Char.ofNat
  let Tf0 := st.rt.map (fun t => List.replicate (valT j cap x.length st.tt t) 0)
  let fuel := (st.rt.map (valT j cap x.length st.tt)).sum + 1
  let Tfin := fixT j cap x st.tt st.ct st.lt st.bodies fuel Tf0
  1000 * (fuel + st.rt.length + Tf0.flatten.length + (valTable j cap x.length st.tt).sum +
      (encItems st.start).length + (evFlat (runT j cap x st.tt st.ct st.lt Tfin st.start [])).length + x.length +
      st.tt.length + 2) *
    (fuel + st.rt.length + Tf0.flatten.length + (valTable j cap x.length st.tt).sum +
      (encItems st.start).length + (evFlat (runT j cap x st.tt st.ct st.lt Tfin st.start [])).length + x.length +
      st.tt.length + 2) +
  fixCost j cap st fuel Tf0 + runCost j cap st Tfin st.start []

end Shallot.MacroPeg.Mach
