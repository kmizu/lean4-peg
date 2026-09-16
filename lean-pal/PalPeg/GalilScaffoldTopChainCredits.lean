import PalPeg.GalilScaffoldTopChainStart

/-!
# Chain preparation with interleaved scan credits

While the chain copies and rewinds (Copy/Back), every matched scan
comparison credits it (`lag++`, `margin++`). The lower layer records this
as `GalilScaffoldChainCredits.prepEvents sm dm bs cs`: the start tick
(matched `sm`), one event `(true, b)` per copy step, the copy end (`dm`),
one event `(false, b)` per back tick. A chain tick is a background step
followed by the optional credit; runs over those event lists reproduce the
credit state exactly. At the last back tick the chain is already watching,
and with a positive lag the credit is `Outer.queued`, the same `lag++`,
`margin++`.
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter

inductive ChainTicks : List Bool → ChainVM → ChainVM → Prop
  | nil (x) : ChainTicks [] x x
  | cons {a as x y z} (h : ChainTick a x y) (hr : ChainTicks as y z) : ChainTicks (a :: as) x z

theorem chainTicks_trans {as bs : List Bool} {x y z : ChainVM} (h1 : ChainTicks as x y)
    (h2 : ChainTicks bs y z) : ChainTicks (as ++ bs) x z := by
  induction h1 with
  | nil => simpa using h2
  | cons h _ ih => exact .cons h (ih h2)

/-- The credit state as a pair `(margin, lag)`. -/
def creditsOf (margin lag : Counter) : GalilScaffoldChainCredits.State := ⟨margin, lag⟩

theorem step_copy (margin lag : Counter) (b : Bool) :
    GalilScaffoldChainCredits.step (creditsOf margin lag) (true, b) =
      creditsOf (if b then inc (GalilScaffoldChainCredits.decFour margin) else GalilScaffoldChainCredits.decFour margin)
        (if b then inc lag else lag) := by
  cases b <;> rfl

theorem step_idle (margin lag : Counter) (b : Bool) :
    GalilScaffoldChainCredits.step (creditsOf margin lag) (false, b) =
      creditsOf (if b then inc margin else margin) (if b then inc lag else lag) := by
  cases b <;> rfl

/-- Copy walk with interleaved credits. -/
theorem copy_ticks (n : ℕ) : ∀ (bs : List Bool), bs.length = n →
    ∀ {t : GalilScaffoldTape.Tape} {c : Counter} {p : GalilScaffoldPlace.Place}
      {v : GalilScaffoldChainPeriod.Tape} {u d q z} (lag margin : Counter) (ver : GalilScaffoldInputHead.PlaceHead),
    GalilScaffoldChainPeriod.Copy t c p v n u d q z →
    ChainTicks bs (.copy t c p v lag margin ver)
      (.copy u d q z (GalilScaffoldChainCredits.run (creditsOf margin lag) (bs.map (fun b => (true, b)))).lag
        (GalilScaffoldChainCredits.run (creditsOf margin lag) (bs.map (fun b => (true, b)))).margin ver) := by
  induction n with
  | zero =>
    intro bs hbs t c p v u d q z lag margin ver h
    cases h
    cases bs with
    | nil => exact .nil _
    | cons _ _ => simp at hbs
  | succ n ih =>
    intro bs hbs t c p v u d q z lag margin ver h
    cases h with
    | next a one legal present rest =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        have hbs' : bs'.length = n := by simpa using hbs
        have hstep : ChainTick b (.copy t c p v lag margin ver)
            (.copy (GalilScaffoldTape.moveLeft t) (inc c) (GalilScaffoldPlace.left p)
              (GalilScaffoldChainPeriod.put v a) (if b then inc lag else lag)
              (if b then inc (GalilScaffoldChainCredits.decFour margin) else GalilScaffoldChainCredits.decFour margin) ver) := by
          refine ⟨_, .copyBit t c p v lag margin ver a one legal present, ?_⟩
          cases b
          · rfl
          · exact .copy _ _ _ _ _ _ _
        have := ih bs' hbs' (if b then inc lag else lag)
          (if b then inc (GalilScaffoldChainCredits.decFour margin) else GalilScaffoldChainCredits.decFour margin) ver rest
        simp only [List.map_cons, GalilScaffoldChainCredits.run, step_copy] at this ⊢
        exact .cons hstep this

theorem zero_ofNat_succ (k : ℕ) : zero (ofNat (k+1)) = false := by
  simp [zero, ofNat, List.replicate_succ]

/-- Back walk with interleaved credits, ending in watch; the lag is a
positive unary counter throughout, so the last credit is `Outer.queued`. -/
theorem back_ticks (n : ℕ) : ∀ (cs : List Bool), cs.length = n →
    ∀ {v u : GalilScaffoldChainPeriod.Tape} (h margin : Counter) (k : ℕ) (ver : GalilScaffoldInputHead.PlaceHead),
    GalilScaffoldChainPeriod.Back v n u →
    ChainTicks cs (.back v h (ofNat (k+1)) margin ver)
      (.watch ⟨⟨ver, ⟨u, reset, reset, reset, 0, true, false⟩⟩,
        (GalilScaffoldChainCredits.run (creditsOf margin (ofNat (k+1))) (cs.map (fun b => (false, b)))).lag,
        (GalilScaffoldChainCredits.run (creditsOf margin (ofNat (k+1))) (cs.map (fun b => (false, b)))).margin⟩) := by
  induction n with
  | zero => intro cs _ v u h margin k ver hb; cases hb
  | succ n ih =>
    intro cs hcs v u h margin k ver hb
    cases cs with
    | nil => simp at hcs
    | cons b cs' =>
      have hcs' : cs'.length = n := by simpa using hcs
      cases hb with
      | done _ hf =>
        cases cs' with
        | cons _ _ => simp at hcs'
        | nil =>
          -- the entering tick: back step into watch, then the credit
          have hstep : ChainTick b (.back v h (ofNat (k+1)) margin ver)
              (.watch ⟨⟨ver, watchControl v⟩, (if b then inc (ofNat (k+1)) else ofNat (k+1)),
                (if b then inc margin else margin)⟩) := by
            refine ⟨_, .backDone v h (ofNat (k+1)) margin ver hf, ?_⟩
            cases b
            · rfl
            · exact .watch _ _ (.queued _ (zero_ofNat_succ k))
          simp only [List.map_cons, List.map_nil, GalilScaffoldChainCredits.run, step_idle]
          exact .cons hstep (.nil _)
      | next _ hf hl hr =>
        have hstep : ChainTick b (.back v h (ofNat (k+1)) margin ver)
            (.back (GalilScaffoldChainPeriod.moveLeft v) h (if b then inc (ofNat (k+1)) else ofNat (k+1))
              (if b then inc margin else margin) ver) := by
          refine ⟨_, .backStep v h (ofNat (k+1)) margin ver hf, ?_⟩
          cases b
          · rfl
          · exact .back _ _ _ _ _
        cases b
        · have := ih cs' hcs' h margin k ver hr
          simp only [List.map_cons, GalilScaffoldChainCredits.run, step_idle] at this ⊢
          (try simp only [Bool.false_eq_true, ite_false] at hstep)
          exact .cons hstep this
        · have := ih cs' hcs' h (inc margin) (k+1) ver hr
          rw [inc_ofNat] at hstep
          simp only [List.map_cons, GalilScaffoldChainCredits.run, step_idle] at this ⊢
          (try simp only [ite_true] at hstep)
          rw [inc_ofNat]
          exact .cons hstep this

#print axioms copy_ticks
#print axioms back_ticks

end PalPeg.GalilScaffoldChainInputSupply
