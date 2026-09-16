import PalPeg.GalilVMEncode

/-!
# A tape encoding of the chain component

`PalPeg.GalilVMEncode` lays out every field of `GalilScaffoldTop.State GalilVM`
on tapes except one: the chain view `GalilVM.chain : ChainVM`, which
`encode_injective` carries along abstractly.  This file closes that gap.

* `Sym2 := Sym ⊕ Token` extends the scaffold alphabet by the eleven period
  symbols of `GalilScaffoldChainPeriod.Token` (25 symbols in all);
* `encodeChain : ChainVM → Fin 8 → STape Sym2` writes the data of whichever
  chain constructor is active; eight tapes suffice, the `copy` and the
  `watch`/`broken` payloads being the widest, both needing exactly eight;
* `chainCtl : ChainVM → ChainCtlFin` keeps the constructor tag together with
  the genuinely finite part of the consume control (`phase`, `forward`,
  `broken`);
* `encodeChain_injective` says the pair determines the chain;
* `encodeAll : State GalilVM → Fin (42 + 8) → STape Sym2` appends the chain
  tapes to the `Sym`-tapes of `encodeState`, lifted along `Sum.inl`, and
  `encodeAll_injective` says the whole scaffold state is now recovered —
  no component is left abstract.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilChainEncode

open PalPeg.Program
open PalPeg.GalilScaffoldTop
open PalPeg.GalilVMEncode
open PalPeg.GalilScaffoldChainInputSupply (ChainVM GalilVM)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.GalilScaffoldPlace (Place)
open PalPeg.GalilScaffoldChainPeriod (Token)

/-! ## The period alphabet is finite

`Token` derives only `DecidableEq` upstream, so the `Fintype` instance is built
here by listing the eleven symbols. -/

def tokenList : List Token :=
  [.blank, .left, .plain 0, .plain 1, .plain 2, .first 0, .first 1, .first 2,
    .last 0, .last 1, .last 2]

theorem tokenList_complete (x : Token) : x ∈ tokenList := by
  cases x with
  | blank => decide
  | left => decide
  | plain a => fin_cases a <;> decide
  | first a => fin_cases a <;> decide
  | last a => fin_cases a <;> decide

instance : Fintype Token := Fintype.ofList tokenList tokenList_complete

example : Fintype.card Token = 11 := by decide

/-! ## The extended alphabet -/

/-- The chain tape alphabet: the scaffold alphabet `Sym` plus the eleven
period symbols. -/
abbrev Sym2 : Type := Sym ⊕ Token

instance : Fintype Sym2 := inferInstance
instance : DecidableEq Sym2 := inferInstance

example : Fintype.card Sym2 = 25 := by decide

/-- The scaffold alphabet inside the chain alphabet. -/
def s2 (s : Sym) : Sym2 := Sum.inl s
/-- A period symbol inside the chain alphabet. -/
def sTok (t : Token) : Sym2 := Sum.inr t

theorem s2_inj : Function.Injective s2 := by
  intro a b h; simpa [s2] using h

theorem sTok_inj : Function.Injective sTok := by
  intro a b h; simpa [sTok] using h

/-- A `Sym`-tape read as a `Sym2`-tape. -/
def lift (t : STape Sym) : STape Sym2 :=
  ⟨t.left.map s2, s2 t.focus, t.right.map s2⟩

theorem lift_inj : Function.Injective lift := by
  intro a b h
  obtain ⟨l1, f1, r1⟩ := a
  obtain ⟨l2, f2, r2⟩ := b
  simp only [lift, STape.mk.injEq] at h
  obtain ⟨hl, hf, hr⟩ := h
  rw [map_inj s2_inj hl, s2_inj hf, map_inj s2_inj hr]

/-- The period tape, already zipper-shaped, taken over as-is. -/
def periodTape (t : PalPeg.GalilScaffoldChainPeriod.Tape) : STape Sym2 :=
  ⟨t.left.map sTok, sTok t.focus, t.right.map sTok⟩

theorem periodTape_inj : Function.Injective periodTape := by
  intro a b h
  obtain ⟨l1, f1, r1⟩ := a
  obtain ⟨l2, f2, r2⟩ := b
  simp only [periodTape, STape.mk.injEq] at h
  obtain ⟨hl, hf, hr⟩ := h
  rw [map_inj sTok_inj hl, sTok_inj hf, map_inj sTok_inj hr]

/-- The empty chain tape. -/
def blank2 : STape Sym2 := ⟨[], s2 blank, []⟩

/-! ## The finite chain control -/

/-- Constructor tag of the chain. -/
def chainTag : ChainVM → Fin 5
  | .idle => 0
  | .copy .. => 1
  | .back .. => 2
  | .watch _ => 3
  | .broken _ => 4

/-- The consume phase, where there is one. -/
def chainPhase : ChainVM → Fin 5
  | .watch w => w.machine.control.phase
  | .broken w => w.machine.control.phase
  | _ => 0

/-- The consume direction flag, where there is one. -/
def chainForward : ChainVM → Bool
  | .watch w => w.machine.control.forward
  | .broken w => w.machine.control.forward
  | _ => false

/-- The consume break flag, where there is one. -/
def chainBroken : ChainVM → Bool
  | .watch w => w.machine.control.broken
  | .broken w => w.machine.control.broken
  | _ => false

/-- The finite control of the chain: the constructor tag plus the three
finite fields of `GalilScaffoldChainConsume.State`. -/
abbrev ChainCtlFin : Type := Fin 5 × Fin 5 × Bool × Bool

instance : Fintype ChainCtlFin := inferInstance

def chainCtl (c : ChainVM) : ChainCtlFin :=
  (chainTag c, chainPhase c, chainForward c, chainBroken c)

/-! ## The chain tape layout -/

/-- `copy`: verifier `0–1`, period `2`, `lag`/`margin` `3–4`, `h` `5`,
the unary DP answer `6`, the copy walker `7`. -/
def copyTapes (answer : GalilScaffoldTape.Tape) (h : Counter) (walker : Place)
    (period : PalPeg.GalilScaffoldChainPeriod.Tape) (lag margin : Counter)
    (verifier : PlaceHead) : Fin 8 → STape Sym2
  | 0 => lift (headZip verifier)
  | 1 => lift (headAux verifier)
  | 2 => periodTape period
  | 3 => lift (ctrTape lag)
  | 4 => lift (ctrTape margin)
  | 5 => lift (ctrTape h)
  | 6 => lift (dpTape answer)
  | 7 => lift (placeTape walker)
  | _ => blank2

/-- `back`: verifier `0–1`, period `2`, `lag`/`margin` `3–4`, `h` `5`. -/
def backTapes (period : PalPeg.GalilScaffoldChainPeriod.Tape) (h lag margin : Counter)
    (verifier : PlaceHead) : Fin 8 → STape Sym2
  | 0 => lift (headZip verifier)
  | 1 => lift (headAux verifier)
  | 2 => periodTape period
  | 3 => lift (ctrTape lag)
  | 4 => lift (ctrTape margin)
  | 5 => lift (ctrTape h)
  | _ => blank2

/-- `watch`/`broken`: verifier `0–1`, the control period `2`,
`lag`/`margin` `3–4`, the control counters `distance`/`boundary`/`last`
`5–7`. -/
def watchTapes (w : GalilScaffoldChainWatch.State) : Fin 8 → STape Sym2
  | 0 => lift (headZip w.machine.verifier)
  | 1 => lift (headAux w.machine.verifier)
  | 2 => periodTape w.machine.control.period
  | 3 => lift (ctrTape w.lag)
  | 4 => lift (ctrTape w.margin)
  | 5 => lift (ctrTape w.machine.control.distance)
  | 6 => lift (ctrTape w.machine.control.boundary)
  | 7 => lift (ctrTape w.machine.control.last)
  | _ => blank2

/-- The chain tapes: eight tapes, shared between the constructors, which the
tag in `chainCtl` tells apart. -/
def encodeChain : ChainVM → Fin 8 → STape Sym2
  | .idle => fun _ => blank2
  | .copy answer h walker period lag margin verifier =>
      copyTapes answer h walker period lag margin verifier
  | .back period h lag margin verifier => backTapes period h lag margin verifier
  | .watch w => watchTapes w
  | .broken w => watchTapes w

/-! ## Injectivity of the chain encoding -/

/-- The `copy` payload is determined by its eight tapes. -/
theorem copy_inj {a1 a2 : GalilScaffoldTape.Tape} {h1 h2 : Counter} {w1 w2 : Place}
    {p1 p2 : PalPeg.GalilScaffoldChainPeriod.Tape} {l1 l2 m1 m2 : Counter}
    {v1 v2 : PlaceHead}
    (he : copyTapes a1 h1 w1 p1 l1 m1 v1 = copyTapes a2 h2 w2 p2 l2 m2 v2) :
    ChainVM.copy a1 h1 w1 p1 l1 m1 v1 = ChainVM.copy a2 h2 w2 p2 l2 m2 v2 := by
  have e0 : lift (headZip v1) = lift (headZip v2) := congrFun he 0
  have e1 : lift (headAux v1) = lift (headAux v2) := congrFun he 1
  have e2 : periodTape p1 = periodTape p2 := congrFun he 2
  have e3 : lift (ctrTape l1) = lift (ctrTape l2) := congrFun he 3
  have e4 : lift (ctrTape m1) = lift (ctrTape m2) := congrFun he 4
  have e5 : lift (ctrTape h1) = lift (ctrTape h2) := congrFun he 5
  have e6 : lift (dpTape a1) = lift (dpTape a2) := congrFun he 6
  have e7 : lift (placeTape w1) = lift (placeTape w2) := congrFun he 7
  obtain rfl := headPair_inj (lift_inj e0) (lift_inj e1)
  obtain rfl := periodTape_inj e2
  obtain rfl := ctrTape_inj (lift_inj e3)
  obtain rfl := ctrTape_inj (lift_inj e4)
  obtain rfl := ctrTape_inj (lift_inj e5)
  obtain rfl := dpTape_inj (lift_inj e6)
  obtain rfl := placeTape_inj (lift_inj e7)
  rfl

/-- The `back` payload is determined by its six tapes. -/
theorem back_inj {p1 p2 : PalPeg.GalilScaffoldChainPeriod.Tape}
    {h1 h2 l1 l2 m1 m2 : Counter} {v1 v2 : PlaceHead}
    (he : backTapes p1 h1 l1 m1 v1 = backTapes p2 h2 l2 m2 v2) :
    ChainVM.back p1 h1 l1 m1 v1 = ChainVM.back p2 h2 l2 m2 v2 := by
  have e0 : lift (headZip v1) = lift (headZip v2) := congrFun he 0
  have e1 : lift (headAux v1) = lift (headAux v2) := congrFun he 1
  have e2 : periodTape p1 = periodTape p2 := congrFun he 2
  have e3 : lift (ctrTape l1) = lift (ctrTape l2) := congrFun he 3
  have e4 : lift (ctrTape m1) = lift (ctrTape m2) := congrFun he 4
  have e5 : lift (ctrTape h1) = lift (ctrTape h2) := congrFun he 5
  obtain rfl := headPair_inj (lift_inj e0) (lift_inj e1)
  obtain rfl := periodTape_inj e2
  obtain rfl := ctrTape_inj (lift_inj e3)
  obtain rfl := ctrTape_inj (lift_inj e4)
  obtain rfl := ctrTape_inj (lift_inj e5)
  rfl

/-- A `watch`/`broken` payload is determined by its eight tapes together with
the three finite control fields. -/
theorem watchTapes_inj {u1 u2 : GalilScaffoldChainWatch.State}
    (he : watchTapes u1 = watchTapes u2)
    (hph : u1.machine.control.phase = u2.machine.control.phase)
    (hfw : u1.machine.control.forward = u2.machine.control.forward)
    (hbr : u1.machine.control.broken = u2.machine.control.broken) : u1 = u2 := by
  have e0 : lift (headZip u1.machine.verifier) = lift (headZip u2.machine.verifier) :=
    congrFun he 0
  have e1 : lift (headAux u1.machine.verifier) = lift (headAux u2.machine.verifier) :=
    congrFun he 1
  have e2 : periodTape u1.machine.control.period = periodTape u2.machine.control.period :=
    congrFun he 2
  have e3 : lift (ctrTape u1.lag) = lift (ctrTape u2.lag) := congrFun he 3
  have e4 : lift (ctrTape u1.margin) = lift (ctrTape u2.margin) := congrFun he 4
  have e5 : lift (ctrTape u1.machine.control.distance)
      = lift (ctrTape u2.machine.control.distance) := congrFun he 5
  have e6 : lift (ctrTape u1.machine.control.boundary)
      = lift (ctrTape u2.machine.control.boundary) := congrFun he 6
  have e7 : lift (ctrTape u1.machine.control.last)
      = lift (ctrTape u2.machine.control.last) := congrFun he 7
  obtain ⟨⟨ver1, ⟨per1, dist1, bnd1, last1, ph1, fw1, br1⟩⟩, lag1, mar1⟩ := u1
  obtain ⟨⟨ver2, ⟨per2, dist2, bnd2, last2, ph2, fw2, br2⟩⟩, lag2, mar2⟩ := u2
  have hph' : ph1 = ph2 := hph
  have hfw' : fw1 = fw2 := hfw
  have hbr' : br1 = br2 := hbr
  subst hph'; subst hfw'; subst hbr'
  obtain rfl := headPair_inj (lift_inj e0) (lift_inj e1)
  obtain rfl := periodTape_inj e2
  obtain rfl := ctrTape_inj (lift_inj e3)
  obtain rfl := ctrTape_inj (lift_inj e4)
  obtain rfl := ctrTape_inj (lift_inj e5)
  obtain rfl := ctrTape_inj (lift_inj e6)
  obtain rfl := ctrTape_inj (lift_inj e7)
  rfl

/-- The chain tapes together with the finite chain control determine the chain
view: the constructor, the `PlaceHead`/`Place` cursors, the period tape, all
counters, the unary DP answer and the whole consume control. -/
theorem encodeChain_injective :
    Function.Injective (fun c : ChainVM => (chainCtl c, encodeChain c)) := by
  intro c1 c2 h
  simp only [Prod.mk.injEq, chainCtl] at h
  obtain ⟨⟨ht, hph, hfw, hbr⟩, he⟩ := h
  cases c1 <;> cases c2 <;> try (simp [chainTag] at ht)
  · rfl
  · exact copy_inj he
  · exact back_inj he
  · exact congrArg ChainVM.watch (watchTapes_inj he hph hfw hbr)
  · exact congrArg ChainVM.broken (watchTapes_inj he hph hfw hbr)

/-! ## The whole state -/

/-- The full tape layout of the scaffold: the forty-two `Sym`-tapes of
`encodeState`, read in the extended alphabet, followed by the eight chain
tapes. -/
def encodeAll (x : State GalilVM) : Fin (42 + 8) → STape Sym2 :=
  Fin.append (fun i => lift (encodeState x i)) (encodeChain x.vm.chain)

/-- Nothing is left abstract: the fifty tapes together with the two finite
controls determine the scaffold state completely. -/
theorem encodeAll_injective :
    Function.Injective
      (fun x : State GalilVM => (encodeCtl x, chainCtl x.vm.chain, encodeAll x)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hctl, hcc, ha⟩ := h
  have hs : encodeState x = encodeState y := by
    funext i
    have hi := congrFun ha (Fin.castAdd 8 i)
    simp only [encodeAll, Fin.append_left] at hi
    exact lift_inj hi
  have hec : encodeChain x.vm.chain = encodeChain y.vm.chain := by
    funext i
    have hi := congrFun ha (Fin.natAdd 42 i)
    simpa only [encodeAll, Fin.append_right] using hi
  have hchain : x.vm.chain = y.vm.chain :=
    encodeChain_injective (by simp only [hcc, hec])
  exact encode_injective (by simp only [hctl, hchain, hs])

#print axioms encodeChain_injective
#print axioms encodeAll_injective

end PalPeg.GalilChainEncode
