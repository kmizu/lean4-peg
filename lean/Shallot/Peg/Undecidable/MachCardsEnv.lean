import Shallot.Peg.Undecidable.MachCardsRows

/-!
# The stacks of the cards stage

The names of the stacks, and the environment the writing programs run in (`BE`): the bits of the input, the rows,
their number, the bound `b`, the number of symbols `n = 2b + 2`, the star `m = 2b + 4`, `3 na`, and two empty
scratch stacks. Updates of other stacks keep the environment (`BE.set`).
-/

namespace Shallot

open Complexity
open Complexity.Univ

namespace MC

abbrev sOUT : Fin UK := 0
abbrev sT1 : Fin UK := 1
abbrev sBV : Fin UK := 2
abbrev sJ : Fin UK := 3
abbrev sRJ : Fin UK := 4
abbrev sX : Fin UK := 5
abbrev sRX : Fin UK := 6
abbrev sXB : Fin UK := 7
abbrev sT2 : Fin UK := 8
abbrev sCC : Fin UK := 9
abbrev sU : Fin UK := 10
abbrev sNN : Fin UK := 11
abbrev sMM : Fin UK := 12
abbrev sRS : Fin UK := 13
abbrev sNQ : Fin UK := 14
abbrev sNA : Fin UK := 15
abbrev sDC : Fin UK := 16
abbrev sK2 : Fin UK := 17
abbrev sLN : Fin UK := 18
abbrev sB : Fin UK := 19
abbrev sN : Fin UK := 20
abbrev sM : Fin UK := 21
abbrev sQ : Fin UK := 22
abbrev sRQ : Fin UK := 23
abbrev sA : Fin UK := 24
abbrev sRA : Fin UK := 25
abbrev sC : Fin UK := 26
abbrev sRC : Fin UK := 27
abbrev sNA3 : Fin UK := 28
abbrev sSC : Fin UK := 29
abbrev sI3 : Fin UK := 30
abbrev sTMP : Fin UK := 32
abbrev sQP : Fin UK := 33
abbrev sWR : Fin UK := 34
abbrev sMV : Fin UK := 35
abbrev sF : Fin UK := 36
abbrev sCT : Fin UK := 37
abbrev sCU : Fin UK := 38
abbrev sCG : Fin UK := 39

/-- The environment of the writing programs. -/
structure BE (S : Lists UK) (bits rest : List Nat) (nw L b n m na3 : Nat) : Prop where
  xb : S sXB = bits
  nn : Top S sNN nw
  rs : S sRS = rest
  ln : Top S sLN L
  bb : Top S sB b
  nN : Top S sN n
  mm : Top S sM m
  na : Top S sNA3 na3
  sc : S sSC = []
  tmp : S sTMP = []

def beStacks : List (Fin UK) := [sXB, sNN, sRS, sLN, sB, sN, sM, sNA3, sSC, sTMP]

theorem BE.set {S : Lists UK} {bits rest : List Nat} {nw L b n m na3 : Nat} (h : BE S bits rest nw L b n m na3)
    (X : Fin UK) (hX : X ∉ beStacks) (v : List Nat) : BE (S.set X v) bits rest nw L b n m na3 := by
  have hne : ∀ Y ∈ beStacks, Y ≠ X := fun Y hY e => hX (e ▸ hY)
  exact
    { xb := by rw [Lists.set_ne _ _ (hne sXB (by decide))]; exact h.xb
      nn := h.nn.set_ne (hne _ (by decide)) v
      rs := by rw [Lists.set_ne _ _ (hne sRS (by decide))]; exact h.rs
      ln := h.ln.set_ne (hne _ (by decide)) v
      bb := h.bb.set_ne (hne _ (by decide)) v
      nN := h.nN.set_ne (hne _ (by decide)) v
      mm := h.mm.set_ne (hne _ (by decide)) v
      na := h.na.set_ne (hne _ (by decide)) v
      sc := by rw [Lists.set_ne _ _ (hne sSC (by decide))]; exact h.sc
      tmp := by rw [Lists.set_ne _ _ (hne sTMP (by decide))]; exact h.tmp }

theorem Top.getD {K : Nat} {S : Lists K} {X : Fin K} {v : Nat} (h : Top S X v) : (S X).getLast?.getD 0 = v :=
  h.tv

/-- Values of tops and stacks of a state built by updates. -/
macro "tvsimp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { decide := true }) [tv, Lists.set, LinE.ev, $ts,*])

end MC

end Shallot
