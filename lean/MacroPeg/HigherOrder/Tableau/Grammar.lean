import MacroPeg.HigherOrder.Levels.Higher
import Complexity.TopFormula

/-!
# A grammar that follows the run of a Turing machine

For a deterministic `kt`-tape machine `M` (`Complexity/TM.lean`) and a level `K`, the grammar `gT M K` has, besides
the level rules, tests on the configuration at time `t` (a level-`K` number):

* `STATE_q(t)`: the state is `q`;
* `HEAD_τ(t, i)`: the head of tape `τ` is at cell `i` (a level-`K` number);
* `SYM_{τ,s}(t, i)`: cell `i` of tape `τ` holds `s`;
* `READ_{τ,s}(t, i)`: the head of tape `τ` is at a cell `≥ i` that holds `s` (a loop over cells; `READ_{τ,s}(t, 0)`
  is "the symbol under head `τ` is `s`").

At time `0` they read the initial configuration: the input on tape `0` comes from `INPUT_s(i, c, K)`, a loop that
keeps a level-`K` counter `c` and the unary code `K` of input site `c` side by side and looks the site up with
`FT(K, X)` — a scan from the start of the input, because every level test runs at the start. At a later time they
follow `TM.step` literally: a halted configuration stays; otherwise the state, the symbols under the heads and the
transition determine the next state, head positions and cells. Each case is a finite disjunction over the states and
the read vectors.

The input is `bitsFrom 0 m ++ '|' :: inSites w ++ ['#']`: `m` bit sites (for the level-1 numbers), `|`, then the
input sites `1ʲ0a` / `1ʲ0b` (input bit `false` / `true`), then `#`.
-/

namespace Shallot.MacroPeg.Tableau

open Complexity (TM Cfg Move initCfg bitSym)
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Levels
open Shallot.MacroPeg.ExpSpace (rcall allChainH anyChainH hcodeE hsiteE bitC)

/-! ## The input -/

/-- Input site `j` with input bit `b`. -/
def inSite (j : Nat) (b : Bool) : List Char := Shallot.MacroPeg.codeStr j ++ [if b then 'b' else 'a']

def inSitesFrom : Nat → List Bool → List Char
  | _, [] => []
  | j, b :: w => inSite j b ++ inSitesFrom (j + 1) w

/-- What follows `|`. -/
def inputTail (w : List Bool) : List Char := inSitesFrom 0 w ++ ['#']

/-- The whole input: `m` bit sites, `|`, the input sites, `#`. -/
def encChars (m : Nat) (w : List Bool) : List Char := sfxB m (inputTail w) 0

/-! ## Pieces -/

def hone : HExp := .lit ['1']
def hzero : HExp := .lit ['0']

/-- One input site. -/
def inSiteE : HExp := .seq hcodeE (.alt (.lit ['a']) (.lit ['b']))

/-- At an input site: the symbol is `s` (`1` for bit `false`, `2` for bit `true`). -/
def symE (s : Nat) : HExp :=
  if s = 1 then .seq hcodeE (.lit ['a']) else if s = 2 then .seq hcodeE (.lit ['b']) else HExp.failAlways

/-- Skip the bit sites and `|`. -/
def skipE : HExp := .seq (.star hsiteE) (.lit ['|'])

/-- The read vectors: one symbol per tape. -/
def readsList (na kt : Nat) : List (List Nat) := allVecs (List.range na) kt

/-- A read vector as the function `TM.delta` takes. -/
def rv {kt : Nat} (r : List Nat) : Fin kt → Nat := fun τ => r.getD τ.val 0

/-! ## Rule numbers -/

section Layout

variable {kt : Nat} (M : TM kt) (K : Nat)

/-- The tableau rules come after the level rules. -/
def tb : Nat := base K
def rFT : Nat := tb K
def rIN (s : Nat) : Nat := tb K + 1 + s
def rST (q : Nat) : Nat := tb K + 4 + q
def rHD (τ : Fin kt) : Nat := tb K + 4 + M.nq + τ.val
def rSY (τ : Fin kt) (s : Nat) : Nat := tb K + 4 + M.nq + kt + τ.val * M.na + s
def rRD (τ : Fin kt) (s : Nat) : Nat := tb K + 4 + M.nq + kt + kt * M.na + τ.val * M.na + s

end Layout

/-! ## Rule bodies -/

section Bodies

variable {kt : Nat} (M : TM kt) (K : Nat)

local notation "O" => ops K

/-- Find input site `Kc` (scanning from the start of the input) and test `X` there. -/
def ftE (Kc X : HExp) : HExp := .seq skipE (rcall (rFT K) [Kc, X])

def ftsBody : HExp :=
  .alt (.seq (HExp.andP (.seq (.var 1) hzero)) (HExp.andP (.var 0))) (.seq inSiteE (rcall (rFT K) [.var 1, .var 0]))

/-- `INPUT_s(i, c, Kc)`: cell `i` of the initial tape `0` holds `s`; `c` and `Kc` count the input sites. -/
def inBody (s : Nat) : HExp :=
  guardE (ftE K (.var 0) .eps)
    (guardE ((ops K).eq (.var 2) (.var 1)) (ftE K (.var 0) (symE s))
      (rcall (rIN K s) [.var 2, (ops K).inc (.var 1), .seq (.var 0) hone]))
    (bitC (s == 0))

/-- The symbols under the heads at time `tp` are `r`. -/
def readsE (r : List Nat) (tp : HExp) : HExp :=
  allChainH ((List.finRange kt).map (fun τ => rcall (rRD M K τ (r.getD τ.val 0)) [tp, (ops K).zero]))

/-- The non-halting states `2, …, nq - 1`. -/
def runStates : List Nat := (List.range M.nq).filter (2 ≤ ·)

def stateNext (q : Nat) (tp : HExp) : HExp :=
  anyChainH (((List.range 2).filter (· == q)).map (fun q' => rcall (rST K q') [tp]) ++
    (runStates M).flatMap (fun q' => ((readsList M.na kt).filter (fun r => (M.delta q' (rv r)).1 == q)).map
      (fun r => .seq (HExp.andP (rcall (rST K q') [tp])) (readsE M K r tp))))

def stateBody (q : Nat) : HExp :=
  guardE ((ops K).isZero (.var 0)) (bitC (q == 2)) (stateNext M K q ((ops K).dec (.var 0)))

/-- Head `τ` is at `i` after moving by `mv` from its position at time `tp`. -/
def movedE (τ : Fin kt) (mv : Move) (tp i : HExp) : HExp :=
  match mv with
  | .L => .alt (guardE ((ops K).isMax i) HExp.failAlways (rcall (rHD M K τ) [tp, (ops K).inc i]))
      (.seq (HExp.andP ((ops K).isZero i)) (rcall (rHD M K τ) [tp, i]))
  | .S => rcall (rHD M K τ) [tp, i]
  | .R => .seq (.notP ((ops K).isZero i)) (rcall (rHD M K τ) [tp, (ops K).dec i])

def headNext (τ : Fin kt) (tp i : HExp) : HExp :=
  anyChainH ((List.range 2).map (fun q' => .seq (HExp.andP (rcall (rST K q') [tp])) (rcall (rHD M K τ) [tp, i])) ++
    (runStates M).flatMap (fun q' => (readsList M.na kt).map (fun r =>
      .seq (HExp.andP (rcall (rST K q') [tp]))
        (.seq (HExp.andP (readsE M K r tp)) (movedE M K τ ((M.delta q' (rv r)).2.2 τ) tp i)))))

def headBody (τ : Fin kt) : HExp :=
  guardE ((ops K).isZero (.var 1)) ((ops K).isZero (.var 0)) (headNext M K τ ((ops K).dec (.var 1)) (.var 0))

/-- The initial content of cell `i` of tape `τ`. -/
def initE (τ : Fin kt) (s : Nat) (i : HExp) : HExp :=
  if τ.val = 0 then (if s ≤ 2 then rcall (rIN K s) [i, (ops K).zero, .eps] else HExp.failAlways) else bitC (s == 0)

def symNext (τ : Fin kt) (s : Nat) (tp i : HExp) : HExp :=
  anyChainH ((List.range 2).map (fun q' => .seq (HExp.andP (rcall (rST K q') [tp])) (rcall (rSY M K τ s) [tp, i])) ++
    (runStates M).flatMap (fun q' => (readsList M.na kt).map (fun r =>
      .seq (HExp.andP (rcall (rST K q') [tp]))
        (.seq (HExp.andP (readsE M K r tp))
          (guardE (rcall (rHD M K τ) [tp, i]) (bitC ((M.delta q' (rv r)).2.1 τ == s)) (rcall (rSY M K τ s) [tp, i]))))))

def symBody (τ : Fin kt) (s : Nat) : HExp :=
  guardE ((ops K).isZero (.var 1)) (initE K τ s (.var 0)) (symNext M K τ s ((ops K).dec (.var 1)) (.var 0))

def readBody (τ : Fin kt) (s : Nat) : HExp :=
  .alt (.seq (HExp.andP (rcall (rHD M K τ) [.var 1, .var 0])) (rcall (rSY M K τ s) [.var 1, .var 0]))
    (.seq (.notP ((ops K).isMax (.var 0))) (rcall (rRD M K τ s) [.var 1, (ops K).inc (.var 0)]))

end Bodies

/-! ## The grammar -/

section Grammar

variable {kt : Nat} (M : TM kt) (K : Nat)

local notation "τK" => lvTy K

def tabRules : List HRule :=
  [⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (ftsBody K)⟩] ++
  (List.range 3).map (fun s => ⟨τK ⇒ τK ⇒ Ty.p ⇒ Ty.p, lamsT [τK, τK, .p] (inBody K s)⟩) ++
  (List.range M.nq).map (fun q => ⟨τK ⇒ Ty.p, lamsT [τK] (stateBody M K q)⟩) ++
  (List.finRange kt).map (fun τ => ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (headBody M K τ)⟩) ++
  (List.finRange kt).flatMap (fun τ => (List.range M.na).map (fun s =>
    ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (symBody M K τ s)⟩)) ++
  (List.finRange kt).flatMap (fun τ => (List.range M.na).map (fun s =>
    ⟨τK ⇒ τK ⇒ Ty.p, lamsT [τK, τK] (readBody M K τ s)⟩))

/-- The levels `0, …, K` and the tableau of `M`. -/
def gT : HGrammar := ⟨level1Rules ++ (List.range K).flatMap blockRules ++ tabRules M K⟩

/-- Accept iff the state at the last time `E - 1` is `0` (accepting), then read the rest. -/
def startT : HExp := .seq (HExp.andP (rcall (rST K 0) [(ops K).max])) (.star .any)

end Grammar

end Shallot.MacroPeg.Tableau
