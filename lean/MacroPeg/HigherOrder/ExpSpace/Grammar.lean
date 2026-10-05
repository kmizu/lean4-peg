import MacroPeg.HigherOrder.ExpSpace.Basic

/-!
# An order-2 grammar simulating an alternating machine with an exponentially long tape

The input is the list of sites of `AtmHard.lean` (`sitesStr w 0`): site `j` is `1ʲ0`, then `y` if `wⱼ = 1`, then `x;`.

* **Addresses** (order 0): an address `a` of `n` bits is a parser that, run at site `j`, reads through the `x` iff
  bit `j` of `a` is `1` (the tape representation of `AtmHard.lean`, now used for addresses). The first address is
  `H0`; the successor `incE H` reads site `j` with bit `Hⱼ xor (all later bits of H are 1)`, looked up with the scan
  `ALL1`; the predecessor `decE H` uses `ALL0`. `EQ(a, h)` compares two addresses site by site.
* **Tapes** (order 1, type `p ⇒ p`): a tape maps an address to a zero-width test that succeeds iff the cell holds `1`.
  Writing `b` at the head `H` gives the closure `λa. &EQ(a, H) b̂ / !EQ(a, H) T a` (`wrE`). The initial tape is
  `λa. &SC(a)`: some site has bit `1` in `a` and carries `y`.
* **States** (order 2, type `p ⇒ (p ⇒ p) ⇒ p`): the rule of state `q` takes the head and the tape, reads the cell under
  the head with `T H`, and continues in the successor states (all of them or one of them), each called with the moved
  head and the written tape. Everything runs at the start of the input and succeeds without consuming (accept) or
  fails (reject).

Rule bodies are written with de Bruijn variables (`stateBody`, …); `instState` and friends compute the body with
closed arguments put in, which is what a call runs (`hobs_call`).
-/

namespace Shallot.MacroPeg.ExpSpace

open Shallot.MacroPeg (ATM Dir Kind codeE siteE optY semi)
open Shallot.MacroPeg.HO

/-! ## Plain pieces -/

def hcodeE : HExp := emb 0 codeE
def hsiteE : HExp := emb 0 siteE
def hoptY : HExp := emb 0 optY
def hsemi : HExp := .lit [';']
def hhash : HExp := .lit ['#']

def rcall (i : Nat) (as : List HExp) : HExp := HExp.apps (.rule i) as

/-- At a site: bit `1`. -/
def bit1 (a : HExp) : HExp := .seq a hsemi

def xorE (P Q : HExp) : HExp := .alt (.seq (HExp.andP P) (.notP Q)) (.seq (.notP P) (HExp.andP Q))

/-- Read one site, through the `x` iff the zero-width test `B` succeeds there. -/
def newSite (B : HExp) : HExp :=
  .alt (.seq (HExp.andP B) (.seq (.seq hcodeE hoptY) (.lit ['x']))) (.seq (.notP B) (.seq hcodeE hoptY))

def bitC : Bool → HExp
  | true => .eps
  | false => HExp.failAlways

def allChainH : List HExp → HExp
  | [] => .eps
  | e :: es => .seq (HExp.andP e) (allChainH es)

def anyChainH : List HExp → HExp
  | [] => HExp.failAlways
  | e :: es => .alt e (anyChainH es)

section Builders

variable (M : ATM)

/-- Rule numbers after the states. -/
def rEQ : Nat := M.states
def rALL1 : Nat := M.states + 1
def rALL0 : Nat := M.states + 2
def rSC : Nat := M.states + 3

/-- The first address (all bits `0`). -/
def H0 : HExp := .seq hcodeE hoptY

def incE (h : HExp) : HExp := newSite (xorE (bit1 h) (.seq hsiteE (rcall (rALL1 M) [h])))
def decE (h : HExp) : HExp := newSite (xorE (bit1 h) (.seq hsiteE (rcall (rALL0 M) [h])))

/-- The tape `T` with `b` written at the head `H` (inside the closure `H`, `T` are `Hin`, `Tin`). -/
def wrE (Hin Tin : HExp) (b : Bool) : HExp :=
  .lam .p (.alt (.seq (HExp.andP (rcall (rEQ M) [.var 0, Hin])) (bitC b))
    (.seq (.notP (rcall (rEQ M) [.var 0, Hin])) (.app Tin (.var 0))))

/-- The initial tape. -/
def T0 : HExp := .lam .p (HExp.andP (rcall (rSC M) [.var 0]))

/-- A branch: write, move (staying put at the ends), continue in the target state. -/
def brE (H Hin Tin : HExp) (tr : Nat × Bool × Dir) : HExp :=
  match tr.2.2 with
  | .left =>
    .alt (.seq (HExp.andP (rcall (rALL0 M) [H])) (rcall tr.1 [H, wrE M Hin Tin tr.2.1]))
      (.seq (.notP (rcall (rALL0 M) [H])) (rcall tr.1 [decE M H, wrE M Hin Tin tr.2.1]))
  | .right =>
    .alt (.seq (HExp.andP (rcall (rALL1 M) [H])) (rcall tr.1 [H, wrE M Hin Tin tr.2.1]))
      (.seq (.notP (rcall (rALL1 M) [H])) (rcall tr.1 [incE M H, wrE M Hin Tin tr.2.1]))

def transE (q : Nat) (b : Bool) (H Hin Tin : HExp) : HExp :=
  match M.kind q with
  | .acc => .eps
  | .rej => HExp.failAlways
  | .univ => allChainH ((M.delta q b).map (brE M H Hin Tin))
  | .exist => anyChainH ((M.delta q b).map (brE M H Hin Tin))

/-- The rule of state `q`: read the cell under the head, then the transitions for that symbol. -/
def stateE (q : Nat) (H T Hin Tin : HExp) : HExp :=
  .alt (.seq (HExp.andP (.app T H)) (transE M q true H Hin Tin))
    (.seq (.notP (.app T H)) (transE M q false H Hin Tin))

end Builders

/-! ## Rule bodies -/

def eqE (M : ATM) (a h : HExp) : HExp :=
  .alt (HExp.andP hhash)
    (.seq (.alt (.seq (HExp.andP (bit1 a)) (HExp.andP (bit1 h))) (.seq (.notP (bit1 a)) (.notP (bit1 h))))
      (.seq hsiteE (rcall (rEQ M) [a, h])))

def all1E (M : ATM) (h : HExp) : HExp :=
  .alt (HExp.andP hhash) (.seq (HExp.andP (bit1 h)) (.seq hsiteE (rcall (rALL1 M) [h])))

def all0E (M : ATM) (h : HExp) : HExp :=
  .alt (HExp.andP hhash) (.seq (.notP (bit1 h)) (.seq hsiteE (rcall (rALL0 M) [h])))

def scE (M : ATM) (a : HExp) : HExp :=
  .alt (.seq (HExp.andP (bit1 a)) (HExp.andP (.seq hcodeE (.lit ['y'])))) (.seq hsiteE (rcall (rSC M) [a]))

def stateTy : HO.Ty := Ty.p ⇒ (Ty.p ⇒ Ty.p) ⇒ Ty.p

/-- The grammar: the state rules, then `EQ`, `ALL1`, `ALL0`, `SC`. -/
def g2 (M : ATM) : HGrammar :=
  ⟨(List.range M.states).map (fun q => ⟨stateTy, lamsT [Ty.p, Ty.p ⇒ Ty.p] (stateE M q (.var 1) (.var 0) (.var 2) (.var 1))⟩) ++
    [⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (eqE M (.var 1) (.var 0))⟩,
     ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all1E M (.var 0))⟩,
     ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all0E M (.var 0))⟩,
     ⟨Ty.p ⇒ Ty.p, lamsT [.p] (scE M (.var 0))⟩]⟩

/-- Start in the start state with the first address and the initial tape, then read the rest. -/
def start2 (M : ATM) : HExp := .seq (rcall M.start [H0, T0 M]) (.star .any)

/-! ## Putting closed arguments into the bodies -/

section Inst

theorem substC_of_cl (σ : List HExp) : ∀ {m k : Nat} {e : HExp}, HExp.Cl m e → m ≤ k → HExp.substC σ k e = e
  | _, _, .var i, h, hk => by simp only [HExp.Cl] at h; simp only [HExp.substC]; split <;> first | rfl | omega
  | m, k, .lam _ b, h, hk => by simp only [HExp.substC, substC_of_cl σ (m := m + 1) (k := k + 1) (e := b) h (by omega)]
  | _, _, .app f c, h, hk | _, _, .seq f c, h, hk | _, _, .alt f c, h, hk => by
    simp only [HExp.substC, substC_of_cl σ (e := f) h.1 hk, substC_of_cl σ (e := c) h.2 hk]
  | _, _, .star c, h, hk | _, _, .notP c, h, hk => by simp only [HExp.substC, substC_of_cl σ (e := c) h hk]
  | _, _, .eps, _, _ | _, _, .any, _, _ | _, _, .chr _, _, _ | _, _, .range _ _, _, _ | _, _, .lit _, _, _
  | _, _, .rule _, _, _ => rfl

/-- Plain PEG pieces have no variables. -/
theorem cl_emb_peg : ∀ (e : MExp), PegOnly e → HExp.Cl 0 (emb 0 e)
  | .seq a b, h | .alt a b, h => ⟨cl_emb_peg a h.1, cl_emb_peg b h.2⟩
  | .star a, h | .notP a, h => cl_emb_peg a h
  | .eps, _ | .any, _ | .chr _, _ | .range _ _, _ | .lit _, _ => trivial
  | .param _, h | .call _ _, h | .dbg _, h | .lam _ _, h | .callParam _ _, h | .invoke _ _ _, h => absurd h id

theorem peg_codeE : PegOnly codeE := ⟨trivial, trivial⟩
theorem peg_optY : PegOnly optY := ⟨trivial, trivial⟩
theorem peg_siteE : PegOnly siteE := ⟨⟨peg_codeE, peg_optY⟩, trivial, trivial⟩

variable (σ : List HExp) (k : Nat)

@[simp] theorem substC_hcodeE : HExp.substC σ k hcodeE = hcodeE := substC_of_cl σ (cl_emb_peg _ peg_codeE) (Nat.zero_le k)
@[simp] theorem substC_hsiteE : HExp.substC σ k hsiteE = hsiteE := substC_of_cl σ (cl_emb_peg _ peg_siteE) (Nat.zero_le k)
@[simp] theorem substC_hoptY : HExp.substC σ k hoptY = hoptY := substC_of_cl σ (cl_emb_peg _ peg_optY) (Nat.zero_le k)

theorem substC_apps : ∀ (f : HExp) (as : List HExp),
    HExp.substC σ k (HExp.apps f as) = HExp.apps (HExp.substC σ k f) (as.map (HExp.substC σ k))
  | _, [] => rfl
  | f, a :: as => by simp only [HExp.apps, substC_apps (.app f a) as, HExp.substC, List.map_cons]

@[simp] theorem substC_rcall (i : Nat) (as : List HExp) :
    HExp.substC σ k (rcall i as) = rcall i (as.map (HExp.substC σ k)) := by
  simp only [rcall, substC_apps]; rfl

@[simp] theorem substC_andP (e : HExp) : HExp.substC σ k (HExp.andP e) = HExp.andP (HExp.substC σ k e) := rfl

@[simp] theorem substC_bitC (b : Bool) : HExp.substC σ k (bitC b) = bitC b := by cases b <;> rfl

theorem substC_allChainH : ∀ es : List HExp, HExp.substC σ k (allChainH es) = allChainH (es.map (HExp.substC σ k))
  | [] => rfl
  | e :: es => by simp only [allChainH, HExp.substC, substC_andP, substC_allChainH es, List.map_cons]

theorem substC_anyChainH : ∀ es : List HExp, HExp.substC σ k (anyChainH es) = anyChainH (es.map (HExp.substC σ k))
  | [] => rfl
  | e :: es => by simp only [anyChainH, HExp.substC, substC_anyChainH es, List.map_cons]

variable (M : ATM)

theorem substC_incE (h : HExp) : HExp.substC σ k (incE M h) = incE M (HExp.substC σ k h) := by
  simp [incE, newSite, xorE, bit1, hsemi, HExp.substC]

theorem substC_decE (h : HExp) : HExp.substC σ k (decE M h) = decE M (HExp.substC σ k h) := by
  simp [decE, newSite, xorE, bit1, hsemi, HExp.substC]

theorem substC_wrE (Hin Tin : HExp) (b : Bool) :
    HExp.substC σ k (wrE M Hin Tin b) = wrE M (HExp.substC σ (k + 1) Hin) (HExp.substC σ (k + 1) Tin) b := by
  simp [wrE, HExp.substC]

theorem substC_brE (H Hin Tin : HExp) (tr : Nat × Bool × Dir) :
    HExp.substC σ k (brE M H Hin Tin tr) =
      brE M (HExp.substC σ k H) (HExp.substC σ (k + 1) Hin) (HExp.substC σ (k + 1) Tin) tr := by
  obtain ⟨q', b, d⟩ := tr
  cases d <;> simp [brE, HExp.substC, substC_incE, substC_decE, substC_wrE]

theorem substC_transE (q : Nat) (b : Bool) (H Hin Tin : HExp) :
    HExp.substC σ k (transE M q b H Hin Tin) =
      transE M q b (HExp.substC σ k H) (HExp.substC σ (k + 1) Hin) (HExp.substC σ (k + 1) Tin) := by
  unfold transE
  split
  · rfl
  · rfl
  · rw [substC_allChainH, List.map_map]; congr 1; apply List.map_congr_left; intro tr _; exact substC_brE σ k M _ _ _ tr
  · rw [substC_anyChainH, List.map_map]; congr 1; apply List.map_congr_left; intro tr _; exact substC_brE σ k M _ _ _ tr

theorem substC_stateE (q : Nat) (H T Hin Tin : HExp) :
    HExp.substC σ k (stateE M q H T Hin Tin) =
      stateE M q (HExp.substC σ k H) (HExp.substC σ k T) (HExp.substC σ (k + 1) Hin) (HExp.substC σ (k + 1) Tin) := by
  simp only [stateE, HExp.substC, substC_andP, substC_transE]

end Inst

section Calls

variable (M : ATM)

/-- The state rule with the head `H` and the tape `T` put in. -/
theorem inst_state (q : Nat) (H T : HExp) :
    HExp.substC [T, H] 0 (stateE M q (.var 1) (.var 0) (.var 2) (.var 1)) = stateE M q H T H T := by
  rw [substC_stateE]; rfl

theorem inst_eq (a h : HExp) : HExp.substC [h, a] 0 (eqE M (.var 1) (.var 0)) = eqE M a h := by
  simp [eqE, bit1, hsemi, hhash, HExp.substC]

theorem inst_all1 (h : HExp) : HExp.substC [h] 0 (all1E M (.var 0)) = all1E M h := by
  simp [all1E, bit1, hsemi, hhash, HExp.substC]

theorem inst_all0 (h : HExp) : HExp.substC [h] 0 (all0E M (.var 0)) = all0E M h := by
  simp [all0E, bit1, hsemi, hhash, HExp.substC]

theorem inst_sc (a : HExp) : HExp.substC [a] 0 (scE M (.var 0)) = scE M a := by
  simp [scE, bit1, hsemi, HExp.substC]

theorem g2_state {q : Nat} (hq : q < M.states) :
    (g2 M).rules[q]? = some ⟨stateTy, lamsT [.p, Ty.p ⇒ Ty.p] (stateE M q (.var 1) (.var 0) (.var 2) (.var 1))⟩ := by
  rw [g2, List.getElem?_append_left (by simpa using hq), List.getElem?_map, List.getElem?_range hq]
  rfl

theorem g2_eq : (g2 M).rules[rEQ M]? = some ⟨Ty.p ⇒ Ty.p ⇒ Ty.p, lamsT [.p, .p] (eqE M (.var 1) (.var 0))⟩ := by
  simp [g2, rEQ]
theorem g2_all1 : (g2 M).rules[rALL1 M]? = some ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all1E M (.var 0))⟩ := by
  simp [g2, rALL1]
theorem g2_all0 : (g2 M).rules[rALL0 M]? = some ⟨Ty.p ⇒ Ty.p, lamsT [.p] (all0E M (.var 0))⟩ := by
  simp [g2, rALL0]
theorem g2_sc : (g2 M).rules[rSC M]? = some ⟨Ty.p ⇒ Ty.p, lamsT [.p] (scE M (.var 0))⟩ := by
  simp [g2, rSC]

end Calls

end Shallot.MacroPeg.ExpSpace
