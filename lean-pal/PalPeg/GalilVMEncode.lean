import PalPeg.ProgramMachine
import PalPeg.GalilScaffoldTopVM

/-!
# A tape encoding of the Galil scaffold state

`PalPeg.Program.StructuredMachine` stores its work in `Fin t → STape Γ` for a
finite alphabet `Γ`, plus a finite control state.  The online Galil scaffold is
instead described by `GalilScaffoldTop.State GalilVM`: a controller record and a
VM record of heads, counters, a search view, a chain view and two `ProgLang`
program machines.

This file gives the corresponding data layout:

* `Sym` — the concrete alphabet (`Option (Fin 2) ⊕ Bool ⊕ Fin 9`, 14 symbols);
* `encodeVM : GalilVM → Fin 41 → STape Sym` and
  `encodeState : State GalilVM → Fin 42 → STape Sym` (tape `0` carries the
  controller clock, see below);
* `encodeCtl : State GalilVM → CtlFin` for the genuinely finite control;
* `encode_injective`, saying that the pair determines the state, apart from the
  one component left unencoded here (`GalilVM.chain`).

Two remarks on what is *not* finite control.  `Control.clock : ℕ` and
`GalilScaffoldProgram.Config.pc : ℕ` are ℕ-valued; only under
`GalilScaffoldController.Bounded delay` would the clock fit in
`BoundedControl delay`.  Rather than assume that here, both are written in unary
on their own tapes, which keeps `CtlFin` finite unconditionally.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.GalilVMEncode

open PalPeg.Program
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (PlaceHead Head)
open PalPeg.GalilScaffoldCounter (Counter)
open PalPeg.GalilScaffoldPlace (Place)

/-! ## The alphabet -/

/-- The tape alphabet: input letters and the absent sentinel (`Option (Fin 2)`),
a bit (booleans and unary marks), and the nine `ProgLang` tape symbols. -/
abbrev Sym : Type := Option (Fin 2) ⊕ Bool ⊕ Fin 9

instance : Fintype Sym := inferInstance
instance : DecidableEq Sym := inferInstance

example : Fintype.card Sym = 14 := by decide

def sOpt (o : Option (Fin 2)) : Sym := Sum.inl o
def sLet (a : Fin 2) : Sym := Sum.inl (some a)
def sBit (b : Bool) : Sym := Sum.inr (Sum.inl b)
def sDp (s : Fin 9) : Sym := Sum.inr (Sum.inr s)

/-- The blank symbol. -/
def blank : Sym := sOpt none
/-- The unary counting mark. -/
def mark : Sym := sBit true

theorem sOpt_inj : Function.Injective sOpt := by
  intro a b h; simpa [sOpt] using h

theorem sLet_inj : Function.Injective sLet := by
  intro a b h; simpa [sLet] using h

theorem sBit_inj : Function.Injective sBit := by
  intro a b h; simpa [sBit] using h

theorem sDp_inj : Function.Injective sDp := by
  intro a b h; simpa [sDp] using h

theorem map_inj {α β : Type} {f : α → β} (hf : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 h
    cases l2 with
    | nil => rfl
    | cons b l2 => simp at h
  | cons a l ih =>
    intro l2 h
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf h.1, ih h.2]

/-! ## Unary numbers and counters -/

theorem unit_list (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a; rw [List.length_cons, List.replicate_succ, ← ih]

/-- A natural number in unary, head at the right end. -/
def natTape (n : ℕ) : STape Sym := ⟨List.replicate n mark, blank, []⟩

theorem natTape_inj : Function.Injective natTape := by
  intro a b h
  have h1 : List.replicate a mark = List.replicate b mark := congrArg STape.left h
  simpa using congrArg List.length h1

/-- A `Counter` as unary marks: the positive stack left of the head, the
negative stack right of it. -/
def ctrTape (c : Counter) : STape Sym :=
  ⟨List.replicate c.pos.length mark, blank, List.replicate c.neg.length mark⟩

theorem ctrTape_inj : Function.Injective ctrTape := by
  intro a b h
  have h1 : List.replicate a.pos.length mark = List.replicate b.pos.length mark :=
    congrArg STape.left h
  have h3 : List.replicate a.neg.length mark = List.replicate b.neg.length mark :=
    congrArg STape.right h
  have e1 : a.pos.length = b.pos.length := by simpa using congrArg List.length h1
  have e3 : a.neg.length = b.neg.length := by simpa using congrArg List.length h3
  obtain ⟨p1, n1⟩ := a
  obtain ⟨p2, n2⟩ := b
  have hp : p1 = p2 := by rw [unit_list p1, unit_list p2, e1]
  have hn : n1 = n2 := by rw [unit_list n1, unit_list n2, e3]
  rw [hp, hn]

/-! ## Heads -/

/-- The read-only place projection (`walker` cursors): letters left of the head,
with the gap flag under the head. -/
def placeTape (p : Place) : STape Sym := ⟨p.letters.map sLet, sBit p.gap, []⟩

theorem placeTape_inj : Function.Injective placeTape := by
  intro a b h
  obtain ⟨l1, g1⟩ := a
  obtain ⟨l2, g2⟩ := b
  simp only [placeTape, STape.mk.injEq] at h
  obtain ⟨h1, h2, -⟩ := h
  rw [map_inj sLet_inj h1, sBit_inj h2]

/-- A `PlaceHead` stack as a zipper: letters left of the head, the current
cell, letters right of it. -/
def headZip (p : PlaceHead) : STape Sym :=
  ⟨p.head.left.map sOpt, sOpt p.head.focus, p.head.right.map sOpt⟩

/-- The rest of a `PlaceHead`: the incoming queue, with the gap flag under the
head. -/
def headAux (p : PlaceHead) : STape Sym :=
  ⟨p.head.incoming.map sLet, sBit p.gap, []⟩

theorem headPair_inj {p q : PlaceHead}
    (h1 : headZip p = headZip q) (h2 : headAux p = headAux q) : p = q := by
  obtain ⟨⟨f1, l1, r1, q1⟩, g1⟩ := p
  obtain ⟨⟨f2, l2, r2, q2⟩, g2⟩ := q
  simp only [headZip, headAux, STape.mk.injEq] at h1 h2
  obtain ⟨hl, hf, hr⟩ := h1
  obtain ⟨hi, hg, -⟩ := h2
  rw [sOpt_inj hf, map_inj sOpt_inj hl, map_inj sOpt_inj hr,
    map_inj sLet_inj hi, sBit_inj hg]

/-! ## `ProgLang` tapes -/

/-- A `ProgLang` tape is already zipper-shaped; it is taken over as-is. -/
def dpTape (t : GalilScaffoldTape.Tape) : STape Sym :=
  ⟨t.left.map sDp, sDp t.focus, t.right.map sDp⟩

theorem dpTape_inj : Function.Injective dpTape := by
  intro a b h
  obtain ⟨l1, f1, r1⟩ := a
  obtain ⟨l2, f2, r2⟩ := b
  simp only [dpTape, STape.mk.injEq] at h
  obtain ⟨hl, hf, hr⟩ := h
  rw [map_inj sDp_inj hl, sDp_inj hf, map_inj sDp_inj hr]

/-! ## The finite control -/

/-- Code of the search mode. -/
def smodeCode : PalPeg.GalilScaffoldSearchFinish.Mode → Fin 11
  | .idle => 0 | .grow => 1 | .lower => 2 | .lowerHome => 3 | .copy => 4
  | .home => 5 | .run => 6 | .found => 7 | .missed => 8 | .wait => 9 | .double => 10

def smodeOf : Fin 11 → PalPeg.GalilScaffoldSearchFinish.Mode
  | 0 => .idle | 1 => .grow | 2 => .lower | 3 => .lowerHome | 4 => .copy
  | 5 => .home | 6 => .run | 7 => .found | 8 => .missed | 9 => .wait | 10 => .double

theorem smodeCode_inj : Function.Injective smodeCode := by
  have h : ∀ m, smodeOf (smodeCode m) = m := by intro m; cases m <;> rfl
  exact Function.LeftInverse.injective h

def fmodeCode : FppControl.Mode → Fin 3
  | .copy => 0 | .home => 1 | .run => 2

def fmodeOf : Fin 3 → FppControl.Mode
  | 0 => .copy | 1 => .home | 2 => .run

theorem fmodeCode_inj : Function.Injective fmodeCode := by
  have h : ∀ m, fmodeOf (fmodeCode m) = m := by intro m; cases m <;> rfl
  exact Function.LeftInverse.injective h

/-- The finite control of the scaffold: the controller record without its
ℕ-valued clock, the search mode/stage/quarter, the fpp mode and `done` flags,
and `periodOnly`. -/
abbrev CtlFin : Type :=
  GalilScaffoldController.Mode × Bool × Bool × Bool × Bool ×
    Fin 11 × Bool × Fin 4 × Fin 3 × Bool × Bool × Bool × Bool

instance : Fintype CtlFin := inferInstance

def encodeCtl (x : State GalilVM) : CtlFin :=
  (x.ctl.mode, x.ctl.output, x.ctl.replaying, x.ctl.odd, x.ctl.pair,
    smodeCode x.vm.search.mode, x.vm.search.finalStage, x.vm.search.quarter,
    fmodeCode x.vm.fpp.mode, x.vm.fpp.program.done, x.vm.fpp.finalStage,
    x.vm.dp.done, x.vm.periodOnly)

/-! ## The tape layout -/

/-- The VM tapes.  Layout: heads `0–5`, the search walker `6`, the counters
`7–12`, the search counters `13–15`, the fpp counter/walker/pc `16–18`, the DP
pc `19`, the nine fpp program tapes `20–28`, the twelve DP tapes `29–40`. -/
def encodeVM (v : GalilVM) : Fin 41 → STape Sym
  | 0 => headZip v.left
  | 1 => headAux v.left
  | 2 => headZip v.center
  | 3 => headAux v.center
  | 4 => headZip v.right
  | 5 => headAux v.right
  | 6 => placeTape v.walker
  | 7 => ctrTape v.cycle
  | 8 => ctrTape v.remaining
  | 9 => ctrTape v.radius
  | 10 => ctrTape v.length
  | 11 => ctrTape v.replay
  | 12 => ctrTape v.lower
  | 13 => ctrTape v.search.span
  | 14 => ctrTape v.search.work
  | 15 => ctrTape v.search.debt
  | 16 => ctrTape v.fpp.work
  | 17 => placeTape v.fpp.walker
  | 18 => natTape v.fpp.program.config.pc
  | 19 => natTape v.dp.config.pc
  | 20 => dpTape (v.fpp.program.config.tapes 0)
  | 21 => dpTape (v.fpp.program.config.tapes 1)
  | 22 => dpTape (v.fpp.program.config.tapes 2)
  | 23 => dpTape (v.fpp.program.config.tapes 3)
  | 24 => dpTape (v.fpp.program.config.tapes 4)
  | 25 => dpTape (v.fpp.program.config.tapes 5)
  | 26 => dpTape (v.fpp.program.config.tapes 6)
  | 27 => dpTape (v.fpp.program.config.tapes 7)
  | 28 => dpTape (v.fpp.program.config.tapes 8)
  | 29 => dpTape (v.dp.config.tapes 0)
  | 30 => dpTape (v.dp.config.tapes 1)
  | 31 => dpTape (v.dp.config.tapes 2)
  | 32 => dpTape (v.dp.config.tapes 3)
  | 33 => dpTape (v.dp.config.tapes 4)
  | 34 => dpTape (v.dp.config.tapes 5)
  | 35 => dpTape (v.dp.config.tapes 6)
  | 36 => dpTape (v.dp.config.tapes 7)
  | 37 => dpTape (v.dp.config.tapes 8)
  | 38 => dpTape (v.dp.config.tapes 9)
  | 39 => dpTape (v.dp.config.tapes 10)
  | 40 => dpTape (v.dp.config.tapes 11)
  | _ => ⟨[], blank, []⟩

/-- The full tape layout: tape `0` carries the controller clock in unary (the
one ℕ-valued controller field), the rest is `encodeVM`. -/
def encodeState (x : State GalilVM) : Fin 42 → STape Sym :=
  Fin.cons (natTape x.ctl.clock) (encodeVM x.vm)


/-! ## Injectivity -/

/-- The tape layout together with the finite control determines the scaffold
state, apart from the one component this file does not encode: the chain view
`GalilVM.chain`, which is carried along abstractly.  Everything else — the three
`PlaceHead`s, the search walker, all nine counters, the search record, the fpp
controller with its nine-tape `ProgLang` machine, the twelve-tape DP machine,
and the controller record including its ℕ-valued clock — is recovered. -/
theorem encode_injective :
    Function.Injective
      (fun x : State GalilVM => (encodeCtl x, x.vm.chain, encodeState x)) := by
  intro x y h
  obtain ⟨⟨cmode1, clock1, out1, rep1, odd1, pair1⟩,
    ⟨left1, center1, right1, chain1, cycle1, remaining1, radius1, length1, replay1,
      ⟨fmode1, ⟨⟨fpc1, ftapes1⟩, fdone1⟩, fwork1, fwalker1, ffinal1⟩,
      ⟨smode1, sfinal1, sspan1, swork1, sdebt1, squarter1⟩,
      ⟨⟨dpc1, dtapes1⟩, ddone1⟩, lower1, periodOnly1, walker1⟩⟩ := x
  obtain ⟨⟨cmode2, clock2, out2, rep2, odd2, pair2⟩,
    ⟨left2, center2, right2, chain2, cycle2, remaining2, radius2, length2, replay2,
      ⟨fmode2, ⟨⟨fpc2, ftapes2⟩, fdone2⟩, fwork2, fwalker2, ffinal2⟩,
      ⟨smode2, sfinal2, sspan2, swork2, sdebt2, squarter2⟩,
      ⟨⟨dpc2, dtapes2⟩, ddone2⟩, lower2, periodOnly2, walker2⟩⟩ := y
  simp only [Prod.mk.injEq] at h
  obtain ⟨hc, hchain, hs⟩ := h
  subst hchain
  -- the finite control
  simp only [encodeCtl, Prod.mk.injEq] at hc
  obtain ⟨hm, ho, hrep, hodd, hpair, hsm, hsf, hsq, hfm, hfd, hff, hdd, hpo⟩ := hc
  subst hm; subst ho; subst hrep; subst hodd; subst hpair
  subst hsf; subst hsq; subst hfd; subst hff; subst hdd; subst hpo
  obtain rfl := smodeCode_inj hsm
  obtain rfl := fmodeCode_inj hfm
  -- the clock, on tape 0
  have h0 : natTape clock1 = natTape clock2 := by
    have := congrFun hs 0
    simpa [encodeState] using this
  obtain rfl := natTape_inj h0
  -- the VM tapes
  have hv : encodeVM
      ⟨left1, center1, right1, chain1, cycle1, remaining1, radius1, length1, replay1,
        ⟨fmode1, ⟨⟨fpc1, ftapes1⟩, fdone1⟩, fwork1, fwalker1, ffinal1⟩,
        ⟨smode1, sfinal1, sspan1, swork1, sdebt1, squarter1⟩,
        ⟨⟨dpc1, dtapes1⟩, ddone1⟩, lower1, periodOnly1, walker1⟩ =
      encodeVM
      ⟨left2, center2, right2, chain1, cycle2, remaining2, radius2, length2, replay2,
        ⟨fmode1, ⟨⟨fpc2, ftapes2⟩, fdone1⟩, fwork2, fwalker2, ffinal1⟩,
        ⟨smode1, sfinal1, sspan2, swork2, sdebt2, squarter1⟩,
        ⟨⟨dpc2, dtapes2⟩, ddone1⟩, lower2, periodOnly1, walker2⟩ := by
    funext i
    have := congrFun hs i.succ
    simpa [encodeState] using this
  have e0 : headZip left1 = headZip left2 := congrFun hv 0
  have e1 : headAux left1 = headAux left2 := congrFun hv 1
  have e2 : headZip center1 = headZip center2 := congrFun hv 2
  have e3 : headAux center1 = headAux center2 := congrFun hv 3
  have e4 : headZip right1 = headZip right2 := congrFun hv 4
  have e5 : headAux right1 = headAux right2 := congrFun hv 5
  have e6 : placeTape walker1 = placeTape walker2 := congrFun hv 6
  have e7 : ctrTape cycle1 = ctrTape cycle2 := congrFun hv 7
  have e8 : ctrTape remaining1 = ctrTape remaining2 := congrFun hv 8
  have e9 : ctrTape radius1 = ctrTape radius2 := congrFun hv 9
  have e10 : ctrTape length1 = ctrTape length2 := congrFun hv 10
  have e11 : ctrTape replay1 = ctrTape replay2 := congrFun hv 11
  have e12 : ctrTape lower1 = ctrTape lower2 := congrFun hv 12
  have e13 : ctrTape sspan1 = ctrTape sspan2 := congrFun hv 13
  have e14 : ctrTape swork1 = ctrTape swork2 := congrFun hv 14
  have e15 : ctrTape sdebt1 = ctrTape sdebt2 := congrFun hv 15
  have e16 : ctrTape fwork1 = ctrTape fwork2 := congrFun hv 16
  have e17 : placeTape fwalker1 = placeTape fwalker2 := congrFun hv 17
  have e18 : natTape fpc1 = natTape fpc2 := congrFun hv 18
  have e19 : natTape dpc1 = natTape dpc2 := congrFun hv 19
  have e20 : dpTape (ftapes1 0) = dpTape (ftapes2 0) := congrFun hv 20
  have e21 : dpTape (ftapes1 1) = dpTape (ftapes2 1) := congrFun hv 21
  have e22 : dpTape (ftapes1 2) = dpTape (ftapes2 2) := congrFun hv 22
  have e23 : dpTape (ftapes1 3) = dpTape (ftapes2 3) := congrFun hv 23
  have e24 : dpTape (ftapes1 4) = dpTape (ftapes2 4) := congrFun hv 24
  have e25 : dpTape (ftapes1 5) = dpTape (ftapes2 5) := congrFun hv 25
  have e26 : dpTape (ftapes1 6) = dpTape (ftapes2 6) := congrFun hv 26
  have e27 : dpTape (ftapes1 7) = dpTape (ftapes2 7) := congrFun hv 27
  have e28 : dpTape (ftapes1 8) = dpTape (ftapes2 8) := congrFun hv 28
  have e29 : dpTape (dtapes1 0) = dpTape (dtapes2 0) := congrFun hv 29
  have e30 : dpTape (dtapes1 1) = dpTape (dtapes2 1) := congrFun hv 30
  have e31 : dpTape (dtapes1 2) = dpTape (dtapes2 2) := congrFun hv 31
  have e32 : dpTape (dtapes1 3) = dpTape (dtapes2 3) := congrFun hv 32
  have e33 : dpTape (dtapes1 4) = dpTape (dtapes2 4) := congrFun hv 33
  have e34 : dpTape (dtapes1 5) = dpTape (dtapes2 5) := congrFun hv 34
  have e35 : dpTape (dtapes1 6) = dpTape (dtapes2 6) := congrFun hv 35
  have e36 : dpTape (dtapes1 7) = dpTape (dtapes2 7) := congrFun hv 36
  have e37 : dpTape (dtapes1 8) = dpTape (dtapes2 8) := congrFun hv 37
  have e38 : dpTape (dtapes1 9) = dpTape (dtapes2 9) := congrFun hv 38
  have e39 : dpTape (dtapes1 10) = dpTape (dtapes2 10) := congrFun hv 39
  have e40 : dpTape (dtapes1 11) = dpTape (dtapes2 11) := congrFun hv 40
  have hft : ftapes1 = ftapes2 := by
    funext i
    fin_cases i
    · exact dpTape_inj e20
    · exact dpTape_inj e21
    · exact dpTape_inj e22
    · exact dpTape_inj e23
    · exact dpTape_inj e24
    · exact dpTape_inj e25
    · exact dpTape_inj e26
    · exact dpTape_inj e27
    · exact dpTape_inj e28
  have hdt : dtapes1 = dtapes2 := by
    funext i
    fin_cases i
    · exact dpTape_inj e29
    · exact dpTape_inj e30
    · exact dpTape_inj e31
    · exact dpTape_inj e32
    · exact dpTape_inj e33
    · exact dpTape_inj e34
    · exact dpTape_inj e35
    · exact dpTape_inj e36
    · exact dpTape_inj e37
    · exact dpTape_inj e38
    · exact dpTape_inj e39
    · exact dpTape_inj e40
  obtain rfl := headPair_inj e0 e1
  obtain rfl := headPair_inj e2 e3
  obtain rfl := headPair_inj e4 e5
  obtain rfl := placeTape_inj e6
  obtain rfl := ctrTape_inj e7
  obtain rfl := ctrTape_inj e8
  obtain rfl := ctrTape_inj e9
  obtain rfl := ctrTape_inj e10
  obtain rfl := ctrTape_inj e11
  obtain rfl := ctrTape_inj e12
  obtain rfl := ctrTape_inj e13
  obtain rfl := ctrTape_inj e14
  obtain rfl := ctrTape_inj e15
  obtain rfl := ctrTape_inj e16
  obtain rfl := placeTape_inj e17
  obtain rfl := natTape_inj e18
  obtain rfl := natTape_inj e19
  subst hft
  subst hdt
  rfl

#print axioms encode_injective

end PalPeg.GalilVMEncode
