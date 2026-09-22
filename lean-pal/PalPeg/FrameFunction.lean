import PalPeg.GalilRunSkeleton
import PalPeg.TickFunction
import PalPeg.GalilTickFair
import PalPeg.GalilSharedFunctional
import PalPeg.GalilScaffoldTopLens
import PalPeg.GalilScaffoldTopScan
import PalPeg.GalilScaffoldTopShift
import PalPeg.GalilScaffoldTopFallback
import PalPeg.GalilScaffoldTopMarks
import PalPeg.GalilScaffoldTopRewind
import PalPeg.GalilScaffoldTopReplay
import PalPeg.GalilScaffoldTopSearch
import PalPeg.GalilScaffoldTopFpp

/-!
# The frame of the Galil controller, as functions

`TickFunction` reduces one controller tick to the value of `tickFun` on a `FrameFun` — a frame
whose relations are functions and whose predicates are Boolean tests.  This file builds that
`FrameFun` for the concrete frame `galilFrameS (PofC …)` and proves `Computes`.

The work splits three ways.

* The relations that are already equations (`copyEnd`, `fppStart`, the mark and rewind units, …)
  are read off: their proofs are `h` or `h.2`.
* The relations with an existential (`shiftOne`, `copyOne`, the chain and search steps, the two
  chain guards) have that existential pinned by a constructor or by an `Option`, so a `match`
  computes them.
* The program machines (the DP quantum of the search, the fpp slice) are runs of
  `GalilScaffoldControl.Tick`, which is functional once the `read` dispatch tables are
  single-valued (`GalilTickDet.ReadFun`, by `decide` for both codes).

Everything is stated in the direction a simulation needs: *whenever the relation has a
successor, it is the value of the function.*  The relations can be stuck — a left move at the
left edge, a `read` with no entry for the symbol under the head — and the run supplies the
successor; the function only has to agree with it.  The one relation that genuinely admits
several successors, the fallback entry, is pinned by the scheduling policy
(`GalilTickFair.Canonical.fallbackPlace`), which arrives as the `Pin` argument of `Computes`.
-/

set_option autoImplicit false

namespace PalPeg.ProgramFunction

open PalPeg.GalilFppWide (Instruction)
open PalPeg.GalilScaffoldProgram (Config Execute changed)
open PalPeg.GalilScaffoldControl (Machine Tick Run)
open PalPeg.GalilTickDet (ReadFun mem_of_getElem?)

/-- one instruction, as a function.  A stuck instruction keeps the configuration. -/
def executeFun {n : ℕ} : Instruction n → Config n → Config n
  | .halt, x => x
  | .move t true pc, x => changed x t (PalPeg.GalilScaffoldTape.moveRight (x.tapes t)) pc
  | .move t false pc, x => changed x t (PalPeg.GalilScaffoldTape.moveLeft (x.tapes t)) pc
  | .write t s pc, x => changed x t (PalPeg.GalilScaffoldTape.write (x.tapes t) s) pc
  | .read t cs, x =>
      match cs.find? (fun choice => choice.1 = (x.tapes t).focus) with
      | some choice => { x with pc := choice.2 }
      | none => x

theorem execute_eq_executeFun {n : ℕ} {code : List (Instruction n)} (hrf : ReadFun code)
    {x y : Config n} {i : Instruction n} (hi : code[x.pc]? = some i) (h : Execute i x y) :
    y = executeFun i x := by
  cases h with
  | right _ t pc => rfl
  | left _ t pc hl => rfl
  | write _ t s pc => rfl
  | read _ t cs pc hmem =>
    show _ = (match cs.find? (fun choice => choice.1 = (x.tapes t).focus) with
      | some choice => { x with pc := choice.2 }
      | none => x)
    cases hfind : cs.find? (fun choice => choice.1 = (x.tapes t).focus) with
    | none =>
      have := List.find?_eq_none.mp hfind _ hmem
      simp at this
    | some choice =>
      have hchoice := List.find?_some hfind
      have hmemChoice := List.mem_of_find?_eq_some hfind
      have hfocus : choice.1 = (x.tapes t).focus := by simpa using hchoice
      have hpc := hrf t cs (mem_of_getElem? hi) (x.tapes t).focus pc choice.2 hmem
        (by rw [← hfocus]; exact hmemChoice)
      show ({ x with pc := pc } : Config n) = { x with pc := choice.2 }
      rw [hpc]

/-- one call of the program machine, as a function. -/
def tickFun {n : ℕ} (code : List (Instruction n)) (enabled : Bool) (x : Machine n) : Machine n :=
  if enabled = false ∨ x.done = true then x
  else
    match code[x.config.pc]? with
    | some .halt => ⟨x.config, true⟩
    | some i => ⟨executeFun i x.config, false⟩
    | none => x

theorem tick_eq_tickFun {n : ℕ} {code : List (Instruction n)} (hrf : ReadFun code)
    {enabled : Bool} {x y : Machine n} (h : Tick code enabled x y) :
    y = tickFun code enabled x := by
  cases h with
  | idle _ _ hidle =>
    unfold tickFun
    rw [if_pos hidle]
  | halt config hi =>
    unfold tickFun
    rw [if_neg (by simp)]
    show _ = (match code[config.pc]? with
      | some .halt => (⟨config, true⟩ : Machine n)
      | some i => ⟨executeFun i config, false⟩
      | none => ⟨config, false⟩)
    rw [hi]
  | execute config target i hi he =>
    unfold tickFun
    rw [if_neg (by simp)]
    show _ = (match code[config.pc]? with
      | some .halt => (⟨config, true⟩ : Machine n)
      | some i => ⟨executeFun i config, false⟩
      | none => ⟨config, false⟩)
    rw [hi]
    cases i with
    | halt => cases he
    | move t right pc => rw [execute_eq_executeFun hrf hi he]
    | write t s pc => rw [execute_eq_executeFun hrf hi he]
    | read t cs => rw [execute_eq_executeFun hrf hi he]

/-- a run of the program machine, as a function. -/
def runFun {n : ℕ} (code : List (Instruction n)) : List Bool → Machine n → Machine n
  | [], x => x
  | b :: bs, x => runFun code bs (tickFun code b x)

theorem run_eq_runFun {n : ℕ} {code : List (Instruction n)} (hrf : ReadFun code) :
    ∀ {x y : Machine n} {bs : List Bool}, Run code x bs y → y = runFun code bs x := by
  intro x y bs h
  induction h with
  | nil x => rfl
  | cons x y z b bs hs hr ih =>
    have hy := tick_eq_tickFun hrf hs
    subst hy
    exact ih

/-- the enabled run of `q` calls of the marked fpp code. -/
def fppRunFun (q : ℕ) (x : Machine 9) : Machine 9 :=
  runFun PalPeg.GalilFppMarkedCode.code (List.replicate q true) x

set_option maxRecDepth 40000 in
theorem readFun_marked : ReadFun PalPeg.GalilFppMarkedCode.code :=
  PalPeg.GalilTickFair.readFun_of_b (by decide)

theorem fppRun_eq {q : ℕ} {x y : Machine 9}
    (h : Run PalPeg.GalilFppMarkedCode.code x (List.replicate q true) y) : y = fppRunFun q x :=
  run_eq_runFun readFun_marked h

/-- the slice of the fpp program a tick runs, and whether it reaches the halt. -/
def fppHaltsTest (q : ℕ) (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) : Bool := (fppRunFun q x.program).done

def fppSliceFun (q : ℕ) (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) : PalPeg.GalilScaffoldChainInputSupply.FppControl.State :=
  {x with program := fppRunFun q x.program}

def fppDoneFun (q : ℕ) (first : Fin 9) (x : PalPeg.GalilScaffoldChainInputSupply.FppControl.State) : PalPeg.GalilScaffoldChainInputSupply.FppControl.State :=
  {x with program := PalPeg.GalilScaffoldChainInputSupply.markNew (fppRunFun q x.program) first}

theorem fppSlice_eq {q : ℕ} {first : Fin 9} {onLetter leftFirst : PalPeg.GalilScaffoldChainInputSupply.FppControl.State → Prop}
    {x y : PalPeg.GalilScaffoldChainInputSupply.FppControl.State}
    (h : (PalPeg.GalilScaffoldChainInputSupply.fppFrame q first onLetter leftFirst).fppSlice x y) :
    fppHaltsTest q x = false ∧ y = fppSliceFun q x := by
  obtain ⟨-, hrun, hdone, hstate⟩ := h
  have hvalue : y.program = fppRunFun q x.program := fppRun_eq hrun
  refine ⟨?_, ?_⟩
  · show (fppRunFun q x.program).done = false
    rw [← hvalue]
    exact hdone
  · show y = {x with program := fppRunFun q x.program}
    rw [← hvalue]
    exact hstate

theorem fppDone_eq {q : ℕ} {first : Fin 9} {onLetter leftFirst : PalPeg.GalilScaffoldChainInputSupply.FppControl.State → Prop}
    {x y : PalPeg.GalilScaffoldChainInputSupply.FppControl.State}
    (h : (PalPeg.GalilScaffoldChainInputSupply.fppFrame q first onLetter leftFirst).fppDone x y) :
    fppHaltsTest q x = true ∧ y = fppDoneFun q first x := by
  obtain ⟨-, landed, hrun, hdone, hstate⟩ := h
  have hvalue : landed = fppRunFun q x.program := fppRun_eq hrun
  subst hvalue
  exact ⟨hdone, hstate⟩

end PalPeg.ProgramFunction

namespace PalPeg.ProgramFunction

open PalPeg.GalilFppWide (Instruction)
open PalPeg.GalilScaffoldProgram (Config Execute changed)
open PalPeg.GalilScaffoldControl (Machine Tick)
open PalPeg.GalilTickDet (ReadFun mem_of_getElem?)

open PalPeg.ProgramFunction (tickFun tick_eq_tickFun)


open PalPeg.GalilScaffoldSearchRun (SafeCalls SafeQuanta advance)
open PalPeg.GalilScaffoldSearchFinish (finish)

/-- The calls of a quantum, as a function. -/
def callsFun : List Bool → PalPeg.GalilScaffoldSearchFinish.State → Machine 12 →
    PalPeg.GalilScaffoldSearchFinish.State × Machine 12
  | [], s, x => (s, x)
  | b :: bs, s, x =>
      callsFun bs
        (finish s (b && decide (s.mode = .run))
          (tickFun PalPeg.GalilDpCode.code (b && decide (s.mode = .run)) x).done
          (tickFun PalPeg.GalilDpCode.code (b && decide (s.mode = .run)) x).config.pc)
        (tickFun PalPeg.GalilDpCode.code (b && decide (s.mode = .run)) x)

theorem safeCalls_eq_callsFun {s t : PalPeg.GalilScaffoldSearchFinish.State} {x y : Machine 12}
    {bs : List Bool} (h : SafeCalls s x bs t y) : (t, y) = callsFun bs s x := by
  induction h with
  | nil s x => rfl
  | cons s x y z b bs t ht hsafe hr ih =>
    have hy := tick_eq_tickFun PalPeg.GalilTickFair.readFun_code ht
    subst hy
    exact ih

/-- The run quantum of one scan tick, as a function: 64 calls and the outer advance. -/
def quantumFun (a : Bool) (s : PalPeg.GalilScaffoldSearchFinish.State) (x : Machine 12) :
    PalPeg.GalilScaffoldSearchFinish.State × Machine 12 :=
  (advance a (callsFun (List.replicate 64 true) s x).1, (callsFun (List.replicate 64 true) s x).2)

theorem safeQuanta_eq_quantumFun {a : Bool} {s t : PalPeg.GalilScaffoldSearchFinish.State}
    {x y : Machine 12} (h : SafeQuanta s x [a] t y) : (t, y) = quantumFun a s x := by
  cases h with
  | cons _ u _ _ middle _ _ _ hm hq hr =>
    cases hr with
    | nil =>
      have hcalls := safeCalls_eq_callsFun hq
      unfold quantumFun
      rw [← hcalls]

end PalPeg.ProgramFunction
namespace PalPeg.GalilScaffoldPrepareControl

open PalPeg.GalilScaffoldTape (moveRight moveLeft write)

/-- one enabled preparation tick, as a function of the state.  A stuck state is kept. -/
def tickFun (x : State) : State :=
  match x.mode with
  | .lower =>
      if GalilScaffoldCounter.positive x.work = true then
        {x with program := tape x 10 (fun t => moveRight (write t 8)), work := GalilScaffoldCounter.dec x.work}
      else {x with program := tape x 10 (fun t => write t 5), mode := .lowerHome}
  | .lowerHome =>
      if (x.program.config.tapes 10).focus = 4 then
        {x with program := tape x 7 (fun t => moveRight (write t 4)), work := GalilScaffoldCounter.inc x.span, mode := .copy}
      else {x with program := tape x 10 moveLeft}
  | .copy =>
      match GalilScaffoldPlace.read x.walker with
      | some a =>
          if GalilScaffoldCounter.zero x.work = false then
            {x with program := tape x 7 (fun t => moveRight (write t (GalilFppPreparation.symbol a))), work := GalilScaffoldCounter.dec x.work, walker := GalilScaffoldPlace.left x.walker}
          else {x with program := tape x 7 (fun t => write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}
      | none => {x with program := tape x 7 (fun t => write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}
  | .home =>
      if (x.program.config.tapes 7).focus = 4 then
        {x with program := GalilScaffoldControl.start 320 x.program, mode := .run}
      else {x with program := tape x 7 moveLeft}
  | _ => x

theorem tick_eq_tickFun {x y : State} (h : Tick true x y) : y = tickFun x := by
  cases h with
  | lowerBit _ hm hp => unfold tickFun; rw [hm]; simp only [hp, if_true]
  | lowerEnd _ hm hp => unfold tickFun; rw [hm]; simp [hp]
  | lowerLeft _ hm hf hl => unfold tickFun; rw [hm]; simp only [if_neg hf]
  | beginCopy _ hm hf => unfold tickFun; rw [hm]; simp only [if_pos hf]
  | copyBit _ a hm ha hw => unfold tickFun; rw [hm]; simp only [ha, hw, if_true]
  | copyEnd _ hm he =>
    unfold tickFun; rw [hm]
    rcases he with hnone | hzero
    · simp only [hnone]
    · cases hread : GalilScaffoldPlace.read x.walker with
      | none => simp only []
      | some a => simp [hzero]
  | sourceLeft _ hm hf hl => unfold tickFun; rw [hm]; simp only [if_neg hf]
  | startRun _ hm hf => unfold tickFun; rw [hm]; simp only [if_pos hf]

end PalPeg.GalilScaffoldPrepareControl
namespace PalPeg.GalilScaffoldChainInputSupply

/-- the background call of the search, as a function. -/
def searchStepFun (center : GalilScaffoldPlace.Place) (a : Bool) (v : SearchVM) : SearchVM :=
  match v.search.mode with
  | .idle | .found | .missed => v
  | .grow =>
      if GalilScaffoldCounter.positive v.search.work = true then
        SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldStagePrepare.growStep v.toPrep)) v.search.quarter v.lower
      else
        SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower
  | .lower | .lowerHome | .copy | .home =>
      SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
        (GalilScaffoldPrepareControl.tickFun v.toPrep)) v.search.quarter v.lower
  | .run =>
      {v with search := (PalPeg.ProgramFunction.quantumFun a v.search v.dp).1,
              dp := (PalPeg.ProgramFunction.quantumFun a v.search v.dp).2}
  | .wait =>
      {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.waitStep true v.search)}
  | .double =>
      if GalilScaffoldCounter.positive v.search.work = true then
        {v with search := GalilScaffoldSearchRun.advance a (GalilScaffoldDouble.step v.search)}
      else
        SearchVM.ofPrep (GalilScaffoldPreparePaced.afterAdvance a
          (GalilScaffoldPrepareControl.prepare v.toPrep v.lower center)) v.search.quarter v.lower

theorem searchStep_eq_searchStepFun {center : GalilScaffoldPlace.Place} {a : Bool}
    {v v' : SearchVM} (h : searchStep center a v v') : v' = searchStepFun center a v := by
  unfold searchStep at h
  unfold searchStepFun
  cases hmode : v.search.mode <;> simp only [hmode] at h ⊢
  all_goals first
    | exact h
    | (by_cases hpositive : GalilScaffoldCounter.positive v.search.work = true
       · rw [if_pos hpositive] at h ⊢
         exact h
       · rw [if_neg hpositive] at h ⊢
         exact h)
    | (obtain ⟨y, htick, hv⟩ := h
       rw [hv, GalilScaffoldPrepareControl.tick_eq_tickFun htick])
    | (obtain ⟨hquanta, hlower, hwalker⟩ := h
       have hpair := PalPeg.ProgramFunction.safeQuanta_eq_quantumFun hquanta
       cases v'
       cases v
       simp only at hlower hwalker hpair ⊢
       subst hlower hwalker
       rw [← hpair])

/-- the search effect of a scan tick, as a function. -/
def searchEffectFun (P : Shared) (a : Bool) (s : GalilVM) : SearchVM :=
  match s.chain with
  | .idle => searchStepFun (P.place s) a (searchLens.get s)
  | _ => searchLens.get s

theorem searchEffect_eq_searchEffectFun {P : Shared} {a : Bool} {s : GalilVM} {vq : SearchVM}
    (h : searchEffect P a s vq) : vq = searchEffectFun P a s := by
  unfold searchEffectFun
  rcases h with ⟨hidle, hstep⟩ | ⟨hactive, hsame⟩
  · rw [hidle]
    exact searchStep_eq_searchStepFun hstep
  · cases hchain : s.chain <;> first
      | exact absurd hchain hactive
      | exact hsame

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- the verdict of `consume()` on a watching chain: the period symbol against the input
under the moved verifier. -/
def watchVerdict (w : GalilScaffoldChainWatch.State) : Option Bool :=
  match GalilScaffoldChainConsume.symbol w.machine.control.period.focus with
  | some a => some (decide (GalilScaffoldInputHead.read (right w.machine.verifier) = some a))
  | none => none

theorem watchVerdict_of_good {w : GalilScaffoldChainWatch.State}
    (hg : GalilScaffoldChainWatch.Good w) : watchVerdict w = some true := by
  obtain ⟨-, a, hsym, hread⟩ := hg
  unfold watchVerdict
  rw [hsym]
  simp [hread]

theorem watchVerdict_of_mismatch {w : GalilScaffoldChainWatch.State} {a : Fin 3}
    (hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a)
    (hread : GalilScaffoldInputHead.read (right w.machine.verifier) ≠ some a) :
    watchVerdict w = some false := by
  unfold watchVerdict
  rw [hsym]
  simp [hread]

/-- one background chain step, as a function.  A stuck chain is kept. -/
def chainStepFun : ChainVM → ChainVM
  | .idle => .idle
  | .broken w => .broken w
  | .copy t h p v lag margin ver =>
      if t.focus = 8 then
        match GalilScaffoldPlace.read (GalilScaffoldPlace.left p) with
        | some a =>
            .copy (GalilScaffoldTape.moveLeft t) (inc h) (GalilScaffoldPlace.left p)
              (GalilScaffoldChainPeriod.put v a) lag (GalilScaffoldChainCredits.decFour margin) ver
        | none => .copy t h p v lag margin ver
      else if t.focus = 4 then
        match v.focus with
        | .plain b => .back (GalilScaffoldChainPeriod.write v (.last b)) h lag margin ver
        | _ => .copy t h p v lag margin ver
      else .copy t h p v lag margin ver
  | .back v h lag margin ver =>
      if GalilScaffoldChainPeriod.isFirst v.focus = true then
        .watch ⟨⟨ver, watchControl v⟩, lag, margin⟩
      else .back (GalilScaffoldChainPeriod.moveLeft v) h lag margin ver
  | .watch w =>
      if positive w.lag = true then
        match watchVerdict w with
        | some true => .watch (GalilScaffoldChainWatch.caught w)
        | some false =>
            .broken ⟨⟨GalilScaffoldChainVerifier.right w.machine.verifier, w.machine.control⟩,
              w.lag, w.margin⟩
        | none => .watch w
      else .watch w

theorem chainStep_eq_chainStepFun {x y : ChainVM} (h : ChainStep x y) : y = chainStepFun x := by
  cases h with
  | idle => rfl
  | brokenIdle w => rfl
  | copyBit t h p v lag margin ver a one legal present =>
    simp only [chainStepFun, if_pos one, present]
  | copyEnd t h p v lag margin ver b hleft hp hv =>
    have hne : ¬ t.focus = 8 := by rw [hleft]; decide
    simp only [chainStepFun, if_neg hne, if_pos hleft, hv]
  | backStep v h lag margin ver hf => simp [chainStepFun, hf]
  | backDone v h lag margin ver hf => simp [chainStepFun, hf]
  | watchStep w w' ht =>
    cases ht with
    | idle hz => simp [chainStepFun, hz]
    | take hp hg => simp [chainStepFun, hp, watchVerdict_of_good hg]
  | watchBreak w hb =>
    obtain ⟨hp, -, a, hsym, hread⟩ := hb
    simp [chainStepFun, hp, watchVerdict_of_mismatch hsym hread]

/-- `chain.matched()`, as a function. -/
def chainMatchedFun : ChainVM → ChainVM
  | .idle => .idle
  | .copy t h p v lag margin ver => .copy t h p v (inc lag) (inc margin) ver
  | .back v h lag margin ver => .back v h (inc lag) (inc margin) ver
  | .broken w => .broken ⟨w.machine, inc w.lag, inc w.margin⟩
  | .watch w =>
      if zero w.lag = true then
        match watchVerdict w with
        | some true => .watch (GalilScaffoldChainWatch.immediate w)
        | some false => .broken ⟨consume w.machine, w.lag, inc w.margin⟩
        | none => .watch w
      else .watch (GalilScaffoldChainWatch.queued w)

theorem chainMatched_eq_chainMatchedFun {x y : ChainVM} (h : ChainMatched x y) :
    y = chainMatchedFun x := by
  cases h with
  | idle => rfl
  | copy => rfl
  | back => rfl
  | brokenMatched w => rfl
  | watch w w' ho =>
    cases ho with
    | queued hz => simp [chainMatchedFun, hz]
    | immediate hz hg => simp [chainMatchedFun, hz, watchVerdict_of_good hg]
  | breaks w w' hb =>
    obtain ⟨hz, -, a, hsym, hread, hw'⟩ := hb
    simp [chainMatchedFun, hz, hw', watchVerdict_of_mismatch hsym hread]

/-- one chain tick on the match event `a`, as a function. -/
def chainTickFun (a : Bool) (x : ChainVM) : ChainVM :=
  if a then chainMatchedFun (chainStepFun x) else chainStepFun x

theorem chainTick_eq_chainTickFun {a : Bool} {x z : ChainVM} (h : ChainTick a x z) :
    z = chainTickFun a x := by
  obtain ⟨y, hstep, hcredit⟩ := h
  unfold chainTickFun
  rw [← chainStep_eq_chainStepFun hstep]
  cases a with
  | true => exact chainMatched_eq_chainMatchedFun hcredit
  | false => exact hcredit

/-- the chain effect of a comparison, as a function. -/
def chainAtFun (a : Bool) (found : Bool) (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (ver : GalilScaffoldInputHead.PlaceHead)
    (radius : GalilScaffoldCounter.Counter) (x : ChainVM) : ChainVM :=
  match x with
  | .idle =>
      if found then
        (if a then chainMatchedFun (chainStart answer c walker ver radius)
          else chainStart answer c walker ver radius)
      else .idle
  | active => chainTickFun a active

theorem chainAt_eq_chainAtFun {a found : Bool} {answer : GalilScaffoldTape.Tape} {c : Fin 3}
    {walker : GalilScaffoldPlace.Place} {ver : GalilScaffoldInputHead.PlaceHead}
    {radius : GalilScaffoldCounter.Counter} {x z : ChainVM}
    (h : chainAt a found answer c walker ver radius x z) :
    z = chainAtFun a found answer c walker ver radius x := by
  rcases h with ⟨hactive, htick⟩ | ⟨hidle, hfound, hz⟩ | ⟨hidle, hfound, hstart⟩
  · have hz := chainTick_eq_chainTickFun htick
    cases x <;> first
      | exact absurd rfl hactive
      | exact hz
  · subst hidle hfound hz
    rfl
  · subst hidle hfound
    cases a with
    | true => exact chainMatched_eq_chainMatchedFun hstart
    | false => exact hstart


/-- the background of a scan tick, as a function of the state. -/
def backgroundFun (P : Shared) (s : GalilVM) : GalilVM :=
  afterBirth (chainBorn (decide ((searchEffectFun P false s).search.mode = .found)) s.chain)
    (searchLens.set
      (scanLens.set s ⟨s.left, s.right,
        chainAtFun false (decide ((searchEffectFun P false s).search.mode = .found))
          ((searchEffectFun P false s).dp.config.tapes 11) (P.centre s) (P.place s) s.center
          s.radius s.chain⟩)
      (searchEffectFun P false s))

theorem backgroundS_eq_backgroundFun {P : Shared} {q : ℕ} {first : Fin 9} {s s' : GalilVM}
    (h : backgroundS P q first s s') : s' = backgroundFun P s := by
  obtain ⟨hleft, hright, hsearch, hchain, hstate⟩ := h
  have hvq := searchEffect_eq_searchEffectFun hsearch
  rw [hvq] at hchain hstate
  have hch := chainAt_eq_chainAtFun hchain
  have hscan : scanLens.get s' = ⟨s.left, s.right,
      chainAtFun false (decide ((searchEffectFun P false s).search.mode = .found))
        ((searchEffectFun P false s).dp.config.tapes 11) (P.centre s) (P.place s) s.center
        s.radius s.chain⟩ := by
    show (⟨s'.left, s'.right, s'.chain⟩ : ScanVM) = _
    rw [hleft, hright, hch]
  rw [hscan] at hstate
  exact hstate

end PalPeg.GalilScaffoldChainInputSupply


namespace PalPeg.GalilScaffoldChainInputSupply

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldInputHead (read left)
open PalPeg.GalilScaffoldChainVerifier (right)

/-- the comparison of a scan tick, as a function of the state. -/
def compareFun (P : Shared) (s : GalilVM) : GalilVM :=
  let headLeft := left s.left
  let headRight := right s.right
  let agree := decide (read headLeft = read headRight)
  let searched := searchEffectFun P agree s
  let born := decide (searched.search.mode = .found)
  let scanned : ScanVM := ⟨headLeft, headRight, chainAtFun agree born (searched.dp.config.tapes 11) (P.centre s) (P.place s) s.center s.radius s.chain⟩
  afterBirth (chainBorn born s.chain)
    (if agree then afterCompare s scanned searched else afterMismatch s scanned searched)

theorem compare_eq_compareFun {P : Shared} {q : ℕ} {first : Fin 9} {s t : GalilVM}
    (h : compareFound P q first s t) : t = compareFun P s := by
  obtain ⟨scanned, searched, agree, hleft, hright, hagree, hsearch, hchain, hvalue⟩ := h
  have hsearched : searched = searchEffectFun P agree s := searchEffect_eq_searchEffectFun hsearch
  subst hsearched
  have hscanned : scanned = ⟨left s.left, right s.right,
      chainAtFun agree (decide ((searchEffectFun P agree s).search.mode = .found))
        ((searchEffectFun P agree s).dp.config.tapes 11) (P.centre s) (P.place s) s.center
        s.radius s.chain⟩ := by
    have hchainValue := chainAt_eq_chainAtFun hchain
    cases scanned
    simp_all
  subst hscanned
  have hagreeValue : agree = decide (read (left s.left) = read (right s.right)) := by
    rw [Bool.eq_iff_iff, hagree, decide_eq_true_eq]
    exact Iff.rfl
  subst hagreeValue
  exact hvalue

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.FrameFunction

open PalPeg.GalilScaffoldTop (Frame)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (inc dec ofNat reset)
open PalPeg.GalilScaffoldChainVerifier (canRight right)

/-- **a relation pulled along a lens is a function as soon as it is one below.** -/
theorem lensRel_eq {σ σ' : Type} {L : PalPeg.GalilScaffoldTop.Lens σ σ'}
    {R : σ' → σ' → Prop} {f : σ' → σ'}
    (hf : ∀ v v', R v v' → v' = f v) {s t : σ} (h : L.rel R s t) :
    t = L.set s (f (L.get s)) := by
  obtain ⟨hR, ht⟩ := h
  rw [ht, ← hf _ _ hR]

/-! ### the shift unit -/

def shiftOneFun (s : ShiftVM) : ShiftVM :=
  match s.chain with
  | .watch w => ⟨shiftTick s.shift, .watch (chainShiftOne w), inc (inc s.cycle)⟩
  | _ => s

theorem shiftOne_eq {onLetter leftFirst : ShiftVM → Prop} {s s' : ShiftVM}
    (h : (shiftFrame onLetter leftFirst).shiftOne s s') : s' = shiftOneFun s := by
  obtain ⟨-, -, -, w, hchain, hvalue⟩ := h
  unfold shiftOneFun
  rw [hchain, hvalue]

/-! ### the units of the fallback copy -/

def copyOneFun (x : FppControl.State) : FppControl.State :=
  match GalilScaffoldPlace.read x.walker with
  | some a =>
      {x with program := FppControl.tape x 7 (fun t => GalilScaffoldTape.moveRight (GalilScaffoldTape.write t (GalilFppPreparation.symbol a))), work := dec x.work, walker := GalilScaffoldPlace.left x.walker}
  | none => x

theorem copyOne_eq {onLetter leftFirst : FppControl.State → Prop} {x y : FppControl.State}
    (h : (fallbackFrame onLetter leftFirst).copyOne x y) : y = copyOneFun x := by
  obtain ⟨a, hread, hvalue⟩ := h
  unfold copyOneFun
  rw [hread, hvalue]

def copyEndFun (x : FppControl.State) : FppControl.State :=
  {x with program := FppControl.tape x 7 (fun t => GalilScaffoldTape.write t 5), mode := .home, finalStage := (GalilScaffoldPlace.read x.walker).isNone}

theorem copyEnd_eq {onLetter leftFirst : FppControl.State → Prop} {x y : FppControl.State}
    (h : (fallbackFrame onLetter leftFirst).copyEnd x y) : y = copyEndFun x := h

def fppStartFun (x : FppControl.State) : FppControl.State :=
  {x with program := GalilScaffoldControl.start 320 x.program, mode := .run}

theorem fppStart_eq {onLetter leftFirst : FppControl.State → Prop} {x y : FppControl.State}
    (h : (fallbackFrame onLetter leftFirst).fppStart x y) : y = fppStartFun x := h

def homeStepFun (x : FppControl.State) : FppControl.State :=
  {x with program := FppControl.tape x 7 GalilScaffoldTape.moveLeft}

theorem homeStep_eq {onLetter leftFirst : FppControl.State → Prop} {x y : FppControl.State}
    (h : (fallbackFrame onLetter leftFirst).homeStep x y) : y = homeStepFun x := h.2

/-! ### the units of the mark walk -/

def markBackFun (x : RewindVM) : RewindVM :=
  {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft}

theorem markBack_eq {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} {x y : RewindVM}
    (h : (rewindFrame first onLetter leftFirst).markBack x y) : y = markBackFun x := h.2

def markForwardFun (x : FppControl.State) : FppControl.State :=
  markStep x GalilScaffoldTape.moveRight

theorem markForward_eq {first : Fin 9} {onLetter leftFirst : FppControl.State → Prop}
    {x y : FppControl.State} (h : (marksFrame first onLetter leftFirst).markForward x y) :
    y = markForwardFun x := h


/-! ### the units of the rewind -/

def chooseFun (x : RewindVM) : RewindVM :=
  {x with left := x.right, center := x.right, length := ofNat 1, radius := reset}

theorem choose_eq {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} {x y : RewindVM}
    (h : (rewindFrame first onLetter leftFirst).choose x y) : y = chooseFun x := h

def fppResetFun (x : RewindVM) : RewindVM :=
  {x with fpp := {x.fpp with program := GalilScaffoldControl.reset 320 x.fpp.program}}

theorem fppReset_eq {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} {x y : RewindVM}
    (h : (rewindFrame first onLetter leftFirst).fppReset x y) : y = fppResetFun x := h

def rewindOneFun (x : RewindVM) : RewindVM :=
  {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left x.left, length := inc x.length}

theorem rewindOne_eq {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} {x y : RewindVM}
    (h : (rewindFrame first onLetter leftFirst).rewindOne x y) : y = rewindOneFun x := h.2

def rewindPairFun (x : RewindVM) : RewindVM :=
  {x with fpp := markStep x.fpp GalilScaffoldTape.moveLeft, left := GalilScaffoldInputHead.left x.left, length := inc x.length, center := GalilScaffoldInputHead.left x.center, radius := inc x.radius}

theorem rewindPair_eq {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} {x y : RewindVM}
    (h : (rewindFrame first onLetter leftFirst).rewindPair x y) : y = rewindPairFun x := h.2

/-! ### the tests the guards read -/

def matchedTest (s : ScanVM) : Bool :=
  decide (GalilScaffoldInputHead.read s.left = GalilScaffoldInputHead.read s.right)

theorem matched_test {onLetter leftFirst : ScanVM → Prop} (s : ScanVM) :
    (scanFrame onLetter leftFirst).matched s ↔ matchedTest s = true := by
  unfold matchedTest
  simp [scanFrame]

def shiftRemainingTest (s : ShiftVM) : Bool := GalilScaffoldCounter.positive s.shift.remaining

theorem shiftRemaining_test {onLetter leftFirst : ShiftVM → Prop} (s : ShiftVM) :
    (shiftFrame onLetter leftFirst).remainingPos s ↔ shiftRemainingTest s = true := Iff.rfl

def copyRemainingTest (x : FppControl.State) : Bool :=
  !(GalilScaffoldPlace.read x.walker).isNone && !GalilScaffoldCounter.zero x.work

theorem copyRemaining_test {onLetter leftFirst : FppControl.State → Prop}
    (x : FppControl.State) :
    (fallbackFrame onLetter leftFirst).remainingPos x ↔ copyRemainingTest x = true := by
  unfold copyRemainingTest
  show (¬ (GalilScaffoldPlace.read x.walker = none ∨ GalilScaffoldCounter.zero x.work = true)) ↔ _
  cases hread : GalilScaffoldPlace.read x.walker <;>
    cases hzero : GalilScaffoldCounter.zero x.work <;> simp_all

def atLeftTest (x : FppControl.State) : Bool := decide ((x.program.config.tapes 7).focus = 4)

theorem atLeft_test {onLetter leftFirst : FppControl.State → Prop} (x : FppControl.State) :
    (fallbackFrame onLetter leftFirst).atLeft x ↔ atLeftTest x = true := by
  unfold atLeftTest
  simp [fallbackFrame]

def atEndTest (x : FppControl.State) : Bool := decide ((marksTape x).focus = 5)

theorem atEnd_test {first : Fin 9} {onLetter leftFirst : FppControl.State → Prop}
    (x : FppControl.State) :
    (marksFrame first onLetter leftFirst).atEnd x ↔ atEndTest x = true := by
  unfold atEndTest
  simp [marksFrame]

def markSetTest (first : Fin 9) (x : RewindVM) : Bool :=
  decide (x.marks.focus = 8) || decide (x.marks.focus = first)

theorem markSet_test {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} (x : RewindVM) :
    (rewindFrame first onLetter leftFirst).markSet x ↔ markSetTest first x = true := by
  unfold markSetTest
  simp [rewindFrame]

def atFirstTest (first : Fin 9) (x : RewindVM) : Bool := decide (x.marks.focus = first)

theorem atFirst_test {first : Fin 9} {onLetter leftFirst : RewindVM → Prop} (x : RewindVM) :
    (rewindFrame first onLetter leftFirst).atFirst x ↔ atFirstTest first x = true := by
  unfold atFirstTest
  simp [rewindFrame]

end PalPeg.FrameFunction

namespace PalPeg.GalilScaffoldChainInputSupply

open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilScaffoldTop (Frame)

/-- the tests of the frame that read the chain: the guard of a shift, and the guard of
the restart of a broken chain.  The watch state existentially quantified in each is pinned by
the constructor of the chain. -/
def shiftGuardTest (s : GalilVM) : Bool :=
  match s.chain with
  | .watch w =>
      zero w.lag && decide (w.machine.control.phase = 4) && !w.machine.control.broken &&
        (if s.periodOnly then singlePositive s.cycle else !negative w.margin) &&
        decide (GalilScaffoldChainConsume.symbol w.machine.control.period.focus = read s.right)
  | _ => false

theorem shiftGuardTest_iff (s : GalilVM) : shiftGuardVM s ↔ shiftGuardTest s = true := by
  unfold shiftGuardVM shiftGuardTest
  cases hchain : s.chain with
  | watch w =>
    constructor
    · rintro ⟨w', hw', hlag, hphase, hbroken, hmargin, hsym⟩
      injection hw' with hww
      subst hww
      cases hperiod : s.periodOnly <;> simp_all
    · intro htest
      refine ⟨w, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · revert htest
          cases hperiod : s.periodOnly <;> simp_all
  | idle => simp [hchain]
  | copy => simp [hchain]
  | back => simp [hchain]
  | broken => simp [hchain]

def restartGuardTest (s : GalilVM) : Bool :=
  match s.chain with
  | .broken w =>
      !negative w.margin && positive w.machine.control.last && zero w.lag
  | _ => false

theorem restartGuardTest_iff (s : GalilVM) : restartGuardVM s ↔ restartGuardTest s = true := by
  unfold restartGuardVM restartGuardTest
  cases hchain : s.chain with
  | broken w =>
    constructor
    · rintro ⟨w', hw', hmargin, hlast, hlag⟩
      injection hw' with hww
      subst hww
      simp_all
    · intro htest
      refine ⟨w, rfl, ?_, ?_, ?_⟩ <;> · revert htest; simp_all
  | idle => simp [hchain]
  | copy => simp [hchain]
  | back => simp [hchain]
  | watch => simp [hchain]

/-- the right head can advance. -/
def canRightTest (p : PlaceHead) : Bool :=
  !p.gap || !p.head.right.isEmpty || !p.head.incoming.isEmpty

theorem canRightTest_iff (p : PlaceHead) : canRight p ↔ canRightTest p = true := by
  unfold canRight canRightTest
  cases hgap : p.gap <;> cases hright : p.head.right <;> cases hincoming : p.head.incoming <;>
    simp_all

/-- the output is refreshed when the right head stands on a letter of the word: its
position is odd and within the word. -/
def onLetterTest (raw : List (Fin 2)) (s : GalilVM) : Bool :=
  decide (position s.right % 2 = 1) && decide (position s.right + 1 ≤ 2 * raw.length)

theorem onLetterTest_iff (raw : List (Fin 2)) (s : GalilVM) :
    onLetterVM raw s ↔ onLetterTest raw s = true := by
  unfold onLetterVM onLetterTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, hkle, hpos⟩
    omega
  · rintro ⟨hodd, hle⟩
    exact ⟨(position s.right + 1) / 2, by omega, by omega, by omega⟩

def leftFirstTest (s : GalilVM) : Bool := decide (position s.left = 1)

theorem leftFirstTest_iff (s : GalilVM) : leftFirstVM s ↔ leftFirstTest s = true := by
  unfold leftFirstVM leftFirstTest
  simp

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.GalilScaffoldChainInputSupply

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (inc ofNat reset)
open PalPeg.GalilScaffoldChainVerifier (right)

/-- the `init` entry, as a function.  `initVM` fixes all fifteen fields of `GalilVM`. -/
def initFun (entry : ℕ) (s : GalilVM) : GalilVM :=
  {s with right := right s.right, left := right s.right, center := right s.right, length := inc s.length, chain := .idle, search := GalilScaffoldSearchFinish.begin reset s.radius, lower := reset, dp := GalilScaffoldControl.reset entry s.dp}

theorem init_eq {entry : ℕ} {s t : GalilVM} (h : initVM entry s t) : t = initFun entry s := by
  obtain ⟨hright, hleft, hcentre, hlength, hradius, hremaining, hreplay, hcycle, hfpp, hchain,
    hsearch, hlower, hdp, hperiodOnly, hwalker⟩ := h
  cases t
  simp_all [initFun]

/-- the `replayStart` entry, as a function. -/
def replayStartFun (entry : ℕ) (s : GalilVM) : GalilVM :=
  {s with replay := s.radius, right := s.center, left := s.center, radius := reset, length := ofNat 1, chain := .idle, search := GalilScaffoldSearchFinish.begin reset reset, lower := reset, dp := GalilScaffoldControl.reset entry s.dp}

theorem replayStart_eq {entry : ℕ} {s t : GalilVM} (h : replayStartVM entry s t) :
    t = replayStartFun entry s := by
  obtain ⟨hreplay, hright, hleft, hcentre, hradius, hlength, hremaining, hcycle, hfpp, hchain,
    hsearch, hlower, hdp, hperiodOnly, hwalker⟩ := h
  cases t
  simp_all [replayStartFun]

end PalPeg.GalilScaffoldChainInputSupply

namespace PalPeg.FrameFunction

open PalPeg.GalilScaffoldTop (Frame FrameFun Computes)
open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldCounter (dec)
open PalPeg.GalilTickFair (rightPlace)
open PalPeg.ProgramFunction (fppHaltsTest fppSliceFun fppDoneFun fppSlice_eq fppDone_eq)
open PalPeg.GalilScaffoldChainInputSupply (compareFun compare_eq_compareFun)
open PalPeg.GalilScaffoldChainInputSupply (initFun init_eq replayStartFun replayStart_eq)
open PalPeg.FrameFunction

/-- **the frame of the Galil controller, as functions.** -/
noncomputable def galilFrameFun (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) : FrameFun GalilVM where
  init := initFun entry
  available := fun s => canRightTest s.right
  background := backgroundFun (PalPeg.GalilRunSkeleton.PofC centre place entry w)
  compare := compareFun (PalPeg.GalilRunSkeleton.PofC centre place entry w)
  matched := fun s => matchedTest (scanLens.get s)
  shiftGuard := shiftGuardTest
  matchedPlace := fun b s => if b then {s with replay := dec s.replay} else s
  onLetter := onLetterTest w
  leftFirst := leftFirstTest
  beginShift := beginShiftFun
  beginFallback := beginFallbackFun rightPlace
  remainingPos := fun s =>
    shiftRemainingTest (shiftLens.get s) || copyRemainingTest (fppLens.get s)
  shiftOne := fun s => shiftLens.set s (shiftOneFun (shiftLens.get s))
  copyOne := fun s => fppLens.set s (copyOneFun (fppLens.get s))
  copyEnd := fun s => fppLens.set s (copyEndFun (fppLens.get s))
  atLeft := fun s => atLeftTest (fppLens.get s)
  fppStart := fun s => fppLens.set s (fppStartFun (fppLens.get s))
  homeStep := fun s => fppLens.set s (homeStepFun (fppLens.get s))
  fppHalts := fun s => fppHaltsTest q (fppLens.get s)
  fppSlice := fun s => fppLens.set s (fppSliceFun q (fppLens.get s))
  fppDone := fun s => fppLens.set s (fppDoneFun q first (fppLens.get s))
  atEnd := fun s => atEndTest (fppLens.get s)
  markBack := fun s => rewindLens.set s (markBackFun (rewindLens.get s))
  markForward := fun s => fppLens.set s (markForwardFun (fppLens.get s))
  markSet := fun s => markSetTest first (rewindLens.get s)
  choose := fun s => rewindLens.set s (chooseFun (rewindLens.get s))
  atFirst := fun s => atFirstTest first (rewindLens.get s)
  fppReset := fun s => rewindLens.set s (fppResetFun (rewindLens.get s))
  rewindOne := fun s => rewindLens.set s (rewindOneFun (rewindLens.get s))
  rewindPair := fun s => rewindLens.set s (rewindPairFun (rewindLens.get s))
  replayStart := replayStartFun entry
  restartGuard := restartGuardTest
  restart := restartFun entry

/-- **The starvation test, as a Boolean function of the state.**  The machine has to decide for
itself whether the abstraction starves, so the test has to be one it can read off its window: it
factors through seven finite readings — the mode, whether each of the four heads can advance,
and the two remaining counters.  `ShadowedLocalFinal.starvedAbs_iff` identifies it with
`LocalSysConcrete.Starved` at the abstraction. -/
def starvedOf (mode : PalPeg.GalilScaffoldController.Mode)
    (rightCanMove centreCanMove leftCanMove verifierCanMove shiftRemains copyRemains : Bool) :
    Bool :=
  !((if mode = PalPeg.GalilScaffoldController.Mode.init ||
        mode = PalPeg.GalilScaffoldController.Mode.scan then rightCanMove else true) &&
    (if (mode = PalPeg.GalilScaffoldController.Mode.shift) && (shiftRemains || copyRemains) then
      centreCanMove && leftCanMove && verifierCanMove
     else true))

def starvedTest (x : PalPeg.GalilScaffoldTop.State GalilVM) : Bool :=
  starvedOf x.ctl.mode (canRightTest x.vm.right) (canRightTest x.vm.center)
    (canRightTest x.vm.left) (canRightTest (PalPeg.GalilScaffoldChainVerifier.right x.vm.left))
    (shiftRemainingTest (shiftLens.get x.vm)) (copyRemainingTest (fppLens.get x.vm))

/-- The shape `starvedTest` was built from, so that its reader can rewrite the guards one at a
time. -/
theorem starvedTest_iff (x : PalPeg.GalilScaffoldTop.State GalilVM) :
    starvedTest x = true ↔
      ¬ (((x.ctl.mode = PalPeg.GalilScaffoldController.Mode.init ∨
            x.ctl.mode = PalPeg.GalilScaffoldController.Mode.scan) →
          PalPeg.GalilScaffoldChainVerifier.canRight x.vm.right) ∧
        (x.ctl.mode = PalPeg.GalilScaffoldController.Mode.shift →
          ((shiftFrame (fun _ => True) (fun _ => True)).remainingPos (shiftLens.get x.vm) ∨
            (fallbackFrame (fun _ => True) (fun _ => True)).remainingPos (fppLens.get x.vm)) →
          PalPeg.GalilScaffoldChainVerifier.canRight x.vm.center ∧
            PalPeg.GalilScaffoldChainVerifier.canRight x.vm.left ∧
            PalPeg.GalilScaffoldChainVerifier.canRight
              (PalPeg.GalilScaffoldChainVerifier.right x.vm.left))) := by
  unfold starvedTest starvedOf
  have hright := canRightTest_iff x.vm.right
  have hcentre := canRightTest_iff x.vm.center
  have hleft := canRightTest_iff x.vm.left
  have hverifier := canRightTest_iff (PalPeg.GalilScaffoldChainVerifier.right x.vm.left)
  have hmoves := shiftRemaining_test (onLetter := fun _ => True) (leftFirst := fun _ => True)
    (shiftLens.get x.vm)
  have hcopy := copyRemaining_test (onLetter := fun _ => True) (leftFirst := fun _ => True)
    (fppLens.get x.vm)
  cases hmode : x.ctl.mode <;>
    cases hcentreValue : canRightTest x.vm.center <;>
    cases hleftValue : canRightTest x.vm.left <;>
    cases hverifierValue :
      canRightTest (PalPeg.GalilScaffoldChainVerifier.right x.vm.left) <;>
    cases hshiftValue : shiftRemainingTest (shiftLens.get x.vm) <;>
    cases hcopyValue : copyRemainingTest (fppLens.get x.vm) <;>
    simp_all

/-- **The functions compute the frame.** -/
theorem computes_galilFrameFun (centre : GalilVM → Fin 3)
    (place : GalilVM → GalilScaffoldPlace.Place) (entry q : ℕ) (first : Fin 9)
    (w : List (Fin 2)) (landed : GalilVM) :
    Computes (galilFrameS (PalPeg.GalilRunSkeleton.PofC centre place entry w) q first)
      (galilFrameFun centre place entry q first w)
      (fun s => s.fpp.walker = rightPlace s) landed where
  init := fun s h => init_eq h
  available := fun s => canRightTest_iff s.right
  background := fun s s' h => backgroundS_eq_backgroundFun (q := q) (first := first) h
  compare := fun s s' h => compare_eq_compareFun (q := q) (first := first) h
  matched := fun s => matched_test (onLetter := fun _ => True) (leftFirst := fun _ => True) (scanLens.get s)
  shiftGuard := fun s => shiftGuardTest_iff s
  matchedPlace := fun b s s' h => h
  onLetter := fun s => onLetterTest_iff w s
  leftFirst := fun s => leftFirstTest_iff s
  beginShift := fun s s' hguard h => beginShiftFun_eq hguard h
  beginFallback := fun s h hpinned => by
    obtain ⟨p, hvalue, -⟩ := h
    have hwalker : landed.fpp.walker = p := by
      rw [show landed = beginFallbackAt p s from hvalue]
      exact beginFallbackAt_walker p s
    have hkept : rightPlace landed = rightPlace s := by
      rw [show landed = beginFallbackAt p s from hvalue]
      rfl
    have hplace : p = rightPlace s := by rw [← hwalker, hpinned, hkept]
    show landed = beginFallbackAt (rightPlace s) s
    rw [← hplace]
    exact hvalue
  remainingPos := fun s => by
    show ((shiftFrame (fun _ => True) (fun _ => True)).remainingPos (shiftLens.get s) ∨
      (fallbackFrame (fun _ => True) (fun _ => True)).remainingPos (fppLens.get s)) ↔ _
    rw [shiftRemaining_test (onLetter := fun _ => True) (leftFirst := fun _ => True) (shiftLens.get s), copyRemaining_test (onLetter := fun _ => True) (leftFirst := fun _ => True) (fppLens.get s)]
    show _ ↔ (shiftRemainingTest (shiftLens.get s) || copyRemainingTest (fppLens.get s)) = true
    rw [Bool.or_eq_true]
  shiftOne := fun s s' h => lensRel_eq (fun v v' hv => shiftOne_eq hv) h
  copyOne := fun s s' h => lensRel_eq (fun v v' hv => copyOne_eq hv) h
  copyEnd := fun s s' h => lensRel_eq (fun v v' hv => copyEnd_eq hv) h
  atLeft := fun s => atLeft_test (onLetter := fun _ => True) (leftFirst := fun _ => True) (fppLens.get s)
  fppStart := fun s s' h => lensRel_eq (fun v v' hv => fppStart_eq hv) h
  homeStep := fun s s' h => lensRel_eq (fun v v' hv => homeStep_eq hv) h
  fppSlice := fun s s' h =>
    ⟨(fppSlice_eq h.1).1, lensRel_eq (fun v v' hv => (fppSlice_eq hv).2) h⟩
  fppDone := fun s s' h =>
    ⟨(fppDone_eq h.1).1, lensRel_eq (fun v v' hv => (fppDone_eq hv).2) h⟩
  atEnd := fun s => atEnd_test (first := first) (onLetter := fun _ => True) (leftFirst := fun _ => True) (fppLens.get s)
  markBack := fun s s' h => lensRel_eq (fun v v' hv => markBack_eq hv) h
  markForward := fun s s' h => lensRel_eq (fun v v' hv => markForward_eq hv) h
  markSet := fun s => markSet_test (first := first) (onLetter := fun _ => True) (leftFirst := fun _ => True) (rewindLens.get s)
  choose := fun s s' h => lensRel_eq (fun v v' hv => choose_eq hv) h
  atFirst := fun s => atFirst_test (first := first) (onLetter := fun _ => True) (leftFirst := fun _ => True) (rewindLens.get s)
  fppReset := fun s s' h => lensRel_eq (fun v v' hv => fppReset_eq hv) h
  rewindOne := fun s s' h => lensRel_eq (fun v v' hv => rewindOne_eq hv) h
  rewindPair := fun s s' h => lensRel_eq (fun v v' hv => rewindPair_eq hv) h
  replayStart := fun s h => replayStart_eq h
  restart := fun s s' h => by
    refine ⟨?_, restartFun_eq entry h⟩
    obtain ⟨watched, hchain, hmargin, hlast, hlag, -⟩ := h
    exact (restartGuardTest_iff s).mp ⟨watched, hchain, hmargin, hlast, hlag⟩

end PalPeg.FrameFunction

#print axioms PalPeg.FrameFunction.computes_galilFrameFun
