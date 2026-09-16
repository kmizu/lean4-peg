import PalPeg.TextFeedPipelineGuarded

/-! Static discharge of the text-write obligation for the actual GS
source, including reset chains, shift loops, and all zigzag directions. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineKeep
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangGuarded
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineGuarded
open PalPeg.GSTapes

variable {k : ℕ}

private def Keep8 (a : GSProg.Act8) : Prop := a.1 = tT → a.2.1 = true

private theorem keep8 (j : Fin 8) (mv : Move) : AllActs Keep8 (GSProg.KEEP j mv) := fun _ => rfl

private theorem put8 (j : Fin 8) (mv : Move) (hj : j ≠ tT) : AllActs Keep8 (GSProg.PUT j mv) :=
  fun he => False.elim (hj he)

private theorem sUpTail8 (i j : Fin 8) (hi : i ≠ tT) (hj : j ≠ tT) :
    AllActs Keep8 (GSProg.sUpTail i j) := ⟨put8 j .stay hj, keep8 j .right, put8 i .right hi⟩

private theorem sUpProg8 (i j : Fin 8) (hi : i ≠ tT) (hj : j ≠ tT) :
    AllActs Keep8 (GSProg.sUpProg i j) := ⟨put8 j .left hj, sUpTail8 i j hi hj⟩

private theorem qInc8 : AllActs Keep8 GSProg.qIncProg :=
  ⟨sUpProg8 tAp tAn (by decide) (by decide), sUpProg8 tRn tRp (by decide) (by decide)⟩

private theorem qDec8 : AllActs Keep8 GSProg.qDecProg :=
  ⟨sUpProg8 tAn tAp (by decide) (by decide), sUpProg8 tRp tRn (by decide) (by decide)⟩

private theorem qDecTail8 : AllActs Keep8 GSProg.qDecTail :=
  ⟨sUpTail8 tAn tAp (by decide) (by decide), sUpProg8 tRp tRn (by decide) (by decide)⟩

private theorem adv8 : AllActs Keep8 GSProg.advProg := ⟨keep8 tP .right, keep8 tT .right, qInc8⟩

private theorem perBody8 : AllActs Keep8 GSProg.perBody :=
  ⟨put8 tC2 .right (by decide), keep8 tP .left, qDec8, put8 tC1 .left (by decide)⟩

private theorem perDown8 : AllActs Keep8 GSProg.perDownLoop :=
  ⟨put8 tC1 .stay (by decide), perBody8⟩

private theorem perUp8 : AllActs Keep8 GSProg.perUpLoop :=
  ⟨put8 tC2 .stay (by decide), put8 tC1 .right (by decide), put8 tC2 .left (by decide)⟩

private theorem per8 : AllActs Keep8 GSProg.perProg :=
  ⟨put8 tC1 .left (by decide), perDown8, keep8 tC1 .right,
    put8 tC2 .left (by decide), perUp8, keep8 tC2 .right⟩

private theorem resChain8 : ∀ n, AllActs Keep8 (GSProg.resChain n) := by
  intro n
  induction n with
  | zero => exact keep8 tP .left
  | succ n ih => exact ⟨keep8 tP .left, ⟨keep8 tT .left, qDec8, ih⟩, trivial⟩

private theorem resLoop8 (rate : ℕ) : AllActs Keep8 (GSProg.resLoopProg rate) :=
  ⟨put8 tAp .left (by decide), qDecTail8, resChain8 (rate - 1)⟩

private theorem res8 (rate : ℕ) : AllActs Keep8 (GSProg.resProg rate) :=
  ⟨keep8 tP .left, ⟨resLoop8 rate, keep8 tP .right⟩, ⟨keep8 tP .right, keep8 tT .right⟩⟩

private theorem scan8 (rate : ℕ) : AllActs Keep8 (GSProg.scanProg rate) :=
  ⟨adv8, put8 tAn .left (by decide),
    ⟨keep8 tAn .right, put8 tRn .left (by decide), keep8 tRn .right, res8 rate⟩,
    keep8 tAn .right, put8 tRn .left (by decide),
    ⟨keep8 tRn .right, res8 rate⟩, ⟨keep8 tRn .right, per8⟩⟩

private theorem keep_fa (a : GSProg.Act8) : KeepText (GSVProg.fa a) ↔ Keep8 a := by
  constructor
  · intro h ht
    exact h.1 (congrArg GSVProg.e8 ht)
  · intro h
    constructor
    · intro ht
      apply h
      exact Fin.ext (congrArg (fun j : Fin 10 => j.val) ht)
    · intro hx
      exact False.elim (GSVProg.e8_ne_tX a.1 hx)

private theorem pmap_good {p : Prog GSProg.Act8 GSProg.Cond8} (hp : AllActs Keep8 p) :
    AllActs KeepText (GSVProg.pmap p) := by
  induction p with
  | skip => trivial
  | act a => exact (keep_fa a).mpr hp
  | seq p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | ite c p q ihp ihq => exact ⟨ihp hp.1, ihq hp.2⟩
  | loop c a b ihb => exact ⟨(keep_fa a).mpr hp.1, ihb hp.2⟩

private theorem keep10 (j : Fin 10) (mv : Move) : AllActs KeepText (GSVProg.KEEP10 j mv) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

private theorem perBodyPre8 : AllActs Keep8 GSVProg.perBodyPre :=
  ⟨put8 tC2 .right (by decide), keep8 tP .left, qDec8⟩

private theorem perBodyX : AllActs KeepText GSVProg.perBodyX :=
  ⟨pmap_good perBodyPre8, keep10 GSVProg.tX .right, pmap_good (put8 tC1 .left (by decide))⟩

private theorem perDownX : AllActs KeepText GSVProg.perDownLoopX :=
  ⟨(keep_fa _).mpr (put8 tC1 .stay (by decide)), perBodyX⟩

private theorem perX : AllActs KeepText GSVProg.perProgX :=
  ⟨pmap_good (put8 tC1 .left (by decide)), perDownX, pmap_good (keep8 tC1 .right),
    pmap_good (put8 tC2 .left (by decide)), pmap_good perUp8, pmap_good (keep8 tC2 .right)⟩

private theorem resLoopX (rate : ℕ) : AllActs KeepText (GSVProg.resLoopProgX rate) :=
  ⟨(keep_fa _).mpr (put8 tAp .left (by decide)), pmap_good qDecTail8,
    keep10 GSVProg.tX .right, pmap_good (resChain8 (rate - 1))⟩

private theorem resX (rate : ℕ) : AllActs KeepText (GSVProg.resProgX rate) :=
  ⟨pmap_good (keep8 tP .left), ⟨resLoopX rate, pmap_good (keep8 tP .right)⟩,
    ⟨pmap_good (keep8 tP .right), pmap_good (keep8 tT .right), keep10 GSVProg.tX .right⟩⟩

theorem shiftCore_good (rate : ℕ) : AllActs KeepText (GSVProg.shiftCore rate) :=
  ⟨pmap_good (put8 tAn .left (by decide)),
    ⟨pmap_good (keep8 tAn .right), pmap_good (put8 tRn .left (by decide)),
      pmap_good (keep8 tRn .right), resX rate⟩,
    pmap_good (keep8 tAn .right), pmap_good (put8 tRn .left (by decide)),
    ⟨pmap_good (keep8 tRn .right), resX rate⟩, ⟨pmap_good (keep8 tRn .right), perX⟩⟩

private theorem lift_good {p : Prog GSVProg.Act10 GSVProg.Cond10} (hp : AllActs KeepText p) :
    AllActs GSGood (GSVProgZLoop.lift p) := by
  rw [GSVProgZLoop.lift, all_map]
  exact hp

private theorem comp_good : AllActs KeepText GSVProg.vcompProg :=
  ⟨⟨keep10 GSVProg.tU .right, keep10 GSVProg.tX .right⟩, trivial⟩

theorem unitsReturn_good : ∀ n up, AllActs GSGood (GSVProgZLoop.unitsReturn n up) := by
  intro n
  induction n with
  | zero => intro up; trivial
  | succ n ih =>
    intro up
    cases up with
    | true => exact ⟨lift_good comp_good, ih true⟩
    | false => exact ⟨lift_good (keep10 GSVProg.tU .left),
        ⟨lift_good (keep10 GSVProg.tX .left), ih false⟩,
        ⟨lift_good (keep10 GSVProg.tU .right), ih true⟩⟩

theorem stepProg_good (rate : ℕ) : AllActs GSGood (GSVProgZLoop.stepProg rate) :=
  ⟨⟨lift_good (pmap_good (scan8 rate)), unitsReturn_good _ true, unitsReturn_good _ false⟩,
    lift_good (shiftCore_good rate), trivial⟩

/-- No text-preservation hypothesis is left to the caller: this is the
actual complete source, for every rate and every prepared pattern. -/
theorem task_safe (e : Env k) (leftSym : Fin k) (rate : ℕ) :
    Certified (Good (k := k)) (task e leftSym rate) :=
  task_certified e leftSym rate (stepProg_good rate)

/-- info: 'PalPeg.TextFeedPipelineKeep.stepProg_good' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepProg_good

/-- info: 'PalPeg.TextFeedPipelineKeep.task_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms task_safe

end PalPeg.TextFeedPipelineKeep
