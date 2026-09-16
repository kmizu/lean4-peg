import PalPeg.TextFeedPrefixControl
import PalPeg.TextFeedAtomic

/-! Every alignment source instruction is a bounded call. In particular,
the source cannot be suspended inside a FIFO supply operation. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixAtomic
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedTiming
open PalPeg.GSVProgZLoop (RunsTo)

variable {k : ℕ} {Terminal : Type}

inductive Act where
  | idle | supply | textRight | uMove (mv : Move)
  deriving DecidableEq, Fintype

inductive Cond where
  | blankText | notEndU | notStartU
  deriving DecidableEq, Fintype

def source : Prog Act Cond :=
  .seq (.loop .notEndU .idle
    (.seq (.act .supply) (.ite .blankText .skip (.seq (.act (.uMove .right)) (.act .textRight)))))
    (.seq (.loop .notStartU (.uMove .left) .skip) (.act (.uMove .right)))

noncomputable def low (e : Env k) : Act → TextFeedPrefixControl.PProg k
  | .idle => .act (.inr .stay)
  | .supply => TextFeedPrefixControl.lift (TextFeedTiming.lift (supplyNonempty e.blank e.mark))
  | .textRight => TextFeedPrefixControl.lift TextFeedAlign.moveRight
  | .uMove mv => .act (.inr mv)

def eval (e : Env k) (σ : Fin 20 → Fin k) : Cond → Bool
  | .blankText => decide (σ 12 = e.blank)
  | .notEndU => decide (σ 19 ≠ e.endSym)
  | .notStartU => decide (σ 19 ≠ e.startSym)

structure Model (k : ℕ) where
  q : Queue (Fin k)
  S : Stage k
  U : TapeConfiguration k

def effect (e : Env k) (a : Act) (D : Model k) : Model k :=
  match a with
  | .idle => D
  | .supply =>
    let z := TextFeedAtomic.supplyEffect e D.q D.S
    ⟨z.1, z.2, D.U⟩
  | .textRight =>
    { D with S := (applyTrace e.blank D.S
      [actVec (GSProg.I8 (Terminal := Unit) e.blank e.endSym e.mark e.startSym)
        (GSTapes.tT, true, .right) D.S]) }
  | .uMove mv => { D with U := Tape.step e.blank D.U D.U.focus mv }

def tapes (e : Env k) (qt : QT k) (m : Mode) (D : Model k) : Fin 20 → STape (Fin k) :=
  TextFeedPrefixControl.tapes (TextFeedControl.tapes e qt m D.S) D.U

theorem low_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (a : Act) (D : Model k) {qt : QT k} {m : Mode} (hq : Ready e.blank e.mark qt m D.q) :
    ∃ ticks qt' m', ticks ≤ 47 ∧
      RunsTo (TextFeedPrefixControl.interp (Terminal := Terminal) e) e.blank (low e a)
        (tapes e qt m D) (tapes e qt' m' (effect e a D)) ticks ∧
      Ready e.blank e.mark qt' m' (effect e a D).q := by
  cases a with
  | idle =>
    exact ⟨1, qt, m, by omega,
      TextFeedPrefixControl.moveU_runs e (TextFeedControl.tapes e qt m D.S) D.U .stay, hq⟩
  | uMove mv =>
    exact ⟨1, qt, m, by omega,
      TextFeedPrefixControl.moveU_runs e (TextFeedControl.tapes e qt m D.S) D.U mv, hq⟩
  | supply =>
    obtain ⟨ticks, qt', m', hlen, he, hr⟩ := TextFeedAtomic.supply_bounded (Terminal := Terminal) hc hmb hq D.S
    obtain ⟨tr, he', hn, ht⟩ := texec_lift he
    exact ⟨ticks, qt', m', hlen, TextFeedPrefixControl.lift_runs ⟨tr, he', ht, hn⟩ D.U, hr⟩
  | textRight =>
    have he := exec_act (I := GSProg.I8 (Terminal := Terminal) e.blank e.endSym e.mark e.startSym)
      (blank := e.blank) (GSProg.inputFree_I8 e.blank e.endSym e.mark e.startSym)
      (GSTapes.tT, true, .right) D.S
    obtain ⟨tr, he', hn, ht⟩ := texec_lift (executes_scan qt m he)
    exact ⟨1, qt, m, by omega, TextFeedPrefixControl.lift_runs ⟨tr, he', ht, hn⟩ D.U, hq⟩

def modelEval (e : Env k) (D : Model k) : Cond → Bool
  | .blankText => decide ((D.S GSTapes.tT).focus = e.blank)
  | .notEndU => decide (D.U.focus ≠ e.endSym)
  | .notStartU => decide (D.U.focus ≠ e.startSym)

theorem eval_tapes (e : Env k) (qt : QT k) (m : Mode) (D : Model k) :
    eval e (fun j => (tapes e qt m D j).focus) = modelEval e D := by
  funext c
  cases c <;> rfl

/-- info: 'PalPeg.TextFeedPrefixAtomic.low_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms low_matches

end PalPeg.TextFeedPrefixAtomic
