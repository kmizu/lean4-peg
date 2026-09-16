import PalPeg.TextFeedInput
import PalPeg.ProgLangCallFrame

/-! Atomic queue calls and individual scanner instructions for the text
feeder. A scanner loop is not an atomic operation: each of its primitive
instructions is a separate call. The bound 47 is independent of the pattern
and queue lengths. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedAtomic
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.ProgLangPersist
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueControl PalPeg.RTQueueClosed PalPeg.RTQueueDequeue
open PalPeg.TextFeedControl PalPeg.TextFeedTiming PalPeg.TextFeedInput

variable {k : ℕ} {Terminal : Type}

inductive Label (k : ℕ) where
  | idle
  | enqueue (a : Fin k)
  | supply
  | scan (a : GSProg.Act8)
  deriving DecidableEq, Fintype

def allowed (mark : Fin k) : Label k → Prop
  | .enqueue a => a ≠ mark
  | _ => True

noncomputable def low (blank mark : Fin k) : Label k → RP k
  | .idle => .skip
  | .enqueue a => liftWorker (lift (liftQueue (RTQueueControl.enqueue blank mark a)))
  | .supply => liftWorker (lift (supplyNonempty blank mark))
  | .scan a => liftWorker (lift (liftScan (.act a)))

def supplyEffect (e : Env k) (q : Queue (Fin k)) (S : Stage k) :
    Queue (Fin k) × Stage k :=
  let a := (toList q).head?.getD e.mark
  if a = e.mark then (q, S)
  else (RTQueue.tail q, changeStage e.blank S GSTapes.tT a .stay)

def effect (e : Env k) (a : Label k) (q : Queue (Fin k)) (S : Stage k) :
    Queue (Fin k) × Stage k :=
  match a with
  | .idle => (q, S)
  | .enqueue a => (snoc q a, S)
  | .supply => supplyEffect e q S
  | .scan a => (q, applyTrace e.blank S
      [actVec (GSProg.I8 (Terminal := Unit) e.blank e.endSym e.mark e.startSym) a S])

/-- Supplying an empty FIFO is a no-op on the scanner. The queue probe still
takes two physical actions; a nonempty supply takes at most 47. -/
theorem supply_bounded {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (h : Ready e.blank e.mark qt m q) (S : Stage k) :
    ∃ n qt' m', n ≤ 47 ∧
      Executes (Terminal := Terminal) e (supplyNonempty e.blank e.mark)
        qt m S n qt' m' (supplyEffect e q S).2 ∧
      Ready e.blank e.mark qt' m' (supplyEffect e q S).1 := by
  by_cases he : (toList q).head?.getD e.mark = e.mark
  · refine ⟨2, qt, m, by omega, ?_, ?_⟩
    · simpa only [supplyEffect, if_pos he] using supply_empty_runs hc h S he
    · simpa only [supplyEffect, if_pos he] using h
  · obtain ⟨n, qt', m', hn, hd, hr⟩ := dequeue_ready (Terminal := Terminal) hc hmb h
    have hw := executes_write (Terminal := Terminal) (e := e) qt m S GSTapes.tT
      ((toList q).head?.getD e.mark) .stay
    have hx := executes_seq hw (executes_queue (e := e)
      (changeStage e.blank S GSTapes.tT ((toList q).head?.getD e.mark) .stay) hd)
    refine ⟨2 + (1 + n), qt', m', by omega, ?_, ?_⟩
    · unfold supplyNonempty
      apply executes_peek (n := 1 + n) hc h
      rw [if_neg he]
      simpa only [supplyEffect, if_neg he] using hx
    · simpa only [supplyEffect, if_neg he] using hr

/-- Uniform low-call bound and queue safety on arbitrary scanner tapes,
including tapes in the middle of a long GS loop. -/
theorem low_bounded {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (h : Ready e.blank e.mark qt m q) (S : Stage k) (old : Fin k)
    (a : Label k) (ha : allowed e.mark a) :
    ∃ n qt' m', n ≤ 47 ∧
      RExec (Terminal := Terminal) e (low e.blank e.mark a)
        qt m S old n qt' m' (effect e a q S).2 ∧
      Ready e.blank e.mark qt' m' (effect e a q S).1 := by
  cases a with
  | idle => exact ⟨0, qt, m, by omega, ⟨[], exec_skip _, rfl, rfl⟩, h⟩
  | enqueue a =>
    obtain ⟨n, qt', m', hn, he, hr⟩ := enqueue_ready (Terminal := Terminal) hc hmb h ha
    exact ⟨n, qt', m', by omega,
      rexec_lift old (texec_lift (executes_queue S he)), hr⟩
  | supply =>
    obtain ⟨n, qt', m', hn, he, hr⟩ := supply_bounded (Terminal := Terminal) hc hmb h S
    exact ⟨n, qt', m', hn, rexec_lift old (texec_lift he), hr⟩
  | scan a =>
    have he := exec_act (I := GSProg.I8 (Terminal := Terminal)
      e.blank e.endSym e.mark e.startSym) (blank := e.blank)
      (GSProg.inputFree_I8 e.blank e.endSym e.mark e.startSym) a S
    exact ⟨1, qt, m, by omega,
      rexec_lift old (texec_lift (executes_scan qt m he)), h⟩

/-- info: 'PalPeg.TextFeedAtomic.low_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms low_bounded

abbrev Index (k : ℕ) := Fin (Fintype.card (Label k))

noncomputable def decode (i : Index k) : Label k := (Fintype.equivFin (Label k)).symm i

noncomputable def programs (blank mark : Fin k) : Index k → RP k :=
  fun i => low blank mark (decode i)

noncomputable def interp (e : Env k) :
    InterpF Terminal (AP k ⊕ Empty) (CT k ⊕ Fin k) (Fin k) 20 where
  toInterp := IR e
  flagOf _ := none

attribute [local irreducible] ProgLangBank.runChunk

/-- Every atomic feeder call fits 48 execution clocks plus one restart.
Its input register is preserved, and the FIFO is Ready even if the scanner
is suspended inside a loop. -/
theorem call_ready {D : Type} {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank)
    (choose : D → (Fin 20 → Fin k) → D × Index k)
    (x : ProgLangBank.CallCtrl (programs e.blank e.mark) D × (Fin 20 → STape (Fin k)))
    (hb : ProgLangBank.AtBoundary (programs e.blank e.mark) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (S : Stage k) (old : Fin k)
    (hx : x.2 = rtapes e qt m S old) (h : Ready e.blank e.mark qt m q)
    (ha : allowed e.mark (decode (choose x.1.1 (fun j => (x.2 j).focus)).2)) :
    let a := decode (choose x.1.1 (fun j => (x.2 j).focus)).2
    let y := ProgLangBank.callRun (programs e.blank e.mark)
      (fun _ => interp (Terminal := Terminal) e) choose 48 e.blank x
    ∃ qt' m', y.2 = rtapes e qt' m' (effect e a q S).2 old ∧
      ProgLangBank.AtBoundary (programs e.blank e.mark) y.1.2.2.1 ∧
      Ready e.blank e.mark qt' m' (effect e a q S).1 := by
  let i := (choose x.1.1 (fun j => (x.2 j).focus)).2
  obtain ⟨n, qt', m', hn, he, hr⟩ := low_bounded (Terminal := Terminal)
    hc hmb h S old (decode i) ha
  obtain ⟨tr, he, hlen, hout⟩ := he
  have hex : Exec (interp (Terminal := Terminal) e).toInterp e.blank
      (programs e.blank e.mark i) x.2 tr := by
    rw [hx]; exact he
  obtain ⟨ht, hb', _, _⟩ := ProgLangBank.callRun_exec (programs e.blank e.mark)
    (fun _ => interp (Terminal := Terminal) e) choose 48 e.blank x hb tr hex (by omega)
  rw [hx, hout] at ht
  exact ⟨qt', m', ht, hb', hr⟩

/-- info: 'PalPeg.TextFeedAtomic.call_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms call_ready

end PalPeg.TextFeedAtomic
