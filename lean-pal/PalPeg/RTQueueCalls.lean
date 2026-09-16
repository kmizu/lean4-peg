import PalPeg.RTQueueSlots
import PalPeg.ProgLangCalls

/-! Head-symbol-selected queue calls, with a reusable bank boundary after
every call. Each call is realized by 46 physical microsteps. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueCalls
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueClosed PalPeg.RTQueueSlots

variable {k slots : ℕ} {Terminal D : Type}

noncomputable def programs (blank mark : Fin k) (ops : Fin slots → Op k) :
    Fin slots → CP k := fun i => operation blank mark (ops i)

attribute [local irreducible] ProgLangBank.runChunk

/-- The outer choice is evaluated at entry; even arbitrary finite outer
control may select a queue operation without exposing the abstract FIFO.
The abstract queue appears only in this correctness statement. -/
theorem call_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} (hmb : mark ≠ blank) (ops : Fin slots → Op k)
    (choose : D → (Fin 11 → Fin k) → D × Fin slots)
    (x : CallCtrl (programs blank mark ops) D × (Fin 11 → STape (Fin k)))
    (hb : AtBoundary (programs blank mark ops) x.1.2.2.1)
    {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (hx : x.2 = tapes code qt m) (h : Ready blank mark qt m q)
    (ha : allowed mark (ops (choose x.1.1 (fun j => (x.2 j).focus)).2)) :
    let y := callRun (programs blank mark ops)
      (fun _ => queueIF (Terminal := Terminal) code) choose 45 blank x
    ∃ qt' m', y.2 = tapes code qt' m' ∧
      AtBoundary (programs blank mark ops) y.1.2.2.1 ∧
      Ready blank mark qt' m'
        (Op.applyQ q (ops (choose x.1.1 (fun j => (x.2 j).focus)).2)) := by
  let i := (choose x.1.1 (fun j => (x.2 j).focus)).2
  obtain ⟨n, qt', m', hn, he, hr⟩ := operation_ready (Terminal := Terminal)
    hc hmb h (ops i) ha
  obtain ⟨tr, he, hlen, hout⟩ := he
  have hex : Exec (queueIF (Terminal := Terminal) code).toInterp blank
      (programs blank mark ops i) x.2 tr := by
    rw [hx]; exact he
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs blank mark ops)
    (fun _ => queueIF (Terminal := Terminal) code) choose 45 blank x hb tr hex
    (by omega)
  rw [hx, hout] at ht
  exact ⟨qt', m', ht, hb', hr⟩

/-- info: 'PalPeg.RTQueueCalls.call_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms call_ready

end PalPeg.RTQueueCalls
