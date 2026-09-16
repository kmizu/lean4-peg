import PalPeg.RTQueueClosed
import PalPeg.ProgLangTransaction

/-! Fixed 45-tick transaction slots. The scheduler may switch at a slot
boundary without observing a partially performed queue operation. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueSlots

open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg
open PalPeg.RTQueueDispatch PalPeg.RTQueueControl PalPeg.RTQueueClosed

variable {k : ℕ} {Terminal : Type}

def slotInputs (Terminal : Type) : List (Option Terminal) := List.replicate 45 none

noncomputable def slotRun (code : Mode → Fin k) (blank mark : Fin k) (op : Op k)
    (T : Fin 11 → STape (Fin k)) :=
  runInputs (IC Terminal code) blank (slotInputs Terminal) ([operation blank mark op], T)

/-- At most 44 actions plus one normalization tick. At the boundary the
continuation is literally empty and the queue is Ready again. -/
theorem slotRun_ready {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} (hmb : mark ≠ blank) {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    (h : Ready blank mark qt m q) (op : Op k) (ha : allowed mark op) :
    ∃ qt' m',
      (slotRun (Terminal := Terminal) code blank mark op (tapes code qt m)).2 = tapes code qt' m' ∧
      (slotRun (Terminal := Terminal) code blank mark op (tapes code qt m)).1 = [] ∧
      Ready blank mark qt' m' (Op.applyQ q op) := by
  obtain ⟨n, qt', m', hn, he, hr⟩ := operation_ready (Terminal := Terminal) hc hmb h op ha
  obtain ⟨tr, he, hlen, hout⟩ := he
  have hb : tr.length < (slotInputs Terminal).length := by
    simp only [slotInputs, List.length_replicate]; omega
  have hs := he.runInputs_gt (slotInputs Terminal) hb
  rw [hout] at hs
  exact ⟨qt', m', congrArg Prod.snd hs, congrArg Prod.fst hs, hr⟩

noncomputable def queueIF (code : Mode → Fin k) :
    InterpF Terminal (ActQ k ⊕ Mode) (CondQ k ⊕ Mode) (Fin k) 11 where
  toInterp := IC Terminal code
  flagOf _ := none

/-- A fixed queue slot within the existing finite continuation bank. All
other continuations stay unchanged; the selected one reaches an empty
boundary. The premise explicitly requires a fresh transaction entry. -/
theorem bank_slot_ready {slots : ℕ} {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} (hmb : mark ≠ blank)
    (progs : Fin slots → CP k) (i : Fin slots) (op : Op k) (ha : allowed mark op)
    (hp : progs i = operation blank mark op)
    (x : (ProgLangBank.Bank progs × Bool) × (Fin 11 → STape (Fin k)))
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (hx : x.2 = tapes code qt m)
    (hstart : (x.1.1 i).val = [progs i]) (h : Ready blank mark qt m q) :
    ∃ qt' m',
      (ProgLangBank.runChunk progs (fun _ => queueIF (Terminal := Terminal) code) blank i
        (slotInputs Terminal) x).2 = tapes code qt' m' ∧
      ((ProgLangBank.runChunk progs (fun _ => queueIF (Terminal := Terminal) code) blank i
          (slotInputs Terminal) x).1.1 i).val = [] ∧
      (∀ j, j ≠ i → (ProgLangBank.runChunk progs
        (fun _ => queueIF (Terminal := Terminal) code) blank i (slotInputs Terminal) x).1.1 j =
          x.1.1 j) ∧ Ready blank mark qt' m' (Op.applyQ q op) := by
  obtain ⟨n, qt', m', hn, he, hr⟩ := operation_ready (Terminal := Terminal) hc hmb h op ha
  obtain ⟨tr, he, hlen, hout⟩ := he
  have hex : Exec (queueIF (Terminal := Terminal) code).toInterp blank (progs i) x.2 tr := by
    rw [hp, hx]; exact he
  have hb : tr.length < (slotInputs Terminal).length := by
    simp only [slotInputs, List.length_replicate]; omega
  obtain ⟨ht, hs⟩ := ProgLangBank.runChunk_exec_lt progs
    (fun _ => queueIF (Terminal := Terminal) code) blank i (slotInputs Terminal) x tr
    hstart hex hb
  rw [hx, hout] at ht
  exact ⟨qt', m', ht, hs,
    fun j hj => ProgLangBank.runChunk_other progs _ blank i j hj (slotInputs Terminal) x, hr⟩

/-- info: 'PalPeg.RTQueueSlots.slotRun_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms slotRun_ready

/-- info: 'PalPeg.RTQueueSlots.bank_slot_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bank_slot_ready

-- Keep the fixed 45-tick run opaque during dependent-control elaboration.
-- Its operational effect is supplied by bank_slot_ready, not recomputed.
attribute [local irreducible] ProgLangBank.runChunk

noncomputable def transact {slots : ℕ} (progs : Fin slots → CP k)
    (code : Mode → Fin k) (blank : Fin k) (i : Fin slots)
    (x : (ProgLangBank.Bank progs × Bool) × (Fin 11 → STape (Fin k))) :=
  ProgLangBank.runChunk progs (fun _ => queueIF (Terminal := Terminal) code)
    blank i (slotInputs Terminal) (ProgLangBank.restartDone progs i x)

/-- A reusable transaction entry/exit contract. The caller supplies a finite
entry index, not the queue value or role map. A completed entry may be reused;
an unfinished continuation cannot satisfy the entry premise. -/
theorem transact_ready {slots : ℕ} {code : Mode → Fin k} (hc : Function.Injective code)
    {blank mark : Fin k} (hmb : mark ≠ blank)
    (progs : Fin slots → CP k) (i : Fin slots) (op : Op k) (ha : allowed mark op)
    (hp : progs i = operation blank mark op)
    (x : (ProgLangBank.Bank progs × Bool) × (Fin 11 → STape (Fin k)))
    {qt : QT k} {m : Mode} {q : Queue (Fin k)} (hx : x.2 = tapes code qt m)
    (hentry : (x.1.1 i).val = []) (h : Ready blank mark qt m q) :
    ∃ qt' m', (transact (Terminal := Terminal) progs code blank i x).2 = tapes code qt' m' ∧
      ((transact (Terminal := Terminal) progs code blank i x).1.1 i).val = [] ∧
      (∀ j, j ≠ i → (transact (Terminal := Terminal) progs code blank i x).1.1 j = x.1.1 j) ∧
      Ready blank mark qt' m' (Op.applyQ q op) := by
  let x1 := ProgLangBank.restartDone progs i x
  have hx1eq : x1 = ((Function.update x.1.1 i (startCtrlS (progs i)), x.1.2), x.2) :=
    ProgLangBank.restartDone_eq progs i x hentry
  have hx1 : x1.2 = tapes code qt m := by
    rw [hx1eq]; exact hx
  have hstart : (x1.1.1 i).val = [progs i] := by
    rw [hx1eq]
    simp only [Function.update_self, startCtrlS]
  obtain ⟨qt', m', ht, hs, ho, hr⟩ := bank_slot_ready (Terminal := Terminal)
    hc hmb progs i op ha hp x1 hx1 hstart h
  refine ⟨qt', m', ht, hs, ?_, hr⟩
  intro j hj
  change (ProgLangBank.runChunk progs (fun _ => queueIF (Terminal := Terminal) code) blank i
    (slotInputs Terminal) x1).1.1 j = _
  rw [ho j hj]
  rw [hx1eq]
  simp only [Function.update_of_ne hj]

/-- info: 'PalPeg.RTQueueSlots.transact_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms transact_ready

/-- The reusable queue transaction is a block of 46 genuine finite-control
phases: one guarded restart and 45 execution ticks. No input is consumed by
this internal block; an enclosing input scheduler is a separate obligation. -/
theorem phaseRun_transact {slots : ℕ} (progs : Fin slots → CP k)
    (code : Mode → Fin k) (blank : Fin k) (i : Fin slots)
    (x : (ProgLangBank.Bank progs × Bool) × (Fin 11 → STape (Fin k))) :
    phaseRun blank (ProgLangBank.transactionBody progs
      (fun _ => queueIF (Terminal := Terminal) code) (by omega : 0 < 46) i)
      (none :: slotInputs Terminal) ⟨0, by omega⟩ x =
        transact (Terminal := Terminal) progs code blank i x := by
  exact ProgLangBank.transactionBody_block progs
    (fun _ => queueIF (Terminal := Terminal) code) 45 i blank x

/-- info: 'PalPeg.RTQueueSlots.phaseRun_transact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phaseRun_transact

end PalPeg.RTQueueSlots
