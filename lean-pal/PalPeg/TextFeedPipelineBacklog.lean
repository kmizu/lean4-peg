import PalPeg.TextFeedPipelineBirthInputCycle
import PalPeg.DualQueueShared

set_option autoImplicit false
namespace PalPeg.TextFeedPipelineBacklog
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.TextFeedControl PalPeg.TextFeedPipelineBirthSource
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
variable {k : ℕ}

/-- One physical backlog read supplies the existing shared FIFO input
register. Blank terminates the source without capturing a bogus symbol. -/
noncomputable def machine (e : Env k) : StructuredMachine Unit Bool (Fin k) 40 1 where
  tapeCount_pos := by decide
  blank := e.blank
  initial := false
  accepting := id
  micro := fun _ _ σ =>
    if σ sourceAddr = e.blank then (false, fun j => (σ j, .stay)) else
    (true, fun j => match (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39) with
      | .inl _ => (σ j, .right)
      | .inr i => DualQueueShared.capture id (some (σ sourceAddr))
          (fun z => σ (targetAddr z)) i)

def packB (b : Bool) (S : STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    SConfig Bool (Fin k) 40 := ⟨b, (pack 0 S T).tape⟩

theorem read_round (e : Env k) (a : Fin k) (w junk : List (Fin k))
    (ha : a ≠ e.blank) (T : Fin 39 → STape (Fin k)) (b : Bool) :
    (machine e).sRound (packB b (HistoryConcat.source e.blank (a :: w) junk) T) () =
      packB true (HistoryConcat.source e.blank w (a :: junk))
        (arriveA e.blank (DualQueueShared.capture id) (some a) T) := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, packB, pack, sourceAddr, targetAddr,
    Equiv.symm_apply_apply, HistoryConcat.source, List.headD_cons, List.tail_cons,
    ha, ↓reduceIte]
  congr 1
  funext j
  cases h : (finSumFinEquiv.symm j : Fin 1 ⊕ Fin 39)
  · cases w <;> rfl
  · rfl

theorem empty_round (e : Env k) (junk : List (Fin k))
    (T : Fin 39 → STape (Fin k)) (b : Bool) :
    (machine e).sRound (packB b (HistoryConcat.source e.blank [] junk) T) () =
      packB false (HistoryConcat.source e.blank [] junk) T := by
  simp only [StructuredMachine.sRound, Speedup.MultiStepMachine.roundInputs,
    Nat.sub_self, List.replicate_zero, List.foldl_cons, List.foldl_nil,
    StructuredMachine.sMicroStep, machine, packB, pack, sourceAddr,
    Equiv.symm_apply_apply, HistoryConcat.source, List.headD_nil, List.tail_nil, ↓reduceIte]
  rfl

/-- The first symbol read from a physical backlog is enqueued into both
actual FIFO layouts within the existing 93-action bound. The preparation
tapes are preserved. This is an executable-trace contract; scheduling the
reader and FIFO worker is still the enclosing controller's responsibility. -/
theorem first_from_source (e : Env k) (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (a : Fin k) (ha : a ≠ e.blank) (ham : a ≠ e.mark)
    (w junk : List (Fin k)) (old : Fin k) (rest : Fin 39 → STape (Fin k)) :
    let T := extend DualQueueShared.pairSlot
      (DualQueueInput.tapes (DualQueue.blankPair e.blank) old) rest
    let y := (machine e).sRound (packB false (HistoryConcat.source e.blank (a :: w) junk) T) ()
    ∃ tr qt₁ m₁ qt₂ m₂,
      Exec (DualQueueShared.interp (Terminal := Fin k) e) e.blank
        (DualQueueInput.worker e true) (fun j => y.tape (targetAddr j)) tr ∧
      1 + tr.length ≤ 93 ∧
      applyTrace e.blank (fun j => y.tape (targetAddr j)) tr =
        extend DualQueueShared.pairSlot
          (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) a) rest ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty a) ∧
      Ready e.blank e.mark qt₂ m₂ (snoc empty a) ∧
      (∀ j, DualQueueShared.Reserved j →
        applyTrace e.blank (fun j => y.tape (targetAddr j)) tr j = rest j) := by
  dsimp only
  rw [read_round e a w junk ha]
  simp only [packB, pack, targetAddr, Equiv.symm_apply_apply]
  exact DualQueueShared.first_arrival hc hmb id a ham old rest

/-- Subsequent backlog symbols use the ordinary bounded FIFO operation,
preserving order in both queues and all reserved matcher tapes. -/
theorem next_from_source (e : Env k) (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank)
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {q₁ q₂ : Queue (Fin k)}
    (h₁ : Ready e.blank e.mark qt₁ m₁ q₁) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (a : Fin k) (ha : a ≠ e.blank) (ham : a ≠ e.mark)
    (w junk : List (Fin k)) (old : Fin k) (rest : Fin 39 → STape (Fin k)) :
    let T := extend DualQueueShared.pairSlot
      (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old) rest
    let y := (machine e).sRound (packB false (HistoryConcat.source e.blank (a :: w) junk) T) ()
    ∃ tr qt₁' m₁' qt₂' m₂',
      Exec (DualQueueShared.interp (Terminal := Fin k) e) e.blank
        (DualQueueInput.worker e false) (fun j => y.tape (targetAddr j)) tr ∧
      1 + tr.length ≤ 69 ∧
      applyTrace e.blank (fun j => y.tape (targetAddr j)) tr =
        extend DualQueueShared.pairSlot
          (DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') a) rest ∧
      Ready e.blank e.mark qt₁' m₁' (snoc q₁ a) ∧
      Ready e.blank e.mark qt₂' m₂' (snoc q₂ a) ∧
      (∀ j, DualQueueShared.Reserved j →
        applyTrace e.blank (fun j => y.tape (targetAddr j)) tr j = rest j) := by
  dsimp only
  rw [read_round e a w junk ha]
  simp only [packB, pack, targetAddr, Equiv.symm_apply_apply]
  exact DualQueueShared.arrival_both hc hmb h₁ h₂ id a ham old rest

/-- info: 'PalPeg.TextFeedPipelineBacklog.next_from_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_from_source

/-- info: 'PalPeg.TextFeedPipelineBacklog.first_from_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_from_source

end PalPeg.TextFeedPipelineBacklog
