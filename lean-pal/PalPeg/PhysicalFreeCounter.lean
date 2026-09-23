import PalPeg.PhysicalContract

/-!
# Reusing an unnamed counter slot without disturbing the physical encoding

During watch/broken, counter 10 no longer denotes chain.h. Its tape and sign can
carry the boundary spare. This frame lemma keeps all other represented fields,
including heads, program buffers, mirrors and macro-boundary facts.
-/
set_option autoImplicit false
namespace PalPeg.PhysicalFreeCounter
open PalPeg.PhysicalEncoding PalPeg.PhysicalContract
open PalPeg.Program (STape)
open PalPeg.LocalCounter (Seg absCtr)
open PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply

/-- Physical polarity is not an abstract control observation. -/
theorem encControl_polarity {fb db : ℕ} {w : List (Fin 2)} {x : State GalilVM}
    {q : QPhys fb db} (henc : EncControl w x q) (polarity : Fin 16 → Bool) :
    EncControl w x {q with polarity := polarity} := by
  cases henc
  constructor <;> assumption

theorem encTapes_free_counter {padding : ℕ} {x : State GalilVM}
    {polarity : Fin 16 → Bool} {gap : Fin 4 → Bool}
    {micro : Fin 4 → PalPeg.ConcreteLocalMachine.MicroControl} {fl dl : Bool}
    {T : Slot → STape Γm} (henc : EncTapes padding x polarity gap micro fl dl T)
    (c : Fin 16) (hfree : counterOf x c = none) (bit : Bool) (tape : STape Γm)
    (hmargin : padding ≤ PalPeg.Local.pos tape) :
    EncTapes padding x (Function.update polarity c bit) gap micro fl dl
      (Function.update T (counterSlot c) tape) where
  margins := by
    intro slot
    by_cases he : slot = counterSlot c
    · simpa [he] using hmargin
    · simpa [Function.update, he] using henc.margins slot
  heads := by
    intro v head hh
    obtain ⟨view, vt, ha, hv, hs, hc, hw⟩ := henc.heads v head hh
    refine ⟨view, vt, ha, hv, ?_, hc, hw⟩
    intro i
    simpa [Function.update, counterSlot] using hs i
  idleHead := by
    intro hh
    obtain ⟨view, vt, hv, hs, hc, hw⟩ := henc.idleHead hh
    refine ⟨view, vt, hv, ?_, hc, hw⟩
    intro i
    simpa [Function.update, counterSlot, headSlot] using hs i
  fpp := by
    intro i
    have hn : progSlotOf fl i ≠ counterSlot c := by cases fl <;> simp [progSlotOf, counterSlot]
    simpa [Function.update, hn] using henc.fpp i
  dp := by
    intro i
    have hn : dpSlotOf dl i ≠ counterSlot c := by cases dl <;> simp [dpSlotOf, counterSlot]
    simpa [Function.update, hn] using henc.dp i
  idleShape := by
    intro i
    have hn : progSlotOf (!fl) i ≠ counterSlot c := by cases fl <;> simp [progSlotOf, counterSlot]
    simpa [Function.update, hn] using henc.idleShape i
  counters := by
    intro j value hv
    have hj : j ≠ c := by intro he; subst j; rw [hfree] at hv; cases hv
    obtain ⟨seg, ha, ht⟩ := henc.counters j value hv
    exact ⟨seg, by simpa [Function.update, hj] using ha,
      by simpa [Function.update, counterSlot, hj] using ht⟩
  places := by
    intro i place hp
    obtain ⟨stack, junk, hj, hs, ht⟩ := henc.places i place hp
    exact ⟨stack, junk, hj, hs, by simpa [Function.update, counterSlot] using ht⟩
  mirrors := by
    intro m value hv
    have hm : mirrorSource m ≠ c := by intro he; rw [he, hfree] at hv; cases hv
    obtain ⟨seg, ha, ht⟩ := henc.mirrors m value hv
    exact ⟨seg, by simpa [Function.update, hm] using ha,
      by simpa [Function.update, counterSlot] using ht⟩
  period := by
    intro t ht
    simpa [Function.update, counterSlot] using henc.period t ht
  answer := by
    intro t ht
    simpa [Function.update, counterSlot] using henc.answer t ht

def setPolarity (q : CoreControl) (c : Fin 16) (bit : Bool) : CoreControl :=
  {q with polarity := Function.update q.polarity c bit}

/-- The frame fact on the exact encoding used by the real fused step. -/
theorem core_free_counter {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : CoreEnc w x p) (c : Fin 16) (hfree : counterOf x c = none)
    (bit : Bool) (tape : STape Γm) (hmargin : margin ≤ PalPeg.Local.pos tape) :
    CoreEnc w x (setPolarity p.1 c bit, Function.update p.2 (slotIndex (counterSlot c)) tape) := by
  refine ⟨⟨encControl_polarity henc.1.1 _, ?_⟩, henc.2⟩
  have ht : (fun slot => Function.update p.2 (slotIndex (counterSlot c)) tape (slotIndex slot)) =
      Function.update (fun slot => p.2 (slotIndex slot)) (counterSlot c) tape := by
    funext slot
    simp [Function.update]
  rw [ht]
  exact encTapes_free_counter henc.1.2 c hfree bit tape hmargin

/-- A replacement tape with enough margin also frames the sweep closure. No
literal equality between physical and ideal tapes is requested. -/
theorem running_free_counter {w : List (Fin 2)} {x : State GalilVM} {p : CoreState}
    (henc : PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x p)
    (c : Fin 16) (hfree : counterOf x c = none) (bit : Bool) (tape : STape Γm)
    (hmargin : margin ≤ PalPeg.Local.pos tape) :
    PalPeg.MachineStep.sweepClosure blankM (CoreEnc w) x
      (setPolarity p.1 c bit, Function.update p.2 (slotIndex (counterSlot c)) tape) := by
  obtain ⟨ideal, hi, hteq⟩ := henc
  refine ⟨Function.update ideal (slotIndex (counterSlot c)) tape,
    core_free_counter hi c hfree bit tape hmargin, ?_⟩
  intro j
  by_cases he : j = slotIndex (counterSlot c)
  · subst j
    simp only [Function.update_self]
    exact ⟨rfl, fun _ => rfl⟩
  · simpa [Function.update, he] using hteq j

/-- info: 'PalPeg.PhysicalFreeCounter.running_free_counter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms running_free_counter

end PalPeg.PhysicalFreeCounter
