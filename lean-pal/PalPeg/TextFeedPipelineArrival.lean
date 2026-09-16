import PalPeg.TextFeedPipelineHandoff

/-! Actual dual-FIFO startup and arrival calls in the complete pipeline.
Preparation changes neither queue nor the captured input cell. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineArrival
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineHandoff

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem prep_reserved (i : Fin 15) : DualQueueShared.Reserved (prepSlot i) := by
  change (11 ≤ 11 + i.val ∧ 11 + i.val < 26) ∨ 11 + i.val = 38
  left
  omega

theorem prep_pair_omitted (j : Fin 23) : proj prepSlot (DualQueueShared.pairSlot j) = none := by
  apply proj_eq_none
  intro i hi
  have hh := DualQueueShared.reserved_omitted (prep_reserved i)
  rw [hi, proj_ι] at hh
  cases hh

theorem prep_preserves_inputs (P : Fin 15 → STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    (fun j => extend prepSlot P T (DualQueueShared.pairSlot j)) = (fun j => T (DualQueueShared.pairSlot j)) := by
  funext j
  exact extend_of_proj_none (prep_pair_omitted j) P T

/-- The first scheduled call initializes both blank FIFOs while retaining
the actual initial preparation continuation. -/
theorem run_first (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0) (hf : x.1.1.2.1 = true)
    (a : Fin k) (ha : a ≠ e.mark) (rest : Fin 39 → STape (Fin k))
    (hx : x.2 = extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) a) rest) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁ m₁ qt₂ m₂,
      y.2 = extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) a) rest ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2 = x.1.1.2.2 ∧ y.1.1.2.1 = false ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty a) ∧ Ready e.blank e.mark qt₂ m₂ (snoc empty a) ∧
      ∀ j, DualQueueShared.Reserved j → y.2 j = rest j := by
  obtain ⟨tr, qt₁, m₁, qt₂, m₂, he, hn, ht, h₁, h₂⟩ := first_exec (Terminal := Terminal) hc hmb a ha rest
  rw [← hx] at he ht
  have he' : Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank
      (low e (.enqueue x.1.1.2.1)) x.2 tr := by rw [hf]; exact he
  obtain ⟨hyt, hby, hcy, hfy⟩ := run_enqueue_exec e leftSym R rate x hb hz tr he' (by omega)
  have hout := hyt.trans ht
  refine ⟨qt₁, m₁, qt₂, m₂, hout, hby, hcy, hfy, h₁, h₂, ?_⟩
  intro j hj
  rw [hout, extend_of_proj_none (DualQueueShared.reserved_omitted hj)]

/-- Subsequent arrivals append once to each FIFO and preserve the
scanner, U, X, preparation auxiliaries, direction, and source control. -/
theorem run_enqueue (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0) (hf : x.1.1.2.1 = false)
    (D : TextFeedPrefixAtomic.Model k) (q₂ : Queue (Fin k))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (a : Fin k) (dir : STape (Fin k))
    (hx : x.2 = TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D X aux a dir)
    (h₁ : Ready e.blank e.mark qt₁ m₁ D.q) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂) (ha : a ≠ e.mark) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    ∃ qt₁' m₁' qt₂' m₂',
      y.2 = TextFeedPrefixBank.tapes e qt₁' m₁' qt₂' m₂' { D with q := snoc D.q a } X aux a dir ∧
      AtBoundary (programs e) y.1.2.2.1 ∧ y.1.1.2.2 = x.1.1.2.2 ∧ y.1.1.2.1 = false ∧
      Ready e.blank e.mark qt₁' m₁' (snoc D.q a) ∧ Ready e.blank e.mark qt₂' m₂' (snoc q₂ a) := by
  obtain ⟨ticks, qt₁', m₁', qt₂', m₂', hn, ⟨tr, he, ht, hlen⟩, h₁', h₂'⟩ :=
    TextFeedPrefixBank.enqueue_matches (Terminal := Terminal) hc hmb D q₂ qt₁ m₁ qt₂ m₂ X aux a dir h₁ h₂ ha
  have he' := exec_prefix he
  rw [← hx] at he' ht
  have hex : Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank
      (low e (.enqueue x.1.1.2.1)) x.2 tr := by rw [hf]; exact he'
  obtain ⟨hyt, hby, hcy, hfy⟩ := run_enqueue_exec e leftSym R rate x hb hz tr hex (by omega)
  exact ⟨qt₁', m₁', qt₂', m₂', hyt.trans ht, hby, hcy, hfy, h₁', h₂'⟩

/-- info: 'PalPeg.TextFeedPipelineArrival.run_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_first

/-- info: 'PalPeg.TextFeedPipelineArrival.run_enqueue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enqueue

end PalPeg.TextFeedPipelineArrival
