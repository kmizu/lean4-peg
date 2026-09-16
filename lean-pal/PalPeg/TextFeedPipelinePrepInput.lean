import PalPeg.TextFeedPipelinePrepWindow

/-! Queue and input invariants during interrupted preparation. The first
input may start from blank FIFOs; all later inputs retain both FIFO orders. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepInput
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineHandoff

variable {k : ℕ} {Terminal : Type}

def pairView (T : Fin 39 → STape (Fin k)) : Fin 23 → STape (Fin k) := fun j => T (DualQueueShared.pairSlot j)

def ReadyAt (e : Env k) (T : Fin 39 → STape (Fin k)) (q₁ q₂ : Queue (Fin k)) (old : Fin k) : Prop :=
  ∃ qt₁ m₁ qt₂ m₂, pairView T = DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old ∧
    Ready e.blank e.mark qt₁ m₁ q₁ ∧ Ready e.blank e.mark qt₂ m₂ q₂

def QueuesAt (e : Env k) (first : Bool) (T : Fin 39 → STape (Fin k)) (q₁ q₂ : Queue (Fin k)) (old : Fin k) : Prop :=
  if first then q₁ = empty ∧ q₂ = empty ∧ pairView T = DualQueueInput.tapes (DualQueue.blankPair e.blank) old
  else ReadyAt e T q₁ q₂ old

theorem pairView_extend (P : Fin 23 → STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    pairView (extend DualQueueShared.pairSlot P T) = P := by
  funext j
  exact extend_ι DualQueueShared.pairSlot P T j

theorem prepView_extend_pair (P : Fin 23 → STape (Fin k)) (T : Fin 39 → STape (Fin k)) :
    prepView (extend DualQueueShared.pairSlot P T) = prepView T := by
  funext j
  exact extend_of_proj_none (DualQueueShared.reserved_omitted (TextFeedPipelineArrival.prep_reserved j)) P T

theorem capture_eq (e : Env k) (enc : Terminal → Fin k) (a : Option Terminal) (T : Fin 39 → STape (Fin k)) :
    arriveA e.blank (DualQueueShared.capture enc) a T =
      extend DualQueueShared.pairSlot (arriveA e.blank (DualQueueInput.capture enc) a (pairView T)) T := by
  have hh := DualQueueShared.capture_extend e enc a (pairView T) T
  have ht : extend DualQueueShared.pairSlot (pairView T) T = T := TextFeedStartupSafety.extend_restrict _ _
  rwa [ht] at hh

theorem capture_prepView (e : Env k) (enc : Terminal → Fin k) (a : Option Terminal) (T : Fin 39 → STape (Fin k)) :
    prepView (arriveA e.blank (DualQueueShared.capture enc) a T) = prepView T := by
  rw [capture_eq, prepView_extend_pair]

theorem capture_queues (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    {first : Bool} {T : Fin 39 → STape (Fin k)} {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (h : QueuesAt e first T q₁ q₂ old) :
    QueuesAt e first (arriveA e.blank (DualQueueShared.capture enc) (some a) T) q₁ q₂ (enc a) := by
  cases first with
  | false =>
    obtain ⟨qt₁, m₁, qt₂, m₂, hv, h₁, h₂⟩ := h
    refine ⟨qt₁, m₁, qt₂, m₂, ?_, h₁, h₂⟩
    rw [capture_eq, pairView_extend, hv, DualQueueInput.capture_some]
  | true =>
    obtain ⟨h₁, h₂, hv⟩ := h
    refine ⟨h₁, h₂, ?_⟩
    rw [capture_eq, pairView_extend, hv, DualQueueInput.capture_some]

theorem ready_prep {e : Env k} {T : Fin 39 → STape (Fin k)} {q₁ q₂ : Queue (Fin k)} {old : Fin k}
    (h : ReadyAt e T q₁ q₂ old) (P : Fin 15 → STape (Fin k)) : ReadyAt e (extend prepSlot P T) q₁ q₂ old := by
  obtain ⟨qt₁, m₁, qt₂, m₂, hv, h₁, h₂⟩ := h
  refine ⟨qt₁, m₁, qt₂, m₂, ?_, h₁, h₂⟩
  exact (TextFeedPipelineArrival.prep_preserves_inputs P T).trans hv

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

/-- One actual enqueue call, including the first bootstrap, preserves
preparation data and control and appends the captured input to both queues. -/
theorem run_queue (e : Env k) (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hz : x.1.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {a : Fin k} (ha : a ≠ e.mark)
    (h : QueuesAt e x.1.1.2.1 x.2 q₁ q₂ a) :
    let y := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
    ReadyAt e y.2 (snoc q₁ a) (snoc q₂ a) a ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.1 = false ∧ y.1.1.2.2 = x.1.1.2.2 ∧ prepView y.2 = prepView x.2 := by
  cases hf : x.1.1.2.1 with
  | true =>
    rw [hf] at h
    obtain ⟨rfl, rfl, hv⟩ := h
    have ht : x.2 = extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) a) x.2 := by
      rw [← hv]
      exact (TextFeedStartupSafety.extend_restrict _ _).symm
    obtain ⟨qt₁, m₁, qt₂, m₂, hout, hb', hc', hf', h₁, h₂, _⟩ :=
      TextFeedPipelineArrival.run_first (Terminal := Terminal) e hc hmb leftSym R rate x hb hz hf a ha x.2 ht
    refine ⟨⟨qt₁, m₁, qt₂, m₂, ?_, h₁, h₂⟩, hb', hf', hc', ?_⟩
    · rw [hout, pairView_extend]
    · rw [hout, prepView_extend_pair]
  | false =>
    rw [hf] at h
    obtain ⟨qt₁, m₁, qt₂, m₂, hv, h₁, h₂⟩ := h
    have hinit : extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) a) x.2 = x.2 := by
      rw [← hv]
      exact TextFeedStartupSafety.extend_restrict _ _
    obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hn, ht, hr₁, hr₂⟩ := DualQueue.enqueue_both (Terminal := Terminal) hc hmb h₁ h₂ a ha
    obtain ⟨tr', he', hn', ht'⟩ := DualQueueInput.read_exec he ht
    have hex := exec_enqueue he' x.2
    rw [hinit] at hex
    have he'' : Exec (TextFeedPipelineBank.interp (Terminal := Terminal) e) e.blank
        (low e (.enqueue x.1.1.2.1)) x.2 (tr'.map (extendVec DualQueueShared.pairSlot x.2)) := by
      rw [hf]
      exact hex
    obtain ⟨hout, hb', hc', hf'⟩ := run_enqueue_exec e leftSym R rate x hb hz _ he'' (by simp only [List.length_map]; omega)
    have hfinal : (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).2 =
        extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') a) x.2 := by
      have heq := applyTrace_extend DualQueueShared.pairSlot e.blank x.2 tr'
        (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) a)
      rw [hinit, ht'] at heq
      exact hout.trans heq
    refine ⟨⟨qt₁', m₁', qt₂', m₂', ?_, hr₁, hr₂⟩, hb', hf', hc', ?_⟩
    · rw [hfinal, pairView_extend]
    · rw [hfinal, prepView_extend_pair]

/-- info: 'PalPeg.TextFeedPipelinePrepInput.run_queue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_queue

end PalPeg.TextFeedPipelinePrepInput
