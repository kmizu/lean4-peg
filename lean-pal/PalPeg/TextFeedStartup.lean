import PalPeg.TextFeedMachine27

/-! The first arrival initializes the private FIFO and enqueues that same
symbol, within the existing atomic-call budget. No scanner precondition is
needed: these calls are valid while preprocessing is still suspended. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartup
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedInit

variable {k : ℕ} {Terminal : Type}

noncomputable def firstEnqueue (blank mark a : Fin k) : RP k :=
  .seq (bootProg blank mark) (TextFeedAtomic.low blank mark (.enqueue a))

/-- Bootstrap and the first enqueue need at most 46 primitive actions.
The scanner and captured input cell are preserved exactly. -/
theorem firstEnqueue_exec {e : Env k} (hc : Function.Injective e.code)
    (hmb : e.mark ≠ e.blank) (S : Stage k) (old a : Fin k) (ha : a ≠ e.mark) :
    ∃ tr qt' m', Exec (IR (Terminal := Terminal) e) e.blank
      (firstEnqueue e.blank e.mark a) (unprepared e S old) tr ∧
      tr.length ≤ 46 ∧
      applyTrace e.blank (unprepared e S old) tr = rtapes e qt' m' S old ∧
      Ready e.blank e.mark qt' m' (snoc empty a) := by
  obtain ⟨b, hb, hbn, hbt⟩ := boot_exec (Terminal := Terminal) e S old
  obtain ⟨n, qt', m', hn, he, hr⟩ := enqueue_ready (Terminal := Terminal)
    hc hmb (initial_ready e.blank e.mark) ha
  obtain ⟨tr, ht, htn, hto⟩ := rexec_lift old
    (TextFeedTiming.texec_lift (executes_queue S he))
  have ht' : Exec (IR (Terminal := Terminal) e) e.blank
      (TextFeedAtomic.low e.blank e.mark (.enqueue a))
      (applyTrace e.blank (unprepared e S old) b) tr := by
    rw [hbt]
    exact ht
  refine ⟨b ++ tr, qt', m', exec_seq hb ht', ?_, ?_, hr⟩
  · simp only [List.length_append, hbn, htn]
    omega
  · rw [applyTrace_append, hbt, hto]

/-- info: 'PalPeg.TextFeedStartup.firstEnqueue_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms firstEnqueue_exec

end PalPeg.TextFeedStartup
