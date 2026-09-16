import PalPeg.TextFeedWorkerBridge

/-! The worker may start with arrivals already queued by preprocessing.
No empty-buffer premise or replay of those arrivals is necessary. -/
set_option autoImplicit false

namespace PalPeg.TextFeedBacklog
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedRefine

variable {k : ℕ}

/-- Logical queue roles are read through the actual finite permutation.
The physical FIFO need not be reset to its initial role assignment. -/
def model (ts : GSTapes.TapesState' k) (qt : QT k) (m : Mode) (q : Queue (Fin k)) :
    TextFeed.Machine' k := ⟨0, ts, q, ⟨qt ∘ m.roles, 0⟩, ⟨0, 0⟩⟩

theorem feedInv {e : Env k} {ts : GSTapes.TapesState' k} {qt : QT k} {m : Mode}
    {q : Queue (Fin k)} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩)
    (hq : Ready e.blank e.mark qt m q) (hl : toList q = Text.take n) :
    TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n (model ts qt m q) := by
  exact ⟨hs, hq.enc, hq.inv, by simpa only [model, List.drop_zero] using hl,
    Nat.zero_le n, Nat.le_refl 0, Nat.zero_le _⟩

noncomputable local instance : DecidableEq (AP k ⊕ Empty) := Classical.decEq _
noncomputable local instance : DecidableEq (CT k ⊕ Fin k) := Classical.decEq _

/-- A proof-only comparison control; the combined physical machine keeps
its own task controller, related by TextFeedWorkerBridge.Link. -/
noncomputable def ctrl (e : Env k) (R rate : ℕ) (counter : Fin (R + 1)) :
    CallCtrl (TextFeedAtomic.programs e.blank e.mark) (TextFeedSchedule.Outer R rate) :=
  ((counter, startCtrlS (TextFeedSchedule.worker rate)), TextFeedSchedule.encode .idle,
    initialBank (TextFeedAtomic.programs e.blank e.mark), false)

/-- The existing streaming invariant holds at the real arrival count n,
not at a fabricated fresh count zero, while all n symbols remain buffered. -/
theorem sim {e : Env k} {ts : GSTapes.TapesState' k} {qt : QT k} {m : Mode}
    {q : Queue (Fin k)} {v Text : List (Fin k)} {R rate p₁ rem n : ℕ}
    (counter : Fin (R + 1)) (old : Fin k)
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩)
    (hq : Ready e.blank e.mark qt m q) (hl : toList q = Text.take n) :
    Sim e v Text R rate p₁ rem n (model ts qt m q) .loop
      (ctrl e R rate counter, rtapes e qt m (GSProg.TS ts) old) old := by
  exact ⟨feedInv hs hq hl, initialBank_boundary _, rfl, trivial, qt, m, rfl, hq⟩

theorem workInv {e : Env k} {ts : GSTapes.TapesState' k} {qt : QT k} {m : Mode}
    {q : Queue (Fin k)} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    (hs : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem ts ⟨0, 0⟩)
    (hq : Ready e.blank e.mark qt m q) (hl : toList q = Text.take n) :
    WorkInv e v Text rate p₁ rem n (model ts qt m q, .loop) := ⟨feedInv hs hq hl, trivial⟩

/-- The initial GS potential can pay for arrivals buffered during prep.
This is the precise startup-delay condition needed by frame_work_credit. -/
theorem credit {ts : GSTapes.TapesState' k} {qt : QT k} {m : Mode} {q : Queue (Fin k)}
    {v : List (Fin k)} {rate n : ℕ} (h : (rate + 1) * n ≤ rate * v.length) :
    workScale rate * ((rate + 1) * n) ≤ workCredit v rate (model ts qt m q, .loop) := by
  simpa only [workCredit, workScore, model, Phi, Nat.mul_zero, Nat.zero_add] using
    Nat.mul_le_mul_left (workScale rate) h

theorem scanInv (ts : GSTapes.TapesState' k) (qt : QT k) (m : Mode) (q : Queue (Fin k))
    (v Text : List (Fin k)) : ScanInv v Text (model ts qt m q).st :=
  ⟨by simpa only [model] using matchLen_zero v Text 0, by simp [model]⟩

/-- info: 'PalPeg.TextFeedBacklog.sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sim

/-- info: 'PalPeg.TextFeedBacklog.credit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms credit

end PalPeg.TextFeedBacklog
