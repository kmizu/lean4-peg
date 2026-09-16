import PalPeg.TextFeedPrefixAtomic
import PalPeg.TextFeedPrefixReady
import PalPeg.DualQueueShared

/-! The input duplicator and atomic prefix worker share the same 39 tapes. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixBank
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl
open PalPeg.GSVProgZLoop (RunsTo)

variable {k : ℕ} {Terminal : Type}

abbrev Act (k : ℕ) := DualQueueInput.Act k ⊕ TextFeedPrefixControl.Act k
abbrev Cond (k : ℕ) := DualQueueInput.Cond k ⊕ TextFeedPrefixControl.Cond k

noncomputable def interp (e : Env k) : Interp Terminal (Act k) (Cond k) (Fin k) 39 where
  actOf
    | .inl a => (DualQueueShared.interp e).actOf a
    | .inr a => (TextFeedPrefixReady.interp e).actOf a
  condOf
    | .inl c => (DualQueueShared.interp (Terminal := Terminal) e).condOf c
    | .inr c => (TextFeedPrefixReady.interp (Terminal := Terminal) e).condOf c

inductive Label where
  | enqueue (first : Bool)
  | work (a : TextFeedPrefixAtomic.Act)
  deriving DecidableEq, Fintype

noncomputable def low (e : Env k) : Label → Prog (Act k) (Cond k)
  | .enqueue first => (DualQueueInput.worker e first).map Sum.inl Sum.inl
  | .work a => (TextFeedPrefixAtomic.low e a).map Sum.inr Sum.inr

def tapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (D : TextFeedPrefixAtomic.Model k) (X : TapeConfiguration k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) : Fin 39 → STape (Fin k) :=
  Fin.append (TextFeedPrefixAtomic.tapes e qt₁ m₁ D)
    (TextFeedPrefixReady.rest e qt₂ m₂ X (Fin.append aux (TextFeedInput.cell old)) dir)

theorem pair_view (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (D : TextFeedPrefixAtomic.Model k) (X : TapeConfiguration k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    (fun j => tapes e qt₁ m₁ qt₂ m₂ D X aux old dir (DualQueueShared.pairSlot j)) =
      DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old := by
  funext j
  fin_cases j <;> rfl

theorem replace_pair (e : Env k) (qt₁ qt₁' : QT k) (m₁ m₁' : Mode) (qt₂ qt₂' : QT k) (m₂ m₂' : Mode)
    (D : TextFeedPrefixAtomic.Model k) (X : TapeConfiguration k)
    (aux : Fin 5 → STape (Fin k)) (old new : Fin k) (dir : STape (Fin k)) :
    extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') new)
      (tapes e qt₁ m₁ qt₂ m₂ D X aux old dir) = tapes e qt₁' m₁' qt₂' m₂' D X aux new dir := by
  funext j
  have hcover : ∀ j : Fin 39, DualQueueShared.Reserved j ∨ ∃ i, DualQueueShared.pairSlot i = j := by
    unfold DualQueueShared.Reserved
    decide
  rcases hcover j with hj | ⟨i, rfl⟩
  · rw [extend_of_proj_none (DualQueueShared.reserved_omitted hj)]
    fin_cases j <;> first | rfl | (simp [DualQueueShared.Reserved] at hj)
  · rw [extend_ι]
    exact (congrFun (pair_view e qt₁' m₁' qt₂' m₂' D X aux new dir) i).symm

theorem capture_some (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (D : TextFeedPrefixAtomic.Model k) (X : TapeConfiguration k)
    (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k)) :
    arriveA e.blank (DualQueueShared.capture enc) (some a) (tapes e qt₁ m₁ qt₂ m₂ D X aux old dir) =
      tapes e qt₁ m₁ qt₂ m₂ D X aux (enc a) dir := by
  have hi := replace_pair e qt₁ qt₁ m₁ m₁ qt₂ qt₂ m₂ m₂ D X aux old old dir
  calc
    _ = arriveA e.blank (DualQueueShared.capture enc) (some a)
      (extend DualQueueShared.pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old)
        (tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)) := congrArg _ hi.symm
    _ = _ := by rw [DualQueueShared.capture_extend, DualQueueInput.capture_some, replace_pair]

theorem work_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (a : TextFeedPrefixAtomic.Act) (D : TextFeedPrefixAtomic.Model k)
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (old : Fin k) (dir : STape (Fin k))
    (h : Ready e.blank e.mark qt₁ m₁ D.q) :
    ∃ ticks qt₁' m₁', ticks ≤ 47 ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (low e (.work a))
        (tapes e qt₁ m₁ qt₂ m₂ D X aux old dir)
        (tapes e qt₁' m₁' qt₂ m₂ (TextFeedPrefixAtomic.effect e a D) X aux old dir) ticks ∧
      Ready e.blank e.mark qt₁' m₁' (TextFeedPrefixAtomic.effect e a D).q := by
  obtain ⟨ticks, qt₁', m₁', hn, he, hr⟩ := TextFeedPrefixAtomic.low_matches (Terminal := Terminal) hc hmb a D h
  obtain ⟨tr, he', ht, hlen⟩ := TextFeedPrefixReady.shared_runs he
    (TextFeedPrefixReady.rest e qt₂ m₂ X (Fin.append aux (TextFeedInput.cell old)) dir)
  exact ⟨ticks, qt₁', m₁', hn, ⟨tr,
    exec_map (I₂ := interp e) (fa := Sum.inr) (fc := Sum.inr)
      (fun _ _ => rfl) (fun _ _ _ => rfl) he', ht, hlen⟩, hr⟩

theorem enqueue_matches {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (D : TextFeedPrefixAtomic.Model k) (q₂ : Queue (Fin k))
    (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode)
    (X : TapeConfiguration k) (aux : Fin 5 → STape (Fin k)) (a : Fin k) (dir : STape (Fin k))
    (h₁ : Ready e.blank e.mark qt₁ m₁ D.q) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂) (ha : a ≠ e.mark) :
    ∃ ticks qt₁' m₁' qt₂' m₂', ticks ≤ 68 ∧
      RunsTo (interp (Terminal := Terminal) e) e.blank (low e (.enqueue false))
        (tapes e qt₁ m₁ qt₂ m₂ D X aux a dir)
        (tapes e qt₁' m₁' qt₂' m₂' { D with q := snoc D.q a } X aux a dir) ticks ∧
      Ready e.blank e.mark qt₁' m₁' (snoc D.q a) ∧ Ready e.blank e.mark qt₂' m₂' (snoc q₂ a) := by
  obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hn, ht, hr₁, hr₂⟩ :=
    DualQueue.enqueue_both (Terminal := Terminal) hc hmb h₁ h₂ a ha
  obtain ⟨tr', he', hn', ht'⟩ := DualQueueInput.read_exec he ht
  obtain ⟨tr'', he'', hn'', ht''⟩ := DualQueueShared.worker_exec he' ht' (tapes e qt₁ m₁ qt₂ m₂ D X aux a dir)
  rw [replace_pair] at he'' ht''
  rw [replace_pair] at ht''
  exact ⟨tr''.length, qt₁', m₁', qt₂', m₂', by omega,
    ⟨tr'', exec_map (I₂ := interp e) (fa := Sum.inl) (fc := Sum.inl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) he'', ht'', rfl⟩, hr₁, hr₂⟩

/-- info: 'PalPeg.TextFeedPrefixBank.enqueue_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms enqueue_matches

/-- info: 'PalPeg.TextFeedPrefixBank.work_matches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms work_matches

end PalPeg.TextFeedPrefixBank
