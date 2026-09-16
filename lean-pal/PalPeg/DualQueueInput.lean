import PalPeg.DualQueue

/-! One stationary arrival register supplies both queues. The program
reads that register; it does not receive two copies of an input event. -/
set_option autoImplicit false

namespace PalPeg.DualQueueInput
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl

variable {k : ℕ} {Terminal : Type}

abbrev Act (k : ℕ) := DualQueue.Act k ⊕ Empty
abbrev Cond (k : ℕ) := DualQueue.Cond k ⊕ Fin k

noncomputable def interp (e : Env k) := Interp.sum (DualQueue.interp (Terminal := Terminal) e)
  (TextFeedInput.IReg (Terminal := Terminal) (k := k))

def tapes (T : Fin 22 → STape (Fin k)) (old : Fin k) : Fin 23 → STape (Fin k) :=
  Fin.append T (TextFeedInput.cell old)

noncomputable def worker (e : Env k) (first : Bool) : Prog (Act k) (Cond k) :=
  choose Sum.inr fun a => (DualQueue.both e.blank e.mark a first).map Sum.inl Sum.inl

theorem read_exec {e : Env k} {first : Bool} {a : Fin k} {T U : Fin 22 → STape (Fin k)}
    {tr : List (Fin 22 → Fin k × Move)}
    (he : Exec (DualQueue.interp (Terminal := Terminal) e) e.blank
      (DualQueue.both e.blank e.mark a first) T tr)
    (ht : applyTrace e.blank T tr = U) :
    ∃ tr', Exec (interp (Terminal := Terminal) e) e.blank (worker e first) (tapes T a) tr' ∧
      tr'.length = tr.length ∧ applyTrace e.blank (tapes T a) tr' = tapes U a := by
  have hh := exec_sum_inl (I2 := TextFeedInput.IReg (Terminal := Terminal) (k := k)) he (tapes T a)
  rw [tapes, extend_castAdd_append] at hh
  refine ⟨_, exec_choose ?_ hh, by simp only [List.length_map], ?_⟩
  · intro b
    change decide (a = b) = decide (a = b)
    rfl
  · have ht' := applyTrace_extend (Fin.castAddEmb 1) e.blank (tapes T a) tr T
    simpa only [tapes, extend_castAdd_append, ht] using ht'

def inputSlot : Fin 23 := 22

def capture (enc : Terminal → Fin k) : ArriveAct Terminal (Fin k) 23 :=
  fun a σ => touchVec inputSlot ((a.map enc).getD (σ inputSlot)) .stay σ

theorem capture_some (blank : Fin k) (enc : Terminal → Fin k) (a : Terminal)
    (T : Fin 22 → STape (Fin k)) (old : Fin k) :
    arriveA blank (capture enc) (some a) (tapes T old) = tapes T (enc a) := by
  funext j
  fin_cases j <;> rfl

theorem arrival_both {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {q₁ q₂ : Queue (Fin k)}
    (h₁ : Ready e.blank e.mark qt₁ m₁ q₁) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) (old : Fin k) :
    let T := tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old
    ∃ tr qt₁' m₁' qt₂' m₂', Exec (interp (Terminal := Terminal) e) e.blank (worker e false)
      (arriveA e.blank (capture enc) (some a) T) tr ∧ 1 + tr.length ≤ 69 ∧
      applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr =
        tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') (enc a) ∧
      Ready e.blank e.mark qt₁' m₁' (snoc q₁ (enc a)) ∧ Ready e.blank e.mark qt₂' m₂' (snoc q₂ (enc a)) := by
  obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hn, ht, hr₁, hr₂⟩ :=
    DualQueue.enqueue_both (Terminal := Terminal) hc hmb h₁ h₂ (enc a) ha
  obtain ⟨tr', he', hn', ht'⟩ := read_exec he ht
  dsimp only
  rw [capture_some]
  exact ⟨tr', qt₁', m₁', qt₂', m₂', he', by omega, ht', hr₁, hr₂⟩

theorem first_arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) (old : Fin k) :
    let T := tapes (DualQueue.blankPair e.blank) old
    ∃ tr qt₁ m₁ qt₂ m₂, Exec (interp (Terminal := Terminal) e) e.blank (worker e true)
      (arriveA e.blank (capture enc) (some a) T) tr ∧ 1 + tr.length ≤ 93 ∧
      applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr =
        tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) (enc a) ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty (enc a)) ∧ Ready e.blank e.mark qt₂ m₂ (snoc empty (enc a)) := by
  obtain ⟨tr, qt₁, m₁, qt₂, m₂, he, hn, ht, hr₁, hr₂⟩ := DualQueue.first_both (Terminal := Terminal) hc hmb (enc a) ha
  obtain ⟨tr', he', hn', ht'⟩ := read_exec he ht
  dsimp only
  rw [capture_some]
  exact ⟨tr', qt₁, m₁, qt₂, m₂, he', by omega, ht', hr₁, hr₂⟩

/-- info: 'PalPeg.DualQueueInput.first_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_arrival

end PalPeg.DualQueueInput
