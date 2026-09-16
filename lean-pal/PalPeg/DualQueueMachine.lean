import PalPeg.DualQueueInput
import PalPeg.ProgLangCallFrame

/-! Two physical queues, one actual arrival, and a fixed 95-tick frame.
The only outer control is a first-frame bit; queue contents are proof data. -/
set_option autoImplicit false

namespace PalPeg.DualQueueMachine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl

variable {k : ℕ} {Terminal : Type}

noncomputable def programs (e : Env k) (i : Fin 2) := DualQueueInput.worker e (i == 0)

noncomputable def interp (e : Env k) :
    InterpF Terminal (DualQueueInput.Act k) (DualQueueInput.Cond k) (Fin k) 23 where
  toInterp := DualQueueInput.interp e
  flagOf _ := none

def choose (first : Bool) (_ : Fin 23 → Fin k) : Bool × Fin 2 :=
  (false, if first then 0 else 1)

noncomputable local instance : DecidableEq (DualQueueInput.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (DualQueueInput.Cond k) := Classical.decEq _

noncomputable def run (e : Env k) :=
  callRun (programs e) (fun _ => interp (Terminal := Terminal) e) choose 93 e.blank

noncomputable def machine (e : Env k) (enc : Terminal → Fin k) :=
  callFrameMachine (programs e) (fun _ => interp (Terminal := Terminal) e) choose
    93 1 e.blank (by omega : 0 < 23) true 0 (DualQueueInput.capture enc)

theorem run_exec {e : Env k} (c : CallCtrl (programs e) Bool)
    (T : Fin 23 → STape (Fin k)) (tr : List (Fin 23 → Fin k × Move))
    (hb : AtBoundary (programs e) c.2.2.1)
    (he : Exec (DualQueueInput.interp (Terminal := Terminal) e) e.blank
      (DualQueueInput.worker e c.1) T tr) (hn : tr.length < 93) :
    let y := run (Terminal := Terminal) e (c, T)
    y.1.1 = false ∧ y.2 = applyTrace e.blank T tr ∧
      AtBoundary (programs e) y.1.2.2.1 := by
  have hp : programs e (choose c.1 (fun j => (T j).focus)).2 = DualQueueInput.worker e c.1 := by
    cases h : c.1 <;> simp [programs, choose]
  have he' : Exec (interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose c.1 (fun j => (T j).focus)).2) T tr := by
    rw [hp]
    exact he
  obtain ⟨ht, hb', _, _⟩ := callRun_exec (programs e)
    (fun _ => interp (Terminal := Terminal) e) choose 93 e.blank (c, T) hb tr he' hn
  exact ⟨rfl, ht, hb'⟩

attribute [local irreducible] runChunk

theorem round_eq (e : Env k) (enc : Terminal → Fin k) (a : Terminal)
    (c : CallCtrl (programs e) Bool) (T : Fin 23 → STape (Fin k)) :
    (machine e enc).sRound { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a =
      let y := run (Terminal := Terminal) e (c, arriveA e.blank (DualQueueInput.capture enc) (some a) T)
      { state := ((y.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := y.2 } := by
  exact callFrameMachine_round (programs e) (fun _ => interp (Terminal := Terminal) e)
    choose 93 1 e.blank (by omega) true 0 (DualQueueInput.capture enc) a c T

theorem arrival_refine {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark)
    (c : CallCtrl (programs e) Bool) (hfirst : c.1 = false)
    (hb : AtBoundary (programs e) c.2.2.1)
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {q₁ q₂ : Queue (Fin k)}
    (h₁ : Ready e.blank e.mark qt₁ m₁ q₁) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (old : Fin k) :
    let y := (machine e enc).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩),
        tape := DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old } a
    ∃ qt₁' m₁' qt₂' m₂', y.state.1.1.1 = false ∧
      y.tape = DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') (enc a) ∧
      AtBoundary (programs e) y.state.1.1.2.2.1 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0 ∧
      Ready e.blank e.mark qt₁' m₁' (snoc q₁ (enc a)) ∧
      Ready e.blank e.mark qt₂' m₂' (snoc q₂ (enc a)) := by
  obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hn, ht, hr₁, hr₂⟩ :=
    DualQueueInput.arrival_both hc hmb h₁ h₂ enc a ha old
  rw [← hfirst] at he
  obtain ⟨hf, hout, hb'⟩ := run_exec c _ tr hb he (by omega)
  dsimp only
  rw [round_eq]
  exact ⟨qt₁', m₁', qt₂', m₂', hf, hout.trans ht, hb', rfl, rfl, hr₁, hr₂⟩

theorem first_refine {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark)
    (c : CallCtrl (programs e) Bool) (hfirst : c.1 = true)
    (hb : AtBoundary (programs e) c.2.2.1) (old : Fin k) :
    let y := (machine e enc).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩),
        tape := DualQueueInput.tapes (DualQueue.blankPair e.blank) old } a
    ∃ qt₁ m₁ qt₂ m₂, y.state.1.1.1 = false ∧
      y.tape = DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) (enc a) ∧
      AtBoundary (programs e) y.state.1.1.2.2.1 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0 ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty (enc a)) ∧
      Ready e.blank e.mark qt₂ m₂ (snoc empty (enc a)) := by
  obtain ⟨tr, qt₁, m₁, qt₂, m₂, he, hn, ht, hr₁, hr₂⟩ :=
    DualQueueInput.first_arrival hc hmb enc a ha old
  rw [← hfirst] at he
  obtain ⟨hf, hout, hb'⟩ := run_exec c _ tr hb he (by omega)
  dsimp only
  rw [round_eq]
  exact ⟨qt₁, m₁, qt₂, m₂, hf, hout.trans ht, hb', rfl, rfl, hr₁, hr₂⟩

abbrev Config (e : Env k) :=
  SConfig ((CallCtrl (programs e) Bool × Fin 94) × Fin 95) (Fin k) 23

attribute [local irreducible] StructuredMachine.sRound

theorem config_ext {e : Env k} {x y : Config e}
    (hs : x.state = y.state) (ht : x.tape = y.tape) : x = y := by
  cases x; cases y; cases hs; cases ht; rfl

def Queued (e : Env k) (x : Config e) (q₁ q₂ : Queue (Fin k)) : Prop :=
  ∃ c qt₁ m₁ qt₂ m₂ old,
    x = { state := ((c, 0), 0), tape := DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old } ∧
    c.1 = false ∧ AtBoundary (programs e) c.2.2.1 ∧
    Ready e.blank e.mark qt₁ m₁ q₁ ∧ Ready e.blank e.mark qt₂ m₂ q₂

theorem queued_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark)
    {x : Config e} {q₁ q₂ : Queue (Fin k)} (hx : Queued e x q₁ q₂) :
    Queued e ((machine e enc).sRound x a) (snoc q₁ (enc a)) (snoc q₂ (enc a)) := by
  obtain ⟨c, qt₁, m₁, qt₂, m₂, old, rfl, hf, hb, hr₁, hr₂⟩ := hx
  obtain ⟨qt₁', m₁', qt₂', m₂', hf', ht, hb', hp, hp', hr₁', hr₂'⟩ :=
    arrival_refine hc hmb enc a ha c hf hb hr₁ hr₂ old
  refine ⟨_, qt₁', m₁', qt₂', m₂', enc a, ?_, hf', hb', hr₁', hr₂'⟩
  apply config_ext
  · exact Prod.ext (Prod.ext rfl hp) hp'
  · exact ht

theorem queued_word {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (w : List Terminal) (ha : ∀ a ∈ w, enc a ≠ e.mark)
    {x : Config e} {q₁ q₂ : Queue (Fin k)} (hx : Queued e x q₁ q₂) :
    Queued e (w.foldl (machine e enc).sRound x)
      (w.foldl (fun q a => snoc q (enc a)) q₁)
      (w.foldl (fun q a => snoc q (enc a)) q₂) := by
  induction w generalizing x q₁ q₂ with
  | nil => exact hx
  | cons a w ih =>
    exact ih (fun b hb => ha b (by simp [hb]))
      (queued_step hc hmb enc a (ha a (by simp)) hx)

theorem initial_queued {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) :
    Queued e ((machine e enc).srun [a]) (snoc empty (enc a)) (snoc empty (enc a)) := by
  let c : CallCtrl (programs e) Bool := (true, 0, initialBank (programs e), false)
  have hi : (machine e enc).sInit =
      { state := ((c, 0), 0), tape := DualQueueInput.tapes (DualQueue.blankPair e.blank) e.blank } := by
    apply config_ext
    · rfl
    · funext j
      fin_cases j <;> rfl
  change Queued e ((machine e enc).sRound (machine e enc).sInit a) _ _
  rw [hi]
  obtain ⟨qt₁, m₁, qt₂, m₂, hf, ht, hb, hp, hp', hr₁, hr₂⟩ :=
    first_refine hc hmb enc a ha c rfl (initialBank_boundary _) e.blank
  refine ⟨_, qt₁, m₁, qt₂, m₂, enc a, ?_, hf, hb, hr₁, hr₂⟩
  apply config_ext
  · exact Prod.ext (Prod.ext rfl hp) hp'
  · exact ht

theorem srun_queued {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (w : List Terminal)
    (ha : ∀ b ∈ a :: w, enc b ≠ e.mark) :
    let q := (a :: w).foldl (fun q b => snoc q (enc b)) empty
    Queued e ((machine e enc).srun (a :: w)) q q := by
  exact queued_word hc hmb enc w (fun b hb => ha b (by simp [hb]))
    (initial_queued hc hmb enc a (ha a (by simp)))

theorem srun_contents {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (w : List Terminal)
    (ha : ∀ b ∈ a :: w, enc b ≠ e.mark) :
    ∃ q, Queued e ((machine e enc).srun (a :: w)) q q ∧ toList q = (a :: w).map enc := by
  refine ⟨_, srun_queued hc hmb enc a w ha, ?_⟩
  rw [← List.foldl_map]
  exact toList_ofList _

/-- info: 'PalPeg.DualQueueMachine.srun_contents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srun_contents

/-- info: 'PalPeg.DualQueueMachine.srun_queued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srun_queued

/-- info: 'PalPeg.DualQueueMachine.first_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_refine

end PalPeg.DualQueueMachine
