import PalPeg.DualQueueInput
import PalPeg.VerifierFeedShared

/-! Reserve the existing preparation/scanner layout and a zigzag direction
tape while both input FIFOs execute. No private copy of an input is assumed. -/
set_option autoImplicit false

namespace PalPeg.DualQueueShared
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl

variable {k : ℕ} {Terminal : Type}

/-- Q1 remains at 0..10, preparation at 11..25, input at 26.
Q2 occupies 27..37 and the future zigzag direction occupies 38. -/
def pairSlot : Fin 23 ↪ Fin 39 where
  toFun j := if j.val < 11 then ⟨j.val, by omega⟩
    else if j.val < 22 then ⟨j.val + 16, by omega⟩ else 26
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    have hi := i.isLt
    have hj := j.isLt
    dsimp only at hh
    split_ifs at hh <;> dsimp at hh <;> omega

def Reserved (j : Fin 39) : Prop := (11 ≤ j.val ∧ j.val < 26) ∨ j.val = 38

theorem reserved_omitted {j : Fin 39} (hj : Reserved j) : proj pairSlot j = none := by
  apply proj_eq_none
  intro i hi
  have h := congrArg Fin.val hi
  have hil := i.isLt
  change (if i.val < 11 then (⟨i.val, by omega⟩ : Fin 39)
    else if i.val < 22 then ⟨i.val + 16, by omega⟩ else 26).val = j.val at h
  split_ifs at h <;> dsimp at h <;> rcases hj with hj | hj <;> omega

attribute [local irreducible] pairSlot

noncomputable def interp (e : Env k) :=
  (DualQueueInput.interp (Terminal := Terminal) e).transport pairSlot

def captureInterp (enc : Terminal → Fin k) : Interp Terminal Unit Unit (Fin k) 23 where
  actOf _ := DualQueueInput.capture enc
  condOf _ _ := false

noncomputable def capture (enc : Terminal → Fin k) : ArriveAct Terminal (Fin k) 39 :=
  ((captureInterp enc).transport pairSlot).actOf ()

theorem capture_extend (e : Env k) (enc : Terminal → Fin k) (a : Option Terminal)
    (T : Fin 23 → STape (Fin k)) (rest : Fin 39 → STape (Fin k)) :
    arriveA e.blank (capture enc) a (extend pairSlot T rest) =
      extend pairSlot (arriveA e.blank (DualQueueInput.capture enc) a T) rest := by
  have hv : capture enc a (fun j => (extend pairSlot T rest j).focus) =
      extendVec pairSlot rest (DualQueueInput.capture enc a (fun j => (T j).focus)) :=
    actOf_transport pairSlot (captureInterp enc) () a T rest
  unfold arriveA
  rw [hv]
  exact applyAction_extend pairSlot e.blank T rest _

theorem worker_exec {e : Env k} {first : Bool} {T U : Fin 23 → STape (Fin k)}
    {tr : List (Fin 23 → Fin k × Move)}
    (he : Exec (DualQueueInput.interp (Terminal := Terminal) e) e.blank
      (DualQueueInput.worker e first) T tr) (ht : applyTrace e.blank T tr = U)
    (rest : Fin 39 → STape (Fin k)) :
    ∃ tr', Exec (interp (Terminal := Terminal) e) e.blank (DualQueueInput.worker e first)
      (extend pairSlot T rest) tr' ∧ tr'.length = tr.length ∧
      applyTrace e.blank (extend pairSlot T rest) tr' = extend pairSlot U rest := by
  refine ⟨_, exec_transport he pairSlot rest, by simp only [List.length_map], ?_⟩
  rw [applyTrace_extend, ht]

theorem arrival_both {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {qt₁ qt₂ : QT k} {m₁ m₂ : Mode} {q₁ q₂ : Queue (Fin k)}
    (h₁ : Ready e.blank e.mark qt₁ m₁ q₁) (h₂ : Ready e.blank e.mark qt₂ m₂ q₂)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) (old : Fin k)
    (rest : Fin 39 → STape (Fin k)) :
    let T := extend pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old) rest
    ∃ tr qt₁' m₁' qt₂' m₂', Exec (interp (Terminal := Terminal) e) e.blank
      (DualQueueInput.worker e false) (arriveA e.blank (capture enc) (some a) T) tr ∧
      1 + tr.length ≤ 69 ∧
      applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr =
        extend pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') (enc a)) rest ∧
      Ready e.blank e.mark qt₁' m₁' (snoc q₁ (enc a)) ∧
      Ready e.blank e.mark qt₂' m₂' (snoc q₂ (enc a)) ∧
      (∀ j, Reserved j →
        applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr j = rest j) := by
  obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hn, ht, hr₁, hr₂⟩ :=
    DualQueueInput.arrival_both hc hmb h₁ h₂ enc a ha old
  obtain ⟨tr', he', hn', ht'⟩ := worker_exec he ht rest
  dsimp only
  rw [capture_extend]
  refine ⟨tr', qt₁', m₁', qt₂', m₂', he', by omega, ht', hr₁, hr₂, ?_⟩
  intro j hj
  rw [ht', extend_of_proj_none (reserved_omitted hj)]

theorem first_arrival {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) (old : Fin k)
    (rest : Fin 39 → STape (Fin k)) :
    let T := extend pairSlot (DualQueueInput.tapes (DualQueue.blankPair e.blank) old) rest
    ∃ tr qt₁ m₁ qt₂ m₂, Exec (interp (Terminal := Terminal) e) e.blank
      (DualQueueInput.worker e true) (arriveA e.blank (capture enc) (some a) T) tr ∧
      1 + tr.length ≤ 93 ∧
      applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr =
        extend pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) (enc a)) rest ∧
      Ready e.blank e.mark qt₁ m₁ (snoc empty (enc a)) ∧
      Ready e.blank e.mark qt₂ m₂ (snoc empty (enc a)) ∧
      (∀ j, Reserved j →
        applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr j = rest j) := by
  obtain ⟨tr, qt₁, m₁, qt₂, m₂, he, hn, ht, hr₁, hr₂⟩ :=
    DualQueueInput.first_arrival hc hmb enc a ha old
  obtain ⟨tr', he', hn', ht'⟩ := worker_exec he ht rest
  dsimp only
  rw [capture_extend]
  refine ⟨tr', qt₁, m₁, qt₂, m₂, he', by omega, ht', hr₁, hr₂, ?_⟩
  intro j hj
  rw [ht', extend_of_proj_none (reserved_omitted hj)]

/-- The abstract arrival remains a proof model; its queue tape layouts
need not equal the actual finite-mode FIFO layouts. -/
theorem arrival_feedInv {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {M : VerifierFeed.VMachine' k} {qt₁ qt₂ : QT k} {m₁ m₂ : Mode}
    (h₁ : Ready e.blank e.mark qt₁ m₁ M.Q1) (h₂ : Ready e.blank e.mark qt₂ m₂ M.Q2)
    (enc : Terminal → Fin k) (a : Terminal) (ha : enc a ≠ e.mark) (old : Fin k)
    (rest : Fin 39 → STape (Fin k)) {u v Text : List (Fin k)} {d p r n : ℕ}
    (hn : n < Text.length) (hat : Text[n]? = some (enc a))
    (hinv : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let M' := VerifierFeed.varrive' e.blank e.mark (enc a) M
    let T := extend pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁ m₁ qt₂ m₂) old) rest
    ∃ tr qt₁' m₁' qt₂' m₂', Exec (interp (Terminal := Terminal) e) e.blank
      (DualQueueInput.worker e false) (arriveA e.blank (capture enc) (some a) T) tr ∧
      1 + tr.length ≤ 69 ∧
      applyTrace e.blank (arriveA e.blank (capture enc) (some a) T) tr =
        extend pairSlot (DualQueueInput.tapes (DualQueue.tapes e qt₁' m₁' qt₂' m₂') (enc a)) rest ∧
      Ready e.blank e.mark qt₁' m₁' M'.Q1 ∧ Ready e.blank e.mark qt₂' m₂' M'.Q2 ∧
      VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r (n + 1) M' := by
  obtain ⟨tr, qt₁', m₁', qt₂', m₂', he, hlen, ht, hr₁, hr₂, _⟩ :=
    arrival_both hc hmb h₁ h₂ enc a ha old rest
  exact ⟨tr, qt₁', m₁', qt₂', m₂', he, hlen, ht, hr₁, hr₂,
    VerifierFeed.varrive'_feedInv hmb hn hat hinv⟩

/-- info: 'PalPeg.DualQueueShared.arrival_feedInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_feedInv

/-- info: 'PalPeg.DualQueueShared.first_arrival' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms first_arrival

/-- info: 'PalPeg.DualQueueShared.arrival_both' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_both

end PalPeg.DualQueueShared
