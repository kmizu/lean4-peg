import PalPeg.RTQueueClosed

/-! Construct the marked empty queue on genuinely blank tapes. -/
set_option autoImplicit false

namespace PalPeg.RTQueueInit
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueClosed

variable {k : ℕ} {Terminal : Type}

def blankQT (blank : Fin k) : QT k := fun _ => ⟨[], blank, []⟩

def initActs (blank mark : Fin k) : List (Act k) :=
  [⟨.front, mark, .right⟩, ⟨.fdup, mark, .right⟩, ⟨.rear, mark, .right⟩,
   ⟨.f, mark, .right⟩, ⟨.fp, mark, .right⟩, ⟨.r, mark, .right⟩,
   ⟨.rp, mark, .right⟩, ⟨.rpdup, mark, .right⟩, ⟨.ok, mark, .right⟩,
   ⟨.dd, mark, .right⟩, ⟨.dd, blank, .right⟩]

def literalProg : List (Act k) → Prog (ActQ k) (CondQ k)
  | [] => .skip
  | a :: as => .seq (.act (a.role, a.write, a.move)) (literalProg as)

theorem literalProg_exec (blank : Fin k) (as : List (Act k)) (qt : QT k) :
    ExecQ Terminal blank (literalProg as) qt as := by
  induction as generalizing qt with
  | nil => exact execQ_skip qt
  | cons a as ih =>
    exact execQ_seq (execQ_act a.role a.write a.move qt) (ih _)

def initProg (blank mark : Fin k) := literalProg (initActs blank mark)

theorem init_run (blank mark : Fin k) :
    RTQueueTapes.run blank (blankQT blank) (initActs blank mark) = initQT blank mark := by
  funext rho
  cases rho <;> rfl

/-- The eleven literal actions install all markers and the difference
counter's initial value; neither is assumed already present. -/
theorem init_exec (blank mark : Fin k) :
    ∃ tr, Exec (IQ (k := k) Terminal) blank (initProg blank mark)
      (fun _ => STape.blankTape blank) tr ∧ tr.length = 11 ∧
      applyTrace blank (fun _ => STape.blankTape blank) tr = TSQ (initQT blank mark) := by
  have he := literalProg_exec (Terminal := Terminal) blank (initActs blank mark) (blankQT blank)
  refine ⟨avecsQ blank (initActs blank mark) (blankQT blank), he, ?_, ?_⟩
  · rw [avecsQ_length]; rfl
  · change applyTrace blank (TSQ (blankQT blank)) _ = _
    rw [applyTrace_avecsQ, init_run]

/-- info: 'PalPeg.RTQueueInit.init_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms init_exec

end PalPeg.RTQueueInit
