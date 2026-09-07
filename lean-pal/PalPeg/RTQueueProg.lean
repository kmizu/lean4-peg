import PalPeg.RTQueueTapes
import PalPeg.ProgLangLib

/-!
# The Hood–Melville queue as a finite-control `Prog` (`RTQueueProg`)

`PalPeg.RTQueueTapes` realises the real-time queue as **lists of tape actions**
(`List (Act k)`) computed from the queue value.  This file re-expresses those
programs as terms of the structured language `PalPeg.ProgLang.Prog` over the
queue's ten tapes, and proves that running such a term for exactly the length of
its action list performs the very same actions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.RTQueueProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.Tape
open PalPeg.RTQueue
open PalPeg.RTQueueTapes

variable {k : ℕ}

/-! ## 1. The ten roles as `Fin 10` -/

/-- Index of a role. -/
def ridx : Role → Fin 10
  | .front => 0 | .fdup => 1 | .rear => 2 | .f => 3 | .fp => 4
  | .r => 5 | .rp => 6 | .rpdup => 7 | .ok => 8 | .dd => 9

/-- The role of an index. -/
def role : Fin 10 → Role
  | 0 => .front | 1 => .fdup | 2 => .rear | 3 => .f | 4 => .fp
  | 5 => .r | 6 => .rp | 7 => .rpdup | 8 => .ok | 9 => .dd

@[simp] theorem role_ridx (ρ : Role) : role (ridx ρ) = ρ := by cases ρ <;> rfl

@[simp] theorem ridx_role (j : Fin 10) : ridx (role j) = j := by fin_cases j <;> rfl

theorem ridx_injective {ρ ρ' : Role} (h : ridx ρ = ridx ρ') : ρ = ρ' := by
  have := congrArg role h; simpa using this

@[simp] theorem ridx_eq_iff (ρ ρ' : Role) : ridx ρ = ridx ρ' ↔ ρ = ρ' :=
  ⟨ridx_injective, fun h => h ▸ rfl⟩

instance : Fintype Role :=
  Fintype.ofList [.front, .fdup, .rear, .f, .fp, .r, .rp, .rpdup, .ok, .dd]
    (by rintro (_|_|_|_|_|_|_|_|_|_) <;> simp)

/-! ## 2. Action and condition identifiers -/

/-- An action identifier: which tape, what to write, where to move.  Writes are
literal symbols; a symbol read off one tape is transported to another by a
zero-cost finite dispatch on the read symbol (`caseSym`), which is exactly what
"the finite control carries the cell just popped" means. -/
abbrev ActQ (k : ℕ) := Role × Fin k × Move

/-- A condition identifier: tape `ρ` currently reads `c`. -/
abbrev CondQ (k : ℕ) := Role × Fin k

/-- The interpretation of the ten-tape queue actions. -/
def IQ (Terminal : Type) : Interp Terminal (ActQ k) (CondQ k) (Fin k) 10 where
  actOf a _ σ := touchVec (ridx a.1) a.2.1 a.2.2 σ
  condOf c σ := decide (σ (ridx c.1) = c.2)

theorem inputFree_IQ (Terminal : Type) : InputFree (IQ (k := k) Terminal) :=
  fun _ _ _ => rfl

/-! ## 3. Tape bundles -/

/-- The artifact's tape as a `ProgLang` zipper. -/
def toS (tp : TapeConfiguration k) : STape (Fin k) := ⟨tp.left, tp.focus, tp.right⟩

@[simp] theorem toS_focus (tp : TapeConfiguration k) : (toS tp).focus = tp.focus := rfl

/-- The ten tapes as a `ProgLang` bundle. -/
def TSQ (qt : QT k) : Fin 10 → STape (Fin k) := fun j => toS (qt (role j))

@[simp] theorem TSQ_focus (qt : QT k) (j : Fin 10) : ((TSQ qt) j).focus = (qt (role j)).focus :=
  rfl

theorem toS_step (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) (m : Move) :
    toS (PalPeg.Tape.step blank tp a m) = (toS tp).applyAction blank (a, m) := by
  obtain ⟨L, f, R⟩ := tp
  cases m <;> cases L <;> cases R <;> rfl

/-! ## 4. Action lists as write+move vectors -/

/-- The write+move vector of one concrete tape action. -/
def avecQ (qt : QT k) (a : Act k) : Fin 10 → Fin k × Move :=
  fun j => if j = ridx a.role then (a.write, a.move) else ((qt (role j)).focus, Move.stay)

/-- The vector list of an action list, each evaluated in its own state. -/
def avecsQ (blank : Fin k) : List (Act k) → QT k → List (Fin 10 → Fin k × Move)
  | [], _ => []
  | a :: l, qt => avecQ qt a :: avecsQ blank l (act blank qt a.role a.write a.move)

@[simp] theorem avecsQ_nil (blank : Fin k) (qt : QT k) : avecsQ blank [] qt = [] := rfl

@[simp] theorem avecsQ_cons (blank : Fin k) (a : Act k) (l : List (Act k)) (qt : QT k) :
    avecsQ blank (a :: l) qt
      = avecQ qt a :: avecsQ blank l (act blank qt a.role a.write a.move) := rfl

@[simp] theorem avecsQ_length (blank : Fin k) :
    ∀ (l : List (Act k)) (qt : QT k), (avecsQ blank l qt).length = l.length := by
  intro l
  induction l with
  | nil => intro qt; rfl
  | cons a l ih => intro qt; simp [ih]

theorem run_cons' (blank : Fin k) (qt : QT k) (a : Act k) (l : List (Act k)) :
    run blank qt (a :: l) = run blank (act blank qt a.role a.write a.move) l := by
  cases a; rfl

theorem avecsQ_append (blank : Fin k) :
    ∀ (l₁ l₂ : List (Act k)) (qt : QT k),
      avecsQ blank (l₁ ++ l₂) qt
        = avecsQ blank l₁ qt ++ avecsQ blank l₂ (run blank qt l₁) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ qt; rfl
  | cons a l ih => intro l₂ qt; simp [ih, run_cons']

theorem applyTrace_avecQ (blank : Fin k) (qt : QT k) (a : Act k) :
    (fun j => ((TSQ qt) j).applyAction blank (avecQ qt a j))
      = TSQ (act blank qt a.role a.write a.move) := by
  funext j
  by_cases hj : j = ridx a.role
  · subst hj
    show (toS (qt (role (ridx a.role)))).applyAction blank _
      = toS (act blank qt a.role a.write a.move (role (ridx a.role)))
    rw [role_ridx]
    simp only [avecQ, act_apply]
    exact (toS_step blank (qt a.role) a.write a.move).symm
  · show (toS (qt (role j))).applyAction blank (avecQ qt a j)
      = toS (act blank qt a.role a.write a.move (role j))
    have hne : role j ≠ a.role := by
      intro hc; exact hj (by rw [← ridx_role j, hc])
    simp only [avecQ, if_neg hj, act_apply, if_neg hne]
    rfl

theorem applyTrace_avecsQ (blank : Fin k) :
    ∀ (l : List (Act k)) (qt : QT k),
      applyTrace blank (TSQ qt) (avecsQ blank l qt) = TSQ (run blank qt l) := by
  intro l
  induction l with
  | nil => intro qt; rfl
  | cons a l ih =>
      intro qt
      rw [avecsQ_cons, applyTrace_cons]
      show applyTrace blank (fun j => ((TSQ qt) j).applyAction blank (avecQ qt a j)) _ = _
      rw [applyTrace_avecQ, ih]
      rfl

/-! ## 5. `Exec` for concrete action lists -/

section ExecQ

variable (Terminal : Type)

/-- "The program `P` performs, from the tapes `qt`, exactly the action list `L`
and returns to its continuation." -/
def ExecQ (blank : Fin k) (P : Prog (ActQ k) (CondQ k)) (qt : QT k)
    (L : List (Act k)) : Prop :=
  Exec (IQ (k := k) Terminal) blank P (TSQ qt) (avecsQ blank L qt)

variable {Terminal}
variable {blank : Fin k}

theorem execQ_of_eq {P : Prog (ActQ k) (CondQ k)} {qt : QT k} {L L' : List (Act k)}
    (h : L = L') (hE : ExecQ Terminal blank P qt L) : ExecQ Terminal blank P qt L' := h ▸ hE

theorem execQ_skip (qt : QT k) : ExecQ Terminal blank Prog.skip qt [] :=
  exec_skip (I := IQ (k := k) Terminal) _

theorem execQ_act (ρ : Role) (w : Fin k) (m : Move) (qt : QT k) :
    ExecQ Terminal blank (Prog.act (ρ, w, m)) qt [⟨ρ, w, m⟩] := by
  have h := exec_act (I := IQ (k := k) Terminal) (blank := blank)
    (inputFree_IQ Terminal) (ρ, w, m) (TSQ qt)
  refine exec_of_eq ?_ h
  show [actVec (IQ (k := k) Terminal) (ρ, w, m) (TSQ qt)] = [avecQ qt ⟨ρ, w, m⟩]
  rfl

theorem execQ_seq {P Q : Prog (ActQ k) (CondQ k)} {qt : QT k} {L₁ L₂ : List (Act k)}
    (h1 : ExecQ Terminal blank P qt L₁)
    (h2 : ExecQ Terminal blank Q (run blank qt L₁) L₂) :
    ExecQ Terminal blank (Prog.seq P Q) qt (L₁ ++ L₂) := by
  unfold ExecQ at h1 h2 ⊢
  rw [avecsQ_append]
  refine exec_seq h1 ?_
  rwa [applyTrace_avecsQ]

theorem execQ_ite_pos {ρ : Role} {c : Fin k} {P Q : Prog (ActQ k) (CondQ k)} {qt : QT k}
    {L : List (Act k)} (hc : (qt ρ).focus = c) (hP : ExecQ Terminal blank P qt L) :
    ExecQ Terminal blank (Prog.ite (ρ, c) P Q) qt L := by
  refine exec_ite_pos ?_ hP
  show decide ((qt (role (ridx ρ))).focus = c) = true
  rw [role_ridx, hc]; simp

theorem execQ_ite_neg {ρ : Role} {c : Fin k} {P Q : Prog (ActQ k) (CondQ k)} {qt : QT k}
    {L : List (Act k)} (hc : (qt ρ).focus ≠ c) (hQ : ExecQ Terminal blank Q qt L) :
    ExecQ Terminal blank (Prog.ite (ρ, c) P Q) qt L := by
  refine exec_ite_neg ?_ hQ
  show decide ((qt (role (ridx ρ))).focus = c) = false
  rw [role_ridx]; simpa using hc

/-- **Running the program is running the action list.**  Feeding the program
`|L|` micro-steps performs exactly the trace `avecsQ blank L qt`, and the
resulting tapes are the ones the action list produces. -/
theorem execQ_trace {P : Prog (ActQ k) (CondQ k)} {qt : QT k} {L : List (Act k)}
    (h : ExecQ Terminal blank P qt L) (r : Stack (ActQ k) (CondQ k))
    (l : List (Option Terminal)) (hl : l.length = L.length) :
    trace (IQ (k := k) Terminal) blank l (P :: r, TSQ qt) = avecsQ blank L qt :=
  Exec.trace_eq h r l (by rw [hl, avecsQ_length])

theorem execQ_exec {P : Prog (ActQ k) (CondQ k)} {qt : QT k} {L : List (Act k)}
    (h : ExecQ Terminal blank P qt L) (l : List (Option Terminal))
    (hl : l.length = L.length) :
    (runInputs (IQ (k := k) Terminal) blank l ([P], TSQ qt)).2 = TSQ (run blank qt L) := by
  rw [runInputs_snd_eq_applyTrace]
  have := execQ_trace h [] l hl
  rw [show ((P :: ([] : Stack (ActQ k) (CondQ k)))) = [P] from rfl] at this
  show applyTrace blank (TSQ qt) (trace (IQ (k := k) Terminal) blank l ([P], TSQ qt)) = _
  rw [this, applyTrace_avecsQ]

/-- **Halting.**  One micro-step past the end of the action list, the control
stack is empty: the program has really finished. -/
theorem execQ_halts {P : Prog (ActQ k) (CondQ k)} {qt : QT k} {L : List (Act k)}
    (h : ExecQ Terminal blank P qt L) (l : List (Option Terminal))
    (hl : l.length = L.length) (x : Option Terminal) :
    (runInputs (IQ (k := k) Terminal) blank (l ++ [x]) ([P], TSQ qt)).1 = [] :=
  exec_halts h l (by rw [hl, avecsQ_length]) x

end ExecQ

/-! ## 6. Zero-cost dispatch on a read symbol -/

/-- Nested `ite` over a list of candidate symbols. -/
def caseSymAux (ρ : Role) (body : Fin k → Prog (ActQ k) (CondQ k)) :
    List (Fin k) → Prog (ActQ k) (CondQ k)
  | [] => Prog.skip
  | c :: cs => Prog.ite (ρ, c) (body c) (caseSymAux ρ body cs)

/-- **Finite dispatch on the symbol tape `ρ` is reading.**  Pure control: it
costs no micro-step, and it is how a symbol just read off one tape is written
onto another one later. -/
def caseSym (ρ : Role) (body : Fin k → Prog (ActQ k) (CondQ k)) : Prog (ActQ k) (CondQ k) :=
  caseSymAux ρ body (List.finRange k)

section Case

variable {Terminal : Type} {blank : Fin k}

theorem execQ_caseSymAux {ρ : Role} {body : Fin k → Prog (ActQ k) (CondQ k)} {qt : QT k}
    {L : List (Act k)} (cs : List (Fin k)) (hmem : (qt ρ).focus ∈ cs)
    (h : ExecQ Terminal blank (body (qt ρ).focus) qt L) :
    ExecQ Terminal blank (caseSymAux ρ body cs) qt L := by
  induction cs with
  | nil => simp at hmem
  | cons c cs ih =>
      by_cases hc : (qt ρ).focus = c
      · refine execQ_ite_pos hc ?_
        rw [← hc]; exact h
      · refine execQ_ite_neg hc (ih ?_)
        rcases List.mem_cons.1 hmem with h' | h'
        · exact absurd h' hc
        · exact h'

theorem execQ_caseSym {ρ : Role} {body : Fin k → Prog (ActQ k) (CondQ k)} {qt : QT k}
    {L : List (Act k)} (h : ExecQ Terminal blank (body (qt ρ).focus) qt L) :
    ExecQ Terminal blank (caseSym ρ body) qt L :=
  execQ_caseSymAux _ (List.mem_finRange _) h

end Case

/-! ## 7. Role renaming (the finite control's tape assignment) -/

/-- Rename the tape an action refers to. -/
def renameAct (π : Role → Role) (a : Act k) : Act k := ⟨π a.role, a.write, a.move⟩

/-- Rename a whole action list. -/
def renameL (π : Role → Role) (L : List (Act k)) : List (Act k) := L.map (renameAct π)

@[simp] theorem renameL_nil (π : Role → Role) : renameL (k := k) π [] = [] := rfl

@[simp] theorem renameL_cons (π : Role → Role) (a : Act k) (L : List (Act k)) :
    renameL π (a :: L) = renameAct π a :: renameL π L := rfl

@[simp] theorem renameL_append (π : Role → Role) (L₁ L₂ : List (Act k)) :
    renameL π (L₁ ++ L₂) = renameL π L₁ ++ renameL π L₂ := List.map_append

@[simp] theorem renameL_length (π : Role → Role) (L : List (Act k)) :
    (renameL π L).length = L.length := List.length_map _

theorem act_comp_rename {π : Role → Role} (hπ : Function.Injective π) (blank : Fin k)
    (qt : QT k) (ρ : Role) (w : Fin k) (m : Move) :
    (act blank qt (π ρ) w m) ∘ π = act blank (qt ∘ π) ρ w m := by
  funext ρ'
  show (if π ρ' = π ρ then _ else _) = if ρ' = ρ then _ else _
  by_cases h : ρ' = ρ
  · simp [h]
  · rw [if_neg h, if_neg (fun hc => h (hπ hc))]; rfl

/-- **Renaming is a change of the control's tape assignment.**  Running the
renamed action list on the physical tapes is running the original one on the
logical (role-indexed) view. -/
theorem run_rename {π : Role → Role} (hπ : Function.Injective π) (blank : Fin k) :
    ∀ (L : List (Act k)) (qt : QT k),
      (run blank qt (renameL π L)) ∘ π = run blank (qt ∘ π) L := by
  intro L
  induction L with
  | nil => intro qt; rfl
  | cons a l ih =>
      intro qt
      show (run blank (act blank qt (π a.role) a.write a.move) (renameL π l)) ∘ π
        = run blank (act blank (qt ∘ π) a.role a.write a.move) l
      rw [ih, act_comp_rename hπ]

theorem run_append (blank : Fin k) :
    ∀ (L₁ L₂ : List (Act k)) (qt : QT k),
      run blank qt (L₁ ++ L₂) = run blank (run blank qt L₁) L₂ := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ qt; rfl
  | cons a l ih => intro L₂ qt; simp [run_cons', ih]

theorem read_rename {π : Role → Role} (hπ : Function.Injective π) (blank : Fin k)
    (L : List (Act k)) (qt : QT k) (ρ : Role) :
    (run blank qt (renameL π L)) (π ρ) = (run blank (qt ∘ π) L) ρ :=
  congrFun (run_rename hπ blank L qt) ρ

/-! ## 8. Straight-line programs -/

/-- The straight-line program performing a literal action list on the tapes
currently assigned by `π`. -/
def straight (π : Role → Role) : List (Act k) → Prog (ActQ k) (CondQ k)
  | [] => Prog.skip
  | a :: L => Prog.seq (Prog.act (π a.role, a.write, a.move)) (straight π L)

theorem execQ_straight {Terminal : Type} {blank : Fin k} (π : Role → Role) :
    ∀ (L : List (Act k)) (qt : QT k),
      ExecQ Terminal blank (straight π L) qt (renameL π L) := by
  intro L
  induction L with
  | nil => intro qt; exact execQ_skip qt
  | cons a L ih =>
      intro qt
      have h1 : ExecQ Terminal blank (Prog.act (π a.role, a.write, a.move)) qt
          [renameAct π a] := execQ_act _ _ _ qt
      have h2 := ih (run blank qt [renameAct π a])
      exact execQ_seq h1 h2

/-! ## 9. One rotation step -/

/-- The shape of a rotation state, as far as `execProg` can tell: a finite tag
that the control carries.  (The lists and the counter it hides are unbounded;
only this tag enters the program.) -/
inductive EShape where
  | revCons | revNil | appZ | appS | nil
  deriving DecidableEq

/-- The shape of a rotation state: exactly the case analysis of `execProg`. -/
def eshapeOf : RotationState (Fin k) → EShape
  | .reversing _ (_ :: _) _ (_ :: _) _ => .revCons
  | .reversing _ [] _ [_] _ => .revNil
  | .appending 0 _ _ => .appZ
  | .appending (_ + 1) (_ :: _) _ => .appS
  | _ => .nil

/-- One rotation step as a program.  Every symbol written is either `blank` or a
symbol just read off a tape, transported by `caseSym`; so the action list is
`execProg` **verbatim**, with the same length. -/
def execStepProg (blank : Fin k) (π : Role → Role) : EShape → Prog (ActQ k) (CondQ k)
  | .nil => Prog.skip
  | .appZ => straight π [⟨.dd, blank, .right⟩]
  | .revCons =>
      Prog.seq (Prog.act (π .f, blank, .left))
        (caseSym (π .f) fun x =>
          Prog.seq (straight π [⟨.f, blank, .stay⟩, ⟨.fp, x, .right⟩, ⟨.r, blank, .left⟩])
            (caseSym (π .r) fun y =>
              straight π [⟨.r, blank, .stay⟩, ⟨.rp, y, .right⟩, ⟨.rpdup, y, .right⟩,
                ⟨.ok, blank, .right⟩, ⟨.dd, blank, .right⟩]))
  | .revNil =>
      Prog.seq (Prog.act (π .r, blank, .left))
        (caseSym (π .r) fun y =>
          straight π [⟨.r, blank, .stay⟩, ⟨.rp, y, .right⟩, ⟨.rpdup, y, .right⟩,
            ⟨.dd, blank, .right⟩])
  | .appS =>
      Prog.seq (Prog.act (π .fp, blank, .left))
        (caseSym (π .fp) fun x =>
          straight π [⟨.fp, blank, .stay⟩, ⟨.rp, x, .right⟩, ⟨.rpdup, x, .right⟩,
            ⟨.ok, blank, .left⟩, ⟨.ok, blank, .stay⟩, ⟨.dd, blank, .right⟩])

section ExecStep

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

/-- **One rotation step, as a `Prog`.**  Under the stack invariants of the five
rotation tapes, the program of shape `eshapeOf s` performs exactly the action
list `execProg blank s`, renamed by the current tape assignment. -/
theorem execQ_execStep (hπ : Function.Injective π) {qt : QT k}
    {s : RotationState (Fin k)} (hs : SEnc blank mark (qt ∘ π) s) :
    ExecQ Terminal blank (execStepProg blank π (eshapeOf s)) qt
      (renameL π (execProg blank s)) := by
  match s with
  | .idle => exact execQ_skip qt
  | .done _ => exact execQ_skip qt
  | .reversing _ [] _ [] _ => exact execQ_skip qt
  | .reversing _ [] _ (_ :: _ :: _) _ => exact execQ_skip qt
  | .reversing _ (_ :: _) _ [] _ => exact execQ_skip qt
  | .appending (_ + 1) [] _ => exact execQ_skip qt
  | .appending 0 _ _ => exact execQ_straight π _ qt
  | .reversing ok (x :: f) f' (y :: r) r' =>
      have hf : SStack blank mark ((qt ∘ π) .f) (x :: f) := hs.1
      have hr : SStack blank mark ((qt ∘ π) .r) (y :: r) := hs.2.2.1
      have hx : ((run blank qt (renameL π [(⟨Role.f, blank, Move.left⟩ : Act k)]))
          (π Role.f)).focus = x := by
        rw [read_rename hπ]
        show (PalPeg.Tape.step blank ((qt ∘ π) Role.f) blank Move.left).focus = x
        simpa using sstack_probe hf
      have hy : ((run blank (run blank qt (renameL π [(⟨Role.f, blank, Move.left⟩ : Act k)]))
            (renameL π [⟨Role.f, blank, Move.stay⟩, ⟨Role.fp, x, Move.right⟩,
              ⟨Role.r, blank, Move.left⟩])) (π Role.r)).focus = y := by
        rw [← run_append, ← renameL_append, read_rename hπ]
        show (PalPeg.Tape.step blank ((qt ∘ π) Role.r) blank Move.left).focus = y
        simpa using sstack_probe hr
      have inner : ExecQ Terminal blank
          (Prog.seq (straight π [⟨Role.f, blank, Move.stay⟩, ⟨Role.fp, x, Move.right⟩,
              ⟨Role.r, blank, Move.left⟩])
            (caseSym (π Role.r) fun y =>
              straight π [⟨Role.r, blank, Move.stay⟩, ⟨Role.rp, y, Move.right⟩,
                ⟨Role.rpdup, y, Move.right⟩, ⟨Role.ok, blank, Move.right⟩,
                ⟨Role.dd, blank, Move.right⟩]))
          (run blank qt (renameL π [(⟨Role.f, blank, Move.left⟩ : Act k)]))
          (renameL π [⟨Role.f, blank, Move.stay⟩, ⟨Role.fp, x, Move.right⟩,
              ⟨Role.r, blank, Move.left⟩] ++
            renameL π [⟨Role.r, blank, Move.stay⟩, ⟨Role.rp, y, Move.right⟩,
              ⟨Role.rpdup, y, Move.right⟩, ⟨Role.ok, blank, Move.right⟩,
              ⟨Role.dd, blank, Move.right⟩]) := by
        refine execQ_seq (execQ_straight π _ _) (execQ_caseSym ?_)
        rw [hy]
        exact execQ_straight π _ _
      have key : ExecQ Terminal blank (execStepProg blank π EShape.revCons) qt
          (renameL π [(⟨Role.f, blank, Move.left⟩ : Act k)] ++
            (renameL π [⟨Role.f, blank, Move.stay⟩, ⟨Role.fp, x, Move.right⟩,
              ⟨Role.r, blank, Move.left⟩] ++
              renameL π [⟨Role.r, blank, Move.stay⟩, ⟨Role.rp, y, Move.right⟩,
                ⟨Role.rpdup, y, Move.right⟩, ⟨Role.ok, blank, Move.right⟩,
                ⟨Role.dd, blank, Move.right⟩])) := by
        refine execQ_seq (execQ_act _ _ _ qt) (execQ_caseSym ?_)
        rw [hx]
        exact inner
      exact execQ_of_eq rfl key
  | .reversing ok [] f' [y] r' =>
      have hr : SStack blank mark ((qt ∘ π) .r) [y] := hs.2.2.1
      have hy : ((run blank qt (renameL π [(⟨Role.r, blank, Move.left⟩ : Act k)]))
          (π Role.r)).focus = y := by
        rw [read_rename hπ]
        show (PalPeg.Tape.step blank ((qt ∘ π) Role.r) blank Move.left).focus = y
        simpa using sstack_probe hr
      have key : ExecQ Terminal blank (execStepProg blank π EShape.revNil) qt
          (renameL π [(⟨Role.r, blank, Move.left⟩ : Act k)] ++
            renameL π [⟨Role.r, blank, Move.stay⟩, ⟨Role.rp, y, Move.right⟩,
              ⟨Role.rpdup, y, Move.right⟩, ⟨Role.dd, blank, Move.right⟩]) := by
        refine execQ_seq (execQ_act _ _ _ qt) (execQ_caseSym ?_)
        rw [hy]
        exact execQ_straight π _ _
      exact execQ_of_eq rfl key
  | .appending (ok + 1) (x :: f') r' =>
      have hfp : SStack blank mark ((qt ∘ π) .fp) (x :: f') := hs.2.1
      have hx : ((run blank qt (renameL π [(⟨Role.fp, blank, Move.left⟩ : Act k)]))
          (π Role.fp)).focus = x := by
        rw [read_rename hπ]
        show (PalPeg.Tape.step blank ((qt ∘ π) Role.fp) blank Move.left).focus = x
        simpa using sstack_probe hfp
      have key : ExecQ Terminal blank (execStepProg blank π EShape.appS) qt
          (renameL π [(⟨Role.fp, blank, Move.left⟩ : Act k)] ++
            renameL π [⟨Role.fp, blank, Move.stay⟩, ⟨Role.rp, x, Move.right⟩,
              ⟨Role.rpdup, x, Move.right⟩, ⟨Role.ok, blank, Move.left⟩,
              ⟨Role.ok, blank, Move.stay⟩, ⟨Role.dd, blank, Move.right⟩]) := by
        refine execQ_seq (execQ_act _ _ _ qt) (execQ_caseSym ?_)
        rw [hx]
        exact execQ_straight π _ _
      exact execQ_of_eq rfl key

end ExecStep

/-! ## 10. Performing a bounded number of micro-steps -/

/-- `Performs P qt n qt'`: the program `P`, run on the physical tapes `qt`,
executes exactly `n` actions and leaves the tapes `qt'`. -/
def Performs (Terminal : Type) (blank : Fin k) (P : Prog (ActQ k) (CondQ k))
    (qt : QT k) (n : ℕ) (qt' : QT k) : Prop :=
  ∃ L : List (Act k), ExecQ Terminal blank P qt L ∧ L.length = n ∧ run blank qt L = qt'

section Performs

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

theorem performs_skip (qt : QT k) : Performs Terminal blank Prog.skip qt 0 qt :=
  ⟨[], execQ_skip qt, rfl, rfl⟩

theorem performs_seq {P Q : Prog (ActQ k) (CondQ k)} {qt qt₁ qt₂ : QT k} {n₁ n₂ : ℕ}
    (h1 : Performs Terminal blank P qt n₁ qt₁) (h2 : Performs Terminal blank Q qt₁ n₂ qt₂) :
    Performs Terminal blank (Prog.seq P Q) qt (n₁ + n₂) qt₂ := by
  obtain ⟨L₁, hE1, hn1, hr1⟩ := h1
  obtain ⟨L₂, hE2, hn2, hr2⟩ := h2
  subst hr1
  exact ⟨L₁ ++ L₂, execQ_seq hE1 hE2, by simp [hn1, hn2], by rw [run_append]; exact hr2⟩

theorem performs_straight (L : List (Act k)) (qt : QT k) :
    Performs Terminal blank (straight π L) qt L.length (run blank qt (renameL π L)) :=
  ⟨renameL π L, execQ_straight π L qt, by simp, rfl⟩

theorem performs_ite_pos {ρ : Role} {c : Fin k} {P Q : Prog (ActQ k) (CondQ k)}
    {qt qt' : QT k} {n : ℕ} (hc : (qt ρ).focus = c)
    (h : Performs Terminal blank P qt n qt') :
    Performs Terminal blank (Prog.ite (ρ, c) P Q) qt n qt' := by
  obtain ⟨L, hE, hn, hr⟩ := h
  exact ⟨L, execQ_ite_pos hc hE, hn, hr⟩

theorem performs_ite_neg {ρ : Role} {c : Fin k} {P Q : Prog (ActQ k) (CondQ k)}
    {qt qt' : QT k} {n : ℕ} (hc : (qt ρ).focus ≠ c)
    (h : Performs Terminal blank Q qt n qt') :
    Performs Terminal blank (Prog.ite (ρ, c) P Q) qt n qt' := by
  obtain ⟨L, hE, hn, hr⟩ := h
  exact ⟨L, execQ_ite_neg hc hE, hn, hr⟩

theorem performs_caseSym {ρ : Role} {body : Fin k → Prog (ActQ k) (CondQ k)}
    {qt qt' : QT k} {n : ℕ} (h : Performs Terminal blank (body (qt ρ).focus) qt n qt') :
    Performs Terminal blank (caseSym ρ body) qt n qt' := by
  obtain ⟨L, hE, hn, hr⟩ := h
  exact ⟨L, execQ_caseSym hE, hn, hr⟩

/-- Running a `Performs` program for its `n` micro-steps produces the stated
tapes. -/
theorem performs_run {P : Prog (ActQ k) (CondQ k)} {qt qt' : QT k} {n : ℕ}
    (h : Performs Terminal blank P qt n qt') (l : List (Option Terminal))
    (hl : l.length = n) :
    (runInputs (IQ (k := k) Terminal) blank l ([P], TSQ qt)).2 = TSQ qt' := by
  obtain ⟨L, hE, hn, hr⟩ := h
  rw [← hr]
  exact execQ_exec hE l (by rw [hl, hn])

/-- Its trace has exactly `n` entries: one action per micro-step. -/
theorem performs_trace_length {P : Prog (ActQ k) (CondQ k)} {qt qt' : QT k} {n : ℕ}
    (h : Performs Terminal blank P qt n qt') (r : Stack (ActQ k) (CondQ k))
    (l : List (Option Terminal)) (hl : l.length = n) :
    (trace (IQ (k := k) Terminal) blank l (P :: r, TSQ qt)).length = n := by
  obtain ⟨L, hE, hn, _⟩ := h
  rw [execQ_trace hE r l (by rw [hl, hn]), avecsQ_length, hn]

/-- One micro-step past the end the control stack is empty: the program halts. -/
theorem performs_halts {P : Prog (ActQ k) (CondQ k)} {qt qt' : QT k} {n : ℕ}
    (h : Performs Terminal blank P qt n qt') (l : List (Option Terminal))
    (hl : l.length = n) (x : Option Terminal) :
    (runInputs (IQ (k := k) Terminal) blank (l ++ [x]) ([P], TSQ qt)).1 = [] := by
  obtain ⟨L, hE, hn, _⟩ := h
  exact execQ_halts hE l (by rw [hl, hn]) x

theorem performs_mono {P : Prog (ActQ k) (CondQ k)} {qt qt' : QT k} {n n' : ℕ}
    (h : Performs Terminal blank P qt n qt') (hn : n = n') :
    Performs Terminal blank P qt n' qt' := hn ▸ h

/-- The rotation step performs exactly `(execProg blank s).length` actions. -/
theorem performs_execStep (hπ : Function.Injective π) {qt : QT k}
    {s : RotationState (Fin k)} (hs : SEnc blank mark (qt ∘ π) s) :
    Performs Terminal blank (execStepProg blank π (eshapeOf s)) qt
      (execProg blank s).length (run blank qt (renameL π (execProg blank s))) :=
  ⟨renameL π (execProg blank s), execQ_execStep hπ hs, by simp, rfl⟩

end Performs

/-! ## 11. Role permutations performed by the finite control -/

/-- The role renaming of `installPerm`, as a map on roles. -/
def ipRole : Role → Role
  | .front => .rp | .fdup => .rpdup | .rp => .front | .rpdup => .fdup | ρ => ρ

/-- The role renaming of `rotStart`, as a map on roles. -/
def rsRole : Role → Role
  | .f => .fdup | .fdup => .f | .r => .rear | .rear => .r | ρ => ρ

@[simp] theorem ipRole_ipRole (ρ : Role) : ipRole (ipRole ρ) = ρ := by cases ρ <;> rfl

@[simp] theorem rsRole_rsRole (ρ : Role) : rsRole (rsRole ρ) = ρ := by cases ρ <;> rfl

theorem ipRole_injective : Function.Injective ipRole := fun a b h => by
  have := congrArg ipRole h; simpa using this

theorem rsRole_injective : Function.Injective rsRole := fun a b h => by
  have := congrArg rsRole h; simpa using this

theorem installPerm_eq (qt : QT k) : installPerm qt = qt ∘ ipRole := by
  funext ρ; cases ρ <;> rfl

theorem rotStart_eq (qt : QT k) : rotStart qt = qt ∘ rsRole := by
  funext ρ; cases ρ <;> rfl

theorem injective_comp {π σ : Role → Role} (hπ : Function.Injective π)
    (hσ : Function.Injective σ) : Function.Injective (π ∘ σ) := hπ.comp hσ

/-! ## 12. `invalidate`, `install`, and the front pop -/

/-- The finite tag `invProg` branches on. -/
inductive IShape where
  | ddDec | okZero | okDec | rpPop | nil
  deriving DecidableEq

/-- Exactly the case analysis of `invProg`. -/
def ishapeOf : RotationState (Fin k) → IShape
  | .idle => .ddDec
  | .reversing 0 _ _ _ _ => .okZero
  | .reversing (_ + 1) _ _ _ _ => .okDec
  | .appending 0 _ (_ :: _) => .rpPop
  | .appending (_ + 1) _ _ => .okDec
  | _ => .nil

/-- `invalidate` as a program: literal writes only. -/
def invStepProg (blank mark : Fin k) (π : Role → Role) : IShape → Prog (ActQ k) (CondQ k)
  | .ddDec => straight π [⟨.dd, blank, .left⟩, ⟨.dd, blank, .stay⟩]
  | .okZero => straight π [⟨.ok, blank, .left⟩, ⟨.ok, mark, .right⟩]
  | .okDec => straight π [⟨.ok, blank, .left⟩, ⟨.ok, blank, .stay⟩]
  | .rpPop => straight π [⟨.rp, blank, .left⟩, ⟨.rp, blank, .stay⟩,
      ⟨.rpdup, blank, .left⟩, ⟨.rpdup, blank, .stay⟩]
  | .nil => Prog.skip

/-- Is the rotation finished? -/
inductive DShape where
  | done | notDone
  deriving DecidableEq

/-- Exactly the case analysis of `installIf`. -/
def dshapeOf : RotationState (Fin k) → DShape
  | .done _ => .done
  | _ => .notDone

/-- Installing a finished rotation. -/
def installStepProg (blank mark : Fin k) (π : Role → Role) : DShape → Prog (ActQ k) (CondQ k)
  | .done => straight π (installProg blank mark)
  | .notDone => Prog.skip

/-- Is the rotation idle? -/
inductive TShape where
  | idle | busy
  deriving DecidableEq

/-- Exactly the case analysis of `tailFrontProg`. -/
def tshapeOf : RotationState (Fin k) → TShape
  | .idle => .idle
  | _ => .busy

/-- Popping the front (and its duplicate while idle). -/
def tailFrontP (blank : Fin k) (π : Role → Role) : TShape → Prog (ActQ k) (CondQ k)
  | .idle => straight π [⟨.front, blank, .left⟩, ⟨.front, blank, .stay⟩,
      ⟨.fdup, blank, .left⟩, ⟨.fdup, blank, .stay⟩]
  | .busy => straight π [⟨.front, blank, .left⟩, ⟨.front, blank, .stay⟩]

section Small

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

theorem performs_invStep (qt : QT k) (s : RotationState (Fin k)) :
    Performs Terminal blank (invStepProg blank mark π (ishapeOf s)) qt
      (invProg blank mark s).length (run blank qt (renameL π (invProg blank mark s))) := by
  match s with
  | .idle => exact performs_straight _ qt
  | .done _ => exact performs_skip qt
  | .reversing 0 _ _ _ _ => exact performs_straight _ qt
  | .reversing (_ + 1) _ _ _ _ => exact performs_straight _ qt
  | .appending 0 _ [] => exact performs_skip qt
  | .appending 0 _ (_ :: _) => exact performs_straight _ qt
  | .appending (_ + 1) _ _ => exact performs_straight _ qt

theorem performs_tailFront (qt : QT k) (s : RotationState (Fin k)) :
    Performs Terminal blank (tailFrontP blank π (tshapeOf s)) qt
      (tailFrontProg blank s).length (run blank qt (renameL π (tailFrontProg blank s))) := by
  cases s <;> exact performs_straight _ qt

end Small

/-! ## 13. Two rotation steps -/

/-- The tape assignment after (possibly) installing a finished rotation. -/
def perm2 (π : Role → Role) : DShape → (Role → Role)
  | .done => π ∘ ipRole
  | .notDone => π

/-- The three finite tags `exec2T` branches on. -/
structure C2 where
  e1 : EShape
  e2 : EShape
  d : DShape
  deriving DecidableEq

/-- The tags of a rotation state. -/
def c2Of (s : RotationState (Fin k)) : C2 :=
  ⟨eshapeOf s, eshapeOf (exec s), dshapeOf (exec (exec s))⟩

/-- Two rotation steps, installing the new front if the rotation completes. -/
def exec2Prog (blank mark : Fin k) (π : Role → Role) (c : C2) : Prog (ActQ k) (CondQ k) :=
  Prog.seq (execStepProg blank π c.e1)
    (Prog.seq (execStepProg blank π c.e2) (installStepProg blank mark π c.d))

section Exec2

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

/-- **`exec2` as a program.**  At most `21` micro-steps, exactly as many as
`exec2T` charges, and the resulting tapes agree with `exec2T` under the updated
tape assignment. -/
theorem performs_exec2 (hπ : Function.Injective π) {qt : QT k} {q : Queue (Fin k)}
    (cst : ℕ) (h : EncodesB blank mark (qt ∘ π) q 0) :
    ∃ (n : ℕ) (qt' : QT k),
      Performs Terminal blank (exec2Prog blank mark π (c2Of q.state)) qt n qt' ∧ n ≤ 21 ∧
      qt' ∘ perm2 π (dshapeOf (exec (exec q.state)))
        = (exec2T blank mark q ⟨qt ∘ π, cst⟩).qt ∧
      (exec2T blank mark q ⟨qt ∘ π, cst⟩).cost = cst + n := by
  set Q : QT k := qt ∘ π with hQ
  set L1 : List (Act k) := execProg blank q.state with hL1
  set L2 : List (Act k) := execProg blank (exec q.state) with hL2
  set qt1 : QT k := run blank qt (renameL π L1) with hqt1
  have hq1 : qt1 ∘ π = run blank Q L1 := run_rename hπ blank L1 qt
  have hs2 : SEnc blank mark (qt1 ∘ π) (exec q.state) := by
    rw [hq1]; exact exec_enc h.state
  have p1 : Performs Terminal blank (execStepProg blank π (eshapeOf q.state)) qt
      L1.length qt1 := performs_execStep hπ h.state
  set qt2 : QT k := run blank qt1 (renameL π L2) with hqt2
  have p2 : Performs Terminal blank (execStepProg blank π (eshapeOf (exec q.state))) qt1
      L2.length qt2 := performs_execStep hπ hs2
  have hq2 : qt2 ∘ π = run blank (run blank Q L1) L2 := by
    rw [hqt2, run_rename hπ, hq1]
  have hb1 : L1.length ≤ 9 := execProg_length blank q.state
  have hb2 : L2.length ≤ 9 := execProg_length blank (exec q.state)
  by_cases hdc : ∃ nf, exec (exec q.state) = RotationState.done nf
  · obtain ⟨nf, hn⟩ := hdc
    set qt3 : QT k := run blank qt2 (renameL π (installProg blank mark)) with hqt3
    have p3 : Performs Terminal blank (installStepProg blank mark π DShape.done) qt2
        (installProg blank mark).length qt3 := performs_straight _ qt2
    refine ⟨L1.length + (L2.length + (installProg blank mark).length), qt3, ?_, ?_, ?_, ?_⟩
    · have : (c2Of q.state).d = DShape.done := by
        show dshapeOf (exec (exec q.state)) = DShape.done
        rw [hn]; rfl
      rw [exec2Prog, this]
      exact performs_seq p1 (performs_seq p2 p3)
    · rw [installProg_length]; omega
    · have hd : dshapeOf (exec (exec q.state)) = DShape.done := by rw [hn]; rfl
      have he : exec2T blank mark q ⟨Q, cst⟩
          = Run.perm (Run.acts blank (Run.acts blank (Run.acts blank ⟨Q, cst⟩ L1) L2)
              (installProg blank mark)) installPerm := by
        unfold exec2T; rw [hn]; rfl
      rw [hd, he]
      show qt3 ∘ (π ∘ ipRole) = installPerm _
      rw [installPerm_eq]
      show qt3 ∘ (π ∘ ipRole) = (run blank (run blank (run blank Q L1) L2)
        (installProg blank mark)) ∘ ipRole
      have : qt3 ∘ π = run blank (run blank (run blank Q L1) L2) (installProg blank mark) := by
        rw [hqt3, run_rename hπ, hq2]
      rw [← this]; rfl
    · have he : exec2T blank mark q ⟨Q, cst⟩
          = Run.perm (Run.acts blank (Run.acts blank (Run.acts blank ⟨Q, cst⟩ L1) L2)
              (installProg blank mark)) installPerm := by
        unfold exec2T; rw [hn]; rfl
      rw [he]
      show cst + L1.length + L2.length + (installProg blank mark).length = _
      omega
  · have hnd : NotDone (exec (exec q.state)) := by
      cases hx : exec (exec q.state) with
      | done nf => exact absurd ⟨nf, hx⟩ hdc
      | idle => trivial
      | reversing _ _ _ _ _ => trivial
      | appending _ _ _ => trivial
    have hd : dshapeOf (exec (exec q.state)) = DShape.notDone := by
      cases hx : exec (exec q.state) with
      | done nf => exact absurd ⟨nf, hx⟩ hdc
      | idle => rfl
      | reversing _ _ _ _ _ => rfl
      | appending _ _ _ => rfl
    have he : exec2T blank mark q ⟨Q, cst⟩
        = Run.acts blank (Run.acts blank ⟨Q, cst⟩ L1) L2 := by
      unfold exec2T; exact installIf_not_done blank mark _ _ hnd
    refine ⟨L1.length + (L2.length + 0), qt2, ?_, by omega, ?_, ?_⟩
    · have : (c2Of q.state).d = DShape.notDone := hd
      rw [exec2Prog, this]
      exact performs_seq p1 (performs_seq p2 (performs_skip qt2))
    · rw [hd, he]; exact hq2
    · rw [he]; show cst + L1.length + L2.length = _; omega

end Exec2

/-! ## 14. `check`: the branch decided by a one-action probe -/

/-- The tags of the two branches of `check`. -/
structure CS where
  rot : C2
  nor : C2
  deriving DecidableEq

/-- The tags of a queue at a `check` point. -/
def csOf (q : Queue (Fin k)) : CS := ⟨c2Of (rotQ q).state, c2Of q.state⟩

/-- **`check` as a program.**  The one action `⟨dd, blank, left⟩` probes the
difference counter and the branch is taken on the symbol read: no numeric
comparison, and the probe is paid for by the action that writes the symbol
back. -/
def checkProg (blank mark : Fin k) (π : Role → Role) (c : CS) : Prog (ActQ k) (CondQ k) :=
  Prog.seq (Prog.act (π .dd, blank, .left))
    (Prog.ite (π .dd, mark)
      (Prog.seq (straight π [⟨.dd, mark, .right⟩])
        (exec2Prog blank mark (π ∘ rsRole) c.rot))
      (caseSym (π .dd) fun d =>
        Prog.seq (straight π [⟨.dd, d, .right⟩]) (exec2Prog blank mark π c.nor)))

section Check

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

theorem performs_check (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT k}
    {q : Queue (Fin k)} (cst : ℕ) (h : CEncodes blank mark (qt ∘ π) q)
    (hsi : SInv q.front q.state) (hlf : q.lenf = (frontList q.state q.front).length)
    (hlr : q.lenr = q.rear.length) :
    ∃ (n : ℕ) (qt' : QT k) (π' : Role → Role),
      Performs Terminal blank (checkProg blank mark π (csOf q)) qt n qt' ∧ n ≤ 23 ∧
      Function.Injective π' ∧
      qt' ∘ π' = (checkT blank mark q ⟨qt ∘ π, cst⟩).qt ∧
      (checkT blank mark q ⟨qt ∘ π, cst⟩).cost = cst + n := by
  set Q : QT k := qt ∘ π with hQ
  obtain ⟨n, hg, heq, hb⟩ := h.dd
  have hsym : dSym blank Q = if n = 0 then mark else blank := gcount_probe hg
  set qt1 : QT k := run blank qt (renameL π [(⟨Role.dd, blank, Move.left⟩ : Act k)]) with hqt1
  have p1 : Performs Terminal blank (Prog.act (π Role.dd, blank, Move.left)) qt 1 qt1 :=
    ⟨renameL π [⟨Role.dd, blank, Move.left⟩], execQ_act _ _ _ qt, rfl, rfl⟩
  have hq1 : qt1 ∘ π = run blank Q [⟨Role.dd, blank, Move.left⟩] := run_rename hπ blank _ qt
  have hfoc : (qt1 (π Role.dd)).focus = dSym blank Q := by
    rw [hqt1, read_rename hπ]
    rfl
  by_cases hc : dSym blank Q = mark
  · -- the probe read the marker: a rotation starts
    have hn0 : n = 0 := by
      by_contra hn
      rw [hsym, if_neg hn] at hc
      exact hne hc.symm
    subst hn0
    have hi : q.state = RotationState.idle := by
      by_contra hni
      exact absurd (hb hni) (by omega)
    have hrem0 : rem q.state = 0 := by rw [hi]; rfl
    have hfl : q.lenf = q.front.length := by rw [hlf, hi]; rfl
    set qt2 : QT k := run blank qt1 (renameL π [(⟨Role.dd, mark, Move.right⟩ : Act k)]) with hqt2
    have p2 : Performs Terminal blank (straight π [(⟨Role.dd, mark, Move.right⟩ : Act k)])
        qt1 1 qt2 := performs_straight _ qt1
    have hq2 : qt2 ∘ π
        = run blank (run blank Q [⟨Role.dd, blank, Move.left⟩])
            [⟨Role.dd, dSym blank Q, Move.right⟩] := by
      rw [hqt2, run_rename hπ, hq1, hc]
    have hg0 : GCount blank mark ((qt2 ∘ π) Role.dd) 0 := by
      rw [hq2, hc]
      exact gcount_dec_zero hg
    have hbase : EncodesB blank mark (qt2 ∘ π) q 0 := by
      refine ⟨?_, ?_, ?_, ?_, ⟨0, hg0, by omega, fun _ => Nat.zero_le _⟩⟩ <;>
        · rw [hq2]
          first
            | exact h.front | exact h.fdup | exact h.rear | exact h.state
    have hrot : EncodesB blank mark (qt2 ∘ (π ∘ rsRole)) (rotQ q) 0 := by
      have : qt2 ∘ (π ∘ rsRole) = rotStart (qt2 ∘ π) := by rw [rotStart_eq]; rfl
      rw [this]
      exact rot_enc hbase hi hg0 hfl (by omega)
    obtain ⟨n2, qt3, p3, hb2, hqt3, hcost3⟩ :=
      performs_exec2 (Terminal := Terminal) (hπ.comp rsRole_injective) (cst + 2) hrot
    have hchk : checkT blank mark q ⟨Q, cst⟩
        = exec2T blank mark (rotQ q) ⟨qt2 ∘ (π ∘ rsRole), cst + 2⟩ := by
      unfold checkT
      rw [if_pos hc]
      have hqe : rotStart (run blank (run blank Q [⟨Role.dd, blank, Move.left⟩])
          [⟨Role.dd, dSym blank Q, Move.right⟩]) = qt2 ∘ (π ∘ rsRole) := by
        rw [rotStart_eq, ← hq2]; rfl
      show exec2T blank mark (rotQ q)
        ⟨rotStart (run blank (run blank Q [⟨Role.dd, blank, Move.left⟩])
          [⟨Role.dd, dSym blank Q, Move.right⟩]), cst + 1 + 1⟩ = _
      rw [hqe]
    refine ⟨1 + (1 + n2), qt3,
      perm2 (π ∘ rsRole) (dshapeOf (exec (exec (rotQ q).state))), ?_, by omega, ?_, ?_, ?_⟩
    · rw [checkProg]
      exact performs_seq p1 (performs_ite_pos (by rw [hfoc]; exact hc) (performs_seq p2 p3))
    · cases hd : dshapeOf (exec (exec (rotQ q).state)) with
      | done => exact (hπ.comp rsRole_injective).comp ipRole_injective
      | notDone => exact hπ.comp rsRole_injective
    · rw [hchk]; exact hqt3
    · rw [hchk, hcost3]; omega
  · -- the probe read a blank: no rotation
    have hn : n ≠ 0 := by
      intro hn0
      rw [hsym, if_pos hn0] at hc
      exact hc rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsym' : dSym blank Q = blank := by rw [hsym, if_neg hn]
    set qt2 : QT k :=
      run blank qt1 (renameL π [(⟨Role.dd, dSym blank Q, Move.right⟩ : Act k)]) with hqt2
    have p2 : Performs Terminal blank
        (straight π [(⟨Role.dd, dSym blank Q, Move.right⟩ : Act k)]) qt1 1 qt2 :=
      performs_straight _ qt1
    have hq2 : qt2 ∘ π
        = run blank (run blank Q [⟨Role.dd, blank, Move.left⟩])
            [⟨Role.dd, dSym blank Q, Move.right⟩] := by
      rw [hqt2, run_rename hπ, hq1]
    have hgm : GCount blank mark ((qt2 ∘ π) Role.dd) (m + 1) := by
      rw [hq2, hsym']
      have hg' : SStack blank mark (Q .dd) (blank :: List.replicate m blank) := by
        rw [← List.replicate_succ]; exact hg
      exact sstack_peek2 hg'
    have hbase : EncodesB blank mark (qt2 ∘ π) q 0 := by
      refine ⟨?_, ?_, ?_, ?_, ⟨m + 1, hgm, by omega, fun _ => Nat.zero_le _⟩⟩ <;>
        · rw [hq2]
          first
            | exact h.front | exact h.fdup | exact h.rear | exact h.state
    obtain ⟨n2, qt3, p3, hb2, hqt3, hcost3⟩ :=
      performs_exec2 (Terminal := Terminal) hπ (cst + 2) hbase
    have hchk : checkT blank mark q ⟨Q, cst⟩ = exec2T blank mark q ⟨qt2 ∘ π, cst + 2⟩ := by
      unfold checkT
      rw [if_neg hc]
      show exec2T blank mark q ⟨run blank (run blank Q [⟨Role.dd, blank, Move.left⟩])
        [⟨Role.dd, dSym blank Q, Move.right⟩], cst + 1 + 1⟩ = _
      rw [← hq2]
    refine ⟨1 + (1 + n2), qt3, perm2 π (dshapeOf (exec (exec q.state))), ?_, by omega, ?_,
      ?_, ?_⟩
    · rw [checkProg]
      refine performs_seq p1 (performs_ite_neg (by rw [hfoc]; exact hc) ?_)
      refine performs_caseSym ?_
      rw [hfoc]
      exact performs_seq p2 p3
    · cases hd : dshapeOf (exec (exec q.state)) with
      | done => exact hπ.comp ipRole_injective
      | notDone => exact hπ
    · rw [hchk]; exact hqt3
    · rw [hchk, hcost3]; omega

end Check

/-! ## 15. `snoc` -/

/-- `snoc a`: push `a` on the rear, decrement the difference counter, `check`. -/
def snocProg (blank mark : Fin k) (π : Role → Role) (c : CS) (a : Fin k) :
    Prog (ActQ k) (CondQ k) :=
  Prog.seq (straight π [⟨.rear, a, .right⟩, ⟨.dd, blank, .left⟩, ⟨.dd, blank, .stay⟩])
    (checkProg blank mark π c)

/-- The finite tags `snoc` needs. -/
def snocCS (q : Queue (Fin k)) (a : Fin k) : CS :=
  csOf { q with lenr := q.lenr + 1, rear := a :: q.rear }

section Snoc

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

/-- **`snoc` as a program.**  At most `26` micro-steps — the same bound as the
action-list version — and the tapes agree with `snocT`. -/
theorem qsnoc_exec (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT k}
    {q : Queue (Fin k)} (a : Fin k) (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q)
    (hq : Inv q) :
    ∃ (n : ℕ) (qt' : QT k) (π' : Role → Role),
      Performs Terminal blank (snocProg blank mark π (snocCS q a) a) qt n qt' ∧ n ≤ 26 ∧
      Function.Injective π' ∧
      qt' ∘ π' = (snocT blank mark q a ⟨qt ∘ π, cst⟩).qt ∧
      (snocT blank mark q a ⟨qt ∘ π, cst⟩).cost = cst + n ∧
      Encodes blank mark (qt' ∘ π') (snoc q a) := by
  set Q : QT k := qt ∘ π with hQ
  set pre : List (Act k) :=
    [⟨Role.rear, a, Move.right⟩, ⟨Role.dd, blank, Move.left⟩, ⟨Role.dd, blank, Move.stay⟩]
    with hpre
  set qt1 : QT k := run blank qt (renameL π pre) with hqt1
  have p1 : Performs Terminal blank (straight π pre) qt 3 qt1 := performs_straight _ qt
  have hq1 : qt1 ∘ π = run blank Q pre := run_rename hπ blank pre qt
  set q' : Queue (Fin k) := { q with lenr := q.lenr + 1, rear := a :: q.rear } with hq'
  obtain ⟨n, hg, heq, hb⟩ := h.dd
  have hn1 : 1 ≤ n := dd_pos hq heq hb
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hCE : CEncodes blank mark (qt1 ∘ π) q' := by
    rw [hq1]
    refine ⟨h.front, h.fdup, sstack_push h.rear a, h.state, ⟨m, ?_, ?_, ?_⟩⟩
    · exact gcount_dec hg
    · show m + rem q.state + (q.lenr + 1) = q.lenf + 1
      omega
    · intro hni
      have := hb hni
      omega
  have hlr' : q.lenr + 1 = (a :: q.rear).length := by rw [hq.lenr_eq]; simp
  have hsn : snocT blank mark q a ⟨Q, cst⟩ = checkT blank mark q' ⟨qt1 ∘ π, cst + 3⟩ := by
    rw [hq1]; rfl
  obtain ⟨n2, qt2, π', p2, hb2, hinj, hqt2, hcost2⟩ :=
    performs_check (Terminal := Terminal) hπ hne (qt := qt1) (q := q') (cst + 3) hCE
      hq.sinv hq.lenf_eq hlr'
  refine ⟨3 + n2, qt2, π', performs_seq p1 p2, by omega, hinj, ?_, ?_, ?_⟩
  · rw [hsn]; exact hqt2
  · rw [hsn, hcost2]; omega
  · have : Encodes blank mark (checkT blank mark q' ⟨qt1 ∘ π, cst + 3⟩).qt (check q') :=
      checkT_encodes hne hCE hq.sinv hq.lenf_eq hlr'
    rw [hqt2]
    exact this

end Snoc

/-! ## 16. `tail` -/

/-- The finite tags `tail` needs.  `ne` is the one bit the control cannot read
for free: whether the queue is non-empty.  It is exactly what the two-action
`head?` probe (`headT`) reports, so a `tail` that follows a `head?` knows it. -/
structure TC where
  ne : Bool
  t : TShape
  i : IShape
  c : CS
  deriving DecidableEq

/-- The queue `check` is applied to by `tail`. -/
def tailQ (q : Queue (Fin k)) : Queue (Fin k) :=
  { q with lenf := q.lenf - 1, front := q.front.tail, state := invalidate q.state }

/-- The tags of a queue for `tail`. -/
def tcOf (q : Queue (Fin k)) : TC :=
  ⟨!q.front.isEmpty, tshapeOf q.state, ishapeOf q.state, csOf (tailQ q)⟩

/-- `tail`: pop the front (and its duplicate while idle), `invalidate`, `check`. -/
def tailProg (blank mark : Fin k) (π : Role → Role) (c : TC) : Prog (ActQ k) (CondQ k) :=
  if c.ne then
    Prog.seq (tailFrontP blank π c.t)
      (Prog.seq (invStepProg blank mark π c.i) (checkProg blank mark π c.c))
  else Prog.skip

section Tail

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

/-- **`tail` as a program.**  At most `31` micro-steps — the same bound as the
action-list version — and the tapes agree with `tailT`. -/
theorem qtail_exec (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT k}
    {q : Queue (Fin k)} (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q) (hq : Inv q) :
    ∃ (n : ℕ) (qt' : QT k) (π' : Role → Role),
      Performs Terminal blank (tailProg blank mark π (tcOf q)) qt n qt' ∧ n ≤ 31 ∧
      Function.Injective π' ∧
      qt' ∘ π' = (tailT blank mark q ⟨qt ∘ π, cst⟩).qt ∧
      (tailT blank mark q ⟨qt ∘ π, cst⟩).cost = cst + n ∧
      Encodes blank mark (qt' ∘ π') (RTQueue.tail q) := by
  set Q : QT k := qt ∘ π with hQ
  cases hfr : q.front with
  | nil =>
      have hne0 : (tcOf q).ne = false := by simp [tcOf, hfr]
      have e1 : RTQueue.tail q = q := by unfold RTQueue.tail; rw [hfr]
      have e2 : tailT blank mark q ⟨Q, cst⟩ = ⟨Q, cst⟩ := by unfold tailT; rw [hfr]
      refine ⟨0, qt, π, ?_, by omega, hπ, ?_, ?_, ?_⟩
      · rw [tailProg, hne0]; exact performs_skip qt
      · rw [e2]
      · rw [e2]; rfl
      · rw [e1]; exact h
  | cons x f =>
      have hnet : (tcOf q).ne = true := by simp [tcOf, hfr]
      set q'' : Queue (Fin k) :=
        { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } with hq''
      have htq : tailQ q = q'' := by simp [hq'', tailQ, hfr]
      set qt1 : QT k := run blank qt (renameL π (tailFrontProg blank q.state)) with hqt1
      have p1 : Performs Terminal blank (tailFrontP blank π (tshapeOf q.state)) qt
          (tailFrontProg blank q.state).length qt1 := performs_tailFront qt q.state
      have hq1 : qt1 ∘ π = run blank Q (tailFrontProg blank q.state) := run_rename hπ blank _ qt
      set qt2 : QT k := run blank qt1 (renameL π (invProg blank mark q.state)) with hqt2
      have p2 : Performs Terminal blank (invStepProg blank mark π (ishapeOf q.state)) qt1
          (invProg blank mark q.state).length qt2 := performs_invStep qt1 q.state
      have hq2 : qt2 ∘ π
          = run blank (run blank Q (tailFrontProg blank q.state))
              (invProg blank mark q.state) := by rw [hqt2, run_rename hπ, hq1]
      obtain ⟨hsi', hfl, hrm⟩ := invalidate_spec hfr hq.sinv hq.nd hq.pot_front
      obtain ⟨n, hg, heq, hb⟩ := h.dd
      obtain ⟨ki1, ki2, ki3⟩ := inv_keeps blank mark
        (run blank Q (tailFrontProg blank q.state)) q.state
      obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
      have hlenf : 1 ≤ q.lenf := by rw [hq.lenf_eq, hP, hfr]; simp
      have hCE : CEncodes blank mark (qt2 ∘ π) q'' := by
        rw [hq2]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show SStack blank mark _ f
          rw [ki1, tailFront_front]
          exact sstack_pop2 (hfr ▸ h.front)
        · show SStack blank mark _ (qFdup _)
          rw [ki2]
          by_cases hi : q.state = RotationState.idle
          · have hidle : invalidate q.state = RotationState.idle := by rw [hi]; rfl
            rw [qFdup_mk_idle hidle, hi, tailFront_fdup_idle]
            have hfd : SStack blank mark (Q .fdup) (x :: f) := by
              rw [← hfr, ← qFdup_eq_front hi]; exact h.fdup
            exact sstack_pop2 hfd
          · rw [qFdup_mk_ne (invalidate_ne_idle hi), tailFront_fdup_ne blank Q hi,
              ← qFdup_eq_nil hi]
            exact h.fdup
        · show SStack blank mark _ q.rear
          rw [ki3, tailFront_rear]
          exact h.rear
        · exact inv_enc (tailFront_senc h.state)
        · by_cases hi : q.state = RotationState.idle
          · have hrem0 : rem q.state = 0 := by rw [hi]; rfl
            have hrem0' : rem (invalidate q.state) = 0 := by rw [hi]; rfl
            have hn1 : 1 ≤ n := dd_pos hq heq hb
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            refine ⟨m, ?_, ?_, ?_⟩
            · have e : run blank (run blank Q (tailFrontProg blank q.state))
                  (invProg blank mark q.state) .dd
                  = step blank (step blank (Q .dd) blank .left) blank .stay := by
                rw [hi]; exact tailInv_dd_idle blank mark Q
              rw [e]
              exact gcount_dec hg
            · show m + rem (invalidate q.state) + q.lenr = q.lenf - 1 + 1
              omega
            · intro hni
              exact absurd (show invalidate q.state = RotationState.idle by rw [hi]; rfl) hni
          · have hrs : rem q.state ≠ 0 := rem_ne_zero_of_ne_idle hq.nd hi
            have hge := inv_rem_ge q.state
            have hexact : rem (invalidate q.state) + 1 = rem q.state := by omega
            refine ⟨n, ?_, ?_, ?_⟩
            · rw [tailInv_dd_ne blank mark Q hi]
              exact hg
            · show n + rem (invalidate q.state) + q.lenr = q.lenf - 1 + 1
              omega
            · intro _
              have := hb hi
              omega
      have hlf'' : q''.lenf = (frontList q''.state q''.front).length := by
        show q.lenf - 1 = (frontList (invalidate q.state) f).length
        rw [hfl, hq.lenf_eq]; simp
      have htl : tailT blank mark q ⟨Q, cst⟩
          = checkT blank mark q'' ⟨qt2 ∘ π,
              cst + (tailFrontProg blank q.state).length
                + (invProg blank mark q.state).length⟩ := by
        rw [hq2]
        unfold tailT
        rw [hfr]
        rfl
      obtain ⟨n2, qt3, π', p3, hb3, hinj, hqt3, hcost3⟩ :=
        performs_check (Terminal := Terminal) hπ hne (qt := qt2) (q := q'')
          (cst + (tailFrontProg blank q.state).length + (invProg blank mark q.state).length)
          hCE hsi' hlf'' hq.lenr_eq
      have hb1 : (tailFrontProg blank q.state).length ≤ 4 := tailFrontProg_length blank q.state
      have hb2 : (invProg blank mark q.state).length ≤ 4 := invProg_length blank mark q.state
      refine ⟨(tailFrontProg blank q.state).length
        + ((invProg blank mark q.state).length + n2), qt3, π', ?_, by omega, hinj, ?_, ?_, ?_⟩
      · rw [tailProg, hnet]
        show Performs Terminal blank (Prog.seq (tailFrontP blank π (tcOf q).t)
          (Prog.seq (invStepProg blank mark π (tcOf q).i) (checkProg blank mark π (tcOf q).c)))
          qt _ qt3
        have hc : (tcOf q).c = csOf q'' := by rw [tcOf, htq]
        have ht : (tcOf q).t = tshapeOf q.state := rfl
        have hi : (tcOf q).i = ishapeOf q.state := rfl
        rw [hc, ht, hi]
        exact performs_seq p1 (performs_seq p2 p3)
      · rw [htl]; exact hqt3
      · rw [htl, hcost3]; omega
      · have : Encodes blank mark (checkT blank mark q'' ⟨qt2 ∘ π,
            cst + (tailFrontProg blank q.state).length
              + (invProg blank mark q.state).length⟩).qt (check q'') :=
          checkT_encodes hne hCE hsi' hlf'' hq.lenr_eq
        have he1 : RTQueue.tail q = check q'' := by unfold RTQueue.tail; rw [hfr]
        rw [← hqt3] at this
        rw [he1]
        exact this

end Tail

/-! ## 17. The downstream interface -/

section Interface

variable {Terminal : Type} {blank mark : Fin k} {π : Role → Role}

/-- **`snoc`: replace "apply the action list" by "run the program".**  For the
`n ≤ 26` micro-steps of the operation the trace has exactly `n` entries, the
tapes end where `snocT` says, the program halts, and the queue invariant is
carried over. -/
theorem qsnoc_trace (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT k}
    {q : Queue (Fin k)} (a : Fin k) (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q)
    (hq : Inv q) :
    ∃ (n : ℕ) (qt' : QT k) (π' : Role → Role),
      n ≤ 26 ∧ Function.Injective π' ∧
      qt' ∘ π' = (snocT blank mark q a ⟨qt ∘ π, cst⟩).qt ∧
      (snocT blank mark q a ⟨qt ∘ π, cst⟩).cost = cst + n ∧
      Encodes blank mark (qt' ∘ π') (snoc q a) ∧
      (∀ (l : List (Option Terminal)), l.length = n →
        (runInputs (IQ (k := k) Terminal) blank l
            ([snocProg blank mark π (snocCS q a) a], TSQ qt)).2 = TSQ qt') ∧
      (∀ (r : Stack (ActQ k) (CondQ k)) (l : List (Option Terminal)), l.length = n →
        (trace (IQ (k := k) Terminal) blank l
            (snocProg blank mark π (snocCS q a) a :: r, TSQ qt)).length = n) ∧
      (∀ (l : List (Option Terminal)), l.length = n → ∀ x : Option Terminal,
        (runInputs (IQ (k := k) Terminal) blank (l ++ [x])
            ([snocProg blank mark π (snocCS q a) a], TSQ qt)).1 = []) := by
  obtain ⟨n, qt', π', hp, hb, hinj, hqt, hcost, henc⟩ :=
    qsnoc_exec (Terminal := Terminal) hπ hne a cst h hq
  exact ⟨n, qt', π', hb, hinj, hqt, hcost, henc,
    fun l hl => performs_run hp l hl,
    fun r l hl => performs_trace_length hp r l hl,
    fun l hl x => performs_halts hp l hl x⟩

/-- **`tail`: the same, with the `≤ 31` bound.** -/
theorem qtail_trace (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT k}
    {q : Queue (Fin k)} (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q) (hq : Inv q) :
    ∃ (n : ℕ) (qt' : QT k) (π' : Role → Role),
      n ≤ 31 ∧ Function.Injective π' ∧
      qt' ∘ π' = (tailT blank mark q ⟨qt ∘ π, cst⟩).qt ∧
      (tailT blank mark q ⟨qt ∘ π, cst⟩).cost = cst + n ∧
      Encodes blank mark (qt' ∘ π') (RTQueue.tail q) ∧
      (∀ (l : List (Option Terminal)), l.length = n →
        (runInputs (IQ (k := k) Terminal) blank l
            ([tailProg blank mark π (tcOf q)], TSQ qt)).2 = TSQ qt') ∧
      (∀ (r : Stack (ActQ k) (CondQ k)) (l : List (Option Terminal)), l.length = n →
        (trace (IQ (k := k) Terminal) blank l
            (tailProg blank mark π (tcOf q) :: r, TSQ qt)).length = n) ∧
      (∀ (l : List (Option Terminal)), l.length = n → ∀ x : Option Terminal,
        (runInputs (IQ (k := k) Terminal) blank (l ++ [x])
            ([tailProg blank mark π (tcOf q)], TSQ qt)).1 = []) := by
  obtain ⟨n, qt', π', hp, hb, hinj, hqt, hcost, henc⟩ :=
    qtail_exec (Terminal := Terminal) hπ hne cst h hq
  exact ⟨n, qt', π', hb, hinj, hqt, hcost, henc,
    fun l hl => performs_run hp l hl,
    fun r l hl => performs_trace_length hp r l hl,
    fun l hl x => performs_halts hp l hl x⟩

/-- **The rotation's incremental step.**  One `exec` step is `≤ 9` micro-steps
and its trace is the action list `execProg` verbatim. -/
theorem qexec_trace (hπ : Function.Injective π) {qt : QT k} {s : RotationState (Fin k)}
    (hs : SEnc blank mark (qt ∘ π) s) (r : Stack (ActQ k) (CondQ k))
    (l : List (Option Terminal)) (hl : l.length = (execProg blank s).length) :
    trace (IQ (k := k) Terminal) blank l (execStepProg blank π (eshapeOf s) :: r, TSQ qt)
        = avecsQ blank (renameL π (execProg blank s)) qt ∧
      (execProg blank s).length ≤ 9 :=
  ⟨execQ_trace (execQ_execStep hπ hs) r l (by rw [hl, renameL_length]),
    execProg_length blank s⟩

end Interface

end PalPeg.RTQueueProg

/-
Axiom check (0 errors; `propext / Classical.choice / Quot.sound` only):

```
#print axioms PalPeg.RTQueueProg.execQ_execStep
#print axioms PalPeg.RTQueueProg.performs_exec2
#print axioms PalPeg.RTQueueProg.performs_check
#print axioms PalPeg.RTQueueProg.qsnoc_exec
#print axioms PalPeg.RTQueueProg.qtail_exec
#print axioms PalPeg.RTQueueProg.qsnoc_trace
#print axioms PalPeg.RTQueueProg.qtail_trace
#print axioms PalPeg.RTQueueProg.qexec_trace
```
-/
