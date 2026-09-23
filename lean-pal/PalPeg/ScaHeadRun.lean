import PalPeg.ScaHeadVM

/-!
# Running the head VM, and lifting a child generator into its caller

A generator called by another sits at the end of the frame chain. While it runs, the caller's
frames are an untouched prefix: `next (f :: c) r` is `next c r` with `f` prepended, until the
child returns and `f` resumes with its value (`next_cons`). So a child's behaviour can be proved
once, on its own chain, and then used inside any caller (`lift_run`).

`MRun` is the matcher head VM's execution: `stepMatch` steps and letter arrivals, interleaved.
-/
set_option autoImplicit false
namespace PalPeg.ScaHeadRun
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM

/-! ## The frame chain -/

theorem next_cons (f : Frame) (c : Config) (hc : c ≠ []) (r : Option Bool) :
    next (f :: c) r =
      match next c r with
      | some (.yielded e cs) => some (.yielded e (f :: cs))
      | some (.returned v) => advance defaultFuel f v
      | none => none := by
  obtain ⟨g, c', rfl⟩ : ∃ g c', c = g :: c' := by
    cases c with
    | nil => exact absurd rfl hc
    | cons g c' => exact ⟨g, c', rfl⟩
  unfold next
  conv_lhs => unfold send
  cases h : send defaultFuel (g :: c') r with
  | none => rfl
  | some o => cases o <;> rfl

/-- The caller `f` around a child's control: a pending child is pending in `f`'s chain; a
returned child resumes `f` with its value. -/
def liftCtl (f : Frame) : Ctl → Ctl
  | .pending cs e => .pending (f :: cs) e
  | .returned v => Ctl.ofOutcome (advance defaultFuel f v)
  | .failed => .failed

/-- Chains reached from a non-empty chain are non-empty. -/
def NonEmptyCtl : Ctl → Prop
  | .pending cs _ => cs ≠ []
  | _ => True

theorem advance_yield_ne : ∀ (fuel : ℕ) (f : Frame) (r : Option Bool) (e : Event) (cs : Config),
    advance fuel f r = some (.yielded e cs) → cs ≠ []
  | 0, _, _, _, _, h => by simp [advance] at h
  | fuel + 1, f, r, e, cs, h => by
    simp only [advance] at h
    cases hs : stepFrame f r with
    | none => simp [hs] at h
    | some a =>
      rw [hs] at h
      cases a with
      | emit e' f' => simp at h; rw [← h.2]; simp
      | ret v => simp at h
      | call f' child =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases ha : advance fuel child none with
        | none => simp [ha] at h
        | some o =>
          rw [ha] at h
          cases o with
          | yielded e2 cs2 => simp at h; rw [← h.2]; simp
          | returned v => exact advance_yield_ne fuel f' v e cs h

theorem send_yield_ne (fuel : ℕ) : ∀ (c : Config) (r : Option Bool) (e : Event) (cs : Config),
    send fuel c r = some (.yielded e cs) → cs ≠ []
  | [], _, _, _, h => by simp [send] at h
  | [f], r, e, cs, h => advance_yield_ne fuel f r e cs (by simpa [send] using h)
  | f :: g :: rest, r, e, cs, h => by
    unfold send at h
    cases hs : send fuel (g :: rest) r with
    | none => simp [hs] at h
    | some o =>
      rw [hs] at h
      cases o with
      | yielded e2 cs2 => simp at h; rw [← h.2]; simp
      | returned v => exact advance_yield_ne fuel f v e cs (by simpa using h)

theorem nonEmpty_ofOutcome (c : Config) (r : Option Bool) :
    NonEmptyCtl (Ctl.ofOutcome (next c r)) := by
  cases h : next c r with
  | none => trivial
  | some o =>
    cases o with
    | yielded e cs => exact send_yield_ne defaultFuel c r e cs h
    | returned v => trivial

theorem nonEmpty_resume (tests : List String) (d : Bool) (k : Ctl) (hk : NonEmptyCtl k) :
    NonEmptyCtl (k.resume tests d) := by
  cases k with
  | pending c e => exact nonEmpty_ofOutcome c _
  | returned v => trivial
  | failed => trivial

theorem resume_lift (f : Frame) (tests : List String) (d : Bool) (cs : Config) (e : Event)
    (hcs : cs ≠ []) :
    (Ctl.pending (f :: cs) e).resume tests d = liftCtl f ((Ctl.pending cs e).resume tests d) := by
  simp only [Ctl.resume]
  rw [next_cons f cs hcs]
  cases h : next cs (respond tests e d) with
  | none => rfl
  | some o => cases o <;> rfl

/-! ## Running the matcher VM -/

/-- One step of the matcher VM, or a letter arriving. -/
inductive MStep : HVM → HVM → Prop
  | step {v w : HVM} : stepMatch v = some w → MStep v w
  | arrive {v : HVM} (a : Fin 2) : MStep v (v.append a)

/-- The matcher VM's executions. -/
def MRun : HVM → HVM → Prop := Relation.ReflTransGen MStep

/-- The VM `v` with its control seen inside the caller `f`. -/
def liftVM (f : Frame) (v : HVM) : HVM := { v with ctl := liftCtl f v.ctl }

theorem stepMatch_lift (f : Frame) (v : HVM) (cs : Config) (e : Event) (hv : v.ctl = .pending cs e)
    (hcs : cs ≠ []) :
    stepMatch { v with ctl := .pending (f :: cs) e } = (stepMatch v).map (liftVM f) := by
  have hr : ∀ d, (Ctl.pending (f :: cs) e).resume matchTests d =
      liftCtl f ((Ctl.pending cs e).resume matchTests d) := fun d => resume_lift f _ d cs e hcs
  unfold stepMatch
  rw [hv]
  simp only [hr]
  cases e <;> simp [liftVM, HVM.inRange, HVM.len] <;> (try split_ifs) <;> simp_all [liftVM]
  all_goals rfl

theorem stepMatch_ctl {v w : HVM} (h : stepMatch v = some w) :
    ∃ cs e, v.ctl = .pending cs e ∧ ∃ d, w.ctl = (Ctl.pending cs e).resume matchTests d := by
  unfold stepMatch at h
  split at h
  · rename_i cs e hv
    refine ⟨cs, e, hv, ?_⟩
    rw [← hv]
    cases e <;> simp at h
    all_goals first
      | (obtain ⟨π, -, rfl⟩ := h; exact ⟨false, rfl⟩)
      | (subst h; exact ⟨_, rfl⟩)
      | (obtain ⟨-, rfl⟩ := h; exact ⟨_, rfl⟩)
  · simp at h

theorem nonEmpty_step {v w : HVM} (hv : NonEmptyCtl v.ctl) (h : MStep v w) : NonEmptyCtl w.ctl := by
  cases h with
  | step h =>
    obtain ⟨cs, e, hc, d, hw⟩ := stepMatch_ctl h
    rw [hw]; exact nonEmpty_ofOutcome cs _
  | arrive a => exact hv

theorem nonEmpty_run {v w : HVM} (hv : NonEmptyCtl v.ctl) (h : MRun v w) : NonEmptyCtl w.ctl := by
  induction h with
  | refl => exact hv
  | tail _ hs ih => exact nonEmpty_step ih hs

/-- **A child's run lifts into its caller**, as long as the child has not returned. -/
theorem lift_step (f : Frame) {v w : HVM} (hv : NonEmptyCtl v.ctl) (h : MStep v w) :
    MStep (liftVM f v) (liftVM f w) := by
  cases h with
  | step h =>
    obtain ⟨cs, e, hc, -⟩ := stepMatch_ctl h
    apply MStep.step
    have hne : cs ≠ [] := by rw [hc] at hv; exact hv
    have := stepMatch_lift f v cs e hc hne
    have hl : liftVM f v = { v with ctl := .pending (f :: cs) e } := by
      simp only [liftVM, hc, liftCtl]
    rw [hl, this, h]; rfl
  | arrive a => exact MStep.arrive a

theorem lift_run (f : Frame) {v w : HVM} (hv : NonEmptyCtl v.ctl) (h : MRun v w) :
    MRun (liftVM f v) (liftVM f w) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hr hs ih =>
    exact Relation.ReflTransGen.tail ih (lift_step f (nonEmpty_run hv hr) hs)

/-! ## One step, per event kind -/

section StepLemmas
variable {v : HVM} {c : Config}

theorem step_copy {t s' : String} (hv : v.ctl = .pending c (.copy t s')) :
    stepMatch v = some { v with
      pos := Function.update v.pos t (v.pos s')
      ctl := (Ctl.pending c (.copy t s')).resume matchTests false } := by
  simp only [stepMatch, hv]

theorem step_less {a b : String} (hv : v.ctl = .pending c (.less a b)) :
    stepMatch v = some { v with
      ctl := (Ctl.pending c (.less a b)).resume matchTests (decide (v.pos a < v.pos b)) } := by
  simp only [stepMatch, hv]

theorem step_equal {a b : String} (hv : v.ctl = .pending c (.equal a b)) :
    stepMatch v = some { v with
      ctl := (Ctl.pending c (.equal a b)).resume matchTests (decide (v.pos a = v.pos b)) } := by
  simp only [stepMatch, hv]

theorem step_move {ms : List Movement} {π : String → ℤ} (hv : v.ctl = .pending c (.move ms))
    (hm : moveSeq blind v.len ms v.pos = some π) :
    stepMatch v = some { v with
      pos := π
      ctl := (Ctl.pending c (.move ms)).resume matchTests false } := by
  simp only [stepMatch, hv, hm, Option.map_some]

theorem step_symbols {a b : String} (hv : v.ctl = .pending c (.symbols a b))
    (ha : v.inRange a) (hb : v.inRange b) :
    stepMatch v = some { v with
      ctl := (Ctl.pending c (.symbols a b)).resume matchTests
        (decide (v.word[(v.pos a).toNat]? = v.word[(v.pos b).toNat]?)) } := by
  simp only [stepMatch, hv, if_pos (And.intro ha hb)]

theorem step_available {h : String} (hv : v.ctl = .pending c (.available h)) :
    stepMatch v = some { v with
      ctl := (Ctl.pending c (.available h)).resume matchTests (decide (v.pos h < v.len)) } := by
  simp only [stepMatch, hv]

theorem step_assertEqual {a b : String} (hv : v.ctl = .pending c (.assertEqual a b))
    (he : v.pos a = v.pos b) :
    stepMatch v = some { v with ctl := (Ctl.pending c (.assertEqual a b)).resume matchTests false } := by
  simp only [stepMatch, hv, if_pos he]

theorem step_match {h : String} (hv : v.ctl = .pending c (.«match» h)) :
    stepMatch v = some { v with
      outputs := v.outputs ++ [v.pos h - v.patternSize]
      ctl := (Ctl.pending c (.«match» h)).resume matchTests false } := by
  simp only [stepMatch, hv]

end StepLemmas

end PalPeg.ScaHeadRun
