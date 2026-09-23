import PalPeg.ScaDecomposeSafe
import PalPeg.ScaMatcherLoop
import PalPeg.ScaMatcherAnswer
import PalPeg.ScaWorkerLink

/-!
# The matcher controller's startup, on the head VM

`stepMatcherController` (`ScaGsCoroutine.lean:459-526`), sites 0–12, with `k = 8`,
`(s, p, r) = decompose x 8`, `p₁ = normP1 x`, `pe = decide (p ≠ 0)`, `x ≠ []`:

* site 0 `copy End Tail`, site 1 `Decompose 8` (`ScaDecomposeSafe.decompose_runS`): **`start_pre`**,
  a guarded run under the birth orientation `ρ₀` (`StartOrient`), ending just before the
  orientation-changing copies.
* sites 2–6 `copy P Tail`, `copy KP End`, `copy A Cut`, `copy B P`, `copy Walk Origin`:
  **`start_copies`** (5 unguarded steps; each event is a `copy`, so the worker's side conditions
  hold trivially, `start_copies_sideRun`), and the ghost orientation becomes
  `loopOrient ρ₀` (`P`, `KP`, `B` forward; `start_copies_orient`), which is
  `ScaMatcherLoop.Orient` (`loopOrient_orient`).
* sites 7–12, the offset walk (`B` advances `s` cells, waiting for text at site 9), under
  `loopOrient ρ₀`: `walk_entry`, `walk_step`, `walk_wait`, `walkHead_append`, ending at the first
  loop head `ScaMatcherLoop.AtHead … pe true ((⟨s, 0⟩, 0))`.

Every run here keeps `word`, `patternSize` and `outputs` (the results are `{ v with ctl, pos }`).
-/
set_option autoImplicit false
namespace PalPeg.ScaMatcherStart
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe PalPeg.ScaHeadDecompose
  PalPeg.ScaDecomposeSafe
open PalPeg.ScaMatcherLoop (mc Orient AtHead LoopRel ok_step2 mc_11 mc_12)
open PalPeg.ScaMatcherAnswer (normP1 normP1_some)
open PalPeg.ScaWorkerLink (startCtl orientAt orientAt_succ orientStep_pending StepSide SideRun)

/-! ## Orientations -/

/-- The worker's ghost orientation at birth, as far as the startup needs it. -/
structure StartOrient (ρ₀ : String → Bool) : Prop where
  dec : DecOrient ρ₀
  tail : ρ₀ "Tail" = false
  endF : ρ₀ "End" = false
  u : ρ₀ "U" = false

/-- The orientation after the startup copies: `P`, `KP`, `B` turn forward. -/
def loopOrient (ρ₀ : String → Bool) : String → Bool := fun h =>
  if h = "P" ∨ h = "KP" ∨ h = "B" then false else ρ₀ h

theorem loopOrient_orient {ρ₀ : String → Bool} (hρ : StartOrient ρ₀) : Orient (loopOrient ρ₀) :=
  ⟨by simp [loopOrient, hρ.dec.origin], by simp [loopOrient, hρ.dec.walk],
    by simp [loopOrient, hρ.dec.a], by simp [loopOrient, hρ.dec.cut], by simp [loopOrient],
    by simp [loopOrient, hρ.u], by simp [loopOrient], by simp [loopOrient]⟩

/-! ## Control transitions -/

section Trans
variable (pe : Bool)

theorem start_ctl : startCtl = .pending [mc 8 none none none 1] (.copy "End" "Tail") := rfl

theorem ms1 : (Ctl.pending [mc 8 none none none 1] (.copy "End" "Tail")).resume matchTests false =
    .pending [mc 8 none none none 2, .decompose 8 1] (.copy "Cut" "Origin") := rfl

theorem ms2 (b : Bool) : liftCtl (mc 8 none none none 2) (.returned (some b)) =
    .pending [mc 8 (some b) none none 3] (.copy "P" "Tail") := rfl

theorem ms3 : (Ctl.pending [mc 8 (some pe) none none 3] (.copy "P" "Tail")).resume matchTests false =
    .pending [mc 8 (some pe) none none 4] (.copy "KP" "End") := rfl
theorem ms4 : (Ctl.pending [mc 8 (some pe) none none 4] (.copy "KP" "End")).resume matchTests false =
    .pending [mc 8 (some pe) none none 5] (.copy "A" "Cut") := rfl
theorem ms5 : (Ctl.pending [mc 8 (some pe) none none 5] (.copy "A" "Cut")).resume matchTests false =
    .pending [mc 8 (some pe) none none 6] (.copy "B" "P") := rfl
theorem ms6 : (Ctl.pending [mc 8 (some pe) none none 6] (.copy "B" "P")).resume matchTests false =
    .pending [mc 8 (some pe) none none 7] (.copy "Walk" "Origin") := rfl
theorem ms7 :
    (Ctl.pending [mc 8 (some pe) none none 7] (.copy "Walk" "Origin")).resume matchTests false =
      .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut") := rfl
theorem ms8t : (Ctl.pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut")).resume matchTests true =
    .pending [mc 8 (some pe) none none 9] (.available "B") := rfl
theorem ms8f :
    (Ctl.pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut")).resume matchTests false =
      .pending [mc 8 (some pe) none none 11] (.copy "Walk" "Origin") := rfl
theorem ms9t : (Ctl.pending [mc 8 (some pe) none none 9] (.available "B")).resume matchTests true =
    .pending [mc 8 (some pe) none none 10] (mv [("Walk", 1), ("B", 1)]) := rfl
theorem ms9f : (Ctl.pending [mc 8 (some pe) none none 9] (.available "B")).resume matchTests false =
    .pending [mc 8 (some pe) none none 9] (.available "B") := rfl
theorem ms10 :
    (Ctl.pending [mc 8 (some pe) none none 10] (mv [("Walk", 1), ("B", 1)])).resume matchTests false =
      .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut") := rfl

end Trans

/-! ## The birth state -/

theorem append_facts (v : HVM) (a : Fin 2) :
    (v.append a).ctl = v.ctl ∧ (v.append a).word = v.word ++ [a] ∧
      (v.append a).patternSize = v.patternSize ∧ (v.append a).outputs = v.outputs ∧
      ∀ h, h ≠ "OriginalEnd" → (v.append a).pos h = v.pos h := by
  refine ⟨rfl, rfl, rfl, rfl, fun h hh => ?_⟩
  simp [HVM.append, Function.update_of_ne hh]

/-- The birth state `matchInitial x startCtl`, with the text letters `l` appended. -/
theorem initial_facts (x l : List (Fin 2)) :
    (l.foldl HVM.append (matchInitial x startCtl)).ctl = startCtl ∧
      (l.foldl HVM.append (matchInitial x startCtl)).word = x ++ l ∧
      (l.foldl HVM.append (matchInitial x startCtl)).patternSize = x.length ∧
      (l.foldl HVM.append (matchInitial x startCtl)).outputs = [] ∧
      (l.foldl HVM.append (matchInitial x startCtl)).pos "Origin" = 0 ∧
      (l.foldl HVM.append (matchInitial x startCtl)).pos "Tail" = x.length := by
  suffices h : ∀ (v : HVM) (l : List (Fin 2)), (l.foldl HVM.append v).ctl = v.ctl ∧
      (l.foldl HVM.append v).word = v.word ++ l ∧
      (l.foldl HVM.append v).patternSize = v.patternSize ∧
      (l.foldl HVM.append v).outputs = v.outputs ∧
      ∀ h, h ≠ "OriginalEnd" → (l.foldl HVM.append v).pos h = v.pos h by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h (matchInitial x startCtl) l
    refine ⟨h1, h2, h3, h4, ?_, ?_⟩
    · rw [h5 _ (by decide)]; simp [matchInitial]
    · rw [h5 _ (by decide)]; simp [matchInitial]
  intro v l
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (v.append a)
    obtain ⟨e1, e2, e3, e4, e5⟩ := append_facts v a
    refine ⟨by simp only [List.foldl_cons]; rw [h1, e1], ?_, by simp only [List.foldl_cons]; rw [h3, e3],
      by simp only [List.foldl_cons]; rw [h4, e4], fun h hh => ?_⟩
    · simp only [List.foldl_cons]; rw [h2, e2]; simp
    · simp only [List.foldl_cons]; rw [h5 h hh, e5 h hh]

/-! ## (S1) `copy End Tail` and `Decompose` -/

/-- **(S1) The startup up to the orientation-changing copies**, guarded under the birth
orientation: `copy End Tail`, then the whole `Decompose 8` run. It ends at the pending
`copy P Tail` of site 2, with the decomposition's flag `pe`, `End = Tail = |x|`, `Cut = s` and
`First`/`KFirst`/`Reach` when `pe`; only `End` and the heads of `dHeads` move. -/
theorem start_pre {x rest : List (Fin 2)} {s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (hx : x ≠ []) {ρ₀ : String → Bool} (hρ : StartOrient ρ₀) (v : HVM) (hv : v.ctl = startCtl)
    (hw : v.word = x ++ rest) (hO : v.pos "Origin" = 0) (hT : v.pos "Tail" = x.length) :
    ∃ n π', n ≤ (160 * 8 + 418) * x.length + (20 * 8 + 69) + 1 ∧
      iterS x.length ρ₀ n v = some { v with
        ctl := .pending [mc 8 (some (decide (p ≠ 0))) none none 3] (.copy "P" "Tail")
        pos := π' } ∧
      Keeps ("End" :: dHeads) v.pos π' ∧ π' "End" = x.length ∧ π' "Cut" = s ∧
      (p ≠ 0 → π' "First" = (s : ℤ) + p ∧ π' "KFirst" = (s : ℤ) + ((8 : ℕ) : ℤ) * p ∧
        π' "Reach" = (s : ℤ) + r) := by
  rw [start_ctl] at hv
  have hx0 : 0 < x.length := List.length_pos_of_ne_nil hx
  obtain ⟨n, b, π', hn, hrun, hkeep, -, hE', hC, hiff, hheads⟩ :=
    decompose_runS (ρ := ρ₀) 8 (by decide) x rest
      { v with
        ctl := .pending [.decompose 8 1] (.copy "Cut" "Origin")
        pos := Function.update v.pos "End" (v.pos "Tail") }
      rfl hw (by simp [hO]) (by simp [hT]) hx0 hρ.dec
  rw [hdec] at hC hiff hheads
  have hb : b = decide (p ≠ 0) := by
    cases b
    · simp at hiff; simp [hiff]
    · simp at hiff; simp [hiff]
  subst hb
  have hchild := runS_child' (W := x.length) (ρ := ρ₀) (mc 8 none none none 2)
    { v with
      ctl := .pending [mc 8 none none none 2, .decompose 8 1] (.copy "Cut" "Origin")
      pos := Function.update v.pos "End" (v.pos "Tail") }
    [.decompose 8 1] (.copy "Cut" "Origin") rfl (by simp) n (some (decide (p ≠ 0))) π' hrun _
    (ms2 _)
  refine ⟨n + 1, π', by omega, ?_, ?_, ?_, hC, ?_⟩
  · exact runS_copy hv (ms1) (hρ.endF.trans hρ.tail.symm) hchild
  · intro h hh
    rw [hkeep h (fun hm => hh (List.mem_cons_of_mem _ hm))]
    have hE : h ≠ "End" := fun e => hh (e ▸ List.mem_cons_self)
    simp [Function.update_of_ne hE]
  · rw [hE']
  · intro hp
    have h3 := hheads (by simpa using hp)
    exact h3

/-! ## (S2) The orientation-changing copies -/

theorem stepSide_copy {W : ℕ} {ρ : String → Bool} {u : HVM} {c : Config} {t s' : String}
    (hu : u.ctl = .pending c (.copy t s')) : StepSide W ρ u := by
  constructor
  · intro c a b h; rw [hu] at h; cases h
  · intro c h h'; rw [hu] at h'; cases h'
  · intro c ms h; rw [hu] at h; cases h
  · intro c h h'; rw [hu] at h'; cases h'

section Copies
variable (pe : Bool) (v : HVM) (hv : v.ctl = .pending [mc 8 (some pe) none none 3] (.copy "P" "Tail"))
include hv

/-- The heads after each of the five copies. -/
def cp1 (π : String → ℤ) : String → ℤ := Function.update π "P" (π "Tail")
def cp2 (π : String → ℤ) : String → ℤ := Function.update (cp1 π) "KP" (cp1 π "End")
def cp3 (π : String → ℤ) : String → ℤ := Function.update (cp2 π) "A" (cp2 π "Cut")
def cp4 (π : String → ℤ) : String → ℤ := Function.update (cp3 π) "B" (cp3 π "P")
def cp5 (π : String → ℤ) : String → ℤ := Function.update (cp4 π) "Walk" (cp4 π "Origin")

/-- The five copy steps, one at a time. -/
theorem copies_chain :
    stepMatch v = some { v with
        ctl := .pending [mc 8 (some pe) none none 4] (.copy "KP" "End")
        pos := cp1 v.pos } ∧
      stepMatch { v with
          ctl := .pending [mc 8 (some pe) none none 4] (.copy "KP" "End")
          pos := cp1 v.pos } =
        some { v with
          ctl := .pending [mc 8 (some pe) none none 5] (.copy "A" "Cut")
          pos := cp2 v.pos } ∧
      stepMatch { v with
          ctl := .pending [mc 8 (some pe) none none 5] (.copy "A" "Cut")
          pos := cp2 v.pos } =
        some { v with
          ctl := .pending [mc 8 (some pe) none none 6] (.copy "B" "P")
          pos := cp3 v.pos } ∧
      stepMatch { v with
          ctl := .pending [mc 8 (some pe) none none 6] (.copy "B" "P")
          pos := cp3 v.pos } =
        some { v with
          ctl := .pending [mc 8 (some pe) none none 7] (.copy "Walk" "Origin")
          pos := cp4 v.pos } ∧
      stepMatch { v with
          ctl := .pending [mc 8 (some pe) none none 7] (.copy "Walk" "Origin")
          pos := cp4 v.pos } =
        some { v with
          ctl := .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut")
          pos := cp5 v.pos } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [step_copy hv, ms3]; rfl
  · rw [step_copy (v := { v with
      ctl := .pending [mc 8 (some pe) none none 4] (.copy "KP" "End")
      pos := cp1 v.pos }) rfl, ms4]; rfl
  · rw [step_copy (v := { v with
      ctl := .pending [mc 8 (some pe) none none 5] (.copy "A" "Cut")
      pos := cp2 v.pos }) rfl, ms5]; rfl
  · rw [step_copy (v := { v with
      ctl := .pending [mc 8 (some pe) none none 6] (.copy "B" "P")
      pos := cp3 v.pos }) rfl, ms6]; rfl
  · rw [step_copy (v := { v with
      ctl := .pending [mc 8 (some pe) none none 7] (.copy "Walk" "Origin")
      pos := cp4 v.pos }) rfl, ms7]; rfl

/-- **(S2) The five copies** `P := Tail`, `KP := End`, `A := Cut`, `B := P`, `Walk := Origin`,
as plain head-VM steps, ending at site 7's `less Walk Cut`. -/
theorem start_copies {x : List (Fin 2)} {s : ℕ} (hT : v.pos "Tail" = x.length)
    (hE : v.pos "End" = x.length) (hC : v.pos "Cut" = s) (hO : v.pos "Origin" = 0) :
    ∃ π', iterStep 5 v = some { v with
        ctl := .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut"), pos := π' } ∧
      π' "P" = x.length ∧ π' "KP" = x.length ∧ π' "A" = s ∧ π' "B" = x.length ∧ π' "Walk" = 0 ∧
      Keeps ["P", "KP", "A", "B", "Walk"] v.pos π' := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := copies_chain pe v hv
  refine ⟨cp5 v.pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [iterStep, e1, e2, e3, e4, e5, Option.bind_some]
  · simp [cp5, cp4, cp3, cp2, cp1, hT]
  · simp [cp5, cp4, cp3, cp2, cp1, hE]
  · simp [cp5, cp4, cp3, cp2, cp1, hC]
  · simp [cp5, cp4, cp3, cp2, cp1, hT]
  · simp [cp5, cp4, cp3, cp2, cp1, hO]
  · intro h hh
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hh
    obtain ⟨h1, h2, h3, h4, h5⟩ := hh
    simp [cp5, cp4, cp3, cp2, cp1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]

/-- The worker's side conditions hold along the five copies, for any orientation: every
pending event there is a `copy`. -/
theorem start_copies_sideRun (W : ℕ) (ρ : String → Bool) : SideRun W ρ 5 v := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := copies_chain pe v hv
  intro i hi u hu
  interval_cases i
  · simp only [iterStep, Option.some.injEq] at hu; subst hu; exact stepSide_copy hv
  · simp only [iterStep, e1, Option.bind_some, Option.some.injEq] at hu; subst hu
    exact stepSide_copy rfl
  · simp only [iterStep, e1, e2, Option.bind_some, Option.some.injEq] at hu; subst hu
    exact stepSide_copy rfl
  · simp only [iterStep, e1, e2, e3, Option.bind_some, Option.some.injEq] at hu; subst hu
    exact stepSide_copy rfl
  · simp only [iterStep, e1, e2, e3, e4, Option.bind_some, Option.some.injEq] at hu; subst hu
    exact stepSide_copy rfl

/-- **The ghost orientation after the copies** is `loopOrient ρ₀`. -/
theorem start_copies_orient {ρ₀ : String → Bool} (hρ : StartOrient ρ₀) :
    orientAt 5 v ρ₀ = loopOrient ρ₀ := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := copies_chain pe v hv
  rw [orientAt_succ ρ₀ e1, orientAt_succ _ e2, orientAt_succ _ e3, orientAt_succ _ e4,
    orientAt_succ _ e5, orientStep_pending hv, orientStep_pending rfl, orientStep_pending rfl,
    orientStep_pending rfl, orientStep_pending rfl]
  funext h
  simp only [orientAt, moveRev]
  have hd := hρ.dec
  by_cases h1 : h = "P" <;> by_cases h2 : h = "KP" <;> by_cases h3 : h = "B" <;>
    by_cases h4 : h = "A" <;> by_cases h5 : h = "Walk" <;>
    simp_all [loopOrient, hρ.tail, hρ.endF, hd.cut, hd.a, hd.origin, hd.walk]

end Copies

/-! ## (S3) The offset walk -/

/-- The heads during the offset walk, with `Walk = i`, `B = |x| + i`. -/
structure WalkRel (x T : List (Fin 2)) (m s p₁ r : ℕ) (pe : Bool) (i : ℕ) (v : HVM) : Prop where
  word : v.word = x ++ T.take m
  tl : m ≤ T.length
  psize : v.patternSize = x.length
  origin : v.pos "Origin" = 0
  cut : v.pos "Cut" = s
  endP : v.pos "End" = x.length
  per : pe = true → v.pos "First" = (s : ℤ) + p₁ ∧ v.pos "KFirst" = (s : ℤ) + ((8 : ℕ) : ℤ) * p₁ ∧
    v.pos "Reach" = (s : ℤ) + r
  a : v.pos "A" = s
  p : v.pos "P" = x.length
  kp : v.pos "KP" = x.length
  walk : v.pos "Walk" = i
  b : v.pos "B" = x.length + i

/-- **Waiting in the offset walk** at site 9 (`available B`), with `i < s` cells walked. -/
structure WalkHead (x T : List (Fin 2)) (m s p₁ r : ℕ) (pe : Bool) (i : ℕ) (v : HVM) : Prop
    extends WalkRel x T m s p₁ r pe i v where
  ctl : v.ctl = .pending [mc 8 (some pe) none none 9] (.available "B")
  lt : i < s

section Walk
variable {x T : List (Fin 2)} {m s p r : ℕ} {ρ₀ : String → Bool}

theorem walkRel_len {p₁ : ℕ} {pe : Bool} {i : ℕ} {v : HVM} (h : WalkRel x T m s p₁ r pe i v) :
    v.len = x.length + m := by
  simp only [HVM.len, h.word, List.length_append, List.length_take]
  rw [Nat.min_eq_left h.tl]; push_cast; ring

/-- The heads after the walk's exit: `Walk := Origin`, then `U := P`. -/
def exitPos (π : String → ℤ) : String → ℤ :=
  Function.update (Function.update π "Walk" (π "Origin")) "U"
    (Function.update π "Walk" (π "Origin") "P")

/-- The exit of the offset walk (`Walk = s`): three guarded steps to the first loop head. -/
theorem walk_exit (hdec : decompose x 8 = (s, p, r)) (hx : x ≠ []) (hρ : StartOrient ρ₀)
    (v : HVM) (hv : v.ctl = .pending [mc 8 (some (decide (p ≠ 0))) none none 8] (.less "Walk" "Cut"))
    (h : WalkRel x T m s (normP1 x) r (decide (p ≠ 0)) s v) (hsm : s ≤ m) :
    iterS x.length (loopOrient ρ₀) 3 v = some { v with
        ctl := .pending [mc 8 (some (decide (p ≠ 0))) (some true) none 13] (.available "B")
        pos := exitPos v.pos } ∧
      AtHead x T m 8 s (normP1 x) r (decide (p ≠ 0)) true ((⟨s, 0⟩ : PalPeg.ScanState), 0)
        { v with
          ctl := .pending [mc 8 (some (decide (p ≠ 0))) (some true) none 13] (.available "B")
          pos := exitPos v.pos } := by
  have h7 := ScaMatcherAnswer.seven_cut_lt hdec hx
  have hsx : s ≤ x.length := by omega
  have hρL := loopOrient_orient hρ
  refine ⟨?_, ?_⟩
  · refine runS_less hv (d := false) (by simp [h.walk, h.cut]) (ms8f _) ?_
    refine runS_copy rfl (mc_11 8 _ _ _) (hρL.walk.trans hρL.origin.symm) ?_
    refine runS_copy rfl (mc_12 8 _ _ _) (hρL.u.trans hρL.p.symm) ?_
    rfl
  · refine ⟨⟨none, rfl⟩, h.word, ?_, fun hok => absurd hok (by decide), le_refl _, hsx,
      by simp; omega, Nat.zero_le _, by simpa using hsm, h.tl⟩
    refine ⟨by simp [exitPos, h.origin], by simp [exitPos, h.cut], by simp [exitPos, h.endP],
      fun hpe => ?_, by simp [exitPos, h.p], by simp [exitPos, h.a], by simp [exitPos, h.b],
      by simp [exitPos, h.origin], by simp [exitPos, h.p]⟩
    obtain ⟨h1, h2, h3⟩ := h.per hpe
    exact ⟨by simp [exitPos, h1], by simp [exitPos, h2], by simp [exitPos, h3]⟩

/-- Entering the offset walk (`i < s`): one guarded test. -/
theorem walk_cont (v : HVM) {pe : Bool} {p₁ i : ℕ}
    (hv : v.ctl = .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut"))
    (h : WalkRel x T m s p₁ r pe i v) (hi : i < s) :
    iterS x.length (loopOrient ρ₀) 1 v =
        some { v with ctl := .pending [mc 8 (some pe) none none 9] (.available "B") } ∧
      WalkHead x T m s p₁ r pe i { v with ctl := .pending [mc 8 (some pe) none none 9] (.available "B") } :=
  ⟨runS_less hv (d := true) (by simp [h.walk, h.cut]; omega) (ms8t _) rfl,
    { h with ctl := rfl, lt := hi }⟩

/-- One cell of the offset walk once text has arrived: `available B`, then `Walk + 1, B + 1`. -/
theorem walk_move (hρ : StartOrient ρ₀) (hsx : s ≤ x.length) (v : HVM) {pe : Bool} {p₁ i : ℕ}
    (h : WalkHead x T m s p₁ r pe i v) (him : i < m) :
    iterS x.length (loopOrient ρ₀) 2 v = some { v with
        ctl := .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut")
        pos := Function.update (Function.update v.pos "Walk" (v.pos "Walk" + 1)) "B"
          (v.pos "B" + 1) } ∧
      WalkRel x T m s p₁ r pe (i + 1) { v with
        ctl := .pending [mc 8 (some pe) none none 8] (.less "Walk" "Cut")
        pos := Function.update (Function.update v.pos "Walk" (v.pos "Walk" + 1)) "B"
          (v.pos "B" + 1) } := by
  have hρL := loopOrient_orient hρ
  have hlen := walkRel_len h.toWalkRel
  have hW := h.walk
  have hB := h.b
  have hlt := h.lt
  refine ⟨?_, ?_⟩
  · have hok : EvOk x.length (loopOrient ρ₀) v.pos v.len (.available "B") :=
      ⟨hρL.b, by rw [hB, hlen]; omega, by decide⟩
    refine iterS_step h.ctl hok (step_available h.ctl) ?_
    rw [show decide (v.pos "B" < v.len) = true by simp; omega, ms9t]
    refine runS_move (ms := [⟨"Walk", 1⟩, ⟨"B", 1⟩]) rfl ?_ (ms10 _) ?_ rfl
    · show moveSeq blind v.len _ v.pos = _
      rw [moveSeq_cons_ok _ _ _ _ _ (fun _ => by constructor <;> omega),
        moveSeq_cons_ok _ _ _ _ _ (fun _ => by simp; constructor <;> omega), moveSeq_nil]
      simp
    · show EvOk x.length (loopOrient ρ₀) v.pos v.len (mv [("Walk", 1), ("B", 1)])
      exact ok_step2 (by decide) hρL.b (by rw [hW]; omega) (by decide) (by decide)
  · exact ⟨h.word, h.tl, h.psize, by simp [h.origin], by simp [h.cut], by simp [h.endP],
      fun hpe => by obtain ⟨h1, h2, h3⟩ := h.per hpe; exact ⟨by simp [h1], by simp [h2], by simp [h3]⟩,
      by simp [h.a], by simp [h.p], by simp [h.kp], by simp [hW], by simp [hB]; ring⟩

/-- **(S3) Entering the offset walk** from site 7 (`Walk = 0`, `B = |x|`): if `s = 0` three guarded
steps reach the first loop head, else one step reaches `WalkHead 0`. -/
theorem walk_entry (hdec : decompose x 8 = (s, p, r)) (hx : x ≠ []) (hρ : StartOrient ρ₀)
    (v : HVM) (hv : v.ctl = .pending [mc 8 (some (decide (p ≠ 0))) none none 8] (.less "Walk" "Cut"))
    (h : WalkRel x T m s (normP1 x) r (decide (p ≠ 0)) 0 v) :
    (s = 0 → ∃ w, iterS x.length (loopOrient ρ₀) 3 v = some w ∧ w.outputs = v.outputs ∧
        w.patternSize = x.length ∧
        AtHead x T m 8 s (normP1 x) r (decide (p ≠ 0)) true ((⟨s, 0⟩ : PalPeg.ScanState), 0) w) ∧
      (0 < s → ∃ w, iterS x.length (loopOrient ρ₀) 1 v = some w ∧ w.outputs = v.outputs ∧
        WalkHead x T m s (normP1 x) r (decide (p ≠ 0)) 0 w) := by
  refine ⟨fun hs0 => ?_, fun hs => ?_⟩
  · subst hs0
    obtain ⟨hrun, hat⟩ := walk_exit hdec hx hρ v hv h (Nat.zero_le _)
    exact ⟨_, hrun, rfl, h.psize, hat⟩
  · obtain ⟨hrun, hwh⟩ := walk_cont (ρ₀ := ρ₀) v hv h hs
    exact ⟨_, hrun, rfl, hwh⟩

/-- **(S3) One step of the offset walk** from `WalkHead i` with the text cell `i` arrived
(`i < m`): three guarded steps to `WalkHead (i+1)` if `i + 1 < s`, else five to the first loop
head. -/
theorem walk_step (hdec : decompose x 8 = (s, p, r)) (hx : x ≠ []) (hρ : StartOrient ρ₀)
    (v : HVM) {i : ℕ} (h : WalkHead x T m s (normP1 x) r (decide (p ≠ 0)) i v) (him : i < m) :
    (i + 1 < s → ∃ w, iterS x.length (loopOrient ρ₀) 3 v = some w ∧ w.outputs = v.outputs ∧
        WalkHead x T m s (normP1 x) r (decide (p ≠ 0)) (i + 1) w) ∧
      (i + 1 = s → ∃ w, iterS x.length (loopOrient ρ₀) 5 v = some w ∧ w.outputs = v.outputs ∧
        w.patternSize = x.length ∧
        AtHead x T m 8 s (normP1 x) r (decide (p ≠ 0)) true ((⟨s, 0⟩ : PalPeg.ScanState), 0) w) := by
  have h7 := ScaMatcherAnswer.seven_cut_lt hdec hx
  obtain ⟨hmv, hrel⟩ := walk_move (ρ₀ := ρ₀) hρ (by omega) v h him
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨hrun, hwh⟩ := walk_cont (ρ₀ := ρ₀) _ rfl hrel hs
    exact ⟨_, iterS_trans hmv hrun, rfl, hwh⟩
  · have hrel' : WalkRel x T m s (normP1 x) r (decide (p ≠ 0)) s _ := hs ▸ hrel
    obtain ⟨hrun, hat⟩ := walk_exit hdec hx hρ _ rfl hrel' (by omega)
    exact ⟨_, iterS_trans hmv hrun, rfl, h.psize, hat⟩

/-- **(S3) Waiting**: with no text cell to read (`m ≤ i`) the step at site 9 leaves the state
unchanged; its event is `available B`, a forward head under `loopOrient ρ₀`. -/
theorem walk_wait {p₁ : ℕ} {pe : Bool} {i : ℕ} (hρ : StartOrient ρ₀) (v : HVM)
    (h : WalkHead x T m s p₁ r pe i v) (hmi : m ≤ i) :
    iterStep 1 v = some v ∧ v.ctl = .pending [mc 8 (some pe) none none 9] (.available "B") ∧
      loopOrient ρ₀ "B" = false := by
  refine ⟨?_, h.ctl, (loopOrient_orient hρ).b⟩
  have hlen := walkRel_len h.toWalkRel
  have e := step_available h.ctl
  rw [show decide (v.pos "B" < v.len) = false by simp [h.b, hlen]; omega, ms9f] at e
  simp only [iterStep, e, Option.bind_some]
  congr 1
  rw [← h.ctl]

/-- **(S3) A text letter arriving during the walk.** -/
theorem walkHead_append {p₁ : ℕ} {pe : Bool} {i : ℕ} (v : HVM)
    (h : WalkHead x T m s p₁ r pe i v) (hm : m < T.length) :
    WalkHead x T (m + 1) s p₁ r pe i (v.append (T[m]'hm)) := by
  obtain ⟨-, e2, e3, -, e5⟩ := append_facts v (T[m]'hm)
  have hper := h.per
  refine ⟨⟨?_, hm, by rw [e3, h.psize], by rw [e5 _ (by decide), h.origin],
    by rw [e5 _ (by decide), h.cut], by rw [e5 _ (by decide), h.endP], fun hpe => ?_,
    by rw [e5 _ (by decide), h.a], by rw [e5 _ (by decide), h.p], by rw [e5 _ (by decide), h.kp],
    by rw [e5 _ (by decide), h.walk], by rw [e5 _ (by decide), h.b]⟩, h.ctl, h.lt⟩
  · rw [e2, h.word, List.append_assoc, List.take_add_one, List.getElem?_eq_getElem hm]
    rfl
  · obtain ⟨h1, h2, h3⟩ := hper hpe
    exact ⟨by rw [e5 _ (by decide), h1], by rw [e5 _ (by decide), h2], by rw [e5 _ (by decide), h3]⟩

end Walk

/-- **(S2 → S3) The copies land in the walk's relation** (`Walk = 0`, `B = |x|`), from the heads
`start_pre` leaves. -/
theorem copies_walkRel {x T : List (Fin 2)} {m s p r : ℕ} (hdec : decompose x 8 = (s, p, r))
    (v : HVM) (hv : v.ctl = .pending [mc 8 (some (decide (p ≠ 0))) none none 3] (.copy "P" "Tail"))
    (hw : v.word = x ++ T.take m) (htl : m ≤ T.length) (hps : v.patternSize = x.length)
    (hO : v.pos "Origin" = 0) (hT : v.pos "Tail" = x.length) (hE : v.pos "End" = x.length)
    (hC : v.pos "Cut" = s)
    (hper : p ≠ 0 → v.pos "First" = (s : ℤ) + p ∧ v.pos "KFirst" = (s : ℤ) + ((8 : ℕ) : ℤ) * p ∧
      v.pos "Reach" = (s : ℤ) + r) :
    ∃ v2, iterStep 5 v = some v2 ∧ v2.outputs = v.outputs ∧
      v2.ctl = .pending [mc 8 (some (decide (p ≠ 0))) none none 8] (.less "Walk" "Cut") ∧
      WalkRel x T m s (normP1 x) r (decide (p ≠ 0)) 0 v2 := by
  obtain ⟨π', hrun, hP, hKP, hA, hB, hW, hkeep⟩ := start_copies _ v hv hT hE hC hO
  refine ⟨_, hrun, rfl, rfl, hw, htl, hps, ?_, ?_, ?_, fun hpe => ?_, hA, hP, hKP, hW, by simpa using hB⟩
  · show π' "Origin" = 0
    rw [hkeep "Origin" (by decide), hO]
  · show π' "Cut" = s
    rw [hkeep "Cut" (by decide), hC]
  · show π' "End" = x.length
    rw [hkeep "End" (by decide), hE]
  · have hp : p ≠ 0 := by simpa using hpe
    obtain ⟨h1, h2, h3⟩ := hper hp
    show π' "First" = _ ∧ π' "KFirst" = _ ∧ π' "Reach" = _
    rw [(normP1_some hdec hp).2, hkeep "First" (by decide), hkeep "KFirst" (by decide),
      hkeep "Reach" (by decide)]
    exact ⟨h1, h2, h3⟩

end PalPeg.ScaMatcherStart
