import MacroPeg.HigherOrder.Mach.Frame0
import MacroPeg.HigherOrder.Mach.StepTypes
import MacroPeg.HigherOrder.Mach.StepRules

/-!
# The reading machine on stacks

The frame programs, dispatched on the frame (`readStepP`), do one step of the reading machine (`readStepP_ok`); the
loop `readP` runs it to its end (`readP_run`): from the stacks of `pinit tk` it reaches the stacks of the final state
when the machine accepts, and stops rejecting otherwise, within a number of steps polynomial in `tk.length`.
-/

namespace Shallot.MacroPeg.Mach

open Complexity

theorem FrameOK.mono {p : NProg NK} {s : PSt} {K : List Nat} {T T' : Nat} (h : FrameOK p s K T) (hT : T ≤ T') :
    FrameOK p s K T' :=
  ⟨fun hok => (h.1 hok).mono hT, fun hf => let ⟨S', x⟩ := h.2 hf; ⟨S', x.mono hT⟩⟩

/-- The frame programs, in order. -/
def framePs : List (NProg NK) :=
  [frame0P, frame1P, pushIfP 3, binP 5, pushIfP 5, binP 6, unP 7, unP 8, frame8P, frame9P, push2 11 0, frame11P,
    push2 13 1, frame13P, frame14P, frame15P, frame16P, frame17P, frame18P]

/-- One step of the reading machine. -/
def readStepP : NProg NK := stepP framePs

/-- The cost of one step. -/
def readStepCost (N : Nat) : Nat := frameCost N + 30 + 40

theorem frameCost_ge (N : Nat) : 100 ≤ frameCost N := by
  unfold frameCost
  have : 1 ≤ (N + 1114113) * (N + 1114113) * (N + 1114113) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  omega

section Frames

variable (s : PSt) (K : List Nat) (hs : s.ok = true)

theorem pstep_push (k a : Nat) (hc : s.ctl = k :: K) (hk : k = 2 ∨ k = 4)
    (ha : a = if k = 2 then 3 else 5) :
    (∀ r, s.ty = 0 :: r → pstep s = { s with ctl := 0 :: a :: K }) ∧
      ((∀ r, s.ty ≠ 0 :: r) → pstep s = s.fail) := by
  refine ⟨fun r hty => ?_, fun h => ?_⟩
  · rcases hk with rfl | rfl <;> subst ha <;> simp [pstep, hc, hty]
  · rcases hk with rfl | rfl <;> simp only [pstep, hc] <;>
      (split <;> first | rfl | (rename_i r hty; exact absurd hty (h r)))

theorem pstep_bin (k tag : Nat) (hc : s.ctl = k :: K) (hk : (k = 3 ∧ tag = 5) ∨ (k = 5 ∧ tag = 6)) :
    (∀ r, s.ty = 0 :: 0 :: r → pstep s = { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out }) ∧
      ((∀ r, s.ty ≠ 0 :: 0 :: r) → pstep s = s.fail) := by
  refine ⟨fun r hty => ?_, fun h => ?_⟩
  · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pstep, hc, binDone, hty]
  · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [pstep, hc, binDone] <;>
      (split <;> first | rfl | (rename_i r hty; exact absurd hty (h r)))

theorem pstep_un (k tag : Nat) (hc : s.ctl = k :: K) (hk : (k = 6 ∧ tag = 7) ∨ (k = 7 ∧ tag = 8)) :
    (∀ r, s.ty = 0 :: r → pstep s = { s with ctl := K, out := ⟨tag, 0, 0, s.cur⟩ :: s.out }) ∧
      ((∀ r, s.ty ≠ 0 :: r) → pstep s = s.fail) := by
  refine ⟨fun r hty => ?_, fun h => ?_⟩
  · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pstep, hc, unDone, hty]
  · rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [pstep, hc, unDone] <;>
      (split <;> first | rfl | (rename_i r hty; exact absurd hty (h r)))

end Frames

/-- **One step of the reading machine on stacks.** -/
theorem readStepP_ok (s : PSt) (hi : MInv s) (hs : s.ok = true) (hne : s.ctl ≠ []) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : StepOK readStepP s (readStepCost N) := by
  have h100 := frameCost_ge N
  refine stepP_ok framePs rfl s hne (fun k hk K hc => ?_)
  match k, hk with
  | 0, _ => exact frame0_frame s K hc hs hi hN
  | 1, _ => exact (frame1_frame s K hc hs hi hN).mono (by omega)
  | 2, _ =>
    have h := pstep_push s K 2 3 hc (.inl rfl) rfl
    exact (pushIfP_frame s K 3 hs h.1 h.2).mono (by omega)
  | 3, _ =>
    have h := pstep_bin s K 3 5 hc (.inl ⟨rfl, rfl⟩)
    exact (binP_frame s K 5 hs h.1 h.2).mono (by omega)
  | 4, _ =>
    have h := pstep_push s K 4 5 hc (.inr rfl) rfl
    exact (pushIfP_frame s K 5 hs h.1 h.2).mono (by omega)
  | 5, _ =>
    have h := pstep_bin s K 5 6 hc (.inr ⟨rfl, rfl⟩)
    exact (binP_frame s K 6 hs h.1 h.2).mono (by omega)
  | 6, _ =>
    have h := pstep_un s K 6 7 hc (.inl ⟨rfl, rfl⟩)
    exact (unP_frame s K 7 hs h.1 h.2).mono (by omega)
  | 7, _ =>
    have h := pstep_un s K 7 8 hc (.inr ⟨rfl, rfl⟩)
    exact (unP_frame s K 8 hs h.1 h.2).mono (by omega)
  | 8, _ => exact (frame8_frame s K hc hs hi hN).mono (by omega)
  | 9, _ => exact (frame9_frame s K hc hs hi hN).mono (by omega)
  | 10, _ => exact (push2_frame s K 11 0 hs (by simp [pstep, hc])).mono (by omega)
  | 11, _ => exact (frame11_frame s K hc hs hi hN).mono (by omega)
  | 12, _ => exact (push2_frame s K 13 1 hs (by simp [pstep, hc])).mono (by omega)
  | 13, _ => exact (frame13_frame s K hc hs hi hN).mono (by omega)
  | 14, _ => exact (frame14_frame s K hc hs hi hN).mono (by omega)
  | 15, _ => exact (frame15_frame s K hc hs hi hN).mono (by omega)
  | 16, _ => exact (frame16_frame s K hc hs hi hN).mono (by omega)
  | 17, _ => exact (frame17_frame s K hc hs hi hN).mono (by omega)
  | 18, _ => exact (frame18_frame s K hc hs hi hN).mono (by omega)
  | k + 19, hk => exact absurd hk (by simp [framePs])

/-! ## The whole reading -/

/-- Read the whole instance. -/
def readP : NProg NK := .loop CTL .nonempty readStepP

/-- A bound on the numbers seen while reading `L` tokens. -/
def readBound (L : Nat) : Nat := 4 * L + (4 * L + 1) * (4 * L + 3)

/-- The cost of reading `L` tokens. -/
def readCost (L : Nat) : Nat := (4 * L + 1) * (readStepCost (readBound L) + 1) + 1

theorem pot_pinit (tk : List Nat) : pot (pinit tk) = 4 * tk.length := by simp [pot, pinit, ctlPot, frameW]

theorem tsize_pinit (tk : List Nat) : tsize (pinit tk) = 0 := by simp [tsize, pinit]

/-- **Reading on stacks**: from the stacks of the start, `readP` reaches the stacks of the final state of the reading
machine when it accepts, and stops rejecting otherwise. -/
theorem readP_run (tk : List Nat) :
    ((pruns (pinit tk) (4 * tk.length + 1)).ok = true →
      NRuns readP (enc (pinit tk)) (enc (pruns (pinit tk) (4 * tk.length + 1))) (readCost tk.length)) ∧
    ((pruns (pinit tk) (4 * tk.length + 1)).ok = false →
      ∃ S', NHalts readP (enc (pinit tk)) false S' (readCost tk.length)) :=
  readLoop readStepP (readBound tk.length) (readStepCost (readBound tk.length))
    (fun s hi hs hne hN => readStepP_ok s hi hs hne hN) (4 * tk.length + 1) (pinit tk)
    (by rw [pot_pinit]; exact Nat.le_refl _) (minv_pinit tk) rfl (by rw [pot_pinit, tsize_pinit, readBound]; omega)

end Shallot.MacroPeg.Mach
