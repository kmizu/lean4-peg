import PalPeg.TextFeedPrepResume

/-! Input capture and enqueue do not disturb the physical preparation
snapshot. This includes all fifteen tapes, not just the future scanner. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepInterrupt
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume

variable {k : ℕ} {Terminal : Type}

def scanSlot (i : Fin 8) : Fin 20 := Fin.castAddEmb 1 (Fin.natAddEmb 11 i)

theorem prepView_feed (F : Fin 20 → STape (Fin k)) (T : Fin 27 → STape (Fin k))
    (h : ∀ i : Fin 8, F (scanSlot i) = T (feedSlot (scanSlot i))) :
    prepView (extend feedSlot F T) = prepView T := by
  funext j
  by_cases hj : j.val < 8
  · let i : Fin 8 := ⟨j.val, hj⟩
    have hij : prepSlot j = feedSlot (scanSlot i) := by
      apply Fin.ext
      change 11 + j.val =
        (if h : 11 + i.val < 19 then (⟨11 + i.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val
      rw [dif_pos (show 11 + i.val < 19 by have := i.isLt; omega)]
    change extend feedSlot F T (prepSlot j) = T (prepSlot j)
    rw [hij, extend_ι]
    exact h i
  · have hp : proj feedSlot (prepSlot j) = none := by
      apply proj_eq_none
      intro i he
      have hh := congrArg Fin.val he
      by_cases hi : i.val < 19
      · change (if h : i.val < 19 then (⟨i.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val =
          11 + j.val at hh
        rw [dif_pos hi] at hh
        dsimp only at hh
        omega
      · change (if h : i.val < 19 then (⟨i.val, by omega⟩ : Fin 27) else ⟨26, by decide⟩).val =
          11 + j.val at hh
        rw [dif_neg hi] at hh
        dsimp only at hh
        omega
    exact extend_of_proj_none hp F T

theorem capture_prepView (blank : Fin k) (enc : Terminal → Fin k) (a : Option Terminal)
    (T : Fin 27 → STape (Fin k)) :
    prepView (arriveA blank (TextFeedStartupSchedule.capture enc) a T) = prepView T := by
  funext j
  have hj : prepSlot j ≠ inputSlot := by
    intro h
    have hh := congrArg Fin.val h
    change 11 + j.val = 26 at hh
    omega
  simp only [prepView, arriveA, TextFeedStartupSchedule.capture, if_neg hj]
  rfl

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _

attribute [local irreducible] ProgLangBank.runChunk

/-- The input interrupt appends one symbol but neither advances the
preparation continuation nor changes any of its fifteen tapes. -/
theorem run_enqueue {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hb : AtBoundary (programs e) x.1.2.2.1) (hf : x.1.1.2.1 = false)
    (hc0 : x.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e x.2 q old) (ha : old ≠ e.mark) :
    let y := run (Terminal := Terminal) e leftSym R rate x
    ReadyAt e y.2 (snoc q old) old ∧ AtBoundary (programs e) y.1.2.2.1 ∧
      y.1.1.2.1 = false ∧ y.1.1.2.2 = x.1.1.2.2 ∧ prepView y.2 = prepView x.2 := by
  have hi := TextFeedStartupRun.ready_input h
  have hsel : decode (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2 =
      .feed (.enqueue old) := by
    rw [TextFeedStartupSchedule.choose, if_pos hc0]
    simp only [hf, Bool.false_eq_true, ↓reduceIte, decode_encode, hi]
  obtain ⟨qt, m, S, hv, hr⟩ := h
  obtain ⟨tr, qt', m', he, hn, ht, hr'⟩ := feed_exec (Terminal := Terminal) hc hmb
    hr S old (.enqueue old) ha x.2
  have hs : extend feedSlot (rtapes e qt m S old) x.2 = x.2 := by
    rw [← hv]
    exact extend_restrict feedSlot x.2
  rw [hs] at he ht
  have hex : Exec (TextFeedStartupSchedule.interp (Terminal := Terminal) e).toInterp e.blank
      (programs e (choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
    change Exec (shared e) e.blank (low e (decode _)) x.2 tr
    rw [hsel]
    exact he
  obtain ⟨hyt, hby, _, _⟩ := callRun_exec (programs e)
    (fun _ => TextFeedStartupSchedule.interp (Terminal := Terminal) e)
    (choose e leftSym R rate) 48 e.blank x hb tr hex (by omega)
  have heffect : (run (Terminal := Terminal) e leftSym R rate x).2 =
      extend feedSlot (rtapes e qt' m' S old) x.2 := hyt.trans ht
  refine ⟨heffect ▸ ready_feed hr' S old x.2, hby, ?_, ?_, ?_⟩
  · simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose, if_pos hc0]
  · simp only [TextFeedStartupSchedule.run, callRun, TextFeedStartupSchedule.choose, if_pos hc0]
  · rw [heffect]
    apply prepView_feed
    intro i
    simpa only [scanSlot, feedView, rtapes, TextFeedControl.tapes, Fin.castAddEmb_apply,
      Fin.natAddEmb_apply, Fin.append_left, Fin.append_right] using
      (congrFun hv (scanSlot i)).symm

/-- info: 'PalPeg.TextFeedPrepInterrupt.run_enqueue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_enqueue

end PalPeg.TextFeedPrepInterrupt
