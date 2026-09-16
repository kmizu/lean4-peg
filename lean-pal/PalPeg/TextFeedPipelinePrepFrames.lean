import PalPeg.TextFeedPipelinePrepInput

/-! Exact preparation progress across real input frames, including the
first dual-FIFO bootstrap. A final partial window can stop at the return
point before the pipeline starts executing prefix alignment. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelinePrepFrames
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2 PalPeg.ProgLangBank PalPeg.TextFeedControl PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineBank PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelinePrepWindow
open PalPeg.TextFeedPipelinePrepInput
open PalPeg.TextFeedPrepResume (source sourceStep)

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem run_false (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hf : x.1.1.2.1 = false) : (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x).1.1.2.1 = false := by
  change (TextFeedPipelineControl.choose e leftSym R rate x.1.1 (fun j => (x.2 j).focus)).1.2.1 = false
  unfold TextFeedPipelineControl.choose
  split
  · rfl
  · exact hf

theorem run_false_iterate (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k)))
    (hf : x.1.1.2.1 = false) :
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.1 = false := by
  induction N with
  | zero => exact hf
  | succ N ih => rw [Function.iterate_succ_apply']; exact run_false e leftSym R rate _ ih

theorem busy_calls {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJR : J ≤ R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hc0 : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (h : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P) (hs : ControlEq c.1.2.2.val s r)
    (htrace : (trace (source e) e.blank (List.replicate J none) (s, P)).length = J) :
    let z := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J + 1]
      (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
    let u := runInputs (source e) e.blank (List.replicate J none) (s, P)
    ∃ c' T', z = (c', T') ∧ prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc q₁ (enc a)) (snoc q₂ (enc a)) (enc a) ∧
      ControlEq c'.1.2.2.val u.1 r ∧ c'.1.1 = nextPhase^[J + 1] c.1.1 ∧ c'.1.2.1 = false := by
  dsimp only
  let x := (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
  let x1 := TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x
  have hvx : prepView x.2 = P := (capture_prepView e enc (some a) T).trans hv
  obtain ⟨hr1, hb1, hf1, hw1, hv1⟩ := run_queue (Terminal := Terminal) e hc hmb leftSym R rate x hb hc0 ha
    (capture_queues e enc a h)
  have hs1 : ControlEq x1.1.1.2.2.val s r := by rw [hw1]; exact hs
  have hcount : x1.1.1.1 = nextPhase (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1)) := by rw [run_counter, hc0]; rfl
  have hpos : J ≠ 0 → 0 < x1.1.1.1.val := by
    intro hj
    have ht : (0 : ℕ) + 1 < R + 1 := by omega
    rw [hcount]
    simp only [nextPhase, dif_pos ht]
    omega
  have hlen : x1.1.1.1.val + J ≤ R + 1 := by
    by_cases hr : R = 0
    · have hh := x1.1.1.1.isLt; omega
    · have ht : (0 : ℕ) + 1 < R + 1 := by omega
      rw [hcount]
      simp only [nextPhase, dif_pos ht]
      omega
  obtain ⟨ht, hb', hs'⟩ := run_window (Terminal := Terminal) e leftSym R rate J x1 hb1 s r P
    (hv1.trans hvx) hs1 htrace hpos hlen
  have hcnt := run_counter_iterate (Terminal := Terminal) e leftSym R rate (J + 1) x
  rw [Function.iterate_succ_apply] at hcnt ⊢
  refine ⟨((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x1).1,
    ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[J] x1).2,
    rfl, ?_, hb', ?_, hs', hcnt, run_false_iterate e leftSym R rate J x1 hf1⟩
  · rw [ht, prepView_extend]
  · rw [ht]
    exact ready_prep hr1 _

theorem busy_frame {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hc0 : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (h : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P) (hs : ControlEq c.1.2.2.val s r)
    (htrace : (trace (source e) e.blank (List.replicate R none) (s, P)).length = R) :
    let z := (machine e leftSym enc R rate).sRound { state := ((c, 0), 0), tape := T } a
    let u := runInputs (source e) e.blank (List.replicate R none) (s, P)
    ∃ c' T', z = { state := ((c', 0), 0), tape := T' } ∧ prepView T' = u.2 ∧
      AtBoundary (programs e) c'.2.2.1 ∧ ReadyAt e T' (snoc q₁ (enc a)) (snoc q₂ (enc a)) (enc a) ∧
      ControlEq c'.1.2.2.val u.1 r ∧ c'.1.1 = 0 ∧ c'.1.2.1 = false := by
  dsimp only
  rw [machine_round]
  obtain ⟨c', T', he, hv', hb', hr, hs', hcnt, hf'⟩ := busy_calls (Terminal := Terminal)
    hc hmb leftSym enc R rate R (Nat.le_refl R) c T hb hc0 h a ha s r P hv hs htrace
  refine ⟨c', T', ?_, hv', hb', hr, hs', ?_, hf'⟩
  · rw [he]
  · rw [hc0] at hcnt
    change c'.1.1 = nextPhase^[R + 1] (⟨0, Nat.zero_lt_succ R⟩ : Fin (R + 1)) at hcnt
    rw [nextPhase_iterate_round] at hcnt
    exact hcnt

/-- Full real input frames, retaining their source control and exact
unconsumed FIFO words. The empty word also permits pre-bootstrap state. -/
theorem busy_frames {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) (word : List Terminal)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 39 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hc0 : c.1.1 = 0)
    {q₁ q₂ : Queue (Fin k)} {old : Fin k} (h : QueuesAt e c.1.2.1 T q₁ q₂ old)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P) (hs : ControlEq c.1.2.2.val s r)
    (htrace : (trace (source e) e.blank (List.replicate (word.length * R) none) (s, P)).length = word.length * R)
    (hall : ∀ a ∈ word, enc a ≠ e.mark) :
    let z := word.foldl (machine e leftSym enc R rate).sRound { state := ((c, 0), 0), tape := T }
    let u := runInputs (source e) e.blank (List.replicate (word.length * R) none) (s, P)
    ∃ c' T', z = { state := ((c', 0), 0), tape := T' } ∧ prepView T' = u.2 ∧
      AtBoundary (programs e) c'.2.2.1 ∧
      QueuesAt e c'.1.2.1 T' (word.foldl (fun q a => snoc q (enc a)) q₁)
        (word.foldl (fun q a => snoc q (enc a)) q₂) (word.foldl (fun _ a => enc a) old) ∧
      ControlEq c'.1.2.2.val u.1 r ∧ c'.1.1 = 0 := by
  induction word generalizing c T q₁ q₂ old s P with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, List.replicate_zero, runInputs_nil, List.foldl_nil]
    exact ⟨c, T, rfl, hv, hb, h, hs, hc0⟩
  | cons a word ih =>
    have hsize : (a :: word).length * R = R + word.length * R := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [hsize] at htrace
    obtain ⟨hpre, htail⟩ := TextFeedPrepFrames.live_split e s P R (word.length * R) htrace
    obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1, hf1⟩ := busy_frame
      hc hmb leftSym enc R rate c T hb hc0 h a (hall a List.mem_cons_self) s r P hv hs hpre
    have hq1 : QueuesAt e c1.1.2.1 T1 (snoc q₁ (enc a)) (snoc q₂ (enc a)) (enc a) := by rw [hf1]; exact hr1
    have hz := ih c1 T1 hb1 hc1 hq1
      (runInputs (source e) e.blank (List.replicate R none) (s, P)).1
      (runInputs (source e) e.blank (List.replicate R none) (s, P)).2
      hv1 hs1 htail (fun b hb => hall b (List.mem_cons_of_mem a hb))
    simpa only [List.foldl_cons, hz1, hsize, List.replicate_add, runInputs_append, Prod.mk.eta] using hz

/-- info: 'PalPeg.TextFeedPipelinePrepFrames.busy_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms busy_frames

end PalPeg.TextFeedPipelinePrepFrames
