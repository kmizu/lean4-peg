import PalPeg.TextFeedPrepInterrupt

/-! Preparation progresses at a fixed rate across actual arrivals. Every
arrived symbol is buffered in FIFO order, while exactly R source primitive
instructions are executed in each productive frame. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrepFrames
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.ProgLangPersist2 PalPeg.PrepInstance
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepInterrupt

variable {k : ℕ} {Terminal : Type}

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem run_false_iterate (e : Env k) (leftSym : Fin k) (R rate N : ℕ)
    (x : CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 27 → STape (Fin k)))
    (hf : x.1.1.2.1 = false) :
    ((run (Terminal := Terminal) e leftSym R rate)^[N] x).1.1.2.1 = false := by
  induction N with
  | zero => exact hf
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact TextFeedStartupRun.choose_false e leftSym R rate _ _ ih

/-- A real arrival enqueues first, and then a productive preparation
window advances its source continuation. No input is skipped or repeated. -/
theorem busy_calls {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate J : ℕ) (hJR : J ≤ R)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = false)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P)
    (hs : c.1.2.2.val = s.map TextFeedPrepResume.lift ++ r)
    (htrace : (trace (source e) e.blank (List.replicate J none) (s, P)).length = J) :
    let z := (run (Terminal := Terminal) e leftSym R rate)^[J + 1]
      (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
    let u := runInputs (source e) e.blank (List.replicate J none) (s, P)
    ∃ c' T', z = (c', T') ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc q (enc a)) (enc a) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++ r ∧
      c'.1.1 = nextPhase^[J + 1] c.1.1 ∧ c'.1.2.1 = false := by
  dsimp only
  let x := (c, arriveA e.blank (TextFeedStartupSchedule.capture enc) (some a) T)
  let x1 := run (Terminal := Terminal) e leftSym R rate x
  have hvx : prepView x.2 = P := (capture_prepView e.blank enc (some a) T).trans hv
  obtain ⟨hr1, hb1, hf1, hw1, hv1⟩ := run_enqueue (Terminal := Terminal) hc hmb leftSym R rate
    x hb hf hc0 (TextFeedStartupRun.capture_ready enc a h) ha
  have hs1 : x1.1.1.2.2.val = s.map TextFeedPrepResume.lift ++ r := by rw [hw1]; exact hs
  have hcount : x1.1.1.1 = nextPhase ⟨0, Nat.zero_lt_succ R⟩ := by rw [run_counter, hc0]
  have hpos : J ≠ 0 → 0 < x1.1.1.1.val := by
    intro hR
    have ht : (0 : ℕ) + 1 < R + 1 := by omega
    rw [hcount]
    simp only [nextPhase, dif_pos ht]
    omega
  have hlen : x1.1.1.1.val + J ≤ R + 1 := by
    by_cases hR : R = 0
    · have hh := x1.1.1.1.isLt; omega
    · have ht : (0 : ℕ) + 1 < R + 1 := by omega
      rw [hcount]
      simp only [nextPhase, dif_pos ht]
      omega
  obtain ⟨ht, hb', hs'⟩ := run_prefix (Terminal := Terminal) e leftSym R rate J x1 hb1
    s r P (hv1.trans hvx) hs1 htrace hpos hlen
  have hcnt := run_counter_iterate (Terminal := Terminal) e leftSym R rate (J + 1) x
  rw [Function.iterate_succ_apply] at hcnt ⊢
  refine ⟨((run (Terminal := Terminal) e leftSym R rate)^[J] x1).1,
    ((run (Terminal := Terminal) e leftSym R rate)^[J] x1).2,
    rfl, ?_, hb', ?_, hs', hcnt, run_false_iterate e leftSym R rate J x1 hf1⟩
  · rw [ht, prepView_extend]
  · rw [ht]
    exact ready_prep hr1 _

theorem busy_frame {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = false)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old)
    (a : Terminal) (ha : enc a ≠ e.mark)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P)
    (hs : c.1.2.2.val = s.map TextFeedPrepResume.lift ++ r)
    (htrace : (trace (source e) e.blank (List.replicate R none) (s, P)).length = R) :
    let z := (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a
    let u := runInputs (source e) e.blank (List.replicate R none) (s, P)
    ∃ c' T', z = { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T' } ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (snoc q (enc a)) (enc a) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++ r ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ c'.1.2.1 = false := by
  dsimp only
  rw [machine_round]
  obtain ⟨c', T', he, hv', hb', hr, hs', hcnt, hf'⟩ := busy_calls (Terminal := Terminal)
    hc hmb leftSym enc R rate R (Nat.le_refl R) c T hb hf hc0 h a ha s r P hv hs htrace
  refine ⟨c', T', ?_, hv', hb', hr, hs', ?_, hf'⟩
  · rw [he]
  · rw [hc0, nextPhase_iterate_round] at hcnt
    exact hcnt

theorem live_split (e : Env k) (s : Stack (PrepAct k) (PrepCond k))
    (P : Fin 15 → STape (Fin k)) (N M : ℕ)
    (h : (trace (source e) e.blank (List.replicate (N + M) none) (s, P)).length = N + M) :
    (trace (source e) e.blank (List.replicate N none) (s, P)).length = N ∧
      (trace (source e) e.blank (List.replicate M none)
        (runInputs (source e) e.blank (List.replicate N none) (s, P))).length = M := by
  rw [List.replicate_add, trace_append, List.length_append] at h
  have h₁ := trace_length_le (source e) e.blank (List.replicate N none) (s, P)
  have h₂ := trace_length_le (source e) e.blank (List.replicate M none)
    (runInputs (source e) e.blank (List.replicate N none) (s, P))
  simp only [List.length_replicate] at h₁ h₂
  omega

/-- Arbitrarily many real-input frames preserve exactly the original
preparation run and append every input to the still-unconsumed FIFO. -/
theorem busy_frames {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (enc : Terminal → Fin k) (R rate : ℕ) (word : List Terminal)
    (c : CallCtrl (programs e) (Outer e leftSym R rate)) (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = false)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩)
    {q : Queue (Fin k)} {old : Fin k} (h : ReadyAt e T q old)
    (s : Stack (PrepAct k) (PrepCond k)) (r : Stack (TaskAct k) (TaskCond k))
    (P : Fin 15 → STape (Fin k)) (hv : prepView T = P)
    (hs : c.1.2.2.val = s.map TextFeedPrepResume.lift ++ r)
    (htrace : (trace (source e) e.blank (List.replicate (word.length * R) none) (s, P)).length =
      word.length * R) (hall : ∀ a ∈ word, enc a ≠ e.mark) :
    let z := word.foldl (machine e leftSym enc R rate).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T }
    let u := runInputs (source e) e.blank (List.replicate (word.length * R) none) (s, P)
    ∃ c' T', z = { state := ((c', ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T' } ∧
      prepView T' = u.2 ∧ AtBoundary (programs e) c'.2.2.1 ∧
      ReadyAt e T' (word.foldl (fun q a => snoc q (enc a)) q)
        (word.foldl (fun _ a => enc a) old) ∧
      c'.1.2.2.val = u.1.map TextFeedPrepResume.lift ++ r ∧
      c'.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧ c'.1.2.1 = false := by
  induction word generalizing c T q old s P with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, List.replicate_zero, runInputs_nil, List.foldl_nil]
    exact ⟨c, T, rfl, hv, hb, h, hs, hc0, hf⟩
  | cons a word ih =>
    have hsize : (a :: word).length * R = R + word.length * R := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [hsize] at htrace
    obtain ⟨hpre, htail⟩ := live_split e s P R (word.length * R) htrace
    obtain ⟨c1, T1, hz1, hv1, hb1, hr1, hs1, hc1, hf1⟩ := busy_frame
      hc hmb leftSym enc R rate c T hb hf hc0 h a (hall a List.mem_cons_self) s r P hv hs hpre
    have hz := ih c1 T1 hb1 hf1 hc1 hr1
      (runInputs (source e) e.blank (List.replicate R none) (s, P)).1
      (runInputs (source e) e.blank (List.replicate R none) (s, P)).2
      hv1 hs1 htail (fun b hb => hall b (List.mem_cons_of_mem a hb))
    simpa only [List.foldl_cons, hz1, hsize, List.replicate_add, runInputs_append,
      Prod.mk.eta] using hz

/-- info: 'PalPeg.TextFeedPrepFrames.busy_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms busy_frames

end PalPeg.TextFeedPrepFrames
