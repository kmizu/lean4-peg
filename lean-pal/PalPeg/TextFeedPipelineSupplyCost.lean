import PalPeg.TextFeedPipelineInstructionCost
import PalPeg.VerifierFeedSupplyProgress

/-! Charge physical supplies to the two currently ready text cells and
verifier instructions, including optional post-move supplies at EOF. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineSupplyCost
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInstructionCost PalPeg.VerifierFeedSupplyProgress
variable {k : ℕ} {Terminal : Type}

/-- This selected supply needs an unarrived symbol. It does not claim
that all subsequent control is frozen; a post-move supply may return. -/
def Blocked (n : ℕ) (u : Snapshot k) (w : Event) : Prop :=
  (w = .feed1 ∧ u.i1 = n) ∨ (w = .feed2 ∧ u.i2 = n)

open PalPeg.TextFeedPipelineFrameCost

/-- A missing symbol is a stopping barrier only when this dispatch does
not discharge a post-instruction frame. In particular, an optional
post-move supply is executable even at the end of the input. -/
def Barrier (n : ℕ) (u : Snapshot k) (gs : List Frame) (w : Event) : Prop :=
  Blocked n u w ∧ afterDebt u.frames ≤ afterDebt gs

theorem after_not_barrier (n : ℕ) (u : Snapshot k) (a : A) (fs : List Frame)
    (hf : u.frames = .after a :: fs) : ¬ Barrier n u fs .feed1 := by
  intro h
  have hh := h.2
  simp only [hf, afterDebt] at hh
  omega

theorem model_ready_bound (e : Env k) (w : Event) (u : Snapshot k) :
    readyCredit e.blank u.model ≤ instructions w + readyCredit e.blank (modelNext e w u.model) := by
  cases w with
  | instruction a => cases a with
    | inl a => exact effect_ready_bound e a u.model
    | inr up => simp [instructions, modelNext]
  | feed1 =>
    simpa only [instructions, Nat.zero_add, modelNext] using fill1_ready_mono e.blank e.mark u.model
  | feed2 =>
    have hx : ¬ VerifierFeedPrimitive.isXR (GSVProg.tX, true, Move.stay) := by intro h; cases h
    simpa only [instructions, Nat.zero_add, modelNext, VerifierFeedPrimitive.effect,
      if_neg hx, if_pos (show VerifierFeedPrimitive.isXS (GSVProg.tX, true, Move.stay) from rfl)] using
      fill2_ready_mono e.blank e.mark u.model
  | idle | halt => simp only [instructions, Nat.zero_add, modelNext, Nat.le_refl]

theorem worker_ready_credit {e : Env k} {leftSym : Fin k} {R rate n : ℕ} {Text : List (Fin k)}
    {x : Config e leftSym R rate} {u v : Snapshot k} {gs : List Frame} {w : Event}
    {caller : Stack (TaskAct k) (TaskCond k)} (hmb : e.mark ≠ e.blank)
    (hu : Valid e leftSym R rate Text n x u caller)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (he : next (taskEval e (fun j => (x.2 j).focus)) u.frames = (gs, w))
    (had : Advance e u v w) (hw : ¬ Blocked n u w) :
    feeds w + readyCredit e.blank u.model ≤ instructions w + readyCredit e.blank v.model := by
  rw [had.model]
  cases w with
  | instruction | idle | halt =>
    simpa only [feeds, Nat.zero_add] using model_ready_bound e _ u
  | feed1 =>
    have hcell := TextFeedPipelineFrameSafety.next_feed1_blank e (fun j => (x.2 j).focus)
      u.frames (congrArg Prod.snd he)
    rw [hu.physical] at hcell
    change Tape.read (u.model.vt.1 GSTapes.tT) = e.blank at hcell
    have hle : u.i1 ≤ n := hu.refines.feed.one.hle.trans hu.refines.feed.one.m2le
    have hne : u.i1 ≠ n := fun hh => hw (Or.inl ⟨rfl, hh⟩)
    have hg := fill1_ready_grow hmb hb hm hn hu.refines.feed.one hcell (by omega : u.i1 < n)
    simp only [feeds, instructions, Nat.zero_add, modelNext]
    change 1 + readyCredit e.blank u.model ≤ readyCredit e.blank (VerifierFeedRaw.fill1 e.blank e.mark u.model)
    rw [hg]
    omega
  | feed2 =>
    have hcell := TextFeedPipelineFrameSafety.next_feed2_blank e (fun j => (x.2 j).focus)
      u.frames (congrArg Prod.snd he)
    rw [hu.physical] at hcell
    change Tape.read u.model.vt.2.Txt2 = e.blank at hcell
    have hle : u.i2 ≤ n := hu.refines.feed.two.hle.trans hu.refines.feed.two.m2le
    have hne : u.i2 ≠ n := fun hh => hw (Or.inr ⟨rfl, hh⟩)
    have hg := fill2_ready_grow hmb hb hm hn hu.refines.feed.two hcell (by omega : u.i2 < n)
    have hx : ¬ VerifierFeedPrimitive.isXR (GSVProg.tX, true, Move.stay) := by intro h; cases h
    simp only [feeds, instructions, Nat.zero_add, modelNext]
    change 1 + readyCredit e.blank u.model ≤
      readyCredit e.blank (VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) u.model)
    rw [VerifierFeedPrimitive.effect, if_neg hx,
      if_pos (show VerifierFeedPrimitive.isXS (GSVProg.tX, true, Move.stay) from rfl), hg]
    omega

theorem worker_barrier_credit {e : Env k} {leftSym : Fin k} {R rate n : ℕ}
    {Text : List (Fin k)} {x : Config e leftSym R rate} {u v : Snapshot k} {w : Event}
    {caller : Stack (TaskAct k) (TaskCond k)}
    (hmb : e.mark ≠ e.blank) (hu : Valid e leftSym R rate Text n x u caller)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (he : next (taskEval e (fun j => (x.2 j).focus)) u.frames = (v.frames, w))
    (had : Advance e u v w) (hw : ¬ Barrier n u v.frames w) :
    feeds w + afterDebt v.frames + readyCredit e.blank u.model ≤
      2 * instructions w + afterDebt u.frames + readyCredit e.blank v.model := by
  by_cases hblock : Blocked n u w
  · have hd : afterDebt v.frames < afterDebt u.frames := by
      by_contra hh
      exact hw ⟨hblock, by omega⟩
    have hmono := model_ready_bound e w u
    rw [← had.model] at hmono
    have hf : feeds w ≤ 1 := by cases w <;> simp [feeds]
    omega
  · have hc := worker_ready_credit hmb hu hb hm hn he had hblock
    have hd := after_charge _ he
    omega

/-- Account for every real worker, including a genuine wait. Only that
last case loses a service unit; its physical control transition is retained. -/
theorem worker_accounted {e : Env k} {leftSym : Fin k} {R rate n : ℕ}
    {Text : List (Fin k)} {x : Config e leftSym R rate} {u v : Snapshot k} {w : Event}
    {caller : Stack (TaskAct k) (TaskCond k)}
    (hmb : e.mark ≠ e.blank) (hu : Valid e leftSym R rate Text n x u caller)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (he : next (taskEval e (fun j => (x.2 j).focus)) u.frames = (v.frames, w))
    (had : Advance e u v w) (lost : ℕ)
    (hlost : Barrier n u v.frames w → lost = 1) :
    feeds w + afterDebt v.frames + readyCredit e.blank u.model ≤
      2 * instructions w + afterDebt u.frames + readyCredit e.blank v.model + lost := by
  classical
  by_cases hw : Barrier n u v.frames w
  · have hd := after_charge _ he
    have hm := model_ready_bound e w u
    rw [← had.model] at hm
    have hf : feeds w ≤ 1 := by cases w <;> simp [feeds]
    have hl := hlost hw
    omega
  · exact (worker_barrier_credit hmb hu hb hm hn he had hw).trans (Nat.le_add_right _ _)

/-- Continue through optional unsuccessful supplies. The returned
certificate charges each of them to the instruction that created its
postlude, rather than requiring a future input symbol. -/
theorem barrier_prefix {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (N : ℕ) (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (hu : Valid e leftSym R rate Text n x u caller) :
    ∃ m v ws, m ≤ N ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u ws v ∧
      (ws.map feeds).sum + afterDebt v.frames + readyCredit e.blank u.model ≤
        2 * (ws.map instructions).sum + afterDebt u.frames + readyCredit e.blank v.model ∧
      (m = N ∨ y.1.1.1 = 0 ∨ (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt ∨
        Barrier n v (next (taskEval e (fun j => (y.2 j).focus)) v.frames).1
          (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2) := by
  classical
  induction N generalizing x u with
  | zero => exact ⟨0, u, [], Nat.le_refl 0, rfl, hu, .nil u, by simp, Or.inl rfl⟩
  | succ N ih =>
    by_cases hz : x.1.1.1 = 0
    · exact ⟨0, u, [], Nat.zero_le _, rfl, hu, .nil u, by simp, Or.inr (Or.inl hz)⟩
    rcases he : next (taskEval e (fun j => (x.2 j).focus)) u.frames with ⟨gs, w⟩
    by_cases hw : w = .halt
    · refine ⟨0, u, [], Nat.zero_le _, rfl, hu, .nil u, by simp, Or.inr (Or.inr (Or.inl ?_))⟩
      change (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt
      simpa only [he] using hw
    by_cases hblock : Barrier n u gs w
    · refine ⟨0, u, [], Nat.zero_le _, rfl, hu, .nil u, by simp, Or.inr (Or.inr (Or.inr ?_))⟩
      change Barrier n u (next (taskEval e (fun j => (x.2 j).focus)) u.frames).1
        (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2
      simpa only [he] using hblock
    obtain ⟨v, hvf, hv, had⟩ := worker_step (Terminal := Terminal) hc hmb leftSym R rate hb hm hn
      x u caller hu hz gs w he hw
    have hcredit := worker_barrier_credit hmb hu hb hm hn
      (by simpa only [hvf] using he) had (by simpa only [hvf] using hblock)
    obtain ⟨m, z, ws, hmN, hlen, hvz, ht, hfeed, hstop⟩ := ih
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v hv
    refine ⟨m + 1, z, w :: ws, Nat.succ_le_succ hmN, ?_, ?_, .step had ht, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
    · simpa only [Function.iterate_succ_apply] using hvz
    · simp only [List.map_cons, List.sum_cons]
      omega
    · rcases hstop with hfull | hstop
      · exact Or.inl (congrArg Nat.succ hfull)
      · exact Or.inr (by simpa only [Function.iterate_succ_apply] using hstop)

/-- Input-size-independent work bound. Only two currently readable
cells are counted; the already arrived input is not charged again. -/
theorem barrier_window {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n cost : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (hu : Valid e leftSym R rate Text n x u caller)
    {p : GSVProgZLoop.DProg} {U : Fin 11 → STape (Fin k)}
    (hcode : erase u.frames = [p])
    (hr : GSVProgZLoop.RunsTo (TextFeedPipelineIdealEngine.engine e) e.blank p
      (TextFeedPipelineIdealEngine.bundle u.ideal u.dir) U cost) :
    ∃ m v ws, m < 4 * cost + afterDebt u.frames + 4 ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u ws v ∧
      ws.length + readyCredit e.blank u.model ≤
        4 * cost + 1 + afterDebt u.frames + readyCredit e.blank v.model ∧
      (y.1.1.1 = 0 ∨ (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt ∨
        Barrier n v (next (taskEval e (fun j => (y.2 j).focus)) v.frames).1
          (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2) := by
  obtain ⟨m, v, ws, hmN, hlen, hv, ht, hcredit, hstop⟩ :=
    barrier_prefix (Terminal := Terminal) hc hmb leftSym R rate hb hm hn
      (4 * cost + afterDebt u.frames + 4) x u caller hu
  have hwork := worker_bound ht hcode hr
  have hins := follows_bound ht hcode hr
  rw [semantic_count] at hcredit
  have hready := readyCredit_le e.blank v.model
  have hbound : ws.length + readyCredit e.blank u.model ≤
      4 * cost + 1 + afterDebt u.frames + readyCredit e.blank v.model := by omega
  have hlt : m < 4 * cost + afterDebt u.frames + 4 := by omega
  exact ⟨m, v, ws, hlt, hlen, hv, ht, hbound, hstop.resolve_left (by omega)⟩

/-- info: 'PalPeg.TextFeedPipelineSupplyCost.barrier_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms barrier_window

end PalPeg.TextFeedPipelineSupplyCost
