import PalPeg.TextFeedPipelineFrameInstruction
import PalPeg.TextFeedPipelineFrameFeeds
import PalPeg.TextFeedPipelineFrameControl

/-! One invariant packages actual control, both physical FIFOs, and the
ideal verifier. Every non-returning worker event preserves the package. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineCoupled
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineVerifier
open PalPeg.VerifierFeed PalPeg.VerifierFeedRawPrimitive PalPeg.VerifierFeedRefinement
open PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineGuardAgreement
open PalPeg.TextFeedPipelineSourceSafety
variable {k : ℕ} {Terminal : Type}

structure Snapshot (k : ℕ) where
  qt1 : QT k
  mode1 : Mode
  qt2 : QT k
  mode2 : Mode
  model : VMachine' k
  aux : Fin 5 → STape (Fin k)
  old : Fin k
  dir : STape (Fin k)
  ideal : GSVTapes.VTapes' k
  i1 : ℕ
  i2 : ℕ
  frames : List Frame

abbrev Config (e : Env k) (leftSym : Fin k) (R rate : ℕ) :=
  CallCtrl (programs e) (Outer e leftSym R rate) × (Fin 39 → STape (Fin k))

noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPipelineBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _
attribute [local irreducible] ProgLangBank.runChunk

structure Valid (e : Env k) (leftSym : Fin k) (R rate : ℕ) (Text : List (Fin k)) (n : ℕ)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k)) : Prop where
  boundary : AtBoundary (programs e) x.1.2.2.1
  safe : SourceSafe e leftSym rate x.1.1.2.2
  control : x.1.1.2.2.val = render u.frames ++ caller
  physical : x.2 = tapes e u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
  ready1 : Ready e.blank e.mark u.qt1 u.mode1 u.model.Q1
  ready2 : Ready e.blank e.mark u.qt2 u.mode2 u.model.Q2
  refines : Refines e Text n u.model u.ideal u.i1 u.i2

def idealNext (e : Env k) (w : Event) (I : GSVTapes.VTapes' k) : GSVTapes.VTapes' k :=
  match w with
  | .instruction (.inl a) => stepTapes e a I
  | _ => I

def dirNext (e : Env k) (w : Event) (dir : STape (Fin k)) : STape (Fin k) :=
  match w with
  | .instruction (.inr up) => dir.applyAction e.blank (GSVProgZLoop.dirSymbol e.blank e.mark up, .stay)
  | _ => dir

noncomputable def modelNext (e : Env k) (w : Event) (M : VMachine' k) : VMachine' k :=
  match w with
  | .instruction (.inl a) => VerifierFeedPrimitive.effect e a M
  | .feed1 => VerifierFeedRaw.fill1 e.blank e.mark M
  | .feed2 => VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) M
  | _ => M

structure Advance (e : Env k) (u v : Snapshot k) (w : Event) : Prop where
  control : ProgLangControlSteps.Star (idealEval e u.ideal u.dir) (erase u.frames) (destination w v.frames)
  ideal : v.ideal = idealNext e w u.ideal
  direction : v.dir = dirNext e w u.dir
  dispatch : ∃ ev : TaskCond k → Bool, next ev u.frames = (v.frames, w)
  nonhalt : w ≠ .halt
  model : v.model = modelNext e w u.model

/-- The real run is fixed in the conclusion; the witness only records its
physical and ideal state. No controller reset or replacement is performed. -/
theorem worker_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 ≠ 0)
    (gs : List Frame) (w : Event)
    (he : next (taskEval e (fun j => (x.2 j).focus)) u.frames = (gs, w)) (hw : w ≠ .halt) :
    ∃ v, v.frames = gs ∧
      Valid e leftSym R rate Text n (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v caller ∧
      Advance e u v w := by
  cases w with
  | halt => exact False.elim (hw rfl)
  | instruction a =>
    cases a with
    | inl a =>
      obtain ⟨hi, q, m, ht, hby, hcy, h1, h2, hf, hs⟩ :=
        TextFeedPipelineFrameInstruction.run_instruction (Terminal := Terminal) hc hmb leftSym R rate x
          hu.safe hu.boundary hz u.frames gs caller a hu.control he
          u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
      let v : Snapshot k := { u with
        qt2 := q
        mode2 := m
        frames := gs
        model := VerifierFeedPrimitive.effect e a u.model
        ideal := stepTapes e a u.ideal
        i1 := nextIndex a (GSVProg.e8 GSTapes.tT) u.i1
        i2 := nextIndex a GSVProg.tX u.i2 }
      exact ⟨v, rfl, ⟨hby, hs, hcy, ht, h1, h2, hf⟩, ⟨hi, rfl, rfl, ⟨_, he⟩, hw, rfl⟩⟩
    | inr up =>
      obtain ⟨hi, ht, hby, hcy, hf, hs⟩ :=
        TextFeedPipelineFrameControl.run_direction (Terminal := Terminal) hmb leftSym R rate x
          hu.safe hu.boundary hz u.frames gs caller up hu.control he
          u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir hu.physical hb hm hn hu.refines
      let v : Snapshot k := { u with frames := gs, dir := dirNext e (.instruction (.inr up)) u.dir }
      exact ⟨v, rfl, ⟨hby, hs, hcy, ht, hu.ready1, hu.ready2, hf⟩, ⟨hi, rfl, rfl, ⟨_, he⟩, hw, rfl⟩⟩
  | feed1 =>
    obtain ⟨hi, q, m, ht, hby, hcy, h1, h2, hf, hs, _⟩ :=
      TextFeedPipelineFrameFeeds.run_feed1 (Terminal := Terminal) hc hmb leftSym R rate x
        hu.safe hu.boundary hz u.frames gs caller hu.control he
        u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
    let v : Snapshot k := { u with
      qt1 := q
      mode1 := m
      frames := gs
      model := VerifierFeedRaw.fill1 e.blank e.mark u.model }
    exact ⟨v, rfl, ⟨hby, hs, hcy, ht, h1, h2, hf⟩, ⟨hi, rfl, rfl, ⟨_, he⟩, hw, rfl⟩⟩
  | feed2 =>
    obtain ⟨hi, q, m, ht, hby, hcy, h1, h2, hf, hs⟩ :=
      TextFeedPipelineFrameFeeds.run_feed2 (Terminal := Terminal) hc hmb leftSym R rate x
        hu.safe hu.boundary hz u.frames gs caller hu.control he
        u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
    let v : Snapshot k := { u with
      qt2 := q
      mode2 := m
      frames := gs
      model := VerifierFeedPrimitive.effect e (GSVProg.tX, true, .stay) u.model }
    exact ⟨v, rfl, ⟨hby, hs, hcy, ht, h1, h2, hf⟩, ⟨hi, rfl, rfl, ⟨_, he⟩, hw, rfl⟩⟩
  | idle =>
    obtain ⟨hi, q, m, ht, hby, hcy, h1, h2, hf, hs⟩ :=
      TextFeedPipelineFrameControl.run_idle (Terminal := Terminal) hc hmb leftSym R rate x
        hu.safe hu.boundary hz u.frames gs caller hu.control he
        u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir hu.physical hu.ready1 hu.ready2 hb hm hn hu.refines
    let v : Snapshot k := { u with qt1 := q, mode1 := m, frames := gs }
    exact ⟨v, rfl, ⟨hby, hs, hcy, ht, h1, h2, hf⟩, ⟨hi, rfl, rfl, ⟨_, he⟩, hw, rfl⟩⟩

inductive Follows (e : Env k) : Snapshot k → List Event → Snapshot k → Prop where
  | nil (u) : Follows e u [] u
  | step {u v z w ws} (h : Advance e u v w) (ht : Follows e v ws z) :
      Follows e u (w :: ws) z
  | stutter {u v z ws} (hf : v.frames = u.frames) (hi : v.ideal = u.ideal)
      (hd : v.dir = u.dir) (ht : Follows e v ws z) : Follows e u ws z

theorem Follows.trans {e : Env k} {u v z : Snapshot k} {xs ys : List Event}
    (h : Follows e u xs v) (ht : Follows e v ys z) : Follows e u (xs ++ ys) z := by
  induction h with
  | nil => exact ht
  | step had _ ih => exact .step had (ih ht)
  | stutter hf hi hd _ ih => exact .stutter hf hi hd (ih ht)

/-- Soundness of every finite worker segment. The segment only stops early
at an actual enqueue clock or an actual verifier return; those are exposed
in the conclusion, not silently assumed away. -/
theorem worker_prefix {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (N : ℕ) (x : Config e leftSym R rate) (u : Snapshot k)
    (caller : Stack (TaskAct k) (TaskCond k)) (hu : Valid e leftSym R rate Text n x u caller) :
    ∃ m v ws, m ≤ N ∧ ws.length = m ∧
      let y := (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[m] x
      Valid e leftSym R rate Text n y v caller ∧ Follows e u ws v ∧
      (m = N ∨ y.1.1.1 = 0 ∨ (next (taskEval e (fun j => (y.2 j).focus)) v.frames).2 = .halt) := by
  induction N generalizing x u with
  | zero => exact ⟨0, u, [], Nat.le_refl 0, rfl, hu, .nil u, Or.inl rfl⟩
  | succ N ih =>
    by_cases hz : x.1.1.1 = 0
    · exact ⟨0, u, [], Nat.zero_le _, rfl, hu, .nil u, Or.inr (Or.inl hz)⟩
    · rcases he : next (taskEval e (fun j => (x.2 j).focus)) u.frames with ⟨gs, w⟩
      by_cases hw : w = .halt
      · refine ⟨0, u, [], Nat.zero_le _, rfl, hu, .nil u, Or.inr (Or.inr ?_)⟩
        change (next (taskEval e (fun j => (x.2 j).focus)) u.frames).2 = .halt
        simpa only [he] using hw
      · obtain ⟨v, _, hv, had⟩ := worker_step (Terminal := Terminal) hc hmb leftSym R rate hb hm hn
          x u caller hu hz gs w he hw
        obtain ⟨m, z, ws, hmN, hlen, hvz, ht, hstop⟩ := ih
          (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v hv
        refine ⟨m + 1, z, w :: ws, Nat.succ_le_succ hmN, ?_, ?_, .step had ht, ?_⟩
        · simp only [List.length_cons, hlen]
        · simpa only [Function.iterate_succ_apply] using hvz
        · rcases hstop with hstop | hstop
          · exact Or.inl (congrArg Nat.succ hstop)
          · exact Or.inr (by simpa only [Function.iterate_succ_apply] using hstop)

theorem capture_valid (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (a : Terminal) {Text : List (Fin k)} {n : ℕ} (x : Config e leftSym R rate)
    (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) :
    Valid e leftSym R rate Text n
      (x.1, arriveA e.blank (DualQueueShared.capture enc) (some a) x.2)
      { u with old := enc a } caller := by
  refine ⟨hu.boundary, hu.safe, hu.control, ?_, hu.ready1, hu.ready2, hu.refines⟩
  rw [hu.physical]
  exact TextFeedPrefixBank.capture_some e enc a u.qt1 u.mode1 u.qt2 u.mode2
    (prefixModel u.model) u.model.vt.2.Txt2 u.aux u.old u.dir

/-- An actual enqueue advances the arrival frontier and both physical
queues while leaving the suspended verifier and ideal state unchanged. -/
theorem arrival_step {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (leftSym : Fin k) (R rate : ℕ) {Text : List (Fin k)} {n : ℕ}
    (hm : e.mark ∉ Text) (hn : n < Text.length)
    (x : Config e leftSym R rate) (u : Snapshot k) (caller : Stack (TaskAct k) (TaskCond k))
    (hu : Valid e leftSym R rate Text n x u caller) (hz : x.1.1.1 = 0)
    (hfirst : x.1.1.2.1 = false) (ha : Text[n]? = some u.old) :
    ∃ v, Valid e leftSym R rate Text (n + 1)
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) v caller ∧
      v.frames = u.frames ∧ v.ideal = u.ideal ∧ v.dir = u.dir ∧
      v.model.m1 = u.model.m1 ∧ v.model.m2 = u.model.m2 ∧ v.model.vt = u.model.vt := by
  have ham : u.old ≠ e.mark := fun he => hm (he ▸ List.mem_of_getElem? ha)
  obtain ⟨q1, m1, q2, m2, ht, hby, hcy, _, h1, h2, hf⟩ :=
    TextFeedPipelineRefinement.run_arrival (Terminal := Terminal) hc hmb leftSym R rate x
      hu.boundary hz hfirst u.qt1 u.mode1 u.qt2 u.mode2 u.model u.aux u.old u.dir
      hu.physical hu.ready1 hu.ready2 ham hn ha hu.refines
  let v : Snapshot k := { u with
    qt1 := q1
    mode1 := m1
    qt2 := q2
    mode2 := m2
    model := varrive' e.blank e.mark u.old u.model }
  refine ⟨v, ⟨hby, run_safe e leftSym R rate x hu.safe, ?_, ht, h1, h2, hf⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hcy]
  exact hu.control

/-- info: 'PalPeg.TextFeedPipelineCoupled.worker_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_step

/-- info: 'PalPeg.TextFeedPipelineCoupled.worker_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_prefix

/-- info: 'PalPeg.TextFeedPipelineCoupled.arrival_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms arrival_step

end PalPeg.TextFeedPipelineCoupled
