import PalPeg.TextFeedPrefixBank
import PalPeg.ProgLangCallFrame

/-! A finite arrival-bearing prefix-phase controller. Each frame captures
one input, enqueues it in both FIFOs, and executes R complete worker calls.
Semantic refinement below starts after FIFO initialization. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPrefixMachine
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist PalPeg.ProgLangPersist2
open PalPeg.ProgLangBank PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueControl PalPeg.RTQueueClosed
open PalPeg.TextFeedControl

variable {k : ℕ} {Terminal : Type}

abbrev Index := Fin (Fintype.card TextFeedPrefixBank.Label)
noncomputable def encode (a : TextFeedPrefixBank.Label) : Index := Fintype.equivFin _ a
noncomputable def decode (i : Index) : TextFeedPrefixBank.Label := (Fintype.equivFin _).symm i
@[simp] theorem decode_encode (a : TextFeedPrefixBank.Label) : decode (encode a) = a := Equiv.symm_apply_apply _ _

noncomputable def programs (e : Env k) (i : Index) := TextFeedPrefixBank.low e (decode i)

noncomputable def interp (e : Env k) :
    InterpF Terminal (TextFeedPrefixBank.Act k) (TextFeedPrefixBank.Cond k) (Fin k) 39 where
  toInterp := TextFeedPrefixBank.interp e
  flagOf _ := none

abbrev Outer (R : ℕ) := Fin (R + 1) × Bool × CtrlS TextFeedPrefixAtomic.source

def eval (e : Env k) (σ : Fin 39 → Fin k) :=
  TextFeedPrefixAtomic.eval e (fun j => σ (Fin.castAddEmb 19 j))

noncomputable def choose (e : Env k) (R : ℕ) (c : Outer R) (σ : Fin 39 → Fin k) : Outer R × Index :=
  if c.1 = 0 then ((nextPhase c.1, false, c.2.2), encode (.enqueue c.2.1))
  else ((nextPhase c.1, c.2.1, stepCtrlS TextFeedPrefixAtomic.source (eval e σ) c.2.2),
    encode (.work ((stepStack (eval e σ) c.2.2.val).2.getD .idle)))

noncomputable local instance : DecidableEq (TextFeedPrefixBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedPrefixBank.Cond k) := Classical.decEq _
noncomputable local instance (R : ℕ) : DecidableEq (Outer R) := Classical.decEq _

noncomputable def run (e : Env k) (R : ℕ) :=
  callRun (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e R) 93 e.blank

/-- R is a fixed speed parameter, not a function of the prefix or input. -/
noncomputable def machine (e : Env k) (enc : Terminal → Fin k) (R : ℕ) :=
  callFrameMachine (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e R)
    93 (R + 1) e.blank (by omega : 0 < 39)
    ((0, true, startCtrlS TextFeedPrefixAtomic.source) : Outer R) (encode (.enqueue true))
    (DualQueueShared.capture enc)

structure Data (k : ℕ) where
  worker : TextFeedPrefixAtomic.Model k
  q₂ : Queue (Fin k)
  X : TapeConfiguration k
  aux : Fin 5 → STape (Fin k)
  old : Fin k
  dir : STape (Fin k)

def tapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (D : Data k) :=
  TextFeedPrefixBank.tapes e qt₁ m₁ qt₂ m₂ D.worker D.X D.aux D.old D.dir

def enqueue (D : Data k) : Data k :=
  { D with worker := { D.worker with q := snoc D.worker.q D.old }, q₂ := snoc D.q₂ D.old }

def work (e : Env k) (a : TextFeedPrefixAtomic.Act) (D : Data k) : Data k :=
  { D with worker := TextFeedPrefixAtomic.effect e a D.worker }

noncomputable def modelStep (e : Env k) (R : ℕ) (z : Outer R × Data k) : Outer R × Data k :=
  if z.1.1 = 0 then ((nextPhase z.1.1, false, z.1.2.2), enqueue z.2)
  else
    let ec := TextFeedPrefixAtomic.modelEval e z.2.worker
    ((nextPhase z.1.1, z.1.2.1, stepCtrlS TextFeedPrefixAtomic.source ec z.1.2.2),
      work e ((stepStack ec z.1.2.2.val).2.getD .idle) z.2)

theorem eval_tapes (e : Env k) (qt₁ : QT k) (m₁ : Mode) (qt₂ : QT k) (m₂ : Mode) (D : Data k) :
    eval e (fun j => (tapes e qt₁ m₁ qt₂ m₂ D j).focus) = TextFeedPrefixAtomic.modelEval e D.worker := by
  change TextFeedPrefixAtomic.eval e
    (fun j => ((Fin.append (TextFeedPrefixAtomic.tapes e qt₁ m₁ D.worker)
      (TextFeedPrefixReady.rest e qt₂ m₂ D.X (Fin.append D.aux (TextFeedInput.cell D.old)) D.dir))
      (Fin.castAdd 19 j)).focus) = _
  simp only [Fin.append_left]
  exact TextFeedPrefixAtomic.eval_tapes e qt₁ m₁ D.worker

attribute [local irreducible] runChunk

theorem run_refine {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R : ℕ) (x : CallCtrl (programs e) (Outer R) × (Fin 39 → STape (Fin k)))
    (D : Data k) {qt₁ qt₂ : QT k} {m₁ m₂ : Mode}
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ D) (hf : x.1.1.2.1 = false)
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (h₁ : Ready e.blank e.mark qt₁ m₁ D.worker.q) (h₂ : Ready e.blank e.mark qt₂ m₂ D.q₂)
    (ha : D.old ≠ e.mark) :
    let z := modelStep e R (x.1.1, D)
    let y := run (Terminal := Terminal) e R x
    ∃ qt₁' m₁' qt₂' m₂', y.1.1 = z.1 ∧ y.2 = tapes e qt₁' m₁' qt₂' m₂' z.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧
      Ready e.blank e.mark qt₁' m₁' z.2.worker.q ∧ Ready e.blank e.mark qt₂' m₂' z.2.q₂ := by
  by_cases hz : x.1.1.1 = 0
  · obtain ⟨ticks, qt₁', m₁', qt₂', m₂', hn, ⟨tr, he, ht, hlen⟩, hr₁, hr₂⟩ :=
      TextFeedPrefixBank.enqueue_matches (Terminal := Terminal) hc hmb D.worker D.q₂
        qt₁ m₁ qt₂ m₂ D.X D.aux D.old D.dir h₁ h₂ ha
    have he' : Exec (interp (Terminal := Terminal) e).toInterp e.blank
        (programs e (choose e R x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
      simp only [programs, choose, hz, ↓reduceIte, hf, decode_encode]
      rw [hx]
      exact he
    obtain ⟨hout, hb', _, _⟩ := callRun_exec (programs e) (fun _ => interp (Terminal := Terminal) e)
      (choose e R) 93 e.blank x hb tr he' (by omega)
    rw [hx, tapes, ht] at hout
    dsimp only
    simp only [modelStep, hz, ↓reduceIte]
    refine ⟨qt₁', m₁', qt₂', m₂', ?_, hout, hb', hr₁, hr₂⟩
    change (choose e R x.1.1 (fun j => (x.2 j).focus)).1 = _
    simp only [choose, hz, ↓reduceIte]
  · let a := (stepStack (TextFeedPrefixAtomic.modelEval e D.worker) x.1.1.2.2.val).2.getD .idle
    obtain ⟨ticks, qt₁', m₁', hn, ⟨tr, he, ht, hlen⟩, hr₁⟩ :=
      TextFeedPrefixBank.work_matches (Terminal := Terminal) hc hmb a D.worker qt₁ m₁ qt₂ m₂
        D.X D.aux D.old D.dir h₁
    have he' : Exec (interp (Terminal := Terminal) e).toInterp e.blank
        (programs e (choose e R x.1.1 (fun j => (x.2 j).focus)).2) x.2 tr := by
      simp only [programs, choose, hz, ↓reduceIte, decode_encode]
      rw [hx, eval_tapes]
      exact he
    obtain ⟨hout, hb', _, _⟩ := callRun_exec (programs e) (fun _ => interp (Terminal := Terminal) e)
      (choose e R) 93 e.blank x hb tr he' (by omega)
    rw [hx, tapes, ht] at hout
    dsimp only
    simp only [modelStep, hz, ↓reduceIte]
    refine ⟨qt₁', m₁', qt₂, m₂, ?_, hout, hb', hr₁, h₂⟩
    change (choose e R x.1.1 (fun j => (x.2 j).focus)).1 = _
    simp only [choose, hz, ↓reduceIte]
    rw [hx, eval_tapes]

theorem modelStep_old (e : Env k) (R : ℕ) (z : Outer R × Data k) :
    (modelStep e R z).2.old = z.2.old := by
  unfold modelStep
  split_ifs <;> rfl

theorem modelStep_first (e : Env k) (R : ℕ) (z : Outer R × Data k) (hf : z.1.2.1 = false) :
    (modelStep e R z).1.2.1 = false := by
  unfold modelStep
  split_ifs
  · rfl
  · exact hf

theorem modelStep_counter (e : Env k) (R : ℕ) (z : Outer R × Data k) :
    (modelStep e R z).1.1 = nextPhase z.1.1 := by
  unfold modelStep
  split_ifs <;> rfl

theorem model_counter_iterate (e : Env k) (R N : ℕ) (z : Outer R × Data k) :
    ((modelStep e R)^[N] z).1.1 = nextPhase^[N] z.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', modelStep_counter, ih, Function.iterate_succ_apply']

theorem run_refine_iterate {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (R N : ℕ) (x : CallCtrl (programs e) (Outer R) × (Fin 39 → STape (Fin k)))
    (D : Data k) {qt₁ qt₂ : QT k} {m₁ m₂ : Mode}
    (hx : x.2 = tapes e qt₁ m₁ qt₂ m₂ D) (hf : x.1.1.2.1 = false)
    (hb : AtBoundary (programs e) x.1.2.2.1)
    (h₁ : Ready e.blank e.mark qt₁ m₁ D.worker.q) (h₂ : Ready e.blank e.mark qt₂ m₂ D.q₂)
    (ha : D.old ≠ e.mark) :
    let z := (modelStep e R)^[N] (x.1.1, D)
    let y := (run (Terminal := Terminal) e R)^[N] x
    ∃ qt₁' m₁' qt₂' m₂', y.1.1 = z.1 ∧ y.2 = tapes e qt₁' m₁' qt₂' m₂' z.2 ∧
      AtBoundary (programs e) y.1.2.2.1 ∧
      Ready e.blank e.mark qt₁' m₁' z.2.worker.q ∧ Ready e.blank e.mark qt₂' m₂' z.2.q₂ := by
  induction N generalizing x D qt₁ m₁ qt₂ m₂ with
  | zero => exact ⟨qt₁, m₁, qt₂, m₂, rfl, hx, hb, h₁, h₂⟩
  | succ N ih =>
    obtain ⟨qt₁', m₁', qt₂', m₂', hc', ht, hb', hr₁, hr₂⟩ := run_refine hc hmb R x D hx hf hb h₁ h₂ ha
    have hf' : (run (Terminal := Terminal) e R x).1.1.2.1 = false := by
      rw [hc']
      exact modelStep_first e R _ hf
    have ha' : (modelStep e R (x.1.1, D)).2.old ≠ e.mark := by
      rwa [modelStep_old]
    have hh := ih (run (Terminal := Terminal) e R x) (modelStep e R (x.1.1, D)).2
      ht hf' hb' hr₁ hr₂ ha'
    rw [hc'] at hh
    simpa only [Function.iterate_succ_apply, Prod.mk.eta] using hh

def capture (D : Data k) (a : Fin k) : Data k := { D with old := a }

noncomputable def modelFrame (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) : Outer R × Data k :=
  (modelStep e R)^[R + 1] (z.1, capture z.2 a)

theorem frame_counter (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) (hz : z.1.1 = 0) :
    (modelFrame e R a z).1.1 = 0 := by
  rw [modelFrame, model_counter_iterate, hz]
  exact nextPhase_iterate_round (Nat.zero_lt_succ R)

theorem round_eq (e : Env k) (enc : Terminal → Fin k) (R : ℕ) (a : Terminal)
    (c : CallCtrl (programs e) (Outer R)) (T : Fin 39 → STape (Fin k)) :
    (machine e enc R).sRound { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := T } a =
      let y := (run (Terminal := Terminal) e R)^[R + 1]
        (c, arriveA e.blank (DualQueueShared.capture enc) (some a) T)
      { state := ((y.1, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := y.2 } :=
  callFrameMachine_round (programs e) (fun _ => interp (Terminal := Terminal) e) (choose e R)
    93 (R + 1) e.blank (by omega) (0, true, startCtrlS TextFeedPrefixAtomic.source)
    (encode (.enqueue true)) (DualQueueShared.capture enc) a c T

attribute [local irreducible] StructuredMachine.sRound

/-- One actual external arrival and R+1 complete calls, with both FIFO
invariants and both clock boundaries restored before the next input. -/
theorem round_refine {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (R : ℕ) (a : Terminal) (ha : enc a ≠ e.mark)
    (c : CallCtrl (programs e) (Outer R)) (D : Data k) {qt₁ qt₂ : QT k} {m₁ m₂ : Mode}
    (hc0 : c.1.1 = 0) (hf : c.1.2.1 = false) (hb : AtBoundary (programs e) c.2.2.1)
    (h₁ : Ready e.blank e.mark qt₁ m₁ D.worker.q) (h₂ : Ready e.blank e.mark qt₂ m₂ D.q₂) :
    let z := modelFrame e R (enc a) (c.1, D)
    let y := (machine e enc R).sRound
      { state := ((c, ⟨0, by omega⟩), ⟨0, by omega⟩), tape := tapes e qt₁ m₁ qt₂ m₂ D } a
    ∃ qt₁' m₁' qt₂' m₂', y.state.1.1.1 = z.1 ∧ y.tape = tapes e qt₁' m₁' qt₂' m₂' z.2 ∧
      AtBoundary (programs e) y.state.1.1.2.2.1 ∧
      Ready e.blank e.mark qt₁' m₁' z.2.worker.q ∧ Ready e.blank e.mark qt₂' m₂' z.2.q₂ ∧
      y.state.1.1.1.1 = 0 ∧ y.state.1.2 = 0 ∧ y.state.2 = 0 := by
  have hcap : arriveA e.blank (DualQueueShared.capture enc) (some a) (tapes e qt₁ m₁ qt₂ m₂ D) =
      tapes e qt₁ m₁ qt₂ m₂ (capture D (enc a)) :=
    TextFeedPrefixBank.capture_some e enc a qt₁ m₁ qt₂ m₂ D.worker D.X D.aux D.old D.dir
  obtain ⟨qt₁', m₁', qt₂', m₂', he, ht, hb', hr₁, hr₂⟩ := run_refine_iterate hc hmb R (R + 1)
    (c, tapes e qt₁ m₁ qt₂ m₂ (capture D (enc a))) (capture D (enc a)) rfl hf hb h₁ h₂ ha
  dsimp only
  rw [round_eq, hcap]
  refine ⟨qt₁', m₁', qt₂', m₂', he, ht, hb', hr₁, hr₂, ?_, rfl, rfl⟩
  rw [he]
  exact frame_counter e R (enc a) (c.1, D) hc0

theorem model_old_iterate (e : Env k) (R N : ℕ) (z : Outer R × Data k) :
    ((modelStep e R)^[N] z).2.old = z.2.old := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', modelStep_old, ih]

theorem model_first_iterate (e : Env k) (R N : ℕ) (z : Outer R × Data k) (hf : z.1.2.1 = false) :
    ((modelStep e R)^[N] z).1.2.1 = false := by
  induction N with
  | zero => exact hf
  | succ N ih => rw [Function.iterate_succ_apply']; exact modelStep_first e R _ ih

theorem model_q₂_prefix (e : Env k) (R : ℕ) (z : Outer R × Data k) (hz : z.1.1 = 0) :
    ∀ N : ℕ, N ≤ R + 1 →
    ((modelStep e R)^[N] z).2.q₂ = if N = 0 then z.2.q₂ else snoc z.2.q₂ z.2.old := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hn
    have hc : ((modelStep e R)^[N] z).1.1 = (⟨N, by omega⟩ : Fin (R + 1)) := by
      rw [model_counter_iterate, hz]
      exact nextPhase_iterate (Nat.zero_lt_succ R) N (by omega)
    by_cases hN : N = 0
    · subst N
      change (modelStep e R z).2.q₂ = snoc z.2.q₂ z.2.old
      rw [modelStep, if_pos hz]
      rfl
    · have hc' : ((modelStep e R)^[N] z).1.1 ≠ 0 := by
        rw [hc]
        intro he
        exact hN (congrArg Fin.val he)
      rw [Function.iterate_succ_apply', modelStep, if_neg hc']
      change ((modelStep e R)^[N] z).2.q₂ = _
      rw [ih (by omega), if_neg hN, if_neg (Nat.succ_ne_zero N)]

/-- Q2 is fed exactly once per frame, regardless of worker suspension. -/
theorem frame_q₂ (e : Env k) (R : ℕ) (a : Fin k) (z : Outer R × Data k) (hz : z.1.1 = 0) :
    (modelFrame e R a z).2.q₂ = snoc z.2.q₂ a := by
  have hh := model_q₂_prefix e R (z.1, capture z.2 a) hz (R + 1) (by omega)
  simpa only [modelFrame, if_neg (Nat.succ_ne_zero R), capture] using hh

abbrev Config (e : Env k) (R : ℕ) :=
  SConfig ((CallCtrl (programs e) (Outer R) × Fin 94) × Fin ((R + 1) * 94 + 1)) (Fin k) 39

def Sim (e : Env k) (R : ℕ) (x : Config e R) (z : Outer R × Data k) : Prop :=
  ∃ c qt₁ m₁ qt₂ m₂,
    x = { state := ((c, 0), 0), tape := tapes e qt₁ m₁ qt₂ m₂ z.2 } ∧ c.1 = z.1 ∧
    z.1.1 = 0 ∧ z.1.2.1 = false ∧ AtBoundary (programs e) c.2.2.1 ∧
    Ready e.blank e.mark qt₁ m₁ z.2.worker.q ∧ Ready e.blank e.mark qt₂ m₂ z.2.q₂

theorem config_ext {e : Env k} {R : ℕ} {x y : Config e R}
    (hs : x.state = y.state) (ht : x.tape = y.tape) : x = y := by
  cases x; cases y; cases hs; cases ht; rfl

theorem round_sim {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (R : ℕ) (a : Terminal) (ha : enc a ≠ e.mark)
    {x : Config e R} {z : Outer R × Data k} (h : Sim e R x z) :
    Sim e R ((machine e enc R).sRound x a) (modelFrame e R (enc a) z) := by
  obtain ⟨c, qt₁, m₁, qt₂, m₂, rfl, hcz, hz, hf, hb, h₁, h₂⟩ := h
  obtain ⟨qt₁', m₁', qt₂', m₂', he, ht, hb', hr₁, hr₂, hp, hph, hph'⟩ :=
    round_refine hc hmb enc R a ha c z.2 (hcz ▸ hz) (hcz ▸ hf) hb h₁ h₂
  rw [hcz] at he ht hr₁ hr₂
  refine ⟨_, qt₁', m₁', qt₂', m₂', ?_, he, frame_counter e R (enc a) z hz,
    model_first_iterate e R (R + 1) (z.1, capture z.2 (enc a)) hf, hb', hr₁, hr₂⟩
  apply config_ext
  · exact Prod.ext (Prod.ext rfl hph) hph'
  · exact ht

/-- Continuous real input, retaining the same finite control between frames. -/
theorem word_sim {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    (enc : Terminal → Fin k) (R : ℕ) (w : List Terminal) (ha : ∀ a ∈ w, enc a ≠ e.mark)
    {x : Config e R} {z : Outer R × Data k} (h : Sim e R x z) :
    Sim e R (w.foldl (machine e enc R).sRound x)
      (w.foldl (fun z a => modelFrame e R (enc a) z) z) := by
  induction w generalizing x z with
  | nil => exact h
  | cons a w ih =>
    exact ih (fun b hb => ha b (List.mem_cons_of_mem a hb))
      (round_sim hc hmb enc R a (ha a List.mem_cons_self) h)

theorem word_q₂ (e : Env k) (enc : Terminal → Fin k) (R : ℕ) (w : List Terminal)
    (z : Outer R × Data k) (hz : z.1.1 = 0) :
    (w.foldl (fun z a => modelFrame e R (enc a) z) z).2.q₂ =
      (w.map enc).foldl snoc z.2.q₂ := by
  induction w generalizing z with
  | nil => rfl
  | cons a w ih =>
    rw [List.foldl_cons, ih _ (frame_counter e R (enc a) z hz), frame_q₂ e R (enc a) z hz]
    rfl

theorem word_q₂_contents (e : Env k) (enc : Terminal → Fin k) (R : ℕ) (w : List Terminal)
    (z : Outer R × Data k) (hz : z.1.1 = 0) (hi : Inv z.2.q₂) :
    toList (w.foldl (fun z a => modelFrame e R (enc a) z) z).2.q₂ = toList z.2.q₂ ++ w.map enc := by
  rw [word_q₂ e enc R w z hz]
  exact toList_foldl_snoc _ _ hi

/-- info: 'PalPeg.TextFeedPrefixMachine.word_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms word_sim

/-- info: 'PalPeg.TextFeedPrefixMachine.frame_q₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frame_q₂

/-- info: 'PalPeg.TextFeedPrefixMachine.round_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms round_refine

/-- info: 'PalPeg.TextFeedPrefixMachine.run_refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_refine

end PalPeg.TextFeedPrefixMachine
