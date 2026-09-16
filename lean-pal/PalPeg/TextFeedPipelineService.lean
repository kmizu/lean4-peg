import PalPeg.TextFeedPipelineFrontier

/-! A single service invariant for the actual pipeline, including suspended
macros, real waits and outer-loop reentry. All records below are proof data;
the controller and its fixed input schedule are unchanged. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineService
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.TextFeedControl
open PalPeg.TextFeedPipelineControl PalPeg.TextFeedPipelineFrames PalPeg.TextFeedPipelineCoupled
open PalPeg.TextFeedPipelineInputMacro PalPeg.TextFeedPipelineInputRun
open PalPeg.TextFeedPipelineFrameCost PalPeg.TextFeedPipelineInstructionCost
open PalPeg.TextFeedPipelineSupplyCost PalPeg.TextFeedPipelineFrontier
open PalPeg.VerifierFeedSupplyProgress PalPeg.GSVerifierZ

variable {k : ℕ} {Terminal : Type}

structure Macro (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (Text leftPat rightPat : List (Fin k)) (p r n : ℕ)
    (x : Config e leftSym R rate) where
  n₀ : ℕ
  x₀ : Config e leftSym R rate
  u₀ : Snapshot k
  z : VStateZ
  u : Snapshot k
  events : List Event
  waits : ℕ
  frontier : n₀ ≤ n
  origin : Valid e leftSym R rate Text n₀ x₀ u₀ [verifyLoop rate]
  start : Start e Text leftPat rightPat rate p r n₀ u₀ z
  valid : Valid e leftSym R rate Text n x u [verifyLoop rate]
  follows : Follows e u₀ events u
  wait_le : waits ≤ events.length
  credit : (events.map feeds).sum + afterDebt u.frames + readyCredit e.blank u₀.model ≤
    2 * (events.map instructions).sum + afterDebt u₀.frames + readyCredit e.blank u.model + waits

def Macro.score {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : Macro e leftSym R rate Text leftPat rightPat p r n x) : ℕ :=
  progressRate rate * Phi rate a.z.1 + (a.events.length - a.waits)

structure Entry (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (Text leftPat rightPat : List (Fin k)) (p r n : ℕ)
    (x : Config e leftSym R rate) where
  n₀ : ℕ
  x₀ : Config e leftSym R rate
  u₀ : Snapshot k
  z : VStateZ
  u : Snapshot k
  rank : ℕ
  positive : 0 < rank
  rank_le : rank ≤ 3
  paid : rank ≤ progressRate rate * Phi rate z.1
  frontier : n₀ ≤ n
  origin : Valid e leftSym R rate Text n₀ x₀ u₀ [verifyLoop rate]
  feed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
    leftPat rightPat Text rate p r n₀ u₀.model
  ghost : u₀.model.z = (z.1, z.2.head)
  wf : ZWf leftPat.length z.2
  direction : u₀.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0
  valid : TextFeedPipelineReentryInput.Entry e leftSym R rate Text n x u rank
  ideal : u.ideal = u₀.ideal
  dir : u.dir = u₀.dir

def Entry.score {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : Entry e leftSym R rate Text leftPat rightPat p r n x) : ℕ :=
  progressRate rate * Phi rate a.z.1 - a.rank

inductive State (e : Env k) (leftSym : Fin k) (R rate : ℕ)
    (Text leftPat rightPat : List (Fin k)) (p r n : ℕ)
    (x : Config e leftSym R rate) where
  | macro (a : Macro e leftSym R rate Text leftPat rightPat p r n x)
  | entry (a : Entry e leftSym R rate Text leftPat rightPat p r n x)

def State.score {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate} :
    State e leftSym R rate Text leftPat rightPat p r n x → ℕ
  | .macro a => a.score
  | .entry a => a.score

def State.z {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate} :
    State e leftSym R rate Text leftPat rightPat p r n x → VStateZ
  | .macro a => a.z
  | .entry a => a.z

def Evolves {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x y : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (b : State e leftSym R rate Text leftPat rightPat p r n y) : Prop :=
  b.z = a.z ∨ (b.z = vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) a.z ∧
    ∃ d, b = .entry d ∧ d.rank = 2)

inductive Trace (e : Env k) (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    (Text leftPat rightPat : List (Fin k)) (p r : ℕ) :
    {n₀ n₁ : ℕ} → {x₀ x₁ : Config e leftSym R rate} →
    State e leftSym R rate Text leftPat rightPat p r n₀ x₀ →
    List (Option Terminal) → State e leftSym R rate Text leftPat rightPat p r n₁ x₁ → Prop where
  | refl {n x} (a : State e leftSym R rate Text leftPat rightPat p r n x) : Trace e leftSym R rate enc Text leftPat rightPat p r a [] a
  | worker {n x} {a : State e leftSym R rate Text leftPat rightPat p r n x}
      {b : State e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x)}
      (hz : x.1.1.1 ≠ 0) (h : Evolves a b) : Trace e leftSym R rate enc Text leftPat rightPat p r a [none] b
  | arrival {n x} (c : Terminal) {a : State e leftSym R rate Text leftPat rightPat p r n x}
      {b : State e leftSym R rate Text leftPat rightPat p r (n + 1)
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate (captured e leftSym R rate enc c x))}
      (hz : x.1.1.1 = 0) (h : b.z = a.z) : Trace e leftSym R rate enc Text leftPat rightPat p r a [some c] b
  | trans {n₀ n₁ n₂ x₀ x₁ x₂ xs ys}
      {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
      {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
      {c : State e leftSym R rate Text leftPat rightPat p r n₂ x₂}
      (h : Trace e leftSym R rate enc Text leftPat rightPat p r a xs b)
      (h' : Trace e leftSym R rate enc Text leftPat rightPat p r b ys c) :
      Trace e leftSym R rate enc Text leftPat rightPat p r a (xs ++ ys) c

def schedule (R : ℕ) (as : List Terminal) : List (Option Terminal) :=
  as.flatMap (fun a => some a :: List.replicate R none)

def target (rate : ℕ) (rightPat : List (Fin k)) (n : ℕ) : ℕ :=
  progressRate rate * ((rate + 1) * n) - progressRate rate * (rate * rightPat.length)

/-- The prefix endpoint starts at the existing outer loop, with its three
pending calls charged before any verifier progress is claimed. -/
def Entry.initial {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (u : Snapshot k) (z : VStateZ)
    (hv : Valid e leftSym R rate Text n x u [verifyLoop rate])
    (hf : u.frames = [])
    (hfeed : VerifierFeed.VFeedInv' e.blank e.startSym e.endSym e.mark
      leftPat rightPat Text rate p r n u.model)
    (hg : u.model.z = (z.1, z.2.head)) (hw : ZWf leftPat.length z.2)
    (hd : u.dir = GSVProgZLoop.dirTape e.blank e.mark z.2.up 0)
    (hpaid : 3 ≤ progressRate rate * Phi rate z.1) :
    Entry e leftSym R rate Text leftPat rightPat p r n x where
  n₀ := n
  x₀ := x
  u₀ := u
  z := z
  u := u
  rank := 3
  positive := by decide
  rank_le := by decide
  paid := hpaid
  frontier := Nat.le_refl _
  origin := hv
  feed := hfeed
  ghost := hg
  wf := hw
  direction := hd
  valid := ⟨hv, by simp only [hf, next]⟩
  ideal := rfl
  dir := rfl

/-- Startup must leave credit for the outer-loop calls as well as the
input frontier. This arithmetic condition is the exact interface to prep's
deadline, and does not treat initialization as free verifier work. -/
theorem Entry.initial_deadline {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : Entry e leftSym R rate Text leftPat rightPat p r n x)
    (hpos : a.z.1.pos = leftPat.length) (hq : a.z.1.q = 0)
    (hbudget : progressRate rate * ((rate + 1) * n) + a.rank ≤
      progressRate rate * ((rate + 1) * leftPat.length) +
        progressRate rate * (rate * rightPat.length)) :
    target rate rightPat n ≤ a.score := by
  have hp := a.paid
  simp only [Phi, hpos, hq, Nat.add_zero] at hp
  simp only [target, Entry.score, Phi, hpos, hq, Nat.add_zero]
  omega

theorem Macro.disabled {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : Macro e leftSym R rate Text leftPat rightPat p r n x)
    (he : ¬ Enabled rightPat n a.z.1) : target rate rightPat n ≤ a.score := by
  have hq : a.z.1.q ≤ rightPat.length := by simpa only [a.start.ghost] using a.start.feed.qle
  have hn : n ≤ a.z.1.pos + a.z.1.q := by
    by_contra hh
    exact he (Or.inr (by omega))
  have hm := Nat.mul_le_mul_left (rate + 1) hn
  have hq' := Nat.mul_le_mul_left rate hq
  have hb : (rate + 1) * n ≤ Phi rate a.z.1 + rate * rightPat.length := by
    simp only [Phi]
    nlinarith
  have hc := Nat.mul_le_mul_left (progressRate rate) hb
  simp only [Nat.mul_add] at hc
  simp only [target, Macro.score]
  omega

/-- After the real startup calls have finished, the initial scan potential
pays the frontier deadline. This also applies when the left pattern is empty. -/
theorem Macro.initial_deadline {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : Macro e leftSym R rate Text leftPat rightPat p r n x)
    (hpos : a.z.1.pos = leftPat.length) (hq : a.z.1.q = 0)
    (hbudget : (rate + 1) * n ≤
      (rate + 1) * leftPat.length + rate * rightPat.length) :
    target rate rightPat n ≤ a.score := by
  have hm := Nat.mul_le_mul_left (progressRate rate) hbudget
  simp only [Nat.mul_add] at hm
  simp only [target, Macro.score, Phi, hpos, hq, Nat.add_zero]
  omega

theorem Macro.worker {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : Macro e leftSym R rate Text leftPat rightPat p r n x)
    (hc : Conditions e Text leftPat rightPat rate p r a.z)
    (hpat : 0 < rightPat.length) (hn : n ≤ Text.length) (hz : x.1.1.1 ≠ 0)
    (hhalt : (next (taskEval e (fun j => (x.2 j).focus)) a.u.frames).2 ≠ .halt) :
    ∃ b : Macro e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x),
      b.z = a.z ∧ min (a.score + 1) (target rate rightPat n) ≤ b.score := by
  classical
  rcases he : next (taskEval e (fun j => (x.2 j).focus)) a.u.frames with ⟨gs, w⟩
  have hw : w ≠ .halt := by simpa only [he] using hhalt
  obtain ⟨v, hvf, hv, had⟩ := worker_step (Terminal := Terminal) hcode hc.mark_blank leftSym R rate
    hc.blank_text hc.mark_text hn x a.u [verifyLoop rate] a.valid hz gs w he hw
  let lost : ℕ := if Barrier n a.u gs w then 1 else 0
  have hl : lost ≤ 1 := by unfold lost; split_ifs <;> omega
  have hc' := worker_accounted hc.mark_blank a.valid hc.blank_text hc.mark_text hn
    (by simpa only [hvf] using he) had lost (by
      intro hb
      rw [hvf] at hb
      simp only [lost, if_pos hb])
  let b : Macro e leftSym R rate Text leftPat rightPat p r n
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) :=
    { n₀ := a.n₀, x₀ := a.x₀, u₀ := a.u₀, z := a.z, u := v
      events := a.events ++ [w], waits := a.waits + lost
      frontier := a.frontier, origin := a.origin, start := a.start
      valid := hv, follows := a.follows.trans (.step had (.nil v))
      wait_le := by
        simp only [List.length_append, List.length_singleton]
        have := a.wait_le
        omega
      credit := by
        simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
          List.sum_nil, Nat.add_zero]
        have := a.credit
        omega }
  refine ⟨b, rfl, ?_⟩
  by_cases hb : Barrier n a.u gs w
  · have hnot : ¬ Enabled rightPat n a.z.1 := by
      intro hen
      have hh := TextFeedPipelineMacroDemand.macro_not_barrier leftSym R rate a.origin.refines
        a.start hc hpat a.frontier hen a.follows x [verifyLoop rate] a.valid hn
      exact hh (by simpa only [he] using hb)
    have ht := a.disabled hnot
    have hs : b.score = a.score := by
      simp only [Macro.score, b, lost, if_pos hb, List.length_append, List.length_singleton]
      omega
    rw [hs]
    exact (Nat.min_le_right _ _).trans ht
  · have hs : b.score = a.score + 1 := by
      simp only [Macro.score, b, lost, if_neg hb, Nat.add_zero, List.length_append, List.length_singleton]
      have := a.wait_le
      omega
    rw [hs]
    exact Nat.min_le_left _ _

theorem Entry.worker {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : Entry e leftSym R rate Text leftPat rightPat p r n x)
    (hmb : e.mark ≠ e.blank) (hb : e.blank ∉ Text) (hm : e.mark ∉ Text)
    (hn : n ≤ Text.length) (hz : x.1.1.1 ≠ 0) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x),
      b.z = a.z ∧ a.score + 1 ≤ b.score := by
  obtain ⟨t, v, ht, hv, hi, hd, _⟩ := a.valid.worker hcode hmb leftSym R rate hb hm hn
    x a.u a.positive a.rank_le hz
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨hv', hs⟩ := TextFeedPipelineReentry.restart a.origin a.feed a.ghost a.wf a.direction
      hv.1 hv.2 (hi.trans a.ideal) (hd.trans a.dir)
    let v' := TextFeedPipelineMacroBoundary.annotate v a.z
    let b : Macro e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) :=
      { n₀ := n, x₀ := _, u₀ := v', z := a.z, u := v', events := [], waits := 0
        frontier := Nat.le_refl _, origin := hv', start := hs, valid := hv'
        follows := .nil _, wait_le := by simp, credit := by simp }
    refine ⟨.macro b, rfl, ?_⟩
    simp only [State.score, Macro.score, b, List.length_nil, Nat.sub_self, Nat.add_zero, Entry.score]
    have := a.paid
    have := a.positive
    omega
  · let b : Entry e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) :=
      { n₀ := a.n₀, x₀ := a.x₀, u₀ := a.u₀, z := a.z, u := v, rank := t
        positive := by omega, rank_le := by have := a.rank_le; omega
        paid := Nat.le_trans (Nat.le_of_lt ht) a.paid
        frontier := a.frontier, origin := a.origin, feed := a.feed, ghost := a.ghost
        wf := a.wf, direction := a.direction, valid := hv
        ideal := hi.trans a.ideal, dir := hd.trans a.dir }
    refine ⟨.entry b, rfl, ?_⟩
    simp only [State.score, Entry.score, b]
    have := a.paid
    omega

theorem Macro.retire {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : Macro e leftSym R rate Text leftPat rightPat p r n x)
    (hc : Conditions e Text leftPat rightPat rate p r a.z)
    (hn : n ≤ Text.length) (hz : x.1.1.1 ≠ 0)
    (hhalt : (next (taskEval e (fun j => (x.2 j).focus)) a.u.frames).2 = .halt) :
    ∃ b : Entry e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x),
      b.z = vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) a.z ∧
      b.rank = 2 ∧ a.score + 1 ≤ b.score := by
  obtain ⟨hv, hf, hw, hd, hg⟩ := TextFeedPipelineMacroBoundary.compiled_boundary leftSym R rate
    a.x₀ x a.u₀ a.u [verifyLoop rate] a.origin a.valid a.start.feed a.start.ghost
    hc.mark_blank hc.blank_text hc.mark_text hn a.follows hhalt hc.positive_rate hc.positive_p
    hc.start_right hc.end_right hc.end_left hc.start_left hc.start_end
    a.start.wf a.start.direction a.start.code
  let z' := vStepZ leftPat rightPat rate p r (TextFeed.padW e.blank Text Text.length) a.z
  let u' := TextFeedPipelineMacroBoundary.annotate a.u z'
  have hh : (next (taskEval e (fun j => (x.2 j).focus)) u'.frames).2 = .halt := hhalt
  obtain ⟨v, hv', hframes, _, hi, hd'⟩ := TextFeedPipelineReentry.return_idle hcode hc.mark_blank
    leftSym R rate x u' hv hz hh
  have hpay := macro_credit a.waits a.origin.refines a.start hc a.follows a.credit
  have hscore : a.score + 8 ≤ progressRate rate * Phi rate z'.1 := by
    have := a.wait_le
    simp only [Macro.score]
    change a.events.length + 8 + progressRate rate * Phi rate a.z.1 ≤
      progressRate rate * Phi rate z'.1 + a.waits at hpay
    omega
  let b : Entry e leftSym R rate Text leftPat rightPat p r n
      (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x) :=
    { n₀ := n, x₀ := x, u₀ := u', z := z', u := v, rank := 2
      positive := by omega, rank_le := by omega, paid := by omega
      frontier := Nat.le_refl _, origin := hv, feed := hf, ghost := hg, wf := hw, direction := hd
      valid := ⟨hv', hframes⟩, ideal := hi, dir := hd' }
  refine ⟨b, rfl, rfl, ?_⟩
  simp only [Entry.score, b]
  omega

/-- Every actual worker gains one unit of service, unless the current
input's target has already been met. Returns and all reentry phases are
included in this one statement. -/
theorem State.worker {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (hn : n ≤ Text.length) (hz : x.1.1.1 ≠ 0) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r n
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate x),
      Evolves a b ∧ min (a.score + 1) (target rate rightPat n) ≤ b.score := by
  classical
  cases a with
  | «macro» a =>
    by_cases hh : (next (taskEval e (fun j => (x.2 j).focus)) a.u.frames).2 = .halt
    · obtain ⟨b, hzb, hrb, hb⟩ := a.retire hcode leftSym R rate (hc a.z) hn hz hh
      exact ⟨.entry b, Or.inr ⟨hzb, b, rfl, hrb⟩, (Nat.min_le_left _ _).trans hb⟩
    · obtain ⟨b, hzb, hb⟩ := a.worker hcode leftSym R rate (hc a.z) hpat hn hz hh
      exact ⟨.macro b, Or.inl hzb, hb⟩
  | entry a =>
    obtain ⟨b, hzb, hb⟩ := a.worker hcode leftSym R rate (hc a.z).mark_blank (hc a.z).blank_text
      (hc a.z).mark_text hn hz
    exact ⟨b, Or.inl hzb, (Nat.min_le_left _ _).trans hb⟩

/-- info: 'PalPeg.TextFeedPipelineService.State.worker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.worker

theorem State.arrival {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (c : Terminal)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hn : n < Text.length) (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hc0 : Text[n]? = some (enc c)) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r (n + 1)
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
          (captured e leftSym R rate enc c x)), b.z = a.z ∧ b.score = a.score := by
  cases a with
  | «macro» a =>
    obtain ⟨v, hv, ht, _, _, hf, hvt⟩ := capture_enqueue hcode (hc a.z).mark_blank
      leftSym R rate enc c (hc a.z).mark_text hn x a.u [verifyLoop rate] a.valid hz hfirst hc0
    let b : Macro e leftSym R rate Text leftPat rightPat p r (n + 1)
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
          (captured e leftSym R rate enc c x)) :=
      { n₀ := a.n₀, x₀ := a.x₀, u₀ := a.u₀, z := a.z, u := v
        events := a.events, waits := a.waits
        frontier := a.frontier.trans (Nat.le_succ _), origin := a.origin, start := a.start
        valid := hv, follows := by simpa using a.follows.trans ht
        wait_le := a.wait_le
        credit := by simpa only [hf, readyCredit, hvt] using a.credit }
    exact ⟨.macro b, rfl, rfl⟩
  | entry a =>
    obtain ⟨v, hv, hi, hd, _⟩ := a.valid.arrival hcode (hc a.z).mark_blank leftSym R rate enc c
      (hc a.z).mark_text hn x a.u a.rank_le hz hfirst hc0
    let b : Entry e leftSym R rate Text leftPat rightPat p r (n + 1)
        (TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate
          (captured e leftSym R rate enc c x)) :=
      { n₀ := a.n₀, x₀ := a.x₀, u₀ := a.u₀, z := a.z, u := v, rank := a.rank
        positive := a.positive, rank_le := a.rank_le, paid := a.paid
        frontier := a.frontier.trans (Nat.le_succ _), origin := a.origin, feed := a.feed
        ghost := a.ghost, wf := a.wf, direction := a.direction, valid := hv
        ideal := hi.trans a.ideal, dir := hd.trans a.dir }
    exact ⟨.entry b, rfl, rfl⟩

theorem State.workers {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate N : ℕ) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (hn : n ≤ Text.length)
    (hz : ∀ j < N,
      ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[j] x).1.1.1 ≠ 0) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r n
        ((TextFeedPipelineControl.run (Terminal := Terminal) e leftSym R rate)^[N] x),
      Trace e leftSym R rate enc Text leftPat rightPat p r a (List.replicate N none) b ∧
      min (a.score + N) (target rate rightPat n) ≤ b.score := by
  induction N generalizing x with
  | zero => exact ⟨a, .refl a, by simp⟩
  | succ N ih =>
    obtain ⟨b, hab, hb⟩ := a.worker hcode leftSym R rate hc hpat hn (hz 0 (by omega))
    obtain ⟨d, hbd, hd⟩ := ih b (by
      intro j hj
      simpa only [Function.iterate_succ_apply] using hz (j + 1) (by omega))
    rw [Function.iterate_succ_apply]
    refine ⟨d, ?_, ?_⟩
    · simpa only [List.replicate_succ, List.singleton_append] using
        (Trace.worker (x := x) (by simpa only [Function.iterate_zero_apply] using hz 0 (by omega)) hab).trans hbd
    · omega

/-- One actual input round restores service credit at its new frontier.
No completion, no-wait, or empty-reentry assumption is hidden here. -/
theorem State.frame {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k) (c : Terminal)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (hn : n < Text.length)
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false) (hc0 : Text[n]? = some (enc c))
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r (n + 1)
      (frame e leftSym R rate enc c x), Trace e leftSym R rate enc Text leftPat rightPat p r a
        (some c :: List.replicate R none) b ∧
        target rate rightPat (n + 1) ≤ b.score := by
  obtain ⟨b, hzb, hb⟩ := a.arrival hcode leftSym R rate enc c hc hn hz hfirst hc0
  obtain ⟨d, hbd, hd⟩ := b.workers hcode leftSym R rate R enc hc hpat (by omega) (by
    intro j hj heq
    have he := run_enqueues_once (Terminal := Terminal) e leftSym R rate (j + 1) (by omega)
      (captured e leftSym R rate enc c x) hz
    simp only [Function.iterate_succ_apply, choose_enqueues] at he
    simp at he
    exact he heq)
  have ht : target rate rightPat (n + 1) ≤ target rate rightPat n + R := by
    simp only [target, Nat.mul_add, Nat.mul_one]
    simp only [Nat.mul_add, Nat.mul_one] at hR
    omega
  refine ⟨d, (Trace.arrival c hz hzb).trans hbd, ?_⟩
  have hg : target rate rightPat (n + 1) ≤ b.score + R := by omega
  rwa [Nat.min_eq_right hg] at hd

/-- Uniform real-time service on every prefix of the actual input word. -/
theorem State.frames {e : Env k} (hcode : Function.Injective e.code)
    (leftSym : Fin k) (R rate : ℕ) (enc : Terminal → Fin k)
    {Text leftPat rightPat : List (Fin k)} {p r n : ℕ} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x)
    (hc : ∀ z, Conditions e Text leftPat rightPat rate p r z)
    (hpat : 0 < rightPat.length) (as : List Terminal) (hn : n + as.length ≤ Text.length)
    (has : ∀ j c, as[j]? = some c → Text[n + j]? = some (enc c))
    (hz : x.1.1.1 = 0) (hfirst : x.1.1.2.1 = false)
    (hR : progressRate rate * (rate + 1) ≤ R) (ha : target rate rightPat n ≤ a.score) :
    ∃ b : State e leftSym R rate Text leftPat rightPat p r (n + as.length)
      (frames e leftSym R rate enc as x), Trace e leftSym R rate enc Text leftPat rightPat p r a (schedule R as) b ∧
        target rate rightPat (n + as.length) ≤ b.score := by
  induction as generalizing n x with
  | nil => exact ⟨a, .refl a, ha⟩
  | cons c cs ih =>
    have hn' : n < Text.length := by simp only [List.length_cons] at hn; omega
    obtain ⟨b, hab, hb⟩ := a.frame hcode leftSym R rate enc c hc hpat hn' hz hfirst
      (by simpa using has 0 c rfl) hR ha
    obtain ⟨d, hbd, hd⟩ := ih b (by simp only [List.length_cons] at hn; omega) (by
      intro j d hd
      have hh := has (j + 1) d (by simpa using hd)
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hh)
      (frame_clock leftSym R rate enc c x hz)
      (frame_not_first leftSym R rate enc c x hfirst) hb
    have heq : n + 1 + cs.length = n + (cs.length + 1) := by omega
    simp only [List.length_cons]
    rw [← heq]
    exact ⟨d, hab.trans hbd, hd⟩

/-- info: 'PalPeg.TextFeedPipelineService.State.frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms State.frames

theorem State.fits {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x) :
    a.z.1.pos + a.z.1.q ≤ n ∧ a.z.1.q ≤ rightPat.length := by
  cases a with
  | «macro» a =>
    have hh := a.start.feed.hd1.trans a.start.feed.m1le
    have hq := a.start.feed.qle
    simp only [a.start.ghost] at hh hq
    exact ⟨hh.trans a.frontier, hq⟩
  | entry a =>
    have hh := a.feed.hd1.trans a.feed.m1le
    have hq := a.feed.qle
    simp only [a.ghost] at hh hq
    exact ⟨hh.trans a.frontier, hq⟩

theorem State.valid {e : Env k} {leftSym : Fin k} {R rate p r n : ℕ}
    {Text leftPat rightPat : List (Fin k)} {x : Config e leftSym R rate}
    (a : State e leftSym R rate Text leftPat rightPat p r n x) :
    ∃ u caller, Valid e leftSym R rate Text n x u caller := by
  cases a with
  | «macro» a => exact ⟨a.u, _, a.valid⟩
  | entry a => exact ⟨a.u, _, a.valid.1⟩

theorem Trace.frontier {e : Env k} {leftSym : Fin k} {R rate p r n₀ n₁ : ℕ}
    {enc : Terminal → Fin k} {Text leftPat rightPat : List (Fin k)}
    {x₀ x₁ : Config e leftSym R rate} {ops : List (Option Terminal)}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b) : n₀ ≤ n₁ := by
  induction h with
  | refl | worker | arrival => omega
  | trans _ _ ih ih' => omega

theorem Trace.time_le {e : Env k} {leftSym : Fin k} {R rate p r n₀ n₁ : ℕ}
    {enc : Terminal → Fin k} {Text leftPat rightPat : List (Fin k)}
    {x₀ x₁ : Config e leftSym R rate} {ops : List (Option Terminal)}
    {a : State e leftSym R rate Text leftPat rightPat p r n₀ x₀}
    {b : State e leftSym R rate Text leftPat rightPat p r n₁ x₁}
    (h : Trace e leftSym R rate enc Text leftPat rightPat p r a ops b) : n₁ ≤ n₀ + ops.length := by
  induction h with
  | refl | worker | arrival => simp
  | trans _ _ ih ih' => simp only [List.length_append]; omega

end PalPeg.TextFeedPipelineService
