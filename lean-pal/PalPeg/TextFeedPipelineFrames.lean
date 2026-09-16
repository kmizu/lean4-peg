import PalPeg.TextFeedPipelineBranch

/-! Typed residual frames for the actual verifier compiler. A loop commit
keeps its mandatory instruction pending; wait frames keep their barrier. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFrames
open PegSeparation.RealTimeTM PalPeg.ProgLang PalPeg.TextFeedPipelineControl
open PalPeg.TextFeedPipelineBranch
abbrev A := GSVProg.Act10 ⊕ Bool
abbrev C := GSVProg.Cond10 ⊕ GSVProgZLoop.DCond

inductive Frame where
  | code (p : GSVProgZLoop.DProg)
  | pending (a : A)
  | after (a : A)
  | test (c : C) (p q : GSVProgZLoop.DProg)
  | cycle (c : C) (a : A) (b : GSVProgZLoop.DProg)
  | body (c : C) (a : A) (b : GSVProgZLoop.DProg)
  | bodyRest (c : C) (a : A) (b : GSVProgZLoop.DProg)
  | skip

def loopCore {k : ℕ} (c : C) (a : A) (b : GSVProgZLoop.DProg) : Task k :=
  .loop (verifyCond c) (.inr (.inl .idle))
    (.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c)))

def renderFrame {k : ℕ} : Frame → Stack (TaskAct k) (TaskCond k)
  | .code p => [liftVerify p]
  | .pending a => [beforeVerify a, .seq (.act (.inr (.inr a))) (afterVerify a)]
  | .after a => [afterVerify a]
  | .test c p q => [beforeCond c, .ite (verifyCond c) (liftVerify p) (liftVerify q)]
  | .cycle c a b => [beforeCond c, loopCore c a b]
  | .body c a b => [.seq (verifyAct a) (.seq (liftVerify b) (beforeCond c)), loopCore c a b]
  | .bodyRest c a b => [.seq (liftVerify b) (beforeCond c), loopCore c a b]
  | .skip => [.skip]

def render {k : ℕ} (fs : List Frame) : Stack (TaskAct k) (TaskCond k) := fs.flatMap renderFrame

def eraseFrame : Frame → Stack A C
  | .code p => [p]
  | .pending a => [.act a]
  | .after _ | .skip => []
  | .test c p q => [.ite c p q]
  | .cycle c a b => [.loop c a b]
  | .body c a b => [.act a, b, .loop c a b]
  | .bodyRest c a b => [b, .loop c a b]

def erase (fs : List Frame) : Stack A C := fs.flatMap eraseFrame

inductive Event where
  | instruction (a : A)
  | feed1 | feed2 | idle | halt

def label {k : ℕ} : Event → Option (TaskAct k)
  | .instruction a => some (.inr (.inr a))
  | .feed1 => some (.inr (.inl .supply))
  | .feed2 => some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))
  | .idle => some (.inr (.inl .idle))
  | .halt => none

def preWait {k : ℕ} (ev : TaskCond k → Bool) : A → Option Event
  | .inr _ => none
  | .inl a =>
    if a.2.2 = .right then
      if a.1 = GSVProg.e8 GSTapes.tT then
        if ev (.inr (.inl .blankText)) then some .feed1 else none
      else if a.1 = GSVProg.tX then
        if ev (.inr (.inr (.inr .blankX))) then some .feed2 else none
      else none
    else none

def condEvent : C → Event
  | .inl .matchOk => .feed1
  | .inl .compOk => .feed2
  | _ => .idle

def postWait {k : ℕ} (ev : TaskCond k → Bool) : A → Bool
  | .inr _ => false
  | .inl a => decide (a.1 = GSVProg.e8 GSTapes.tT ∧ a.2.2 = .right) && ev (.inr (.inl .blankText))

def codeWeight : GSVProgZLoop.DProg → ℕ
  | .skip => 1
  | .act _ => 5
  | .seq p q => codeWeight p + codeWeight q + 1
  | .ite _ p q => codeWeight p + codeWeight q + 3
  | .loop _ _ b => codeWeight b + 4

def frameWeight : Frame → ℕ
  | .code p => codeWeight p
  | .pending _ => 4
  | .after _ | .skip => 1
  | .test _ p q => codeWeight p + codeWeight q + 2
  | .cycle _ _ b => codeWeight b + 3
  | .body _ _ b => 2 * codeWeight b + 10
  | .bodyRest _ _ b => 2 * codeWeight b + 4

def weight (fs : List Frame) : ℕ := (fs.map frameWeight).sum

def next {k : ℕ} (ev : TaskCond k → Bool) : List Frame → List Frame × Event
  | [] => ([], .halt)
  | .skip :: fs => next ev fs
  | .code .skip :: fs => next ev fs
  | .code (.act a) :: fs => next ev (.pending a :: fs)
  | .code (.seq p q) :: fs => next ev (.code p :: .code q :: fs)
  | .code (.ite c p q) :: fs => next ev (.test c p q :: fs)
  | .code (.loop c a b) :: fs => next ev (.cycle c a b :: fs)
  | .pending a :: fs =>
    match preWait ev a with
    | some w => (.skip :: .pending a :: fs, w)
    | none => (.after a :: fs, .instruction a)
  | .after a :: fs => if postWait ev a then (fs, .feed1) else next ev fs
  | .test c p q :: fs =>
    if Waiting ev c then (.skip :: .test c p q :: fs, condEvent c)
    else next ev (.code (if ev (verifyCond c) then p else q) :: fs)
  | .cycle c a b :: fs =>
    if Waiting ev c then (.skip :: .cycle c a b :: fs, condEvent c)
    else if ev (verifyCond c) then (.body c a b :: fs, .idle) else next ev fs
  | .body c a b :: fs => next ev (.code (.act a) :: .bodyRest c a b :: fs)
  | .bodyRest c a b :: fs => next ev (.code b :: .cycle c a b :: fs)
termination_by fs => weight fs
decreasing_by
  all_goals simp_all [weight, frameWeight, codeWeight]
  all_goals first | omega | (split <;> omega)

theorem pending_step {k : ℕ} (ev : TaskCond k → Bool) (a : A)
    (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (beforeVerify a :: .seq (.act (.inr (.inr a))) (afterVerify a) :: s) =
      match preWait ev a with
      | some w => (.skip :: renderFrame (.pending a) ++ s, label w)
      | none => (afterVerify a :: s, some (.inr (.inr a))) := by
  cases a with
  | inr up => simp [preWait, beforeVerify]
  | inl a =>
    by_cases hr : a.2.2 = .right
    · by_cases ht : a.1 = GSVProg.e8 GSTapes.tT
      · cases he : ev (.inr (.inl .blankText)) <;>
          simp [renderFrame, preWait, beforeVerify, hr, ht, he, waitText1, label]
      · by_cases hx : a.1 = GSVProg.tX
        · have hn : GSVProg.tX ≠ GSVProg.e8 GSTapes.tT := fun h => ht (hx.trans h)
          cases he : ev (.inr (.inr (.inr .blankX))) <;>
            simp [renderFrame, preWait, beforeVerify, hr, hx, hn, he, waitText2, label]
        · simp [preWait, beforeVerify, hr, ht, hx]
    · simp [preWait, beforeVerify, hr]

theorem after_step {k : ℕ} (ev : TaskCond k → Bool) (a : A)
    (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (afterVerify a :: s) =
      if postWait ev a then (s, label .feed1) else stepStack ev s := by
  cases a with
  | inr up => simp [afterVerify, postWait]
  | inl a =>
    by_cases ht : a.1 = GSVProg.e8 GSTapes.tT ∧ a.2.2 = .right
    · cases he : ev (.inr (.inl .blankText)) <;> simp [afterVerify, postWait, ht, he, feedHead, label]
    · simp [afterVerify, postWait, ht]

theorem cond_step {k : ℕ} (ev : TaskCond k → Bool) (c : C)
    (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (beforeCond c :: s) =
      if Waiting ev c then (.skip :: beforeCond c :: s, label (condEvent c)) else stepStack ev s := by
  cases c with
  | inl c => cases c <;> simp [Waiting, beforeCond, condEvent, label]
  | inr c => cases c <;> simp [Waiting, beforeCond]

/-- The typed evaluator is the real compiler's source dispatch, including
its exact stack representation and its actual (possibly feed) label. -/
theorem next_render {k : ℕ} (ev : TaskCond k → Bool) (fs : List Frame) :
    stepStack ev (render fs) = (render (next ev fs).1, label (next ev fs).2) := by
  induction fs using next.induct (ev := ev) <;>
    simp_all [next, render, renderFrame, liftVerify, verifyAct, loopCore, label,
      after_step, cond_step]
  case case8 a fs w h =>
    simpa [h, render, renderFrame, label] using pending_step ev a (render fs)
  case case9 a fs h =>
    simpa [h, render, label] using pending_step ev a (render fs)
  case case13 c p q fs h ih =>
    split at ih <;> simp_all

def destination (ev : Event) (fs : List Frame) : Stack A C :=
  match ev with
  | .instruction a => .act a :: erase fs
  | _ => erase fs

theorem preWait_stutters {k : ℕ} (ev : TaskCond k → Bool) (a : A) (w : Event)
    (h : preWait ev a = some w) (fs : List Frame) : destination w fs = erase fs := by
  cases a with
  | inr up => simp [preWait] at h
  | inl a =>
    simp only [preWait] at h
    split_ifs at h <;> cases h <;> rfl

theorem condEvent_stutters (c : C) (fs : List Frame) : destination (condEvent c) fs = erase fs := by
  cases c with
  | inl c => cases c <;> rfl
  | inr c => cases c <;> rfl

/-- Under ready-guard agreement, every actual compiled dispatch either
selects the same pending ideal instruction or advances only ideal control.
This covers all residual frames, not just a fresh top-level program. -/
theorem next_erase {k : ℕ} (ev : TaskCond k → Bool) (ideal : C → Bool)
    (compatible : ∀ c, Waiting ev c = false → ev (verifyCond c) = ideal c)
    (fs : List Frame) :
    ProgLangControlSteps.Star ideal (erase fs) (destination (next ev fs).2 (next ev fs).1) := by
  induction fs using next.induct (ev := ev) with
  | case1 => simp only [next]; exact .refl _
  | case2 fs ih => simpa [next, erase, eraseFrame] using ih
  | case3 fs ih =>
    simpa [next, erase, eraseFrame] using
      ProgLangControlSteps.Star.cons (.skip (erase fs)) ih
  | case4 a fs ih => simpa [next, erase, eraseFrame] using ih
  | case5 p q fs ih =>
    simpa [next, erase, eraseFrame] using
      ProgLangControlSteps.Star.cons (.seq p q (erase fs)) ih
  | case6 c p q fs ih => simpa [next, erase, eraseFrame] using ih
  | case7 c a b fs ih => simpa [next, erase, eraseFrame] using ih
  | case8 a fs w h =>
    simpa [next, h, preWait_stutters ev a w h, erase, eraseFrame] using
      (ProgLangControlSteps.Star.refl (ev := ideal) (erase (.pending a :: fs)))
  | case9 a fs h =>
    simp only [next, h]
    exact .refl _
  | case10 a fs h =>
    simp only [next, h, if_true]
    exact .refl _
  | case11 a fs h ih => simpa [next, h, erase, eraseFrame] using ih
  | case12 c p q fs h =>
    simp only [next, h, if_true, condEvent_stutters]
    exact .refl _
  | case13 c p q fs h ih =>
    have he := compatible c (Bool.eq_false_iff.mpr h)
    rw [next, if_neg h]
    apply ProgLangControlSteps.Star.cons (.branch c p q (erase fs))
    rw [← he]
    by_cases ht : ev (verifyCond c) = true <;>
      simpa [erase, eraseFrame, ht] using ih
  | case14 c a b fs h =>
    simp only [next, h, if_true, condEvent_stutters]
    exact .refl _
  | case15 c a b fs h hc =>
    have hi : ideal c = true := (compatible c (Bool.eq_false_iff.mpr h)).symm.trans hc
    simpa [next, h, hc, destination, erase, eraseFrame] using
      ProgLangControlSteps.Star.single (.loop_yes c a b (erase fs) hi)
  | case16 c a b fs h hc ih =>
    have hi : ideal c = false := (compatible c (Bool.eq_false_iff.mpr h)).symm.trans (Bool.eq_false_iff.mpr hc)
    simpa [next, h, hc, erase, eraseFrame] using
      ProgLangControlSteps.Star.cons (.loop_no c a b (erase fs) hi) ih
  | case17 c a b fs ih => simpa [next, erase, eraseFrame] using ih
  | case18 c a b fs ih => simpa [next, erase, eraseFrame] using ih

def runFrames {k : ℕ} : List (TaskCond k → Bool) → List Frame → List Frame × List Event
  | [], fs => (fs, [])
  | ev :: es, fs =>
    let z := next ev fs
    let u := runFrames es z.1
    (u.1, z.2 :: u.2)

theorem observe_render {k : ℕ} (es : List (TaskCond k → Bool)) (fs : List Frame) :
    ProgLangWait.observe es (render fs) =
      (render (runFrames es fs).1, (runFrames es fs).2.map label) := by
  induction es generalizing fs with
  | nil => rfl
  | cons ev es ih =>
    simp only [ProgLangWait.observe_cons, next_render, runFrames, ih, List.map_cons]

/-- Arbitrary caller continuations are retained. If the framed verifier
returns without an action, the same source call continues in the caller. -/
theorem next_render_suffix {k : ℕ} (ev : TaskCond k → Bool) (fs : List Frame)
    (s : Stack (TaskAct k) (TaskCond k)) :
    stepStack ev (render fs ++ s) =
      match (next ev fs).2 with
      | .halt => stepStack ev s
      | w => (render (next ev fs).1 ++ s, label w) := by
  rcases he : next ev fs with ⟨gs, w⟩
  have hs := next_render ev fs
  rw [he] at hs
  cases w <;> simp only [label] at hs ⊢
  all_goals first
    | exact ProgLangControlSteps.dispatch_append ev (render fs) (render gs) s _ hs
    | exact ((ProgLangControlSteps.halted_path ev (render fs) (congrArg Prod.snd hs)).append s).dispatch

/-- info: 'PalPeg.TextFeedPipelineFrames.next_render' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_render

/-- info: 'PalPeg.TextFeedPipelineFrames.next_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_erase

end PalPeg.TextFeedPipelineFrames
