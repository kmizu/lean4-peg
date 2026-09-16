import PalPeg.TextFeedPipelineBranch
import PalPeg.ProgLangWait

/-! Exact pending-instruction traces in the compiled source, including
arbitrarily many intervening observations and the actual after-feed suffix. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineActionWait
open PalPeg.ProgLang PalPeg.ProgLangWait PalPeg.TextFeedPipelineControl
variable {k : ℕ}

theorem pending_release (a : GSVProg.Act10 ⊕ Bool)
    (c : TaskCond k) (w : TaskAct k)
    (hbefore : beforeVerify a = .loop c w .skip)
    (s : Stack (TaskAct k) (TaskCond k))
    (xs : List (TaskCond k → Bool)) (last : TaskCond k → Bool)
    (hw : ∀ ev ∈ xs, ev c = true) (hl : last c = false) :
    observe (xs ++ [last]) (verifyAct a :: s) =
      (afterVerify a :: s, List.replicate xs.length (some w) ++ [some (.inr (.inr a))]) := by
  have he : ∀ ev, stepStack ev (verifyAct a :: s) =
      stepStack ev (.loop c w .skip :: .seq (.act (.inr (.inr a))) (afterVerify a) :: s) := by
    intro ev
    rw [verifyAct, stepStack_seq, hbefore]
  rw [observe_nonempty_congr he (xs ++ [last]) (by simp)]
  simpa only [stepStack_seq, stepStack_act] using
    wait_release_to c w (.seq (.act (.inr (.inr a))) (afterVerify a) :: s) xs last hw hl

theorem text1_release (a : GSVProg.Act10)
    (ht : a.1 = GSVProg.e8 GSTapes.tT) (hr : a.2.2 = .right)
    (s : Stack (TaskAct k) (TaskCond k))
    (xs : List (TaskCond k → Bool)) (last : TaskCond k → Bool)
    (hw : ∀ ev ∈ xs, ev (.inr (.inl .blankText)) = true)
    (hl : last (.inr (.inl .blankText)) = false) :
    observe (xs ++ [last]) (verifyAct (.inl a) :: s) =
      (feedHead :: s, List.replicate xs.length (some (.inr (.inl .supply))) ++
        [some (.inr (.inr (.inl a)))]) := by
  have hb : beforeVerify (k := k) (.inl a) = waitText1 := by
    simp [beforeVerify, hr, ht]
  have h := pending_release (.inl a) (.inr (.inl .blankText)) (.inr (.inl .supply))
    hb s xs last hw hl
  simpa only [afterVerify, ht, hr, and_self, ↓reduceIte] using h

theorem text2_release (a : GSVProg.Act10)
    (ht : a.1 = GSVProg.tX) (hr : a.2.2 = .right)
    (s : Stack (TaskAct k) (TaskCond k))
    (xs : List (TaskCond k → Bool)) (last : TaskCond k → Bool)
    (hw : ∀ ev ∈ xs, ev (.inr (.inr (.inr .blankX))) = true)
    (hl : last (.inr (.inr (.inr .blankX))) = false) :
    observe (xs ++ [last]) (verifyAct (.inl a) :: s) =
      (.skip :: s, List.replicate xs.length
        (some (.inr (.inr (.inl (GSVProg.tX, true, .stay))))) ++
        [some (.inr (.inr (.inl a)))]) := by
  have hne : a.1 ≠ GSVProg.e8 GSTapes.tT := by
    intro he
    exact GSVProg.e8_ne_tX GSTapes.tT (he.symm.trans ht)
  have hb : beforeVerify (k := k) (.inl a) = waitText2 := by
    simp only [beforeVerify, if_pos hr, if_neg hne, if_pos ht]
  have h := pending_release (.inl a) (.inr (.inr (.inr .blankX)))
    (.inr (.inr (.inl (GSVProg.tX, true, .stay)))) hb s xs last hw hl
  simpa only [afterVerify, hne, false_and, ↓reduceIte] using h

/-- info: 'PalPeg.TextFeedPipelineActionWait.text1_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms text1_release

/-- info: 'PalPeg.TextFeedPipelineActionWait.text2_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms text2_release

end PalPeg.TextFeedPipelineActionWait
