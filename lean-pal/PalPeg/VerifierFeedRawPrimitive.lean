import PalPeg.VerifierFeedRaw

/-! Instruction-level preservation of both feed frontiers. The head
indices here advance with the real tapes, independently of `M.z`. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedRawPrimitive
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.TextFeedControl PalPeg.TextFeed PalPeg.VerifierFeed PalPeg.VerifierFeedRaw
open PalPeg.VerifierFeedPrimitive

variable {k : ℕ}

def rawTape (vt : GSVTapes.VTapes' k) (j : Fin 10) : TapeConfiguration k :=
  fromS (GSVProg.vTS vt j)

@[simp] theorem rawTape_e8 (vt : GSVTapes.VTapes' k) (j : Fin 8) :
    rawTape vt (GSVProg.e8 j) = vt.1 j := by
  rw [rawTape, GSVProg.vTS_e8]
  rfl

@[simp] theorem rawTape_X (vt : GSVTapes.VTapes' k) : rawTape vt GSVProg.tX = vt.2.Txt2 := rfl

theorem fromS_action (blank : Fin k) (T : STape (Fin k)) (w : Fin k) (mv : Move) :
    fromS (T.applyAction blank (w, mv)) = Tape.step blank (fromS T) w mv := by
  obtain ⟨L, f, R⟩ := T
  cases mv <;> cases L <;> cases R <;> rfl

theorem primitive_at (e : Env k) (a : GSVProg.Act10) (M : VMachine' k) (j : Fin 10) :
    rawTape (primitive e a M).vt j =
      if a.1 = j then Tape.step e.blank (rawTape M.vt j)
        (if a.2.1 then (rawTape M.vt j).focus else e.blank) a.2.2
      else rawTape M.vt j := by
  unfold rawTape primitive
  rw [vTS_fromTapes]
  simp only [applyTrace_cons, applyTrace_nil, actVec, GSVProg.I10, GSVProg.actOf10, touchVec]
  by_cases hj : j = a.1
  · subst j
    simp only
    exact fromS_action e.blank _ _ _
  · simp only [if_neg hj, if_neg (Ne.symm hj), applyAction_focus_stay]

def moveIndex (mv : Move) (i : ℕ) : ℕ :=
  match mv with
  | .left => i - 1
  | .stay => i
  | .right => i + 1

def nextIndex (a : GSVProg.Act10) (j : Fin 10) (i : ℕ) : ℕ :=
  if a.1 = j then moveIndex a.2.2 i else i

/-- Text instructions preserve their symbols. A right move is enabled
only at an already filled cell; left-edge moves use the real saturation rule. -/
def SafeAt (a : GSVProg.Act10) (j : Fin 10) (i m : ℕ) : Prop :=
  a.1 = j → a.2.1 = true ∧ (a.2.2 = .right → i < m)

def Safe (a : GSVProg.Act10) (M : VMachine' k) (i₁ i₂ : ℕ) : Prop :=
  SafeAt a (GSVProg.e8 GSTapes.tT) i₁ M.m1 ∧ SafeAt a GSVProg.tX i₂ M.m2

theorem move_view {blank : Fin k} {Text : List (Fin k)} {tp : TapeConfiguration k}
    {m i : ℕ} (hm : m ≤ Text.length) (hi : i ≤ m)
    (h : Tape.SeqView blank tp (padW blank Text m) i) (mv : Move)
    (hr : mv = .right → i < m) :
    Tape.SeqView blank (Tape.step blank tp tp.focus mv) (padW blank Text m) (moveIndex mv i) ∧
      moveIndex mv i ≤ m := by
  cases mv with
  | stay => exact ⟨h, hi⟩
  | right =>
    have hr' := hr rfl
    exact ⟨Tape.seq_move_right h (by rw [padW_length hm]; omega), by dsimp [moveIndex]; omega⟩
  | left =>
    cases i with
    | zero => exact ⟨Tape.seq_move_left_edge h, Nat.zero_le _⟩
    | succ i => exact ⟨Tape.seq_move_left h, by dsimp [moveIndex]; omega⟩

theorem primitive_view {e : Env k} {Text : List (Fin k)} {m i : ℕ}
    {a : GSVProg.Act10} {j : Fin 10} {M : VMachine' k}
    (hm : m ≤ Text.length) (hi : i ≤ m)
    (h : Tape.SeqView e.blank (rawTape M.vt j) (padW e.blank Text m) i)
    (hs : SafeAt a j i m) :
    Tape.SeqView e.blank (rawTape (primitive e a M).vt j)
      (padW e.blank Text m) (nextIndex a j i) ∧ nextIndex a j i ≤ m := by
  rw [primitive_at]
  unfold nextIndex
  by_cases hj : a.1 = j
  · obtain ⟨hk, hr⟩ := hs hj
    simp only [if_pos hj, hk, ↓reduceIte]
    exact move_view hm hi h a.2.2 hr
  · simp only [if_neg hj]
    exact ⟨h, hi⟩

theorem raw_primitive {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {a : GSVProg.Act10} {M : VMachine' k} (hn : n ≤ Text.length)
    (h : RawInv e.blank e.mark Text n M i₁ i₂) (hs : Safe a M i₁ i₂) :
    RawInv e.blank e.mark Text n (primitive e a M)
      (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  have hv₁ : Tape.SeqView e.blank (rawTape M.vt (GSVProg.e8 GSTapes.tT))
      (padW e.blank Text M.m1) i₁ := by simpa only [rawTape_e8, channel1] using h.one.view
  have hv₂ : Tape.SeqView e.blank (rawTape M.vt GSVProg.tX)
      (padW e.blank Text M.m2) i₂ := h.two.view
  obtain ⟨hv₁', hi₁'⟩ := primitive_view (le_trans h.one.m2le hn) h.one.hle hv₁ hs.1
  obtain ⟨hv₂', hi₂'⟩ := primitive_view (le_trans h.two.m2le hn) h.two.hle hv₂ hs.2
  constructor
  · refine ⟨?_, h.one.buf, h.one.qinv, h.one.qlist, h.one.m2le, hi₁'⟩
    change Tape.SeqView e.blank ((primitive e a M).vt.1 GSTapes.tT)
      (padW e.blank Text M.m1) (nextIndex a (GSVProg.e8 GSTapes.tT) i₁)
    simpa only [rawTape_e8, channel1] using hv₁'
  · exact ⟨hv₂', h.two.buf, h.two.qinv, h.two.qlist, h.two.m2le, hi₂'⟩

theorem primitive_XR (e : Env k) (M : VMachine' k) :
    primitive e (GSVProg.tX, true, .right) M = vmoveXR e.blank M := by
  have ht : applyTrace e.blank (GSVProg.vTS M.vt)
      [actVec (GSVProg.I10 (Terminal := Unit) e.blank e.endSym e.mark e.startSym)
        (GSVProg.tX, true, .right) (GSVProg.vTS M.vt)] = GSVProg.vTS (vmoveXR e.blank M).vt := by
    funext j
    fin_cases j <;> try rfl
    change (RTQueueProg.toS M.vt.2.Txt2).applyAction e.blank (M.vt.2.Txt2.focus, .right) =
      RTQueueProg.toS (Tape.step e.blank M.vt.2.Txt2 M.vt.2.Txt2.focus .right)
    rw [RTQueueProg.toS_step]
  unfold primitive
  rw [ht, fromTapes_vTS]
  rfl

/-- This is the actual augmented instruction effect: XR includes its
post-move Q2 fill, while XS supplies Q2 without changing the head index. -/
theorem raw_effect {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {a : GSVProg.Act10} {M : VMachine' k} (hmb : e.mark ≠ e.blank)
    (hb : e.blank ∉ Text) (hm : e.mark ∉ Text) (hn : n ≤ Text.length)
    (h : RawInv e.blank e.mark Text n M i₁ i₂) (hs : Safe a M i₁ i₂) :
    RawInv e.blank e.mark Text n (effect e a M)
      (nextIndex a (GSVProg.e8 GSTapes.tT) i₁) (nextIndex a GSVProg.tX i₂) := by
  have hp := raw_primitive hn h hs
  unfold effect
  split_ifs with hxr hxs
  · change a = (GSVProg.tX, true, .right) at hxr
    subst a
    rw [primitive_XR] at hp
    exact (raw_fill2 hmb hb hm hn hp).1
  · change a = (GSVProg.tX, true, .stay) at hxs
    subst a
    have hi₁ : nextIndex (GSVProg.tX, true, .stay) (GSVProg.e8 GSTapes.tT) i₁ = i₁ := by
      simp only [nextIndex, moveIndex, ite_self]
    have hi₂ : nextIndex (GSVProg.tX, true, .stay) GSVProg.tX i₂ = i₂ := by
      simp only [nextIndex, moveIndex, ite_self]
    rw [hi₁, hi₂]
    exact (raw_fill2 hmb hb hm hn h).1
  · exact hp

/-- The two right-move safety obligations are decided by actual text
cells. Nontext writes and left/stationary text moves need no arrival oracle. -/
theorem safe_of_reads {e : Env k} {Text : List (Fin k)} {n i₁ i₂ : ℕ}
    {a : GSVProg.Act10} {M : VMachine' k} (hb : e.blank ∉ Text) (hn : n ≤ Text.length)
    (h : RawInv e.blank e.mark Text n M i₁ i₂)
    (hk₁ : a.1 = GSVProg.e8 GSTapes.tT → a.2.1 = true)
    (hk₂ : a.1 = GSVProg.tX → a.2.1 = true)
    (hr₁ : a.1 = GSVProg.e8 GSTapes.tT → a.2.2 = .right →
      Tape.read (M.vt.1 GSTapes.tT) ≠ e.blank)
    (hr₂ : a.1 = GSVProg.tX → a.2.2 = .right → Tape.read M.vt.2.Txt2 ≠ e.blank) :
    Safe a M i₁ i₂ := by
  constructor
  · intro hj
    refine ⟨hk₁ hj, ?_⟩
    intro hm
    have hne : i₁ ≠ M.m1 := fun he => hr₁ hj hm ((read1_blank_iff hb hn h.one).mpr he)
    have hle : i₁ ≤ M.m1 := h.one.hle
    omega
  · intro hj
    refine ⟨hk₂ hj, ?_⟩
    intro hm
    have hne : i₂ ≠ M.m2 := fun he => hr₂ hj hm ((read_Txt2_blank_iff hb hn h.two).mpr he)
    have hle := h.two.hle
    omega

/-- info: 'PalPeg.VerifierFeedRawPrimitive.raw_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_effect

/-- info: 'PalPeg.VerifierFeedRawPrimitive.safe_of_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms safe_of_reads

/-- info: 'PalPeg.VerifierFeedRawPrimitive.raw_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms raw_primitive

end PalPeg.VerifierFeedRawPrimitive
