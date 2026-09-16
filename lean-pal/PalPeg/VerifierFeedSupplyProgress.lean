import PalPeg.VerifierFeedRaw
import PalPeg.VerifierFeedRawPrimitive

/-! Supply accounting using the two currently readable text cells.
Historical write counts are retained only for reentry monotonicity. -/
set_option autoImplicit false

namespace PalPeg.VerifierFeedSupplyProgress
open PegSeparation.RealTimeTM PalPeg.TextFeedControl PalPeg.VerifierFeed PalPeg.VerifierFeedRaw
variable {k : ℕ}

def filled (M : VMachine' k) : ℕ := M.m1 + M.m2

theorem fill1_mono (blank mark : Fin k) (M : VMachine' k) :
    filled M ≤ filled (fill1 blank mark M) := by
  unfold fill1
  split_ifs <;> simp [filled, vfill1']

theorem fill2_mono (blank mark : Fin k) (M : VMachine' k) :
    filled M ≤ filled (vfillHead2 blank mark M) := by
  unfold vfillHead2
  split_ifs <;> simp [filled]

theorem effect_mono (e : Env k) (a : GSVProg.Act10) (M : VMachine' k) :
    filled M ≤ filled (VerifierFeedPrimitive.effect e a M) := by
  unfold VerifierFeedPrimitive.effect
  split_ifs
  · exact fill2_mono e.blank e.mark (vmoveXR e.blank M)
  · exact fill2_mono e.blank e.mark M
  · exact Nat.le_refl _

/-- Only the two cells currently under the text heads can pay for a
future supply. This credit is at most two, independently of input size. -/
def readyCell (blank : Fin k) (tp : TapeConfiguration k) : ℕ :=
  if Tape.read tp = blank then 0 else 1

def readyCredit (blank : Fin k) (M : VMachine' k) : ℕ :=
  readyCell blank (M.vt.1 GSTapes.tT) + readyCell blank M.vt.2.Txt2

theorem readyCell_le (blank : Fin k) (tp : TapeConfiguration k) : readyCell blank tp ≤ 1 := by
  unfold readyCell; split <;> omega

theorem readyCredit_le (blank : Fin k) (M : VMachine' k) : readyCredit blank M ≤ 2 := by
  have h1 := readyCell_le blank (M.vt.1 GSTapes.tT)
  have h2 := readyCell_le blank M.vt.2.Txt2
  unfold readyCredit
  omega

theorem fill1_ready_mono (blank mark : Fin k) (M : VMachine' k) :
    readyCredit blank M ≤ readyCredit blank (fill1 blank mark M) := by
  unfold fill1
  split_ifs with h
  · have hz : readyCell blank (M.vt.1 GSTapes.tT) = 0 := if_pos h.1
    unfold readyCredit
    rw [hz, Nat.zero_add]
    change readyCell blank M.vt.2.Txt2 ≤
      readyCell blank ((vfill1' blank mark M).vt.1 GSTapes.tT) + readyCell blank M.vt.2.Txt2
    exact Nat.le_add_left _ _
  · exact Nat.le_refl _

theorem fill2_ready_mono (blank mark : Fin k) (M : VMachine' k) :
    readyCredit blank M ≤ readyCredit blank (vfillHead2 blank mark M) := by
  unfold vfillHead2
  split_ifs with h
  · have he : M.vt.2.Txt2.focus = blank := h.1
    simp [readyCredit, readyCell, Tape.read_eq_focus, he]
  · exact Nat.le_refl _

/-- One verifier instruction changes at most one text cell. -/
theorem effect_ready_bound (e : Env k) (a : GSVProg.Act10) (M : VMachine' k) :
    readyCredit e.blank M ≤ 1 + readyCredit e.blank (VerifierFeedPrimitive.effect e a M) := by
  unfold VerifierFeedPrimitive.effect
  split_ifs
  · have hm := fill2_ready_mono e.blank e.mark (vmoveXR e.blank M)
    have hcell := readyCell_le e.blank M.vt.2.Txt2
    change readyCredit e.blank M ≤ 1 + readyCredit e.blank (vfillHead2 e.blank e.mark (vmoveXR e.blank M))
    have hb : readyCredit e.blank M ≤ 1 + readyCredit e.blank (vmoveXR e.blank M) := by
      unfold readyCredit vmoveXR
      dsimp only
      omega
    omega
  · have hm := fill2_ready_mono e.blank e.mark M
    omega
  · have h1 := VerifierFeedRawPrimitive.primitive_at e a M (GSVProg.e8 GSTapes.tT)
    have h2 := VerifierFeedRawPrimitive.primitive_at e a M GSVProg.tX
    simp only [VerifierFeedRawPrimitive.rawTape_e8, VerifierFeedRawPrimitive.rawTape_X] at h1 h2
    by_cases h : a.1 = GSVProg.e8 GSTapes.tT
    · have hx : a.1 ≠ GSVProg.tX := by rw [h]; decide
      rw [if_neg hx] at h2
      unfold readyCredit
      rw [h2]
      have hb := readyCell_le e.blank (M.vt.1 GSTapes.tT)
      omega
    · rw [if_neg h] at h1
      unfold readyCredit
      rw [h1]
      have hb := readyCell_le e.blank M.vt.2.Txt2
      omega

theorem fill1_ready_grow {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ} {M : VMachine' k}
    (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text) (hn : n ≤ Text.length)
    (h : Txt1Inv blank mark Text n M i) (hc : Tape.read (M.vt.1 GSTapes.tT) = blank)
    (hi : i < n) : readyCredit blank (fill1 blank mark M) = readyCredit blank M + 1 := by
  obtain ⟨hf, hok⟩ := fill1_inv hmb hb hm hn h
  have hlt : i < (fill1 blank mark M).m1 := by rcases hok with hh | hh <;> omega
  have hnb : Tape.read ((fill1 blank mark M).vt.1 GSTapes.tT) ≠ blank := by
    intro hh
    have he := (read1_blank_iff hb hn hf).mp hh
    omega
  have hsame : (fill1 blank mark M).vt.2.Txt2 = M.vt.2.Txt2 := by
    unfold fill1; split <;> rfl
  simp only [readyCredit, readyCell, if_pos hc, if_neg hnb, hsame]
  omega

theorem fill2_ready_grow {blank mark : Fin k} {Text : List (Fin k)} {n i : ℕ} {M : VMachine' k}
    (hmb : mark ≠ blank) (hb : blank ∉ Text) (hm : mark ∉ Text) (hn : n ≤ Text.length)
    (h : Txt2Inv blank mark Text n M i) (hc : Tape.read M.vt.2.Txt2 = blank)
    (hi : i < n) : readyCredit blank (vfillHead2 blank mark M) = readyCredit blank M + 1 := by
  obtain ⟨hf, hok⟩ := vfillHead2_inv hmb hb hm hn h
  have hlt : i < (vfillHead2 blank mark M).m2 := by rcases hok with hh | hh <;> omega
  have hnb : Tape.read (vfillHead2 blank mark M).vt.2.Txt2 ≠ blank := by
    intro hh
    have he := (read_Txt2_blank_iff hb hn hf).mp hh
    omega
  simp only [readyCredit, readyCell, if_pos hc, if_neg hnb, vfillHead2_vt1]

/-- info: 'PalPeg.VerifierFeedSupplyProgress.effect_ready_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms effect_ready_bound

end PalPeg.VerifierFeedSupplyProgress
