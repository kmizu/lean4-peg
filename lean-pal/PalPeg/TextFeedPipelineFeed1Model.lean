import PalPeg.TextFeedPipelineFeed2
import PalPeg.TextFeedPrefixFinish

/-! The tape-only Q1 guard implements the verifier's count-indexed
specification; the physical controller never reads that ghost count. -/
set_option autoImplicit false

namespace PalPeg.TextFeedPipelineFeed1Model
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.TextFeedControl
open PalPeg.RTQueue PalPeg.TextFeed PalPeg.VerifierFeed
open PalPeg.TextFeedPipelineVerifier

variable {k : ℕ}

theorem scan_inv {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ} {M : VMachine' k}
    (h : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    FeedInv' e.blank e.startSym e.endSym e.mark v Text d p r n (toM M) :=
  ⟨h.scan, h.buf1, h.qinv1, h.qlist1, h.m1le, h.hd1, h.qle⟩

theorem supply_blank {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ} {M : VMachine' k}
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (h : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M)
    (hb : ((prefixModel M).S GSTapes.tT).focus = e.blank) :
    TextFeedPrefixAtomic.effect e .supply (prefixModel M) =
      prefixModel (vfillIf1' e.blank e.mark n M) := by
  have hf := scan_inv h
  have hpos : M.z.1.pos + M.z.1.q = M.m1 := (TextFeedProg2.read_tT_blank_iff hblank hn hf).mp hb
  by_cases hlt : M.m1 < n
  · have hne := (TextFeedProg2.head_ne_mark_iff hmark hn hf).mpr hlt
    rw [head?_eq hf.qinv] at hne
    have he := TextFeedPrefixFinish.supply_data (toM M) M.vt.2.U hf.qinv hf.buf hne
    rw [vfillIf1', if_pos ⟨hpos, hlt⟩]
    exact he
  · have heq : (toList M.Q1).head?.getD e.mark = e.mark := by
      by_contra hh
      rw [← head?_eq h.qinv1] at hh
      exact hlt ((TextFeedProg2.head_ne_mark_iff hmark hn hf).mp hh)
    rw [vfillIf1', if_neg (by intro hh; exact hlt hh.2)]
    simp only [TextFeedPrefixAtomic.effect, prefixModel, TextFeedAtomic.supplyEffect, heq, if_true]

theorem skip_present {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ} {M : VMachine' k}
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    (h : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M)
    (hb : ((prefixModel M).S GSTapes.tT).focus ≠ e.blank) :
    vfillIf1' e.blank e.mark n M = M := by
  have hf := scan_inv h
  have he : M.z.1.pos + M.z.1.q ≠ M.m1 := by
    intro hh
    exact hb ((TextFeedProg2.read_tT_blank_iff hblank hn hf).mpr hh)
  exact if_neg (by intro hh; exact he hh.1)

theorem both_feedInv {e : Env k} {u v Text : List (Fin k)} {d p r n : ℕ} {M : VMachine' k}
    (hmb : e.mark ≠ e.blank) (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text) (hn : n ≤ Text.length)
    (h : VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M) :
    let M' := vfillHead2 e.blank e.mark (vfillIf1' e.blank e.mark n M)
    VFeedInv' e.blank e.startSym e.endSym e.mark u v Text d p r n M' ∧
      Ok2 n M' (M'.z.1.pos - u.length + M'.z.2) :=
  vfillHead2_feedInv hmb hblank hmark hn (vfillIf1'_feedInv hmb hn h)

/-- info: 'PalPeg.TextFeedPipelineFeed1Model.supply_blank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms supply_blank

/-- info: 'PalPeg.TextFeedPipelineFeed1Model.both_feedInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms both_feedInv

end PalPeg.TextFeedPipelineFeed1Model
