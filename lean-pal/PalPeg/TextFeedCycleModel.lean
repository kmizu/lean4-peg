import PalPeg.TextFeedCycle

/-! Reference-model facts for the worker's supply and scan gates. In
particular, an arrival between supply and the gate may cause a harmless
extra wait: gate safety does not assume that no such arrival occurred. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedCycleModel
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang
open PalPeg.RTQueue PalPeg.RTQueueTapes PalPeg.RTQueueProg PalPeg.RTQueueClosed
open PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedAtomic
open PalPeg.TextFeedSchedule PalPeg.TextFeedScan PalPeg.TextFeedCycle PalPeg.GSProg

variable {k : ℕ}

def fillEffect (e : Env k) (q : Queue (Fin k)) (S : Stage k) : Queue (Fin k) × Stage k :=
  if (S GSTapes.tT).focus = e.blank then supplyEffect e q S else (q, S)

def GateEnabled (e : Env k) (S : Stage k) : Prop :=
  (S GSTapes.tP).focus = e.endSym ∨ (S GSTapes.tT).focus ≠ e.blank

/-- Tape-based supply has the same FIFO and scanner effect as fillIf' on
a valid reference state. The program never receives m, n, or st as inputs. -/
theorem fill_effect_matches {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M) :
    fillEffect e M.Q (TS M.ts) =
      ((TextFeed.fillIf' e.blank e.mark n M).Q, TS (TextFeed.fillIf' e.blank e.mark n M).ts) := by
  have hb : (TS M.ts GSTapes.tT).focus = e.blank ↔ M.st.pos + M.st.q = M.m :=
    TextFeedProg2.read_tT_blank_iff hblank hn hf
  have hh : (toList M.Q).head?.getD e.mark ≠ e.mark ↔ M.m < n := by
    rw [← head?_eq hf.qinv]
    exact TextFeedProg2.head_ne_mark_iff hmark hn hf
  by_cases ht : (TS M.ts GSTapes.tT).focus = e.blank
  · rw [fillEffect, if_pos ht]
    have hd := hb.mp ht
    by_cases hlt : M.m < n
    · rw [supplyEffect, if_neg (hh.mpr hlt), TextFeed.fillIf', if_pos ⟨hd, hlt⟩]
      exact congrArg (fun S => (RTQueue.tail M.Q, S)) (legacy_supply_stage M hf.qinv hf.buf)
    · have he : (toList M.Q).head?.getD e.mark = e.mark := by
        by_contra he; exact hlt (hh.mp he)
      rw [supplyEffect, if_pos he, TextFeed.fillIf', if_neg (by omega)]
  · have hd : M.st.pos + M.st.q ≠ M.m := fun h => ht (hb.mpr h)
    rw [fillEffect, if_neg ht, TextFeed.fillIf', if_neg (by omega)]

/-- A positive gate is always safe, including after an intervening arrival. -/
theorem enabled_sound {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hend : e.endSym ∉ v) (hblank : e.blank ∉ Text)
    (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (he : GateEnabled e (TS M.ts)) : Enabled v n M.st := by
  rcases he with hp | ht
  · exact Or.inl ((TextFeedProg2.read_tP_end_iff hend hf.qle hf.scan).mp hp)
  · have hne : M.st.pos + M.st.q ≠ M.m :=
      fun h => ht ((TextFeedProg2.read_tT_blank_iff hblank hn hf).mpr h)
    have hhd := hf.hd
    have hmle := hf.mle
    exact Or.inr (by omega)

/-- The stronger scanner-readiness condition needed by scanOne'_feedInv
also follows directly from a positive gate, without a no-arrival premise. -/
theorem scan_ready {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hend : e.endSym ∉ v) (hblank : e.blank ∉ Text)
    (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (he : GateEnabled e (TS M.ts)) :
    M.st.q ≠ v.length → M.st.pos + M.st.q < M.m := by
  intro hq
  have hp : (TS M.ts GSTapes.tP).focus ≠ e.endSym :=
    fun h => hq ((TextFeedProg2.read_tP_end_iff hend hf.qle hf.scan).mp h)
  have ht := he.resolve_left hp
  have hne : M.st.pos + M.st.q ≠ M.m :=
    fun h => ht ((TextFeedProg2.read_tT_blank_iff hblank hn hf).mpr h)
  have hh := hf.hd
  omega

/-- If new data arrived after the supply check, a false gate may lag behind
Enabled. This precisely identifies the missing supply instead of assuming
an invalid equivalence at an interrupted iteration boundary. -/
theorem disabled_pending {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hend : e.endSym ∉ v) (hblank : e.blank ∉ Text)
    (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M)
    (hg : ¬ GateEnabled e (TS M.ts)) (he : Enabled v n M.st) :
    M.st.pos + M.st.q = M.m ∧ M.m < n := by
  have hp : (TS M.ts GSTapes.tP).focus ≠ e.endSym := fun h => hg (Or.inl h)
  have ht : (TS M.ts GSTapes.tT).focus = e.blank := by
    by_contra h; exact hg (Or.inr h)
  have hd := (TextFeedProg2.read_tT_blank_iff hblank hn hf).mp ht
  have hq : M.st.q ≠ v.length := fun h =>
    hp ((TextFeedProg2.read_tP_end_iff hend hf.qle hf.scan).mpr h)
  have hh := he.resolve_left hq
  exact ⟨hd, by omega⟩

/-- After a supply attempt with no intervening arrival, the numeric and
tape-based enable conditions agree. -/
theorem filled_enabled {e : Env k} {v Text : List (Fin k)} {rate p₁ rem n : ℕ}
    {M : TextFeed.Machine' k} (hmb : e.mark ≠ e.blank) (hend : e.endSym ∉ v)
    (hblank : e.blank ∉ Text) (hn : n ≤ Text.length)
    (hf : TextFeed.FeedInv' e.blank e.startSym e.endSym e.mark v Text rate p₁ rem n M) :
    GateEnabled e (TS (TextFeed.fillIf' e.blank e.mark n M).ts) ↔ Enabled v n M.st := by
  have hf' := TextFeed.fillIf'_feedInv hmb hn hf
  constructor
  · intro h
    simpa only [TextFeed.fillIf'_st] using enabled_sound hend hblank hn hf' h
  · intro he
    by_contra hg
    have he' : Enabled v n (TextFeed.fillIf' e.blank e.mark n M).st := by
      simpa only [TextFeed.fillIf'_st] using he
    exact TextFeedProg2.fillIf'_not_again e.blank e.mark n M
      (disabled_pending hend hblank hn hf' hg he')

/-- info: 'PalPeg.TextFeedCycleModel.fill_effect_matches' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fill_effect_matches

/-- info: 'PalPeg.TextFeedCycleModel.filled_enabled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms filled_enabled

end PalPeg.TextFeedCycleModel
