import PalPeg.CloseoutPreload38

/-!
# `CloseoutPreload39`: the ready field without the `hact` hypothesis

`CloseoutPreload38.readyField2_tick'` leaves a named residue `hact`, needed
because `CloseoutPreload37.ReadyFieldP2.paced` is conditioned on an idle chain
while `shifting` is not: with an active chain the search view is frozen
(`searchEffect_active`), so the datum has nothing paced to hand to the
`scan_shift` landing.

The fix is a shape fix.  Dropping the idle condition from `paced` outright is
**not** available: the `scan_count` tick decrements the clock, so the landing
asks for one more unit of slack than the entry has, and with a frozen view
there is no `searchEffect` to buy it (`readyPacedS_effect_false`).  What *is*
available is the slack-free clause

  `paced0 : mode = scan → ReadyPacedS v n 0`,

which is unconditional in the chain and is exactly what every landing of a
comparison tick (`scan_match`, `scan_shift`, both of which set
`clock := 2048`, i.e. slack `0`) asks for.  `ReadyFieldP3` is `ReadyFieldP2`
plus `paced0`, and `readyField3_tick` has **no `hact`**: the active-chain
branches go through `searchEffect_active` + `readyPacedS_mono` on `paced0`.

`CloseoutPreload37.readyField2_entry_of_datum` already establishes `paced0` at
a restart / replayStart entry: its proof discharges *both* paced clauses from
the same `readyPacedS_restarted` datum at slack `0`, ignoring the chain, so
`readyField3_entry_of_datum` is immediate.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload39

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.GalilScaffoldCounter (Counter value)
open PalPeg.CloseoutReadyStage (ReadyPacedS readyPacedS_ready readyPacedS_mono
  readyPacedS_effect_false readyPacedS_effect_true)
open PalPeg.CloseoutPreload5 (CentreLongRun NoReturn EntryDepthG dpEntryG)
open PalPeg.CloseoutPreload6 (prepLen runEntriesS_of_namedG)
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun18 (BigPack2M'')
open PalPeg.CloseoutPreload37 (ReadyFieldP2 readyField2_entry_of_datum)
open GalilScaffoldInputHead GalilScaffoldCounter GalilScaffoldChainVerifier

/-! ## 1. The chain-free ready field -/

/-- **`CloseoutPreload37.ReadyFieldP2` plus a chain-free paced clause.**  The
extra clause `paced0` is the idle condition *dropped* at the price of the
slack: at slack `0` the datum survives a frozen view, which is what the
active-chain branches need. -/
structure ReadyFieldP3 (n : ℕ) (x : State GalilVM) : Prop where
  ready : x.ctl.mode = Mode.scan →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  readyS : x.ctl.mode = Mode.shift →
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm)
  paced : x.ctl.mode = Mode.scan → x.vm.chain = ChainVM.idle →
    ReadyPacedS (searchLens.get x.vm) n (2048 - x.ctl.clock)
  paced0 : x.ctl.mode = Mode.scan → ReadyPacedS (searchLens.get x.vm) n 0
  shifting : x.ctl.mode = Mode.shift → ReadyPacedS (searchLens.get x.vm) n (2048 - x.ctl.clock)

/-- The projection to `CloseoutPreload37.ReadyFieldP2`. -/
theorem readyField3_to_field2 {n : ℕ} {x : State GalilVM} (h : ReadyFieldP3 n x) :
    ReadyFieldP2 n x := ⟨h.ready, h.readyS, h.paced, h.shifting⟩

#print axioms readyField3_to_field2

/-- **The entry, unchanged.**  `readyField2_entry_of_datum` proves both paced
clauses from the same restart datum at slack `0`, so `paced0` comes for free. -/
theorem readyField3_entry_of_datum {raw : List (Fin 2)} {c : Control} {r : GalilVM}
    {Rad D : ℕ} {last : Counter}
    (hclk : c.clock = 2048)
    (hR : Restarted raw r Rad last) (hSE : StageEntry Rad last)
    (hcl : CentreLongRun r (value last).toNat) (hnr : NoReturn r)
    (hdep : EntryDepthG r D) (hD : D ≤ prepLen (value last).toNat) :
    ReadyFieldP3 (dpEntryG (value last).toNat D) ⟨c, r⟩ := by
  have h := readyField2_entry_of_datum hclk hR hSE hcl hnr hdep hD
  have h0 : ReadyPacedS (searchLens.get r) (dpEntryG (value last).toNat D) 0 :=
    PalPeg.CloseoutReadyStage.readyPacedS_restarted hR _ 0
      (fun as hlen hpaced => runEntriesS_of_namedG hR hSE hcl hnr hdep hD as hlen hpaced)
  exact ⟨h.ready, h.readyS, h.paced, fun _ => h0, h.shifting⟩

#print axioms readyField3_entry_of_datum

/-! ## 2. The tick, with no `hact` -/

section TickT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- A background tick on the chain-free datum: `CloseoutPreload37.readyField2_background`
plus the slack-free conclusion, which survives a frozen view. -/
theorem readyField3_background {w : List (Fin 2)} {c : Control} {s t : GalilVM} {n n' k' : ℕ}
    (hm0 : c.mode = Mode.scan) (hf : ReadyFieldP3 n ⟨c, s⟩)
    (hb : (galilFrameS (PofC centre place entry w) q first).background s t)
    (hn : n ≤ n') (hk : k' ≤ (2048 - c.clock) + 1) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get t) ∧
      (t.chain = ChainVM.idle → ReadyPacedS (searchLens.get t) n' k') ∧
      ReadyPacedS (searchLens.get t) n' 0 := by
  obtain ⟨-, -, hch, -, -, -, -, -, -, -, -, hse⟩ :=
    backgroundS_fields _ q first hb
  by_cases hidle : s.chain = ChainVM.idle
  · have h1 : ReadyPacedS (searchLens.get s) n (2048 - c.clock) := hf.paced hm0 hidle
    have hp : ReadyPacedS (searchLens.get t) n' k' :=
      readyPacedS_effect_false _ hk hidle
        (readyPacedS_mono (by omega) le_rfl h1) hse
    exact ⟨readyPacedS_ready hp, fun _ => hp, readyPacedS_mono le_rfl (Nat.zero_le _) hp⟩
  · have hget : searchLens.get t = searchLens.get s :=
      searchEffect_active _ hse hidle
    refine ⟨by rw [hget]; exact hf.ready hm0, fun ht => absurd ht ?_, ?_⟩
    · rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
      · exact chainTick_ne_idle' htk hidle
      · exact absurd hi hidle
      · exact absurd hi hidle
    · rw [hget]; exact readyPacedS_mono hn le_rfl (hf.paced0 hm0)

#print axioms readyField3_background

/-- **The `scan_shift` tick, with no `hact`.**  When the chain is active the
view is frozen, so the slack-free clause `paced0` carries over verbatim. -/
theorem readyField3_shift {w : List (Fin 2)} {n n' : ℕ} {c : Control} {s s' t : GalilVM}
    (hf : ReadyFieldP3 n ⟨c, s⟩) (hn : n ≤ n')
    (hm0 : c.mode = Mode.scan) (hc : c.clock = 1)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s')
    (hb : (PofC centre place entry w).beginShift s' t) :
    ReadyFieldP3 n' ⟨{c with clock := 2048, mode := Mode.shift}, t⟩ := by
  obtain ⟨vs, vq, a, -, -, -, hse, hch, hs'⟩ := hcmp
  obtain ⟨wch, -, ht⟩ : beginShiftVM' s' t := hb
  have hget : searchLens.get t = vq := by
    subst ht; subst hs'; cases a <;> rfl
  have hp : ReadyPacedS (searchLens.get t) n' 0 := by
    rw [hget]
    by_cases hidle : s.chain = ChainVM.idle
    · have hp0 : ReadyPacedS (searchLens.get s) (n' + 1) (2048 - c.clock) :=
        readyPacedS_mono (n := n) (n' := n' + 1) (by omega) le_rfl (hf.paced hm0 hidle)
      cases a
      · exact readyPacedS_effect_false _ (Nat.zero_le _) hidle hp0 hse
      · exact readyPacedS_effect_true _ (by omega) hidle hp0 hse
    · have hvq : vq = searchLens.get s := searchEffect_active _ hse hidle
      rw [hvq]
      exact readyPacedS_mono hn le_rfl (hf.paced0 hm0)
  refine ⟨fun hm => by simp at hm, fun _ => readyPacedS_ready hp, fun hm => by simp at hm,
    fun hm => by simp at hm, fun _ => ?_⟩
  show ReadyPacedS (searchLens.get t) n' (2048 - 2048)
  simpa using hp

#print axioms readyField3_shift

/-- **`CloseoutPreload38.readyField2_tick'` with `hact` gone.**  Only the two
re-entry residues (`restart`, `replayStart`) are left, and both are discharged
pointwise by `readyField3_entry_of_datum`. -/
theorem readyField3_tick {w : List (Fin 2)} {n n' : ℕ} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x) (hf : ReadyFieldP3 n x)
    (hn : n ≤ n')
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hentry : x.ctl.mode = Mode.scan → restartVM entry x.vm y.vm → ReadyFieldP3 n' y)
    (hentry' : x.ctl.mode = Mode.replayStart → ReadyFieldP3 n' y) :
    ReadyFieldP3 n' y := by
  obtain ⟨c, s⟩ := x
  obtain ⟨c', t⟩ := y
  cases h
  case init => rename_i hm0 h0; exact absurd hm0 hx.aux.front.notInit
  case scan_wait =>
    rename_i hm0 h0 hb
    obtain ⟨hr, hp, hp0⟩ := readyField3_background centre place entry q first hm0 hf hb
      (n' := n') hn (k' := 2048 - c.clock) (by omega)
    exact ⟨fun _ => hr, fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ hi => hp hi,
      fun _ => hp0, fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
  case scan_count =>
    rename_i hm0 h0 hc hb
    obtain ⟨hr, hp, hp0⟩ := readyField3_background centre place entry q first hm0 hf hb
      (n' := n') hn (k' := 2048 - (c.clock - 1)) (by omega)
    exact ⟨fun _ => hr, fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ hi => hp hi,
      fun _ => hp0, fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
  case scan_match =>
    rename_i s' o hmt hm0 hc hcmp h0 hpl ho
    obtain ⟨vs, vq, a, -, -, -, hse, hch, hs'⟩ := hcmp
    have hpl' : t = (if c.replaying then {s' with replay := GalilScaffoldCounter.dec s'.replay}
        else s') := hpl
    have hget : searchLens.get t = vq := by
      subst hpl'; subst hs'; cases c.replaying <;> cases a <;> rfl
    have hchain : t.chain = vs.chain := by
      subst hpl'; subst hs'; cases c.replaying <;> cases a <;> rfl
    by_cases hidle : s.chain = ChainVM.idle
    · have hp0 : ReadyPacedS (searchLens.get s) (n' + 1) (2048 - c.clock) :=
        readyPacedS_mono (n := n) (n' := n' + 1) (by omega) le_rfl (hf.paced hm0 hidle)
      have hp : ReadyPacedS vq n' 0 := by
        cases a
        · exact readyPacedS_effect_false _ (Nat.zero_le _) hidle hp0 hse
        · exact readyPacedS_effect_true _ (by omega) hidle hp0 hse
      rw [← hget] at hp
      exact ⟨fun _ => readyPacedS_ready hp, fun hm => absurd (hm0.symm.trans hm) (by decide),
        fun _ _ => hp, fun _ => hp, fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
    · have hget' : vq = searchLens.get s :=
        searchEffect_active _ hse hidle
      have hp0 : ReadyPacedS (searchLens.get t) n' 0 := by
        rw [hget, hget']; exact readyPacedS_mono hn le_rfl (hf.paced0 hm0)
      refine ⟨fun _ => by rw [hget, hget']; exact hf.ready hm0,
        fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ ht => absurd ht ?_,
        fun _ => hp0, fun hm => absurd (hm0.symm.trans hm) (by decide)⟩
      rw [hchain]
      rcases hch with ⟨_, htk⟩ | ⟨hi, _⟩ | ⟨hi, _⟩
      · exact chainTick_ne_idle' htk hidle
      · exact absurd hi hidle
      · exact absurd hi hidle
  case scan_shift =>
    rename_i s1 hm0 h0 hc hcmp hmt hr hg hbs
    exact readyField3_shift centre place entry q first hf hn hc hcmp hr hbs
  case shift_one =>
    rename_i hm0 hpos hso
    have hget : searchLens.get t = searchLens.get s := by
      obtain ⟨-, hset⟩ := hso
      rw [hset]; rfl
    refine ⟨fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ => by
        rw [hget]; exact hf.readyS hm0,
      fun hm => absurd (hm0.symm.trans hm) (by decide),
      fun hm => absurd (hm0.symm.trans hm) (by decide), fun _ => ?_⟩
    rw [hget]
    exact readyPacedS_mono hn le_rfl (hf.shifting hm0)
  case shift_done =>
    rename_i o hm0 hpos ho
    exact ⟨fun _ => hf.readyS hm0, fun hm => by simp at hm,
      fun _ _ => readyPacedS_mono hn le_rfl (hf.shifting hm0),
      fun _ => readyPacedS_mono hn (Nat.zero_le _) (hf.shifting hm0), fun hm => by simp at hm⟩
  case replayStart =>
    rename_i o hm0 h0 ho ho'
    exact hentry' hm0
  case restart =>
    rename_i hm0 hb
    exact hentry hm0 hb
  all_goals
    (clear hx hentry hentry' hf
     refine ⟨fun hm => ?_, fun hm => ?_, fun hm _ => ?_, fun hm => ?_, fun hm => ?_⟩ <;>
       exfalso <;> simp_all)

#print axioms readyField3_tick

/-- **The datum along a run**, with no `hact`. -/
theorem readyField3_along_run {w : List (Fin 2)} {n m : ℕ} {x y : State GalilVM}
    (hr : GalilScaffoldChainInputSupply.StepsAll
      (galilFrameS (PofC centre place entry w) q first) 2048
      (BigPack2M'' centre place entry q first w) m x y)
    (hf : ReadyFieldP3 n x)
    (hentry : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.scan → restartVM entry z.vm z'.vm → ReadyFieldP3 n z')
    (hentry' : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.replayStart → ReadyFieldP3 n z') :
    ReadyFieldP3 n y := by
  induction hr with
  | zero z hz => exact hf
  | succ hz h hrest ih =>
    exact ih (readyField3_tick centre place entry q first hz hf le_rfl h
      (hentry _ _ h) (hentry' _ _ h))

#print axioms readyField3_along_run

end TickT

/-- **The `Extra5S.ready` shape.**  In `scan` or `shift` mode the field gives
the search readiness `CloseoutPackRun45` asks for. -/
theorem readyField3_to_ready {n : ℕ} {x : State GalilVM} (hf : ReadyFieldP3 n x)
    (hm : x.ctl.mode = Mode.scan ∨ x.ctl.mode = Mode.shift) :
    PalPeg.GalilBranchInvariants2.SearchReady (searchLens.get x.vm) :=
  hm.elim hf.ready hf.readyS

#print axioms readyField3_to_ready

end PalPeg.CloseoutPreload39
