import PalPeg.TextFeedWarmBoundary
import PalPeg.TextFeedStartupClock

/-! Close the gap between the actual startup endpoint and the initial
conditions of continuous physical streaming, at the true arrival count. -/
set_option autoImplicit false

namespace PalPeg.TextFeedStartupBoundary
open PegSeparation.RealTimeTM PalPeg.Program PalPeg.ProgLang PalPeg.ProgLangPersist
open PalPeg.ProgLangBank PalPeg.PrepInstance PalPeg.PatternTapes PalPeg.PatternProg
open PalPeg.RTQueue PalPeg.TextFeedControl PalPeg.TextFeedInput PalPeg.TextFeedPrepare
open PalPeg.TextFeedStartupBank PalPeg.TextFeedStartupSchedule PalPeg.TextFeedStartupSafety
open PalPeg.TextFeedPrepResume PalPeg.TextFeedPrepEndpoint PalPeg.TextFeedRefine

variable {k : ℕ} {Terminal : Type}
noncomputable local instance : DecidableEq (TaskAct k) := Classical.decEq _
noncomputable local instance : DecidableEq (TaskCond k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Act k) := Classical.decEq _
noncomputable local instance : DecidableEq (TextFeedStartupBank.Cond k) := Classical.decEq _
noncomputable local instance (e : Env k) (leftSym : Fin k) (R rate : ℕ) :
    DecidableEq (Outer e leftSym R rate) := Classical.decEq _

theorem end_at_boundary {e : Env k} (hc : Function.Injective e.code) (hmb : e.mark ≠ e.blank)
    {leftSym : Fin k} {v Text : List (Fin k)} {R rate p₁ rem J : ℕ}
    (hk : 0 < rate) (hv : 0 < v.length) (hend : e.endSym ∉ v) (hstart : e.startSym ∉ v)
    (hblank : e.blank ∉ Text) (hmark : e.mark ∉ Text)
    (hK : KSimple v rate p₁ rem) (hJ : J < R)
    (enc : Terminal → Fin k) (c : CallCtrl (programs e) (Outer e leftSym R rate))
    (T : Fin 27 → STape (Fin k))
    (hb : AtBoundary (programs e) c.2.2.1) (hf : c.1.2.1 = true)
    (hc0 : c.1.1 = ⟨0, Nat.zero_lt_succ R⟩) (S : Stage k) (old : Fin k)
    (hx : feedView T = TextFeedInit.unprepared e S old)
    (hs : c.1.2.2.val = [task e leftSym rate]) (word : List Terminal) (a : Terminal)
    (hall : ∀ b ∈ word ++ [a], enc b ≠ e.mark)
    (hprefix : (word ++ [a]).map enc = Text.take (word.length + 1))
    (hn : word.length + 1 ≤ Text.length)
    (tr : List (Fin 15 → Fin k × Move)) (S' : PatternTapes.Tapes k)
    (he : Exec (source e) e.blank
      (finitePrepSetup e.blank e.startSym e.endSym leftSym e.mark rate) (prepView T) tr)
    (hout : applyTrace e.blank (prepView T) tr = TSg S')
    (hsplit : word.length * R + J = tr.length)
    (hscan : GSTapes.Encodes' e.blank e.startSym e.endSym e.mark v
      (TextFeed.padW e.blank Text 0) rate p₁ rem (toGS S') ⟨0, 0⟩)
    (hdelay : (rate + 1) * (word.length + 1) ≤ rate * v.length) :
    let z := stateBefore e leftSym enc R rate c T (word ++ [a])
    ∃ (y : Phys e R rate) (M : TextFeed.Machine' k) (ph : Phase) (q : Queue (Fin k)),
      TextFeedWorkerBridge.Link e leftSym R rate (z.state.1.1, z.tape) y ∧
      ReadyAt e z.tape q (enc a) ∧
      Sim e v Text R rate p₁ rem (word.length + 1) M ph y (enc a) ∧
      workScale rate * ((rate + 1) * (word.length + 1)) ≤ workCredit v rate (M, ph) ∧
      ScanInv v Text M.st ∧ (∀ i, OccAt v Text i → M.st.pos ≤ i) ∧
      y.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.1.1.1 = ⟨0, Nat.zero_lt_succ R⟩ ∧
      z.state.1.2 = ⟨0, by omega⟩ ∧ z.state.2 = ⟨0, by omega⟩ := by
  let x := prefixRun e leftSym enc R rate c T word a (J + 2)
  let q₀ := snoc (word.foldl (fun q b => snoc q (enc b)) empty) (enc a)
  obtain ⟨_, _, hview, hb', hr, hs', hf'⟩ := end_at_cost hc hmb leftSym enc R rate J
    (by omega) hJ c T hb hf hc0 S old hx hs word a hall tr he hsplit
  have hview' : prepView x.2 = TSg S' := hview.trans hout
  have hlist : toList q₀ = Text.take (word.length + 1) := by
    have hh := TextFeedScan.arrivals_fifo enc (word ++ [a]) empty inv_empty
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, toList_empty,
      List.nil_append, hprefix, q₀] using hh
  obtain ⟨qt, m, y, hl, hsim, hcredit⟩ := TextFeedPrepared.prepared_link hb' hf' hs'
    hview' hr hlist hscan hdelay
  have hcount : y.1.1.1 = nextPhase^[J + 2] ⟨0, Nat.zero_lt_succ R⟩ :=
    hl.ctrl.counter.symm.trans (TextFeedStartupClock.prefixRun_counter e leftSym enc R rate
      c T hc0 word a (J + 2))
  have ha := hall a (by simp)
  have hscan₀ := TextFeedBacklog.scanInv (toGS S') qt m q₀ v Text
  have hearly := TextFeedWarmBoundary.delay_before_first hv hdelay
  have hfinish := TextFeedWarmBoundary.finish_frame (Terminal := Terminal) hc hmb hk hv hend hstart
    hblank hmark hn hK hJ hearly hl hr ha hsim hcount hcredit hscan₀ rfl
  obtain ⟨hlast, ⟨q', hready⟩, hsim', hcredit', hscan', hpos', hxcount, hycount⟩ := hfinish
  dsimp only
  rw [TextFeedStartupClock.finish_prefix e leftSym enc R rate J hJ c T hc0 word a]
  exact ⟨_, _, _, q', hlast, hready, hsim', hcredit', hscan', hpos', hycount, hxcount, rfl, rfl⟩

/-- info: 'PalPeg.TextFeedStartupBoundary.end_at_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms end_at_boundary

end PalPeg.TextFeedStartupBoundary
