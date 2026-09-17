import PalPeg.CloseoutPreload37

/-!
# `CloseoutPreload38`: the `scan_shift` tick of the fuel-indexed ready field

`CloseoutPreload37.readyField2_tick` leaves three residues; this module
discharges the middle one, `hshift`: the `scan_shift` tick of
`GalilScaffoldTop.Tick`, which is a **comparison** (`compareFound`, i.e. the
very same search quantum as `scan_match`/`scan_count`) followed by
`beginShift` in one step, landing in `shift` mode.

Two observations make the branch go through.

* The search effect is a comparison effect, so `readyPacedS_effect_true` /
  `readyPacedS_effect_false` apply verbatim, exactly as in `scan_match`.  The
  tick sets `clock := delay = 2048`, so the slack `2048 - clock` at the target
  is `0` — which is what a comparison leaves anyway.
* `beginShiftVM` writes only `remaining`, `length`, `chain`, `cycle` and
  `periodOnly`, none of which is in `searchLens`, so the landing's search view
  is the compared one.

One hypothesis is named: `hact`.  When the chain is **not** idle the search
view is frozen (`searchEffect_active`), so `ready`/`readyS` come from the datum
— but the datum's `paced` clause is conditioned on an idle chain, so there is
simply no paced list to hand over, and the unconditional `shifting` clause has
to be supplied from outside.  `hact` is that supply, and it is a statement
about the *entry* state (the frozen view), not about the landing.

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPreload38

open PalPeg PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldTop GalilScaffoldController
open PalPeg.CloseoutReadyStage (ReadyPacedS readyPacedS_ready readyPacedS_mono
  readyPacedS_effect_false readyPacedS_effect_true)
open PalPeg.GalilRunSkeleton (PofC)
open PalPeg.CloseoutPackRun18 (BigPack2M'')
open PalPeg.CloseoutPreload37 (ReadyFieldP2 readyField2_tick)

section ShiftT
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **The `scan_shift` tick carries the fuel-indexed datum into `shift` mode.**
The comparison spends one event of fuel and resets the slack to `0`; the
`beginShift` half leaves the search view alone. -/
theorem readyField2_shift {w : List (Fin 2)} {n n' : ℕ} {c : Control} {s s' t : GalilVM}
    (hf : ReadyFieldP2 n ⟨c, s⟩) (hn : n ≤ n' + 1)
    (hm0 : c.mode = Mode.scan) (hc : c.clock = 1)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare s s')
    (hb : (PofC centre place entry w).beginShift s' t)
    (hact : s.chain ≠ ChainVM.idle → ReadyPacedS (searchLens.get s) n' 0) :
    ReadyFieldP2 n' ⟨{c with clock := 2048, mode := Mode.shift}, t⟩ := by
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
      exact hact hidle
  refine ⟨fun hm => by simp at hm, fun _ => readyPacedS_ready hp, fun hm => by simp at hm,
    fun _ => ?_⟩
  show ReadyPacedS (searchLens.get t) n' (2048 - 2048)
  simpa using hp

#print axioms readyField2_shift

/-- **`CloseoutPreload37.readyField2_tick` with `hshift` discharged.**  Only the
two re-entry residues (`restart`, `replayStart`) are left, plus the named
`hact`. -/
theorem readyField2_tick' {w : List (Fin 2)} {n n' : ℕ} {x y : State GalilVM}
    (hx : BigPack2M'' centre place entry q first w x) (hf : ReadyFieldP2 n x)
    (hn : n ≤ n') (hn1 : n ≤ n' + 1)
    (h : Tick (galilFrameS (PofC centre place entry w) q first) 2048 x y)
    (hact : x.vm.chain ≠ ChainVM.idle → ReadyPacedS (searchLens.get x.vm) n' 0)
    (hentry : x.ctl.mode = Mode.scan → restartVM entry x.vm y.vm → ReadyFieldP2 n' y)
    (hentry' : x.ctl.mode = Mode.replayStart → ReadyFieldP2 n' y) :
    ReadyFieldP2 n' y := by
  refine readyField2_tick centre place entry q first hx hf hn h hentry hentry' ?_
  intro _ _
  clear hentry hentry' hx
  obtain ⟨c, s⟩ := x
  cases h
  case scan_shift =>
    rename_i _ s1 s2 _ _ hbs hm0 hc _ hcmp _ _
    exact readyField2_shift centre place entry q first hf hn1 hm0 hc hcmp hbs hact
  all_goals simp_all

#print axioms readyField2_tick'

/-- **The datum along a run.**  With the two re-entry residues and `hact`
supplied uniformly, `ReadyFieldP2 n` walks along every `galilFrameS` run whose
states satisfy the pack — in particular along a run started at a `restart` /
`replayStart` landing, where `CloseoutPreload37.readyField2_entry_of_datum`
provides the datum at fuel `n = dpEntryG k D`. -/
theorem readyField2_along_run {w : List (Fin 2)} {n m : ℕ} {x y : State GalilVM}
    (hr : GalilScaffoldChainInputSupply.StepsAll
      (galilFrameS (PofC centre place entry w) q first) 2048
      (BigPack2M'' centre place entry q first w) m x y)
    (hf : ReadyFieldP2 n x)
    (hact : ∀ z : State GalilVM, z.vm.chain ≠ ChainVM.idle →
      ReadyPacedS (searchLens.get z.vm) n 0)
    (hentry : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.scan → restartVM entry z.vm z'.vm → ReadyFieldP2 n z')
    (hentry' : ∀ z z' : State GalilVM,
      Tick (galilFrameS (PofC centre place entry w) q first) 2048 z z' →
      z.ctl.mode = Mode.replayStart → ReadyFieldP2 n z') :
    ReadyFieldP2 n y := by
  induction hr with
  | zero z hz => exact hf
  | succ hz h hrest ih =>
    exact ih (readyField2_tick' centre place entry q first hz hf le_rfl (by omega) h
      (hact _) (hentry _ _ h) (hentry' _ _ h))

#print axioms readyField2_along_run

end ShiftT

end PalPeg.CloseoutPreload38
