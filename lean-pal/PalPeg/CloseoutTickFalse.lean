import PalPeg.GalilChainTickable

/-!
# The background tick needs no `Good`

`GalilReplayChainSeg.ChainTickable` asks that a live, ready chain tick into a
**ready** chain on either event.  That is the wrong statement, and not for a
subtle reason: `.broken` is a state the machine legitimately reaches — Galil's
chain breaks exactly when the period prediction fails, which is how the end of a
periodic run is detected — and `ChainReady .broken` is `False`.  So `ChainReady`
is by design not closed under ticks, and `GalilChainTickable`'s
`chainTickable_unless_break` (ready **or** broken) is the honest form.

*(Record correction: earlier notes in this development reported `ChainTickable`
as "refuted".  No machine-checked derivation of `False` from it was ever
written; the claim was carried over from prose.  What is true is the statement
above — the statement is malformed — and that is what this file uses.)*

The `break` lives in `ChainMatched`, and `ChainTick` only consults it at
`a = true`:

```
ChainTick a x z := ∃ y, ChainStep x y ∧ (if a then ChainMatched y z else z = y)
```

So at `a = false` the tick **is** the step, and no step out of a non-broken
chain lands in `.broken` (the only `ChainStep` constructor with a `.broken`
target is `brokenIdle`, whose source is `.broken`).  So the break analysis is
free at `a = false`.

**But this does not yet give the background countdown what it needs.**  The
theorem below is stated **relative to a `WatchOk` instance** (`hOk`), because
`chainOk_tick`'s watch case goes through `internal_exists`, which uses
`WatchOk.good`.  And:

* **no `WatchOk` instance exists in this repository** (`grep` for `WatchOk `
  outside its own definition and the `hOk` binders finds none);
* `GalilWatchOkInst.no_watchOk_instance` rules out instances that additionally
  satisfy `∀ w, Ok w → Good w` **unconditionally** — but `WatchOk.good` only
  asks for `Good` at *positive lag*, so that theorem does **not** settle
  `WatchOk` alone.

Whether `WatchOk` is satisfiable is therefore **unsettled**, and it is not
claimed here either way.  Until an instance exists, re-basing
`CloseoutWatchRound.watchSeg_countdown` / `CloseoutWatchRound9.scanSeg_countdown`
on `ChainOk` is blocked.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutTickFalse

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilTickFun PalPeg.GalilChainTickable

/-- **No `ChainStep` out of a `ChainOk` chain lands in `.broken`.** -/
theorem step_ne_broken {Ok : WState → Prop} {x y : ChainVM} (hx : ChainOk Ok x)
    (h : ChainStep x y) (w : GalilScaffoldChainWatch.State) : y ≠ ChainVM.broken w := by
  intro hy
  rw [hy] at h
  cases h with
  | brokenIdle w0 => exact hx.elim

/-- **The background tick, with no `Good` and no break case.** -/
theorem chainOk_tick_false {Ok : WState → Prop} (hOk : WatchOk Ok) {x : ChainVM}
    (hx : ChainOk Ok x) (hne : x ≠ ChainVM.idle) :
    ∃ z, ChainTick false x z ∧ ChainOk Ok z ∧ ChainReady z := by
  obtain ⟨z, hz, hcase⟩ := chainOk_tick hOk false hx hne
  rcases hcase with hok | ⟨w', hbr⟩
  · exact ⟨z, hz, hok, chainReady_of_chainOk hOk hok⟩
  · exfalso
    obtain ⟨y, hstep, hzy⟩ := hz
    have hy : y = ChainVM.broken w' := by
      rw [← show z = y from hzy]; exact hbr
    exact step_ne_broken hx hstep w' hy

#print axioms step_ne_broken
#print axioms chainOk_tick_false

end PalPeg.CloseoutTickFalse
