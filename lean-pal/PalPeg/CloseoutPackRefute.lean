import PalPeg.CloseoutChainPack

/-!
# `hpack` is false as stated — `ChainPack.scanBound` is a run property

`CloseoutFinalW4.pal_in_peg_final37`'s fourth hypothesis is

```
hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s
```

and it does not hold.  `ChainPosInv2` has exactly three fields
(`CloseoutPackRun41:215`) — `Coupled'`, the payload at a non-idle chain, and the
shift-mode ledger — and `chainPosInv2_of_idle` gives it for **every** `w`, `c`
and `s` whose chain is idle.  But `ChainPack` carries

```
scanBound : c.mode = Mode.scan → ∃ m : ℕ, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2 * m - 1
```

whose existential is **unsatisfiable** as soon as `w.length ≤ 1`: it asks for
`1 ≤ m < w.length`.  A scan-mode state with an idle chain is exactly where every
run starts (`Tick.init`'s landing has `t.chain = ChainVM.idle`), so the
counterexample is in the theorem's own domain — `PAL` contains the one-letter
words.

`hpack_false_at_short_word` below is that contradiction, machine-checked.

**Consequence.**  `scanBound` is a *checkpoint* fact about the run, not a
one-state invariant: it says the right head has not passed the cell `2m-1` of
the checkpoint the oracle is reporting at.  Its shape is the same one
`GalilLeafPos` / `CloseoutSegBudget` already carry (`position r.right ≤ 2*m-1`
with `1 ≤ m ≤ w.length`), and the consumers of `ChainPack` that need it are the
ones running inside a cycle at a fixed `m`.  So the reformulation is to make the
checkpoint a *parameter* of the pack rather than an existential inside it, i.e.

```
ChainPackAt (m : ℕ) … with  scanBoundAt : c.mode = Mode.scan → position s.right ≤ 2 * m - 1
```

premised by `1 ≤ m` and `m ≤ w.length`, which is what every consumer already has
in scope.  Until that is done, the leaf stays **OPEN**, and the four-hypothesis
form of `pal_in_peg_final37` cannot be driven to zero through this route.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutPackRefute

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.CloseoutPackRun41 PalPeg.CloseoutChainPack

/-- **`hpack` contradicts a short word.**  At a scan-mode state with an idle
chain — the landing of `Tick.init` — `ChainPosInv2` holds for every `w`, while
`ChainPack.scanBound` needs `1 ≤ m < w.length`. -/
theorem hpack_false_at_short_word {q : ℕ} {first : Fin 9}
    (hp : ∀ (w : List (Fin 2)) (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → ChainPack q first w c s)
    (w : List (Fin 2)) (hw : w.length ≤ 1) (c : Control) (s : GalilVM)
    (hm : c.mode = Mode.scan) (hi : s.chain = ChainVM.idle) : False := by
  obtain ⟨m, hm1, hmlt, -⟩ := (hp w c s (chainPosInv2_of_idle hi)).scanBound hm
  omega

/-- The same, with the word's length as the only datum: `ChainPack` at a
one-letter word is uninhabited in scan mode. -/
theorem chainPack_false_at_short_word {q : ℕ} {first : Fin 9}
    {w : List (Fin 2)} (hw : w.length ≤ 1) {c : Control} {s : GalilVM}
    (hm : c.mode = Mode.scan) (hP : ChainPack q first w c s) : False := by
  obtain ⟨m, hm1, hmlt, -⟩ := hP.scanBound hm
  omega

/-- **The simpler witness: `centreCanR` has no mode premise at all.**
`ChainPack.centreCanR : canRight s.center` is asserted unconditionally, while
`ChainPosInv2` holds of every idle-chain state — including one whose centre head
has reached the end of the input, which is where every completed scan leaves
it. -/
theorem hpack_false_at_exhausted_centre {q : ℕ} {first : Fin 9}
    (hp : ∀ (w : List (Fin 2)) (c : Control) (s : GalilVM),
      ChainPosInv2 w c s → ChainPack q first w c s)
    (w : List (Fin 2)) (c : Control) (s : GalilVM)
    (hi : s.chain = ChainVM.idle)
    (hc : ¬ GalilScaffoldChainVerifier.canRight s.center) : False :=
  hc (hp w c s (chainPosInv2_of_idle hi)).centreCanR

/-! ## The diagnosis

`ChainPack` is a bundle of **run** facts written as a one-state predicate:
besides `scanBound` it asserts `shiftCanR` (`canRight s.right` in shift mode),
`centreCanR` (`canRight s.center`, unconditionally), `saneR`, `centreSane`,
`scanCentre`, `lenNonneg` … — every one of which fails at some state a
`ChainPosInv2` allows, because `ChainPosInv2` has only three fields
(`Coupled'`, the non-idle payload, the shift ledger) and `chainPosInv2_of_idle`
makes it free at an idle chain.

`ChainPack`'s own docstring for `scanBudget_of_chainPack` says it: "`ChainPack`
is established **along the run** (where the bound comes from)".  That is the
fix — the pack has to be threaded through `Steps` from the boot state, the way
`CloseoutRoundBundle.RoundBundle` is (`roundBundle_tick` / `roundBundle_steps`),
not premised on a one-state invariant.  At the boot state the heads are at the
input origin, so every `canRight` holds, and each tick either keeps the head or
advances it by one under the run's own budget.

Until then `hpack` is **REFUTED**, and `pal_in_peg_final37`'s four-hypothesis
form is not a four-*provable*-hypothesis form.  The count was reached in part by
folding the earlier separate leaf `ScanBudget` (`CloseoutFinalPack`'s `hbudget`)
into the bundle as `scanBound`, which the ledger's own rule marks as no
reduction at all — and here it also turned a leaf that was already false into a
false bundle. -/

#print axioms hpack_false_at_short_word
#print axioms chainPack_false_at_short_word
#print axioms hpack_false_at_exhausted_centre

end PalPeg.CloseoutPackRefute
