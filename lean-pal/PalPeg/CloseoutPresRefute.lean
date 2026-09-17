import PalPeg.GalilLeafPres

/-!
# `hended` / `hlastMatch` are not closed: their side input `hpres` is false

`CLAUDE.md` §3 lists `hended` and `hlastMatch` under 閉 (closed).  That is
wrong, and this file records why in a machine-checked form.

Both producers — `GalilLeafReport.hended_C` (`:234`),
`GalilLeafReport.hlastMatch_C` (`:352`) and `GalilOracleMC4.hlastMatch_C'`
(`:71`) — take

```
hpres : ∀ w s a v, SearchReady (searchLens.get s) →
          searchEffect (PofC centre place entry w) a s v → SearchReady v
```

i.e. bare `SearchReady` is preserved by a search quantum.  But
`GalilLeafPres.searchReady_run_true_iff` already proves the exact law:

```
SearchReady v' ↔ 1 ≤ value v.search.debt
```

for a `.run → .run` quantum on the event `true`.  So readiness survives **iff**
the debt had a unit left — a stage-ledger fact that `SearchReady v` (which only
gives `0 ≤ value v.search.debt`) cannot see.  At debt `0` the conclusion fails,
which `hpres_fails_at_zero_debt` below states outright.

Consequence: `hended` and `hlastMatch` stay leaves of
`CloseoutOracle8.h_oracle_of_leaves7`, and closing them needs the
reformulation `GalilLeafPres` prescribes (`SearchReadyB := ReadyRem ∧
RunEntriesAll`), not a proof of the current `hpres`.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutPresRefute

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter
open PalPeg.GalilBranchInvariants2 PalPeg.GalilLeafPres

/-- **`hpres` fails at debt zero.**  Directly from
`GalilLeafPres.searchReady_run_true_iff`: a `.run → .run` quantum on `true`
from a zero debt lands on a state that is *not* `SearchReady`, so the
unconditional preservation `hended_C` / `hlastMatch_C` / `hlastMatch_C'` ask for
cannot hold. -/
theorem hpres_fails_at_zero_debt {center : GalilScaffoldPlace.Place} {v v' : SearchVM}
    (hm : v.search.mode = GalilScaffoldSearchFinish.Mode.run)
    (hm' : v'.search.mode = GalilScaffoldSearchFinish.Mode.run)
    (hsr : SearchReady v) (h : searchStep center true v v')
    (hzero : value v.search.debt = 0) : ¬ SearchReady v' := by
  intro h'
  have := (searchReady_run_true_iff hm hm' hsr h).mp h'
  omega

#print axioms hpres_fails_at_zero_debt

end PalPeg.CloseoutPresRefute
