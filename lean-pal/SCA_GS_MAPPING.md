# GS head programs ↔ list-level GS: a simulation design

Design note, 2026-09-23. **Nothing in this note is proved.** Abbreviations:

* **H** = head program. Python `docs/palindromes-in-peg/gs_heads.py` (gh), `gs_match_heads.py` (gm);
  Scala `scala/pal/src/main/scala/pal/GsHeads.scala` (GH), `GsMatchHeads.scala` (GM); Lean control
  transcription `PalPeg/ScaGsCoroutine.lean` (C). "Site n" means the Scala/C `site`.
* **E** = `docs/palindromes-in-peg/gs_events.py` (ge).
* **L** = Lean list level in `lean-pal/PalPeg/`: `GSPreprocess` (GP), `GSScan` (GS), `GSRealTime` (RT),
  `GSVerifier` (GV), `StageMatcher` (SM), `BorderJob` (BJ), `MiddleBorder` (MB).

## 0. Coordinates, and the missing layer

* **Matcher.** `start` places Origin at (end, reversed) and Tail at (end, forward), with Tail−Origin = length
  (`ScaWindowWorker.lean:469-473`). A reversed head at logical i sits at physical W−i and reads w[W−1−i].
  So the heads live on one logical word X = x ++ T, where x = (w.take W).reverse and T = w.drop W. These are
  exactly `stageMatch`'s u++v and T (SM:169). Copies keep the orientation. After the scan setup,
  A, Walk, Cut, First, KFirst and Reach are reversed (pattern side); P, B and U are forward (text side).
* **Flags.** Origin = (begin, fwd), TextOrigin = (end, rev), OriginalEnd = (begin, rev); Upper = b,
  Lower = b−h, where b is the segment length (`ScaWindowWorker.lean:454-468`). The pattern view is
  y = (w.drop W).take b and the text view is y.reverse, both on [0, b]. This is BJ's two-view setting (BJ:208).
* **Missing layer.** Lean has no head VM. C covers control only: a `Config` is a frame list with no positions.
  The relation R therefore needs HVM := (Config, π : Head → ℤ, text). Its event semantics are
  `StreamingMatcher.step` (gm:89-120) and `DualFlagVM.step`. Table rows ↔ `Config` is `ScaGsCert.sim_step`.
  Worker distance registers ↔ π-differences on live pairs (liveness, `ScaWindowWorker.lean:148-160`) is a
  separate lemma.

## 1. What each head holds

Notation:

* (s,p₁,r) = GP `decompose x 8` (GP:169). p₁ = 0 ↔ `period_exists = false`, and then L uses
  `effPeriod = |v|+1`, `effReach = 0` (SM:63-66).
* u = x.take s and v = x.drop s.
* Scan positions differ by file: GV/GS `pos` is the start of **v** in T (initial ⟨s,0⟩, GV:160). BJ `pos` and
  E `position` are the start of **x**.

| head | decomposition (`_first`/`_second`/strip) | matcher scan, GV state (⟨pos,q⟩,c) | border stage L, BJ state ⟨i,q⟩ |
|---|---|---|---|
| Origin / End | 0 / \|x\| (End:=Tail, gm:18) | 0 / \|x\| | 0 / L (End−1 per shrink, gh:195) |
| Tail / OriginalEnd | — | \|x\| / frontier W+n' | b−L (text origin) / b |
| Cut | current start s₀ (E `start`) | s | s |
| P | s₀+p (E/GP `p`) | \|x\|+pos−s (x-start) | Tail+i |
| A | s₀+q | s+q | s+q |
| B | P+q (compared with A; B−A = p) | P+(A−Origin) = \|x\|+pos+q | P+(A−Origin) |
| KP (blind) | s₀+k·p (B<KP ↔ q<(k−1)p) | dead after site 4 | ℓ = L−i, the overlap length (−1 per P+1) |
| First / KFirst / Reach | s+p₁ / s+k·p₁ (= GP's m) / s+r | same; read at sites 22-23 and in PeriodShift | same, per stage |
| Second (blind) | s₀+p₂ during strip (moves with Cut, gh:111) | unused | last start \|T\|−max(1,2s) (gh:158-163) |
| Walk / U | PeriodShift counter | c = checked (E `checked`) / P+c | prefix cursor at the frontier; shrink counter |
| locals | ResetShift `phase` = rewound mod k, `nonempty` = (q>0) | `prefix_ok`; `phase` ↔ E 2−`quota` | Cursor = E `remaining`; Lower/Upper = E `lower`/`upper` |

## 2. Generators, sites, and rates

Events are counted per yield, i.e. per table row. The window tables are `unit=false`, so one move tuple is
one row.

* **Initialize** (GH:47-68, C:145; gh:18-24). 6 events per `_first`/`_second` call ↔ `firstOuter … 1` and
  `secondOuter … 1 0` (GP:104,143).
* **First(k,bounded)** (GH:186-246, C:204; gh:60-74; ge:13-26).
  * Sites 2(+3) are the guard `p<|v| (∧ p<bound)` (ge:15, GP:96).
  * **Sites 4-7 are one `firstInner` iteration** (ge:17-21, GP:84-90): **4 events per comparison**.
  * Site 8, `B=KP`, is `q=(k−1)p` (ge:22, GP:97).
  * Site 9, ResetShift(false), is `p += shiftNoPeriod q k` (GP:51,100): 2q+⌈q/k⌉+≤4 events per L outer
    iteration.
* **Decompose** (GH:320-403, C:271; gh:93-112; ge:49-71; GP `decomposeLoop` 157-167).
  * Site 2 is `firstPeriod`; `none` returns `false` ↔ (s,0,0).
  * Sites 5-7 are one `extendReach` step (GP:110), 3 events per char. Site 9 is `secondPeriod` (GP:143).
  * Sites 10-13 are `stripLoop` (ge:66-71, GP:149): a bounded First, then Cut and Second move together at
    2 events per deleted char. A failed bounded First triggers `outer()`, the next `decomposeLoop` round.
  * **H matches GP's per-period deletion, not `decompose2`'s run skip (GSDecompose2:66).**
* **Second** (GH:251-314, C:236; gh:77-90; ge:29-46; GP:119-147).
  * Sites 3-7 are one `secondInner` step (3-5 events). "Found" ↔ `none`.
  * Sites 8-9 test k·p₁ ≤ q ≤ r as A ≥ KFirst ∧ A ≤ Reach (ge:40).
  * Site 10 is PeriodShift(false), 2p₁+2 events ↔ `p+=p₁, q-=p₁` (GP:137). Site 11 is ResetShift(false).
* **PeriodShift** (GH:153-180, C:189; gh:51-57). Walk goes from Cut to First, and each step does P+1, A−1.
  That is 2p₁+2 events for the one atomic `gsShift = p₁, gsNextQ = q−p₁` (GS:187-192). B is untouched,
  so B = P+(A−Origin) is kept.
* **ResetShift** (GH:73-148, C:158; gh:27-48). It rewinds A (and B when searching) one cell per 2 events.
  Every k cells it does P+1. On exit it adds one more P+1 iff q=0 ∨ k∤q. Net effect:
  P += max(1,⌈q/k⌉), the reset branch of `gsShift` (GS:187). Cost: 2q+⌈q/k⌉+≤4 events.
* **MatcherController** (GM:29-196, C:462-526; gm:15-58). E is `PatternMatcher` (ge:168-235) and L is
  GV `vStep` (GV:120):

| sites | H | E | L |
|---|---|---|---|
| 1-2 | End:=Tail; decompose x | preparation, ge:205-209 | (s,p₁,r) passed to `stageMatch` (SM:169) |
| 3-7 | P:=Tail, KP:=End, A:=Cut, B:=P, Walk:=Origin | position=matched=0 | — |
| 8-10 | B crosses s arrived cells, `available` first | none | none: GV starts at ⟨s,0⟩ (stuttering) |
| 11-12 | Walk:=Origin, U:=P, prefixOk:=true | ge:218 | `vStep` shift branch, `c:=0` |
| 13 | `available B`; spin if false | `waiting`, ge:187-190 | `Enabled` (RT:73) |
| 14-15 | `symbols A B`; A,B+1 | ge:228-231 | `scanStep` compare branch (GS:204) |
| 16-18, ≤2× | `symbols Walk U`; Walk,U+1 | prefix mode, ge:220-227 | `vComp ∘ vComp` (GV:80,123) |
| 19 | `equal A End` | ge:194 | q = \|v\| |
| 20-21 | `assert_equal Walk Cut`; `match B` | ge:196-199 | `vReportFlag` (GV:165) |
| 22-25 | shift decision; PeriodShift / ResetShift | ge:211-219 | `scanStep` shift, `gsShift`/`gsNextQ` |

**Rate per L step (`vStep`).**

* A v-success costs 4-10 events (13, 14, 15, [16,17,18]≤2, 19).
* A mismatch or a report costs 2, then the shift. The shift costs 2 (sites 22-23), then 2p₁+2 or
  2q+⌈q/k⌉+4, then 2 (sites 11-12).
* So the cost per step is not O(1). With L's Φ = (k+1)·pos+q (GS:225), however, ΔΦ is 1 on a success,
  k·p₁ on a period shift and ≥ max(1,⌈q/k⌉) on a reset. Hence **events ≤ (2k+12)·ΔΦ**, which is 28 at k=8.
* One `vComp` costs 3 events on success, 2 on failure, and 0 once prefixOk = false.
* Spins at site 13 occur only when the state is not `Enabled`.

## 3. The `match` event and the per-tick output

* **When `match` fires.** `match B` (site 21, gm:52) fires exactly when H leaves an L state z with q=|v| and
  prefixOk. Under the deadline invariant of §4.2, prefixOk ↔ c=|u| there. So it fires iff
  `vReportFlag n' z` (GV:165) with n' = B−Tail = pos+|v|.
* **What it means.** `vAnswer_correct` (GV:398) turns this into `OccAt (u++v) T (n'−|x|)`.
  `answer_iff_occursAt` (SM:174), with n = W+n', turns that into `occursAt (w.take W).reverse (w.take n)`,
  which is `MatchOracle.spec` (Assembly.lean:31).
* **Worker output.** `arrive` clears `output` (ScaWindowWorker.lean:430). `step` sets `output ||= match` and
  faults when B is still available (504-511). So `mOps.output` after tick n is "some `match` during this
  tick's 512 rows". No fault means B is at the frontier, i.e. the occurrence ends at exactly n. Hence
  output(tick n) = ans n of the MatchOracle for 2W ≤ n; this is `hmatch` of `window_correct`
  (ScaWindowOutput.lean:126-128).
* **L lemma to add: the drained answer.** Run `vStep` while `Enabled`, with fuel from the `scanSteps` bound
  (GS:511), and prove it equals `vAnswer`/`OccAt`. It is the same `vStep` orbit as `vOnlineRun`, cut at
  different points. It is easier than the rate-(k+1) lag argument (RT:230), because a drained state has
  pos+q = n', so Φ ≤ (k+1)n'.
* **H timing lemma.** By the end of tick W+n', H reaches the drained index j*(n') if
  Dec(x)+3s+28·(k+1)·n'+c₀ ≤ 512·(n'+1). The reason: H spins only when drained, and otherwise it spends the
  whole quantum. For n' ≥ W this needs **Dec(x) ≲ 257·|x|**, where Dec is H's decomposition row count.
  `OnlineMachine.stageRound` (OnlineMachine.lean:368-395) models this catch-up as one burst at n = 2W.

## 4. Deviations, and the invariants they need

1. **`available` waits** (sites 9, 13). Invariant: B ≤ frontier (`canMoveTo`) and B−Tail = pos+q; this is
   RT `Fits` (RT:84). The offset loop (sites 8-10) stutters on the L state ⟨s,0⟩.
2. **The U prefix check.** H's prefixOk replaces L's encoding, where a mismatch leaves `checked` stuck.
   * R needs: prefixOk=false → c<|u| ∧ T[pos−s+c] ≠ u[c].
   * `assert_equal` needs the **unconditional** deadline: prefixOk → |u| ≤ c+2(|v|−q). This is stronger than
     VInv's fourth clause (GV:64-69), which assumes that u matches.
   * The arithmetic is `prefix_verifier_deadline` (RT:440), which needs L1 for (s,p₁).
3. **Unary shifts.** Each shift loop is a stuttering segment of one L step, paid for by ΔΦ (§2).
   * ResetShift, mid-loop: ρ = q₀−(A−Cut), phase = ρ mod k, P−P₀ = ⌊ρ/k⌋, nonempty = (q₀>0).
     When searching, B−P = A−Origin. When not searching, B is stale until `copy B P` (site 9) and
     KP = Cut+k(P−Cut).
   * PeriodShift: Walk−Cut = t, P = P₀+t, A = A₀−t.
4. **Late decomposition.** L assumes (s,p₁,r) at text round 0, but H decomposes after birth while the text
   arrives, which needs Dec(x). GP `decomposeWork_le` (GP:1986) bounds 166|x|+21 *indexed* events. H spends
   4-5 rows per indexed event plus 2 per rewound cell, which exceeds 257. The row-level amortization has to
   be redone; GS_LOCAL_CLOCK.md claims D_batch(8) = 129.
5. **L1.** H's `_decompose` is GP's per-period deletion. For that function, L1 (`GSDecomp`) is only a
   hypothesis: `hdec` (EndToEnd.lean:20) and `DecOK` (MiddleBorder.lean:43). L1 is proved only for
   `decompose2` (GSDecompose2:354). Two places need it:
   * the deadline in item 2, which needs 3s<|x| and s<2p₁;
   * the flag stages, which need `nextLen s < L`. Otherwise `border_controller` never shrinks and never halts.

## 5. Flags: GsDualFlags vs Lean

* **The head program.** `DualFlagController` (GsDualFlags.scala:22 = GsFlagHeads.scala:30-53, C:530) runs
  `BorderController(flags=true, tailOrigin=TextOrigin)` (GH:496-732, C:350; gh:139-199). E's
  `borders`/`palindrome_flags` (ge:74-139) is only the single-view `u#reverse(u)` version.
* **Lean does have the matching list-level algorithm.** Besides Manacher (`MiddleJob`), `BorderJob.lean`
  is the two-view GS border job taken from `gs_dual_flags.py`:

| BJ | H sites |
|---|---|
| `ovStep` (BJ:241) | 19-21 scan, 32-35 shift |
| frontier `pos+\|u\|+q=\|T\|` | 22 |
| `MatchLen u T pos \|u\|` | 23-28 |
| `max 1 (2s)` | 12-17 |
| guard `\|T\| < pos+minimum` | 18 |
| `nextLen` (BJ:605) | shrink 36-43 |
| `borderJob` (BJ:646) | stage loop 3/6 |

  The specs are `borderJob_mem_iff` (BJ:666) and `palPrefixFlagsGS_spec` (BJ:713). `MiddleBorder` uses them
  with `gsDec` (MB:21), the same `decompose (y.take L) 8` that H runs, and `EndToEnd` builds on it.
* **Rates.** One `ovStep` comparison is 3 events. A frontier costs ≈7+3s events plus Report. A shift costs
  as in §2, plus site 18. L counts indexed `ovCost` (BJ:260); `palPrefixFlagsGS_work` gives ≤ 258|x| (BJ:785).
* **Gaps.**
  1. H's first stage starts at P = Tail+1 (gh:154-155), but BJ starts at ⟨0,0⟩ (BJ:455). A ⟨1,0⟩ variant of
     `stageRun_mem_iff` (BJ:460) is needed; the difference is harmless because Upper ≤ b.
  2. H streams the bits in descending order and fills gaps (`_report`, gh:115-127 = ge:116-137). L proves
     only membership. It needs "`borderJob` is strictly decreasing" plus a bit-stream lemma.
  3. The interval stop `End<Lower` (gh:146) and the `KP<Lower` exit have no L counterpart.
  4. The batch deadline is missing from L: 1024 rows per tick, the job must finish within h arrivals, and
     `require(¬pending)` fires at release. MB's schedule is a different one (13 jobs, rate 27900, MB:81-93).
  5. StageOK and L1, as in §4.5.

## 6. Hardest gap

**L1 for the decomposition that H actually runs**, i.e. per-period deletion = `GSPreprocess.decompose`.

* For this decomposition, Lean proves linear work (GP:1986) but not L1.
* Lean proves L1 only for `decompose2`. That uses run-skip deletion, and its linear work is open
  (Σpⱼ = O(T), GSDecompose2Work).
* Every no-fault, deadline and termination argument above depends on this bound.

Evidence only: `gs_overlap.decompose` showed no L1 violation on all binary words of length ≤ 20 (k=8) or
≤ 18 (k=4), nor on 20,000 structured random words of length ≤ 400.
