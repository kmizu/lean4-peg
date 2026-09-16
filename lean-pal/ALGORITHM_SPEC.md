# PAL in real time — algorithm specification for Lean 4

Scope: the live **GS delayed-stage** route (`delayed_pal.py` + `gs_*`). An older
Galil-1978 online-center route (`galil_clock.py`, `galil_contracts.py`) supplies
§4 only; the docs never say which is final. Paths are relative to
`docs/palindromes-in-peg/`.

## 1. Top-level decomposition

Input `w ∈ {a,b}*`, 0-based; `now = n = len(data)` is the 1-based prefix length
(`delayed_pal.py:95`). A **stage** of width `W ∈ {2,4,8,…}` is created at arrival
`now = W` (`:103-105`), answers on `now ∈ [2W,4W)` (`:75-82`), and is retired at
`now = 4W` before the new stage is made (`:98-102`).

**Split.** For `2W ≤ n < 4W`, `ℓ = n−2W ∈ [0,2W)` and
`data[0..n) = data[0..W) · data[W..W+ℓ) · data[n−W..n)`.

**L8 (split).** `data[0..n)` is a palindrome ⟺ `data[n−W..n) =
reverse(data[0..W))` (`match(n)`) **and** `data[W..W+ℓ)` is a palindrome
(`middle(n)`). (`DELAYED_PAL.md:7-14`)

**≤2 live.** Stage `W` is live on `now ∈ [W,4W)`, i.e. `n/4 < W ≤ n`; at most two
powers of two lie there, at least one for `n ≥ 2`. `n < 4` is finite-cased
(`True` for `n<2`, `data[0]==char` otherwise, `:106`). Asserted at `:110-114`.

## 2. Pattern matcher (`gs_events.PatternMatcher`; heads `gs_match_heads.py`)

Not KMP. **Galil–Seiferas** (JCSS 26 (1983) 280–294) with fixed `k = 8`
(`GS_OVERLAP.md:17-29`).

Pattern = `reverse(data[0..W))`, text = `data[W..)` growing (`delayed_pal.py:34`).
A match with text-end `e` is an occurrence ending at input `W+e`; the stage
requires `e + W == now` (`:71-73`), so the match is for the *current* arrival.

**Preprocessing.** `decomposition(|x|,k)` → `(cut s, period p1|None, reach r)`
(`gs_events.py:49-71`): `x = uv`, `|u| = s`, `v` has at most one basic prefix
repeated `k` times.

- **L1**: `s < |x|/(k−1)`, `s < (k−1)/(k−2)·p1` (`GS_OVERLAP.md:24-29`).
- **L2 (safe shift)**: with `q` chars of `v` matched, if `k·p1 ≤ q ≤ r` advance by
  `p1` keeping `q−p1`, else by `max(1,⌈q/k⌉)` with `q:=0`
  (`GS_OVERLAP.md:31-33`, `gs_overlap.py:32`, `gs_events.py:210-218`).
- **L3 (potential)**: `Φ = (k+1)p+q` strictly increases on each successful
  comparison and each reset (`GS_OVERLAP.md:34-36`); streaming variant `Φ = 2kp+q`
  (`GS_LOCAL_CLOCK.md:105-110`).

**State** (finite tuple; no failure table, recursion stack or candidate list,
`GS_OVERLAP.md:47-49`): `(s,p1,r)`, `position`, `matched`, `checked`, `prefix_ok`,
`quota`, `mode ∈ {compare,prefix,shift}` (`gs_events.py:180-185`).

**Interleaving / predictability.** Each successful `v`-comparison is followed by
`quota = 2` comparisons of the short prefix `u` (`:232-234`); a shift restarts the
verifier (`:218`). Since `|u| < (k−1)/(k−2)·p1` and `|u| < |x|/(k−1)`, it finishes
before a full candidate can be reported (`DELAYED_PAL.md:36-39`). Violation:
`prefix verifier missed the full-match deadline` (`gs_events.py:196-198`); in
heads, `assert_equal Walk Cut` (`gs_match_heads.py:50,107-109`).

**Rate.** `MATCH_RATE = 80` *indexed* steps/arrival (`delayed_pal.py:10`,
`DELAYED_PAL.md:36-41`) — not head/SCA steps: the head clock is logical 512 /
physical 2,048 (`GS_LOCAL_CLOCK.md:112-117`), batch backend 512 (`:152`).

## 3. Middle-palindrome job (`gs_events.palindrome_job`)

Offline; four jobs per stage, `j = 0..3`, `h = W/2`, `b = (j+1)h`.

- **Released** at `now = W+b`, `batch = (now−W)/h − 1` (`delayed_pal.py:43-51`);
  overrun is an error (`:47-48`).
- **Input window**: `data[W..W+b)`, frozen.
- **Computes** flags for lengths `[jh,(j+1)h)` via
  `palindrome_flags(size, lower=jh, upper=b)` (`gs_events.py:108-139`), emitted
  **descending**; a persistent stack pops them **ascending**, one per active
  arrival (`delayed_pal.py:78-81`).
- **Deadline**: first use at `now = 2W+b−h`, exactly `h = W/2` arrivals of service
  (`DELAYED_PAL.md:22-28`). Checked at `:59-60` and `:79-80`.

**Algorithm** — border enumeration on the internal view `u # reverse(u)`:

- **L4 (duality)**: nonempty proper borders of `u # reverse(u)` = nonempty
  palindromic prefixes of `u`; the fresh `#` rules out longer overlaps
  (`GS_OVERLAP.md:51-54`, `gs_overlap.py:149-155`). `#` is illegal in the final
  input, so the view must be built internally (`GS_OVERLAP.md:55-57`).
- **L5 (shrinking stages)**: a stage of pattern length `m` searches overlaps
  `≥ max(1,2s)`, then sets `m := max(1,2s)−1`; stages shrink by `< 2/(k−1)`, hence
  geometric (`GS_OVERLAP.md:36-45`).
- **L9 (two-view)**: with pattern `u`, text `reverse(u)`, an overlap of length `ℓ`
  is exactly `u[:ℓ] = reverse(u[:ℓ])`, recurring after shrinking to `m`
  (`GS_LOCAL_CLOCK.md:126-140`); removes the `2b+1` preprocessing length.

**Cost.** Indexed, one flag interval costs `≤ 215b+109` (`GS_OVERLAP.md:106-107`);
with `b ≤ 2W`, `W ≥ 2`, `215b+109 ≤ 430W+109 ≤ 512W` over `W/2` arrivals, giving
`JOB_RATE = 1024` (`delayed_pal.py:11`, `DELAYED_PAL.md:30-33`). Lowered:
`C(8)=420` head instr/char, dual-view `8(2C+0.5)=6724 → 8192`
(`GS_LOCAL_CLOCK.md:88-101,142-147`); batch `max(339,4·245+1)=981 → 1024`
(`:193-202`).

## 4. FIFO/service argument (`GALIL_CLOCK.md`, Galil-1978 route)

Symbols (`galil_clock.py:14-46`). `q` = instructions batched per source
transition (compilation granularity, `q=64`). `K` = stage factor `= 10`; every DP
stage of span `ell` costs `≤ K·ell` (`GALIL_CLOCK.md:17-28`). `M` = match
interval, `≥ 24K` rounded to a power of two, `= 256` (`:30-37`).
`α = move_slope = 8M+40+⌈8·296/q⌉` (`:62-67`).
`β = interval_overhead = 4M+2(6+⌈190/q⌉)+2` (`:69-73`).
`c = predictability = α+β = 3169`. `C_i` = tentative center in *place*
coordinates at the output for prefix length `i` (places interleave letters and
gaps: `place = 2·depth(l) − [¬gap]`, `galil_contracts.py:26-33`).
`k_i = max(C_i−i−1,0)`. `δ = C_{i+1}−C_i ≥ 0`. `d_i` = source transitions between
outputs `i−1` and `i`.

Chain (`GALIL_CLOCK.md:75-99`):
1. `d ≤ α·δ + β` (`galil_contracts.py:155`).
2. **L10 (move lemma)**: a move advancing `C` by `δ` has old radius `≤ 4δ`, copied
   window `m = 2·radius ≤ 8δ` (`:62-63`; asserted `4(C−C_move) > R_move−C_move−1`,
   `galil_contracts.py:110`).
3. **L11 (predictability)**: the next `k_i` answers are 0; a positive answer has
   `C_i = i`, `k_i = 0`; centers never decrease; gain `≥ δ−2` (`≥ −1` if `δ=0`), so
   `d/c ≤ max(δ,1)` (`:79-90`; `galil_contracts.py:147,158-159`).
4. Positive answer `i` ⇒ `k_{i−1}=0`, `d_i ≤ c` (`galil_contracts.py:156-157`).
5. FIFO service at `2c` transitions per input round: any busy interval `j..i`
   telescopes to `Σ d_t ≤ 2c(i−j)+c ≤ 2c(i−j+1)`, so the positive answer meets its
   deadline; an unproduced answer is reported `0` (`:92-101`).

**Contracts checked by `galil_contracts.py`** (each a proof obligation).
`dp_found` (`:77-85`): `h = min{step > lower : word[C−4step..C]` and
`word[C−2step..C]` both palindromes`}`, `R−C < 2h`. `main` (`:86-93`):
`lower ≤ R−C`, `3(R−C) ≤ 5·lower`, `rad = R−C`, `L = 2C−R`, `word[L..R]`
palindrome, and no `h ≤ min(lower,(C−1)/2)` whose palindromic block of width `2h`
ending at `C` reflection-extends to `R` (`:40-55`). `move` (`:95-103`):
`rem = |word[L+1..R]|`, `selected = R−(size−1)/2`, `size` = longest odd
palindromic suffix. `replay_start/return` (`:105-124`): `C = selected`,
`C_move < C ≤ R_move`, `R = L = C`, `rad = 0`, `replay = R_move−C`; on return
`R = RR`, `L = 2C−RR`, `rad = RR−C`, `len = 2(RR−C)+1`. `shift/shift_return`
(`:126-142`): `h>0`, `rem = h`, `ch.phase = 4`, `ch.lag = 0`; then `C' = C+h`,
`L' = L+2h`, `rad = R−C−h`, `ch.cycle = 2h`, `word[L+2h..R]` palindrome.
`output` (`:144-147`): `output = [word palindrome]`, `C ≥ |word|`,
`C = |word| ⟺ output`.

## 5. Heads and storage in the lowered version

14 heads (`gs_heads.py:12-15`): `Origin, OriginalEnd, End, Cut, Tail, A, B, P,
First, Reach, Walk, KP, KFirst, Second`; `BLIND = {KP,KFirst,Second}` may leave
the tape, cannot be read, cannot restore a data head (`:346-347,357`). The matcher
adds `U` and the test `available` (`gs_match_heads.py:11-12`); the flag worker
adds blind `Lower, Upper, Cursor` (`gs_flag_heads.py:12-13`).

Instructions: `move((head,±1)…)`, `copy dst src`, tests `equal/less/symbols`
(+`available`), outputs `border/flag/match`, `halt`. `unit_moves` reduces every
batch to one head, one unit (`gs_heads.py:249-264`). Tables: border 468 → **746**
unit states, matcher **457**, flags **768** (`GS_OVERLAP.md:66-68`,
`HANDOFF.md:129-131`).

Ordering uses signed unary head-pair differences, never pointer identity: a move
adjusts affected differences, a copy copies the row/column with sign reversal
(`GS_OVERLAP.md:71-76`). Liveness cuts this to 27/91 pairs, ≤18 live (border),
28/18 (matcher), 37/22 (flags) (`HANDOFF.md:141-143`).

Per round (`WINDOW_ROUNDS.md:41-74`) the input is split into blocks of fixed
length `B` exceeding the per-round movement bound; each head = block zipper +
queue of completed blocks + finite offset. Per old head the compiler prepares the
current block and its immediate left and right neighbours; all intermediate
moves/copies/reads use those three, and only the final zipper is stored. The last
block uses the live arrival endpoint and puts no live marker on the right stack.
`scaffold_window_workers.py` gives each live register a forward and a reverse view
over one raw cursor (reverse read = offset `−1`, reverse move = negated delta)
(`:131-138`). One round's flags form one packet, popped once per arrival
(`:78-86`). Head motions per round: 512 matcher + 1,024 flag instructions
(`GS_LOCAL_CLOCK.md:152-153`); the dual-flag local clock is 2,048+8,192+39 = 8,231
physical transitions (`:3-5`).

**No tape count exists anywhere in the docs.** The artifact targets an SCA /
ordinary PEG, not a multitape TM; the TM step is the missing ring (1)/(2b) of
`FORMALIZATION_SURVEY.md:274-289`.

## 6. Proof obligations

**Combinatorics on words.** L1 decomposition exists with both `s` bounds.
L2 safe-shift soundness (no occurrence skipped), both rules. L3 potential
strictly increases ⇒ linear work. L4 border/palindrome duality. L5 stages shrink
by `< 2/(k−1)`, next covers exactly the unexamined lengths. L6 second periods
grow by `≥ k−2`, last `≤ m/k` (`GS_LOCAL_CLOCK.md:58-59`,
`GS_OVERLAP.md:101-103`). L7 `p2 ≥ (k−2)p1`, `reach ≤ p2+p1`
(`GS_LOCAL_CLOCK.md:47-48`). L8 dyadic split. L9 two-view invariant and its
recurrence. L10 move inequality. L11 predictability + center monotonicity. L12
the chain lemmas behind "no small live period at main entry" —
`small_live_period` is only a *sufficient diagnostic witness*
(`galil_contracts.py:40-46`).

**Engineering invariants.** (1) ≤2 live stages; answers partition `n ≥ 2`
(`delayed_pal.py:110-114`). (2) Job release never overruns (`:47-48`). (3) Each job
emits exactly `W/2` flags (`:59-60`) and finishes before first use (`:79-80`).
(4) Matches arrive at their own frontier (`:71-73`). (5) Short-prefix verifier
deadline (`gs_events.py:196-198`, `gs_match_heads.py:50`). (6) No head crosses the
arrival frontier or the left end (`gs_match_heads.py:97-98,104-105`;
`gs_heads.py:343-344,357-358`). (7) Blind heads never restore data heads
(`gs_heads.py:346-347`). (8) Controller finiteness: locals freeze to
`bool/int/str/tuple` (`:202-207`); table closure terminates (`:267-315`).
(9) `unit_moves` and `minimize` preserve semantics (`:231-264`). (10) Counter
normalization: update history `< B/2` ⇒ remainder in `(−B,B)`, `Q` shifts by ≤1
(`WINDOW_ROUNDS.md:22-29`). (11) Sign stability when `B/2 > 2·movement bound`
(`:31-39`). (12) `B` exceeds per-round movement (`:44-46`). (13) One writer per
packet pool/node; pops cross packets (`:82-86`). (14) The FIFO inequality of §4.5
**and** representability of buffer/dispatcher as bounded local fields of an SCA
transition (`GALIL_CLOCK.md:100-104`).

## 7. Flagged as unverified or only tested

- `DELAYED_PAL.md:50-53` — 33,237 words agreed and all indexed deadlines held;
  "does not by itself certify the local schedule or final PEG."
- `GS_LOCAL_CLOCK.md:119-121` — "written loop-accounting arguments… not a
  mechanized proof"; `:145-147` observed maxima are evidence only; `:208-214`
  "not a proof by sampling".
- `GS_OVERLAP.md:88` — `/tmp/gs-heads.peg` accepts a loading/work *trace*; "not a
  claim that its start rule recognizes PAL". `:109-112` — indexed bounds are not a
  service bound for the head table; that schedule and the
  single-original-character SCA transition "remain to be completed".
- `GALIL_CLOCK.md:12-13` — arbitrary-length verification "remains separate from
  these tests"; `:102-104` — Python's `deque` scheduler does not satisfy the
  SCA-wrapper requirement.
- `WINDOW_ROUNDS.md:73-74` — the stream needs *consecutive* input; stage reset and
  frozen views need an adapter that must not count work markers as letters.
- `FPP_COST.md:54-56` — the graph cut "does not by itself prove the resource
  ledger."
- `HANDOFF.md:5-27`, `WINDOW_ROUNDS.md:195-210` — the artifact (13,248,052 rules)
  passed **79** unchanged-input checks only.
- `FORMALIZATION_SURVEY.md:274-289` — rings (1) "Galil's machine decides PAL on
  every prefix" and (2b) "constant delay → strict real time" have no Lean proof
  and no Mathlib support; §6 estimates 8–15k lines / 4–9 months.
- `HANDOFF.md:150-161` — closed dead ends (KMP fail-array, eertree, Manacher,
  two-way-in-`W·W`, `lps_halving`); do not re-enter.
