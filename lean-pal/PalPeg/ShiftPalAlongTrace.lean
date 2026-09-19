import PalPeg.CloseoutBundleRun
import PalPeg.CopyPhaseNoShift
import PalPeg.GalilPeriodUnion
import PalPeg.GalilRoundPeriod
import PalPeg.CloseoutShiftLocalFree

/-!
# `ShiftPal` を trace 形で（`hSP` の正しい形）

**2026-09-19（n238）**: 公理 `obligation_shiftPalResiduesAlongRun` は**不一致比較直前の
誕生 anchor 窓 1 本**になった。`ShiftPal` は `freshShiftLedger_of_chainW`（このファイル、窓の
周期構造）→ `shiftPal_of_freshShiftLedger` で出る。下の「残差 3 つ」の表と run/trace 形の
記述は n237 までの歴史。round 機構経由の `shiftPal_alongRun`／`shiftPal_alongTrace`／
`roundBundle_alongTrace` と `ShiftInv` 入口の組み立て（`shiftInv_of_watch_entry` 系）は
参照ゼロになり削除した（`ShiftEntryBoundary` の条件付き反証を参照）。

**2026-09-19（n112）**: 公理 `obligation_shiftPalAtScanStates` は

    ∀ w x, BigPack2MG7W … w x → ScanNR x → ShiftPal … w x.vm

という**一状態述語**の形で、`ShiftPal` の結論「chain の周期が入力語 `w` の本物の周期で
ある」という**履歴の事実**を要求していた。`BigPack2MG7W` の場を一次情報で全部展開すると、
chain の周期テープの中身と `w` を結びつける場が 1 つも無い（`w` に触れる場はヘッド、
chain に触れる場はカウンタ）。`hpack` が偽だったのと同じ欠陥で、**偽の疑いが濃い**
（機械検査した反証はまだ無いので `REFUTED` とは書かない）。

正しい形は run/trace 形。`CloseoutRoundBundle.RoundBundle` を trace に沿って運び、
各 scan 点で `shiftPal_of_roundBundle` が読み出す。起点は `st 1`——boot の 1 手目は
`init` で、`initVM` は `t.chain = .idle` を置くから（`AuxPack` は boot では偽なので
`st 0` からは始められない: `AuxPackNotAtBoot`）。

残差は 3 つで、どれも trace 形かつ狭い:

| 残差 | 形 |
|---|---|
| `AuxPack` | trace 形（`BranchSupply.auxPack_alongTrace_afterFirstStep` で**放電済み**） |
| `canRight right` | trace 形（`BranchSupply.canRightAtScanOrShift_alongTrace` で**放電済み**） |
| `H_readsShift` | trace 形（`RoundSegFromRun.readsShift_at_actual` が実状態で出す） |
| `H_freshShiftAtShiftEntry` | tick 形（shift 入口に狭めた版、`first_round` から） |
| `hfresh`（`periodOnly = false` 分岐） | 状態ごと |

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ShiftPalAlongTrace

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilFinalAssembly
open PalPeg.CloseoutPackRun2 PalPeg.CloseoutPackRun29 PalPeg.CloseoutPackRun37
open PalPeg.CloseoutRoundUnique PalPeg.CloseoutRoundBundle PalPeg.CloseoutBundleRun

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-! ## `periodOnly = false` 分岐の**空虚な半分**

`obligation_shiftPalAtFreshChainAlongTrace`（n132 の原子 3 本目）は
`periodOnly = false` の点で `ShiftPal` を要求する。そこで chain の相で場合分けすると:

* **`CopyOrBack`（lag 正）** — 比較の行き先に `shiftGuardVM` が立たないので **空虚**（下の定理）
* `.watch`（準備完了、まだ shift していない） — 本体。DP 正当性の帰結のはず

`shiftGuardVM` は `zero w.lag = true` を要求するが、copy/back から 1 手で生まれる watch は
lag をそのまま受け継ぐ（`backDone`）か `inc` する（`Outer.queued`）ので、誕生 chain の
正 lag が保たれて guard が落ちる（`CopyPhaseNoShift.tick_not_watch_or_posLag`）。 -/


/-! ## `periodOnly = false` ＋ watch の本体（残差を名前付きに絞った形）

n141 で数学の芯（`PalPeg.reshift_of_palAt_pair`）が完成したので、`ShiftPalAt` の
結論をその適用として書き、**残差を名前付き仮説として上に出す**。

残差は 5 つで、どれも「chain の履歴」か「台帳」:

| 残差 | 何か | 材料 |
|---|---|---|
| `hIn` / `hOut` | この watch の周期テープが DP の `Candidate` から来たという履歴 | `GalilPrepLeast.prep_watch_start_least` ＋ `CloseoutWatchPhase3.palAt_pair_of_candidate` |
| `hLo` (`2h ≤ r₀`) / `hHi` (`r₀ ≤ 4h`) | 半径と周期の台帳 | `GalilReplayBudgetProof.found_radius_le_two_period`（found 時 `radius ≤ 2h`）＋ 一致比較ぶんの伸び |
| `hCaught` | chain が周期 `2h` 分遅れて入力に追随している | `periodOnly = true` 側では `RoundScan.pred` が同じ形を持つ |

**入力側の添字化はここで済ませている**（`GalilRoundPeriod.right_read_index` ＋
`ScanInvariant.rightPos`）ので、`hCaught` は純粋に chain 側の事実。 -/

/-- **`periodOnly = false` ＋ watch での `ShiftPal` の結論。**  残差は上表の 5 つだけ。 -/
theorem shiftPalAt_fresh_of_candidate {w : List (Fin 2)} {s s' : GalilVM}
    {wch : GalilScaffoldChainWatch.State} {h r₀ : ℕ}
    (hChain : s'.chain = ChainVM.watch wch)
    (hGuard : shiftGuardVM s')
    (hRight : s'.right = right s.right)
    (hCan : canRight s.right)
    (hScanInv : ScanInvariant w (position s.center) r₀ s.left s.right)
    (hPeriod : periodLength wch = h)
    (hIn : Manacher.PalAt (encoded w) (position s.center - h) h)
    (hLeft : PeriodOn (encoded w) (2 * h) (position s.center - r₀) (position s.center))
    (hPos : 0 < h) (hLo : 2 * h ≤ r₀)
    (hEnd : position s.center + r₀ + 1 < (encoded w).length)
    (hCaught : (encoded w)[position s.center + r₀ + 1 - 2 * h]? =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus) :
    1 ≤ periodLength wch ∧ periodLength wch ≤ r₀ + 1 ∧
      Manacher.PalAt (encoded w) (position s.center + periodLength wch)
        (r₀ + 1 - periodLength wch) := by
  obtain ⟨wg, hwg, -, -, -, -, hsym⟩ := hGuard
  have hwe : wg = wch := by rw [hChain] at hwg; cases hwg; rfl
  rw [hwe] at hsym
  have hread : GalilScaffoldInputHead.read (right s.right) =
      (encoded w)[position s.center + r₀ + 1]? := by
    rw [PalPeg.GalilRoundPeriod.right_read_index s.right w hScanInv.rightRep
      hScanInv.rightPresent hCan, hScanInv.rightPos]
  have hsym' : GalilScaffoldChainConsume.symbol wch.machine.control.period.focus =
      (encoded w)[position s.center + r₀ + 1]? := by
    rw [← hread, ← hRight]; exact hsym
  have hpredIdx : (encoded w)[position s.center + r₀ + 1]? =
      (encoded w)[position s.center + r₀ + 1 - 2 * h]? := by
    rw [← hsym']; exact hCaught.symm
  refine ⟨by omega, by omega, ?_⟩
  rw [hPeriod]
  exact PalPeg.reshift_of_palAt_period (encoded w) (position s.center) h r₀
    hIn hScanInv.palindrome hPos hLo hEnd hLeft hpredIdx

#print axioms shiftPalAt_fresh_of_candidate

/-! ## `ChainW` の `.watch` 枝から `ShiftInv` の 23 場へ

shift 入口で run 層が手にしているのは `GalilReplaySpan.ChainW … (.watch w)`
（`CloseoutWatchRound42.LandingData` 由来）で、その窓 `BlockOn … (cen+1) E` は
**走査の右ヘッド `E = cen + R` までしか届かない**。shift 判定はまさにその右端で起きるので、
「右へ 1 歩の余裕」を要求する `GalilReplaySpan.coreX_next` / `coreX_good` は使えず、
窓に無い 2 事実——右ヘッドの読み（`shiftGuardVM` の最後の連言が供給）と
中心の記号 `x[cen] = cc`（DP の `Candidate` 由来）——を外から受け取る。
-/

/-- **`BlockOn` は周期 `2(|xs|+1)` そのもの。**  入力の `[anchor, E]` が長さ `2h` の
ブロックの巡回である、という言明を `PeriodOn` の形に直す。 -/
theorem periodOn_of_blockOn {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor E : ℕ} (h : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E) :
    PeriodOn (encoded raw) (2 * (xs.length + 1)) anchor E := by
  intro i hi hb
  have h1 := h (i - anchor) (by omega)
  have h2 := h (i - anchor + 2 * (xs.length + 1)) (by omega)
  rw [show anchor + (i - anchor) = i from by omega] at h1
  rw [show anchor + (i - anchor + 2 * (xs.length + 1))
      = i + 2 * (xs.length + 1) from by omega] at h2
  rw [h1, h2, Nat.add_mod_right]

#print axioms periodOn_of_blockOn

/-- **`bounce` は `b` を中心に対称。**  `bounce cc b xs = xs ++ [b] ++ xs.reverse ++ [cc]` の
添字 `|xs| ∓ i`（`i ≤ |xs|`）は同じ記号。 -/
theorem bounce_getElem?_symm (cc b : Fin 3) (xs : List (Fin 3)) (i : ℕ) (hi : i ≤ xs.length) :
    (GalilScaffoldChainSweep.bounce cc b xs)[xs.length - i]?
      = (GalilScaffoldChainSweep.bounce cc b xs)[xs.length + i]? := by
  unfold GalilScaffoldChainSweep.bounce
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [List.getElem?_append_left (l₁ := xs ++ [b]) (l₂ := xs.reverse ++ [cc])
        (by simp only [List.length_append, List.length_singleton]; omega),
      List.getElem?_append_left (l₁ := xs) (l₂ := [b]) (by omega),
      List.getElem?_append_right (l₁ := xs ++ [b]) (l₂ := xs.reverse ++ [cc])
        (by simp only [List.length_append, List.length_singleton]; omega),
      List.getElem?_append_left (l₁ := xs.reverse) (l₂ := [cc])
        (by simp only [List.length_append, List.length_singleton, List.length_reverse]; omega),
      List.getElem?_reverse
        (by simp only [List.length_append, List.length_singleton]; omega)]
    congr 1
    simp only [List.length_append, List.length_singleton]
    omega

#print axioms bounce_getElem?_symm

/-- **ブロックの末尾 `cc` は窓の中。**  `bounce cc b xs` の最後の記号は `cc` なので、
窓が 1 周期ぶん届いていれば `x[cen + 2h] = cc`。 -/
theorem block_last_of_blockOn {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {cen E : ℕ} (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen + 1) E)
    (hE : cen + 2 * (xs.length + 1) ≤ E) :
    (encoded raw)[cen + 2 * (xs.length + 1)]? = some cc := by
  have h2 := hblk (2 * (xs.length + 1) - 1) (by omega)
  rw [show cen + 1 + (2 * (xs.length + 1) - 1) = cen + 2 * (xs.length + 1) from by omega,
    Nat.mod_eq_of_lt (by omega)] at h2
  rw [h2]
  unfold GalilScaffoldChainSweep.bounce
  rw [show 2 * (xs.length + 1) - 1 = ((xs ++ [b]) ++ xs.reverse).length from by
      simp only [List.length_append, List.length_singleton, List.length_reverse]; omega,
    ← List.append_assoc, List.getElem?_concat_length]

#print axioms block_last_of_blockOn

/-- **ブロックは `cen + h` を中心に半径 `h` の回文。**  `i < h` は 1 ブロックの内側で
`bounce` の対称性（`bounce_getElem?_symm`）、`i = h` は `x[cen] = cc = x[cen + 2h]`。 -/
theorem palAt_block_of_centre {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {cen E : ℕ} (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen + 1) E)
    (hcentre : (encoded raw)[cen]? = some cc)
    (hE : cen + 2 * (xs.length + 1) ≤ E) (hlen : E < (encoded raw).length) :
    Manacher.PalAt (encoded raw) (cen + (xs.length + 1)) (xs.length + 1) := by
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  rcases Nat.lt_or_ge i (xs.length + 1) with hlt | hge
  · have h1 := hblk (xs.length - i) (by omega)
    have h2 := hblk (xs.length + i) (by omega)
    rw [show cen + 1 + (xs.length - i) = cen + (xs.length + 1) - i from by omega] at h1
    rw [show cen + 1 + (xs.length + i) = cen + (xs.length + 1) + i from by omega] at h2
    rw [h1, h2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact bounce_getElem?_symm cc b xs i (by omega)
  · have hi' : i = xs.length + 1 := by omega
    subst hi'
    rw [show cen + (xs.length + 1) - (xs.length + 1) = cen from by omega,
      show cen + (xs.length + 1) + (xs.length + 1) = cen + 2 * (xs.length + 1) from by omega,
      hcentre, block_last_of_blockOn hblk hE]

#print axioms palAt_block_of_centre


/-- **回文の鏡映。**  `C` を中心とする半径 `R` の回文の内側で、`C + d` を中心とする半径 `r` の
回文は `C − d` を中心とする半径 `r` の回文に写る。 -/
theorem palAt_mirror {α : Type} {x : List α} {C R d r : ℕ}
    (hpal : Manacher.PalAt x C R) (hin : Manacher.PalAt x (C + d) r) (hd : d + r ≤ R) :
    Manacher.PalAt x (C - d) r := by
  have hRC : R ≤ C := hpal.1
  have hlen : C + R < x.length := hpal.2.1
  refine ⟨by omega, by omega, ?_⟩
  intro i hi
  have h1 : x[C - d - i]? = x[C + d + i]? := by
    have := Manacher.mirror_getElem? hpal (p := C - d - i) (by omega) (by omega)
    rwa [show 2 * C - (C - d - i) = C + d + i from by omega] at this
  have h2 : x[C - d + i]? = x[C + d - i]? := by
    have := Manacher.mirror_getElem? hpal (p := C - d + i) (by omega) (by omega)
    rwa [show 2 * C - (C - d + i) = C + d - i from by omega] at this
  rw [h1, h2, hin.2.2 i hi]

#print axioms palAt_mirror

/-- **周期区間を左へ 1 つ伸ばす。** -/
theorem periodOn_extend_left {α : Type} {x : List α} {p a b : ℕ}
    (h : PeriodOn x p (a + 1) b) (ha : x[a]? = x[a + p]?) : PeriodOn x p a b := by
  intro i hi hb
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · exact ha
  · exact h i hlt hb

#print axioms periodOn_extend_left

/-- **`CoreX` の shift 越え版。**  `GalilReplaySpan.CoreX` は制御全体を `run (ready cc xs b) pre`
に等置するが、`chainShiftOne` は sweep カウンタ（distance/boundary/last）を `dec` するので
shift 以降は成り立たない。予測記号に要るのは period テープと進行方向だけ
（`GalilScaffoldChainPrediction.SamePrediction`——「カウンタを調整した継続は元の予測器の
位相を保つ」）。`broken = false` は watch している chain の不変量（`take`/`immediate` は
`Good` を持参、不一致は `.broken` へ）。 -/
def CoreP (raw : List (Fin 2)) (cc b : Fin 3) (xs : List (Fin 3)) (anchor : ℕ)
    (m : GalilScaffoldChainVerifier.State) : Prop :=
  GalilBranchInvariants.OnBlock m.control.period ∧
    GalilScaffoldInputTrace.Represents m.verifier.head raw ∧ m.verifier.head.focus ≠ none ∧
    m.control.broken = false ∧
    ∃ pre : List (Fin 3),
      GalilScaffoldChainPrediction.SamePrediction m.control
        (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cc xs b) pre) ∧
      (GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cc xs b) pre).broken = false ∧
      position m.verifier + 1 = anchor + pre.length

theorem coreP_of_coreX {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {m : GalilScaffoldChainVerifier.State}
    (h : PalPeg.GalilReplaySpan.CoreX raw cc b xs anchor m) : CoreP raw cc b xs anchor m := by
  obtain ⟨hblk, hrep, hpres, pre, hctl, hbr0, hidx⟩ := h
  exact ⟨hblk, hrep, hpres, by rw [hctl]; exact hbr0, pre, by rw [hctl]; exact ⟨rfl, rfl⟩,
    hbr0, hidx⟩

#print axioms coreP_of_coreX

/-- **`CoreP` の予測記号、窓の右端でも。**  `GalilReplaySpan.coreX_next` は `canRight` を
出すために右に 1 歩の余裕（`position ver + 1 < |encoded raw|`）を要求するが、**予測記号
そのもの**は `SamePrediction` と `GalilScaffoldChainPrediction.continued_prediction` だけで決まる。 -/
theorem symbol_of_coreP {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {m : GalilScaffoldChainVerifier.State}
    (hcore : CoreP raw cc b xs anchor m) :
    GalilScaffoldChainConsume.symbol m.control.period.focus
      = (GalilScaffoldChainSweep.bounce cc b xs)[(position m.verifier + 1 - anchor) %
          (2 * (xs.length + 1))]? := by
  obtain ⟨-, -, -, hbr, pre, hsame, hbr0, hidx⟩ := hcore
  have hpred := GalilScaffoldChainPrediction.continued_prediction cc b xs pre [] m.control hsame
    (by rw [hbr, hbr0]) (by simpa [GalilScaffoldChainSweep.run] using hbr)
  simp only [List.length_nil, Nat.add_zero, GalilScaffoldChainSweep.run] at hpred
  rw [hpred, show position m.verifier + 1 - anchor = pre.length from by omega]

#print axioms symbol_of_coreP

/-- **窓を verifier の 1 つ先まで伸ばす。**  `symbol_of_coreP` が焦点記号を `bounce` の添字で
名指し、guard（または `Good`）がそれを次の読みと一致させるので `BlockOn` が 1 つ伸びる。 -/
theorem blockOn_succ_of_symbol {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor E : ℕ} {w : GalilScaffoldChainWatch.State}
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E)
    (hcore : CoreP raw cc b xs anchor w.machine)
    (hver : position w.machine.verifier = E)
    (hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
      = (encoded raw)[E + 1]?) :
    PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor (E + 1) := by
  intro j hj
  rcases Nat.lt_or_ge (anchor + j) (E + 1) with hlt | hge
  · exact hblk j (by omega)
  · have hj' : anchor + j = E + 1 := by omega
    rw [hj', ← hsym, symbol_of_coreP hcore, hver, show E + 1 - anchor = j from by omega]

#print axioms blockOn_succ_of_symbol

/-- **`run` は period テープの長さを変えない**（`OnBlock` 上で）。 -/
theorem cells_run {s : GalilScaffoldChainConsume.State} (pre : List (Fin 3))
    (hb : GalilBranchInvariants.OnBlock s.period) :
    PalPeg.GalilShiftH.cells (GalilScaffoldChainSweep.run s pre).period
        = PalPeg.GalilShiftH.cells s.period ∧
      GalilBranchInvariants.OnBlock (GalilScaffoldChainSweep.run s pre).period := by
  induction pre generalizing s with
  | nil => exact ⟨rfl, hb⟩
  | cons a pre ih =>
    obtain ⟨h1, h2⟩ := ih (GalilBranchInvariants.onBlock_consume s (some a) hb)
    exact ⟨h1.trans (PalPeg.GalilShiftH.cells_consume s (some a) hb), h2⟩

#print axioms cells_run

/-- **`CoreP` の chain の半周期は `|xs| + 1`。**  `ready cc xs b` のテープは `|xs| + 2` セルで、
`run` はセル数を変えず、`SamePrediction` は period テープを等置する。 -/
theorem periodLength_of_coreP {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor : ℕ} {w : GalilScaffoldChainWatch.State}
    (hcore : CoreP raw cc b xs anchor w.machine) :
    periodLength w = xs.length + 1 := by
  obtain ⟨-, -, -, -, pre, hsame, -, -⟩ := hcore
  have hrun := (cells_run pre (GalilBranchInvariants.onBlock_ready cc b xs)).1
  have hready : PalPeg.GalilShiftH.cells (GalilScaffoldChainConsume.ready cc xs b).period
      = xs.length + 2 := by
    show PalPeg.GalilShiftH.cells (GalilScaffoldChainPeriod.moveRight
      ⟨[], GalilScaffoldChainPeriod.Token.first cc,
        xs.map GalilScaffoldChainPeriod.Token.plain ++ [GalilScaffoldChainPeriod.Token.last b]⟩)
      = xs.length + 2
    rw [PalPeg.GalilShiftH.cells_moveRight _ (by simp)]
    simp only [PalPeg.GalilShiftH.cells, List.length_nil, List.length_append, List.length_map,
      List.length_singleton]
    omega
  have hcells := PalPeg.GalilShiftH.periodLength_succ_eq_cells w
  rw [hsame.1, hrun, hready] at hcells
  omega

#print axioms periodLength_of_coreP

/-- **一致する consume は `CoreP` を保つ**（`GalilReplaySpan.coreX_consume` の `SamePrediction` 版）。 -/
theorem coreP_consume {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hc : CoreP raw cc b xs anchor w.machine) (hg : GalilScaffoldChainWatch.Good w) :
    CoreP raw cc b xs anchor (GalilScaffoldChainVerifier.consume w.machine) := by
  obtain ⟨hblk, hrep, hpres, hbr, pre, hsame, hbr0, hidx⟩ := hc
  obtain ⟨hcan, a, hsym, hread⟩ := hg
  have hleft := (represented_position _ raw hrep hpres).1
  have hctl' : (GalilScaffoldChainVerifier.consume w.machine).control =
      GalilScaffoldChainConsume.consume w.machine.control (some a) := by
    show GalilScaffoldChainConsume.consume w.machine.control
      (read (GalilScaffoldChainVerifier.right w.machine.verifier)) = _
    rw [hread]
  refine ⟨GalilBranchInvariants.onBlock_verifier_consume _ hblk, right_word _ raw hrep hcan,
    right_present _ raw hrep hpres hcan, ?_, pre ++ [a], ?_, ?_, ?_⟩
  · rw [hctl']; exact consume_keeps_unbroken _ a hsym hbr
  · rw [hctl', GalilScaffoldChainSweep.run_append]
    exact GalilScaffoldChainPrediction.consume_same_prediction hsame (some a)
  · rw [GalilScaffoldChainSweep.run_append]
    show (GalilScaffoldChainConsume.consume _ (some a)).broken = false
    exact consume_keeps_unbroken _ a (by rw [← hsame.1]; exact hsym) hbr0
  · show position (GalilScaffoldChainVerifier.right w.machine.verifier) + 1 = _
    rw [right_position _ hcan hleft, List.length_append, List.length_singleton]
    omega

#print axioms coreP_consume

/-- **shift の 1 歩は `CoreP` を保つ**——`chainShiftOne` は sweep カウンタと margin しか触らない。 -/
theorem coreP_chainShiftOne {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)} {anchor : ℕ}
    {w : GalilScaffoldChainWatch.State}
    (hc : CoreP raw cc b xs anchor w.machine) :
    CoreP raw cc b xs anchor (chainShiftOne w).machine := hc

#print axioms coreP_chainShiftOne





/-- **(NAMED) 準備直後の watch の台帳。**  `shiftPalAt_fresh_of_candidate` の 5 残差を
1 つの場にまとめたもの。`ShiftPal` の `periodOnly = false` 分岐に必要な全部で、
3 種類しかない（n144）:

* `hIn` / `hOut` — period テープの**中身**（DP の `Candidate` 由来）
* `0 < h` / `2h ≤ r₀` / `r₀ ≤ 4h` / `hEnd` — 半径と周期の**大小**
* 最後の等式 — period テープの**位相**（`RoundScan.pred` の `periodOnly = false` 版） -/
def FreshShiftLedger (w : List (Fin 2)) (s s' : GalilVM) : Prop :=
  shiftGuardVM s' →
  ∀ wch : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch wch →
    ∀ r₀ : ℕ, ScanInvariant w (position s.center) r₀ s.left s.right →
      Manacher.PalAt (encoded w) (position s.center - periodLength wch) (periodLength wch) ∧
      PeriodOn (encoded w) (2 * periodLength wch)
        (position s.center - r₀) (position s.center) ∧
      0 < periodLength wch ∧
      2 * periodLength wch ≤ r₀ ∧
      (encoded w)[position s.center + r₀ + 1 - 2 * periodLength wch]? =
        (encoded w)[position s.center + r₀ + 1]?

/-- **半径 `h` の回文は周期 `2h` で `h` だけ右へ写る。** -/
theorem palAt_shift_half {α : Type} {x : List α} {c h : ℕ}
    (hpal : Manacher.PalAt x c h) (hper : PeriodOn x (2 * h) (c - h) (c + h + h))
    (hlen : c + h + h < x.length) : Manacher.PalAt x (c + h) h := by
  have hhc : h ≤ c := hpal.1
  refine ⟨by omega, hlen, ?_⟩
  intro i hi
  have h1 : x[c + h + i]? = x[c - h + i]? := by
    have := hper (c - h + i) (by omega) (by omega)
    rw [show c - h + i + 2 * h = c + h + i from by omega] at this
    exact this.symm
  have h2 : x[c - h + i]? = x[c + h - i]? := by
    have := hpal.2.2 (h - i) (by omega)
    rw [show c - (h - i) = c - h + i from by omega,
      show c + (h - i) = c + h - i from by omega] at this
    exact this
  rw [h1, h2]

#print axioms palAt_shift_half

/-- **誕生中心から `h` 刻みの全中心はブロック回文。**  `j = 0` は `palAt_block_of_centre`、
以降は `palAt_shift_half`（周期は中心記号で `cen` まで左へ伸ばした窓 `periodOn_extend_left`）。 -/
theorem palAt_block_periodic {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {cen E : ℕ} (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen + 1) E)
    (hcentre : (encoded raw)[cen]? = some cc) (hlen : E < (encoded raw).length) :
    ∀ j, cen + j * (xs.length + 1) + 2 * (xs.length + 1) ≤ E →
      Manacher.PalAt (encoded raw) (cen + j * (xs.length + 1) + (xs.length + 1))
        (xs.length + 1) := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [Nat.zero_mul, Nat.add_zero] at hj ⊢
    exact palAt_block_of_centre hblk hcentre hj hlen
  | succ j ih =>
    intro hj
    rw [add_one_mul] at hj ⊢
    have hper : PeriodOn (encoded raw) (2 * (xs.length + 1)) cen E :=
      periodOn_extend_left (periodOn_of_blockOn hblk)
        (by rw [hcentre, block_last_of_blockOn hblk (by omega)])
    have hprev := ih (by omega)
    rw [show cen + (j * (xs.length + 1) + (xs.length + 1)) + (xs.length + 1)
        = cen + j * (xs.length + 1) + (xs.length + 1) + (xs.length + 1) from by omega]
    exact palAt_shift_half hprev (hper.mono (by omega) (by omega)) (by omega)

#print axioms palAt_block_periodic

/-- **shift を越えて生き残る watch chain の窓データ。**  verifier ＋ lag が右ヘッド `R`、
窓は **verifier が消費した接頭辞**（`BlockOn … (cen₀+1) (position ver)`）、制御は誕生中心
`cen₀` に anchor した `CoreP`。`GalilReplaySpan.ChainW` の `.watch` 枝の最初の 3 場と同型だが、
margin 等式と予算は持たず（`chainShiftOne` が `margin` を `dec` するので誕生中心を `C` にした
`ChainW` は最初の shift 以降は偽、n240）、窓の終端を verifier の位置に固定し（lag > 0 の間は
窓が右ヘッドに追いつかない、n241）、制御の等式を `SamePrediction` に弱める（`chainShiftOne` が
sweep カウンタを `dec` する、n242）。guard 点（lag ゼロ）では verifier ＝ 右ヘッド。 -/
def WatchWindow (raw : List (Fin 2)) (cen₀ R : ℕ) (cc b : Fin 3) (xs : List (Fin 3)) :
    ChainVM → Prop
  | ChainVM.watch w =>
      PalPeg.GalilReplayGeneral2.LagAt w.lag w.machine.verifier R ∧
      PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen₀ + 1) (position w.machine.verifier) ∧
      CoreP raw cc b xs (cen₀ + 1) w.machine
  | _ => False

/-- `ChainW` の `.watch` 枝から（誕生中心が `C`、窓が verifier まで届くとき）。 -/
theorem watchWindow_of_chainW {raw : List (Fin 2)} {cen₀ E R bud : ℕ} {lim : Bool}
    {cc b : Fin 3} {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State}
    (h : PalPeg.GalilReplaySpan.ChainW raw cen₀ E R bud lim cc b xs (ChainVM.watch w))
    (hE : position w.machine.verifier ≤ E) :
    WatchWindow raw cen₀ R cc b xs (ChainVM.watch w) := by
  obtain ⟨hlag, hblk, hcore, -, -, -⟩ := h
  exact ⟨hlag, fun j hj => hblk j (le_trans hj hE), coreP_of_coreX hcore⟩

#print axioms watchWindow_of_chainW

/-- **`Good` を持つ consume は窓を 1 つ伸ばし `CoreP` を保つ。**  `take`（background）と
`immediate`（一致比較・shift 入口）の共通部分。 -/
theorem window_consume_of_good {raw : List (Fin 2)} {cen₀ : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State}
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen₀ + 1) (position w.machine.verifier))
    (hcore : CoreP raw cc b xs (cen₀ + 1) w.machine) (hg : GalilScaffoldChainWatch.Good w) :
    position (GalilScaffoldChainVerifier.consume w.machine).verifier
        = position w.machine.verifier + 1 ∧
      PalPeg.GalilReplaySpan.BlockOn raw cc b xs (cen₀ + 1)
        (position (GalilScaffoldChainVerifier.consume w.machine).verifier) ∧
      CoreP raw cc b xs (cen₀ + 1) (GalilScaffoldChainVerifier.consume w.machine) := by
  have hcan : GalilScaffoldChainVerifier.canRight w.machine.verifier := hg.1
  obtain ⟨a, hsa, hra⟩ := hg.2
  have hl0 : 0 < w.machine.verifier.head.left.length :=
    (represented_position _ raw hcore.2.1 hcore.2.2.1).1
  have hpc : position (GalilScaffoldChainVerifier.consume w.machine).verifier
      = position w.machine.verifier + 1 :=
    right_position _ hcan hl0
  have hread : read (GalilScaffoldChainVerifier.right w.machine.verifier)
      = (encoded raw)[position w.machine.verifier + 1]? := by
    rw [represented_read _ raw (right_word _ raw hcore.2.1 hcan)
      (right_present _ raw hcore.2.1 hcore.2.2.1 hcan), right_position _ hcan hl0]
  have hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus
      = (encoded raw)[position w.machine.verifier + 1]? := by
    rw [← hread]; exact hsa.trans hra.symm
  refine ⟨hpc, ?_, coreP_consume hcore hg⟩
  rw [hpc]
  exact blockOn_succ_of_symbol hblk hcore rfl hsym

#print axioms window_consume_of_good

/-- **1 background 歩（`Internal`）越しの窓。**  `idle` は不変、`take` は verifier が 1 つ右へ、
lag が 1 つ減り、窓は `take` が持参する `Good` で 1 つ伸びる。 -/
theorem watchWindow_step {raw : List (Fin 2)} {cen₀ R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w w' : GalilScaffoldChainWatch.State}
    (hw : WatchWindow raw cen₀ R cc b xs (ChainVM.watch w))
    (hi : GalilScaffoldChainWatch.Internal w w') :
    WatchWindow raw cen₀ R cc b xs (ChainVM.watch w') := by
  obtain ⟨hlag, hblk, hcore⟩ := hw
  rcases w with ⟨mach, ⟨ps, ns⟩, margin⟩
  obtain ⟨hneg, hpos⟩ := hlag
  simp only at hneg hpos hblk hcore
  subst hneg
  cases hi with
  | idle _ => exact ⟨⟨rfl, hpos⟩, hblk, hcore⟩
  | take hp hg =>
    cases ps with
    | nil => simp [GalilScaffoldCounter.positive] at hp
    | cons u ps =>
      obtain ⟨hpc, hblk', hcore'⟩ :=
        window_consume_of_good (w := ⟨mach, ⟨u :: ps, []⟩, margin⟩) hblk hcore hg
      refine ⟨⟨rfl, ?_⟩, hblk', hcore'⟩
      show position (GalilScaffoldChainVerifier.consume mach).verifier
        + (GalilScaffoldCounter.dec ⟨u :: ps, []⟩).pos.length = R
      rw [hpc]
      simp [GalilScaffoldCounter.dec] at hpos ⊢
      omega

#print axioms watchWindow_step

/-- **一致比較（`ChainMatched.watch`、`Outer … true`）越しの窓。**  右ヘッドが 1 つ進む:
`queued` は lag +1（`lagAt_inc`）、`immediate` は `Good` 持参で consume。 -/
theorem watchWindow_outer {raw : List (Fin 2)} {cen₀ R : ℕ} {cc b : Fin 3} {xs : List (Fin 3)}
    {w w' : GalilScaffoldChainWatch.State}
    (hw : WatchWindow raw cen₀ R cc b xs (ChainVM.watch w))
    (ho : GalilScaffoldChainWatch.Outer w true w') :
    WatchWindow raw cen₀ (R + 1) cc b xs (ChainVM.watch w') := by
  obtain ⟨hlag, hblk, hcore⟩ := hw
  cases ho with
  | queued _ => exact ⟨PalPeg.GalilReplayGeneral2.lagAt_inc hlag, hblk, hcore⟩
  | immediate _ hg =>
    obtain ⟨hpc, hblk', hcore'⟩ := window_consume_of_good hblk hcore hg
    refine ⟨⟨hlag.1, ?_⟩, hblk', hcore'⟩
    show position (GalilScaffoldChainVerifier.consume w.machine).verifier + w.lag.pos.length = R + 1
    rw [hpc]
    have := hlag.2
    omega

#print axioms watchWindow_outer

/-- **shift の 1 歩（`chainShiftOne`）は窓を変えない。** -/
theorem watchWindow_shiftOne {raw : List (Fin 2)} {cen₀ R : ℕ} {cc b : Fin 3}
    {xs : List (Fin 3)} {w : GalilScaffoldChainWatch.State}
    (hw : WatchWindow raw cen₀ R cc b xs (ChainVM.watch w)) :
    WatchWindow raw cen₀ R cc b xs (ChainVM.watch (chainShiftOne w)) := by
  obtain ⟨hlag, hblk, hcore⟩ := hw
  exact ⟨hlag, hblk, coreP_chainShiftOne hcore⟩

#print axioms watchWindow_shiftOne

/-- **`FreshShiftLedger` の producer——誕生中心に anchor した窓から、どの shift 入口でも。**

入力は run 層が不一致比較の直前に持つ一次事実の、右ヘッド側だけ:

* `hW` — 誕生中心 `cen₀` に anchor した窓 `WatchWindow`（比較後の chain `s'.chain`、窓は
  現在の右ヘッド `cen + R` まで）
* `hk` — 現在の中心 `cen = cen₀ + k·h`（shift は中心を `h` ずつ右へ動かす）
* `hR` — 直前の右ヘッド `position s.right = cen + R`（`ScanInvariant` の `r₀` を `R` に固定）
* 比較後の右ヘッド 3 事実（`s'.right = right s.right`）
* `hcentre` — 誕生中心の記号 `x[cen₀] = cc`（窓に無い唯一の静的事実）
* `hsize` — `2h ≤ R`（新鮮な shift では margin から `4h ≤ R`、以降は round の半径）

左端の不一致でも成り立つ（5 成分とも語レベルで左端に触れない）。 -/
theorem freshShiftLedger_of_chainW {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {cen₀ k cen R : ℕ} {s s' : GalilVM}
    (hcen : position s.center = cen)
    (hk : cen = cen₀ + k * (xs.length + 1))
    (hW : WatchWindow raw cen₀ (cen + R) cc b xs s'.chain)
    (hR : position s.right = cen + R)
    (hrightRep : GalilScaffoldInputTrace.Represents s'.right.head raw)
    (hrightPresent : s'.right.head.focus ≠ none)
    (hrightPos : position s'.right = cen + R + 1)
    (hcentre : (encoded raw)[cen₀]? = some cc)
    (hsize : 2 * (xs.length + 1) ≤ R) :
    FreshShiftLedger raw s s' := by
  intro hguard wch hchain r₀ hscan
  have hr₀ : r₀ = R := by have := hscan.rightPos; omega
  rw [hr₀] at hscan ⊢
  have hpal : Manacher.PalAt (encoded raw) cen R := by rw [← hcen]; exact hscan.palindrome
  rw [hchain] at hW
  obtain ⟨hlag, hblk, hcore⟩ := hW
  obtain ⟨w', hw', hlagZ, -, -, -, hsym⟩ := hguard
  rw [hchain] at hw'
  have hww : wch = w' := ChainVM.watch.inj hw'
  subst hww
  have hpl : periodLength wch = xs.length + 1 := periodLength_of_coreP hcore
  rw [hpl, hcen]
  -- the verifier sits on the previous right head
  have hposNil : wch.lag.pos = [] := by
    have hz : (wch.lag.pos.isEmpty && wch.lag.neg.isEmpty) = true := hlagZ
    cases hp : wch.lag.pos with
    | nil => rfl
    | cons _ _ => simp [hp] at hz
  have hver : position wch.machine.verifier = cen + R := by
    have hl := hlag.2
    rw [hposNil, List.length_nil, Nat.add_zero] at hl
    exact hl
  rw [hver] at hblk
  -- the read at the new right head extends the window by one
  have hreadR : read s'.right = (encoded raw)[cen + R + 1]? := by
    rw [represented_read s'.right raw hrightRep hrightPresent, hrightPos]
  have hreadRne : read s'.right ≠ none := fun hnone =>
    hrightPresent (Option.map_eq_none_iff.1 hnone)
  have hrightLt : cen + R + 1 < (encoded raw).length := by
    rcases Nat.lt_or_ge (cen + R + 1) (encoded raw).length with hlt | hge
    · exact hlt
    · exact absurd (hreadR.trans (List.getElem?_eq_none_iff.2 hge)) hreadRne
  have hblk' := blockOn_succ_of_symbol hblk hcore hver (hsym.trans hreadR)
  -- the window, extended to the birth centre by its symbol
  have hper : PeriodOn (encoded raw) (2 * (xs.length + 1)) cen₀ (cen + R + 1) :=
    periodOn_extend_left (periodOn_of_blockOn hblk')
      (by rw [hcentre, block_last_of_blockOn hblk' (by omega)])
  have hblock : Manacher.PalAt (encoded raw) (cen + (xs.length + 1)) (xs.length + 1) := by
    have := palAt_block_periodic hblk' hcentre hrightLt k (by omega)
    rwa [← hk] at this
  refine ⟨?_, ?_, by omega, by omega, ?_⟩
  · exact palAt_mirror hpal hblock (by omega)
  · exact PalPeg.periodOn_mirror hpal (by omega) (hper.mono (by omega) (by omega))
  · have hp := periodOn_of_blockOn hblk' (cen + R + 1 - 2 * (xs.length + 1)) (by omega)
      (by omega)
    rwa [show cen + R + 1 - 2 * (xs.length + 1) + 2 * (xs.length + 1) = cen + R + 1
      from by omega] at hp

#print axioms freshShiftLedger_of_chainW

/-- **`ShiftPal` を `FreshShiftLedger` 1 つから。**  比較の行き先の右ヘッドが
`right s.right` であることは `compareFound` の `hvr` から出る（`afterBirth` /
`afterCompare` / `afterMismatch` はどれも右ヘッドを `vs.right` にする）。 -/
theorem shiftPal_of_freshShiftLedger {w : List (Fin 2)} {s : GalilVM}
    (hCan : canRight s.right)
    (hLedger : ∀ s' : GalilVM,
      compareFound (PofC centre place entry w) q first s s' →
      ¬ (galilFrameS (PofC centre place entry w) q first).matched s' →
      FreshShiftLedger w s s') :
    ShiftPal centre place entry q first w s := by
  intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
  obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchainAt, hteq⟩ :
    compareFound (PofC centre place entry w) q first s s' := id hCompare
  have hRight : s'.right = right s.right := by
    rw [hteq, afterBirth_right]
    cases a with
    | false => rw [if_neg (by simp)]; exact hvr
    | true => rw [if_pos rfl]; exact hvr
  obtain ⟨hIn, hLeft, hPos, hLo, hCaught'⟩ :=
    hLedger s' hCompare hNotMatched hGuard wch hChain r₀ hScanInv
  -- the frontier is inside the encoded word: the right head can still move.
  have hrp : position (right s.right) = position s.right + 1 :=
    right_position s.right hCan
      (represented_position s.right.head w hScanInv.rightRep hScanInv.rightPresent).1
  have hEnd : position s.center + r₀ + 1 < (encoded w).length := by
    have hpos := represented_position (right s.right).head w
      (right_word s.right w hScanInv.rightRep hCan)
      (right_present s.right w hScanInv.rightRep hScanInv.rightPresent hCan)
    have hb : position (right s.right) < (encoded w).length := by
      simp only [encoded, List.length_append, List.length_singleton, pairs_length]
      unfold position
      split <;> omega
    rw [← hScanInv.rightPos, ← hrp]; exact hb
  -- the frontier symbol: the shift guard reads it off the right head, and the
  -- scan invariant places that head at `centre + r₀ + 1`.
  obtain ⟨wg, hwg, -, -, -, -, hsym⟩ := id hGuard
  have hwe : wg = wch := by rw [hChain] at hwg; cases hwg; rfl
  have hsym' : GalilScaffoldChainConsume.symbol wch.machine.control.period.focus
      = GalilScaffoldInputHead.read s'.right := by rw [← hwe]; exact hsym
  have hread : GalilScaffoldInputHead.read (right s.right)
      = (encoded w)[position s.right + 1]? :=
    PalPeg.GalilRoundPeriod.right_read_index s.right w hScanInv.rightRep
      hScanInv.rightPresent hCan
  have hCaught : (encoded w)[position s.center + r₀ + 1 - 2 * periodLength wch]? =
      GalilScaffoldChainConsume.symbol wch.machine.control.period.focus := by
    rw [hCaught', hsym', hRight, hread, hScanInv.rightPos]
  exact shiftPalAt_fresh_of_candidate hChain hGuard hRight hCan hScanInv rfl
    hIn hLeft hPos hLo hEnd hCaught

#print axioms shiftPal_of_freshShiftLedger


end


end PalPeg.ShiftPalAlongTrace
