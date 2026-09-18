import PalPeg.GalilScaffoldTopScanSeg

/-!
# `OnlyMatchedRun` を**後ろから**伸ばす

`CloseoutRoundSeg` は `hSP` の残差を 2 つに絞ったが、そのどちらも
`GalilScaffoldTopRoundS.round_next` / `GalilScaffoldTopFirstRound.first_round` が
要求する **`ScanSeg`（run の区間）** を作れるかに帰着する。区間を run から
抽出するのが CLAUDE.md §1 の壁 (1)（`ScanToScan`）。

このファイルはその壁を**回り込む**ための最初の部品。

`OnlyMatchedRun` は

```
| stop (s) : OnlyMatchedRun s 0 s
| next (s) (available) (continuing) (matched) (rest : OnlyMatchedRun (onlyCompareNext s) n t)
    : OnlyMatchedRun s (n+1) t
```

と**前から**積む inductive なので、「区間の先頭を知ってから末尾まで走る」形でしか
作れない。run を tick ごとに歩きながら積むには**後ろから**伸ばせないといけない。
`onlyMatchedRun_snoc` がそれで、run に沿った不変量

    「いまの `toOnly` 状態は、あるラウンド起点から `n` 回の一致比較で到達した」

を `scan_match` tick ごとに 1 手ずつ伸ばせるようにする。これができれば
`CompareRounds.next` の `OnlyMatchedRun` 引数は**区間抽出なしで**手に入り、
`RoundSeg`（＝`CompareRounds h _ 1 _`）が run の帰納から出る。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.MatchedRunSnoc

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **一致比較 1 手を末尾に足す。**  `OnlyMatchedRun` の帰納は前から積むので、
末尾に足すには run 自体に帰納法をかける（`List.concat` と同じ形）。 -/
theorem onlyMatchedRun_snoc {s t : OnlyCompareState} {n : ℕ}
    (hrun : OnlyMatchedRun s n t)
    (hAvailable : canRight t.right)
    (hContinuing : singlePositive t.cycle = false)
    (hMatched : read (left t.left) = read (right t.right)) :
    OnlyMatchedRun s (n + 1) (onlyCompareNext t) := by
  induction hrun with
  | stop u => exact .next u hAvailable hContinuing hMatched (.stop _)
  | next u hav hcont hmt _ ih =>
    exact .next u hav hcont hmt (ih hAvailable hContinuing hMatched)

/-- **同じことを「1 手を左から剥がす」向きでも。**  `OnlyMatchedRun s (n+1) t` の
先頭 1 手を取り出す（`cases` の別名だが、run 形の不変量を書くときに毎回
`cases` を書かずに済む）。 -/
theorem onlyMatchedRun_head {s t : OnlyCompareState} {n : ℕ}
    (hrun : OnlyMatchedRun s (n + 1) t) :
    canRight s.right ∧ singlePositive s.cycle = false ∧
      read (left s.left) = read (right s.right) ∧
      OnlyMatchedRun (onlyCompareNext s) n t := by
  cases hrun with
  | next u hav hcont hmt rest => exact ⟨hav, hcont, hmt, rest⟩

/-- **連結。**  2 本の一致比較 run をつなぐ。 -/
theorem onlyMatchedRun_trans {s t u : OnlyCompareState} {n m : ℕ}
    (h1 : OnlyMatchedRun s n t) (h2 : OnlyMatchedRun t m u) :
    OnlyMatchedRun s (n + m) u := by
  induction h1 with
  | stop v => simpa using h2
  | next v hav hcont hmt _ ih =>
    rw [Nat.add_right_comm]
    exact .next v hav hcont hmt (ih h2)

#print axioms onlyMatchedRun_snoc
#print axioms onlyMatchedRun_head
#print axioms onlyMatchedRun_trans


/-! ## 機械側: `MatchedSeq` を後ろから伸ばす

`MatchedSeq P q first n s t` は run そのものの上の inductive で、
`count`（background 量子、カウントしない）と `compare`（一致比較、+1）から成る。
`Tick` の `scan_wait` / `scan_count` は `background` を持ち、`scan_match` は
`compare` ＋ `matched` を持つので、**この 2 つの snoc が run 上の tick と 1 対 1 に対応する**。

これで「区間を先に取ってから射影する」（`scanSeg_only`）のではなく、
「tick ごとに射影付きで積む」ことができる。`matchedSeq_only` が
`MatchedSeq → OnlyMatchedRun` を与えるので、射影は最後に 1 回で済む。 -/

/-- **background 量子を末尾に足す。**  カウントは増えない。 -/
theorem matchedSeq_snoc_background {P : Shared} {q : ℕ} {first : Fin 9} {n : ℕ}
    {s t t' : GalilVM} (hSeq : MatchedSeq P q first n s t)
    (hBackground : (galilFrameS P q first).background t t') :
    MatchedSeq P q first n s t' := by
  induction hSeq with
  | stop u => exact .count u t' hBackground (.stop _)
  | count u u' hb _ ih => exact .count u u' hb (ih hBackground)
  | compare u vs vq hav hcont hcmp hmt hwatch hq _ ih =>
    exact .compare u vs vq hav hcont hcmp hmt hwatch hq (ih hBackground)

/-- **一致比較を末尾に足す。**  カウントが 1 増える。 -/
theorem matchedSeq_snoc_compare {P : Shared} {q : ℕ} {first : Fin 9} {n : ℕ}
    {s t : GalilVM} {vs : ScanVM} {vq : SearchVM} (hSeq : MatchedSeq P q first n s t)
    (hAvailable : canRight t.right) (hContinuing : singlePositive t.cycle = false)
    (hCompare : (galilFrame P q first).compare t (scanLens.set t vs))
    (hMatched : (galilFrame P q first).matched (scanLens.set t vs))
    (hWatch : ∃ w', vs.chain = .watch w')
    (hSearch : searchEffect P true t vq) :
    MatchedSeq P q first (n + 1) s (afterCompare t vs vq) := by
  induction hSeq with
  | stop u => exact .compare u vs vq hAvailable hContinuing hCompare hMatched hWatch hSearch (.stop _)
  | count u u' hb _ ih =>
    exact .count u u' hb (ih hAvailable hContinuing hCompare hMatched hSearch)
  | compare u vs' vq' hav hcont hcmp hmt hwatch hq _ ih =>
    exact .compare u vs' vq' hav hcont hcmp hmt hwatch hq
      (ih hAvailable hContinuing hCompare hMatched hSearch)

#print axioms matchedSeq_snoc_background
#print axioms matchedSeq_snoc_compare


/-! ## 制御つき: `ScanSeg` を後ろから伸ばす

`MatchedSeq` は VM だけを見るが、run を歩くには制御（`clock` / `output` /
`replaying`）も要る。`ScanSeg` はそれを持っていて、しかも 3 つの構成子が
`Tick` の `scan_wait` / `scan_count` / `scan_match` と 1 対 1（`scanSeg_steps` が
その対応を作っている）。ここではその逆向き——run を 1 tick 進めるたびに
`ScanSeg` を末尾から伸ばす——を用意する。

**注意**: `ScanSeg.match` は `hwatch : ∃ w', vs.chain = .watch w'` を要求するので、
chain が watch している間しか伸ばせない。これは `hSP` が要る領域
（`ChainRound` は `s.chain = .watch wch` で guard されている）と一致する。 -/

/-- **wait 量子を末尾に足す。**  `ScanSeg.wait` は制御を変えない。 -/
theorem scanSeg_snoc_wait {P : Shared} {q : ℕ} {first : Fin 9} {delay n : ℕ}
    {c c' : Control} {s t t' : GalilVM}
    (hSeg : ScanSeg P q first delay n c s c' t)
    (hScan : c'.mode = Mode.scan) (hNotReplaying : c'.replaying = false)
    (hUnavailable : ¬ canRight t.right)
    (hBackground : (galilFrameS P q first).background t t') :
    ScanSeg P q first delay n c s c' t' := by
  induction hSeg with
  | stop u v => exact .wait u v t' hScan hNotReplaying hUnavailable hBackground (.stop _ _)
  | wait u v v' hm hr hn hb _ ih => exact .wait u v v' hm hr hn hb (ih hScan hNotReplaying hUnavailable hBackground)
  | count u v v' hm hr ha hc hb _ ih => exact .count u v v' hm hr ha hc hb (ih hScan hNotReplaying hUnavailable hBackground)
  | «match» u v vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    exact .match u v vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho (ih hScan hNotReplaying hUnavailable hBackground)

/-- **count 量子を末尾に足す。**  `clock` が 1 減る。 -/
theorem scanSeg_snoc_count {P : Shared} {q : ℕ} {first : Fin 9} {delay n : ℕ}
    {c c' : Control} {s t t' : GalilVM}
    (hSeg : ScanSeg P q first delay n c s c' t)
    (hScan : c'.mode = Mode.scan) (hNotReplaying : c'.replaying = false)
    (hAvailable : canRight t.right) (hClock : 1 < c'.clock)
    (hBackground : (galilFrameS P q first).background t t') :
    ScanSeg P q first delay n c s { c' with clock := c'.clock - 1 } t' := by
  induction hSeg with
  | stop u v =>
    exact .count u v t' hScan hNotReplaying hAvailable hClock hBackground (.stop _ _)
  | wait u v v' hm hr hn hb _ ih => exact .wait u v v' hm hr hn hb (ih hScan hNotReplaying hAvailable hClock hBackground)
  | count u v v' hm hr ha hc hb _ ih => exact .count u v v' hm hr ha hc hb (ih hScan hNotReplaying hAvailable hClock hBackground)
  | «match» u v vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    exact .match u v vs vq o hm hr ha hc hcont hcmp hmt hwatch hq ho (ih hScan hNotReplaying hAvailable hClock hBackground)

/-- **一致比較を末尾に足す。**  比較数が 1 増え、制御は `clock := delay` /
`output := o` / `replaying := false` に更新される。 -/
theorem scanSeg_snoc_match {P : Shared} {q : ℕ} {first : Fin 9} {delay n : ℕ}
    {c c' : Control} {s t : GalilVM} {vs : ScanVM} {vq : SearchVM} {o : Bool}
    (hSeg : ScanSeg P q first delay n c s c' t)
    (hScan : c'.mode = Mode.scan) (hNotReplaying : c'.replaying = false)
    (hAvailable : canRight t.right) (hClock : c'.clock = 1)
    (hContinuing : singlePositive t.cycle = false)
    (hCompare : (galilFrame P q first).compare t (scanLens.set t vs))
    (hMatched : (galilFrame P q first).matched (scanLens.set t vs))
    (hWatch : ∃ w', vs.chain = .watch w')
    (hSearch : searchEffect P true t vq)
    (hRefresh : refresh (galilFrame P q first) (afterCompare t vs vq) c'.output o) :
    ScanSeg P q first delay (n + 1) c s
      { c' with clock := delay, output := o, replaying := false } (afterCompare t vs vq) := by
  induction hSeg with
  | stop u v =>
    exact .match u v vs vq o hScan hNotReplaying hAvailable hClock hContinuing hCompare hMatched
      hWatch hSearch hRefresh (.stop _ _)
  | wait u v v' hm hr hn hb _ ih => exact .wait u v v' hm hr hn hb (ih hScan hNotReplaying hAvailable hClock hContinuing hCompare hMatched hSearch hRefresh)
  | count u v v' hm hr ha hc hb _ ih => exact .count u v v' hm hr ha hc hb (ih hScan hNotReplaying hAvailable hClock hContinuing hCompare hMatched hSearch hRefresh)
  | «match» u v vs' vq' o' hm hr ha hc hcont hcmp hmt hwatch hq ho _ ih =>
    exact .match u v vs' vq' o' hm hr ha hc hcont hcmp hmt hwatch hq ho (ih hScan hNotReplaying hAvailable hClock hContinuing hCompare hMatched hSearch hRefresh)

#print axioms scanSeg_snoc_wait
#print axioms scanSeg_snoc_count
#print axioms scanSeg_snoc_match


/-! ## `Tick` 1 手を `ScanSeg` に吸収する

ここが「区間抽出（`ScanToScan`）なしで run から `ScanSeg` を作る」の要。
scan 相の `Tick` は `scan_wait` / `scan_count` / `scan_match` / `scan_shift` /
`scan_fallback` の 5 つしかなく、前 3 つは `ScanSeg` の構成子そのもの、
後ろ 2 つは mode が scan を離れる（＝ラウンド境界）。 -/

/-- **一致比較 tick の分解。**  `compareFound` から `galilFrame` 側の比較を取り出す。
chain が watch していれば `chainBorn` は false なので `afterBirth` は恒等。 -/
theorem compare_matched_parts {P : Shared} {q : ℕ} {first : Fin 9} {t u : GalilVM}
    (hCompare : (galilFrameS P q first).compare t u)
    (hMatched : (galilFrameS P q first).matched u)
    {wch : GalilScaffoldChainWatch.State} (hWatch : t.chain = ChainVM.watch wch) :
    ∃ (vs : ScanVM) (vq : SearchVM),
      u = afterCompare t vs vq ∧ vs.chain = u.chain ∧
      searchEffect P true t vq ∧
      (galilFrame P q first).compare t (scanLens.set t vs) ∧
      (galilFrame P q first).matched (scanLens.set t vs) := by
  obtain ⟨vs, vq, a, hvl, hvr, hiff, hsearch, hchain, hteq⟩ := hCompare
  have hNotIdle : t.chain ≠ ChainVM.idle := by rw [hWatch]; intro h0; cases h0
  have hATrue : a = true := by
    cases a with
    | true => rfl
    | false =>
      exfalso
      rw [if_neg (by simp)] at hteq
      subst hteq
      refine absurd (hiff.2 ?_) (by simp)
      have h0 : GalilScaffoldInputHead.read
            (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found))
              t.chain) (afterMismatch t vs vq)).left
          = GalilScaffoldInputHead.read
            (afterBirth (chainBorn (decide (vq.search.mode = GalilScaffoldSearchFinish.Mode.found))
              t.chain) (afterMismatch t vs vq)).right := hMatched
      rw [afterBirth_left, afterBirth_right] at h0
      exact h0
  subst hATrue
  rw [if_pos rfl, afterBirth_of_ne_idle hNotIdle] at hteq
  have hMatchedSet : (galilFrame P q first).matched (scanLens.set t vs) := hiff.1 rfl
  have hChainTick : ChainTick true t.chain vs.chain := by
    rcases hchain with ⟨-, hct⟩ | ⟨hidle, -, -⟩ | ⟨hidle, -, -⟩
    · exact hct
    · exact absurd hidle hNotIdle
    · exact absurd hidle hNotIdle
  refine ⟨vs, vq, hteq, by rw [hteq]; rfl, hsearch, ?_, hMatchedSet⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · show (scanLens.get (scanLens.set t vs)).left = GalilScaffoldInputHead.left t.left
    rw [scanLens.get_set]; exact hvl
  · show (scanLens.get (scanLens.set t vs)).right = GalilScaffoldChainVerifier.right t.right
    rw [scanLens.get_set]; exact hvr
  · show ChainTick (decide (GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left)
      = GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right t.right))) t.chain
      (scanLens.get (scanLens.set t vs)).chain
    rw [scanLens.get_set]
    have hread : GalilScaffoldInputHead.read (GalilScaffoldInputHead.left t.left)
        = GalilScaffoldInputHead.read (GalilScaffoldChainVerifier.right t.right) := by
      have h0 : GalilScaffoldInputHead.read (scanLens.get (scanLens.set t vs)).left
          = GalilScaffoldInputHead.read (scanLens.get (scanLens.set t vs)).right := hMatchedSet
      rw [scanLens.get_set] at h0
      rw [← hvl, ← hvr]; exact h0
    rw [decide_eq_true hread]
    exact hChainTick
  · rw [scanLens.get_set]

#print axioms compare_matched_parts

/-- **run の 1 tick を `ScanSeg` に吸収する。**  3 つの出口しかない:

1. `ScanSeg` が 1 手伸びる（`scan_wait` / `scan_count` / `scan_match`）
2. mode が scan を離れる（`scan_shift` / `scan_fallback` ＝ ラウンド境界）
3. chain が watch でなくなる（終端の一致比較で chain が壊れる場合）

`hContinuing`（周期がまだ終端でない）は `ScanSeg.match` が要求するもので、呼び手は
`RoundScan.fresh`（`used < 2h`）と `RoundScan.terminal_iff` から無償で作れる。

`hRestartNeedsBroken` は `P.restart` が壊れた chain でしか起きないという枠の性質で、
`PofC`（`restartVM`）では定義からの定理。 -/
theorem scanSeg_snoc_tick {P : Shared} {q : ℕ} {first : Fin 9} {delay n : ℕ}
    {c : Control} {s : GalilVM} {x y : State GalilVM}
    (hRestartNeedsBroken : ∀ u v : GalilVM, P.restart u v → ∃ wb, u.chain = ChainVM.broken wb)
    (hSeg : ScanSeg P q first delay n c s x.ctl x.vm)
    (hScan : x.ctl.mode = Mode.scan) (hNotReplaying : x.ctl.replaying = false)
    (hWatching : ∃ wch, x.vm.chain = ChainVM.watch wch)
    (hContinuing : singlePositive x.vm.cycle = false)
    (hTick : Tick (galilFrameS P q first) delay x y) :
    (∃ m, ScanSeg P q first delay m c s y.ctl y.vm) ∨ y.ctl.mode ≠ Mode.scan ∨
      (∀ w, y.vm.chain ≠ ChainVM.watch w) := by
  cases hTick with
  | init c0 s0 s0' hm _ => exact absurd (hm.symm.trans hScan) (by decide)
  | scan_wait c0 s0 s0' hm hav hBg =>
    exact Or.inl ⟨n, scanSeg_snoc_wait hSeg hScan hNotReplaying hav.2 hBg⟩
  | scan_count c0 s0 s0' hm hav hClock hBg =>
    exact Or.inl ⟨n, scanSeg_snoc_count hSeg hScan hNotReplaying
      (hav.resolve_left (by rw [hNotReplaying]; simp)) hClock hBg⟩
  | scan_match c0 s0 s0' s0'' o hm hav hClock hCompare hMatched hPlace hRefresh =>
    obtain ⟨wch, hWatch⟩ := hWatching
    obtain ⟨vs, vq, hteq, -, hSearch, hCmp', hMt'⟩ :=
      compare_matched_parts hCompare hMatched hWatch
    have hPlace' : s0'' = s0' := by
      have h0 : s0'' = (if c0.replaying then
        { s0' with replay := GalilScaffoldCounter.dec s0'.replay } else s0') := hPlace
      rw [hNotReplaying] at h0
      simpa using h0
    subst hPlace'
    subst hteq
    by_cases hTargetWatch : ∃ w', vs.chain = ChainVM.watch w'
    · refine Or.inl ⟨n + 1, ?_⟩
      rw [hNotReplaying]
      simpa using scanSeg_snoc_match hSeg hScan hNotReplaying
        (hav.resolve_left (by rw [hNotReplaying]; simp)) hClock hContinuing hCmp' hMt'
        hTargetWatch hSearch hRefresh
    · exact Or.inr (Or.inr (fun w hc => hTargetWatch ⟨w, hc⟩))
  | scan_shift c0 s0 s0' s0'' hm _ _ _ _ _ _ _ =>
    exact Or.inr (Or.inl (fun h => Mode.noConfusion h))
  | scan_fallback c0 s0 s0' s0'' hm _ _ _ _ _ _ _ =>
    exact Or.inr (Or.inl (fun h => Mode.noConfusion h))
  | shift_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | shift_done c0 s0 o hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | replayStart c0 s0 s0' o hm _ _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | restart c0 s0 s0' hm hRst =>
    obtain ⟨wch, hWatch⟩ := hWatching
    obtain ⟨wb, hBroken⟩ := hRestartNeedsBroken _ _ hRst
    exact absurd (hWatch.symm.trans hBroken) (fun h => ChainVM.noConfusion h)
  | copy_one c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | copy_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | home_start c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | home_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | fpp_slice c0 s0 s0' hm _ => exact absurd (hm.symm.trans hScan) (by decide)
  | fpp_done c0 s0 s0' hm _ => exact absurd (hm.symm.trans hScan) (by decide)
  | markEnd_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | markEnd_found c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | choose_select c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | choose_step c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | rewind_done c0 s0 s0' hm _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | rewind_one c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hScan) (by decide)
  | rewind_pair c0 s0 s0' hm _ _ _ => exact absurd (hm.symm.trans hScan) (by decide)

#print axioms scanSeg_snoc_tick


/-- **`restartVM` は壊れた chain でしか起きない。**  `scanSeg_snoc_tick` の
`hRestartNeedsBroken` を具体枠（`sharedC` / `PofC`）で放電する。 -/
theorem restartNeedsBroken_of_restartVM (entry : ℕ) :
    ∀ u v : GalilVM, restartVM entry u v → ∃ wb, u.chain = ChainVM.broken wb :=
  fun _ _ h => ⟨h.choose, h.choose_spec.1⟩

#print axioms restartNeedsBroken_of_restartVM

end PalPeg.MatchedRunSnoc
