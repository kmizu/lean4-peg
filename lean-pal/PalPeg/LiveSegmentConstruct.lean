import PalPeg.CopyPhaseTickMatched
import PalPeg.GalilSegmentConstruct

/-!
# live chain 版の区間構成（`watchSegE_constructB` と同じ形）

**n125 の訂正。** `CopyPhaseTick.watchSegE_backgroundRun_live` は `n < c.clock` を
要求していたので `2h+2 < 2048` の準備しか載らなかった。そこから
「`ReachesWatchPhase` の無条件形は成り立たない」と書いたが、**考えすぎだった**。

既存の idle chain 版 `GalilSegmentConstructB.watchSegE_constructB` は `n < c.clock` を
**要求していない**。clock は構成の中で処理する（`1 < clock` なら `count`、`clock = 1`
なら `match`、`delay` に戻る）。呼び出し側は `n = headRank r.right * 2048 + c.clock`
という「入力が尽きるまでの全機械ステップ数」を渡し、結論は
`es.length = n ∨ SegEnd P c' t` になっている。

**live chain 版も同じ形でよい。** 唯一足りなかった部品は「一致事象で chain が 1 手
進める」で、それが `CopyPhaseTickMatched.copyOrBack_tick_true_exists`。
探索側の帳簿（`ReadyFuel` / `hsearch`）は live chain では**丸ごと不要**——
`searchEffect P a s v` は `s.chain ≠ .idle` の枝で `v = searchLens.get s` に潰れ、
`chainBorn` も `false` になるので誕生も起きない。

`SegEnd` の 5 枝のうち live で実際に使うのは `.mismatch` だけ:

* `.ended`（右が進めない）は `.wait` で素通しして chain を進める方が得
* `.found` / `.foundBackground` は探索が不活性なので chain に影響しない
* `.lastLetter` は入力側の都合で、chain の準備とは独立

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LiveSegmentConstruct

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.GalilBranchInvariants PalPeg.CopyPhaseTick PalPeg.CopyPhaseTickMatched
open PalPeg.GalilSegmentConstruct

/-- **一致比較 1 手分の証人**（live chain）。`WatchSegE.match` の側条件をすべて作る。
探索量子は不活性（`vq = searchLens.get s`）。 -/
theorem match_step_live (P : Shared) (q : ℕ) (first : Fin 9) (c : Control) (s : GalilVM)
    (hNotIdle : s.chain ≠ ChainVM.idle)
    (hMatch : GalilScaffoldInputHead.read (left s.left) = GalilScaffoldInputHead.read (right s.right))
    {z : ChainVM} (hTick : ChainTick true s.chain z) :
    ∃ (vs : ScanVM) (vq : SearchVM) (o : Bool),
      (galilFrame P q first).compare s (scanLens.set s vs) ∧
      (galilFrame P q first).matched (scanLens.set s vs) ∧
      searchEffect P true s vq ∧
      refresh (galilFrame P q first) (afterCompare s vs vq) c.output o ∧
      (afterCompare s vs vq).chain = z ∧
      (afterCompare s vs vq).left = left s.left ∧
      (afterCompare s vs vq).right = right s.right ∧
      (afterCompare s vs vq).center = s.center := by
  classical
  let vs : ScanVM := ⟨left s.left, right s.right, z⟩
  let vq : SearchVM := searchLens.get s
  let u : GalilVM := afterCompare s vs vq
  let o : Bool := if P.onLetter u then decide (P.leftFirst u) else c.output
  refine ⟨vs, vq, o, ?_, hMatch, Or.inr ⟨hNotIdle, rfl⟩, ?_, ?_, rfl, rfl, rfl⟩
  · refine ⟨⟨rfl, rfl, ?_⟩, rfl⟩
    show ChainTick (decide (GalilScaffoldInputHead.read (left s.left)
      = GalilScaffoldInputHead.read (right s.right))) s.chain z
    rw [decide_eq_true hMatch]
    exact hTick
  · refine ⟨fun hOnLetter => ?_, fun hOnLetter => ?_⟩
    · have hOn : P.onLetter u := hOnLetter
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = true ↔ P.leftFirst u
      rw [if_pos hOn]; exact decide_eq_true_iff
    · have hOn : ¬ P.onLetter u := hOnLetter
      show (if P.onLetter u then decide (P.leftFirst u) else c.output) = c.output
      rw [if_neg hOn]
  · exact afterCompare_chain s vs vq

#print axioms match_step_live

/-- **live chain 版の区間構成。**  `watchSegE_constructB` と同じ形で、`n` 手走り切るか
`SegEnd` で終わるか、その前に chain が watch 相に着く。**clock の余裕は要らない**——
`match` 段が clock を `delay` に戻す。 -/
theorem watchSegE_constructLive (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ)
    (hDelay : 1 ≤ delay) :
    ∀ (n : ℕ) (c : Control) (s : GalilVM),
      c.mode = Mode.scan → c.replaying = false → 1 ≤ c.clock →
      CopyOrBack s.chain → LagPos s.chain →
      ∃ (es : List Bool) (c' : Control) (s' : GalilVM),
        WatchSegE P q first delay es c s c' s' ∧
        c'.mode = Mode.scan ∧ c'.replaying = false ∧ 1 ≤ c'.clock ∧
        ((∃ w : GalilScaffoldChainWatch.State, s'.chain = ChainVM.watch w) ∨
          (CopyOrBack s'.chain ∧ LagPos s'.chain ∧
            (es.length = n ∨ SegEnd P c' s'))) := by
  classical
  intro n
  induction n with
  | zero =>
    intro c s hScan hNotReplaying hClock hPhase hLag
    exact ⟨[], c, s, .stop _ _, hScan, hNotReplaying, hClock, Or.inr ⟨hPhase, hLag, Or.inl rfl⟩⟩
  | succ n ih =>
    intro c s hScan hNotReplaying hClock hPhase hLag
    have hNotIdle : s.chain ≠ ChainVM.idle := copyOrBack_not_idle hPhase
    by_cases hAvailable : canRight s.right
    · rcases Nat.lt_or_ge 1 c.clock with hClockTwo | hClockLe
      · -- `count`: background tick, clock 1 減
        obtain ⟨z, hTick⟩ := copyOrBack_tick_false_exists hPhase
        obtain ⟨s1, hBg, hChain1, -, hR1, -, -, -⟩ :=
          live_background_exists P q first s hNotIdle hTick
        rcases copyOrBack_tick_false hPhase hTick with hPhase1 | ⟨w, hw⟩
        · have hPhase1' : CopyOrBack s1.chain := by rw [hChain1]; exact hPhase1
          have hLag1 : LagPos s1.chain := by rw [hChain1]; exact lagPos_tick hLag hTick
          obtain ⟨es, c', s', hSeg, hMode', hRep', hClock', hEnd⟩ :=
            ih { c with clock := c.clock - 1 } s1 hScan hNotReplaying (by simp; omega)
              hPhase1' hLag1
          refine ⟨false :: es, c', s',
            .count c s s1 hScan hNotReplaying hAvailable hClockTwo hBg hSeg,
            hMode', hRep', hClock', ?_⟩
          rcases hEnd with hWatch | ⟨hP, hL, hLenOrEnd⟩
          · exact Or.inl hWatch
          · exact Or.inr ⟨hP, hL, by
              rcases hLenOrEnd with hLen | hSegEnd
              · exact Or.inl (by simp [hLen])
              · exact Or.inr hSegEnd⟩
        · exact ⟨[false], _, s1,
            .count c s s1 hScan hNotReplaying hAvailable hClockTwo hBg (.stop _ _),
            hScan, hNotReplaying, by simp; omega, Or.inl ⟨w, by rw [hChain1]; exact hw⟩⟩
      · -- clock = 1: 比較
        have hClockOne : c.clock = 1 := le_antisymm hClockLe hClock
        by_cases hMatch : GalilScaffoldInputHead.read (left s.left)
            = GalilScaffoldInputHead.read (right s.right)
        · obtain ⟨z, hTick⟩ := copyOrBack_tick_true_exists hPhase hLag
          obtain ⟨vs, vq, o, hCompare, hMatched, hSearch, hRefresh, hChainAC, -, -, -⟩ :=
            match_step_live P q first c s hNotIdle hMatch hTick
          rcases copyOrBack_tick_true hPhase hLag hTick with hPhase1 | ⟨w, hw⟩
          · have hPhase1' : CopyOrBack (afterCompare s vs vq).chain := by
              rw [hChainAC]; exact hPhase1
            have hLag1 : LagPos (afterCompare s vs vq).chain := by
              rw [hChainAC]; exact lagPos_tick hLag hTick
            obtain ⟨es, c', s', hSeg, hMode', hRep', hClock', hEnd⟩ :=
              ih { c with clock := delay, output := o, replaying := false }
                (afterCompare s vs vq) hScan rfl hDelay hPhase1' hLag1
            refine ⟨true :: es, c', s',
              .match c s vs vq o hScan hNotReplaying hAvailable hClockOne hNotIdle hCompare
                hMatched hSearch hRefresh hSeg,
              hMode', hRep', hClock', ?_⟩
            rcases hEnd with hWatch | ⟨hP, hL, hLenOrEnd⟩
            · exact Or.inl hWatch
            · exact Or.inr ⟨hP, hL, by
                rcases hLenOrEnd with hLen | hSegEnd
                · exact Or.inl (by simp [hLen])
                · exact Or.inr hSegEnd⟩
          · exact ⟨[true], _, afterCompare s vs vq,
              .match c s vs vq o hScan hNotReplaying hAvailable hClockOne hNotIdle hCompare
                hMatched hSearch hRefresh (.stop _ _),
              hScan, rfl, hDelay, Or.inl ⟨w, by rw [hChainAC]; exact hw⟩⟩
        · -- 不一致: 区間はここで終わる（`SegEnd.mismatch`）
          exact ⟨[], c, s, .stop _ _, hScan, hNotReplaying, hClock,
            Or.inr ⟨hPhase, hLag,
              Or.inr (.mismatch hNotReplaying hClockOne hAvailable hMatch)⟩⟩
    · -- `wait`: 右ヘッドが進めない。clock は動かず chain だけ進む
      obtain ⟨z, hTick⟩ := copyOrBack_tick_false_exists hPhase
      obtain ⟨s1, hBg, hChain1, -, hR1, -, -, -⟩ :=
        live_background_exists P q first s hNotIdle hTick
      rcases copyOrBack_tick_false hPhase hTick with hPhase1 | ⟨w, hw⟩
      · have hPhase1' : CopyOrBack s1.chain := by rw [hChain1]; exact hPhase1
        have hLag1 : LagPos s1.chain := by rw [hChain1]; exact lagPos_tick hLag hTick
        obtain ⟨es, c', s', hSeg, hMode', hRep', hClock', hEnd⟩ :=
          ih c s1 hScan hNotReplaying hClock hPhase1' hLag1
        refine ⟨false :: es, c', s',
          .wait c s s1 hScan hNotReplaying hAvailable hBg hSeg, hMode', hRep', hClock', ?_⟩
        rcases hEnd with hWatch | ⟨hP, hL, hLenOrEnd⟩
        · exact Or.inl hWatch
        · exact Or.inr ⟨hP, hL, by
            rcases hLenOrEnd with hLen | hSegEnd
            · exact Or.inl (by simp [hLen])
            · exact Or.inr hSegEnd⟩
      · exact ⟨[false], c, s1,
          .wait c s s1 hScan hNotReplaying hAvailable hBg (.stop _ _),
          hScan, hNotReplaying, hClock, Or.inl ⟨w, by rw [hChain1]; exact hw⟩⟩

#print axioms watchSegE_constructLive

end PalPeg.LiveSegmentConstruct
