import PalPeg.CloseoutWatchRound2
import PalPeg.CloseoutWatchRound8
import PalPeg.CloseoutFoundRoute1

/-!
# `foundExit_compare_final20` の `hpack` は **REFUTED（条件付き）**

`CloseoutFoundRoute1.foundExit_compare_final20` の名前付き仮説 `hpack` は、
`FoundCompareCtxC` を満たす各 `(cP, sP)` について 7 節の連言を主張する。その 4 番目が
`CloseoutWatchRound7.PrepLandingWatchC` で、定義は

    ∀ es c2 s2, WatchSegE P q first 2048 es cP sP c2 s2 → ∃ w, s2.chain = .watch w

`WatchSegE.stop cP sP` は無条件に存在するから、`es = []` の実例で
`∃ w, sP.chain = .watch w` が出る（`CloseoutWatchRound8.prepLandingWatchC_watch_start`）。

ところが guard の `FoundCompareCtxC`（`CloseoutWatchRound2:270`）は
`sP = afterBirth true (afterCompare sF ⟨…, ch⟩ vq)`、つまり `sP.chain = ch` で、
`ch` は `ChainMatched (chainStart …) ch` を満たす。そして

* `chainStart` は `.copy`（`GalilScaffoldTopChainVM:41`）
* `ChainMatched` は**構成子の形を保つ 1 歩の関係**で、`.copy` から出る構成子は
  `.copy → .copy` **だけ**（`GalilScaffoldTopChainVM:69`）

したがって `ch` は必ず `.copy` であり、`.watch` にはなれない。**両立しない。**

`hpack_false_of_foundCompareCtx` がその矛盾を機械検査したもの。前提として
`FoundCompareCtxC` の証人を取るので **`REFUTED（条件付き）`**——未構成の証人は
`FoundCompareCtxC`（`WatchSegE` / `searchEffect` / `refresh` の証人が要る）。

**`PrepLandingWatchC` 自身は偽ではない。** chain が watch になった後の landing では真で、
producer もある（`CloseoutWatchRound10.prepLandingWatchC_of_short`）。
**束ねる場所が間違っている**——`hpack` は 7 節の束であり、CLAUDE.md
「葉を束に畳み込むと偽になりうる」の典型（`hpack` という名前は
`CloseoutPackRefute.hpack_false` で既に一度偽になっている）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.FoundPackRefute

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton
open PalPeg.CloseoutWatchRound2 (FoundCompareCtxC)
open PalPeg.CloseoutWatchRound7 (PrepLandingWatchC)

/-- **`ChainMatched` は `.copy` から `.copy` にしか行かない。** -/
theorem chainMatched_copy_stays_copy {t : GalilScaffoldTape.Tape} {h : Counter}
    {p : GalilScaffoldPlace.Place} {v : GalilScaffoldChainPeriod.Tape}
    {lag margin : Counter} {ver : PlaceHead} {z : ChainVM}
    (hMatched : ChainMatched (ChainVM.copy t h p v lag margin ver) z) :
    ∃ lag' margin', z = ChainVM.copy t h p v lag' margin' ver := by
  cases hMatched with
  | copy _ _ _ _ _ _ _ => exact ⟨_, _, rfl⟩

/-- **`chainStart` は `.copy`。** -/
theorem chainStart_is_copy (answer : GalilScaffoldTape.Tape) (c : Fin 3)
    (walker : GalilScaffoldPlace.Place) (verifier : PlaceHead) (radius : Counter) :
    chainStart answer c walker verifier radius
      = ChainVM.copy answer reset walker (GalilScaffoldChainPeriod.start c) radius radius
        verifier := rfl


/-! ## 同じ欠陥は `PrepLandingWatchC` だけではない

`CloseoutWatchRun.LiveScanWatch c s` は

    c.mode = .scan ∧ c.replaying = false ∧ 1 ≤ c.clock ∧ ∃ w, s.chain = .watch w

で、最後の節がまた **watch を要求する**。よって
`CloseoutWatchRound5.PrepLandingLiveC cP sP`（`∀ es c2 s2, WatchSegE … → LiveScanWatch c2 s2`）
も `es = []` 実例で `sP.chain` が watch であることを強制し、found 比較直後の `sP`
（chain は生まれたばかりの `.copy`）では偽。

**これが found 経路が閉じなかった根本原因**と見られる: 設計が「chain は誕生直後から
watch している」を前提にしているが、モデルは Scala 正本どおり `chain.start()` が
`.copy` 相を作り、周期を写して、巻き戻して、それから `.watch` になる。 -/

/-- `PrepLandingLiveC` も watch 始点を強制する（`es = []` 実例）。 -/
theorem prepLandingLiveC_watch_start (P : Shared) (q : ℕ) (first : Fin 9)
    {cP : Control} {sP : GalilVM}
    (hLive : PalPeg.CloseoutWatchRound5.PrepLandingLiveC P q first cP sP) :
    ∃ w : GalilScaffoldChainWatch.State, sP.chain = ChainVM.watch w :=
  (hLive [] cP sP (.stop cP sP)).2.2.2

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **REFUTED（条件付き）**: `FoundCompareCtxC` の証人があれば `hpack` の 4 番目の節
`PrepLandingWatchC` は矛盾する。未構成の証人は `FoundCompareCtxC` そのもの。 -/
theorem hpack_false_of_foundCompareCtx {w : List (Fin 2)} {c cP : Control} {r sP : GalilVM}
    (hCtx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hPrepLandingWatch : PrepLandingWatchC (PofC centre place entry w) q first cP sP) :
    False := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg, hmF, hrF, hcF, havF, hidle,
    hcen, hqe, hf, hmtF, hch, hchne, hoF, hcPe, hsPe⟩ := hCtx
  obtain ⟨wv, hWatch⟩ :=
    PalPeg.CloseoutWatchRound8.prepLandingWatchC_watch_start _ _ _ hPrepLandingWatch
  have hChainEq : sP.chain = ch := by rw [hsPe, afterBirth_chain]; rfl
  obtain ⟨lag', margin', hCopy⟩ := chainMatched_copy_stays_copy hch
  rw [hChainEq, hCopy] at hWatch
  exact ChainVM.noConfusion hWatch


/-- **REFUTED（条件付き）その 2**: `PrepLandingLiveC` も found 比較直後で偽。 -/
theorem prepLandingLiveC_false_of_foundCompareCtx {w : List (Fin 2)} {c cP : Control}
    {r sP : GalilVM}
    (hCtx : FoundCompareCtxC centre place entry q first w c r cP sP)
    (hLive : PalPeg.CloseoutWatchRound5.PrepLandingLiveC (PofC centre place entry w) q first
      cP sP) :
    False := by
  obtain ⟨es0, cF, sF, vq, ch, oF, a, ls, rs, qw, gap, hraw, hseg, hmF, hrF, hcF, havF, hidle,
    hcen, hqe, hf, hmtF, hch, hchne, hoF, hcPe, hsPe⟩ := hCtx
  obtain ⟨wv, hWatch⟩ := prepLandingLiveC_watch_start _ _ _ hLive
  have hChainEq : sP.chain = ch := by rw [hsPe, afterBirth_chain]; rfl
  obtain ⟨lag', margin', hCopy⟩ := chainMatched_copy_stays_copy hch
  rw [hChainEq, hCopy] at hWatch
  exact ChainVM.noConfusion hWatch

/-- **到達可能性まで込めた反証。**  `CloseoutFoundRoute1.foundCompareCtxC_of_found` が
`InvLPC` ＋ `SegReachedW` ＋ found 比較のデータから `FoundCompareCtxC` の証人を出すので、
`hpack` の 4 番目の節（`PrepLandingWatchC`）だけを弱く取り出した形が**そこで偽**になる。

仮説名 `hPrepLandingWatchAtAnyFoundCtx` は過剰量化を名前に出したもの
（CLAUDE.md「過剰量化した仮定には、その過剰量化が名前に出る名前を付ける」）。
`hpack` はこれを含意するので、**`hpack` は found 比較が到達可能な限り偽**。 -/
theorem hpack_false_of_foundReachable {raw : List (Fin 2)} {c c' : Control} {r t : GalilVM}
    (hIC : PalPeg.GalilInvPlus2.InvLPC raw c r)
    (hsW : PalPeg.GalilInvPlus.SegReachedW centre place entry q first raw c r c' t)
    (hClock : c'.clock = 1) (hAvailable : canRight t.right)
    (hMatched : read (left t.left) = read (right t.right))
    (hFound : ∃ vq : SearchVM, searchEffect (PofC centre place entry raw) true t vq ∧
      vq.search.mode = GalilScaffoldSearchFinish.Mode.found)
    (hPrepLandingWatchAtAnyFoundCtx : ∀ (cP : Control) (sP : GalilVM),
      FoundCompareCtxC centre place entry q first raw c r cP sP →
      PrepLandingWatchC (PofC centre place entry raw) q first cP sP) :
    False := by
  obtain ⟨cP, sP, hCtx⟩ :=
    PalPeg.CloseoutFoundRoute1.foundCompareCtxC_of_found centre place entry q first raw
      hIC hsW hClock hAvailable hMatched hFound
  exact hpack_false_of_foundCompareCtx centre place entry q first hCtx
    (hPrepLandingWatchAtAnyFoundCtx cP sP hCtx)

#print axioms prepLandingLiveC_watch_start
#print axioms prepLandingLiveC_false_of_foundCompareCtx
#print axioms hpack_false_of_foundReachable

end

#print axioms chainMatched_copy_stays_copy
#print axioms chainStart_is_copy
#print axioms hpack_false_of_foundCompareCtx


end PalPeg.FoundPackRefute
