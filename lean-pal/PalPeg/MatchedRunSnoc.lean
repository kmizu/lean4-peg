import PalPeg.GalilScaffoldTopMatchedSeq

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

end PalPeg.MatchedRunSnoc
