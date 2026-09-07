import PalPeg.GSScanTapes
import PalPeg.GSRealTime
import PalPeg.RTQueueTapes

/-!
# テキストの供給 (`TextFeed`)

走査段のテキストテープ `Txt` はヘッドが 1 個しかなく、その位置は `pos + q`
（`GSScanTapes.Encodes`）である。ところがオンライン計算では記号は毎ラウンド
到着し、到着境界 `n` はヘッド位置より最大 `|v|` 先に進みうる。テープには
**ヘッドのある場所にしか書けない**ので、到着した記号をそのまま `Txt` に
書き込むことはできない。

本ファイルはその隙間を **Hood–Melville 待ち行列**（`RTQueueTapes`）で埋める。

* ラウンドごとに到着した記号は待ち行列 `B` に `snoc` される（`arrive`, コスト `≤ 26`）。
* 走査テープ `Txt` にはテキストの接頭辞 `Text.take m` だけが書かれており、
  それより右は空白（`padW`）。
* 走査ヘッドが先端セル（添字 `m`）に来て比較したくなったら、まず待ち行列から
  1 記号取り出して（`head?` + `tail`）そのセルに書き（`fill`, コスト `≤ 33`）、
  それから比較する。

## 先端セルの扱い

`Tape.SeqView blank tp w i` は `i < |w|` を要求するので、「ヘッドが接頭辞の
すぐ右の空白セルにいる」状態をそのまま `SeqView` で書くことはできない。
そこで機械が「今テキストだと思っている語」を

`padW blank Text m = Text.take m ++ List.replicate (|Text| + 1 - m) blank`

とする。長さは常に `|Text| + 1` で、添字 `i ≤ m` のあいだ `SeqView` が成り立つ
（`i = m` のときは空白セルを読む）。空白セルは物理的には「まだ書いていないセル」
であり、`replicate` はその明示表現にすぎない（`TapeConfiguration` の `right` に
空白を明示的に置いても機械の観測は変わらない）。

この表現のおかげで `GSScanTapes.encodes_step` を **そのまま** 使える：走査段は
`padW blank Text m` を相手にしていると思って動き、供給が済んでいる添字
（`< m`）でしか読まないので、抽象側の `scanStep` は本物の `Text` に対するものと
一致する（`scanStep_padW`）。

## 主結果

* `fill_feedInv` — 供給は不変条件を保ち、コストは `≤ 33`。
* `arrive_feedInv` — 到着は不変条件を保ち、コストは `≤ 26`。
* `runInT_st` / `runInT_feedInv` / `runInT_cost` — ラウンド内の `gsRate k` 歩は
  `GSRealTime.runIn` に一致し、不変条件を保つ。
* `round_feed` — 1 ラウンド（到着 + 走査）全体。コスト `≤ gsRate k * (c + 33) + 26`。
* `onlineT_st` — 全ラウンドを通して `GSRealTime.onlineRun` に一致する。
-/

namespace PalPeg
namespace TextFeed

open PegSeparation.RealTimeTM
open PalPeg.Tape

variable {sc : ℕ}

/-! ## 0. 走査テープに書かれている語 -/

/-- 機械が「テキスト」だと思っている語：到着済みで書き込み済みの接頭辞
`Text.take m` と、その右の空白セル。長さは（`m ≤ |Text|` のとき）常に `|Text|+1`。 -/
def padW (blank : Fin sc) (Text : List (Fin sc)) (m : ℕ) : List (Fin sc) :=
  Text.take m ++ List.replicate (Text.length + 1 - m) blank

theorem padW_length {blank : Fin sc} {Text : List (Fin sc)} {m : ℕ}
    (hm : m ≤ Text.length) : (padW blank Text m).length = Text.length + 1 := by
  simp only [padW, List.length_append, List.length_take, List.length_replicate]
  omega

theorem padW_getElem?_of_lt {blank : Fin sc} {Text : List (Fin sc)} {m i : ℕ}
    (hm : m ≤ Text.length) (hi : i < m) : (padW blank Text m)[i]? = Text[i]? := by
  have h1 : i < (Text.take m).length := by
    simp only [List.length_take]; omega
  have h2 : i < Text.length := by omega
  rw [padW, List.getElem?_append_left h1]
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, List.getElem_take]

private theorem set_append_len {α : Type _} (l₁ : List α) (x a : α) (l₂ : List α) :
    (l₁ ++ x :: l₂).set l₁.length a = l₁ ++ a :: l₂ := by
  induction l₁ with
  | nil => rfl
  | cons y ys ih => simp [ih]

/-- 先端セルに `Text[m]` を書き込むと、書かれている語がひとつ伸びる。 -/
theorem padW_set {blank : Fin sc} {Text : List (Fin sc)} {m : ℕ} {a : Fin sc}
    (hm : m < Text.length) (ha : Text[m]? = some a) :
    (padW blank Text m).set m a = padW blank Text (m + 1) := by
  have hlen : (Text.take m).length = m := by
    simp only [List.length_take]; omega
  have hrep : Text.length + 1 - m = (Text.length - m) + 1 := by omega
  have htake : Text.take (m + 1) = Text.take m ++ [a] := by
    rw [List.take_add_one, ha]; rfl
  have hrep2 : Text.length + 1 - (m + 1) = Text.length - m := by omega
  have key := set_append_len (Text.take m) blank a
    (List.replicate (Text.length - m) blank)
  rw [hlen] at key
  rw [padW, padW, hrep, List.replicate_succ, key, htake, hrep2]
  simp

/-! ## 1. ずらしによるヘッド添字の変化 -/

theorem gs_index_le {k p₁ r : ℕ} (hk : 0 < k) (q : ℕ) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ q + 1 := by
  unfold gsShift gsNextQ
  split_ifs with hc
  · have hp : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    omega
  · have h := GSTapes.ceilDiv_le_self (k := k) (q := q) hk
    omega

theorem gs_index_le_pos {k p₁ r q : ℕ} (hk : 0 < k) (hq : 0 < q) :
    gsShift k p₁ r q + gsNextQ k p₁ r q ≤ q := by
  unfold gsShift gsNextQ
  split_ifs with hc
  · have hp : p₁ ≤ q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    omega
  · have h := GSTapes.ceilDiv_le_self (k := k) (q := q) hk
    omega

/-- **ヘッドは書き込み済み領域を出ない**：読む一歩の前に供給が済んでいれば
（`hrd`）、一歩あとのヘッド添字も `m` 以下。 -/
theorem scanStep_index_le {v T : List (Fin sc)} {k p₁ r m : ℕ} (hk : 0 < k)
    (hv : 0 < v.length) {st : ScanState} (hle : st.pos + st.q ≤ m)
    (hrd : st.q ≠ v.length → st.pos + st.q < m) :
    (scanStep v k p₁ r T st).pos + (scanStep v k p₁ r T st).q ≤ m := by
  unfold scanStep
  split_ifs with h1 h2
  · have hq : 0 < st.q := by omega
    have h := gs_index_le_pos (p₁ := p₁) (r := r) hk hq
    dsimp only
    omega
  · have h := hrd h1
    dsimp only
    omega
  · have h := hrd h1
    have h2 := gs_index_le (p₁ := p₁) (r := r) hk st.q
    dsimp only
    omega

/-- **接頭辞と本物のテキストは区別できない**：読む添字が書き込み済みなら、
`padW` 上の一歩は `Text` 上の一歩に等しい。 -/
theorem scanStep_padW {blank : Fin sc} {v Text : List (Fin sc)} {k p₁ r m : ℕ}
    {st : ScanState} (hm : m ≤ Text.length)
    (hrd : st.q ≠ v.length → st.pos + st.q < m) :
    scanStep v k p₁ r (padW blank Text m) st = scanStep v k p₁ r Text st := by
  unfold scanStep
  by_cases h1 : st.q = v.length
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, padW_getElem?_of_lt hm (hrd h1)]

theorem stepCost_padW {blank : Fin sc} {v Text : List (Fin sc)} {k p₁ r m : ℕ}
    {st : ScanState} (hm : m ≤ Text.length)
    (hrd : st.q ≠ v.length → st.pos + st.q < m) :
    GSTapes.stepCost v k p₁ r (padW blank Text m) st
      = GSTapes.stepCost v k p₁ r Text st := by
  unfold GSTapes.stepCost
  by_cases h1 : st.q = v.length
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1, padW_getElem?_of_lt hm (hrd h1)]

/-! ## 2. 機械の状態と不変条件 -/

/-- 供給機構つきの機械：走査段の 3 本のテープ、待ち行列の 9 本のテープ、
書き込み済み記号数 `m`、そしてゴーストの走査状態。`R.cost` は
**すべてのテープ動作の総数**（走査段＋待ち行列）を数える。 -/
structure Machine (sc : ℕ) where
  /-- `Txt` テープに書き込み済みの記号数。 -/
  m : ℕ
  /-- 走査段の 3 本のテープ。 -/
  ts : GSTapes.TapesState sc
  /-- 待ち行列（抽象）。 -/
  Q : RTQueue.Queue (Fin sc)
  /-- 待ち行列のテープと総動作数。 -/
  R : RTQueueTapes.Run sc
  /-- 走査状態（ゴースト変数）。 -/
  st : ScanState

/-- 動作数だけ増やす。 -/
def Machine.charge (M : Machine sc) (c : ℕ) : Machine sc :=
  { M with R := ⟨M.R.qt, M.R.cost + c⟩ }

/-- **供給の不変条件**：走査テープは `Text.take m` を保持し、待ち行列には
到着済みで未書き込みの記号 `(Text.take n).drop m` がちょうど入っており、
走査ヘッドは書き込み済み領域を出ていない。 -/
structure FeedInv (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (p₁ n : ℕ) (M : Machine sc) : Prop where
  /-- 走査段の 3 本のテープは、テキストが `padW blank Text M.m` であるかのように
  走査状態 `M.st` を符号化している。 -/
  scan : GSTapes.Encodes blank startSym endSym mark v (padW blank Text M.m) p₁ M.ts M.st
  /-- 待ち行列のテープは `M.Q` を符号化している。 -/
  buf : RTQueueTapes.Encodes blank mark M.R.qt M.Q
  /-- 待ち行列の不変条件。 -/
  qinv : RTQueue.Inv M.Q
  /-- 待ち行列の中身は「到着済みだが未書き込み」の記号列そのもの。 -/
  qlist : RTQueue.toList M.Q = (Text.take n).drop M.m
  /-- 書き込み済み記号は到着済み。 -/
  mle : M.m ≤ n
  /-- 走査ヘッドは書き込み済み領域を出ない。 -/
  hd : M.st.pos + M.st.q ≤ M.m
  /-- 一致長は `|v|` 以下。 -/
  qle : M.st.q ≤ v.length

/-! ## 3. 到着（`arrive`） -/

/-- ラウンドの頭：到着した記号を待ち行列に入れる。 -/
def arrive (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) : Machine sc :=
  { M with Q := RTQueue.snoc M.Q a, R := RTQueueTapes.snocT blank mark M.Q a M.R }

theorem arrive_st (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (arrive blank mark a M).st = M.st := rfl

theorem arrive_m (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (arrive blank mark a M).m = M.m := rfl

/-- **到着は不変条件を保つ**（境界は `n` から `n+1` へ）。 -/
theorem arrive_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {a : Fin sc} {M : Machine sc} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ (n + 1) (arrive blank mark a M) := by
  have hlen : (Text.take n).length = n := by
    simp only [List.length_take]; omega
  refine ⟨h.scan, ?_, RTQueue.inv_snoc h.qinv a, ?_, Nat.le_succ_of_le h.mle, h.hd, h.qle⟩
  · exact RTQueueTapes.snocT_encodes hmb h.buf h.qinv
  · have htake : Text.take (n + 1) = Text.take n ++ [a] := by
      rw [List.take_add_one, ha]; rfl
    show RTQueue.toList (RTQueue.snoc M.Q a) = (Text.take (n + 1)).drop M.m
    rw [RTQueue.toList_snoc h.qinv, h.qlist, htake,
      List.drop_append_of_le_length (by rw [hlen]; exact h.mle)]

/-- 到着のコストは `≤ 26`。 -/
theorem arrive_cost (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (arrive blank mark a M).R.cost ≤ M.R.cost + 26 :=
  RTQueueTapes.snocT_cost blank mark M.Q a M.R

/-! ## 4. 供給（`fill`） -/

/-- 待ち行列の先頭記号（1 動作の probe で読める）。 -/
def peek (blank : Fin sc) (R : RTQueueTapes.Run sc) : Fin sc :=
  Tape.read (RTQueueTapes.run blank R.qt (RTQueueTapes.headProbe blank) .front)

/-- **供給**：待ち行列から 1 記号取り出し、走査テープの先端セルに書く。 -/
def fill (blank mark : Fin sc) (M : Machine sc) : Machine sc :=
  { m := M.m + 1
    ts := { M.ts with Txt := Tape.step blank M.ts.Txt (peek blank M.R) .stay }
    Q := RTQueue.tail M.Q
    R := RTQueueTapes.tailT blank mark M.Q (RTQueueTapes.headT blank M.R)
    st := M.st }

theorem fill_st (blank mark : Fin sc) (M : Machine sc) : (fill blank mark M).st = M.st := rfl

theorem fill_m (blank mark : Fin sc) (M : Machine sc) :
    (fill blank mark M).m = M.m + 1 := rfl

/-- probe が読むのは次に書き込むべき記号 `Text[m]`。 -/
theorem peek_eq {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hn : n ≤ Text.length) (hlt : M.m < n)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    Text[M.m]? = some (peek blank M.R) := by
  have hmT : M.m < Text.length := by omega
  have hlen : (Text.take n).length = n := by
    simp only [List.length_take]; omega
  have hidx : M.m < (Text.take n).length := by rw [hlen]; exact hlt
  have hdrop : (Text.take n).drop M.m
      = (Text.take n)[M.m] :: (Text.take n).drop (M.m + 1) :=
    List.drop_eq_getElem_cons hidx
  have h3 : ((Text.take n).drop M.m).head? = some Text[M.m] := by
    rw [hdrop, List.head?_cons, List.getElem_take]
  have h1 : peek blank M.R = (RTQueue.head? M.Q).getD mark :=
    RTQueueTapes.headT_read h.buf
  rw [h1, RTQueue.head?_eq h.qinv, h.qlist, h3, List.getElem?_eq_getElem hmT]
  rfl

/-- **供給は不変条件を保ち**、書き込み済み記号数がひとつ増える。 -/
theorem fill_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length) (hlt : M.m < n)
    (hhd : M.st.pos + M.st.q = M.m)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ n (fill blank mark M) := by
  have hpk : Text[M.m]? = some (peek blank M.R) := peek_eq hn hlt h
  have htxt : Tape.SeqView blank
      (Tape.step blank M.ts.Txt (peek blank M.R) .stay)
      (padW blank Text (M.m + 1)) (M.st.pos + M.st.q) := by
    have h0 := Tape.seq_write h.scan.txt (peek blank M.R)
    rw [hhd] at h0 ⊢
    rw [padW_set (by omega) hpk] at h0
    exact h0
  refine ⟨⟨h.scan.pat, htxt, h.scan.cnt⟩, ?_, RTQueue.inv_tail h.qinv, ?_,
    (by show M.m + 1 ≤ n; omega), (by show M.st.pos + M.st.q ≤ M.m + 1; omega), h.qle⟩
  · exact RTQueueTapes.tailT_encodes hmb (RTQueueTapes.headT_encodes h.buf) h.qinv
  · show RTQueue.toList (RTQueue.tail M.Q) = (Text.take n).drop (M.m + 1)
    rw [RTQueue.toList_tail h.qinv, h.qlist, List.tail_drop]

/-- 供給のコストは `≤ 33`（probe 2 + `tail` 31）。 -/
theorem fill_cost (blank mark : Fin sc) (M : Machine sc) :
    (fill blank mark M).R.cost ≤ M.R.cost + 33 := by
  have h1 := RTQueueTapes.tailT_cost blank mark M.Q (RTQueueTapes.headT blank M.R)
  have h2 := RTQueueTapes.headT_cost blank M.R
  show (RTQueueTapes.tailT blank mark M.Q (RTQueueTapes.headT blank M.R)).cost ≤ _
  omega

/-- **読み出しの正当性**：書き込み済みの添字なら、走査ヘッドが読む記号は
本物の `Text` のその位置の記号である。したがって `GSScanTapes.Encodes` を
`padW blank Text M.m` について保っておけば、比較の結果は `Text` に対するものと
一致する（`scanStep_padW`）。なお `GSScanTapes.program` はそもそも `Text` を
引数に取らない（分岐はテープの読み取りとオラクルビットだけで決まる）ので、
動作列そのものは「機械が思っているテキスト」に依存しない
（`program_prefix_eq` は `rfl`）。 -/
theorem read_ok {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hn : n ≤ Text.length)
    (hlt : M.st.pos + M.st.q < M.m)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    Text[M.st.pos + M.st.q]? = some (Tape.read M.ts.Txt) := by
  have hr := h.scan.txt.read_eq
  rwa [padW_getElem?_of_lt (le_trans h.mle hn) hlt] at hr

/-- 動作列はテープの中身だけで決まる（テキストにも `m` にも依存しない）。 -/
theorem program_prefix_eq {blank endSym mark : Fin sc} {k : ℕ} {b : Bool}
    {ts ts' : GSTapes.TapesState sc} (h : ts = ts') :
    GSTapes.program blank endSym mark k b ts
      = GSTapes.program blank endSym mark k b ts' := by
  rw [h]

/-! ## 5. 供給の物理的な判定条件

供給すべきかどうかは、`blank` と `mark` がテキストに現れなければ
**テープの読み取りだけで決まる**：走査ヘッドが空白を読めば先端にいて、
待ち行列の probe が `mark` を返せば空である。 -/

/-- 走査ヘッドが空白を読む ⟺ 先端セルにいる。 -/
theorem head_blank_iff {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hn : n ≤ Text.length)
    (hb : blank ∉ Text) (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    Tape.read M.ts.Txt = blank ↔ M.st.pos + M.st.q = M.m := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hread := h.scan.txt.read_eq
  have hlen : (Text.take M.m).length = M.m := by
    simp only [List.length_take]; omega
  constructor
  · intro hbl
    by_contra hne
    have hlt : M.st.pos + M.st.q < M.m := by have := h.hd; omega
    rw [hbl, padW_getElem?_of_lt hmT hlt] at hread
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hread
    exact hb (h2 ▸ List.getElem_mem h1)
  · intro heq
    rw [heq] at hread
    have hb2 : (padW blank Text M.m)[M.m]? = some blank := by
      rw [padW, List.getElem?_append_right (by omega : (Text.take M.m).length ≤ M.m),
        hlen, Nat.sub_self, List.getElem?_replicate]
      have hpos : 0 < Text.length + 1 - M.m := by omega
      simp [hpos]
    rw [hb2] at hread
    exact (Option.some.inj hread).symm

/-- 待ち行列の probe が `mark` を返す ⟺ 未書き込みの記号がない。 -/
theorem queue_empty_iff {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hn : n ≤ Text.length) (hm : mark ∉ Text)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    peek blank M.R = mark ↔ M.m = n := by
  have h1 : peek blank M.R = (RTQueue.head? M.Q).getD mark :=
    RTQueueTapes.headT_read h.buf
  have h2 : RTQueue.head? M.Q = ((Text.take n).drop M.m).head? := by
    rw [RTQueue.head?_eq h.qinv, h.qlist]
  constructor
  · intro hp
    by_contra hne
    have hlt : M.m < n := by have := h.mle; omega
    have h3 : Text[M.m]? = some (peek blank M.R) := peek_eq hn hlt h
    rw [hp] at h3
    obtain ⟨i1, i2⟩ := List.getElem?_eq_some_iff.1 h3
    exact hm (i2 ▸ List.getElem_mem i1)
  · intro he
    have hnil : (Text.take n).drop M.m = [] := by
      rw [he]
      exact List.drop_eq_nil_of_le (by simp only [List.length_take]; omega)
    rw [h1, h2, hnil]
    rfl

/-! ## 6. 走査の一歩 -/

/-- 一歩の動作列（周期条件はオラクルビットではなく直接計算する）。 -/
def scanProg (blank endSym mark : Fin sc) (k p₁ r : ℕ) (M : Machine sc) :
    List (GSTapes.Act sc) :=
  GSTapes.program blank endSym mark k (decide (k * p₁ ≤ M.st.q ∧ M.st.q ≤ r)) M.ts

/-- 走査段の一歩（テープ動作を実行し、ゴースト状態を `scanStep` で進める）。 -/
def scanOne (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : Machine sc) : Machine sc :=
  { m := M.m
    ts := GSTapes.applyActs blank (scanProg blank endSym mark k p₁ r M) M.ts
    Q := M.Q
    R := ⟨M.R.qt, M.R.cost + (scanProg blank endSym mark k p₁ r M).length⟩
    st := scanStep v k p₁ r Text M.st }

theorem scanOne_st (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : Machine sc) :
    (scanOne blank endSym mark v k p₁ r Text M).st = scanStep v k p₁ r Text M.st := rfl

/-- **一歩の実現**：供給が済んでいれば（`hrd`）、走査段の一歩はテープ上で
実現され、不変条件を保つ。 -/
theorem scanOne_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n k r : ℕ} {M : Machine sc} (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length)
    (hrd : M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ n
      (scanOne blank endSym mark v k p₁ r Text M) := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hidx : (scanStep v k p₁ r Text M.st).pos + (scanStep v k p₁ r Text M.st).q ≤ M.m :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd hrd
  have hstep : scanStep v k p₁ r (padW blank Text M.m) M.st = scanStep v k p₁ r Text M.st :=
    scanStep_padW hmT hrd
  have hfit : (scanStep v k p₁ r (padW blank Text M.m) M.st).pos +
      (scanStep v k p₁ r (padW blank Text M.m) M.st).q < (padW blank Text M.m).length := by
    rw [hstep, padW_length hmT]
    omega
  have hE := GSTapes.encodes_step (r := r) (b := decide (k * p₁ ≤ M.st.q ∧ M.st.q ≤ r))
    hk hend h.scan h.qle rfl hfit
  rw [hstep] at hE
  refine ⟨hE, h.buf, h.qinv, h.qlist, h.mle, hidx, ?_⟩
  exact scanStep_q_le h.qle

/-- 一歩のコストは `GSScanTapes.stepCost`。 -/
theorem scanOne_cost {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n k r : ℕ} {M : Machine sc} (hk : 0 < k) (hend : endSym ∉ v) (hn : n ≤ Text.length)
    (hrd : M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    (scanOne blank endSym mark v k p₁ r Text M).R.cost
      = M.R.cost + GSTapes.stepCost v k p₁ r Text M.st := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hlen := GSTapes.program_length (r := r)
    (b := decide (k * p₁ ≤ M.st.q ∧ M.st.q ≤ r)) hk hend h.scan h.qle rfl
  show M.R.cost + (scanProg blank endSym mark k p₁ r M).length = _
  rw [scanProg, hlen, stepCost_padW hmT hrd]

/-! ## 7. ラウンド内の実行 -/

/-- 走査ヘッドが先端にいて、まだ未書き込みの記号があるなら 1 つ供給する。 -/
def fillIf (blank mark : Fin sc) (n : ℕ) (M : Machine sc) : Machine sc :=
  if M.st.pos + M.st.q = M.m ∧ M.m < n then fill blank mark M else M

theorem fillIf_st (blank mark : Fin sc) (n : ℕ) (M : Machine sc) :
    (fillIf blank mark n M).st = M.st := by
  unfold fillIf; split_ifs <;> rfl

theorem fillIf_cost (blank mark : Fin sc) (n : ℕ) (M : Machine sc) :
    (fillIf blank mark n M).R.cost ≤ M.R.cost + 33 := by
  unfold fillIf
  split_ifs with hc
  · exact fill_cost blank mark M
  · omega

theorem fillIf_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ n (fillIf blank mark n M) := by
  unfold fillIf
  split_ifs with hc
  · exact fill_feedInv hmb hn hc.2 hc.1 h
  · exact h

/-- **供給後は読める**：`Enabled` な一歩の直前に `fillIf` を通せば、
比較する添字は必ず書き込み済み。 -/
theorem fillIf_ready {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc}
    (h : FeedInv blank startSym endSym mark v Text p₁ n M)
    (he : Enabled v n M.st) :
    (fillIf blank mark n M).st.q ≠ v.length →
      (fillIf blank mark n M).st.pos + (fillIf blank mark n M).st.q
        < (fillIf blank mark n M).m := by
  rw [fillIf_st]
  intro hq
  have hlt : M.st.pos + M.st.q < n := by
    rcases he with h1 | h1
    · exact absurd h1 hq
    · exact h1
  unfold fillIf
  by_cases hc : M.st.pos + M.st.q = M.m ∧ M.m < n
  · rw [if_pos hc]
    show M.st.pos + M.st.q < M.m + 1
    omega
  · rw [if_neg hc]
    have := h.hd
    have := h.mle
    by_cases he2 : M.st.pos + M.st.q = M.m
    · exact absurd ⟨he2, by omega⟩ hc
    · omega

/-- ラウンド `n` の中で高々 `j` 歩。各歩の前に必要なら供給する。 -/
def runInT (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) : ℕ → Machine sc → Machine sc
  | 0, M => M
  | j + 1, M =>
      if Enabled v n (fillIf blank mark n M).st then
        runInT blank endSym mark v k p₁ r n Text j
          (scanOne blank endSym mark v k p₁ r Text (fillIf blank mark n M))
      else fillIf blank mark n M

/-- **抽象側との一致**：ゴースト状態は `GSRealTime.runIn` に一致する。 -/
theorem runInT_st (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) :
    ∀ (j : ℕ) (M : Machine sc),
      (runInT blank endSym mark v k p₁ r n Text j M).st = runIn v k p₁ r Text n j M.st := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih =>
    intro M
    rw [runInT, runIn, fillIf_st]
    split_ifs with he
    · rw [ih, scanOne_st, fillIf_st]
    · rw [fillIf_st]

/-- **不変条件はラウンド内で保たれる**。 -/
theorem runInT_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n k r : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : Machine sc), FeedInv blank startSym endSym mark v Text p₁ n M →
      FeedInv blank startSym endSym mark v Text p₁ n
        (runInT blank endSym mark v k p₁ r n Text j M) := by
  intro j
  induction j with
  | zero => intro M h; exact h
  | succ j ih =>
    intro M h
    rw [runInT]
    split_ifs with he
    · rw [fillIf_st] at he
      exact ih _ (scanOne_feedInv (r := r) hk hv hend hn (fillIf_ready h he)
        (fillIf_feedInv hmb hn h))
    · exact fillIf_feedInv hmb hn h

/-- ラウンド内のコスト（供給 `29` ＋ 走査の一歩）。 -/
def runInCost (v : List (Fin sc)) (k p₁ r n : ℕ) (Text : List (Fin sc)) :
    ℕ → ScanState → ℕ
  | 0, _ => 0
  | j + 1, st =>
      33 + (if Enabled v n st then
              GSTapes.stepCost v k p₁ r Text st
                + runInCost v k p₁ r n Text j (scanStep v k p₁ r Text st)
            else 0)

/-- **ラウンド内のコスト**。 -/
theorem runInT_cost {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n k r : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : Machine sc), FeedInv blank startSym endSym mark v Text p₁ n M →
      (runInT blank endSym mark v k p₁ r n Text j M).R.cost
        ≤ M.R.cost + runInCost v k p₁ r n Text j M.st := by
  intro j
  induction j with
  | zero => intro M _; exact Nat.le_add_right _ _
  | succ j ih =>
    intro M h
    have hf := fillIf_feedInv (blank := blank) (mark := mark) hmb hn h
    have hfc := fillIf_cost blank mark n M
    rw [runInT, fillIf_st, runInCost]
    split_ifs with he
    · have hrd := fillIf_ready (blank := blank) (mark := mark) h he
      have h1 := ih _ (scanOne_feedInv (r := r) hk hv hend hn hrd hf)
      have h2 := scanOne_cost (r := r) hk hend hn hrd hf
      rw [scanOne_st, fillIf_st] at h1
      rw [fillIf_st] at h2
      omega
    · omega

/-- `q ≤ |v|` の状態で一歩あたり `c` 動作という上界があれば、ラウンド内は
`j * (c + 33)` で押さえられる。 -/
theorem runInCost_le {v Text : List (Fin sc)} {p₁ n k r c : ℕ}
    (hc : ∀ st : ScanState, st.q ≤ v.length → GSTapes.stepCost v k p₁ r Text st ≤ c) :
    ∀ (j : ℕ) (st : ScanState), st.q ≤ v.length →
      runInCost v k p₁ r n Text j st ≤ j * (c + 33) := by
  intro j
  induction j with
  | zero => intro st _; simp [runInCost]
  | succ j ih =>
    intro st hq
    rw [runInCost]
    have h1 := hc st hq
    have h2 := ih (scanStep v k p₁ r Text st) (scanStep_q_le hq)
    have e : (j + 1) * (c + 33) = j * (c + 33) + (c + 33) := by ring
    split_ifs with he <;> omega

/-! ## 8. 1 ラウンド -/

/-- **1 ラウンド**：到着した記号を待ち行列へ入れ、`gsRate k` 歩の走査を
（必要な供給を挟みながら）実行する。 -/
def roundT (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (a : Fin sc) (M : Machine sc) : Machine sc :=
  runInT blank endSym mark v k p₁ r (n + 1) Text (gsRate k)
    (arrive blank mark a M)

/-- **1 ラウンドの主定理**：ゴースト状態は `GSRealTime` のラウンドに一致し、
不変条件は保たれ、動作数は `gsRate k * (c + 33) + 26` 以内。 -/
theorem round_feed {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n k r c : ℕ} {a : Fin sc} {M : Machine sc} (hmb : mark ≠ blank) (hk : 0 < k)
    (hv : 0 < v.length) (hend : endSym ∉ v) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hc : ∀ st : ScanState, st.q ≤ v.length → GSTapes.stepCost v k p₁ r Text st ≤ c)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    (roundT blank endSym mark v k p₁ r n Text a M).st
        = runIn v k p₁ r Text (n + 1) (gsRate k) M.st ∧
      FeedInv blank startSym endSym mark v Text p₁ (n + 1)
        (roundT blank endSym mark v k p₁ r n Text a M) ∧
      (roundT blank endSym mark v k p₁ r n Text a M).R.cost
        ≤ M.R.cost + gsRate k * (c + 33) + 26 := by
  have hA := arrive_feedInv (blank := blank) (mark := mark) hmb hn ha h
  have hAc := arrive_cost blank mark a M
  refine ⟨?_, ?_, ?_⟩
  · rw [roundT, runInT_st, arrive_st]
  · exact runInT_feedInv hmb hk hv hend (by omega) _ _ hA
  · have h1 := runInT_cost (r := r) hmb hk hv hend (by omega : n + 1 ≤ Text.length)
      (gsRate k) (arrive blank mark a M) hA
    have h2 := runInCost_le (n := n + 1) hc (gsRate k) (arrive blank mark a M).st hA.qle
    show (runInT blank endSym mark v k p₁ r (n + 1) Text (gsRate k)
      (arrive blank mark a M)).R.cost ≤ _
    omega

/-! ## 9. 起動フェーズ：走査ヘッドを開始位置 `|u|` まで歩かせる

走査は `⟨|u|, 0⟩` から始まる（`GSRealTime.onlineRun`）。しかし最初の `|u|`
ラウンドは `Enabled` が偽なので抽象側は 1 歩も進まない（`onlineRun_start`）。
その間に機械は、到着した記号を書きながら `Txt` のヘッドを 1 セルずつ右へ運ぶ。
この段階でもゴースト状態 `⟨n, 0⟩` に対する `FeedInv` がそのまま成り立つ。 -/

/-- 走査テープのヘッドを 1 セル右へ（読んだ記号を書き戻す）。 -/
def stepRight (blank : Fin sc) (M : Machine sc) : Machine sc :=
  { m := M.m
    ts := { M.ts with Txt := Tape.step blank M.ts.Txt M.ts.Txt.focus .right }
    Q := M.Q
    R := ⟨M.R.qt, M.R.cost + 1⟩
    st := ⟨M.st.pos + 1, M.st.q⟩ }

theorem stepRight_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {M : Machine sc} (hm : M.st.pos + M.st.q + 1 ≤ M.m)
    (hmT : M.m ≤ Text.length) (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ n (stepRight blank M) := by
  have hlt : M.st.pos + M.st.q + 1 < (padW blank Text M.m).length := by
    rw [padW_length hmT]; omega
  have htxt := Tape.seq_move_right h.scan.txt hlt
  refine ⟨⟨h.scan.pat, ?_, h.scan.cnt⟩, h.buf, h.qinv, h.qlist, h.mle, ?_, h.qle⟩
  · show Tape.SeqView blank (Tape.step blank M.ts.Txt M.ts.Txt.focus .right)
      (padW blank Text M.m) (M.st.pos + 1 + M.st.q)
    have e : M.st.pos + 1 + M.st.q = M.st.pos + M.st.q + 1 := by omega
    rw [e]; exact htxt
  · show M.st.pos + 1 + M.st.q ≤ M.m
    omega

/-- 起動フェーズの 1 ラウンド：到着 → 供給 → ヘッドを 1 右へ。 -/
def startRound (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) : Machine sc :=
  stepRight blank (fill blank mark (arrive blank mark a M))

theorem startRound_st (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (startRound blank mark a M).st = ⟨M.st.pos + 1, M.st.q⟩ := rfl

theorem startRound_m (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (startRound blank mark a M).m = M.m + 1 := rfl

theorem startRound_cost (blank mark : Fin sc) (a : Fin sc) (M : Machine sc) :
    (startRound blank mark a M).R.cost ≤ M.R.cost + 60 := by
  have h1 := arrive_cost blank mark a M
  have h2 := fill_cost blank mark (arrive blank mark a M)
  show (fill blank mark (arrive blank mark a M)).R.cost + 1 ≤ M.R.cost + 60
  omega

theorem startRound_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ n : ℕ} {a : Fin sc} {M : Machine sc} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (hm : M.m = n) (hpos : M.st.pos = n) (hq : M.st.q = 0)
    (h : FeedInv blank startSym endSym mark v Text p₁ n M) :
    FeedInv blank startSym endSym mark v Text p₁ (n + 1) (startRound blank mark a M) := by
  have h1 := arrive_feedInv (blank := blank) (mark := mark) hmb hn ha h
  have h2 : FeedInv blank startSym endSym mark v Text p₁ (n + 1)
      (fill blank mark (arrive blank mark a M)) := by
    refine fill_feedInv hmb ?_ ?_ ?_ h1
    · omega
    · show M.m < n + 1
      omega
    · show M.st.pos + M.st.q = M.m
      omega
  refine stepRight_feedInv ?_ ?_ h2
  · show M.st.pos + M.st.q + 1 ≤ M.m + 1
    omega
  · show M.m + 1 ≤ Text.length
    omega

/-- 起動フェーズ全体（`n` ラウンド）。 -/
def startT (blank mark : Fin sc) (Text : List (Fin sc)) : ℕ → Machine sc → Machine sc
  | 0, M => M
  | n + 1, M => startRound blank mark (Text.getD n blank) (startT blank mark Text n M)

theorem getD_eq {blank : Fin sc} {Text : List (Fin sc)} {n : ℕ} (hn : n < Text.length) :
    Text[n]? = some (Text.getD n blank) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
  rfl

/-- **起動フェーズの主定理**：`n` ラウンドで書き込み済み記号数もヘッド位置も `n`
になり、不変条件が保たれる。動作数は 1 ラウンド `60` 以内。 -/
theorem startT_spec {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ : ℕ} {M : Machine sc} (hmb : mark ≠ blank) (hm : M.m = 0) (hst : M.st = ⟨0, 0⟩)
    (h : FeedInv blank startSym endSym mark v Text p₁ 0 M) :
    ∀ n, n ≤ Text.length →
      FeedInv blank startSym endSym mark v Text p₁ n (startT blank mark Text n M) ∧
        (startT blank mark Text n M).st = ⟨n, 0⟩ ∧
        (startT blank mark Text n M).m = n ∧
        (startT blank mark Text n M).R.cost ≤ M.R.cost + 60 * n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨h, hst, hm, by simp [startT]⟩
  | succ n ih =>
    intro hle
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have hc := startRound_cost blank mark (Text.getD n blank) (startT blank mark Text n M)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact startRound_feedInv hmb (by omega) (getD_eq (by omega)) i3
        (by rw [i2]) (by rw [i2]) i1
    · rw [startT, startRound_st, i2]
    · rw [startT, startRound_m, i3]
    · show (startRound blank mark (Text.getD n blank) (startT blank mark Text n M)).R.cost
        ≤ M.R.cost + 60 * (n + 1)
      have e : 60 * (n + 1) = 60 * n + 60 := by ring
      omega

/-! ## 10. 全ラウンド -/

/-- ラウンド `s` から `s + n - 1` まで。到着する記号はテキストから読む。 -/
def onlineT (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (s : ℕ) : ℕ → Machine sc → Machine sc
  | 0, M => M
  | n + 1, M =>
      roundT blank endSym mark v k p₁ r (s + n) Text (Text.getD (s + n) blank)
        (onlineT blank endSym mark v k p₁ r Text s n M)

theorem runIn_stuck {v Text : List (Fin sc)} {k p₁ r n : ℕ} {st : ScanState}
    (he : ¬ Enabled v n st) (j : ℕ) : runIn v k p₁ r Text n j st = st := by
  cases j with
  | zero => rfl
  | succ j => rw [runIn, if_neg he]

/-- 最初の `|u|` ラウンドは抽象側では 1 歩も進まない。 -/
theorem onlineRun_start {u v Text : List (Fin sc)} {k p₁ r : ℕ} (hv : 0 < v.length) :
    ∀ n, n ≤ u.length → onlineRun u v k p₁ r Text n = ⟨u.length, 0⟩ := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hle
    show runIn v k p₁ r Text (n + 1) (gsRate k) (onlineRun u v k p₁ r Text n) = _
    rw [ih (by omega)]
    refine runIn_stuck ?_ _
    rintro (h1 | h1) <;> simp only [] at h1 <;> omega

/-- **全ラウンドの一致**：ゴースト状態は `GSRealTime.onlineRun` に一致する。 -/
theorem onlineT_st {u v Text : List (Fin sc)} {blank endSym mark : Fin sc} {k p₁ r s : ℕ}
    {M : Machine sc} (hM : M.st = onlineRun u v k p₁ r Text s) :
    ∀ n, (onlineT blank endSym mark v k p₁ r Text s n M).st
      = onlineRun u v k p₁ r Text (s + n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    have e : s + (n + 1) = (s + n) + 1 := by omega
    rw [onlineT, roundT, runInT_st, arrive_st, ih, e]
    rfl

/-- **全ラウンドの不変条件とコスト**。 -/
theorem onlineT_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {p₁ k r c s : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v)
    (hc : ∀ st : ScanState, st.q ≤ v.length → GSTapes.stepCost v k p₁ r Text st ≤ c) :
    ∀ (n : ℕ) (M : Machine sc), s + n ≤ Text.length →
      FeedInv blank startSym endSym mark v Text p₁ s M →
      FeedInv blank startSym endSym mark v Text p₁ (s + n)
          (onlineT blank endSym mark v k p₁ r Text s n M) ∧
        (onlineT blank endSym mark v k p₁ r Text s n M).R.cost
          ≤ M.R.cost + n * (gsRate k * (c + 33) + 26) := by
  intro n
  induction n with
  | zero => intro M _ h; exact ⟨h, by simp [onlineT]⟩
  | succ n ih =>
    intro M hle h
    obtain ⟨i1, i2⟩ := ih M (by omega) h
    obtain ⟨_, r2, r3⟩ := round_feed (a := Text.getD (s + n) blank) hmb hk hv hend
      (by omega : s + n < Text.length) (getD_eq (by omega)) hc i1
    have e1 : s + (n + 1) = (s + n) + 1 := by omega
    refine ⟨by rw [e1]; exact r2, ?_⟩
    have e : (n + 1) * (gsRate k * (c + 33) + 26)
        = n * (gsRate k * (c + 33) + 26) + (gsRate k * (c + 33) + 26) := by ring
    show (roundT blank endSym mark v k p₁ r (s + n) Text (Text.getD (s + n) blank)
      (onlineT blank endSym mark v k p₁ r Text s n M)).R.cost ≤ _
    omega

/-! ## 11. 初期状態 -/

/-- 初期テープ：`P` は `startSym` の右（添字 `1`）、`Txt` は全部空白でヘッドは
セル `0`、`Cnt` は `p₁` を保持、待ち行列の 9 本は空。 -/
def initM (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc)) (p₁ : ℕ) :
    Machine sc :=
  { m := 0
    ts := { P := ⟨[startSym], (v ++ [endSym]).headD blank, (v ++ [endSym]).tail⟩
            Txt := ⟨[], blank, List.replicate Text.length blank⟩
            Cnt := ⟨List.replicate p₁ blank ++ [mark], blank, []⟩ }
    Q := (RTQueue.empty : RTQueue.Queue (Fin sc))
    R := ⟨RTQueueTapes.initQT blank mark, 0⟩
    st := ⟨0, 0⟩ }

theorem initM_feedInv (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (p₁ : ℕ) :
    FeedInv blank startSym endSym mark v Text p₁ 0
      (initM blank startSym endSym mark v Text p₁) := by
  have hp0 : padW blank Text 0 = blank :: List.replicate Text.length blank := by
    simp [padW, List.replicate_succ]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, v ++ [endSym] = x :: xs := by
    cases hv2 : v with
    | nil => exact ⟨endSym, [], by simp⟩
    | cons y ys => exact ⟨y, ys ++ [endSym], by simp⟩
  refine ⟨⟨?_, ?_, ⟨rfl, rfl, Tape.blanks_nil blank⟩⟩,
    RTQueueTapes.initQT_encodes blank mark, RTQueue.inv_empty, ?_,
    Nat.le_refl 0, Nat.le_refl 0, Nat.zero_le _⟩
  · show Tape.SeqView blank ⟨[startSym], (v ++ [endSym]).headD blank, (v ++ [endSym]).tail⟩
      (startSym :: (v ++ [endSym])) (0 + 1)
    rw [hx]
    exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
  · show Tape.SeqView blank ⟨[], blank, List.replicate Text.length blank⟩
      (padW blank Text 0) (0 + 0)
    rw [hp0]
    exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
  · show RTQueue.toList (RTQueue.empty : RTQueue.Queue (Fin sc)) = (Text.take 0).drop 0
    simp [RTQueue.toList_empty]

/-- **主定理**：空のテープから出発し、`|u|` ラウンドの起動フェーズ
（1 ラウンド `≤ 60` 動作）ののち、各ラウンドで到着記号 1 つを待ち行列へ入れ
`gsRate k` 歩の走査を（必要な供給を挟みながら）実行する機械は、

* ゴースト状態が `GSRealTime.onlineRun` に一致し（＝実時間の答えが出せる）、
* 供給の不変条件を保ち、
* 1 ラウンドあたり `gsRate k * (c + 33) + 26` 動作以内で動く。

`c` は 1 走査ステップの動作数の上界（`GSScanTapes.stepCost`）。 -/
theorem feed_online {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {p₁ k r c : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v)
    (hc : ∀ st : ScanState, st.q ≤ v.length → GSTapes.stepCost v k p₁ r Text st ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length) :
    (onlineT blank endSym mark v k p₁ r Text u.length n
          (startT blank mark Text u.length
            (initM blank startSym endSym mark v Text p₁))).st
        = onlineRun u v k p₁ r Text (u.length + n) ∧
      FeedInv blank startSym endSym mark v Text p₁ (u.length + n)
          (onlineT blank endSym mark v k p₁ r Text u.length n
            (startT blank mark Text u.length
              (initM blank startSym endSym mark v Text p₁))) ∧
      (onlineT blank endSym mark v k p₁ r Text u.length n
            (startT blank mark Text u.length
              (initM blank startSym endSym mark v Text p₁))).R.cost
        ≤ 60 * u.length + n * (gsRate k * (c + 33) + 26) := by
  obtain ⟨s1, s2, _, s4⟩ := startT_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (p₁ := p₁) hmb rfl rfl
    (initM_feedInv blank startSym endSym mark v Text p₁) u.length (by omega)
  have hst : (startT blank mark Text u.length
      (initM blank startSym endSym mark v Text p₁)).st
      = onlineRun u v k p₁ r Text u.length := by
    rw [s2, onlineRun_start (u := u) (Text := Text) (k := k) (p₁ := p₁) (r := r) hv
      u.length (Nat.le_refl _)]
  obtain ⟨o1, o2⟩ := onlineT_feedInv (s := u.length) hmb hk hv hend hc n _ hn s1
  refine ⟨onlineT_st hst n, o1, ?_⟩
  have : (initM blank startSym endSym mark v Text p₁).R.cost = 0 := rfl
  omega

/-! ## 12. 定数 -/

example : (26 : ℕ) = 26 := rfl   -- `arrive`（`snoc`）の動作数上界
example : (33 : ℕ) = 2 + 31 := rfl -- `fill`（`head?` + `tail`）の動作数上界
example : (60 : ℕ) = 26 + 33 + 1 := rfl -- 起動フェーズ 1 ラウンド
example : gsRate 8 = 9 := by decide

/-! ## 13. オラクル無し版への移植 (`NoOracle`)

`GSScanTapes` の `section NoOracle` は、周期条件 `k*p₁ ≤ q ∧ q ≤ r` を
オラクルビットではなく 4 本の飽和カウンタで判定する 8 本テープ版
(`TapesState' = Fin 8 → TapeConfiguration`, `program'`, `encodes_step'`) を与える。
供給機構はテキストテープ `tT` にしか触らないので、`padW` による「先端セルの
SeqView 化」はそのまま通用し、上の議論を機械的に移植できる。

コスト定数は待ち行列側が同じ（`arrive' ≤ 26`, `fill' ≤ 33`）で、走査側は
`program_cost'` の `A' = 8k + 13`, `B' = 8`（`stepCost'`）。 -/

section NoOracle

/-- テキストテープ以外は `fill'`/`stepRight'` で変わらない。 -/
private theorem upd_tT_ne {i : Fin 8} (h : i ≠ GSTapes.tT) (ts : GSTapes.TapesState' sc)
    (tp : TapeConfiguration sc) : GSTapes.upd ts GSTapes.tT tp i = ts i :=
  GSTapes.upd_ne _ _ h

/-- 供給機構つきの機械（オラクル無し版）：走査段は 8 本、待ち行列は 9 本。 -/
structure Machine' (sc : ℕ) where
  /-- `tT` に書き込み済みの記号数。 -/
  m : ℕ
  /-- 走査段の 8 本のテープ。 -/
  ts : GSTapes.TapesState' sc
  /-- 待ち行列（抽象）。 -/
  Q : RTQueue.Queue (Fin sc)
  /-- 待ち行列のテープと総動作数。 -/
  R : RTQueueTapes.Run sc
  /-- 走査状態（ゴースト変数）。 -/
  st : ScanState

/-- 供給の不変条件（オラクル無し版）。 -/
structure FeedInv' (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r n : ℕ) (M : Machine' sc) : Prop where
  /-- 8 本のテープは、テキストが `padW blank Text M.m` であるかのように符号化する。 -/
  scan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m) k p₁ r M.ts M.st
  /-- 待ち行列のテープは `M.Q` を符号化している。 -/
  buf : RTQueueTapes.Encodes blank mark M.R.qt M.Q
  /-- 待ち行列の不変条件。 -/
  qinv : RTQueue.Inv M.Q
  /-- 待ち行列の中身は「到着済みだが未書き込み」の記号列。 -/
  qlist : RTQueue.toList M.Q = (Text.take n).drop M.m
  /-- 書き込み済み記号は到着済み。 -/
  mle : M.m ≤ n
  /-- 走査ヘッドは書き込み済み領域を出ない。 -/
  hd : M.st.pos + M.st.q ≤ M.m
  /-- 一致長は `|v|` 以下。 -/
  qle : M.st.q ≤ v.length

/-! ### 到着 -/

def arrive' (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) : Machine' sc :=
  { M with Q := RTQueue.snoc M.Q a, R := RTQueueTapes.snocT blank mark M.Q a M.R }

theorem arrive'_st (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) :
    (arrive' blank mark a M).st = M.st := rfl

theorem arrive'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {a : Fin sc} {M : Machine' sc} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r (n + 1) (arrive' blank mark a M) := by
  have hlen : (Text.take n).length = n := by
    simp only [List.length_take]; omega
  refine ⟨h.scan, ?_, RTQueue.inv_snoc h.qinv a, ?_, Nat.le_succ_of_le h.mle, h.hd, h.qle⟩
  · exact RTQueueTapes.snocT_encodes hmb h.buf h.qinv
  · have htake : Text.take (n + 1) = Text.take n ++ [a] := by
      rw [List.take_add_one, ha]; rfl
    show RTQueue.toList (RTQueue.snoc M.Q a) = (Text.take (n + 1)).drop M.m
    rw [RTQueue.toList_snoc h.qinv, h.qlist, htake,
      List.drop_append_of_le_length (by rw [hlen]; exact h.mle)]

/-- 到着のコストは `≤ 26`。 -/
theorem arrive'_cost (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) :
    (arrive' blank mark a M).R.cost ≤ M.R.cost + 26 :=
  RTQueueTapes.snocT_cost blank mark M.Q a M.R

/-! ### 供給 -/

/-- **供給**：待ち行列から 1 記号取り出し、テキストテープ `tT` の先端セルに書く。 -/
def fill' (blank mark : Fin sc) (M : Machine' sc) : Machine' sc :=
  { m := M.m + 1
    ts := GSTapes.upd M.ts GSTapes.tT
            (Tape.step blank (M.ts GSTapes.tT) (peek blank M.R) .stay)
    Q := RTQueue.tail M.Q
    R := RTQueueTapes.tailT blank mark M.Q (RTQueueTapes.headT blank M.R)
    st := M.st }

theorem fill'_st (blank mark : Fin sc) (M : Machine' sc) : (fill' blank mark M).st = M.st := rfl

theorem peek'_eq {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hn : n ≤ Text.length) (hlt : M.m < n)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    Text[M.m]? = some (peek blank M.R) := by
  have hmT : M.m < Text.length := by omega
  have hlen : (Text.take n).length = n := by
    simp only [List.length_take]; omega
  have hidx : M.m < (Text.take n).length := by rw [hlen]; exact hlt
  have hdrop : (Text.take n).drop M.m
      = (Text.take n)[M.m] :: (Text.take n).drop (M.m + 1) :=
    List.drop_eq_getElem_cons hidx
  have h3 : ((Text.take n).drop M.m).head? = some Text[M.m] := by
    rw [hdrop, List.head?_cons, List.getElem_take]
  have h1 : peek blank M.R = (RTQueue.head? M.Q).getD mark :=
    RTQueueTapes.headT_read h.buf
  rw [h1, RTQueue.head?_eq h.qinv, h.qlist, h3, List.getElem?_eq_getElem hmT]
  rfl

/-- **供給は不変条件を保つ**（オラクル無し版）。 -/
theorem fill'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (hlt : M.m < n) (hhd : M.st.pos + M.st.q = M.m)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r n (fill' blank mark M) := by
  have hpk : Text[M.m]? = some (peek blank M.R) := peek'_eq hn hlt h
  have htxt : Tape.SeqView blank
      (Tape.step blank (M.ts GSTapes.tT) (peek blank M.R) .stay)
      (padW blank Text (M.m + 1)) (M.st.pos + M.st.q) := by
    have h0 := Tape.seq_write h.scan.txt (peek blank M.R)
    rw [hhd] at h0 ⊢
    rw [padW_set (by omega) hpk] at h0
    exact h0
  have hts : (fill' blank mark M).ts
      = GSTapes.upd M.ts GSTapes.tT
          (Tape.step blank (M.ts GSTapes.tT) (peek blank M.R) .stay) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, ?_, RTQueue.inv_tail h.qinv, ?_,
    (by show M.m + 1 ≤ n; omega), (by show M.st.pos + M.st.q ≤ M.m + 1; omega), h.qle⟩
  · rw [hts, upd_tT_ne (i := GSTapes.tP) (by decide)]; exact h.scan.pat
  · rw [hts, GSTapes.upd_self]; exact htxt
  · rw [hts, upd_tT_ne (i := GSTapes.tC1) (by decide)]; exact h.scan.c1
  · rw [hts, upd_tT_ne (i := GSTapes.tC2) (by decide)]; exact h.scan.c2
  · rw [hts, upd_tT_ne (i := GSTapes.tAp) (by decide)]; exact h.scan.quad.ap
  · rw [hts, upd_tT_ne (i := GSTapes.tAn) (by decide)]; exact h.scan.quad.an
  · rw [hts, upd_tT_ne (i := GSTapes.tRp) (by decide)]; exact h.scan.quad.rp
  · rw [hts, upd_tT_ne (i := GSTapes.tRn) (by decide)]; exact h.scan.quad.rn
  · exact RTQueueTapes.tailT_encodes hmb (RTQueueTapes.headT_encodes h.buf) h.qinv
  · show RTQueue.toList (RTQueue.tail M.Q) = (Text.take n).drop (M.m + 1)
    rw [RTQueue.toList_tail h.qinv, h.qlist, List.tail_drop]

/-- 供給のコストは `≤ 33`。 -/
theorem fill'_cost (blank mark : Fin sc) (M : Machine' sc) :
    (fill' blank mark M).R.cost ≤ M.R.cost + 33 := by
  have h1 := RTQueueTapes.tailT_cost blank mark M.Q (RTQueueTapes.headT blank M.R)
  have h2 := RTQueueTapes.headT_cost blank M.R
  show (RTQueueTapes.tailT blank mark M.Q (RTQueueTapes.headT blank M.R)).cost ≤ _
  omega

/-- **読み出しの正当性**（オラクル無し版）。 -/
theorem read_ok' {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hn : n ≤ Text.length)
    (hlt : M.st.pos + M.st.q < M.m)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    Text[M.st.pos + M.st.q]? = some (Tape.read (M.ts GSTapes.tT)) := by
  have hr := h.scan.txt.read_eq
  rwa [padW_getElem?_of_lt (le_trans h.mle hn) hlt] at hr

/-! ### 走査の一歩 -/

/-- 一歩あたりの動作数の償却上界（`program_cost'` の右辺、`A' = 8k+13`, `B' = 8`）。 -/
def stepCost' (v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) (st : ScanState) : ℕ :=
  (8 * k + 13) * (Phi k (scanStep v k p₁ r Text st) - Phi k st) + 8

/-- 走査段の一歩（オラクルビット無し）。 -/
def scanOne' (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : Machine' sc) : Machine' sc :=
  { m := M.m
    ts := GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k M.ts) M.ts
    Q := M.Q
    R := ⟨M.R.qt, M.R.cost + (GSTapes.program' blank endSym mark k M.ts).length⟩
    st := scanStep v k p₁ r Text M.st }

theorem scanOne'_st (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : Machine' sc) :
    (scanOne' blank endSym mark v k p₁ r Text M).st = scanStep v k p₁ r Text M.st := rfl

theorem scanOne'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hk : 0 < k) (hmb : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length)
    (hrd : M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r n
      (scanOne' blank endSym mark v k p₁ r Text M) := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hidx : (scanStep v k p₁ r Text M.st).pos + (scanStep v k p₁ r Text M.st).q ≤ M.m :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd hrd
  have hstep : scanStep v k p₁ r (padW blank Text M.m) M.st = scanStep v k p₁ r Text M.st :=
    scanStep_padW hmT hrd
  have hfit : (scanStep v k p₁ r (padW blank Text M.m) M.st).pos +
      (scanStep v k p₁ r (padW blank Text M.m) M.st).q < (padW blank Text M.m).length := by
    rw [hstep, padW_length hmT]
    omega
  have hE := GSTapes.encodes_step' hk hmb hend h.scan h.qle hfit
  rw [hstep] at hE
  exact ⟨hE, h.buf, h.qinv, h.qlist, h.mle, hidx, scanStep_q_le h.qle⟩

/-- 一歩のコストは `stepCost'`（`= A' * ΔΦ + B'`）以下。 -/
theorem scanOne'_cost {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hk : 0 < k) (hmb : mark ≠ blank) (hend : endSym ∉ v)
    (hn : n ≤ Text.length) (hrd : M.st.q ≠ v.length → M.st.pos + M.st.q < M.m)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    (scanOne' blank endSym mark v k p₁ r Text M).R.cost
      ≤ M.R.cost + stepCost' v k p₁ r Text M.st := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hstep : scanStep v k p₁ r (padW blank Text M.m) M.st = scanStep v k p₁ r Text M.st :=
    scanStep_padW hmT hrd
  have hc := GSTapes.program_cost' hk hmb hend h.scan h.qle
  rw [hstep] at hc
  show M.R.cost + (GSTapes.program' blank endSym mark k M.ts).length ≤ _
  unfold stepCost'
  omega

/-! ### ラウンド内の実行 -/

def fillIf' (blank mark : Fin sc) (n : ℕ) (M : Machine' sc) : Machine' sc :=
  if M.st.pos + M.st.q = M.m ∧ M.m < n then fill' blank mark M else M

theorem fillIf'_st (blank mark : Fin sc) (n : ℕ) (M : Machine' sc) :
    (fillIf' blank mark n M).st = M.st := by
  unfold fillIf'; split_ifs <;> rfl

theorem fillIf'_cost (blank mark : Fin sc) (n : ℕ) (M : Machine' sc) :
    (fillIf' blank mark n M).R.cost ≤ M.R.cost + 33 := by
  unfold fillIf'
  split_ifs with hc
  · exact fill'_cost blank mark M
  · omega

theorem fillIf'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r n (fillIf' blank mark n M) := by
  unfold fillIf'
  split_ifs with hc
  · exact fill'_feedInv hmb hn hc.2 hc.1 h
  · exact h

theorem fillIf'_ready {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc}
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) (he : Enabled v n M.st) :
    (fillIf' blank mark n M).st.q ≠ v.length →
      (fillIf' blank mark n M).st.pos + (fillIf' blank mark n M).st.q
        < (fillIf' blank mark n M).m := by
  rw [fillIf'_st]
  intro hq
  have hlt : M.st.pos + M.st.q < n := by
    rcases he with h1 | h1
    · exact absurd h1 hq
    · exact h1
  unfold fillIf'
  by_cases hc : M.st.pos + M.st.q = M.m ∧ M.m < n
  · rw [if_pos hc]
    show M.st.pos + M.st.q < M.m + 1
    omega
  · rw [if_neg hc]
    have := h.hd
    have := h.mle
    by_cases he2 : M.st.pos + M.st.q = M.m
    · exact absurd ⟨he2, by omega⟩ hc
    · omega

/-- ラウンド `n` の中で高々 `j` 歩（各歩の前に必要なら供給する）。 -/
def runInT' (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) : ℕ → Machine' sc → Machine' sc
  | 0, M => M
  | j + 1, M =>
      if Enabled v n (fillIf' blank mark n M).st then
        runInT' blank endSym mark v k p₁ r n Text j
          (scanOne' blank endSym mark v k p₁ r Text (fillIf' blank mark n M))
      else fillIf' blank mark n M

theorem runInT'_st (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) :
    ∀ (j : ℕ) (M : Machine' sc),
      (runInT' blank endSym mark v k p₁ r n Text j M).st
        = runIn v k p₁ r Text n j M.st := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih =>
    intro M
    rw [runInT', runIn, fillIf'_st]
    split_ifs with he
    · rw [ih, scanOne'_st, fillIf'_st]
    · rw [fillIf'_st]

theorem runInT'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : Machine' sc), FeedInv' blank startSym endSym mark v Text k p₁ r n M →
      FeedInv' blank startSym endSym mark v Text k p₁ r n
        (runInT' blank endSym mark v k p₁ r n Text j M) := by
  intro j
  induction j with
  | zero => intro M h; exact h
  | succ j ih =>
    intro M h
    rw [runInT']
    split_ifs with he
    · rw [fillIf'_st] at he
      exact ih _ (scanOne'_feedInv hk hmb hv hend hn (fillIf'_ready h he)
        (fillIf'_feedInv hmb hn h))
    · exact fillIf'_feedInv hmb hn h

/-- ラウンド内のコスト（供給 `33` ＋ 走査の一歩 `stepCost'`）。 -/
def runInCost' (v : List (Fin sc)) (k p₁ r n : ℕ) (Text : List (Fin sc)) :
    ℕ → ScanState → ℕ
  | 0, _ => 0
  | j + 1, st =>
      33 + (if Enabled v n st then
              stepCost' v k p₁ r Text st
                + runInCost' v k p₁ r n Text j (scanStep v k p₁ r Text st)
            else 0)

theorem runInT'_cost {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : Machine' sc), FeedInv' blank startSym endSym mark v Text k p₁ r n M →
      (runInT' blank endSym mark v k p₁ r n Text j M).R.cost
        ≤ M.R.cost + runInCost' v k p₁ r n Text j M.st := by
  intro j
  induction j with
  | zero => intro M _; exact Nat.le_add_right _ _
  | succ j ih =>
    intro M h
    have hf := fillIf'_feedInv (blank := blank) (mark := mark) hmb hn h
    have hfc := fillIf'_cost blank mark n M
    rw [runInT', fillIf'_st, runInCost']
    split_ifs with he
    · have hrd := fillIf'_ready (blank := blank) (mark := mark) h he
      have h1 := ih _ (scanOne'_feedInv hk hmb hv hend hn hrd hf)
      have h2 := scanOne'_cost hk hmb hend hn hrd hf
      rw [scanOne'_st, fillIf'_st] at h1
      rw [fillIf'_st] at h2
      omega
    · omega

theorem runInCost'_le {v Text : List (Fin sc)} {k p₁ r n c : ℕ}
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c) :
    ∀ (j : ℕ) (st : ScanState), st.q ≤ v.length →
      runInCost' v k p₁ r n Text j st ≤ j * (c + 33) := by
  intro j
  induction j with
  | zero => intro st _; simp [runInCost']
  | succ j ih =>
    intro st hq
    rw [runInCost']
    have h1 := hc st hq
    have h2 := ih (scanStep v k p₁ r Text st) (scanStep_q_le hq)
    have e : (j + 1) * (c + 33) = j * (c + 33) + (c + 33) := by ring
    split_ifs with he <;> omega

/-! ### 1 ラウンド -/

def roundT' (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (a : Fin sc) (M : Machine' sc) : Machine' sc :=
  runInT' blank endSym mark v k p₁ r (n + 1) Text (gsRate k) (arrive' blank mark a M)

/-- **1 ラウンドの主定理（オラクル無し版）**。 -/
theorem round_feed' {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n c : ℕ} {a : Fin sc} {M : Machine' sc} (hmb : mark ≠ blank) (hk : 0 < k)
    (hv : 0 < v.length) (hend : endSym ∉ v) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    (roundT' blank endSym mark v k p₁ r n Text a M).st
        = runIn v k p₁ r Text (n + 1) (gsRate k) M.st ∧
      FeedInv' blank startSym endSym mark v Text k p₁ r (n + 1)
        (roundT' blank endSym mark v k p₁ r n Text a M) ∧
      (roundT' blank endSym mark v k p₁ r n Text a M).R.cost
        ≤ M.R.cost + gsRate k * (c + 33) + 26 := by
  have hA := arrive'_feedInv (blank := blank) (mark := mark) hmb hn ha h
  have hAc := arrive'_cost blank mark a M
  refine ⟨?_, ?_, ?_⟩
  · rw [roundT', runInT'_st, arrive'_st]
  · exact runInT'_feedInv hmb hk hv hend (by omega) _ _ hA
  · have h1 := runInT'_cost hmb hk hv hend (by omega : n + 1 ≤ Text.length)
      (gsRate k) (arrive' blank mark a M) hA
    have h2 := runInCost'_le (n := n + 1) hc (gsRate k) (arrive' blank mark a M).st hA.qle
    show (runInT' blank endSym mark v k p₁ r (n + 1) Text (gsRate k)
      (arrive' blank mark a M)).R.cost ≤ _
    omega

/-! ### 起動フェーズ -/

def stepRight' (blank : Fin sc) (M : Machine' sc) : Machine' sc :=
  { m := M.m
    ts := GSTapes.upd M.ts GSTapes.tT
            (Tape.step blank (M.ts GSTapes.tT) (M.ts GSTapes.tT).focus .right)
    Q := M.Q
    R := ⟨M.R.qt, M.R.cost + 1⟩
    st := ⟨M.st.pos + 1, M.st.q⟩ }

theorem stepRight'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : Machine' sc} (hm : M.st.pos + M.st.q + 1 ≤ M.m)
    (hmT : M.m ≤ Text.length) (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r n (stepRight' blank M) := by
  have hlt : M.st.pos + M.st.q + 1 < (padW blank Text M.m).length := by
    rw [padW_length hmT]; omega
  have htxt := Tape.seq_move_right h.scan.txt hlt
  have hts : (stepRight' blank M).ts
      = GSTapes.upd M.ts GSTapes.tT
          (Tape.step blank (M.ts GSTapes.tT) (M.ts GSTapes.tT).focus .right) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, h.buf, h.qinv, h.qlist, h.mle, ?_, h.qle⟩
  · rw [hts, upd_tT_ne (i := GSTapes.tP) (by decide)]; exact h.scan.pat
  · rw [hts, GSTapes.upd_self]
    show Tape.SeqView blank (Tape.step blank (M.ts GSTapes.tT) (M.ts GSTapes.tT).focus .right)
      (padW blank Text M.m) (M.st.pos + 1 + M.st.q)
    have e : M.st.pos + 1 + M.st.q = M.st.pos + M.st.q + 1 := by omega
    rw [e]; exact htxt
  · rw [hts, upd_tT_ne (i := GSTapes.tC1) (by decide)]; exact h.scan.c1
  · rw [hts, upd_tT_ne (i := GSTapes.tC2) (by decide)]; exact h.scan.c2
  · rw [hts, upd_tT_ne (i := GSTapes.tAp) (by decide)]; exact h.scan.quad.ap
  · rw [hts, upd_tT_ne (i := GSTapes.tAn) (by decide)]; exact h.scan.quad.an
  · rw [hts, upd_tT_ne (i := GSTapes.tRp) (by decide)]; exact h.scan.quad.rp
  · rw [hts, upd_tT_ne (i := GSTapes.tRn) (by decide)]; exact h.scan.quad.rn
  · show M.st.pos + 1 + M.st.q ≤ M.m
    omega

def startRound' (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) : Machine' sc :=
  stepRight' blank (fill' blank mark (arrive' blank mark a M))

theorem startRound'_st (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) :
    (startRound' blank mark a M).st = ⟨M.st.pos + 1, M.st.q⟩ := rfl

theorem startRound'_m (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) :
    (startRound' blank mark a M).m = M.m + 1 := rfl

theorem startRound'_cost (blank mark : Fin sc) (a : Fin sc) (M : Machine' sc) :
    (startRound' blank mark a M).R.cost ≤ M.R.cost + 60 := by
  have h1 := arrive'_cost blank mark a M
  have h2 := fill'_cost blank mark (arrive' blank mark a M)
  show (fill' blank mark (arrive' blank mark a M)).R.cost + 1 ≤ M.R.cost + 60
  omega

theorem startRound'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {a : Fin sc} {M : Machine' sc} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (hm : M.m = n) (hpos : M.st.pos = n) (hq : M.st.q = 0)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    FeedInv' blank startSym endSym mark v Text k p₁ r (n + 1) (startRound' blank mark a M) := by
  have h1 := arrive'_feedInv (blank := blank) (mark := mark) hmb hn ha h
  have h2 : FeedInv' blank startSym endSym mark v Text k p₁ r (n + 1)
      (fill' blank mark (arrive' blank mark a M)) := by
    refine fill'_feedInv hmb ?_ ?_ ?_ h1
    · omega
    · show M.m < n + 1
      omega
    · show M.st.pos + M.st.q = M.m
      omega
  refine stepRight'_feedInv ?_ ?_ h2
  · show M.st.pos + M.st.q + 1 ≤ M.m + 1
    omega
  · show M.m + 1 ≤ Text.length
    omega

def startT' (blank mark : Fin sc) (Text : List (Fin sc)) : ℕ → Machine' sc → Machine' sc
  | 0, M => M
  | n + 1, M => startRound' blank mark (Text.getD n blank) (startT' blank mark Text n M)

theorem startT'_spec {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r : ℕ} {M : Machine' sc} (hmb : mark ≠ blank) (hm : M.m = 0) (hst : M.st = ⟨0, 0⟩)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r 0 M) :
    ∀ n, n ≤ Text.length →
      FeedInv' blank startSym endSym mark v Text k p₁ r n (startT' blank mark Text n M) ∧
        (startT' blank mark Text n M).st = ⟨n, 0⟩ ∧
        (startT' blank mark Text n M).m = n ∧
        (startT' blank mark Text n M).R.cost ≤ M.R.cost + 60 * n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨h, hst, hm, by simp [startT']⟩
  | succ n ih =>
    intro hle
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have hc := startRound'_cost blank mark (Text.getD n blank) (startT' blank mark Text n M)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact startRound'_feedInv hmb (by omega) (getD_eq (by omega)) i3
        (by rw [i2]) (by rw [i2]) i1
    · rw [startT', startRound'_st, i2]
    · rw [startT', startRound'_m, i3]
    · show (startRound' blank mark (Text.getD n blank) (startT' blank mark Text n M)).R.cost
        ≤ M.R.cost + 60 * (n + 1)
      have e : 60 * (n + 1) = 60 * n + 60 := by ring
      omega

/-! ### 全ラウンド -/

def onlineT' (blank endSym mark : Fin sc) (v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (s : ℕ) : ℕ → Machine' sc → Machine' sc
  | 0, M => M
  | n + 1, M =>
      roundT' blank endSym mark v k p₁ r (s + n) Text (Text.getD (s + n) blank)
        (onlineT' blank endSym mark v k p₁ r Text s n M)

theorem onlineT'_st {u v Text : List (Fin sc)} {blank endSym mark : Fin sc} {k p₁ r s : ℕ}
    {M : Machine' sc} (hM : M.st = onlineRun u v k p₁ r Text s) :
    ∀ n, (onlineT' blank endSym mark v k p₁ r Text s n M).st
      = onlineRun u v k p₁ r Text (s + n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    have e : s + (n + 1) = (s + n) + 1 := by omega
    rw [onlineT', roundT', runInT'_st, arrive'_st, ih, e]
    rfl

theorem onlineT'_feedInv {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r c s : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c) :
    ∀ (n : ℕ) (M : Machine' sc), s + n ≤ Text.length →
      FeedInv' blank startSym endSym mark v Text k p₁ r s M →
      FeedInv' blank startSym endSym mark v Text k p₁ r (s + n)
          (onlineT' blank endSym mark v k p₁ r Text s n M) ∧
        (onlineT' blank endSym mark v k p₁ r Text s n M).R.cost
          ≤ M.R.cost + n * (gsRate k * (c + 33) + 26) := by
  intro n
  induction n with
  | zero => intro M _ h; exact ⟨h, by simp [onlineT']⟩
  | succ n ih =>
    intro M hle h
    obtain ⟨i1, i2⟩ := ih M (by omega) h
    obtain ⟨_, r2, r3⟩ := round_feed' (a := Text.getD (s + n) blank) hmb hk hv hend
      (by omega : s + n < Text.length) (getD_eq (by omega)) hc i1
    have e1 : s + (n + 1) = (s + n) + 1 := by omega
    refine ⟨by rw [e1]; exact r2, ?_⟩
    have e : (n + 1) * (gsRate k * (c + 33) + 26)
        = n * (gsRate k * (c + 33) + 26) + (gsRate k * (c + 33) + 26) := by ring
    show (roundT' blank endSym mark v k p₁ r (s + n) Text (Text.getD (s + n) blank)
      (onlineT' blank endSym mark v k p₁ r Text s n M)).R.cost ≤ _
    omega

/-! ### 初期状態 -/

/-- 初期テープ 8 本：`P` は添字 `1`、`T` は全部空白でヘッドはセル `0`、
`C1 = p₁`, `C2 = 0`, `Ap = 0 ∸ k p₁ = 0`, `An = k p₁`, `Rp = r`, `Rn = 0`。 -/
def initTapes' (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r : ℕ) : GSTapes.TapesState' sc := fun i =>
  if i = GSTapes.tP then ⟨[startSym], (v ++ [endSym]).headD blank, (v ++ [endSym]).tail⟩
  else if i = GSTapes.tT then ⟨[], blank, List.replicate Text.length blank⟩
  else if i = GSTapes.tC1 then ⟨List.replicate p₁ blank ++ [mark], blank, []⟩
  else if i = GSTapes.tAn then ⟨List.replicate (k * p₁) blank ++ [mark], blank, []⟩
  else if i = GSTapes.tRp then ⟨List.replicate r blank ++ [mark], blank, []⟩
  else ⟨[mark], blank, []⟩

def initM' (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc)) (k p₁ r : ℕ) :
    Machine' sc :=
  { m := 0
    ts := initTapes' blank startSym endSym mark v Text k p₁ r
    Q := (RTQueue.empty : RTQueue.Queue (Fin sc))
    R := ⟨RTQueueTapes.initQT blank mark, 0⟩
    st := ⟨0, 0⟩ }

theorem initM'_feedInv (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r : ℕ) :
    FeedInv' blank startSym endSym mark v Text k p₁ r 0
      (initM' blank startSym endSym mark v Text k p₁ r) := by
  have hp0 : padW blank Text 0 = blank :: List.replicate Text.length blank := by
    simp [padW, List.replicate_succ]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, v ++ [endSym] = x :: xs := by
    cases hv2 : v with
    | nil => exact ⟨endSym, [], by simp⟩
    | cons y ys => exact ⟨y, ys ++ [endSym], by simp⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩,
    RTQueueTapes.initQT_encodes blank mark, RTQueue.inv_empty, ?_,
    Nat.le_refl 0, Nat.le_refl 0, Nat.zero_le _⟩
  · show Tape.SeqView blank ⟨[startSym], (v ++ [endSym]).headD blank, (v ++ [endSym]).tail⟩
      (startSym :: (v ++ [endSym])) (0 + 1)
    rw [hx]
    exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
  · show Tape.SeqView blank ⟨[], blank, List.replicate Text.length blank⟩
      (padW blank Text 0) (0 + 0)
    rw [hp0]
    exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
  · show Tape.CounterView' blank mark ⟨List.replicate p₁ blank ++ [mark], blank, []⟩ p₁
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show Tape.CounterView' blank mark ⟨[mark], blank, []⟩ 0
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show Tape.CounterView' blank mark ⟨[mark], blank, []⟩ (0 - k * p₁)
    rw [Nat.zero_sub]
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show Tape.CounterView' blank mark
      ⟨List.replicate (k * p₁) blank ++ [mark], blank, []⟩ (k * p₁ - 0)
    rw [Nat.sub_zero]
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show Tape.CounterView' blank mark ⟨List.replicate r blank ++ [mark], blank, []⟩ (r - 0)
    rw [Nat.sub_zero]
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show Tape.CounterView' blank mark ⟨[mark], blank, []⟩ (0 - r)
    rw [Nat.zero_sub]
    exact ⟨rfl, rfl, Tape.blanks_nil blank⟩
  · show RTQueue.toList (RTQueue.empty : RTQueue.Queue (Fin sc)) = (Text.take 0).drop 0
    simp [RTQueue.toList_empty]

/-- **主定理（オラクル無し版）**：空のテープから出発し、`|u|` ラウンドの起動フェーズ
（1 ラウンド `≤ 60` 動作）ののち、各ラウンドで到着記号 1 つを待ち行列へ入れ
`gsRate k` 歩の走査（`program'`：オラクルビット無し、分岐はすべてテープ読み取り）を
実行する機械は、ゴースト状態が `GSRealTime.onlineRun` に一致し、供給の不変条件を保ち、
1 ラウンドあたり `gsRate k * (c + 33) + 26` 動作以内で動く。
`c` は 1 走査ステップの動作数の上界（`stepCost'`、`program_cost'` により
`A' * ΔΦ + B'`、`A' = 8k+13`, `B' = 8`）。 -/
theorem feed_online' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r c : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length) :
    (onlineT' blank endSym mark v k p₁ r Text u.length n
          (startT' blank mark Text u.length
            (initM' blank startSym endSym mark v Text k p₁ r))).st
        = onlineRun u v k p₁ r Text (u.length + n) ∧
      FeedInv' blank startSym endSym mark v Text k p₁ r (u.length + n)
          (onlineT' blank endSym mark v k p₁ r Text u.length n
            (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r))) ∧
      (onlineT' blank endSym mark v k p₁ r Text u.length n
            (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r))).R.cost
        ≤ 60 * u.length + n * (gsRate k * (c + 33) + 26) := by
  obtain ⟨s1, s2, _, s4⟩ := startT'_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (k := k) (p₁ := p₁) (r := r) hmb rfl rfl
    (initM'_feedInv blank startSym endSym mark v Text k p₁ r) u.length (by omega)
  have hst : (startT' blank mark Text u.length
      (initM' blank startSym endSym mark v Text k p₁ r)).st
      = onlineRun u v k p₁ r Text u.length := by
    rw [s2, onlineRun_start (u := u) (Text := Text) (k := k) (p₁ := p₁) (r := r) hv
      u.length (Nat.le_refl _)]
  obtain ⟨o1, o2⟩ := onlineT'_feedInv (s := u.length) hmb hk hv hend hc n _ hn s1
  refine ⟨onlineT'_st hst n, o1, ?_⟩
  have : (initM' blank startSym endSym mark v Text k p₁ r).R.cost = 0 := rfl
  omega

end NoOracle

end TextFeed
end PalPeg

