import PalPeg.TextFeed
import PalPeg.GSVerifierTapes

/-!
# 検証器つき機械への供給 (`VerifierFeed`)

`TextFeed` の `section NoOracle` は、走査段のテキストテープ `tT` が到着済み記号の
接頭辞 `Text.take m` しか持たない（残りは空白）という「供給つき」の機械を扱った。
検証器（`GSVerifierTapes` の `section NoOracle`）はテキストの **2 本目のコピー**
`Txt2` を持ち、そのヘッドは `pos - |u| + checked` にある。このコピーも到着した
記号を書き込まねばならないので、待ち行列は 2 本（`Q1` が `tT` を、`Q2` が `Txt2`
を養う）になる。

## 供給の到達可能性について（重要）

`tT` のヘッド添字 `pos + q` は 1 歩で高々 1 しか増えず（`scanStep_index_le`）、
先端セル（＝書き込み済み領域の右端）にいるときだけ供給すればよい。ところが
`Txt2` のヘッド添字 `pos - |u| + checked` は

* 比較枝では 1 歩で **2** 増えうる（`vcomp2Acts` は `vComp` を 2 回行う）、
* ずらし枝では `pos + δ - |u|` へ **飛ぶ**（`walkActs`）

ので、「ヘッドが先端にいるときに 1 回だけ書く」供給では追い付かない場合がある。
ヘッドの位置でしか書けない以上、これは `vprogram'` を 1 歩の原子操作とみなす限り
避けられない（ヘッドが飛び越えた区間に穴が空く）。本ファイルでは、この読み出し
可能性を述語 `VRead2` として **明示の仮定** に出し、その仮定のもとで
1 ラウンド定理・オンライン定理を証明する。`VRead2` を無条件に導くには、
`vprogram'` の内部（`.X .right` の各移動の直後）に供給を挟む細粒度の構成が要る。
**その構成は §16–§19 で与える**（`vscanOne''` / `vround_feed''` / `vfeed_online''`：
`VRead2` / `VFed2` の仮定は不要）。§1–§14 は粗粒度版の記録として残してある。
-/

namespace PalPeg
namespace VerifierFeed

open PegSeparation.RealTimeTM
open PalPeg.TextFeed

variable {sc : ℕ}

/-! ## 1. 機械と不変条件 -/

/-- 供給機構つきの検証器つき機械：走査段 8 本 ＋ 検証器 2 本 ＋ 待ち行列 2 本。 -/
structure VMachine' (sc : ℕ) where
  /-- `tT` に書き込み済みの記号数。 -/
  m1 : ℕ
  /-- `Txt2` に書き込み済みの記号数。 -/
  m2 : ℕ
  /-- 走査段 8 本 ＋ 検証器 2 本。 -/
  vt : GSVTapes.VTapes' sc
  /-- `tT` を養う待ち行列。 -/
  Q1 : RTQueue.Queue (Fin sc)
  /-- `Txt2` を養う待ち行列。 -/
  Q2 : RTQueue.Queue (Fin sc)
  /-- `Q1` のテープと総動作数。 -/
  R1 : RTQueueTapes.Run sc
  /-- `Q2` のテープと総動作数。 -/
  R2 : RTQueueTapes.Run sc
  /-- 検証器つき走査状態（ゴースト変数）。 -/
  z : VState

/-- 機械の総動作数。 -/
def VMachine'.cost (M : VMachine' sc) : ℕ := M.R1.cost + M.R2.cost

/-- 供給の不変条件（検証器つき）。`VEncodes'` の 3 つの成分を、走査側は
`padW blank Text m1`、`Txt2` 側は `padW blank Text m2` でほどいたもの。 -/
structure VFeedInv' (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc))
    (k p₁ r n : ℕ) (M : VMachine' sc) : Prop where
  /-- 走査段 8 本（テキストは `padW blank Text m1`）。 -/
  scan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
    M.vt.1 M.z.1
  /-- 接頭辞テープ `U`。 -/
  pat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1)
  /-- テキスト 2 本目（`padW blank Text m2`）。 -/
  txt2 : Tape.SeqView blank M.vt.2.Txt2 (padW blank Text M.m2)
    (M.z.1.pos - u.length + M.z.2)
  buf1 : RTQueueTapes.Encodes blank mark M.R1.qt M.Q1
  qinv1 : RTQueue.Inv M.Q1
  qlist1 : RTQueue.toList M.Q1 = (Text.take n).drop M.m1
  m1le : M.m1 ≤ n
  buf2 : RTQueueTapes.Encodes blank mark M.R2.qt M.Q2
  qinv2 : RTQueue.Inv M.Q2
  qlist2 : RTQueue.toList M.Q2 = (Text.take n).drop M.m2
  m2le : M.m2 ≤ n
  /-- 走査ヘッドは書き込み済み領域を出ない。 -/
  hd1 : M.z.1.pos + M.z.1.q ≤ M.m1
  /-- `Txt2` のヘッドも書き込み済み領域を出ない。 -/
  hd2 : M.z.1.pos - u.length + M.z.2 ≤ M.m2
  qle : M.z.1.q ≤ v.length
  cle : M.z.2 ≤ u.length
  posle : u.length ≤ M.z.1.pos

/-- `Txt2` の読み出し可能性（本ファイル冒頭の注意を参照）。 -/
def VRead2 (u v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) (m2 : ℕ)
    (z : VState) : Prop :=
  ((z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) →
      z.1.pos - u.length + z.2 + 1 < m2) ∧
    (vStep u v k p₁ r Text z).1.pos - u.length + (vStep u v k p₁ r Text z).2 ≤ m2

/-! ## 2. `padW` と `vComp` -/

theorem vComp_padW {blank : Fin sc} {u Text : List (Fin sc)} {m pos c : ℕ}
    (hm : m ≤ Text.length) (hlt : pos - u.length + c < m) :
    vComp u (padW blank Text m) pos c = vComp u Text pos c := by
  unfold vComp
  rw [padW_getElem?_of_lt hm hlt]

/-! ## 3. 到着 -/

/-- **到着**：到着した記号を **両方** の待ち行列へ入れる。 -/
def varrive' (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    Q1 := RTQueue.snoc M.Q1 a
    R1 := RTQueueTapes.snocT blank mark M.Q1 a M.R1
    Q2 := RTQueue.snoc M.Q2 a
    R2 := RTQueueTapes.snocT blank mark M.Q2 a M.R2 }

@[simp] theorem varrive'_z (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) :
    (varrive' blank mark a M).z = M.z := rfl

@[simp] theorem varrive'_m1 (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) :
    (varrive' blank mark a M).m1 = M.m1 := rfl

@[simp] theorem varrive'_m2 (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) :
    (varrive' blank mark a M).m2 = M.m2 := rfl

/-- 到着のコストは `≤ 52 = 2 * 26`。 -/
theorem varrive'_cost (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) :
    (varrive' blank mark a M).cost ≤ M.cost + 52 := by
  have h1 := RTQueueTapes.snocT_cost blank mark M.Q1 a M.R1
  have h2 := RTQueueTapes.snocT_cost blank mark M.Q2 a M.R2
  show (RTQueueTapes.snocT blank mark M.Q1 a M.R1).cost
      + (RTQueueTapes.snocT blank mark M.Q2 a M.R2).cost ≤ M.R1.cost + M.R2.cost + 52
  omega

private theorem qlist_snoc {Text : List (Fin sc)} {n m : ℕ} {Q : RTQueue.Queue (Fin sc)}
    {a : Fin sc} (hqinv : RTQueue.Inv Q) (hn : n < Text.length) (ha : Text[n]? = some a)
    (hm : m ≤ n) (hq : RTQueue.toList Q = (Text.take n).drop m) :
    RTQueue.toList (RTQueue.snoc Q a) = (Text.take (n + 1)).drop m := by
  have hlen : (Text.take n).length = n := by simp only [List.length_take]; omega
  have htake : Text.take (n + 1) = Text.take n ++ [a] := by
    rw [List.take_add_one, ha]; rfl
  rw [RTQueue.toList_snoc hqinv, hq, htake,
    List.drop_append_of_le_length (by rw [hlen]; exact hm)]

theorem varrive'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {a : Fin sc} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n < Text.length)
    (ha : Text[n]? = some a) (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r (n + 1)
      (varrive' blank mark a M) :=
  { scan := h.scan, pat := h.pat, txt2 := h.txt2
    buf1 := RTQueueTapes.snocT_encodes hmb h.buf1 h.qinv1
    qinv1 := RTQueue.inv_snoc h.qinv1 a
    qlist1 := qlist_snoc h.qinv1 hn ha h.m1le h.qlist1
    m1le := Nat.le_succ_of_le h.m1le
    buf2 := RTQueueTapes.snocT_encodes hmb h.buf2 h.qinv2
    qinv2 := RTQueue.inv_snoc h.qinv2 a
    qlist2 := qlist_snoc h.qinv2 hn ha h.m2le h.qlist2
    m2le := Nat.le_succ_of_le h.m2le
    hd1 := h.hd1, hd2 := h.hd2, qle := h.qle, cle := h.cle, posle := h.posle }

/-! ## 4. 供給 -/

private theorem peek_eq {blank mark : Fin sc} {Text : List (Fin sc)} {n m : ℕ}
    {Q : RTQueue.Queue (Fin sc)} {R : RTQueueTapes.Run sc}
    (hbuf : RTQueueTapes.Encodes blank mark R.qt Q) (hqinv : RTQueue.Inv Q)
    (hqlist : RTQueue.toList Q = (Text.take n).drop m) (hn : n ≤ Text.length) (hlt : m < n) :
    Text[m]? = some (peek blank R) := by
  have hmT : m < Text.length := by omega
  have hlen : (Text.take n).length = n := by simp only [List.length_take]; omega
  have hidx : m < (Text.take n).length := by rw [hlen]; exact hlt
  have hdrop : (Text.take n).drop m = (Text.take n)[m] :: (Text.take n).drop (m + 1) :=
    List.drop_eq_getElem_cons hidx
  have h3 : ((Text.take n).drop m).head? = some Text[m] := by
    rw [hdrop, List.head?_cons, List.getElem_take]
  have h1 : peek blank R = (RTQueue.head? Q).getD mark := RTQueueTapes.headT_read hbuf
  rw [h1, RTQueue.head?_eq hqinv, hqlist, h3, List.getElem?_eq_getElem hmT]
  rfl

/-- **供給 1**：`Q1` から 1 記号取り出し、`tT` の先端セルに書く。 -/
def vfill1' (blank mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    m1 := M.m1 + 1
    vt := (GSTapes.upd M.vt.1 GSTapes.tT
            (Tape.step blank (M.vt.1 GSTapes.tT) (peek blank M.R1) .stay), M.vt.2)
    Q1 := RTQueue.tail M.Q1
    R1 := RTQueueTapes.tailT blank mark M.Q1 (RTQueueTapes.headT blank M.R1) }

/-- **供給 2**：`Q2` から 1 記号取り出し、`Txt2` の先端セルに書く。 -/
def vfill2' (blank mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    m2 := M.m2 + 1
    vt := (M.vt.1,
      { M.vt.2 with Txt2 := Tape.step blank M.vt.2.Txt2 (peek blank M.R2) .stay })
    Q2 := RTQueue.tail M.Q2
    R2 := RTQueueTapes.tailT blank mark M.Q2 (RTQueueTapes.headT blank M.R2) }

@[simp] theorem vfill1'_z (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill1' blank mark M).z = M.z := rfl

@[simp] theorem vfill2'_z (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill2' blank mark M).z = M.z := rfl

@[simp] theorem vfill1'_m1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill1' blank mark M).m1 = M.m1 + 1 := rfl

@[simp] theorem vfill1'_m2 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill1' blank mark M).m2 = M.m2 := rfl

@[simp] theorem vfill2'_m1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill2' blank mark M).m1 = M.m1 := rfl

@[simp] theorem vfill2'_m2 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill2' blank mark M).m2 = M.m2 + 1 := rfl

theorem vfill1'_cost (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill1' blank mark M).cost ≤ M.cost + 33 := by
  have h1 := RTQueueTapes.tailT_cost blank mark M.Q1 (RTQueueTapes.headT blank M.R1)
  have h2 := RTQueueTapes.headT_cost blank M.R1
  show (RTQueueTapes.tailT blank mark M.Q1 (RTQueueTapes.headT blank M.R1)).cost + M.R2.cost
      ≤ M.R1.cost + M.R2.cost + 33
  omega

theorem vfill2'_cost (blank mark : Fin sc) (M : VMachine' sc) :
    (vfill2' blank mark M).cost ≤ M.cost + 33 := by
  have h1 := RTQueueTapes.tailT_cost blank mark M.Q2 (RTQueueTapes.headT blank M.R2)
  have h2 := RTQueueTapes.headT_cost blank M.R2
  show M.R1.cost + (RTQueueTapes.tailT blank mark M.Q2 (RTQueueTapes.headT blank M.R2)).cost
      ≤ M.R1.cost + M.R2.cost + 33
  omega

/-- **供給 1 は不変条件を保つ**。 -/
theorem vfill1'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (hlt : M.m1 < n) (hhd : M.z.1.pos + M.z.1.q = M.m1)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfill1' blank mark M) := by
  have hpk : Text[M.m1]? = some (peek blank M.R1) :=
    peek_eq h.buf1 h.qinv1 h.qlist1 hn hlt
  have htxt : Tape.SeqView blank
      (Tape.step blank (M.vt.1 GSTapes.tT) (peek blank M.R1) .stay)
      (padW blank Text (M.m1 + 1)) (M.z.1.pos + M.z.1.q) := by
    have h0 := Tape.seq_write h.scan.txt (peek blank M.R1)
    rw [hhd] at h0 ⊢
    rw [padW_set (by omega) hpk] at h0
    exact h0
  have hts : (vfill1' blank mark M).vt.1
      = GSTapes.upd M.vt.1 GSTapes.tT
          (Tape.step blank (M.vt.1 GSTapes.tT) (peek blank M.R1) .stay) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩, h.pat, h.txt2, ?_,
    RTQueue.inv_tail h.qinv1, ?_, (by show M.m1 + 1 ≤ n; omega),
    h.buf2, h.qinv2, h.qlist2, h.m2le,
    (by show M.z.1.pos + M.z.1.q ≤ M.m1 + 1; omega), h.hd2, h.qle, h.cle, h.posle⟩
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tP ≠ GSTapes.tT by decide)]; exact h.scan.pat
  · rw [hts, GSTapes.upd_self]; exact htxt
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tC1 ≠ GSTapes.tT by decide)]; exact h.scan.c1
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tC2 ≠ GSTapes.tT by decide)]; exact h.scan.c2
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tAp ≠ GSTapes.tT by decide)]
    exact h.scan.quad.ap
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tAn ≠ GSTapes.tT by decide)]
    exact h.scan.quad.an
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tRp ≠ GSTapes.tT by decide)]
    exact h.scan.quad.rp
  · rw [hts, GSTapes.upd_ne _ _ (show GSTapes.tRn ≠ GSTapes.tT by decide)]
    exact h.scan.quad.rn
  · exact RTQueueTapes.tailT_encodes hmb (RTQueueTapes.headT_encodes h.buf1) h.qinv1
  · show RTQueue.toList (RTQueue.tail M.Q1) = (Text.take n).drop (M.m1 + 1)
    rw [RTQueue.toList_tail h.qinv1, h.qlist1, List.tail_drop]

/-- **供給 2 は不変条件を保つ**。 -/
theorem vfill2'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (hlt : M.m2 < n) (hhd : M.z.1.pos - u.length + M.z.2 = M.m2)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfill2' blank mark M) := by
  have hpk : Text[M.m2]? = some (peek blank M.R2) :=
    peek_eq h.buf2 h.qinv2 h.qlist2 hn hlt
  have htxt : Tape.SeqView blank
      (Tape.step blank M.vt.2.Txt2 (peek blank M.R2) .stay)
      (padW blank Text (M.m2 + 1)) (M.z.1.pos - u.length + M.z.2) := by
    have h0 := Tape.seq_write h.txt2 (peek blank M.R2)
    rw [hhd] at h0 ⊢
    rw [padW_set (by omega) hpk] at h0
    exact h0
  exact ⟨h.scan, h.pat, htxt, h.buf1, h.qinv1, h.qlist1, h.m1le,
    RTQueueTapes.tailT_encodes hmb (RTQueueTapes.headT_encodes h.buf2) h.qinv2,
    RTQueue.inv_tail h.qinv2,
    (by show RTQueue.toList (RTQueue.tail M.Q2) = (Text.take n).drop (M.m2 + 1)
        rw [RTQueue.toList_tail h.qinv2, h.qlist2, List.tail_drop]),
    (by show M.m2 + 1 ≤ n; omega), h.hd1,
    (by show M.z.1.pos - u.length + M.z.2 ≤ M.m2 + 1; omega), h.qle, h.cle, h.posle⟩

/-! ## 5. 走査＋検証の一歩 -/

/-- **一歩の実現（テキスト 2 本が別々の接頭辞しか持たない版）**：
走査段は `padW blank Text m1`、`Txt2` は `padW blank Text m2` を持つ状態で
`vprogram'` を 1 歩適用すると、ゴーストは本物の `Text` 上の `vStep` に一致する。 -/
theorem vencodes_step2' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r m1 m2 : ℕ} {vt : GSVTapes.VTapes' sc} {z : VState}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text m1) k p₁ r
      vt.1 z.1)
    (hpat : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (z.2 + 1))
    (htxt2 : Tape.SeqView blank vt.2.Txt2 (padW blank Text m2) (z.1.pos - u.length + z.2))
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hm1 : m1 ≤ Text.length) (hm2 : m2 ≤ Text.length)
    (hd1 : z.1.pos + z.1.q ≤ m1) (hrd1 : z.1.q ≠ v.length → z.1.pos + z.1.q < m1)
    (hrd2 : VRead2 u v k p₁ r Text m2 z) :
    GSTapes.Encodes' blank startSym endSym mark v (padW blank Text m1) k p₁ r
        (GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt).1
        (vStep u v k p₁ r Text z).1 ∧
      Tape.SeqView blank
        (GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt).2.U
        (startSym :: (u ++ [endSym])) ((vStep u v k p₁ r Text z).2 + 1) ∧
      Tape.SeqView blank
        (GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt).2.Txt2
        (padW blank Text m2)
        ((vStep u v k p₁ r Text z).1.pos - u.length + (vStep u v k p₁ r Text z).2) := by
  have hidx : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q ≤ m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  have hstep : scanStep v k p₁ r (padW blank Text m1) z.1 = scanStep v k p₁ r Text z.1 :=
    scanStep_padW hm1 hrd1
  have hfit : (scanStep v k p₁ r (padW blank Text m1) z.1).pos
      + (scanStep v k p₁ r (padW blank Text m1) z.1).q < (padW blank Text m1).length := by
    rw [hstep, padW_length hm1]; omega
  have hscan' := GSTapes.encodes_step' hk hne hend hscan hq hfit
  rw [hstep] at hscan'
  have hsplit : GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k vt) vt
      = GSVTapes.vApplyActs' blank
          ((GSVTapes.vExtActs' blank endSym mark k vt).map GSVTapes.liftAct)
          (GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k vt.1) vt.1,
            vt.2) := by
    rw [GSVTapes.vprogram', GSVTapes.vApplyActs'_append, GSVTapes.vApplyActs'_map_S]
  rw [hsplit]
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hscan hq).1 hadv
    have haT : Text[z.1.pos + z.1.q]? = v[z.1.q]? := by
      rw [← padW_getElem?_of_lt (blank := blank) hm1 (hrd1 ha1)]; exact ha2
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv ⟨ha1, haT⟩
    have hvs : vStep u v k p₁ r Text z
        = (scanStep v k p₁ r Text z.1,
            vComp u Text z.1.pos (vComp u Text z.1.pos z.2)) := by
      unfold vStep; rw [if_neg ha1, if_pos haT]
    have hr1 : z.1.pos - u.length + z.2 + 1 < m2 := hrd2.1 ⟨ha1, haT⟩
    have hroom : z.1.pos < (padW blank Text m2).length := by
      rw [padW_length hm2]; omega
    have hext : GSVTapes.vExtActs' blank endSym mark k vt
        = GSVTapes.vcomp2Acts blank endSym vt.2 := by
      unfold GSVTapes.vExtActs'; rw [if_pos hadv]
    obtain ⟨hU2, hX2⟩ := GSVTapes.vcomp2Acts_spec (blank := blank) (startSym := startSym)
      (pos := z.1.pos) hendu hpat htxt2 hc hpos hroom
    have e1 : vComp u (padW blank Text m2) z.1.pos z.2 = vComp u Text z.1.pos z.2 :=
      vComp_padW hm2 (by omega)
    rw [e1] at hU2 hX2
    have hle2 := vComp_le_succ u Text z.1.pos z.2
    have e2 : vComp u (padW blank Text m2) z.1.pos (vComp u Text z.1.pos z.2)
        = vComp u Text z.1.pos (vComp u Text z.1.pos z.2) :=
      vComp_padW hm2 (by omega)
    rw [e2] at hU2 hX2
    rw [hvs, hext]
    refine ⟨?_, ?_, ?_⟩
    · rw [GSVTapes.vApplyActs'_map_liftAct_fst]
      exact hscan'
    · rw [GSVTapes.vApplyActs'_snd, GSVTapes.extActs'_map_liftAct]
      exact hU2
    · rw [GSVTapes.vApplyActs'_snd, GSVTapes.extActs'_map_liftAct]
      show Tape.SeqView blank
        (GSVTapes.extActs blank (GSVTapes.vcomp2Acts blank endSym vt.2) vt.2).Txt2
        (padW blank Text m2)
        ((scanStep v k p₁ r Text z.1).pos - u.length
          + vComp u Text z.1.pos (vComp u Text z.1.pos z.2))
      rw [hss]
      exact hX2
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) := by
      rintro ⟨hcon1, hcon2⟩
      refine hadv ((GSTapes.advance_iff' hend hscan hq).2 ⟨hcon1, ?_⟩)
      rw [padW_getElem?_of_lt (blank := blank) hm1 (hrd1 hcon1)]; exact hcon2
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : GSVTapes.vDelta' blank mark k vt.1 = gsShift k p₁ r z.1.q := by
      unfold GSVTapes.vDelta' gsShift
      by_cases hcd : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark
      · rw [if_pos hcd, if_pos ((GSTapes.period_iff' hne hscan).1 hcd),
          GSTapes.p1Of'_eq hscan]
      · rw [if_neg hcd, if_neg (fun hcon => hcd ((GSTapes.period_iff' hne hscan).2 hcon)),
          GSTapes.qOf'_eq hscan]
    have hcc : GSVTapes.cOf vt.2 = z.2 := GSVTapes.cOf_eq hpat
    have hroom : z.1.pos + gsShift k p₁ r z.1.q < (padW blank Text m2).length := by
      rw [hss] at hidx
      rw [padW_length hm2]
      simp only at hidx
      omega
    have hext : GSVTapes.vExtActs' blank endSym mark k vt
        = GSVTapes.walkActs (GSVTapes.cOf vt.2) (GSVTapes.vDelta' blank mark k vt.1) := by
      unfold GSVTapes.vExtActs'; rw [if_neg hadv]
    obtain ⟨hU2, hX2⟩ := GSVTapes.walkActs_spec (blank := blank) (startSym := startSym)
      (u := u) (Text := padW blank Text m2) (e := vt.2) (pos := z.1.pos) (c := z.2)
      (d := gsShift k p₁ r z.1.q) hpat htxt2 hpos hroom
    rw [GSVTapes.vStep_shift hna, hext, hd, hcc]
    refine ⟨?_, ?_, ?_⟩
    · rw [GSVTapes.vApplyActs'_map_liftAct_fst]
      exact hscan'
    · rw [GSVTapes.vApplyActs'_snd, GSVTapes.extActs'_map_liftAct]
      exact hU2
    · rw [GSVTapes.vApplyActs'_snd, GSVTapes.extActs'_map_liftAct]
      show Tape.SeqView blank
        (GSVTapes.extActs blank (GSVTapes.walkActs z.2 (gsShift k p₁ r z.1.q)) vt.2).Txt2
        (padW blank Text m2) ((scanStep v k p₁ r Text z.1).pos - u.length + 0)
      rw [hss]
      exact hX2

/-! ## 6. 機械の一歩 -/

/-- 走査＋検証の一歩（`vprogram'` を適用し、動作数を `R1` に計上する）。 -/
def vscanOne' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := GSVTapes.vApplyActs' blank (GSVTapes.vprogram' blank endSym mark k M.vt) M.vt
    R1 := ⟨M.R1.qt, M.R1.cost + (GSVTapes.vprogram' blank endSym mark k M.vt).length⟩
    z := vStep u v k p₁ r Text M.z }

@[simp] theorem vscanOne'_z (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne' blank endSym mark u v k p₁ r Text M).z = vStep u v k p₁ r Text M.z := rfl

@[simp] theorem vscanOne'_m1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne' blank endSym mark u v k p₁ r Text M).m1 = M.m1 := rfl

@[simp] theorem vscanOne'_m2 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne' blank endSym mark u v k p₁ r Text M).m2 = M.m2 := rfl

theorem vscanOne'_cost {c : ℕ} {blank endSym mark : Fin sc} {u v : List (Fin sc)}
    {k p₁ r : ℕ} {Text : List (Fin sc)} {M : VMachine' sc}
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    (vscanOne' blank endSym mark u v k p₁ r Text M).cost ≤ M.cost + c := by
  have h := hcost M.vt
  show M.R1.cost + (GSVTapes.vprogram' blank endSym mark k M.vt).length + M.R2.cost
      ≤ M.R1.cost + M.R2.cost + c
  omega

theorem vscanOne'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hn : n ≤ Text.length)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1)
    (hrd2 : VRead2 u v k p₁ r Text M.m2 M.z)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
      (vscanOne' blank endSym mark u v k p₁ r Text M) := by
  have hm1 : M.m1 ≤ Text.length := le_trans h.m1le hn
  have hm2 : M.m2 ≤ Text.length := le_trans h.m2le hn
  obtain ⟨e1, e2, e3⟩ := vencodes_step2' (m1 := M.m1) (m2 := M.m2) hk hne hv hend hendu
    h.scan h.pat h.txt2 h.qle h.cle h.posle hm1 hm2 h.hd1 hrd1 hrd2
  refine ⟨e1, e2, e3, h.buf1, h.qinv1, h.qlist1, h.m1le, h.buf2, h.qinv2, h.qlist2, h.m2le,
    ?_, hrd2.2, ?_, GSVTapes.vStep_checked_le h.cle, ?_⟩
  · show (vStep u v k p₁ r Text M.z).1.pos + (vStep u v k p₁ r Text M.z).1.q ≤ M.m1
    rw [vStep_fst]
    exact scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd1 hrd1
  · show (vStep u v k p₁ r Text M.z).1.q ≤ v.length
    rw [vStep_fst]; exact scanStep_q_le h.qle
  · show u.length ≤ (vStep u v k p₁ r Text M.z).1.pos
    rw [vStep_fst]; exact le_trans h.posle (scanStep_pos_le v k p₁ r Text M.z.1)

/-! ## 7. 各歩の前の供給 -/

def vfillIf1' (blank mark : Fin sc) (n : ℕ) (M : VMachine' sc) : VMachine' sc :=
  if M.z.1.pos + M.z.1.q = M.m1 ∧ M.m1 < n then vfill1' blank mark M else M

def vfillIf2' (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ) (M : VMachine' sc) :
    VMachine' sc :=
  if M.z.1.pos - u.length + M.z.2 = M.m2 ∧ M.m2 < n then vfill2' blank mark M else M

/-- 各歩の前に、ヘッドが先端セルにいる方のテープを（待ち行列が空でなければ）養う。 -/
def vfillBoth' (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ) (M : VMachine' sc) :
    VMachine' sc := vfillIf2' blank mark u n (vfillIf1' blank mark n M)

@[simp] theorem vfillIf1'_z (blank mark : Fin sc) (n : ℕ) (M : VMachine' sc) :
    (vfillIf1' blank mark n M).z = M.z := by unfold vfillIf1'; split_ifs <;> rfl

@[simp] theorem vfillIf2'_z (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ)
    (M : VMachine' sc) : (vfillIf2' blank mark u n M).z = M.z := by
  unfold vfillIf2'; split_ifs <;> rfl

@[simp] theorem vfillIf2'_m1 (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ)
    (M : VMachine' sc) : (vfillIf2' blank mark u n M).m1 = M.m1 := by
  unfold vfillIf2'; split_ifs <;> rfl

@[simp] theorem vfillBoth'_z (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ)
    (M : VMachine' sc) : (vfillBoth' blank mark u n M).z = M.z := by
  unfold vfillBoth'; rw [vfillIf2'_z, vfillIf1'_z]

theorem vfillIf1'_cost (blank mark : Fin sc) (n : ℕ) (M : VMachine' sc) :
    (vfillIf1' blank mark n M).cost ≤ M.cost + 33 := by
  unfold vfillIf1'
  split_ifs with hc
  · exact vfill1'_cost blank mark M
  · omega

theorem vfillIf2'_cost (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ)
    (M : VMachine' sc) : (vfillIf2' blank mark u n M).cost ≤ M.cost + 33 := by
  unfold vfillIf2'
  split_ifs with hc
  · exact vfill2'_cost blank mark M
  · omega

theorem vfillBoth'_cost (blank mark : Fin sc) (u : List (Fin sc)) (n : ℕ)
    (M : VMachine' sc) : (vfillBoth' blank mark u n M).cost ≤ M.cost + 66 := by
  have h1 := vfillIf1'_cost blank mark n M
  have h2 := vfillIf2'_cost blank mark u n (vfillIf1' blank mark n M)
  show (vfillIf2' blank mark u n (vfillIf1' blank mark n M)).cost ≤ M.cost + 66
  omega

theorem vfillIf1'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfillIf1' blank mark n M) := by
  unfold vfillIf1'
  split_ifs with hc
  · exact vfill1'_feedInv hmb hn hc.2 hc.1 h
  · exact h

theorem vfillIf2'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfillIf2' blank mark u n M) := by
  unfold vfillIf2'
  split_ifs with hc
  · exact vfill2'_feedInv hmb hn hc.2 hc.1 h
  · exact h

theorem vfillBoth'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfillBoth' blank mark u n M) :=
  vfillIf2'_feedInv hmb hn (vfillIf1'_feedInv hmb hn h)

/-- 供給のあとは、走査ヘッドの読む位置は書き込み済み（`TextFeed.fillIf'_ready` の鏡）。 -/
theorem vfillBoth'_ready1 {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) (he : Enabled v n M.z.1) :
    (vfillBoth' blank mark u n M).z.1.q ≠ v.length →
      (vfillBoth' blank mark u n M).z.1.pos + (vfillBoth' blank mark u n M).z.1.q
        < (vfillBoth' blank mark u n M).m1 := by
  rw [vfillBoth'_z]
  intro hq
  have hlt : M.z.1.pos + M.z.1.q < n := by
    rcases he with h1 | h1
    · exact absurd h1 hq
    · exact h1
  have hm : (vfillBoth' blank mark u n M).m1 = (vfillIf1' blank mark n M).m1 :=
    vfillIf2'_m1 _ _ _ _ _
  rw [hm]
  unfold vfillIf1'
  by_cases hc : M.z.1.pos + M.z.1.q = M.m1 ∧ M.m1 < n
  · rw [if_pos hc]
    show M.z.1.pos + M.z.1.q < M.m1 + 1
    omega
  · rw [if_neg hc]
    have := h.hd1
    have := h.m1le
    by_cases he2 : M.z.1.pos + M.z.1.q = M.m1
    · exact absurd ⟨he2, by omega⟩ hc
    · show M.z.1.pos + M.z.1.q < M.m1
      omega

/-! ## 8. ラウンド内の実行 -/

/-- ラウンド `n` の中で高々 `j` 歩（各歩の前に、先端にいるテープを養う）。 -/
def vrunInT' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) : ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | j + 1, M =>
      if Enabled v n (vfillBoth' blank mark u n M).z.1 then
        vrunInT' blank endSym mark u v k p₁ r n Text j
          (vscanOne' blank endSym mark u v k p₁ r Text (vfillBoth' blank mark u n M))
      else vfillBoth' blank mark u n M

/-- 実行中つねに `Txt2` の読み出しが可能であること（冒頭の注意を参照）。 -/
def VFed2 (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) : ℕ → VMachine' sc → Prop
  | 0, _ => True
  | j + 1, M =>
      Enabled v n (vfillBoth' blank mark u n M).z.1 →
        VRead2 u v k p₁ r Text (vfillBoth' blank mark u n M).m2
            (vfillBoth' blank mark u n M).z ∧
          VFed2 blank endSym mark u v k p₁ r n Text j
            (vscanOne' blank endSym mark u v k p₁ r Text (vfillBoth' blank mark u n M))

theorem vrunInT'_z (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) :
    ∀ (j : ℕ) (M : VMachine' sc),
      (vrunInT' blank endSym mark u v k p₁ r n Text j M).z
        = vRunIn u v k p₁ r Text n j M.z := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih =>
    intro M
    rw [vrunInT', vRunIn, vfillBoth'_z]
    split_ifs with he
    · rw [ih, vscanOne'_z, vfillBoth'_z]
    · rw [vfillBoth'_z]

theorem vrunInT'_cost {c : ℕ} (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r n : ℕ) (Text : List (Fin sc))
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    ∀ (j : ℕ) (M : VMachine' sc),
      (vrunInT' blank endSym mark u v k p₁ r n Text j M).cost ≤ M.cost + j * (c + 66) := by
  intro j
  induction j with
  | zero => intro M; exact Nat.le_add_right _ _
  | succ j ih =>
    intro M
    have hf := vfillBoth'_cost blank mark u n M
    have e : (j + 1) * (c + 66) = j * (c + 66) + (c + 66) := by ring
    rw [vrunInT']
    split_ifs with he
    · have h1 := ih (vscanOne' blank endSym mark u v k p₁ r Text (vfillBoth' blank mark u n M))
      have h2 := vscanOne'_cost (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text)
        (M := vfillBoth' blank mark u n M) hcost
      omega
    · omega

theorem vrunInT'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : VMachine' sc),
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n M →
      VFed2 blank endSym mark u v k p₁ r n Text j M →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (vrunInT' blank endSym mark u v k p₁ r n Text j M) := by
  intro j
  induction j with
  | zero => intro M h _; exact h
  | succ j ih =>
    intro M h hfed
    have hf := vfillBoth'_feedInv (u := u) hmb hn h
    rw [vrunInT']
    split_ifs with he
    · obtain ⟨hr2, hfed'⟩ := hfed he
      rw [vfillBoth'_z] at he
      exact ih _ (vscanOne'_feedInv hk hmb hv hend hendu hn
        (vfillBoth'_ready1 h he) hr2 hf) hfed'
    · exact hf

/-! ## 9. 1 ラウンド -/

def vroundT' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (a : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  vrunInT' blank endSym mark u v k p₁ r (n + 1) Text (gsRate k)
    (varrive' blank mark a M)

/-- **1 ラウンドの主定理（検証器つき）**：到着記号を両方の待ち行列へ入れ、
`gsRate k` 歩を（各歩の前の供給つきで）実行すると、ゴーストは `vRunIn` に一致し、
供給の不変条件が保たれ、コストは `gsRate k * (c + 66) + 52` 以内。
`c` は `vprogram'` の 1 歩の動作数の上界（`vprogram_cost'` / `vprogram'_amortized`）。 -/
theorem vround_feed' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n c : ℕ} {a : Fin sc} {M : VMachine' sc} (hmb : mark ≠ blank) (hk : 0 < k)
    (hv : 0 < v.length) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hn : n < Text.length) (ha : Text[n]? = some a)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hfed : VFed2 blank endSym mark u v k p₁ r (n + 1) Text (gsRate k)
      (varrive' blank mark a M)) :
    (vroundT' blank endSym mark u v k p₁ r n Text a M).z
        = vRunIn u v k p₁ r Text (n + 1) (gsRate k) M.z ∧
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (n + 1)
        (vroundT' blank endSym mark u v k p₁ r n Text a M) ∧
      (vroundT' blank endSym mark u v k p₁ r n Text a M).cost
        ≤ M.cost + gsRate k * (c + 66) + 52 := by
  have hA := varrive'_feedInv (u := u) hmb hn ha h
  have hAc := varrive'_cost blank mark a M
  refine ⟨?_, ?_, ?_⟩
  · rw [vroundT', vrunInT'_z, varrive'_z]
  · exact vrunInT'_feedInv hmb hk hv hend hendu (by omega) _ _ hA hfed
  · have h1 := vrunInT'_cost (c := c) blank endSym mark u v k p₁ r (n + 1) Text hcost
      (gsRate k) (varrive' blank mark a M)
    show (vrunInT' blank endSym mark u v k p₁ r (n + 1) Text (gsRate k)
      (varrive' blank mark a M)).cost ≤ _
    omega

/-! ## 10. 全ラウンド -/

def vonlineT' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (s : ℕ) : ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | n + 1, M =>
      vroundT' blank endSym mark u v k p₁ r (s + n) Text (Text.getD (s + n) blank)
        (vonlineT' blank endSym mark u v k p₁ r Text s n M)

/-- 全ラウンドを通じた `Txt2` の読み出し可能性。 -/
def VFedRounds (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (s : ℕ) : ℕ → VMachine' sc → Prop
  | 0, _ => True
  | n + 1, M =>
      VFedRounds blank endSym mark u v k p₁ r Text s n M ∧
        VFed2 blank endSym mark u v k p₁ r (s + n + 1) Text (gsRate k)
          (varrive' blank mark (Text.getD (s + n) blank)
            (vonlineT' blank endSym mark u v k p₁ r Text s n M))

theorem vonlineT'_z {u v Text : List (Fin sc)} {blank endSym mark : Fin sc} {k p₁ r s : ℕ}
    {M : VMachine' sc} (hM : M.z = vOnlineRun u v k p₁ r Text s) :
    ∀ n, (vonlineT' blank endSym mark u v k p₁ r Text s n M).z
      = vOnlineRun u v k p₁ r Text (s + n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    have e : s + (n + 1) = (s + n) + 1 := by omega
    rw [vonlineT', vroundT', vrunInT'_z, varrive'_z, ih, e]
    rfl

theorem vonlineT'_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r c s : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    ∀ (n : ℕ) (M : VMachine' sc), s + n ≤ Text.length →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r s M →
      VFedRounds blank endSym mark u v k p₁ r Text s n M →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (s + n)
          (vonlineT' blank endSym mark u v k p₁ r Text s n M) ∧
        (vonlineT' blank endSym mark u v k p₁ r Text s n M).cost
          ≤ M.cost + n * (gsRate k * (c + 66) + 52) := by
  intro n
  induction n with
  | zero => intro M _ h _; exact ⟨h, by simp [vonlineT', VMachine'.cost]⟩
  | succ n ih =>
    intro M hle h hfed
    obtain ⟨i1, i2⟩ := ih M (by omega) h hfed.1
    obtain ⟨_, r2, r3⟩ := vround_feed' (a := Text.getD (s + n) blank) hmb hk hv hend hendu
      (by omega : s + n < Text.length) (getD_eq (by omega)) hcost i1
      (by
        have := hfed.2
        rw [show s + n + 1 = (s + n) + 1 from rfl] at this
        exact this)
    have e1 : s + (n + 1) = (s + n) + 1 := by omega
    refine ⟨by rw [e1]; exact r2, ?_⟩
    have e : (n + 1) * (gsRate k * (c + 66) + 52)
        = n * (gsRate k * (c + 66) + 52) + (gsRate k * (c + 66) + 52) := by ring
    show (vroundT' blank endSym mark u v k p₁ r (s + n) Text (Text.getD (s + n) blank)
      (vonlineT' blank endSym mark u v k p₁ r Text s n M)).cost ≤ _
    omega

/-! ## 11. 起動フェーズ -/

/-- 走査段だけを見た機械（`TextFeed` の供給機構をそのまま流用するための射影）。 -/
def toM (M : VMachine' sc) : TextFeed.Machine' sc :=
  { m := M.m1, ts := M.vt.1, Q := M.Q1, R := M.R1, st := M.z.1 }

def vstepRight' (blank : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (GSTapes.upd M.vt.1 GSTapes.tT
            (Tape.step blank (M.vt.1 GSTapes.tT) (M.vt.1 GSTapes.tT).focus .right), M.vt.2)
    R1 := ⟨M.R1.qt, M.R1.cost + 1⟩
    z := (⟨M.z.1.pos + 1, M.z.1.q⟩, M.z.2) }

def vstartRound' (blank mark : Fin sc) (a : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  vstepRight' blank (vfill1' blank mark (varrive' blank mark a M))

def vstartT' (blank mark : Fin sc) (Text : List (Fin sc)) :
    ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | n + 1, M => vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M)

theorem toM_vstartT' (blank mark : Fin sc) (Text : List (Fin sc)) :
    ∀ (n : ℕ) (M : VMachine' sc),
      toM (vstartT' blank mark Text n M) = TextFeed.startT' blank mark Text n (toM M) := by
  intro n
  induction n with
  | zero => intro M; rfl
  | succ n ih =>
    intro M
    show toM (vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M))
        = TextFeed.startRound' blank mark (Text.getD n blank)
            (TextFeed.startT' blank mark Text n (toM M))
    rw [← ih]
    rfl

theorem vstartT'_ext (blank mark : Fin sc) (Text : List (Fin sc)) :
    ∀ (n : ℕ) (M : VMachine' sc),
      (vstartT' blank mark Text n M).vt.2 = M.vt.2 ∧
        (vstartT' blank mark Text n M).m2 = M.m2 ∧
        (vstartT' blank mark Text n M).z.2 = M.z.2 := by
  intro n
  induction n with
  | zero => intro M; exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    intro M
    obtain ⟨i1, i2, i3⟩ := ih M
    exact ⟨i1, i2, i3⟩

/-- 起動フェーズでも到着記号は `Q2` に貯まる。 -/
theorem vstartT'_queue2 {blank mark : Fin sc} {Text : List (Fin sc)} (hmb : mark ≠ blank) :
    ∀ (n : ℕ) (M : VMachine' sc), n ≤ Text.length →
      RTQueueTapes.Encodes blank mark M.R2.qt M.Q2 → RTQueue.Inv M.Q2 →
      RTQueue.toList M.Q2 = [] →
      RTQueueTapes.Encodes blank mark (vstartT' blank mark Text n M).R2.qt
          (vstartT' blank mark Text n M).Q2 ∧
        RTQueue.Inv (vstartT' blank mark Text n M).Q2 ∧
        RTQueue.toList (vstartT' blank mark Text n M).Q2 = Text.take n ∧
        (vstartT' blank mark Text n M).R2.cost ≤ M.R2.cost + 26 * n := by
  intro n
  induction n with
  | zero =>
    intro M _ h1 h2 h3
    refine ⟨h1, h2, ?_, ?_⟩
    · show RTQueue.toList M.Q2 = Text.take 0
      rw [h3]; simp
    · show M.R2.cost ≤ M.R2.cost + 26 * 0
      omega
  | succ n ih =>
    intro M hle h1 h2 h3
    obtain ⟨i1, i2, i3, i4⟩ := ih M (by omega) h1 h2 h3
    have ha : Text[n]? = some (Text.getD n blank) := getD_eq (by omega)
    have hq2 : (vstartRound' blank mark (Text.getD n blank)
        (vstartT' blank mark Text n M)).Q2
        = RTQueue.snoc (vstartT' blank mark Text n M).Q2 (Text.getD n blank) := rfl
    have hr2 : (vstartRound' blank mark (Text.getD n blank)
        (vstartT' blank mark Text n M)).R2
        = RTQueueTapes.snocT blank mark (vstartT' blank mark Text n M).Q2
            (Text.getD n blank) (vstartT' blank mark Text n M).R2 := rfl
    have hc := RTQueueTapes.snocT_cost blank mark (vstartT' blank mark Text n M).Q2
      (Text.getD n blank) (vstartT' blank mark Text n M).R2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show RTQueueTapes.Encodes blank mark
        (vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M)).R2.qt
        (vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M)).Q2
      rw [hq2, hr2]
      exact RTQueueTapes.snocT_encodes hmb i1 i2
    · show RTQueue.Inv
        (vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M)).Q2
      rw [hq2]
      exact RTQueue.inv_snoc i2 _
    · show RTQueue.toList
        (vstartRound' blank mark (Text.getD n blank) (vstartT' blank mark Text n M)).Q2
          = Text.take (n + 1)
      rw [hq2, RTQueue.toList_snoc i2, i3, List.take_add_one, ha]
      rfl
    · show (vstartRound' blank mark (Text.getD n blank)
        (vstartT' blank mark Text n M)).R2.cost ≤ M.R2.cost + 26 * (n + 1)
      rw [hr2]
      have e : 26 * (n + 1) = 26 * n + 26 := by ring
      omega

/-! ## 12. 初期状態 -/

def initVM' (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc)) (k p₁ r : ℕ) :
    VMachine' sc :=
  { m1 := 0
    m2 := 0
    vt := (TextFeed.initTapes' blank startSym endSym mark v Text k p₁ r,
      { U := ⟨[startSym], (u ++ [endSym]).headD blank, (u ++ [endSym]).tail⟩
        Txt2 := ⟨[], blank, List.replicate Text.length blank⟩ })
    Q1 := (RTQueue.empty : RTQueue.Queue (Fin sc))
    Q2 := (RTQueue.empty : RTQueue.Queue (Fin sc))
    R1 := ⟨RTQueueTapes.initQT blank mark, 0⟩
    R2 := ⟨RTQueueTapes.initQT blank mark, 0⟩
    z := ((⟨0, 0⟩ : ScanState), 0) }

theorem toM_initVM' (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc))
    (k p₁ r : ℕ) :
    toM (initVM' blank startSym endSym mark u v Text k p₁ r)
      = TextFeed.initM' blank startSym endSym mark v Text k p₁ r := rfl

/-! ## 13. 抽象側の起動 -/

theorem vRunIn_stuck {u v Text : List (Fin sc)} {k p₁ r n : ℕ} {z : VState}
    (he : ¬ Enabled v n z.1) : ∀ j, vRunIn u v k p₁ r Text n j z = z := by
  intro j
  cases j with
  | zero => rfl
  | succ j => rw [vRunIn, if_neg he]

theorem vOnlineRun_start {u v Text : List (Fin sc)} {k p₁ r : ℕ} (hv : 0 < v.length) :
    ∀ n, n ≤ u.length →
      vOnlineRun u v k p₁ r Text n = ((⟨u.length, 0⟩ : ScanState), 0) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hle
    show vRunIn u v k p₁ r Text (n + 1) (gsRate k) (vOnlineRun u v k p₁ r Text n) = _
    rw [ih (by omega)]
    refine vRunIn_stuck ?_ _
    rintro (h1 | h1) <;> simp only [] at h1 <;> omega

/-- 起動フェーズの仕上げ：`|u|` ラウンド後の状態は不変条件を満たし、ゴーストは
`vOnlineRun … |u|`、コストは `86 * |u|` 以内。 -/
theorem vstart_spec {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r : ℕ} (hmb : mark ≠ blank) (hv : 0 < v.length) (hlen : u.length ≤ Text.length) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r u.length
        (vstartT' blank mark Text u.length
          (initVM' blank startSym endSym mark u v Text k p₁ r)) ∧
      (vstartT' blank mark Text u.length
          (initVM' blank startSym endSym mark u v Text k p₁ r)).z
        = vOnlineRun u v k p₁ r Text u.length ∧
      (vstartT' blank mark Text u.length
          (initVM' blank startSym endSym mark u v Text k p₁ r)).cost ≤ 86 * u.length := by
  set M0 := initVM' blank startSym endSym mark u v Text k p₁ r with hM0
  set MS := vstartT' blank mark Text u.length M0 with hMS
  -- 走査段は `TextFeed` の起動フェーズそのもの
  obtain ⟨s1, s2, _, s4⟩ := TextFeed.startT'_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (k := k) (p₁ := p₁) (r := r) hmb rfl rfl
    (TextFeed.initM'_feedInv blank startSym endSym mark v Text k p₁ r) u.length hlen
  have hproj : toM MS
      = TextFeed.startT' blank mark Text u.length
          (TextFeed.initM' blank startSym endSym mark v Text k p₁ r) := by
    rw [hMS, toM_vstartT', hM0, toM_initVM']
  rw [← hproj] at s1 s2 s4
  have hR1 : (toM MS).R.cost = MS.R1.cost := rfl
  have hI0 : (TextFeed.initM' blank startSym endSym mark v Text k p₁ r).R.cost = 0 := rfl
  rw [hR1, hI0] at s4
  -- 検証器側の 2 本は起動フェーズでは動かない
  obtain ⟨x1, x2, x3⟩ := vstartT'_ext blank mark Text u.length M0
  obtain ⟨q1, q2, q3, q4⟩ := vstartT'_queue2 (Text := Text) (M := M0) hmb u.length hlen
    (RTQueueTapes.initQT_encodes blank mark) RTQueue.inv_empty
    (by show RTQueue.toList (RTQueue.empty : RTQueue.Queue (Fin sc)) = []
        simp [RTQueue.toList_empty])
  rw [← hMS] at q1 q2 q3 q4
  have hQ0 : M0.R2.cost = 0 := by rw [hM0]; rfl
  rw [hQ0] at q4
  have hz : MS.z = ((⟨u.length, 0⟩ : ScanState), 0) := by
    have h1 : MS.z.1 = (⟨u.length, 0⟩ : ScanState) := s2
    have h2 : MS.z.2 = 0 := x3
    exact Prod.ext h1 h2
  have hm2 : MS.m2 = 0 := x2
  have hvt2 : MS.vt.2 = M0.vt.2 := x1
  have hpad0 : padW blank Text 0 = blank :: List.replicate Text.length blank := by
    simp [padW, List.replicate_succ]
  obtain ⟨y, ys, hy⟩ : ∃ y ys, u ++ [endSym] = y :: ys := by
    cases hu : u with
    | nil => exact ⟨endSym, [], by simp⟩
    | cons a as => exact ⟨a, as ++ [endSym], by simp⟩
  have hstart : VFeedInv' blank startSym endSym mark u v Text k p₁ r u.length MS := by
    refine ⟨s1.scan, ?_, ?_, s1.buf, s1.qinv, s1.qlist, s1.mle, q1, q2, ?_, ?_,
      s1.hd, ?_, s1.qle, ?_, ?_⟩
    · rw [hz]
      show Tape.SeqView blank MS.vt.2.U (startSym :: (u ++ [endSym])) (0 + 1)
      rw [hvt2]
      show Tape.SeqView blank
        ⟨[startSym], (u ++ [endSym]).headD blank, (u ++ [endSym]).tail⟩
        (startSym :: (u ++ [endSym])) (0 + 1)
      rw [hy]
      exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
    · rw [hz, hm2]
      show Tape.SeqView blank MS.vt.2.Txt2 (padW blank Text 0) (u.length - u.length + 0)
      rw [hvt2, hpad0]
      show Tape.SeqView blank ⟨[], blank, List.replicate Text.length blank⟩
        (blank :: List.replicate Text.length blank) (u.length - u.length + 0)
      rw [show u.length - u.length + 0 = 0 from by omega]
      exact ⟨rfl, rfl, ⟨[], by simp, Tape.blanks_nil blank⟩⟩
    · rw [hm2, q3]; simp
    · rw [hm2]; exact Nat.zero_le _
    · rw [hz, hm2]
      show u.length - u.length + 0 ≤ 0
      omega
    · rw [hz]; exact Nat.zero_le _
    · rw [hz]
  have hcost0 : MS.cost ≤ 86 * u.length := by
    show MS.R1.cost + MS.R2.cost ≤ 86 * u.length
    have e : 86 * u.length = 60 * u.length + 26 * u.length := by ring
    omega
  have hzs : MS.z = vOnlineRun u v k p₁ r Text u.length := by
    rw [hz, vOnlineRun_start hv u.length (Nat.le_refl _)]
  exact ⟨hstart, hzs, hcost0⟩

/-! ## 14. 主定理 -/

/-- **主定理（検証器つき、オラクル無し）**：空のテープから出発し、`|u|` ラウンドの
起動フェーズ（1 ラウンド `≤ 86 = 26 + 26 + 33 + 1` 動作）ののち、各ラウンドで
到着記号 1 つを **両方の** 待ち行列へ入れ、`gsRate k` 歩の検証器つき走査
（各歩の前に先端にいるテープを養う）を実行する機械は、ゴースト状態が
`GSVerifier.vOnlineRun` に一致し、供給の不変条件を保ち、1 ラウンドあたり
`gsRate k * (c + 66) + 52` 動作以内で動く（`c` は `vprogram'` の 1 歩の動作数の
上界）。`Txt2` の読み出し可能性は仮定 `VFedRounds`（冒頭の注意を参照）。 -/
theorem vfeed_online' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r c : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length)
    (hfed : VFedRounds blank endSym mark u v k p₁ r Text u.length n
      (vstartT' blank mark Text u.length
        (initVM' blank startSym endSym mark u v Text k p₁ r))) :
    (vonlineT' blank endSym mark u v k p₁ r Text u.length n
          (vstartT' blank mark Text u.length
            (initVM' blank startSym endSym mark u v Text k p₁ r))).z
        = vOnlineRun u v k p₁ r Text (u.length + n) ∧
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (u.length + n)
          (vonlineT' blank endSym mark u v k p₁ r Text u.length n
            (vstartT' blank mark Text u.length
              (initVM' blank startSym endSym mark u v Text k p₁ r))) ∧
      (vonlineT' blank endSym mark u v k p₁ r Text u.length n
            (vstartT' blank mark Text u.length
              (initVM' blank startSym endSym mark u v Text k p₁ r))).cost
        ≤ 86 * u.length + n * (gsRate k * (c + 66) + 52) := by
  obtain ⟨hstart, hzs, hcost0⟩ := vstart_spec (u := u) (v := v) (Text := Text) (k := k)
    (p₁ := p₁) (r := r) (startSym := startSym) (endSym := endSym) hmb hv (by omega)
  obtain ⟨o1, o2⟩ := vonlineT'_feedInv (s := u.length) hmb hk hv hend hendu hcost n _
    hn hstart hfed
  refine ⟨vonlineT'_z hzs n, o1, ?_⟩
  omega

/-! ## 16. 細粒度の供給：移動の途中で `Txt2` を養う

冒頭の注意で述べた障害は、`vprogram'` を 1 歩の原子操作として扱うことから来る。
本節以降では **`.X .right` の各移動の直後に供給を挟む** 機械 `vprogram''` を組み、
`VRead2` / `VFed2` の仮定なしで実現とコストを証明する。

供給の判定はすべてテープ読み取りで行う：

* `Tape.read Txt2 = blank` ⇔ ヘッドが先端セル（`blank ∉ Text` が必要）
* `peek blank R2 = mark` ⇔ 待ち行列が空（`mark ∉ Text` が必要）
-/

/-- `Txt2` と待ち行列 `Q2` の不変条件（ヘッド添字 `i`）。 -/
structure Txt2Inv (blank mark : Fin sc) (Text : List (Fin sc)) (n : ℕ) (M : VMachine' sc)
    (i : ℕ) : Prop where
  view : Tape.SeqView blank M.vt.2.Txt2 (padW blank Text M.m2) i
  buf : RTQueueTapes.Encodes blank mark M.R2.qt M.Q2
  qinv : RTQueue.Inv M.Q2
  qlist : RTQueue.toList M.Q2 = (Text.take n).drop M.m2
  m2le : M.m2 ≤ n
  hle : i ≤ M.m2

/-- 「ヘッドの下のセルは書き込み済み、さもなくば到着待ち」。 -/
def Ok2 (n : ℕ) (M : VMachine' sc) (i : ℕ) : Prop := i < M.m2 ∨ M.m2 = n

theorem padW_getElem?_blank {blank : Fin sc} {Text : List (Fin sc)} {m i : ℕ}
    (hm : m ≤ Text.length) (h1 : m ≤ i) (h2 : i < Text.length + 1) :
    (padW blank Text m)[i]? = some blank := by
  have hlen : (Text.take m).length = m := by simp only [List.length_take]; omega
  rw [padW, List.getElem?_append_right (by rw [hlen]; exact h1), hlen]
  rw [List.getElem?_replicate]
  rw [if_pos (by omega)]

/-- 先端セルの判定はテープ読み取りでできる。 -/
theorem read_Txt2_blank_iff {blank mark : Fin sc} {Text : List (Fin sc)} {n i : ℕ}
    {M : VMachine' sc} (hb : blank ∉ Text) (hn : n ≤ Text.length)
    (h : Txt2Inv blank mark Text n M i) :
    Tape.read M.vt.2.Txt2 = blank ↔ i = M.m2 := by
  have hm2 : M.m2 ≤ Text.length := le_trans h.m2le hn
  have hr := h.view.read_eq
  have hlt : i < (padW blank Text M.m2).length := h.view.lt
  rw [padW_length hm2] at hlt
  constructor
  · intro hcon
    by_contra hne
    have hi : i < M.m2 := by have := h.hle; omega
    rw [padW_getElem?_of_lt hm2 hi] at hr
    have hi2 : i < Text.length := by omega
    rw [List.getElem?_eq_getElem hi2] at hr
    exact hb (hcon ▸ (Option.some.inj hr) ▸ List.getElem_mem hi2)
  · intro hcon
    rw [padW_getElem?_blank hm2 (by omega) (by omega)] at hr
    exact (Option.some.inj hr).symm

/-- 待ち行列が空かどうかの判定もテープ読み取りでできる。 -/
theorem peek2_mark_iff {blank mark : Fin sc} {Text : List (Fin sc)} {n i : ℕ}
    {M : VMachine' sc} (hmT : mark ∉ Text) (hn : n ≤ Text.length)
    (h : Txt2Inv blank mark Text n M i) :
    peek blank M.R2 = mark ↔ M.m2 = n := by
  have h1 : peek blank M.R2 = (RTQueue.head? M.Q2).getD mark :=
    RTQueueTapes.headT_read h.buf
  have hlen : (Text.take n).length = n := by simp only [List.length_take]; omega
  rw [h1, RTQueue.head?_eq h.qinv, h.qlist]
  constructor
  · intro hcon
    by_contra hne
    have hlt : M.m2 < n := by have := h.m2le; omega
    have hidx : M.m2 < (Text.take n).length := by rw [hlen]; exact hlt
    have hdrop : (Text.take n).drop M.m2
        = (Text.take n)[M.m2] :: (Text.take n).drop (M.m2 + 1) :=
      List.drop_eq_getElem_cons hidx
    rw [hdrop, List.head?_cons, Option.getD_some, List.getElem_take] at hcon
    exact hmT (hcon ▸ List.getElem_mem (by omega))
  · intro hcon
    have : (Text.take n).drop M.m2 = [] := by
      rw [List.drop_eq_nil_iff]; rw [hlen]; omega
    rw [this]
    rfl

/-! ### 1 セルの移動と供給 -/

/-- `Txt2` のヘッドを右へ 1（動作数 1）。 -/
def vmoveXR (blank : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (M.vt.1,
      { M.vt.2 with Txt2 := Tape.step blank M.vt.2.Txt2 M.vt.2.Txt2.focus .right })
    R1 := ⟨M.R1.qt, M.R1.cost + 1⟩ }

/-- `U` のヘッドを右へ 1（動作数 1）。 -/
def vmoveUR (blank : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (M.vt.1, { M.vt.2 with U := Tape.step blank M.vt.2.U M.vt.2.U.focus .right })
    R1 := ⟨M.R1.qt, M.R1.cost + 1⟩ }

/-- `U` のヘッドを左へ `c`（動作数 `c`）。 -/
def vmoveULN (blank : Fin sc) (c : ℕ) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (M.vt.1, { M.vt.2 with U := GSTapes.leftN blank M.vt.2.U c })
    R1 := ⟨M.R1.qt, M.R1.cost + c⟩ }

/-- `Txt2` のヘッドを左へ `c`（動作数 `c`）。 -/
def vmoveXLN (blank : Fin sc) (c : ℕ) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (M.vt.1, { M.vt.2 with Txt2 := GSTapes.leftN blank M.vt.2.Txt2 c })
    R1 := ⟨M.R1.qt, M.R1.cost + c⟩ }

/-- **細粒度の供給**：ヘッドが先端セルにいて `Q2` が空でなければ、1 記号書く。
判定は 2 つのテープ読み取りだけで行う（`headT` の probe 込みで動作数 `≤ 33`）。 -/
def vfillHead2 (blank mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  if Tape.read M.vt.2.Txt2 = blank ∧ peek blank M.R2 ≠ mark then
    { M with
      m2 := M.m2 + 1
      vt := (M.vt.1,
        { M.vt.2 with Txt2 := Tape.step blank M.vt.2.Txt2 (peek blank M.R2) .stay })
      Q2 := RTQueue.tail M.Q2
      R2 := RTQueueTapes.tailT blank mark M.Q2 (RTQueueTapes.headT blank M.R2) }
  else { M with R2 := RTQueueTapes.headT blank M.R2 }

/-- `.X .right` ＋ 供給。 -/
def vstepXR (blank mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  vfillHead2 blank mark (vmoveXR blank M)

@[simp] theorem vfillHead2_z (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).z = M.z := by unfold vfillHead2; split_ifs <;> rfl

@[simp] theorem vfillHead2_m1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).m1 = M.m1 := by unfold vfillHead2; split_ifs <;> rfl

@[simp] theorem vfillHead2_vt1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).vt.1 = M.vt.1 := by unfold vfillHead2; split_ifs <;> rfl

@[simp] theorem vfillHead2_U (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).vt.2.U = M.vt.2.U := by unfold vfillHead2; split_ifs <;> rfl

@[simp] theorem vfillHead2_Q1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).Q1 = M.Q1 := by unfold vfillHead2; split_ifs <;> rfl

@[simp] theorem vfillHead2_R1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).R1 = M.R1 := by unfold vfillHead2; split_ifs <;> rfl

theorem vfillHead2_cost (blank mark : Fin sc) (M : VMachine' sc) :
    (vfillHead2 blank mark M).cost ≤ M.cost + 33 := by
  unfold vfillHead2 VMachine'.cost
  split_ifs with hc
  · have h1 := RTQueueTapes.tailT_cost blank mark M.Q2 (RTQueueTapes.headT blank M.R2)
    have h2 := RTQueueTapes.headT_cost blank M.R2
    show M.R1.cost + (RTQueueTapes.tailT blank mark M.Q2
      (RTQueueTapes.headT blank M.R2)).cost ≤ M.R1.cost + M.R2.cost + 33
    omega
  · have h2 := RTQueueTapes.headT_cost blank M.R2
    show M.R1.cost + (RTQueueTapes.headT blank M.R2).cost ≤ M.R1.cost + M.R2.cost + 33
    omega

/-- **供給の正しさ**：不変条件を保ち、そのあとヘッドの下は書き込み済み
（さもなくば全到着記号を書き終えている）。 -/
theorem vfillHead2_inv {blank mark : Fin sc} {Text : List (Fin sc)} {n i : ℕ}
    {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length) (h : Txt2Inv blank mark Text n M i) :
    Txt2Inv blank mark Text n (vfillHead2 blank mark M) i ∧
      Ok2 n (vfillHead2 blank mark M) i := by
  have hm2 : M.m2 ≤ Text.length := le_trans h.m2le hn
  unfold vfillHead2
  split_ifs with hc
  · have hi : i = M.m2 := (read_Txt2_blank_iff hb hn h).1 hc.1
    have hne2 : M.m2 ≠ n := fun hcon => hc.2 ((peek2_mark_iff hmT hn h).2 hcon)
    have hlt : M.m2 < n := by have := h.m2le; omega
    have hpk : Text[M.m2]? = some (peek blank M.R2) :=
      peek_eq h.buf h.qinv h.qlist hn hlt
    have hview : Tape.SeqView blank
        (Tape.step blank M.vt.2.Txt2 (peek blank M.R2) .stay)
        (padW blank Text (M.m2 + 1)) i := by
      have h0 := Tape.seq_write h.view (peek blank M.R2)
      rw [hi] at h0 ⊢
      rw [padW_set (by omega) hpk] at h0
      exact h0
    refine ⟨⟨hview, ?_, RTQueue.inv_tail h.qinv, ?_,
      (by show M.m2 + 1 ≤ n; omega), (by show i ≤ M.m2 + 1; omega)⟩, ?_⟩
    · exact RTQueueTapes.tailT_encodes hmb (RTQueueTapes.headT_encodes h.buf) h.qinv
    · show RTQueue.toList (RTQueue.tail M.Q2) = (Text.take n).drop (M.m2 + 1)
      rw [RTQueue.toList_tail h.qinv, h.qlist, List.tail_drop]
    · show i < M.m2 + 1 ∨ M.m2 + 1 = n
      omega
  · refine ⟨⟨h.view, RTQueueTapes.headT_encodes h.buf, h.qinv, h.qlist, h.m2le, h.hle⟩, ?_⟩
    show i < M.m2 ∨ M.m2 = n
    rcases not_and_or.1 hc with h1 | h1
    · have : i ≠ M.m2 := fun hcon => h1 ((read_Txt2_blank_iff hb hn h).2 hcon)
      have := h.hle
      omega
    · exact Or.inr ((peek2_mark_iff hmT hn h).1 (by simpa using h1))

/-- **右への 1 歩＋供給**：ヘッド添字が 1 増え、不変条件と「読み出し可能」が保たれる。 -/
theorem vstepXR_inv {blank mark : Fin sc} {Text : List (Fin sc)} {n i : ℕ}
    {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length) (h : Txt2Inv blank mark Text n M i) (hok : Ok2 n M i)
    (hnext : i + 1 ≤ n) :
    Txt2Inv blank mark Text n (vstepXR blank mark M) (i + 1) ∧
      Ok2 n (vstepXR blank mark M) (i + 1) := by
  have hm2 : M.m2 ≤ Text.length := le_trans h.m2le hn
  have hi : i < M.m2 := by
    rcases hok with h1 | h1
    · exact h1
    · have := h.hle; omega
  have hview : Tape.SeqView blank
      (Tape.step blank M.vt.2.Txt2 M.vt.2.Txt2.focus .right) (padW blank Text M.m2) (i + 1) :=
    Tape.seq_move_right h.view (by rw [padW_length hm2]; omega)
  have h' : Txt2Inv blank mark Text n (vmoveXR blank M) (i + 1) :=
    ⟨hview, h.buf, h.qinv, h.qlist, h.m2le, (by show i + 1 ≤ M.m2; omega)⟩
  exact vfillHead2_inv hmb hb hmT hn h'

@[simp] theorem vstepXR_z (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).z = M.z := by unfold vstepXR; rw [vfillHead2_z]; rfl

@[simp] theorem vstepXR_m1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).m1 = M.m1 := by unfold vstepXR; rw [vfillHead2_m1]; rfl

@[simp] theorem vstepXR_vt1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).vt.1 = M.vt.1 := by unfold vstepXR; rw [vfillHead2_vt1]; rfl

@[simp] theorem vstepXR_U (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).vt.2.U = M.vt.2.U := by unfold vstepXR; rw [vfillHead2_U]; rfl

@[simp] theorem vstepXR_Q1 (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).Q1 = M.Q1 := by unfold vstepXR; rw [vfillHead2_Q1]; rfl

theorem vstepXR_cost (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).cost ≤ M.cost + 34 := by
  have h1 := vfillHead2_cost blank mark (vmoveXR blank M)
  have h2 : (vmoveXR blank M).cost = M.cost + 1 := by
    show M.R1.cost + 1 + M.R2.cost = M.R1.cost + M.R2.cost + 1
    omega
  show (vfillHead2 blank mark (vmoveXR blank M)).cost ≤ M.cost + 34
  omega

/-! ### 供給つきの比較 -/

/-- 1 回の `vComp`（供給つき）：`U` と `Txt2` を比べ、一致すれば両ヘッドを右へ 1
（`Txt2` の移動には供給が付く）。 -/
def vcompFed (blank endSym mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  if Tape.read M.vt.2.U ≠ endSym ∧ Tape.read M.vt.2.U = Tape.read M.vt.2.Txt2 then
    vstepXR blank mark (vmoveUR blank M)
  else M

/-- `quota = 2`：2 回目は 1 回目の供給後のテープの上で判定する
（ここが `vcomp2Acts` との違い）。 -/
def vcomp2Fed (blank endSym mark : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  vcompFed blank endSym mark (vcompFed blank endSym mark M)

@[simp] theorem vcompFed_z (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).z = M.z := by
  unfold vcompFed; split_ifs with h
  · rw [vstepXR_z]; rfl
  · rfl

@[simp] theorem vcompFed_m1 (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).m1 = M.m1 := by
  unfold vcompFed; split_ifs with h
  · rw [vstepXR_m1]; rfl
  · rfl

@[simp] theorem vcompFed_vt1 (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).vt.1 = M.vt.1 := by
  unfold vcompFed; split_ifs with h
  · rw [vstepXR_vt1]; rfl
  · rfl

@[simp] theorem vcompFed_Q1 (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).Q1 = M.Q1 := by
  unfold vcompFed; split_ifs with h
  · rw [vstepXR_Q1]; rfl
  · rfl

theorem vcompFed_cost (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).cost ≤ M.cost + 35 := by
  unfold vcompFed
  split_ifs with h
  · have h1 := vstepXR_cost blank mark (vmoveUR blank M)
    have h2 : (vmoveUR blank M).cost = M.cost + 1 := by
      show M.R1.cost + 1 + M.R2.cost = M.R1.cost + M.R2.cost + 1
      omega
    omega
  · omega

theorem vcomp2Fed_cost (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcomp2Fed blank endSym mark M).cost ≤ M.cost + 70 := by
  have h1 := vcompFed_cost blank endSym mark M
  have h2 := vcompFed_cost blank endSym mark (vcompFed blank endSym mark M)
  show (vcompFed blank endSym mark (vcompFed blank endSym mark M)).cost ≤ M.cost + 70
  omega

/-- **供給つき 1 比較の実現**。 -/
theorem vcompFed_spec {blank startSym endSym mark : Fin sc} {u Text : List (Fin sc)}
    {n pos c : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hendu : endSym ∉ u) (hn : n ≤ Text.length)
    (hU : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Txt2Inv blank mark Text n M (pos - u.length + c))
    (hok : Ok2 n M (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hroom : pos < n) :
    Tape.SeqView blank (vcompFed blank endSym mark M).vt.2.U
        (startSym :: (u ++ [endSym])) (vComp u Text pos c + 1) ∧
      Txt2Inv blank mark Text n (vcompFed blank endSym mark M)
        (pos - u.length + vComp u Text pos c) ∧
      Ok2 n (vcompFed blank endSym mark M) (pos - u.length + vComp u Text pos c) := by
  have hm2 : M.m2 ≤ Text.length := le_trans hX.m2le hn
  have hile : pos - u.length + c ≤ pos := by omega
  have hilt : pos - u.length + c < M.m2 := by
    rcases hok with h1 | h1
    · exact h1
    · have := hX.hle; omega
  have hiff : (Tape.read M.vt.2.U ≠ endSym ∧ Tape.read M.vt.2.U = Tape.read M.vt.2.Txt2)
      ↔ (c < u.length ∧ Text[pos - u.length + c]? = u[c]?) := by
    rw [GSVTapes.vcomp_iff (Text := padW blank Text M.m2) hendu hU hX.view hc,
      padW_getElem?_of_lt hm2 hilt]
  unfold vcompFed
  split_ifs with hbr
  · obtain ⟨hcl, hceq⟩ := hiff.1 hbr
    have hv : vComp u Text pos c = c + 1 := by unfold vComp; rw [if_pos ⟨hcl, hceq⟩]
    have hU' : Tape.SeqView blank (vmoveUR blank M).vt.2.U
        (startSym :: (u ++ [endSym])) (c + 1 + 1) := by
      refine Tape.seq_move_right hU ?_
      simp only [List.length_cons, List.length_append]
      omega
    have hX' : Txt2Inv blank mark Text n (vmoveUR blank M) (pos - u.length + c) :=
      ⟨hX.view, hX.buf, hX.qinv, hX.qlist, hX.m2le, hX.hle⟩
    have hok' : Ok2 n (vmoveUR blank M) (pos - u.length + c) := hok
    obtain ⟨i1, i2⟩ := vstepXR_inv hmb hb hmT hn hX' hok' (by omega)
    rw [hv]
    refine ⟨?_, ?_, ?_⟩
    · show Tape.SeqView blank (vstepXR blank mark (vmoveUR blank M)).vt.2.U
        (startSym :: (u ++ [endSym])) (c + 1 + 1)
      rw [vstepXR_U]
      exact hU'
    · have e : pos - u.length + (c + 1) = pos - u.length + c + 1 := by omega
      rw [e]; exact i1
    · have e : pos - u.length + (c + 1) = pos - u.length + c + 1 := by omega
      rw [e]; exact i2
  · have hv : vComp u Text pos c = c := by
      unfold vComp
      rw [if_neg (fun hcon => hbr (hiff.2 hcon))]
    rw [hv]
    exact ⟨hU, hX, hok⟩

/-- **供給つき 2 比較の実現**。 -/
theorem vcomp2Fed_spec {blank startSym endSym mark : Fin sc} {u Text : List (Fin sc)}
    {n pos c : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hendu : endSym ∉ u) (hn : n ≤ Text.length)
    (hU : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Txt2Inv blank mark Text n M (pos - u.length + c))
    (hok : Ok2 n M (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hroom : pos < n) :
    Tape.SeqView blank (vcomp2Fed blank endSym mark M).vt.2.U
        (startSym :: (u ++ [endSym])) (vComp u Text pos (vComp u Text pos c) + 1) ∧
      Txt2Inv blank mark Text n (vcomp2Fed blank endSym mark M)
        (pos - u.length + vComp u Text pos (vComp u Text pos c)) ∧
      Ok2 n (vcomp2Fed blank endSym mark M)
        (pos - u.length + vComp u Text pos (vComp u Text pos c)) := by
  obtain ⟨h1U, h1X, h1ok⟩ := vcompFed_spec hmb hb hmT hendu hn hU hX hok hc hpos hroom
  exact vcompFed_spec hmb hb hmT hendu hn h1U h1X h1ok (vComp_le_length hc) hpos hroom

/-! ### 供給つきの歩き直し -/

/-- `.X .right` ＋ 供給を `j` 回。 -/
def vwalkXRFed (blank mark : Fin sc) : ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | j + 1, M => vwalkXRFed blank mark j (vstepXR blank mark M)

@[simp] theorem vwalkXRFed_z (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).z = M.z := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_z]

@[simp] theorem vwalkXRFed_m1 (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).m1 = M.m1 := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_m1]

@[simp] theorem vwalkXRFed_vt1 (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).vt.1 = M.vt.1 := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_vt1]

@[simp] theorem vwalkXRFed_U (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).vt.2.U = M.vt.2.U := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_U]

@[simp] theorem vwalkXRFed_Q1 (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).Q1 = M.Q1 := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_Q1]

theorem vwalkXRFed_cost (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc),
      (vwalkXRFed blank mark j M).cost ≤ M.cost + 34 * j := by
  intro j
  induction j with
  | zero => intro M; show M.cost ≤ M.cost + 34 * 0; omega
  | succ j ih =>
    intro M
    have h1 := ih (vstepXR blank mark M)
    have h2 := vstepXR_cost blank mark M
    have e : 34 * (j + 1) = 34 * j + 34 := by ring
    show (vwalkXRFed blank mark j (vstepXR blank mark M)).cost ≤ M.cost + 34 * (j + 1)
    omega

theorem vwalkXRFed_inv {blank mark : Fin sc} {Text : List (Fin sc)} {n : ℕ}
    (hmb : mark ≠ blank) (hb : blank ∉ Text) (hmT : mark ∉ Text) (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : VMachine' sc) (i : ℕ), Txt2Inv blank mark Text n M i → Ok2 n M i →
      i + j ≤ n →
      Txt2Inv blank mark Text n (vwalkXRFed blank mark j M) (i + j) ∧
        Ok2 n (vwalkXRFed blank mark j M) (i + j) := by
  intro j
  induction j with
  | zero => intro M i h hok _; simpa using ⟨h, hok⟩
  | succ j ih =>
    intro M i h hok hle
    obtain ⟨h1, h2⟩ := vstepXR_inv hmb hb hmT hn h hok (by omega)
    have h3 := ih (vstepXR blank mark M) (i + 1) h1 h2 (by omega)
    rw [show i + (j + 1) = i + 1 + j from by omega]
    exact h3

/-- 歩き直し（供給つき）：`U` を `c` 歩左、`Txt2` を右なら供給しながら。 -/
def vwalkFed (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) : VMachine' sc :=
  if c ≤ d then vwalkXRFed blank mark (d - c) (vmoveULN blank c M)
  else vmoveXLN blank (c - d) (vmoveULN blank c M)

@[simp] theorem vwalkFed_z (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).z = M.z := by
  unfold vwalkFed; split_ifs with h
  · rw [vwalkXRFed_z]; rfl
  · rfl

@[simp] theorem vwalkFed_m1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).m1 = M.m1 := by
  unfold vwalkFed; split_ifs with h
  · rw [vwalkXRFed_m1]; rfl
  · rfl

@[simp] theorem vwalkFed_vt1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).vt.1 = M.vt.1 := by
  unfold vwalkFed; split_ifs with h
  · rw [vwalkXRFed_vt1]; rfl
  · rfl

@[simp] theorem vwalkFed_Q1 (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).Q1 = M.Q1 := by
  unfold vwalkFed; split_ifs with h
  · rw [vwalkXRFed_Q1]; rfl
  · rfl

theorem vwalkFed_cost (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).cost ≤ M.cost + 34 * GSVTapes.walkLen c d := by
  have hU : (vmoveULN blank c M).cost = M.cost + c := by
    show M.R1.cost + c + M.R2.cost = M.R1.cost + M.R2.cost + c
    omega
  unfold vwalkFed GSVTapes.walkLen
  split_ifs with h
  · have h1 := vwalkXRFed_cost blank mark (d - c) (vmoveULN blank c M)
    have e : 34 * (c + (d - c)) = 34 * c + 34 * (d - c) := by ring
    omega
  · have h2 : (vmoveXLN blank (c - d) (vmoveULN blank c M)).cost
        = (vmoveULN blank c M).cost + (c - d) := by
      show (vmoveULN blank c M).R1.cost + (c - d) + (vmoveULN blank c M).R2.cost
        = (vmoveULN blank c M).R1.cost + (vmoveULN blank c M).R2.cost + (c - d)
      omega
    have e : 34 * (c + (c - d)) = 34 * c + 34 * (c - d) := by ring
    omega

/-- **供給つき歩き直しの実現**。 -/
theorem vwalkFed_spec {blank startSym endSym mark : Fin sc} {u Text : List (Fin sc)}
    {n pos c d : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hn : n ≤ Text.length)
    (hU : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Txt2Inv blank mark Text n M (pos - u.length + c))
    (hok : Ok2 n M (pos - u.length + c))
    (hpos : u.length ≤ pos) (hroom : pos + d ≤ n) :
    Tape.SeqView blank (vwalkFed blank mark c d M).vt.2.U
        (startSym :: (u ++ [endSym])) (0 + 1) ∧
      Txt2Inv blank mark Text n (vwalkFed blank mark c d M) (pos + d - u.length + 0) ∧
      Ok2 n (vwalkFed blank mark c d M) (pos + d - u.length + 0) := by
  have hUL : Tape.SeqView blank (vmoveULN blank c M).vt.2.U
      (startSym :: (u ++ [endSym])) (0 + 1) := by
    show Tape.SeqView blank (GSTapes.leftN blank M.vt.2.U c)
      (startSym :: (u ++ [endSym])) (0 + 1)
    refine GSTapes.seq_leftN c M.vt.2.U (0 + 1) ?_
    rw [show 0 + 1 + c = c + 1 from by omega]
    exact hU
  have hXL : Txt2Inv blank mark Text n (vmoveULN blank c M) (pos - u.length + c) :=
    ⟨hX.view, hX.buf, hX.qinv, hX.qlist, hX.m2le, hX.hle⟩
  have hokL : Ok2 n (vmoveULN blank c M) (pos - u.length + c) := hok
  unfold vwalkFed
  split_ifs with hcd
  · obtain ⟨i1, i2⟩ := vwalkXRFed_inv hmb hb hmT hn (d - c) (vmoveULN blank c M)
      (pos - u.length + c) hXL hokL (by omega)
    rw [show pos - u.length + c + (d - c) = pos + d - u.length + 0 from by omega] at i1 i2
    exact ⟨by rw [vwalkXRFed_U]; exact hUL, i1, i2⟩
  · refine ⟨hUL, ⟨?_, hX.buf, hX.qinv, hX.qlist, hX.m2le, ?_⟩, ?_⟩
    · show Tape.SeqView blank (GSTapes.leftN blank (vmoveULN blank c M).vt.2.Txt2 (c - d))
        (padW blank Text M.m2) (pos + d - u.length + 0)
      refine GSTapes.seq_leftN (c - d) M.vt.2.Txt2 (pos + d - u.length + 0) ?_
      rw [show pos + d - u.length + 0 + (c - d) = pos - u.length + c from by omega]
      exact hX.view
    · show pos + d - u.length + 0 ≤ M.m2
      have := hX.hle
      omega
    · show pos + d - u.length + 0 < M.m2 ∨ M.m2 = n
      rcases hok with h1 | h1
      · left; omega
      · right; exact h1

/-! ## 17. 細粒度供給つきの一歩 `vprogram''` -/

/-- 走査段 8 本への `program'` の適用（検証器 2 本には触らない）。 -/
def vscanApply (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) : VMachine' sc :=
  { M with
    vt := (GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k M.vt.1) M.vt.1,
      M.vt.2)
    R1 := ⟨M.R1.qt, M.R1.cost + (GSTapes.program' blank endSym mark k M.vt.1).length⟩ }

/-- 検証器 2 本への作用（`vExtActs'` の供給つき版）。分岐は `vExtActs'` と同じく
**この一歩の開始時の** 走査テープの読み取りで決まる。 -/
def vExtFed (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) : VMachine' sc :=
  if Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT) then
    vcomp2Fed blank endSym mark M
  else vwalkFed blank mark (GSVTapes.cOf M.vt.2) (GSVTapes.vDelta' blank mark k M.vt.1) M

/-- **`vprogram''` の 1 歩**：`vprogram'` と同じ動作列を、`.X .right` のたびに
供給を挟みながら実行する（2 回目の比較は 1 回目の供給後のテープで判定される）。 -/
def vscanOne'' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) : VMachine' sc :=
  { vscanApply blank endSym mark k (vExtFed blank endSym mark k M) with
    z := vStep u v k p₁ r Text M.z }

@[simp] theorem vExtFed_z (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFed blank endSym mark k M).z = M.z := by
  unfold vExtFed; split_ifs
  · rw [vcomp2Fed, vcompFed_z, vcompFed_z]
  · rw [vwalkFed_z]

@[simp] theorem vExtFed_m1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFed blank endSym mark k M).m1 = M.m1 := by
  unfold vExtFed; split_ifs
  · rw [vcomp2Fed, vcompFed_m1, vcompFed_m1]
  · rw [vwalkFed_m1]

@[simp] theorem vExtFed_vt1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFed blank endSym mark k M).vt.1 = M.vt.1 := by
  unfold vExtFed; split_ifs
  · rw [vcomp2Fed, vcompFed_vt1, vcompFed_vt1]
  · rw [vwalkFed_vt1]

@[simp] theorem vExtFed_Q1 (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFed blank endSym mark k M).Q1 = M.Q1 := by
  unfold vExtFed; split_ifs
  · rw [vcomp2Fed, vcompFed_Q1, vcompFed_Q1]
  · rw [vwalkFed_Q1]

@[simp] theorem vscanOne''_z (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).z = vStep u v k p₁ r Text M.z := rfl

@[simp] theorem vscanOne''_m1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).m1 = M.m1 := by
  show (vExtFed blank endSym mark k M).m1 = M.m1
  rw [vExtFed_m1]

@[simp] theorem vscanOne''_m2 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).m2
      = (vExtFed blank endSym mark k M).m2 := rfl

@[simp] theorem vscanOne''_Q1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).Q1 = M.Q1 := by
  show (vExtFed blank endSym mark k M).Q1 = M.Q1
  rw [vExtFed_Q1]

theorem vscanOne''_vt1 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).vt.1
      = GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k M.vt.1) M.vt.1 := by
  show GSTapes.applyActs' blank
      (GSTapes.program' blank endSym mark k (vExtFed blank endSym mark k M).vt.1)
      (vExtFed blank endSym mark k M).vt.1 = _
  rw [vExtFed_vt1]

theorem vscanOne''_vt2 (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).vt.2
      = (vExtFed blank endSym mark k M).vt.2 := rfl

/-- **検証器 2 本への作用の実現（細粒度供給つき）**。 -/
theorem vExtFed_spec {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
      M.vt.1 M.z.1)
    (hpat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1))
    (hX : Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2))
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (hq : M.z.1.q ≤ v.length) (hc : M.z.2 ≤ u.length) (hpos : u.length ≤ M.z.1.pos)
    (hn : n ≤ Text.length) (hm1n : M.m1 ≤ n)
    (hd1 : M.z.1.pos + M.z.1.q ≤ M.m1)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1) :
    Tape.SeqView blank (vExtFed blank endSym mark k M).vt.2.U
        (startSym :: (u ++ [endSym])) ((vStep u v k p₁ r Text M.z).2 + 1) ∧
      Txt2Inv blank mark Text n (vExtFed blank endSym mark k M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) ∧
      Ok2 n (vExtFed blank endSym mark k M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) := by
  have hm1 : M.m1 ≤ Text.length := le_trans hm1n hn
  have hidx : (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q ≤ M.m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  unfold vExtFed
  by_cases hadv : Tape.read (M.vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (M.vt.1 GSTapes.tP) = Tape.read (M.vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hscan hq).1 hadv
    have haT : Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]? := by
      rw [← padW_getElem?_of_lt (blank := blank) hm1 (hrd1 ha1)]; exact ha2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos, M.z.1.q + 1⟩ : ScanState) := GSTapes.scanStep_adv ⟨ha1, haT⟩
    have hvs : vStep u v k p₁ r Text M.z
        = (scanStep v k p₁ r Text M.z.1,
            vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2)) := by
      unfold vStep; rw [if_neg ha1, if_pos haT]
    have hroom : M.z.1.pos < n := by
      have := hrd1 ha1; omega
    obtain ⟨c1, c2, c3⟩ := vcomp2Fed_spec (startSym := startSym) (pos := M.z.1.pos)
      hne hb hmT hendu hn hpat hX hok hc hpos hroom
    rw [hvs]
    refine ⟨c1, ?_, ?_⟩
    · show Txt2Inv blank mark Text n (vcomp2Fed blank endSym mark M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length
          + vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2))
      rw [hss]; exact c2
    · show Ok2 n (vcomp2Fed blank endSym mark M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length
          + vComp u Text M.z.1.pos (vComp u Text M.z.1.pos M.z.2))
      rw [hss]; exact c3
  · rw [if_neg hadv]
    have hna : ¬ (M.z.1.q ≠ v.length ∧ Text[M.z.1.pos + M.z.1.q]? = v[M.z.1.q]?) := by
      rintro ⟨hcon1, hcon2⟩
      refine hadv ((GSTapes.advance_iff' hend hscan hq).2 ⟨hcon1, ?_⟩)
      rw [padW_getElem?_of_lt (blank := blank) hm1 (hrd1 hcon1)]; exact hcon2
    have hss : scanStep v k p₁ r Text M.z.1
        = (⟨M.z.1.pos + gsShift k p₁ r M.z.1.q, gsNextQ k p₁ r M.z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : GSVTapes.vDelta' blank mark k M.vt.1 = gsShift k p₁ r M.z.1.q := by
      unfold GSVTapes.vDelta' gsShift
      by_cases hcd : Tape.read (Tape.step blank (M.vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (M.vt.1 GSTapes.tRn) blank .left) = mark
      · rw [if_pos hcd, if_pos ((GSTapes.period_iff' hne hscan).1 hcd),
          GSTapes.p1Of'_eq hscan]
      · rw [if_neg hcd, if_neg (fun hcon => hcd ((GSTapes.period_iff' hne hscan).2 hcon)),
          GSTapes.qOf'_eq hscan]
    have hcc : GSVTapes.cOf M.vt.2 = M.z.2 := GSVTapes.cOf_eq hpat
    have hroom : M.z.1.pos + gsShift k p₁ r M.z.1.q ≤ n := by
      rw [hss] at hidx
      simp only at hidx
      omega
    obtain ⟨w1, w2, w3⟩ := vwalkFed_spec (startSym := startSym) (u := u)
      (pos := M.z.1.pos) (c := M.z.2) (d := gsShift k p₁ r M.z.1.q)
      hne hb hmT hn hpat hX hok hpos hroom
    rw [hd, hcc, GSVTapes.vStep_shift hna]
    refine ⟨w1, ?_, ?_⟩
    · show Txt2Inv blank mark Text n
        (vwalkFed blank mark M.z.2 (gsShift k p₁ r M.z.1.q) M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + 0)
      rw [hss]; exact w2
    · show Ok2 n (vwalkFed blank mark M.z.2 (gsShift k p₁ r M.z.1.q) M)
        ((scanStep v k p₁ r Text M.z.1).pos - u.length + 0)
      rw [hss]; exact w3

/-- **実現（細粒度供給つき、`VRead2` の仮定なし）**。 -/
theorem vencodes_step'' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hscan : GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
      M.vt.1 M.z.1)
    (hpat : Tape.SeqView blank M.vt.2.U (startSym :: (u ++ [endSym])) (M.z.2 + 1))
    (hX : Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2))
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2))
    (hq : M.z.1.q ≤ v.length) (hc : M.z.2 ≤ u.length) (hpos : u.length ≤ M.z.1.pos)
    (hn : n ≤ Text.length) (hm1n : M.m1 ≤ n)
    (hd1 : M.z.1.pos + M.z.1.q ≤ M.m1)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1) :
    GSTapes.Encodes' blank startSym endSym mark v (padW blank Text M.m1) k p₁ r
        (vscanOne'' blank endSym mark u v k p₁ r Text M).vt.1
        (vStep u v k p₁ r Text M.z).1 ∧
      Tape.SeqView blank (vscanOne'' blank endSym mark u v k p₁ r Text M).vt.2.U
        (startSym :: (u ++ [endSym])) ((vStep u v k p₁ r Text M.z).2 + 1) ∧
      Txt2Inv blank mark Text n (vscanOne'' blank endSym mark u v k p₁ r Text M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) ∧
      Ok2 n (vscanOne'' blank endSym mark u v k p₁ r Text M)
        ((vStep u v k p₁ r Text M.z).1.pos - u.length + (vStep u v k p₁ r Text M.z).2) := by
  have hm1 : M.m1 ≤ Text.length := le_trans hm1n hn
  have hstep : scanStep v k p₁ r (padW blank Text M.m1) M.z.1
      = scanStep v k p₁ r Text M.z.1 := scanStep_padW hm1 hrd1
  have hidx : (scanStep v k p₁ r Text M.z.1).pos + (scanStep v k p₁ r Text M.z.1).q ≤ M.m1 :=
    scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv hd1 hrd1
  have hfit : (scanStep v k p₁ r (padW blank Text M.m1) M.z.1).pos
      + (scanStep v k p₁ r (padW blank Text M.m1) M.z.1).q
      < (padW blank Text M.m1).length := by
    rw [hstep, padW_length hm1]; omega
  have hscan' := GSTapes.encodes_step' hk hne hend hscan hq hfit
  rw [hstep] at hscan'
  obtain ⟨e1, e2, e3⟩ := vExtFed_spec (startSym := startSym) (p₁ := p₁) (r := r)
    hk hne hv hend hendu hb hmT hscan hpat hX hok hq hc hpos hn hm1n hd1 hrd1
  refine ⟨?_, e1, ⟨e2.view, e2.buf, e2.qinv, e2.qlist, e2.m2le, e2.hle⟩, e3⟩
  rw [vscanOne''_vt1, vStep_fst]
  exact hscan'

/-- 一歩のコスト：`34 * (vprogram' …).length + 70`。 -/
theorem vscanOne''_cost (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).cost
      ≤ M.cost + 34 * (GSVTapes.vprogram' blank endSym mark k M.vt).length + 70 := by
  have hlen := GSVTapes.vprogram_length' blank endSym mark k M.vt
  have hsa : ∀ N : VMachine' sc, (vscanApply blank endSym mark k N).cost
      = N.cost + (GSTapes.program' blank endSym mark k N.vt.1).length := by
    intro N
    show N.R1.cost + (GSTapes.program' blank endSym mark k N.vt.1).length + N.R2.cost
      = N.R1.cost + N.R2.cost + (GSTapes.program' blank endSym mark k N.vt.1).length
    omega
  have hz : (vscanOne'' blank endSym mark u v k p₁ r Text M).cost
      = (vscanApply blank endSym mark k (vExtFed blank endSym mark k M)).cost := rfl
  rw [hz, hsa, vExtFed_vt1, hlen]
  unfold GSVTapes.vExtActs' vExtFed
  split_ifs with hadv
  · have h1 := vcomp2Fed_cost blank endSym mark M
    have h2 : 0 ≤ 34 * (GSVTapes.vcomp2Acts blank endSym M.vt.2).length := Nat.zero_le _
    have e : 34 * ((GSTapes.program' blank endSym mark k M.vt.1).length
        + (GSVTapes.vcomp2Acts blank endSym M.vt.2).length)
        = 34 * (GSTapes.program' blank endSym mark k M.vt.1).length
          + 34 * (GSVTapes.vcomp2Acts blank endSym M.vt.2).length := by ring
    have e2 : (GSTapes.program' blank endSym mark k M.vt.1).length
        ≤ 34 * (GSTapes.program' blank endSym mark k M.vt.1).length := by omega
    omega
  · have h1 := vwalkFed_cost blank mark (GSVTapes.cOf M.vt.2)
      (GSVTapes.vDelta' blank mark k M.vt.1) M
    have hwl : (GSVTapes.walkActs (sc := sc) (GSVTapes.cOf M.vt.2)
        (GSVTapes.vDelta' blank mark k M.vt.1)).length
        = GSVTapes.walkLen (GSVTapes.cOf M.vt.2)
            (GSVTapes.vDelta' blank mark k M.vt.1) := GSVTapes.walkActs_length _ _
    rw [hwl]
    have e : 34 * ((GSTapes.program' blank endSym mark k M.vt.1).length
        + GSVTapes.walkLen (GSVTapes.cOf M.vt.2) (GSVTapes.vDelta' blank mark k M.vt.1))
        = 34 * (GSTapes.program' blank endSym mark k M.vt.1).length
          + 34 * GSVTapes.walkLen (GSVTapes.cOf M.vt.2)
              (GSVTapes.vDelta' blank mark k M.vt.1) := by ring
    have e2 : (GSTapes.program' blank endSym mark k M.vt.1).length
        ≤ 34 * (GSTapes.program' blank endSym mark k M.vt.1).length := by omega
    omega

/-! ### 待ち行列テープの同一性（`R1.qt` は検証器側の動作で変わらない） -/

@[simp] theorem vmoveXR_R1qt (blank : Fin sc) (M : VMachine' sc) :
    (vmoveXR blank M).R1.qt = M.R1.qt := rfl

@[simp] theorem vmoveUR_R1qt (blank : Fin sc) (M : VMachine' sc) :
    (vmoveUR blank M).R1.qt = M.R1.qt := rfl

@[simp] theorem vmoveULN_R1qt (blank : Fin sc) (c : ℕ) (M : VMachine' sc) :
    (vmoveULN blank c M).R1.qt = M.R1.qt := rfl

@[simp] theorem vmoveXLN_R1qt (blank : Fin sc) (c : ℕ) (M : VMachine' sc) :
    (vmoveXLN blank c M).R1.qt = M.R1.qt := rfl

@[simp] theorem vstepXR_R1qt (blank mark : Fin sc) (M : VMachine' sc) :
    (vstepXR blank mark M).R1.qt = M.R1.qt := by
  unfold vstepXR; rw [vfillHead2_R1]; rfl

@[simp] theorem vcompFed_R1qt (blank endSym mark : Fin sc) (M : VMachine' sc) :
    (vcompFed blank endSym mark M).R1.qt = M.R1.qt := by
  unfold vcompFed; split_ifs
  · rw [vstepXR_R1qt]; rfl
  · rfl

@[simp] theorem vwalkXRFed_R1qt (blank mark : Fin sc) :
    ∀ (j : ℕ) (M : VMachine' sc), (vwalkXRFed blank mark j M).R1.qt = M.R1.qt := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih => intro M; rw [vwalkXRFed, ih, vstepXR_R1qt]

@[simp] theorem vwalkFed_R1qt (blank mark : Fin sc) (c d : ℕ) (M : VMachine' sc) :
    (vwalkFed blank mark c d M).R1.qt = M.R1.qt := by
  unfold vwalkFed; split_ifs
  · rw [vwalkXRFed_R1qt]; rfl
  · rfl

@[simp] theorem vExtFed_R1qt (blank endSym mark : Fin sc) (k : ℕ) (M : VMachine' sc) :
    (vExtFed blank endSym mark k M).R1.qt = M.R1.qt := by
  unfold vExtFed; split_ifs
  · rw [vcomp2Fed, vcompFed_R1qt, vcompFed_R1qt]
  · rw [vwalkFed_R1qt]

@[simp] theorem vscanOne''_R1qt (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r : ℕ) (Text : List (Fin sc)) (M : VMachine' sc) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).R1.qt = M.R1.qt := by
  show (vExtFed blank endSym mark k M).R1.qt = M.R1.qt
  rw [vExtFed_R1qt]

/-! ## 18. ラウンド（細粒度供給つき、無条件） -/

/-- 不変条件から `Txt2` 側だけを取り出す。 -/
theorem VFeedInv'.txt2Inv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    Txt2Inv blank mark Text n M (M.z.1.pos - u.length + M.z.2) :=
  ⟨h.txt2, h.buf2, h.qinv2, h.qlist2, h.m2le, h.hd2⟩

/-- ラウンド頭の供給（到着直後に 1 回だけ）：`Ok2` を回復する。 -/
theorem vfillHead2_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hmb : mark ≠ blank) (hb : blank ∉ Text)
    (hmT : mark ∉ Text) (hn : n ≤ Text.length)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n (vfillHead2 blank mark M) ∧
      Ok2 n (vfillHead2 blank mark M)
        ((vfillHead2 blank mark M).z.1.pos - u.length + (vfillHead2 blank mark M).z.2) := by
  obtain ⟨i1, i2⟩ := vfillHead2_inv hmb hb hmT hn h.txt2Inv
  have hz := vfillHead2_z blank mark M
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, i1.buf, i1.qinv, i1.qlist, i1.m2le,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hz, vfillHead2_vt1, vfillHead2_m1]; exact h.scan
  · rw [hz, vfillHead2_U]; exact h.pat
  · rw [hz]; exact i1.view
  · rw [vfillHead2_R1, vfillHead2_Q1]; exact h.buf1
  · rw [vfillHead2_Q1]; exact h.qinv1
  · rw [vfillHead2_Q1, vfillHead2_m1]; exact h.qlist1
  · rw [vfillHead2_m1]; exact h.m1le
  · rw [hz, vfillHead2_m1]; exact h.hd1
  · rw [hz]; exact i1.hle
  · rw [hz]; exact h.qle
  · rw [hz]; exact h.cle
  · rw [hz]; exact h.posle
  · show Ok2 n (vfillHead2 blank mark M)
      ((vfillHead2 blank mark M).z.1.pos - u.length + (vfillHead2 blank mark M).z.2)
    rw [hz]; exact i2

/-- 一歩（細粒度供給つき）の不変条件。 -/
theorem vscanOne''_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc} (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length)
    (hrd1 : M.z.1.q ≠ v.length → M.z.1.pos + M.z.1.q < M.m1)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M)
    (hok : Ok2 n M (M.z.1.pos - u.length + M.z.2)) :
    VFeedInv' blank startSym endSym mark u v Text k p₁ r n
        (vscanOne'' blank endSym mark u v k p₁ r Text M) ∧
      Ok2 n (vscanOne'' blank endSym mark u v k p₁ r Text M)
        ((vscanOne'' blank endSym mark u v k p₁ r Text M).z.1.pos - u.length
          + (vscanOne'' blank endSym mark u v k p₁ r Text M).z.2) := by
  obtain ⟨e1, e2, e3, e4⟩ := vencodes_step'' hk hne hv hend hendu hb hmT h.scan h.pat
    h.txt2Inv hok h.qle h.cle h.posle hn h.m1le h.hd1 hrd1
  refine ⟨⟨?_, e2, ?_, ?_, ?_, ?_, ?_, e3.buf, e3.qinv, e3.qlist, e3.m2le,
    ?_, ?_, ?_, ?_, ?_⟩, e4⟩
  · rw [vscanOne''_m1]; exact e1
  · exact e3.view
  · rw [vscanOne''_R1qt, vscanOne''_Q1]; exact h.buf1
  · rw [vscanOne''_Q1]; exact h.qinv1
  · rw [vscanOne''_Q1, vscanOne''_m1]; exact h.qlist1
  · rw [vscanOne''_m1]; exact h.m1le
  · show (vStep u v k p₁ r Text M.z).1.pos + (vStep u v k p₁ r Text M.z).1.q
      ≤ (vscanOne'' blank endSym mark u v k p₁ r Text M).m1
    rw [vscanOne''_m1, vStep_fst]
    exact scanStep_index_le (p₁ := p₁) (r := r) (T := Text) hk hv h.hd1 hrd1
  · exact e3.hle
  · show (vStep u v k p₁ r Text M.z).1.q ≤ v.length
    rw [vStep_fst]; exact scanStep_q_le h.qle
  · exact GSVTapes.vStep_checked_le h.cle
  · show u.length ≤ (vStep u v k p₁ r Text M.z).1.pos
    rw [vStep_fst]; exact le_trans h.posle (scanStep_pos_le v k p₁ r Text M.z.1)

theorem vscanOne''_cost' {c : ℕ} {blank endSym mark : Fin sc} {u v : List (Fin sc)}
    {k p₁ r : ℕ} {Text : List (Fin sc)} {M : VMachine' sc}
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    (vscanOne'' blank endSym mark u v k p₁ r Text M).cost ≤ M.cost + (34 * c + 70) := by
  have h1 := vscanOne''_cost blank endSym mark u v k p₁ r Text M
  have h2 := hcost M.vt
  have h3 : 34 * (GSVTapes.vprogram' blank endSym mark k M.vt).length ≤ 34 * c :=
    Nat.mul_le_mul_left 34 h2
  omega

/-- 供給のあと走査ヘッドの読む位置は書き込み済み（`tT` 側）。 -/
theorem vfillIf1'_ready {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} {M : VMachine' sc}
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) (he : Enabled v n M.z.1) :
    (vfillIf1' blank mark n M).z.1.q ≠ v.length →
      (vfillIf1' blank mark n M).z.1.pos + (vfillIf1' blank mark n M).z.1.q
        < (vfillIf1' blank mark n M).m1 := by
  rw [vfillIf1'_z]
  intro hq
  have hlt : M.z.1.pos + M.z.1.q < n := by
    rcases he with h1 | h1
    · exact absurd h1 hq
    · exact h1
  unfold vfillIf1'
  by_cases hc : M.z.1.pos + M.z.1.q = M.m1 ∧ M.m1 < n
  · rw [if_pos hc]
    show M.z.1.pos + M.z.1.q < M.m1 + 1
    omega
  · rw [if_neg hc]
    have := h.hd1
    have := h.m1le
    by_cases he2 : M.z.1.pos + M.z.1.q = M.m1
    · exact absurd ⟨he2, by omega⟩ hc
    · show M.z.1.pos + M.z.1.q < M.m1
      omega

/-- ラウンド `n` の中で高々 `j` 歩（各歩の前に `tT` を養う）。 -/
def vrunInT'' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) : ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | j + 1, M =>
      if Enabled v n (vfillIf1' blank mark n M).z.1 then
        vrunInT'' blank endSym mark u v k p₁ r n Text j
          (vscanOne'' blank endSym mark u v k p₁ r Text (vfillIf1' blank mark n M))
      else vfillIf1' blank mark n M

theorem vrunInT''_z (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) :
    ∀ (j : ℕ) (M : VMachine' sc),
      (vrunInT'' blank endSym mark u v k p₁ r n Text j M).z
        = vRunIn u v k p₁ r Text n j M.z := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih =>
    intro M
    rw [vrunInT'', vRunIn, vfillIf1'_z]
    split_ifs with he
    · rw [ih, vscanOne''_z, vfillIf1'_z]
    · rw [vfillIf1'_z]

theorem vrunInT''_cost {c : ℕ} (blank endSym mark : Fin sc) (u v : List (Fin sc))
    (k p₁ r n : ℕ) (Text : List (Fin sc))
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    ∀ (j : ℕ) (M : VMachine' sc),
      (vrunInT'' blank endSym mark u v k p₁ r n Text j M).cost
        ≤ M.cost + j * (34 * c + 103) := by
  intro j
  induction j with
  | zero => intro M; exact Nat.le_add_right _ _
  | succ j ih =>
    intro M
    have hf := vfillIf1'_cost blank mark n M
    have e : (j + 1) * (34 * c + 103) = j * (34 * c + 103) + (34 * c + 103) := by ring
    rw [vrunInT'']
    split_ifs with he
    · have h1 := ih (vscanOne'' blank endSym mark u v k p₁ r Text
        (vfillIf1' blank mark n M))
      have h2 := vscanOne''_cost' (u := u) (v := v) (p₁ := p₁) (r := r) (Text := Text)
        (M := vfillIf1' blank mark n M) hcost
      omega
    · omega

theorem vrunInT''_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n ≤ Text.length) :
    ∀ (j : ℕ) (M : VMachine' sc),
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n M →
      Ok2 n M (M.z.1.pos - u.length + M.z.2) →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r n
          (vrunInT'' blank endSym mark u v k p₁ r n Text j M) ∧
        Ok2 n (vrunInT'' blank endSym mark u v k p₁ r n Text j M)
          ((vrunInT'' blank endSym mark u v k p₁ r n Text j M).z.1.pos - u.length
            + (vrunInT'' blank endSym mark u v k p₁ r n Text j M).z.2) := by
  intro j
  induction j with
  | zero => intro M h hok; exact ⟨h, hok⟩
  | succ j ih =>
    intro M h hok
    have hf := vfillIf1'_feedInv (u := u) hmb hn h
    have hokf : Ok2 n (vfillIf1' blank mark n M)
        ((vfillIf1' blank mark n M).z.1.pos - u.length + (vfillIf1' blank mark n M).z.2) := by
      unfold vfillIf1'
      split_ifs with hc
      · exact hok
      · exact hok
    rw [vrunInT'']
    split_ifs with he
    · rw [vfillIf1'_z] at he
      obtain ⟨s1, s2⟩ := vscanOne''_feedInv hk hmb hv hend hendu hb hmT hn
        (vfillIf1'_ready h he) hf hokf
      exact ih _ s1 s2
    · exact ⟨hf, hokf⟩

/-- 1 ラウンド：到着（両待ち行列）→ `Txt2` の頭出し供給 → `gsRate k` 歩。 -/
def vroundT'' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r n : ℕ)
    (Text : List (Fin sc)) (a : Fin sc) (M : VMachine' sc) : VMachine' sc :=
  vrunInT'' blank endSym mark u v k p₁ r (n + 1) Text (gsRate k)
    (vfillHead2 blank mark (varrive' blank mark a M))

/-- **1 ラウンドの主定理（細粒度供給つき、無条件）**。 -/
theorem vround_feed'' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r n c : ℕ} {a : Fin sc} {M : VMachine' sc} (hmb : mark ≠ blank) (hk : 0 < k)
    (hv : 0 < v.length) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hn : n < Text.length) (ha : Text[n]? = some a)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c)
    (h : VFeedInv' blank startSym endSym mark u v Text k p₁ r n M) :
    (vroundT'' blank endSym mark u v k p₁ r n Text a M).z
        = vRunIn u v k p₁ r Text (n + 1) (gsRate k) M.z ∧
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (n + 1)
        (vroundT'' blank endSym mark u v k p₁ r n Text a M) ∧
      (vroundT'' blank endSym mark u v k p₁ r n Text a M).cost
        ≤ M.cost + gsRate k * (34 * c + 103) + 85 := by
  have hA := varrive'_feedInv (u := u) hmb hn ha h
  have hAc := varrive'_cost blank mark a M
  obtain ⟨hF, hok⟩ := vfillHead2_feedInv (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
    hmb hb hmT (by omega : n + 1 ≤ Text.length) hA
  have hFc := vfillHead2_cost blank mark (varrive' blank mark a M)
  refine ⟨?_, ?_, ?_⟩
  · rw [vroundT'', vrunInT''_z, vfillHead2_z, varrive'_z]
  · exact (vrunInT''_feedInv hmb hk hv hend hendu hb hmT (by omega) _ _ hF hok).1
  · have h1 := vrunInT''_cost (c := c) blank endSym mark u v k p₁ r (n + 1) Text hcost
      (gsRate k) (vfillHead2 blank mark (varrive' blank mark a M))
    show (vrunInT'' blank endSym mark u v k p₁ r (n + 1) Text (gsRate k)
      (vfillHead2 blank mark (varrive' blank mark a M))).cost ≤ _
    omega

/-! ## 19. 全ラウンドと主定理（無条件） -/

def vonlineT'' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) (s : ℕ) : ℕ → VMachine' sc → VMachine' sc
  | 0, M => M
  | n + 1, M =>
      vroundT'' blank endSym mark u v k p₁ r (s + n) Text (Text.getD (s + n) blank)
        (vonlineT'' blank endSym mark u v k p₁ r Text s n M)

theorem vonlineT''_z {u v Text : List (Fin sc)} {blank endSym mark : Fin sc} {k p₁ r s : ℕ}
    {M : VMachine' sc} (hM : M.z = vOnlineRun u v k p₁ r Text s) :
    ∀ n, (vonlineT'' blank endSym mark u v k p₁ r Text s n M).z
      = vOnlineRun u v k p₁ r Text (s + n) := by
  intro n
  induction n with
  | zero => exact hM
  | succ n ih =>
    have e : s + (n + 1) = (s + n) + 1 := by omega
    rw [vonlineT'', vroundT'', vrunInT''_z, vfillHead2_z, varrive'_z, ih, e]
    rfl

theorem vonlineT''_feedInv {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r c s : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c) :
    ∀ (n : ℕ) (M : VMachine' sc), s + n ≤ Text.length →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r s M →
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (s + n)
          (vonlineT'' blank endSym mark u v k p₁ r Text s n M) ∧
        (vonlineT'' blank endSym mark u v k p₁ r Text s n M).cost
          ≤ M.cost + n * (gsRate k * (34 * c + 103) + 85) := by
  intro n
  induction n with
  | zero => intro M _ h; exact ⟨h, by simp [vonlineT'']⟩
  | succ n ih =>
    intro M hle h
    obtain ⟨i1, i2⟩ := ih M (by omega) h
    obtain ⟨_, r2, r3⟩ := vround_feed'' (a := Text.getD (s + n) blank) hmb hk hv hend hendu
      hb hmT (by omega : s + n < Text.length) (getD_eq (by omega)) hcost i1
    have e1 : s + (n + 1) = (s + n) + 1 := by omega
    refine ⟨by rw [e1]; exact r2, ?_⟩
    have e : (n + 1) * (gsRate k * (34 * c + 103) + 85)
        = n * (gsRate k * (34 * c + 103) + 85) + (gsRate k * (34 * c + 103) + 85) := by ring
    show (vroundT'' blank endSym mark u v k p₁ r (s + n) Text (Text.getD (s + n) blank)
      (vonlineT'' blank endSym mark u v k p₁ r Text s n M)).cost ≤ _
    omega

/-- **主定理（細粒度供給つき、無条件）**：空のテープから出発し、`|u|` ラウンドの起動
フェーズののち、各ラウンドで到着記号 1 つを両方の待ち行列へ入れ、`Txt2` の頭出し供給を
1 回行い、`gsRate k` 歩の検証器つき走査（各歩の前に `tT` を養い、`.X .right` の
たびに `Txt2` を養う）を実行する機械は、ゴースト状態が `vOnlineRun` に一致し、
供給の不変条件を保ち、1 ラウンドあたり `gsRate k * (34 * c + 103) + 85` 動作以内で
動く。読み出し可能性の仮定は不要。 -/
theorem vfeed_online'' {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)}
    {k p₁ r c : ℕ} (hmb : mark ≠ blank) (hk : 0 < k) (hv : 0 < v.length)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hb : blank ∉ Text) (hmT : mark ∉ Text)
    (hcost : ∀ vt : GSVTapes.VTapes' sc,
      (GSVTapes.vprogram' blank endSym mark k vt).length ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length) :
    (vonlineT'' blank endSym mark u v k p₁ r Text u.length n
          (vstartT' blank mark Text u.length
            (initVM' blank startSym endSym mark u v Text k p₁ r))).z
        = vOnlineRun u v k p₁ r Text (u.length + n) ∧
      VFeedInv' blank startSym endSym mark u v Text k p₁ r (u.length + n)
          (vonlineT'' blank endSym mark u v k p₁ r Text u.length n
            (vstartT' blank mark Text u.length
              (initVM' blank startSym endSym mark u v Text k p₁ r))) ∧
      (vonlineT'' blank endSym mark u v k p₁ r Text u.length n
            (vstartT' blank mark Text u.length
              (initVM' blank startSym endSym mark u v Text k p₁ r))).cost
        ≤ 86 * u.length + n * (gsRate k * (34 * c + 103) + 85) := by
  obtain ⟨hstart, hzs, hcost0⟩ := vstart_spec (u := u) (v := v) (k := k) (p₁ := p₁) (r := r)
    (startSym := startSym) (endSym := endSym) hmb hv
    (by omega : u.length ≤ Text.length)
  obtain ⟨o1, o2⟩ := vonlineT''_feedInv (s := u.length) hmb hk hv hend hendu hb hmT hcost n
    _ hn hstart
  refine ⟨vonlineT''_z hzs n, o1, ?_⟩
  omega

/-! ## 15. コスト定数の小例 -/

section Examples

example : (52 : ℕ) = 26 + 26 := rfl        -- `varrive'`（両待ち行列への `snoc`）
example : (33 : ℕ) = 2 + 31 := rfl         -- 1 本ぶんの `fill`（`head?` + `tail`）
example : (66 : ℕ) = 33 + 33 := rfl        -- 1 歩あたりの供給（両テープ）
example : (86 : ℕ) = 26 + 26 + 33 + 1 := rfl -- 起動フェーズ 1 ラウンド
example : gsRate 8 = 9 := by decide
example : (34 : ℕ) = 1 + 33 := rfl        -- `.X .right` ＋ 途中供給
example : (35 : ℕ) = 1 + 34 := rfl        -- 供給つき 1 比較
example : (70 : ℕ) = 35 + 35 := rfl       -- 供給つき 2 比較
example : (103 : ℕ) = 33 + 70 := rfl      -- 1 歩（`tT` の供給 ＋ 定数項）
example : (85 : ℕ) = 52 + 33 := rfl       -- ラウンド頭（到着 ＋ `Txt2` の頭出し供給）

end Examples

end VerifierFeed
end PalPeg
