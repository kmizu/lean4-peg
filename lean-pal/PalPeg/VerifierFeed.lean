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
`vprogram'` の内部（`.X .right` の各移動の直前）に供給を挟む細粒度の構成が要る。
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
  set M0 := initVM' blank startSym endSym mark u v Text k p₁ r with hM0
  set MS := vstartT' blank mark Text u.length M0 with hMS
  -- 走査段は `TextFeed` の起動フェーズそのもの
  obtain ⟨s1, s2, _, s4⟩ := TextFeed.startT'_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (k := k) (p₁ := p₁) (r := r) hmb rfl rfl
    (TextFeed.initM'_feedInv blank startSym endSym mark v Text k p₁ r) u.length (by omega)
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
  obtain ⟨q1, q2, q3, q4⟩ := vstartT'_queue2 (Text := Text) (M := M0) hmb u.length (by omega)
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
  obtain ⟨o1, o2⟩ := vonlineT'_feedInv (s := u.length) hmb hk hv hend hendu hcost n MS
    hn hstart hfed
  refine ⟨vonlineT'_z hzs n, o1, ?_⟩
  omega

/-! ## 15. コスト定数の小例 -/

section Examples

example : (52 : ℕ) = 26 + 26 := rfl        -- `varrive'`（両待ち行列への `snoc`）
example : (33 : ℕ) = 2 + 31 := rfl         -- 1 本ぶんの `fill`（`head?` + `tail`）
example : (66 : ℕ) = 33 + 33 := rfl        -- 1 歩あたりの供給（両テープ）
example : (86 : ℕ) = 26 + 26 + 33 + 1 := rfl -- 起動フェーズ 1 ラウンド
example : gsRate 8 = 9 := by decide

end Examples

end VerifierFeed
end PalPeg
