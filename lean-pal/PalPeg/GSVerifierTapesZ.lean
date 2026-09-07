import PalPeg.GSVerifierFused
import PalPeg.GSVerifierZ

/-!
# ジグザグ検証器のテープ実現 (`GSVerifierTapesZ`)

`PalPeg.GSVerifierZ` のジグザグ検証器（巻き戻しの無い `u` 検証）を、
`PalPeg.GSVTapes` の 10 本テープ機械の上に実現する。

`GSVTapes.vprogramX` との違いは 2 点だけである。

* **比較枝**：`vcomp2Acts`（`vComp` を 2 回）を、**ジグザグ単位動作 `zQuota = 4` 個**
  `zUnits` に置き換える。1 単位は高々 2 動作。
* **ずらし枝**：`uxWalk`（`U` の巻き戻し `2·checked + 4` 動作）を**完全に削除**する。
  `U` はずらしのとき動かないので、融合ループ（`perProgramX` / `resProgramX`）が
  `Txt2` を `gsShift` だけ右へ運べば整列はそのまま保たれる。

その結果、一歩の費用は **点ごとに** `(9k+14)·ΔΦ + 16` で抑えられ、
`PalPeg.PointwiseGap.rewind_not_pointwise` が示す `2·checked` の壁を回避する。

## 整列（向きによらない）

* `U` は `startSym :: (u ++ [endSym])`、ヘッドは添字 `head + 1`、
* `Txt2` はテキストの 2 本目、ヘッドは添字 `pos - |u| + head`。

上りの掃引だけで `[0, |u|)` を覆うので下りでは照合しない（`GSVerifierZ.zMove`）。
したがって整列は向きによらず同じで、`VEncodesZ'` は `GSVTapes.VEncodes'` の
`checked` を `head` に置き換えただけのものになる。

向きの 1 ビットはテープに置かず、プログラムの引数（有限制御）として持つ。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg
namespace GSVTapesZ

open PegSeparation.RealTimeTM
open PalPeg.GSVTapes
open PalPeg.GSVerifierZ

variable {sc : ℕ}

/-! ## 1. ジグザグ単位動作 -/

/-- `U` を 1 つ左へ動かして読む記号。`head = 0` の判定に使う。
（有限制御は `U .left` を実行してから現在の記号を見るので、これは*プログラムで
表現できる*判定である。`U` の添字は `head + 1 ≥ 1` なので左端規則には触れない。） -/
def zPeekL (blank : Fin sc) (e : VExt sc) : Fin sc :=
  Tape.read (Tape.step blank e.U e.U.focus .left)

/-- **1 単位動作の動作列**（高々 2 動作）。

* `up`：`GSVTapes.vcompActs endSym`（`endSym` を読んでいなければ照合して両ヘッド右）。
* `down`：まず `U` を 1 つ左へ動かす。そこが `startSym`（＝`head = 0`）なら
  `U` を戻して向きだけ反転、そうでなければ `Txt2` も 1 つ左へ動かす。 -/
def zUnitActs (blank startSym endSym : Fin sc) (up : Bool) (e : VExt sc) : List (VAct sc) :=
  if up then vcompActs endSym e
  else VAct.U .left :: (if zPeekL blank e = startSym then [VAct.U .right] else [VAct.X .left])

/-- 1 単位動作のあとの向き。`up` は `up` のまま、`down` は `startSym` を読んだら `up` へ。 -/
def zNextDir (blank startSym : Fin sc) (up : Bool) (e : VExt sc) : Bool :=
  up || decide (zPeekL blank e = startSym)

/-- `n` 単位動作の動作列。 -/
def zUnits (blank startSym endSym : Fin sc) : ℕ → Bool → VExt sc → List (VAct sc)
  | 0, _, _ => []
  | n + 1, up, e =>
      zUnitActs blank startSym endSym up e ++
        zUnits blank startSym endSym n (zNextDir blank startSym up e)
          (extActs blank (zUnitActs blank startSym endSym up e) e)

/-- `n` 単位動作のあとの向き。 -/
def zDirN (blank startSym endSym : Fin sc) : ℕ → Bool → VExt sc → Bool
  | 0, up, _ => up
  | n + 1, up, e =>
      zDirN blank startSym endSym n (zNextDir blank startSym up e)
        (extActs blank (zUnitActs blank startSym endSym up e) e)

theorem zUnitActs_length_le (blank startSym endSym : Fin sc) (up : Bool) (e : VExt sc) :
    (zUnitActs blank startSym endSym up e).length ≤ 2 := by
  unfold zUnitActs
  split_ifs with h1 h2
  · exact vcompActs_length_le endSym e
  · simp
  · simp

theorem zUnits_length_le (blank startSym endSym : Fin sc) :
    ∀ (n : ℕ) (up : Bool) (e : VExt sc),
      (zUnits blank startSym endSym n up e).length ≤ 2 * n := by
  intro n
  induction n with
  | zero => intro up e; simp [zUnits]
  | succ n ih =>
    intro up e
    show ((zUnitActs blank startSym endSym up e) ++ _).length ≤ 2 * (n + 1)
    rw [List.length_append]
    have h1 := zUnitActs_length_le blank startSym endSym up e
    have h2 := ih (zNextDir blank startSym up e)
      (extActs blank (zUnitActs blank startSym endSym up e) e)
    omega

/-! ## 2. 符号化 -/

/-- 10 本のテープがジグザグ検証器つき状態 `z = (st, ZS)` を符号化していること。
`GSVTapes.VEncodes'` の `checked` を `head` に置き換えたもの（向きには依存しない）。 -/
structure VEncodesZ' (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc))
    (k p₁ r : ℕ) (vt : VTapes' sc) (z : VStateZ) : Prop where
  scan : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1
  pat : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (z.2.head + 1)
  txt2 : Tape.SeqView blank vt.2.Txt2 Text (z.1.pos - u.length + z.2.head)

/-! ## 3. 単位動作の実現 -/

section Unit

variable {blank startSym endSym : Fin sc} {u Text : List (Fin sc)}

/-- `U` の 1 つ左を覗くと、`startSym :: (u ++ [endSym])` の添字 `head` が読める。 -/
theorem zPeekL_eq {e : VExt sc} {c : ℕ}
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1)) :
    (startSym :: (u ++ [endSym]))[c]? = some (zPeekL blank e) :=
  (Tape.seq_move_left hU).read_eq

/-- 覗きが `startSym` であることは `head = 0` と同値（`startSym ∉ u`, `startSym ≠ endSym`）。 -/
theorem zPeekL_startSym_iff {e : VExt sc} {c : ℕ} (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym) (hc : c ≤ u.length)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1)) :
    zPeekL blank e = startSym ↔ c = 0 := by
  have h := zPeekL_eq (u := u) hU
  constructor
  · intro hs
    rw [hs] at h
    by_contra hne
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [List.getElem?_cons_succ] at h
    rcases Nat.lt_or_ge c' u.length with hlt | hge
    · rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt] at h
      exact hstartu (Option.some_inj.1 h ▸ List.getElem_mem hlt)
    · have hcc : c' = u.length := by omega
      rw [hcc, List.getElem?_append_right (by omega)] at h
      simp only [Nat.sub_self] at h
      exact hse (by simpa using h.symm)
  · intro hc0
    subst hc0
    simpa using h.symm

/-- **1 単位動作の実現**：`GSVerifierZ.zMove` と一致する。 -/
theorem zUnitActs_spec {e : VExt sc} {pos : ℕ} {zz : ZS}
    (hendu : endSym ∉ u) (hstartu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hwf : ZWf u.length zz)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (zz.head + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + zz.head))
    (hpos : u.length ≤ pos) (hroom : pos < Text.length) :
    Tape.SeqView blank (extActs blank (zUnitActs blank startSym endSym zz.up e) e).U
        (startSym :: (u ++ [endSym])) ((zMove u Text pos zz).head + 1) ∧
      Tape.SeqView blank (extActs blank (zUnitActs blank startSym endSym zz.up e) e).Txt2 Text
        (pos - u.length + (zMove u Text pos zz).head) ∧
      zNextDir blank startSym zz.up e = (zMove u Text pos zz).up := by
  obtain ⟨w1, w2, w3⟩ := hwf
  by_cases hup : zz.up = true
  · -- 上り：`vcompActs` そのもの。
    have hacts : zUnitActs blank startSym endSym zz.up e = vcompActs endSym e := by
      unfold zUnitActs; rw [if_pos hup]
    have hhead : (zMove u Text pos zz).head = vComp u Text pos zz.head := by
      unfold zMove vComp
      rw [if_pos hup]
      by_cases h1 : zz.head < u.length
      · rw [if_pos h1]
        by_cases h2 : Text[pos - u.length + zz.head]? = u[zz.head]?
        · rw [if_pos h2, if_pos ⟨h1, h2⟩]
        · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
      · rw [if_neg h1, if_neg (fun hc => h1 hc.1)]
    have hupz : (zMove u Text pos zz).up = true := by
      unfold zMove; rw [if_pos hup]; split_ifs <;> first | rfl | exact hup
    obtain ⟨s1, s2⟩ := vcompActs_spec (blank := blank) (startSym := startSym)
      (pos := pos) hendu hU hX w1 hpos hroom
    rw [hacts, hhead, hupz]
    exact ⟨s1, s2, by simp only [zNextDir, hup, Bool.true_or]⟩
  · have hupf : zz.up = false := by simpa using hup
    by_cases h0 : zz.head = 0
    · -- 下りの左端：向きを反転するだけ（動作 0）。
      have hpk : zPeekL blank e = startSym :=
        (zPeekL_startSym_iff (u := u) hstartu hse w1 hU).2 h0
      have hacts : zUnitActs blank startSym endSym zz.up e
          = [VAct.U (sc := sc) .left, VAct.U .right] := by
        unfold zUnitActs; rw [if_neg hup, if_pos hpk]
      have hz : zMove u Text pos zz = ⟨0, 0, 0, true⟩ := by
        unfold zMove; rw [if_neg hup, if_neg (by omega : ¬ 0 < zz.head)]
      have hext : extActs blank [VAct.U (sc := sc) .left, VAct.U .right] e
          = { U := Tape.step blank (Tape.step blank e.U e.U.focus .left)
                (Tape.step blank e.U e.U.focus .left).focus .right,
              Txt2 := e.Txt2 } := rfl
      have hUlen : (0 : ℕ) + 1 < (startSym :: (u ++ [endSym])).length := by
        simp only [List.length_cons, List.length_append]; omega
      rw [hacts, hz, hext]
      refine ⟨?_, ?_, ?_⟩
      · show Tape.SeqView blank _ _ (0 + 1)
        refine Tape.seq_move_right (Tape.seq_move_left (i := 0) ?_) hUlen
        rw [← h0]; exact hU
      · show Tape.SeqView blank e.Txt2 _ (pos - u.length + 0); rw [← h0]; exact hX
      · simp only [zNextDir, hupf, Bool.false_or, hpk, decide_true]
    · -- 下り：両ヘッドを 1 つ左へ。
      have hpk : ¬ zPeekL blank e = startSym := by
        intro hc; exact h0 ((zPeekL_startSym_iff (u := u) hstartu hse w1 hU).1 hc)
      have hacts : zUnitActs blank startSym endSym zz.up e = [VAct.U .left, VAct.X .left] := by
        unfold zUnitActs; rw [if_neg hup, if_neg hpk]
      have hz : zMove u Text pos zz = ⟨zz.head - 1, zz.lo, zz.hi, false⟩ := by
        unfold zMove; rw [if_neg hup, if_pos (by omega : 0 < zz.head)]
      have hext : extActs blank [VAct.U (sc := sc) .left, VAct.X .left] e
          = { U := Tape.step blank e.U e.U.focus .left,
              Txt2 := Tape.step blank e.Txt2 e.Txt2.focus .left } := rfl
      rw [hacts, hz, hext]
      refine ⟨?_, ?_, ?_⟩
      · show Tape.SeqView blank (Tape.step blank e.U e.U.focus .left) _ (zz.head - 1 + 1)
        rw [show zz.head - 1 + 1 = zz.head from by omega]
        exact Tape.seq_move_left (i := zz.head) hU
      · show Tape.SeqView blank (Tape.step blank e.Txt2 e.Txt2.focus .left) _
          (pos - u.length + (zz.head - 1))
        refine Tape.seq_move_left (i := pos - u.length + (zz.head - 1)) ?_
        rw [show pos - u.length + (zz.head - 1) + 1 = pos - u.length + zz.head from by omega]
        exact hX
      · simp only [zNextDir, hupf, Bool.false_or]
        exact (decide_eq_false hpk)

/-! ### `zMove` のヘッドと向き（枝別） -/

theorem zMove_head_up {u Text : List (Fin sc)} {pos : ℕ} {zz : ZS} (hup : zz.up = true) :
    (zMove u Text pos zz).head = vComp u Text pos zz.head := by
  unfold zMove vComp
  rw [if_pos hup]
  by_cases h1 : zz.head < u.length
  · rw [if_pos h1]
    by_cases h2 : Text[pos - u.length + zz.head]? = u[zz.head]?
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun hc => h2 hc.2)]
  · rw [if_neg h1, if_neg (fun hc => h1 hc.1)]

theorem zMove_up_up {u Text : List (Fin sc)} {pos : ℕ} {zz : ZS} (hup : zz.up = true) :
    (zMove u Text pos zz).up = true := by
  unfold zMove; rw [if_pos hup]; split_ifs <;> first | rfl | exact hup

theorem zMove_head_down {u Text : List (Fin sc)} {pos : ℕ} {zz : ZS} (hup : zz.up = false) :
    (zMove u Text pos zz).head = zz.head - 1 := by
  unfold zMove
  rw [if_neg (by simp [hup])]
  by_cases h1 : 0 < zz.head
  · rw [if_pos h1]
  · rw [if_neg h1]; show 0 = zz.head - 1; omega

theorem zMove_up_down {u Text : List (Fin sc)} {pos : ℕ} {zz : ZS} (hup : zz.up = false) :
    (zMove u Text pos zz).up = decide (zz.head = 0) := by
  unfold zMove
  rw [if_neg (by simp [hup])]
  by_cases h1 : 0 < zz.head
  · rw [if_pos h1]; exact (decide_eq_false (by omega)).symm
  · rw [if_neg h1]; exact (decide_eq_true (by omega)).symm

/-- **`n` 単位動作の実現**：`GSVerifierZ.zMoves` と一致する。 -/
theorem zUnits_spec {pos : ℕ}
    (hendu : endSym ∉ u) (hstartu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hpos : u.length ≤ pos) (hroom : pos < Text.length) :
    ∀ (n : ℕ) (zz : ZS) (e : VExt sc), ZWf u.length zz →
      Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (zz.head + 1) →
      Tape.SeqView blank e.Txt2 Text (pos - u.length + zz.head) →
      Tape.SeqView blank (extActs blank (zUnits blank startSym endSym n zz.up e) e).U
          (startSym :: (u ++ [endSym])) ((zMoves u Text pos n zz).head + 1) ∧
        Tape.SeqView blank (extActs blank (zUnits blank startSym endSym n zz.up e) e).Txt2 Text
          (pos - u.length + (zMoves u Text pos n zz).head) ∧
        zDirN blank startSym endSym n zz.up e = (zMoves u Text pos n zz).up := by
  intro n
  induction n with
  | zero => intro zz e _ hU hX; exact ⟨hU, hX, rfl⟩
  | succ n ih =>
    intro zz e hwf hU hX
    obtain ⟨s1, s2, s3⟩ := zUnitActs_spec (u := u) (Text := Text) (pos := pos)
      hendu hstartu hse hwf hU hX hpos hroom
    have hwf' : ZWf u.length (zMove u Text pos zz) := zMove_wf hwf
    have key := ih (zMove u Text pos zz)
      (extActs blank (zUnitActs blank startSym endSym zz.up e) e) hwf' s1 s2
    rw [← s3] at key
    refine ⟨?_, ?_, ?_⟩
    · show Tape.SeqView blank
        (extActs blank (zUnitActs blank startSym endSym zz.up e ++
          zUnits blank startSym endSym n (zNextDir blank startSym zz.up e)
            (extActs blank (zUnitActs blank startSym endSym zz.up e) e)) e).U _ _
      rw [extActs_append]; exact key.1
    · show Tape.SeqView blank
        (extActs blank (zUnitActs blank startSym endSym zz.up e ++
          zUnits blank startSym endSym n (zNextDir blank startSym zz.up e)
            (extActs blank (zUnitActs blank startSym endSym zz.up e) e)) e).Txt2 _ _
      rw [extActs_append]; exact key.2.1
    · show zDirN blank startSym endSym n (zNextDir blank startSym zz.up e)
        (extActs blank (zUnitActs blank startSym endSym zz.up e) e) = _
      exact key.2.2

end Unit


/-! ## 4. 一歩の動作列 `vprogramZ'` -/

/-- **ジグザグ一歩の動作列**。向きの 1 ビット `up` は有限制御が持つ（テープには無い）。

* 比較枝：`advActs`（走査）＋ ジグザグ単位動作 `zQuota = 4` 個。
* ずらし枝：`probeActs` 2 本 ＋ 融合ループ（`perProgramX` / `resProgramX`）だけ。
  **`uxWalk` は無い**——`U` は動かさず、`Txt2` はループが `gsShift` だけ右へ運ぶ。 -/
def vprogramZ' (blank startSym endSym mark : Fin sc) (k : ℕ) (up : Bool) (vt : VTapes' sc) :
    List (VAct' sc) :=
  if Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) then
    (GSTapes.advActs blank mark vt.1).map VAct'.S ++
      (zUnits blank startSym endSym zQuota up vt.2).map liftAct
  else
    (GSTapes.probeActs blank GSTapes.tAn).map VAct'.S ++
      (GSTapes.probeActs blank GSTapes.tRn).map VAct'.S ++
      (if Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark then
        perProgramX blank mark (GSTapes.p1Of' vt.1) vt
      else
        resProgramX blank mark k (GSTapes.qOf' vt.1) vt)

/-- 一歩のあとの向き（有限制御の状態遷移）。ずらしでは `down` に張り直す。 -/
def vDirZ (blank startSym endSym : Fin sc) (up : Bool) (vt : VTapes' sc) : Bool :=
  if Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) then
    zDirN blank startSym endSym zQuota up vt.2
  else false

/-! ## 5. 抽象一歩の枝分け -/

section StepBranch

variable {u v Text : List (Fin sc)} {k p₁ r : ℕ} {z : VStateZ}

theorem vStepZ_adv (h : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    vStepZ u v k p₁ r Text z
      = (scanStep v k p₁ r Text z.1, zMoves u Text z.1.pos zQuota z.2) := by
  unfold vStepZ; rw [if_neg h.1, if_pos h.2]

theorem vStepZ_shift (h : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?)) :
    vStepZ u v k p₁ r Text z = (scanStep v k p₁ r Text z.1, zReset z.2) := by
  unfold vStepZ
  by_cases h1 : z.1.q = v.length
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (fun hc => h ⟨h1, hc⟩)]

end StepBranch

/-! ## 6. 主定理：一歩が符号化を保つこと -/

section VEncodesZ

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VStateZ}

/-- **主定理**：`vprogramZ'` の一歩は `VEncodesZ'` を保ち、向きも整合する
（`GSVTapes.vencodes_stepX` のジグザグ版）。 -/
theorem vencodes_stepZ (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (hstartu : startSym ∉ u)
    (hse : startSym ≠ endSym)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hwf : ZWf u.length z.2)
    (hq : z.1.q ≤ v.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length) :
    VEncodesZ' blank startSym endSym mark u v Text k p₁ r
        (vApplyActs' blank (vprogramZ' blank startSym endSym mark k z.2.up vt) vt)
        (vStepZ u v k p₁ r Text z) ∧
      vDirZ blank startSym endSym z.2.up vt = (vStepZ u v k p₁ r Text z).2.up := by
  have hscan := GSTapes.encodes_step' hk hne hend hE.scan hq hfit
  have hheadle : z.2.head ≤ u.length := hwf.1
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · -- 比較枝
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hE.scan hq).1 hadv
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv ⟨ha1, ha2⟩
    have hvs := vStepZ_adv (u := u) (k := k) (p₁ := p₁) (r := r) ⟨ha1, ha2⟩
    have hroom : z.1.pos < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    have hveq : vprogramZ' blank startSym endSym mark k z.2.up vt
        = (GSTapes.advActs blank mark vt.1).map VAct'.S ++
          (zUnits blank startSym endSym zQuota z.2.up vt.2).map liftAct := by
      unfold vprogramZ'; rw [if_pos hadv]
    have hprogAdv : GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k vt.1) vt.1
        = GSTapes.applyActs' blank (GSTapes.advActs blank mark vt.1) vt.1 := by
      unfold GSTapes.program'; rw [if_pos hadv]
    rw [hprogAdv] at hscan
    obtain ⟨hU2, hX2, hD2⟩ := zUnits_spec (blank := blank) (startSym := startSym)
      (endSym := endSym) (u := u) (Text := Text) (pos := z.1.pos)
      hendu hstartu hse hpos hroom zQuota z.2 vt.2 hwf hE.pat hE.txt2
    rw [hveq, hvs]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [vApplyActs'_append, vApplyActs'_map_S, vApplyActs'_map_liftAct_fst]
      exact hscan
    · rw [vApplyActs'_append, vApplyActs'_map_S, vApplyActs'_snd, extActs'_map_liftAct]
      exact hU2
    · rw [vApplyActs'_append, vApplyActs'_map_S, vApplyActs'_snd, extActs'_map_liftAct, hss]
      exact hX2
    · show vDirZ blank startSym endSym z.2.up vt = _
      unfold vDirZ; rw [if_pos hadv]; exact hD2
  · -- ずらし枝：`U` は動かない。`Txt2` は融合ループが `gsShift` だけ右へ運ぶ。
    have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hroom : z.1.pos + gsShift k p₁ r z.1.q < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    have hvs := vStepZ_shift (u := u) (k := k) (p₁ := p₁) (r := r) hna
    rw [hvs, hss]
    rw [hss] at hscan
    have hveq : vprogramZ' blank startSym endSym mark k z.2.up vt
        = (GSTapes.probeActs blank GSTapes.tAn).map VAct'.S ++
          (GSTapes.probeActs blank GSTapes.tRn).map VAct'.S ++
          (if Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
              Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark then
            perProgramX blank mark (GSTapes.p1Of' vt.1) vt
          else
            resProgramX blank mark k (GSTapes.qOf' vt.1) vt) := by
      unfold vprogramZ'; rw [if_neg hadv]
    have hdir : vDirZ blank startSym endSym z.2.up vt = false := by
      unfold vDirZ; rw [if_neg hadv]
    rw [hveq]
    simp only [vApplyActs'_append, vApplyActs'_map_S]
    have hrnId : GSTapes.applyActs' blank (GSTapes.probeActs blank GSTapes.tRn)
        (GSTapes.applyActs' blank (GSTapes.probeActs blank GSTapes.tAn) vt.1) = vt.1 := by
      rw [GSTapes.probeActs_id hE.scan.quad.an]
      exact GSTapes.probeActs_id hE.scan.quad.rn
    rw [hrnId]
    have hprogEq : GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k vt.1) vt.1
        = GSTapes.applyActs' blank
            (if Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
                Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark then
              GSTapes.perProgram blank mark (GSTapes.p1Of' vt.1) vt.1
            else
              GSTapes.resProgram blank mark k (GSTapes.qOf' vt.1) vt.1) vt.1 := by
      unfold GSTapes.program'
      rw [if_neg hadv, GSTapes.applyActs'_append, GSTapes.applyActs'_append,
        GSTapes.probeActs_id hE.scan.quad.an, GSTapes.probeActs_id hE.scan.quad.rn]
    by_cases hcond : k * p₁ ≤ z.1.q ∧ z.1.q ≤ r
    · -- 周期ずらし
      have hcondT : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark :=
        (GSTapes.period_iff' hne hE.scan).2 hcond
      have hgs : gsShift k p₁ r z.1.q = p₁ := by unfold gsShift; rw [if_pos hcond]
      have hp1 : GSTapes.p1Of' vt.1 = p₁ := GSTapes.p1Of'_eq hE.scan
      rw [if_pos hcondT, hp1] at hprogEq
      rw [hprogEq] at hscan
      rw [if_pos hcondT, hp1]
      have hle : p₁ ≤ z.1.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
      have hroomP : (z.1.pos - u.length + z.2.head) + p₁ < Text.length := by
        rw [hgs] at hroom; omega
      obtain ⟨_, _, _, _, _, _, hLoopTxt2⟩ := perLoop1X_spec (blank := blank) (mark := mark)
        (w := startSym :: (v ++ [endSym])) (Text := Text) hne p₁ vt z.1.q p₁ 0
        (k * p₁) r (z.1.pos - u.length + z.2.head) hle (Nat.le_refl _) hE.scan.pat hE.scan.c1
        hE.scan.c2 hE.scan.quad hE.txt2 hroomP
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [perProgramX_fst]; exact hscan
      · show Tape.SeqView blank (vApplyActs' blank (perProgramX blank mark p₁ vt) vt).2.U _
          ((zReset z.2).head + 1)
        rw [perProgramX_U]; exact hE.pat
      · show Tape.SeqView blank (vApplyActs' blank (perProgramX blank mark p₁ vt) vt).2.Txt2
          Text (z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head)
        rw [perProgramX_Txt2,
          show z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head
            = z.1.pos - u.length + z.2.head + p₁ from by
              simp only [zReset]; rw [hgs]; omega]
        exact hLoopTxt2
      · exact hdir
    · -- リセットずらし
      have hcondT : ¬ (Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark) :=
        fun hc => hcond ((GSTapes.period_iff' hne hE.scan).1 hc)
      have hgs : gsShift k p₁ r z.1.q = max 1 (ceilDiv z.1.q k) := by
        unfold gsShift; rw [if_neg hcond]
      have hqz : GSTapes.qOf' vt.1 = z.1.q := GSTapes.qOf'_eq hE.scan
      rw [if_neg hcondT, hqz] at hprogEq
      rw [hprogEq] at hscan
      rw [if_neg hcondT, hqz]
      have hUres : Tape.SeqView blank
          (vApplyActs' blank (resProgramX blank mark k z.1.q vt) vt).2.U
          (startSym :: (u ++ [endSym])) ((zReset z.2).head + 1) := by
        rw [resProgramX_U]; exact hE.pat
      rcases Nat.eq_zero_or_pos z.1.q with hq0 | hq0
      · -- `q = 0`：`stays k 0 0 = 0`、`resProgramX` の特別枝が `Txt2` を `+1`。
        have hcd0 : ceilDiv 0 k = 0 := by
          unfold ceilDiv
          simpa using Nat.div_eq_of_lt (by omega : (0 : ℕ) + k - 1 < k)
        have hgs1 : gsShift k p₁ r z.1.q = 1 := by rw [hgs, hq0, hcd0]; rfl
        have hstaysroom : (z.1.pos - u.length + z.2.head) + GSTapes.stays k z.1.q 0
            < Text.length := by
          rw [hq0]; simp only [GSTapes.stays, Nat.add_zero]
          rw [hgs1] at hroom; omega
        have hTarg : Tape.SeqView blank (vt.1 GSTapes.tT) Text
            ((z.1.pos + z.1.q) + GSTapes.moves k z.1.q 0) := by
          have heq : (z.1.pos + z.1.q) + GSTapes.moves k z.1.q 0 = z.1.pos + z.1.q := by
            rw [hq0]; simp [GSTapes.moves]
          rw [heq]; exact hE.scan.txt
        obtain ⟨_, _, _, _, _, _, hL⟩ := resLoopX_spec (blank := blank) (mark := mark) hne
          (w := startSym :: (v ++ [endSym])) (Text := Text) k z.1.q 0 vt z.1.q
          (z.1.pos + z.1.q) (k * p₁) r (z.1.pos - u.length + z.2.head) (Nat.le_refl _)
          hE.scan.pat hTarg hE.scan.quad hE.txt2 hstaysroom
        have hstays0 : GSTapes.stays k z.1.q 0 = 0 := by rw [hq0]; rfl
        have hL' : Tape.SeqView blank
            (vApplyActs' blank (resLoopX blank mark k z.1.q 0 vt) vt).2.Txt2 Text
            (z.1.pos - u.length + z.2.head) := by
          rw [hstays0] at hL; simpa using hL
        refine ⟨⟨?_, hUres, ?_⟩, hdir⟩
        · rw [resProgramX_fst]; exact hscan
        · show Tape.SeqView blank
            (vApplyActs' blank (resProgramX blank mark k z.1.q vt) vt).2.Txt2 Text
            (z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head)
          rw [resProgramX_Txt2_of_eq hq0 vt,
            show z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head
              = (z.1.pos - u.length + z.2.head) + 1 from by
                simp only [zReset]; rw [hgs1]; omega]
          refine Tape.seq_move_right hL' ?_
          rw [hgs1] at hroom; omega
      · -- `q ≥ 1`：`stays k q 0 = ceilDiv q k = gsShift`。
        have hc1 : 1 ≤ ceilDiv z.1.q k := GSTapes.ceilDiv_pos hk hq0
        have hgs' : gsShift k p₁ r z.1.q = ceilDiv z.1.q k := by rw [hgs]; omega
        have hqne : ¬ z.1.q = 0 := by omega
        have hstaysval : GSTapes.stays k z.1.q 0 = ceilDiv z.1.q k := by
          have h1 := GSTapes.stays_add_moves k z.1.q 0
          have h2 := GSTapes.moves_zero k hk z.1.q
          have h3 := GSTapes.ceilDiv_le_self (k := k) (q := z.1.q) hk
          omega
        have hroom' := hroom
        rw [hgs'] at hroom'
        have hstaysroom : (z.1.pos - u.length + z.2.head) + GSTapes.stays k z.1.q 0
            < Text.length := by rw [hstaysval]; omega
        have hTarg : Tape.SeqView blank (vt.1 GSTapes.tT) Text
            ((z.1.pos + ceilDiv z.1.q k) + GSTapes.moves k z.1.q 0) := by
          have hle : ceilDiv z.1.q k ≤ z.1.q := GSTapes.ceilDiv_le_self hk
          have heq : (z.1.pos + ceilDiv z.1.q k) + GSTapes.moves k z.1.q 0
              = z.1.pos + z.1.q := by rw [GSTapes.moves_zero k hk z.1.q]; omega
          rw [heq]; exact hE.scan.txt
        obtain ⟨_, _, _, _, _, _, hL⟩ := resLoopX_spec (blank := blank) (mark := mark) hne
          (w := startSym :: (v ++ [endSym])) (Text := Text) k z.1.q 0 vt z.1.q
          (z.1.pos + ceilDiv z.1.q k) (k * p₁) r (z.1.pos - u.length + z.2.head)
          (Nat.le_refl _) hE.scan.pat hTarg hE.scan.quad hE.txt2 hstaysroom
        refine ⟨⟨?_, hUres, ?_⟩, hdir⟩
        · rw [resProgramX_fst]; exact hscan
        · show Tape.SeqView blank
            (vApplyActs' blank (resProgramX blank mark k z.1.q vt) vt).2.Txt2 Text
            (z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head)
          rw [resProgramX_Txt2_of_ne hqne vt,
            show z.1.pos + gsShift k p₁ r z.1.q - u.length + (zReset z.2).head
              = (z.1.pos - u.length + z.2.head) + GSTapes.stays k z.1.q 0 from by
                simp only [zReset]; rw [hgs', ← hstaysval]; omega]
          exact hL

end VEncodesZ


/-! ## 7. 費用（点ごと、`Ψ` 無し） -/

/-- 償却係数 `A_Z = 9k + 14`（`StageMatcherProg.xA` と同じ）。 -/
def zA (k : ℕ) : ℕ := 9 * k + 14

/-- 償却定数 `B_Z = 16`。**`X` 版の `2·checked` に当たる項は無い**。 -/
def zB : ℕ := 16

example : zA 8 = 86 := by norm_num [zA]

section Cost

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VStateZ}

/-- **比較（前進）枝の動作数**：`|advActs| ≤ 8` ＋ ジグザグ `4` 単位 `≤ 8`。 -/
theorem vprogramZ'_adv_le (hend : endSym ∉ v)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length)
    (hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    (vprogramZ' blank startSym endSym mark k z.2.up vt).length ≤ 8 + 8 := by
  have hadvT : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) :=
    (GSTapes.advance_iff' hend hE.scan hq).2 hadv
  unfold vprogramZ'
  rw [if_pos hadvT]
  simp only [List.length_append, List.length_map]
  have h1 := GSTapes.advActs_length_le blank mark vt.1
  have h2 := zUnits_length_le blank startSym endSym zQuota z.2.up vt.2
  simp only [zQuota] at h2 ⊢
  omega

/-- **一歩の費用（点ごと）**：`|vprogramZ'| ≤ (9k+14)·ΔΦ + 16`。
`StageMatcherProg.vprogramX_cost` の `+ 2·checked` の項が**無い**のが要点である
（`PalPeg.PointwiseGap.rewind_not_pointwise` の反例を回避する）。 -/
theorem vprogramZ'_cost (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    (vprogramZ' blank startSym endSym mark k z.2.up vt).length ≤
      zA k * (Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1) + zB := by
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD]
  unfold vprogramZ' zA zB
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    simp only [List.length_append, List.length_map]
    have h1 := GSTapes.advActs_length_le blank mark vt.1
    have h2 := zUnits_length_le blank startSym endSym zQuota z.2.up vt.2
    simp only [zQuota] at h2 ⊢
    omega
  · rw [if_neg hadv]
    have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hsh : gsShift k p₁ r z.1.q ≤ D := by
      have h := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
      rw [← hss, hD] at h
      exact h
    have hAn := GSTapes.probeActs_length blank GSTapes.tAn
    have hRn := GSTapes.probeActs_length blank GSTapes.tRn
    simp only [List.length_append, List.length_map]
    by_cases hcond : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
        Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark
    · rw [if_pos hcond]
      have hp1 : GSTapes.p1Of' vt.1 = p₁ := GSTapes.p1Of'_eq hE.scan
      have hgs : gsShift k p₁ r z.1.q = p₁ := by
        unfold gsShift; rw [if_pos ((GSTapes.period_iff' hne hE.scan).1 hcond)]
      have hle := perProgramX_length_le blank mark (GSTapes.p1Of' vt.1) vt
      have hpD : p₁ ≤ D := by rw [← hgs]; exact hsh
      rw [hp1] at hle
      rw [hp1, hAn, hRn]
      have h14 : 14 * p₁ ≤ (9 * k + 14) * D := by
        have : (9 * k + 14) * D = 9 * k * D + 14 * D := by ring
        have h2 : 14 * p₁ ≤ 14 * D := Nat.mul_le_mul_left 14 hpD
        omega
      omega
    · rw [if_neg hcond]
      have hqz : GSTapes.qOf' vt.1 = z.1.q := GSTapes.qOf'_eq hE.scan
      have hgs : gsShift k p₁ r z.1.q = max 1 (ceilDiv z.1.q k) := by
        unfold gsShift
        rw [if_neg (fun hcon => hcond ((GSTapes.period_iff' hne hE.scan).2 hcon))]
      have hcb : z.1.q ≤ k * ceilDiv z.1.q k := (ceilDiv_bounds hk).1
      have hmax : ceilDiv z.1.q k ≤ max 1 (ceilDiv z.1.q k) := le_max_right _ _
      have hkq : z.1.q ≤ k * D := by
        have h1 : k * ceilDiv z.1.q k ≤ k * gsShift k p₁ r z.1.q := by
          rw [hgs]; exact Nat.mul_le_mul_left k hmax
        have h2 : k * gsShift k p₁ r z.1.q ≤ k * D := Nat.mul_le_mul_left k hsh
        omega
      have hle := resProgramX_length_le blank mark k (GSTapes.qOf' vt.1) vt
      rw [hqz] at hle
      rw [hqz, hAn, hRn]
      have h9 : 9 * z.1.q ≤ 9 * (k * D) := Nat.mul_le_mul_left 9 hkq
      have h9' : 9 * (k * D) ≤ (9 * k + 14) * D := by
        have : (9 * k + 14) * D = 9 * (k * D) + 14 * D := by ring
        omega
      omega

end Cost

/-! ## 8. 公理の確認 -/

#print axioms zUnitActs_spec
#print axioms zUnits_spec
#print axioms vencodes_stepZ
#print axioms vprogramZ'_cost
#print axioms vprogramZ'_adv_le

end GSVTapesZ
end PalPeg
