import PalPeg.GSVerifierProgX
import PalPeg.GSVerifierTapesZ

/-!
# ジグザグ検証器の有限制御プログラム (`GSVerifierProgZ`)

`PalPeg.GSVTapesZ.vprogramZ'` の一歩を、`Prog Act10 Cond10` の有限制御プログラム
`vprogZ k up` として実現する（`PalPeg.GSVProg.vprogX` のジグザグ版）。

`vprogX` との違いは 2 点だけである。

* **比較枝**：`vcomp2Prog`（`vcompProg` を 2 回）を、ジグザグ単位動作 `zQuota = 4`
  個のプログラム `zUnitsProg` に置き換える。
* **ずらし枝**：`shiftProg k = shiftCore k ; uxWalkProg` の **`uxWalkProg` を削除**し、
  `shiftCore k` だけにする。

向きの 1 ビットはテープではなくプログラム（有限制御の状態）が持つ。`up` / `down` の
2 種類のプログラムがあり、一歩のあとの向きは `GSVTapesZ.vDirZ` が与える。
下り向きの判定は `U` を 1 つ左へ動かしてから `Cond10.notStartU` を見る形なので、
条件は**現在読んでいる記号**だけで書けている（`startSym ∉ u`, `startSym ≠ endSym` が要る）。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg
namespace GSVProgZ

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.GSProg
open PalPeg.GSTapes
open PalPeg.GSVProg
open PalPeg.GSVTapes (VAct VAct' VTapes' vApplyAct' vApplyActs' liftAct vcompActs extActs
  extActs' extActs'_map_liftAct vApplyActs'_snd)
open PalPeg.GSVTapesZ
open PalPeg.GSVerifierZ (ZWf VStateZ zQuota vStepZ)

variable {sc : ℕ}

/-! ## 1. ジグザグ単位動作のプログラム -/

/-- **`n` 単位動作のプログラム**。向き `up` はプログラムの構造に埋め込まれる。

* 上り：`GSVProg.vcompProg`（`U` が `endSym` でなく `Txt2` と一致すれば両ヘッド右）。
* 下り：`U` を 1 つ左へ動かし、`startSym` でなければ `Txt2` も左へ（下りのまま）、
  `startSym` なら `U` を戻して上りに切り替える。 -/
def zUnitsProg : ℕ → Bool → Prog Act10 Cond10
  | 0, _ => Prog.skip
  | n + 1, true => Prog.seq vcompProg (zUnitsProg n true)
  | n + 1, false =>
      Prog.seq (KEEP10 tU .left)
        (Prog.ite Cond10.notStartU
          (Prog.seq (KEEP10 tX .left) (zUnitsProg n false))
          (Prog.seq (KEEP10 tU .right) (zUnitsProg n true)))

section UnitSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}

/-- **単位動作プログラムの一致**：`zUnitsProg n up` はちょうど
`GSVTapesZ.zUnits blank startSym endSym n up vt.2` の動作列を実行する。 -/
theorem zUnitsProg_exec :
    ∀ (n : ℕ) (up : Bool) (vt : VTapes' sc),
      ExecV Terminal blank endSym mark startSym (zUnitsProg n up) vt
        ((zUnits blank startSym endSym n up vt.2).map liftAct) := by
  intro n
  induction n with
  | zero =>
    intro up vt
    show ExecV Terminal blank endSym mark startSym Prog.skip vt _
    rw [show (zUnits blank startSym endSym 0 up vt.2).map liftAct
        = ([] : List (VAct' sc)) from rfl]
    exact execV_skip
  | succ n ih =>
    intro up vt
    cases up with
    | true =>
      have h1 := vcompProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
        (mark := mark) (startSym := startSym) vt
      have hsnd : (vApplyActs' blank ((vcompActs endSym vt.2).map liftAct) vt).2
          = extActs blank (vcompActs endSym vt.2) vt.2 := by
        rw [vApplyActs'_snd, extActs'_map_liftAct]
      have h2 := ih true (vApplyActs' blank ((vcompActs endSym vt.2).map liftAct) vt)
      rw [hsnd] at h2
      refine execV_of_eq ?_ (execV_seq h1 h2)
      rw [show zUnits blank startSym endSym (n + 1) true vt.2
          = zUnitActs blank startSym endSym true vt.2 ++
            zUnits blank startSym endSym n
              (zNextDir blank startSym true vt.2)
              (extActs blank (zUnitActs blank startSym endSym true vt.2) vt.2) from rfl,
        show zUnitActs blank startSym endSym true vt.2 = vcompActs endSym vt.2 from rfl,
        show zNextDir blank startSym true vt.2 = true from rfl, List.map_append]
    | false =>
      have hstep := execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
        (mark := mark) (startSym := startSym) Move.left vt
      set vt1 := vApplyAct' blank vt (VAct'.U (sc := sc) .left) with hvt1
      have hpk : Tape.read vt1.2.U = zPeekL blank vt.2 := rfl
      by_cases hs : zPeekL blank vt.2 = startSym
      · -- 左端：`U` を戻して上りへ。
        have hunit : zUnitActs blank startSym endSym false vt.2
            = [VAct.U (sc := sc) .left, VAct.U .right] := by
          unfold zUnitActs; rw [if_neg (by simp), if_pos hs]
        have hcond : condOf10 endSym mark startSym Cond10.notStartU
            (fun j => ((vTS vt1) j).focus) = false := by
          rw [notStartU_eq]
          exact decide_eq_false (by rw [hpk, hs]; exact fun hc => hc rfl)
        have h2 := execV_keepU (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) Move.right vt1
        have h3 := ih true (vApplyActs' blank [VAct'.U (sc := sc) .right] vt1)
        have hsnd : (vApplyActs' blank [VAct'.U (sc := sc) .right] vt1).2
            = extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2 := by
          show extActs' blank [VAct'.U (sc := sc) .right] vt1.2 = _
          rw [hunit]; rfl
        rw [hsnd] at h3
        refine execV_of_eq ?_ (execV_seq hstep (execV_ite_neg hcond (execV_seq h2 h3)))
        rw [show zUnits blank startSym endSym (n + 1) false vt.2
            = zUnitActs blank startSym endSym false vt.2 ++
              zUnits blank startSym endSym n
                (zNextDir blank startSym false vt.2)
                (extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2) from rfl,
          hunit,
          show zNextDir blank startSym false vt.2 = true from by
            simp only [zNextDir, Bool.false_or, hs, decide_true]]
        simp [liftAct]
      · -- 左端でない：`Txt2` も左へ、下りのまま。
        have hunit : zUnitActs blank startSym endSym false vt.2
            = [VAct.U (sc := sc) .left, VAct.X .left] := by
          unfold zUnitActs; rw [if_neg (by simp), if_neg hs]
        have hcond : condOf10 endSym mark startSym Cond10.notStartU
            (fun j => ((vTS vt1) j).focus) = true := by
          rw [notStartU_eq]
          exact decide_eq_true (by rw [hpk]; exact hs)
        have h2 := execV_keepX (Terminal := Terminal) (blank := blank) (endSym := endSym)
          (mark := mark) (startSym := startSym) Move.left vt1
        have h3 := ih false (vApplyActs' blank [VAct'.X (sc := sc) .left] vt1)
        have hsnd : (vApplyActs' blank [VAct'.X (sc := sc) .left] vt1).2
            = extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2 := by
          show extActs' blank [VAct'.X (sc := sc) .left] vt1.2 = _
          rw [hunit]; rfl
        rw [hsnd] at h3
        refine execV_of_eq ?_ (execV_seq hstep (execV_ite_pos hcond (execV_seq h2 h3)))
        rw [show zUnits blank startSym endSym (n + 1) false vt.2
            = zUnitActs blank startSym endSym false vt.2 ++
              zUnits blank startSym endSym n
                (zNextDir blank startSym false vt.2)
                (extActs blank (zUnitActs blank startSym endSym false vt.2) vt.2) from rfl,
          hunit,
          show zNextDir blank startSym false vt.2 = false from by
            simp only [zNextDir, Bool.false_or]; exact decide_eq_false hs]
        simp [liftAct]

end UnitSpec

/-! ## 2. 一歩のプログラム -/

/-- **ジグザグ一歩のプログラム**。比較枝は走査＋`zQuota` 単位、
ずらし枝は `shiftCore k`（**`uxWalkProg` は無い**）。 -/
def vprogZ (k : ℕ) (up : Bool) : Prog Act10 Cond10 :=
  Prog.ite Cond10.matchOk (Prog.seq (pmap (scanProg k)) (zUnitsProg zQuota up))
    (shiftCore k)

theorem vprogramZ'_shift (blank startSym endSym mark : Fin sc) (k : ℕ) (up : Bool)
    (vt : VTapes' sc)
    (hadv : ¬ (Tape.read (vt.1 tP) ≠ endSym ∧ Tape.read (vt.1 tP) = Tape.read (vt.1 tT))) :
    vprogramZ' blank startSym endSym mark k up vt = shiftCoreActs blank mark k vt := by
  unfold PalPeg.GSVTapesZ.vprogramZ' shiftCoreActs shiftBranch
  rw [if_neg hadv]

section RoundZSpec

variable {Terminal : Type} {blank endSym mark startSym : Fin sc}
variable {u v Text : List (Fin sc)} {k p₁ r : ℕ} {vt : VTapes' sc} {z : VStateZ}

/-- **主定理（1 ラウンドの一致、両枝）**：`vprogZ k up` は状態 `vt` からちょうど
`vprogramZ' blank startSym endSym mark k up vt` の動作列を実行して継続に戻る。 -/
theorem vprogZ_exec (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (up : Bool)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length) :
    ExecV Terminal blank endSym mark startSym (vprogZ k up) vt
      (vprogramZ' blank startSym endSym mark k up vt) := by
  unfold vprogZ
  by_cases hadv : Tape.read (vt.1 tP) ≠ endSym ∧ Tape.read (vt.1 tP) = Tape.read (vt.1 tT)
  · have hprog : program' blank endSym mark k vt.1 = advActs blank mark vt.1 := by
      unfold program'; rw [if_pos hadv]
    have hscan := execV_lift (Terminal := Terminal) (vt := vt)
      (scanProg_exec (Terminal := Terminal) (startSym := startSym) hk hne hstart hE hq)
    have hsnd : (vApplyActs' blank
        ((program' blank endSym mark k vt.1).map VAct'.S) vt).2 = vt.2 := by
      rw [PalPeg.GSVTapes.vApplyActs'_map_S]
    have hunits := zUnitsProg_exec (Terminal := Terminal) (blank := blank) (endSym := endSym)
      (mark := mark) (startSym := startSym) zQuota up
      (vApplyActs' blank ((program' blank endSym mark k vt.1).map VAct'.S) vt)
    rw [hsnd] at hunits
    refine execV_ite_pos (by rw [matchOk_eq]; exact decide_eq_true hadv) ?_
    refine execV_of_eq ?_ (execV_seq hscan hunits)
    unfold PalPeg.GSVTapesZ.vprogramZ'
    rw [if_pos hadv, hprog]
  · refine execV_ite_neg (by rw [matchOk_eq]; exact decide_eq_false hadv) ?_
    rw [vprogramZ'_shift blank startSym endSym mark k up vt hadv]
    exact shiftCore_exec (Terminal := Terminal) (z := (z.1, 0)) hk hne hstart hE hq

/-- **トレースの一致**。 -/
theorem vprogZ_trace (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v) (up : Bool)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramZ' blank startSym endSym mark k up vt).length) :
    trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogZ k up], vTS vt)
      = vavecs blank (vprogramZ' blank startSym endSym mark k up vt) vt := by
  have h := vprogZ_exec (Terminal := Terminal) (startSym := startSym) (v := v) (Text := Text)
    (p₁ := p₁) (r := r) (z := z) hk hne hstart up hE hq
  have h2 := (h [] l (by rw [vavecs_length]; exact hl)).1
  rw [show ([vprogZ k up] ++ ([] : Stack Act10 Cond10)) = [vprogZ k up] from rfl] at h2
  exact h2

/-- トレースの長さは動作列の長さに等しい。 -/
theorem vprogZ_trace_length (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v)
    (up : Bool)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramZ' blank startSym endSym mark k up vt).length) :
    (trace (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogZ k up], vTS vt)).length
      = (vprogramZ' blank startSym endSym mark k up vt).length := by
  rw [vprogZ_trace (Terminal := Terminal) (startSym := startSym) (v := v) (Text := Text)
    (p₁ := p₁) (r := r) (z := z) hk hne hstart up hE hq l hl, vavecs_length]

/-- **テープの一致**。 -/
theorem vprogZ_tapes (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v) (up : Bool)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramZ' blank startSym endSym mark k up vt).length) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
        ([vprogZ k up], vTS vt)).2
      = vTS (vApplyActs' blank (vprogramZ' blank startSym endSym mark k up vt) vt) := by
  rw [runInputs_snd_eq_applyTrace,
    vprogZ_trace (Terminal := Terminal) (startSym := startSym) (v := v) (Text := Text)
      (p₁ := p₁) (r := r) (z := z) hk hne hstart up hE hq l hl]
  exact applyTrace_vavecs blank _ vt

/-- **停止**。 -/
theorem vprogZ_halts (hk : 0 < k) (hne : mark ≠ blank) (hstart : startSym ∉ v) (up : Bool)
    (hE : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1)
    (hq : z.1.q ≤ v.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramZ' blank startSym endSym mark k up vt).length)
    (x : Option Terminal) :
    (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
      ([vprogZ k up], vTS vt)).1 = [] :=
  exec_halts (vprogZ_exec (Terminal := Terminal) (startSym := startSym) (v := v)
    (Text := Text) (p₁ := p₁) (r := r) (z := z) hk hne hstart up hE hq) l
    (by rw [vavecs_length]; exact hl) x

/-- **符号化の保存**（`GSVTapesZ.vencodes_stepZ` の言い換え）。
向きは `GSVTapesZ.vDirZ` に従って更新される。 -/
theorem vprogZ_encodes (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hstart : startSym ∉ v) (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hsu : startSym ∉ u) (hse : startSym ≠ endSym)
    (hE : VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt z)
    (hwf : ZWf u.length z.2)
    (hq : z.1.q ≤ v.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length)
    (l : List (Option Terminal))
    (hl : l.length = (vprogramZ' blank startSym endSym mark k z.2.up vt).length) :
    ∃ vt' : VTapes' sc,
      (runInputs (I10 (Terminal := Terminal) blank endSym mark startSym) blank l
          ([vprogZ k z.2.up], vTS vt)).2 = vTS vt' ∧
        VEncodesZ' blank startSym endSym mark u v Text k p₁ r vt'
          (vStepZ u v k p₁ r Text z) ∧
        vDirZ blank startSym endSym z.2.up vt = (vStepZ u v k p₁ r Text z).2.up := by
  obtain ⟨he1, he2⟩ := vencodes_stepZ hk hp hne hend hendu hsu hse hE hwf hq hpos hfit
  exact ⟨vApplyActs' blank (vprogramZ' blank startSym endSym mark k z.2.up vt) vt,
    vprogZ_tapes (Terminal := Terminal) (startSym := startSym) (v := v) (Text := Text)
      (p₁ := p₁) (r := r) (z := z) hk hne hstart z.2.up hE.scan hq l hl, he1, he2⟩

end RoundZSpec

/-! ## 3. 公理の確認 -/

#print axioms zUnitsProg_exec
#print axioms vprogZ_exec
#print axioms vprogZ_trace
#print axioms vprogZ_trace_length
#print axioms vprogZ_tapes
#print axioms vprogZ_halts
#print axioms vprogZ_encodes

end GSVProgZ
end PalPeg
