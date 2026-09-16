import PalPeg.GSVerifier
import PalPeg.GSScanTapes

/-!
# インターリーブ検証器のテープ実現 (`GSVerifierTapes`)

`PalPeg.GSVerifier` の添字レベルの一歩 `vStep`（走査 1 歩 ＋ 接頭辞 `u` の比較高々 2 回、
ずらしなら `checked := 0`）を、`PalPeg.GSScanTapes` の走査段テープ計画の**上に積んで**
1 セル単位のヘッド動作列として実現する。

## テープ配置

走査段の 3 本（`P` / `Txt` / `Cnt`、`GSTapes.TapesState`）に、検証器用の 2 本を足す：

* `U`    — 接頭辞テープ。語 `startSym :: (u ++ [endSym])`、ヘッドは添字 `checked + 1`。
           左端 `startSym` は左端検出用、右端 `endSym` は `checked = |u|` 検出用
           （`P` テープと完全に同じ規約）。
* `Txt2` — テキストの **2 本目のコピー**（内容は `Txt` と同じ `Text`）。ヘッドは検証器の
           読み位置 `pos - |u| + checked`。走査ヘッド `pos + q` とは独立に動かしたいので
           テープを分ける（`checked ≤ |u| ≤ pos` より読むのは到着済みの文字だけ）。

`VTapes := GSTapes.TapesState × VExt`、`VEncodes` はこの 5 本の符号化。

## ラウンドの動作列 `vprogram`

1. 走査段 `GSTapes.program`（オラクルビット `b` は `GSScanTapes` と**同じ仮定のまま**
   パラメータとして受け取る）を `VAct.S` で持ち上げて実行。
2. 続けて検証器の動作。分岐はすべて**テープの読み**で決まる（`GSTapes.advance_iff`）：
   * `v` の比較成功（`read P ≠ endSym ∧ read P = read Txt`）なら `vComp` を高々 2 回。
     1 回の `vComp` は「`read U` と `read Txt2` を比べ、等しくかつ `read U ≠ endSym` なら
     両ヘッドを右へ 1、そうでなければ何もしない」（`vcompActs`）。不一致で何もしないのは
     `vComp` が `checked` をその場で止める（＝この候補は死ぬ）ことの忠実な写し。
   * ずらし（周期 or リセット）なら `checked := 0`：`U` のヘッドを添字 `1` まで
     `checked` 歩戻し、`Txt2` を新しい `pos' - |u|` へ張り直す（`walkActs`）。

## 費用

* 比較枝の追加動作は `≤ 4`。
* ずらし枝の追加動作 `walkLen checked δ = checked + |δ - checked|` は
  `≤ 2*checked + δ ≤ 2|u| + δ`、すなわち周期ずらしで `≤ p₁ + 2|u|`、
  リセットずらしで `≤ q + 1 + 2|u|`（`walkLen_le_period` / `walkLen_le_reset`）。
* `δ = gsShift ≤ ΔΦ`（`gsShift_le_dPhi`）なので、追加動作のうち `δ` の部分は
  走査段と同じポテンシャルで償却でき、残るのは `|u|` に比例する項だけ：

  `vprogram_cost : (vprogram …).length ≤ (2k+3) * (Φ(scanStep st) - Φ st) + 12 + 2|u|`

  （`A = 2k+3`, `B = 12`, `C = 2`）。
* さらに **`C * |u|` の項は L1（`(k-1)|u| < |x|`）を使わずに償却できる**（§8）。
  ずらしの巻き戻し `2*checked` は、前回のずらし以降に成功した `v` の比較
  （`Φ` が `+1` される歩）にそのまま付け替えられる（不変条件
  `VCheckedInv : checked ≤ 2*q`、ポテンシャル `Ψ = 2*checked`）：

  `vrun_tape_cost_init : vRunCostTapes … n (vt, (⟨|u|,0⟩,0))
      ≤ (2k+3) * (Φ_end - Φ_start) + 18*n`

  （`A' = 2k+3`, `B' = 18`。`|u|` に比例する項は残らない。）
-/

namespace PalPeg.GSVTapes

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 0. 右向きの反復移動（`GSTapes.leftN` の鏡） -/

/-- 現在の記号を書き戻しながら右へ `n` セル。 -/
def rightN (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => rightN blank (Tape.step blank tp tp.focus .right) n

theorem seq_rightN {blank : Fin sc} {w : List (Fin sc)} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (i : ℕ), Tape.SeqView blank tp w i →
      i + n < w.length → Tape.SeqView blank (rightN blank tp n) w (i + n) := by
  intro n
  induction n with
  | zero => intro tp i h _; simpa [rightN] using h
  | succ n ih =>
    intro tp i h hlt
    have h1 : Tape.SeqView blank (Tape.step blank tp tp.focus .right) w (i + 1) :=
      Tape.seq_move_right h (by omega)
    have h2 := ih _ (i + 1) h1 (by omega)
    rw [show i + 1 + n = i + (n + 1) from by omega] at h2
    exact h2

/-! ## 1. テープ配置と 1 セル動作 -/

/-- 検証器が追加で使う 2 本のテープ。 -/
structure VExt (sc : ℕ) where
  /-- 接頭辞テープ `startSym :: (u ++ [endSym])`、ヘッドは `checked + 1`。 -/
  U : TapeConfiguration sc
  /-- テキストの 2 本目のコピー、ヘッドは `pos - |u| + checked`。 -/
  Txt2 : TapeConfiguration sc

/-- 走査段の 3 本 ＋ 検証器の 2 本。 -/
abbrev VTapes (sc : ℕ) := GSTapes.TapesState sc × VExt sc

/-- 5 本のテープに対する 1 個のヘッド動作。`S` は走査段の動作をそのまま持ち上げる。
`U`/`X` は読んだ記号を書き戻して移動する（テープを書き換えない移動）。 -/
inductive VAct (sc : ℕ) where
  | S : GSTapes.Act sc → VAct sc
  | U : Move → VAct sc
  | X : Move → VAct sc

def vApplyAct (blank : Fin sc) (vt : VTapes sc) : VAct sc → VTapes sc
  | .S a => (GSTapes.applyAct blank vt.1 a, vt.2)
  | .U m => (vt.1, { vt.2 with U := Tape.step blank vt.2.U vt.2.U.focus m })
  | .X m => (vt.1, { vt.2 with Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus m })

def vApplyActs (blank : Fin sc) (l : List (VAct sc)) (vt : VTapes sc) : VTapes sc :=
  l.foldl (vApplyAct blank) vt

@[simp] theorem vApplyActs_nil (blank : Fin sc) (vt : VTapes sc) :
    vApplyActs blank [] vt = vt := rfl

@[simp] theorem vApplyActs_cons (blank : Fin sc) (a : VAct sc) (l : List (VAct sc))
    (vt : VTapes sc) :
    vApplyActs blank (a :: l) vt = vApplyActs blank l (vApplyAct blank vt a) := rfl

theorem vApplyActs_append (blank : Fin sc) (l₁ l₂ : List (VAct sc)) (vt : VTapes sc) :
    vApplyActs blank (l₁ ++ l₂) vt = vApplyActs blank l₂ (vApplyActs blank l₁ vt) := by
  simp [vApplyActs]

/-- 検証器 2 本だけへの作用（`S` は無視）。 -/
def vApplyExt (blank : Fin sc) (e : VExt sc) : VAct sc → VExt sc
  | .S _ => e
  | .U m => { e with U := Tape.step blank e.U e.U.focus m }
  | .X m => { e with Txt2 := Tape.step blank e.Txt2 e.Txt2.focus m }

def extActs (blank : Fin sc) (l : List (VAct sc)) (e : VExt sc) : VExt sc :=
  l.foldl (vApplyExt blank) e

@[simp] theorem extActs_nil (blank : Fin sc) (e : VExt sc) : extActs blank [] e = e := rfl

@[simp] theorem extActs_cons (blank : Fin sc) (a : VAct sc) (l : List (VAct sc))
    (e : VExt sc) : extActs blank (a :: l) e = extActs blank l (vApplyExt blank e a) := rfl

theorem extActs_append (blank : Fin sc) (l₁ l₂ : List (VAct sc)) (e : VExt sc) :
    extActs blank (l₁ ++ l₂) e = extActs blank l₂ (extActs blank l₁ e) := by
  simp [extActs]

/-- 検証器成分は `vApplyActs` でも `extActs` でも同じ。 -/
theorem vApplyActs_snd (blank : Fin sc) : ∀ (l : List (VAct sc)) (vt : VTapes sc),
    (vApplyActs blank l vt).2 = extActs blank l vt.2 := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
    intro vt
    rw [vApplyActs_cons, extActs_cons, ih]
    cases a <;> rfl

/-- 走査段の動作列の持ち上げ。 -/
theorem vApplyActs_map_S (blank : Fin sc) :
    ∀ (l : List (GSTapes.Act sc)) (vt : VTapes sc),
      vApplyActs blank (l.map VAct.S) vt = (GSTapes.applyActs blank l vt.1, vt.2) := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
    intro vt
    rw [List.map_cons, vApplyActs_cons, GSTapes.applyActs_cons]
    exact ih _

/-! ## 2. 検証器の動作列 -/

/-- 1 回の `vComp`：`read U` と `read Txt2` を比べ、等しくかつ `U` が `endSym` でなければ
両ヘッドを右へ 1、そうでなければ何もしない。 -/
def vcompActs (endSym : Fin sc) (e : VExt sc) : List (VAct sc) :=
  if Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2 then
    [VAct.U .right, VAct.X .right]
  else []

/-- `quota = 2`：`vComp` を 2 回（2 回目は 1 回目の結果の上で判定）。 -/
def vcomp2Acts (blank endSym : Fin sc) (e : VExt sc) : List (VAct sc) :=
  vcompActs endSym e ++ vcompActs endSym (extActs blank (vcompActs endSym e) e)

/-- ずらしの歩き直し：`U` を `c` 歩左（`checked := 0`）、`Txt2` を `|d - c|` 歩だけ移動。 -/
def walkActs (c d : ℕ) : List (VAct sc) :=
  List.replicate c (VAct.U (sc := sc) .left) ++
    (if c ≤ d then List.replicate (d - c) (VAct.X (sc := sc) .right)
      else List.replicate (c - d) (VAct.X (sc := sc) .left))

/-- ずらしの歩数。 -/
def walkLen (c d : ℕ) : ℕ := c + (if c ≤ d then d - c else c - d)

theorem walkLen_le (c d : ℕ) : walkLen c d ≤ 2 * c + d := by
  unfold walkLen; split_ifs <;> omega

/-- テープから読み取れる `checked`（`GSTapes.qOf` の鏡）。 -/
def cOf (e : VExt sc) : ℕ := e.U.left.length - 1

/-- テープとオラクルビットから読み取れるずらし幅（`gsShift` の鏡）。 -/
def vDelta (k : ℕ) (b : Bool) (ts : GSTapes.TapesState sc) : ℕ :=
  if b then GSTapes.p1Of ts else max 1 (ceilDiv (GSTapes.qOf ts) k)

/-- 検証器つきの一歩の動作列：走査段 → 検証器。 -/
def vprogram (blank endSym mark : Fin sc) (k : ℕ) (b : Bool) (vt : VTapes sc) :
    List (VAct sc) :=
  (GSTapes.program blank endSym mark k b vt.1).map VAct.S ++
    (if Tape.read vt.1.P ≠ endSym ∧ Tape.read vt.1.P = Tape.read vt.1.Txt then
        vcomp2Acts blank endSym vt.2
      else walkActs (cOf vt.2) (vDelta k b vt.1))

/-! ### 動作列の効果（検証器 2 本の射影） -/

theorem extActs_vcompActs_U (blank endSym : Fin sc) (e : VExt sc)
    (h : Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2) :
    (extActs blank (vcompActs endSym e) e).U = Tape.step blank e.U e.U.focus .right := by
  unfold vcompActs; rw [if_pos h]; rfl

theorem extActs_vcompActs_Txt2 (blank endSym : Fin sc) (e : VExt sc)
    (h : Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2) :
    (extActs blank (vcompActs endSym e) e).Txt2
      = Tape.step blank e.Txt2 e.Txt2.focus .right := by
  unfold vcompActs; rw [if_pos h]; rfl

theorem extActs_replicate_U (blank : Fin sc) : ∀ (n : ℕ) (e : VExt sc),
    extActs blank (List.replicate n (VAct.U (sc := sc) .left)) e
      = ⟨GSTapes.leftN blank e.U n, e.Txt2⟩ := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih => intro e; rw [List.replicate_succ, extActs_cons, ih]; rfl

theorem extActs_replicate_XR (blank : Fin sc) : ∀ (n : ℕ) (e : VExt sc),
    extActs blank (List.replicate n (VAct.X (sc := sc) .right)) e
      = ⟨e.U, rightN blank e.Txt2 n⟩ := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih => intro e; rw [List.replicate_succ, extActs_cons, ih]; rfl

theorem extActs_replicate_XL (blank : Fin sc) : ∀ (n : ℕ) (e : VExt sc),
    extActs blank (List.replicate n (VAct.X (sc := sc) .left)) e
      = ⟨e.U, GSTapes.leftN blank e.Txt2 n⟩ := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih => intro e; rw [List.replicate_succ, extActs_cons, ih]; rfl

theorem extActs_walk_U (blank : Fin sc) (c d : ℕ) (e : VExt sc) :
    (extActs blank (walkActs c d) e).U = GSTapes.leftN blank e.U c := by
  unfold walkActs
  rw [extActs_append, extActs_replicate_U]
  split_ifs with h
  · rw [extActs_replicate_XR]
  · rw [extActs_replicate_XL]

theorem extActs_walk_Txt2 (blank : Fin sc) (c d : ℕ) (e : VExt sc) :
    (extActs blank (walkActs c d) e).Txt2
      = if c ≤ d then rightN blank e.Txt2 (d - c)
        else GSTapes.leftN blank e.Txt2 (c - d) := by
  unfold walkActs
  rw [extActs_append, extActs_replicate_U]
  split_ifs with h
  · rw [extActs_replicate_XR]
  · rw [extActs_replicate_XL]

/-! ### 検証器の動作列は走査段のテープに触らない -/

theorem vApplyActs_replicate_U_fst (blank : Fin sc) (m : Move) :
    ∀ (n : ℕ) (vt : VTapes sc),
      (vApplyActs blank (List.replicate n (VAct.U (sc := sc) m)) vt).1 = vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs_cons]; exact ih _

theorem vApplyActs_replicate_X_fst (blank : Fin sc) (m : Move) :
    ∀ (n : ℕ) (vt : VTapes sc),
      (vApplyActs blank (List.replicate n (VAct.X (sc := sc) m)) vt).1 = vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs_cons]; exact ih _

theorem vApplyActs_walk_fst (blank : Fin sc) (c d : ℕ) (vt : VTapes sc) :
    (vApplyActs blank (walkActs c d) vt).1 = vt.1 := by
  unfold walkActs
  rw [vApplyActs_append]
  split_ifs with h
  · rw [vApplyActs_replicate_X_fst, vApplyActs_replicate_U_fst]
  · rw [vApplyActs_replicate_X_fst, vApplyActs_replicate_U_fst]

theorem vApplyActs_vcompActs_fst (blank endSym : Fin sc) (e : VExt sc) (vt : VTapes sc) :
    (vApplyActs blank (vcompActs endSym e) vt).1 = vt.1 := by
  unfold vcompActs; split_ifs <;> rfl

theorem vApplyActs_vcomp2Acts_fst (blank endSym : Fin sc) (e : VExt sc) (vt : VTapes sc) :
    (vApplyActs blank (vcomp2Acts blank endSym e) vt).1 = vt.1 := by
  unfold vcomp2Acts
  rw [vApplyActs_append, vApplyActs_vcompActs_fst, vApplyActs_vcompActs_fst]

/-! ## 3. 符号化 -/

/-- 5 本のテープが検証器つき状態 `z = (st, checked)` を符号化していること。 -/
structure VEncodes (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc)) (p₁ : ℕ)
    (vt : VTapes sc) (z : VState) : Prop where
  /-- 走査段の 3 本は `GSScanTapes` の符号化のまま。 -/
  scan : GSTapes.Encodes blank startSym endSym mark v Text p₁ vt.1 z.1
  /-- `U` は `startSym :: (u ++ [endSym])`、ヘッドは `checked + 1`。 -/
  pat : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (z.2 + 1)
  /-- `Txt2` はテキストの 2 本目、ヘッドは `pos - |u| + checked`。 -/
  txt2 : Tape.SeqView blank vt.2.Txt2 Text (z.1.pos - u.length + z.2)

section Reads

variable {blank startSym endSym : Fin sc} {u Text : List (Fin sc)} {e : VExt sc} {c : ℕ}

theorem read_U_lt (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hc : c < u.length) : u[c]? = some (Tape.read e.U) := by
  have h := hU.read_eq
  rw [List.getElem?_cons_succ, List.getElem?_append_left hc] at h
  exact h

theorem read_U_end (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hc : c = u.length) : Tape.read e.U = endSym := by
  have h := hU.read_eq
  rw [List.getElem?_cons_succ, hc,
    List.getElem?_append_right (Nat.le_refl u.length)] at h
  simp at h
  exact h.symm

theorem read_U_ne_end (hendu : endSym ∉ u)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hc : c < u.length) : Tape.read e.U ≠ endSym := by
  intro hcon
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 (read_U_lt hU hc)
  exact hendu (hcon ▸ h2 ▸ List.getElem_mem h1)

theorem cOf_eq (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1)) :
    cOf e = c := by
  have h := hU.left_eq
  have hlt := hU.lt
  simp only [List.length_cons, List.length_append] at hlt
  unfold cOf
  rw [h, List.length_reverse, List.length_take]
  simp only [List.length_cons, List.length_append]
  omega

/-- 検証器の比較分岐は、テープの読みと添字レベルの `vComp` の条件で一致する
（`GSTapes.advance_iff` の鏡）。 -/
theorem vcomp_iff (hendu : endSym ∉ u) {pos : ℕ}
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c)) (hc : c ≤ u.length) :
    (Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2) ↔
      (c < u.length ∧ Text[pos - u.length + c]? = u[c]?) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hne : c ≠ u.length := fun hcon => h1 (read_U_end hU hcon)
    refine ⟨by omega, ?_⟩
    rw [hX.read_eq, read_U_lt hU (by omega), h2]
  · rintro ⟨h1, h2⟩
    refine ⟨read_U_ne_end hendu hU h1, ?_⟩
    rw [hX.read_eq, read_U_lt hU h1] at h2
    exact (Option.some.inj h2).symm

end Reads

/-! ## 4. 検証器の動作列の実現 -/

section Ext

variable {blank startSym endSym : Fin sc} {u Text : List (Fin sc)} {e : VExt sc}
  {pos c d : ℕ}

/-- 1 回の `vComp` の実現。 -/
theorem vcompActs_spec (hendu : endSym ∉ u)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hroom : pos < Text.length) :
    Tape.SeqView blank (extActs blank (vcompActs endSym e) e).U
        (startSym :: (u ++ [endSym])) (vComp u Text pos c + 1) ∧
      Tape.SeqView blank (extActs blank (vcompActs endSym e) e).Txt2 Text
        (pos - u.length + vComp u Text pos c) := by
  by_cases hh : Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2
  · obtain ⟨hcl, hceq⟩ := (vcomp_iff hendu hU hX hc).1 hh
    have hv : vComp u Text pos c = c + 1 := by unfold vComp; rw [if_pos ⟨hcl, hceq⟩]
    rw [hv, extActs_vcompActs_U blank endSym e hh, extActs_vcompActs_Txt2 blank endSym e hh]
    constructor
    · refine Tape.seq_move_right hU ?_
      simp only [List.length_cons, List.length_append]
      omega
    · rw [show pos - u.length + (c + 1) = (pos - u.length + c) + 1 from by omega]
      exact Tape.seq_move_right hX (by omega)
  · have hv : vComp u Text pos c = c := by
      unfold vComp
      rw [if_neg (fun hcon => hh ((vcomp_iff hendu hU hX hc).2 hcon))]
    have he : extActs blank (vcompActs endSym e) e = e := by
      unfold vcompActs; rw [if_neg hh]; rfl
    rw [hv, he]
    exact ⟨hU, hX⟩

/-- `quota = 2` の実現：`checked` は `vComp` を 2 回適用した値になる。 -/
theorem vcomp2Acts_spec (hendu : endSym ∉ u)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hroom : pos < Text.length) :
    Tape.SeqView blank (extActs blank (vcomp2Acts blank endSym e) e).U
        (startSym :: (u ++ [endSym])) (vComp u Text pos (vComp u Text pos c) + 1) ∧
      Tape.SeqView blank (extActs blank (vcomp2Acts blank endSym e) e).Txt2 Text
        (pos - u.length + vComp u Text pos (vComp u Text pos c)) := by
  obtain ⟨h1U, h1X⟩ := vcompActs_spec hendu hU hX hc hpos hroom
  have h2 := vcompActs_spec (blank := blank) (startSym := startSym) hendu h1U h1X
    (vComp_le_length hc) hpos hroom
  rw [vcomp2Acts, extActs_append]
  exact h2

/-- ずらしの歩き直しの実現：`U` は添字 `1`（`checked = 0`）へ、`Txt2` は
新しい `pos + d - |u|` へ。 -/
theorem walkActs_spec
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c))
    (hpos : u.length ≤ pos) (hroom : pos + d < Text.length) :
    Tape.SeqView blank (extActs blank (walkActs c d) e).U
        (startSym :: (u ++ [endSym])) (0 + 1) ∧
      Tape.SeqView blank (extActs blank (walkActs c d) e).Txt2 Text
        (pos + d - u.length + 0) := by
  constructor
  · rw [extActs_walk_U]
    refine GSTapes.seq_leftN c e.U (0 + 1) ?_
    rw [show 0 + 1 + c = c + 1 from by omega]
    exact hU
  · rw [extActs_walk_Txt2]
    split_ifs with h
    · have ht := seq_rightN (d - c) e.Txt2 (pos - u.length + c) hX (by omega)
      rw [show pos - u.length + c + (d - c) = pos + d - u.length + 0 from by omega] at ht
      exact ht
    · refine GSTapes.seq_leftN (c - d) e.Txt2 (pos + d - u.length + 0) ?_
      rw [show pos + d - u.length + 0 + (c - d) = pos - u.length + c from by omega]
      exact hX

end Ext

/-! ## 5. 一歩の実現 -/

section Step

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {p₁ : ℕ}
  {vt : VTapes sc} {z : VState}

/-- ずらし枝では `checked := 0`。 -/
theorem vStep_shift {k p₁ r : ℕ}
    (h : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?)) :
    vStep u v k p₁ r Text z = (scanStep v k p₁ r Text z.1, 0) := by
  unfold vStep
  by_cases h1 : z.1.q = v.length
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (fun hc => h ⟨h1, hc⟩)]

/-- テープから読み取ったずらし幅は `gsShift`。 -/
theorem vDelta_eq {k r : ℕ} {b : Bool}
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt z)
    (hb : b = decide (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r)) :
    vDelta k b vt.1 = gsShift k p₁ r z.1.q := by
  unfold vDelta gsShift
  rcases Bool.eq_false_or_eq_true b with hbb | hbb
  · subst hbb
    have hcond : k * p₁ ≤ z.1.q ∧ z.1.q ≤ r := of_decide_eq_true hb.symm
    rw [if_pos rfl, if_pos hcond, GSTapes.p1Of_eq hE.scan]
  · subst hbb
    have hcond : ¬ (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r) := of_decide_eq_false hb.symm
    rw [if_neg (by simp), if_neg hcond, GSTapes.qOf_eq hE.scan]

/-- **主定理 1（実現）**：`vprogram` の動作列を適用すると、5 本のテープは `vStep` 後の
検証器つき状態を符号化する。 -/
theorem vencodes_step {k r : ℕ} {b : Bool} (hk : 0 < k)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hb : b = decide (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r))
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length) :
    VEncodes blank startSym endSym mark u v Text p₁
      (vApplyActs blank (vprogram blank endSym mark k b vt) vt)
      (vStep u v k p₁ r Text z) := by
  have hscan := GSTapes.encodes_step hk hend hE.scan hq hb hfit
  have hsplit : vApplyActs blank (vprogram blank endSym mark k b vt) vt
      = vApplyActs blank
          (if Tape.read vt.1.P ≠ endSym ∧ Tape.read vt.1.P = Tape.read vt.1.Txt then
              vcomp2Acts blank endSym vt.2
            else walkActs (cOf vt.2) (vDelta k b vt.1))
          (GSTapes.applyActs blank (GSTapes.program blank endSym mark k b vt.1) vt.1,
            vt.2) := by
    rw [vprogram, vApplyActs_append, vApplyActs_map_S]
  rw [hsplit]
  by_cases hadv : Tape.read vt.1.P ≠ endSym ∧ Tape.read vt.1.P = Tape.read vt.1.Txt
  · -- `v` の比較成功：`vComp` を 2 回
    rw [if_pos hadv]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff hend hE.scan hq).1 hadv
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv ⟨ha1, ha2⟩
    have hvs : vStep u v k p₁ r Text z
        = (scanStep v k p₁ r Text z.1,
            vComp u Text z.1.pos (vComp u Text z.1.pos z.2)) := by
      unfold vStep; rw [if_neg ha1, if_pos ha2]
    have hroom : z.1.pos < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    obtain ⟨hU2, hX2⟩ := vcomp2Acts_spec (blank := blank) (startSym := startSym)
      (pos := z.1.pos) hendu hE.pat hE.txt2 hc hpos hroom
    rw [hvs]
    refine ⟨?_, ?_, ?_⟩
    · rw [vApplyActs_vcomp2Acts_fst]
      exact hscan
    · rw [vApplyActs_snd]
      exact hU2
    · rw [vApplyActs_snd, hss]
      exact hX2
  · -- ずらし：`checked := 0` に戻して `Txt2` を張り直す
    rw [if_neg hadv]
    have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : vDelta k b vt.1 = gsShift k p₁ r z.1.q := vDelta_eq hE hb
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hroom : z.1.pos + gsShift k p₁ r z.1.q < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    obtain ⟨hU2, hX2⟩ := walkActs_spec (blank := blank) (startSym := startSym) (u := u)
      (Text := Text) (e := vt.2) (pos := z.1.pos) (c := z.2)
      (d := gsShift k p₁ r z.1.q) hE.pat hE.txt2 hpos hroom
    rw [vStep_shift hna, hd, hcc]
    refine ⟨?_, ?_, ?_⟩
    · rw [vApplyActs_walk_fst]
      exact hscan
    · rw [vApplyActs_snd]
      exact hU2
    · rw [vApplyActs_snd, hss]
      exact hX2

end Step

/-! ## 6. 費用 -/

section Cost

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {p₁ : ℕ}
  {vt : VTapes sc} {z : VState}

@[simp] theorem walkActs_length (c d : ℕ) :
    (walkActs (sc := sc) c d).length = walkLen c d := by
  unfold walkActs walkLen
  rw [List.length_append]
  split_ifs <;> simp

theorem vcompActs_length_le (endSym : Fin sc) (e : VExt sc) :
    (vcompActs endSym e).length ≤ 2 := by
  unfold vcompActs; split_ifs <;> simp

theorem vcomp2Acts_length_le (blank endSym : Fin sc) (e : VExt sc) :
    (vcomp2Acts blank endSym e).length ≤ 4 := by
  unfold vcomp2Acts
  rw [List.length_append]
  have h1 := vcompActs_length_le endSym e
  have h2 := vcompActs_length_le endSym (extActs blank (vcompActs endSym e) e)
  omega

theorem vprogram_length (blank endSym mark : Fin sc) (k : ℕ) (b : Bool) (vt : VTapes sc) :
    (vprogram blank endSym mark k b vt).length
      = (GSTapes.program blank endSym mark k b vt.1).length
        + (if Tape.read vt.1.P ≠ endSym ∧ Tape.read vt.1.P = Tape.read vt.1.Txt then
            (vcomp2Acts blank endSym vt.2).length
          else walkLen (cOf vt.2) (vDelta k b vt.1)) := by
  unfold vprogram
  rw [List.length_append, List.length_map]
  split_ifs with h
  · rfl
  · rw [walkActs_length]

/-! ### ずらしの歩数の明示的な上界 -/

/-- 周期ずらしの歩き直しは `≤ p₁ + |u|`。 -/
theorem walkLen_le_period {k p₁ r q c m : ℕ} (hcond : k * p₁ ≤ q ∧ q ≤ r) (hc : c ≤ m) :
    walkLen c (gsShift k p₁ r q) ≤ p₁ + 2 * m := by
  have hd : gsShift k p₁ r q = p₁ := by unfold gsShift; rw [if_pos hcond]
  have h := walkLen_le c (gsShift k p₁ r q)
  rw [hd] at h ⊢
  omega

/-- リセットずらしの歩き直しは `≤ q + 1 + |u|`。 -/
theorem walkLen_le_reset {k p₁ r q c m : ℕ} (hk : 0 < k)
    (hcond : ¬ (k * p₁ ≤ q ∧ q ≤ r)) (hc : c ≤ m) :
    walkLen c (gsShift k p₁ r q) ≤ q + 1 + 2 * m := by
  have hd : gsShift k p₁ r q = max 1 (ceilDiv q k) := by unfold gsShift; rw [if_neg hcond]
  have hce : ceilDiv q k ≤ q := GSTapes.ceilDiv_le_self hk
  have h := walkLen_le c (gsShift k p₁ r q)
  rw [hd] at h ⊢
  omega

/-- ずらし幅そのものはポテンシャルの増分で償却できる。 -/
theorem gsShift_le_dPhi {k p₁ r : ℕ} (hk : 0 < k) (st : ScanState) :
    gsShift k p₁ r st.q ≤
      Phi k (⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ : ScanState) - Phi k st := by
  unfold gsShift gsNextQ Phi
  split_ifs with hc
  · have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, k * p₁ = Y := ⟨_, rfl⟩
    have e1 : (k + 1) * (st.pos + p₁) = X + (Y + p₁) := by rw [← hX, ← hY]; ring
    have hpY : p₁ ≤ Y := by rw [← hY]; exact Nat.le_mul_of_pos_left p₁ hk
    rw [e1, hX, show X + (Y + p₁) + (st.q - p₁) - (X + st.q) = Y from by omega]
    omega
  · have hks : st.q ≤ k * max 1 (ceilDiv st.q k) :=
      le_trans (ceilDiv_bounds hk).1 (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right 1 _))
    obtain ⟨s, hs⟩ : ∃ s, max 1 (ceilDiv st.q k) = s := ⟨_, rfl⟩
    rw [hs] at hks ⊢
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, k * s = A := ⟨_, rfl⟩
    rw [hA] at hks
    have e1 : (k + 1) * (st.pos + s) = X + (A + s) := by rw [← hX, ← hA]; ring
    rw [e1, hX, show X + (A + s) + 0 - (X + st.q) = A + s - st.q from by omega]
    omega

/-- **主定理 2（費用）**：検証器つきの一歩の動作数は、走査段と同じポテンシャルで
償却される部分と、`|u|` に比例する部分に分かれる。`A = 2k+3`, `B = 12`, `C = 2`。 -/
theorem vprogram_cost {k r : ℕ} {b : Bool} (hk : 0 < k) (hend : endSym ∉ v)
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length)
    (hb : b = decide (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r)) :
    (vprogram blank endSym mark k b vt).length ≤
      (2 * k + 3) * (Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1) + 12 + 2 * u.length := by
  have hprog := GSTapes.program_cost (r := r) hk hend hE.scan hq hb
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD] at hprog ⊢
  have hmono : (2 * k + 3) * D = (2 * k + 2) * D + D := by ring
  rw [vprogram_length]
  split_ifs with hadv
  · have h4 := vcomp2Acts_length_le blank endSym vt.2
    omega
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : vDelta k b vt.1 = gsShift k p₁ r z.1.q := vDelta_eq hE hb
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hwalk : walkLen (cOf vt.2) (vDelta k b vt.1) ≤ 2 * z.2 + gsShift k p₁ r z.1.q := by
      rw [hd, hcc]; exact walkLen_le _ _
    have hsh : gsShift k p₁ r z.1.q ≤ D := by
      have h := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
      rw [← hss, hD] at h
      exact h
    omega

end Cost

/-!
## 8. 実行全体の費用：`2|u|` の項の償却（L1 を使わない）

1 歩の費用 `vprogram_cost` に現れる `2|u|` は、ずらしのときに `U` のヘッドを
`checked` 歩戻す分（と `Txt2` の張り直し）である。これは **`checked` が
「前回のずらし以降に成功した `v` の比較の 2 倍以下」** であること
（不変条件 `VCheckedInv : checked ≤ 2*q`）から、既に `Φ` の増分として
数え終わった比較に付け替えられる。

形式化はポテンシャル `Ψ(z) = 2 * checked` を使う（＝「まだ払っていない巻き戻し費用」）：

* 比較成功の一歩：`Φ` は `+1`、`checked` は `≤ +2` なので
  `cost + ΔΨ ≤ 2 + 4*2 = 10 ≤ (2k+3)*1 + 18`。
* ずらしの一歩：`Ψ` は `2*checked → 0` と減り、その減少がちょうど巻き戻し
  `walkLen checked δ ≤ 2*checked + δ` の `2*checked` を払う。残る `δ` は
  `gsShift_le_dPhi` で `Φ` の増分に吸収されるので
  `cost + ΔΨ ≤ (2k+2)*ΔΦ + 8 + δ ≤ (2k+3)*ΔΦ + 18`。

telescoping して `vrun_cost_le`：

`vRunCostIdx n z + 2*(vRunState n z).2 ≤ (2k+3)*(Φ_end - Φ_start) + 18*n + 2*z.2`

初期状態は `checked = 0` なので右端の項は消え、`|u|` に比例する項は
**まったく残らない**（`vrun_cost_le_of_start`）。`VCheckedInv` は、
ポテンシャルに載せた「借金」`2*checked ≤ 4*q ≤ 4*Φ` が常に
過去の比較で裏付けられていることを保証する（`checkedInv_debt_le`）。

テープ側の実行 `vRunCostTapes`（`vApplyActs` を `vStep` に沿って反復）は、
符号化が保たれる限り `vRunCostIdx` と**一致する**（`vRunCostTapes_eq`）ので、
同じ上界が実際の動作数に対して成り立つ（`vrun_tape_cost_le`,
`vrun_tape_cost_init`）。`A' = 2k+3`, `B' = 18`。
-/

section RunDefs

/-- 検証器つきの一歩のテープ動作数（添字レベルの式）。 -/
def vStepTapeCost (u v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) (z : VState) : ℕ :=
  GSTapes.stepCost v k p₁ r Text z.1 +
    (if z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]? then
        2 * (vComp u Text z.1.pos (vComp u Text z.1.pos z.2) - z.2)
      else walkLen z.2 (gsShift k p₁ r z.1.q))

/-- `n` 歩後の検証器つき状態。 -/
def vRunState (u v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) :
    ℕ → VState → VState
  | 0, z => z
  | n + 1, z => vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)

/-- `n` 歩の総動作数（添字レベル）。 -/
def vRunCostIdx (u v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) : ℕ → VState → ℕ
  | 0, _ => 0
  | n + 1, z =>
      vStepTapeCost u v k p₁ r Text z + vRunCostIdx u v k p₁ r Text n (vStep u v k p₁ r Text z)

/-- 毎ステップのオラクルビット。 -/
def vOracle (k p₁ r : ℕ) (st : ScanState) : Bool := decide (k * p₁ ≤ st.q ∧ st.q ≤ r)

/-- テープ側の実行：`vApplyActs` を `vStep` に沿って反復する。 -/
def vRunTapes (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes sc × VState → VTapes sc × VState
  | 0, s => s
  | n + 1, s =>
      vRunTapes blank endSym mark u v k p₁ r Text n
        (vApplyActs blank (vprogram blank endSym mark k (vOracle k p₁ r s.2.1) s.1) s.1,
          vStep u v k p₁ r Text s.2)

/-- テープ側の実行の総動作数。 -/
def vRunCostTapes (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes sc × VState → ℕ
  | 0, _ => 0
  | n + 1, s =>
      (vprogram blank endSym mark k (vOracle k p₁ r s.2.1) s.1).length +
        vRunCostTapes blank endSym mark u v k p₁ r Text n
          (vApplyActs blank (vprogram blank endSym mark k (vOracle k p₁ r s.2.1) s.1) s.1,
            vStep u v k p₁ r Text s.2)

/-- 最初の `n` 歩がすべてテキストの内側に収まること（符号化を保つための条件）。 -/
def VFits (v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) : ℕ → ScanState → Prop
  | 0, _ => True
  | n + 1, st =>
      (scanStep v k p₁ r Text st).pos + (scanStep v k p₁ r Text st).q < Text.length ∧
        VFits v k p₁ r Text n (scanStep v k p₁ r Text st)

/-- **不変条件**：`checked` は前回のずらし以降に成功した `v` の比較の 2 倍以下。
ずらしで `checked` も `q` も基準に戻るので、`checked ≤ 2*q` の形で表せる。 -/
def VCheckedInv (z : VState) : Prop := z.2 ≤ 2 * z.1.q

end RunDefs

/-! ### 不変条件 `checked ≤ 2*q` -/

section Inv

variable {k p₁ r : ℕ} {u v Text : List (Fin sc)} {z : VState}

theorem vStep_snd_adv (h : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :
    (vStep u v k p₁ r Text z).2 = vComp u Text z.1.pos (vComp u Text z.1.pos z.2) := by
  unfold vStep; rw [if_neg h.1, if_pos h.2]

theorem vStep_snd_shift (h : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?)) :
    (vStep u v k p₁ r Text z).2 = 0 := by rw [vStep_shift h]

/-- 一歩で不変条件は保たれる：比較成功なら `q` が `+1`、`checked` は `≤ +2`、
ずらしなら `checked := 0`。 -/
theorem vStep_checkedInv (h : VCheckedInv z) :
    VCheckedInv (vStep u v k p₁ r Text z) := by
  unfold VCheckedInv at h ⊢
  rw [vStep_fst]
  by_cases hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?
  · have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv hadv
    have h3 := vComp_le_succ u Text z.1.pos z.2
    have h4 := vComp_le_succ u Text z.1.pos (vComp u Text z.1.pos z.2)
    rw [vStep_snd_adv hadv, hss]
    show vComp u Text z.1.pos (vComp u Text z.1.pos z.2) ≤ 2 * (z.1.q + 1)
    omega
  · rw [vStep_snd_shift hadv]
    exact Nat.zero_le _

theorem vRunState_checkedInv (u v Text : List (Fin sc)) (k p₁ r : ℕ) :
    ∀ (n : ℕ) (z : VState), VCheckedInv z →
      VCheckedInv (vRunState u v k p₁ r Text n z) := by
  intro n
  induction n with
  | zero => intro z h; exact h
  | succ n ih => intro z h; exact ih _ (vStep_checkedInv h)

/-- 初期状態は不変条件を満たす。 -/
theorem checkedInv_init (pos : ℕ) : VCheckedInv ((⟨pos, 0⟩ : ScanState), 0) := by
  show (0 : ℕ) ≤ 2 * 0
  omega

/-- ポテンシャルに載せた「借金」は常に過去の比較（＝`Φ` の増分）で裏付けられている。 -/
theorem checkedInv_debt_le (k : ℕ) (h : VCheckedInv z) : 2 * z.2 ≤ 4 * Phi k z.1 := by
  unfold VCheckedInv at h
  have hq : z.1.q ≤ Phi k z.1 := by
    show z.1.q ≤ (k + 1) * z.1.pos + z.1.q
    omega
  omega

/-- `checked` は `|u|` を超えない。 -/
theorem vStep_checked_le (h : z.2 ≤ u.length) :
    (vStep u v k p₁ r Text z).2 ≤ u.length := by
  by_cases hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?
  · rw [vStep_snd_adv hadv]
    exact vComp_le_length (vComp_le_length h)
  · rw [vStep_snd_shift hadv]
    exact Nat.zero_le _

end Inv

/-! ### 一歩の費用の式（テープの動作数との一致） -/

section StepCostEq

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {p₁ : ℕ}
  {vt : VTapes sc} {z : VState} {e : VExt sc} {pos c : ℕ}

theorem vcompActs_length_eq (hendu : endSym ∉ u)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c)) (hc : c ≤ u.length) :
    (vcompActs endSym e).length = 2 * (vComp u Text pos c - c) := by
  by_cases hh : Tape.read e.U ≠ endSym ∧ Tape.read e.U = Tape.read e.Txt2
  · have hv : vComp u Text pos c = c + 1 := by
      unfold vComp; rw [if_pos ((vcomp_iff hendu hU hX hc).1 hh)]
    unfold vcompActs; rw [if_pos hh, hv]; simp
  · have hv : vComp u Text pos c = c := by
      unfold vComp
      rw [if_neg (fun hcon => hh ((vcomp_iff hendu hU hX hc).2 hcon))]
    unfold vcompActs; rw [if_neg hh, hv]; simp

theorem vcomp2Acts_length_eq (hendu : endSym ∉ u)
    (hU : Tape.SeqView blank e.U (startSym :: (u ++ [endSym])) (c + 1))
    (hX : Tape.SeqView blank e.Txt2 Text (pos - u.length + c))
    (hc : c ≤ u.length) (hpos : u.length ≤ pos) (hroom : pos < Text.length) :
    (vcomp2Acts blank endSym e).length
      = 2 * (vComp u Text pos (vComp u Text pos c) - c) := by
  obtain ⟨h1U, h1X⟩ := vcompActs_spec hendu hU hX hc hpos hroom
  have e1 := vcompActs_length_eq hendu hU hX hc
  have e2 := vcompActs_length_eq (blank := blank) (startSym := startSym) hendu h1U h1X
    (vComp_le_length hc)
  have hle1 : c ≤ vComp u Text pos c := le_vComp u Text pos c
  have hle2 : vComp u Text pos c ≤ vComp u Text pos (vComp u Text pos c) :=
    le_vComp u Text pos (vComp u Text pos c)
  unfold vcomp2Acts
  rw [List.length_append, e1, e2]
  omega

/-- **一歩の動作数の式**：テープ上の動作列の長さは `vStepTapeCost`。 -/
theorem vprogram_length_eq {k r : ℕ} {b : Bool} (hk : 0 < k) (hend : endSym ∉ v)
    (hendu : endSym ∉ u)
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hb : b = decide (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r))
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length) :
    (vprogram blank endSym mark k b vt).length = vStepTapeCost u v k p₁ r Text z := by
  rw [vprogram_length, GSTapes.program_length hk hend hE.scan hq hb]
  unfold vStepTapeCost
  by_cases hadv : Tape.read vt.1.P ≠ endSym ∧ Tape.read vt.1.P = Tape.read vt.1.Txt
  · have habs := (GSTapes.advance_iff hend hE.scan hq).1 hadv
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv habs
    have hroom : z.1.pos < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    rw [if_pos hadv, if_pos habs,
      vcomp2Acts_length_eq (startSym := startSym) hendu hE.pat hE.txt2 hc hpos hroom]
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff hend hE.scan hq).2 hcon)
    rw [if_neg hadv, if_neg hna, cOf_eq hE.pat, vDelta_eq hE hb]

end StepCostEq

/-! ### 一歩の償却（ポテンシャル `Ψ = 2*checked`） -/

section Amortized

variable {k p₁ r : ℕ} {u v Text : List (Fin sc)} {z : VState}

theorem phi_advance (k : ℕ) (st : ScanState) :
    Phi k (⟨st.pos, st.q + 1⟩ : ScanState) - Phi k st = 1 := by
  obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
  show (k + 1) * st.pos + (st.q + 1) - ((k + 1) * st.pos + st.q) = 1
  rw [hX]
  omega

/-- **一歩の償却不等式**：`Ψ = 2*checked` を含めた費用は `(2k+3)*ΔΦ + 18` 以下。 -/
theorem vStepTapeCost_amortized (hk : 0 < k) (u v Text : List (Fin sc)) (p₁ r : ℕ)
    (z : VState) :
    vStepTapeCost u v k p₁ r Text z + 2 * (vStep u v k p₁ r Text z).2 ≤
      (2 * k + 3) * (Phi k (vStep u v k p₁ r Text z).1 - Phi k z.1) + 18 + 2 * z.2 := by
  rw [vStep_fst]
  unfold vStepTapeCost
  by_cases hadv : z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?
  · have hsc : GSTapes.stepCost v k p₁ r Text z.1 = 2 := by
      unfold GSTapes.stepCost; rw [if_neg hadv.1, if_pos hadv.2]
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv hadv
    have h1 : z.2 ≤ vComp u Text z.1.pos z.2 := le_vComp u Text z.1.pos z.2
    have h2 : vComp u Text z.1.pos z.2 ≤ vComp u Text z.1.pos (vComp u Text z.1.pos z.2) :=
      le_vComp u Text z.1.pos (vComp u Text z.1.pos z.2)
    have h3 : vComp u Text z.1.pos z.2 ≤ z.2 + 1 := vComp_le_succ u Text z.1.pos z.2
    have h4 : vComp u Text z.1.pos (vComp u Text z.1.pos z.2)
        ≤ vComp u Text z.1.pos z.2 + 1 :=
      vComp_le_succ u Text z.1.pos (vComp u Text z.1.pos z.2)
    rw [if_pos hadv, hsc, vStep_snd_adv hadv, hss, phi_advance, Nat.mul_one]
    omega
  · have hsc : GSTapes.stepCost v k p₁ r Text z.1 = GSTapes.shiftCost k p₁ r z.1.q := by
      unfold GSTapes.stepCost
      by_cases h1 : z.1.q = v.length
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg (fun hcon => hadv ⟨h1, hcon⟩)]
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hadv
    have hsh := GSTapes.shiftCost_le (p₁ := p₁) (r := r) hk z.1
    have hgs := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
    have hw := walkLen_le z.2 (gsShift k p₁ r z.1.q)
    rw [if_neg hadv, hsc, vStep_snd_shift hadv, hss]
    obtain ⟨D, hD⟩ : ∃ D, Phi k (⟨z.1.pos + gsShift k p₁ r z.1.q,
        gsNextQ k p₁ r z.1.q⟩ : ScanState) - Phi k z.1 = D := ⟨_, rfl⟩
    rw [hD] at hsh hgs ⊢
    have hsplit : (2 * k + 3) * D = (2 * k + 2) * D + D := by ring
    omega

theorem phi_vStep_le (hk : 0 < k) (hp : 0 < p₁) (u v Text : List (Fin sc)) (z : VState) :
    Phi k z.1 ≤ Phi k (vStep u v k p₁ r Text z).1 := by
  rw [vStep_fst]
  exact le_of_lt (phi_step_lt (v := v) (T := Text) (p₁ := p₁) (r := r) hk hp z.1)

theorem phi_vRunState_le (hk : 0 < k) (hp : 0 < p₁) (u v Text : List (Fin sc)) :
    ∀ (n : ℕ) (z : VState), Phi k z.1 ≤ Phi k (vRunState u v k p₁ r Text n z).1 := by
  intro n
  induction n with
  | zero => intro z; exact Nat.le_refl _
  | succ n ih =>
    intro z
    exact le_trans (phi_vStep_le (r := r) hk hp u v Text z) (ih (vStep u v k p₁ r Text z))

/-- **実行全体の償却**：`Ψ = 2*checked` を込めた総費用は
`(2k+3)*(Φ_end - Φ_start) + 18*n + 2*checked_start` 以下。 -/
theorem vrun_cost_le (hk : 0 < k) (hp : 0 < p₁) (u v Text : List (Fin sc)) :
    ∀ (n : ℕ) (z : VState),
      vRunCostIdx u v k p₁ r Text n z + 2 * (vRunState u v k p₁ r Text n z).2 ≤
        (2 * k + 3) * (Phi k (vRunState u v k p₁ r Text n z).1 - Phi k z.1)
          + 18 * n + 2 * z.2 := by
  intro n
  induction n with
  | zero =>
    intro z
    show 0 + 2 * z.2 ≤ (2 * k + 3) * (Phi k z.1 - Phi k z.1) + 18 * 0 + 2 * z.2
    rw [Nat.sub_self, Nat.mul_zero]
  | succ n ih =>
    intro z
    have hstep := vStepTapeCost_amortized (r := r) hk u v Text p₁ z
    have hih := ih (vStep u v k p₁ r Text z)
    have hm1 := phi_vStep_le (r := r) hk hp u v Text z
    have hm2 := phi_vRunState_le (r := r) hk hp u v Text n (vStep u v k p₁ r Text z)
    obtain ⟨P0, hP0⟩ : ∃ P0, Phi k z.1 = P0 := ⟨_, rfl⟩
    obtain ⟨P1, hP1⟩ : ∃ P1, Phi k (vStep u v k p₁ r Text z).1 = P1 := ⟨_, rfl⟩
    obtain ⟨P2, hP2⟩ : ∃ P2,
        Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 = P2 := ⟨_, rfl⟩
    rw [hP0, hP1] at hstep
    rw [hP0] at hm1
    rw [hP1] at hm1 hih hm2
    rw [hP2] at hih hm2
    have hsum : (2 * k + 3) * (P2 - P1) + (2 * k + 3) * (P1 - P0)
        = (2 * k + 3) * (P2 - P0) := by
      rw [← Nat.mul_add, show P2 - P1 + (P1 - P0) = P2 - P0 from by omega]
    show vStepTapeCost u v k p₁ r Text z
        + vRunCostIdx u v k p₁ r Text n (vStep u v k p₁ r Text z)
        + 2 * (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).2 ≤
      (2 * k + 3)
          * (Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 - Phi k z.1)
        + 18 * (n + 1) + 2 * z.2
    rw [hP0, hP2]
    omega

/-- `checked = 0` から始めれば、`|u|` に比例する項は残らない。 -/
theorem vrun_cost_le_of_start (hk : 0 < k) (hp : 0 < p₁) (u v Text : List (Fin sc))
    (n : ℕ) (z : VState) (h0 : z.2 = 0) :
    vRunCostIdx u v k p₁ r Text n z ≤
      (2 * k + 3) * (Phi k (vRunState u v k p₁ r Text n z).1 - Phi k z.1) + 18 * n := by
  have h := vrun_cost_le (r := r) hk hp u v Text n z
  rw [h0] at h
  omega

end Amortized

/-! ### テープ側の実行との一致 -/

section RunTapes

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {p₁ : ℕ}

/-- テープ上で実際に実行した動作数は、添字レベルの `vRunCostIdx` と一致する。 -/
theorem vRunCostTapes_eq {k r : ℕ} (hk : 0 < k) (hend : endSym ∉ v) (hendu : endSym ∉ u) :
    ∀ (n : ℕ) (vt : VTapes sc) (z : VState),
      VEncodes blank startSym endSym mark u v Text p₁ vt z →
      z.1.q ≤ v.length → z.2 ≤ u.length → u.length ≤ z.1.pos →
      VFits v k p₁ r Text n z.1 →
      vRunCostTapes blank endSym mark u v k p₁ r Text n (vt, z)
        = vRunCostIdx u v k p₁ r Text n z := by
  intro n
  induction n with
  | zero => intro vt z _ _ _ _ _; rfl
  | succ n ih =>
    intro vt z hE hq hc hpos hfits
    obtain ⟨hfit, hfits'⟩ := hfits
    have hb : vOracle k p₁ r z.1 = decide (k * p₁ ≤ z.1.q ∧ z.1.q ≤ r) := rfl
    have hlen := vprogram_length_eq hk hend hendu hE hq hc hpos hb hfit
    have hE' := vencodes_step hk hend hendu hE hq hc hpos hb hfit
    have hrec := ih _ _ hE'
      (by rw [vStep_fst]; exact scanStep_q_le hq)
      (vStep_checked_le hc)
      (by rw [vStep_fst]; exact le_trans hpos (scanStep_pos_le v k p₁ r Text z.1))
      (by rw [vStep_fst]; exact hfits')
    show (vprogram blank endSym mark k (vOracle k p₁ r z.1) vt).length
        + vRunCostTapes blank endSym mark u v k p₁ r Text n
            (vApplyActs blank (vprogram blank endSym mark k (vOracle k p₁ r z.1) vt) vt,
              vStep u v k p₁ r Text z)
      = vStepTapeCost u v k p₁ r Text z
          + vRunCostIdx u v k p₁ r Text n (vStep u v k p₁ r Text z)
    rw [hlen, hrec]

/-- **主定理 3（実行全体の費用）**：テープ上の総動作数は
`(2k+3)*(Φ_end - Φ_start) + 18*n + 2*checked_start`。`|u|` に比例する項は無い。 -/
theorem vrun_tape_cost_le {k r : ℕ} (hk : 0 < k) (hp : 0 < p₁) (hend : endSym ∉ v)
    (hendu : endSym ∉ u) (n : ℕ) (vt : VTapes sc) (z : VState)
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfits : VFits v k p₁ r Text n z.1) :
    vRunCostTapes blank endSym mark u v k p₁ r Text n (vt, z) ≤
      (2 * k + 3) * (Phi k (vRunState u v k p₁ r Text n z).1 - Phi k z.1)
        + 18 * n + 2 * z.2 := by
  rw [vRunCostTapes_eq hk hend hendu n vt z hE hq hc hpos hfits]
  have h := vrun_cost_le (r := r) hk hp u v Text n z
  omega

/-- 初期状態 `(⟨|u|, 0⟩, 0)` からの実行：`|u|` に比例する項も定数項も残らない。 -/
theorem vrun_tape_cost_init {k r : ℕ} (hk : 0 < k) (hp : 0 < p₁) (hend : endSym ∉ v)
    (hendu : endSym ∉ u) (n : ℕ) (vt : VTapes sc)
    (hE : VEncodes blank startSym endSym mark u v Text p₁ vt
      ((⟨u.length, 0⟩ : ScanState), 0))
    (hfits : VFits v k p₁ r Text n (⟨u.length, 0⟩ : ScanState)) :
    vRunCostTapes blank endSym mark u v k p₁ r Text n (vt, ((⟨u.length, 0⟩ : ScanState), 0)) ≤
      (2 * k + 3)
          * (Phi k (vRunState u v k p₁ r Text n ((⟨u.length, 0⟩ : ScanState), 0)).1
              - Phi k (⟨u.length, 0⟩ : ScanState))
        + 18 * n := by
  have h := vrun_tape_cost_le (r := r) hk hp hend hendu n vt _ hE
    (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _) hfits
  simpa using h

end RunTapes

/-!
## 9. オラクル無しの層への移植 (`section NoOracle`)

`GSScanTapes` の `section NoOracle`（8 本テープ `TapesState' = Fin 8 → TapeConfiguration`、
オラクルビットを持たない `program'`）の上に、同じ検証器を積む。

* テープ配置：`VTapes' sc := GSTapes.TapesState' sc × VExt sc`。走査段の 8 本
  （`tP tT tC1 tC2 tAp tAn tRp tRn`）はそのまま、検証器の `U` / `Txt2` は
  §1 の `VExt` を**そのまま再利用**する。
* 動作型 `VAct'`：走査段の `GSTapes.Act'` を `S` で持ち上げ、`U` / `X` は前と同じ。
  検証器側の動作列（`vcomp2Acts` / `walkActs`）は `S` を含まないので、
  `liftAct : VAct sc → VAct' sc` で貼り替えるだけで、§2–§4 の仕様
  （`vcomp2Acts_spec` / `walkActs_spec`）をそのまま使える
  （`extActs'_map_liftAct`）。
* ずらし幅はオラクルではなく**カウンタのマーカ読み取り**で決まる
  （`vDelta'`, `GSTapes.period_iff'`）。したがって `vprogram'` にも
  `vRunCostTapes'` にも `Bool` は一切現れない。

定数：`vprogram_cost'` は `A'' = 8k+14`, `B'' = 12`, `C = 2`
（走査段の `A' = 8k+13`, `B' = 8` に、ずらし幅 `δ ≤ ΔΦ` の分の `+D` と
比較 `≤ 4` の分を足したもの）。実行全体では §8 と同じ `Ψ = 2*checked` の
償却で `|u|` の項が消えて `A'' = 8k+14`, `B''' = 18`。
-/

section NoOracle

/-- 走査段 8 本 ＋ 検証器 2 本。 -/
abbrev VTapes' (sc : ℕ) := GSTapes.TapesState' sc × VExt sc

/-- 10 本のテープに対する 1 動作。 -/
inductive VAct' (sc : ℕ) where
  | S : GSTapes.Act' sc → VAct' sc
  | U : Move → VAct' sc
  | X : Move → VAct' sc

def vApplyAct' (blank : Fin sc) (vt : VTapes' sc) : VAct' sc → VTapes' sc
  | .S a => (GSTapes.applyAct' blank vt.1 a, vt.2)
  | .U m => (vt.1, { vt.2 with U := Tape.step blank vt.2.U vt.2.U.focus m })
  | .X m => (vt.1, { vt.2 with Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus m })

def vApplyActs' (blank : Fin sc) (l : List (VAct' sc)) (vt : VTapes' sc) : VTapes' sc :=
  l.foldl (vApplyAct' blank) vt

@[simp] theorem vApplyActs'_nil (blank : Fin sc) (vt : VTapes' sc) :
    vApplyActs' blank [] vt = vt := rfl

@[simp] theorem vApplyActs'_cons (blank : Fin sc) (a : VAct' sc) (l : List (VAct' sc))
    (vt : VTapes' sc) :
    vApplyActs' blank (a :: l) vt = vApplyActs' blank l (vApplyAct' blank vt a) := rfl

theorem vApplyActs'_append (blank : Fin sc) (l₁ l₂ : List (VAct' sc)) (vt : VTapes' sc) :
    vApplyActs' blank (l₁ ++ l₂) vt = vApplyActs' blank l₂ (vApplyActs' blank l₁ vt) := by
  simp [vApplyActs']

def vApplyExt' (blank : Fin sc) (e : VExt sc) : VAct' sc → VExt sc
  | .S _ => e
  | .U m => { e with U := Tape.step blank e.U e.U.focus m }
  | .X m => { e with Txt2 := Tape.step blank e.Txt2 e.Txt2.focus m }

def extActs' (blank : Fin sc) (l : List (VAct' sc)) (e : VExt sc) : VExt sc :=
  l.foldl (vApplyExt' blank) e

@[simp] theorem extActs'_nil (blank : Fin sc) (e : VExt sc) : extActs' blank [] e = e := rfl

@[simp] theorem extActs'_cons (blank : Fin sc) (a : VAct' sc) (l : List (VAct' sc))
    (e : VExt sc) : extActs' blank (a :: l) e = extActs' blank l (vApplyExt' blank e a) := rfl

theorem vApplyActs'_snd (blank : Fin sc) : ∀ (l : List (VAct' sc)) (vt : VTapes' sc),
    (vApplyActs' blank l vt).2 = extActs' blank l vt.2 := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
    intro vt
    rw [vApplyActs'_cons, extActs'_cons, ih]
    cases a <;> rfl

theorem vApplyActs'_map_S (blank : Fin sc) :
    ∀ (l : List (GSTapes.Act' sc)) (vt : VTapes' sc),
      vApplyActs' blank (l.map VAct'.S) vt = (GSTapes.applyActs' blank l vt.1, vt.2) := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
    intro vt
    rw [List.map_cons, vApplyActs'_cons, GSTapes.applyActs'_cons]
    exact ih _

/-- 検証器の動作列を新しい動作型へ貼り替える（`S` は現れないのでダミーでよい。
ダミーとして選んだ `keep tP .stay` はテープを変えない）。 -/
def liftAct : VAct sc → VAct' sc
  | .S _ => .S (GSTapes.Act'.keep GSTapes.tP .stay)
  | .U m => .U m
  | .X m => .X m

theorem applyAct'_keep_stay_id (blank : Fin sc) (ts : GSTapes.TapesState' sc) (i : Fin 8) :
    GSTapes.applyAct' blank ts (GSTapes.Act'.keep i .stay) = ts := by
  show GSTapes.upd ts i (Tape.step blank (ts i) (ts i).focus .stay) = ts
  funext j
  by_cases h : j = i
  · subst h
    rw [GSTapes.upd_self]
    rfl
  · rw [GSTapes.upd_ne _ _ h]

/-- 貼り替えても検証器 2 本への作用は変わらない。 -/
theorem extActs'_map_liftAct (blank : Fin sc) :
    ∀ (l : List (VAct sc)) (e : VExt sc),
      extActs' blank (l.map liftAct) e = extActs blank l e := by
  intro l
  induction l with
  | nil => intro e; rfl
  | cons a l ih =>
    intro e
    rw [List.map_cons, extActs'_cons, extActs_cons,
      show vApplyExt' blank e (liftAct a) = vApplyExt blank e a from by cases a <;> rfl]
    exact ih _

/-- 貼り替えた検証器の動作列は走査段の 8 本を変えない。 -/
theorem vApplyActs'_map_liftAct_fst (blank : Fin sc) :
    ∀ (l : List (VAct sc)) (vt : VTapes' sc),
      (vApplyActs' blank (l.map liftAct) vt).1 = vt.1 := by
  intro l
  induction l with
  | nil => intro vt; rfl
  | cons a l ih =>
    intro vt
    rw [List.map_cons, vApplyActs'_cons, ih]
    cases a with
    | S x => exact applyAct'_keep_stay_id blank vt.1 GSTapes.tP
    | U m => rfl
    | X m => rfl

/-! ### 符号化とプログラム（オラクル無し） -/

/-- ずらし幅：オラクルではなく符号付きカウンタのマーカ読み取りで決まる。 -/
def vDelta' (blank mark : Fin sc) (k : ℕ) (ts : GSTapes.TapesState' sc) : ℕ :=
  if Tape.read (Tape.step blank (ts GSTapes.tAn) blank .left) = mark ∧
      Tape.read (Tape.step blank (ts GSTapes.tRn) blank .left) = mark then
    GSTapes.p1Of' ts
  else max 1 (ceilDiv (GSTapes.qOf' ts) k)

/-- 検証器側の動作列（`S` を含まない）。 -/
def vExtActs' (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct sc) :=
  if Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) then
    vcomp2Acts blank endSym vt.2
  else walkActs (cOf vt.2) (vDelta' blank mark k vt.1)

/-- **オラクル無しの一歩の動作列**：走査段 `program'` → 検証器。`Bool` は現れない。 -/
def vprogram' (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.program' blank endSym mark k vt.1).map VAct'.S ++
    (vExtActs' blank endSym mark k vt).map liftAct

/-- 10 本のテープが検証器つき状態を符号化していること（オラクル無し版）。 -/
structure VEncodes' (blank startSym endSym mark : Fin sc) (u v Text : List (Fin sc))
    (k p₁ r : ℕ) (vt : VTapes' sc) (z : VState) : Prop where
  scan : GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r vt.1 z.1
  pat : Tape.SeqView blank vt.2.U (startSym :: (u ++ [endSym])) (z.2 + 1)
  txt2 : Tape.SeqView blank vt.2.Txt2 Text (z.1.pos - u.length + z.2)

section StepNo

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VState}

theorem vDelta'_eq (hne : mark ≠ blank)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z) :
    vDelta' blank mark k vt.1 = gsShift k p₁ r z.1.q := by
  unfold vDelta' gsShift
  by_cases hc : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
      Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark
  · rw [if_pos hc, if_pos ((GSTapes.period_iff' hne hE.scan).1 hc), GSTapes.p1Of'_eq hE.scan]
  · rw [if_neg hc, if_neg (fun hcon => hc ((GSTapes.period_iff' hne hE.scan).2 hcon)),
      GSTapes.qOf'_eq hE.scan]

/-- **主定理 1'（実現、オラクル無し）**。 -/
theorem vencodes_step' (hk : 0 < k) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length) :
    VEncodes' blank startSym endSym mark u v Text k p₁ r
      (vApplyActs' blank (vprogram' blank endSym mark k vt) vt)
      (vStep u v k p₁ r Text z) := by
  have hscan := GSTapes.encodes_step' hk hne hend hE.scan hq hfit
  have hsplit : vApplyActs' blank (vprogram' blank endSym mark k vt) vt
      = vApplyActs' blank ((vExtActs' blank endSym mark k vt).map liftAct)
          (GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k vt.1) vt.1, vt.2) := by
    rw [vprogram', vApplyActs'_append, vApplyActs'_map_S]
  rw [hsplit]
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hE.scan hq).1 hadv
    have hss : scanStep v k p₁ r Text z.1 = (⟨z.1.pos, z.1.q + 1⟩ : ScanState) :=
      GSTapes.scanStep_adv ⟨ha1, ha2⟩
    have hvs : vStep u v k p₁ r Text z
        = (scanStep v k p₁ r Text z.1,
            vComp u Text z.1.pos (vComp u Text z.1.pos z.2)) := by
      unfold vStep; rw [if_neg ha1, if_pos ha2]
    have hroom : z.1.pos < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    have hext : vExtActs' blank endSym mark k vt = vcomp2Acts blank endSym vt.2 := by
      unfold vExtActs'; rw [if_pos hadv]
    obtain ⟨hU2, hX2⟩ := vcomp2Acts_spec (blank := blank) (startSym := startSym)
      (pos := z.1.pos) hendu hE.pat hE.txt2 hc hpos hroom
    rw [hvs, hext]
    refine ⟨?_, ?_, ?_⟩
    · rw [vApplyActs'_map_liftAct_fst]
      exact hscan
    · rw [vApplyActs'_snd, extActs'_map_liftAct]
      exact hU2
    · rw [vApplyActs'_snd, extActs'_map_liftAct, hss]
      exact hX2
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : vDelta' blank mark k vt.1 = gsShift k p₁ r z.1.q := vDelta'_eq hne hE
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hroom : z.1.pos + gsShift k p₁ r z.1.q < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    have hext : vExtActs' blank endSym mark k vt
        = walkActs (cOf vt.2) (vDelta' blank mark k vt.1) := by
      unfold vExtActs'; rw [if_neg hadv]
    obtain ⟨hU2, hX2⟩ := walkActs_spec (blank := blank) (startSym := startSym) (u := u)
      (Text := Text) (e := vt.2) (pos := z.1.pos) (c := z.2)
      (d := gsShift k p₁ r z.1.q) hE.pat hE.txt2 hpos hroom
    rw [vStep_shift hna, hext, hd, hcc]
    refine ⟨?_, ?_, ?_⟩
    · rw [vApplyActs'_map_liftAct_fst]
      exact hscan
    · rw [vApplyActs'_snd, extActs'_map_liftAct]
      exact hU2
    · rw [vApplyActs'_snd, extActs'_map_liftAct, hss]
      exact hX2

/-! ### 費用（オラクル無し） -/

theorem vprogram_length' (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc) :
    (vprogram' blank endSym mark k vt).length
      = (GSTapes.program' blank endSym mark k vt.1).length
        + (vExtActs' blank endSym mark k vt).length := by
  rw [vprogram', List.length_append, List.length_map, List.length_map]

/-- **主定理 2'（費用、オラクル無し）**：`A'' = 8k+14`, `B'' = 12`, `C = 2`。 -/
theorem vprogram_cost' (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) :
    (vprogram' blank endSym mark k vt).length ≤
      (8 * k + 14) * (Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1) + 12 + 2 * u.length := by
  have hp' := GSTapes.program_cost' (p₁ := p₁) (r := r) hk hne hend hE.scan hq
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD] at hp' ⊢
  have hsplitD : (8 * k + 14) * D = (8 * k + 13) * D + D := by ring
  rw [vprogram_length']
  unfold vExtActs'
  split_ifs with hadv
  · have h4 := vcomp2Acts_length_le blank endSym vt.2
    omega
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : vDelta' blank mark k vt.1 = gsShift k p₁ r z.1.q := vDelta'_eq hne hE
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hwalk : (walkActs (sc := sc) (cOf vt.2) (vDelta' blank mark k vt.1)).length
        ≤ 2 * z.2 + gsShift k p₁ r z.1.q := by
      rw [walkActs_length, hd, hcc]
      exact walkLen_le _ _
    have hsh : gsShift k p₁ r z.1.q ≤ D := by
      have h := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
      rw [← hss, hD] at h
      exact h
    omega

/-- 一歩の償却（`Ψ = 2*checked` 込み）：`A'' = 8k+14`, `B''' = 18`。 -/
theorem vprogram'_amortized (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) :
    (vprogram' blank endSym mark k vt).length + 2 * (vStep u v k p₁ r Text z).2 ≤
      (8 * k + 14) * (Phi k (vStep u v k p₁ r Text z).1 - Phi k z.1) + 18 + 2 * z.2 := by
  rw [vStep_fst]
  have hp' := GSTapes.program_cost' (p₁ := p₁) (r := r) hk hne hend hE.scan hq
  obtain ⟨D, hD⟩ : ∃ D, Phi k (scanStep v k p₁ r Text z.1) - Phi k z.1 = D := ⟨_, rfl⟩
  rw [hD] at hp' ⊢
  have hsplitD : (8 * k + 14) * D = (8 * k + 13) * D + D := by ring
  rw [vprogram_length']
  unfold vExtActs'
  split_ifs with hadv
  · obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hE.scan hq).1 hadv
    have hvs : (vStep u v k p₁ r Text z).2
        = vComp u Text z.1.pos (vComp u Text z.1.pos z.2) := vStep_snd_adv ⟨ha1, ha2⟩
    have h3 := vComp_le_succ u Text z.1.pos z.2
    have h4 := vComp_le_succ u Text z.1.pos (vComp u Text z.1.pos z.2)
    have h5 := vcomp2Acts_length_le blank endSym vt.2
    rw [hvs]
    omega
  · have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hd : vDelta' blank mark k vt.1 = gsShift k p₁ r z.1.q := vDelta'_eq hne hE
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hwalk : (walkActs (sc := sc) (cOf vt.2) (vDelta' blank mark k vt.1)).length
        ≤ 2 * z.2 + gsShift k p₁ r z.1.q := by
      rw [walkActs_length, hd, hcc]
      exact walkLen_le _ _
    have hsh : gsShift k p₁ r z.1.q ≤ D := by
      have h := gsShift_le_dPhi (p₁ := p₁) (r := r) hk z.1
      rw [← hss, hD] at h
      exact h
    have hvs : (vStep u v k p₁ r Text z).2 = 0 := vStep_snd_shift hna
    rw [hvs]
    omega

end StepNo

/-! ### 実行全体（オラクル無し） -/

/-- テープ側の実行（オラクル無し）。 -/
def vRunTapes' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes' sc × VState → VTapes' sc × VState
  | 0, s => s
  | n + 1, s =>
      vRunTapes' blank endSym mark u v k p₁ r Text n
        (vApplyActs' blank (vprogram' blank endSym mark k s.1) s.1,
          vStep u v k p₁ r Text s.2)

/-- その総動作数（オラクル無し）。 -/
def vRunCostTapes' (blank endSym mark : Fin sc) (u v : List (Fin sc)) (k p₁ r : ℕ)
    (Text : List (Fin sc)) : ℕ → VTapes' sc × VState → ℕ
  | 0, _ => 0
  | n + 1, s =>
      (vprogram' blank endSym mark k s.1).length +
        vRunCostTapes' blank endSym mark u v k p₁ r Text n
          (vApplyActs' blank (vprogram' blank endSym mark k s.1) s.1,
            vStep u v k p₁ r Text s.2)

section RunNo

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}

/-- **主定理 3'（実行全体、オラクル無し）**：`Ψ = 2*checked` 込みの総動作数は
`(8k+14)*(Φ_end - Φ_start) + 18*n + 2*checked_start` 以下。 -/
theorem vrun_tape_cost_le' (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) :
    ∀ (n : ℕ) (vt : VTapes' sc) (z : VState),
      VEncodes' blank startSym endSym mark u v Text k p₁ r vt z →
      z.1.q ≤ v.length → z.2 ≤ u.length → u.length ≤ z.1.pos →
      VFits v k p₁ r Text n z.1 →
      vRunCostTapes' blank endSym mark u v k p₁ r Text n (vt, z)
          + 2 * (vRunState u v k p₁ r Text n z).2 ≤
        (8 * k + 14) * (Phi k (vRunState u v k p₁ r Text n z).1 - Phi k z.1)
          + 18 * n + 2 * z.2 := by
  intro n
  induction n with
  | zero =>
    intro vt z _ _ _ _ _
    show 0 + 2 * z.2 ≤ (8 * k + 14) * (Phi k z.1 - Phi k z.1) + 18 * 0 + 2 * z.2
    rw [Nat.sub_self, Nat.mul_zero]
  | succ n ih =>
    intro vt z hE hq hc hpos hfits
    obtain ⟨hfit, hfits'⟩ := hfits
    have hE' := vencodes_step' hk hne hend hendu hE hq hc hpos hfit
    have hq' : (vStep u v k p₁ r Text z).1.q ≤ v.length := by
      rw [vStep_fst]; exact scanStep_q_le hq
    have hc' : (vStep u v k p₁ r Text z).2 ≤ u.length := vStep_checked_le hc
    have hpos' : u.length ≤ (vStep u v k p₁ r Text z).1.pos := by
      rw [vStep_fst]; exact le_trans hpos (scanStep_pos_le v k p₁ r Text z.1)
    have hfits'' : VFits v k p₁ r Text n (vStep u v k p₁ r Text z).1 := by
      rw [vStep_fst]; exact hfits'
    have hih := ih _ _ hE' hq' hc' hpos' hfits''
    have hstep := vprogram'_amortized hk hne hend hE hq
    have hm1 := phi_vStep_le (r := r) hk hp u v Text z
    have hm2 := phi_vRunState_le (r := r) hk hp u v Text n (vStep u v k p₁ r Text z)
    obtain ⟨P0, hP0⟩ : ∃ P0, Phi k z.1 = P0 := ⟨_, rfl⟩
    obtain ⟨P1, hP1⟩ : ∃ P1, Phi k (vStep u v k p₁ r Text z).1 = P1 := ⟨_, rfl⟩
    obtain ⟨P2, hP2⟩ : ∃ P2,
        Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 = P2 := ⟨_, rfl⟩
    rw [hP0, hP1] at hstep
    rw [hP0] at hm1
    rw [hP1] at hm1 hih hm2
    rw [hP2] at hih hm2
    have hsum : (8 * k + 14) * (P2 - P1) + (8 * k + 14) * (P1 - P0)
        = (8 * k + 14) * (P2 - P0) := by
      rw [← Nat.mul_add, show P2 - P1 + (P1 - P0) = P2 - P0 from by omega]
    show (vprogram' blank endSym mark k vt).length
        + vRunCostTapes' blank endSym mark u v k p₁ r Text n
            (vApplyActs' blank (vprogram' blank endSym mark k vt) vt,
              vStep u v k p₁ r Text z)
        + 2 * (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).2 ≤
      (8 * k + 14)
          * (Phi k (vRunState u v k p₁ r Text n (vStep u v k p₁ r Text z)).1 - Phi k z.1)
        + 18 * (n + 1) + 2 * z.2
    rw [hP0, hP2]
    omega

/-- **初期状態からの実行（オラクル無し）**：`|u|` に比例する項は残らない。
`A'' = 8k+14`, `B''' = 18`。 -/
theorem vrun_tape_cost_init' (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u) (n : ℕ) (vt : VTapes' sc)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt
      ((⟨u.length, 0⟩ : ScanState), 0))
    (hfits : VFits v k p₁ r Text n (⟨u.length, 0⟩ : ScanState)) :
    vRunCostTapes' blank endSym mark u v k p₁ r Text n
        (vt, ((⟨u.length, 0⟩ : ScanState), 0)) ≤
      (8 * k + 14)
          * (Phi k (vRunState u v k p₁ r Text n ((⟨u.length, 0⟩ : ScanState), 0)).1
              - Phi k (⟨u.length, 0⟩ : ScanState))
        + 18 * n := by
  have h := vrun_tape_cost_le' hk hp hne hend hendu n vt _ hE
    (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl _) hfits
  have h0 : (((⟨u.length, 0⟩ : ScanState), (0 : ℕ))).2 = 0 := rfl
  have h1 : (((⟨u.length, 0⟩ : ScanState), (0 : ℕ))).1 = (⟨u.length, 0⟩ : ScanState) := rfl
  rw [h0, h1] at h
  omega

end RunNo

end NoOracle

/-! ## 7. 小例 -/

section Examples

example : walkLen 3 7 = 3 + 4 := by decide
example : walkLen 7 3 = 7 + 4 := by decide
example : (walkActs (sc := 3) 3 7).length = walkLen 3 7 := by decide
example : (walkActs (sc := 3) 7 3).length = walkLen 7 3 := by decide

end Examples

end PalPeg.GSVTapes
