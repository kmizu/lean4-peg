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

  （`A = 2k+3`, `B = 12`, `C = 2`）。`(k-1)|u| < |x|`（L1）による全体の償却は
  ここでは扱わず、1 歩あたりの費用を明示するに留める。
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

/-! ## 7. 小例 -/

section Examples

example : walkLen 3 7 = 3 + 4 := by decide
example : walkLen 7 3 = 7 + 4 := by decide
example : (walkActs (sc := 3) 3 7).length = walkLen 3 7 := by decide
example : (walkActs (sc := 3) 7 3).length = walkLen 7 3 := by decide

end Examples

end PalPeg.GSVTapes
