import PalPeg.GSVerifierTapes

/-!
# 検証器局所の「相乗り」ずらし部分プログラム (`GSVerifierFused`)

`PalPeg.GSVerifierTapes` §9（`walkActs` は有限制御では実現できない）で述べたとおり、
`Txt2` の残りの移動 `gsShift` 分は、`Txt2` 自身の内容からは読み取れない。実現するには
**走査段のずらしループ（`GSScanTapes.perDown` / `resDown2` の各周回）に `Txt2` の
1 歩を相乗りさせる**しかない。

このファイルは `GSScanTapes` を変更せず、その上に「検証器局所」のコピー
`perDownX` / `perLoop1X`（周期ずらし枝）と `resDown1X` / `resDown2X` / `resLoopX`
（リセットずらし枝）を追加する。それぞれ元のテープ 8 本への効果は元の
`perDown` / `resDown1` / `resDown2` と完全に同じで、そのうえで `Txt2` を

* `perDownX`：**毎周回** 1 歩右へ（周期ずらしでは `perLoop1` は `p₁ = gsShift` 回
  ちょうど回るので、これで `Txt2` は `gsShift` 歩動く）。
* `resDown1X`：`T` を止める周回でだけ 1 歩右へ、`resDown2X`（`T` を動かす周回）では
  動かさない。`gsShift = max 1 (ceilDiv q k)` は `T` が**動く**回数（`moves`）ではなく
  **止まる**回数（`stays`）に一致する（`moves_zero` と `stays_add_moves` から
  `stays k n 0 = ceilDiv n k`）ので、これで `Txt2` も `gsShift` と同じ量だけ動く。

進める（相乗りさせる）ことで、`U` の巻き戻し（`GSVProg.uWalkProg`、既存）と合わせて、
のちに `walkActs` 全体を有限制御で置き換える土台になる。

本ファイルでは **テープレベルの意味論**（`VTapes'` への効果）だけを扱う。有限制御
プログラム化（`Prog`）は別ファイルで行う。
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace PalPeg.GSVTapes

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 1. 周期ずらし枝：`perDownX` / `perLoop1X` -/

section PerFused

variable {blank mark : Fin sc}

/-- `perDown` に `Txt2` の 1 歩（右）を相乗りさせたもの。 -/
def perDownX (blank mark : Fin sc) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.perDown blank mark vt.1).map VAct'.S ++ [VAct'.X .right]

/-- `perLoop1` の相乗り版：`n` 周回すると `Txt2` はちょうど `n` 歩右へ動く。 -/
def perLoop1X (blank mark : Fin sc) : ℕ → VTapes' sc → List (VAct' sc)
  | 0, _ => []
  | n + 1, vt =>
      perDownX blank mark vt ++
        perLoop1X blank mark n (vApplyActs' blank (perDownX blank mark vt) vt)

/-- `map VAct'.S l ++ [VAct'.X m]` を 1 個の走査段作用 ＋ `Txt2` の 1 歩へ分解する。 -/
theorem vApplyActs'_mapS_append_X (blank : Fin sc) (l : List (GSTapes.Act' sc)) (m : Move)
    (vt : VTapes' sc) :
    vApplyActs' blank (l.map VAct'.S ++ [VAct'.X m]) vt
      = (GSTapes.applyActs' blank l vt.1,
          { vt.2 with Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus m }) := by
  rw [vApplyActs'_append, vApplyActs'_map_S]
  rfl

/-- **`perDownX` の実現**：走査段 8 本への効果は `perDown` と同じ、
`U` は変わらず、`Txt2` はちょうど 1 歩右へ。 -/
theorem perDownX_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {vt : VTapes' sc} {qq cc dd m r i : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1))
    (h1 : Tape.CounterView' blank mark (vt.1 GSTapes.tC1) (cc + 1))
    (h2 : Tape.CounterView' blank mark (vt.1 GSTapes.tC2) dd)
    (hQ : GSTapes.CQuad blank mark vt.1 m r qq)
    (hX : Tape.SeqView blank vt.2.Txt2 Text i) (hroom : i + 1 < Text.length) :
    Tape.SeqView blank ((vApplyActs' blank (perDownX blank mark vt) vt).1 GSTapes.tP) w
        (qq - 1 + 1) ∧
      Tape.CounterView' blank mark
        ((vApplyActs' blank (perDownX blank mark vt) vt).1 GSTapes.tC1) cc ∧
      Tape.CounterView' blank mark
        ((vApplyActs' blank (perDownX blank mark vt) vt).1 GSTapes.tC2) (dd + 1) ∧
      GSTapes.CQuad blank mark (vApplyActs' blank (perDownX blank mark vt) vt).1 m r (qq - 1) ∧
      (vApplyActs' blank (perDownX blank mark vt) vt).1 GSTapes.tT = vt.1 GSTapes.tT ∧
      (vApplyActs' blank (perDownX blank mark vt) vt).2.U = vt.2.U ∧
      Tape.SeqView blank (vApplyActs' blank (perDownX blank mark vt) vt).2.Txt2 Text (i + 1) := by
  obtain ⟨hP', h1', h2', hQ', hT'⟩ := GSTapes.perDown_spec hne hqq hP h1 h2 hQ
  unfold perDownX
  rw [vApplyActs'_mapS_append_X]
  exact ⟨hP', h1', h2', hQ', hT', rfl, Tape.seq_move_right hX hroom⟩

/-- **`perLoop1X` の実現**：走査段 8 本への効果は `perLoop1` と同じ（`n` 周）、
`U` は変わらず、`Txt2` はちょうど `n` 歩右へ。 -/
theorem perLoop1X_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)} :
    ∀ (n : ℕ) (vt : VTapes' sc) (qq cc dd m r i : ℕ), n ≤ qq → n ≤ cc →
      Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1) →
      Tape.CounterView' blank mark (vt.1 GSTapes.tC1) cc →
      Tape.CounterView' blank mark (vt.1 GSTapes.tC2) dd →
      GSTapes.CQuad blank mark vt.1 m r qq →
      Tape.SeqView blank vt.2.Txt2 Text i → i + n < Text.length →
      Tape.SeqView blank ((vApplyActs' blank (perLoop1X blank mark n vt) vt).1 GSTapes.tP) w
          (qq - n + 1) ∧
        Tape.CounterView' blank mark
          ((vApplyActs' blank (perLoop1X blank mark n vt) vt).1 GSTapes.tC1) (cc - n) ∧
        Tape.CounterView' blank mark
          ((vApplyActs' blank (perLoop1X blank mark n vt) vt).1 GSTapes.tC2) (dd + n) ∧
        GSTapes.CQuad blank mark (vApplyActs' blank (perLoop1X blank mark n vt) vt).1 m r
          (qq - n) ∧
        (vApplyActs' blank (perLoop1X blank mark n vt) vt).1 GSTapes.tT = vt.1 GSTapes.tT ∧
        (vApplyActs' blank (perLoop1X blank mark n vt) vt).2.U = vt.2.U ∧
        Tape.SeqView blank (vApplyActs' blank (perLoop1X blank mark n vt) vt).2.Txt2 Text
          (i + n) := by
  intro n
  induction n with
  | zero =>
      intro vt qq cc dd m r i _ _ hP h1 h2 hQ hX _
      exact ⟨hP, h1, h2, hQ, rfl, rfl, by simpa [perLoop1X] using hX⟩
  | succ n ih =>
      intro vt qq cc dd m r i hnq hnc hP h1 h2 hQ hX hroom
      obtain ⟨c', rfl⟩ : ∃ c', cc = c' + 1 := ⟨cc - 1, by omega⟩
      obtain ⟨hP', h1', h2', hQ', hT', hU', hX'⟩ :=
        perDownX_spec (blank := blank) (mark := mark) hne (by omega) hP h1 h2 hQ hX (by omega)
      have := ih (vApplyActs' blank (perDownX blank mark vt) vt) (qq - 1) c' (dd + 1) m r
        (i + 1) (by omega) (by omega) hP' h1' h2' hQ' hX' (by omega)
      show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      rw [perLoop1X, vApplyActs'_append]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
      · rw [show c' + 1 - (n + 1) = c' - n from by omega]; exact this.2.1
      · rw [show dd + (n + 1) = dd + 1 + n from by omega]; exact this.2.2.1
      · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.2.1
      · rw [this.2.2.2.2.1, hT']
      · rw [this.2.2.2.2.2.1, hU']
      · rw [show i + (n + 1) = i + 1 + n from by omega]; exact this.2.2.2.2.2.2

/-- `perDownX` の動作数は `perDown` に `+1`（`Txt2` の 1 歩）：`≤ 11`。 -/
theorem perDownX_length_le (blank mark : Fin sc) (vt : VTapes' sc) :
    (perDownX blank mark vt).length ≤ 11 := by
  unfold perDownX
  rw [List.length_append, List.length_map]
  have h1 : (GSTapes.perDown blank mark vt.1).length ≤ 10 := by
    unfold GSTapes.perDown GSTapes.perPre
    rw [List.length_append]
    have := GSTapes.qDecActs_length_le blank mark vt.1
    simp only [List.length_cons, List.length_nil]
    omega
  simp only [List.length_cons, List.length_nil]
  omega

/-- `perLoop1X` の動作数は `perLoop1` に `n` 回分の `+1`（`Txt2`）：`≤ 11*n`。 -/
theorem perLoop1X_length_le (blank mark : Fin sc) :
    ∀ (n : ℕ) (vt : VTapes' sc), (perLoop1X blank mark n vt).length ≤ 11 * n := by
  intro n
  induction n with
  | zero => intro vt; simp [perLoop1X]
  | succ n ih =>
      intro vt
      rw [perLoop1X, List.length_append]
      have h1 := perDownX_length_le blank mark vt
      have h2 := ih (vApplyActs' blank (perDownX blank mark vt) vt)
      omega

end PerFused

/-! ## 2. リセットずらし枝：`resDown1X` / `resDown2X` / `resLoopX` -/

section ResFused

/-- `resDown1`（`T` を止める周、位相 `0`）に `Txt2` の 1 歩（右）を相乗りさせたもの。
**注意**：`gsShift = max 1 (ceilDiv q k)` は `T` が動く回数（`moves`）ではなく
`T` が**止まる**回数（`stays`）に一致する（`moves_zero : moves k n 0 = n - ceilDiv n k`
と `stays_add_moves` から `stays k n 0 = ceilDiv n k`）。したがって `Txt2` は
`resDown1` 側（`T` 停止）に相乗りさせる。 -/
def resDown1X (blank mark : Fin sc) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.resDown1 blank mark vt.1).map VAct'.S ++ [VAct'.X .right]

/-- `resDown2`（`T` を動かす周）はそのまま。`Txt2` は動かさない。 -/
def resDown2X (blank mark : Fin sc) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.resDown2 blank mark vt.1).map VAct'.S

/-- `resLoop` の相乗り版：位相 `c`（`mod k`）に従い `resDown1X` / `resDown2X` を選ぶ。 -/
def resLoopX (blank mark : Fin sc) (k : ℕ) : ℕ → ℕ → VTapes' sc → List (VAct' sc)
  | 0, _, _ => []
  | n + 1, 0, vt =>
      resDown1X blank mark vt ++
        resLoopX blank mark k n (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt)
  | n + 1, c + 1, vt =>
      resDown2X blank mark vt ++
        resLoopX blank mark k n c (vApplyActs' blank (resDown2X blank mark vt) vt)

/-- **`resDown1X` の実現**：走査段 8 本への効果は `resDown1` と同じ、
`U` は変わらず、`Txt2` はちょうど 1 歩右へ。 -/
theorem resDown1X_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {vt : VTapes' sc} {qq m r i : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1))
    (hQ : GSTapes.CQuad blank mark vt.1 m r qq)
    (hX : Tape.SeqView blank vt.2.Txt2 Text i) (hroom : i + 1 < Text.length) :
    Tape.SeqView blank ((vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tP) w
        (qq - 1 + 1) ∧
      GSTapes.CQuad blank mark (vApplyActs' blank (resDown1X blank mark vt) vt).1 m r (qq - 1) ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tT = vt.1 GSTapes.tT ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tC1 = vt.1 GSTapes.tC1 ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tC2 = vt.1 GSTapes.tC2 ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).2.U = vt.2.U ∧
      Tape.SeqView blank (vApplyActs' blank (resDown1X blank mark vt) vt).2.Txt2 Text
        (i + 1) := by
  obtain ⟨hP', hQ', hT', h1', h2'⟩ := GSTapes.resDown1_spec hne hqq hP hQ
  unfold resDown1X
  rw [vApplyActs'_mapS_append_X]
  exact ⟨hP', hQ', hT', h1', h2', rfl, Tape.seq_move_right hX hroom⟩

/-- **`resDown2X` の実現**：走査段 8 本への効果は `resDown2` と同じ、
`U` も `Txt2` も変わらない。 -/
theorem resDown2X_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {vt : VTapes' sc} {qq ii m r i : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1))
    (hT : Tape.SeqView blank (vt.1 GSTapes.tT) Text (ii + 1))
    (hQ : GSTapes.CQuad blank mark vt.1 m r qq)
    (hX : Tape.SeqView blank vt.2.Txt2 Text i) :
    Tape.SeqView blank ((vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tP) w
        (qq - 1 + 1) ∧
      Tape.SeqView blank ((vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tT) Text
        ii ∧
      GSTapes.CQuad blank mark (vApplyActs' blank (resDown2X blank mark vt) vt).1 m r (qq - 1) ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tC1 = vt.1 GSTapes.tC1 ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tC2 = vt.1 GSTapes.tC2 ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).2.U = vt.2.U ∧
      Tape.SeqView blank (vApplyActs' blank (resDown2X blank mark vt) vt).2.Txt2 Text i := by
  obtain ⟨hP', hT', hQ', h1', h2'⟩ := GSTapes.resDown2_spec hne hqq hP hT hQ
  unfold resDown2X
  rw [vApplyActs'_map_S]
  exact ⟨hP', hT', hQ', h1', h2', rfl, hX⟩

/-- **`resLoopX` の実現**：走査段 8 本（`P`, `T`, `C1`, `C2`）への効果は `resLoop`
と同じ、`U` は変わらず、`Txt2` はちょうど `stays k n c`（`resLoop` が `T` を**止める**
回数、すなわち `moves_zero`/`stays_add_moves` によりリセットずらしの
`gsShift = max 1 (ceilDiv q k)` に一致する量）歩だけ右へ。 -/
theorem resLoopX_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    (k : ℕ) :
    ∀ (n c : ℕ) (vt : VTapes' sc) (qq ii m r i : ℕ), n ≤ qq →
      Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1) →
      Tape.SeqView blank (vt.1 GSTapes.tT) Text (ii + GSTapes.moves k n c) →
      GSTapes.CQuad blank mark vt.1 m r qq →
      Tape.SeqView blank vt.2.Txt2 Text i → i + GSTapes.stays k n c < Text.length →
      Tape.SeqView blank ((vApplyActs' blank (resLoopX blank mark k n c vt) vt).1 GSTapes.tP)
          w (qq - n + 1) ∧
        Tape.SeqView blank ((vApplyActs' blank (resLoopX blank mark k n c vt) vt).1 GSTapes.tT)
          Text ii ∧
        GSTapes.CQuad blank mark (vApplyActs' blank (resLoopX blank mark k n c vt) vt).1 m r
          (qq - n) ∧
        (vApplyActs' blank (resLoopX blank mark k n c vt) vt).1 GSTapes.tC1
          = vt.1 GSTapes.tC1 ∧
        (vApplyActs' blank (resLoopX blank mark k n c vt) vt).1 GSTapes.tC2
          = vt.1 GSTapes.tC2 ∧
        (vApplyActs' blank (resLoopX blank mark k n c vt) vt).2.U = vt.2.U ∧
        Tape.SeqView blank (vApplyActs' blank (resLoopX blank mark k n c vt) vt).2.Txt2 Text
          (i + GSTapes.stays k n c) := by
  intro n
  induction n with
  | zero =>
      intro c vt qq ii m r i _ hP hT hQ hX _
      refine ⟨hP, by simpa [GSTapes.moves, resLoopX] using hT, hQ, rfl, rfl, rfl, ?_⟩
      simpa [GSTapes.stays, resLoopX] using hX
  | succ n ih =>
      intro c vt qq ii m r i hnq hP hT hQ hX hroom
      cases c with
      | zero =>
          have hms : GSTapes.stays k (n + 1) 0 = GSTapes.stays k n (k - 1) + 1 := rfl
          have hroom1 : i + 1 < Text.length := by rw [hms] at hroom; omega
          obtain ⟨hP', hQ', hT', h1', h2', hU', hX'⟩ :=
            resDown1X_spec (blank := blank) (mark := mark) hne (by omega) hP hQ hX hroom1
          have hmv : GSTapes.moves k (n + 1) 0 = GSTapes.moves k n (k - 1) := rfl
          have hTT : Tape.SeqView blank
              ((vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tT)
              Text (ii + GSTapes.moves k n (k - 1)) := by
            rw [hT']; rw [hmv] at hT; exact hT
          have hroom2 : i + 1 + GSTapes.stays k n (k - 1) < Text.length := by
            rw [hms] at hroom; omega
          have := ih (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt) (qq - 1) ii m r
            (i + 1) (by omega) hP' hTT hQ' hX' hroom2
          rw [resLoopX, vApplyActs'_append]
          refine ⟨?_, this.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
          · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
          · rw [this.2.2.2.1, h1']
          · rw [this.2.2.2.2.1, h2']
          · rw [this.2.2.2.2.2.1, hU']
          · rw [hms, show i + (GSTapes.stays k n (k - 1) + 1) = i + 1 + GSTapes.stays k n (k - 1)
              from by omega]
            exact this.2.2.2.2.2.2
      | succ c =>
          have hms : GSTapes.stays k (n + 1) (c + 1) = GSTapes.stays k n c := rfl
          have hmv : GSTapes.moves k (n + 1) (c + 1) = GSTapes.moves k n c + 1 := rfl
          have hT1 : Tape.SeqView blank (vt.1 GSTapes.tT) Text ((ii + GSTapes.moves k n c) + 1) :=
            by rw [show ii + GSTapes.moves k n c + 1 = ii + GSTapes.moves k (n + 1) (c + 1) from
              by rw [hmv]; omega]; exact hT
          have hroom' : i + GSTapes.stays k n c < Text.length := by rw [← hms]; exact hroom
          obtain ⟨hP', hT', hQ', h1', h2', hU', hX'⟩ :=
            resDown2X_spec (blank := blank) (mark := mark) hne (by omega) hP hT1 hQ hX
          have := ih c (vApplyActs' blank (resDown2X blank mark vt) vt) (qq - 1) ii m r i
            (by omega) hP' hT' hQ' hX' hroom'
          rw [resLoopX, vApplyActs'_append]
          refine ⟨?_, this.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
          · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
          · rw [this.2.2.2.1, h1']
          · rw [this.2.2.2.2.1, h2']
          · rw [this.2.2.2.2.2.1, hU']
          · rw [hms]; exact this.2.2.2.2.2.2

/-- `resDown1X` の動作数は `resDown1` に `+1`（`Txt2` の 1 歩）：`≤ 9`。 -/
theorem resDown1X_length_le (blank mark : Fin sc) (vt : VTapes' sc) :
    (resDown1X blank mark vt).length ≤ 9 := by
  unfold resDown1X
  rw [List.length_append, List.length_map]
  unfold GSTapes.resDown1
  rw [List.length_append]
  have := GSTapes.qDecActs_length_le blank mark vt.1
  simp only [List.length_cons, List.length_nil]
  omega

/-- `resDown2X` の動作数：`resDown2` と同じ、`≤ 8`。 -/
theorem resDown2X_length_le (blank mark : Fin sc) (vt : VTapes' sc) :
    (resDown2X blank mark vt).length ≤ 8 := by
  unfold resDown2X
  rw [List.length_map]
  unfold GSTapes.resDown2
  rw [List.length_append]
  have := GSTapes.qDecActs_length_le blank mark vt.1
  simp only [List.length_cons, List.length_nil]
  omega

/-- `resLoopX` の動作数は `resLoop` に `n` 回分の `+1`（`Txt2`）：`≤ 9*n`。 -/
theorem resLoopX_length_le (blank mark : Fin sc) (k : ℕ) :
    ∀ (n c : ℕ) (vt : VTapes' sc), (resLoopX blank mark k n c vt).length ≤ 9 * n := by
  intro n
  induction n with
  | zero => intro c vt; simp [resLoopX]
  | succ n ih =>
      intro c vt
      cases c with
      | zero =>
          rw [resLoopX, List.length_append]
          have h1 := resDown1X_length_le blank mark vt
          have h2 := ih (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt)
          omega
      | succ c =>
          rw [resLoopX, List.length_append]
          have h1 := resDown2X_length_le blank mark vt
          have h2 := ih c (vApplyActs' blank (resDown2X blank mark vt) vt)
          omega

end ResFused

/-! ## 3. 構造的な補題（`.1` と `.2.U` は不変条件なしに決まる） -/

section Structural

theorem perDownX_fst (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (perDownX blank mark vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.perDown blank mark vt.1) vt.1 := by
  unfold perDownX; rw [vApplyActs'_mapS_append_X]

theorem perDownX_U (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (perDownX blank mark vt) vt).2.U = vt.2.U := by
  unfold perDownX; rw [vApplyActs'_mapS_append_X]

theorem perLoop1X_fst (blank mark : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (perLoop1X blank mark n vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.perLoop1 blank mark n vt.1) vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih =>
      intro vt
      rw [perLoop1X, vApplyActs'_append]
      have h2 := ih (vApplyActs' blank (perDownX blank mark vt) vt)
      rw [perDownX_fst] at h2
      rw [h2, GSTapes.perLoop1, GSTapes.applyActs'_append]

theorem perLoop1X_U (blank mark : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (perLoop1X blank mark n vt) vt).2.U = vt.2.U := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih =>
      intro vt
      rw [perLoop1X, vApplyActs'_append, ih (vApplyActs' blank (perDownX blank mark vt) vt),
        perDownX_U]

theorem resDown1X_fst (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (resDown1X blank mark vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.resDown1 blank mark vt.1) vt.1 := by
  unfold resDown1X; rw [vApplyActs'_mapS_append_X]

theorem resDown1X_U (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (resDown1X blank mark vt) vt).2.U = vt.2.U := by
  unfold resDown1X; rw [vApplyActs'_mapS_append_X]

theorem resDown2X_fst (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (resDown2X blank mark vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.resDown2 blank mark vt.1) vt.1 := by
  unfold resDown2X; rw [vApplyActs'_map_S]

theorem resDown2X_U (blank mark : Fin sc) (vt : VTapes' sc) :
    (vApplyActs' blank (resDown2X blank mark vt) vt).2.U = vt.2.U := by
  unfold resDown2X; rw [vApplyActs'_map_S]

theorem resLoopX_fst (blank mark : Fin sc) (k : ℕ) : ∀ (n c : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (resLoopX blank mark k n c vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.resLoop blank mark k n c vt.1) vt.1 := by
  intro n
  induction n with
  | zero => intro c vt; rfl
  | succ n ih =>
      intro c vt
      cases c with
      | zero =>
          rw [resLoopX, vApplyActs'_append]
          have h2 := ih (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt)
          rw [resDown1X_fst] at h2
          rw [h2, GSTapes.resLoop, GSTapes.applyActs'_append]
      | succ c =>
          rw [resLoopX, vApplyActs'_append]
          have h2 := ih c (vApplyActs' blank (resDown2X blank mark vt) vt)
          rw [resDown2X_fst] at h2
          rw [h2, GSTapes.resLoop, GSTapes.applyActs'_append]

theorem resLoopX_U (blank mark : Fin sc) (k : ℕ) : ∀ (n c : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (resLoopX blank mark k n c vt) vt).2.U = vt.2.U := by
  intro n
  induction n with
  | zero => intro c vt; rfl
  | succ n ih =>
      intro c vt
      cases c with
      | zero =>
          rw [resLoopX, vApplyActs'_append,
            ih (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt), resDown1X_U]
      | succ c =>
          rw [resLoopX, vApplyActs'_append,
            ih c (vApplyActs' blank (resDown2X blank mark vt) vt), resDown2X_U]

/-- 走査段の動作（`Act' sc` を `S` で持ち上げたもの）は `Txt2` を動かさない。 -/
theorem vApplyActs'_mapS_Txt2 (blank : Fin sc) (l : List (GSTapes.Act' sc)) (vt : VTapes' sc) :
    (vApplyActs' blank (l.map VAct'.S) vt).2.Txt2 = vt.2.Txt2 := by
  rw [vApplyActs'_map_S]

end Structural

/-! ## 4. `U` の巻き戻しと `Txt2` の残差補正 -/

section UWalk

/-- `U` の巻き戻し：`startSym` を読むまで左、そして 1 右
（`GSVProg.uWalkProg_exec` と動作数は同じ `c + 2`）。**この一覧は `U` しか動かさない。** -/
def uWalk (vt : VTapes' sc) : List (VAct' sc) :=
  List.replicate (cOf vt.2 + 1) (VAct'.U (sc := sc) .left) ++ [VAct'.U (sc := sc) .right]

/-- `Txt2` 側の残差補正：`checked` 分だけ左へ。

**設計メモ（コーディネータへの報告事項）**：`vprogram'` の `walkActs c d` は
`U` を `c` 歩戻すのとは独立に、`Txt2` を `|d − c|` 歩動かして
`pos - |u| + c → pos + d - |u| + 0` を実現する（`walkActs_spec`）。相乗りループ
（`perLoop1X` / `resLoopX`）は `Txt2` に `+d`（`d = gsShift`）だけを足すので、
`VEncodes'.txt2`（目標 `pos + d - |u| + 0`）に届けるには **`c` 分の左移動が
別途必要**（`(pos - |u| + c + d) - c = pos + d - |u|`）。`uWalk` 自体は指示どおり
`U` のみを動かす一覧のままとし、この残差補正は別の一覧 `txt2Rewind` として独立に
追加した（`checked` は `U` の左移動回数と同じ量なので、これも `cOf vt.2` から
直接計算できる——`Prog` 化する段では `U` の巻き戻しループにこの `X` の 1 歩を
相乗りさせればよい）。 -/
def txt2Rewind (vt : VTapes' sc) : List (VAct' sc) :=
  List.replicate (cOf vt.2) (VAct'.X (sc := sc) .left)

theorem vApplyActs'_replicate_U_fst (blank : Fin sc) (m : Move) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.U (sc := sc) m)) vt).1 = vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

theorem vApplyActs'_replicate_X_fst (blank : Fin sc) (m : Move) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.X (sc := sc) m)) vt).1 = vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

theorem vApplyActs'_replicate_U_Txt2 (blank : Fin sc) (m : Move) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.U (sc := sc) m)) vt).2.Txt2 = vt.2.Txt2 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

theorem vApplyActs'_replicate_X_U (blank : Fin sc) (m : Move) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.X (sc := sc) m)) vt).2.U = vt.2.U := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

theorem vApplyActs'_replicate_U_left_eq (blank : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.U (sc := sc) .left)) vt).2.U
      = GSTapes.leftN blank vt.2.U n := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

theorem vApplyActs'_replicate_X_left_eq (blank : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (List.replicate n (VAct'.X (sc := sc) .left)) vt).2.Txt2
      = GSTapes.leftN blank vt.2.Txt2 n := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih => intro vt; rw [List.replicate_succ, vApplyActs'_cons]; exact ih _

/-- `uWalk vt0` の動作数（`cOf vt0.2 + 2`）は `vt0` から決まるが、これは
どんな状態 `vt'` に適用してもよい（`Prod` の 2 つ目の成分の `U` フィールドだけが
その効果に関わる）。以下は `vt0 ≠ vt'` の場合も込みで一般に成り立つ形にしておく。 -/
theorem uWalk_fst (blank : Fin sc) (vt0 vt' : VTapes' sc) :
    (vApplyActs' blank (uWalk vt0) vt').1 = vt'.1 := by
  unfold uWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right]
      (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt')).1
      = (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt').1 from rfl]
  exact vApplyActs'_replicate_U_fst blank .left _ vt'

theorem uWalk_Txt2 (blank : Fin sc) (vt0 vt' : VTapes' sc) :
    (vApplyActs' blank (uWalk vt0) vt').2.Txt2 = vt'.2.Txt2 := by
  unfold uWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right]
      (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt')).2.Txt2
      = (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt').2.Txt2 from rfl]
  exact vApplyActs'_replicate_U_Txt2 blank .left _ vt'

/-- **`uWalk` の実現**：`U` は `startSym :: (u ++ [endSym])` 上で添字 `checked + 1`
から `0 + 1` へ。`vt0.2.U = vt'.2.U`（すなわち `cOf vt0.2 = cOf vt'.2`）であれば、
`uWalk vt0` を `vt'` へ適用した効果は `uWalk vt'` を `vt'` へ適用したときと同じになる。 -/
theorem uWalk_U {blank startSym endSym : Fin sc} {u : List (Fin sc)} {vt0 vt' : VTapes' sc}
    {c : ℕ} (hUeq : vt'.2.U = vt0.2.U)
    (hU : Tape.SeqView blank vt'.2.U (startSym :: (u ++ [endSym])) (c + 1)) :
    Tape.SeqView blank (vApplyActs' blank (uWalk vt0) vt').2.U
      (startSym :: (u ++ [endSym])) (0 + 1) := by
  have hc' : cOf vt'.2 = c := cOf_eq hU
  have hc : cOf vt0.2 = c := by
    rw [show cOf vt0.2 = cOf vt'.2 from by unfold cOf; rw [hUeq]]
    exact hc'
  unfold uWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right]
      (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt')).2.U
      = Tape.step blank
          (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt').2.U
          (vApplyActs' blank (List.replicate (cOf vt0.2 + 1) (VAct'.U .left)) vt').2.U.focus
          .right from rfl]
  rw [vApplyActs'_replicate_U_left_eq, hc]
  refine Tape.seq_move_right (GSTapes.seq_leftN (c + 1) vt'.2.U 0 ?_) ?_
  · rw [show 0 + (c + 1) = c + 1 from by omega]; exact hU
  · simp only [List.length_cons, List.length_append]; omega

theorem txt2Rewind_fst (blank : Fin sc) (vt0 vt' : VTapes' sc) :
    (vApplyActs' blank (txt2Rewind vt0) vt').1 = vt'.1 :=
  vApplyActs'_replicate_X_fst blank .left _ vt'

theorem txt2Rewind_U (blank : Fin sc) (vt0 vt' : VTapes' sc) :
    (vApplyActs' blank (txt2Rewind vt0) vt').2.U = vt'.2.U :=
  vApplyActs'_replicate_X_U blank .left _ vt'

/-- **`txt2Rewind` の実現**：`Txt2` を `cOf vt0.2` 歩左へ。 -/
theorem txt2Rewind_Txt2 {blank : Fin sc} {Text : List (Fin sc)} {vt0 vt' : VTapes' sc} {i c : ℕ}
    (hc : cOf vt0.2 = c) (hX : Tape.SeqView blank vt'.2.Txt2 Text (i + c)) :
    Tape.SeqView blank (vApplyActs' blank (txt2Rewind vt0) vt').2.Txt2 Text i := by
  unfold txt2Rewind
  rw [vApplyActs'_replicate_X_left_eq, hc]
  exact GSTapes.seq_leftN c vt'.2.Txt2 i hX

/-! ### `uxWalk`：`U` の巻き戻しに `Txt2` を相乗りさせた融合版

`uWalk ++ txt2Rewind` は「`U` だけ `c+2` 歩」＋「`Txt2` だけ `c` 歩」という
**別々の**動作列だった。有限制御では `U` の検索ループ（`startSym` を読むまで）が
そのループ回数 `c+1` を暗黙に持っているので、そこへ `Txt2` の 1 歩を相乗りさせれば
`Txt2` を数えずに動かせる。`uxWalk` は「`(U .left, X .left)` を `c+1` 回、
続けて `(U .right, X .right)` を 1 回」——動作数はちょうど `2*(c+1)+2 = 2c+4`。
最終的な `Txt2` の値は `uWalk ++ txt2Rewind` と同じ（`-(c+1)+1 = -c` で相殺）。 -/

/-- `(U .left, X .left)` を `n` 回。 -/
def uxWalkLoop : ℕ → List (VAct' sc)
  | 0 => []
  | n + 1 => [VAct'.U (sc := sc) .left, VAct'.X (sc := sc) .left] ++ uxWalkLoop n

/-- `uxWalkLoop (checked+1)` に続けて `(U .right, X .right)`。 -/
def uxWalk (vt : VTapes' sc) : List (VAct' sc) :=
  uxWalkLoop (cOf vt.2 + 1) ++ [VAct'.U (sc := sc) .right, VAct'.X (sc := sc) .right]

theorem uxWalkLoop_fst (blank : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (uxWalkLoop n) vt).1 = vt.1 := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih =>
      intro vt
      rw [uxWalkLoop, vApplyActs'_append]
      rw [show vApplyActs' blank
          [VAct'.U (sc := sc) .left, VAct'.X (sc := sc) .left] vt
          = (vt.1, ({ vt.2 with
              U := Tape.step blank vt.2.U vt.2.U.focus .left,
              Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus .left } : VExt sc)) from rfl]
      exact ih _

theorem uxWalkLoop_U (blank : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (uxWalkLoop n) vt).2.U = GSTapes.leftN blank vt.2.U n := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih =>
      intro vt
      rw [uxWalkLoop, vApplyActs'_append]
      rw [show vApplyActs' blank
          [VAct'.U (sc := sc) .left, VAct'.X (sc := sc) .left] vt
          = (vt.1, ({ vt.2 with
              U := Tape.step blank vt.2.U vt.2.U.focus .left,
              Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus .left } : VExt sc)) from rfl]
      exact ih _

theorem uxWalkLoop_Txt2 (blank : Fin sc) : ∀ (n : ℕ) (vt : VTapes' sc),
    (vApplyActs' blank (uxWalkLoop n) vt).2.Txt2 = GSTapes.leftN blank vt.2.Txt2 n := by
  intro n
  induction n with
  | zero => intro vt; rfl
  | succ n ih =>
      intro vt
      rw [uxWalkLoop, vApplyActs'_append]
      rw [show vApplyActs' blank
          [VAct'.U (sc := sc) .left, VAct'.X (sc := sc) .left] vt
          = (vt.1, ({ vt.2 with
              U := Tape.step blank vt.2.U vt.2.U.focus .left,
              Txt2 := Tape.step blank vt.2.Txt2 vt.2.Txt2.focus .left } : VExt sc)) from rfl]
      exact ih _

theorem uxWalk_fst (blank : Fin sc) (vt0 vt' : VTapes' sc) :
    (vApplyActs' blank (uxWalk vt0) vt').1 = vt'.1 := by
  unfold uxWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right, VAct'.X (sc := sc) .right]
      (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt')).1
      = (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt').1 from rfl]
  exact uxWalkLoop_fst blank _ vt'

/-- **`uxWalk` の `U` 側の実現**：`startSym` を読む位置（添字 `0`）まで戻り、
それから 1 右で添字 `1`（`checked = 0`）へ。 -/
theorem uxWalk_U {blank startSym endSym : Fin sc} {u : List (Fin sc)} {vt0 vt' : VTapes' sc}
    {c : ℕ} (hUeq : vt'.2.U = vt0.2.U)
    (hU : Tape.SeqView blank vt'.2.U (startSym :: (u ++ [endSym])) (c + 1)) :
    Tape.SeqView blank (vApplyActs' blank (uxWalk vt0) vt').2.U
      (startSym :: (u ++ [endSym])) (0 + 1) := by
  have hc' : cOf vt'.2 = c := cOf_eq hU
  have hc : cOf vt0.2 = c := by
    rw [show cOf vt0.2 = cOf vt'.2 from by unfold cOf; rw [hUeq]]
    exact hc'
  unfold uxWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right, VAct'.X (sc := sc) .right]
      (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt')).2.U
      = Tape.step blank
          (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt').2.U
          (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt').2.U.focus .right from rfl]
  rw [uxWalkLoop_U, hc]
  refine Tape.seq_move_right (GSTapes.seq_leftN (c + 1) vt'.2.U 0 ?_) ?_
  · rw [show 0 + (c + 1) = c + 1 from by omega]; exact hU
  · simp only [List.length_cons, List.length_append]; omega

/-- **`uxWalk` の `Txt2` 側の実現**：`checked` 分だけ左へ（正味 `-(c+1)+1 = -c`、
`uWalk ++ txt2Rewind` と同じ値）。`vt0.2.U` から読める `c := cOf vt0.2` を用いる。 -/
theorem uxWalk_Txt2 {blank : Fin sc} {Text : List (Fin sc)} {vt0 vt' : VTapes' sc} {c i : ℕ}
    (hc : cOf vt0.2 = c) (hi : 1 ≤ i) (hroom : i < Text.length)
    (hX : Tape.SeqView blank vt'.2.Txt2 Text (i - 1 + (c + 1))) :
    Tape.SeqView blank (vApplyActs' blank (uxWalk vt0) vt').2.Txt2 Text i := by
  unfold uxWalk
  rw [vApplyActs'_append]
  rw [show (vApplyActs' blank [VAct'.U (sc := sc) .right, VAct'.X (sc := sc) .right]
      (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt')).2.Txt2
      = Tape.step blank
          (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt').2.Txt2
          (vApplyActs' blank (uxWalkLoop (cOf vt0.2 + 1)) vt').2.Txt2.focus .right from rfl]
  rw [uxWalkLoop_Txt2, hc]
  have hstep := GSTapes.seq_leftN (c + 1) vt'.2.Txt2 (i - 1) hX
  have := Tape.seq_move_right hstep (by omega)
  rwa [show i - 1 + 1 = i from by omega] at this

theorem uxWalkLoop_length : ∀ (n : ℕ), (uxWalkLoop (sc := sc) n).length = 2 * n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => unfold uxWalkLoop; rw [List.length_append, ih]; simp; omega

/-- `uxWalk` の動作数は `2*(checked+1)+2 = 2*checked+4`。 -/
theorem uxWalk_length (vt : VTapes' sc) : (uxWalk vt).length = 2 * cOf vt.2 + 4 := by
  unfold uxWalk
  rw [List.length_append, uxWalkLoop_length]
  simp
  omega

end UWalk

/-! ## 5. `vprogramX`：ずらし枝を相乗りループ＋巻き戻しへ置き換えた一歩の動作列 -/

section VProgX

/-- 周期ずらし枝の相乗り版 `perProgram`。 -/
def perProgramX (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  perLoop1X blank mark n vt ++
    (GSTapes.probeActs blank GSTapes.tC1).map VAct'.S ++
    (GSTapes.perUp blank n).map VAct'.S ++
    (GSTapes.probeActs blank GSTapes.tC2).map VAct'.S

/-- リセットずらし枝の相乗り版 `resProgram`。`q = 0`（`gsShift = 1`）のときは、
元の `resProgram` が追加する `T` の 1 歩（`Act'.keep tT .right`）と対にして、
`Txt2` の 1 歩も追加する。 -/
def resProgramX (blank mark : Fin sc) (k q : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  resLoopX blank mark k q 0 vt ++
    (VAct'.S (GSTapes.Act'.keep GSTapes.tP .left) ::
      VAct'.S (GSTapes.Act'.keep GSTapes.tP .right) ::
      (if q = 0 then [VAct'.S (GSTapes.Act'.keep GSTapes.tT .right), VAct'.X .right]
        else []))

/-- **オラクル無しの一歩の動作列（ずらし枝を有限制御向けに再構成したもの）**。
比較枝は `vprogram'` と同一。ずらし枝は「相乗りさせた走査ループ
（`perLoop1X` / `resLoopX`）＋ `U` の巻き戻し（`uWalk`）＋ `Txt2` の残差補正
（`txt2Rewind`）」に置き換える。 -/
def vprogramX (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc) : List (VAct' sc) :=
  if Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT) then
    (GSTapes.advActs blank mark vt.1).map VAct'.S ++ (vcomp2Acts blank endSym vt.2).map liftAct
  else
    (GSTapes.probeActs blank GSTapes.tAn).map VAct'.S ++
      (GSTapes.probeActs blank GSTapes.tRn).map VAct'.S ++
      (if Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark then
        perProgramX blank mark (GSTapes.p1Of' vt.1) vt
      else
        resProgramX blank mark k (GSTapes.qOf' vt.1) vt) ++
      uxWalk vt

theorem perProgramX_fst (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (perProgramX blank mark n vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.perProgram blank mark n vt.1) vt.1 := by
  unfold perProgramX GSTapes.perProgram
  rw [vApplyActs'_append, vApplyActs'_append, vApplyActs'_append,
    GSTapes.applyActs'_append, GSTapes.applyActs'_append, GSTapes.applyActs'_append,
    vApplyActs'_map_S, vApplyActs'_map_S, vApplyActs'_map_S, perLoop1X_fst]

theorem perProgramX_U (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (perProgramX blank mark n vt) vt).2.U = vt.2.U := by
  unfold perProgramX
  rw [vApplyActs'_append, vApplyActs'_append, vApplyActs'_append,
    vApplyActs'_map_S, vApplyActs'_map_S, vApplyActs'_map_S, perLoop1X_U]

theorem resProgramX_fst (blank mark : Fin sc) (k q : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (resProgramX blank mark k q vt) vt).1
      = GSTapes.applyActs' blank (GSTapes.resProgram blank mark k q vt.1) vt.1 := by
  unfold resProgramX GSTapes.resProgram
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    rw [if_pos rfl, if_pos rfl, vApplyActs'_append, GSTapes.applyActs'_append]
    have hstep : (vApplyActs' blank
        (VAct'.S (GSTapes.Act'.keep GSTapes.tP .left) ::
          VAct'.S (GSTapes.Act'.keep GSTapes.tP .right) ::
          [VAct'.S (GSTapes.Act'.keep GSTapes.tT .right), VAct'.X .right])
        (vApplyActs' blank (resLoopX blank mark k 0 0 vt) vt)).1
        = GSTapes.applyActs' blank
            [GSTapes.Act'.keep GSTapes.tP .left, GSTapes.Act'.keep GSTapes.tP .right,
              GSTapes.Act'.keep GSTapes.tT .right]
            (vApplyActs' blank (resLoopX blank mark k 0 0 vt) vt).1 := rfl
    rw [hstep, resLoopX_fst]
  · have hq0' : ¬ q = 0 := by omega
    rw [if_neg hq0', if_neg hq0', vApplyActs'_append, GSTapes.applyActs'_append]
    have hstep : (vApplyActs' blank
        (VAct'.S (GSTapes.Act'.keep GSTapes.tP .left) ::
          [VAct'.S (GSTapes.Act'.keep GSTapes.tP (sc := sc) .right)])
        (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt)).1
        = GSTapes.applyActs' blank
            [GSTapes.Act'.keep GSTapes.tP .left, GSTapes.Act'.keep GSTapes.tP .right]
            (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt).1 := rfl
    rw [hstep, resLoopX_fst]

theorem resProgramX_U (blank mark : Fin sc) (k q : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (resProgramX blank mark k q vt) vt).2.U = vt.2.U := by
  unfold resProgramX
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    rw [if_pos rfl, vApplyActs'_append]
    have hstep : (vApplyActs' blank
        (VAct'.S (GSTapes.Act'.keep GSTapes.tP .left) ::
          VAct'.S (GSTapes.Act'.keep GSTapes.tP .right) ::
          [VAct'.S (GSTapes.Act'.keep GSTapes.tT .right), VAct'.X .right])
        (vApplyActs' blank (resLoopX blank mark k 0 0 vt) vt)).2.U
        = (vApplyActs' blank (resLoopX blank mark k 0 0 vt) vt).2.U := rfl
    rw [hstep, resLoopX_U]
  · have hq0' : ¬ q = 0 := by omega
    rw [if_neg hq0', vApplyActs'_append]
    have hstep : (vApplyActs' blank
        (VAct'.S (GSTapes.Act'.keep GSTapes.tP .left) ::
          [VAct'.S (GSTapes.Act'.keep GSTapes.tP (sc := sc) .right)])
        (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt)).2.U
        = (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt).2.U := rfl
    rw [hstep, resLoopX_U]

theorem perProgramX_Txt2 (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) :
    (vApplyActs' blank (perProgramX blank mark n vt) vt).2.Txt2
      = (vApplyActs' blank (perLoop1X blank mark n vt) vt).2.Txt2 := by
  unfold perProgramX
  rw [vApplyActs'_append, vApplyActs'_append, vApplyActs'_append,
    vApplyActs'_mapS_Txt2, vApplyActs'_mapS_Txt2, vApplyActs'_mapS_Txt2]

theorem resProgramX_Txt2_of_ne {blank mark : Fin sc} {k q : ℕ} (hq0 : ¬ q = 0)
    (vt : VTapes' sc) :
    (vApplyActs' blank (resProgramX blank mark k q vt) vt).2.Txt2
      = (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt).2.Txt2 := by
  unfold resProgramX
  rw [if_neg hq0, vApplyActs'_append]
  rfl

theorem resProgramX_Txt2_of_eq {blank mark : Fin sc} {k q : ℕ} (hq0 : q = 0)
    (vt : VTapes' sc) :
    (vApplyActs' blank (resProgramX blank mark k q vt) vt).2.Txt2
      = Tape.step blank (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt).2.Txt2
          (vApplyActs' blank (resLoopX blank mark k q 0 vt) vt).2.Txt2.focus .right := by
  subst hq0
  unfold resProgramX
  rw [if_pos rfl, vApplyActs'_append]
  rfl

/-- `perProgramX` の動作数は `perLoop1X`（`≤ 11*n`）＋ `probeC1`/`perUp`/`probeC2`
（`2 + 3*n + 2`）：`≤ 14*n+4`。 -/
theorem perProgramX_length_le (blank mark : Fin sc) (n : ℕ) (vt : VTapes' sc) :
    (perProgramX blank mark n vt).length ≤ 14 * n + 4 := by
  unfold perProgramX
  simp only [List.length_append, List.length_map, GSTapes.probeActs_length, GSTapes.perUp_length]
  have := perLoop1X_length_le blank mark n vt
  omega

/-- `resProgramX` の動作数は `resLoopX`（`≤ 9*q`）＋末尾（`q = 0` なら `4`、
それ以外は `2`）：`≤ 9*q+4`。 -/
theorem resProgramX_length_le (blank mark : Fin sc) (k q : ℕ) (vt : VTapes' sc) :
    (resProgramX blank mark k q vt).length ≤ 9 * q + 4 := by
  unfold resProgramX
  rw [List.length_append]
  have hle := resLoopX_length_le blank mark k q 0 vt
  by_cases hq0 : q = 0
  · subst hq0
    rw [if_pos rfl]
    simp only [List.length_cons, List.length_nil]
    omega
  · rw [if_neg hq0]
    simp only [List.length_cons, List.length_nil]
    omega

end VProgX

/-! ## 6. `vencodes_stepX`：`vprogramX` の一歩が `VEncodes'` を保つこと -/

section VEncodesX

variable {blank startSym endSym mark : Fin sc} {u v Text : List (Fin sc)} {k p₁ r : ℕ}
  {vt : VTapes' sc} {z : VState}

/-- **主定理（実現、有限制御向け再構成）**：`vencodes_step'` と同じ主張を、
`vprogram'` の代わりに `vprogramX`（相乗りループ＋巻き戻し＋残差補正）で示す。 -/
theorem vencodes_stepX (hk : 0 < k) (hp : 0 < p₁) (hne : mark ≠ blank)
    (hend : endSym ∉ v) (hendu : endSym ∉ u)
    (hE : VEncodes' blank startSym endSym mark u v Text k p₁ r vt z)
    (hq : z.1.q ≤ v.length) (hc : z.2 ≤ u.length) (hpos : u.length ≤ z.1.pos)
    (hfit : (scanStep v k p₁ r Text z.1).pos + (scanStep v k p₁ r Text z.1).q < Text.length) :
    VEncodes' blank startSym endSym mark u v Text k p₁ r
      (vApplyActs' blank (vprogramX blank endSym mark k vt) vt)
      (vStep u v k p₁ r Text z) := by
  have hscan := GSTapes.encodes_step' hk hne hend hE.scan hq hfit
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · -- 比較枝：`vprogram'` と同一。
    have hveq : vprogramX blank endSym mark k vt
        = (GSTapes.advActs blank mark vt.1).map VAct'.S ++
          (vcomp2Acts blank endSym vt.2).map liftAct := by
      unfold vprogramX; rw [if_pos hadv]
    rw [hveq, vApplyActs'_append, vApplyActs'_map_S]
    obtain ⟨ha1, ha2⟩ := (GSTapes.advance_iff' hend hE.scan hq).1 hadv
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
    have hprogAdv : GSTapes.applyActs' blank (GSTapes.program' blank endSym mark k vt.1) vt.1
        = GSTapes.applyActs' blank (GSTapes.advActs blank mark vt.1) vt.1 := by
      unfold GSTapes.program'; rw [if_pos hadv]
    rw [hprogAdv] at hscan
    rw [hvs]
    refine ⟨?_, ?_, ?_⟩
    · rw [vApplyActs'_map_liftAct_fst]
      exact hscan
    · rw [vApplyActs'_snd, extActs'_map_liftAct]
      exact hU2
    · rw [vApplyActs'_snd, extActs'_map_liftAct, hss]
      exact hX2
  · -- ずらし枝：相乗りループ＋巻き戻し＋残差補正。
    have hna : ¬ (z.1.q ≠ v.length ∧ Text[z.1.pos + z.1.q]? = v[z.1.q]?) :=
      fun hcon => hadv ((GSTapes.advance_iff' hend hE.scan hq).2 hcon)
    have hss : scanStep v k p₁ r Text z.1
        = (⟨z.1.pos + gsShift k p₁ r z.1.q, gsNextQ k p₁ r z.1.q⟩ : ScanState) :=
      GSTapes.scanStep_shift hna
    have hcc : cOf vt.2 = z.2 := cOf_eq hE.pat
    have hroom : z.1.pos + gsShift k p₁ r z.1.q < Text.length := by
      rw [hss] at hfit
      exact lt_of_le_of_lt (Nat.le_add_right _ _) hfit
    rw [vStep_shift hna, hss]
    rw [hss] at hscan
    have hveq : vprogramX blank endSym mark k vt
        = (GSTapes.probeActs blank GSTapes.tAn).map VAct'.S ++
          (GSTapes.probeActs blank GSTapes.tRn).map VAct'.S ++
          (if Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
              Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark then
            perProgramX blank mark (GSTapes.p1Of' vt.1) vt
          else
            resProgramX blank mark k (GSTapes.qOf' vt.1) vt) ++
          uxWalk vt := by
      unfold vprogramX; rw [if_neg hadv]
    rw [hveq]
    simp only [vApplyActs'_append, vApplyActs'_map_S]
    have hrnId : GSTapes.applyActs' blank (GSTapes.probeActs blank GSTapes.tRn)
        (GSTapes.applyActs' blank (GSTapes.probeActs blank GSTapes.tAn) vt.1) = vt.1 := by
      rw [GSTapes.probeActs_id hE.scan.quad.an]
      exact GSTapes.probeActs_id hE.scan.quad.rn
    rw [hrnId]
    -- `probeActs (an, rn)` は `vt` を変えない。以降は `C := perProgramX/resProgramX` の
    -- 分岐、`D := uWalk vt`、`E := txt2Rewind vt` を順に適用する。
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
    · -- 周期ずらし：`perLoop1X` はちょうど `p₁ = gsShift` 周。
      have hcondT : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark :=
        (GSTapes.period_iff' hne hE.scan).2 hcond
      have hgs : gsShift k p₁ r z.1.q = p₁ := by unfold gsShift; rw [if_pos hcond]
      have hp1 : GSTapes.p1Of' vt.1 = p₁ := GSTapes.p1Of'_eq hE.scan
      rw [if_pos hcondT, hp1] at hprogEq
      rw [hprogEq] at hscan
      rw [if_pos hcondT, hp1]
      set vt2 := vApplyActs' blank (perProgramX blank mark p₁ vt) vt with hvt2def
      have hvt2fst : vt2.1 = GSTapes.applyActs' blank (GSTapes.perProgram blank mark p₁ vt.1)
          vt.1 := perProgramX_fst blank mark p₁ vt
      have hvt2U : vt2.2.U = vt.2.U := perProgramX_U blank mark p₁ vt
      have hle : p₁ ≤ z.1.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
      have hroomP : (z.1.pos - u.length + z.2) + p₁ < Text.length := by omega
      obtain ⟨_, _, _, _, _, _, hLoopTxt2⟩ := perLoop1X_spec (blank := blank) (mark := mark)
        (w := startSym :: (v ++ [endSym])) (Text := Text) hne p₁ vt z.1.q p₁ 0
        (k * p₁) r (z.1.pos - u.length + z.2) hle (Nat.le_refl _) hE.scan.pat hE.scan.c1
        hE.scan.c2 hE.scan.quad hE.txt2 hroomP
      have hvt2Txt2eq : vt2.2.Txt2 = (vApplyActs' blank (perLoop1X blank mark p₁ vt) vt).2.Txt2 :=
        by rw [hvt2def]; exact perProgramX_Txt2 blank mark p₁ vt
      have hvt2Txt2 : Tape.SeqView blank vt2.2.Txt2 Text
          (z.1.pos - u.length + z.2 + p₁) := by rw [hvt2Txt2eq]; exact hLoopTxt2
      have hUvt2 : Tape.SeqView blank vt2.2.U (startSym :: (u ++ [endSym])) (z.2 + 1) := by
        rw [hvt2U]; exact hE.pat
      have huxU : Tape.SeqView blank (vApplyActs' blank (uxWalk vt) vt2).2.U
          (startSym :: (u ++ [endSym])) (0 + 1) :=
        uxWalk_U (blank := blank) (startSym := startSym) (endSym := endSym) (u := u)
          (vt0 := vt) (vt' := vt2) (c := z.2) hvt2U hUvt2
      have huxfst : (vApplyActs' blank (uxWalk vt) vt2).1 = vt2.1 := uxWalk_fst blank vt vt2
      have htarg1 : 1 ≤ z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 := by rw [hgs]; omega
      have htargroom : z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 < Text.length := by omega
      have huxTxt2 : Tape.SeqView blank (vApplyActs' blank (uxWalk vt) vt2).2.Txt2 Text
          (z.1.pos + gsShift k p₁ r z.1.q - u.length + 0) :=
        uxWalk_Txt2 (blank := blank) (vt0 := vt) (vt' := vt2) hcc htarg1 htargroom
          (by
            rw [show z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 - 1 + (z.2 + 1)
              = z.1.pos - u.length + z.2 + p₁ from by rw [hgs]; omega]
            exact hvt2Txt2)
      refine ⟨?_, ?_, ?_⟩
      · rw [huxfst, hvt2fst]; exact hscan
      · exact huxU
      · exact huxTxt2
    · -- リセットずらし：`resLoopX` の `Txt2` 総量は `stays k q 0`。
      have hcondT : ¬ (Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
          Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark) :=
        fun hc => hcond ((GSTapes.period_iff' hne hE.scan).1 hc)
      have hgs : gsShift k p₁ r z.1.q = max 1 (ceilDiv z.1.q k) := by
        unfold gsShift; rw [if_neg hcond]
      have hqz : GSTapes.qOf' vt.1 = z.1.q := GSTapes.qOf'_eq hE.scan
      rw [if_neg hcondT, hqz] at hprogEq
      rw [hprogEq] at hscan
      rw [if_neg hcondT, hqz]
      set vt2 := vApplyActs' blank (resProgramX blank mark k z.1.q vt) vt with hvt2def
      have hvt2fst : vt2.1 = GSTapes.applyActs' blank
          (GSTapes.resProgram blank mark k z.1.q vt.1) vt.1 :=
        resProgramX_fst blank mark k z.1.q vt
      have hvt2U : vt2.2.U = vt.2.U := resProgramX_U blank mark k z.1.q vt
      have hUvt2 : Tape.SeqView blank vt2.2.U (startSym :: (u ++ [endSym])) (z.2 + 1) := by
        rw [hvt2U]; exact hE.pat
      have huxU : Tape.SeqView blank (vApplyActs' blank (uxWalk vt) vt2).2.U
          (startSym :: (u ++ [endSym])) (0 + 1) :=
        uxWalk_U (blank := blank) (startSym := startSym) (endSym := endSym) (u := u)
          (vt0 := vt) (vt' := vt2) (c := z.2) hvt2U hUvt2
      have huxfst : (vApplyActs' blank (uxWalk vt) vt2).1 = vt2.1 := uxWalk_fst blank vt vt2
      have hgspos : 1 ≤ gsShift k p₁ r z.1.q := by rw [hgs]; omega
      have htarg1 : 1 ≤ z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 := by omega
      have htargroom : z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 < Text.length := by omega
      rcases Nat.eq_zero_or_pos z.1.q with hq0 | hq0
      · -- `q = 0`：`stays k 0 0 = 0`、`resProgramX` の特別枝が `+1`。`gsShift = 1`。
        have hcd0 : ceilDiv 0 k = 0 := by
          unfold ceilDiv
          simpa using Nat.div_eq_of_lt (by omega : (0 : ℕ) + k - 1 < k)
        have hgs1 : gsShift k p₁ r z.1.q = 1 := by rw [hgs, hq0, hcd0]; rfl
        have hvt2Txt2step : vt2.2.Txt2
            = Tape.step blank (vApplyActs' blank (resLoopX blank mark k z.1.q 0 vt) vt).2.Txt2
                (vApplyActs' blank (resLoopX blank mark k z.1.q 0 vt) vt).2.Txt2.focus .right := by
          rw [hvt2def]; exact resProgramX_Txt2_of_eq hq0 vt
        have hstaysroom : (z.1.pos - u.length + z.2) + GSTapes.stays k z.1.q 0 < Text.length := by
          rw [hq0]; simp only [GSTapes.stays, Nat.add_zero]; omega
        have hTarg : Tape.SeqView blank (vt.1 GSTapes.tT) Text
            ((z.1.pos + z.1.q) + GSTapes.moves k z.1.q 0) := by
          have heq : (z.1.pos + z.1.q) + GSTapes.moves k z.1.q 0 = z.1.pos + z.1.q := by
            rw [hq0]; simp [GSTapes.moves]
          rw [heq]; exact hE.scan.txt
        obtain ⟨_, _, _, _, _, _, hL⟩ := resLoopX_spec (blank := blank) (mark := mark) hne
          (w := startSym :: (v ++ [endSym])) (Text := Text) k z.1.q 0 vt z.1.q
          (z.1.pos + z.1.q) (k * p₁) r (z.1.pos - u.length + z.2) (Nat.le_refl _) hE.scan.pat
          hTarg hE.scan.quad hE.txt2 hstaysroom
        have hstays0 : GSTapes.stays k z.1.q 0 = 0 := by rw [hq0]; rfl
        have hL' : Tape.SeqView blank
            (vApplyActs' blank (resLoopX blank mark k z.1.q 0 vt) vt).2.Txt2 Text
            (z.1.pos - u.length + z.2) := by
          rw [hstays0] at hL; simpa using hL
        have hvt2Txt2 : Tape.SeqView blank vt2.2.Txt2 Text
            ((z.1.pos - u.length + z.2) + 1) := by
          rw [hvt2Txt2step]
          refine Tape.seq_move_right hL' ?_
          have hroom1 := hroom
          rw [hgs1] at hroom1
          omega
        have huxTxt2 : Tape.SeqView blank (vApplyActs' blank (uxWalk vt) vt2).2.Txt2 Text
            (z.1.pos + gsShift k p₁ r z.1.q - u.length + 0) :=
          uxWalk_Txt2 (blank := blank) (vt0 := vt) (vt' := vt2) hcc htarg1 htargroom
            (by
              rw [show z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 - 1 + (z.2 + 1)
                = (z.1.pos - u.length + z.2) + 1 from by rw [hgs1]; omega]
              exact hvt2Txt2)
        refine ⟨?_, ?_, ?_⟩
        · rw [huxfst, hvt2fst]; exact hscan
        · exact huxU
        · exact huxTxt2
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
        have hstaysroom : (z.1.pos - u.length + z.2) + GSTapes.stays k z.1.q 0 < Text.length := by
          rw [hstaysval]; omega
        have hTarg : Tape.SeqView blank (vt.1 GSTapes.tT) Text
            ((z.1.pos + ceilDiv z.1.q k) + GSTapes.moves k z.1.q 0) := by
          have hle : ceilDiv z.1.q k ≤ z.1.q := GSTapes.ceilDiv_le_self hk
          have heq : (z.1.pos + ceilDiv z.1.q k) + GSTapes.moves k z.1.q 0 = z.1.pos + z.1.q := by
            rw [GSTapes.moves_zero k hk z.1.q]; omega
          rw [heq]; exact hE.scan.txt
        obtain ⟨_, _, _, _, _, _, hL⟩ := resLoopX_spec (blank := blank) (mark := mark) hne
          (w := startSym :: (v ++ [endSym])) (Text := Text) k z.1.q 0 vt z.1.q
          (z.1.pos + ceilDiv z.1.q k) (k * p₁) r (z.1.pos - u.length + z.2) (Nat.le_refl _)
          hE.scan.pat hTarg hE.scan.quad hE.txt2 hstaysroom
        have hvt2Txt2eq : vt2.2.Txt2
            = (vApplyActs' blank (resLoopX blank mark k z.1.q 0 vt) vt).2.Txt2 := by
          rw [hvt2def]; exact resProgramX_Txt2_of_ne hqne vt
        have hvt2Txt2 : Tape.SeqView blank vt2.2.Txt2 Text
            ((z.1.pos - u.length + z.2) + GSTapes.stays k z.1.q 0) := by
          rw [hvt2Txt2eq]; exact hL
        have huxTxt2 : Tape.SeqView blank (vApplyActs' blank (uxWalk vt) vt2).2.Txt2 Text
            (z.1.pos + gsShift k p₁ r z.1.q - u.length + 0) :=
          uxWalk_Txt2 (blank := blank) (vt0 := vt) (vt' := vt2) hcc htarg1 htargroom
            (by
              rw [show z.1.pos + gsShift k p₁ r z.1.q - u.length + 0 - 1 + (z.2 + 1)
                = (z.1.pos - u.length + z.2) + GSTapes.stays k z.1.q 0 from by
                rw [hgs', ← hstaysval]; omega]
              exact hvt2Txt2)
        refine ⟨?_, ?_, ?_⟩
        · rw [huxfst, hvt2fst]; exact hscan
        · exact huxU
        · exact huxTxt2

end VEncodesX

/-! ## 7. コスト -/

section VProgXCost

/-- `vprogramX` の動作数：比較枝は `≤ 8 + 4 = 12`（元の `vprogram'` と同じ形）、
ずらし枝は「相乗りループ（`perProgramX`/`resProgramX`：周期なら `≤ 14*p₁+4`、
リセットなら `≤ 9*q+4`）＋ `uxWalk`（`= 2*checked+4`）＋ probe 2 本（`= 4`）」。
まとめて `p₁` と `q` の項を両方持つ形で一様に上から抑える。 -/
theorem vprogramX_length_le (blank endSym mark : Fin sc) (k : ℕ) (vt : VTapes' sc) :
    (vprogramX blank endSym mark k vt).length
      ≤ 14 * GSTapes.p1Of' vt.1 + 9 * GSTapes.qOf' vt.1 + 12 + 2 * cOf vt.2 := by
  unfold vprogramX
  by_cases hadv : Tape.read (vt.1 GSTapes.tP) ≠ endSym ∧
      Tape.read (vt.1 GSTapes.tP) = Tape.read (vt.1 GSTapes.tT)
  · rw [if_pos hadv]
    simp only [List.length_append, List.length_map]
    have h1 := GSTapes.advActs_length_le blank mark vt.1
    have h2 := vcomp2Acts_length_le (blank := blank) (endSym := endSym) vt.2
    omega
  · rw [if_neg hadv]
    have hAn := GSTapes.probeActs_length blank GSTapes.tAn
    have hRn := GSTapes.probeActs_length blank GSTapes.tRn
    have hUXW : (uxWalk vt).length = 2 * cOf vt.2 + 4 := uxWalk_length vt
    simp only [List.length_append, List.length_map]
    by_cases hcond : Tape.read (Tape.step blank (vt.1 GSTapes.tAn) blank .left) = mark ∧
        Tape.read (Tape.step blank (vt.1 GSTapes.tRn) blank .left) = mark
    · rw [if_pos hcond]
      have hle := perProgramX_length_le blank mark (GSTapes.p1Of' vt.1) vt
      rw [hAn, hRn, hUXW]
      omega
    · rw [if_neg hcond]
      have hle := resProgramX_length_le blank mark k (GSTapes.qOf' vt.1) vt
      rw [hAn, hRn, hUXW]
      omega

end VProgXCost

/-! ## 8. 公理の確認 -/

#print axioms perDownX_spec
#print axioms perLoop1X_spec
#print axioms perDownX_length_le
#print axioms perLoop1X_length_le
#print axioms resDown1X_spec
#print axioms resDown2X_spec
#print axioms resLoopX_spec
#print axioms resDown1X_length_le
#print axioms resDown2X_length_le
#print axioms resLoopX_length_le
#print axioms perProgramX_fst
#print axioms perProgramX_U
#print axioms perProgramX_Txt2
#print axioms resProgramX_fst
#print axioms resProgramX_U
#print axioms resProgramX_Txt2_of_ne
#print axioms resProgramX_Txt2_of_eq
#print axioms uxWalkLoop_fst
#print axioms uxWalkLoop_U
#print axioms uxWalkLoop_Txt2
#print axioms uxWalk_fst
#print axioms uxWalk_U
#print axioms uxWalk_Txt2
#print axioms uxWalk_length
#print axioms vencodes_stepX
#print axioms perProgramX_length_le
#print axioms resProgramX_length_le
#print axioms vprogramX_length_le

end PalPeg.GSVTapes
