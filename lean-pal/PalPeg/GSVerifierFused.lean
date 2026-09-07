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
* `resDown2X`：`T` を動かす周回でだけ 1 歩右へ、`resDown1X`（`T` を止める周回）では
  動かさない（`resLoop` の `T` の移動量は `moves k n c`＝リセットずらしの
  `gsShift = max 1 (ceilDiv q k)` にちょうど一致するので、これで `Txt2` も
  同じ量だけ動く）。

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

/-- `resDown1`（`T` を止める周）はそのまま。`Txt2` は動かさない。 -/
def resDown1X (blank mark : Fin sc) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.resDown1 blank mark vt.1).map VAct'.S

/-- `resDown2`（`T` を動かす周）に `Txt2` の 1 歩（右）を相乗りさせたもの。 -/
def resDown2X (blank mark : Fin sc) (vt : VTapes' sc) : List (VAct' sc) :=
  (GSTapes.resDown2 blank mark vt.1).map VAct'.S ++ [VAct'.X .right]

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
`U` も `Txt2` も変わらない。 -/
theorem resDown1X_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {vt : VTapes' sc} {qq m r i : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1))
    (hQ : GSTapes.CQuad blank mark vt.1 m r qq)
    (hX : Tape.SeqView blank vt.2.Txt2 Text i) :
    Tape.SeqView blank ((vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tP) w
        (qq - 1 + 1) ∧
      GSTapes.CQuad blank mark (vApplyActs' blank (resDown1X blank mark vt) vt).1 m r (qq - 1) ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tT = vt.1 GSTapes.tT ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tC1 = vt.1 GSTapes.tC1 ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tC2 = vt.1 GSTapes.tC2 ∧
      (vApplyActs' blank (resDown1X blank mark vt) vt).2.U = vt.2.U ∧
      Tape.SeqView blank (vApplyActs' blank (resDown1X blank mark vt) vt).2.Txt2 Text i := by
  obtain ⟨hP', hQ', hT', h1', h2'⟩ := GSTapes.resDown1_spec hne hqq hP hQ
  unfold resDown1X
  rw [vApplyActs'_map_S]
  exact ⟨hP', hQ', hT', h1', h2', rfl, hX⟩

/-- **`resDown2X` の実現**：走査段 8 本への効果は `resDown2` と同じ、
`U` は変わらず、`Txt2` はちょうど 1 歩右へ。 -/
theorem resDown2X_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {vt : VTapes' sc} {qq ii m r i : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1))
    (hT : Tape.SeqView blank (vt.1 GSTapes.tT) Text (ii + 1))
    (hQ : GSTapes.CQuad blank mark vt.1 m r qq)
    (hX : Tape.SeqView blank vt.2.Txt2 Text i) (hroom : i + 1 < Text.length) :
    Tape.SeqView blank ((vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tP) w
        (qq - 1 + 1) ∧
      Tape.SeqView blank ((vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tT) Text
        ii ∧
      GSTapes.CQuad blank mark (vApplyActs' blank (resDown2X blank mark vt) vt).1 m r (qq - 1) ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tC1 = vt.1 GSTapes.tC1 ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).1 GSTapes.tC2 = vt.1 GSTapes.tC2 ∧
      (vApplyActs' blank (resDown2X blank mark vt) vt).2.U = vt.2.U ∧
      Tape.SeqView blank (vApplyActs' blank (resDown2X blank mark vt) vt).2.Txt2 Text
        (i + 1) := by
  obtain ⟨hP', hT', hQ', h1', h2'⟩ := GSTapes.resDown2_spec hne hqq hP hT hQ
  unfold resDown2X
  rw [vApplyActs'_mapS_append_X]
  exact ⟨hP', hT', hQ', h1', h2', rfl, Tape.seq_move_right hX hroom⟩

/-- **`resLoopX` の実現**：走査段 8 本（`P`, `T`, `C1`, `C2`）への効果は `resLoop`
と同じ、`U` は変わらず、`Txt2` はちょうど `moves k n c`（`resLoop` が `T` を動かす
回数、すなわちリセットずらしの `gsShift`）歩だけ右へ。 -/
theorem resLoopX_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    (k : ℕ) :
    ∀ (n c : ℕ) (vt : VTapes' sc) (qq ii m r i : ℕ), n ≤ qq →
      Tape.SeqView blank (vt.1 GSTapes.tP) w (qq + 1) →
      Tape.SeqView blank (vt.1 GSTapes.tT) Text (ii + GSTapes.moves k n c) →
      GSTapes.CQuad blank mark vt.1 m r qq →
      Tape.SeqView blank vt.2.Txt2 Text i → i + GSTapes.moves k n c < Text.length →
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
          (i + GSTapes.moves k n c) := by
  intro n
  induction n with
  | zero =>
      intro c vt qq ii m r i _ hP hT hQ hX _
      refine ⟨hP, by simpa [GSTapes.moves, resLoopX] using hT, hQ, rfl, rfl, rfl, ?_⟩
      simpa [GSTapes.moves, resLoopX] using hX
  | succ n ih =>
      intro c vt qq ii m r i hnq hP hT hQ hX hroom
      cases c with
      | zero =>
          obtain ⟨hP', hQ', hT', h1', h2', hU', hX'⟩ :=
            resDown1X_spec (blank := blank) (mark := mark) hne (by omega) hP hQ hX
          have hmv : GSTapes.moves k (n + 1) 0 = GSTapes.moves k n (k - 1) := rfl
          have hTT : Tape.SeqView blank
              ((vApplyActs' blank (resDown1X blank mark vt) vt).1 GSTapes.tT)
              Text (ii + GSTapes.moves k n (k - 1)) := by
            rw [hT']; rw [hmv] at hT; exact hT
          have hroom' : i + GSTapes.moves k n (k - 1) < Text.length := by
            rw [← hmv]; exact hroom
          have := ih (k - 1) (vApplyActs' blank (resDown1X blank mark vt) vt) (qq - 1) ii m r i
            (by omega) hP' hTT hQ' hX' hroom'
          rw [resLoopX, vApplyActs'_append]
          refine ⟨?_, this.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
          · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
          · rw [this.2.2.2.1, h1']
          · rw [this.2.2.2.2.1, h2']
          · rw [this.2.2.2.2.2.1, hU']
          · rw [hmv]; exact this.2.2.2.2.2.2
      | succ c =>
          have hmv : GSTapes.moves k (n + 1) (c + 1) = GSTapes.moves k n c + 1 := rfl
          have hT1 : Tape.SeqView blank (vt.1 GSTapes.tT) Text ((ii + GSTapes.moves k n c) + 1) :=
            by rw [show ii + GSTapes.moves k n c + 1 = ii + GSTapes.moves k (n + 1) (c + 1) from
              by rw [hmv]; omega]; exact hT
          have hroom1 : i + 1 < Text.length := by rw [hmv] at hroom; omega
          obtain ⟨hP', hT', hQ', h1', h2', hU', hX'⟩ :=
            resDown2X_spec (blank := blank) (mark := mark) hne (by omega) hP hT1 hQ hX hroom1
          have hroom2 : i + 1 + GSTapes.moves k n c < Text.length := by
            rw [hmv] at hroom; omega
          have := ih c (vApplyActs' blank (resDown2X blank mark vt) vt) (qq - 1) ii m r (i + 1)
            (by omega) hP' hT' hQ' hX' hroom2
          rw [resLoopX, vApplyActs'_append]
          refine ⟨?_, this.2.1, ?_, ?_, ?_, ?_, ?_⟩
          · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
          · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
          · rw [this.2.2.2.1, h1']
          · rw [this.2.2.2.2.1, h2']
          · rw [this.2.2.2.2.2.1, hU']
          · rw [hmv, show i + (GSTapes.moves k n c + 1) = i + 1 + GSTapes.moves k n c from
              by omega]
            exact this.2.2.2.2.2.2

/-- `resDown1X` の動作数：`resDown1` と同じ、`≤ 8`。 -/
theorem resDown1X_length_le (blank mark : Fin sc) (vt : VTapes' sc) :
    (resDown1X blank mark vt).length ≤ 8 := by
  unfold resDown1X
  rw [List.length_map]
  unfold GSTapes.resDown1
  rw [List.length_append]
  have := GSTapes.qDecActs_length_le blank mark vt.1
  simp only [List.length_cons, List.length_nil]
  omega

/-- `resDown2X` の動作数は `resDown2` に `+1`（`Txt2` の 1 歩）：`≤ 9`。 -/
theorem resDown2X_length_le (blank mark : Fin sc) (vt : VTapes' sc) :
    (resDown2X blank mark vt).length ≤ 9 := by
  unfold resDown2X
  rw [List.length_append, List.length_map]
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

/-! ## 3. 公理の確認 -/

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

end PalPeg.GSVTapes
