import PegSeparation.Common.Compiler.RealTimeTM.Model

/-!
# テープの抽象ビュー (`TapeLib`)

Kim–Park 成果物の 1 本のテープ (`PegSeparation.RealTimeTM.TapeConfiguration`) を、
生のセル列ではなく **データ構造として** 扱うための再利用可能な層。

テープ意味論は再定義せず、成果物の `TapeConfiguration.applyAction` を**そのまま**使う
（`PalPeg.Tape.step` は `applyAction` の薄い別名にすぎない：`step_eq_applyAction`）。

* `Zipper`       — 左文脈・注目セル・右文脈の三つ組。テープ表現との全単射 (`Zipper.equivTape`)
                   と `TapeAction` 適用の書き換え規則（左端では移動せず書き込みのみ）。
* `StackView`    — スタック。ヘッドは最上段の**ひとつ上の空白セル**に載る。
                   `push a` = 「`a` を書いて右」、`pop` = 「左」（次の読みで最上段が読める）。
* `SeqView`      — セル 0 から語 `w` を格納し、ヘッドが位置 `i` を歩く。
                   左右移動でビューが保たれ、`read = w[i]?`、書き込みで `w.set i a` になる。
* `CounterView`  — 空白テープ上のヘッド位置による単進カウンタ。`dec` は左端で停留するので
                   `0` は保たれるが、`0` かどうかは**読めない**。
* `CounterView'` — セル 0 にマーカ記号を置いた変種（スタックビューの特別な場合）。
                   `0` かどうかが読み取りで判定できる。

いずれのビューも記号型 `Fin k`（成果物の `symbolCount`）についてパラメトリック。
-/

namespace PalPeg.Tape

open PegSeparation.RealTimeTM

variable {k : ℕ}

/-! ## 0. 1 行動の適用（成果物の意味論の薄い包み） -/

/-- ヘッドが読む記号。 -/
def read (tp : TapeConfiguration k) : Fin k := tp.focus

@[simp] theorem read_mk (l : List (Fin k)) (f : Fin k) (r : List (Fin k)) :
    read (TapeConfiguration.mk l f r) = f := rfl

@[simp] theorem read_eq_focus (tp : TapeConfiguration k) : read tp = tp.focus := rfl

/-- 「記号 `a` を書き、`m` の向きに動く」1 行動。成果物の `applyAction` をそのまま呼ぶ。 -/
def step (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) (m : Move) :
    TapeConfiguration k :=
  tp.applyAction blank { write := a, move := m }

theorem step_eq_applyAction (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k)
    (m : Move) : step blank tp a m = tp.applyAction blank { write := a, move := m } := rfl

@[simp] theorem step_stay (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) :
    step blank tp a .stay = { tp with focus := a } := rfl

@[simp] theorem step_right (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) :
    step blank tp a .right =
      { left := a :: tp.left
        focus := tp.right.headD blank
        right := tp.right.tail } := by
  obtain ⟨l, f, r⟩ := tp
  cases r <;> rfl

/-- **左端規則**：左に何も無いときは移動せず、書き込みだけが起きる。 -/
theorem step_left_of_left_nil {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    (h : tp.left = []) : step blank tp a .left = ⟨[], a, tp.right⟩ := by
  obtain ⟨l, f, r⟩ := tp
  cases l with
  | nil => rfl
  | cons x xs => simp at h

/-- 左移動（左文脈が空でない場合）：注目セルには左隣の記号が来る。 -/
theorem step_left_of_left_cons {blank : Fin k} {tp : TapeConfiguration k}
    {a n : Fin k} {l : List (Fin k)} (h : tp.left = n :: l) :
    step blank tp a .left = ⟨l, n, a :: tp.right⟩ := by
  obtain ⟨l', f, r⟩ := tp
  cases h
  rfl

/-- 左端で「現在の記号を書き直して左へ」は恒等。 -/
theorem step_left_edge_self (blank : Fin k) (tp : TapeConfiguration k)
    (h : tp.left = []) : step blank tp tp.focus .left = tp := by
  rw [step_left_of_left_nil h]
  obtain ⟨l, f, r⟩ := tp
  cases l with
  | nil => rfl
  | cons x xs => simp at h

@[simp] theorem read_step_stay (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) :
    read (step blank tp a .stay) = a := rfl

@[simp] theorem read_step_right (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k) :
    read (step blank tp a .right) = tp.right.headD blank := by
  rw [step_right]
  rfl

theorem read_step_left_nil {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    (h : tp.left = []) : read (step blank tp a .left) = a := by
  rw [step_left_of_left_nil h]
  rfl

theorem read_step_left_cons {blank : Fin k} {tp : TapeConfiguration k} {a n : Fin k}
    {l : List (Fin k)} (h : tp.left = n :: l) : read (step blank tp a .left) = n := by
  rw [step_left_of_left_cons h]
  rfl

/-! ## 1. `Zipper` ビュー -/

/-- テープの zipper 表現：`left` はヘッドの左側のセル（近い順）、`cur` は注目セル、
`right` はヘッドの右側のセル（近い順）。末尾の空白は表さない。 -/
structure Zipper (k : ℕ) where
  left : List (Fin k)
  cur : Fin k
  right : List (Fin k)
  deriving DecidableEq

namespace Zipper

/-- zipper をテープ表現へ。 -/
def toTape (z : Zipper k) : TapeConfiguration k :=
  { left := z.left, focus := z.cur, right := z.right }

/-- テープ表現を zipper へ。 -/
def ofTape (tp : TapeConfiguration k) : Zipper k :=
  { left := tp.left, cur := tp.focus, right := tp.right }

@[simp] theorem ofTape_toTape (z : Zipper k) : ofTape (toTape z) = z := rfl

@[simp] theorem toTape_ofTape (tp : TapeConfiguration k) : toTape (ofTape tp) = tp := rfl

/-- zipper 表現とテープ表現は全単射。 -/
def equivTape : Zipper k ≃ TapeConfiguration k where
  toFun := toTape
  invFun := ofTape
  left_inv := ofTape_toTape
  right_inv := toTape_ofTape

/-- zipper が読む記号。 -/
def read (z : Zipper k) : Fin k := z.cur

@[simp] theorem read_toTape (z : Zipper k) : Tape.read (toTape z) = z.read := rfl

/-- zipper 上の 1 行動（テープ意味論に落として戻すだけ）。 -/
def step (blank : Fin k) (z : Zipper k) (a : Fin k) (m : Move) : Zipper k :=
  ofTape (Tape.step blank (toTape z) a m)

@[simp] theorem toTape_step (blank : Fin k) (z : Zipper k) (a : Fin k) (m : Move) :
    toTape (step blank z a m) = Tape.step blank (toTape z) a m := rfl

/-- `stay`：注目セルを書き換えるだけ。 -/
@[simp] theorem apply_action_stay (blank : Fin k) (z : Zipper k) (a : Fin k) :
    step blank z a .stay = { z with cur := a } := rfl

/-- `right`：書いた記号が左文脈に積まれ、右文脈の先頭（無ければ空白）が新しい注目セル。 -/
@[simp] theorem apply_action_right (blank : Fin k) (z : Zipper k) (a : Fin k) :
    step blank z a .right =
      { left := a :: z.left, cur := z.right.headD blank, right := z.right.tail } := by
  obtain ⟨l, c, r⟩ := z
  cases r <;> rfl

/-- `left`（左文脈が空でない場合）。 -/
@[simp] theorem apply_action_left_cons (blank : Fin k) (n : Fin k) (l : List (Fin k))
    (c : Fin k) (r : List (Fin k)) (a : Fin k) :
    step blank ⟨n :: l, c, r⟩ a .left = ⟨l, n, a :: r⟩ := rfl

/-- **左端規則**：左文脈が空なら移動できず、書き込みだけが起きる。 -/
@[simp] theorem apply_action_left_edge (blank : Fin k) (c : Fin k) (r : List (Fin k))
    (a : Fin k) : step blank ⟨[], c, r⟩ a .left = ⟨[], a, r⟩ := rfl

@[simp] theorem read_apply_action_stay (blank : Fin k) (z : Zipper k) (a : Fin k) :
    read (step blank z a .stay) = a := rfl

@[simp] theorem read_apply_action_right (blank : Fin k) (z : Zipper k) (a : Fin k) :
    read (step blank z a .right) = z.right.headD blank := by
  rw [apply_action_right]
  rfl

theorem read_apply_action_left_edge (blank : Fin k) (c : Fin k) (r : List (Fin k))
    (a : Fin k) : read (step blank ⟨[], c, r⟩ a .left) = a := rfl

theorem read_apply_action_left_cons (blank : Fin k) (n : Fin k) (l : List (Fin k))
    (c : Fin k) (r : List (Fin k)) (a : Fin k) :
    read (step blank ⟨n :: l, c, r⟩ a .left) = n := rfl

end Zipper

/-! ## 2. `StackView`：スタックとしてのテープ

規約：ヘッドは**最上段のひとつ上の空白セル**に載る。こうすると
`push a` = 「`a` を書いて右」、`pop` = 「（空白を書いて）左」（次の読みで最上段が読める）が
それぞれ 1 行動になる。 -/

/-- リストの成分がすべて空白であること。 -/
def Blanks (blank : Fin k) (l : List (Fin k)) : Prop := ∀ s ∈ l, s = blank

@[simp] theorem blanks_nil (blank : Fin k) : Blanks blank ([] : List (Fin k)) := by
  intro s hs
  simp at hs

theorem Blanks.tail {blank : Fin k} {l : List (Fin k)} (h : Blanks blank l) :
    Blanks blank l.tail := by
  cases l with
  | nil => exact blanks_nil blank
  | cons x xs => exact fun s hs => h s (List.mem_cons_of_mem x hs)

theorem Blanks.cons {blank : Fin k} {l : List (Fin k)} (h : Blanks blank l) :
    Blanks blank (blank :: l) := by
  intro s hs
  rcases List.mem_cons.1 hs with hs | hs
  · exact hs
  · exact h s hs

theorem Blanks.headD {blank : Fin k} {l : List (Fin k)} (h : Blanks blank l) :
    l.headD blank = blank := by
  cases l with
  | nil => rfl
  | cons x xs => exact h x (List.mem_cons_self ..)

theorem blanks_replicate (blank : Fin k) (n : ℕ) :
    Blanks blank (List.replicate n blank) := fun _ hs => List.eq_of_mem_replicate hs

/-- スタックビュー：ヘッドは最上段の**ひとつ上**の空白セルに載り、ヘッドより左のセルが
スタックの中身 `l`（先頭が最上段）である。セルを左から右へ読むと `l.reverse` が並ぶ。 -/
structure StackView (blank : Fin k) (tp : TapeConfiguration k) (l : List (Fin k)) :
    Prop where
  left_eq : tp.left = l
  focus_blank : tp.focus = blank
  right_blanks : Blanks blank tp.right

/-- ヘッドが最上段セルそのものに載っている中間状態（`pop` の直後）。 -/
structure StackTopView (blank : Fin k) (tp : TapeConfiguration k) (a : Fin k)
    (l : List (Fin k)) : Prop where
  left_eq : tp.left = l
  focus_eq : tp.focus = a
  right_blanks : Blanks blank tp.right

/-- スタックビューでは空白が読める（最上段はまだ読めない）。 -/
theorem StackView.read_eq {blank : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : StackView blank tp l) : read tp = blank := h.focus_blank

/-- 最上段の記号はこの状態で読める。 -/
theorem StackTopView.read_eq {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : StackTopView blank tp a l) : read tp = a := h.focus_eq

/-- 初期テープは空スタック。 -/
theorem stackView_initial (blank : Fin k) :
    StackView blank ⟨[], blank, []⟩ ([] : List (Fin k)) :=
  ⟨rfl, rfl, blanks_nil blank⟩

/-- `push a` = 「`a` を書いて右へ」。 -/
theorem push_spec {blank : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : StackView blank tp l) (a : Fin k) :
    StackView blank (step blank tp a .right) (a :: l) := by
  rw [step_right]
  refine ⟨?_, ?_, ?_⟩
  · show a :: tp.left = a :: l
    rw [h.left_eq]
  · show tp.right.headD blank = blank
    exact h.right_blanks.headD
  · show Blanks blank tp.right.tail
    exact h.right_blanks.tail

/-- `push` の直後に読めるのは空白（新しい最上段のひとつ上のセル）。 -/
theorem read_after_push {blank : Fin k} {tp : TapeConfiguration k} {l : List (Fin k)}
    (h : StackView blank tp l) (a : Fin k) : read (step blank tp a .right) = blank := by
  rw [read_step_right]
  exact h.right_blanks.headD

/-- `pop` = 「空白を書いて左へ」。ヘッドは最上段セルに移る。 -/
theorem pop_spec {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : StackView blank tp (a :: l)) :
    StackTopView blank (step blank tp blank .left) a l := by
  rw [step_left_of_left_cons h.left_eq]
  exact ⟨rfl, rfl, h.right_blanks.cons⟩

/-- `pop` の直後に読めるのは最上段の記号。 -/
theorem read_after_pop {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : StackView blank tp (a :: l)) :
    read (step blank tp blank .left) = a :=
  read_step_left_cons h.left_eq

/-- 空スタックでの `pop` は左端規則で停留し、空スタックのまま。 -/
theorem pop_empty {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) : StackView blank (step blank tp blank .left) [] := by
  rw [step_left_of_left_nil h.left_eq]
  exact ⟨rfl, rfl, h.right_blanks⟩

/-- 空スタックでの `pop` は空白を読む（底のマーカと区別できる）。 -/
theorem read_after_pop_empty {blank : Fin k} {tp : TapeConfiguration k}
    (h : StackView blank tp []) : read (step blank tp blank .left) = blank :=
  read_step_left_nil h.left_eq

/-- 最上段を消す：ヘッドはその場（＝新しい最上段のひとつ上）に留まればよい。 -/
theorem pop_erase {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : StackTopView blank tp a l) :
    StackView blank (step blank tp blank .stay) l :=
  ⟨h.left_eq, rfl, h.right_blanks⟩

/-- 最上段を読んで元に戻す（peek）：`a` を書き戻して右へ。 -/
theorem peek_restore {blank : Fin k} {tp : TapeConfiguration k} {a : Fin k}
    {l : List (Fin k)} (h : StackTopView blank tp a l) :
    StackView blank (step blank tp a .right) (a :: l) := by
  rw [step_right]
  refine ⟨?_, ?_, ?_⟩
  · show a :: tp.left = a :: l
    rw [h.left_eq]
  · show tp.right.headD blank = blank
    exact h.right_blanks.headD
  · show Blanks blank tp.right.tail
    exact h.right_blanks.tail

/-! ## 3. `SeqView`：語の逐次読み書き -/

/-- 逐次ビュー：テープはセル 0 から語 `w` を保持し、ヘッドは位置 `i` にある。
`w` の右側には（あっても）空白しか無い。 -/
structure SeqView (blank : Fin k) (tp : TapeConfiguration k) (w : List (Fin k))
    (i : ℕ) : Prop where
  left_eq : tp.left = (w.take i).reverse
  focus_eq : w[i]? = some tp.focus
  right_eq : ∃ t, tp.right = w.drop (i + 1) ++ t ∧ Blanks blank t

theorem SeqView.lt {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    {i : ℕ} (h : SeqView blank tp w i) : i < w.length :=
  (List.getElem?_eq_some_iff.1 h.focus_eq).1

/-- 読み取りは `w[i]`。 -/
theorem SeqView.read_eq {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    {i : ℕ} (h : SeqView blank tp w i) : w[i]? = some (read tp) := h.focus_eq

/-- 右移動（現在の記号を書き戻す）：語は変わらず位置が 1 進む。 -/
theorem seq_move_right {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    {i : ℕ} (h : SeqView blank tp w i) (hi : i + 1 < w.length) :
    SeqView blank (step blank tp tp.focus .right) w (i + 1) := by
  obtain ⟨t, hr, ht⟩ := h.right_eq
  have hdrop : List.drop (i + 1) w = w[i + 1] :: List.drop (i + 1 + 1) w :=
    List.drop_eq_getElem_cons hi
  have htake : List.take (i + 1) w = List.take i w ++ [tp.focus] := by
    rw [List.take_add_one, h.focus_eq]
    rfl
  rw [step_right]
  refine ⟨?_, ?_, ⟨t, ?_, ht⟩⟩
  · show tp.focus :: tp.left = (List.take (i + 1) w).reverse
    rw [h.left_eq, htake, List.reverse_concat]
  · show w[i + 1]? = some (tp.right.headD blank)
    rw [hr, hdrop, List.cons_append]
    exact List.getElem?_eq_getElem hi
  · show tp.right.tail = List.drop (i + 1 + 1) w ++ t
    rw [hr, hdrop, List.cons_append]
    rfl

/-- 左移動（現在の記号を書き戻す）：語は変わらず位置が 1 戻る。 -/
theorem seq_move_left {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    {i : ℕ} (h : SeqView blank tp w (i + 1)) :
    SeqView blank (step blank tp tp.focus .left) w i := by
  obtain ⟨t, hr, ht⟩ := h.right_eq
  obtain ⟨hlt1, hfocus⟩ := List.getElem?_eq_some_iff.1 h.focus_eq
  have hlt : i < w.length := Nat.lt_of_succ_lt hlt1
  have hgi : w[i]? = some w[i] := List.getElem?_eq_getElem hlt
  have htake : List.take (i + 1) w = List.take i w ++ [w[i]] := by
    rw [List.take_add_one, hgi]
    rfl
  have hleft : tp.left = w[i] :: (List.take i w).reverse := by
    rw [h.left_eq, htake, List.reverse_concat]
  rw [step_left_of_left_cons hleft]
  refine ⟨rfl, ?_, ⟨t, ?_, ht⟩⟩
  · show w[i]? = some w[i]
    exact hgi
  · show tp.focus :: tp.right = List.drop (i + 1) w ++ t
    rw [hr, List.drop_eq_getElem_cons hlt1, hfocus, List.cons_append]

/-- 左端規則：位置 `0` で左へ動こうとしても停留し、ビューは保たれる。 -/
theorem seq_move_left_edge {blank : Fin k} {tp : TapeConfiguration k}
    {w : List (Fin k)} (h : SeqView blank tp w 0) :
    SeqView blank (step blank tp tp.focus .left) w 0 := by
  have hnil : tp.left = [] := by
    rw [h.left_eq]
    simp
  rw [step_left_edge_self blank tp hnil]
  exact h

/-- 書き込み：語が `w.set i a` になり、位置は変わらない。 -/
theorem seq_write {blank : Fin k} {tp : TapeConfiguration k} {w : List (Fin k)}
    {i : ℕ} (h : SeqView blank tp w i) (a : Fin k) :
    SeqView blank (step blank tp a .stay) (w.set i a) i := by
  obtain ⟨t, hr, ht⟩ := h.right_eq
  rw [step_stay]
  refine ⟨?_, ?_, ⟨t, ?_, ht⟩⟩
  · show tp.left = ((w.set i a).take i).reverse
    rw [h.left_eq, List.take_set_of_le (Nat.le_refl i)]
  · show (w.set i a)[i]? = some a
    exact List.getElem?_set_self h.lt
  · show tp.right = (w.set i a).drop (i + 1) ++ t
    rw [List.drop_set_of_lt (Nat.lt_succ_self i)]
    exact hr

/-- 書き込み直後に読めるのは書いた記号。 -/
theorem read_after_seq_write {blank : Fin k} {tp : TapeConfiguration k}
    {w : List (Fin k)} {i : ℕ} (_h : SeqView blank tp w i) (a : Fin k) :
    read (step blank tp a .stay) = a := rfl

/-! ## 4. `CounterView`：単進カウンタ -/

/-- 空白テープ上のヘッド位置を値とする単進カウンタ。 -/
structure CounterView (blank : Fin k) (tp : TapeConfiguration k) (n : ℕ) : Prop where
  left_eq : tp.left = List.replicate n blank
  focus_blank : tp.focus = blank
  right_blanks : Blanks blank tp.right

theorem counterView_initial (blank : Fin k) : CounterView blank ⟨[], blank, []⟩ 0 :=
  ⟨rfl, rfl, blanks_nil blank⟩

/-- `inc` = 空白を書いて右へ。 -/
theorem counter_inc {blank : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView blank tp n) :
    CounterView blank (step blank tp blank .right) (n + 1) := by
  rw [step_right]
  refine ⟨?_, ?_, ?_⟩
  · show blank :: tp.left = List.replicate (n + 1) blank
    rw [h.left_eq, List.replicate_succ]
  · show tp.right.headD blank = blank
    exact h.right_blanks.headD
  · show Blanks blank tp.right.tail
    exact h.right_blanks.tail

/-- `dec` = 空白を書いて左へ。 -/
theorem counter_dec {blank : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView blank tp (n + 1)) :
    CounterView blank (step blank tp blank .left) n := by
  have hleft : tp.left = blank :: List.replicate n blank := by
    rw [h.left_eq, List.replicate_succ]
  rw [step_left_of_left_cons hleft]
  exact ⟨rfl, rfl, h.right_blanks.cons⟩

/-- **左端規則**：`0` での `dec` は停留し、`0` のまま。 -/
theorem counter_dec_zero {blank : Fin k} {tp : TapeConfiguration k}
    (h : CounterView blank tp 0) :
    CounterView blank (step blank tp blank .left) 0 := by
  have hleft : tp.left = [] := by
    rw [h.left_eq]
    simp
  rw [step_left_of_left_nil hleft]
  exact ⟨rfl, rfl, h.right_blanks⟩

/-- マーカ無しでは常に空白しか読めない。 -/
theorem counter_read_eq {blank : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView blank tp n) : read tp = blank := h.focus_blank

/-- `dec` の直後も空白しか読めない（＝ゼロ判定ができない）。 -/
theorem counter_read_after_dec {blank : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView blank tp n) : read (step blank tp blank .left) = blank := by
  cases n with
  | zero =>
      refine read_step_left_nil (a := blank) ?_
      rw [h.left_eq]
      simp
  | succ m =>
      refine read_step_left_cons (a := blank) (n := blank)
        (l := List.replicate m blank) ?_
      rw [h.left_eq, List.replicate_succ]

/-- マーカ付き単進カウンタ：セル 0 に `mark` を置き、その上に `n` 個の空白を積む。
スタックビューの特別な場合として定義するので、`push`/`pop` の補題がそのまま効く。 -/
def CounterView' (blank mark : Fin k) (tp : TapeConfiguration k) (n : ℕ) : Prop :=
  StackView blank tp (List.replicate n blank ++ [mark])

theorem counterView'_initial (blank mark : Fin k) (r : List (Fin k))
    (hr : Blanks blank r) : CounterView' blank mark ⟨[mark], blank, r⟩ 0 :=
  ⟨rfl, rfl, hr⟩

theorem counterView'_cons {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ} :
    CounterView' blank mark tp (n + 1) ↔
      StackView blank tp (blank :: (List.replicate n blank ++ [mark])) := by
  rw [CounterView', List.replicate_succ, List.cons_append]

theorem counterView'_zero {blank mark : Fin k} {tp : TapeConfiguration k} :
    CounterView' blank mark tp 0 ↔ StackView blank tp [mark] := by
  rw [CounterView']
  simp

/-- `inc` = 空白を書いて右へ。 -/
theorem counter'_inc {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView' blank mark tp n) :
    CounterView' blank mark (step blank tp blank .right) (n + 1) :=
  counterView'_cons.2 (push_spec h blank)

/-- probe（空白を書いて左へ）で読める記号：`n = 0` のときだけマーカ。 -/
theorem counter'_read_after_probe {blank mark : Fin k} {tp : TapeConfiguration k}
    {n : ℕ} (h : CounterView' blank mark tp n) :
    read (step blank tp blank .left) = if n = 0 then mark else blank := by
  cases n with
  | zero => simpa using read_after_pop (counterView'_zero.1 h)
  | succ m => simpa using read_after_pop (counterView'_cons.1 h)

/-- `mark ≠ blank` のとき、probe の読みでゼロ判定ができる。 -/
theorem counter'_isZero_iff {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (hne : mark ≠ blank) (h : CounterView' blank mark tp n) :
    read (step blank tp blank .left) = mark ↔ n = 0 := by
  rw [counter'_read_after_probe h]
  cases n with
  | zero => simp
  | succ m => simp [hne.symm]

/-- `dec`（`n + 1` から）：probe（左）してから最上段の空白を消す（stay）。 -/
theorem counter'_dec {blank mark : Fin k} {tp : TapeConfiguration k} {n : ℕ}
    (h : CounterView' blank mark tp (n + 1)) :
    CounterView' blank mark
      (step blank (step blank tp blank .left) blank .stay) n :=
  pop_erase (pop_spec (counterView'_cons.1 h))

/-- `0` で `dec` を試みた場合：probe でマーカを読んだら書き戻して元に戻す。 -/
theorem counter'_dec_zero {blank mark : Fin k} {tp : TapeConfiguration k}
    (h : CounterView' blank mark tp 0) :
    CounterView' blank mark
      (step blank (step blank tp blank .left) mark .right) 0 :=
  counterView'_zero.2 (peek_restore (pop_spec (counterView'_zero.1 h)))

end PalPeg.Tape
