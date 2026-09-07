import PalPeg.GSScan
import PalPeg.TapeLib

/-!
# GS 走査段のテープ実現 (`GSScanTapes`)

`PalPeg.GSScan` の添字レベルの一歩 `scanStep` を、Kim–Park 成果物のテープ模型
(`PegSeparation.RealTimeTM.TapeConfiguration`, 1 テープ 1 ヘッド) 上の
**1 セル単位のヘッド動作列**として実現し、動作数がポテンシャル `Phi` の増分で
償却されることを示す（実時間 TM に落とすための償却解析）。

## テープ配置

* `P`   — パターンテープ。語 `startSym :: (v ++ [endSym])`、ヘッドは添字 `q + 1`。
          左端の `startSym` が左端検出用、右端の `endSym` が `q = |v|` 検出用。
* `Txt` — テキストテープ。語 `Text`、ヘッドは添字 `pos + q`。
* `Cnt` — 周期 `p₁` を保持する単進カウンタ（`CounterView'`、底にマーカ `mark`）。
          「`P` のヘッドを `p₁` だけ左へ」をカウンタの上げ下げで実現する（コスト `O(p₁)`）。

`k` は有限制御の定数、`p₁ r` は非有界なので、`p₁` はカウンタテープに、
`r` との比較はオラクルビットに委ねる（下記）。

## 3 つの枝

* 一致 (`q ← q+1`)   : `P` を右へ 1、`Txt` を右へ 1。コスト `2`。
* 周期ずらし          : `pos ← pos + p₁`, `q ← q - p₁`。このとき `pos + q` は不変なので
                        **`Txt` のヘッドは動かない**。`P` を左へ `p₁`、カウンタを
                        `p₁` 下げて `p₁` 上げる。コスト `4*p₁ + 2`。
* リセットずらし      : `pos ← pos + max 1 ⌈q/k⌉`, `q ← 0`。`P` のヘッドを `q` 回左へ
                        歩かせながら、`k` 回に `k-1` 回だけ `Txt` を左へ動かす
                        （mod `k` の位相は有限制御）。`Txt` は正味 `q - ⌈q/k⌉` だけ左へ動き、
                        添字は `pos + q` から `pos + ⌈q/k⌉` になる。
                        最後に左端 `startSym` を踏んで 1 歩戻る。コスト `≤ 2q + 3`。

## オラクルビット

条件 `k*p₁ ≤ q ∧ q ≤ r` の判定は、`q - k*p₁` と `r - q` の符号付き単進カウンタを
別途維持すれば有限制御で行えるが、本ファイルではその簿記は行わず、
**毎ステップ与えられるオラクルビット `b` として仮定する**
（`hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r)`）。他はすべて実際のテープ読み取りから
決定される（`endSym` の読み取りで `q = |v|` を、`P` と `Txt` の読み比べで一致を判定）。
-/

namespace PalPeg.GSTapes

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 0. 天井除算の補助 -/

theorem ceilDiv_le_self {k q : ℕ} (hk : 0 < k) : ceilDiv q k ≤ q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h : ceilDiv 0 k = 0 := by
      unfold ceilDiv
      exact Nat.div_eq_of_lt (by omega)
    omega
  · by_contra hcon
    push Not at hcon
    have h2 := (ceilDiv_bounds (q := q) (k := k) hk).2
    have h3 : k * (q + 1) ≤ k * ceilDiv q k := Nat.mul_le_mul (Nat.le_refl k) (by omega)
    have h4 : k * (q + 1) = k * q + k := by ring
    have h5 : q ≤ k * q := Nat.le_mul_of_pos_left q hk
    obtain ⟨X, hX⟩ : ∃ X, k * ceilDiv q k = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, k * q = Y := ⟨_, rfl⟩
    rw [hX] at h2 h3
    rw [hY] at h4 h5
    rw [h4] at h3
    omega

theorem ceilDiv_pos {k q : ℕ} (hk : 0 < k) (hq : 0 < q) : 0 < ceilDiv q k := by
  have h1 := (ceilDiv_bounds (q := q) (k := k) hk).1
  rcases Nat.eq_zero_or_pos (ceilDiv q k) with h | h
  · rw [h, Nat.mul_zero] at h1; omega
  · exact h

theorem ceilDiv_eq_succ {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    ceilDiv n k = (n - 1) / k + 1 := by
  unfold ceilDiv
  have h : n + k - 1 = (n - 1) + k := by omega
  rw [h, Nat.add_div_right _ hk]

/-! ## 1. mod `k` スケジュール：`Txt` を動かさない歩数 -/

/-- `n` 回の `P` 左移動のうち `Txt` を **動かさない** 回数（位相 `c` から開始）。 -/
def stays (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, 0 => stays k n (k - 1) + 1
  | n + 1, c + 1 => stays k n c

/-- `n` 回の `P` 左移動のうち `Txt` を **動かす** 回数。 -/
def moves (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, 0 => moves k n (k - 1)
  | n + 1, c + 1 => moves k n c + 1

theorem stays_add_moves (k : ℕ) : ∀ n c, stays k n c + moves k n c = n := by
  intro n
  induction n with
  | zero => intro c; simp [stays, moves]
  | succ n ih =>
    intro c
    cases c with
    | zero =>
      have h := ih (k - 1)
      simp only [stays, moves]
      omega
    | succ c =>
      have h := ih c
      simp only [stays, moves]
      omega

theorem stays_shift (k : ℕ) : ∀ c n, stays k (n + c) c = stays k n 0 := by
  intro c
  induction c with
  | zero => intro n; rfl
  | succ c ih =>
    intro n
    have h : n + (c + 1) = (n + c) + 1 := by omega
    rw [h]
    simp only [stays]
    exact ih n

theorem stays_small (k : ℕ) : ∀ n c, n ≤ c → stays k n c = 0 := by
  intro n
  induction n with
  | zero => intro c _; simp [stays]
  | succ n ih =>
    intro c hc
    cases c with
    | zero => omega
    | succ c =>
      simp only [stays]
      exact ih c (by omega)

theorem stays_zero (k : ℕ) (hk : 0 < k) (n : ℕ) : stays k n 0 = ceilDiv n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      simp only [stays]
      unfold ceilDiv
      exact (Nat.div_eq_of_lt (by omega)).symm
    | succ m =>
      simp only [stays]
      rw [ceilDiv_eq_succ hk (Nat.succ_pos m), Nat.succ_sub_one]
      have key : stays k m (k - 1) = m / k := by
        rcases Nat.lt_or_ge m k with hm | hm
        · rw [stays_small k m (k - 1) (by omega), Nat.div_eq_of_lt hm]
        · have hsplit : m = (m - (k - 1)) + (k - 1) := by omega
          have h1 : stays k m (k - 1) = stays k (m - (k - 1)) 0 := by
            conv_lhs => rw [hsplit]
            exact stays_shift k (k - 1) (m - (k - 1))
          rw [h1, ih (m - (k - 1)) (by omega), ceilDiv_eq_succ hk (by omega)]
          have h2 : m - (k - 1) - 1 = m - k := by omega
          rw [h2]
          conv_rhs => rw [Nat.div_eq_sub_div hk hm]
      omega

theorem moves_zero (k : ℕ) (hk : 0 < k) (n : ℕ) : moves k n 0 = n - ceilDiv n k := by
  have h1 := stays_add_moves k n 0
  have h2 := stays_zero k hk n
  omega

/-! ## 2. テープ状態と 1 セル動作 -/

/-- 走査段が使う 3 本のテープ。 -/
structure TapesState (sc : ℕ) where
  P : TapeConfiguration sc
  Txt : TapeConfiguration sc
  Cnt : TapeConfiguration sc

/-- 1 本のテープに対する 1 個のヘッド動作。`P`/`T` は読んだ記号を書き戻して移動する
（テープを書き換えない移動）。`C` は書く記号を明示する（空白またはマーカ）。 -/
inductive Act (sc : ℕ) where
  | P : Move → Act sc
  | T : Move → Act sc
  | C : Fin sc → Move → Act sc

def applyAct (blank : Fin sc) (ts : TapesState sc) : Act sc → TapesState sc
  | .P m => { ts with P := Tape.step blank ts.P ts.P.focus m }
  | .T m => { ts with Txt := Tape.step blank ts.Txt ts.Txt.focus m }
  | .C a m => { ts with Cnt := Tape.step blank ts.Cnt a m }

def applyActs (blank : Fin sc) (l : List (Act sc)) (ts : TapesState sc) : TapesState sc :=
  l.foldl (applyAct blank) ts

@[simp] theorem applyActs_nil (blank : Fin sc) (ts : TapesState sc) :
    applyActs blank [] ts = ts := rfl

@[simp] theorem applyActs_cons (blank : Fin sc) (a : Act sc) (l : List (Act sc))
    (ts : TapesState sc) :
    applyActs blank (a :: l) ts = applyActs blank l (applyAct blank ts a) := rfl

theorem applyActs_append (blank : Fin sc) (l₁ l₂ : List (Act sc)) (ts : TapesState sc) :
    applyActs blank (l₁ ++ l₂) ts = applyActs blank l₂ (applyActs blank l₁ ts) := by
  simp [applyActs]

/-! ## 3. ヘッドの反復移動 -/

/-- 現在の記号を書き戻しながら左へ `n` セル。 -/
def leftN (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => leftN blank (Tape.step blank tp tp.focus .left) n

/-- カウンタを `n` 回 `dec`（probe して最上段を消す、1 回 2 動作）。 -/
def decN (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 =>
      decN blank (Tape.step blank (Tape.step blank tp blank .left) blank .stay) n

/-- カウンタを `n` 回 `inc`。 -/
def incN (blank : Fin sc) : TapeConfiguration sc → ℕ → TapeConfiguration sc
  | tp, 0 => tp
  | tp, n + 1 => incN blank (Tape.step blank tp blank .right) n

theorem seq_leftN {blank : Fin sc} {w : List (Fin sc)} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (i : ℕ), Tape.SeqView blank tp w (i + n) →
      Tape.SeqView blank (leftN blank tp n) w i := by
  intro n
  induction n with
  | zero => intro tp i h; simpa [leftN] using h
  | succ n ih =>
    intro tp i h
    have h' : Tape.SeqView blank tp w ((i + n) + 1) := by
      have : i + (n + 1) = (i + n) + 1 := by omega
      rwa [this] at h
    exact ih _ i (Tape.seq_move_left h')

theorem counter'_decN {blank mark : Fin sc} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (m : ℕ),
      Tape.CounterView' blank mark tp (m + n) →
        Tape.CounterView' blank mark (decN blank tp n) m := by
  intro n
  induction n with
  | zero => intro tp m h; simpa [decN] using h
  | succ n ih =>
    intro tp m h
    have h' : Tape.CounterView' blank mark tp ((m + n) + 1) := by
      have : m + (n + 1) = (m + n) + 1 := by omega
      rwa [this] at h
    exact ih _ m (Tape.counter'_dec h')

theorem counter'_incN {blank mark : Fin sc} :
    ∀ (n : ℕ) (tp : TapeConfiguration sc) (m : ℕ),
      Tape.CounterView' blank mark tp m →
        Tape.CounterView' blank mark (incN blank tp n) (m + n) := by
  intro n
  induction n with
  | zero => intro tp m h; simpa [incN] using h
  | succ n ih =>
    intro tp m h
    have h' := ih (Tape.step blank tp blank .right) (m + 1) (Tape.counter'_inc h)
    have : m + 1 + n = m + (n + 1) := by omega
    rwa [this] at h'

/-! ## 4. 動作列 -/

/-- 周期ずらしの下げループ：`P` を 1 左、カウンタを 1 下げる、を `n` 回。 -/
def perLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => Act.P .left :: Act.C blank .left :: Act.C blank .stay :: perLoop blank n

/-- 周期ずらしの動作列（下げ `n` 回 → マーカ検出 → 上げ `n` 回）。 -/
def periodActs (blank mark : Fin sc) (n : ℕ) : List (Act sc) :=
  perLoop blank n ++
    (Act.C blank .left :: Act.C mark .right :: List.replicate n (Act.C blank .right))

/-- リセットずらしの歩行：`P` を `n` 回左へ、位相 `c` が `0` のときだけ `Txt` を止める。 -/
def resetActs (sc k : ℕ) : ℕ → ℕ → List (Act sc)
  | 0, _ => []
  | n + 1, 0 => Act.P .left :: resetActs sc k n (k - 1)
  | n + 1, c + 1 => Act.P .left :: Act.T .left :: resetActs sc k n c

/-- リセットずらしの動作列：歩行 → 左端 `startSym` を踏んで 1 歩戻る →
（`q = 0` のときだけ）`Txt` を 1 右へ。 -/
def resetProgram (sc k q : ℕ) : List (Act sc) :=
  resetActs sc k q 0 ++
    (Act.P .left :: Act.P .right :: (if q = 0 then [Act.T (sc := sc) .right] else []))

@[simp] theorem perLoop_length (blank : Fin sc) (n : ℕ) :
    (perLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [perLoop]
  | succ n ih => simp only [perLoop, List.length_cons, ih]; omega

@[simp] theorem periodActs_length (blank mark : Fin sc) (n : ℕ) :
    (periodActs blank mark n).length = 4 * n + 2 := by
  simp only [periodActs, List.length_append, List.length_cons, List.length_replicate,
    perLoop_length]
  omega

theorem resetActs_length (sc k : ℕ) : ∀ n c,
    (resetActs sc k n c).length = n + moves k n c := by
  intro n
  induction n with
  | zero => intro c; simp [resetActs, moves]
  | succ n ih =>
    intro c
    cases c with
    | zero =>
      have h := ih (k - 1)
      simp only [resetActs, moves, List.length_cons, h]
      omega
    | succ c =>
      have h := ih c
      simp only [resetActs, moves, List.length_cons, h]
      omega

theorem resetProgram_length (sc k q : ℕ) :
    (resetProgram sc k q).length = q + moves k q 0 + 2 + (if q = 0 then 1 else 0) := by
  simp only [resetProgram, List.length_append, List.length_cons, resetActs_length]
  split_ifs <;> simp

/-! ### 動作列の効果（テープごとの射影） -/

theorem perLoop_P (blank : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (perLoop blank n) ts).P = leftN blank ts.P n := by
  intro n
  induction n with
  | zero => intro ts; simp [perLoop, leftN]
  | succ n ih =>
    intro ts
    simp only [perLoop, applyActs_cons, applyAct, leftN]
    exact ih _

theorem perLoop_Txt (blank : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (perLoop blank n) ts).Txt = ts.Txt := by
  intro n
  induction n with
  | zero => intro ts; simp [perLoop]
  | succ n ih =>
    intro ts
    simp only [perLoop, applyActs_cons, applyAct]
    exact ih _

theorem perLoop_Cnt (blank : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (perLoop blank n) ts).Cnt = decN blank ts.Cnt n := by
  intro n
  induction n with
  | zero => intro ts; simp [perLoop, decN]
  | succ n ih =>
    intro ts
    simp only [perLoop, applyActs_cons, applyAct, decN]
    exact ih _

theorem replC_P (blank c : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (List.replicate n (Act.C c .right)) ts).P = ts.P := by
  intro n
  induction n with
  | zero => intro ts; simp
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_Txt (blank c : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (List.replicate n (Act.C c .right)) ts).Txt = ts.Txt := by
  intro n
  induction n with
  | zero => intro ts; simp
  | succ n ih => intro ts; simp only [List.replicate_succ, applyActs_cons, applyAct]; exact ih _

theorem replC_Cnt (blank : Fin sc) : ∀ n (ts : TapesState sc),
    (applyActs blank (List.replicate n (Act.C blank .right)) ts).Cnt = incN blank ts.Cnt n := by
  intro n
  induction n with
  | zero => intro ts; simp [incN]
  | succ n ih =>
    intro ts
    simp only [List.replicate_succ, applyActs_cons, applyAct, incN]
    exact ih _

theorem resetActs_P (blank : Fin sc) (k : ℕ) : ∀ n c (ts : TapesState sc),
    (applyActs blank (resetActs sc k n c) ts).P = leftN blank ts.P n := by
  intro n
  induction n with
  | zero => intro c ts; simp [resetActs, leftN]
  | succ n ih =>
    intro c ts
    cases c with
    | zero =>
      simp only [resetActs, applyActs_cons, applyAct, leftN]
      exact ih _ _
    | succ c =>
      simp only [resetActs, applyActs_cons, applyAct, leftN]
      exact ih _ _

theorem resetActs_Cnt (blank : Fin sc) (k : ℕ) : ∀ n c (ts : TapesState sc),
    (applyActs blank (resetActs sc k n c) ts).Cnt = ts.Cnt := by
  intro n
  induction n with
  | zero => intro c ts; simp [resetActs]
  | succ n ih =>
    intro c ts
    cases c with
    | zero => simp only [resetActs, applyActs_cons, applyAct]; exact ih _ _
    | succ c => simp only [resetActs, applyActs_cons, applyAct]; exact ih _ _

theorem resetActs_Txt (blank : Fin sc) (k : ℕ) : ∀ n c (ts : TapesState sc),
    (applyActs blank (resetActs sc k n c) ts).Txt = leftN blank ts.Txt (moves k n c) := by
  intro n
  induction n with
  | zero => intro c ts; simp [resetActs, moves, leftN]
  | succ n ih =>
    intro c ts
    cases c with
    | zero =>
      simp only [resetActs, applyActs_cons, applyAct, moves]
      exact ih _ _
    | succ c =>
      simp only [resetActs, applyActs_cons, applyAct, moves, leftN]
      exact ih _ _

/-! ## 5. 符号化 -/

/-- `P` のヘッド位置から読み取れる一致長 `q`。 -/
def qOf (ts : TapesState sc) : ℕ := ts.P.left.length - 1

/-- カウンタテープから読み取れる周期 `p₁`。 -/
def p1Of (ts : TapesState sc) : ℕ := ts.Cnt.left.length - 1

/-- テープ状態が走査状態 `st` を符号化していること。 -/
structure Encodes (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc)) (p₁ : ℕ)
    (ts : TapesState sc) (st : ScanState) : Prop where
  pat : Tape.SeqView blank ts.P (startSym :: (v ++ [endSym])) (st.q + 1)
  txt : Tape.SeqView blank ts.Txt Text (st.pos + st.q)
  cnt : Tape.CounterView' blank mark ts.Cnt p₁

section Step

variable {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)} {p₁ : ℕ}
  {ts : TapesState sc} {st : ScanState}

theorem read_T (hE : Encodes blank startSym endSym mark v Text p₁ ts st) :
    Text[st.pos + st.q]? = some (Tape.read ts.Txt) := hE.txt.read_eq

theorem read_P_lt (hE : Encodes blank startSym endSym mark v Text p₁ ts st)
    (hq : st.q < v.length) : v[st.q]? = some (Tape.read ts.P) := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, List.getElem?_append_left hq] at h
  exact h

theorem read_P_end (hE : Encodes blank startSym endSym mark v Text p₁ ts st)
    (hq : st.q = v.length) : Tape.read ts.P = endSym := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, hq,
    List.getElem?_append_right (Nat.le_refl v.length)] at h
  simp at h
  exact h.symm

theorem read_P_ne_end (hend : endSym ∉ v)
    (hE : Encodes blank startSym endSym mark v Text p₁ ts st) (hq : st.q < v.length) :
    Tape.read ts.P ≠ endSym := by
  intro hcon
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 (read_P_lt hE hq)
  exact hend (hcon ▸ h2 ▸ List.getElem_mem h1)

theorem qOf_eq (hE : Encodes blank startSym endSym mark v Text p₁ ts st) :
    qOf ts = st.q := by
  have h := hE.pat.left_eq
  have hlt := hE.pat.lt
  simp only [List.length_cons, List.length_append] at hlt
  unfold qOf
  rw [h, List.length_reverse, List.length_take]
  simp only [List.length_cons, List.length_append]
  omega

theorem p1Of_eq (hE : Encodes blank startSym endSym mark v Text p₁ ts st) :
    p1Of ts = p₁ := by
  have h : ts.Cnt.left = List.replicate p₁ blank ++ [mark] :=
    Tape.StackView.left_eq hE.cnt
  unfold p1Of
  rw [h]
  simp

/-- 走査段の一歩を実現する動作列。分岐は `endSym` の読み取り（`q = |v|`）と
`P`/`Txt` の読み比べ（一致）で決まり、周期条件 `k*p₁ ≤ q ∧ q ≤ r` だけは
オラクルビット `b` で与えられる。 -/
def program (blank endSym mark : Fin sc) (k : ℕ) (b : Bool) (ts : TapesState sc) :
    List (Act sc) :=
  if Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.Txt then
    [Act.P .right, Act.T .right]
  else if b then periodActs blank mark (p1Of ts)
  else resetProgram sc k (qOf ts)

/-! ## 6. 一歩の実現 -/

/-- `program` の第一分岐（テープ読み取り）と `scanStep` の一致分岐は同値。 -/
theorem advance_iff (hend : endSym ∉ v)
    (hE : Encodes blank startSym endSym mark v Text p₁ ts st) (hq : st.q ≤ v.length) :
    (Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.Txt) ↔
      (st.q ≠ v.length ∧ Text[st.pos + st.q]? = v[st.q]?) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hne : st.q ≠ v.length := fun hc => h1 (read_P_end hE hc)
    refine ⟨hne, ?_⟩
    rw [read_T hE, read_P_lt hE (by omega), h2]
  · rintro ⟨h1, h2⟩
    have hlt : st.q < v.length := by omega
    refine ⟨read_P_ne_end hend hE hlt, ?_⟩
    rw [read_T hE, read_P_lt hE hlt] at h2
    exact (Option.some.inj h2).symm

theorem scanStep_adv {k p₁ r : ℕ} (h : st.q ≠ v.length ∧ Text[st.pos + st.q]? = v[st.q]?) :
    scanStep v k p₁ r Text st = ⟨st.pos, st.q + 1⟩ := by
  unfold scanStep
  rw [if_neg h.1, if_pos h.2]

theorem scanStep_shift {k p₁ r : ℕ}
    (h : ¬ (st.q ≠ v.length ∧ Text[st.pos + st.q]? = v[st.q]?)) :
    scanStep v k p₁ r Text st =
      ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ := by
  unfold scanStep
  by_cases h1 : st.q = v.length
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg (fun hc => h ⟨h1, hc⟩)]

/-- **主定理 1（実現）**：`program` の動作列を適用すると、テープは `scanStep` 後の
走査状態を符号化する。 -/
theorem encodes_step {k r : ℕ} {b : Bool} (hk : 0 < k) (hend : endSym ∉ v)
    (hE : Encodes blank startSym endSym mark v Text p₁ ts st)
    (hq : st.q ≤ v.length)
    (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r))
    (hfit : (scanStep v k p₁ r Text st).pos + (scanStep v k p₁ r Text st).q < Text.length) :
    Encodes blank startSym endSym mark v Text p₁
      (applyActs blank (program blank endSym mark k b ts) ts)
      (scanStep v k p₁ r Text st) := by
  by_cases hadv : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.Txt
  · -- 一致：P と Txt を 1 セル右へ
    have habs := (advance_iff hend hE hq).1 hadv
    have hs : scanStep v k p₁ r Text st = ⟨st.pos, st.q + 1⟩ := scanStep_adv habs
    rw [hs] at hfit ⊢
    have hprog : program blank endSym mark k b ts = [Act.P .right, Act.T .right] := by
      unfold program; rw [if_pos hadv]
    rw [hprog]
    have hlt : st.q < v.length := by omega
    refine ⟨?_, ?_, ?_⟩
    · show Tape.SeqView blank (Tape.step blank ts.P ts.P.focus .right) _ (st.q + 1 + 1)
      refine Tape.seq_move_right hE.pat ?_
      simp only [List.length_cons, List.length_append]
      omega
    · show Tape.SeqView blank (Tape.step blank ts.Txt ts.Txt.focus .right) Text
        (st.pos + (st.q + 1))
      have e : st.pos + (st.q + 1) = (st.pos + st.q) + 1 := by omega
      rw [e]
      exact Tape.seq_move_right hE.txt (by omega)
    · exact hE.cnt
  · -- ずらし
    have hs : scanStep v k p₁ r Text st =
        ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ :=
      scanStep_shift (fun hc => hadv ((advance_iff hend hE hq).2 hc))
    rw [hs] at hfit ⊢
    rcases Bool.eq_false_or_eq_true b with hbb | hbb
    · subst hbb
      have hcond : k * p₁ ≤ st.q ∧ st.q ≤ r := of_decide_eq_true hb.symm
      have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
      have hprog : program blank endSym mark k true ts = periodActs blank mark p₁ := by
        unfold program
        rw [if_neg hadv, if_pos rfl, p1Of_eq hE]
      rw [hprog]
      have hgs : gsShift k p₁ r st.q = p₁ := by unfold gsShift; rw [if_pos hcond]
      have hgq : gsNextQ k p₁ r st.q = st.q - p₁ := by unfold gsNextQ; rw [if_pos hcond]
      rw [hgs, hgq]
      have hPp : (applyActs blank (periodActs blank mark p₁) ts).P = leftN blank ts.P p₁ := by
        simp [periodActs, applyActs_append, applyAct, replC_P, perLoop_P]
      have hTp : (applyActs blank (periodActs blank mark p₁) ts).Txt = ts.Txt := by
        simp [periodActs, applyActs_append, applyAct, replC_Txt, perLoop_Txt]
      have hCp : (applyActs blank (periodActs blank mark p₁) ts).Cnt =
          incN blank (Tape.step blank
            (Tape.step blank (decN blank ts.Cnt p₁) blank .left) mark .right) p₁ := by
        simp [periodActs, applyActs_append, applyAct, replC_Cnt, perLoop_Cnt]
      refine ⟨?_, ?_, ?_⟩
      · rw [hPp]
        refine seq_leftN p₁ ts.P (st.q - p₁ + 1) ?_
        rw [show st.q - p₁ + 1 + p₁ = st.q + 1 from by omega]
        exact hE.pat
      · rw [hTp, show st.pos + p₁ + (st.q - p₁) = st.pos + st.q from by omega]
        exact hE.txt
      · rw [hCp]
        have c0 : Tape.CounterView' blank mark (decN blank ts.Cnt p₁) 0 :=
          counter'_decN p₁ ts.Cnt 0 (by simpa using hE.cnt)
        have c2 := counter'_incN p₁ _ 0 (Tape.counter'_dec_zero c0)
        simpa using c2
    · subst hbb
      have hcond : ¬ (k * p₁ ≤ st.q ∧ st.q ≤ r) := of_decide_eq_false hb.symm
      have hprog : program blank endSym mark k false ts = resetProgram sc k st.q := by
        unfold program
        rw [if_neg hadv, if_neg (by simp), qOf_eq hE]
      rw [hprog]
      have hgs : gsShift k p₁ r st.q = max 1 (ceilDiv st.q k) := by
        unfold gsShift; rw [if_neg hcond]
      have hgq : gsNextQ k p₁ r st.q = 0 := by unfold gsNextQ; rw [if_neg hcond]
      rw [hgs, hgq] at hfit ⊢
      dsimp only at hfit
      have hvlen : (startSym :: (v ++ [endSym])).length = v.length + 2 := by
        simp
      rcases Nat.eq_zero_or_pos st.q with hq0 | hq0
      · -- `q = 0`：P は左端を踏んで戻るだけ、Txt は 1 右へ
        have hc0 : ceilDiv st.q k = 0 := by
          rw [hq0]; unfold ceilDiv; exact Nat.div_eq_of_lt (by omega)
        have hprog2 : resetProgram sc k st.q
            = [Act.P .left, Act.P .right, Act.T (sc := sc) .right] := by
          rw [resetProgram, hq0]; simp [resetActs]
        rw [hprog2]
        refine ⟨?_, ?_, hE.cnt⟩
        · have hp1 : Tape.SeqView blank ts.P (startSym :: (v ++ [endSym])) (0 + 1) := by
            rw [show (0 : ℕ) + 1 = st.q + 1 from by omega]
            exact hE.pat
          exact Tape.seq_move_right (Tape.seq_move_left hp1) (by simp only [hvlen]; omega)
        · rw [show st.pos + max 1 (ceilDiv st.q k) + 0 = (st.pos + st.q) + 1 from by
            rw [hc0]; omega]
          exact Tape.seq_move_right hE.txt (by rw [hc0] at hfit; omega)
      · -- `q ≥ 1`：mod `k` スケジュールで歩き、Txt は `q - ⌈q/k⌉` だけ左へ
        have hc1 : 1 ≤ ceilDiv st.q k := ceilDiv_pos hk hq0
        have hc2 : ceilDiv st.q k ≤ st.q := ceilDiv_le_self hk
        have hXP : (applyActs blank (resetActs sc k st.q 0) ts).P = leftN blank ts.P st.q :=
          resetActs_P blank k st.q 0 ts
        have hXT : (applyActs blank (resetActs sc k st.q 0) ts).Txt
            = leftN blank ts.Txt (moves k st.q 0) := resetActs_Txt blank k st.q 0 ts
        have hXC : (applyActs blank (resetActs sc k st.q 0) ts).Cnt = ts.Cnt :=
          resetActs_Cnt blank k st.q 0 ts
        have hprog2 : resetProgram sc k st.q
            = resetActs sc k st.q 0 ++ [Act.P .left, Act.P (sc := sc) .right] := by
          rw [resetProgram, if_neg (by omega : ¬ st.q = 0)]
        rw [hprog2, applyActs_append]
        refine ⟨?_, ?_, ?_⟩
        · have hp1 : Tape.SeqView blank (applyActs blank (resetActs sc k st.q 0) ts).P
              (startSym :: (v ++ [endSym])) (0 + 1) := by
            rw [hXP]
            refine seq_leftN st.q ts.P (0 + 1) ?_
            rw [show 0 + 1 + st.q = st.q + 1 from by omega]
            exact hE.pat
          exact Tape.seq_move_right (Tape.seq_move_left hp1) (by simp only [hvlen]; omega)
        · show Tape.SeqView blank (applyActs blank (resetActs sc k st.q 0) ts).Txt Text _
          rw [show st.pos + max 1 (ceilDiv st.q k) + 0 = st.pos + ceilDiv st.q k from by omega]
          rw [hXT, moves_zero k hk st.q]
          refine seq_leftN _ ts.Txt _ ?_
          rw [show st.pos + ceilDiv st.q k + (st.q - ceilDiv st.q k) = st.pos + st.q from by
            omega]
          exact hE.txt
        · show Tape.CounterView' blank mark (applyActs blank (resetActs sc k st.q 0) ts).Cnt p₁
          rw [hXC]; exact hE.cnt

end Step

/-! ## 7. コスト（償却） -/

section Cost

variable {v Text : List (Fin sc)} {k p₁ r : ℕ} {st : ScanState}

/-- ずらし枝の動作数。 -/
def shiftCost (k p₁ r q : ℕ) : ℕ :=
  if k * p₁ ≤ q ∧ q ≤ r then 4 * p₁ + 2
  else q + (q - ceilDiv q k) + 2 + (if q = 0 then 1 else 0)

/-- 一歩の動作数（`program` の長さ）。 -/
def stepCost (v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) (st : ScanState) : ℕ :=
  if st.q = v.length then shiftCost k p₁ r st.q
  else if Text[st.pos + st.q]? = v[st.q]? then 2
  else shiftCost k p₁ r st.q

/-- **主定理 2a**：動作列の長さは `stepCost`。 -/
theorem program_length {blank startSym endSym mark : Fin sc} {ts : TapesState sc}
    {b : Bool} (hk : 0 < k) (hend : endSym ∉ v)
    (hE : Encodes blank startSym endSym mark v Text p₁ ts st) (hq : st.q ≤ v.length)
    (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r)) :
    (program blank endSym mark k b ts).length = stepCost v k p₁ r Text st := by
  by_cases hadv : Tape.read ts.P ≠ endSym ∧ Tape.read ts.P = Tape.read ts.Txt
  · obtain ⟨h1, h2⟩ := (advance_iff hend hE hq).1 hadv
    have hprog : program blank endSym mark k b ts = [Act.P .right, Act.T .right] := by
      unfold program; rw [if_pos hadv]
    rw [hprog]
    unfold stepCost
    rw [if_neg h1, if_pos h2]
    rfl
  · have hna : ¬ (st.q ≠ v.length ∧ Text[st.pos + st.q]? = v[st.q]?) :=
      fun hc => hadv ((advance_iff hend hE hq).2 hc)
    have hsc : stepCost v k p₁ r Text st = shiftCost k p₁ r st.q := by
      unfold stepCost
      by_cases h1 : st.q = v.length
      · rw [if_pos h1]
      · rw [if_neg h1, if_neg (fun hc => hna ⟨h1, hc⟩)]
    rw [hsc]
    rcases Bool.eq_false_or_eq_true b with hbb | hbb
    · subst hbb
      have hcond : k * p₁ ≤ st.q ∧ st.q ≤ r := of_decide_eq_true hb.symm
      have hprog : program blank endSym mark k true ts = periodActs blank mark p₁ := by
        unfold program; rw [if_neg hadv, if_pos rfl, p1Of_eq hE]
      rw [hprog, periodActs_length]
      unfold shiftCost; rw [if_pos hcond]
    · subst hbb
      have hcond : ¬ (k * p₁ ≤ st.q ∧ st.q ≤ r) := of_decide_eq_false hb.symm
      have hprog : program blank endSym mark k false ts = resetProgram sc k st.q := by
        unfold program; rw [if_neg hadv, if_neg (by simp), qOf_eq hE]
      rw [hprog, resetProgram_length, moves_zero k hk st.q]
      unfold shiftCost; rw [if_neg hcond]

/-- リセットずらしの償却不等式（末尾の `e` は左端検出の定数）。 -/
theorem reset_amortized (hk : 0 < k) (pos q e : ℕ) (he : e ≤ 1) :
    q + (q - ceilDiv q k) + 2 + e ≤
      (2 * k + 2) * ((k + 1) * (pos + max 1 (ceilDiv q k)) + 0 - ((k + 1) * pos + q)) + 8 := by
  obtain ⟨X, hX⟩ : ∃ X, (k + 1) * pos = X := ⟨_, rfl⟩
  have hks : q ≤ k * max 1 (ceilDiv q k) :=
    le_trans (ceilDiv_bounds hk).1 (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right 1 _))
  obtain ⟨A, hA⟩ : ∃ A, k * max 1 (ceilDiv q k) = A := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, max 1 (ceilDiv q k) = s := ⟨_, rfl⟩
  rw [hsdef] at hks hA
  have e1 : (k + 1) * (pos + s) = X + (A + s) := by rw [← hX, ← hA]; ring
  rw [hsdef, e1, hX]
  rw [show X + (A + s) + 0 - (X + q) = A + s - q from by omega]
  obtain ⟨D, hD⟩ : ∃ D, A + s - q = D := ⟨_, rfl⟩
  have hDq : D + q = A + s := by omega
  have e2 : k * D + k * q = k * A + A := by
    calc k * D + k * q = k * (D + q) := by ring
      _ = k * (A + s) := by rw [hDq]
      _ = k * A + k * s := by ring
      _ = k * A + A := by rw [hA]
  have e3 : k * q ≤ k * A := Nat.mul_le_mul (Nat.le_refl k) (by omega)
  have h2 : 2 * (k * D) ≤ (2 * k + 2) * D := by
    calc 2 * (k * D) = (2 * k) * D := by ring
      _ ≤ (2 * k + 2) * D := Nat.mul_le_mul (by omega) (Nat.le_refl D)
  obtain ⟨U, hU⟩ : ∃ U, k * D = U := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, k * q = V := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, k * A = W := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, (2 * k + 2) * D = Z := ⟨_, rfl⟩
  rw [hU, hV, hW] at e2
  rw [hV, hW] at e3
  rw [hU, hZ] at h2
  rw [hD, hZ]
  have hcle : q - ceilDiv q k ≤ q := Nat.sub_le _ _
  omega

/-- ずらし枝のコストはポテンシャルの増分で償却される。 -/
theorem shiftCost_le (hk : 0 < k) (st : ScanState) :
    shiftCost k p₁ r st.q ≤
      (2 * k + 2) *
        (Phi k ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ - Phi k st) + 8 := by
  unfold shiftCost gsShift gsNextQ Phi
  split_ifs with hc hz
  · -- 周期ずらし：増分は `k * p₁`
    have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hc.1
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, k * p₁ = Y := ⟨_, rfl⟩
    have e1 : (k + 1) * (st.pos + p₁) = X + (Y + p₁) := by rw [← hX, ← hY]; ring
    rw [e1, hX]
    rw [show X + (Y + p₁) + (st.q - p₁) - (X + st.q) = Y from by omega]
    have hpY : p₁ ≤ Y := by rw [← hY]; exact Nat.le_mul_of_pos_left p₁ hk
    have h4 : 4 * Y ≤ (2 * k + 2) * Y := Nat.mul_le_mul (by omega) (Nat.le_refl Y)
    obtain ⟨Z, hZ⟩ : ∃ Z, (2 * k + 2) * Y = Z := ⟨_, rfl⟩
    rw [hZ] at h4 ⊢
    omega
  · exact reset_amortized hk st.pos st.q 1 (Nat.le_refl 1)
  · exact reset_amortized hk st.pos st.q 0 (Nat.zero_le 1)

/-- **主定理 2b（償却）**：一歩の動作数はポテンシャルの増分で償却される。 -/
theorem stepCost_le (hk : 0 < k) (v Text : List (Fin sc)) (st : ScanState) :
    stepCost v k p₁ r Text st ≤
      (2 * k + 2) * (Phi k (scanStep v k p₁ r Text st) - Phi k st) + 8 := by
  unfold stepCost scanStep
  split_ifs with h1 h2
  · exact shiftCost_le hk st
  · unfold Phi
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    rw [hX, show X + (st.q + 1) - (X + st.q) = 1 from by omega, Nat.mul_one]
    omega
  · exact shiftCost_le hk st

/-- **主定理 2（コスト）**：動作列の長さはポテンシャルの増分で償却される。
`A = 2k + 2`, `B = 8`。 -/
theorem program_cost {blank startSym endSym mark : Fin sc} {ts : TapesState sc}
    {b : Bool} (hk : 0 < k) (hend : endSym ∉ v)
    (hE : Encodes blank startSym endSym mark v Text p₁ ts st) (hq : st.q ≤ v.length)
    (hb : b = decide (k * p₁ ≤ st.q ∧ st.q ≤ r)) :
    (program blank endSym mark k b ts).length ≤
      (2 * k + 2) * (Phi k (scanStep v k p₁ r Text st) - Phi k st) + 8 := by
  rw [program_length hk hend hE hq hb]
  exact stepCost_le hk v Text st

/-! ### 走査全体のコスト -/

theorem phi_step_le (hk : 0 < k) (hv : 0 < v.length) (hq : st.q ≤ v.length)
    (hstop : st.pos + v.length ≤ Text.length) :
    Phi k (scanStep v k p₁ r Text st) ≤ (k + 1) * Text.length + v.length + 1 := by
  have hsl : gsShift k p₁ r st.q ≤ v.length := by
    unfold gsShift
    split_ifs with hc
    · have h := Nat.le_mul_of_pos_left p₁ hk
      have := hc.1
      omega
    · have h1 : ceilDiv st.q k ≤ st.q := ceilDiv_le_self hk
      omega
  have hnq : gsNextQ k p₁ r st.q ≤ v.length := by
    unfold gsNextQ; split_ifs <;> omega
  have hb1 : (k + 1) * (st.pos + gsShift k p₁ r st.q) ≤ (k + 1) * Text.length :=
    Nat.mul_le_mul (Nat.le_refl _) (by omega)
  have hb2 : (k + 1) * st.pos ≤ (k + 1) * Text.length :=
    Nat.mul_le_mul (Nat.le_refl _) (by omega)
  unfold scanStep Phi
  split_ifs with h1 h2 <;> dsimp only <;> omega

/-- 走査全体の動作数。 -/
def runCost (v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) : ℕ → ScanState → ℕ
  | 0, _ => 0
  | fuel + 1, st =>
      if Text.length < st.pos + v.length then 0
      else stepCost v k p₁ r Text st + runCost v k p₁ r Text fuel (scanStep v k p₁ r Text st)

/-- **系（走査全体のコスト）**：総動作数は `A * ((k+1)|T| + |v| + 1 - Φ) + B * 歩数`。 -/
theorem total_cost (hk : 0 < k) (hp : 0 < p₁) (hv : 0 < v.length) :
    ∀ (fuel : ℕ) (st : ScanState), st.q ≤ v.length →
      runCost v k p₁ r Text fuel st ≤
        (2 * k + 2) * ((k + 1) * Text.length + v.length + 1 - Phi k st) +
          8 * scanSteps v k p₁ r Text fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [runCost, scanSteps]
  | succ fuel ih =>
    intro st hq
    simp only [runCost, scanSteps]
    split_ifs with hstop
    · simp
    · have h1 := stepCost_le (p₁ := p₁) (r := r) hk v Text st
      have h2 := ih (scanStep v k p₁ r Text st) (scanStep_q_le hq)
      have hlt := phi_step_lt (v := v) (T := Text) (p₁ := p₁) (r := r) hk hp st
      have hle := phi_step_le (v := v) (Text := Text) (p₁ := p₁) (r := r) hk hv hq (by omega)
      have hsum : (Phi k (scanStep v k p₁ r Text st) - Phi k st) +
          ((k + 1) * Text.length + v.length + 1 - Phi k (scanStep v k p₁ r Text st)) =
          (k + 1) * Text.length + v.length + 1 - Phi k st := by omega
      have key : (2 * k + 2) * (Phi k (scanStep v k p₁ r Text st) - Phi k st) +
          (2 * k + 2) *
            ((k + 1) * Text.length + v.length + 1 - Phi k (scanStep v k p₁ r Text st)) =
          (2 * k + 2) * ((k + 1) * Text.length + v.length + 1 - Phi k st) := by
        rw [← Nat.mul_add, hsum]
      omega

/-- 初期状態 `⟨0, 0⟩` からの走査全体のコスト（`A = 2k+2`, `B = 8`）。 -/
theorem total_cost_init (hk : 0 < k) (hp : 0 < p₁) (hv : 0 < v.length) (fuel : ℕ) :
    runCost v k p₁ r Text fuel ⟨0, 0⟩ ≤
      (2 * k + 2) * ((k + 1) * Text.length + v.length + 1) +
        8 * scanSteps v k p₁ r Text fuel ⟨0, 0⟩ := by
  have h := total_cost (Text := Text) (p₁ := p₁) (r := r) hk hp hv fuel ⟨0, 0⟩ (by simp)
  have h0 : Phi k (⟨0, 0⟩ : ScanState) = 0 := by simp [Phi]
  rw [h0] at h
  simpa using h

end Cost

/-! ## 9. オラクルビットの除去（テープだけで `k*p₁ ≤ q ∧ q ≤ r` を判定する）

セクション 6 の `program` は周期条件をオラクルビットで受け取っていた。ここでは
それをテープ上に実現する。

* 符号付き量 `q - k*p₁` を **2 本の飽和カウンタ** `Ap = q ∸ k*p₁`, `An = k*p₁ ∸ q` で持つ。
  `An = 0 ↔ k*p₁ ≤ q` はマーカ読み取りで判定できる（`counter'_isZero_iff`）。
* 同様に `Rp = r ∸ q`, `Rn = q ∸ r` を持ち、`Rn = 0 ↔ q ≤ r`。
* `q` の変化はすべて既存の歩行に相乗りする：`+1`（一致）は定数回、`-p₁`（周期ずらし）は
  `p₁` 回のループ、`→ 0`（リセット）は長さ `q` のループ。
* 周期カウンタは `C1`（値 `p₁`）と `C2`（値 `0`）の 2 本にして、下げ／上げを
  **転送**で行う（セクション 6 の `List.replicate p₁ inc` は歩数を有限制御で数える必要が
  あったが、転送なら両方向ともマーカ検出で止まる）。

テープは 8 本：`P, T, C1, C2, Ap, An, Rp, Rn`。
-/

section NoOracle

/-- テープ番号。 -/
def tP : Fin 8 := 0
def tT : Fin 8 := 1
def tC1 : Fin 8 := 2
def tC2 : Fin 8 := 3
def tAp : Fin 8 := 4
def tAn : Fin 8 := 5
def tRp : Fin 8 := 6
def tRn : Fin 8 := 7

/-- 8 本のテープ。 -/
abbrev TapesState' (sc : ℕ) := Fin 8 → TapeConfiguration sc

/-- 1 本のテープへの 1 動作。`keep` は読んだ記号を書き戻して移動する。 -/
inductive Act' (sc : ℕ) where
  | keep : Fin 8 → Move → Act' sc
  | put : Fin 8 → Fin sc → Move → Act' sc

/-- 動作が触るテープ。 -/
def actTape : Act' sc → Fin 8
  | .keep i _ => i
  | .put i _ _ => i

/-- 1 本だけ差し替える。 -/
def upd (ts : TapesState' sc) (i : Fin 8) (tp : TapeConfiguration sc) : TapesState' sc :=
  fun j => if j = i then tp else ts j

@[simp] theorem upd_self (ts : TapesState' sc) (i : Fin 8) (tp : TapeConfiguration sc) :
    upd ts i tp i = tp := by simp [upd]

theorem upd_ne {i j : Fin 8} (ts : TapesState' sc) (tp : TapeConfiguration sc) (h : j ≠ i) :
    upd ts i tp j = ts j := by simp [upd, h]

def applyAct' (blank : Fin sc) (ts : TapesState' sc) : Act' sc → TapesState' sc
  | .keep i m => upd ts i (Tape.step blank (ts i) (ts i).focus m)
  | .put i a m => upd ts i (Tape.step blank (ts i) a m)

def applyActs' (blank : Fin sc) (l : List (Act' sc)) (ts : TapesState' sc) : TapesState' sc :=
  l.foldl (applyAct' blank) ts

@[simp] theorem applyActs'_nil (blank : Fin sc) (ts : TapesState' sc) :
    applyActs' blank [] ts = ts := rfl

@[simp] theorem applyActs'_cons (blank : Fin sc) (a : Act' sc) (l : List (Act' sc))
    (ts : TapesState' sc) :
    applyActs' blank (a :: l) ts = applyActs' blank l (applyAct' blank ts a) := rfl

theorem applyActs'_append (blank : Fin sc) (l₁ l₂ : List (Act' sc)) (ts : TapesState' sc) :
    applyActs' blank (l₁ ++ l₂) ts = applyActs' blank l₂ (applyActs' blank l₁ ts) := by
  simp [applyActs']

theorem applyAct'_put_self (blank : Fin sc) (ts : TapesState' sc) (i : Fin 8) (a : Fin sc)
    (m : Move) : applyAct' blank ts (.put i a m) i = Tape.step blank (ts i) a m :=
  upd_self ..

theorem applyAct'_put_ne (blank : Fin sc) (ts : TapesState' sc) {i j : Fin 8} (a : Fin sc)
    (m : Move) (h : j ≠ i) : applyAct' blank ts (.put i a m) j = ts j := upd_ne _ _ h

theorem applyAct'_keep_self (blank : Fin sc) (ts : TapesState' sc) (i : Fin 8) (m : Move) :
    applyAct' blank ts (.keep i m) i = Tape.step blank (ts i) (ts i).focus m := upd_self ..

theorem applyAct'_keep_ne (blank : Fin sc) (ts : TapesState' sc) {i j : Fin 8} (m : Move)
    (h : j ≠ i) : applyAct' blank ts (.keep i m) j = ts j := upd_ne _ _ h

theorem applyAct'_ne (blank : Fin sc) (ts : TapesState' sc) (a : Act' sc) {j : Fin 8}
    (h : j ≠ actTape a) : applyAct' blank ts a j = ts j := by
  cases a <;> exact upd_ne _ _ h

/-- 触られないテープは変わらない。 -/
theorem applyActs'_untouched (blank : Fin sc) (j : Fin 8) :
    ∀ (l : List (Act' sc)) (ts : TapesState' sc), (∀ a ∈ l, actTape a ≠ j) →
      applyActs' blank l ts j = ts j := by
  intro l
  induction l with
  | nil => intro ts _; rfl
  | cons a l ih =>
    intro ts h
    rw [applyActs'_cons, ih _ (fun b hb => h b (List.mem_cons_of_mem a hb)),
      applyAct'_ne blank ts a (Ne.symm (h a (List.mem_cons_self ..)))]

/-! ### プローブ（カウンタの値を読むが変えない） -/

/-- プローブして書き戻す 2 動作は、スタックビューを持つテープでは恒等。 -/
theorem probe_id {blank : Fin sc} {tp : TapeConfiguration sc} {a : Fin sc} {l : List (Fin sc)}
    (h : Tape.StackView blank tp (a :: l)) :
    Tape.step blank (Tape.step blank tp blank .left)
      (Tape.step blank tp blank .left).focus .right = tp := by
  have hl := h.left_eq
  have hf := h.focus_blank
  rw [Tape.step_left_of_left_cons (a := blank) hl]
  show Tape.step blank (TapeConfiguration.mk l a (blank :: tp.right)) a .right = tp
  rw [Tape.step_right]
  obtain ⟨tl, tf, tr⟩ := tp
  simp only at hl hf
  subst hl
  subst hf
  rfl

theorem counterView'_cons_ex (blank mark : Fin sc) (n : ℕ) :
    ∃ a l, List.replicate n blank ++ [mark] = a :: l := by
  cases n with
  | zero => exact ⟨mark, [], rfl⟩
  | succ m => exact ⟨blank, List.replicate m blank ++ [mark], by rw [List.replicate_succ]; rfl⟩

theorem probe_id' {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) :
    Tape.step blank (Tape.step blank tp blank .left)
      (Tape.step blank tp blank .left).focus .right = tp := by
  obtain ⟨a, l, he⟩ := counterView'_cons_ex blank mark n
  have h' : Tape.StackView blank tp (List.replicate n blank ++ [mark]) := h
  rw [he] at h'
  exact probe_id h'

/-- プローブ動作列（値を読むだけ）。 -/
def probeActs (blank : Fin sc) (j : Fin 8) : List (Act' sc) :=
  [Act'.put j blank .left, Act'.keep j .right]

@[simp] theorem probeActs_length (blank : Fin sc) (j : Fin 8) :
    (probeActs blank j).length = 2 := rfl

theorem probeActs_id {blank mark : Fin sc} {ts : TapesState' sc} {j : Fin 8} {n : ℕ}
    (h : Tape.CounterView' blank mark (ts j) n) :
    applyActs' blank (probeActs blank j) ts = ts := by
  have hstep : applyActs' blank (probeActs blank j) ts
      = applyAct' blank (applyAct' blank ts (Act'.put j blank .left)) (Act'.keep j .right) := rfl
  funext i
  rw [hstep]
  by_cases hi : i = j
  · subst hi
    rw [applyAct'_keep_self, applyAct'_put_self]
    exact probe_id' h
  · rw [applyAct'_keep_ne _ _ _ hi, applyAct'_put_ne _ _ _ _ hi]

/-! ### 符号付きカウンタ対の 1 増加 -/

/-- 対 `(i, j)`（`i` が正部、`j` が負部）が表す符号付き値を 1 増やす動作列。
`j` をプローブし、`0` なら書き戻して `i` を上げ、そうでなければ `j` を下げる。 -/
def sUpActs (blank mark : Fin sc) (i j : Fin 8) (tpj : TapeConfiguration sc) :
    List (Act' sc) :=
  if Tape.read (Tape.step blank tpj blank .left) = mark then
    [Act'.put j blank .left, Act'.keep j .right, Act'.put i blank .right]
  else
    [Act'.put j blank .left, Act'.put j blank .stay]

theorem sUpActs_length_le (blank mark : Fin sc) (i j : Fin 8)
    (tpj : TapeConfiguration sc) : (sUpActs blank mark i j tpj).length ≤ 3 := by
  unfold sUpActs; split_ifs <;> simp

theorem sUpActs_mem {blank mark : Fin sc} {i j : Fin 8} {tpj : TapeConfiguration sc}
    {a : Act' sc} (h : a ∈ sUpActs blank mark i j tpj) :
    actTape a = i ∨ actTape a = j := by
  unfold sUpActs at h
  split_ifs at h with hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [actTape]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [actTape]

theorem sUp_spec {blank mark : Fin sc} (hne : mark ≠ blank) {i j : Fin 8} (hij : i ≠ j)
    {ts : TapesState' sc} {x y : ℕ}
    (hi : Tape.CounterView' blank mark (ts i) x)
    (hj : Tape.CounterView' blank mark (ts j) y) :
    Tape.CounterView' blank mark (applyActs' blank (sUpActs blank mark i j (ts j)) ts i)
        (if y = 0 then x + 1 else x) ∧
      Tape.CounterView' blank mark (applyActs' blank (sUpActs blank mark i j (ts j)) ts j)
        (y - 1) := by
  by_cases hread : Tape.read (Tape.step blank (ts j) blank Move.left) = mark
  · have hy : y = 0 := (Tape.counter'_isZero_iff hne hj).1 hread
    subst hy
    have hlist : sUpActs blank mark i j (ts j)
        = [Act'.put j blank .left, Act'.keep j (sc := sc) .right, Act'.put i blank .right] := by
      unfold sUpActs; rw [if_pos hread]
    rw [hlist]
    have hstep : applyActs' blank
        [Act'.put j blank .left, Act'.keep j (sc := sc) .right, Act'.put i blank .right] ts
        = applyAct' blank
            (applyAct' blank (applyAct' blank ts (Act'.put j blank .left))
              (Act'.keep j .right)) (Act'.put i blank .right) := rfl
    have h2j : (applyAct' blank (applyAct' blank ts (Act'.put j blank .left))
        (Act'.keep j (sc := sc) .right)) j = ts j := by
      rw [applyAct'_keep_self, applyAct'_put_self]
      exact probe_id' hj
    have h2i : (applyAct' blank (applyAct' blank ts (Act'.put j blank .left))
        (Act'.keep j (sc := sc) .right)) i = ts i := by
      rw [applyAct'_keep_ne _ _ _ hij, applyAct'_put_ne _ _ _ _ hij]
    refine ⟨?_, ?_⟩
    · rw [hstep, applyAct'_put_self, h2i]
      simpa using Tape.counter'_inc hi
    · rw [hstep, applyAct'_put_ne _ _ _ _ (Ne.symm hij), h2j]
      simpa using hj
  · have hy : y ≠ 0 := fun hc => hread ((Tape.counter'_isZero_iff hne hj).2 hc)
    obtain ⟨m, rfl⟩ : ∃ m, y = m + 1 := ⟨y - 1, by omega⟩
    have hlist : sUpActs blank mark i j (ts j)
        = [Act'.put j blank .left, Act'.put j blank (sc := sc) .stay] := by
      unfold sUpActs; rw [if_neg hread]
    rw [hlist]
    have hstep : applyActs' blank
        [Act'.put j blank .left, Act'.put j blank (sc := sc) .stay] ts
        = applyAct' blank (applyAct' blank ts (Act'.put j blank .left))
            (Act'.put j blank .stay) := rfl
    refine ⟨?_, ?_⟩
    · rw [hstep, applyAct'_put_ne _ _ _ _ hij, applyAct'_put_ne _ _ _ _ hij]
      simpa using hi
    · rw [hstep, applyAct'_put_self, applyAct'_put_self]
      simpa using Tape.counter'_dec hj

/-! ### カウンタ 4 本の同時更新 -/

theorem sUpActs_untouched (blank mark : Fin sc) (i j : Fin 8) (tpj : TapeConfiguration sc)
    (ts : TapesState' sc) {l : Fin 8} (hi : l ≠ i) (hj : l ≠ j) :
    applyActs' blank (sUpActs blank mark i j tpj) ts l = ts l := by
  refine applyActs'_untouched blank l _ ts (fun a ha => ?_)
  rcases sUpActs_mem ha with h | h
  · rw [h]; exact Ne.symm hi
  · rw [h]; exact Ne.symm hj

/-- カウンタ 4 本のビュー（`m` は `k*p₁`）。 -/
structure CQuad (blank mark : Fin sc) (ts : TapesState' sc) (m r q : ℕ) : Prop where
  ap : Tape.CounterView' blank mark (ts tAp) (q - m)
  an : Tape.CounterView' blank mark (ts tAn) (m - q)
  rp : Tape.CounterView' blank mark (ts tRp) (r - q)
  rn : Tape.CounterView' blank mark (ts tRn) (q - r)

/-- `q ← q + 1` に伴うカウンタ更新。 -/
def qIncActs (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  sUpActs blank mark tAp tAn (ts tAn) ++ sUpActs blank mark tRn tRp (ts tRp)

/-- `q ← q - 1` に伴うカウンタ更新。 -/
def qDecActs (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  sUpActs blank mark tAn tAp (ts tAp) ++ sUpActs blank mark tRp tRn (ts tRn)

theorem qIncActs_length_le (blank mark : Fin sc) (ts : TapesState' sc) :
    (qIncActs blank mark ts).length ≤ 6 := by
  unfold qIncActs
  rw [List.length_append]
  have h1 := sUpActs_length_le blank mark tAp tAn (ts tAn)
  have h2 := sUpActs_length_le blank mark tRn tRp (ts tRp)
  omega

theorem qDecActs_length_le (blank mark : Fin sc) (ts : TapesState' sc) :
    (qDecActs blank mark ts).length ≤ 6 := by
  unfold qDecActs
  rw [List.length_append]
  have h1 := sUpActs_length_le blank mark tAn tAp (ts tAp)
  have h2 := sUpActs_length_le blank mark tRp tRn (ts tRn)
  omega

theorem qIncActs_untouched (blank mark : Fin sc) (ts ts₀ : TapesState' sc) {l : Fin 8}
    (h1 : l ≠ tAp) (h2 : l ≠ tAn) (h3 : l ≠ tRp) (h4 : l ≠ tRn) :
    applyActs' blank (qIncActs blank mark ts₀) ts l = ts l := by
  unfold qIncActs
  rw [applyActs'_append, sUpActs_untouched _ _ _ _ _ _ h4 h3,
    sUpActs_untouched _ _ _ _ _ _ h1 h2]

theorem qDecActs_untouched (blank mark : Fin sc) (ts ts₀ : TapesState' sc) {l : Fin 8}
    (h1 : l ≠ tAp) (h2 : l ≠ tAn) (h3 : l ≠ tRp) (h4 : l ≠ tRn) :
    applyActs' blank (qDecActs blank mark ts₀) ts l = ts l := by
  unfold qDecActs
  rw [applyActs'_append, sUpActs_untouched _ _ _ _ _ _ h3 h4,
    sUpActs_untouched _ _ _ _ _ _ h2 h1]

theorem qIncActs_spec {blank mark : Fin sc} (hne : mark ≠ blank) {ts : TapesState' sc}
    {m r q : ℕ} (h : CQuad blank mark ts m r q) :
    CQuad blank mark (applyActs' blank (qIncActs blank mark ts) ts) m r (q + 1) := by
  unfold qIncActs
  rw [applyActs'_append]
  have hA := sUp_spec hne (by decide : tAp ≠ tAn) h.ap h.an
  have hRp : (applyActs' blank (sUpActs blank mark tAp tAn (ts tAn)) ts) tRp = ts tRp :=
    sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  have hRn : (applyActs' blank (sUpActs blank mark tAp tAn (ts tAn)) ts) tRn = ts tRn :=
    sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  rw [← hRp]
  have hR := sUp_spec hne (by decide : tRn ≠ tRp) (hRn ▸ h.rn) (hRp ▸ h.rp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)]
    have := hA.1
    rw [show (if m - q = 0 then (q - m) + 1 else q - m) = (q + 1) - m from by
      split_ifs <;> omega] at this
    exact this
  · rw [sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)]
    have := hA.2
    rw [show m - q - 1 = m - (q + 1) from by omega] at this
    exact this
  · have := hR.2
    rw [show r - q - 1 = r - (q + 1) from by omega] at this
    exact this
  · have := hR.1
    rw [show (if r - q = 0 then (q - r) + 1 else q - r) = (q + 1) - r from by
      split_ifs <;> omega] at this
    exact this

theorem qDecActs_spec {blank mark : Fin sc} (hne : mark ≠ blank) {ts : TapesState' sc}
    {m r q : ℕ} (hq : 1 ≤ q) (h : CQuad blank mark ts m r q) :
    CQuad blank mark (applyActs' blank (qDecActs blank mark ts) ts) m r (q - 1) := by
  unfold qDecActs
  rw [applyActs'_append]
  have hA := sUp_spec hne (by decide : tAn ≠ tAp) h.an h.ap
  have hRp : (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts) tRp = ts tRp :=
    sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  have hRn : (applyActs' blank (sUpActs blank mark tAn tAp (ts tAp)) ts) tRn = ts tRn :=
    sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)
  rw [← hRn]
  have hR := sUp_spec hne (by decide : tRp ≠ tRn) (hRp ▸ h.rp) (hRn ▸ h.rn)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)]
    have := hA.2
    rw [show q - m - 1 = (q - 1) - m from by omega] at this
    exact this
  · rw [sUpActs_untouched _ _ _ _ _ _ (by decide) (by decide)]
    have := hA.1
    rw [show (if q - m = 0 then (m - q) + 1 else m - q) = m - (q - 1) from by
      split_ifs <;> omega] at this
    exact this
  · have := hR.1
    rw [show (if q - r = 0 then (r - q) + 1 else r - q) = r - (q - 1) from by
      split_ifs <;> omega] at this
    exact this
  · have := hR.2
    rw [show q - r - 1 = (q - 1) - r from by omega] at this
    exact this


/-! ### 一致枝 -/

def advPre : List (Act' sc) := [Act'.keep tP .right, Act'.keep tT .right]

/-- 一致枝の動作列。 -/
def advActs (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  advPre ++ qIncActs blank mark ts

theorem advActs_length_le (blank mark : Fin sc) (ts : TapesState' sc) :
    (advActs blank mark ts).length ≤ 8 := by
  unfold advActs advPre
  rw [List.length_append]
  have := qIncActs_length_le blank mark ts
  simp only [List.length_cons, List.length_nil]
  omega

/-! ### 周期ずらし枝 -/

def perPre (blank : Fin sc) : List (Act' sc) :=
  [Act'.put tC1 blank .left, Act'.put tC1 blank .stay, Act'.put tC2 blank .right,
    Act'.keep tP .left]

/-- 下げループの 1 周：C1 を 1 下げ C2 へ移し、P を 1 左へ、`q` を 1 減らす。 -/
def perDown (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  perPre blank ++ qDecActs blank mark ts

def perLoop1 (blank mark : Fin sc) : ℕ → TapesState' sc → List (Act' sc)
  | 0, _ => []
  | n + 1, ts =>
      perDown blank mark ts ++
        perLoop1 blank mark n (applyActs' blank (perDown blank mark ts) ts)

/-- 上げループ（C2 → C1 の転送）。状態に依存しない。 -/
def perUp (blank : Fin sc) : ℕ → List (Act' sc)
  | 0 => []
  | n + 1 =>
      Act'.put tC2 blank .left :: Act'.put tC2 blank .stay :: Act'.put tC1 blank .right ::
        perUp blank n

def perProgram (blank mark : Fin sc) (n : ℕ) (ts : TapesState' sc) : List (Act' sc) :=
  perLoop1 blank mark n ts ++ probeActs blank tC1 ++ perUp blank n ++ probeActs blank tC2

theorem perDown_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w : List (Fin sc)}
    {ts : TapesState' sc} {qq cc dd m r : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (ts tP) w (qq + 1))
    (h1 : Tape.CounterView' blank mark (ts tC1) (cc + 1))
    (h2 : Tape.CounterView' blank mark (ts tC2) dd)
    (hQ : CQuad blank mark ts m r qq) :
    Tape.SeqView blank (applyActs' blank (perDown blank mark ts) ts tP) w (qq - 1 + 1) ∧
      Tape.CounterView' blank mark (applyActs' blank (perDown blank mark ts) ts tC1) cc ∧
      Tape.CounterView' blank mark (applyActs' blank (perDown blank mark ts) ts tC2) (dd + 1) ∧
      CQuad blank mark (applyActs' blank (perDown blank mark ts) ts) m r (qq - 1) ∧
      applyActs' blank (perDown blank mark ts) ts tT = ts tT := by
  have eP : applyActs' blank (perPre blank) ts tP
      = Tape.step blank (ts tP) (ts tP).focus .left := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2]
  have eT : applyActs' blank (perPre blank) ts tT = ts tT := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2, tT]
  have e1 : applyActs' blank (perPre blank) ts tC1
      = Tape.step blank (Tape.step blank (ts tC1) blank .left) blank .stay := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2]
  have e2 : applyActs' blank (perPre blank) ts tC2
      = Tape.step blank (ts tC2) blank .right := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2]
  have eAp : applyActs' blank (perPre blank) ts tAp = ts tAp := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2, tAp]
  have eAn : applyActs' blank (perPre blank) ts tAn = ts tAn := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2, tAn]
  have eRp : applyActs' blank (perPre blank) ts tRp = ts tRp := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2, tRp]
  have eRn : applyActs' blank (perPre blank) ts tRn = ts tRn := by
    simp [perPre, applyActs', applyAct', upd, tP, tC1, tC2, tRn]
  have hQ1 : CQuad blank mark (applyActs' blank (perPre blank) ts) m r qq :=
    ⟨by rw [eAp]; exact hQ.ap, by rw [eAn]; exact hQ.an, by rw [eRp]; exact hQ.rp,
      by rw [eRn]; exact hQ.rn⟩
  have hlist : qDecActs blank mark ts
      = qDecActs blank mark (applyActs' blank (perPre blank) ts) := by
    unfold qDecActs; rw [eAp, eRn]
  unfold perDown
  rw [applyActs'_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eP]
    refine Tape.seq_move_left ?_
    rw [show qq - 1 + 1 + 1 = qq + 1 from by omega]
    exact hP
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e1]
    exact Tape.counter'_dec h1
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e2]
    exact Tape.counter'_inc h2
  · rw [hlist]
    exact qDecActs_spec hne hqq hQ1
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eT]

theorem perLoop1_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w : List (Fin sc)} :
    ∀ (n : ℕ) (ts : TapesState' sc) (qq cc dd m r : ℕ), n ≤ qq → n ≤ cc →
      Tape.SeqView blank (ts tP) w (qq + 1) →
      Tape.CounterView' blank mark (ts tC1) cc →
      Tape.CounterView' blank mark (ts tC2) dd →
      CQuad blank mark ts m r qq →
      Tape.SeqView blank (applyActs' blank (perLoop1 blank mark n ts) ts tP) w (qq - n + 1) ∧
        Tape.CounterView' blank mark
          (applyActs' blank (perLoop1 blank mark n ts) ts tC1) (cc - n) ∧
        Tape.CounterView' blank mark
          (applyActs' blank (perLoop1 blank mark n ts) ts tC2) (dd + n) ∧
        CQuad blank mark (applyActs' blank (perLoop1 blank mark n ts) ts) m r (qq - n) ∧
        applyActs' blank (perLoop1 blank mark n ts) ts tT = ts tT := by
  intro n
  induction n with
  | zero => intro ts qq cc dd m r _ _ hP h1 h2 hQ; exact ⟨hP, h1, h2, hQ, rfl⟩
  | succ n ih =>
    intro ts qq cc dd m r hnq hnc hP h1 h2 hQ
    obtain ⟨c', rfl⟩ : ∃ c', cc = c' + 1 := ⟨cc - 1, by omega⟩
    obtain ⟨hP', h1', h2', hQ', hT'⟩ := perDown_spec hne (by omega) hP h1 h2 hQ
    have := ih (applyActs' blank (perDown blank mark ts) ts) (qq - 1) c' (dd + 1) m r
      (by omega) (by omega) hP' h1' h2' hQ'
    show _ ∧ _ ∧ _ ∧ _ ∧ _
    rw [perLoop1, applyActs'_append]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
    · rw [show c' + 1 - (n + 1) = c' - n from by omega]; exact this.2.1
    · rw [show dd + (n + 1) = dd + 1 + n from by omega]; exact this.2.2.1
    · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.2.1
    · rw [this.2.2.2.2, hT']

theorem perUp_mem {blank : Fin sc} : ∀ (n : ℕ) (a : Act' sc), a ∈ perUp blank n →
    actTape a = tC1 ∨ actTape a = tC2 := by
  intro n
  induction n with
  | zero => intro a ha; simp [perUp] at ha
  | succ n ih =>
    intro a ha
    rw [perUp] at ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Or.inr rfl
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Or.inr rfl
    rcases List.mem_cons.1 ha with rfl | ha
    · exact Or.inl rfl
    exact ih a ha

theorem perUp_untouched {blank : Fin sc} (n : ℕ) (ts : TapesState' sc) {l : Fin 8}
    (h1 : l ≠ tC1) (h2 : l ≠ tC2) : applyActs' blank (perUp blank n) ts l = ts l := by
  refine applyActs'_untouched blank l _ ts (fun a ha => ?_)
  rcases perUp_mem n a ha with h | h
  · rw [h]; exact Ne.symm h1
  · rw [h]; exact Ne.symm h2

theorem perUp_spec {blank mark : Fin sc} : ∀ (n : ℕ) (ts : TapesState' sc) (cc dd : ℕ),
    n ≤ dd → Tape.CounterView' blank mark (ts tC1) cc →
    Tape.CounterView' blank mark (ts tC2) dd →
    Tape.CounterView' blank mark (applyActs' blank (perUp blank n) ts tC1) (cc + n) ∧
      Tape.CounterView' blank mark (applyActs' blank (perUp blank n) ts tC2) (dd - n) := by
  intro n
  induction n with
  | zero => intro ts cc dd _ h1 h2; exact ⟨by simpa [perUp] using h1, by simpa [perUp] using h2⟩
  | succ n ih =>
    intro ts cc dd hnd h1 h2
    obtain ⟨d', rfl⟩ : ∃ d', dd = d' + 1 := ⟨dd - 1, by omega⟩
    have e1 : applyActs' blank
        [Act'.put tC2 blank .left, Act'.put tC2 blank .stay, Act'.put tC1 blank (sc := sc) .right]
        ts tC1 = Tape.step blank (ts tC1) blank .right := by
      simp [applyActs', applyAct', upd, tC1, tC2]
    have e2 : applyActs' blank
        [Act'.put tC2 blank .left, Act'.put tC2 blank .stay, Act'.put tC1 blank (sc := sc) .right]
        ts tC2 = Tape.step blank (Tape.step blank (ts tC2) blank .left) blank .stay := by
      simp [applyActs', applyAct', upd, tC1, tC2]
    have hstep : perUp blank (n + 1) =
        [Act'.put tC2 blank .left, Act'.put tC2 blank .stay,
          Act'.put tC1 blank (sc := sc) .right] ++ perUp blank n := rfl
    rw [hstep, applyActs'_append]
    have := ih (applyActs' blank
        [Act'.put tC2 blank .left, Act'.put tC2 blank .stay, Act'.put tC1 blank (sc := sc) .right]
        ts) (cc + 1) d' (by omega) (by rw [e1]; exact Tape.counter'_inc h1)
      (by rw [e2]; exact Tape.counter'_dec h2)
    refine ⟨?_, ?_⟩
    · rw [show cc + (n + 1) = cc + 1 + n from by omega]; exact this.1
    · rw [show d' + 1 - (n + 1) = d' - n from by omega]; exact this.2

theorem perLoop1_length_le {blank mark : Fin sc} : ∀ (n : ℕ) (ts : TapesState' sc),
    (perLoop1 blank mark n ts).length ≤ 10 * n := by
  intro n
  induction n with
  | zero => intro ts; simp [perLoop1]
  | succ n ih =>
    intro ts
    rw [perLoop1, List.length_append]
    have h1 : (perDown blank mark ts).length ≤ 10 := by
      unfold perDown perPre
      rw [List.length_append]
      have := qDecActs_length_le blank mark ts
      simp only [List.length_cons, List.length_nil]
      omega
    have h2 := ih (applyActs' blank (perDown blank mark ts) ts)
    omega

@[simp] theorem perUp_length {blank : Fin sc} (n : ℕ) : (perUp blank n).length = 3 * n := by
  induction n with
  | zero => simp [perUp]
  | succ n ih => rw [perUp]; simp only [List.length_cons, ih]; omega

theorem perProgram_length_le {blank mark : Fin sc} (n : ℕ) (ts : TapesState' sc) :
    (perProgram blank mark n ts).length ≤ 13 * n + 4 := by
  unfold perProgram
  simp only [List.length_append, probeActs_length, perUp_length]
  have := perLoop1_length_le (blank := blank) (mark := mark) n ts
  omega


/-! ### リセットずらし枝 -/

/-- `T` を止める周（位相 `0`）。 -/
def resDown1 (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  [Act'.keep tP .left] ++ qDecActs blank mark ts

/-- `T` も左へ動かす周。 -/
def resDown2 (blank mark : Fin sc) (ts : TapesState' sc) : List (Act' sc) :=
  [Act'.keep tP .left, Act'.keep tT .left] ++ qDecActs blank mark ts

def resLoop (blank mark : Fin sc) (k : ℕ) : ℕ → ℕ → TapesState' sc → List (Act' sc)
  | 0, _, _ => []
  | n + 1, 0, ts =>
      resDown1 blank mark ts ++
        resLoop blank mark k n (k - 1) (applyActs' blank (resDown1 blank mark ts) ts)
  | n + 1, c + 1, ts =>
      resDown2 blank mark ts ++
        resLoop blank mark k n c (applyActs' blank (resDown2 blank mark ts) ts)

def resProgram (blank mark : Fin sc) (k q : ℕ) (ts : TapesState' sc) : List (Act' sc) :=
  resLoop blank mark k q 0 ts ++ Act'.keep tP .left :: Act'.keep tP .right ::
    (if q = 0 then [Act'.keep tT (sc := sc) .right] else [])

theorem resDown1_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w : List (Fin sc)}
    {ts : TapesState' sc} {qq m r : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (ts tP) w (qq + 1)) (hQ : CQuad blank mark ts m r qq) :
    Tape.SeqView blank (applyActs' blank (resDown1 blank mark ts) ts tP) w (qq - 1 + 1) ∧
      CQuad blank mark (applyActs' blank (resDown1 blank mark ts) ts) m r (qq - 1) ∧
      applyActs' blank (resDown1 blank mark ts) ts tT = ts tT ∧
      applyActs' blank (resDown1 blank mark ts) ts tC1 = ts tC1 ∧
      applyActs' blank (resDown1 blank mark ts) ts tC2 = ts tC2 := by
  have eP : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tP
      = Tape.step blank (ts tP) (ts tP).focus .left := by
    simp [applyActs', applyAct', upd, tP]
  have eT : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tT = ts tT := by
    simp [applyActs', applyAct', upd, tP, tT]
  have e1 : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tC1 = ts tC1 := by
    simp [applyActs', applyAct', upd, tP, tC1]
  have e2 : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tC2 = ts tC2 := by
    simp [applyActs', applyAct', upd, tP, tC2]
  have eAp : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tAp = ts tAp := by
    simp [applyActs', applyAct', upd, tP, tAp]
  have eAn : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tAn = ts tAn := by
    simp [applyActs', applyAct', upd, tP, tAn]
  have eRp : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tRp = ts tRp := by
    simp [applyActs', applyAct', upd, tP, tRp]
  have eRn : applyActs' blank [Act'.keep tP (sc := sc) .left] ts tRn = ts tRn := by
    simp [applyActs', applyAct', upd, tP, tRn]
  have hQ1 : CQuad blank mark (applyActs' blank [Act'.keep tP (sc := sc) .left] ts) m r qq :=
    ⟨by rw [eAp]; exact hQ.ap, by rw [eAn]; exact hQ.an, by rw [eRp]; exact hQ.rp,
      by rw [eRn]; exact hQ.rn⟩
  have hlist : qDecActs blank mark ts
      = qDecActs blank mark (applyActs' blank [Act'.keep tP (sc := sc) .left] ts) := by
    unfold qDecActs; rw [eAp, eRn]
  unfold resDown1
  rw [applyActs'_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eP]
    refine Tape.seq_move_left ?_
    rw [show qq - 1 + 1 + 1 = qq + 1 from by omega]
    exact hP
  · rw [hlist]; exact qDecActs_spec hne hqq hQ1
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eT]
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e1]
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e2]

theorem resDown2_spec {blank mark : Fin sc} (hne : mark ≠ blank) {w Text : List (Fin sc)}
    {ts : TapesState' sc} {qq ii m r : ℕ} (hqq : 1 ≤ qq)
    (hP : Tape.SeqView blank (ts tP) w (qq + 1))
    (hT : Tape.SeqView blank (ts tT) Text (ii + 1))
    (hQ : CQuad blank mark ts m r qq) :
    Tape.SeqView blank (applyActs' blank (resDown2 blank mark ts) ts tP) w (qq - 1 + 1) ∧
      Tape.SeqView blank (applyActs' blank (resDown2 blank mark ts) ts tT) Text ii ∧
      CQuad blank mark (applyActs' blank (resDown2 blank mark ts) ts) m r (qq - 1) ∧
      applyActs' blank (resDown2 blank mark ts) ts tC1 = ts tC1 ∧
      applyActs' blank (resDown2 blank mark ts) ts tC2 = ts tC2 := by
  have eP : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tP
      = Tape.step blank (ts tP) (ts tP).focus .left := by
    simp [applyActs', applyAct', upd, tP, tT]
  have eT : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tT
      = Tape.step blank (ts tT) (ts tT).focus .left := by
    simp [applyActs', applyAct', upd, tP, tT]
  have e1 : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tC1
      = ts tC1 := by simp [applyActs', applyAct', upd, tP, tT, tC1]
  have e2 : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tC2
      = ts tC2 := by simp [applyActs', applyAct', upd, tP, tT, tC2]
  have eAp : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tAp
      = ts tAp := by simp [applyActs', applyAct', upd, tP, tT, tAp]
  have eAn : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tAn
      = ts tAn := by simp [applyActs', applyAct', upd, tP, tT, tAn]
  have eRp : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tRp
      = ts tRp := by simp [applyActs', applyAct', upd, tP, tT, tRp]
  have eRn : applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts tRn
      = ts tRn := by simp [applyActs', applyAct', upd, tP, tT, tRn]
  have hQ1 : CQuad blank mark
      (applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts) m r qq :=
    ⟨by rw [eAp]; exact hQ.ap, by rw [eAn]; exact hQ.an, by rw [eRp]; exact hQ.rp,
      by rw [eRn]; exact hQ.rn⟩
  have hlist : qDecActs blank mark ts
      = qDecActs blank mark
        (applyActs' blank [Act'.keep tP .left, Act'.keep tT (sc := sc) .left] ts) := by
    unfold qDecActs; rw [eAp, eRn]
  unfold resDown2
  rw [applyActs'_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eP]
    refine Tape.seq_move_left ?_
    rw [show qq - 1 + 1 + 1 = qq + 1 from by omega]
    exact hP
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eT]
    exact Tape.seq_move_left hT
  · rw [hlist]; exact qDecActs_spec hne hqq hQ1
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e1]
  · rw [qDecActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e2]

theorem resLoop_spec {blank mark : Fin sc} (hne : mark ≠ blank)
    {w Text : List (Fin sc)} (k : ℕ) :
    ∀ (n c : ℕ) (ts : TapesState' sc) (qq ii m r : ℕ), n ≤ qq →
      Tape.SeqView blank (ts tP) w (qq + 1) →
      Tape.SeqView blank (ts tT) Text (ii + moves k n c) →
      CQuad blank mark ts m r qq →
      Tape.SeqView blank (applyActs' blank (resLoop blank mark k n c ts) ts tP) w
          (qq - n + 1) ∧
        Tape.SeqView blank (applyActs' blank (resLoop blank mark k n c ts) ts tT) Text ii ∧
        CQuad blank mark (applyActs' blank (resLoop blank mark k n c ts) ts) m r (qq - n) ∧
        applyActs' blank (resLoop blank mark k n c ts) ts tC1 = ts tC1 ∧
        applyActs' blank (resLoop blank mark k n c ts) ts tC2 = ts tC2 := by
  intro n
  induction n with
  | zero =>
    intro c ts qq ii m r _ hP hT hQ
    exact ⟨hP, by simpa [moves, resLoop] using hT, hQ, rfl, rfl⟩
  | succ n ih =>
    intro c ts qq ii m r hnq hP hT hQ
    cases c with
    | zero =>
      obtain ⟨hP', hQ', hT', h1', h2'⟩ := resDown1_spec hne (by omega) hP hQ
      have hTT : Tape.SeqView blank
          (applyActs' blank (resDown1 blank mark ts) ts tT) Text (ii + moves k n (k - 1)) := by
        rw [hT']
        simpa [moves] using hT
      have := ih (k - 1) (applyActs' blank (resDown1 blank mark ts) ts) (qq - 1) ii m r
        (by omega) hP' hTT hQ'
      rw [resLoop, applyActs'_append]
      refine ⟨?_, this.2.1, ?_, ?_, ?_⟩
      · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
      · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
      · rw [this.2.2.2.1, h1']
      · rw [this.2.2.2.2, h2']
    | succ c =>
      have hT1 : Tape.SeqView blank (ts tT) Text ((ii + moves k n c) + 1) := by
        rw [show ii + moves k n c + 1 = ii + moves k (n + 1) (c + 1) from by
          simp only [moves]; omega]
        exact hT
      obtain ⟨hP', hT', hQ', h1', h2'⟩ := resDown2_spec hne (by omega) hP hT1 hQ
      have := ih c (applyActs' blank (resDown2 blank mark ts) ts) (qq - 1) ii m r
        (by omega) hP' hT' hQ'
      rw [resLoop, applyActs'_append]
      refine ⟨?_, this.2.1, ?_, ?_, ?_⟩
      · rw [show qq - (n + 1) + 1 = qq - 1 - n + 1 from by omega]; exact this.1
      · rw [show qq - (n + 1) = qq - 1 - n from by omega]; exact this.2.2.1
      · rw [this.2.2.2.1, h1']
      · rw [this.2.2.2.2, h2']

theorem resLoop_length_le {blank mark : Fin sc} (k : ℕ) :
    ∀ (n c : ℕ) (ts : TapesState' sc), (resLoop blank mark k n c ts).length ≤ 8 * n := by
  intro n
  induction n with
  | zero => intro c ts; simp [resLoop]
  | succ n ih =>
    intro c ts
    have hd1 : ∀ ts', (resDown1 blank mark ts').length ≤ 8 := by
      intro ts'
      unfold resDown1
      rw [List.length_append]
      have := qDecActs_length_le blank mark ts'
      simp only [List.length_cons, List.length_nil]
      omega
    have hd2 : ∀ ts', (resDown2 blank mark ts').length ≤ 8 := by
      intro ts'
      unfold resDown2
      rw [List.length_append]
      have := qDecActs_length_le blank mark ts'
      simp only [List.length_cons, List.length_nil]
      omega
    cases c with
    | zero =>
      rw [resLoop, List.length_append]
      have := ih (k - 1) (applyActs' blank (resDown1 blank mark ts) ts)
      have := hd1 ts
      omega
    | succ c =>
      rw [resLoop, List.length_append]
      have := ih c (applyActs' blank (resDown2 blank mark ts) ts)
      have := hd2 ts
      omega

theorem resProgram_length_le {blank mark : Fin sc} (k q : ℕ) (ts : TapesState' sc) :
    (resProgram blank mark k q ts).length ≤ 8 * q + 3 := by
  unfold resProgram
  rw [List.length_append]
  have := resLoop_length_le (blank := blank) (mark := mark) k q 0 ts
  split_ifs <;> simp <;> omega


/-! ### 符号化とプログラム（オラクル無し） -/

def qOf' (ts : TapesState' sc) : ℕ := (ts tP).left.length - 1
def p1Of' (ts : TapesState' sc) : ℕ := (ts tC1).left.length - 1

/-- テープ状態が走査状態を符号化していること（オラクル無し版）。 -/
structure Encodes' (blank startSym endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r : ℕ) (ts : TapesState' sc) (st : ScanState) : Prop where
  pat : Tape.SeqView blank (ts tP) (startSym :: (v ++ [endSym])) (st.q + 1)
  txt : Tape.SeqView blank (ts tT) Text (st.pos + st.q)
  c1 : Tape.CounterView' blank mark (ts tC1) p₁
  c2 : Tape.CounterView' blank mark (ts tC2) 0
  quad : CQuad blank mark ts (k * p₁) r st.q

/-- 一歩を実現する動作列。分岐はすべてテープ読み取りで決まる。 -/
def program' (blank endSym mark : Fin sc) (k : ℕ) (ts : TapesState' sc) : List (Act' sc) :=
  if Tape.read (ts tP) ≠ endSym ∧ Tape.read (ts tP) = Tape.read (ts tT) then
    advActs blank mark ts
  else
    probeActs blank tAn ++ probeActs blank tRn ++
      (if Tape.read (Tape.step blank (ts tAn) blank .left) = mark ∧
           Tape.read (Tape.step blank (ts tRn) blank .left) = mark then
        perProgram blank mark (p1Of' ts) ts
      else resProgram blank mark k (qOf' ts) ts)

section StepNo

variable {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)} {k p₁ r : ℕ}
  {ts : TapesState' sc} {st : ScanState}

theorem read_T' (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) :
    Text[st.pos + st.q]? = some (Tape.read (ts tT)) := hE.txt.read_eq

theorem read_P_lt' (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st)
    (hq : st.q < v.length) : v[st.q]? = some (Tape.read (ts tP)) := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, List.getElem?_append_left hq] at h
  exact h

theorem read_P_end' (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st)
    (hq : st.q = v.length) : Tape.read (ts tP) = endSym := by
  have h := hE.pat.read_eq
  rw [List.getElem?_cons_succ, hq,
    List.getElem?_append_right (Nat.le_refl v.length)] at h
  simp at h
  exact h.symm

theorem read_P_ne_end' (hend : endSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q < v.length) :
    Tape.read (ts tP) ≠ endSym := by
  intro hcon
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 (read_P_lt' hE hq)
  exact hend (hcon ▸ h2 ▸ List.getElem_mem h1)

theorem advance_iff' (hend : endSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length) :
    (Tape.read (ts tP) ≠ endSym ∧ Tape.read (ts tP) = Tape.read (ts tT)) ↔
      (st.q ≠ v.length ∧ Text[st.pos + st.q]? = v[st.q]?) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hne : st.q ≠ v.length := fun hc => h1 (read_P_end' hE hc)
    refine ⟨hne, ?_⟩
    rw [read_T' hE, read_P_lt' hE (by omega), h2]
  · rintro ⟨h1, h2⟩
    have hlt : st.q < v.length := by omega
    refine ⟨read_P_ne_end' hend hE hlt, ?_⟩
    rw [read_T' hE, read_P_lt' hE hlt] at h2
    exact (Option.some.inj h2).symm

/-- 周期条件はカウンタのマーカ読み取りで決まる。 -/
theorem period_iff' (hne : mark ≠ blank)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) :
    (Tape.read (Tape.step blank (ts tAn) blank .left) = mark ∧
      Tape.read (Tape.step blank (ts tRn) blank .left) = mark) ↔
      (k * p₁ ≤ st.q ∧ st.q ≤ r) := by
  rw [Tape.counter'_isZero_iff hne hE.quad.an, Tape.counter'_isZero_iff hne hE.quad.rn]
  constructor
  · rintro ⟨h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; omega

theorem qOf'_eq (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) :
    qOf' ts = st.q := by
  have h := hE.pat.left_eq
  have hlt := hE.pat.lt
  simp only [List.length_cons, List.length_append] at hlt
  unfold qOf'
  rw [h, List.length_reverse, List.length_take]
  simp only [List.length_cons, List.length_append]
  omega

theorem p1Of'_eq (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) :
    p1Of' ts = p₁ := by
  have h : (ts tC1).left = List.replicate p₁ blank ++ [mark] :=
    Tape.StackView.left_eq hE.c1
  unfold p1Of'
  rw [h]
  simp

/-- **主定理 1'（実現、オラクル無し）**。 -/
theorem encodes_step' (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st)
    (hq : st.q ≤ v.length)
    (hfit : (scanStep v k p₁ r Text st).pos + (scanStep v k p₁ r Text st).q < Text.length) :
    Encodes' blank startSym endSym mark v Text k p₁ r
      (applyActs' blank (program' blank endSym mark k ts) ts)
      (scanStep v k p₁ r Text st) := by
  have hvlen : (startSym :: (v ++ [endSym])).length = v.length + 2 := by simp
  by_cases hadv : Tape.read (ts tP) ≠ endSym ∧ Tape.read (ts tP) = Tape.read (ts tT)
  · -- 一致枝
    have hs : scanStep v k p₁ r Text st = ⟨st.pos, st.q + 1⟩ :=
      scanStep_adv ((advance_iff' hend hE hq).1 hadv)
    have hlt : st.q < v.length := ((advance_iff' hend hE hq).1 hadv).1.lt_of_le hq
    rw [hs] at hfit ⊢
    dsimp only at hfit
    have hprog : program' blank endSym mark k ts = advActs blank mark ts := by
      unfold program'; rw [if_pos hadv]
    rw [hprog]
    unfold advActs
    rw [applyActs'_append]
    have eP : applyActs' blank (advPre (sc := sc)) ts tP
        = Tape.step blank (ts tP) (ts tP).focus .right := by
      simp [advPre, applyActs', applyAct', upd, tP, tT]
    have eT : applyActs' blank (advPre (sc := sc)) ts tT
        = Tape.step blank (ts tT) (ts tT).focus .right := by
      simp [advPre, applyActs', applyAct', upd, tP, tT]
    have e1 : applyActs' blank (advPre (sc := sc)) ts tC1 = ts tC1 := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tC1]
    have e2 : applyActs' blank (advPre (sc := sc)) ts tC2 = ts tC2 := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tC2]
    have eAp : applyActs' blank (advPre (sc := sc)) ts tAp = ts tAp := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tAp]
    have eAn : applyActs' blank (advPre (sc := sc)) ts tAn = ts tAn := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tAn]
    have eRp : applyActs' blank (advPre (sc := sc)) ts tRp = ts tRp := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tRp]
    have eRn : applyActs' blank (advPre (sc := sc)) ts tRn = ts tRn := by
      simp [advPre, applyActs', applyAct', upd, tP, tT, tRn]
    have hQ1 : CQuad blank mark (applyActs' blank (advPre (sc := sc)) ts) (k * p₁) r st.q :=
      ⟨by rw [eAp]; exact hE.quad.ap, by rw [eAn]; exact hE.quad.an,
        by rw [eRp]; exact hE.quad.rp, by rw [eRn]; exact hE.quad.rn⟩
    have hlist : qIncActs blank mark ts
        = qIncActs blank mark (applyActs' blank (advPre (sc := sc)) ts) := by
      unfold qIncActs; rw [eAn, eRp]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [qIncActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eP]
      refine Tape.seq_move_right hE.pat ?_
      simp only [hvlen]
      omega
    · rw [qIncActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), eT]
      rw [show st.pos + (st.q + 1) = (st.pos + st.q) + 1 from by omega]
      exact Tape.seq_move_right hE.txt (by omega)
    · rw [qIncActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e1]
      exact hE.c1
    · rw [qIncActs_untouched _ _ _ _ (by decide) (by decide) (by decide) (by decide), e2]
      exact hE.c2
    · rw [hlist]; exact qIncActs_spec hne hQ1
  · -- ずらし枝
    have hs : scanStep v k p₁ r Text st =
        ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ :=
      scanStep_shift (fun hc => hadv ((advance_iff' hend hE hq).2 hc))
    rw [hs] at hfit ⊢
    dsimp only at hfit
    have hprobe : ∀ X : List (Act' sc),
        applyActs' blank (probeActs blank tAn ++ probeActs blank tRn ++ X) ts
          = applyActs' blank X ts := by
      intro X
      rw [applyActs'_append, applyActs'_append, probeActs_id hE.quad.an,
        probeActs_id hE.quad.rn]
    have hprog : program' blank endSym mark k ts =
        probeActs blank tAn ++ probeActs blank tRn ++
          (if Tape.read (Tape.step blank (ts tAn) blank .left) = mark ∧
               Tape.read (Tape.step blank (ts tRn) blank .left) = mark then
            perProgram blank mark (p1Of' ts) ts
          else resProgram blank mark k (qOf' ts) ts) := by
      unfold program'; rw [if_neg hadv]
    rw [hprog, hprobe]
    by_cases hcond : k * p₁ ≤ st.q ∧ st.q ≤ r
    · -- 周期ずらし
      rw [if_pos ((period_iff' hne hE).2 hcond), p1Of'_eq hE]
      have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
      have hgs : gsShift k p₁ r st.q = p₁ := by unfold gsShift; rw [if_pos hcond]
      have hgq : gsNextQ k p₁ r st.q = st.q - p₁ := by unfold gsNextQ; rw [if_pos hcond]
      rw [hgs, hgq]
      unfold perProgram
      rw [applyActs'_append, applyActs'_append, applyActs'_append]
      obtain ⟨lP, l1, l2, lQ, lT⟩ := perLoop1_spec (w := startSym :: (v ++ [endSym])) hne
        p₁ ts st.q p₁ 0 (k * p₁) r hle (Nat.le_refl _) hE.pat hE.c1 hE.c2 hE.quad
      rw [show p₁ - p₁ = 0 from by omega] at l1
      rw [show (0 : ℕ) + p₁ = p₁ from by omega] at l2
      rw [probeActs_id l1]
      obtain ⟨u1, u2⟩ := perUp_spec (mark := mark) p₁
        (applyActs' blank (perLoop1 blank mark p₁ ts) ts) 0 p₁ (Nat.le_refl _) l1 l2
      rw [show (0 : ℕ) + p₁ = p₁ from by omega] at u1
      rw [show p₁ - p₁ = 0 from by omega] at u2
      rw [probeActs_id u2]
      refine ⟨?_, ?_, u1, u2, ?_⟩
      · rw [perUp_untouched _ _ (by decide) (by decide)]
        rw [show st.q - p₁ + 1 = st.q - p₁ + 1 from rfl]
        exact lP
      · rw [perUp_untouched _ _ (by decide) (by decide), lT,
          show st.pos + p₁ + (st.q - p₁) = st.pos + st.q from by omega]
        exact hE.txt
      · exact ⟨by rw [perUp_untouched _ _ (by decide) (by decide)]; exact lQ.ap,
          by rw [perUp_untouched _ _ (by decide) (by decide)]; exact lQ.an,
          by rw [perUp_untouched _ _ (by decide) (by decide)]; exact lQ.rp,
          by rw [perUp_untouched _ _ (by decide) (by decide)]; exact lQ.rn⟩
    · -- リセットずらし
      rw [if_neg (fun hc => hcond ((period_iff' hne hE).1 hc)), qOf'_eq hE]
      have hgs : gsShift k p₁ r st.q = max 1 (ceilDiv st.q k) := by
        unfold gsShift; rw [if_neg hcond]
      have hgq : gsNextQ k p₁ r st.q = 0 := by unfold gsNextQ; rw [if_neg hcond]
      rw [hgs, hgq] at hfit ⊢
      unfold resProgram
      rw [applyActs'_append]
      rcases Nat.eq_zero_or_pos st.q with hq0 | hq0
      · -- `q = 0`
        have hc0 : ceilDiv st.q k = 0 := by
          rw [hq0]; unfold ceilDiv; exact Nat.div_eq_of_lt (by omega)
        obtain ⟨lP, lT, lQ, l1, l2⟩ := resLoop_spec (w := startSym :: (v ++ [endSym]))
          (Text := Text) hne k st.q 0 ts st.q (st.pos + st.q) (k * p₁) r (Nat.le_refl _)
          hE.pat (by rw [show moves k st.q 0 = 0 from by rw [hq0]; rfl]; simpa using hE.txt)
          hE.quad
        rw [show st.q - st.q = 0 from by omega] at lP lQ
        rw [if_pos hq0]
        have etail : ∀ (ts' : TapesState' sc),
            applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
              Act'.keep tT (sc := sc) .right] ts' = applyActs' blank
              [Act'.keep tP .left, Act'.keep tP .right, Act'.keep tT (sc := sc) .right] ts' :=
          fun _ => rfl
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show Tape.SeqView blank (applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
            Act'.keep tT (sc := sc) .right] _ tP) _ (0 + 1)
          rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
            Act'.keep tT (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tP
            = Tape.step blank (Tape.step blank
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP)
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP).focus .left)
              (Tape.step blank (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP)
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP).focus .left).focus
              .right from by simp [applyActs', applyAct', upd, tP, tT]]
          refine Tape.seq_move_right (Tape.seq_move_left lP) ?_
          rw [hvlen]; omega
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
            Act'.keep tT (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tT
            = Tape.step blank (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tT)
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tT).focus .right from by
              simp [applyActs', applyAct', upd, tP, tT]]
          rw [show st.pos + max 1 (ceilDiv st.q k) + 0 = (st.pos + st.q) + 1 from by
            rw [hc0]; omega]
          exact Tape.seq_move_right lT (by rw [hc0] at hfit; omega)
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
            Act'.keep tT (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tC1
            = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tC1 from by
              simp [applyActs', applyAct', upd, tP, tT, tC1]]
          rw [l1]; exact hE.c1
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
            Act'.keep tT (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tC2
            = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tC2 from by
              simp [applyActs', applyAct', upd, tP, tT, tC2]]
          rw [l2]; exact hE.c2
        · exact ⟨by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
              Act'.keep tT (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tAp
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tAp from by
                simp [applyActs', applyAct', upd, tP, tT, tAp]]; exact lQ.ap,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
              Act'.keep tT (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tAn
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tAn from by
                simp [applyActs', applyAct', upd, tP, tT, tAn]]; exact lQ.an,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
              Act'.keep tT (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tRp
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tRp from by
                simp [applyActs', applyAct', upd, tP, tT, tRp]]; exact lQ.rp,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP .right,
              Act'.keep tT (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tRn
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tRn from by
                simp [applyActs', applyAct', upd, tP, tT, tRn]]; exact lQ.rn⟩
      · -- `q ≥ 1`
        have hc1 : 1 ≤ ceilDiv st.q k := ceilDiv_pos hk hq0
        have hc2 : ceilDiv st.q k ≤ st.q := ceilDiv_le_self hk
        obtain ⟨lP, lT, lQ, l1, l2⟩ := resLoop_spec (w := startSym :: (v ++ [endSym]))
          (Text := Text) hne k st.q 0 ts st.q (st.pos + ceilDiv st.q k) (k * p₁) r
          (Nat.le_refl _) hE.pat
          (by rw [moves_zero k hk st.q,
                show st.pos + ceilDiv st.q k + (st.q - ceilDiv st.q k) = st.pos + st.q from by
                  omega]
              exact hE.txt) hE.quad
        rw [show st.q - st.q = 0 from by omega] at lP lQ
        rw [if_neg (by omega : ¬ st.q = 0)]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show Tape.SeqView blank (applyActs' blank [Act'.keep tP .left,
            Act'.keep tP (sc := sc) .right] _ tP) _ (0 + 1)
          rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tP
            = Tape.step blank (Tape.step blank
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP)
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP).focus .left)
              (Tape.step blank (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP)
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts tP).focus .left).focus
              .right from by simp [applyActs', applyAct', upd, tP]]
          refine Tape.seq_move_right (Tape.seq_move_left lP) ?_
          rw [hvlen]; omega
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tT
            = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tT from by
              simp [applyActs', applyAct', upd, tP, tT]]
          rw [show st.pos + max 1 (ceilDiv st.q k) + 0 = st.pos + ceilDiv st.q k from by omega]
          exact lT
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tC1
            = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tC1 from by
              simp [applyActs', applyAct', upd, tP, tC1]]
          rw [l1]; exact hE.c1
        · rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
              (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tC2
            = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tC2 from by
              simp [applyActs', applyAct', upd, tP, tC2]]
          rw [l2]; exact hE.c2
        · exact ⟨by rw [show applyActs' blank [Act'.keep tP .left,
              Act'.keep tP (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tAp
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tAp from by
                simp [applyActs', applyAct', upd, tP, tAp]]; exact lQ.ap,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tAn
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tAn from by
                simp [applyActs', applyAct', upd, tP, tAn]]; exact lQ.an,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tRp
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tRp from by
                simp [applyActs', applyAct', upd, tP, tRp]]; exact lQ.rp,
            by rw [show applyActs' blank [Act'.keep tP .left, Act'.keep tP (sc := sc) .right]
                (applyActs' blank (resLoop blank mark k st.q 0 ts) ts) tRn
              = applyActs' blank (resLoop blank mark k st.q 0 ts) ts tRn from by
                simp [applyActs', applyAct', upd, tP, tRn]]; exact lQ.rn⟩

end StepNo


/-! ### コスト（オラクル無し版）：`A' = 8k + 13`, `B' = 8` -/

theorem period_amortized {k p₁ : ℕ} (hk : 0 < k) (pos q : ℕ) (hle : p₁ ≤ q) :
    13 * p₁ + 8 ≤
      (8 * k + 13) * ((k + 1) * (pos + p₁) + (q - p₁) - ((k + 1) * pos + q)) + 8 := by
  obtain ⟨X, hX⟩ : ∃ X, (k + 1) * pos = X := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, k * p₁ = Y := ⟨_, rfl⟩
  have e1 : (k + 1) * (pos + p₁) = X + (Y + p₁) := by rw [← hX, ← hY]; ring
  rw [e1, hX, show X + (Y + p₁) + (q - p₁) - (X + q) = Y from by omega]
  have hpY : p₁ ≤ Y := by rw [← hY]; exact Nat.le_mul_of_pos_left p₁ hk
  have h13 : 13 * Y ≤ (8 * k + 13) * Y := Nat.mul_le_mul (by omega) (Nat.le_refl Y)
  obtain ⟨Z, hZ⟩ : ∃ Z, (8 * k + 13) * Y = Z := ⟨_, rfl⟩
  rw [hZ] at h13 ⊢
  omega

theorem reset_amortized' {k : ℕ} (hk : 0 < k) (pos q e : ℕ) (he : e ≤ 7) :
    8 * q + e ≤
      (8 * k + 13) * ((k + 1) * (pos + max 1 (ceilDiv q k)) + 0 - ((k + 1) * pos + q)) + 8 := by
  obtain ⟨X, hX⟩ : ∃ X, (k + 1) * pos = X := ⟨_, rfl⟩
  have hks : q ≤ k * max 1 (ceilDiv q k) :=
    le_trans (ceilDiv_bounds hk).1 (Nat.mul_le_mul (Nat.le_refl k) (Nat.le_max_right 1 _))
  obtain ⟨A, hA⟩ : ∃ A, k * max 1 (ceilDiv q k) = A := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, max 1 (ceilDiv q k) = s := ⟨_, rfl⟩
  rw [hsdef] at hks hA
  have e1 : (k + 1) * (pos + s) = X + (A + s) := by rw [← hX, ← hA]; ring
  rw [hsdef, e1, hX]
  rw [show X + (A + s) + 0 - (X + q) = A + s - q from by omega]
  obtain ⟨D, hD⟩ : ∃ D, A + s - q = D := ⟨_, rfl⟩
  have hDq : D + q = A + s := by omega
  have e2 : k * D + k * q = k * A + A := by
    calc k * D + k * q = k * (D + q) := by ring
      _ = k * (A + s) := by rw [hDq]
      _ = k * A + k * s := by ring
      _ = k * A + A := by rw [hA]
  have e3 : k * q ≤ k * A := Nat.mul_le_mul (Nat.le_refl k) (by omega)
  have h2 : 8 * (k * D) ≤ (8 * k + 13) * D := by
    calc 8 * (k * D) = (8 * k) * D := by ring
      _ ≤ (8 * k + 13) * D := Nat.mul_le_mul (by omega) (Nat.le_refl D)
  obtain ⟨U, hU⟩ : ∃ U, k * D = U := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, k * q = V := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, k * A = W := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, (8 * k + 13) * D = Z := ⟨_, rfl⟩
  rw [hU, hV, hW] at e2
  rw [hV, hW] at e3
  rw [hU, hZ] at h2
  rw [hD, hZ]
  omega

/-- **主定理 2'（コスト、オラクル無し）**：`A' = 8k + 13`, `B' = 8`。 -/
theorem program_cost' {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)}
    {k p₁ r : ℕ} {ts : TapesState' sc} {st : ScanState}
    (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hE : Encodes' blank startSym endSym mark v Text k p₁ r ts st) (hq : st.q ≤ v.length) :
    (program' blank endSym mark k ts).length ≤
      (8 * k + 13) * (Phi k (scanStep v k p₁ r Text st) - Phi k st) + 8 := by
  by_cases hadv : Tape.read (ts tP) ≠ endSym ∧ Tape.read (ts tP) = Tape.read (ts tT)
  · have hs : scanStep v k p₁ r Text st = ⟨st.pos, st.q + 1⟩ :=
      scanStep_adv ((advance_iff' hend hE hq).1 hadv)
    rw [hs]
    have hprog : program' blank endSym mark k ts = advActs blank mark ts := by
      unfold program'; rw [if_pos hadv]
    rw [hprog]
    have hl := advActs_length_le blank mark ts
    unfold Phi
    dsimp only
    obtain ⟨X, hX⟩ : ∃ X, (k + 1) * st.pos = X := ⟨_, rfl⟩
    rw [hX, show X + (st.q + 1) - (X + st.q) = 1 from by omega, Nat.mul_one]
    omega
  · have hs : scanStep v k p₁ r Text st =
        ⟨st.pos + gsShift k p₁ r st.q, gsNextQ k p₁ r st.q⟩ :=
      scanStep_shift (fun hc => hadv ((advance_iff' hend hE hq).2 hc))
    rw [hs]
    have hprog : program' blank endSym mark k ts =
        probeActs blank tAn ++ probeActs blank tRn ++
          (if Tape.read (Tape.step blank (ts tAn) blank .left) = mark ∧
               Tape.read (Tape.step blank (ts tRn) blank .left) = mark then
            perProgram blank mark (p1Of' ts) ts
          else resProgram blank mark k (qOf' ts) ts) := by
      unfold program'; rw [if_neg hadv]
    rw [hprog, List.length_append, List.length_append, probeActs_length, probeActs_length]
    by_cases hcond : k * p₁ ≤ st.q ∧ st.q ≤ r
    · rw [if_pos ((period_iff' hne hE).2 hcond), p1Of'_eq hE]
      have hle : p₁ ≤ st.q := le_trans (Nat.le_mul_of_pos_left p₁ hk) hcond.1
      have hgs : gsShift k p₁ r st.q = p₁ := by unfold gsShift; rw [if_pos hcond]
      have hgq : gsNextQ k p₁ r st.q = st.q - p₁ := by unfold gsNextQ; rw [if_pos hcond]
      rw [hgs, hgq]
      have hl := perProgram_length_le (blank := blank) (mark := mark) p₁ ts
      have ha := period_amortized (k := k) (p₁ := p₁) hk st.pos st.q hle
      unfold Phi
      dsimp only
      omega
    · rw [if_neg (fun hc => hcond ((period_iff' hne hE).1 hc)), qOf'_eq hE]
      have hgs : gsShift k p₁ r st.q = max 1 (ceilDiv st.q k) := by
        unfold gsShift; rw [if_neg hcond]
      have hgq : gsNextQ k p₁ r st.q = 0 := by unfold gsNextQ; rw [if_neg hcond]
      rw [hgs, hgq]
      have hl := resProgram_length_le (blank := blank) (mark := mark) k st.q ts
      have ha := reset_amortized' (k := k) hk st.pos st.q 7 (Nat.le_refl 7)
      unfold Phi
      dsimp only
      omega


/-! ### 走査全体（汎用の telescoping） -/

/-- 一歩あたりのコスト関数 `c` を与えたときの走査全体のコスト。 -/
def runCostOf (c : ScanState → ℕ) (v : List (Fin sc)) (k p₁ r : ℕ) (Text : List (Fin sc)) :
    ℕ → ScanState → ℕ
  | 0, _ => 0
  | fuel + 1, st =>
      if Text.length < st.pos + v.length then 0
      else c st + runCostOf c v k p₁ r Text fuel (scanStep v k p₁ r Text st)

/-- **系（走査全体）**：毎歩のコストが `A * ΔΦ + B` で抑えられるなら、総コストは
`A * ((k+1)|T| + |v| + 1 - Φ) + B * 歩数`。`program_cost'` はこの仮定を
`A = 8k+13`, `B = 8` で与える。 -/
theorem total_cost_gen {v Text : List (Fin sc)} {k p₁ r : ℕ} (hk : 0 < k) (hp : 0 < p₁)
    (hv : 0 < v.length) (A B : ℕ) (c : ScanState → ℕ)
    (hc : ∀ st : ScanState, st.q ≤ v.length →
      c st ≤ A * (Phi k (scanStep v k p₁ r Text st) - Phi k st) + B) :
    ∀ (fuel : ℕ) (st : ScanState), st.q ≤ v.length →
      runCostOf c v k p₁ r Text fuel st ≤
        A * ((k + 1) * Text.length + v.length + 1 - Phi k st) +
          B * scanSteps v k p₁ r Text fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _; simp [runCostOf, scanSteps]
  | succ fuel ih =>
    intro st hq
    simp only [runCostOf, scanSteps]
    split_ifs with hstop
    · simp
    · have h1 := hc st hq
      have h2 := ih (scanStep v k p₁ r Text st) (scanStep_q_le hq)
      have hlt := phi_step_lt (v := v) (T := Text) (p₁ := p₁) (r := r) hk hp st
      have hle := phi_step_le (v := v) (Text := Text) (p₁ := p₁) (r := r) hk hv hq (by omega)
      have hsum : (Phi k (scanStep v k p₁ r Text st) - Phi k st) +
          ((k + 1) * Text.length + v.length + 1 - Phi k (scanStep v k p₁ r Text st)) =
          (k + 1) * Text.length + v.length + 1 - Phi k st := by omega
      have key : A * (Phi k (scanStep v k p₁ r Text st) - Phi k st) +
          A * ((k + 1) * Text.length + v.length + 1 - Phi k (scanStep v k p₁ r Text st)) =
          A * ((k + 1) * Text.length + v.length + 1 - Phi k st) := by
        rw [← Nat.mul_add, hsum]
      obtain ⟨P1, e1⟩ : ∃ x, A * (Phi k (scanStep v k p₁ r Text st) - Phi k st) = x := ⟨_, rfl⟩
      obtain ⟨P2, e2⟩ : ∃ x, A * ((k + 1) * Text.length + v.length + 1 -
          Phi k (scanStep v k p₁ r Text st)) = x := ⟨_, rfl⟩
      obtain ⟨P3, e3⟩ : ∃ x, A * ((k + 1) * Text.length + v.length + 1 - Phi k st) = x :=
        ⟨_, rfl⟩
      obtain ⟨S1, f1⟩ : ∃ x, scanSteps v k p₁ r Text fuel (scanStep v k p₁ r Text st) = x :=
        ⟨_, rfl⟩
      have hB : B * (1 + S1) = B + B * S1 := by ring
      rw [e1] at h1
      rw [e2, f1] at h2
      rw [e1, e2, e3] at key
      rw [e3, f1, hB]
      omega


end NoOracle


/-! ## 8. 小例による健全性チェック -/

section Examples

example : ceilDiv 20 8 = 3 := by decide
example : stays 8 20 0 = ceilDiv 20 8 := by decide
example : moves 8 20 0 = 20 - ceilDiv 20 8 := by decide
example : (periodActs (0 : Fin 3) 1 5).length = 4 * 5 + 2 := by decide
example : (resetProgram 3 8 20).length = 20 + (20 - 3) + 2 + 0 := by decide
example : (resetProgram 3 8 0).length = 0 + 0 + 2 + 1 := by decide
example : shiftCost 8 2 40 40 = 4 * 2 + 2 := by decide
example : shiftCost 8 2 40 41 = 41 + (41 - 6) + 2 + 0 := by decide

-- オラクル無し版
example : (perUp (0 : Fin 3) 5).length = 3 * 5 := by simp
example : (probeActs (0 : Fin 3) tAn).length = 2 := rfl
example : tAp ≠ tAn ∧ tRp ≠ tRn ∧ tC1 ≠ tC2 := by decide

end Examples

end PalPeg.GSTapes


