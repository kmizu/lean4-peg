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

end Examples

end PalPeg.GSTapes

