import PalPeg.GSPreprocess
import PalPeg.GSDecompose2
import PalPeg.TapeLib

/-!
# GS 前処理段のテープ実現 (`GSPreprocessTapes`)

`PalPeg.GSPreprocess` の添字レベルのループ（`firstInner` / `firstOuter` /
`extendReach` / `secondInner` / `secondOuter` / `stripLoop` / `decomposeLoop`）を、
Kim–Park 成果物のテープ模型 (`PegSeparation.RealTimeTM.TapeConfiguration`) 上の
**1 セル単位のヘッド動作列**として実現し、その動作数を同ファイルの instrumented
work counter（`firstInnerWork` など）で上から押さえる。

`GSScanTapes.lean` が走査段に対してやったことの前処理段版で、道具立て
（`Tape.SeqView` / `Tape.CounterView'` / 動作リスト `applyActs`）は共通である。

## テープ配置

前処理のループはすべて「パターンの 2 つの位置を突き合わせる」自己照合であり、
`firstInner` は `v[q]` と `v[p+q]`、`extendReach` は `v[r-p]` と `v[r]`、
`secondInner` は `v[q]` と `v[p+q]` を比べる。そこでパターンの**コピーを 2 本**持つ。

* `V1` — 語 `startSym :: (x ++ [endSym])`。ヘッドは添字 `a + 1`（`a` は `x` の添字）。
* `V2` — 同じ語。ヘッドは添字 `b + 1`。
* `Cd` — 単進カウンタ（`CounterView'`、底にマーカ `mark`）。**残余予算**
         `d = (k-1)*p - q`。内側ループの停止条件 `q < (k-1)*p` は `d ≠ 0` と同値で、
         `d` は 1 反復あたり ±1 でしか動かないので、probe（1 セル左へ）1 回で判定できる。
* `Cq` — 一致長 `q`。ヘッドの巻き戻し（`q` 歩左）でゼロ検出に使う。
* `Ce` — ずらし幅 `e = shiftNoPeriod q k = max 1 ⌈q/k⌉` の作業用カウンタ。
* `Cp` — 現在の候補周期 `p`。
* `Cf` — `_second_period` の `first`（= `p₁`）。
* `Cs` — 削除済み接頭辞の長さ `s`（`decompose` の `cut`）。
* `Cr` — `reach`。

**切り取り `x.drop s` の扱い**：`v = x.drop s` を物理的に作り直すことはせず、
`v` の添字 `i` を `x` の添字 `s + i` として読む（`List.getElem?_drop`）。したがって
`V1`/`V2` のヘッド位置はつねに `x` の絶対添字であり、削除（`s := s + p`）では
`V1` を `p` セル右へ動かすだけでよい（`V2` は `s+p+1`、すなわち 1 セル右）。
この再配置は **捨てた接頭辞 `p` に比例**するので、削除ループの償却に載る
（`stripStepCost` の定数を参照）。

## 有限制御で決まらない比較

`q < (k-1)*p` は上記のとおり `Cd` の probe で**実際に**判定する。
一方 `_second_period` の `k*first ≤ q'` と `q' ≤ r`、および内側の中断条件
`r < p + (q+1)` は、`GSScanTapes` が走査段でしたのと同じく**オラクルビット**として
仮定する（`hb : b = decide ...`）。これらは符号付き差分カウンタをもう 2 本足せば
同じ手口で実現できるが、本ファイルでは簿記を増やさない。
-/

namespace PalPeg.GSPre

open PegSeparation.RealTimeTM

variable {sc : ℕ}

/-! ## 1. テープの束と 1 セル動作 -/

/-- 文字テープに載せる語：左端番人 `startSym`、右端番人 `endSym`。 -/
def pword (startSym endSym : Fin sc) (x : List (Fin sc)) : List (Fin sc) :=
  startSym :: (x ++ [endSym])

@[simp] theorem pword_length (startSym endSym : Fin sc) (x : List (Fin sc)) :
    (pword startSym endSym x).length = x.length + 2 := by
  simp [pword]

/-- 前処理段が使う 9 本のテープ。 -/
structure Tapes (sc : ℕ) where
  V1 : TapeConfiguration sc
  V2 : TapeConfiguration sc
  Cd : TapeConfiguration sc
  Cq : TapeConfiguration sc
  Ce : TapeConfiguration sc
  Cp : TapeConfiguration sc
  Cf : TapeConfiguration sc
  Cs : TapeConfiguration sc
  Cr : TapeConfiguration sc

/-- 1 本のテープに対する 1 個のヘッド動作。文字テープ `V1`/`V2` は読んだ記号を
書き戻して移動する（内容を壊さない移動）。カウンタは書く記号を明示する。 -/
inductive Act (sc : ℕ) where
  | V1 : Move → Act sc
  | V2 : Move → Act sc
  | Cd : Fin sc → Move → Act sc
  | Cq : Fin sc → Move → Act sc
  | Ce : Fin sc → Move → Act sc
  | Cp : Fin sc → Move → Act sc
  | Cf : Fin sc → Move → Act sc
  | Cs : Fin sc → Move → Act sc
  | Cr : Fin sc → Move → Act sc

def applyAct (blank : Fin sc) (ts : Tapes sc) : Act sc → Tapes sc
  | .V1 m => { ts with V1 := Tape.step blank ts.V1 ts.V1.focus m }
  | .V2 m => { ts with V2 := Tape.step blank ts.V2 ts.V2.focus m }
  | .Cd a m => { ts with Cd := Tape.step blank ts.Cd a m }
  | .Cq a m => { ts with Cq := Tape.step blank ts.Cq a m }
  | .Ce a m => { ts with Ce := Tape.step blank ts.Ce a m }
  | .Cp a m => { ts with Cp := Tape.step blank ts.Cp a m }
  | .Cf a m => { ts with Cf := Tape.step blank ts.Cf a m }
  | .Cs a m => { ts with Cs := Tape.step blank ts.Cs a m }
  | .Cr a m => { ts with Cr := Tape.step blank ts.Cr a m }

def applyActs (blank : Fin sc) (l : List (Act sc)) (ts : Tapes sc) : Tapes sc :=
  l.foldl (applyAct blank) ts

@[simp] theorem applyActs_nil (blank : Fin sc) (ts : Tapes sc) :
    applyActs blank [] ts = ts := rfl

@[simp] theorem applyActs_cons (blank : Fin sc) (a : Act sc) (l : List (Act sc))
    (ts : Tapes sc) :
    applyActs blank (a :: l) ts = applyActs blank l (applyAct blank ts a) := rfl

theorem applyActs_append (blank : Fin sc) (l₁ l₂ : List (Act sc)) (ts : Tapes sc) :
    applyActs blank (l₁ ++ l₂) ts = applyActs blank l₂ (applyActs blank l₁ ts) := by
  simp [applyActs]

/-! ## 2. 符号化 -/

/-- 7 本のカウンタテープが表す値の組。 -/
structure Ctr where
  d : ℕ
  q : ℕ
  e : ℕ
  p : ℕ
  f : ℕ
  s : ℕ
  r : ℕ
  deriving DecidableEq

/-- テープ状態が「`V1` のヘッドが `x` の添字 `a`、`V2` が `b`、カウンタが `c`」を
表していること。 -/
structure Enc (blank startSym endSym mark : Fin sc) (x : List (Fin sc))
    (a b : ℕ) (c : Ctr) (ts : Tapes sc) : Prop where
  v1 : Tape.SeqView blank ts.V1 (pword startSym endSym x) (a + 1)
  v2 : Tape.SeqView blank ts.V2 (pword startSym endSym x) (b + 1)
  cd : Tape.CounterView' blank mark ts.Cd c.d
  cq : Tape.CounterView' blank mark ts.Cq c.q
  ce : Tape.CounterView' blank mark ts.Ce c.e
  cp : Tape.CounterView' blank mark ts.Cp c.p
  cf : Tape.CounterView' blank mark ts.Cf c.f
  cs : Tape.CounterView' blank mark ts.Cs c.s
  cr : Tape.CounterView' blank mark ts.Cr c.r

section Reads

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {n : ℕ}
  {tp : TapeConfiguration sc}

/-- 文字テープのビューは `n ≤ |x|` を含意する。 -/
theorem pat_le (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1)) :
    n ≤ x.length := by
  have := h.lt
  rw [pword_length] at this
  omega

/-- `n < |x|` なら読み取りは `x[n]`。 -/
theorem read_pat_lt (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1))
    (hn : n < x.length) : x[n]? = some (Tape.read tp) := by
  have h2 := h.read_eq
  rw [pword, List.getElem?_cons_succ, List.getElem?_append_left hn] at h2
  exact h2

/-- `n = |x|` なら読み取りは番人 `endSym`。 -/
theorem read_pat_end (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1))
    (hn : n = x.length) : Tape.read tp = endSym := by
  have h2 := h.read_eq
  rw [pword, List.getElem?_cons_succ, hn,
    List.getElem?_append_right (Nat.le_refl x.length)] at h2
  simp at h2
  exact h2.symm

/-- `endSym` が `x` に現れなければ、番人の読み取りは `n = |x|` と同値。 -/
theorem read_pat_end_iff (hend : endSym ∉ x)
    (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1)) :
    Tape.read tp = endSym ↔ n = x.length := by
  constructor
  · intro hc
    by_contra hne
    have hlt : n < x.length := lt_of_le_of_ne (pat_le h) hne
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 (read_pat_lt h hlt)
    exact hend (hc ▸ h2 ▸ List.getElem_mem h1)
  · exact read_pat_end h

/-- 右移動（記号を書き戻す）。 -/
theorem pat_right (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1))
    (hn : n < x.length) :
    Tape.SeqView blank (Tape.step blank tp tp.focus .right)
      (pword startSym endSym x) (n + 1 + 1) := by
  refine Tape.seq_move_right h ?_
  rw [pword_length]
  omega

/-- 左移動（記号を書き戻す）。 -/
theorem pat_left (h : Tape.SeqView blank tp (pword startSym endSym x) (n + 1 + 1)) :
    Tape.SeqView blank (Tape.step blank tp tp.focus .left)
      (pword startSym endSym x) (n + 1) :=
  Tape.seq_move_left h

end Reads

/-! ## 3. カウンタの probe（ゼロ判定と復元） -/

/-- probe で読める記号（空白を書いて 1 セル左へ動いたときの読み）。 -/
def probe (blank : Fin sc) (tp : TapeConfiguration sc) : Fin sc :=
  Tape.read (Tape.step blank tp blank .left)

theorem probe_eq {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) :
    probe blank tp = if n = 0 then mark else blank :=
  Tape.counter'_read_after_probe h

theorem probe_iff {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (hne : mark ≠ blank) (h : Tape.CounterView' blank mark tp n) :
    probe blank tp = mark ↔ n = 0 :=
  Tape.counter'_isZero_iff hne h

/-- 「probe して読んだ記号を書き戻して右へ」＝値を変えない検査（2 動作）。 -/
theorem counter'_test {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) :
    Tape.CounterView' blank mark
      (Tape.step blank (Tape.step blank tp blank .left) (probe blank tp) .right) n := by
  rw [probe_eq h]
  cases n with
  | zero => simpa using Tape.counter'_dec_zero h
  | succ m =>
      simp only [Nat.succ_ne_zero, if_false]
      exact Tape.counterView'_cons.2
        (Tape.peek_restore (Tape.pop_spec (Tape.counterView'_cons.1 h)))

/-! ## 4. 内側の自己照合ループ（`firstInner` のテープ実現）

これがすべての内側走査の**雛形**である。`V1` を `x` の添字 `a`、`V2` を `b` に置き、
一致する限り両方を 1 セルずつ右へ動かす。停止条件は
`b = |x|`（`V2` が右端番人 `endSym` を読む）、予算切れ（`Cd` の probe がマーカ）、
不一致（`V1` と `V2` の読みが違う）の 3 つで、**すべてテープ読み取りだけで決まる**。 -/

section Inner

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
  {a b : ℕ} {c : Ctr} {ts : Tapes sc}

/-- 内側ループ 1 反復の継続条件。 -/
def mCond (blank endSym mark : Fin sc) (ts : Tapes sc) : Prop :=
  Tape.read ts.V2 ≠ endSym ∧ probe blank ts.Cd ≠ mark ∧ Tape.read ts.V1 = Tape.read ts.V2

instance mCond_dec (blank endSym mark : Fin sc) (ts : Tapes sc) :
    Decidable (mCond blank endSym mark ts) := by
  unfold mCond; infer_instance

/-- 内側ループ 1 反復の動作列。継続なら 5 動作（`Cd` の probe と消去、`V1`/`V2` の右移動、
`Cq` の増加）、停止なら 2 動作（probe と復元）。 -/
def mActs (blank endSym mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  Act.Cd blank .left ::
    (if mCond blank endSym mark ts then
       [Act.Cd blank .stay, Act.V1 .right, Act.V2 .right, Act.Cq blank .right]
     else [Act.Cd (probe blank ts.Cd) .right])

theorem mActs_length_pos (h : mCond blank endSym mark ts) :
    (mActs blank endSym mark ts).length = 5 := by
  simp [mActs, if_pos h]

theorem mActs_length_neg (h : ¬ mCond blank endSym mark ts) :
    (mActs blank endSym mark ts).length = 2 := by
  simp [mActs, if_neg h]

theorem applyActs_mActs_pos (h : mCond blank endSym mark ts) :
    applyActs blank (mActs blank endSym mark ts) ts =
      { V1 := Tape.step blank ts.V1 ts.V1.focus .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) blank .stay
        Cq := Tape.step blank ts.Cq blank .right
        Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr } := by
  simp only [mActs, if_pos h]
  rfl

theorem applyActs_mActs_neg (h : ¬ mCond blank endSym mark ts) :
    applyActs blank (mActs blank endSym mark ts) ts =
      { ts with
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left)
                (probe blank ts.Cd) .right } := by
  simp only [mActs, if_neg h]
  rfl

/-- **継続条件は添字レベルの番人条件と一致する**。 -/
theorem mCond_iff (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b) :
    mCond blank endSym mark ts ↔ (b < x.length ∧ c.d ≠ 0 ∧ x[a]? = x[b]?) := by
  have hble : b ≤ x.length := pat_le hE.v2
  have hprobe : probe blank ts.Cd ≠ mark ↔ c.d ≠ 0 :=
    not_congr (probe_iff hmark hE.cd)
  by_cases hb : b < x.length
  · have hale : a < x.length := lt_of_le_of_lt hab hb
    have hV2 : Tape.read ts.V2 ≠ endSym := by
      intro hc
      have := (read_pat_end_iff hend hE.v2).1 hc
      omega
    have h1 := read_pat_lt hE.v1 hale
    have h2 := read_pat_lt hE.v2 hb
    constructor
    · rintro ⟨_, hd, hm⟩
      exact ⟨hb, hprobe.1 hd, by rw [h1, h2, hm]⟩
    · rintro ⟨_, hd, hm⟩
      refine ⟨hV2, hprobe.2 hd, ?_⟩
      rw [h1, h2] at hm
      exact Option.some.inj hm
  · have hbe : b = x.length := by omega
    have hV2 : Tape.read ts.V2 = endSym := read_pat_end hE.v2 hbe
    constructor
    · rintro ⟨h1, _, _⟩; exact absurd hV2 h1
    · rintro ⟨h1, _, _⟩; omega

/-- **1 反復の実現（継続枝）**：`a`、`b`、`q` が 1 増え、予算 `d` が 1 減る。 -/
theorem enc_m_step (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (h : mCond blank endSym mark ts) :
    Enc blank startSym endSym mark x (a + 1) (b + 1)
      { c with d := c.d - 1, q := c.q + 1 }
      (applyActs blank (mActs blank endSym mark ts) ts) := by
  obtain ⟨hb, hd, _⟩ := (mCond_iff hend hmark hE hab).1 h
  have hale : a < x.length := lt_of_le_of_lt hab hb
  rw [applyActs_mActs_pos h]
  obtain ⟨m, hm⟩ : ∃ m, c.d = m + 1 := ⟨c.d - 1, by omega⟩
  refine ⟨pat_right hE.v1 hale, pat_right hE.v2 hb, ?_, Tape.counter'_inc hE.cq,
    hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩
  show Tape.CounterView' blank mark _ (c.d - 1)
  rw [hm]
  simpa using Tape.counter'_dec (n := m) (by rw [← hm]; exact hE.cd)

/-- **1 反復の実現（停止枝）**：符号化は保たれる。 -/
theorem enc_m_stop (hE : Enc blank startSym endSym mark x a b c ts)
    (h : ¬ mCond blank endSym mark ts) :
    Enc blank startSym endSym mark x a b c
      (applyActs blank (mActs blank endSym mark ts) ts) := by
  rw [applyActs_mActs_neg h]
  exact ⟨hE.v1, hE.v2, counter'_test hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-! ### 添字レベルの双子走査とその仕事量 -/

/-- 添字レベルの双子走査が進む歩数。 -/
def mSteps (x : List (Fin sc)) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | fuel + 1, a, b, d =>
      if b < x.length ∧ d ≠ 0 ∧ x[a]? = x[b]? then 1 + mSteps x fuel (a + 1) (b + 1) (d - 1)
      else 0

/-- 双子走査の仕事量（`firstInnerWork` と同じ数え方：反復 1 回につき 1）。 -/
def mWork (x : List (Fin sc)) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | fuel + 1, a, b, d =>
      1 + (if b < x.length ∧ d ≠ 0 ∧ x[a]? = x[b]? then mWork x fuel (a + 1) (b + 1) (d - 1)
           else 0)

/-- 内側ループ全体の動作列。 -/
def mProg (blank endSym mark : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if mCond blank endSym mark ts then
        mActs blank endSym mark ts ++
          mProg blank endSym mark fuel (applyActs blank (mActs blank endSym mark ts) ts)
      else mActs blank endSym mark ts

/-- **主定理（内側ループの実現）**：`mProg` を適用すると、テープは双子走査の終状態を
符号化する。 -/
theorem mProg_spec (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel : ℕ) (ts : Tapes sc) (a b : ℕ) (c : Ctr),
      Enc blank startSym endSym mark x a b c ts → a ≤ b →
        Enc blank startSym endSym mark x (a + mSteps x fuel a b c.d)
          (b + mSteps x fuel a b c.d)
          { c with d := c.d - mSteps x fuel a b c.d, q := c.q + mSteps x fuel a b c.d }
          (applyActs blank (mProg blank endSym mark fuel ts) ts) := by
  intro fuel
  induction fuel with
  | zero =>
      intro ts a b c hE _
      simpa [mSteps, mProg] using hE
  | succ fuel ih =>
      intro ts a b c hE hab
      by_cases h : mCond blank endSym mark ts
      · have hcond : b < x.length ∧ c.d ≠ 0 ∧ x[a]? = x[b]? := (mCond_iff hend hmark hE hab).1 h
        have hstep := enc_m_step hend hmark hE hab h
        have : Enc blank startSym endSym mark x
            (a + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            (b + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            { d := c.d - 1 - mSteps x fuel (a + 1) (b + 1) (c.d - 1)
              q := c.q + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1)
              e := c.e, p := c.p, f := c.f, s := c.s, r := c.r }
            (applyActs blank
              (mProg blank endSym mark fuel (applyActs blank (mActs blank endSym mark ts) ts))
              (applyActs blank (mActs blank endSym mark ts) ts)) :=
          ih (applyActs blank (mActs blank endSym mark ts) ts) (a + 1) (b + 1)
            { c with d := c.d - 1, q := c.q + 1 } hstep (by omega)
        simp only [mSteps, if_pos hcond, mProg, if_pos h, applyActs_append]
        have he : a + (1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            = a + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1) := by omega
        have he2 : b + (1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            = b + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1) := by omega
        have he3 : c.d - (1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            = c.d - 1 - mSteps x fuel (a + 1) (b + 1) (c.d - 1) := by omega
        have he4 : c.q + (1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1))
            = c.q + 1 + mSteps x fuel (a + 1) (b + 1) (c.d - 1) := by omega
        rw [he, he2, he3, he4]
        exact this
      · have hg : ¬ (b < x.length ∧ c.d ≠ 0 ∧ x[a]? = x[b]?) :=
          fun hc => h ((mCond_iff hend hmark hE hab).2 hc)
        simp only [mSteps, if_neg hg, mProg, if_neg h]
        simpa using enc_m_stop hE h

/-- **主定理（内側ループのコスト）**：動作数は仕事量の 5 倍以下。 -/
theorem mProg_length (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel : ℕ) (ts : Tapes sc) (a b : ℕ) (c : Ctr),
      Enc blank startSym endSym mark x a b c ts → a ≤ b →
        (mProg blank endSym mark fuel ts).length ≤ 5 * mWork x fuel a b c.d := by
  intro fuel
  induction fuel with
  | zero => intro ts a b c _ _; simp [mProg, mWork]
  | succ fuel ih =>
      intro ts a b c hE hab
      by_cases h : mCond blank endSym mark ts
      · have hcond : b < x.length ∧ c.d ≠ 0 ∧ x[a]? = x[b]? := (mCond_iff hend hmark hE hab).1 h
        have hstep := enc_m_step hend hmark hE hab h
        have hrec : (mProg blank endSym mark fuel
              (applyActs blank (mActs blank endSym mark ts) ts)).length
            ≤ 5 * mWork x fuel (a + 1) (b + 1) (c.d - 1) :=
          ih (applyActs blank (mActs blank endSym mark ts) ts) (a + 1) (b + 1)
            { c with d := c.d - 1, q := c.q + 1 } hstep (by omega)
        simp only [mProg, if_pos h, mWork, if_pos hcond, List.length_append,
          mActs_length_pos h]
        omega
      · have hg : ¬ (b < x.length ∧ c.d ≠ 0 ∧ x[a]? = x[b]?) :=
          fun hc => h ((mCond_iff hend hmark hE hab).2 hc)
        simp only [mProg, if_neg h, mWork, if_neg hg, mActs_length_neg h]
        omega

end Inner

/-! ## 5. 双子走査と `firstInner` の対応

`v = x.drop s` の添字 `i` は `x` の添字 `s + i`（`List.getElem?_drop`）。
予算 `d = (k-1)*p - q` を保つ限り、テープ側の停止条件は `firstInner` の停止条件と一致する。 -/

section FirstInner

variable {x : List (Fin sc)} {k p s : ℕ}

/-- 番人条件の一致。 -/
theorem mGuard_iff (hs : s ≤ x.length) (q d : ℕ) (hd : q + d = (k - 1) * p) :
    ((s + p + q) < x.length ∧ d ≠ 0 ∧ x[s + q]? = x[s + p + q]?) ↔
      (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
        (x.drop s)[q]? = (x.drop s)[p + q]?) := by
  have hlen : (x.drop s).length = x.length - s := by simp
  have e1 : (x.drop s)[q]? = x[s + q]? := List.getElem?_drop
  have e2 : (x.drop s)[p + q]? = x[s + p + q]? := by
    rw [List.getElem?_drop]
    congr 1
    omega
  rw [hlen, e1, e2]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩

/-- 双子走査の歩数と仕事量は `firstInner` / `firstInnerWork` と一致する。 -/
theorem mSteps_firstInner (hs : s ≤ x.length) :
    ∀ (fuel q d : ℕ), q + d = (k - 1) * p → s + p + q ≤ x.length →
      (q + mSteps x fuel (s + q) (s + p + q) d = firstInner (x.drop s) k p fuel q ∧
        mWork x fuel (s + q) (s + p + q) d = firstInnerWork (x.drop s) k p fuel q) := by
  intro fuel
  induction fuel with
  | zero => intro q d _ _; simp [mSteps, mWork, firstInner, firstInnerWork]
  | succ fuel ih =>
      intro q d hd hle
      by_cases hg : (s + p + q) < x.length ∧ d ≠ 0 ∧ x[s + q]? = x[s + p + q]?
      · have hg' := (mGuard_iff hs q d hd).1 hg
        obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
        have hd' : (q + 1) + (d - 1) = (k - 1) * p := by omega
        have hle' : s + p + (q + 1) ≤ x.length := by omega
        have hrec := ih (q + 1) (d - 1) hd' hle'
        have e1 : s + (q + 1) = s + q + 1 := by omega
        have e2 : s + p + (q + 1) = s + p + q + 1 := by omega
        rw [e1, e2] at hrec
        simp only [mSteps, mWork, if_pos hg, firstInner, firstInnerWork, if_pos hg']
        omega
      · have hg' : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
            (x.drop s)[q]? = (x.drop s)[p + q]?) := fun hc => hg ((mGuard_iff hs q d hd).2 hc)
        simp only [mSteps, mWork, if_neg hg, firstInner, firstInnerWork, if_neg hg']
        exact ⟨by omega, by trivial⟩

end FirstInner

/-! ## 6. `extendReach` のテープ実現

`extendReach v p fuel r` は `v[r-p]` と `v[r]` を比べる。`t = r - p` と置くと
`(v-添字) = (t, p + t)`、すなわち `x` の添字では `(s + t, s + p + t)` で、
`firstInner` とまったく同じ双子走査である（予算 `Cd` は使わず、`Cr` を数える）。 -/

section Reach

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
  {a b : ℕ} {c : Ctr} {ts : Tapes sc}

/-- `extendReach` の 1 反復の継続条件。 -/
def rCond (endSym : Fin sc) (ts : Tapes sc) : Prop :=
  Tape.read ts.V2 ≠ endSym ∧ Tape.read ts.V1 = Tape.read ts.V2

instance rCond_dec (endSym : Fin sc) (ts : Tapes sc) : Decidable (rCond endSym ts) := by
  unfold rCond; infer_instance

/-- 1 反復の動作列（継続なら 3 動作、停止なら 0 動作）。 -/
def rActs (blank endSym : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if rCond endSym ts then [Act.V1 .right, Act.V2 .right, Act.Cr blank .right] else []

theorem rActs_length_pos (h : rCond endSym ts) :
    (rActs blank endSym ts).length = 3 := by
  simp [rActs, if_pos h]

theorem rActs_length_neg (h : ¬ rCond endSym ts) :
    (rActs blank endSym ts).length = 0 := by
  simp [rActs, if_neg h]

theorem applyActs_rActs_pos (h : rCond endSym ts) :
    applyActs blank (rActs blank endSym ts) ts =
      { V1 := Tape.step blank ts.V1 ts.V1.focus .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Cr := Tape.step blank ts.Cr blank .right
        Cd := ts.Cd, Cq := ts.Cq, Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs } := by
  simp only [rActs, if_pos h]
  rfl

theorem rCond_iff (hend : endSym ∉ x)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b) :
    rCond endSym ts ↔ (b < x.length ∧ x[a]? = x[b]?) := by
  have hble : b ≤ x.length := pat_le hE.v2
  by_cases hb : b < x.length
  · have hale : a < x.length := lt_of_le_of_lt hab hb
    have hV2 : Tape.read ts.V2 ≠ endSym := by
      intro hc
      have := (read_pat_end_iff hend hE.v2).1 hc
      omega
    have h1 := read_pat_lt hE.v1 hale
    have h2 := read_pat_lt hE.v2 hb
    constructor
    · rintro ⟨_, hm⟩; exact ⟨hb, by rw [h1, h2, hm]⟩
    · rintro ⟨_, hm⟩
      refine ⟨hV2, ?_⟩
      rw [h1, h2] at hm
      exact Option.some.inj hm
  · have hbe : b = x.length := by omega
    have hV2 : Tape.read ts.V2 = endSym := read_pat_end hE.v2 hbe
    constructor
    · rintro ⟨h1, _⟩; exact absurd hV2 h1
    · rintro ⟨h1, _⟩; omega

/-- **1 反復の実現**：`a`、`b`、`r` が 1 ずつ増える。 -/
theorem enc_r_step (hend : endSym ∉ x)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (h : rCond endSym ts) :
    Enc blank startSym endSym mark x (a + 1) (b + 1) { c with r := c.r + 1 }
      (applyActs blank (rActs blank endSym ts) ts) := by
  obtain ⟨hb, _⟩ := (rCond_iff hend hE hab).1 h
  have hale : a < x.length := lt_of_le_of_lt hab hb
  rw [applyActs_rActs_pos h]
  exact ⟨pat_right hE.v1 hale, pat_right hE.v2 hb, hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs,
    Tape.counter'_inc hE.cr⟩

/-- 添字レベルの走査歩数と仕事量（`extendReachWork` と同じ数え方）。 -/
def rSteps (x : List (Fin sc)) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => if b < x.length ∧ x[a]? = x[b]? then 1 + rSteps x fuel (a + 1) (b + 1) else 0

def rWork (x : List (Fin sc)) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, a, b => 1 + (if b < x.length ∧ x[a]? = x[b]? then rWork x fuel (a + 1) (b + 1) else 0)

theorem rSteps_le_rWork (x : List (Fin sc)) : ∀ fuel a b, rSteps x fuel a b ≤ rWork x fuel a b := by
  intro fuel
  induction fuel with
  | zero => intro a b; simp [rSteps, rWork]
  | succ fuel ih =>
      intro a b
      by_cases hg : b < x.length ∧ x[a]? = x[b]?
      · have := ih (a + 1) (b + 1)
        rw [rSteps, if_pos hg, rWork, if_pos hg]
        omega
      · rw [rSteps, if_neg hg, rWork, if_neg hg]
        omega

/-- `extendReach` 全体の動作列。 -/
def rProg (blank endSym : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if rCond endSym ts then
        rActs blank endSym ts ++ rProg blank endSym fuel (applyActs blank (rActs blank endSym ts) ts)
      else []

/-- **主定理（`extendReach` の実現）**。 -/
theorem rProg_spec (hend : endSym ∉ x) :
    ∀ (fuel : ℕ) (ts : Tapes sc) (a b : ℕ) (c : Ctr),
      Enc blank startSym endSym mark x a b c ts → a ≤ b →
        Enc blank startSym endSym mark x (a + rSteps x fuel a b) (b + rSteps x fuel a b)
          { c with r := c.r + rSteps x fuel a b }
          (applyActs blank (rProg blank endSym fuel ts) ts) := by
  intro fuel
  induction fuel with
  | zero => intro ts a b c hE _; simpa [rSteps, rProg] using hE
  | succ fuel ih =>
      intro ts a b c hE hab
      by_cases h : rCond endSym ts
      · have hcond : b < x.length ∧ x[a]? = x[b]? := (rCond_iff hend hE hab).1 h
        have hstep := enc_r_step hend hE hab h
        have : Enc blank startSym endSym mark x
            (a + 1 + rSteps x fuel (a + 1) (b + 1)) (b + 1 + rSteps x fuel (a + 1) (b + 1))
            { d := c.d, q := c.q, e := c.e, p := c.p, f := c.f, s := c.s
              r := c.r + 1 + rSteps x fuel (a + 1) (b + 1) }
            (applyActs blank (rProg blank endSym fuel
              (applyActs blank (rActs blank endSym ts) ts))
              (applyActs blank (rActs blank endSym ts) ts)) :=
          ih (applyActs blank (rActs blank endSym ts) ts) (a + 1) (b + 1)
            { c with r := c.r + 1 } hstep (by omega)
        simp only [rSteps, if_pos hcond, rProg, if_pos h, applyActs_append]
        have e1 : a + (1 + rSteps x fuel (a + 1) (b + 1)) = a + 1 + rSteps x fuel (a + 1) (b + 1) := by
          omega
        have e2 : b + (1 + rSteps x fuel (a + 1) (b + 1)) = b + 1 + rSteps x fuel (a + 1) (b + 1) := by
          omega
        have e3 : c.r + (1 + rSteps x fuel (a + 1) (b + 1))
            = c.r + 1 + rSteps x fuel (a + 1) (b + 1) := by omega
        rw [e1, e2, e3]
        exact this
      · have hg : ¬ (b < x.length ∧ x[a]? = x[b]?) := fun hc => h ((rCond_iff hend hE hab).2 hc)
        simp only [rSteps, if_neg hg, rProg, if_neg h]
        simpa using hE

/-- **主定理（`extendReach` のコスト）**：動作数は仕事量の 3 倍以下。 -/
theorem rProg_length (hend : endSym ∉ x) :
    ∀ (fuel : ℕ) (ts : Tapes sc) (a b : ℕ) (c : Ctr),
      Enc blank startSym endSym mark x a b c ts → a ≤ b →
        (rProg blank endSym fuel ts).length ≤ 3 * rWork x fuel a b := by
  intro fuel
  induction fuel with
  | zero => intro ts a b c _ _; simp [rProg, rWork]
  | succ fuel ih =>
      intro ts a b c hE hab
      by_cases h : rCond endSym ts
      · have hcond : b < x.length ∧ x[a]? = x[b]? := (rCond_iff hend hE hab).1 h
        have hstep := enc_r_step hend hE hab h
        have hrec : (rProg blank endSym fuel
              (applyActs blank (rActs blank endSym ts) ts)).length
            ≤ 3 * rWork x fuel (a + 1) (b + 1) :=
          ih (applyActs blank (rActs blank endSym ts) ts) (a + 1) (b + 1)
            { c with r := c.r + 1 } hstep (by omega)
        simp only [rProg, if_pos h, rWork, if_pos hcond, List.length_append,
          rActs_length_pos h]
        omega
      · have hg : ¬ (b < x.length ∧ x[a]? = x[b]?) := fun hc => h ((rCond_iff hend hE hab).2 hc)
        simp only [rProg, if_neg h, rWork, if_neg hg]
        simp

/-- 添字レベルの対応：`extendReach` は `t = r - p` についての双子走査。 -/
theorem rSteps_extendReach {p s : ℕ} (hs : s ≤ x.length) :
    ∀ (fuel t : ℕ), s + p + t ≤ x.length →
      (p + t + rSteps x fuel (s + t) (s + p + t) = extendReach (x.drop s) p fuel (p + t) ∧
        rWork x fuel (s + t) (s + p + t) = extendReachWork (x.drop s) p fuel (p + t)) := by
  have hguard : ∀ t : ℕ, ((s + p + t) < x.length ∧ x[s + t]? = x[s + p + t]?) ↔
      (p + t < (x.drop s).length ∧ (x.drop s)[p + t - p]? = (x.drop s)[p + t]?) := by
    intro t
    have hlen : (x.drop s).length = x.length - s := by simp
    have e1 : (x.drop s)[p + t - p]? = x[s + t]? := by
      rw [show p + t - p = t from by omega, List.getElem?_drop]
    have e2 : (x.drop s)[p + t]? = x[s + p + t]? := by
      rw [List.getElem?_drop]; congr 1; omega
    rw [hlen, e1, e2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  intro fuel
  induction fuel with
  | zero => intro t _; simp [rSteps, rWork, extendReach, extendReachWork]
  | succ fuel ih =>
      intro t hle
      by_cases hg : (s + p + t) < x.length ∧ x[s + t]? = x[s + p + t]?
      · have hg' := (hguard t).1 hg
        have hrec := ih (t + 1) (by omega)
        have e1 : s + (t + 1) = s + t + 1 := by omega
        have e2 : s + p + (t + 1) = s + p + t + 1 := by omega
        have e3 : p + (t + 1) = p + t + 1 := by omega
        rw [e1, e2, e3] at hrec
        simp only [rSteps, rWork, if_pos hg, extendReach, extendReachWork, if_pos hg']
        omega
      · have hg' : ¬ (p + t < (x.drop s).length ∧
            (x.drop s)[p + t - p]? = (x.drop s)[p + t]?) := fun hc => hg ((hguard t).2 hc)
        simp only [rSteps, rWork, if_neg hg, extendReach, extendReachWork, if_neg hg']
        exact ⟨by omega, by trivial⟩

end Reach

/-! ## 7. `⌈q/k⌉` を数える mod `k` スケジュール

`GSScanTapes` の `stays` と同じもの（あちらは `Txt` を止める回数、ここは `Ce` を上げる回数）。
本ファイルを `GSScanTapes` から独立に読めるよう再掲する。 -/

theorem ceilDiv_le_self' {k q : ℕ} (hk : 0 < k) : ceilDiv q k ≤ q := by
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

theorem ceilDiv_eq_succ' {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    ceilDiv n k = (n - 1) / k + 1 := by
  unfold ceilDiv
  have h : n + k - 1 = (n - 1) + k := by omega
  rw [h, Nat.add_div_right _ hk]

/-- `n` 歩のうち `Ce` を上げる回数（位相 `c` から開始）。 -/
def stays (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, 0 => stays k n (k - 1) + 1
  | n + 1, c + 1 => stays k n c

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
      rw [ceilDiv_eq_succ' hk (Nat.succ_pos m), Nat.succ_sub_one]
      have key : stays k m (k - 1) = m / k := by
        rcases Nat.lt_or_ge m k with hm | hm
        · rw [stays_small k m (k - 1) (by omega), Nat.div_eq_of_lt hm]
        · have hsplit : m = (m - (k - 1)) + (k - 1) := by omega
          have h1 : stays k m (k - 1) = stays k (m - (k - 1)) 0 := by
            conv_lhs => rw [hsplit]
            exact stays_shift k (k - 1) (m - (k - 1))
          rw [h1, ih (m - (k - 1)) (by omega), ceilDiv_eq_succ' hk (by omega)]
          have h2 : m - (k - 1) - 1 = m - k := by omega
          rw [h2]
          conv_rhs => rw [Nat.div_eq_sub_div hk hm]
      omega

theorem stays_le (k : ℕ) : ∀ n c, stays k n c ≤ n := by
  intro n
  induction n with
  | zero => intro c; simp [stays]
  | succ n ih =>
      intro c
      cases c with
      | zero => have := ih (k - 1); simp only [stays]; omega
      | succ c => have := ih c; simp only [stays]; omega

/-! ## 8. カウンタの読み出しと外側 1 反復の再配置 -/

section Outer

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- カウンタテープから読み取れる値。 -/
def qOf (ts : Tapes sc) : ℕ := ts.Cq.left.length - 1
def eOf (ts : Tapes sc) : ℕ := ts.Ce.left.length - 1

theorem ctr_len {blank mark : Fin sc} {tp : TapeConfiguration sc} {n : ℕ}
    (h : Tape.CounterView' blank mark tp n) : tp.left.length - 1 = n := by
  have h2 : tp.left = List.replicate n blank ++ [mark] := Tape.StackView.left_eq h
  rw [h2]; simp

theorem qOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : qOf ts = c.q := ctr_len hE.cq

theorem eOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : eOf ts = c.e := ctr_len hE.ce

/-- `Cp` の読み出し。 -/
def pOf (ts : Tapes sc) : ℕ := ts.Cp.left.length - 1

theorem pOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : pOf ts = c.p := ctr_len hE.cp

/-! ### 巻き戻し（`q` 歩ぶん左へ戻しつつ `Cd` を復元し、`⌈q/k⌉` を `Ce` に数える） -/

/-- 巻き戻し 1 単位：`V1`・`V2` を 1 左、`Cq` を 1 下げ、`Cd` を 1 上げる（5 動作）。 -/
def rewindUnit (blank : Fin sc) : List (Act sc) :=
  [Act.V1 .left, Act.V2 .left, Act.Cq blank .left, Act.Cq blank .stay, Act.Cd blank .right]

/-- 巻き戻しループ（位相 `c` が `0` の回だけ `Ce` を 1 上げる）。 -/
def rewindLoop (blank : Fin sc) (k : ℕ) : ℕ → ℕ → List (Act sc)
  | 0, _ => []
  | n + 1, 0 => (rewindUnit blank ++ [Act.Ce blank .right]) ++ rewindLoop blank k n (k - 1)
  | n + 1, c + 1 => rewindUnit blank ++ rewindLoop blank k n c

theorem rewindLoop_length (blank : Fin sc) (k : ℕ) : ∀ n c,
    (rewindLoop blank k n c).length = 5 * n + stays k n c := by
  intro n
  induction n with
  | zero => intro c; simp [rewindLoop, stays]
  | succ n ih =>
      intro c
      cases c with
      | zero =>
          have h := ih (k - 1)
          simp only [rewindLoop, stays, List.length_append, rewindUnit, List.length_cons,
            List.length_nil, h]
          omega
      | succ c =>
          have h := ih c
          simp only [rewindLoop, stays, List.length_append, rewindUnit, List.length_cons,
            List.length_nil, h]
          omega

theorem applyActs_rewindUnit (ts : Tapes sc) :
    applyActs blank (rewindUnit blank) ts =
      { V1 := Tape.step blank ts.V1 ts.V1.focus .left
        V2 := Tape.step blank ts.V2 ts.V2.focus .left
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay
        Cd := Tape.step blank ts.Cd blank .right
        Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr } := rfl

/-- 巻き戻し 1 単位の実現。 -/
theorem rewind_unit_enc {a b D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (a + 1) (b + 1) ⟨D, Q + 1, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D + 1, Q, E, P, F, S, R⟩
      (applyActs blank (rewindUnit blank) ts) := by
  rw [applyActs_rewindUnit]
  exact ⟨pat_left hE.v1, pat_left hE.v2, Tape.counter'_inc hE.cd,
    by simpa using Tape.counter'_dec (n := Q) hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- **巻き戻しの実現**：`V1`/`V2` が `n` セル左に戻り、`Cq` が `n` 減り、`Cd` が `n` 増え、
`Ce` に `stays k n c`（位相 `0` からなら `⌈n/k⌉`）が加わる。 -/
theorem rewind_enc (k : ℕ) : ∀ (n c a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D + n, Q, E + stays k n c, P, F, S, R⟩
        (applyActs blank (rewindLoop blank k n c) ts) := by
  intro n
  induction n with
  | zero => intro c a b D Q E P F S R ts hE; simpa [rewindLoop, stays] using hE
  | succ n ih =>
      intro c a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1, e2, e3] at hE
        exact hE
      have hstep := rewind_unit_enc hE'
      cases c with
      | zero =>
          have hce : Enc blank startSym endSym mark x (a + n) (b + n)
              ⟨D + 1, Q + n, E + 1, P, F, S, R⟩
              (applyActs blank (rewindUnit blank ++ [Act.Ce blank .right]) ts) := by
            rw [applyActs_append]
            refine ⟨hstep.v1, hstep.v2, hstep.cd, hstep.cq, ?_, hstep.cp, hstep.cf, hstep.cs,
              hstep.cr⟩
            exact Tape.counter'_inc hstep.ce
          have := ih (k - 1) a b (D + 1) Q (E + 1) P F S R _ hce
          simp only [rewindLoop, stays, applyActs_append]
          have e4 : D + 1 + n = D + (n + 1) := by omega
          have e5 : E + 1 + stays k n (k - 1) = E + (stays k n (k - 1) + 1) := by omega
          rw [e4, e5] at this
          exact this
      | succ c =>
          have := ih c a b (D + 1) Q E P F S R _ hstep
          simp only [rewindLoop, stays, applyActs_append]
          have e4 : D + 1 + n = D + (n + 1) := by omega
          rw [e4] at this
          exact this

/-! ### `max 1 ⌈q/k⌉`：`Ce` が `0` なら `1` にする -/

def maxOneActs (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Ce = mark then
    [Act.Ce blank .left, Act.Ce mark .right, Act.Ce blank .right]
  else [Act.Ce blank .left, Act.Ce blank .right]

theorem maxOneActs_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (maxOneActs blank mark ts).length ≤ 3 := by
  unfold maxOneActs; split_ifs <;> simp

theorem maxOne_enc {a b : ℕ} {c : Ctr} {ts : Tapes sc} (hmark : mark ≠ blank)
    (hE : Enc blank startSym endSym mark x a b c ts) :
    Enc blank startSym endSym mark x a b { c with e := max 1 c.e }
      (applyActs blank (maxOneActs blank mark ts) ts) := by
  by_cases h : probe blank ts.Ce = mark
  · have h0 : c.e = 0 := (probe_iff hmark hE.ce).1 h
    have hres : applyActs blank (maxOneActs blank mark ts) ts =
        { ts with
          Ce := Tape.step blank (Tape.step blank
            (Tape.step blank ts.Ce blank .left) mark .right) blank .right } := by
      simp only [maxOneActs, if_pos h]; rfl
    rw [hres]
    refine ⟨hE.v1, hE.v2, hE.cd, hE.cq, ?_, hE.cp, hE.cf, hE.cs, hE.cr⟩
    show Tape.CounterView' blank mark _ (max 1 c.e)
    rw [h0]
    have h1 : Tape.CounterView' blank mark ts.Ce 0 := by rw [← h0]; exact hE.ce
    simpa using Tape.counter'_inc (Tape.counter'_dec_zero h1)
  · have h0 : c.e ≠ 0 := fun hc => h ((probe_iff hmark hE.ce).2 hc)
    have hres : applyActs blank (maxOneActs blank mark ts) ts =
        { ts with
          Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .right } := by
      simp only [maxOneActs, if_neg h]; rfl
    rw [hres]
    refine ⟨hE.v1, hE.v2, hE.cd, hE.cq, ?_, hE.cp, hE.cf, hE.cs, hE.cr⟩
    show Tape.CounterView' blank mark _ (max 1 c.e)
    have hmax : max 1 c.e = c.e := by omega
    rw [hmax]
    have := counter'_test hE.ce
    rw [probe_eq hE.ce] at this
    simpa [h0] using this

/-! ### ずらしの適用（`p := p + e`、`V2` を `e` セル右へ、`Cd` に `(k-1)*e` を足す） -/

def cdIncs (blank : Fin sc) (m : ℕ) : List (Act sc) := List.replicate m (Act.Cd blank .right)

@[simp] theorem cdIncs_length (blank : Fin sc) (m : ℕ) : (cdIncs blank m).length = m := by
  simp [cdIncs]

theorem cdIncs_enc : ∀ (m a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D + m, Q, E, P, F, S, R⟩
        (applyActs blank (cdIncs blank m) ts) := by
  intro m
  induction m with
  | zero => intro a b D Q E P F S R ts hE; simpa [cdIncs] using hE
  | succ m ih =>
      intro a b D Q E P F S R ts hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D + 1, Q, E, P, F, S, R⟩
          (applyAct blank ts (Act.Cd blank .right)) :=
        ⟨hE.v1, hE.v2, Tape.counter'_inc hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩
      have := ih a b (D + 1) Q E P F S R _ hstep
      have e1 : D + 1 + m = D + (m + 1) := by omega
      rw [e1] at this
      simpa [cdIncs, List.replicate_succ] using this

def shiftHead (blank : Fin sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce blank .stay, Act.Cp blank .right, Act.V2 .right]

/-- ずらし 1 単位：`Ce` を 1 下げ、`Cp` を 1 上げ、`V2` を 1 右へ、`Cd` を `k-1` 上げる。 -/
def shiftUnit (blank : Fin sc) (k : ℕ) : List (Act sc) := shiftHead blank ++ cdIncs blank (k - 1)

def shiftLoop (blank : Fin sc) (k : ℕ) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => shiftUnit blank k ++ shiftLoop blank k n

theorem shiftLoop_length (blank : Fin sc) (k n : ℕ) :
    (shiftLoop blank k n).length = (4 + (k - 1)) * n := by
  induction n with
  | zero => simp [shiftLoop]
  | succ n ih =>
      simp only [shiftLoop, List.length_append, shiftUnit, shiftHead, cdIncs_length, ih,
        List.length_cons, List.length_nil]
      ring

theorem applyActs_shiftHead (ts : Tapes sc) :
    applyActs blank (shiftHead blank) ts =
      { V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
        Cp := Tape.step blank ts.Cp blank .right
        V1 := ts.V1, Cd := ts.Cd, Cq := ts.Cq, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr } := rfl

theorem shift_unit_enc {a b D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩ ts)
    (hb : b < x.length) :
    Enc blank startSym endSym mark x a (b + 1) ⟨D + (k - 1), Q, E, P + 1, F, S, R⟩
      (applyActs blank (shiftUnit blank k) ts) := by
  have hhead : Enc blank startSym endSym mark x a (b + 1) ⟨D, Q, E, P + 1, F, S, R⟩
      (applyActs blank (shiftHead blank) ts) := by
    rw [applyActs_shiftHead]
    exact ⟨hE.v1, pat_right hE.v2 hb, hE.cd, hE.cq,
      by simpa using Tape.counter'_dec (n := E) hE.ce, Tape.counter'_inc hE.cp,
      hE.cf, hE.cs, hE.cr⟩
  rw [shiftUnit, applyActs_append]
  exact cdIncs_enc (k - 1) a (b + 1) D Q E (P + 1) F S R _ hhead

/-- **ずらしの実現**：`e` 単位で `V2` が `e` 右へ、`p` が `e` 増え、`Cd` が `(k-1)*e` 増える。 -/
theorem shiftLoop_enc (k : ℕ) : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts → b + n ≤ x.length →
      Enc blank startSym endSym mark x a (b + n)
        ⟨D + (k - 1) * n, Q, E, P + n, F, S, R⟩
        (applyActs blank (shiftLoop blank k n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE _; simpa [shiftLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE hle
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep := shift_unit_enc (k := k) hE' (by omega)
      have := ih a (b + 1) (D + (k - 1)) Q E (P + 1) F S R _ hstep (by omega)
      simp only [shiftLoop, applyActs_append]
      have e1 : b + 1 + n = b + (n + 1) := by omega
      have e2 : D + (k - 1) + (k - 1) * n = D + (k - 1) * (n + 1) := by ring
      have e3 : P + 1 + n = P + (n + 1) := by omega
      rw [e1, e2, e3] at this
      exact this

/-! ### 外側 1 反復の再配置（巻き戻し → `max 1 ⌈q/k⌉` → ずらし） -/

/-- 外側 1 反復の再配置動作列。反復回数はテープから読み取った `qOf` / `eOf`。 -/
def shiftPhase (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  (rewindLoop blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) ++
    shiftLoop blank k
      (eOf (applyActs blank
        (rewindLoop blank k (qOf ts) 0 ++
          maxOneActs blank mark (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) ts))

/-- **主定理（外側 1 反復の再配置、一般形）**：`q = 0`、`p := p + shiftNoPeriod q k` の
状態へ移る。`Cd` は「巻き戻しぶん `q`」と「ずらしぶん `(k-1)*e`」だけ増える。 -/
theorem shiftPhase_enc' (hk : 0 < k) (hmark : mark ≠ blank)
    {s p q D F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, 0, p, F, S, R⟩ ts)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length) :
    Enc blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
      ⟨D + q + (k - 1) * shiftNoPeriod q k, 0, 0, p + shiftNoPeriod q k, F, S, R⟩
      (applyActs blank (shiftPhase blank mark k ts) ts)
    ∧ (shiftPhase blank mark k ts).length
        ≤ 5 * q + ceilDiv q k + 3 + (4 + (k - 1)) * shiftNoPeriod q k := by
  have hq : qOf ts = q := qOf_eq hE
  have hE0 : Enc blank startSym endSym mark x (s + q) ((s + p) + q)
      ⟨D, 0 + q, 0, p, F, S, R⟩ ts := by
    have e1 : 0 + q = q := by omega
    rw [e1]; exact hE
  have h1 := rewind_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) k q 0 s (s + p) D 0 0 p F S R ts hE0
  have hst : 0 + stays k q 0 = ceilDiv q k := by rw [stays_zero k hk q]; omega
  rw [hst] at h1
  have h2 := maxOne_enc (a := s) (b := s + p) hmark h1
  have hmaxe : max 1 (ceilDiv q k) = shiftNoPeriod q k := rfl
  have h2' : Enc blank startSym endSym mark x s (s + p)
      ⟨D + q, 0, shiftNoPeriod q k, p, F, S, R⟩
      (applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop blank k (qOf ts) 0) ts))
        (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) := by
    rw [hq]
    simpa [hmaxe] using h2
  have hmid : applyActs blank (rewindLoop blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) ts =
      applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop blank k (qOf ts) 0) ts))
        (applyActs blank (rewindLoop blank k (qOf ts) 0) ts) := applyActs_append _ _ _ _
  have he : eOf (applyActs blank (rewindLoop blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) ts)
      = shiftNoPeriod q k := by
    rw [hmid]; exact eOf_eq h2'
  have h3 : Enc blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
      ⟨D + q + (k - 1) * shiftNoPeriod q k, 0, 0, p + shiftNoPeriod q k, F, S, R⟩
      (applyActs blank (shiftLoop blank k (shiftNoPeriod q k))
        (applyActs blank (rewindLoop blank k (qOf ts) 0 ++
          maxOneActs blank mark (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)) ts)) := by
    refine shiftLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) k (shiftNoPeriod q k) s (s + p) (D + q) 0 0 p F S R _ ?_
      (by omega)
    rw [hmid]
    have e0 : (0 : ℕ) + shiftNoPeriod q k = shiftNoPeriod q k := by omega
    rw [e0]
    exact h2'
  constructor
  · rw [shiftPhase, he, applyActs_append]
    exact h3
  · rw [shiftPhase, he]
    have hm := maxOneActs_length_le blank mark
      (applyActs blank (rewindLoop blank k (qOf ts) 0) ts)
    simp only [List.length_append, rewindLoop_length, shiftLoop_length,
      stays_zero k hk (qOf ts)]
    rw [hq] at hm ⊢
    omega

/-- `firstOuter` 用の特殊形（`D = (k-1)*p - q` のとき次の予算は `(k-1)*(p+e)`）。 -/
theorem shiftPhase_enc (hk : 0 < k) (hmark : mark ≠ blank)
    {s p q F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q)
      ⟨(k - 1) * p - q, q, 0, p, F, S, R⟩ ts)
    (hd : q ≤ (k - 1) * p)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length) :
    Enc blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
      ⟨(k - 1) * (p + shiftNoPeriod q k), 0, 0, p + shiftNoPeriod q k, F, S, R⟩
      (applyActs blank (shiftPhase blank mark k ts) ts)
    ∧ (shiftPhase blank mark k ts).length
        ≤ 5 * q + ceilDiv q k + 3 + (4 + (k - 1)) * shiftNoPeriod q k := by
  obtain ⟨h1, h2⟩ := shiftPhase_enc' (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hmark hE hfit
  refine ⟨?_, h2⟩
  have hmul : (k - 1) * p - q + q + (k - 1) * shiftNoPeriod q k
      = (k - 1) * (p + shiftNoPeriod q k) := by
    have e : (k - 1) * (p + shiftNoPeriod q k) = (k - 1) * p + (k - 1) * shiftNoPeriod q k := by
      ring
    omega
  rw [hmul] at h1
  exact h1

/-! ### 添字レベルの補助 -/

theorem mSteps_le_d (x : List (Fin sc)) : ∀ fuel a b d, mSteps x fuel a b d ≤ d := by
  intro fuel
  induction fuel with
  | zero => intro a b d; simp [mSteps]
  | succ fuel ih =>
      intro a b d
      by_cases hg : b < x.length ∧ d ≠ 0 ∧ x[a]? = x[b]?
      · have := ih (a + 1) (b + 1) (d - 1)
        rw [mSteps, if_pos hg]
        omega
      · rw [mSteps, if_neg hg]; omega

theorem mSteps_le_mWork (x : List (Fin sc)) : ∀ fuel a b d, mSteps x fuel a b d ≤ mWork x fuel a b d := by
  intro fuel
  induction fuel with
  | zero => intro a b d; simp [mSteps, mWork]
  | succ fuel ih =>
      intro a b d
      by_cases hg : b < x.length ∧ d ≠ 0 ∧ x[a]? = x[b]?
      · have := ih (a + 1) (b + 1) (d - 1)
        rw [mSteps, if_pos hg, mWork, if_pos hg]
        omega
      · rw [mSteps, if_neg hg, mWork, if_neg hg]; omega

/-- `firstInner` は燃料が十分なら燃料に依存しない。 -/
theorem firstInner_fuel (v : List (Fin sc)) (k p : ℕ) :
    ∀ (f g q : ℕ), v.length ≤ f + q → f + 1 ≤ g →
      (firstInner v k p (f + 1) q = firstInner v k p g q ∧
        firstInnerWork v k p (f + 1) q = firstInnerWork v k p g q) := by
  intro f
  induction f with
  | zero =>
      intro g q hle hg
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have hgd : ¬ (p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?) := by
        rintro ⟨h1, -, -⟩; omega
      constructor
      · conv_lhs => rw [firstInner, if_neg hgd]
        conv_rhs => rw [firstInner, if_neg hgd]
      · conv_lhs => rw [firstInnerWork, if_neg hgd]
        conv_rhs => rw [firstInnerWork, if_neg hgd]
  | succ f ih =>
      intro g q hle hg
      obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      by_cases hgd : p + q < v.length ∧ q < (k - 1) * p ∧ v[q]? = v[p + q]?
      · obtain ⟨hr1, hr2⟩ := ih g' (q + 1) (by omega) (by omega)
        constructor
        · conv_lhs => rw [firstInner, if_pos hgd]
          conv_rhs => rw [firstInner, if_pos hgd]
          rw [hr1]
        · conv_lhs => rw [firstInnerWork, if_pos hgd]
          conv_rhs => rw [firstInnerWork, if_pos hgd]
          rw [hr2]
      · constructor
        · conv_lhs => rw [firstInner, if_neg hgd]
          conv_rhs => rw [firstInner, if_neg hgd]
        · conv_lhs => rw [firstInnerWork, if_neg hgd]
          conv_rhs => rw [firstInnerWork, if_neg hgd]

/-! ### `firstOuter` / `firstPeriod` のテープ実現 -/

/-- 成功判定（`Cd = 0`、すなわち `q = (k-1)*p`）の probe と復元（2 動作）。 -/
def oTest (blank _mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  [Act.Cd blank .left, Act.Cd (probe blank ts.Cd) .right]

@[simp] theorem oTest_length (blank mark : Fin sc) (ts : Tapes sc) :
    (oTest blank mark ts).length = 2 := rfl

theorem oTest_enc {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) :
    Enc blank startSym endSym mark x a b c (applyActs blank (oTest blank mark ts) ts) := by
  have hres : applyActs blank (oTest blank mark ts) ts =
      { ts with
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) (probe blank ts.Cd) .right } :=
    rfl
  rw [hres]
  exact ⟨hE.v1, hE.v2, counter'_test hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- 外側 1 反復の前半（内側走査 → 成功判定）。 -/
def oHead (blank endSym mark : Fin sc) (Fi : ℕ) (ts : Tapes sc) : List (Act sc) :=
  mProg blank endSym mark Fi ts ++
    oTest blank mark (applyActs blank (mProg blank endSym mark Fi ts) ts)

/-- 成功枝かどうか（`Cd` の probe がマーカ）。 -/
def oSucc (blank endSym mark : Fin sc) (Fi : ℕ) (ts : Tapes sc) : Prop :=
  probe blank (applyActs blank (mProg blank endSym mark Fi ts) ts).Cd = mark

instance oSucc_dec (blank endSym mark : Fin sc) (Fi : ℕ) (ts : Tapes sc) :
    Decidable (oSucc blank endSym mark Fi ts) := by unfold oSucc; infer_instance

/-- `firstOuter`（`bound = |v|` 版、すなわち `firstPeriod`）の動作列。 -/
def oCondB (endSym : Fin sc) (orcB : Tapes sc → Bool) (ts : Tapes sc) : Prop :=
  Tape.read ts.V2 ≠ endSym ∧ orcB ts = true

instance oCondB_dec (endSym : Fin sc) (orcB : Tapes sc → Bool) (ts : Tapes sc) :
    Decidable (oCondB endSym orcB ts) := by unfold oCondB; infer_instance

/-- `firstOuter v k bound` の動作列。番人 `endSym`（`p < |v|`）に加えて、
候補上限 `p < bound` をオラクル `orcB` で判定する。 -/
def oProg (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k Fi : ℕ) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if oCondB endSym orcB ts then
        (if oSucc blank endSym mark Fi ts then oHead blank endSym mark Fi ts
      else oHead blank endSym mark Fi ts ++
        (shiftPhase blank mark k (applyActs blank (oHead blank endSym mark Fi ts) ts) ++
          oProg blank endSym mark orcB k Fi fuel
            (applyActs blank
              (shiftPhase blank mark k (applyActs blank (oHead blank endSym mark Fi ts) ts))
              (applyActs blank (oHead blank endSym mark Fi ts) ts))))
      else []

/-- 内側走査の直後の状態（外側 1 反復の途中状態）。 -/
theorem oHead_enc (_hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s p F S R : ℕ} {ts : Tapes sc} (hs : s ≤ x.length) (hp : s + p ≤ x.length)
    (Fi : ℕ)
    (hE : Enc blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x (s + firstInner (x.drop s) k p Fi 0)
      (s + p + firstInner (x.drop s) k p Fi 0)
      ⟨(k - 1) * p - firstInner (x.drop s) k p Fi 0, firstInner (x.drop s) k p Fi 0,
        0, p, F, S, R⟩
      (applyActs blank (oHead blank endSym mark Fi ts) ts)
    ∧ firstInner (x.drop s) k p Fi 0 ≤ (k - 1) * p
    ∧ (oHead blank endSym mark Fi ts).length
        ≤ 5 * firstInnerWork (x.drop s) k p Fi 0 + 2
    ∧ Enc blank startSym endSym mark x (s + firstInner (x.drop s) k p Fi 0)
        (s + p + firstInner (x.drop s) k p Fi 0)
        ⟨(k - 1) * p - firstInner (x.drop s) k p Fi 0, firstInner (x.drop s) k p Fi 0,
          0, p, F, S, R⟩
        (applyActs blank (mProg blank endSym mark Fi ts) ts) := by
  have hcorr := mSteps_firstInner (x := x) (k := k) (p := p) (s := s) hs Fi 0 ((k - 1) * p)
    (by omega) (by omega)
  have hj : mSteps x Fi s (s + p) ((k - 1) * p) = firstInner (x.drop s) k p Fi 0 := by
    have := hcorr.1
    simpa using this
  have hw : mWork x Fi s (s + p) ((k - 1) * p) = firstInnerWork (x.drop s) k p Fi 0 := by
    have := hcorr.2
    simpa using this
  have hle : firstInner (x.drop s) k p Fi 0 ≤ (k - 1) * p := by
    rw [← hj]; exact mSteps_le_d x Fi s (s + p) ((k - 1) * p)
  have h1 := mProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) hend hmark Fi ts s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ hE
    (by omega)
  rw [hj] at h1
  have h1' : Enc blank startSym endSym mark x (s + firstInner (x.drop s) k p Fi 0)
      (s + p + firstInner (x.drop s) k p Fi 0)
      ⟨(k - 1) * p - firstInner (x.drop s) k p Fi 0, firstInner (x.drop s) k p Fi 0,
        0, p, F, S, R⟩ (applyActs blank (mProg blank endSym mark Fi ts) ts) := by
    have e0 : 0 + firstInner (x.drop s) k p Fi 0 = firstInner (x.drop s) k p Fi 0 := by omega
    simpa [e0] using h1
  refine ⟨?_, hle, ?_, h1'⟩
  · rw [oHead, applyActs_append]
    exact oTest_enc h1'
  · have hlen := mProg_length (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) hend hmark Fi ts s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ hE
      (by omega)
    rw [hw] at hlen
    simp only [oHead, List.length_append, oTest_length]
    omega

/-- ずらし幅の評価。 -/
theorem shiftNoPeriod_le_succ (hk : 0 < k) (q : ℕ) : shiftNoPeriod q k ≤ q + 1 := by
  have h := ceilDiv_le_self' (k := k) (q := q) hk
  unfold shiftNoPeriod
  omega

theorem shiftNoPeriod_zero (hk : 0 < k) : shiftNoPeriod 0 k = 1 := by
  have h : ceilDiv 0 k = 0 := by
    unfold ceilDiv
    exact Nat.div_eq_of_lt (by omega)
  unfold shiftNoPeriod
  omega

theorem shiftNoPeriod_le_of_pos (hk : 0 < k) {q : ℕ} (hq : 0 < q) : shiftNoPeriod q k ≤ q := by
  have h1 := (ceilDiv_bounds (q := q) (k := k) hk).1
  have h2 := ceilDiv_le_self' (k := k) (q := q) hk
  have h3 : 0 < ceilDiv q k := by
    rcases Nat.eq_zero_or_pos (ceilDiv q k) with h | h
    · rw [h, Nat.mul_zero] at h1; omega
    · exact h
  unfold shiftNoPeriod
  omega

/-- **主定理（`firstOuter` / `firstPeriod` のテープ実現とコスト）**。
`A = 2k + 22`、`B = 0`：総動作数は `A * firstOuterWork` 以下。 -/
theorem oProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s bound Fi : ℕ} {orcB : Tapes sc → Bool} (hs : s ≤ x.length)
    (hFi : (x.drop s).length + 1 ≤ Fi)
    (horcB : ∀ ts', orcB ts' = decide (pOf ts' < bound)) :
    ∀ (fuel p F S R : ℕ) (ts : Tapes sc), 0 < p → s + p ≤ x.length →
      Enc blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ ts →
      ((oProg blank endSym mark orcB k Fi fuel ts).length
          ≤ (2 * k + 22) * firstOuterWork (x.drop s) k bound fuel p
        ∧ (∀ p' m, firstOuter (x.drop s) k bound fuel p = some (p', m) →
            Enc blank startSym endSym mark x (s + (k - 1) * p') (s + m)
              ⟨0, (k - 1) * p', 0, p', F, S, R⟩
              (applyActs blank
                (oProg blank endSym mark orcB k Fi fuel ts) ts)
            ∧ (k - 1) * p'
                ≤ firstOuterWork (x.drop s) k bound fuel p)
        ∧ (∃ a b D Q E P, Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
              (applyActs blank
                (oProg blank endSym mark orcB k Fi fuel ts) ts))
        ∧ (firstOuter (x.drop s) k bound fuel p = none →
            ∃ P, 0 < P ∧ s + P ≤ x.length ∧
              Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, S, R⟩
                (applyActs blank
                  (oProg blank endSym mark orcB k Fi fuel ts) ts))) := by
  have hdroplen : (x.drop s).length = x.length - s := by simp
  intro fuel
  induction fuel with
  | zero =>
      intro p F S R ts hp hsp hE
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [oProg, firstOuterWork]; simp
      · intro p' m hc; rw [firstOuter] at hc; simp at hc
      · refine ⟨s, s + p, (k - 1) * p, 0, 0, p, ?_⟩
        rw [oProg, applyActs_nil]
        exact hE
      · intro _
        refine ⟨p, hp, hsp, ?_⟩
        rw [oProg, applyActs_nil]
        exact hE
  | succ fuel ih =>
      intro p F S R ts hp hsp hE
      have hgiff : oCondB endSym orcB ts ↔ (p < (x.drop s).length ∧ p < bound) := by
        have h1 : Tape.read ts.V2 = endSym ↔ s + p = x.length := read_pat_end_iff hend hE.v2
        have h2 : orcB ts = true ↔ p < bound := by
          rw [horcB ts, pOf_eq hE]; simp
        unfold oCondB
        constructor
        · rintro ⟨ha, hb⟩
          have hne : s + p ≠ x.length := fun hcc => ha (h1.2 hcc)
          exact ⟨by rw [hdroplen]; omega, h2.1 hb⟩
        · rintro ⟨ha, hb⟩
          rw [hdroplen] at ha
          refine ⟨fun hcc => ?_, h2.2 hb⟩
          have := h1.1 hcc
          omega
      by_cases hcg : oCondB endSym orcB ts
      · have hg : p < (x.drop s).length ∧ p < bound := hgiff.1 hcg
        have hlt : s + p < x.length := by
          have hgg := hg.1
          rw [hdroplen] at hgg
          omega
        obtain ⟨hhead, hqle, hlen, hmid⟩ :=
          oHead_enc (blank := blank) (startSym := startSym) (endSym := endSym) (mark := mark)
            (x := x) (k := k) hk hend hmark hs hsp Fi hE
        obtain ⟨hfi1, hfi2⟩ := firstInner_fuel (x.drop s) k p ((x.drop s).length) Fi 0
          (by omega) hFi
        rw [← hfi1] at hhead hqle hmid
        rw [← hfi2] at hlen
        -- 内側走査の到達位置
        have hin := firstInner_le (x.drop s) k p ((x.drop s).length + 1) 0 (by omega)
        have hqfit : s + p + firstInner (x.drop s) k p ((x.drop s).length + 1) 0 ≤ x.length := by
          have := hin.2
          omega
        have hqW0 : firstInner (x.drop s) k p ((x.drop s).length + 1) 0
            ≤ firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 := by
          have h1 := mSteps_firstInner (x := x) (k := k) (p := p) (s := s) hs
            ((x.drop s).length + 1) 0 ((k - 1) * p) (by omega) (by omega)
          have h3 := mSteps_le_mWork x ((x.drop s).length + 1) (s + 0) (s + p + 0) ((k - 1) * p)
          omega
        by_cases hsucc : oSucc blank endSym mark Fi ts
        · -- 成功枝
          have hd0 : (k - 1) * p - firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = 0 :=
            (probe_iff hmark hmid.cd).1 hsucc
          have hqeq : firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = (k - 1) * p := by
            omega
          have hprog : oProg blank endSym mark orcB k Fi (fuel + 1) ts
              = oHead blank endSym mark Fi ts := by
            rw [oProg, if_pos hcg, if_pos hsucc]
          have hres : Enc blank startSym endSym mark x (s + (k - 1) * p)
              (s + (p + (k - 1) * p)) ⟨0, (k - 1) * p, 0, p, F, S, R⟩
              (applyActs blank (oHead blank endSym mark Fi ts) ts) := by
            have e1 : s + p + (k - 1) * p = s + (p + (k - 1) * p) := by omega
            rw [hqeq, Nat.sub_self, e1] at hhead
            exact hhead
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hprog, firstOuterWork, if_pos hg, if_pos hqeq]
            obtain ⟨W, hW⟩ : ∃ W, firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 = W :=
              ⟨_, rfl⟩
            rw [hW] at hlen ⊢
            have hmono : 28 * (1 + W + 0) ≤ (2 * k + 22) * (1 + W + 0) :=
              Nat.mul_le_mul_right _ (by omega)
            have hexp : 28 * (1 + W + 0) = 28 + 28 * W := by ring
            omega
          · intro p' m hc
            rw [firstOuter, if_pos hg, if_pos hqeq] at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            refine ⟨by rw [hprog]; exact hres, ?_⟩
            rw [firstOuterWork, if_pos hg, if_pos hqeq]
            omega
          · exact ⟨_, _, _, _, _, _, by rw [hprog]; exact hres⟩
          · intro hc
            rw [firstOuter, if_pos hg, if_pos hqeq] at hc
            simp at hc
        · -- 失敗枝：巻き戻して `p` をずらす
          have hd0 : (k - 1) * p - firstInner (x.drop s) k p ((x.drop s).length + 1) 0 ≠ 0 :=
            fun hc => hsucc ((probe_iff hmark hmid.cd).2 hc)
          have hqne : firstInner (x.drop s) k p ((x.drop s).length + 1) 0 ≠ (k - 1) * p := by
            omega
          have hfit : s + p +
              shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k
                ≤ x.length := by
            rcases Nat.eq_zero_or_pos (firstInner (x.drop s) k p ((x.drop s).length + 1) 0)
              with h0 | h0
            · rw [h0, shiftNoPeriod_zero (by omega)]; omega
            · have := shiftNoPeriod_le_of_pos (k := k) (by omega) h0
              omega
          obtain ⟨hshift, hslen⟩ :=
            shiftPhase_enc (blank := blank) (startSym := startSym) (endSym := endSym)
              (mark := mark) (x := x) (k := k) (by omega) hmark
              (s := s) (p := p) (q := firstInner (x.drop s) k p ((x.drop s).length + 1) 0)
              (F := F) (S := S) (R := R) hhead hqle hfit
          -- 次の反復の入口状態
          have hnext : Enc blank startSym endSym mark x s
              (s + (p + shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k))
              ⟨(k - 1) * (p + shiftNoPeriod (firstInner (x.drop s) k p
                    ((x.drop s).length + 1) 0) k), 0, 0,
                p + shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k,
                F, S, R⟩
              (applyActs blank
                (shiftPhase blank mark k
                  (applyActs blank (oHead blank endSym mark Fi ts) ts))
                (applyActs blank (oHead blank endSym mark Fi ts) ts)) := by
            have e1 : s + p +
                shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k
                = s + (p +
                  shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k) := by
              omega
            rw [e1] at hshift
            exact hshift
          have hrec := ih (p + shiftNoPeriod (firstInner (x.drop s) k p
              ((x.drop s).length + 1) 0) k) F S R _
            (by have := shiftNoPeriod_pos (firstInner (x.drop s) k p
                  ((x.drop s).length + 1) 0) k; omega)
            (by omega) hnext
          have hprog : oProg blank endSym mark orcB k Fi (fuel + 1) ts
              = oHead blank endSym mark Fi ts ++
                (shiftPhase blank mark k
                    (applyActs blank (oHead blank endSym mark Fi ts) ts) ++
                  oProg blank endSym mark orcB k Fi fuel
                    (applyActs blank
                      (shiftPhase blank mark k
                        (applyActs blank
                          (oHead blank endSym mark Fi ts) ts))
                      (applyActs blank
                        (oHead blank endSym mark Fi ts) ts))) := by
            rw [oProg, if_pos hcg, if_neg hsucc]
          have happ : applyActs blank
              (oProg blank endSym mark orcB k Fi (fuel + 1) ts) ts
              = applyActs blank
                (oProg blank endSym mark orcB k Fi fuel
                  (applyActs blank
                    (shiftPhase blank mark k
                      (applyActs blank (oHead blank endSym mark Fi ts) ts))
                    (applyActs blank (oHead blank endSym mark Fi ts) ts)))
                (applyActs blank
                  (shiftPhase blank mark k
                    (applyActs blank (oHead blank endSym mark Fi ts) ts))
                  (applyActs blank (oHead blank endSym mark Fi ts) ts)) := by
            rw [hprog, applyActs_append, applyActs_append]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hprog, firstOuterWork, if_pos hg, if_neg hqne]
            simp only [List.length_append]
            -- 記号を潰して算術に落とす
            obtain ⟨W, hW⟩ : ∃ W, firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 = W :=
              ⟨_, rfl⟩
            obtain ⟨Wo, hWo⟩ : ∃ Wo, firstOuterWork (x.drop s) k bound fuel
                (p + shiftNoPeriod (firstInner (x.drop s) k p ((x.drop s).length + 1) 0) k)
                = Wo := ⟨_, rfl⟩
            obtain ⟨q, hq⟩ : ∃ q, firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = q :=
              ⟨_, rfl⟩
            obtain ⟨e, he⟩ : ∃ e, shiftNoPeriod q k = e := ⟨_, rfl⟩
            obtain ⟨K, hK⟩ : ∃ K, 4 + (k - 1) = K := ⟨_, rfl⟩
            obtain ⟨A, hA⟩ : ∃ A, 2 * k + 22 = A := ⟨_, rfl⟩
            have hrl := hrec.1
            rw [hWo, hA] at hrl
            rw [hW] at hlen
            rw [hq, he] at hslen
            rw [hW, hWo, hA]
            rw [hK] at hslen
            -- 数量の関係
            have hqW : q ≤ W := by
              have h1 : firstInner (x.drop s) k p ((x.drop s).length + 1) 0
                  = 0 + mSteps x ((x.drop s).length + 1) (s + 0) (s + p + 0) ((k - 1) * p) := by
                have := (mSteps_firstInner (x := x) (k := k) (p := p) (s := s) hs
                  ((x.drop s).length + 1) 0 ((k - 1) * p) (by omega) (by omega)).1
                omega
              have h2 : mWork x ((x.drop s).length + 1) (s + 0) (s + p + 0) ((k - 1) * p)
                  = firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 :=
                (mSteps_firstInner (x := x) (k := k) (p := p) (s := s) hs
                  ((x.drop s).length + 1) 0 ((k - 1) * p) (by omega) (by omega)).2
              have h3 := mSteps_le_mWork x ((x.drop s).length + 1) (s + 0) (s + p + 0)
                ((k - 1) * p)
              omega
            have heW : e ≤ W + 1 := by
              have := shiftNoPeriod_le_succ (k := k) (by omega) q
              omega
            have hcq : ceilDiv q k ≤ q := ceilDiv_le_self' (by omega)
            have hKe : K * e ≤ K * (W + 1) := Nat.mul_le_mul_left _ heW
            have hKexp : K * (W + 1) = K * W + K := by ring
            have hKA : K + 11 ≤ A := by omega
            have hmono : K * W + 11 * W ≤ A * W := by
              calc K * W + 11 * W = (K + 11) * W := by ring
                _ ≤ A * W := Nat.mul_le_mul_right W hKA
            have hAexp : A * (1 + W + Wo) = A + A * W + A * Wo := by ring
            omega
          · intro p' m hc
            rw [firstOuter, if_pos hg, if_neg hqne] at hc
            obtain ⟨hEnc, hwk⟩ := hrec.2.1 p' m hc
            refine ⟨by rw [happ]; exact hEnc, ?_⟩
            rw [firstOuterWork, if_pos hg, if_neg hqne]
            omega
          · rw [happ]
            exact hrec.2.2.1
          · intro hc
            rw [firstOuter, if_pos hg, if_neg hqne] at hc
            obtain ⟨P, hP1, hP2, hP3⟩ := hrec.2.2.2 hc
            exact ⟨P, hP1, hP2, by rw [happ]; exact hP3⟩
      · have hng : ¬ (p < (x.drop s).length ∧ p < bound) := fun hcc => hcg (hgiff.2 hcc)
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [oProg, if_neg hcg, firstOuterWork, if_neg hng]
          simp
        · intro p' m hcc
          rw [firstOuter, if_neg hng] at hcc
          simp at hcc
        · refine ⟨s, s + p, (k - 1) * p, 0, 0, p, ?_⟩
          rw [oProg, if_neg hcg, applyActs_nil]
          exact hE
        · intro _
          refine ⟨p, hp, hsp, ?_⟩
          rw [oProg, if_neg hcg, applyActs_nil]
          exact hE

/-! ## 9. 外側ループの入口整備と `firstPeriod` 全体 -/

/-- `p := 1`、`Cd := k-1`、`V2` を 1 セル右へ（`k` は有限制御の定数なので `O(k)` 動作）。 -/
def initActs (blank : Fin sc) (k : ℕ) : List (Act sc) :=
  cdIncs blank (k - 1) ++ [Act.Cp blank .right, Act.V2 .right]

@[simp] theorem initActs_length (blank : Fin sc) (k : ℕ) :
    (initActs blank k).length = (k - 1) + 2 := by
  simp [initActs]

theorem initActs_enc {s F S R : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x s (s + 1) ⟨(k - 1) * 1, 0, 0, 1, F, S, R⟩
      (applyActs blank (initActs blank k) ts) := by
  have h1 := cdIncs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k - 1) s s 0 0 0 0 F S R ts hE
  have h2 : Enc blank startSym endSym mark x s (s + 1) ⟨0 + (k - 1), 0, 0, 1, F, S, R⟩
      (applyActs blank [Act.Cp blank .right, Act.V2 .right]
        (applyActs blank (cdIncs blank (k - 1)) ts)) := by
    refine ⟨h1.v1, ?_, h1.cd, h1.cq, h1.ce, ?_, h1.cf, h1.cs, h1.cr⟩
    · exact pat_right h1.v2 hs
    · exact Tape.counter'_inc h1.cp
  have e1 : 0 + (k - 1) = (k - 1) * 1 := by omega
  rw [e1] at h2
  rw [initActs, applyActs_append]
  exact h2

/-- `firstPeriod`（`= firstOuter v k |v| (|v|+1) 1`）のテープ実現。 -/
def fpProg (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  initActs blank k ++
    oProg blank endSym mark orcB k (n + 1) Fo (applyActs blank (initActs blank k) ts)

/-- **主定理（`firstPeriod` のテープ実現とコスト）**。 -/
theorem fpProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s F S R bound Fo n : ℕ} {ts : Tapes sc} {orcB : Tapes sc → Bool} (hs : s < x.length)
    (hn : (x.drop s).length ≤ n)
    (horcB : ∀ ts', orcB ts' = decide (pOf ts' < bound))
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩ ts) :
    ((fpProg blank endSym mark orcB k n Fo ts).length
        ≤ (k - 1) + 2 + (2 * k + 22) * firstOuterWork (x.drop s) k bound Fo 1
      ∧ (∀ p₁ m, firstOuter (x.drop s) k bound Fo 1 = some (p₁, m) →
          Enc blank startSym endSym mark x (s + (k - 1) * p₁) (s + m)
            ⟨0, (k - 1) * p₁, 0, p₁, F, S, R⟩
            (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)
          ∧ (k - 1) * p₁ ≤ firstOuterWork (x.drop s) k bound Fo 1)
      ∧ (∃ a b D Q E P, Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
            (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
      ∧ (firstOuter (x.drop s) k bound Fo 1 = none →
          ∃ P, 0 < P ∧ s + P ≤ x.length ∧
            Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, S, R⟩
              (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))) := by
  have hsle : s ≤ x.length := le_of_lt hs
  have hinit := initActs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) hs hE
  have hinit' : Enc blank startSym endSym mark x s (s + 1) ⟨(k - 1) * 1, 0, 0, 1, F, S, R⟩
      (applyActs blank (initActs blank k) ts) := hinit
  obtain ⟨hcost, hsome, hex, hnone⟩ := oProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) (Fi := n + 1) hk hend hmark hsle
    (by omega) horcB Fo 1 F S R (applyActs blank (initActs blank k) ts)
    (by omega) (by omega) hinit'
  have happ : applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts =
      applyActs blank
        (oProg blank endSym mark orcB k (n + 1) Fo
          (applyActs blank (initActs blank k) ts))
        (applyActs blank (initActs blank k) ts) := by
    rw [fpProg, applyActs_append]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [fpProg, List.length_append, initActs_length]
    omega
  · intro p₁ m hc
    obtain ⟨hEnc, hwk⟩ := hsome p₁ m hc
    exact ⟨by rw [happ]; exact hEnc, hwk⟩
  · rw [happ]
    exact hex
  · intro hc
    obtain ⟨P, hP1, hP2, hP3⟩ := hnone hc
    exact ⟨P, hP1, hP2, by rw [happ]; exact hP3⟩

/-! ## 10. `Cr := k*p₁` の設定（カウンタ転送）と `extendReach` の合成 -/

/-- `Cq` を 1 減らして `Cr` を 1 増やす（3 動作）。 -/
def qrUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank .left, Act.Cq blank .stay, Act.Cr blank .right]

def qrLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => qrUnit blank ++ qrLoop blank n

@[simp] theorem qrLoop_length (blank : Fin sc) (n : ℕ) : (qrLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [qrLoop]
  | succ n ih => simp only [qrLoop, List.length_append, qrUnit, ih]; simp; omega

theorem applyActs_qrUnit (ts : Tapes sc) :
    applyActs blank (qrUnit blank) ts =
      { ts with
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay
        Cr := Tape.step blank ts.Cr blank .right } := rfl

theorem qrLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩
        (applyActs blank (qrLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [qrLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q + n, E, P, F, S, R + 1⟩
          (applyActs blank (qrUnit blank) ts) := by
        rw [applyActs_qrUnit]
        refine ⟨hE'.v1, hE'.v2, hE'.cd, ?_, hE'.ce, hE'.cp, hE'.cf, hE'.cs, ?_⟩
        · exact by simpa using Tape.counter'_dec (n := Q + n) hE'.cq
        · exact Tape.counter'_inc hE'.cr
      have := ih a b D Q E P F S (R + 1) _ hstep
      have e2 : R + 1 + n = R + (n + 1) := by omega
      rw [e2] at this
      simp only [qrLoop, applyActs_append]
      exact this

/-- `Cp` を 1 減らして `Cr` と `Ce` を 1 ずつ増やす（4 動作）。 -/
def pcUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.Cr blank .right, Act.Ce blank .right]

def pcLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => pcUnit blank ++ pcLoop blank n

@[simp] theorem pcLoop_length (blank : Fin sc) (n : ℕ) : (pcLoop blank n).length = 4 * n := by
  induction n with
  | zero => simp [pcLoop]
  | succ n ih => simp only [pcLoop, List.length_append, pcUnit, ih]; simp; omega

theorem applyActs_pcUnit (ts : Tapes sc) :
    applyActs blank (pcUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        Cr := Tape.step blank ts.Cr blank .right
        Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem pcLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R + n⟩
        (applyActs blank (pcLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [pcLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + 1, P + n, F, S, R + 1⟩
          (applyActs blank (pcUnit blank) ts) := by
        rw [applyActs_pcUnit]
        refine ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, ?_, ?_, hE'.cf, hE'.cs, ?_⟩
        · exact Tape.counter'_inc hE'.ce
        · exact by simpa using Tape.counter'_dec (n := P + n) hE'.cp
        · exact Tape.counter'_inc hE'.cr
      have := ih a b D Q (E + 1) P F S (R + 1) _ hstep
      have e2 : R + 1 + n = R + (n + 1) := by omega
      have e3 : E + 1 + n = E + (n + 1) := by omega
      rw [e2, e3] at this
      simp only [pcLoop, applyActs_append]
      exact this

/-- `Ce` を 1 減らして `Cp` を 1 増やす（3 動作）。 -/
def cpUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce blank .stay, Act.Cp blank .right]

def cpLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => cpUnit blank ++ cpLoop blank n

@[simp] theorem cpLoop_length (blank : Fin sc) (n : ℕ) : (cpLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [cpLoop]
  | succ n ih => simp only [cpLoop, List.length_append, cpUnit, ih]; simp; omega

theorem applyActs_cpUnit (ts : Tapes sc) :
    applyActs blank (cpUnit blank) ts =
      { ts with
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
        Cp := Tape.step blank ts.Cp blank .right } := rfl

theorem cpLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩
        (applyActs blank (cpLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [cpLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P + 1, F, S, R⟩
          (applyActs blank (cpUnit blank) ts) := by
        rw [applyActs_cpUnit]
        refine ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, ?_, ?_, hE'.cf, hE'.cs, hE'.cr⟩
        · exact by simpa using Tape.counter'_dec (n := E + n) hE'.ce
        · exact Tape.counter'_inc hE'.cp
      have := ih a b D Q E (P + 1) F S R _ hstep
      have e2 : P + 1 + n = P + (n + 1) := by omega
      rw [e2] at this
      simp only [cpLoop, applyActs_append]
      exact this

/-- `Cr := Cq + Cp`（`Cq := 0`、`Cp` は復元）。動作数 `3*Q + 7*P`。 -/
def loadR (blank : Fin sc) (Q P : ℕ) : List (Act sc) :=
  qrLoop blank Q ++ (pcLoop blank P ++ cpLoop blank P)

@[simp] theorem loadR_length (blank : Fin sc) (Q P : ℕ) :
    (loadR blank Q P).length = 3 * Q + 7 * P := by
  simp [loadR]; omega

theorem loadR_enc {a b D E P Q F S : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, 0⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, 0, E, P, F, S, Q + P⟩
      (applyActs blank (loadR blank Q P) ts) := by
  have h1 : Enc blank startSym endSym mark x a b ⟨D, 0, E, P, F, S, 0 + Q⟩
      (applyActs blank (qrLoop blank Q) ts) := by
    refine qrLoop_enc Q a b D 0 E P F S 0 ts ?_
    have e1 : (0 : ℕ) + Q = Q := by omega
    rw [e1]; exact hE
  have h2 : Enc blank startSym endSym mark x a b ⟨D, 0, E + P, 0, F, S, 0 + Q + P⟩
      (applyActs blank (pcLoop blank P) (applyActs blank (qrLoop blank Q) ts)) := by
    refine pcLoop_enc P a b D 0 E 0 F S (0 + Q) _ ?_
    have e2 : (0 : ℕ) + P = P := by omega
    rw [e2]; exact h1
  have h3 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P a b D 0 E 0 F S (0 + Q + P) _ h2
  have e3 : (0 : ℕ) + P = P := by omega
  have e4 : (0 : ℕ) + Q + P = Q + P := by omega
  rw [e3, e4] at h3
  rw [loadR, applyActs_append, applyActs_append]
  exact h3

/-- `firstOuter` は成功時に `(p, p + (k-1)*p)` を返す。 -/
theorem firstOuter_snd (v : List (Fin sc)) (k bound : ℕ) :
    ∀ (fuel p p' m : ℕ), firstOuter v k bound fuel p = some (p', m) → m = p' + (k - 1) * p' := by
  intro fuel
  induction fuel with
  | zero => intro p p' m hc; simp [firstOuter] at hc
  | succ fuel ih =>
      intro p p' m hc
      rw [firstOuter] at hc
      split_ifs at hc with h1 h2
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        rfl
      · exact ih _ p' m hc

/-- `firstPeriod` → `Cr := k*p₁` → `extendReach` の合成動作列。 -/
def frProg (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  fpProg blank endSym mark orcB k n Fo ts ++
    (loadR blank (qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
        (pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)) ++
      rProg blank endSym Fr
        (applyActs blank
          (loadR blank (qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
            (pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))
          (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))

/-- **主定理（`firstPeriod` + `extendReach` のテープ実現とコスト）**。
出力：`Cp = p₁`、`Cr = r`（`Cs` と `Cf` は不変）、ヘッドは `V1 = s + (r - p₁)`、`V2 = s + r`。 -/
theorem frProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s F S bound Fo n : ℕ} {ts : Tapes sc} {orcB : Tapes sc → Bool} (hs : s < x.length)
    (hn : (x.drop s).length ≤ n)
    (horcB : ∀ ts', orcB ts' = decide (pOf ts' < bound))
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, 0⟩ ts)
    {p₁ m : ℕ} (hfp : firstOuter (x.drop s) k bound Fo 1 = some (p₁, m)) :
    (Enc blank startSym endSym mark x
        (s + (extendReach (x.drop s) p₁ (x.length + 1) m - p₁))
        (s + extendReach (x.drop s) p₁ (x.length + 1) m)
        ⟨0, 0, 0, p₁, F, S, extendReach (x.drop s) p₁ (x.length + 1) m⟩
        (applyActs blank (frProg blank endSym mark orcB k n Fo (x.length + 1) ts) ts)
      ∧ (frProg blank endSym mark orcB k n Fo (x.length + 1) ts).length
          ≤ (k - 1) + 2
            + (2 * k + 32) * firstOuterWork (x.drop s) k bound Fo 1
            + 3 * extendReachWork (x.drop s) p₁ (x.length + 1) m
      ∧ (k - 1) * p₁ ≤ firstOuterWork (x.drop s) k bound Fo 1
      ∧ m ≤ extendReach (x.drop s) p₁ (x.length + 1) m
      ∧ extendReach (x.drop s) p₁ (x.length + 1) m
          ≤ m + extendReachWork (x.drop s) p₁ (x.length + 1) m) := by
  have hsle : s ≤ x.length := le_of_lt hs
  obtain ⟨hfcost, hfsome, _, _⟩ := fpProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hend hmark hs hn horcB hE
  obtain ⟨h1, hwk⟩ := hfsome p₁ m hfp
  have hm : m = p₁ + (k - 1) * p₁ := firstOuter_snd (x.drop s) k bound _ 1 p₁ m hfp
  -- カウンタ読み出し
  have hq1 : qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)
      = (k - 1) * p₁ := qOf_eq h1
  have hp1 : pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts) = p₁ :=
    pOf_eq h1
  -- `Cr := (k-1)*p₁ + p₁ = m`
  have h2 : Enc blank startSym endSym mark x (s + (k - 1) * p₁) (s + m)
      ⟨0, 0, 0, p₁, F, S, m⟩
      (applyActs blank
        (loadR blank (qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
          (pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))
        (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)) := by
    rw [hq1, hp1]
    have := loadR_enc (blank := blank) (startSym := startSym) (endSym := endSym) (mark := mark)
      (x := x) h1
    have e1 : (k - 1) * p₁ + p₁ = m := by omega
    rw [e1] at this
    exact this
  -- `extendReach`
  have hble : s + m ≤ x.length := pat_le h2.v2
  have hab : s + (k - 1) * p₁ ≤ s + m := by omega
  have h3 := rProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) hend (x.length + 1) _ (s + (k - 1) * p₁) (s + m)
    ⟨0, 0, 0, p₁, F, S, m⟩ h2 hab
  have hlen3 := rProg_length (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) hend (x.length + 1) _ (s + (k - 1) * p₁) (s + m)
    ⟨0, 0, 0, p₁, F, S, m⟩ h2 hab
  -- 添字レベルの対応
  have hcorr := rSteps_extendReach (x := x) (p := p₁) (s := s) hsle (x.length + 1) ((k - 1) * p₁)
    (by omega)
  have hidx1 : s + p₁ + (k - 1) * p₁ = s + m := by omega
  have hidx2 : p₁ + (k - 1) * p₁ = m := by omega
  rw [hidx1, hidx2] at hcorr
  obtain ⟨j, hj⟩ : ∃ j, rSteps x (x.length + 1) (s + (k - 1) * p₁) (s + m) = j := ⟨_, rfl⟩
  rw [hj] at h3 hcorr
  have hjw : rWork x (x.length + 1) (s + (k - 1) * p₁) (s + m)
      = extendReachWork (x.drop s) p₁ (x.length + 1) m := hcorr.2
  rw [hjw] at hlen3
  have hr : m + j = extendReach (x.drop s) p₁ (x.length + 1) m := hcorr.1
  have happ : applyActs blank (frProg blank endSym mark orcB k n Fo (x.length + 1) ts) ts
      = applyActs blank
          (rProg blank endSym (x.length + 1)
            (applyActs blank
              (loadR blank
                (qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
                (pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))
              (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))
          (applyActs blank
            (loadR blank
              (qOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))
              (pOf (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)))
            (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts)) := by
    rw [frProg, applyActs_append, applyActs_append]
  have hjle : j ≤ extendReachWork (x.drop s) p₁ (x.length + 1) m := by
    rw [← hjw, ← hj]
    exact rSteps_le_rWork x (x.length + 1) (s + (k - 1) * p₁) (s + m)
  refine ⟨?_, ?_, hwk, by omega, by omega⟩
  · rw [happ, ← hr]
    have e1 : s + (m + j - p₁) = s + (k - 1) * p₁ + j := by omega
    have e2 : s + (m + j) = s + m + j := by omega
    rw [e1, e2]
    exact h3
  · rw [frProg, List.length_append, List.length_append, loadR_length, hq1, hp1]
    have hple : p₁ ≤ (k - 1) * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
    obtain ⟨Wo, hWo⟩ : ∃ Wo, firstOuterWork (x.drop s) k bound Fo 1 = Wo := ⟨_, rfl⟩
    obtain ⟨ER, hER⟩ : ∃ ER, extendReachWork (x.drop s) p₁ (x.length + 1) m = ER := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T, (k - 1) * p₁ = T := ⟨_, rfl⟩
    rw [hq1, hp1] at hlen3
    rw [hWo] at hfcost hwk
    rw [hER] at hlen3
    rw [hT] at hwk hple hlen3
    rw [hWo, hER, hT]
    obtain ⟨A, hA⟩ : ∃ A, 2 * k + 22 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, 2 * k + 32 = B := ⟨_, rfl⟩
    rw [hA] at hfcost
    rw [hB]
    have hmono : A * Wo + 10 * Wo ≤ B * Wo := by
      calc A * Wo + 10 * Wo = (A + 10) * Wo := by ring
        _ ≤ B * Wo := Nat.mul_le_mul_right Wo (by omega)
    omega

end Outer

/-! ## 11. `_second_period` の内側ループ

`secondInner` は `v[q]` と `v[p+q]` を比べる双子走査で、番人条件は `p+q < |v|` のみ。
中断条件 `r < p + (q+1) ∧ (k-1)*p ≤ q+1` は `r` との比較を含むので、`GSScanTapes` が
走査段でしたのと同様に**オラクルビット** `orc : Tapes sc → Bool` として与える
（`horc` がその正しさ：読み出し `pOf` / `qOf` の関数として一致する）。 -/

section Second

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k r : ℕ}
  {orc : Tapes sc → Bool} {a b : ℕ} {c : Ctr} {ts : Tapes sc}

/-- 1 反復の継続条件。 -/
def sCond (endSym : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) : Prop :=
  Tape.read ts.V2 ≠ endSym ∧ Tape.read ts.V1 = Tape.read ts.V2 ∧ orc ts = false

instance sCond_dec (endSym : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) :
    Decidable (sCond endSym orc ts) := by unfold sCond; infer_instance

/-- 1 反復の動作列（継続なら 3 動作、停止なら 0 動作）。 -/
def sActs (blank endSym : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) : List (Act sc) :=
  if sCond endSym orc ts then [Act.V1 .right, Act.V2 .right, Act.Cq blank .right] else []

theorem sActs_length_pos (h : sCond endSym orc ts) :
    (sActs blank endSym orc ts).length = 3 := by simp [sActs, if_pos h]

theorem applyActs_sActs_pos (h : sCond endSym orc ts) :
    applyActs blank (sActs blank endSym orc ts) ts =
      { V1 := Tape.step blank ts.V1 ts.V1.focus .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Cq := Tape.step blank ts.Cq blank .right
        Cd := ts.Cd, Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr } := by
  simp only [sActs, if_pos h]
  rfl

theorem sCond_iff (hend : endSym ∉ x)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b) :
    sCond endSym orc ts ↔ (b < x.length ∧ x[a]? = x[b]? ∧ orc ts = false) := by
  have hble : b ≤ x.length := pat_le hE.v2
  by_cases hb : b < x.length
  · have hale : a < x.length := lt_of_le_of_lt hab hb
    have hV2 : Tape.read ts.V2 ≠ endSym := by
      intro hc
      have := (read_pat_end_iff hend hE.v2).1 hc
      omega
    have h1 := read_pat_lt hE.v1 hale
    have h2 := read_pat_lt hE.v2 hb
    constructor
    · rintro ⟨_, hm, ho⟩; exact ⟨hb, by rw [h1, h2, hm], ho⟩
    · rintro ⟨_, hm, ho⟩
      refine ⟨hV2, ?_, ho⟩
      rw [h1, h2] at hm
      exact Option.some.inj hm
  · have hbe : b = x.length := by omega
    have hV2 : Tape.read ts.V2 = endSym := read_pat_end hE.v2 hbe
    constructor
    · rintro ⟨h1, _, _⟩; exact absurd hV2 h1
    · rintro ⟨h1, _, _⟩; omega

theorem enc_s_step (hend : endSym ∉ x)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (h : sCond endSym orc ts) :
    Enc blank startSym endSym mark x (a + 1) (b + 1) { c with q := c.q + 1 }
      (applyActs blank (sActs blank endSym orc ts) ts) := by
  obtain ⟨hb, _, _⟩ := (sCond_iff hend hE hab).1 h
  have hale : a < x.length := lt_of_le_of_lt hab hb
  rw [applyActs_sActs_pos h]
  exact ⟨pat_right hE.v1 hale, pat_right hE.v2 hb, hE.cd, Tape.counter'_inc hE.cq,
    hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- 添字レベルの走査歩数（中断条件込み）。 -/
def sSteps (x : List (Fin sc)) (k p r s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      if s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
          ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) then
        1 + sSteps x k p r s fuel (q + 1)
      else 0

/-- 添字レベルの仕事量（`secondInnerWork` と同じ数え方）。 -/
def sWork (x : List (Fin sc)) (k p r s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      1 + (if s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? then
             (if r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1 then 0
              else sWork x k p r s fuel (q + 1))
           else 0)

/-- 内側ループ全体の動作列。 -/
def sProg (blank endSym : Fin sc) (orc : Tapes sc → Bool) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if sCond endSym orc ts then
        sActs blank endSym orc ts ++
          sProg blank endSym orc fuel (applyActs blank (sActs blank endSym orc ts) ts)
      else []

/-- **主定理（`_second_period` 内側ループの実現とコスト）**。
オラクル `orc` は読み出し `pOf` / `qOf` の関数として中断条件を返すと仮定する。 -/
theorem sProg_spec (hend : endSym ∉ x)
    (horc : ∀ ts', orc ts' = decide (r < pOf ts' + qOf ts' + 1 ∧ (k - 1) * pOf ts' ≤ qOf ts' + 1)) :
    ∀ (fuel q D E p F S R : ℕ) (ts : Tapes sc),
      Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, E, p, F, S, R⟩ ts →
        (Enc blank startSym endSym mark x (s + q + sSteps x k p r s fuel q)
            (s + p + q + sSteps x k p r s fuel q)
            ⟨D, q + sSteps x k p r s fuel q, E, p, F, S, R⟩
            (applyActs blank (sProg blank endSym orc fuel ts) ts)
          ∧ (sProg blank endSym orc fuel ts).length ≤ 3 * sWork x k p r s fuel q) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q D E p F S R ts hE
      exact ⟨by simpa [sSteps, sProg] using hE, by simp [sProg, sWork]⟩
  | succ fuel ih =>
      intro q D E p F S R ts hE
      have hab : s + q ≤ s + p + q := by omega
      have hpq : pOf ts = p := pOf_eq hE
      have hqq : qOf ts = q := qOf_eq hE
      have horcq : orc ts = decide (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
        rw [horc ts, hpq, hqq, Nat.add_assoc]
      by_cases h : sCond endSym orc ts
      · obtain ⟨hb, hm, ho⟩ := (sCond_iff hend hE hab).1 h
        have hnab : ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
          rw [horcq] at ho
          exact of_decide_eq_false ho
        have hcond : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
            ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := ⟨hb, hm, hnab⟩
        have hstep := enc_s_step (orc := orc) hend hE hab h
        have hrec := ih (q + 1) D E p F S R (applyActs blank (sActs blank endSym orc ts) ts)
          (by
            have e1 : s + q + 1 = s + (q + 1) := by omega
            have e2 : s + p + q + 1 = s + p + (q + 1) := by omega
            rw [e1, e2] at hstep
            exact hstep)
        constructor
        · simp only [sSteps, if_pos hcond, sProg, if_pos h, applyActs_append]
          have e1 : s + q + (1 + sSteps x k p r s fuel (q + 1))
              = s + (q + 1) + sSteps x k p r s fuel (q + 1) := by omega
          have e2 : s + p + q + (1 + sSteps x k p r s fuel (q + 1))
              = s + p + (q + 1) + sSteps x k p r s fuel (q + 1) := by omega
          have e3 : q + (1 + sSteps x k p r s fuel (q + 1))
              = q + 1 + sSteps x k p r s fuel (q + 1) := by omega
          rw [e1, e2, e3]
          exact hrec.1
        · have h2 := hrec.2
          have hbm : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? := ⟨hb, hm⟩
          simp only [sProg, if_pos h, sWork, if_pos hbm, if_neg hnab, List.length_append,
            sActs_length_pos h]
          omega
      · have hg : ¬ (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
            ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)) := by
          intro hc
          refine h ((sCond_iff hend hE hab).2 ⟨hc.1, hc.2.1, ?_⟩)
          rw [horcq]
          exact decide_eq_false hc.2.2
        constructor
        · simp only [sSteps, if_neg hg, sProg, if_neg h]
          simpa using hE
        · simp only [sProg, if_neg h, sWork]
          simp

/-- 添字レベルの対応：`sWork` は `secondInnerWork` と一致し、`sSteps` は
`secondInner` が `some q'` を返すときの一致長を与える。 -/
theorem sSteps_secondInner {p : ℕ} (hs : s ≤ x.length) :
    ∀ (fuel q : ℕ), s + p + q ≤ x.length →
      ((∀ q', secondInner (x.drop s) k p r fuel q = some q' →
          q + sSteps x k p r s fuel q = q')
        ∧ sWork x k p r s fuel q = secondInnerWork (x.drop s) k p r fuel q) := by
  have hguard : ∀ q : ℕ, (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]?) ↔
      (p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?) := by
    intro q
    have hlen : (x.drop s).length = x.length - s := by simp
    have e1 : (x.drop s)[q]? = x[s + q]? := List.getElem?_drop
    have e2 : (x.drop s)[p + q]? = x[s + p + q]? := by
      rw [List.getElem?_drop]; congr 1; omega
    rw [hlen, e1, e2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  intro fuel
  induction fuel with
  | zero =>
      intro q _
      refine ⟨?_, by simp [sWork, secondInnerWork]⟩
      intro q' hc
      simp only [secondInner, Option.some.injEq] at hc
      simp [sSteps]
      omega
  | succ fuel ih =>
      intro q hle
      by_cases hg : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]?
      · have hg' := (hguard q).1 hg
        by_cases hab : r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1
        · refine ⟨?_, ?_⟩
          · intro q' hc
            rw [secondInner, if_pos hg', if_pos hab] at hc
            simp at hc
          · simp only [sWork, if_pos hg, if_pos hab, secondInnerWork, if_pos hg']
        · have hrec := ih (q + 1) (by omega)
          have e1 : s + p + (q + 1) = s + p + q + 1 := by omega
          have e2 : s + (q + 1) = s + q + 1 := by omega
          refine ⟨?_, ?_⟩
          · intro q' hc
            rw [secondInner, if_pos hg', if_neg hab] at hc
            have := hrec.1 q' hc
            have hc3 : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
                ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := ⟨hg.1, hg.2, hab⟩
            simp only [sSteps, if_pos hc3]
            omega
          · simp only [sWork, if_pos hg, secondInnerWork, if_pos hg', if_neg hab]
            exact congrArg (1 + ·) hrec.2
      · have hg' : ¬ (p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?) :=
          fun hc => hg ((hguard q).2 hc)
        refine ⟨?_, ?_⟩
        · intro q' hc
          rw [secondInner, if_neg hg'] at hc
          simp only [Option.some.injEq] at hc
          simp only [sSteps, if_neg (fun hc' : _ ∧ _ ∧ _ => hg ⟨hc'.1, hc'.2.1⟩)]
          omega
        · simp only [sWork, if_neg hg, secondInnerWork, if_neg hg']


/-! ### 内側ループの停止理由（中断か通常終了か） -/

/-- 添字レベルの「中断」条件（`secondInner` が `none` を返す状態）。 -/
def AbortAt (x : List (Fin sc)) (k p r s q : ℕ) : Prop :=
  s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
    (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)

instance AbortAt_dec (x : List (Fin sc)) (k p r s q : ℕ) : Decidable (AbortAt x k p r s q) := by
  unfold AbortAt; infer_instance

theorem sSteps_le_sWork (x : List (Fin sc)) (k p r s : ℕ) :
    ∀ fuel q, sSteps x k p r s fuel q ≤ sWork x k p r s fuel q := by
  intro fuel
  induction fuel with
  | zero => intro q; simp [sSteps, sWork]
  | succ fuel ih =>
      intro q
      by_cases hg : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
          ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)
      · have := ih (q + 1)
        have hg2 : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? := ⟨hg.1, hg.2.1⟩
        rw [sSteps, if_pos hg, sWork, if_pos hg2, if_neg hg.2.2]
        omega
      · rw [sSteps, if_neg hg, sWork]
        omega

/-- 走査後の位置は `x` の範囲に収まる。 -/
theorem sSteps_fit (x : List (Fin sc)) (k p r s : ℕ) :
    ∀ fuel q, s + p + q ≤ x.length → s + p + (q + sSteps x k p r s fuel q) ≤ x.length := by
  intro fuel
  induction fuel with
  | zero => intro q h; simpa [sSteps] using h
  | succ fuel ih =>
      intro q h
      by_cases hg : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
          ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)
      · have := ih (q + 1) (by omega)
        rw [sSteps, if_pos hg]
        omega
      · rw [sSteps, if_neg hg]
        omega

/-- 燃料が十分なら、`secondInner` が `none` を返すことと最終位置での中断条件は同値。 -/
theorem sInner_none_iff {x : List (Fin sc)} {k p r s : ℕ} (hs : s ≤ x.length) :
    ∀ (fuel q : ℕ), s + p + q ≤ x.length → x.length ≤ fuel + q + s →
      (secondInner (x.drop s) k p r fuel q = none ↔
        AbortAt x k p r s (q + sSteps x k p r s fuel q)) := by
  have hguard : ∀ q : ℕ, (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]?) ↔
      (p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?) := by
    intro q
    have hlen : (x.drop s).length = x.length - s := by simp
    have e1 : (x.drop s)[q]? = x[s + q]? := List.getElem?_drop
    have e2 : (x.drop s)[p + q]? = x[s + p + q]? := by
      rw [List.getElem?_drop]; congr 1; omega
    rw [hlen, e1, e2]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  intro fuel
  induction fuel with
  | zero =>
      intro q hle hf
      simp only [secondInner, sSteps, Nat.add_zero]
      constructor
      · intro hc; simp at hc
      · rintro ⟨h1, -, -⟩; omega
  | succ fuel ih =>
      intro q hle hf
      by_cases hg : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]?
      · have hg' := (hguard q).1 hg
        by_cases hab : r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1
        · have hstop : ¬ (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
              ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)) := by
            rintro ⟨-, -, h3⟩; exact h3 hab
          rw [secondInner, if_pos hg', if_pos hab, sSteps, if_neg hstop, Nat.add_zero]
          simp only [AbortAt]
          exact ⟨fun _ => ⟨hg.1, hg.2, hab⟩, fun _ => trivial⟩
        · have hcont : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
              ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := ⟨hg.1, hg.2, hab⟩
          have := ih (q + 1) (by omega) (by omega)
          rw [secondInner, if_pos hg', if_neg hab, sSteps, if_pos hcont]
          have e1 : q + (1 + sSteps x k p r s fuel (q + 1))
              = (q + 1) + sSteps x k p r s fuel (q + 1) := by omega
          rw [e1]
          exact this
      · have hg' : ¬ (p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?) :=
          fun hc => hg ((hguard q).2 hc)
        have hstop : ¬ (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
            ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)) := by
          rintro ⟨h1, h2, -⟩; exact hg ⟨h1, h2⟩
        rw [secondInner, if_neg hg', sSteps, if_neg hstop, Nat.add_zero]
        simp only [AbortAt]
        constructor
        · intro hc; simp at hc
        · rintro ⟨h1, h2, -⟩; exact absurd ⟨h1, h2⟩ hg

/-- テープ側の「中断」判定（すべて読み取りで決まる）。 -/
def sAbort (endSym : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) : Prop :=
  Tape.read ts.V2 ≠ endSym ∧ Tape.read ts.V1 = Tape.read ts.V2 ∧ orc ts = true

instance sAbort_dec (endSym : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) :
    Decidable (sAbort endSym orc ts) := by unfold sAbort; infer_instance

theorem sAbort_iff (hend : endSym ∉ x)
    (horc : ∀ ts', orc ts' = decide (r < pOf ts' + qOf ts' + 1 ∧ (k - 1) * pOf ts' ≤ qOf ts' + 1))
    {q D E p F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, E, p, F, S, R⟩ ts) :
    sAbort endSym orc ts ↔ AbortAt x k p r s q := by
  have hab : s + q ≤ s + p + q := by omega
  have hble : s + p + q ≤ x.length := pat_le hE.v2
  have hpq : pOf ts = p := pOf_eq hE
  have hqq : qOf ts = q := qOf_eq hE
  have horcq : orc ts = decide (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
    rw [horc ts, hpq, hqq, Nat.add_assoc]
  unfold sAbort AbortAt
  rw [horcq]
  by_cases hb : s + p + q < x.length
  · have hale : s + q < x.length := by omega
    have hV2 : Tape.read ts.V2 ≠ endSym := by
      intro hc
      have := (read_pat_end_iff hend hE.v2).1 hc
      omega
    have h1 := read_pat_lt hE.v1 hale
    have h2 := read_pat_lt hE.v2 hb
    constructor
    · rintro ⟨-, hm, ho⟩
      exact ⟨hb, by rw [h1, h2, hm], of_decide_eq_true ho⟩
    · rintro ⟨-, hm, hc⟩
      rw [h1, h2] at hm
      exact ⟨hV2, Option.some.inj hm, decide_eq_true hc⟩
  · have hbe : s + p + q = x.length := by omega
    have hV2 : Tape.read ts.V2 = endSym := read_pat_end hE.v2 hbe
    constructor
    · rintro ⟨h1, -, -⟩; exact absurd hV2 h1
    · rintro ⟨h1, -, -⟩; omega


/-! ### 周期ずらし（`p += first`, `q -= first`、`V2` は不動で `V1` を `first` だけ左へ） -/

/-- `Cf` の読み出し。 -/
def fOf (ts : Tapes sc) : ℕ := ts.Cf.left.length - 1

theorem fOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : fOf ts = c.f := ctr_len hE.cf

/-- 周期ずらし 1 単位（7 動作）。`V2` は動かない。 -/
def perUnit (blank : Fin sc) : List (Act sc) :=
  [Act.V1 .left, Act.Cq blank .left, Act.Cq blank .stay, Act.Cp blank .right,
    Act.Cf blank .left, Act.Cf blank .stay, Act.Ce blank .right]

theorem applyActs_perUnit (ts : Tapes sc) :
    applyActs blank (perUnit blank) ts =
      { ts with
        V1 := Tape.step blank ts.V1 ts.V1.focus .left
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay
        Cp := Tape.step blank ts.Cp blank .right
        Cf := Tape.step blank (Tape.step blank ts.Cf blank .left) blank .stay
        Ce := Tape.step blank ts.Ce blank .right } := rfl

def perLoop1 (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => perUnit blank ++ perLoop1 blank n

@[simp] theorem perLoop1_length (blank : Fin sc) (n : ℕ) :
    (perLoop1 blank n).length = 7 * n := by
  induction n with
  | zero => simp [perLoop1]
  | succ n ih => simp only [perLoop1, List.length_append, perUnit, ih]; simp; omega

theorem perLoop1_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P + n, F, S, R⟩
        (applyActs blank (perLoop1 blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [perLoop1] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) b
          ⟨D, (Q + n) + 1, E, P, (F + n) + 1, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : Q + (n + 1) = (Q + n) + 1 := by omega
        have e3 : F + (n + 1) = (F + n) + 1 := by omega
        rw [e1, e2, e3] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x (a + n) b
          ⟨D, Q + n, E + 1, P + 1, F + n, S, R⟩ (applyActs blank (perUnit blank) ts) := by
        rw [applyActs_perUnit]
        refine ⟨pat_left hE'.v1, hE'.v2, hE'.cd, ?_, Tape.counter'_inc hE'.ce,
          Tape.counter'_inc hE'.cp, ?_, hE'.cs, hE'.cr⟩
        · exact by simpa using Tape.counter'_dec (n := Q + n) hE'.cq
        · exact by simpa using Tape.counter'_dec (n := F + n) hE'.cf
      have := ih a b D Q (E + 1) (P + 1) F S R _ hstep
      have e4 : E + 1 + n = E + (n + 1) := by omega
      have e5 : P + 1 + n = P + (n + 1) := by omega
      rw [e4, e5] at this
      simp only [perLoop1, applyActs_append]
      exact this

/-- `Ce` を `Cf` へ戻す（1 単位 3 動作）。 -/
def cfLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => [Act.Ce blank .left, Act.Ce blank .stay, Act.Cf blank .right] ++ cfLoop blank n

@[simp] theorem cfLoop_length (blank : Fin sc) (n : ℕ) : (cfLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [cfLoop]
  | succ n ih => simp only [cfLoop, List.length_append, ih]; simp; omega

theorem cfLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩
        (applyActs blank (cfLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [cfLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hres : applyActs blank [Act.Ce blank .left, Act.Ce blank .stay,
          Act.Cf (sc := sc) blank .right] ts =
          { ts with
            Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
            Cf := Tape.step blank ts.Cf blank .right } := rfl
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F + 1, S, R⟩
          (applyActs blank [Act.Ce blank .left, Act.Ce blank .stay,
            Act.Cf (sc := sc) blank .right] ts) := by
        rw [hres]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq,
          by simpa using Tape.counter'_dec (n := E + n) hE'.ce, hE'.cp,
          Tape.counter'_inc hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P (F + 1) S R _ hstep
      have e2 : F + 1 + n = F + (n + 1) := by omega
      rw [e2] at this
      simp only [cfLoop, applyActs_append]
      exact this

/-- 周期ずらし（`10*n` 動作）。 -/
def periodShift (blank : Fin sc) (n : ℕ) : List (Act sc) :=
  perLoop1 blank n ++ cfLoop blank n

@[simp] theorem periodShift_length (blank : Fin sc) (n : ℕ) :
    (periodShift blank n).length = 10 * n := by
  simp [periodShift]; omega

theorem periodShift_enc {n a b D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F + n, S, R⟩
      (applyActs blank (periodShift blank n) ts) := by
  have h1 := perLoop1_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) n a b D Q E P F S R ts hE
  have h2 := cfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) n a b D Q E (P + n) F S R _ h1
  rw [periodShift, applyActs_append]
  exact h2


/-! ### `_second_period` の外側ループ -/

/-- `Cq` のゼロ判定 probe と復元（2 動作）。 -/
def soTest (blank : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  [Act.Cq blank .left, Act.Cq (probe blank ts.Cq) .right]

@[simp] theorem soTest_length (blank : Fin sc) (ts : Tapes sc) :
    (soTest blank ts).length = 2 := rfl

theorem soTest_enc {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) :
    Enc blank startSym endSym mark x a b c (applyActs blank (soTest blank ts) ts) := by
  have hres : applyActs blank (soTest blank ts) ts =
      { ts with
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) (probe blank ts.Cq) .right } :=
    rfl
  rw [hres]
  exact ⟨hE.v1, hE.v2, hE.cd, counter'_test hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- 外側の番人条件：`q = 0` かつ `V2` が右端番人を読むときだけ停止する。 -/
def soCond (blank endSym mark : Fin sc) (ts : Tapes sc) : Prop :=
  ¬ (probe blank ts.Cq = mark ∧ Tape.read ts.V2 = endSym)

instance soCond_dec (blank endSym mark : Fin sc) (ts : Tapes sc) :
    Decidable (soCond blank endSym mark ts) := by unfold soCond; infer_instance

def soAfterTest (blank : Fin sc) (ts : Tapes sc) : Tapes sc :=
  applyActs blank (soTest blank ts) ts

def soInner (blank endSym : Fin sc) (orc : Tapes sc → Bool) (Fs : ℕ) (ts : Tapes sc) :
    List (Act sc) :=
  sProg blank endSym orc Fs (soAfterTest blank ts)

def soAfterInner (blank endSym : Fin sc) (orc : Tapes sc → Bool) (Fs : ℕ) (ts : Tapes sc) :
    Tapes sc :=
  applyActs blank (soInner blank endSym orc Fs ts) (soAfterTest blank ts)

/-- ずらし部（中断なら空、周期ずらしかリセットずらし）。 -/
def soShift (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  if sAbort endSym orc (soAfterInner blank endSym orc Fs ts) then []
  else if orc2 (soAfterInner blank endSym orc Fs ts) then
    periodShift blank (fOf (soAfterInner blank endSym orc Fs ts))
  else shiftPhase blank mark k (soAfterInner blank endSym orc Fs ts)

def soAfterShift (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ)
    (ts : Tapes sc) : Tapes sc :=
  applyActs blank (soShift blank endSym mark orc orc2 k Fs ts)
    (soAfterInner blank endSym orc Fs ts)

/-- `_second_period` の外側ループ全体の動作列。 -/
def soProg (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if soCond blank endSym mark ts then
        soTest blank ts ++ (soInner blank endSym orc Fs ts ++
          (soShift blank endSym mark orc orc2 k Fs ts ++
            (if sAbort endSym orc (soAfterInner blank endSym orc Fs ts) then []
             else soProg blank endSym mark orc orc2 k Fs fuel
               (soAfterShift blank endSym mark orc orc2 k Fs ts))))
      else soTest blank ts


/-- **主定理（`_second_period` 外側ループの実現とコスト）**。
`A = k + 12`, `B = 2`：総動作数は `(k+12) * secondOuterWork + (k+9) * q + 2` 以下。
入口 `q = 0`（`secondPeriod`）なら `(k+12) * secondOuterWork + 2`。
オラクル `orc`（中断条件）と `orc2`（`k*first ≤ q' ∧ q' ≤ r`）は読み出しの関数として仮定する。 -/
theorem soProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s first S R : ℕ} (hs : s ≤ x.length) (_hfirst : 0 < first)
    (horc : ∀ ts', orc ts' = decide (r < pOf ts' + qOf ts' + 1 ∧ (k - 1) * pOf ts' ≤ qOf ts' + 1))
    (horc2 : ∀ ts', orc2 ts' = decide (k * first ≤ qOf ts' ∧ qOf ts' ≤ r)) :
    ∀ (fuel p q D : ℕ) (ts : Tapes sc), s + p + q ≤ x.length →
      Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, 0, p, first, S, R⟩ ts →
      ((soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel ts).length
          ≤ (k + 12) * secondOuterWork (x.drop s) k first r fuel p q + (k + 9) * q + 2
        ∧ (∃ a b D' q' E' P',
            Enc blank startSym endSym mark x a b ⟨D', q', E', P', first, S, R⟩
              (applyActs blank
                (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel ts) ts)
            ∧ (∀ p₂, secondOuter (x.drop s) k first r fuel p q = some p₂ → P' = p₂))) := by
  have hdrop : (x.drop s).length = x.length - s := by simp
  intro fuel
  induction fuel with
  | zero =>
      intro p q D ts _ hE
      refine ⟨by simp [soProg, secondOuterWork], ⟨s + q, s + p + q, D, q, 0, p, ?_, ?_⟩⟩
      · rw [soProg, applyActs_nil]; exact hE
      · intro p₂ hc; rw [secondOuter] at hc; simp at hc
  | succ fuel ih =>
      intro p q D ts hfit hE
      have hq0 : probe blank ts.Cq = mark ↔ q = 0 := probe_iff hmark hE.cq
      have hv2 : Tape.read ts.V2 = endSym ↔ s + p + q = x.length := read_pat_end_iff hend hE.v2
      have hguard : soCond blank endSym mark ts ↔ p < (x.drop s).length := by
        unfold soCond
        rw [hq0, hv2, hdrop]
        omega
      by_cases hc : soCond blank endSym mark ts
      · have hg : p < (x.drop s).length := hguard.1 hc
        -- 内側走査
        have hE0 : Enc blank startSym endSym mark x (s + q) (s + p + q)
            ⟨D, q, 0, p, first, S, R⟩ (soAfterTest blank ts) := soTest_enc hE
        obtain ⟨hEnc2, hcost2⟩ := sProg_spec (blank := blank) (startSym := startSym)
          (endSym := endSym) (mark := mark) (x := x) (k := k) (r := r) (orc := orc) hend horc
          ((x.drop s).length + 1) q D 0 p first S R (soAfterTest blank ts) hE0
        obtain ⟨j, hj⟩ : ∃ j, sSteps x k p r s ((x.drop s).length + 1) q = j := ⟨_, rfl⟩
        rw [hj] at hEnc2
        have hE2 : Enc blank startSym endSym mark x (s + (q + j)) (s + p + (q + j))
            ⟨D, q + j, 0, p, first, S, R⟩ (soAfterInner blank endSym orc
              ((x.drop s).length + 1) ts) := by
          have e1 : s + q + j = s + (q + j) := by omega
          have e2 : s + p + q + j = s + p + (q + j) := by omega
          rw [e1, e2] at hEnc2
          exact hEnc2
        have hfit2 : s + p + (q + j) ≤ x.length := by
          have := sSteps_fit x k p r s ((x.drop s).length + 1) q hfit
          omega
        have hWeq : sWork x k p r s ((x.drop s).length + 1) q
            = secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q :=
          (sSteps_secondInner (x := x) (k := k) (r := r) (p := p) hs
            ((x.drop s).length + 1) q hfit).2
        have hjW : j ≤ sWork x k p r s ((x.drop s).length + 1) q := by
          rw [← hj]; exact sSteps_le_sWork x k p r s _ q
        have hnone := sInner_none_iff (x := x) (k := k) (p := p) (r := r) hs
          ((x.drop s).length + 1) q hfit (by omega)
        rw [hj] at hnone
        have habort := sAbort_iff (blank := blank) (startSym := startSym) (endSym := endSym)
          (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (s := s) hend horc hE2
        rw [hWeq] at hjW hcost2
        obtain ⟨W, hW⟩ : ∃ W, secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q = W :=
          ⟨_, rfl⟩
        rw [hW] at hcost2 hjW
        by_cases hab : sAbort endSym orc (soAfterInner blank endSym orc
            ((x.drop s).length + 1) ts)
        · -- 中断：第 2 周期 `p` を発見
          have hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = none :=
            hnone.2 (habort.1 hab)
          have hshift0 : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts = [] := by
            rw [soShift, if_pos hab]
          have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
              = soTest blank ts ++ soInner blank endSym orc ((x.drop s).length + 1) ts := by
            rw [soProg, if_pos hc, if_pos hab, hshift0]
            simp
          have happ : applyActs blank
              (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts) ts
              = soAfterInner blank endSym orc ((x.drop s).length + 1) ts := by
            rw [hprog, applyActs_append]
            rfl
          refine ⟨?_, ⟨s + (q + j), s + p + (q + j), D, q + j, 0, p, by rw [happ]; exact hE2, ?_⟩⟩
          · rw [hprog, secondOuterWork, if_pos hg]
            simp only [hsi, hW, List.length_append, soTest_length]
            have h3 : (soInner blank endSym orc ((x.drop s).length + 1) ts).length ≤ 3 * W :=
              hcost2
            have hmono : 3 * W ≤ (k + 12) * W := Nat.mul_le_mul_right W (by omega)
            have hmono2 : 0 ≤ (k + 12) * (1 + W + 0) := Nat.zero_le _
            have hexp : (k + 12) * (1 + W + 0) = (k + 12) + (k + 12) * W := by ring
            omega
          · intro p₂ hp2
            rw [secondOuter, if_pos hg] at hp2
            simp only [hsi, Option.some.injEq] at hp2
            omega
        · -- 通常終了：`secondInner = some (q + j)`
          have hnab : ¬ AbortAt x k p r s (q + j) := fun hcc => hab (habort.2 hcc)
          have hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = some (q + j) := by
            rcases hsome : secondInner (x.drop s) k p r ((x.drop s).length + 1) q with _ | q'
            · exact absurd (hnone.1 hsome) hnab
            · have := (sSteps_secondInner (x := x) (k := k) (r := r) (p := p) hs
                ((x.drop s).length + 1) q hfit).1 q' hsome
              rw [hj] at this
              rw [this]
          have hq2 : qOf (soAfterInner blank endSym orc ((x.drop s).length + 1) ts) = q + j :=
            qOf_eq hE2
          have hf2 : fOf (soAfterInner blank endSym orc ((x.drop s).length + 1) ts) = first :=
            fOf_eq hE2
          have horc2q : orc2 (soAfterInner blank endSym orc ((x.drop s).length + 1) ts)
              = decide (k * first ≤ q + j ∧ q + j ≤ r) := by
            rw [horc2, hq2]
          by_cases hb2 : k * first ≤ q + j ∧ q + j ≤ r
          · -- 周期ずらし
            have hfq : first ≤ q + j := by
              have : first ≤ k * first := Nat.le_mul_of_pos_left first (by omega)
              omega
            have horcT : orc2 (soAfterInner blank endSym orc ((x.drop s).length + 1) ts) = true := by
              rw [horc2q]; exact decide_eq_true hb2
            have hshift : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts
                = periodShift blank first := by
              rw [soShift, if_neg hab, if_pos horcT, hf2]
            have hE3 : Enc blank startSym endSym mark x (s + (q + j - first))
                (s + (p + first) + (q + j - first))
                ⟨D, q + j - first, 0, p + first, first, S, R⟩
                (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              have hpre : Enc blank startSym endSym mark x ((s + (q + j - first)) + first)
                  (s + p + (q + j)) ⟨D, (q + j - first) + first, 0, p, 0 + first, S, R⟩
                  (soAfterInner blank endSym orc ((x.drop s).length + 1) ts) := by
                have e1 : (s + (q + j - first)) + first = s + (q + j) := by omega
                have e2 : (q + j - first) + first = q + j := by omega
                have e3 : (0 : ℕ) + first = first := by omega
                rw [e1, e2, e3]
                exact hE2
              have := periodShift_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) hpre
              have e4 : s + p + (q + j) = s + (p + first) + (q + j - first) := by omega
              have e5 : (0 : ℕ) + first = first := by omega
              rw [e4, e5] at this
              rw [soAfterShift, hshift]
              exact this
            obtain ⟨hrc, hre⟩ := ih (p + first) (q + j - first) D _ (by omega) hE3
            have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
                = soTest blank ts ++ (soInner blank endSym orc ((x.drop s).length + 1) ts ++
                  (soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts ++
                    soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel
                      (soAfterShift blank endSym mark orc orc2 k
                        ((x.drop s).length + 1) ts))) := by
              rw [soProg, if_pos hc, if_neg hab]
            have happ : applyActs blank
                (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts) ts
                = applyActs blank (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1)
                    fuel (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts))
                  (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              rw [hprog, applyActs_append, applyActs_append, applyActs_append]
              simp only [soAfterInner, soAfterTest, soAfterShift]
            have hso : secondOuter (x.drop s) k first r (fuel + 1) p q
                = secondOuter (x.drop s) k first r fuel (p + first) (q + j - first) := by
              rw [secondOuter, if_pos hg]
              simp only [hsi, if_pos hb2]
            refine ⟨?_, ?_⟩
            · rw [hprog, secondOuterWork, if_pos hg]
              simp only [hsi, if_pos hb2, hW, List.length_append, soTest_length, hshift,
                periodShift_length]
              have h3 : (soInner blank endSym orc ((x.drop s).length + 1) ts).length ≤ 3 * W :=
                hcost2
              obtain ⟨Wr, hWr⟩ : ∃ Wr, secondOuterWork (x.drop s) k first r fuel (p + first)
                  (q + j - first) = Wr := ⟨_, rfl⟩
              rw [hWr] at hrc
              rw [hWr]
              obtain ⟨A, hA⟩ : ∃ A, k + 12 = A := ⟨_, rfl⟩
              obtain ⟨C, hC⟩ : ∃ C, k + 9 = C := ⟨_, rfl⟩
              rw [hA, hC] at hrc ⊢
              have hexp : A * (1 + W + Wr) = A + A * W + A * Wr := by ring
              have hmul : 3 * W + C * W ≤ A * W := by
                calc 3 * W + C * W = (3 + C) * W := by ring
                  _ ≤ A * W := Nat.mul_le_mul_right W (by omega)
              have hCsub : C * (q + j - first) + C * first = C * (q + j) := by
                rw [← Nat.mul_add]
                congr 1
                omega
              have hCq : C * (q + j) ≤ C * q + C * W := by
                have : C * (q + j) = C * q + C * j := by ring
                have h2 : C * j ≤ C * W := Nat.mul_le_mul_left C (by omega)
                omega
              have hfC : 10 * first ≤ C * first := Nat.mul_le_mul_right first (by omega)
              omega
            · obtain ⟨a', b', D', q', E', P', hEnc', hp2⟩ := hre
              exact ⟨a', b', D', q', E', P', by rw [happ]; exact hEnc',
                by intro p₂ hh; exact hp2 p₂ (by rw [← hso]; exact hh)⟩
          · -- リセットずらし
            have horcF : orc2 (soAfterInner blank endSym orc ((x.drop s).length + 1) ts)
                = false := by
              rw [horc2q]; exact decide_eq_false hb2
            have hshift : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts
                = shiftPhase blank mark k
                  (soAfterInner blank endSym orc ((x.drop s).length + 1) ts) := by
              rw [soShift, if_neg hab, horcF]
              simp
            have hfitE : s + p + shiftNoPeriod (q + j) k ≤ x.length := by
              rcases Nat.eq_zero_or_pos (q + j) with h0 | h0
              · rw [h0, shiftNoPeriod_zero (by omega)]
                omega
              · have := shiftNoPeriod_le_of_pos (k := k) (by omega) h0
                omega
            obtain ⟨hE3, hlen3⟩ := shiftPhase_enc' (blank := blank) (startSym := startSym)
              (endSym := endSym) (mark := mark) (x := x) (k := k) (by omega) hmark hE2 hfitE
            have hE3' : Enc blank startSym endSym mark x s
                (s + (p + shiftNoPeriod (q + j) k))
                ⟨D + (q + j) + (k - 1) * shiftNoPeriod (q + j) k, 0, 0,
                  p + shiftNoPeriod (q + j) k, first, S, R⟩
                (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              rw [soAfterShift, hshift]
              have e1 : s + p + shiftNoPeriod (q + j) k
                  = s + (p + shiftNoPeriod (q + j) k) := by omega
              rw [e1] at hE3
              exact hE3
            obtain ⟨hrc, hre⟩ := ih (p + shiftNoPeriod (q + j) k) 0
              (D + (q + j) + (k - 1) * shiftNoPeriod (q + j) k) _ (by omega) hE3'
            have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
                = soTest blank ts ++ (soInner blank endSym orc ((x.drop s).length + 1) ts ++
                  (soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts ++
                    soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel
                      (soAfterShift blank endSym mark orc orc2 k
                        ((x.drop s).length + 1) ts))) := by
              rw [soProg, if_pos hc, if_neg hab]
            have happ : applyActs blank
                (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts) ts
                = applyActs blank (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1)
                    fuel (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts))
                  (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              rw [hprog, applyActs_append, applyActs_append, applyActs_append]
              simp only [soAfterInner, soAfterTest, soAfterShift]
            have hso : secondOuter (x.drop s) k first r (fuel + 1) p q
                = secondOuter (x.drop s) k first r fuel
                  (p + shiftNoPeriod (q + j) k) 0 := by
              rw [secondOuter, if_pos hg]
              simp only [hsi, if_neg hb2]
            refine ⟨?_, ?_⟩
            · rw [hprog, secondOuterWork, if_pos hg]
              simp only [hsi, if_neg hb2, hW, List.length_append, soTest_length, hshift]
              have h3 : (soInner blank endSym orc ((x.drop s).length + 1) ts).length ≤ 3 * W :=
                hcost2
              obtain ⟨Wr, hWr⟩ : ∃ Wr, secondOuterWork (x.drop s) k first r fuel
                  (p + shiftNoPeriod (q + j) k) 0 = Wr := ⟨_, rfl⟩
              rw [hWr] at hrc
              rw [hWr]
              obtain ⟨e, he⟩ : ∃ e, shiftNoPeriod (q + j) k = e := ⟨_, rfl⟩
              rw [he] at hlen3 hfitE
              have hce : ceilDiv (q + j) k ≤ q + j := ceilDiv_le_self' (by omega)
              have heq1 : e ≤ (q + j) + 1 := by
                rw [← he]; exact shiftNoPeriod_le_succ (by omega) (q + j)
              obtain ⟨A, hA⟩ : ∃ A, k + 12 = A := ⟨_, rfl⟩
              obtain ⟨C, hC⟩ : ∃ C, k + 9 = C := ⟨_, rfl⟩
              rw [hA, hC] at hrc ⊢
              have hexp : A * (1 + W + Wr) = A + A * W + A * Wr := by ring
              have hmul : 3 * W + C * W ≤ A * W := by
                calc 3 * W + C * W = (3 + C) * W := by ring
                  _ ≤ A * W := Nat.mul_le_mul_right W (by omega)
              have hke : (4 + (k - 1)) * e ≤ (k + 3) * e := Nat.mul_le_mul_right e (by omega)
              have hke2 : (k + 3) * e ≤ (k + 3) * ((q + j) + 1) := Nat.mul_le_mul_left _ heq1
              have hke3 : (k + 3) * ((q + j) + 1) = (k + 3) * (q + j) + (k + 3) := by ring
              have hCqj : C * (q + j) = C * q + C * j := by ring
              have hCj : C * j ≤ C * W := Nat.mul_le_mul_left C (by omega)
              have hsplit : 5 * (q + j) + (q + j) + (k + 3) * (q + j) = C * (q + j) := by
                rw [← hC]; ring
              omega
            · obtain ⟨a', b', D', q', E', P', hEnc', hp2⟩ := hre
              exact ⟨a', b', D', q', E', P', by rw [happ]; exact hEnc',
                by intro p₂ hh; exact hp2 p₂ (by rw [← hso]; exact hh)⟩
      · -- 番人：`p ≥ |v|` で `none`
        have hng : ¬ (p < (x.drop s).length) := fun hcc => hc (hguard.2 hcc)
        have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
            = soTest blank ts := by rw [soProg, if_neg hc]
        refine ⟨?_, ⟨s + q, s + p + q, D, q, 0, p, ?_, ?_⟩⟩
        · rw [hprog, secondOuterWork, if_neg hng, soTest_length]
          omega
        · rw [hprog]; exact soTest_enc hE
        · intro p₂ hp2
          rw [secondOuter, if_neg hng] at hp2
          simp at hp2


/-- `secondPeriod`（`= secondOuter v k first r (|v|+1) 1 0`）のテープ実現。 -/
def spProg (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k n : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  soProg blank endSym mark orc orc2 k (n + 1) (n + 1) ts

/-- **系（`secondPeriod` のテープ実現とコスト）**：`A = k+12`, `B = 2`。 -/
theorem spProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s first S R D : ℕ} {ts : Tapes sc} (hs : s ≤ x.length) (hfirst : 0 < first)
    (horc : ∀ ts', orc ts' = decide (r < pOf ts' + qOf ts' + 1 ∧ (k - 1) * pOf ts' ≤ qOf ts' + 1))
    (horc2 : ∀ ts', orc2 ts' = decide (k * first ≤ qOf ts' ∧ qOf ts' ≤ r))
    (hfit : s + 1 ≤ x.length)
    (hE : Enc blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, first, S, R⟩ ts) :
    ((spProg blank endSym mark orc orc2 k (x.drop s).length ts).length
        ≤ (k + 12) * secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0 + 2
      ∧ (∃ a b D' q' E' P',
          Enc blank startSym endSym mark x a b ⟨D', q', E', P', first, S, R⟩
            (applyActs blank (spProg blank endSym mark orc orc2 k (x.drop s).length ts) ts)
          ∧ (∀ p₂, secondPeriod (x.drop s) k first r = some p₂ → P' = p₂))) := by
  have hE' : Enc blank startSym endSym mark x (s + 0) (s + 1 + 0) ⟨D, 0, 0, 1, first, S, R⟩ ts :=
    hE
  obtain ⟨hc, he⟩ := soProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (orc2 := orc2) hk hend hmark hs hfirst
    horc horc2 ((x.drop s).length + 1) 1 0 D ts (by omega) hE'
  refine ⟨?_, ?_⟩
  · rw [spProg]
    simpa using hc
  · obtain ⟨a', b', D', q', E', P', hEnc, hp2⟩ := he
    exact ⟨a', b', D', q', E', P', hEnc, hp2⟩

/-! ### 第 2 相の入口への再配置に使うカウンタ転送

`extendReach` 直後は `V1 = s + (r - p₁)`, `V2 = s + r`, `Cp = p₁`, `Cr = r`。
第 2 相の入口は `V1 = s`, `V2 = s + 1`, `Cp = 1`, `Cf = p₁`, `Cr = r`。 -/

/-- `Cp` を 1 減らして `Cf` と `Ce` を 1 ずつ増やす（4 動作）。 -/
def pfUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.Cf blank .right, Act.Ce blank .right]

def pfLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => pfUnit blank ++ pfLoop blank n

@[simp] theorem pfLoop_length (blank : Fin sc) (n : ℕ) : (pfLoop blank n).length = 4 * n := by
  induction n with
  | zero => simp [pfLoop]
  | succ n ih => simp only [pfLoop, List.length_append, pfUnit, ih]; simp; omega

theorem applyActs_pfUnit (ts : Tapes sc) :
    applyActs blank (pfUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        Cf := Tape.step blank ts.Cf blank .right
        Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem pfLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F + n, S, R⟩
        (applyActs blank (pfLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [pfLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + 1, P + n, F + 1, S, R⟩
          (applyActs blank (pfUnit blank) ts) := by
        rw [applyActs_pfUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, Tape.counter'_inc hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp,
          Tape.counter'_inc hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q (E + 1) P (F + 1) S R _ hstep
      have e2 : E + 1 + n = E + (n + 1) := by omega
      have e3 : F + 1 + n = F + (n + 1) := by omega
      rw [e2, e3] at this
      simp only [pfLoop, applyActs_append]
      exact this

/-- `Cp` と `Cr` を 1 ずつ減らして `Ce` を 1 増やす（5 動作）。 -/
def prUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.Cr blank .left, Act.Cr blank .stay,
    Act.Ce blank .right]

def prLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => prUnit blank ++ prLoop blank n

@[simp] theorem prLoop_length (blank : Fin sc) (n : ℕ) : (prLoop blank n).length = 5 * n := by
  induction n with
  | zero => simp [prLoop]
  | succ n ih => simp only [prLoop, List.length_append, prUnit, ih]; simp; omega

theorem applyActs_prUnit (ts : Tapes sc) :
    applyActs blank (prUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        Cr := Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay
        Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem prLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R + n⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
        (applyActs blank (prLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [prLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (P + n) + 1, F, S, (R + n) + 1⟩ ts := by
        have e1 : P + (n + 1) = (P + n) + 1 := by omega
        have e2 : R + (n + 1) = (R + n) + 1 := by omega
        rw [e1, e2] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + 1, P + n, F, S, R + n⟩
          (applyActs blank (prUnit blank) ts) := by
        rw [applyActs_prUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, Tape.counter'_inc hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp, hE'.cf, hE'.cs,
          by simpa using Tape.counter'_dec (n := R + n) hE'.cr⟩
      have := ih a b D Q (E + 1) P F S R _ hstep
      have e3 : E + 1 + n = E + (n + 1) := by omega
      rw [e3] at this
      simp only [prLoop, applyActs_append]
      exact this

/-- `Cr` を 1 減らし、`V1`/`V2` を 1 左へ、`Ce` を 1 増やす（5 動作）。 -/
def rvUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cr blank .left, Act.Cr blank .stay, Act.V1 .left, Act.V2 .left, Act.Ce blank .right]

def rvLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => rvUnit blank ++ rvLoop blank n

@[simp] theorem rvLoop_length (blank : Fin sc) (n : ℕ) : (rvLoop blank n).length = 5 * n := by
  induction n with
  | zero => simp [rvLoop]
  | succ n ih => simp only [rvLoop, List.length_append, rvUnit, ih]; simp; omega

theorem applyActs_rvUnit (ts : Tapes sc) :
    applyActs blank (rvUnit blank) ts =
      { ts with
        Cr := Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay
        V1 := Tape.step blank ts.V1 ts.V1.focus .left
        V2 := Tape.step blank ts.V2 ts.V2.focus .left
        Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem rvLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q, E, P, F, S, R + n⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
        (applyActs blank (rvLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [rvLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, Q, E, P, F, S, (R + n) + 1⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : R + (n + 1) = (R + n) + 1 := by omega
        rw [e1, e2, e3] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x (a + n) (b + n)
          ⟨D, Q, E + 1, P, F, S, R + n⟩ (applyActs blank (rvUnit blank) ts) := by
        rw [applyActs_rvUnit]
        exact ⟨pat_left hE'.v1, pat_left hE'.v2, hE'.cd, hE'.cq, Tape.counter'_inc hE'.ce,
          hE'.cp, hE'.cf, hE'.cs,
          by simpa using Tape.counter'_dec (n := R + n) hE'.cr⟩
      have := ih a b D Q (E + 1) P F S R _ hstep
      have e4 : E + 1 + n = E + (n + 1) := by omega
      rw [e4] at this
      simp only [rvLoop, applyActs_append]
      exact this

/-- `Ce` を 1 減らして `Cr` を 1 増やす（3 動作）。 -/
def crUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce blank .stay, Act.Cr blank .right]

def crLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => crUnit blank ++ crLoop blank n

@[simp] theorem crLoop_length (blank : Fin sc) (n : ℕ) : (crLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [crLoop]
  | succ n ih => simp only [crLoop, List.length_append, crUnit, ih]; simp; omega

theorem applyActs_crUnit (ts : Tapes sc) :
    applyActs blank (crUnit blank) ts =
      { ts with
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
        Cr := Tape.step blank ts.Cr blank .right } := rfl

theorem crLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩
        (applyActs blank (crLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [crLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R + 1⟩
          (applyActs blank (crUnit blank) ts) := by
        rw [applyActs_crUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq,
          by simpa using Tape.counter'_dec (n := E + n) hE'.ce, hE'.cp, hE'.cf, hE'.cs,
          Tape.counter'_inc hE'.cr⟩
      have := ih a b D Q E P F S (R + 1) _ hstep
      have e2 : R + 1 + n = R + (n + 1) := by omega
      rw [e2] at this
      simp only [crLoop, applyActs_append]
      exact this

/-- `Cp` を 1 減らして `V2` を 1 左へ（3 動作）。 -/
def pvUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.V2 .left]

def pvLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => pvUnit blank ++ pvLoop blank n

@[simp] theorem pvLoop_length (blank : Fin sc) (n : ℕ) : (pvLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [pvLoop]
  | succ n ih => simp only [pvLoop, List.length_append, pvUnit, ih]; simp; omega

theorem applyActs_pvUnit (ts : Tapes sc) :
    applyActs blank (pvUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        V2 := Tape.step blank ts.V2 ts.V2.focus .left } := rfl

theorem pvLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (pvLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [pvLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a (b + n + 1)
          ⟨D, Q, E, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : b + (n + 1) = b + n + 1 := by omega
        have e2 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1, e2] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E, P + n, F, S, R⟩
          (applyActs blank (pvUnit blank) ts) := by
        rw [applyActs_pvUnit]
        exact ⟨hE'.v1, pat_left hE'.v2, hE'.cd, hE'.cq, hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [pvLoop, applyActs_append]
      exact this


/-- `extendReach` 直後（`V1 = s + (r - p₁)`, `V2 = s + r`, `Cp = p₁`, `Cr = r`, `Cf = 0`）から、
第 2 相の入口（`V1 = s`, `V2 = s + 1`, `Cp = 1`, `Cf = p₁`, `Cr = r`）へ再配置する。
動作数 `8r + 17p₁` 以下。 -/
def repoProg (blank : Fin sc) (P R : ℕ) : List (Act sc) :=
  pfLoop blank P ++ (cpLoop blank P ++
    (prLoop blank P ++ (cpLoop blank P ++
      (rvLoop blank (R - P) ++ (crLoop blank (R - P) ++
        (pcLoop blank P ++ (cpLoop blank P ++ pvLoop blank (P - 1))))))))

theorem repoProg_length (blank : Fin sc) {P R : ℕ} (hPR : P ≤ R) :
    (repoProg blank P R).length ≤ 8 * R + 17 * P := by
  simp only [repoProg, List.length_append, pfLoop_length, cpLoop_length, prLoop_length,
    rvLoop_length, crLoop_length, pcLoop_length, pvLoop_length]
  omega

theorem repoProg_enc {s P R D S : ℕ} {ts : Tapes sc} (hP : 0 < P) (hPR : P ≤ R)
    (hE : Enc blank startSym endSym mark x (s + (R - P)) (s + R) ⟨D, 0, 0, P, 0, S, R⟩ ts) :
    Enc blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, P, S, R⟩
      (applyActs blank (repoProg blank P R) ts) := by
  have e0 : (0 : ℕ) + P = P := by omega
  have e0' : (0 : ℕ) + (R - P) = R - P := by omega
  -- (a) `Cp → Cf, Ce`
  have ha := pfLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 0 S R ts (by rw [e0]; exact hE)
  rw [e0] at ha
  -- (b) `Ce → Cp`
  have hb := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S R _ (by rw [e0]; exact ha)
  rw [e0] at hb
  -- (c) `Cp` と `Cr` を `P` 減らす
  have hc := prLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S (R - P) _
    (by rw [e0, show R - P + P = R from by omega]; exact hb)
  rw [e0] at hc
  -- (d) `Ce → Cp`
  have hd := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - P)) (s + R) D 0 0 0 P S (R - P) _
    (by rw [e0]; exact hc)
  rw [e0] at hd
  -- (e) `Cr` を落としつつ `V1`/`V2` を `R - P` セル左へ
  have he := rvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P P S 0 _
    (by rw [e0', show s + P + (R - P) = s + R from by omega]; exact hd)
  rw [e0'] at he
  -- (f) `Ce → Cr`
  have hf := crLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P P S 0 _ (by rw [e0']; exact he)
  rw [e0'] at hf
  -- (g) `Cp → Cr, Ce`（`Cr` を `R` に戻す）
  have hg := pcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s (s + P) D 0 0 0 P S (R - P) _ (by rw [e0]; exact hf)
  rw [e0, show R - P + P = R from by omega] at hg
  have hg2 := cpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s (s + P) D 0 0 0 P S R _ (by rw [e0]; exact hg)
  rw [e0] at hg2
  -- (h) `V2` を `s + 1` へ
  have hh := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (P - 1) s (s + 1) D 0 0 1 P S R _
    (by rw [show s + 1 + (P - 1) = s + P from by omega,
      show 1 + (P - 1) = P from by omega]; exact hg2)
  rw [repoProg]
  rw [applyActs_append, applyActs_append, applyActs_append, applyActs_append,
    applyActs_append, applyActs_append, applyActs_append, applyActs_append]
  exact hh

end Second

/-! ## 12. 外側 1 反復（`firstPeriod` → `extendReach` → 再配置 → `secondPeriod`）の合成 -/

section Compose

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}
  {orcB orc orc2 : Tapes sc → Bool}

/-- `Cr` の読み出し。 -/
def rOf (ts : Tapes sc) : ℕ := ts.Cr.left.length - 1

theorem rOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : rOf ts = c.r := ctr_len hE.cr

/-- `firstOuter` は成功時に正の周期を返す。 -/
theorem firstOuter_pos (v : List (Fin sc)) (k bound : ℕ) :
    ∀ (fuel p p' m : ℕ), 0 < p → firstOuter v k bound fuel p = some (p', m) → 0 < p' := by
  intro fuel
  induction fuel with
  | zero => intro p p' m _ hc; simp [firstOuter] at hc
  | succ fuel ih =>
      intro p p' m hp hc
      rw [firstOuter] at hc
      split_ifs at hc with h1 h2
      · simp only [Option.some.injEq, Prod.mk.injEq] at hc
        omega
      · refine ih _ p' m ?_ hc
        have := shiftNoPeriod_pos (firstInner v k p (v.length + 1) 0) k
        omega

def afterFr (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : Tapes sc :=
  applyActs blank (frProg blank endSym mark orcB k n Fo Fr ts) ts

def afterRepo (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : Tapes sc :=
  applyActs blank
    (repoProg blank (pOf (afterFr blank endSym mark orcB k n Fo Fr ts))
      (rOf (afterFr blank endSym mark orcB k n Fo Fr ts)))
    (afterFr blank endSym mark orcB k n Fo Fr ts)

/-- `decompose` の外側 1 反復の前半（削除ループを除く）全体の動作列。 -/
def stepProg (blank endSym mark : Fin sc) (orcB orc orc2 : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  frProg blank endSym mark orcB k n Fo Fr ts ++
    (repoProg blank (pOf (afterFr blank endSym mark orcB k n Fo Fr ts))
        (rOf (afterFr blank endSym mark orcB k n Fo Fr ts)) ++
      spProg blank endSym mark orc orc2 k n (afterRepo blank endSym mark orcB k n Fo Fr ts))

/-- **主定理（外側 1 反復のテープ実現とコスト）**：`A = 2k + 65`, `B = k + 3`。
終状態は `Cf = p₁`、`Cr = r`、`Cs` は不変で、第 2 周期が見つかれば `Cp = p₂`。 -/
theorem stepProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s S : ℕ} {ts : Tapes sc} {orcB : Tapes sc → Bool} (hs : s < x.length)
    (horcB : ∀ ts', orcB ts' = decide (pOf ts' < (x.drop s).length))
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, S, 0⟩ ts)
    {p₁ m : ℕ} (hfp : firstPeriod (x.drop s) k = some (p₁, m))
    (horc : ∀ ts', orc ts' =
      decide (extendReach (x.drop s) p₁ (x.length + 1) m < pOf ts' + qOf ts' + 1 ∧
        (k - 1) * pOf ts' ≤ qOf ts' + 1))
    (horc2 : ∀ ts', orc2 ts' =
      decide (k * p₁ ≤ qOf ts' ∧ qOf ts' ≤ extendReach (x.drop s) p₁ (x.length + 1) m)) :
    ((stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts).length
        ≤ (2 * k + 65) * decomposeStepWork x k s + (k + 3)
      ∧ (∃ a b D' q' E' P',
          Enc blank startSym endSym mark x a b
            ⟨D', q', E', P', p₁, S, extendReach (x.drop s) p₁ (x.length + 1) m⟩
            (applyActs blank
              (stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) ts)
          ∧ (∀ p₂, secondPeriod (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m) = some p₂ → P' = p₂))) := by
  have hsle : s ≤ x.length := le_of_lt hs
  have hp₁ : 0 < p₁ := firstOuter_pos (x.drop s) k (x.drop s).length _ 1 p₁ m (by omega) hfp
  obtain ⟨hfr, hfrlen, hwk, hmr, hrle⟩ := frProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hend hmark hs (le_refl _) horcB hE hfp
  obtain ⟨r, hrdef⟩ : ∃ r, extendReach (x.drop s) p₁ (x.length + 1) m = r := ⟨_, rfl⟩
  rw [hrdef] at hfr hmr hrle horc horc2
  have hm : m = p₁ + (k - 1) * p₁ :=
    firstOuter_snd (x.drop s) k (x.drop s).length _ 1 p₁ m hfp
  have hpr : p₁ ≤ r := by omega
  -- 再配置
  have hpOf : pOf (afterFr blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) = p₁ :=
    pOf_eq hfr
  have hrOf : rOf (afterFr blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) = r :=
    rOf_eq hfr
  have hrepo : Enc blank startSym endSym mark x s (s + 1) ⟨0, 0, 0, 1, p₁, S, r⟩
      (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) := by
    rw [afterRepo, hpOf, hrOf]
    exact repoProg_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) hp₁ hpr hfr
  -- 第 2 相
  obtain ⟨hsplen, hspe⟩ := spProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (orc2 := orc2)
    hk hend hmark hsle hp₁ horc horc2 (by omega) hrepo
  have happ : applyActs blank
      (stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) ts
      = applyActs blank
        (spProg blank endSym mark orc orc2 k (x.drop s).length
          (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts))
        (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) := by
    rw [stepProg, applyActs_append, applyActs_append]
    rfl
  refine ⟨?_, ?_⟩
  · -- コスト
    rw [stepProg, List.length_append, List.length_append, hpOf, hrOf]
    have hrepolen : (repoProg blank p₁ r).length ≤ 8 * r + 17 * p₁ :=
      repoProg_length blank hpr
    have hdsw : decomposeStepWork x k s
        = firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1
          + (extendReachWork (x.drop s) p₁ (x.length + 1) m
            + secondOuterWork (x.drop s) k p₁ r ((x.drop s).length + 1) 1 0) := by
      simp only [decomposeStepWork, hfp, hrdef]
    rw [hdsw]
    obtain ⟨FO, hFO⟩ : ∃ FO, firstOuterWork (x.drop s) k (x.drop s).length
        ((x.drop s).length + 1) 1 = FO := ⟨_, rfl⟩
    obtain ⟨ER, hER⟩ : ∃ ER, extendReachWork (x.drop s) p₁ (x.length + 1) m = ER := ⟨_, rfl⟩
    obtain ⟨SO, hSO⟩ : ∃ SO, secondOuterWork (x.drop s) k p₁ r ((x.drop s).length + 1) 1 0
        = SO := ⟨_, rfl⟩
    rw [hFO] at hfrlen hwk
    rw [hER] at hfrlen hrle
    rw [hSO] at hsplen
    rw [hFO, hER, hSO]
    have hp₁FO : p₁ ≤ FO := by
      have : p₁ ≤ (k - 1) * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
      omega
    have hkp : (k - 1) * p₁ ≤ FO := hwk
    obtain ⟨A, hA⟩ : ∃ A, 2 * k + 65 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, 2 * k + 32 = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, k + 12 = C := ⟨_, rfl⟩
    rw [hB] at hfrlen
    rw [hC] at hsplen
    rw [hA]
    have hexp : A * (FO + (ER + SO)) = A * FO + A * ER + A * SO := by ring
    have h1 : B * FO + 33 * FO ≤ A * FO := by
      calc B * FO + 33 * FO = (B + 33) * FO := by ring
        _ ≤ A * FO := Nat.mul_le_mul_right FO (by omega)
    have h2 : C * SO ≤ A * SO := Nat.mul_le_mul_right SO (by omega)
    have h3 : 11 * ER ≤ A * ER := Nat.mul_le_mul_right ER (by omega)
    have h4 : 8 * r ≤ 8 * m + 8 * ER := by omega
    have h5 : 8 * m + 17 * p₁ ≤ 33 * FO := by
      have : m ≤ 2 * FO := by omega
      omega
    omega
  · rw [hrdef]
    obtain ⟨a', b', D', q', E', P', hEnc, hp2⟩ := hspe
    exact ⟨a', b', D', q', E', P', by rw [happ]; exact hEnc, hp2⟩

end Compose

/-! ## 13. 新しい削除規則（`stripLoop2`）：切断を `s + (r - k*p + 1)` へ進める -/

section Advance

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}

/-- `Cr` を 1 減らして `V2` を 1 左へ、`Ce` を 1 増やす（4 動作）。 -/
def rv2Unit (blank : Fin sc) : List (Act sc) :=
  [Act.Cr blank .left, Act.Cr blank .stay, Act.V2 .left, Act.Ce blank .right]

def rv2Loop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => rv2Unit blank ++ rv2Loop blank n

@[simp] theorem rv2Loop_length (blank : Fin sc) (n : ℕ) : (rv2Loop blank n).length = 4 * n := by
  induction n with
  | zero => simp [rv2Loop]
  | succ n ih => simp only [rv2Loop, List.length_append, rv2Unit, ih]; simp; omega

theorem applyActs_rv2Unit (ts : Tapes sc) :
    applyActs blank (rv2Unit blank) ts =
      { ts with
        Cr := Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay
        V2 := Tape.step blank ts.V2 ts.V2.focus .left
        Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem rv2Loop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E, P, F, S, R + n⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
        (applyActs blank (rv2Loop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [rv2Loop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a (b + n + 1)
          ⟨D, Q, E, P, F, S, (R + n) + 1⟩ ts := by
        have e1 : b + (n + 1) = b + n + 1 := by omega
        have e2 : R + (n + 1) = (R + n) + 1 := by omega
        rw [e1, e2] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E + 1, P, F, S, R + n⟩
          (applyActs blank (rv2Unit blank) ts) := by
        rw [applyActs_rv2Unit]
        exact ⟨hE'.v1, pat_left hE'.v2, hE'.cd, hE'.cq, Tape.counter'_inc hE'.ce, hE'.cp,
          hE'.cf, hE'.cs, by simpa using Tape.counter'_dec (n := R + n) hE'.cr⟩
      have := ih a b D Q (E + 1) P F S R _ hstep
      have e3 : E + 1 + n = E + (n + 1) := by omega
      rw [e3] at this
      simp only [rv2Loop, applyActs_append]
      exact this

/-- `Cp` と `Ce` を 1 ずつ減らして `Cq` を 1 増やす（5 動作）。 -/
def ecUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.Ce blank .left, Act.Ce blank .stay,
    Act.Cq blank .right]

def ecLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => ecUnit blank ++ ecLoop blank n

@[simp] theorem ecLoop_length (blank : Fin sc) (n : ℕ) : (ecLoop blank n).length = 5 * n := by
  induction n with
  | zero => simp [ecLoop]
  | succ n ih => simp only [ecLoop, List.length_append, ecUnit, ih]; simp; omega

theorem applyActs_ecUnit (ts : Tapes sc) :
    applyActs blank (ecUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
        Cq := Tape.step blank ts.Cq blank .right } := rfl

theorem ecLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q + n, E, P, F, S, R⟩
        (applyActs blank (ecLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [ecLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b
          ⟨D, Q, (E + n) + 1, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        have e2 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1, e2] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q + 1, E + n, P + n, F, S, R⟩
          (applyActs blank (ecUnit blank) ts) := by
        rw [applyActs_ecUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, Tape.counter'_inc hE'.cq,
          by simpa using Tape.counter'_dec (n := E + n) hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D (Q + 1) E P F S R _ hstep
      have e3 : Q + 1 + n = Q + (n + 1) := by omega
      rw [e3] at this
      simp only [ecLoop, applyActs_append]
      exact this

/-- `Cq` を 1 減らして `Cp` を 1 増やす（3 動作）。 -/
def qpUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank .left, Act.Cq blank .stay, Act.Cp blank .right]

def qpLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => qpUnit blank ++ qpLoop blank n

@[simp] theorem qpLoop_length (blank : Fin sc) (n : ℕ) : (qpLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [qpLoop]
  | succ n ih => simp only [qpLoop, List.length_append, qpUnit, ih]; simp; omega

theorem applyActs_qpUnit (ts : Tapes sc) :
    applyActs blank (qpUnit blank) ts =
      { ts with
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay
        Cp := Tape.step blank ts.Cp blank .right } := rfl

theorem qpLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩
        (applyActs blank (qpLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [qpLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q + n, E, P + 1, F, S, R⟩
          (applyActs blank (qpUnit blank) ts) := by
        rw [applyActs_qpUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd,
          by simpa using Tape.counter'_dec (n := Q + n) hE'.cq, hE'.ce,
          Tape.counter'_inc hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E (P + 1) F S R _ hstep
      have e2 : P + 1 + n = P + (n + 1) := by omega
      rw [e2] at this
      simp only [qpLoop, applyActs_append]
      exact this

/-- `Ce` から `Cp`（`= p`）を `n` 回引く（`Cp` は復元）。動作数 `8*p*n`。 -/
def subKLoop (blank : Fin sc) (p : ℕ) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => (ecLoop blank p ++ qpLoop blank p) ++ subKLoop blank p n

@[simp] theorem subKLoop_length (blank : Fin sc) (p n : ℕ) :
    (subKLoop blank p n).length = 8 * p * n := by
  induction n with
  | zero => simp [subKLoop]
  | succ n ih =>
      simp only [subKLoop, List.length_append, ecLoop_length, qpLoop_length, ih]
      ring

theorem subKLoop_enc (p : ℕ) : ∀ (n a b D E F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, 0, E + n * p, p, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, 0, E, p, F, S, R⟩
        (applyActs blank (subKLoop blank p n) ts) := by
  intro n
  induction n with
  | zero => intro a b D E F S R ts hE; simpa [subKLoop] using hE
  | succ n ih =>
      intro a b D E F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b
          ⟨D, 0, (E + n * p) + p, 0 + p, F, S, R⟩ ts := by
        have e1 : E + (n + 1) * p = (E + n * p) + p := by ring
        have e2 : (0 : ℕ) + p = p := by omega
        rw [← e1, e2]; exact hE
      have h1 := ecLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R ts hE'
      have h2 := qpLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
        (mark := mark) (x := x) p a b D 0 (E + n * p) 0 F S R _ h1
      have e4 : (0 : ℕ) + p = p := by omega
      rw [e4] at h2
      have := ih a b D E F S R _ h2
      simp only [subKLoop, applyActs_append]
      exact this

/-- `Ce` を 1 減らして `Cs` を 1 増やし、`V1`/`V2` を 1 右へ（5 動作）。 -/
def csUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce blank .stay, Act.Cs blank .right, Act.V1 .right, Act.V2 .right]

def csLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => csUnit blank ++ csLoop blank n

@[simp] theorem csLoop_length (blank : Fin sc) (n : ℕ) : (csLoop blank n).length = 5 * n := by
  induction n with
  | zero => simp [csLoop]
  | succ n ih => simp only [csLoop, List.length_append, csUnit, ih]; simp; omega

theorem applyActs_csUnit (ts : Tapes sc) :
    applyActs blank (csUnit blank) ts =
      { ts with
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
        Cs := Tape.step blank ts.Cs blank .right
        V1 := Tape.step blank ts.V1 ts.V1.focus .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .right } := rfl

theorem csLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts →
      a + n ≤ x.length → b + n ≤ x.length →
      Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q, E, P, F, S + n, R⟩
        (applyActs blank (csLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE _ _; simpa [csLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE ha hb
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x (a + 1) (b + 1)
          ⟨D, Q, E + n, P, F, S + 1, R⟩ (applyActs blank (csUnit blank) ts) := by
        rw [applyActs_csUnit]
        exact ⟨pat_right hE'.v1 (by omega), pat_right hE'.v2 (by omega), hE'.cd, hE'.cq,
          by simpa using Tape.counter'_dec (n := E + n) hE'.ce, hE'.cp, hE'.cf,
          Tape.counter'_inc hE'.cs, hE'.cr⟩
      have := ih (a + 1) (b + 1) D Q E P F (S + 1) R _ hstep (by omega) (by omega)
      have e2 : a + 1 + n = a + (n + 1) := by omega
      have e3 : b + 1 + n = b + (n + 1) := by omega
      have e4 : S + 1 + n = S + (n + 1) := by omega
      rw [e2, e3, e4] at this
      simp only [csLoop, applyActs_append]
      exact this

/-- `Cp` を `n` 回減らす（2 動作／回）。 -/
def pzUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay]

def pzLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => pzUnit blank ++ pzLoop blank n

@[simp] theorem pzLoop_length (blank : Fin sc) (n : ℕ) : (pzLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [pzLoop]
  | succ n ih => simp only [pzLoop, List.length_append, pzUnit, ih]; simp; omega

theorem applyActs_pzUnit (ts : Tapes sc) :
    applyActs blank (pzUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay } := rfl

theorem pzLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (pzLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [pzLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩
          (applyActs blank (pzUnit blank) ts) := by
        rw [applyActs_pzUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [pzLoop, applyActs_append]
      exact this

/-- **切断の前進**：`extendReach` 直後の状態から、切断を `r - k*p + 1` だけ進めた
「まっさらな」状態（`V1 = V2 = s'`、カウンタは `Cs = S + (r - k*p + 1)` と `Cf` 以外すべて `0`）
へ移る。動作数 `11*r + 3*k*p + 3` 以下。 -/
def advanceProg (blank : Fin sc) (k P R : ℕ) : List (Act sc) :=
  rvLoop blank (R - P) ++ (rv2Loop blank P ++ (subKLoop blank P k ++
    (csLoop blank (R - k * P) ++
      ((Act.Cs blank .right :: Act.V1 .right :: [Act.V2 (sc := sc) .right]) ++
        pzLoop blank P))))

theorem advanceProg_length (blank : Fin sc) {k P R : ℕ} (hPR : P ≤ R) (hkP : k * P ≤ R) :
    (advanceProg blank k P R).length ≤ 11 * R + 3 * (k * P) + 3 := by
  simp only [advanceProg, List.length_append, rvLoop_length, rv2Loop_length, subKLoop_length,
    csLoop_length, pzLoop_length, List.length_cons, List.length_nil]
  have h : 8 * P * k = 8 * (k * P) := by ring
  omega

theorem advanceProg_enc {s P R D F S : ℕ} {ts : Tapes sc} (hkP : k * P ≤ R) (hP : P ≤ R)
    (hfit : s + (R - k * P + 1) ≤ x.length)
    (hE : Enc blank startSym endSym mark x (s + (R - P)) (s + R) ⟨D, 0, 0, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x (s + (R - k * P + 1)) (s + (R - k * P + 1))
      ⟨D, 0, 0, 0, F, S + (R - k * P + 1), 0⟩
      (applyActs blank (advanceProg blank k P R) ts) := by
  -- (1) `V1`/`V2` を `R - P` 左へ
  have h1 := rvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - P) s (s + P) D 0 0 P F S P _
    (by rw [show s + P + (R - P) = s + R from by omega,
      show P + (R - P) = R from by omega]; exact hE)
  rw [show (0 : ℕ) + (R - P) = R - P from by omega] at h1
  -- (2) `V2` を `P` 左へ（`Cr` を使い切る）
  have h2 := rv2Loop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s D 0 (R - P) P F S 0 _
    (by rw [show (0 : ℕ) + P = P from by omega]; exact h1)
  rw [show R - P + P = R from by omega] at h2
  -- (3) `Ce := r - k*p`
  have h3 := subKLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P k s s D (R - k * P) F S 0 _
    (by rw [show R - k * P + k * P = R from by omega]; exact h2)
  -- (4) `Ce` を `Cs` へ流しつつ両ヘッドを右へ
  have h4 := csLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (R - k * P) s s D 0 0 P F S 0 _
    (by rw [show (0 : ℕ) + (R - k * P) = R - k * P from by omega]; exact h3)
    (by omega) (by omega)
  -- (5) もう 1 歩
  have h5 : Enc blank startSym endSym mark x (s + (R - k * P) + 1) (s + (R - k * P) + 1)
      ⟨D, 0, 0, P, F, S + (R - k * P) + 1, 0⟩
      (applyActs blank (Act.Cs blank .right :: Act.V1 .right :: [Act.V2 (sc := sc) .right])
        (applyActs blank (csLoop blank (R - k * P))
          (applyActs blank (subKLoop blank P k)
            (applyActs blank (rv2Loop blank P)
              (applyActs blank (rvLoop blank (R - P)) ts))))) := by
    have hres : applyActs blank
        (Act.Cs blank .right :: Act.V1 .right :: [Act.V2 (sc := sc) .right])
        (applyActs blank (csLoop blank (R - k * P))
          (applyActs blank (subKLoop blank P k)
            (applyActs blank (rv2Loop blank P)
              (applyActs blank (rvLoop blank (R - P)) ts)))) =
        { (applyActs blank (csLoop blank (R - k * P))
            (applyActs blank (subKLoop blank P k)
              (applyActs blank (rv2Loop blank P)
                (applyActs blank (rvLoop blank (R - P)) ts)))) with
          Cs := Tape.step blank (applyActs blank (csLoop blank (R - k * P))
            (applyActs blank (subKLoop blank P k)
              (applyActs blank (rv2Loop blank P)
                (applyActs blank (rvLoop blank (R - P)) ts)))).Cs blank .right
          V1 := Tape.step blank (applyActs blank (csLoop blank (R - k * P))
            (applyActs blank (subKLoop blank P k)
              (applyActs blank (rv2Loop blank P)
                (applyActs blank (rvLoop blank (R - P)) ts)))).V1
            (applyActs blank (csLoop blank (R - k * P))
              (applyActs blank (subKLoop blank P k)
                (applyActs blank (rv2Loop blank P)
                  (applyActs blank (rvLoop blank (R - P)) ts)))).V1.focus .right
          V2 := Tape.step blank (applyActs blank (csLoop blank (R - k * P))
            (applyActs blank (subKLoop blank P k)
              (applyActs blank (rv2Loop blank P)
                (applyActs blank (rvLoop blank (R - P)) ts)))).V2
            (applyActs blank (csLoop blank (R - k * P))
              (applyActs blank (subKLoop blank P k)
                (applyActs blank (rv2Loop blank P)
                  (applyActs blank (rvLoop blank (R - P)) ts)))).V2.focus .right } := rfl
    rw [hres]
    exact ⟨pat_right h4.v1 (by omega), pat_right h4.v2 (by omega), h4.cd, h4.cq, h4.ce,
      h4.cp, h4.cf, Tape.counter'_inc h4.cs, h4.cr⟩
  -- (6) `Cp` を `0` へ
  have h6 := pzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P (s + (R - k * P) + 1) (s + (R - k * P) + 1) D 0 0 0 F
    (S + (R - k * P) + 1) 0 _ (by rw [show (0 : ℕ) + P = P from by omega]; exact h5)
  rw [advanceProg, applyActs_append, applyActs_append, applyActs_append, applyActs_append,
    applyActs_append]
  have e1 : s + (R - k * P) + 1 = s + (R - k * P + 1) := by omega
  have e2 : S + (R - k * P) + 1 = S + (R - k * P + 1) := by omega
  rw [e1, e2] at h6
  exact h6

end Advance

/-! ### 削除ループ `stripLoop2` のテープ実現 -/

section Strip2

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}
  {orcB : Tapes sc → Bool}

/-- `frProg` の後半（`Cr := k*p` の設定と `extendReach`）。 -/
def frTail (blank endSym : Fin sc) (Fr : ℕ) (t : Tapes sc) : List (Act sc) :=
  loadR blank (qOf t) (pOf t) ++
    rProg blank endSym Fr (applyActs blank (loadR blank (qOf t) (pOf t)) t)

theorem frProg_split (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) :
    frProg blank endSym mark orcB k n Fo Fr ts
      = fpProg blank endSym mark orcB k n Fo ts ++
        frTail blank endSym Fr (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts) :=
  rfl

/-- 削除ループ 1 反復の動作列（`firstOuter` が成功したときだけ `extendReach` と
切断の前進を行う）。成功判定は `Cd` の probe（成功なら `Cd = 0`）。 -/
def stripStep (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  fpProg blank endSym mark orcB k n Fo ts ++
    (if probe blank (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts).Cd = mark then
       frTail blank endSym Fr (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts) ++
         advanceProg blank k
           (pOf (applyActs blank (frProg blank endSym mark orcB k n Fo Fr ts) ts))
           (rOf (applyActs blank (frProg blank endSym mark orcB k n Fo Fr ts) ts))
     else [])

/-- 削除ループ全体の動作列。 -/
def stripProg2 (blank endSym mark : Fin sc) (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if Tape.read ts.V2 = endSym then []
      else
        stripStep blank endSym mark orcB k n Fo Fr ts ++
          (if probe blank
              (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts).Cd = mark then
            stripProg2 blank endSym mark orcB k n Fo Fr fuel
              (applyActs blank (stripStep blank endSym mark orcB k n Fo Fr ts) ts)
          else [])

/-- **主定理（削除ループ `stripLoop2` のテープ実現とコスト）**。
`A = 16k + 32`, `B = k + 4`：総動作数は `A * stripLoop2Work + B * fuel` 以下。
終状態では `Cs` が新しい切断 `stripLoop2 x k bound fuel s` を保持する（`Cf`、`Cr` は不変）。 -/
theorem stripProg2_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {bound n : ℕ} (hn : x.length ≤ n)
    (horcB : ∀ ts', orcB ts' = decide (pOf ts' < bound)) :
    ∀ (fuel s : ℕ) (ts : Tapes sc), s ≤ x.length →
      Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, s, 0⟩ ts →
      ((stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1) fuel ts).length
          ≤ (16 * k + 32) * stripLoop2Work x k bound fuel s + (k + 4) * fuel
        ∧ (∃ P, stripLoop2 x k bound fuel s + P ≤ x.length ∧
            Enc blank startSym endSym mark x (stripLoop2 x k bound fuel s)
              (stripLoop2 x k bound fuel s + P)
              ⟨(k - 1) * P, 0, 0, P, 0, stripLoop2 x k bound fuel s, 0⟩
              (applyActs blank
                (stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1)
                  fuel ts) ts))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s ts _ hE
      refine ⟨by simp [stripProg2, stripLoop2Work], ⟨0, ?_, ?_⟩⟩
      · rw [stripLoop2]; omega
      · rw [stripProg2, applyActs_nil, stripLoop2]
        simpa using hE
  | succ fuel ih =>
      intro s ts hs hE
      have hdrop : (x.drop s).length = x.length - s := by simp
      have hnn : (x.drop s).length ≤ n := by omega
      by_cases hend2 : Tape.read ts.V2 = endSym
      · -- `s = |x|`：`firstOuter` は `none`
        have heq : s = x.length := by
          have := (read_pat_end_iff hend hE.v2).1 hend2
          omega
        have hng : ¬ (1 < (x.drop s).length ∧ 1 < bound) := by rw [hdrop]; omega
        have hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 = none := by
          rw [firstOuter, if_neg hng]
        refine ⟨?_, ⟨0, ?_, ?_⟩⟩
        · rw [stripProg2, if_pos hend2]
          simp
        · rw [stripLoop2]
          simp only [hfo]
          omega
        · rw [stripProg2, if_pos hend2, applyActs_nil, stripLoop2]
          simp only [hfo]
          simpa using hE
      · have hslt : s < x.length := by
          have hne : s ≠ x.length := fun hc => hend2 (read_pat_end hE.v2 hc)
          omega
        obtain ⟨hfcost, hfsome, hfex, hfnone⟩ := fpProg_spec (blank := blank)
          (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k)
          (bound := bound) (Fo := x.length + 1) (n := n) hk hend hmark hslt hnn horcB hE
        obtain ⟨FO, hFO⟩ : ∃ FO, firstOuterWork (x.drop s) k bound (x.length + 1) 1 = FO :=
          ⟨_, rfl⟩
        rw [hFO] at hfcost
        rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
        · -- 失敗：切断はそのまま
          obtain ⟨P, hP1, hP2, hP3⟩ := hfnone hfo
          have hprobe : ¬ (probe blank
              (applyActs blank (fpProg blank endSym mark orcB k n (x.length + 1) ts) ts).Cd
                = mark) := by
            intro hc
            have hcd : Tape.CounterView' blank mark
                (applyActs blank (fpProg blank endSym mark orcB k n (x.length + 1) ts) ts).Cd
                ((k - 1) * P) := hP3.cd
            have h0 := (probe_iff hmark hcd).1 hc
            have hle : P ≤ (k - 1) * P := Nat.le_mul_of_pos_left P (by omega)
            omega
          have hstep : stripStep blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts
              = fpProg blank endSym mark orcB k n (x.length + 1) ts := by
            rw [stripStep, if_neg hprobe]
            simp
          have hprog : stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1)
              (fuel + 1) ts = fpProg blank endSym mark orcB k n (x.length + 1) ts := by
            rw [stripProg2, if_neg hend2, hstep, if_neg hprobe]
            simp
          refine ⟨?_, ⟨P, ?_, ?_⟩⟩
          · rw [hprog, stripLoop2Work]
            simp only [hfo, hFO, Nat.add_zero]
            have hmono : (2 * k + 22) * FO ≤ (16 * k + 32) * FO :=
              Nat.mul_le_mul_right FO (by omega)
            have hj : k + 4 ≤ (k + 4) * (fuel + 1) :=
              Nat.le_mul_of_pos_right _ (by omega)
            omega
          · rw [stripLoop2]
            simp only [hfo]
            omega
          · rw [hprog, stripLoop2]
            simp only [hfo]
            exact hP3
        · -- 成功：`extendReach` して切断を進める
          obtain ⟨hEnc1, hwk⟩ := hfsome p m hfo
          have hprobe : probe blank
              (applyActs blank (fpProg blank endSym mark orcB k n (x.length + 1) ts) ts).Cd
                = mark := by
            have hcd : Tape.CounterView' blank mark
                (applyActs blank (fpProg blank endSym mark orcB k n (x.length + 1) ts) ts).Cd
                0 := hEnc1.cd
            exact (probe_iff hmark hcd).2 rfl
          have hp : 0 < p := firstOuter_pos (x.drop s) k bound _ 1 p m (by omega) hfo
          have hm : m = p + (k - 1) * p := firstOuter_snd (x.drop s) k bound _ 1 p m hfo
          have hmk : m = k * p := by
            have : k * p = (k - 1) * p + p := by
              have hkk : k = (k - 1) + 1 := by omega
              calc k * p = ((k - 1) + 1) * p := by rw [← hkk]
                _ = (k - 1) * p + p := by ring
            omega
          obtain ⟨hEnc2, hrcost, hwk2, hmr, hrle⟩ := frProg_spec (blank := blank)
            (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k)
            (bound := bound) (Fo := x.length + 1) (n := n) hk hend hmark hslt hnn horcB hE hfo
          obtain ⟨r, hr⟩ : ∃ r, extendReach (x.drop s) p (x.length + 1) m = r := ⟨_, rfl⟩
          rw [hr] at hEnc2 hmr hrle
          obtain ⟨ER, hER⟩ : ∃ ER, extendReachWork (x.drop s) p (x.length + 1) m = ER :=
            ⟨_, rfl⟩
          rw [hER] at hrcost hrle
          rw [hFO] at hrcost hwk2
          have hr' : extendReach (x.drop s) p (x.length + 1) (k * p) = r := by
            rw [← hmk]; exact hr
          have hER' : extendReachWork (x.drop s) p (x.length + 1) (k * p) = ER := by
            rw [← hmk]; exact hER
          have hsr : s + r ≤ x.length := pat_le hEnc2.v2
          have hpOf : pOf (applyActs blank
              (frProg blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts) ts) = p :=
            pOf_eq hEnc2
          have hrOf : rOf (applyActs blank
              (frProg blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts) ts) = r :=
            rOf_eq hEnc2
          have hkp : k * p ≤ r := by omega
          have hpr : p ≤ r := by
            have : p ≤ k * p := Nat.le_mul_of_pos_left p (by omega)
            omega
          have hfit : s + (r - k * p + 1) ≤ x.length := by omega
          have hadv := advanceProg_enc (blank := blank) (startSym := startSym)
            (endSym := endSym) (mark := mark) (x := x) (k := k) hkp hpr hfit hEnc2
          -- 新しい切断
          have hs' : stripLoop2 x k bound (fuel + 1) s
              = stripLoop2 x k bound fuel (s + (r - k * p + 1)) := by
            rw [stripLoop2]
            simp only [hfo, hr']
          have hstep : stripStep blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts
              = frProg blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts ++
                advanceProg blank k p r := by
            rw [stripStep, if_pos hprobe, hpOf, hrOf, frProg_split]
            simp [List.append_assoc]
          have hnext : Enc blank startSym endSym mark x (s + (r - k * p + 1))
              (s + (r - k * p + 1)) ⟨0, 0, 0, 0, 0, s + (r - k * p + 1), 0⟩
              (applyActs blank
                (stripStep blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts) ts) := by
            rw [hstep, applyActs_append, frProg_split, applyActs_append]
            rw [frProg_split, applyActs_append] at hadv
            exact hadv
          obtain ⟨hrc, hre⟩ := ih (s + (r - k * p + 1)) _ (by omega) hnext
          have hprog : stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1)
              (fuel + 1) ts
              = stripStep blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts ++
                stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1) fuel
                  (applyActs blank
                    (stripStep blank endSym mark orcB k n (x.length + 1) (x.length + 1) ts) ts) := by
            rw [stripProg2, if_neg hend2, if_pos hprobe]
          refine ⟨?_, ?_⟩
          · rw [hprog, List.length_append, hstep, List.length_append, stripLoop2Work]
            simp only [hfo, hFO, hER', hr']
            have hadvlen := advanceProg_length blank (k := k) (P := p) (R := r) hpr hkp
            obtain ⟨W2, hW2⟩ : ∃ W2, stripLoop2Work x k bound fuel (s + (r - k * p + 1)) = W2 :=
              ⟨_, rfl⟩
            rw [hW2] at hrc
            rw [hstep] at hrc
            rw [hW2]
            obtain ⟨A, hA⟩ : ∃ A, 16 * k + 32 = A := ⟨_, rfl⟩
            rw [hA] at hrc ⊢
            have hpFO : p ≤ FO := by
              have : p ≤ (k - 1) * p := Nat.le_mul_of_pos_left p (by omega)
              omega
            have hkpFO : k * p ≤ k * FO := Nat.mul_le_mul_left k hpFO
            have hexp : A * (FO + (ER + W2)) = A * FO + A * ER + A * W2 := by ring
            have hkFO : 14 * (k * FO) ≤ (14 * k) * FO := by
              have : 14 * (k * FO) = (14 * k) * FO := by ring
              omega
            have hm1 : (2 * k + 32) * FO + (14 * k) * FO ≤ A * FO := by
              calc (2 * k + 32) * FO + (14 * k) * FO = (2 * k + 32 + 14 * k) * FO := by ring
                _ ≤ A * FO := Nat.mul_le_mul_right FO (by omega)
            have hm2 : 14 * ER ≤ A * ER := Nat.mul_le_mul_right ER (by omega)
            have hrkp : r ≤ k * p + ER := by omega
            have hkp2 : 11 * r + 3 * (k * p) ≤ 14 * (k * FO) + 11 * ER := by omega
            have hfe : (k + 4) * (fuel + 1) = (k + 4) * fuel + (k + 4) := by ring
            omega
          · rw [hprog, applyActs_append, hs']
            obtain ⟨P', hP'1, hP'2⟩ := hre
            exact ⟨P', hP'1, hP'2⟩


/-- `Cd` を `n` 回減らす（2 動作／回）。 -/
def dzUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cd blank .left, Act.Cd blank .stay]

def dzLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => dzUnit blank ++ dzLoop blank n

@[simp] theorem dzLoop_length (blank : Fin sc) (n : ℕ) : (dzLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [dzLoop]
  | succ n ih => simp only [dzLoop, List.length_append, dzUnit, ih]; simp; omega

theorem applyActs_dzUnit (ts : Tapes sc) :
    applyActs blank (dzUnit blank) ts =
      { ts with
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) blank .stay } := rfl

theorem dzLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D + n, Q, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (dzLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [dzLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨(D + n) + 1, Q, E, P, F, S, R⟩ ts := by
        have e1 : D + (n + 1) = (D + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D + n, Q, E, P, F, S, R⟩
          (applyActs blank (dzUnit blank) ts) := by
        rw [applyActs_dzUnit]
        exact ⟨hE'.v1, hE'.v2, by simpa using Tape.counter'_dec (n := D + n) hE'.cd,
          hE'.cq, hE'.ce, hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      exact by simp only [dzLoop, applyActs_append]; exact ih a b D Q E P F S R _ hstep

/-- 削除ループ終了後の後始末：`V2` を切断へ戻し、`Cd`/`Cp` を `0` にして「まっさら」な状態に
する。動作数 `(2k+1)*P`。 -/
def cleanProg (blank : Fin sc) (k P : ℕ) : List (Act sc) :=
  pvLoop blank P ++ dzLoop blank ((k - 1) * P)

theorem cleanProg_length (blank : Fin sc) (k P : ℕ) :
    (cleanProg blank k P).length = 3 * P + 2 * ((k - 1) * P) := by
  simp [cleanProg]

theorem cleanProg_enc {s P F : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, s, 0⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩
      (applyActs blank (cleanProg blank k P) ts) := by
  have h1 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) P s s ((k - 1) * P) 0 0 0 F s 0 ts
    (by rw [show (0 : ℕ) + P = P from by omega]; exact hE)
  have h2 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) ((k - 1) * P) s s 0 0 0 0 F s 0 _
    (by rw [show (0 : ℕ) + (k - 1) * P = (k - 1) * P from by omega]; exact h1)
  rw [cleanProg, applyActs_append]
  exact h2

end Strip2

/-! ## 14. 小例による健全性チェック -/

section Examples

example : stays 8 20 0 = ceilDiv 20 8 := by decide
example : (rewindLoop (0 : Fin 3) 8 5 0).length = 5 * 5 + stays 8 5 0 := by decide
example : (shiftLoop (0 : Fin 3) 8 4).length = (4 + (8 - 1)) * 4 := by decide
example : (loadR (0 : Fin 3) 6 2).length = 3 * 6 + 7 * 2 := by decide
example : (initActs (0 : Fin 3) 8).length = (8 - 1) + 2 := by decide
example : (qrLoop (0 : Fin 3) 7).length = 3 * 7 := by decide
example : (cdIncs (0 : Fin 3) 7).length = 7 := by decide

end Examples

/-! ## 15. 到達点と残り

### 完成しているもの（すべて sorry なし）

* **配置**（§1–§3）：文字テープ 2 本 `V1`/`V2`（語 `startSym :: (x ++ [endSym])`、ヘッドは
  `x` の絶対添字）とマーカ付き単進カウンタ 7 本 `Cd`（予算 `(k-1)p-q`）、`Cq`、`Ce`、`Cp`、
  `Cf`、`Cs`（切断）、`Cr`（reach）。`v = x.drop s` は作り直さず `v` の添字 `i` を `x` の
  添字 `s+i` として読む。
* **内側の自己照合ループ**（§4–§5）：`mProg_spec` / `mProg_length : ≤ 5 * mWork` /
  `mSteps_firstInner`。`q < (k-1)*p` は `Cd` の probe で実際に判定する。
* **`extendReach`**（§6）：`rProg_spec` / `rProg_length : ≤ 3 * rWork` / `rSteps_extendReach`。
* **外側 1 反復の再配置**（§7–§8）：`rewindLoop`（`⌈q/k⌉` を数える mod `k` スケジュール）、
  `maxOneActs`、`shiftLoop`、`shiftPhase_enc'`（一般形）/`shiftPhase_enc`。
* **`firstOuter`（`bound` 付き）**（§9）：`oProg` は番人 `endSym`（`p < |v|`）に加えて
  候補上限 `p < bound` をオラクル `orcB` で判定する。`oProg_spec`：
  `≤ (2k+22) * firstOuterWork (x.drop s) k bound fuel p`、成功時のテープ内容と
  `(k-1)*p' ≤ firstOuterWork`、失敗時（`none`）は「きれいな状態」
  `Enc x s (s+P) ⟨(k-1)P,0,0,P,F,S,R⟩`（`0 < P`）に止まる。
  燃料非依存性 `firstInner_fuel` により内側燃料 `Fi` は `|v|+1` 以上なら何でもよい。
* **`fpProg` / `frProg`**（§9–§10）：`initActs`、`loadR`、
  `frProg_spec`：`≤ (k-1)+2 + (2k+32)*firstOuterWork + 3*extendReachWork`、出力
  `Cp = p₁`、`Cr = r`、`V1 = s+(r-p₁)`、`V2 = s+r`、および `m ≤ r ≤ m + extendReachWork`。
* **`_second_period`**（§11–§12）：内側 `sProg_spec`（`≤ 3 * sWork`）、
  `sInner_none_iff`（中断のテープ判定）、周期ずらし `periodShift`、外側
  `soProg_spec`：**`≤ (k+12) * secondOuterWork + (k+9)*q + 2`**（入口 `q=0` なら `+2` のみ）。
  償却は `q` の減少ぶんを払う形で、ポテンシャル `(k+2)p+q` を使わずに済む。
  `spProg_spec` は `secondPeriod` への系。再配置 `repoProg`（`≤ 8r + 17p₁`）。
* **外側 1 反復の合成**（§12）：`stepProg_spec`：
  **`≤ (2k+65) * decomposeStepWork x k s + (k+3)`**。
* **新しい削除規則**（§13）：切断の前進 `advanceProg`
  （`V1`/`V2` を切断へ戻し、`Cr` から `k` 回 `Cp` を引いて `d = r - k*p + 1` を作り、
  `Cs` へ流し込みながら両ヘッドを右へ）。`advanceProg_enc` / `advanceProg_length :
  ≤ 11r + 3(k*p) + 3`。1 反復 `stripStep`（`firstOuter` の成否は `Cd` の probe で判定）と
  ループ `stripProg2`、そして
  **`stripProg2_spec : ≤ (16k+32) * stripLoop2Work x k bound fuel s + (k+4) * fuel`**
  （`PalPeg.GSDecompose2` の `stripLoop2` / `stripLoop2Work` をそのまま鏡写しにしている）。
  終状態は `Cs = stripLoop2 x k bound fuel s` を保持する「きれいな状態」
  `Enc x s' (s'+P) ⟨(k-1)P,0,0,P,0,s',0⟩`。後始末 `cleanProg`（`(2k+1)*P` 動作）で
  まっさらな状態 `Enc x s' s' ⟨0,0,0,0,0,s',0⟩` に戻せる。

### 未実装（`decomposeLoop2` / `decompose2_on_tapes`）

必要な部品はすべて揃っていて、残りは次の 3 点である。

1. **オラクル `orcB` の一本化**。`stripProg2` の上限は `bound = p₂` だが、`p₂` は反復ごとに
   変わるので、プログラム側では `orcB ts' = decide (pOf ts' < fOf ts')`（`Cp` と `Cf` の
   平行歩行）に統一し、削除ループの間 `Cf = p₂` を保つのが自然。そのため `oProg_spec` の
   仮定 `horcB : ∀ ts', orcB ts' = decide (pOf ts' < bound)` を
   「ループ状態 `Enc x s (s+p') ⟨(k-1)p',0,0,p',F,S,R⟩` 上でのみ
   `oCondB ↔ (p' < |v| ∧ p' < bound)`」という形に弱めればよい
   （`F`, `S`, `R` を `∀` の外へ出す必要がある）。
2. **第 2 相の後始末**。`stepProg` 終了後（`V1 = s+q`, `V2 = s+p₂+q`, `Cp = p₂`,
   `Cf = p₁`, `Cr = r`）から削除ループの入口（`Cf = p₂`、他は `0`、両ヘッド `s`）へ戻す
   プログラム。`rvLoop`/`pvLoop`/`pzLoop`/`dzLoop`/`pfLoop` の組み合わせで `O(p₂+q+r+p₁)`。
   課金には `p₂ ≤ 1 + 2*secondOuterWork` が要る（`oProg_spec` の `none` 節に
   `P ≤ p + firstOuterWork` を足したのと同じ議論を `soProg_spec` にも足す）。
3. **`decomposeLoop2` の外側帰納法**。`stepProg_spec` と `stripProg2_spec` と `cleanProg` を
   つなぐだけで、形は `oProg_spec` / `stripProg2_spec` と同じ。
   `decomposeLoop2Work x k fuel s = decomposeStepWork x k s + (… + stripLoop2Work … + 再帰)`
   なので、1 反復あたり `(2k+65)*decomposeStepWork + (16k+32)*stripLoop2Work + O(k)` となり、
   全体で `decompose2_on_tapes : ≤ (16k+65) * decompose2Work x k + O(k) * (反復数)` が出る。
-/

end PalPeg.GSPre
