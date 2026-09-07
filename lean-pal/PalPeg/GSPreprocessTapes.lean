import PalPeg.GSPreprocess
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
def oProg (blank endSym mark : Fin sc) (k Fi : ℕ) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if Tape.read ts.V2 = endSym then []
      else if oSucc blank endSym mark Fi ts then oHead blank endSym mark Fi ts
      else oHead blank endSym mark Fi ts ++
        (shiftPhase blank mark k (applyActs blank (oHead blank endSym mark Fi ts) ts) ++
          oProg blank endSym mark k Fi fuel
            (applyActs blank
              (shiftPhase blank mark k (applyActs blank (oHead blank endSym mark Fi ts) ts))
              (applyActs blank (oHead blank endSym mark Fi ts) ts)))

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
    {s : ℕ} (hs : s ≤ x.length) :
    ∀ (fuel p F S R : ℕ) (ts : Tapes sc), 0 < p → s + p ≤ x.length →
      Enc blank startSym endSym mark x s (s + p) ⟨(k - 1) * p, 0, 0, p, F, S, R⟩ ts →
      ((oProg blank endSym mark k ((x.drop s).length + 1) fuel ts).length
          ≤ (2 * k + 22) * firstOuterWork (x.drop s) k (x.drop s).length fuel p
        ∧ (∀ p' m, firstOuter (x.drop s) k (x.drop s).length fuel p = some (p', m) →
            Enc blank startSym endSym mark x (s + (k - 1) * p') (s + m)
              ⟨0, (k - 1) * p', 0, p', F, S, R⟩
              (applyActs blank
                (oProg blank endSym mark k ((x.drop s).length + 1) fuel ts) ts)
            ∧ (k - 1) * p'
                ≤ firstOuterWork (x.drop s) k (x.drop s).length fuel p)
        ∧ (∃ a b D Q E P, Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
              (applyActs blank
                (oProg blank endSym mark k ((x.drop s).length + 1) fuel ts) ts))) := by
  have hdroplen : (x.drop s).length = x.length - s := by simp
  intro fuel
  induction fuel with
  | zero =>
      intro p F S R ts _ _ hE
      refine ⟨?_, ?_, ?_⟩
      · rw [oProg, firstOuterWork]; simp
      · intro p' m hc; rw [firstOuter] at hc; simp at hc
      · refine ⟨s, s + p, (k - 1) * p, 0, 0, p, ?_⟩
        rw [oProg, applyActs_nil]
        exact hE
  | succ fuel ih =>
      intro p F S R ts hp hsp hE
      by_cases hguard : Tape.read ts.V2 = endSym
      · have heq : s + p = x.length := (read_pat_end_iff hend hE.v2).1 hguard
        have hng : ¬ (p < (x.drop s).length ∧ p < (x.drop s).length) := by
          rw [hdroplen]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [oProg, if_pos hguard, firstOuterWork, if_neg hng]
          simp
        · intro p' m hc
          rw [firstOuter, if_neg hng] at hc
          simp at hc
        · refine ⟨s, s + p, (k - 1) * p, 0, 0, p, ?_⟩
          rw [oProg, if_pos hguard, applyActs_nil]
          exact hE
      · have hne : s + p ≠ x.length := fun hc => hguard (read_pat_end hE.v2 hc)
        have hlt : s + p < x.length := by omega
        have hg : p < (x.drop s).length ∧ p < (x.drop s).length := by rw [hdroplen]; omega
        obtain ⟨hhead, hqle, hlen, hmid⟩ :=
          oHead_enc (blank := blank) (startSym := startSym) (endSym := endSym) (mark := mark)
            (x := x) (k := k) hk hend hmark hs hsp ((x.drop s).length + 1) hE
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
        by_cases hsucc : oSucc blank endSym mark ((x.drop s).length + 1) ts
        · -- 成功枝
          have hd0 : (k - 1) * p - firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = 0 :=
            (probe_iff hmark hmid.cd).1 hsucc
          have hqeq : firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = (k - 1) * p := by
            omega
          have hprog : oProg blank endSym mark k ((x.drop s).length + 1) (fuel + 1) ts
              = oHead blank endSym mark ((x.drop s).length + 1) ts := by
            rw [oProg, if_neg hguard, if_pos hsucc]
          have hres : Enc blank startSym endSym mark x (s + (k - 1) * p)
              (s + (p + (k - 1) * p)) ⟨0, (k - 1) * p, 0, p, F, S, R⟩
              (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts) := by
            have e1 : s + p + (k - 1) * p = s + (p + (k - 1) * p) := by omega
            rw [hqeq, Nat.sub_self, e1] at hhead
            exact hhead
          refine ⟨?_, ?_, ?_⟩
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
                  (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts))
                (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts)) := by
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
          have hprog : oProg blank endSym mark k ((x.drop s).length + 1) (fuel + 1) ts
              = oHead blank endSym mark ((x.drop s).length + 1) ts ++
                (shiftPhase blank mark k
                    (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts) ++
                  oProg blank endSym mark k ((x.drop s).length + 1) fuel
                    (applyActs blank
                      (shiftPhase blank mark k
                        (applyActs blank
                          (oHead blank endSym mark ((x.drop s).length + 1) ts) ts))
                      (applyActs blank
                        (oHead blank endSym mark ((x.drop s).length + 1) ts) ts))) := by
            rw [oProg, if_neg hguard, if_neg hsucc]
          have happ : applyActs blank
              (oProg blank endSym mark k ((x.drop s).length + 1) (fuel + 1) ts) ts
              = applyActs blank
                (oProg blank endSym mark k ((x.drop s).length + 1) fuel
                  (applyActs blank
                    (shiftPhase blank mark k
                      (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts))
                    (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts)))
                (applyActs blank
                  (shiftPhase blank mark k
                    (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts))
                  (applyActs blank (oHead blank endSym mark ((x.drop s).length + 1) ts) ts)) := by
            rw [hprog, applyActs_append, applyActs_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [hprog, firstOuterWork, if_pos hg, if_neg hqne]
            simp only [List.length_append]
            -- 記号を潰して算術に落とす
            obtain ⟨W, hW⟩ : ∃ W, firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 = W :=
              ⟨_, rfl⟩
            obtain ⟨Wo, hWo⟩ : ∃ Wo, firstOuterWork (x.drop s) k (x.drop s).length fuel
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
            exact hrec.2.2

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
def fpProg (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : List (Act sc) :=
  initActs blank k ++
    oProg blank endSym mark k (n + 1) (n + 1) (applyActs blank (initActs blank k) ts)

/-- **主定理（`firstPeriod` のテープ実現とコスト）**。 -/
theorem fpProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s F S R : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, R⟩ ts) :
    ((fpProg blank endSym mark k (x.drop s).length ts).length
        ≤ (k - 1) + 2 + (2 * k + 22) *
            firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1
      ∧ (∀ p₁ m, firstPeriod (x.drop s) k = some (p₁, m) →
          Enc blank startSym endSym mark x (s + (k - 1) * p₁) (s + m)
            ⟨0, (k - 1) * p₁, 0, p₁, F, S, R⟩
            (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)
          ∧ (k - 1) * p₁ ≤ firstOuterWork (x.drop s) k (x.drop s).length
              ((x.drop s).length + 1) 1)
      ∧ (∃ a b D Q E P, Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
            (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts))) := by
  have hsle : s ≤ x.length := le_of_lt hs
  have hinit := initActs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) hs hE
  have hinit' : Enc blank startSym endSym mark x s (s + 1) ⟨(k - 1) * 1, 0, 0, 1, F, S, R⟩
      (applyActs blank (initActs blank k) ts) := hinit
  obtain ⟨hcost, hsome, hex⟩ := oProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hend hmark hsle
    ((x.drop s).length + 1) 1 F S R (applyActs blank (initActs blank k) ts)
    (by omega) (by omega) hinit'
  have happ : applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts =
      applyActs blank
        (oProg blank endSym mark k ((x.drop s).length + 1) ((x.drop s).length + 1)
          (applyActs blank (initActs blank k) ts))
        (applyActs blank (initActs blank k) ts) := by
    rw [fpProg, applyActs_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [fpProg, List.length_append, initActs_length]
    omega
  · intro p₁ m hc
    obtain ⟨hEnc, hwk⟩ := hsome p₁ m hc
    exact ⟨by rw [happ]; exact hEnc, hwk⟩
  · rw [happ]
    exact hex

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

/-- `Cp` の読み出し。 -/
def pOf (ts : Tapes sc) : ℕ := ts.Cp.left.length - 1

theorem pOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : pOf ts = c.p := ctr_len hE.cp

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
def frProg (blank endSym mark : Fin sc) (k n Fr : ℕ) (ts : Tapes sc) : List (Act sc) :=
  fpProg blank endSym mark k n ts ++
    (loadR blank (qOf (applyActs blank (fpProg blank endSym mark k n ts) ts))
        (pOf (applyActs blank (fpProg blank endSym mark k n ts) ts)) ++
      rProg blank endSym Fr
        (applyActs blank
          (loadR blank (qOf (applyActs blank (fpProg blank endSym mark k n ts) ts))
            (pOf (applyActs blank (fpProg blank endSym mark k n ts) ts)))
          (applyActs blank (fpProg blank endSym mark k n ts) ts)))

/-- **主定理（`firstPeriod` + `extendReach` のテープ実現とコスト）**。
出力：`Cp = p₁`、`Cr = r`（`Cs` と `Cf` は不変）、ヘッドは `V1 = s + (r - p₁)`、`V2 = s + r`。 -/
theorem frProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s F S : ℕ} {ts : Tapes sc} (hs : s < x.length)
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, S, 0⟩ ts)
    {p₁ m : ℕ} (hfp : firstPeriod (x.drop s) k = some (p₁, m)) :
    (Enc blank startSym endSym mark x
        (s + (extendReach (x.drop s) p₁ (x.length + 1) m - p₁))
        (s + extendReach (x.drop s) p₁ (x.length + 1) m)
        ⟨0, 0, 0, p₁, F, S, extendReach (x.drop s) p₁ (x.length + 1) m⟩
        (applyActs blank (frProg blank endSym mark k (x.drop s).length (x.length + 1) ts) ts)
      ∧ (frProg blank endSym mark k (x.drop s).length (x.length + 1) ts).length
          ≤ (k - 1) + 2
            + (2 * k + 32) * firstOuterWork (x.drop s) k (x.drop s).length
                ((x.drop s).length + 1) 1
            + 3 * extendReachWork (x.drop s) p₁ (x.length + 1) m) := by
  have hsle : s ≤ x.length := le_of_lt hs
  obtain ⟨hfcost, hfsome, _⟩ := fpProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hend hmark hs hE
  obtain ⟨h1, hwk⟩ := hfsome p₁ m hfp
  have hm : m = p₁ + (k - 1) * p₁ := firstOuter_snd (x.drop s) k (x.drop s).length _ 1 p₁ m hfp
  -- カウンタ読み出し
  have hq1 : qOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)
      = (k - 1) * p₁ := qOf_eq h1
  have hp1 : pOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts) = p₁ :=
    pOf_eq h1
  -- `Cr := (k-1)*p₁ + p₁ = m`
  have h2 : Enc blank startSym endSym mark x (s + (k - 1) * p₁) (s + m)
      ⟨0, 0, 0, p₁, F, S, m⟩
      (applyActs blank
        (loadR blank (qOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts))
          (pOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)))
        (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)) := by
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
  have happ : applyActs blank (frProg blank endSym mark k (x.drop s).length (x.length + 1) ts) ts
      = applyActs blank
          (rProg blank endSym (x.length + 1)
            (applyActs blank
              (loadR blank
                (qOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts))
                (pOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)))
              (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)))
          (applyActs blank
            (loadR blank
              (qOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts))
              (pOf (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)))
            (applyActs blank (fpProg blank endSym mark k (x.drop s).length ts) ts)) := by
    rw [frProg, applyActs_append, applyActs_append]
  constructor
  · rw [happ, ← hr]
    have e1 : s + (m + j - p₁) = s + (k - 1) * p₁ + j := by omega
    have e2 : s + (m + j) = s + m + j := by omega
    rw [e1, e2]
    exact h3
  · rw [frProg, List.length_append, List.length_append, loadR_length, hq1, hp1]
    have hple : p₁ ≤ (k - 1) * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
    obtain ⟨Wo, hWo⟩ : ∃ Wo, firstOuterWork (x.drop s) k (x.drop s).length
        ((x.drop s).length + 1) 1 = Wo := ⟨_, rfl⟩
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

end Second

/-! ## 12. 小例による健全性チェック -/

section Examples

example : stays 8 20 0 = ceilDiv 20 8 := by decide
example : (rewindLoop (0 : Fin 3) 8 5 0).length = 5 * 5 + stays 8 5 0 := by decide
example : (shiftLoop (0 : Fin 3) 8 4).length = (4 + (8 - 1)) * 4 := by decide
example : (loadR (0 : Fin 3) 6 2).length = 3 * 6 + 7 * 2 := by decide
example : (initActs (0 : Fin 3) 8).length = (8 - 1) + 2 := by decide
example : (qrLoop (0 : Fin 3) 7).length = 3 * 7 := by decide
example : (cdIncs (0 : Fin 3) 7).length = 7 := by decide

end Examples

/-! ## 13. 到達点と残り

### 完成しているもの

* **配置**（§1–§3）：文字テープ 2 本 `V1`/`V2`（語 `startSym :: (x ++ [endSym])`、
  ヘッドは `x` の絶対添字）とマーカ付き単進カウンタ 7 本
  `Cd`（予算 `(k-1)p - q`）、`Cq`、`Ce`、`Cp`、`Cf`、`Cs`、`Cr`。
  `v = x.drop s` は作り直さず、`v` の添字 `i` を `x` の添字 `s + i` として読む。
* **内側の自己照合ループ**（§4–§5）：`mCond`/`mActs`/`mProg`、
  `mCond_iff`（テープ読み取り＝添字条件）、`enc_m_step`/`enc_m_stop`、
  `mProg_spec`（実現）、`mProg_length : ≤ 5 * mWork`、
  `mSteps_firstInner`（`mSteps`/`mWork` = `firstInner`/`firstInnerWork`）。
  比較 `q < (k-1)*p` は `Cd` の probe（1 セル左へ動いて読む）で**実際に**判定し、
  `Cd` は 1 反復 ±1 でしか動かさない。
* **`extendReach`**（§6）：`rCond`/`rActs`/`rProg`、`rProg_spec`、
  `rProg_length : ≤ 3 * rWork`、`rSteps_extendReach`。
  `t = r - p` と置けば同じ双子走査で、`firstPeriod` 成功直後のヘッド位置が
  そのまま `extendReach` の初期位置になる（再配置ゼロ）。
* **外側 1 反復の再配置**（§7–§8）：`rewindLoop`（巻き戻しつつ `Cd` を復元し
  `Ce` に `⌈q/k⌉` を数える mod `k` スケジュール `stays`）、`maxOneActs`（`max 1 ·`）、
  `shiftLoop`（`p += e`、`V2` を `e` 右へ、`Cd` に `(k-1)e`）、合成 `shiftPhase`、
  `shiftPhase_enc'`（一般形）と `shiftPhase_enc`（`firstOuter` 用）。
  動作数 `≤ 5q + ⌈q/k⌉ + 3 + (k+3)*e`。
* **`firstOuter` / `firstPeriod`**（§9）：`oProg`、
  `oProg_spec`：総動作数 `≤ (2k+22) * firstOuterWork`（`A = 2k+22`, `B = 0`）、
  成功時のテープ内容、および `(k-1)*p₁ ≤ firstOuterWork`。
  `initActs`（`p := 1`, `Cd := k-1`, `O(k)` 動作）と `fpProg`/`fpProg_spec`。
* **カウンタ転送と `firstPeriod`+`extendReach` の合成**（§10）：
  `qrLoop`/`pcLoop`/`cpLoop`/`loadR`（`Cr := Cq + Cp`、`3Q + 7P` 動作）、
  `frProg`/`frProg_spec`：
  `≤ (k-1) + 2 + (2k+32) * firstOuterWork + 3 * extendReachWork` 動作で、
  `Cp = p₁`、`Cr = r`、ヘッド `V1 = s + (r - p₁)`、`V2 = s + r` になる。
* **`_second_period` の内側ループ**（§11）：`sCond`/`sActs`/`sProg`、
  `sProg_spec`（実現とコスト `≤ 3 * sWork`）、`sSteps_secondInner`
  （`sWork = secondInnerWork`、`sSteps` は `some q'` のときの一致長）。
  中断条件 `r < p + (q+1) ∧ (k-1)*p ≤ q+1` はオラクル `orc` として与える
  （`GSScanTapes` が走査段で `k*p₁ ≤ q ∧ q ≤ r` をオラクルにしたのと同じ扱い）。

### 未実装（意図的に残した部分）

* **`secondOuter`**：外側 2 分岐のうち、周期ずらし（`p += first`, `q -= first`、
  `V2` は不動で `V1` を `first` だけ左へ）は `Cf` を `Ce` 経由で往復させる
  `O(first)` のループで書ける。リセットずらしは `shiftPhase_enc'` がそのまま使える
  （`Cd` は第 2 相では未使用なので値は不問）。条件 `k*first ≤ q' ∧ q' ≤ r` は
  やはりオラクル。加えて、`extendReach` 直後の `(V1, V2) = (s + (r-p₁), s + r)` から
  第 2 相の入口 `(s, s + 1)` へ戻す再配置（`Cr` を `Ce` に写しながら `O(r)` 歩）が要る。
* **`stripLoop`**：`firstOuter` を `bound = p₂` で回す。`p < bound` の判定は
  素の番人では取れないので、`V1` の添字 `s + p₂` にマーカを書いて（1 パス `O(p₂)`）
  読み取りで判定する、というのが想定の実装。削除 `s := s + p` は
  `Cp` を `Cs` へ流し込みながら `V1` を `p` 右へ動かす `O(p)` で、捨てた接頭辞に課金される。
* **`decomposeLoop` と `decompose_on_tapes`**：上記が揃えば、外側 1 反復は
  `frProg`（`≤ (2k+32)*firstOuterWork + 3*extendReachWork + O(k)`）＋第 2 相
  ＋削除ループの合成で、`decomposeStepWork` に比例する。大域の線形性は
  `GSPreprocess.decomposeWork_le`（`4 ≤ k` で `≤ (16k+38)|x| + (2k+5)`）に委ねる。

いずれも本ファイルの雛形（`Enc` + 1 反復の動作列 + `applyActs` の帰納法）を
そのまま繰り返せば書ける。 -/

end PalPeg.GSPre
