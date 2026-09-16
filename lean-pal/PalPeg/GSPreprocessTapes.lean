import PalPeg.GSPreprocess
import PalPeg.GSDecompose2
import PalPeg.TapeLib

set_option autoImplicit true

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
  /-- 第 2 相の符号つき比較カウンタ（正部）。それ以外の相では常に `0`。 -/
  Ca : TapeConfiguration sc
  /-- 第 2 相の符号つき比較カウンタ（負部）。それ以外の相では常に `0`。 -/
  Cb : TapeConfiguration sc
  /-- 第 2 相の第 2 の符号つき比較カウンタ（負部）。それ以外の相では常に `0`。 -/
  Cc : TapeConfiguration sc

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
  | Ca : Fin sc → Move → Act sc
  | Cb : Fin sc → Move → Act sc
  | Cc : Fin sc → Move → Act sc

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
  | .Ca a m => { ts with Ca := Tape.step blank ts.Ca a m }
  | .Cb a m => { ts with Cb := Tape.step blank ts.Cb a m }
  | .Cc a m => { ts with Cc := Tape.step blank ts.Cc a m }

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

/-- 第1相の動作は追加の符号カウンタを変更しない。 -/
def Act.noSigned : Act sc → Prop
  | .Ca _ _ | .Cb _ _ | .Cc _ _ => False
  | _ => True

def NoSigned (acts : List (Act sc)) : Prop := ∀ act ∈ acts, act.noSigned

@[simp] theorem noSigned_nil : NoSigned ([] : List (Act sc)) := by
  simp [NoSigned]

@[simp] theorem noSigned_cons (act : Act sc) (acts : List (Act sc)) :
    NoSigned (act :: acts) ↔ act.noSigned ∧ NoSigned acts := by
  simp [NoSigned]

@[simp] theorem noSigned_append (xs ys : List (Act sc)) :
    NoSigned (xs ++ ys) ↔ NoSigned xs ∧ NoSigned ys := by
  simp [NoSigned, or_imp, forall_and]

theorem applyActs_signed_preserved (blank : Fin sc) (acts : List (Act sc))
    (h : NoSigned acts) (ts : Tapes sc) :
    (applyActs blank acts ts).Ca = ts.Ca ∧
    (applyActs blank acts ts).Cb = ts.Cb ∧
    (applyActs blank acts ts).Cc = ts.Cc := by
  induction acts generalizing ts with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons act acts ih =>
      obtain ⟨ha, hs⟩ := (noSigned_cons act acts).mp h
      have hi := ih hs (applyAct blank ts act)
      cases act <;> simp_all [Act.noSigned, applyActs_cons, applyAct]

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

/-! ### 第 2 相の符号つき比較カウンタ

`orcR` は内側走査の**1 ステップごと**に評価されるので、`Cr`/`Cp`/`Cq` を毎回
読み比べる実装では総コストが二乗になる。そこで

```
A := r - (p+q)      （符号つき）… 正部 `Ca`、負部 `Cb`
B := (k-1)*p - (q+1)（符号つき）… 正部 `Cd`、負部 `Cc`
```

の 2 つを符号つきカウンタとして持ち回る。`orcR ⟺ A ≤ 0 ∧ B ≤ 0 ⟺ A₊ = 0 ∧ B₊ = 0`
なので、判定は `Ca` と `Cd` の probe **2 回だけ**（`O(1)`）で済む。
内側 1 ステップでは `q` が 1 増えるので `A`, `B` がそれぞれ 1 減るだけ。 -/

/-- 符号つきカウンタの「負部」たちの値（正部は `Ctr` の `d` と `Ca` の値）。 -/
structure Ctr3 where
  /-- `A` の正部（テープ `Ca`）。 -/
  ap : ℕ
  /-- `A` の負部（テープ `Cb`）。 -/
  an : ℕ
  /-- `B` の負部（テープ `Cc`）。`B` の正部は `Ctr.d`（テープ `Cd`）。 -/
  bn : ℕ
  deriving DecidableEq

/-- 第 2 相の符号化：`Enc` に加えて `Ca`/`Cb`/`Cc` の内容も指定する。 -/
structure EncS (blank startSym endSym mark : Fin sc) (x : List (Fin sc))
    (a b : ℕ) (c : Ctr) (g : Ctr3) (ts : Tapes sc) : Prop where
  base : Enc blank startSym endSym mark x a b c ts
  ca : Tape.CounterView' blank mark ts.Ca g.ap
  cb : Tape.CounterView' blank mark ts.Cb g.an
  cc : Tape.CounterView' blank mark ts.Cc g.bn

theorem EncS.frame {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    {a b a' b' : ℕ} {c c' : Ctr} {g : Ctr3} {ts : Tapes sc}
    {acts : List (Act sc)}
    (hE : EncS blank startSym endSym mark x a b c g ts)
    (hacts : NoSigned acts)
    (hout : Enc blank startSym endSym mark x a' b' c' (applyActs blank acts ts)) :
    EncS blank startSym endSym mark x a' b' c' g (applyActs blank acts ts) := by
  obtain ⟨ha, hb, hc⟩ := applyActs_signed_preserved blank acts hacts ts
  refine ⟨hout, ?_, ?_, ?_⟩
  · rw [ha]; exact hE.ca
  · rw [hb]; exact hE.cb
  · rw [hc]; exact hE.cc

/-- Erase a known number of signed-counter cells, two tape actions per cell. -/
def eraseCells (mk : Fin sc → Move → Act sc) (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => [mk blank .left, mk blank .stay] ++ eraseCells mk blank n

@[simp] theorem eraseCells_length (mk : Fin sc → Move → Act sc) (blank : Fin sc) (n : ℕ) :
    (eraseCells mk blank n).length = 2 * n := by
  induction n with
  | zero => simp [eraseCells]
  | succ n ih => simp [eraseCells, ih]; omega

theorem eraseCells_Ca_enc {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    (n : ℕ) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c ({ g with ap := g.ap + n }) ts) :
    EncS blank startSym endSym mark x a b c g
      (applyActs blank (eraseCells Act.Ca blank n) ts) := by
  induction n generalizing ts with
  | zero => simpa [eraseCells] using hE
  | succ n ih =>
      have he : EncS blank startSym endSym mark x a b c ({ g with ap := g.ap + n })
          (applyActs blank [Act.Ca blank .left, Act.Ca blank .stay] ts) := by
        refine ⟨⟨hE.base.v1, hE.base.v2, hE.base.cd, hE.base.cq, hE.base.ce, hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩, by simpa [applyAct] using Tape.counter'_dec hE.ca, hE.cb, hE.cc⟩
      simpa only [eraseCells, applyActs_append] using ih he

theorem eraseCells_Cb_enc {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    (n : ℕ) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c ({ g with an := g.an + n }) ts) :
    EncS blank startSym endSym mark x a b c g
      (applyActs blank (eraseCells Act.Cb blank n) ts) := by
  induction n generalizing ts with
  | zero => simpa [eraseCells] using hE
  | succ n ih =>
      have he : EncS blank startSym endSym mark x a b c ({ g with an := g.an + n })
          (applyActs blank [Act.Cb blank .left, Act.Cb blank .stay] ts) := by
        refine ⟨⟨hE.base.v1, hE.base.v2, hE.base.cd, hE.base.cq, hE.base.ce, hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩, hE.ca, by simpa [applyAct] using Tape.counter'_dec hE.cb, hE.cc⟩
      simpa only [eraseCells, applyActs_append] using ih he

theorem eraseCells_Cc_enc {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    (n : ℕ) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c ({ g with bn := g.bn + n }) ts) :
    EncS blank startSym endSym mark x a b c g
      (applyActs blank (eraseCells Act.Cc blank n) ts) := by
  induction n generalizing ts with
  | zero => simpa [eraseCells] using hE
  | succ n ih =>
      have he : EncS blank startSym endSym mark x a b c ({ g with bn := g.bn + n })
          (applyActs blank [Act.Cc blank .left, Act.Cc blank .stay] ts) := by
        refine ⟨⟨hE.base.v1, hE.base.v2, hE.base.cd, hE.base.cq, hE.base.ce, hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩, hE.ca, hE.cb, by simpa [applyAct] using Tape.counter'_dec hE.cc⟩
      simpa only [eraseCells, applyActs_append] using ih he

theorem eraseCells_Cd_enc {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    (n : ℕ) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b ({ c with d := c.d + n }) g ts) :
    EncS blank startSym endSym mark x a b c g
      (applyActs blank (eraseCells Act.Cd blank n) ts) := by
  induction n generalizing ts with
  | zero => simpa [eraseCells] using hE
  | succ n ih =>
      have he : EncS blank startSym endSym mark x a b ({ c with d := c.d + n }) g
          (applyActs blank [Act.Cd blank .left, Act.Cd blank .stay] ts) := by
        refine ⟨⟨hE.base.v1, hE.base.v2, by simpa [applyAct] using Tape.counter'_dec hE.base.cd, hE.base.cq, hE.base.ce, hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩, hE.ca, hE.cb, hE.cc⟩
      simpa only [eraseCells, applyActs_append] using ih he

/-- 符号つきカウンタが `(k, r, p, q)` を正しく表していること。 -/
def SignedOK (k r p q : ℕ) (c : Ctr) (g : Ctr3) : Prop :=
  g.ap = r - (p + q) ∧ g.an = (p + q) - r
    ∧ c.d = (k - 1) * p - (q + 1) ∧ g.bn = (q + 1) - (k - 1) * p

/-- Clear the four cells counters used for signed comparisons. -/
def clearSigned (blank : Fin sc) (d : ℕ) (g : Ctr3) : List (Act sc) :=
  eraseCells Act.Cd blank d ++ (eraseCells Act.Ca blank g.ap ++
    (eraseCells Act.Cb blank g.an ++ eraseCells Act.Cc blank g.bn))

@[simp] theorem clearSigned_length (blank : Fin sc) (d : ℕ) (g : Ctr3) :
    (clearSigned blank d g).length = 2 * (d + g.ap + g.an + g.bn) := by
  simp [clearSigned]; omega

theorem clearSigned_enc {blank startSym endSym mark : Fin sc} {x : List (Fin sc)}
    {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b { c with d := 0 } ⟨0, 0, 0⟩
      (applyActs blank (clearSigned blank c.d g) ts) := by
  have hd := eraseCells_Cd_enc c.d (c := { c with d := 0 })
    (by simpa using hE)
  have ha := eraseCells_Ca_enc g.ap (g := { g with ap := 0 })
    (by simpa using hd)
  have hb := eraseCells_Cb_enc g.an (g := { g with ap := 0, an := 0 })
    (by simpa using ha)
  have hc := eraseCells_Cc_enc g.bn (g := ⟨0, 0, 0⟩)
    (by simpa using hb)
  simpa only [clearSigned, applyActs_append] using hc

theorem clearSigned_length_bound (blank : Fin sc) {k r p q : ℕ} {c : Ctr} {g : Ctr3}
    (hk : 1 ≤ k) (hok : SignedOK k r p q c g) :
    (clearSigned blank c.d g).length ≤ 2 * (r + k * p + 2 * q + 1) := by
  obtain ⟨ha, hb, hd, hc⟩ := hok
  rw [clearSigned_length, ha, hb, hd, hc]
  have hmul : (k - 1) * p + p = k * p := by
    calc
      (k - 1) * p + p = ((k - 1) + 1) * p := by simp [Nat.add_mul]
      _ = k * p := by rw [Nat.sub_add_cancel hk]
  omega

/-- **符号つきカウンタから読む中断オラクル**：`Ca` と `Cd` の probe だけを見る。 -/
def orcAB (blank mark : Fin sc) (ts : Tapes sc) : Bool :=
  decide (probe blank ts.Ca = mark ∧ probe blank ts.Cd = mark)

/-- **`orcAB` は `orcR` と一致する**（`O(1)` 動作で同じ判定ができる）。 -/
theorem orcAB_spec (hmark : mark ≠ blank) {k r p q a b : ℕ} {c : Ctr} {g : Ctr3}
    {ts : Tapes sc} (hE : EncS blank startSym endSym mark x a b c g ts)
    (hok : SignedOK k r p q c g) :
    orcAB blank mark ts = decide (r < p + q + 1 ∧ (k - 1) * p ≤ q + 1) := by
  obtain ⟨hap, _, hd, _⟩ := hok
  have h1 : probe blank ts.Ca = mark ↔ g.ap = 0 := probe_iff hmark hE.ca
  have h2 : probe blank ts.Cd = mark ↔ c.d = 0 := probe_iff hmark hE.base.cd
  rw [orcAB]
  refine decide_eq_decide.2 ⟨?_, ?_⟩
  · rintro ⟨e1, e2⟩
    rw [h1, hap] at e1
    rw [h2, hd] at e2
    omega
  · rintro ⟨e1, e2⟩
    refine ⟨h1.2 ?_, h2.2 ?_⟩
    · rw [hap]; omega
    · rw [hd]; omega

/-! #### 符号つき 1 減算（`O(1)` 動作） -/

/-- `A` を 1 減らす：正部 `Ca` が非零ならそれを 1 減らし、零なら負部 `Cb` を 1 増やす。 -/
def sDecA (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Ca = mark then
    [Act.Ca blank .left, Act.Ca mark .right, Act.Cb blank .right]
  else [Act.Ca blank .left, Act.Ca blank .stay]

/-- `B` を 1 減らす：正部 `Cd` が非零ならそれを 1 減らし、零なら負部 `Cc` を 1 増やす。 -/
def sDecB (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Cd = mark then
    [Act.Cd blank .left, Act.Cd mark .right, Act.Cc blank .right]
  else [Act.Cd blank .left, Act.Cd blank .stay]

theorem sDecA_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (sDecA blank mark ts).length ≤ 3 := by rw [sDecA]; split <;> simp

theorem sDecB_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (sDecB blank mark ts).length ≤ 3 := by rw [sDecB]; split <;> simp

theorem applyActs_sDecA_zero {ts : Tapes sc} (h : probe blank ts.Ca = mark) :
    applyActs blank (sDecA blank mark ts) ts =
      { ts with
        Ca := Tape.step blank (Tape.step blank ts.Ca blank .left) mark .right
        Cb := Tape.step blank ts.Cb blank .right } := by
  rw [sDecA, if_pos h]; rfl

theorem applyActs_sDecA_pos {ts : Tapes sc} (h : ¬ probe blank ts.Ca = mark) :
    applyActs blank (sDecA blank mark ts) ts =
      { ts with
        Ca := Tape.step blank (Tape.step blank ts.Ca blank .left) blank .stay } := by
  rw [sDecA, if_neg h]; rfl

theorem applyActs_sDecB_zero {ts : Tapes sc} (h : probe blank ts.Cd = mark) :
    applyActs blank (sDecB blank mark ts) ts =
      { ts with
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) mark .right
        Cc := Tape.step blank ts.Cc blank .right } := by
  rw [sDecB, if_pos h]; rfl

theorem applyActs_sDecB_pos {ts : Tapes sc} (h : ¬ probe blank ts.Cd = mark) :
    applyActs blank (sDecB blank mark ts) ts =
      { ts with
        Cd := Tape.step blank (Tape.step blank ts.Cd blank .left) blank .stay } := by
  rw [sDecB, if_neg h]; rfl

/-- **`sDecA` は `A` をちょうど 1 減らす**（符号つきの意味で）。他のテープは不変。 -/
theorem sDecA_enc (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b c
      ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn⟩
      (applyActs blank (sDecA blank mark ts) ts) := by
  obtain ⟨hb, hca, hcb, hcc⟩ := hE
  by_cases h : probe blank ts.Ca = mark
  · have hz : g.ap = 0 := (probe_iff hmark hca).1 h
    have hca0 : Tape.CounterView' blank mark ts.Ca 0 := by rw [← hz]; exact hca
    have e1 : g.ap - 1 = 0 := by omega
    rw [applyActs_sDecA_zero h]
    refine ⟨⟨hb.v1, hb.v2, hb.cd, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, ?_, ?_, hcc⟩
    · show Tape.CounterView' blank mark _ (g.ap - 1)
      rw [e1]
      simpa using Tape.counter'_dec_zero hca0
    · show Tape.CounterView' blank mark _ (g.an + (if g.ap = 0 then 1 else 0))
      rw [if_pos hz]
      simpa using Tape.counter'_inc hcb
  · have hz : g.ap ≠ 0 := fun hc => h ((probe_iff hmark hca).2 hc)
    obtain ⟨m, hm⟩ : ∃ m, g.ap = m + 1 := ⟨g.ap - 1, by omega⟩
    rw [applyActs_sDecA_pos h]
    refine ⟨⟨hb.v1, hb.v2, hb.cd, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, ?_, ?_, hcc⟩
    · show Tape.CounterView' blank mark _ (g.ap - 1)
      rw [hm]
      simpa using Tape.counter'_dec (n := m) (by rw [← hm]; exact hca)
    · show Tape.CounterView' blank mark ts.Cb (g.an + (if g.ap = 0 then 1 else 0))
      rw [if_neg hz]
      simpa using hcb

/-- **`sDecB` は `B` をちょうど 1 減らす**（符号つきの意味で）。他のテープは不変。 -/
theorem sDecB_enc (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b
      ⟨c.d - 1, c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap, g.an, g.bn + (if c.d = 0 then 1 else 0)⟩
      (applyActs blank (sDecB blank mark ts) ts) := by
  obtain ⟨hb, hca, hcb, hcc⟩ := hE
  by_cases h : probe blank ts.Cd = mark
  · have hz : c.d = 0 := (probe_iff hmark hb.cd).1 h
    have hcd0 : Tape.CounterView' blank mark ts.Cd 0 := by rw [← hz]; exact hb.cd
    have e1 : c.d - 1 = 0 := by omega
    rw [applyActs_sDecB_zero h]
    refine ⟨⟨hb.v1, hb.v2, ?_, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, hca, hcb, ?_⟩
    · show Tape.CounterView' blank mark _ (c.d - 1)
      rw [e1]
      simpa using Tape.counter'_dec_zero hcd0
    · show Tape.CounterView' blank mark _ (g.bn + (if c.d = 0 then 1 else 0))
      rw [if_pos hz]
      simpa using Tape.counter'_inc hcc
  · have hz : c.d ≠ 0 := fun hc => h ((probe_iff hmark hb.cd).2 hc)
    obtain ⟨m, hm⟩ : ∃ m, c.d = m + 1 := ⟨c.d - 1, by omega⟩
    rw [applyActs_sDecB_pos h]
    refine ⟨⟨hb.v1, hb.v2, ?_, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, hca, hcb, ?_⟩
    · show Tape.CounterView' blank mark _ (c.d - 1)
      rw [hm]
      simpa using Tape.counter'_dec (n := m) (by rw [← hm]; exact hb.cd)
    · show Tape.CounterView' blank mark ts.Cc (g.bn + (if c.d = 0 then 1 else 0))
      rw [if_neg hz]
      simpa using hcc

/-- **符号つき 1 減算は `SignedOK` を `q → q+1` へ進める**。 -/
theorem signedOK_step {k r p q : ℕ} {c : Ctr} {g : Ctr3} (hok : SignedOK k r p q c g) :
    SignedOK k r p (q + 1)
      ⟨c.d - 1, c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn + (if c.d = 0 then 1 else 0)⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hok
  refine ⟨?_, ?_, ?_, ?_⟩
  · show g.ap - 1 = r - (p + (q + 1))
    omega
  · show g.an + (if g.ap = 0 then 1 else 0) = (p + (q + 1)) - r
    split_ifs <;> omega
  · show c.d - 1 = (k - 1) * p - ((q + 1) + 1)
    omega
  · show g.bn + (if c.d = 0 then 1 else 0) = ((q + 1) + 1) - (k - 1) * p
    split_ifs <;> omega

/-! #### 符号つき 1 加算（`O(1)` 動作）と正準表現 `SgnA` / `SgnB` -/

/-- `A = ap - an` の正準表現（`ap = M ∸ N`, `an = N ∸ M`）。 -/
def SgnA (M N : ℕ) (g : Ctr3) : Prop := g.ap = M - N ∧ g.an = N - M

/-- `B = c.d - bn` の正準表現。 -/
def SgnB (M N : ℕ) (c : Ctr) (g : Ctr3) : Prop := c.d = M - N ∧ g.bn = N - M

theorem signedOK_iff (k r p q : ℕ) (c : Ctr) (g : Ctr3) :
    SignedOK k r p q c g ↔ (SgnA r (p + q) g ∧ SgnB ((k - 1) * p) (q + 1) c g) := by
  unfold SignedOK SgnA SgnB
  tauto

/-- `A` を 1 増やす：負部 `Cb` が非零ならそれを 1 減らし、零なら正部 `Ca` を 1 増やす。 -/
def sIncA (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Cb = mark then [Act.Ca blank .right]
  else [Act.Cb blank .left, Act.Cb blank .stay]

/-- `B` を 1 増やす：負部 `Cc` が非零ならそれを 1 減らし、零なら正部 `Cd` を 1 増やす。 -/
def sIncB (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  if probe blank ts.Cc = mark then [Act.Cd blank .right]
  else [Act.Cc blank .left, Act.Cc blank .stay]

theorem sIncA_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (sIncA blank mark ts).length ≤ 2 := by rw [sIncA]; split <;> simp

theorem sIncB_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (sIncB blank mark ts).length ≤ 2 := by rw [sIncB]; split <;> simp

theorem sIncA_congr (blank mark : Fin sc) {ts ts' : Tapes sc} (h : ts.Cb = ts'.Cb) :
    sIncA blank mark ts = sIncA blank mark ts' := by unfold sIncA; rw [h]

theorem sIncB_congr (blank mark : Fin sc) {ts ts' : Tapes sc} (h : ts.Cc = ts'.Cc) :
    sIncB blank mark ts = sIncB blank mark ts' := by unfold sIncB; rw [h]

/-- **`sIncA` は `A` をちょうど 1 増やす**。他のテープは不変。 -/
theorem sIncA_enc (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b c
      ⟨g.ap + (if g.an = 0 then 1 else 0), g.an - 1, g.bn⟩
      (applyActs blank (sIncA blank mark ts) ts) := by
  obtain ⟨hb, hca, hcb, hcc⟩ := hE
  by_cases h : probe blank ts.Cb = mark
  · have hz : g.an = 0 := (probe_iff hmark hcb).1 h
    have hres : applyActs blank (sIncA blank mark ts) ts =
        { ts with Ca := Tape.step blank ts.Ca blank .right } := by
      rw [sIncA, if_pos h]; rfl
    rw [hres]
    refine ⟨⟨hb.v1, hb.v2, hb.cd, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, ?_, ?_, hcc⟩
    · show Tape.CounterView' blank mark _ (g.ap + (if g.an = 0 then 1 else 0))
      rw [if_pos hz]
      simpa using Tape.counter'_inc hca
    · show Tape.CounterView' blank mark ts.Cb (g.an - 1)
      have e : g.an - 1 = g.an := by omega
      rw [e]; exact hcb
  · have hz : g.an ≠ 0 := fun hc => h ((probe_iff hmark hcb).2 hc)
    obtain ⟨m, hm⟩ : ∃ m, g.an = m + 1 := ⟨g.an - 1, by omega⟩
    have hres : applyActs blank (sIncA blank mark ts) ts =
        { ts with Cb := Tape.step blank (Tape.step blank ts.Cb blank .left) blank .stay } := by
      rw [sIncA, if_neg h]; rfl
    rw [hres]
    refine ⟨⟨hb.v1, hb.v2, hb.cd, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, ?_, ?_, hcc⟩
    · show Tape.CounterView' blank mark ts.Ca (g.ap + (if g.an = 0 then 1 else 0))
      rw [if_neg hz]
      simpa using hca
    · show Tape.CounterView' blank mark _ (g.an - 1)
      rw [hm]
      simpa using Tape.counter'_dec (n := m) (by rw [← hm]; exact hcb)

/-- **`sIncB` は `B` をちょうど 1 増やす**。他のテープは不変。 -/
theorem sIncB_enc (hmark : mark ≠ blank) {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b
      ⟨c.d + (if g.bn = 0 then 1 else 0), c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap, g.an, g.bn - 1⟩
      (applyActs blank (sIncB blank mark ts) ts) := by
  obtain ⟨hb, hca, hcb, hcc⟩ := hE
  by_cases h : probe blank ts.Cc = mark
  · have hz : g.bn = 0 := (probe_iff hmark hcc).1 h
    have hres : applyActs blank (sIncB blank mark ts) ts =
        { ts with Cd := Tape.step blank ts.Cd blank .right } := by
      rw [sIncB, if_pos h]; rfl
    rw [hres]
    refine ⟨⟨hb.v1, hb.v2, ?_, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, hca, hcb, ?_⟩
    · show Tape.CounterView' blank mark _ (c.d + (if g.bn = 0 then 1 else 0))
      rw [if_pos hz]
      simpa using Tape.counter'_inc hb.cd
    · show Tape.CounterView' blank mark ts.Cc (g.bn - 1)
      have e : g.bn - 1 = g.bn := by omega
      rw [e]; exact hcc
  · have hz : g.bn ≠ 0 := fun hcx => h ((probe_iff hmark hcc).2 hcx)
    obtain ⟨m, hm⟩ : ∃ m, g.bn = m + 1 := ⟨g.bn - 1, by omega⟩
    have hres : applyActs blank (sIncB blank mark ts) ts =
        { ts with Cc := Tape.step blank (Tape.step blank ts.Cc blank .left) blank .stay } := by
      rw [sIncB, if_neg h]; rfl
    rw [hres]
    refine ⟨⟨hb.v1, hb.v2, ?_, hb.cq, hb.ce, hb.cp, hb.cf, hb.cs, hb.cr⟩, hca, hcb, ?_⟩
    · show Tape.CounterView' blank mark ts.Cd (c.d + (if g.bn = 0 then 1 else 0))
      rw [if_neg hz]
      exact hb.cd
    · show Tape.CounterView' blank mark _ (g.bn - 1)
      rw [hm]
      simpa using Tape.counter'_dec (n := m) (by rw [← hm]; exact hcc)

/-! ##### 正準表現の上での 1 加算・1 減算 -/

theorem sgnA_inc {M N : ℕ} {g : Ctr3} (h : SgnA M N g) :
    SgnA (M + 1) N ⟨g.ap + (if g.an = 0 then 1 else 0), g.an - 1, g.bn⟩ := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · show g.ap + (if g.an = 0 then 1 else 0) = M + 1 - N
    split_ifs <;> omega
  · show g.an - 1 = N - (M + 1)
    omega

theorem sgnB_inc {M N : ℕ} {c : Ctr} {g : Ctr3} (h : SgnB M N c g) :
    SgnB (M + 1) N ⟨c.d + (if g.bn = 0 then 1 else 0), c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap, g.an, g.bn - 1⟩ := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · show c.d + (if g.bn = 0 then 1 else 0) = M + 1 - N
    split_ifs <;> omega
  · show g.bn - 1 = N - (M + 1)
    omega

theorem sgnA_dec {M N : ℕ} {g : Ctr3} (h : SgnA M N g) :
    SgnA M (N + 1) ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn⟩ := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · show g.ap - 1 = M - (N + 1)
    omega
  · show g.an + (if g.ap = 0 then 1 else 0) = N + 1 - M
    split_ifs <;> omega

theorem sgnB_dec {M N : ℕ} {c : Ctr} {g : Ctr3} (h : SgnB M N c g) :
    SgnB M (N + 1) ⟨c.d - 1, c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap, g.an, g.bn + (if c.d = 0 then 1 else 0)⟩ := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · show c.d - 1 = M - (N + 1)
    omega
  · show g.bn + (if c.d = 0 then 1 else 0) = N + 1 - M
    split_ifs <;> omega

/-! ##### `B` への `n` 回加算（`≤ 2n` 動作） -/

def sIncBLoop (blank mark : Fin sc) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      sIncB blank mark ts ++
        sIncBLoop blank mark n (applyActs blank (sIncB blank mark ts) ts)

theorem sIncBLoop_length_le (blank mark : Fin sc) :
    ∀ (n : ℕ) (ts : Tapes sc), (sIncBLoop blank mark n ts).length ≤ 2 * n := by
  intro n
  induction n with
  | zero => intro ts; simp [sIncBLoop]
  | succ n ih =>
      intro ts
      have h1 := sIncB_length_le blank mark ts
      have h2 := ih (applyActs blank (sIncB blank mark ts) ts)
      simp only [sIncBLoop, List.length_append]
      omega

theorem sIncBLoop_enc (hmark : mark ≠ blank) :
    ∀ (n M N a b : ℕ) (c : Ctr) (g : Ctr3) (ts : Tapes sc),
      EncS blank startSym endSym mark x a b c g ts → SgnB M N c g →
      ∃ (D' bn' : ℕ),
        EncS blank startSym endSym mark x a b ⟨D', c.q, c.e, c.p, c.f, c.s, c.r⟩
            ⟨g.ap, g.an, bn'⟩ (applyActs blank (sIncBLoop blank mark n ts) ts)
          ∧ SgnB (M + n) N ⟨D', c.q, c.e, c.p, c.f, c.s, c.r⟩ ⟨g.ap, g.an, bn'⟩ := by
  intro n
  induction n with
  | zero =>
      intro M N a b c g ts hE hsg
      refine ⟨c.d, g.bn, ?_, ?_⟩
      · simpa [sIncBLoop] using hE
      · simpa using hsg
  | succ n ih =>
      intro M N a b c g ts hE hsg
      have h1 := sIncB_enc (startSym := startSym) (x := x) hmark hE
      have h2 := sgnB_inc hsg
      obtain ⟨D', bn', hE', hsg'⟩ := ih (M + 1) N a b
        ⟨c.d + (if g.bn = 0 then 1 else 0), c.q, c.e, c.p, c.f, c.s, c.r⟩
        ⟨g.ap, g.an, g.bn - 1⟩ _ h1 h2
      refine ⟨D', bn', ?_, ?_⟩
      · simp only [sIncBLoop, applyActs_append]
        exact hE'
      · have e : M + 1 + n = M + (n + 1) := by omega
        rw [e] at hsg'
        exact hsg'

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
        Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr
        Ca := ts.Ca, Cb := ts.Cb, Cc := ts.Cc } := by
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
        Cd := ts.Cd, Cq := ts.Cq, Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs
        Ca := ts.Ca, Cb := ts.Cb, Cc := ts.Cc } := by
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
        Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr
        Ca := ts.Ca, Cb := ts.Cb, Cc := ts.Cc } := rfl

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

/-! ### 第 2 相用：`Cd` に触れない巻き戻し

第 2 相のあいだ `Cd` は書かれるだけで一度も読まれない（予算カウンタとして働くのは
第 1 相の `mProg` だけである）。そこで第 2 相では `Cd` を増やさない変種を使い、
`Cd` を比較ガジェット用の空きテープとして確保する。 -/

/-- `rewindUnit` から `Cd` の増加を除いたもの（4 動作）。 -/
def rewindUnit2 (blank : Fin sc) : List (Act sc) :=
  [Act.V1 .left, Act.V2 .left, Act.Cq blank .left, Act.Cq blank .stay]

def rewindLoop2 (blank : Fin sc) (k : ℕ) : ℕ → ℕ → List (Act sc)
  | 0, _ => []
  | n + 1, 0 => (rewindUnit2 blank ++ [Act.Ce blank .right]) ++ rewindLoop2 blank k n (k - 1)
  | n + 1, c + 1 => rewindUnit2 blank ++ rewindLoop2 blank k n c

theorem rewindLoop2_length (blank : Fin sc) (k : ℕ) : ∀ n c,
    (rewindLoop2 blank k n c).length = 4 * n + stays k n c := by
  intro n
  induction n with
  | zero => intro c; simp [rewindLoop2, stays]
  | succ n ih =>
      intro c
      cases c with
      | zero =>
          have h := ih (k - 1)
          simp only [rewindLoop2, stays, List.length_append, rewindUnit2, List.length_cons,
            List.length_nil, h]
          omega
      | succ c =>
          have h := ih c
          simp only [rewindLoop2, stays, List.length_append, rewindUnit2, List.length_cons,
            List.length_nil, h]
          omega

theorem applyActs_rewindUnit2 (ts : Tapes sc) :
    applyActs blank (rewindUnit2 blank) ts =
      { ts with
        V1 := Tape.step blank ts.V1 ts.V1.focus .left
        V2 := Tape.step blank ts.V2 ts.V2.focus .left
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay } := rfl

theorem rewind2_unit_enc {a b D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (a + 1) (b + 1) ⟨D, Q + 1, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
      (applyActs blank (rewindUnit2 blank) ts) := by
  rw [applyActs_rewindUnit2]
  exact ⟨pat_left hE.v1, pat_left hE.v2, hE.cd,
    by simpa using Tape.counter'_dec (n := Q) hE.cq, hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- **`Cd` に触れない巻き戻しの実現**。 -/
theorem rewind2_enc (k : ℕ) : ∀ (n c a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E + stays k n c, P, F, S, R⟩
        (applyActs blank (rewindLoop2 blank k n c) ts) := by
  intro n
  induction n with
  | zero => intro c a b D Q E P F S R ts hE; simpa [rewindLoop2, stays] using hE
  | succ n ih =>
      intro c a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1, e2, e3] at hE
        exact hE
      have hstep := rewind2_unit_enc hE'
      cases c with
      | zero =>
          have hce : Enc blank startSym endSym mark x (a + n) (b + n)
              ⟨D, Q + n, E + 1, P, F, S, R⟩
              (applyActs blank (rewindUnit2 blank ++ [Act.Ce blank .right]) ts) := by
            rw [applyActs_append]
            refine ⟨hstep.v1, hstep.v2, hstep.cd, hstep.cq, ?_, hstep.cp, hstep.cf, hstep.cs,
              hstep.cr⟩
            exact Tape.counter'_inc hstep.ce
          have := ih (k - 1) a b D Q (E + 1) P F S R _ hce
          simp only [rewindLoop2, stays, applyActs_append]
          have e5 : E + 1 + stays k n (k - 1) = E + (stays k n (k - 1) + 1) := by omega
          rw [e5] at this
          exact this
      | succ c =>
          have := ih c a b D Q E P F S R _ hstep
          simp only [rewindLoop2, stays, applyActs_append]
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
        V1 := ts.V1, Cd := ts.Cd, Cq := ts.Cq, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr
        Ca := ts.Ca, Cb := ts.Cb, Cc := ts.Cc } := rfl

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

/-- 第 2 相用の再配置（`Cd` に触れない）。 -/
def shiftPhase2 (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  (rewindLoop2 blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ++
    shiftLoop blank 1
      (eOf (applyActs blank
        (rewindLoop2 blank k (qOf ts) 0 ++
          maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ts))

/-- **第 2 相の再配置の実現**：`Cd` は不変。動作数も `shiftPhase` より小さい。 -/
theorem shiftPhase2_enc' (hk : 0 < k) (hmark : mark ≠ blank)
    {s p q D F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, 0, p, F, S, R⟩ ts)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length) :
    Enc blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
      ⟨D, 0, 0, p + shiftNoPeriod q k, F, S, R⟩
      (applyActs blank (shiftPhase2 blank mark k ts) ts)
    ∧ (shiftPhase2 blank mark k ts).length
        ≤ 4 * q + ceilDiv q k + 3 + 4 * shiftNoPeriod q k := by
  have hq : qOf ts = q := qOf_eq hE
  have hE0 : Enc blank startSym endSym mark x (s + q) ((s + p) + q)
      ⟨D, 0 + q, 0, p, F, S, R⟩ ts := by
    have e1 : 0 + q = q := by omega
    rw [e1]; exact hE
  have h1 := rewind2_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) k q 0 s (s + p) D 0 0 p F S R ts hE0
  have hst : 0 + stays k q 0 = ceilDiv q k := by rw [stays_zero k hk q]; omega
  rw [hst] at h1
  have h2 := maxOne_enc (a := s) (b := s + p) hmark h1
  have hmaxe : max 1 (ceilDiv q k) = shiftNoPeriod q k := rfl
  have h2' : Enc blank startSym endSym mark x s (s + p)
      ⟨D, 0, shiftNoPeriod q k, p, F, S, R⟩
      (applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts))
        (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) := by
    rw [hq]
    simpa [hmaxe] using h2
  have hmid : applyActs blank (rewindLoop2 blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ts =
      applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts))
        (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts) := applyActs_append _ _ _ _
  have he : eOf (applyActs blank (rewindLoop2 blank k (qOf ts) 0 ++
      maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ts)
      = shiftNoPeriod q k := by
    rw [hmid]; exact eOf_eq h2'
  have h3 : Enc blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
      ⟨D, 0, 0, p + shiftNoPeriod q k, F, S, R⟩
      (applyActs blank (shiftLoop blank 1 (shiftNoPeriod q k))
        (applyActs blank (rewindLoop2 blank k (qOf ts) 0 ++
          maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ts)) := by
    have hsl := shiftLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) 1 (shiftNoPeriod q k) s (s + p) D 0 0 p F S R
      (applyActs blank (rewindLoop2 blank k (qOf ts) 0 ++
        maxOneActs blank mark (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)) ts)
      (by rw [hmid]; rw [show (0 : ℕ) + shiftNoPeriod q k = shiftNoPeriod q k from by omega]
          exact h2') (by omega)
    simpa using hsl
  constructor
  · rw [shiftPhase2, he, applyActs_append]
    exact h3
  · rw [shiftPhase2, he]
    have hm := maxOneActs_length_le blank mark
      (applyActs blank (rewindLoop2 blank k (qOf ts) 0) ts)
    simp only [List.length_append, rewindLoop2_length, shiftLoop_length,
      stays_zero k hk (qOf ts)]
    rw [hq] at hm ⊢
    omega

/-! ### 正準表現の「減る側」更新（`N` が 1 減るときの `+1`） -/

/-- `sDecA` の動作列は `Ca` の内容にしか依存しない。 -/
theorem sDecA_congr (blank mark : Fin sc) {ts ts' : Tapes sc} (h : ts.Ca = ts'.Ca) :
    sDecA blank mark ts = sDecA blank mark ts' := by
  unfold sDecA; rw [h]

/-- `sDecB` の動作列は `Cd` の内容にしか依存しない。 -/
theorem sDecB_congr (blank mark : Fin sc) {ts ts' : Tapes sc} (h : ts.Cd = ts'.Cd) :
    sDecB blank mark ts = sDecB blank mark ts' := by
  unfold sDecB; rw [h]

/-- `sDecA` は `Cd` に触れない。 -/
theorem sDecA_Cd (blank mark : Fin sc) (ts : Tapes sc) :
    (applyActs blank (sDecA blank mark ts) ts).Cd = ts.Cd := by
  rw [sDecA]; split <;> rfl


theorem sgnA_inc' {M N : ℕ} {g : Ctr3} (h : SgnA M (N + 1) g) :
    SgnA M N ⟨g.ap + (if g.an = 0 then 1 else 0), g.an - 1, g.bn⟩ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show g.ap + (if g.an = 0 then 1 else 0) = M - N
    split_ifs <;> omega
  · show g.an - 1 = N - M
    omega

theorem sgnB_inc' {M N : ℕ} {c : Ctr} {g : Ctr3} (h : SgnB M (N + 1) c g) :
    SgnB M N ⟨c.d + (if g.bn = 0 then 1 else 0), c.q, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap, g.an, g.bn - 1⟩ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show c.d + (if g.bn = 0 then 1 else 0) = M - N
    split_ifs <;> omega
  · show g.bn - 1 = N - M
    omega

theorem maxOneActs_Ca (blank mark : Fin sc) (ts : Tapes sc) :
    (applyActs blank (maxOneActs blank mark ts) ts).Ca = ts.Ca := by
  unfold maxOneActs; split <;> rfl

theorem maxOneActs_Cb (blank mark : Fin sc) (ts : Tapes sc) :
    (applyActs blank (maxOneActs blank mark ts) ts).Cb = ts.Cb := by
  unfold maxOneActs; split <;> rfl

theorem maxOneActs_Cc (blank mark : Fin sc) (ts : Tapes sc) :
    (applyActs blank (maxOneActs blank mark ts) ts).Cc = ts.Cc := by
  unfold maxOneActs; split <;> rfl

theorem maxOneS_enc {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc} (hmark : mark ≠ blank)
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b { c with e := max 1 c.e } g
      (applyActs blank (maxOneActs blank mark ts) ts) := by
  refine ⟨maxOne_enc hmark hE.base, ?_, ?_, ?_⟩
  · rw [maxOneActs_Ca]; exact hE.ca
  · rw [maxOneActs_Cb]; exact hE.cb
  · rw [maxOneActs_Cc]; exact hE.cc
/-! ### 第 2 相用：符号つきカウンタを同時更新する巻き戻し／ずらし

第 2 相では `A = r - (p+q)`（`Ca`/`Cb`）と `B = (k-1)p - (q+1)`（`Cd`/`Cc`）を
持ち回る。外側 1 反復の再配置では

* 巻き戻し 1 単位（`q` が 1 減る）：`A` も `B` も `+1`、
* ずらし 1 単位（`p` が 1 増える）：`A` は `-1`、`B` は `+(k-1)`

なので、どちらも既存のループへ `O(1)`（`B` は `O(k)`）の動作を挿し込めばよい。
巻き戻しは `q` 歩、ずらしは `e` 単位なので、追加コストはその反復の内側走査
（`q` 歩）と `firstOuter` の仕事量に付け替えられる。 -/

/-- 巻き戻し 1 単位＋`A`,`B` をそれぞれ 1 増やす。 -/
def rewindUnit2S (blank mark : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  rewindUnit2 blank ++ (sIncA blank mark ts ++ sIncB blank mark ts)

theorem rewindUnit2S_length_le (blank mark : Fin sc) (ts : Tapes sc) :
    (rewindUnit2S blank mark ts).length ≤ 8 := by
  have h1 := sIncA_length_le blank mark ts
  have h2 := sIncB_length_le blank mark ts
  simp only [rewindUnit2S, List.length_append, rewindUnit2, List.length_cons, List.length_nil]
  omega

theorem rewindUnit2S_enc (hmark : mark ≠ blank)
    {a b D Q E P F S R M N M' N' : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (a + 1) (b + 1) ⟨D, Q + 1, E, P, F, S, R⟩ g ts)
    (hA : SgnA M (N + 1) g) (hB : SgnB M' (N' + 1) ⟨D, Q + 1, E, P, F, S, R⟩ g) :
    ∃ (D' ap' an' bn' : ℕ),
      EncS blank startSym endSym mark x a b ⟨D', Q, E, P, F, S, R⟩ ⟨ap', an', bn'⟩
          (applyActs blank (rewindUnit2S blank mark ts) ts)
        ∧ SgnA M N ⟨ap', an', bn'⟩
        ∧ SgnB M' N' ⟨D', Q, E, P, F, S, R⟩ ⟨ap', an', bn'⟩ := by
  obtain ⟨hb, hca, hcb, hcc⟩ := hE
  have h0 : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g
      (applyActs blank (rewindUnit2 blank) ts) := by
    refine ⟨rewind2_unit_enc hb, ?_, ?_, ?_⟩ <;> rw [applyActs_rewindUnit2]
    · exact hca
    · exact hcb
    · exact hcc
  have hCb : ts.Cb = (applyActs blank (rewindUnit2 blank) ts).Cb := by
    rw [applyActs_rewindUnit2]
  have h1 := sIncA_enc (startSym := startSym) (x := x) hmark h0
  have hCc : ts.Cc
      = (applyActs blank (sIncA blank mark (applyActs blank (rewindUnit2 blank) ts))
          (applyActs blank (rewindUnit2 blank) ts)).Cc := by
    rw [sIncA, applyActs_rewindUnit2]
    split <;> rfl
  have h2 := sIncB_enc (startSym := startSym) (x := x) hmark h1
  refine ⟨D + (if g.bn = 0 then 1 else 0), g.ap + (if g.an = 0 then 1 else 0),
    g.an - 1, g.bn - 1, ?_, ?_, ?_⟩
  · rw [rewindUnit2S, applyActs_append, applyActs_append,
      sIncA_congr blank mark hCb, sIncB_congr blank mark hCc]
    exact h2
  · exact sgnA_inc' hA
  · exact sgnB_inc' hB

/-- 巻き戻しループ（符号つき更新つき）。 -/
def rewindLoop2S (blank mark : Fin sc) (k : ℕ) : ℕ → ℕ → Tapes sc → List (Act sc)
  | 0, _, _ => []
  | n + 1, 0, ts =>
      (rewindUnit2S blank mark ts ++ [Act.Ce blank .right]) ++
        rewindLoop2S blank mark k n (k - 1)
          (applyActs blank (rewindUnit2S blank mark ts ++ [Act.Ce blank .right]) ts)
  | n + 1, c + 1, ts =>
      rewindUnit2S blank mark ts ++
        rewindLoop2S blank mark k n c (applyActs blank (rewindUnit2S blank mark ts) ts)

theorem rewindLoop2S_length_le (blank mark : Fin sc) (k : ℕ) :
    ∀ (n c : ℕ) (ts : Tapes sc), (rewindLoop2S blank mark k n c ts).length ≤ 9 * n := by
  intro n
  induction n with
  | zero => intro c ts; simp [rewindLoop2S]
  | succ n ih =>
      intro c ts
      cases c with
      | zero =>
          have h1 := rewindUnit2S_length_le blank mark ts
          have h2 := ih (k - 1)
            (applyActs blank (rewindUnit2S blank mark ts ++ [Act.Ce blank .right]) ts)
          simp only [rewindLoop2S, List.length_append, List.length_cons, List.length_nil]
          omega
      | succ c =>
          have h1 := rewindUnit2S_length_le blank mark ts
          have h2 := ih c (applyActs blank (rewindUnit2S blank mark ts) ts)
          simp only [rewindLoop2S, List.length_append]
          omega

/-- **符号つき巻き戻しの実現**：`q` を `n` 歩戻しつつ `A`,`B` をそれぞれ `n` 増やす。
`Ce` には `stays k n c` が積まれる。 -/
theorem rewindLoop2S_enc (hmark : mark ≠ blank) (k : ℕ) :
    ∀ (n c a b D Q E P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc),
      EncS blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ g ts →
      SgnA M (N + n) g → SgnB M' (N' + n) ⟨D, Q + n, E, P, F, S, R⟩ g →
      ∃ (D' ap' an' bn' : ℕ),
        EncS blank startSym endSym mark x a b
            ⟨D', Q, E + stays k n c, P, F, S, R⟩ ⟨ap', an', bn'⟩
            (applyActs blank (rewindLoop2S blank mark k n c ts) ts)
          ∧ SgnA M N ⟨ap', an', bn'⟩
          ∧ SgnB M' N' ⟨D', Q, E + stays k n c, P, F, S, R⟩ ⟨ap', an', bn'⟩ := by
  intro n
  induction n with
  | zero =>
      intro c a b D Q E P F S R M N M' N' g ts hE hA hB
      exact ⟨D, g.ap, g.an, g.bn, by simpa [rewindLoop2S, stays] using hE,
        by simpa using hA, by simpa [stays] using hB⟩
  | succ n ih =>
      intro c a b D Q E P F S R M N M' N' g ts hE hA hB
      have hE' : EncS blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1, e2, e3] at hE
        exact hE
      have hA' : SgnA M ((N + n) + 1) g := by
        have e : N + (n + 1) = (N + n) + 1 := by omega
        rw [e] at hA; exact hA
      have hB' : SgnB M' ((N' + n) + 1) ⟨D, (Q + n) + 1, E, P, F, S, R⟩ g := by
        have e : N' + (n + 1) = (N' + n) + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e, e3] at hB; exact hB
      obtain ⟨D1, ap1, an1, bn1, hE1, hA1, hB1⟩ :=
        rewindUnit2S_enc (startSym := startSym) (x := x) hmark hE' hA' hB'
      cases c with
      | zero =>
          have hce : EncS blank startSym endSym mark x (a + n) (b + n)
              ⟨D1, Q + n, E + 1, P, F, S, R⟩ ⟨ap1, an1, bn1⟩
              (applyActs blank (rewindUnit2S blank mark ts ++ [Act.Ce blank .right]) ts) := by
            rw [applyActs_append]
            obtain ⟨hbb, h1, h2, h3⟩ := hE1
            exact ⟨⟨hbb.v1, hbb.v2, hbb.cd, hbb.cq, Tape.counter'_inc hbb.ce, hbb.cp,
              hbb.cf, hbb.cs, hbb.cr⟩, h1, h2, h3⟩
          obtain ⟨D2, ap2, an2, bn2, hE2, hA2, hB2⟩ := ih (k - 1) a b D1 Q (E + 1) P F S R
            M N M' N' ⟨ap1, an1, bn1⟩ _ hce hA1 hB1
          have e5 : E + 1 + stays k n (k - 1) = E + (stays k n (k - 1) + 1) := by omega
          rw [e5] at hE2 hB2
          refine ⟨D2, ap2, an2, bn2, ?_, hA2, ?_⟩
          · rw [rewindLoop2S, applyActs_append]
            simp only [stays]
            exact hE2
          · simp only [stays]
            exact hB2
      | succ c =>
          obtain ⟨D2, ap2, an2, bn2, hE2, hA2, hB2⟩ := ih c a b D1 Q E P F S R
            M N M' N' ⟨ap1, an1, bn1⟩ _ hE1 hA1 hB1
          refine ⟨D2, ap2, an2, bn2, ?_, hA2, ?_⟩
          · rw [rewindLoop2S, applyActs_append]
            simp only [stays]
            exact hE2
          · simp only [stays]
            exact hB2

/-! #### 符号つきずらし -/

/-- ずらし 1 単位＋`A` を 1 減らし `B` を `k-1` 増やす。 -/
def shiftUnitS (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  (shiftHead blank ++ sDecA blank mark ts) ++
    sIncBLoop blank mark (k - 1)
      (applyActs blank (shiftHead blank ++ sDecA blank mark ts) ts)

theorem shiftUnitS_length_le (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) :
    (shiftUnitS blank mark k ts).length ≤ 2 * k + 7 := by
  have h1 := sDecA_length_le blank mark ts
  have h2 := sIncBLoop_length_le blank mark (k - 1)
    (applyActs blank (shiftHead blank ++ sDecA blank mark ts) ts)
  have h3 : (shiftHead blank : List (Act sc)).length = 4 := rfl
  rw [shiftUnitS, List.length_append, List.length_append, h3]
  omega

theorem shiftUnitS_enc (hmark : mark ≠ blank) (k : ℕ)
    {a b D Q E P F S R M N M' N' : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩ g ts)
    (hb : b < x.length)
    (hA : SgnA M N g) (hB : SgnB M' N' ⟨D, Q, E + 1, P, F, S, R⟩ g) :
    ∃ (D' ap' an' bn' : ℕ),
      EncS blank startSym endSym mark x a (b + 1) ⟨D', Q, E, P + 1, F, S, R⟩
          ⟨ap', an', bn'⟩ (applyActs blank (shiftUnitS blank mark k ts) ts)
        ∧ SgnA M (N + 1) ⟨ap', an', bn'⟩
        ∧ SgnB (M' + (k - 1)) N' ⟨D', Q, E, P + 1, F, S, R⟩ ⟨ap', an', bn'⟩ := by
  obtain ⟨hbse, hca, hcb, hcc⟩ := hE
  have hhead : EncS blank startSym endSym mark x a (b + 1) ⟨D, Q, E, P + 1, F, S, R⟩ g
      (applyActs blank (shiftHead blank) ts) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [applyActs_shiftHead]
    · exact ⟨hbse.v1, pat_right hbse.v2 hb, hbse.cd, hbse.cq,
        by simpa using Tape.counter'_dec (n := E) hbse.ce, Tape.counter'_inc hbse.cp,
        hbse.cf, hbse.cs, hbse.cr⟩
    · exact hca
    · exact hcb
    · exact hcc
  have hCa : ts.Ca = (applyActs blank (shiftHead blank) ts).Ca := by rw [applyActs_shiftHead]
  have hdec := sDecA_enc (startSym := startSym) (x := x) hmark hhead
  have hpre : applyActs blank (shiftHead blank ++ sDecA blank mark ts) ts
      = applyActs blank (sDecA blank mark (applyActs blank (shiftHead blank) ts))
          (applyActs blank (shiftHead blank) ts) := by
    rw [applyActs_append, sDecA_congr blank mark hCa]
  obtain ⟨D2, bn2, hE2, hB2⟩ := sIncBLoop_enc (startSym := startSym) (x := x) hmark (k - 1)
    M' N' a (b + 1) ⟨D, Q, E, P + 1, F, S, R⟩
    ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn⟩ _ hdec hB
  refine ⟨D2, g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), bn2, ?_, sgnA_dec hA, hB2⟩
  rw [shiftUnitS, applyActs_append, hpre]
  exact hE2

def shiftLoopS (blank mark : Fin sc) (k : ℕ) : ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | n + 1, ts =>
      shiftUnitS blank mark k ts ++
        shiftLoopS blank mark k n (applyActs blank (shiftUnitS blank mark k ts) ts)

theorem shiftLoopS_length_le (blank mark : Fin sc) (k : ℕ) :
    ∀ (n : ℕ) (ts : Tapes sc), (shiftLoopS blank mark k n ts).length ≤ (2 * k + 7) * n := by
  intro n
  induction n with
  | zero => intro ts; simp [shiftLoopS]
  | succ n ih =>
      intro ts
      have h1 := shiftUnitS_length_le blank mark k ts
      have h2 := ih (applyActs blank (shiftUnitS blank mark k ts) ts)
      have e : (2 * k + 7) * (n + 1) = (2 * k + 7) + (2 * k + 7) * n := by ring
      simp only [shiftLoopS, List.length_append]
      omega

/-- **符号つきずらしの実現**：`n` 単位で `p` が `n` 増え、`A` は `n` 減り、
`B` は `(k-1)*n` 増える。 -/
theorem shiftLoopS_enc (hmark : mark ≠ blank) (k : ℕ) :
    ∀ (n a b D Q E P F S R M N M' N' : ℕ) (g : Ctr3) (ts : Tapes sc),
      EncS blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ g ts → b + n ≤ x.length →
      SgnA M N g → SgnB M' N' ⟨D, Q, E + n, P, F, S, R⟩ g →
      ∃ (D' ap' an' bn' : ℕ),
        EncS blank startSym endSym mark x a (b + n) ⟨D', Q, E, P + n, F, S, R⟩
            ⟨ap', an', bn'⟩ (applyActs blank (shiftLoopS blank mark k n ts) ts)
          ∧ SgnA M (N + n) ⟨ap', an', bn'⟩
          ∧ SgnB (M' + (k - 1) * n) N' ⟨D', Q, E, P + n, F, S, R⟩ ⟨ap', an', bn'⟩ := by
  intro n
  induction n with
  | zero =>
      intro a b D Q E P F S R M N M' N' g ts hE _ hA hB
      exact ⟨D, g.ap, g.an, g.bn, by simpa [shiftLoopS] using hE, by simpa using hA,
        by simpa using hB⟩
  | succ n ih =>
      intro a b D Q E P F S R M N M' N' g ts hE hle hA hB
      have hE' : EncS blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ g ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hB' : SgnB M' N' ⟨D, Q, (E + n) + 1, P, F, S, R⟩ g := hB
      obtain ⟨D1, ap1, an1, bn1, hE1, hA1, hB1⟩ :=
        shiftUnitS_enc (startSym := startSym) (x := x) hmark k hE' (by omega) hA hB'
      obtain ⟨D2, ap2, an2, bn2, hE2, hA2, hB2⟩ := ih a (b + 1) D1 Q E (P + 1) F S R
        M (N + 1) (M' + (k - 1)) N' ⟨ap1, an1, bn1⟩ _ hE1 (by omega) hA1 hB1
      have e1 : b + 1 + n = b + (n + 1) := by omega
      have e3 : P + 1 + n = P + (n + 1) := by omega
      have e4 : N + 1 + n = N + (n + 1) := by omega
      have e5 : M' + (k - 1) + (k - 1) * n = M' + (k - 1) * (n + 1) := by ring
      rw [e1, e3] at hE2
      rw [e4] at hA2
      rw [e3, e5] at hB2
      refine ⟨D2, ap2, an2, bn2, ?_, hA2, hB2⟩
      simp only [shiftLoopS, applyActs_append]
      exact hE2

/-! #### 第 2 相の符号つき再配置 `shiftPhase2S` -/

/-- 第 2 相用の再配置（`A`/`B` を同時更新する）。 -/
def shiftPhase2S (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) : List (Act sc) :=
  (rewindLoop2S blank mark k (qOf ts) 0 ts ++
      maxOneActs blank mark (applyActs blank (rewindLoop2S blank mark k (qOf ts) 0 ts) ts)) ++
    shiftLoopS blank mark k
      (eOf (applyActs blank
        (rewindLoop2S blank mark k (qOf ts) 0 ts ++
          maxOneActs blank mark
            (applyActs blank (rewindLoop2S blank mark k (qOf ts) 0 ts) ts)) ts))
      (applyActs blank
        (rewindLoop2S blank mark k (qOf ts) 0 ts ++
          maxOneActs blank mark
            (applyActs blank (rewindLoop2S blank mark k (qOf ts) 0 ts) ts)) ts)

/-- **第 2 相の符号つき再配置の実現**：`q = 0`、`p := p + shiftNoPeriod q k` へ移り、
`A = r - (p+q)` と `B = (k-1)p - (q+1)` が新しい `p`, `q` に対して正しく更新される。 -/
theorem shiftPhase2S_enc' (hk : 0 < k) (hmark : mark ≠ blank)
    {s p q D F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, 0, p, F, S, R⟩ g ts)
    (hfit : s + p + shiftNoPeriod q k ≤ x.length)
    (hA : SgnA r (p + q) g)
    (hB : SgnB ((k - 1) * p) (q + 1) ⟨D, q, 0, p, F, S, R⟩ g) :
    (∃ (D' ap' an' bn' : ℕ),
        EncS blank startSym endSym mark x s (s + p + shiftNoPeriod q k)
            ⟨D', 0, 0, p + shiftNoPeriod q k, F, S, R⟩ ⟨ap', an', bn'⟩
            (applyActs blank (shiftPhase2S blank mark k ts) ts)
          ∧ SgnA r (p + shiftNoPeriod q k) ⟨ap', an', bn'⟩
          ∧ SgnB ((k - 1) * (p + shiftNoPeriod q k)) 1
              ⟨D', 0, 0, p + shiftNoPeriod q k, F, S, R⟩ ⟨ap', an', bn'⟩)
      ∧ (shiftPhase2S blank mark k ts).length
          ≤ 9 * q + 3 + (2 * k + 7) * shiftNoPeriod q k := by
  have hq : qOf ts = q := qOf_eq hE.base
  have hE0 : EncS blank startSym endSym mark x (s + q) ((s + p) + q)
      ⟨D, 0 + q, 0, p, F, S, R⟩ g ts := by
    have e1 : 0 + q = q := by omega
    rw [e1]; exact hE
  have hB0 : SgnB ((k - 1) * p) (1 + q) ⟨D, 0 + q, 0, p, F, S, R⟩ g := by
    have e1 : 1 + q = q + 1 := by omega
    rw [e1]; exact hB
  obtain ⟨D1, ap1, an1, bn1, hE1, hA1, hB1⟩ :=
    rewindLoop2S_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) hmark k q 0 s (s + p) D 0 0 p F S R
      r p ((k - 1) * p) 1 g ts hE0 hA hB0
  have hst : (0 : ℕ) + stays k q 0 = ceilDiv q k := by rw [stays_zero k hk q]; omega
  rw [hst] at hE1 hB1
  have h2 := maxOneS_enc (a := s) (b := s + p) hmark hE1
  have hmaxe : max 1 (ceilDiv q k) = shiftNoPeriod q k := rfl
  have hRW : rewindLoop2S blank mark k (qOf ts) 0 ts = rewindLoop2S blank mark k q 0 ts := by
    rw [hq]
  have h2' : EncS blank startSym endSym mark x s (s + p)
      ⟨D1, 0, shiftNoPeriod q k, p, F, S, R⟩ ⟨ap1, an1, bn1⟩
      (applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts))
        (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)) := by
    simpa [hmaxe] using h2
  have hmid : applyActs blank (rewindLoop2S blank mark k q 0 ts ++
      maxOneActs blank mark (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)) ts =
      applyActs blank (maxOneActs blank mark
        (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts))
        (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts) := applyActs_append _ _ _ _
  have he : eOf (applyActs blank (rewindLoop2S blank mark k q 0 ts ++
      maxOneActs blank mark (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)) ts)
      = shiftNoPeriod q k := by
    rw [hmid]; exact eOf_eq h2'.base
  have hB1' : SgnB ((k - 1) * p) 1 ⟨D1, 0, shiftNoPeriod q k, p, F, S, R⟩ ⟨ap1, an1, bn1⟩ :=
    hB1
  obtain ⟨D2, ap2, an2, bn2, hE2, hA2, hB2⟩ :=
    shiftLoopS_enc (blank := blank) (startSym := startSym) (endSym := endSym)
      (mark := mark) (x := x) hmark k (shiftNoPeriod q k) s (s + p) D1 0 0 p F S R
      r p ((k - 1) * p) 1 ⟨ap1, an1, bn1⟩
      (applyActs blank (rewindLoop2S blank mark k q 0 ts ++
        maxOneActs blank mark (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)) ts)
      (by rw [hmid]
          have e0 : (0 : ℕ) + shiftNoPeriod q k = shiftNoPeriod q k := by omega
          rw [e0]
          exact h2')
      (by omega) hA1 hB1'
  have hmulB : (k - 1) * p + (k - 1) * shiftNoPeriod q k
      = (k - 1) * (p + shiftNoPeriod q k) := by ring
  rw [hmulB] at hB2
  constructor
  · refine ⟨D2, ap2, an2, bn2, ?_, hA2, hB2⟩
    rw [shiftPhase2S, hq, he, applyActs_append]
    exact hE2
  · rw [shiftPhase2S, hq, he]
    have hm := maxOneActs_length_le blank mark
      (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)
    have hr := rewindLoop2S_length_le blank mark k q 0 ts
    have hs2 := shiftLoopS_length_le blank mark k (shiftNoPeriod q k)
      (applyActs blank (rewindLoop2S blank mark k q 0 ts ++
        maxOneActs blank mark (applyActs blank (rewindLoop2S blank mark k q 0 ts) ts)) ts)
    simp only [List.length_append]
    omega

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
    {s bound Fi F S R : ℕ} {orcB : Tapes sc → Bool} (hs : s ≤ x.length)
    (hFi : (x.drop s).length + 1 ≤ Fi)
    (horcB : ∀ (p' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', F, S, R⟩ ts' →
      (orcB ts' = true ↔ p' < bound)) :
    ∀ (fuel p : ℕ) (ts : Tapes sc), 0 < p → s + p ≤ x.length →
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
              P ≤ p + firstOuterWork (x.drop s) k bound fuel p ∧
              Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, S, R⟩
                (applyActs blank
                  (oProg blank endSym mark orcB k Fi fuel ts) ts))) := by
  have hdroplen : (x.drop s).length = x.length - s := by simp
  intro fuel
  induction fuel with
  | zero =>
      intro p ts hp hsp hE
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [oProg, firstOuterWork]; simp
      · intro p' m hc; rw [firstOuter] at hc; simp at hc
      · refine ⟨s, s + p, (k - 1) * p, 0, 0, p, ?_⟩
        rw [oProg, applyActs_nil]
        exact hE
      · intro _
        refine ⟨p, hp, hsp, by rw [firstOuterWork]; omega, ?_⟩
        rw [oProg, applyActs_nil]
        exact hE
  | succ fuel ih =>
      intro p ts hp hsp hE
      have hgiff : oCondB endSym orcB ts ↔ (p < (x.drop s).length ∧ p < bound) := by
        have h1 : Tape.read ts.V2 = endSym ↔ s + p = x.length := read_pat_end_iff hend hE.v2
        have h2 : orcB ts = true ↔ p < bound := horcB p ts hE
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
              ((x.drop s).length + 1) 0) k) _
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
            obtain ⟨P, hP1, hP2, hP4, hP3⟩ := hrec.2.2.2 hc
            refine ⟨P, hP1, hP2, ?_, by rw [happ]; exact hP3⟩
            rw [firstOuterWork, if_pos hg, if_neg hqne]
            have hsn := shiftNoPeriod_le_succ (k := k) (by omega)
              (firstInner (x.drop s) k p ((x.drop s).length + 1) 0)
            omega
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
          refine ⟨p, hp, hsp, by rw [firstOuterWork, if_neg hng]; omega, ?_⟩
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
    (horcB : ∀ (p' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', F, S, R⟩ ts' →
      (orcB ts' = true ↔ p' < bound))
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
            P ≤ 1 + firstOuterWork (x.drop s) k bound Fo 1 ∧
            Enc blank startSym endSym mark x s (s + P) ⟨(k - 1) * P, 0, 0, P, F, S, R⟩
              (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts))) := by
  have hsle : s ≤ x.length := le_of_lt hs
  have hinit := initActs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) hs hE
  have hinit' : Enc blank startSym endSym mark x s (s + 1) ⟨(k - 1) * 1, 0, 0, 1, F, S, R⟩
      (applyActs blank (initActs blank k) ts) := hinit
  obtain ⟨hcost, hsome, hex, hnone⟩ := oProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) (Fi := n + 1) (F := F) (S := S)
    (R := R) hk hend hmark hsle
    (by omega) horcB Fo 1 (applyActs blank (initActs blank k) ts)
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
    obtain ⟨P, hP1, hP2, hP4, hP3⟩ := hnone hc
    exact ⟨P, hP1, hP2, hP4, by rw [happ]; exact hP3⟩

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
    (horcB : ∀ (p' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', F, S, 0⟩ ts' →
      (orcB ts' = true ↔ p' < bound))
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

/-- 内側 1 反復の基本動作（`V1`/`V2` を 1 セル右へ、`Cq` を 1 増やす）。 -/
def sBase (blank : Fin sc) : List (Act sc) :=
  [Act.V1 .right, Act.V2 .right, Act.Cq blank .right]

@[simp] theorem sBase_length (blank : Fin sc) : (sBase blank).length = 3 := rfl

theorem applyActs_sBase (blank : Fin sc) (ts : Tapes sc) :
    applyActs blank (sBase blank) ts =
      { V1 := Tape.step blank ts.V1 ts.V1.focus .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .right
        Cq := Tape.step blank ts.Cq blank .right
        Cd := ts.Cd, Ce := ts.Ce, Cp := ts.Cp, Cf := ts.Cf, Cs := ts.Cs, Cr := ts.Cr
        Ca := ts.Ca, Cb := ts.Cb, Cc := ts.Cc } := rfl

/-- 1 反復の動作列（継続なら基本 3 動作＋符号つき減算 2 本で高々 9 動作、停止なら 0）。 -/
def sActs (blank endSym mark : Fin sc) (orc : Tapes sc → Bool) (ts : Tapes sc) :
    List (Act sc) :=
  if sCond endSym orc ts then
    sBase blank ++ (sDecA blank mark ts ++ sDecB blank mark ts)
  else []

theorem sActs_length_le (blank endSym mark : Fin sc) (orc : Tapes sc → Bool)
    (ts : Tapes sc) : (sActs blank endSym mark orc ts).length ≤ 9 := by
  rw [sActs]
  split
  · have h1 := sDecA_length_le blank mark ts
    have h2 := sDecB_length_le blank mark ts
    simp only [List.length_append, sBase_length]
    omega
  · simp

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

theorem enc_s_base (hend : endSym ∉ x)
    (hE : Enc blank startSym endSym mark x a b c ts) (hab : a ≤ b)
    (h : sCond endSym orc ts) :
    Enc blank startSym endSym mark x (a + 1) (b + 1) { c with q := c.q + 1 }
      (applyActs blank (sBase blank) ts) := by
  obtain ⟨hb, _, _⟩ := (sCond_iff (orc := orc) hend hE hab).1 h
  have hale : a < x.length := lt_of_le_of_lt hab hb
  rw [applyActs_sBase]
  exact ⟨pat_right hE.v1 hale, pat_right hE.v2 hb, hE.cd, Tape.counter'_inc hE.cq,
    hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

/-- **符号つきカウンタ込みの内側 1 反復**：`A` と `B` がそれぞれちょうど 1 減る。 -/
theorem encS_s_step (hend : endSym ∉ x) (hmark : mark ≠ blank) {g : Ctr3}
    (hE : EncS blank startSym endSym mark x a b c g ts) (hab : a ≤ b)
    (h : sCond endSym orc ts) :
    EncS blank startSym endSym mark x (a + 1) (b + 1)
      ⟨c.d - 1, c.q + 1, c.e, c.p, c.f, c.s, c.r⟩
      ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn + (if c.d = 0 then 1 else 0)⟩
      (applyActs blank (sActs blank endSym mark orc ts) ts) := by
  have hbase : EncS blank startSym endSym mark x (a + 1) (b + 1)
      { c with q := c.q + 1 } g (applyActs blank (sBase blank) ts) := by
    refine ⟨enc_s_base (orc := orc) hend hE.base hab h, ?_, ?_, ?_⟩
    · rw [applyActs_sBase]; exact hE.ca
    · rw [applyActs_sBase]; exact hE.cb
    · rw [applyActs_sBase]; exact hE.cc
  rw [sActs, if_pos h, applyActs_append, applyActs_append]
  rw [sDecA_congr blank mark
    (show ts.Ca = (applyActs blank (sBase blank) ts).Ca by rw [applyActs_sBase])]
  rw [sDecB_congr blank mark
    (show ts.Cd = (applyActs blank (sDecA blank mark (applyActs blank (sBase blank) ts))
        (applyActs blank (sBase blank) ts)).Cd by rw [sDecA_Cd, applyActs_sBase])]
  exact sDecB_enc (startSym := startSym) (x := x) hmark
    (sDecA_enc (startSym := startSym) (x := x) hmark hbase)

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
def sProg (blank endSym mark : Fin sc) (orc : Tapes sc → Bool) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if sCond endSym orc ts then
        sActs blank endSym mark orc ts ++
          sProg blank endSym mark orc fuel
            (applyActs blank (sActs blank endSym mark orc ts) ts)
      else []

/-- **主定理（`_second_period` 内側ループの実現とコスト）**。
符号つきカウンタ `A = r - (p+q)`（正部 `Ca`／負部 `Cb`）と `B = (k-1)p - (q+1)`
（正部 `Cd`／負部 `Cc`）を持ち回り、1 ステップにつき両方を `O(1)` 動作で 1 ずつ
減らす。中断オラクル `orc` は `SignedOK` を満たす状態の上で中断条件と一致すれば
よく、`orcAB`（`Ca` と `Cd` の probe 2 回）がその実装である。 -/
theorem sProg_spec (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q')
          ⟨D', q', E', p', F', S', r⟩ g' ts' →
      SignedOK k r p' q' ⟨D', q', E', p', F', S', r⟩ g' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1)) :
    ∀ (fuel q D E p F S : ℕ) (g : Ctr3) (ts : Tapes sc),
      EncS blank startSym endSym mark x (s + q) (s + p + q)
          ⟨D, q, E, p, F, S, r⟩ g ts →
      SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g →
        ((∃ D' g',
            EncS blank startSym endSym mark x (s + q + sSteps x k p r s fuel q)
                (s + p + q + sSteps x k p r s fuel q)
                ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g'
                (applyActs blank (sProg blank endSym mark orc fuel ts) ts)
              ∧ SignedOK k r p (q + sSteps x k p r s fuel q)
                  ⟨D', q + sSteps x k p r s fuel q, E, p, F, S, r⟩ g')
          ∧ (sProg blank endSym mark orc fuel ts).length
              ≤ 9 * sWork x k p r s fuel q) := by
  intro fuel
  induction fuel with
  | zero =>
      intro q D E p F S g ts hE hok
      refine ⟨⟨D, g, ?_, ?_⟩, by simp [sProg, sWork]⟩
      · simpa [sSteps, sProg] using hE
      · simpa [sSteps] using hok
  | succ fuel ih =>
      intro q D E p F S g ts hE hok
      have hab : s + q ≤ s + p + q := by omega
      have horcq : orc ts = decide (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
        rw [horc q D E p F S g ts hE hok, Nat.add_assoc]
      by_cases h : sCond endSym orc ts
      · obtain ⟨hb, hm, ho⟩ := (sCond_iff hend hE.base hab).1 h
        have hnab : ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
          rw [horcq] at ho
          exact of_decide_eq_false ho
        have hcond : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
            ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := ⟨hb, hm, hnab⟩
        have hstep := encS_s_step (orc := orc) hend hmark hE hab h
        have hokstep := signedOK_step (c := (⟨D, q, E, p, F, S, r⟩ : Ctr)) (g := g) hok
        have hrec := ih (q + 1) (D - 1) E p F S
          ⟨g.ap - 1, g.an + (if g.ap = 0 then 1 else 0), g.bn + (if D = 0 then 1 else 0)⟩
          (applyActs blank (sActs blank endSym mark orc ts) ts)
          (by
            have e1 : s + q + 1 = s + (q + 1) := by omega
            have e2 : s + p + q + 1 = s + p + (q + 1) := by omega
            rw [e1, e2] at hstep
            exact hstep)
          hokstep
        obtain ⟨⟨D2, g2, hEnc2, hok2⟩, hlen2⟩ := hrec
        have e3 : q + (1 + sSteps x k p r s fuel (q + 1))
            = q + 1 + sSteps x k p r s fuel (q + 1) := by omega
        refine ⟨⟨D2, g2, ?_, ?_⟩, ?_⟩
        · simp only [sSteps, if_pos hcond, sProg, if_pos h, applyActs_append]
          have e1 : s + q + (1 + sSteps x k p r s fuel (q + 1))
              = s + (q + 1) + sSteps x k p r s fuel (q + 1) := by omega
          have e2 : s + p + q + (1 + sSteps x k p r s fuel (q + 1))
              = s + p + (q + 1) + sSteps x k p r s fuel (q + 1) := by omega
          rw [e1, e2, e3]
          exact hEnc2
        · simp only [sSteps, if_pos hcond]
          rw [e3]
          exact hok2
        · have hbm : s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? := ⟨hb, hm⟩
          have hA := sActs_length_le blank endSym mark orc ts
          simp only [sProg, if_pos h, sWork, if_pos hbm, if_neg hnab, List.length_append]
          omega
      · have hg : ¬ (s + p + q < x.length ∧ x[s + q]? = x[s + p + q]? ∧
            ¬ (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1)) := by
          intro hc
          refine h ((sCond_iff hend hE.base hab).2 ⟨hc.1, hc.2.1, ?_⟩)
          rw [horcq]
          exact decide_eq_false hc.2.2
        refine ⟨⟨D, g, ?_, ?_⟩, ?_⟩
        · simp only [sSteps, if_neg hg, sProg, if_neg h]
          simpa using hE
        · simp only [sSteps, if_neg hg]
          simpa using hok
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
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x (s + q') (s + p' + q') ⟨D', q', E', p', F', S', r⟩ ts' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1))
    {q D E p F S : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, E, p, F, S, r⟩ ts) :
    sAbort endSym orc ts ↔ AbortAt x k p r s q := by
  have hab : s + q ≤ s + p + q := by omega
  have hble : s + p + q ≤ x.length := pat_le hE.v2
  have horcq : orc ts = decide (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
    rw [horc q D E p F S ts hE, Nat.add_assoc]
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

/-! #### 第 2 相の符号つき周期ずらし -/

theorem perLoop1_ctr3 (blank : Fin sc) : ∀ (n : ℕ) (ts : Tapes sc),
    (applyActs blank (perLoop1 blank n) ts).Ca = ts.Ca
      ∧ (applyActs blank (perLoop1 blank n) ts).Cb = ts.Cb
      ∧ (applyActs blank (perLoop1 blank n) ts).Cc = ts.Cc := by
  intro n
  induction n with
  | zero => intro ts; simp [perLoop1]
  | succ n ih =>
      intro ts
      obtain ⟨h1, h2, h3⟩ := ih (applyActs blank (perUnit blank) ts)
      rw [perLoop1, applyActs_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [h1, applyActs_perUnit]
      · rw [h2, applyActs_perUnit]
      · rw [h3, applyActs_perUnit]

theorem cfLoop_ctr3 (blank : Fin sc) : ∀ (n : ℕ) (ts : Tapes sc),
    (applyActs blank (cfLoop blank n) ts).Ca = ts.Ca
      ∧ (applyActs blank (cfLoop blank n) ts).Cb = ts.Cb
      ∧ (applyActs blank (cfLoop blank n) ts).Cc = ts.Cc := by
  intro n
  induction n with
  | zero => intro ts; simp [cfLoop]
  | succ n ih =>
      intro ts
      obtain ⟨h1, h2, h3⟩ := ih (applyActs blank [Act.Ce blank .left, Act.Ce blank .stay,
        Act.Cf (sc := sc) blank .right] ts)
      have hres : applyActs blank [Act.Ce blank .left, Act.Ce blank .stay,
          Act.Cf (sc := sc) blank .right] ts =
          { ts with
            Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay
            Cf := Tape.step blank ts.Cf blank .right } := rfl
      rw [cfLoop, applyActs_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [h1, hres]
      · rw [h2, hres]
      · rw [h3, hres]

theorem periodShift_ctr3 (blank : Fin sc) (n : ℕ) (ts : Tapes sc) :
    (applyActs blank (periodShift blank n) ts).Ca = ts.Ca
      ∧ (applyActs blank (periodShift blank n) ts).Cb = ts.Cb
      ∧ (applyActs blank (periodShift blank n) ts).Cc = ts.Cc := by
  obtain ⟨h1, h2, h3⟩ := cfLoop_ctr3 blank n (applyActs blank (perLoop1 blank n) ts)
  obtain ⟨e1, e2, e3⟩ := perLoop1_ctr3 blank n ts
  rw [periodShift, applyActs_append]
  exact ⟨h1.trans e1, h2.trans e2, h3.trans e3⟩

theorem periodShiftS_pre {n a b D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E, P + n, F + n, S, R⟩ g
      (applyActs blank (periodShift blank n) ts) := by
  obtain ⟨h1, h2, h3⟩ := periodShift_ctr3 blank n ts
  refine ⟨periodShift_enc hE.base, ?_, ?_, ?_⟩
  · rw [h1]; exact hE.ca
  · rw [h2]; exact hE.cb
  · rw [h3]; exact hE.cc

/-- 周期ずらし＋`B` への `k*n` 加算（`A` は不変）。 -/
def periodShiftS (blank mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : List (Act sc) :=
  periodShift blank n ++
    sIncBLoop blank mark (k * n) (applyActs blank (periodShift blank n) ts)

theorem periodShiftS_length_le (blank mark : Fin sc) (k n : ℕ) (ts : Tapes sc) :
    (periodShiftS blank mark k n ts).length ≤ 10 * n + 2 * (k * n) := by
  have h := sIncBLoop_length_le blank mark (k * n) (applyActs blank (periodShift blank n) ts)
  rw [periodShiftS, List.length_append, periodShift_length]
  omega

/-- **符号つき周期ずらしの実現**：`p += n`, `q -= n` に対して `B` が `k*n` 増える。 -/
theorem periodShiftS_enc (hmark : mark ≠ blank)
    {n a b D Q E P F S R M N : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (a + n) b ⟨D, Q + n, E, P, F + n, S, R⟩ g ts)
    (hB : SgnB M N ⟨D, Q + n, E, P, F + n, S, R⟩ g) :
    ∃ (D' bn' : ℕ),
      EncS blank startSym endSym mark x a b ⟨D', Q, E, P + n, F + n, S, R⟩
          ⟨g.ap, g.an, bn'⟩ (applyActs blank (periodShiftS blank mark k n ts) ts)
        ∧ SgnB (M + k * n) N ⟨D', Q, E, P + n, F + n, S, R⟩ ⟨g.ap, g.an, bn'⟩ := by
  have hpre := periodShiftS_pre (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) hE
  obtain ⟨D', bn', hE', hB'⟩ := sIncBLoop_enc (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) hmark (k * n) M N a b
    ⟨D, Q, E, P + n, F + n, S, R⟩ g _ hpre hB
  refine ⟨D', bn', ?_, hB'⟩
  rw [periodShiftS, applyActs_append]
  exact hE'

/-! #### `soTest` / `ceFlag` の符号つき版 -/

theorem soTestS_enc {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b c g (applyActs blank (soTest blank ts) ts) := by
  have hres : applyActs blank (soTest blank ts) ts =
      { ts with
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left)
          (probe blank ts.Cq) .right } := rfl
  refine ⟨soTest_enc hE.base, ?_, ?_, ?_⟩ <;> rw [hres]
  · exact hE.ca
  · exact hE.cb
  · exact hE.cc

/-- 符号つきカウンタから読む中断判定（`orcAB` が使える形）。 -/
theorem sAbort_iffS (hend : endSym ∉ x)
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q')
          ⟨D', q', E', p', F', S', r⟩ g' ts' →
      SignedOK k r p' q' ⟨D', q', E', p', F', S', r⟩ g' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1))
    {q D E p F S : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, E, p, F, S, r⟩ g ts)
    (hok : SignedOK k r p q ⟨D, q, E, p, F, S, r⟩ g) :
    sAbort endSym orc ts ↔ AbortAt x k p r s q := by
  have hab : s + q ≤ s + p + q := by omega
  have hble : s + p + q ≤ x.length := pat_le hE.base.v2
  have horcq : orc ts = decide (r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1) := by
    rw [horc q D E p F S g ts hE hok, Nat.add_assoc]
  unfold sAbort AbortAt
  rw [horcq]
  by_cases hb : s + p + q < x.length
  · have hale : s + q < x.length := by omega
    have hV2 : Tape.read ts.V2 ≠ endSym := by
      intro hc
      have := (read_pat_end_iff hend hE.base.v2).1 hc
      omega
    have h1 := read_pat_lt hE.base.v1 hale
    have h2 := read_pat_lt hE.base.v2 hb
    constructor
    · rintro ⟨-, hm, ho⟩
      exact ⟨hb, by rw [h1, h2, hm], of_decide_eq_true ho⟩
    · rintro ⟨-, hm, hc⟩
      rw [h1, h2] at hm
      exact ⟨hV2, Option.some.inj hm, decide_eq_true hc⟩
  · have hbe : s + p + q = x.length := by omega
    have hV2 : Tape.read ts.V2 = endSym := read_pat_end hE.base.v2 hbe
    constructor
    · rintro ⟨h1, -, -⟩; exact absurd hV2 h1
    · rintro ⟨h1, -, -⟩; omega

def soInner (blank endSym mark : Fin sc) (orc : Tapes sc → Bool) (Fs : ℕ) (ts : Tapes sc) :
    List (Act sc) :=
  sProg blank endSym mark orc Fs (soAfterTest blank ts)

def soAfterInner (blank endSym mark : Fin sc) (orc : Tapes sc → Bool) (Fs : ℕ)
    (ts : Tapes sc) : Tapes sc :=
  applyActs blank (soInner blank endSym mark orc Fs ts) (soAfterTest blank ts)

/-- ずらし部（中断なら空、周期ずらしかリセットずらし）。 -/
def soShift (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  if sAbort endSym orc (soAfterInner blank endSym mark orc Fs ts) then []
  else if orc2 (soAfterInner blank endSym mark orc Fs ts) then
    periodShiftS blank mark k (fOf (soAfterInner blank endSym mark orc Fs ts))
      (soAfterInner blank endSym mark orc Fs ts)
  else shiftPhase2S blank mark k (soAfterInner blank endSym mark orc Fs ts)

def soAfterShift (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ)
    (ts : Tapes sc) : Tapes sc :=
  applyActs blank (soShift blank endSym mark orc orc2 k Fs ts)
    (soAfterInner blank endSym mark orc Fs ts)

/-- 中断（＝第 2 周期の発見）を記録するフラグ：`Ce` を 1 増やす（1 動作）。
第 2 相のあいだ `Ce` は常に `0` で、このフラグはループを抜ける最後の 1 回だけ立つ。 -/
def ceFlag (blank : Fin sc) : List (Act sc) := [Act.Ce blank .right]

@[simp] theorem ceFlag_length (blank : Fin sc) : (ceFlag blank).length = 1 := rfl

theorem applyActs_ceFlag (ts : Tapes sc) :
    applyActs blank (ceFlag blank) ts =
      { ts with Ce := Tape.step blank ts.Ce blank .right } := rfl

theorem ceFlag_enc {a b : ℕ} {D Q E P F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ ts) :
    Enc blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩
      (applyActs blank (ceFlag blank) ts) := by
  rw [applyActs_ceFlag]
  exact ⟨hE.v1, hE.v2, hE.cd, hE.cq, Tape.counter'_inc hE.ce, hE.cp, hE.cf, hE.cs, hE.cr⟩

theorem ceFlagS_enc {a b : ℕ} {D Q E P F S R : ℕ} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ g ts) :
    EncS blank startSym endSym mark x a b ⟨D, Q, E + 1, P, F, S, R⟩ g
      (applyActs blank (ceFlag blank) ts) := by
  refine ⟨ceFlag_enc hE.base, ?_, ?_, ?_⟩ <;> rw [applyActs_ceFlag]
  · exact hE.ca
  · exact hE.cb
  · exact hE.cc

/-- `_second_period` の外側ループ全体の動作列。 -/
def soProg (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k Fs : ℕ) :
    ℕ → Tapes sc → List (Act sc)
  | 0, _ => []
  | fuel + 1, ts =>
      if soCond blank endSym mark ts then
        soTest blank ts ++ (soInner blank endSym mark orc Fs ts ++
          (soShift blank endSym mark orc orc2 k Fs ts ++
            (if sAbort endSym orc (soAfterInner blank endSym mark orc Fs ts) then ceFlag blank
             else soProg blank endSym mark orc orc2 k Fs fuel
               (soAfterShift blank endSym mark orc orc2 k Fs ts))))
      else soTest blank ts


/-- **主定理（`_second_period` 外側ループの実現とコスト）**。
`A = 2k + 40`, `C = 2k + 20`：総動作数は
`(2k+40) * secondOuterWork + (2k+20) * q + 2` 以下。入口 `q = 0`（`secondPeriod`）なら
`(2k+40) * secondOuterWork + 2`。符号つきカウンタ `A = r - (p+q)`（`Ca`/`Cb`）と
`B = (k-1)p - (q+1)`（`Cd`/`Cc`）は巻き戻し・ずらし・周期ずらしのすべてで
その場で正しく更新される（`SignedOK` が出入りともに成り立つ）。
終状態の `Ce` は「第 2 周期が見つかったか」のフラグ（見つかれば `1`、さもなくば `0`）。 -/
theorem soProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s first S : ℕ} (hs : s ≤ x.length) (_hfirst : 0 < first)
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q')
          ⟨D', q', E', p', F', S', r⟩ g' ts' →
      SignedOK k r p' q' ⟨D', q', E', p', F', S', r⟩ g' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1))
    (horc2 : ∀ (q' D' E' p' S' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x (s + q') (s + p' + q') ⟨D', q', E', p', first, S', r⟩ ts' →
      orc2 ts' = decide (k * first ≤ q' ∧ q' ≤ r)) :
    ∀ (fuel p q D : ℕ) (g : Ctr3) (ts : Tapes sc), s + p + q ≤ x.length →
      EncS blank startSym endSym mark x (s + q) (s + p + q) ⟨D, q, 0, p, first, S, r⟩ g ts →
      SignedOK k r p q ⟨D, q, 0, p, first, S, r⟩ g →
      ((soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel ts).length
          ≤ (2 * k + 40) * secondOuterWork (x.drop s) k first r fuel p q
              + (2 * k + 20) * q + 2
        ∧ (∃ D' q' E' P' g',
            EncS blank startSym endSym mark x (s + q') (s + P' + q')
              ⟨D', q', E', P', first, S, r⟩ g'
              (applyActs blank
                (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) fuel ts) ts)
            ∧ SignedOK k r P' q' ⟨D', q', E', P', first, S, r⟩ g'
            ∧ s + P' + q' ≤ x.length
            ∧ q' ≤ q + secondOuterWork (x.drop s) k first r fuel p q
            ∧ P' ≤ p + q + 2 * secondOuterWork (x.drop s) k first r fuel p q
            ∧ (∀ p₂, secondOuter (x.drop s) k first r fuel p q = some p₂ → P' = p₂)
            ∧ E' = (if (secondOuter (x.drop s) k first r fuel p q).isSome then 1 else 0))) := by
  have hdrop : (x.drop s).length = x.length - s := by simp
  intro fuel
  induction fuel with
  | zero =>
      intro p q D g ts hfit hE hok
      refine ⟨by simp [soProg, secondOuterWork],
        ⟨D, q, 0, p, g, ?_, hok, hfit, ?_, ?_, ?_, ?_⟩⟩
      · rw [soProg, applyActs_nil]; exact hE
      · simp [secondOuterWork]
      · simp [secondOuterWork]
      · intro p₂ hc; rw [secondOuter] at hc; simp at hc
      · simp [secondOuter]
  | succ fuel ih =>
      intro p q D g ts hfit hE hok
      have hq0 : probe blank ts.Cq = mark ↔ q = 0 := probe_iff hmark hE.base.cq
      have hv2 : Tape.read ts.V2 = endSym ↔ s + p + q = x.length :=
        read_pat_end_iff hend hE.base.v2
      have hguard : soCond blank endSym mark ts ↔ p < (x.drop s).length := by
        unfold soCond
        rw [hq0, hv2, hdrop]
        omega
      by_cases hc : soCond blank endSym mark ts
      · have hg : p < (x.drop s).length := hguard.1 hc
        have hE0 : EncS blank startSym endSym mark x (s + q) (s + p + q)
            ⟨D, q, 0, p, first, S, r⟩ g (soAfterTest blank ts) := soTestS_enc hE
        obtain ⟨⟨D2, g2, hEnc2, hok2'⟩, hcost2⟩ := sProg_spec (blank := blank)
          (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k) (r := r)
          (orc := orc) hend hmark horc
          ((x.drop s).length + 1) q D 0 p first S g (soAfterTest blank ts) hE0 hok
        obtain ⟨j, hj⟩ : ∃ j, sSteps x k p r s ((x.drop s).length + 1) q = j := ⟨_, rfl⟩
        rw [hj] at hEnc2 hok2'
        have hE2 : EncS blank startSym endSym mark x (s + (q + j)) (s + p + (q + j))
            ⟨D2, q + j, 0, p, first, S, r⟩ g2 (soAfterInner blank endSym mark orc
              ((x.drop s).length + 1) ts) := by
          have e1 : s + q + j = s + (q + j) := by omega
          have e2 : s + p + q + j = s + p + (q + j) := by omega
          rw [e1, e2] at hEnc2
          exact hEnc2
        have hok2 : SignedOK k r p (q + j) ⟨D2, q + j, 0, p, first, S, r⟩ g2 := hok2'
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
        have habort := sAbort_iffS (blank := blank) (startSym := startSym) (endSym := endSym)
          (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (s := s) hend horc hE2 hok2
        rw [hWeq] at hjW hcost2
        obtain ⟨W, hW⟩ : ∃ W, secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q = W :=
          ⟨_, rfl⟩
        rw [hW] at hcost2 hjW
        obtain ⟨A, hA⟩ : ∃ A, 2 * k + 40 = A := ⟨_, rfl⟩
        obtain ⟨C, hC⟩ : ∃ C, 2 * k + 20 = C := ⟨_, rfl⟩
        by_cases hab : sAbort endSym orc (soAfterInner blank endSym mark orc
            ((x.drop s).length + 1) ts)
        · -- 中断：第 2 周期 `p` を発見
          have hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = none :=
            hnone.2 (habort.1 hab)
          have hshift0 : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts
              = [] := by rw [soShift, if_pos hab]
          have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
              = soTest blank ts ++ (soInner blank endSym mark orc ((x.drop s).length + 1) ts ++
                  ceFlag blank) := by
            rw [soProg, if_pos hc, if_pos hab, hshift0]
            simp
          have happ : applyActs blank
              (soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts) ts
              = applyActs blank (ceFlag blank)
                  (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts) := by
            rw [hprog, applyActs_append, applyActs_append]
            rfl
          refine ⟨?_, ⟨D2, q + j, 1, p, g2, by rw [happ]; exact ceFlagS_enc hE2, hok2,
            by omega, ?_, ?_, ?_, ?_⟩⟩
          · rw [hprog, secondOuterWork, if_pos hg]
            simp only [hsi, hW, List.length_append, soTest_length, ceFlag_length]
            rw [hA, hC]
            have h3 : (soInner blank endSym mark orc ((x.drop s).length + 1) ts).length
                ≤ 9 * W := hcost2
            have hexp : A * (1 + W + 0) = A + A * W := by ring
            have hmul : 9 * W ≤ A * W := Nat.mul_le_mul_right W (by omega)
            omega
          · rw [secondOuterWork, if_pos hg]
            simp only [hsi, hW]
            omega
          · rw [secondOuterWork, if_pos hg]
            simp only [hsi, hW]
            omega
          · intro p₂ hp2
            rw [secondOuter, if_pos hg] at hp2
            simp only [hsi, Option.some.injEq] at hp2
            omega
          · rw [secondOuter, if_pos hg]
            simp only [hsi, Option.isSome_some, if_true]
        · -- 通常終了：`secondInner = some (q + j)`
          have hnab : ¬ AbortAt x k p r s (q + j) := fun hcc => hab (habort.2 hcc)
          have hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q = some (q + j) := by
            rcases hsome : secondInner (x.drop s) k p r ((x.drop s).length + 1) q with _ | q'
            · exact absurd (hnone.1 hsome) hnab
            · have := (sSteps_secondInner (x := x) (k := k) (r := r) (p := p) hs
                ((x.drop s).length + 1) q hfit).1 q' hsome
              rw [hj] at this
              rw [this]
          have hf2 : fOf (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts)
              = first := fOf_eq hE2.base
          have horc2q : orc2 (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts)
              = decide (k * first ≤ q + j ∧ q + j ≤ r) :=
            horc2 (q + j) D2 0 p S _ hE2.base
          obtain ⟨hA2, hB2⟩ := (signedOK_iff k r p (q + j)
            ⟨D2, q + j, 0, p, first, S, r⟩ g2).1 hok2
          have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
              = soTest blank ts ++ (soInner blank endSym mark orc ((x.drop s).length + 1) ts ++
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
          have h3 : (soInner blank endSym mark orc ((x.drop s).length + 1) ts).length
              ≤ 9 * W := hcost2
          have hmul : 9 * W + C * W ≤ A * W := by
            calc 9 * W + C * W = (9 + C) * W := by ring
              _ ≤ A * W := Nat.mul_le_mul_right W (by omega)
          by_cases hb2 : k * first ≤ q + j ∧ q + j ≤ r
          · -- 周期ずらし
            have hfq : first ≤ q + j := by
              have : first ≤ k * first := Nat.le_mul_of_pos_left first (by omega)
              omega
            have horcT : orc2 (soAfterInner blank endSym mark orc
                ((x.drop s).length + 1) ts) = true := by
              rw [horc2q]; exact decide_eq_true hb2
            have hshift : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts
                = periodShiftS blank mark k first
                    (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts) := by
              rw [soShift, if_neg hab, if_pos horcT, hf2]
            have hpre : EncS blank startSym endSym mark x ((s + (q + j - first)) + first)
                (s + p + (q + j)) ⟨D2, (q + j - first) + first, 0, p, 0 + first, S, r⟩ g2
                (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts) := by
              have e1 : (s + (q + j - first)) + first = s + (q + j) := by omega
              have e2 : (q + j - first) + first = q + j := by omega
              have e3 : (0 : ℕ) + first = first := by omega
              rw [e1, e2, e3]
              exact hE2
            have hBpre : SgnB ((k - 1) * p) ((q + j) + 1)
                ⟨D2, (q + j - first) + first, 0, p, 0 + first, S, r⟩ g2 := hB2
            obtain ⟨D3, bn3, hE3a, hB3⟩ := periodShiftS_enc (blank := blank)
              (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k)
              hmark hpre hBpre
            have e4 : s + p + (q + j) = s + (p + first) + (q + j - first) := by omega
            have e5 : (0 : ℕ) + first = first := by omega
            rw [e4, e5] at hE3a
            have hE3 : EncS blank startSym endSym mark x (s + (q + j - first))
                (s + (p + first) + (q + j - first))
                ⟨D3, q + j - first, 0, p + first, first, S, r⟩ ⟨g2.ap, g2.an, bn3⟩
                (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              rw [soAfterShift, hshift]
              exact hE3a
            have hBnew : SgnB ((k - 1) * (p + first)) ((q + j - first) + 1)
                ⟨D3, q + j - first, 0, p + first, first, S, r⟩ ⟨g2.ap, g2.an, bn3⟩ := by
              obtain ⟨eb1, eb2⟩ := hB3
              dsimp only at eb1 eb2
              have hx : (k - 1) * (p + first) = (k - 1) * p + (k - 1) * first := by ring
              have hk1 : k - 1 + 1 = k := by omega
              have hy : k * first = (k - 1) * first + first := by
                calc k * first = (k - 1 + 1) * first := by rw [hk1]
                  _ = (k - 1) * first + first := by ring
              constructor <;> dsimp only <;> omega
            have hAnew : SgnA r ((p + first) + (q + j - first)) ⟨g2.ap, g2.an, bn3⟩ := by
              have e : (p + first) + (q + j - first) = p + (q + j) := by omega
              rw [e]; exact hA2
            have hok3 : SignedOK k r (p + first) (q + j - first)
                ⟨D3, q + j - first, 0, p + first, first, S, r⟩ ⟨g2.ap, g2.an, bn3⟩ :=
              (signedOK_iff k r (p + first) (q + j - first) _ _).2 ⟨hAnew, hBnew⟩
            obtain ⟨hrc, hre⟩ := ih (p + first) (q + j - first) D3 ⟨g2.ap, g2.an, bn3⟩ _
              (by omega) hE3 hok3
            have hso : secondOuter (x.drop s) k first r (fuel + 1) p q
                = secondOuter (x.drop s) k first r fuel (p + first) (q + j - first) := by
              rw [secondOuter, if_pos hg]
              simp only [hsi, if_pos hb2]
            have hps := periodShiftS_length_le blank mark k first
              (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts)
            refine ⟨?_, ?_⟩
            · rw [hprog, secondOuterWork, if_pos hg]
              simp only [hsi, if_pos hb2, hW, List.length_append, soTest_length, hshift]
              obtain ⟨Wr, hWr⟩ : ∃ Wr, secondOuterWork (x.drop s) k first r fuel (p + first)
                  (q + j - first) = Wr := ⟨_, rfl⟩
              rw [hWr] at hrc
              rw [hWr, hA, hC]
              rw [hA, hC] at hrc
              have hexp : A * (1 + W + Wr) = A + A * W + A * Wr := by ring
              have h10 : 10 * first + 2 * (k * first) ≤ C * first := by
                calc 10 * first + 2 * (k * first) = (2 * k + 10) * first := by ring
                  _ ≤ C * first := Nat.mul_le_mul_right first (by omega)
              have hCsub : C * (q + j - first) + C * first = C * (q + j) := by
                rw [← Nat.mul_add]
                congr 1
                omega
              have hCq : C * (q + j) ≤ C * q + C * W := by
                have e : C * (q + j) = C * q + C * j := by ring
                have h2 : C * j ≤ C * W := Nat.mul_le_mul_left C (by omega)
                omega
              omega
            · obtain ⟨D', q', E', P', g', hEnc', hok', hfit', hq', hP', hp2, hflag⟩ := hre
              refine ⟨D', q', E', P', g', by rw [happ]; exact hEnc', hok', hfit', ?_, ?_,
                (by intro p₂ hh; exact hp2 p₂ (by rw [← hso]; exact hh)),
                (by rw [hso]; exact hflag)⟩
              · rw [secondOuterWork, if_pos hg]
                simp only [hsi, if_pos hb2, hW]
                omega
              · rw [secondOuterWork, if_pos hg]
                simp only [hsi, if_pos hb2, hW]
                omega
          · -- リセットずらし
            have horcF : orc2 (soAfterInner blank endSym mark orc
                ((x.drop s).length + 1) ts) = false := by
              rw [horc2q]; exact decide_eq_false hb2
            have hshift : soShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts
                = shiftPhase2S blank mark k
                  (soAfterInner blank endSym mark orc ((x.drop s).length + 1) ts) := by
              rw [soShift, if_neg hab, horcF]
              simp
            have hfitE : s + p + shiftNoPeriod (q + j) k ≤ x.length := by
              rcases Nat.eq_zero_or_pos (q + j) with h0 | h0
              · rw [h0, shiftNoPeriod_zero (by omega)]
                omega
              · have := shiftNoPeriod_le_of_pos (k := k) (by omega) h0
                omega
            obtain ⟨⟨D3, ap3, an3, bn3, hE3a, hA3, hB3⟩, hlen3⟩ :=
              shiftPhase2S_enc' (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) (k := k) (r := r) (by omega) hmark hE2 hfitE hA2 hB2
            have hE3 : EncS blank startSym endSym mark x (s + 0)
                (s + (p + shiftNoPeriod (q + j) k) + 0)
                ⟨D3, 0, 0, p + shiftNoPeriod (q + j) k, first, S, r⟩ ⟨ap3, an3, bn3⟩
                (soAfterShift blank endSym mark orc orc2 k ((x.drop s).length + 1) ts) := by
              rw [soAfterShift, hshift]
              have e1 : s + p + shiftNoPeriod (q + j) k
                  = s + (p + shiftNoPeriod (q + j) k) + 0 := by omega
              have e2 : s = s + 0 := by omega
              rw [e1] at hE3a
              rw [← e2]
              exact hE3a
            have hok3 : SignedOK k r (p + shiftNoPeriod (q + j) k) 0
                ⟨D3, 0, 0, p + shiftNoPeriod (q + j) k, first, S, r⟩ ⟨ap3, an3, bn3⟩ := by
              refine (signedOK_iff k r (p + shiftNoPeriod (q + j) k) 0 _ _).2 ⟨?_, ?_⟩
              · have e : (p + shiftNoPeriod (q + j) k) + 0 = p + shiftNoPeriod (q + j) k := by
                  omega
                rw [e]; exact hA3
              · have e : (0 : ℕ) + 1 = 1 := by omega
                rw [e]; exact hB3
            obtain ⟨hrc, hre⟩ := ih (p + shiftNoPeriod (q + j) k) 0 D3 ⟨ap3, an3, bn3⟩ _
              (by omega) hE3 hok3
            have hso : secondOuter (x.drop s) k first r (fuel + 1) p q
                = secondOuter (x.drop s) k first r fuel
                  (p + shiftNoPeriod (q + j) k) 0 := by
              rw [secondOuter, if_pos hg]
              simp only [hsi, if_neg hb2]
            refine ⟨?_, ?_⟩
            · rw [hprog, secondOuterWork, if_pos hg]
              simp only [hsi, if_neg hb2, hW, List.length_append, soTest_length, hshift]
              obtain ⟨Wr, hWr⟩ : ∃ Wr, secondOuterWork (x.drop s) k first r fuel
                  (p + shiftNoPeriod (q + j) k) 0 = Wr := ⟨_, rfl⟩
              rw [hWr] at hrc
              rw [hWr, hA, hC]
              rw [hA, hC] at hrc
              obtain ⟨e, he⟩ : ∃ e, shiftNoPeriod (q + j) k = e := ⟨_, rfl⟩
              rw [he] at hlen3
              obtain ⟨K7, hK7⟩ : ∃ K7, 2 * k + 7 = K7 := ⟨_, rfl⟩
              rw [hK7] at hlen3
              have heq1 : e ≤ (q + j) + 1 := by
                rw [← he]; exact shiftNoPeriod_le_succ (by omega) (q + j)
              have hKe : K7 * e ≤ K7 * ((q + j) + 1) := Nat.mul_le_mul_left K7 heq1
              have hKe2 : K7 * ((q + j) + 1) = K7 * (q + j) + K7 := by ring
              have hsum : 9 * (q + j) + K7 * (q + j) ≤ C * (q + j) := by
                calc 9 * (q + j) + K7 * (q + j) = (9 + K7) * (q + j) := by ring
                  _ ≤ C * (q + j) := Nat.mul_le_mul_right (q + j) (by omega)
              have hCq : C * (q + j) ≤ C * q + C * W := by
                have e2 : C * (q + j) = C * q + C * j := by ring
                have h2 : C * j ≤ C * W := Nat.mul_le_mul_left C (by omega)
                omega
              have hexp : A * (1 + W + Wr) = A + A * W + A * Wr := by ring
              omega
            · obtain ⟨D', q', E', P', g', hEnc', hok', hfit', hq', hP', hp2, hflag⟩ := hre
              have he' : shiftNoPeriod (q + j) k ≤ (q + j) + 1 :=
                shiftNoPeriod_le_succ (by omega) (q + j)
              refine ⟨D', q', E', P', g', by rw [happ]; exact hEnc', hok', hfit', ?_, ?_,
                (by intro p₂ hh; exact hp2 p₂ (by rw [← hso]; exact hh)),
                (by rw [hso]; exact hflag)⟩
              · rw [secondOuterWork, if_pos hg]
                simp only [hsi, if_neg hb2, hW]
                omega
              · rw [secondOuterWork, if_pos hg]
                simp only [hsi, if_neg hb2, hW]
                omega
      · -- 番人：`p ≥ |v|` で `none`
        have hng : ¬ (p < (x.drop s).length) := fun hcc => hc (hguard.2 hcc)
        have hprog : soProg blank endSym mark orc orc2 k ((x.drop s).length + 1) (fuel + 1) ts
            = soTest blank ts := by rw [soProg, if_neg hc]
        refine ⟨?_, ⟨D, q, 0, p, g, ?_, hok, hfit, ?_, ?_, ?_, ?_⟩⟩
        · rw [hprog, secondOuterWork, if_neg hng, soTest_length]
          omega
        · rw [hprog]; exact soTestS_enc hE
        · rw [secondOuterWork, if_neg hng]; omega
        · rw [secondOuterWork, if_neg hng]; omega
        · intro p₂ hp2
          rw [secondOuter, if_neg hng] at hp2
          simp at hp2
        · rw [secondOuter, if_neg hng]; simp

/-- 第2相の正部カウンタの初期値を積む。各反復は1セル動作。 -/
def seedSigned (blank : Fin sc) : ℕ → ℕ → List (Act sc)
  | 0, 0 => []
  | 0, d + 1 => Act.Cd blank .right :: seedSigned blank 0 d
  | a + 1, d => Act.Ca blank .right :: seedSigned blank a d

theorem seedSigned_length (blank : Fin sc) (a d : ℕ) :
    (seedSigned blank a d).length = a + d := by
  induction a with
  | zero =>
      induction d with
      | zero => simp [seedSigned]
      | succ d ih => simp [seedSigned, ih]
  | succ a ih => simp [seedSigned, ih]; omega

theorem seedSigned_enc {a b : ℕ} {c : Ctr} {g : Ctr3} :
    ∀ (ap d : ℕ) (ts : Tapes sc),
      EncS blank startSym endSym mark x a b c g ts →
      EncS blank startSym endSym mark x a b
        ⟨c.d + d, c.q, c.e, c.p, c.f, c.s, c.r⟩
        ⟨g.ap + ap, g.an, g.bn⟩ (applyActs blank (seedSigned blank ap d) ts) := by
  intro ap
  induction ap generalizing c g with
  | zero =>
      intro d
      induction d generalizing c with
      | zero => intro ts hE; simpa [seedSigned, applyActs] using hE
      | succ d ih =>
          intro ts hE
          have h1 : EncS blank startSym endSym mark x a b
              ⟨c.d + 1, c.q, c.e, c.p, c.f, c.s, c.r⟩ g
              (applyAct blank ts (Act.Cd blank .right)) :=
            ⟨⟨hE.base.v1, hE.base.v2, Tape.counter'_inc hE.base.cd,
              hE.base.cq, hE.base.ce, hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩,
              hE.ca, hE.cb, hE.cc⟩
          simpa [seedSigned, applyActs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih _ h1
  | succ ap ih =>
      intro d ts hE
      have h1 : EncS blank startSym endSym mark x a b c
          ⟨g.ap + 1, g.an, g.bn⟩ (applyAct blank ts (Act.Ca blank .right)) :=
        ⟨⟨hE.base.v1, hE.base.v2, hE.base.cd, hE.base.cq, hE.base.ce,
          hE.base.cp, hE.base.cf, hE.base.cs, hE.base.cr⟩,
          Tape.counter'_inc hE.ca, hE.cb, hE.cc⟩
      simpa [seedSigned, applyActs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih d _ h1

/-- `p=1,q=0` の入口で符号つき不変条件を確立する。
追加テープが零であることを明示的に要求し、未初期化の領域は仮定しない。 -/
theorem seedSigned_initial (hk : 3 ≤ k) (hr : 1 ≤ r)
    {s first S : ℕ} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x s (s + 1)
      ⟨0, 0, 0, 1, first, S, r⟩ ⟨0, 0, 0⟩ ts) :
    EncS blank startSym endSym mark x s (s + 1)
        ⟨k - 2, 0, 0, 1, first, S, r⟩ ⟨r - 1, 0, 0⟩
        (applyActs blank (seedSigned blank (r - 1) (k - 2)) ts)
      ∧ SignedOK k r 1 0 ⟨k - 2, 0, 0, 1, first, S, r⟩ ⟨r - 1, 0, 0⟩ := by
  constructor
  · simpa using seedSigned_enc (r - 1) (k - 2) ts hE
  · simp [SignedOK]
    omega

/-- Signed scratch values read from their unary tape representation. -/
def signedOf (ts : Tapes sc) : Ctr3 :=
  ⟨ts.Ca.left.length - 1, ts.Cb.left.length - 1, ts.Cc.left.length - 1⟩

theorem signedOf_eq {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) : signedOf ts = g := by
  have ha := ctr_len hE.ca
  have hb := ctr_len hE.cb
  have hc := ctr_len hE.cc
  cases g
  simp_all [signedOf]

def clearSignedAt (blank : Fin sc) (ts : Tapes sc) : List (Act sc) :=
  clearSigned blank (ts.Cd.left.length - 1) (signedOf ts)

theorem clearSignedAt_spec {a b : ℕ} {c : Ctr} {g : Ctr3} {ts : Tapes sc}
    (hE : EncS blank startSym endSym mark x a b c g ts) :
    EncS blank startSym endSym mark x a b { c with d := 0 } ⟨0, 0, 0⟩
        (applyActs blank (clearSignedAt blank ts) ts)
      ∧ (clearSignedAt blank ts).length = 2 * (c.d + g.ap + g.an + g.bn) := by
  rw [clearSignedAt, signedOf_eq hE, ctr_len hE.base.cd]
  exact ⟨clearSigned_enc hE, clearSigned_length blank c.d g⟩

/-- `secondPeriod`（`= secondOuter v k first r (|v|+1) 1 0`）のテープ実現。 -/
def spProg (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool) (k n : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  soProg blank endSym mark orc orc2 k (n + 1) (n + 1) ts

/-- **系（`secondPeriod` のテープ実現とコスト）**：`A = 2k+40`, `B = 2`。
終状態の `Ce` は「第 2 周期が見つかったか」のフラグ。 -/
theorem spProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s first S D : ℕ} {g : Ctr3} {ts : Tapes sc} (hs : s ≤ x.length) (hfirst : 0 < first)
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q') ⟨D', q', E', p', F', S', r⟩ g' ts' →
      SignedOK k r p' q' ⟨D', q', E', p', F', S', r⟩ g' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1))
    (horc2 : ∀ (q' D' E' p' S' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x (s + q') (s + p' + q')
        ⟨D', q', E', p', first, S', r⟩ ts' →
      orc2 ts' = decide (k * first ≤ q' ∧ q' ≤ r))
    (hfit : s + 1 ≤ x.length)
    (hE : EncS blank startSym endSym mark x s (s + 1) ⟨D, 0, 0, 1, first, S, r⟩ g ts)
    (hok : SignedOK k r 1 0 ⟨D, 0, 0, 1, first, S, r⟩ g) :
    ((spProg blank endSym mark orc orc2 k (x.drop s).length ts).length
        ≤ (2 * k + 40) * secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0 + 2
      ∧ (∃ D' q' E' P' g',
          EncS blank startSym endSym mark x (s + q') (s + P' + q')
            ⟨D', q', E', P', first, S, r⟩ g'
            (applyActs blank (spProg blank endSym mark orc orc2 k (x.drop s).length ts) ts)
          ∧ SignedOK k r P' q' ⟨D', q', E', P', first, S, r⟩ g'
          ∧ s + P' + q' ≤ x.length
          ∧ q' ≤ secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0
          ∧ P' ≤ 1 + 2 * secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0
          ∧ (∀ p₂, secondPeriod (x.drop s) k first r = some p₂ → P' = p₂)
          ∧ E' = (if (secondPeriod (x.drop s) k first r).isSome then 1 else 0))) := by
  have hE' : EncS blank startSym endSym mark x (s + 0) (s + 1 + 0) ⟨D, 0, 0, 1, first, S, r⟩ g ts :=
    hE
  obtain ⟨hc, he⟩ := soProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (orc2 := orc2) hk hend hmark hs hfirst
    horc horc2 ((x.drop s).length + 1) 1 0 D g ts (by omega) hE' hok
  refine ⟨?_, ?_⟩
  · rw [spProg]
    simpa using hc
  · obtain ⟨D', q', E', P', g', hEnc, hok', hfit', hq', hP', hp2, hflag⟩ := he
    refine ⟨D', q', E', P', g', ?_, hok', hfit', by omega, by omega, hp2, hflag⟩
    rw [spProg]
    exact hEnc

/-- Second phase with explicitly initialized and reclaimed signed scratch space. -/
def spClosedProg (blank endSym mark : Fin sc) (orc orc2 : Tapes sc → Bool)
    (k n r : ℕ) (ts : Tapes sc) : List (Act sc) :=
  let seed := seedSigned blank (r - 1) (k - 2)
  let t := applyActs blank seed ts
  let body := spProg blank endSym mark orc orc2 k n t
  seed ++ (body ++ clearSignedAt blank (applyActs blank body t))

theorem spClosedProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s first S : ℕ} {ts : Tapes sc} (hs : s ≤ x.length) (hfirst : 0 < first)
    (hr : 1 ≤ r)
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q')
        ⟨D', q', E', p', F', S', r⟩ g' ts' →
      SignedOK k r p' q' ⟨D', q', E', p', F', S', r⟩ g' →
      orc ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1))
    (horc2 : ∀ (q' D' E' p' S' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x (s + q') (s + p' + q')
        ⟨D', q', E', p', first, S', r⟩ ts' →
      orc2 ts' = decide (k * first ≤ q' ∧ q' ≤ r))
    (hfit : s + 1 ≤ x.length)
    (hE : EncS blank startSym endSym mark x s (s + 1)
      ⟨0, 0, 0, 1, first, S, r⟩ ⟨0, 0, 0⟩ ts) :
    (spClosedProg blank endSym mark orc orc2 k (x.drop s).length r ts).length
        ≤ (6 * k + 50) * secondOuterWork (x.drop s) k first r
          ((x.drop s).length + 1) 1 0 + 3 * r + 3 * k + 8
      ∧ ∃ q' E' P',
        EncS blank startSym endSym mark x (s + q') (s + P' + q')
          ⟨0, q', E', P', first, S, r⟩ ⟨0, 0, 0⟩
          (applyActs blank
            (spClosedProg blank endSym mark orc orc2 k (x.drop s).length r ts) ts)
        ∧ s + P' + q' ≤ x.length
        ∧ q' ≤ secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0
        ∧ P' ≤ 1 + 2 * secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0
        ∧ (∀ p₂, secondPeriod (x.drop s) k first r = some p₂ → P' = p₂)
        ∧ E' = (if (secondPeriod (x.drop s) k first r).isSome then 1 else 0) := by
  obtain ⟨hseed, hOK⟩ := seedSigned_initial hk hr hE
  obtain ⟨hcost, D', q', E', P', g', he, hok, hf, hq, hp, hp2, hflag⟩ :=
    spProg_spec hk hend hmark hs hfirst horc horc2 hfit hseed hOK
  obtain ⟨hclear, hlen⟩ := clearSignedAt_spec he
  have hclearBound := clearSigned_length_bound blank (by omega : 1 ≤ k) hok
  have hlenBound : (clearSignedAt blank
      (applyActs blank (spProg blank endSym mark orc orc2 k (x.drop s).length
        (applyActs blank (seedSigned blank (r - 1) (k - 2)) ts))
        (applyActs blank (seedSigned blank (r - 1) (k - 2)) ts))).length
      ≤ 2 * (r + k * P' + 2 * q' + 1) := by
    rw [hlen]
    simpa only [clearSigned_length] using hclearBound
  constructor
  · simp only [spClosedProg, List.length_append, seedSigned_length]
    have hkp := Nat.mul_le_mul_left k hp
    have hrsub : r - 1 ≤ r := Nat.sub_le _ _
    have hksub : k - 2 ≤ k := Nat.sub_le _ _
    nlinarith only [hcost, hlenBound, hkp, hq, hrsub, hksub,
      Nat.zero_le (secondOuterWork (x.drop s) k first r ((x.drop s).length + 1) 1 0)]
  · refine ⟨q', E', P', ?_, hf, hq, hp, hp2, hflag⟩
    simpa only [spClosedProg, applyActs_append] using hclear

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

/-- `firstOuter` が成功したなら、その仕事量は少なくとも `1`。
（外側 1 反復あたりの定数オーバーヘッドを仕事量へ付け替えるのに使う。） -/
theorem firstOuterWork_pos (v : List (Fin sc)) (k bound : ℕ) :
    ∀ (fuel p p' m : ℕ), firstOuter v k bound fuel p = some (p', m) →
      1 ≤ firstOuterWork v k bound fuel p := by
  intro fuel
  induction fuel with
  | zero => intro p p' m hc; simp [firstOuter] at hc
  | succ fuel ih =>
      intro p p' m hc
      rw [firstOuter] at hc
      by_cases h1 : p < v.length ∧ p < bound
      · rw [firstOuterWork, if_pos h1]; omega
      · rw [if_neg h1] at hc; simp at hc

@[simp] theorem mActs_noSigned (blank endSym mark : Fin sc) (ts : Tapes sc) :
    NoSigned (mActs blank endSym mark ts) := by
  unfold mActs; split_ifs <;> simp [Act.noSigned]

@[simp] theorem mProg_noSigned (blank endSym mark : Fin sc) (fuel : ℕ) (ts : Tapes sc) :
    NoSigned (mProg blank endSym mark fuel ts) := by
  induction fuel generalizing ts with
  | zero => simp [mProg]
  | succ fuel ih => unfold mProg; split_ifs <;> simp [ih]

@[simp] theorem rActs_noSigned (blank endSym : Fin sc) (ts : Tapes sc) :
    NoSigned (rActs blank endSym ts) := by
  unfold rActs; split_ifs <;> simp [Act.noSigned]

@[simp] theorem rProg_noSigned (blank endSym : Fin sc) (fuel : ℕ) (ts : Tapes sc) :
    NoSigned (rProg blank endSym fuel ts) := by
  induction fuel generalizing ts with
  | zero => simp [rProg]
  | succ fuel ih => unfold rProg; split_ifs <;> simp [ih]

@[simp] theorem rewindLoop_noSigned (blank : Fin sc) (k n c : ℕ) :
    NoSigned (rewindLoop blank k n c) := by
  induction n generalizing c with
  | zero => simp [rewindLoop]
  | succ n ih => cases c <;> simp [rewindLoop, rewindUnit, Act.noSigned, ih]

@[simp] theorem cdIncs_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (cdIncs blank n) := by
  intro act h
  have he : act = Act.Cd blank .right := (List.mem_replicate.mp h).2
  subst act
  trivial

@[simp] theorem shiftLoop_noSigned (blank : Fin sc) (k n : ℕ) :
    NoSigned (shiftLoop blank k n) := by
  induction n with
  | zero => simp [shiftLoop]
  | succ n ih => simp [shiftLoop, shiftUnit, shiftHead, Act.noSigned, ih]

@[simp] theorem maxOneActs_noSigned (blank mark : Fin sc) (ts : Tapes sc) :
    NoSigned (maxOneActs blank mark ts) := by
  unfold maxOneActs; split_ifs <;> simp [Act.noSigned]

@[simp] theorem shiftPhase_noSigned (blank mark : Fin sc) (k : ℕ) (ts : Tapes sc) :
    NoSigned (shiftPhase blank mark k ts) := by simp [shiftPhase]

@[simp] theorem oHead_noSigned (blank endSym mark : Fin sc) (Fi : ℕ) (ts : Tapes sc) :
    NoSigned (oHead blank endSym mark Fi ts) := by simp [oHead, oTest, Act.noSigned]

@[simp] theorem oProg_noSigned (blank endSym mark : Fin sc)
    (orcB : Tapes sc → Bool) (k Fi fuel : ℕ) (ts : Tapes sc) :
    NoSigned (oProg blank endSym mark orcB k Fi fuel ts) := by
  induction fuel generalizing ts with
  | zero => simp [oProg]
  | succ fuel ih => unfold oProg; split_ifs <;> simp [ih]

@[simp] theorem fpProg_noSigned (blank endSym mark : Fin sc)
    (orcB : Tapes sc → Bool) (k n Fo : ℕ) (ts : Tapes sc) :
    NoSigned (fpProg blank endSym mark orcB k n Fo ts) := by
  simp [fpProg, initActs, Act.noSigned]

@[simp] theorem qrLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (qrLoop blank n) := by
  induction n with
  | zero => simp [qrLoop]
  | succ n ih => simp [qrLoop, qrUnit, Act.noSigned, ih]

@[simp] theorem pcLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (pcLoop blank n) := by
  induction n with
  | zero => simp [pcLoop]
  | succ n ih => simp [pcLoop, pcUnit, Act.noSigned, ih]

@[simp] theorem cpLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (cpLoop blank n) := by
  induction n with
  | zero => simp [cpLoop]
  | succ n ih => simp [cpLoop, cpUnit, Act.noSigned, ih]

@[simp] theorem pfLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (pfLoop blank n) := by
  induction n with
  | zero => simp [pfLoop]
  | succ n ih => simp [pfLoop, pfUnit, Act.noSigned, ih]

@[simp] theorem prLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (prLoop blank n) := by
  induction n with
  | zero => simp [prLoop]
  | succ n ih => simp [prLoop, prUnit, Act.noSigned, ih]

@[simp] theorem rvLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (rvLoop blank n) := by
  induction n with
  | zero => simp [rvLoop]
  | succ n ih => simp [rvLoop, rvUnit, Act.noSigned, ih]

@[simp] theorem crLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (crLoop blank n) := by
  induction n with
  | zero => simp [crLoop]
  | succ n ih => simp [crLoop, crUnit, Act.noSigned, ih]

@[simp] theorem pvLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (pvLoop blank n) := by
  induction n with
  | zero => simp [pvLoop]
  | succ n ih => simp [pvLoop, pvUnit, Act.noSigned, ih]

@[simp] theorem frProg_noSigned (blank endSym mark : Fin sc)
    (orcB : Tapes sc → Bool) (k n Fo Fr : ℕ) (ts : Tapes sc) :
    NoSigned (frProg blank endSym mark orcB k n Fo Fr ts) := by
  simp [frProg, loadR]

@[simp] theorem repoProg_noSigned (blank : Fin sc) (P R : ℕ) :
    NoSigned (repoProg blank P R) := by simp [repoProg]

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
      spClosedProg blank endSym mark orc orc2 k n
        (rOf (afterFr blank endSym mark orcB k n Fo Fr ts))
        (afterRepo blank endSym mark orcB k n Fo Fr ts))

/-- **主定理（外側 1 反復のテープ実現とコスト）**：`A = 6k + 100`, `B = 4k + 10`。
入口と出口の追加3カウンタはすべてゼロ。初期化と消去の動作数も含む。
終状態は `Cf = p₁`、`Cr = r`、`Cs` は不変で、第 2 周期が見つかれば `Cp = p₂`。
`Ce` は「第 2 周期が見つかったか」のフラグ（見つかれば `1`、さもなくば `0`）。 -/
theorem stepProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {s S : ℕ} {ts : Tapes sc} {orcB : Tapes sc → Bool} (hs : s < x.length)
    (horcB : ∀ (p' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', 0, S, 0⟩ ts' →
      (orcB ts' = true ↔ p' < (x.drop s).length))
    (hE : EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, S, 0⟩ ⟨0, 0, 0⟩ ts)
    {p₁ m : ℕ} (hfp : firstPeriod (x.drop s) k = some (p₁, m))
    (horc : ∀ (q' D' E' p' F' S' : ℕ) (g' : Ctr3) (ts' : Tapes sc),
      EncS blank startSym endSym mark x (s + q') (s + p' + q')
        ⟨D', q', E', p', F', S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ g' ts' →
      SignedOK k (extendReach (x.drop s) p₁ (x.length + 1) m) p' q'
        ⟨D', q', E', p', F', S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ g' →
      orc ts' = decide (extendReach (x.drop s) p₁ (x.length + 1) m < p' + q' + 1 ∧
        (k - 1) * p' ≤ q' + 1))
    (horc2 : ∀ (q' D' E' p' S' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x (s + q') (s + p' + q')
        ⟨D', q', E', p', p₁, S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ ts' →
      orc2 ts' = decide (k * p₁ ≤ q' ∧ q' ≤ extendReach (x.drop s) p₁ (x.length + 1) m)) :
    ((stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts).length
        ≤ (6 * k + 100) * decomposeStepWork x k s + (4 * k + 10)
      ∧ (∃ D' q' E' P',
          EncS blank startSym endSym mark x (s + q') (s + P' + q')
            ⟨D', q', E', P', p₁, S, extendReach (x.drop s) p₁ (x.length + 1) m⟩ ⟨0, 0, 0⟩
            (applyActs blank
              (stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) ts)
          ∧ s + P' + q' ≤ x.length
          ∧ q' ≤ secondOuterWork (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m) ((x.drop s).length + 1) 1 0
          ∧ P' ≤ 1 + 2 * secondOuterWork (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m) ((x.drop s).length + 1) 1 0
          ∧ D' ≤ (k + 1) * (2 * secondOuterWork (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m) ((x.drop s).length + 1) 1 0)
          ∧ (∀ p₂, secondPeriod (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m) = some p₂ → P' = p₂)
          ∧ E' = (if (secondPeriod (x.drop s) k p₁
              (extendReach (x.drop s) p₁ (x.length + 1) m)).isSome then 1 else 0))) := by
  have hsle : s ≤ x.length := le_of_lt hs
  have hp₁ : 0 < p₁ := firstOuter_pos (x.drop s) k (x.drop s).length _ 1 p₁ m (by omega) hfp
  obtain ⟨hfr, hfrlen, hwk, hmr, hrle⟩ := frProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) hk hend hmark hs (le_refl _) horcB hE.base hfp
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
  have hfrS := hE.frame (by simp) hfr
  have hrepoS : EncS blank startSym endSym mark x s (s + 1)
      ⟨0, 0, 0, 1, p₁, S, r⟩ ⟨0, 0, 0⟩
      (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) := by
    apply EncS.frame hfrS (by simp)
    exact hrepo
  obtain ⟨hsplen, hspe⟩ := spClosedProg_spec (blank := blank) (startSym := startSym)
    (endSym := endSym) (mark := mark) (x := x) (k := k) (r := r) (orc := orc) (orc2 := orc2)
    hk hend hmark hsle hp₁ (by omega) horc horc2 (by omega) hrepoS
  have happ : applyActs blank
      (stepProg blank endSym mark orcB orc orc2 k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) ts
      = applyActs blank
        (spClosedProg blank endSym mark orc orc2 k (x.drop s).length r
          (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts))
        (afterRepo blank endSym mark orcB k (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) := by
    rw [stepProg, applyActs_append, applyActs_append, hrOf]
    simp only [afterRepo, hrOf]
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
    obtain ⟨A, hA⟩ : ∃ A, 6 * k + 100 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, 2 * k + 32 = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, 6 * k + 50 = C := ⟨_, rfl⟩
    rw [hB] at hfrlen
    rw [hC] at hsplen
    rw [hA]
    have hexp : A * (FO + (ER + SO)) = A * FO + A * ER + A * SO := by ring
    have h1 : B * FO + 39 * FO ≤ A * FO := by
      calc B * FO + 39 * FO = (B + 39) * FO := by ring
        _ ≤ A * FO := Nat.mul_le_mul_right FO (by omega)
    have h2 : C * SO ≤ A * SO := Nat.mul_le_mul_right SO (by omega)
    have h3 : 14 * ER ≤ A * ER := Nat.mul_le_mul_right ER (by omega)
    have h4 : 11 * r ≤ 11 * m + 11 * ER := by omega
    have h5 : 11 * m + 17 * p₁ ≤ 39 * FO := by
      have : m ≤ 2 * FO := by omega
      omega
    omega
  · rw [hrdef]
    obtain ⟨q', E', P', hEnc, hfit', hq', hP', hp2, hflag⟩ := hspe
    exact ⟨0, q', E', P', by rw [happ]; exact hEnc, hfit', hq', hP', by omega, hp2, hflag⟩

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
`A = 17k + 36`, `B = k + 4`：総動作数は `A * stripLoop2Work + B` 以下
（1 反復あたりの定数 `k+4` は、その反復の `firstOuterWork ≥ 1` に付け替えてある）。
終状態では `Cs` が新しい切断 `stripLoop2 x k bound fuel s` を保持する（`Cf`、`Cr` は不変）。 -/
theorem stripProg2_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    {bound n F : ℕ} (hn : x.length ≤ n)
    (horcB : ∀ (s' p' : ℕ) (ts' : Tapes sc),
      Enc blank startSym endSym mark x s' (s' + p') ⟨(k - 1) * p', 0, 0, p', F, s', 0⟩ ts' →
      (orcB ts' = true ↔ p' < bound)) :
    ∀ (fuel s : ℕ) (ts : Tapes sc), s ≤ x.length →
      Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ts →
      ((stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1) fuel ts).length
          ≤ (17 * k + 36) * stripLoop2Work x k bound fuel s + (k + 4)
        ∧ (∃ P, stripLoop2 x k bound fuel s + P ≤ x.length ∧
            P ≤ 1 + stripLoop2Work x k bound fuel s ∧
            Enc blank startSym endSym mark x (stripLoop2 x k bound fuel s)
              (stripLoop2 x k bound fuel s + P)
              ⟨(k - 1) * P, 0, 0, P, F, stripLoop2 x k bound fuel s, 0⟩
              (applyActs blank
                (stripProg2 blank endSym mark orcB k n (x.length + 1) (x.length + 1)
                  fuel ts) ts))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s ts _ hE
      refine ⟨by simp [stripProg2, stripLoop2Work], ⟨0, ?_, by omega, ?_⟩⟩
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
        refine ⟨?_, ⟨0, ?_, by omega, ?_⟩⟩
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
          (bound := bound) (Fo := x.length + 1) (n := n) (F := F) (S := s) (R := 0)
          hk hend hmark hslt hnn (horcB s) hE
        obtain ⟨FO, hFO⟩ : ∃ FO, firstOuterWork (x.drop s) k bound (x.length + 1) 1 = FO :=
          ⟨_, rfl⟩
        rw [hFO] at hfcost
        rcases hfo : firstOuter (x.drop s) k bound (x.length + 1) 1 with _ | ⟨p, m⟩
        · -- 失敗：切断はそのまま
          obtain ⟨P, hP1, hP2, hP4, hP3⟩ := hfnone hfo
          rw [hFO] at hP4
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
          refine ⟨?_, ⟨P, ?_, ?_, ?_⟩⟩
          · rw [hprog, stripLoop2Work]
            simp only [hfo, hFO, Nat.add_zero]
            have hmono : (2 * k + 22) * FO ≤ (17 * k + 36) * FO :=
              Nat.mul_le_mul_right FO (by omega)
            omega
          · rw [stripLoop2]
            simp only [hfo]
            omega
          · rw [stripLoop2Work]
            simp only [hfo, hFO, Nat.add_zero]
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
            (bound := bound) (Fo := x.length + 1) (n := n) (F := F) (S := s)
            hk hend hmark hslt hnn (horcB s) hE hfo
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
              (s + (r - k * p + 1)) ⟨0, 0, 0, 0, F, s + (r - k * p + 1), 0⟩
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
            obtain ⟨A, hA⟩ : ∃ A, 17 * k + 36 = A := ⟨_, rfl⟩
            rw [hA] at hrc ⊢
            have hFO1 : 1 ≤ FO := by
              rw [← hFO]; exact firstOuterWork_pos (x.drop s) k bound (x.length + 1) 1 p m hfo
            have hpFO : p ≤ FO := by
              have : p ≤ (k - 1) * p := Nat.le_mul_of_pos_left p (by omega)
              omega
            have hkpFO : k * p ≤ k * FO := Nat.mul_le_mul_left k hpFO
            have hexp : A * (FO + (ER + W2)) = A * FO + A * ER + A * W2 := by ring
            have hkFO : 14 * (k * FO) ≤ (14 * k) * FO := by
              have : 14 * (k * FO) = (14 * k) * FO := by ring
              omega
            have hm1 : (2 * k + 32) * FO + (14 * k) * FO + (k + 4) ≤ A * FO := by
              have e1 : (2 * k + 32) * FO + (14 * k) * FO = (16 * k + 32) * FO := by ring
              have e2 : (k + 4) ≤ (k + 4) * FO := Nat.le_mul_of_pos_right _ (by omega)
              have e3 : (16 * k + 32) * FO + (k + 4) * FO = A * FO := by rw [← hA]; ring
              omega
            have hm2 : 14 * ER ≤ A * ER := Nat.mul_le_mul_right ER (by omega)
            have hrkp : r ≤ k * p + ER := by omega
            have hkp2 : 11 * r + 3 * (k * p) ≤ 14 * (k * FO) + 11 * ER := by omega
            omega
          · rw [hprog, applyActs_append, hs', stripLoop2Work]
            simp only [hfo, hFO, hER', hr']
            obtain ⟨P', hP'1, hP'3, hP'2⟩ := hre
            refine ⟨P', hP'1, ?_, hP'2⟩
            refine Nat.le_trans hP'3 (Nat.add_le_add_left ?_ 1)
            exact Nat.le_trans (Nat.le_add_left _ ER) (Nat.le_add_left _ FO)


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


/-! ## 14. 外側ループ `decomposeLoop2` のテープ実現 -/

section Outer2

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

/-! ### 14.1 追加のカウンタ／ヘッド転送 -/

/-- `Cq` を 1 減らして `V1`/`V2` を 1 左へ（4 動作）。 -/
def qvUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cq blank .left, Act.Cq blank .stay, Act.V1 .left, Act.V2 .left]

def qvLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => qvUnit blank ++ qvLoop blank n

@[simp] theorem qvLoop_length (blank : Fin sc) (n : ℕ) : (qvLoop blank n).length = 4 * n := by
  induction n with
  | zero => simp [qvLoop]
  | succ n ih => simp only [qvLoop, List.length_append, qvUnit, ih]; simp; omega

theorem applyActs_qvUnit (ts : Tapes sc) :
    applyActs blank (qvUnit blank) ts =
      { ts with
        Cq := Tape.step blank (Tape.step blank ts.Cq blank .left) blank .stay
        V1 := Tape.step blank ts.V1 ts.V1.focus .left
        V2 := Tape.step blank ts.V2 ts.V2.focus .left } := rfl

theorem qvLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x (a + n) (b + n) ⟨D, Q + n, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (qvLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [qvLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x (a + n + 1) (b + n + 1)
          ⟨D, (Q + n) + 1, E, P, F, S, R⟩ ts := by
        have e1 : a + (n + 1) = a + n + 1 := by omega
        have e2 : b + (n + 1) = b + n + 1 := by omega
        have e3 : Q + (n + 1) = (Q + n) + 1 := by omega
        rw [e1, e2, e3] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x (a + n) (b + n)
          ⟨D, Q + n, E, P, F, S, R⟩ (applyActs blank (qvUnit blank) ts) := by
        rw [applyActs_qvUnit]
        exact ⟨pat_left hE'.v1, pat_left hE'.v2, hE'.cd,
          by simpa using Tape.counter'_dec (n := Q + n) hE'.cq,
          hE'.ce, hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [qvLoop, applyActs_append]
      exact this

/-- `Cf` を `n` 回減らす（2 動作／回）。 -/
def fzUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cf blank .left, Act.Cf blank .stay]

def fzLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => fzUnit blank ++ fzLoop blank n

@[simp] theorem fzLoop_length (blank : Fin sc) (n : ℕ) : (fzLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [fzLoop]
  | succ n ih => simp only [fzLoop, List.length_append, fzUnit, ih]; simp; omega

theorem applyActs_fzUnit (ts : Tapes sc) :
    applyActs blank (fzUnit blank) ts =
      { ts with
        Cf := Tape.step blank (Tape.step blank ts.Cf blank .left) blank .stay } := rfl

theorem fzLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (fzLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [fzLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, (F + n) + 1, S, R⟩ ts := by
        have e1 : F + (n + 1) = (F + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩
          (applyActs blank (fzUnit blank) ts) := by
        rw [applyActs_fzUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, hE'.ce, hE'.cp,
          by simpa using Tape.counter'_dec (n := F + n) hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [fzLoop, applyActs_append]
      exact this

/-- `Ce` を `n` 回減らす（2 動作／回）。 -/
def ezUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Ce blank .left, Act.Ce blank .stay]

def ezLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => ezUnit blank ++ ezLoop blank n

@[simp] theorem ezLoop_length (blank : Fin sc) (n : ℕ) : (ezLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [ezLoop]
  | succ n ih => simp only [ezLoop, List.length_append, ezUnit, ih]; simp; omega

theorem applyActs_ezUnit (ts : Tapes sc) :
    applyActs blank (ezUnit blank) ts =
      { ts with
        Ce := Tape.step blank (Tape.step blank ts.Ce blank .left) blank .stay } := rfl

theorem ezLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (ezLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [ezLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, (E + n) + 1, P, F, S, R⟩ ts := by
        have e1 : E + (n + 1) = (E + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E + n, P, F, S, R⟩
          (applyActs blank (ezUnit blank) ts) := by
        rw [applyActs_ezUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq,
          by simpa using Tape.counter'_dec (n := E + n) hE'.ce, hE'.cp, hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [ezLoop, applyActs_append]
      exact this

/-- `Cr` を `n` 回減らす（2 動作／回）。 -/
def rzUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cr blank .left, Act.Cr blank .stay]

def rzLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => rzUnit blank ++ rzLoop blank n

@[simp] theorem rzLoop_length (blank : Fin sc) (n : ℕ) : (rzLoop blank n).length = 2 * n := by
  induction n with
  | zero => simp [rzLoop]
  | succ n ih => simp only [rzLoop, List.length_append, rzUnit, ih]; simp; omega

theorem applyActs_rzUnit (ts : Tapes sc) :
    applyActs blank (rzUnit blank) ts =
      { ts with
        Cr := Tape.step blank (Tape.step blank ts.Cr blank .left) blank .stay } := rfl

theorem rzLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩
        (applyActs blank (rzLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [rzLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, (R + n) + 1⟩ ts := by
        have e1 : R + (n + 1) = (R + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R + n⟩
          (applyActs blank (rzUnit blank) ts) := by
        rw [applyActs_rzUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, hE'.ce, hE'.cp, hE'.cf, hE'.cs,
          by simpa using Tape.counter'_dec (n := R + n) hE'.cr⟩
      have := ih a b D Q E P F S R _ hstep
      simp only [rzLoop, applyActs_append]
      exact this

/-- `Cp` を 1 減らして `Cf` を 1 増やし、`V2` を 1 左へ（4 動作）。 -/
def pfvUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cp blank .left, Act.Cp blank .stay, Act.Cf blank .right, Act.V2 .left]

def pfvLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => pfvUnit blank ++ pfvLoop blank n

@[simp] theorem pfvLoop_length (blank : Fin sc) (n : ℕ) : (pfvLoop blank n).length = 4 * n := by
  induction n with
  | zero => simp [pfvLoop]
  | succ n ih => simp only [pfvLoop, List.length_append, pfvUnit, ih]; simp; omega

theorem applyActs_pfvUnit (ts : Tapes sc) :
    applyActs blank (pfvUnit blank) ts =
      { ts with
        Cp := Tape.step blank (Tape.step blank ts.Cp blank .left) blank .stay
        Cf := Tape.step blank ts.Cf blank .right
        V2 := Tape.step blank ts.V2 ts.V2.focus .left } := rfl

theorem pfvLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a (b + n) ⟨D, Q, E, P + n, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩
        (applyActs blank (pfvLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [pfvLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a (b + n + 1)
          ⟨D, Q, E, (P + n) + 1, F, S, R⟩ ts := by
        have e1 : b + (n + 1) = b + n + 1 := by omega
        have e2 : P + (n + 1) = (P + n) + 1 := by omega
        rw [e1, e2] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a (b + n)
          ⟨D, Q, E, P + n, F + 1, S, R⟩ (applyActs blank (pfvUnit blank) ts) := by
        rw [applyActs_pfvUnit]
        exact ⟨hE'.v1, pat_left hE'.v2, hE'.cd, hE'.cq, hE'.ce,
          by simpa using Tape.counter'_dec (n := P + n) hE'.cp,
          Tape.counter'_inc hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E P (F + 1) S R _ hstep
      have e3 : F + 1 + n = F + (n + 1) := by omega
      rw [e3] at this
      simp only [pfvLoop, applyActs_append]
      exact this

/-- `Cf` を 1 減らして `Cp` を 1 増やす（3 動作）。 -/
def fcUnit (blank : Fin sc) : List (Act sc) :=
  [Act.Cf blank .left, Act.Cf blank .stay, Act.Cp blank .right]

def fcLoop (blank : Fin sc) : ℕ → List (Act sc)
  | 0 => []
  | n + 1 => fcUnit blank ++ fcLoop blank n

@[simp] theorem fcLoop_length (blank : Fin sc) (n : ℕ) : (fcLoop blank n).length = 3 * n := by
  induction n with
  | zero => simp [fcLoop]
  | succ n ih => simp only [fcLoop, List.length_append, fcUnit, ih]; simp; omega

theorem applyActs_fcUnit (ts : Tapes sc) :
    applyActs blank (fcUnit blank) ts =
      { ts with
        Cf := Tape.step blank (Tape.step blank ts.Cf blank .left) blank .stay
        Cp := Tape.step blank ts.Cp blank .right } := rfl

theorem fcLoop_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F + n, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P + n, F, S, R⟩
        (applyActs blank (fcLoop blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [fcLoop] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hE' : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, (F + n) + 1, S, R⟩ ts := by
        have e1 : F + (n + 1) = (F + n) + 1 := by omega
        rw [e1] at hE; exact hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E, P + 1, F + n, S, R⟩
          (applyActs blank (fcUnit blank) ts) := by
        rw [applyActs_fcUnit]
        exact ⟨hE'.v1, hE'.v2, hE'.cd, hE'.cq, hE'.ce, Tape.counter'_inc hE'.cp,
          by simpa using Tape.counter'_dec (n := F + n) hE'.cf, hE'.cs, hE'.cr⟩
      have := ih a b D Q E (P + 1) F S R _ hstep
      have e3 : P + 1 + n = P + (n + 1) := by omega
      rw [e3] at this
      simp only [fcLoop, applyActs_append]
      exact this

/-- `Cs` を `n` 回増やす（1 動作／回）。 -/
def sIncs (blank : Fin sc) (n : ℕ) : List (Act sc) := List.replicate n (Act.Cs blank .right)

@[simp] theorem sIncs_length (blank : Fin sc) (n : ℕ) : (sIncs blank n).length = n := by
  simp [sIncs]

theorem sIncs_enc : ∀ (n a b D Q E P F S R : ℕ) (ts : Tapes sc),
    Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S, R⟩ ts →
      Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S + n, R⟩
        (applyActs blank (sIncs blank n) ts) := by
  intro n
  induction n with
  | zero => intro a b D Q E P F S R ts hE; simpa [sIncs] using hE
  | succ n ih =>
      intro a b D Q E P F S R ts hE
      have hstep : Enc blank startSym endSym mark x a b ⟨D, Q, E, P, F, S + 1, R⟩
          (applyAct blank ts (Act.Cs blank .right)) :=
        ⟨hE.v1, hE.v2, hE.cd, hE.cq, hE.ce, hE.cp, hE.cf, Tape.counter'_inc hE.cs, hE.cr⟩
      have := ih a b D Q E P F (S + 1) R _ hstep
      have e1 : S + 1 + n = S + (n + 1) := by omega
      rw [e1] at this
      simpa [sIncs, List.replicate_succ] using this

/-! ### 14.2 テープ読み出しだけで決まるオラクル -/

/-- `Cd` の読み出し。 -/
def dOf (ts : Tapes sc) : ℕ := ts.Cd.left.length - 1

theorem dOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : dOf ts = c.d := by
  simpa [dOf] using ctr_len hE.cd

/-- `Cs` の読み出し。 -/
def sOf (ts : Tapes sc) : ℕ := ts.Cs.left.length - 1

theorem sOf_eq {a b : ℕ} {c : Ctr} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x a b c ts) : sOf ts = c.s := by
  simpa [sOf] using ctr_len hE.cs

/-- `firstPeriod`（`bound = |v|`）用のオラクル：番人テストそのもの。 -/
def orcEnd (endSym : Fin sc) (ts : Tapes sc) : Bool := decide (Tape.read ts.V2 ≠ endSym)

/-- 削除ループ用のオラクル：`Cp` と `Cf` の平行歩行。 -/
def orcCf (ts : Tapes sc) : Bool := decide (pOf ts < fOf ts)

theorem orcEnd_spec (hend : endSym ∉ x) {s p' F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', F, S, R⟩ ts) :
    (orcEnd endSym ts = true ↔ p' < (x.drop s).length) := by
  have h1 : Tape.read ts.V2 = endSym ↔ s + p' = x.length := read_pat_end_iff hend hE.v2
  have h2 : s + p' ≤ x.length := pat_le hE.v2
  have hdrop : (x.drop s).length = x.length - s := by simp
  constructor
  · intro hc
    have : Tape.read ts.V2 ≠ endSym := by simpa [orcEnd] using hc
    have : s + p' ≠ x.length := fun hcc => this (h1.2 hcc)
    rw [hdrop]; omega
  · intro hc
    rw [hdrop] at hc
    have : s + p' ≠ x.length := by omega
    simp only [orcEnd, decide_eq_true_eq]
    exact fun hcc => this (h1.1 hcc)

theorem orcCf_spec {s p' F S R : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s (s + p') ⟨(k - 1) * p', 0, 0, p', F, S, R⟩ ts) :
    (orcCf ts = true ↔ p' < F) := by
  simp [orcCf, pOf_eq hE, fOf_eq hE]

end Outer2


/-! ### 14.3 第 2 相の後始末 -/

section Outer2b

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

/-- **第 2 相の後始末（第 2 周期が見つかったとき）**。
`stepProg` の終状態 `V1 = s+q`, `V2 = s+p₂+q`, `Cd = d`, `Cq = q`, `Cp = p₂`, `Cf = p₁`,
`Cs = s`, `Cr = r` から、削除ループの入口 `V1 = V2 = s`, `Cf = p₂`, 他は `0` へ戻す。
動作数 `4q + 2p₁ + 4p₂ + 2r + 2d`。 -/
def resetProg (blank : Fin sc) (Q P₁ P₂ R D : ℕ) : List (Act sc) :=
  qvLoop blank Q ++ (fzLoop blank P₁ ++ (pfvLoop blank P₂ ++
    (rzLoop blank R ++ dzLoop blank D)))

@[simp] theorem resetProg_length (blank : Fin sc) (Q P₁ P₂ R D : ℕ) :
    (resetProg blank Q P₁ P₂ R D).length = 4 * Q + 2 * P₁ + 4 * P₂ + 2 * R + 2 * D := by
  simp only [resetProg, List.length_append, qvLoop_length, fzLoop_length, pfvLoop_length,
    rzLoop_length, dzLoop_length]
  omega

theorem resetProg_enc {s q p₁ p₂ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p₂ + q) ⟨d, q, 0, p₂, p₁, s, r⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, p₂, s, 0⟩
      (applyActs blank (resetProg blank q p₁ p₂ r d) ts) := by
  have h1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) q s (s + p₂) d 0 0 p₂ p₁ s r ts (by simpa using hE)
  have h2 := fzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₁ s (s + p₂) d 0 0 p₂ 0 s r _ (by simpa using h1)
  have h3 := pfvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₂ s s d 0 0 0 0 s r _ (by simpa using h2)
  have h4 := rzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) r s s d 0 0 0 (0 + p₂) s 0 _ (by simpa using h3)
  have h5 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) d s s 0 0 0 0 (0 + p₂) s 0 _ (by simpa using h4)
  rw [resetProg, applyActs_append, applyActs_append, applyActs_append, applyActs_append]
  simpa using h5

/-- **第 2 相の後始末（第 2 周期が見つからなかったとき）**。終状態を
`Cs = s`, `Cp = p₁`, `Cr = r`（他は `0`）にそろえる。動作数 `4q + 3P + 3p₁ + 2d`。 -/
def swapProg (blank : Fin sc) (Q P P₁ D : ℕ) : List (Act sc) :=
  qvLoop blank Q ++ (pvLoop blank P ++ (fcLoop blank P₁ ++ dzLoop blank D))

@[simp] theorem swapProg_length (blank : Fin sc) (Q P P₁ D : ℕ) :
    (swapProg blank Q P P₁ D).length = 4 * Q + 3 * P + 3 * P₁ + 2 * D := by
  simp only [swapProg, List.length_append, qvLoop_length, pvLoop_length, fcLoop_length,
    dzLoop_length]
  omega

theorem swapProg_enc {s q p p₁ r d : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q) (s + p + q) ⟨d, q, 0, p, p₁, s, r⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, p₁, 0, s, r⟩
      (applyActs blank (swapProg blank q p p₁ d) ts) := by
  have h1 := qvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) q s (s + p) d 0 0 p p₁ s r ts (by simpa using hE)
  have h2 := pvLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p s s d 0 0 0 p₁ s r _ (by simpa using h1)
  have h3 := fcLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) p₁ s s d 0 0 0 0 s r _ (by simpa using h2)
  have h4 := dzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) d s s 0 0 0 (0 + p₁) 0 s r _ (by simpa using h3)
  rw [swapProg, applyActs_append, applyActs_append, applyActs_append]
  simpa using h4

/-- 燃料切れの枝：`decomposeLoop2 x k 0 s = (|x|, 0, 0)` に合わせて `Cs := |x|` にする。 -/
def bottomProg (blank : Fin sc) (n : ℕ) (ts : Tapes sc) : List (Act sc) :=
  sIncs blank (n - sOf ts)

theorem bottomProg_enc {n s F : ℕ} {ts : Tapes sc} (hn : n = x.length) (hs : s ≤ x.length)
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ts) :
    Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, x.length, 0⟩
      (applyActs blank (bottomProg blank n ts) ts) := by
  have hsOf : sOf ts = s := sOf_eq hE
  rw [bottomProg, hsOf]
  have h := sIncs_enc (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (n - s) s s 0 0 0 0 F s 0 ts hE
  have e : s + (n - s) = x.length := by omega
  rw [e] at h
  exact h

theorem bottomProg_length {n s F : ℕ} {ts : Tapes sc}
    (hE : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, F, s, 0⟩ ts) :
    (bottomProg blank n ts).length = n - s := by
  rw [bottomProg, sIncs_length, sOf_eq hE]

end Outer2b


/-! ### 14.4 外側ループのプログラム -/

section Outer2c

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

/-- `stepProg` の `fpProg` を除いた残り。 -/
def stepTail (blank endSym mark : Fin sc) (orcB orc orc2 : Tapes sc → Bool) (k n Fo Fr : ℕ)
    (ts : Tapes sc) : List (Act sc) :=
  frTail blank endSym Fr (applyActs blank (fpProg blank endSym mark orcB k n Fo ts) ts) ++
    (repoProg blank (pOf (afterFr blank endSym mark orcB k n Fo Fr ts))
        (rOf (afterFr blank endSym mark orcB k n Fo Fr ts)) ++
      spClosedProg blank endSym mark orc orc2 k n
        (rOf (afterFr blank endSym mark orcB k n Fo Fr ts))
        (afterRepo blank endSym mark orcB k n Fo Fr ts))

theorem stepProg_split (blank endSym mark : Fin sc) (orcB orc orc2 : Tapes sc → Bool)
    (k n Fo Fr : ℕ) (ts : Tapes sc) :
    stepProg blank endSym mark orcB orc orc2 k n Fo Fr ts
      = fpProg blank endSym mark orcB k n Fo ts ++
        stepTail blank endSym mark orcB orc orc2 k n Fo Fr ts := by
  rw [stepProg, stepTail, frProg_split]
  simp [List.append_assoc]

/-- 第 2 相の内側中断オラクル（`Cr`, `Cp`, `Cq` の読み出しだけで決まる）。 -/
def orcR (k : ℕ) (ts : Tapes sc) : Bool :=
  decide (rOf ts < pOf ts + qOf ts + 1 ∧ (k - 1) * pOf ts ≤ qOf ts + 1)

/-- 第 2 相の周期ずらし判定（`Cf`, `Cq`, `Cr` の読み出しだけで決まる）。 -/
def orc2R (k : ℕ) (ts : Tapes sc) : Bool :=
  decide (k * fOf ts ≤ qOf ts ∧ qOf ts ≤ rOf ts)

theorem orcR_spec {s q' D' E' p' F' S' r : ℕ} {ts' : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q') (s + p' + q')
      ⟨D', q', E', p', F', S', r⟩ ts') :
    orcR k ts' = decide (r < p' + q' + 1 ∧ (k - 1) * p' ≤ q' + 1) := by
  simp only [orcR, rOf_eq hE, pOf_eq hE, qOf_eq hE]

theorem orc2R_spec {s q' D' E' p' first S' r : ℕ} {ts' : Tapes sc}
    (hE : Enc blank startSym endSym mark x (s + q') (s + p' + q')
      ⟨D', q', E', p', first, S', r⟩ ts') :
    orc2R k ts' = decide (k * first ≤ q' ∧ q' ≤ r) := by
  simp only [orc2R, fOf_eq hE, qOf_eq hE, rOf_eq hE]

/-! #### 部品の合成 -/

def dLen (n : ℕ) (ts : Tapes sc) : ℕ := n - sOf ts

def dFp (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : List (Act sc) :=
  fpProg blank endSym mark (orcEnd endSym) k (dLen n ts) (dLen n ts + 1) ts

def dFpS (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : Tapes sc :=
  applyActs blank (dFp blank endSym mark k n ts) ts

def dTl (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : List (Act sc) :=
  stepTail blank endSym mark (orcEnd endSym) (orcR k) (orc2R k) k
    (dLen n ts) (dLen n ts + 1) (n + 1) ts

def dTlS (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) : Tapes sc :=
  applyActs blank (dTl blank endSym mark k n ts) (dFpS blank endSym mark k n ts)

/-- 第 2 周期の有無を決めるオラクル：`Ce` のフラグの読み出しそのもの。 -/
def orcE (ts : Tapes sc) : Bool := decide (0 < eOf ts)

/-- フラグ `Ce` を消してから削除ループの入口へ戻す。 -/
def dRst (blank : Fin sc) (t : Tapes sc) : List (Act sc) :=
  ezLoop blank (eOf t) ++ resetProg blank (qOf t) (fOf t) (pOf t) (rOf t) (dOf t)

def dRstS (blank : Fin sc) (t : Tapes sc) : Tapes sc := applyActs blank (dRst blank t) t

def dStr (blank endSym mark : Fin sc) (k n : ℕ) (t : Tapes sc) : List (Act sc) :=
  stripProg2 blank endSym mark orcCf k n (n + 1) (n + 1) (n + 1) (dRstS blank t)

def dStrS (blank endSym mark : Fin sc) (k n : ℕ) (t : Tapes sc) : Tapes sc :=
  applyActs blank (dStr blank endSym mark k n t) (dRstS blank t)

def dCln (blank endSym mark : Fin sc) (k n : ℕ) (t : Tapes sc) : List (Act sc) :=
  cleanProg blank k (pOf (dStrS blank endSym mark k n t)) ++ fzLoop blank (pOf t)

def dBody (blank endSym mark : Fin sc) (k n : ℕ) (t : Tapes sc) : List (Act sc) :=
  dRst blank t ++ (dStr blank endSym mark k n t ++ dCln blank endSym mark k n t)

def dBodyS (blank endSym mark : Fin sc) (k n : ℕ) (t : Tapes sc) : Tapes sc :=
  applyActs blank (dBody blank endSym mark k n t) t

/-- フラグ `Ce` を消してから第 2 周期なしの終状態へそろえる。 -/
def dSwap (blank : Fin sc) (t : Tapes sc) : List (Act sc) :=
  ezLoop blank (eOf t) ++ swapProg blank (qOf t) (pOf t) (fOf t) (dOf t)

/-- **`decomposeLoop2` のテープ動作列生成**。外部オラクル引数はないが、
`orcR` / `orc2R` などはテープのリスト長を参照する。この定義自体は有限制御の
プログラムではなく、そのコンパイルと計算量保存は別途必要である。 -/
def decProg (blank endSym mark : Fin sc) (k n : ℕ) :
    ℕ → Tapes sc → List (Act sc)
  | 0, ts => bottomProg blank n ts
  | fuel + 1, ts =>
      if Tape.read ts.V2 = endSym then [] else
      dFp blank endSym mark k n ts ++
        (if probe blank (dFpS blank endSym mark k n ts).Cd = mark then
           dTl blank endSym mark k n ts ++
             (if orcE (dTlS blank endSym mark k n ts) then
                dBody blank endSym mark k n (dTlS blank endSym mark k n ts) ++
                  decProg blank endSym mark k n fuel
                    (dBodyS blank endSym mark k n (dTlS blank endSym mark k n ts))
              else dSwap blank (dTlS blank endSym mark k n ts))
         else cleanProg blank k (pOf (dFpS blank endSym mark k n ts)))

end Outer2c


/-! ### 14.5 外側ループの主定理 -/

@[simp] theorem rv2Loop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (rv2Loop blank n) := by
  induction n with
  | zero => simp [rv2Loop]
  | succ n ih => simp [rv2Loop, rv2Unit, Act.noSigned, ih]

@[simp] theorem ecLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (ecLoop blank n) := by
  induction n with
  | zero => simp [ecLoop]
  | succ n ih => simp [ecLoop, ecUnit, Act.noSigned, ih]

@[simp] theorem qpLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (qpLoop blank n) := by
  induction n with
  | zero => simp [qpLoop]
  | succ n ih => simp [qpLoop, qpUnit, Act.noSigned, ih]

@[simp] theorem csLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (csLoop blank n) := by
  induction n with
  | zero => simp [csLoop]
  | succ n ih => simp [csLoop, csUnit, Act.noSigned, ih]

@[simp] theorem pzLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (pzLoop blank n) := by
  induction n with
  | zero => simp [pzLoop]
  | succ n ih => simp [pzLoop, pzUnit, Act.noSigned, ih]

@[simp] theorem dzLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (dzLoop blank n) := by
  induction n with
  | zero => simp [dzLoop]
  | succ n ih => simp [dzLoop, dzUnit, Act.noSigned, ih]

@[simp] theorem qvLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (qvLoop blank n) := by
  induction n with
  | zero => simp [qvLoop]
  | succ n ih => simp [qvLoop, qvUnit, Act.noSigned, ih]

@[simp] theorem fzLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (fzLoop blank n) := by
  induction n with
  | zero => simp [fzLoop]
  | succ n ih => simp [fzLoop, fzUnit, Act.noSigned, ih]

@[simp] theorem ezLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (ezLoop blank n) := by
  induction n with
  | zero => simp [ezLoop]
  | succ n ih => simp [ezLoop, ezUnit, Act.noSigned, ih]

@[simp] theorem rzLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (rzLoop blank n) := by
  induction n with
  | zero => simp [rzLoop]
  | succ n ih => simp [rzLoop, rzUnit, Act.noSigned, ih]

@[simp] theorem pfvLoop_noSigned (blank : Fin sc) (n : ℕ) :
    NoSigned (pfvLoop blank n) := by
  induction n with
  | zero => simp [pfvLoop]
  | succ n ih => simp [pfvLoop, pfvUnit, Act.noSigned, ih]

@[simp] theorem subKLoop_noSigned (blank : Fin sc) (p n : ℕ) :
    NoSigned (subKLoop blank p n) := by
  induction n with
  | zero => simp [subKLoop]
  | succ n ih => simp [subKLoop, ih]

@[simp] theorem stripProg2_noSigned (blank endSym mark : Fin sc)
    (orcB : Tapes sc → Bool) (k n Fo Fr fuel : ℕ) (ts : Tapes sc) :
    NoSigned (stripProg2 blank endSym mark orcB k n Fo Fr fuel ts) := by
  induction fuel generalizing ts with
  | zero => simp [stripProg2]
  | succ fuel ih =>
      simp only [stripProg2]
      split_ifs <;> simp_all [stripStep, frTail, loadR, advanceProg, Act.noSigned]

@[simp] theorem dBody_noSigned (blank endSym mark : Fin sc) (k n : ℕ) (ts : Tapes sc) :
    NoSigned (dBody blank endSym mark k n ts) := by
  simp [dBody, dRst, resetProg, dStr, dCln, cleanProg]

section Outer2d

variable {blank startSym endSym mark : Fin sc} {x : List (Fin sc)} {k : ℕ}

/-- **主定理（`decomposeLoop2` のテープ実現とコスト）**。
`A = 23k + 120`, `B = 7k + 23`, `C = |x|+1`：1 反復あたりのオーバーヘッドは
`|x|` に依存しない定数 `B` に落としてあるので、`fuel = |x|+1` でも全体は
`A * decomposeLoop2Work + B * (|x|+1) + (|x|+1)` に収まる。 -/
theorem decProg_spec (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank) :
    ∀ (fuel s : ℕ) (ts : Tapes sc), s ≤ x.length →
      EncS blank startSym endSym mark x s s ⟨0, 0, 0, 0, 0, s, 0⟩ ⟨0, 0, 0⟩ ts →
      ((decProg blank endSym mark k x.length fuel ts).length
          ≤ (23 * k + 120) * decomposeLoop2Work x k fuel s
            + (7 * k + 23) * fuel + (x.length + 1)
        ∧ (∃ a b D Q E, Enc blank startSym endSym mark x a b
            ⟨D, Q, E, (decomposeLoop2 x k fuel s).2.1, 0,
              (decomposeLoop2 x k fuel s).1, (decomposeLoop2 x k fuel s).2.2⟩
            (applyActs blank
              (decProg blank endSym mark k x.length fuel ts) ts))) := by
  intro fuel
  induction fuel with
  | zero =>
      intro s ts hs hES
      have hE := hES.base
      refine ⟨?_, ⟨s, s, 0, 0, 0, ?_⟩⟩
      · rw [decProg, bottomProg_length hE, decomposeLoop2Work]
        omega
      · rw [decProg, decomposeLoop2]
        exact bottomProg_enc (n := x.length) rfl hs hE
  | succ fuel ih =>
      intro s ts hs hES
      have hE := hES.base
      have hsOf : sOf ts = s := sOf_eq hE
      have hdl : dLen x.length ts = (x.drop s).length := by
        simp only [dLen, hsOf, List.length_drop]
      by_cases hend2 : Tape.read ts.V2 = endSym
      · -- `s = |x|`：`firstPeriod` は `none`
        have heq : s = x.length := by
          have := (read_pat_end_iff hend hE.v2).1 hend2
          omega
        have hdrop : (x.drop s).length = 0 := by simp; omega
        have hfp : firstPeriod (x.drop s) k = none := by
          rw [firstPeriod, firstOuter, if_neg (by rw [hdrop]; omega)]
        have hloop : decomposeLoop2 x k (fuel + 1) s = (s, 0, 0) := by
          rw [decomposeLoop2]; simp only [hfp]
        refine ⟨?_, ⟨s, s, 0, 0, 0, ?_⟩⟩
        · rw [decProg, if_pos hend2]; simp
        · rw [decProg, if_pos hend2, applyActs_nil, hloop]
          exact hE
      · have hslt : s < x.length := by
          have hne : s ≠ x.length := fun hc => hend2 (read_pat_end hE.v2 hc)
          omega
        have horcB : ∀ (p' : ℕ) (ts' : Tapes sc),
            Enc blank startSym endSym mark x s (s + p')
              ⟨(k - 1) * p', 0, 0, p', 0, s, 0⟩ ts' →
            (orcEnd endSym ts' = true ↔ p' < (x.drop s).length) :=
          fun p' ts' hEE => orcEnd_spec hend hEE
        have hfpP : dFp blank endSym mark k x.length ts
            = fpProg blank endSym mark (orcEnd endSym) k (x.drop s).length
                ((x.drop s).length + 1) ts := by
          rw [dFp, hdl]
        obtain ⟨hfcost, hfsome, _, hfnone⟩ := fpProg_spec (blank := blank)
          (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k)
          (bound := (x.drop s).length) (Fo := (x.drop s).length + 1)
          (n := (x.drop s).length) (F := 0) (S := s) (R := 0)
          hk hend hmark hslt (le_refl _) horcB hE
        rw [← hfpP] at hfcost hfsome hfnone
        have hstate : dFpS blank endSym mark k x.length ts
            = applyActs blank (dFp blank endSym mark k x.length ts) ts := rfl
        rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
        · -- `firstPeriod` 失敗
          obtain ⟨P, hP0, hPfit, hPwk, hPenc⟩ := hfnone (by rw [firstPeriod] at hfp; exact hfp)
          have hprobe : ¬ (probe blank (dFpS blank endSym mark k x.length ts).Cd = mark) := by
            intro hc
            rw [hstate] at hc
            have hcd : Tape.CounterView' blank mark
                (applyActs blank (dFp blank endSym mark k x.length ts) ts).Cd
                ((k - 1) * P) := hPenc.cd
            have h0 := (probe_iff hmark hcd).1 hc
            have hle : P ≤ (k - 1) * P := Nat.le_mul_of_pos_left P (by omega)
            omega
          have hprog : decProg blank endSym mark k x.length (fuel + 1) ts
              = dFp blank endSym mark k x.length ts ++
                cleanProg blank k (pOf (dFpS blank endSym mark k x.length ts)) := by
            rw [decProg, if_neg hend2, if_neg hprobe]
          have hpOf : pOf (dFpS blank endSym mark k x.length ts) = P :=
            pOf_eq hPenc
          have hloop : decomposeLoop2 x k (fuel + 1) s = (s, 0, 0) := by
            rw [decomposeLoop2]; simp only [hfp]
          have hwork : decomposeLoop2Work x k (fuel + 1) s = decomposeStepWork x k s := by
            rw [decomposeLoop2Work]; simp only [hfp, Nat.add_zero]
          have hdsw : firstOuterWork (x.drop s) k (x.drop s).length
              ((x.drop s).length + 1) 1 ≤ decomposeStepWork x k s := by
            rw [decomposeStepWork]; simp only [hfp]; omega
          refine ⟨?_, ⟨s, s, 0, 0, 0, ?_⟩⟩
          · rw [hprog, List.length_append, hpOf, cleanProg_length, hwork]
            obtain ⟨FO, hFO⟩ : ∃ FO, firstOuterWork (x.drop s) k (x.drop s).length
                ((x.drop s).length + 1) 1 = FO := ⟨_, rfl⟩
            rw [hFO] at hfcost hdsw hPwk
            obtain ⟨A, hA⟩ : ∃ A, 23 * k + 120 = A := ⟨_, rfl⟩
            obtain ⟨B, hB⟩ : ∃ B, 7 * k + 23 = B := ⟨_, rfl⟩
            rw [hA, hB]
            -- `cleanProg` は `(2k+1) * P`、`P ≤ 1 + FO`
            have hcl : 3 * P + 2 * ((k - 1) * P) = (2 * k + 1) * P := by
              obtain ⟨kk, hkk⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
              subst hkk
              simp only [Nat.add_sub_cancel]
              ring
            have hclP : (2 * k + 1) * P ≤ (2 * k + 1) * (1 + FO) :=
              Nat.mul_le_mul_left _ hPwk
            have hclE : (2 * k + 1) * (1 + FO) = (2 * k + 1) + (2 * k + 1) * FO := by ring
            have hsum : (2 * k + 22) * FO + (2 * k + 1) * FO ≤ A * FO := by
              have : (2 * k + 22) * FO + (2 * k + 1) * FO = (4 * k + 23) * FO := by ring
              have h2 : (4 * k + 23) * FO ≤ A * FO := Nat.mul_le_mul_right FO (by omega)
              omega
            have hmono : A * FO ≤ A * decomposeStepWork x k s := Nat.mul_le_mul_left _ hdsw
            have hconst : (k - 1) + 2 + (2 * k + 1) ≤ B * (fuel + 1) := by
              have h1 : (k - 1) + 2 + (2 * k + 1) ≤ B := by omega
              have h2 : B ≤ B * (fuel + 1) := Nat.le_mul_of_pos_right _ (by omega)
              omega
            have hBfuel : B * (fuel + 1) = B * fuel + B := by ring
            omega
          · rw [hprog, applyActs_append, hloop, hpOf]
            exact cleanProg_enc (blank := blank) (startSym := startSym) (endSym := endSym)
              (mark := mark) (x := x) (k := k) hPenc
        · -- `firstPeriod` 成功
          have hfp' : firstOuter (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1
              = some (p₁, m) := by rw [firstPeriod] at hfp; exact hfp
          obtain ⟨hEnc1, hwk1⟩ := hfsome p₁ m hfp'
          have hprobe : probe blank (dFpS blank endSym mark k x.length ts).Cd = mark := by
            rw [hstate]
            exact (probe_iff hmark hEnc1.cd).2 rfl
          obtain ⟨r, hrdef⟩ : ∃ r, extendReach (x.drop s) p₁ (x.length + 1) m = r := ⟨_, rfl⟩
          have horc : ∀ (q' D' E' p' F' S' : ℕ) (g : Ctr3) (ts' : Tapes sc),
              EncS blank startSym endSym mark x (s + q') (s + p' + q')
                ⟨D', q', E', p', F', S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ g ts' →
              SignedOK k (extendReach (x.drop s) p₁ (x.length + 1) m) p' q'
                ⟨D', q', E', p', F', S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ g →
              orcR k ts' = decide (extendReach (x.drop s) p₁ (x.length + 1) m < p' + q' + 1 ∧
                (k - 1) * p' ≤ q' + 1) :=
            fun q' D' E' p' F' S' g ts' hEE _ => orcR_spec hEE.base
          have horc2 : ∀ (q' D' E' p' S' : ℕ) (ts' : Tapes sc),
              Enc blank startSym endSym mark x (s + q') (s + p' + q')
                ⟨D', q', E', p', p₁, S', extendReach (x.drop s) p₁ (x.length + 1) m⟩ ts' →
              orc2R k ts' = decide (k * p₁ ≤ q' ∧
                q' ≤ extendReach (x.drop s) p₁ (x.length + 1) m) :=
            fun q' D' E' p' S' ts' hEE => orc2R_spec hEE
          obtain ⟨hslen, D', q', E', P', hsEnc, hsfit, hq'b, hP'b, hD'b, hp2, hflag⟩ :=
            stepProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
              (mark := mark) (x := x) (k := k) (orcB := orcEnd endSym) (orc := orcR k)
              (orc2 := orc2R k) hk hend hmark hslt horcB hES hfp horc horc2
          have hsplit : dFp blank endSym mark k x.length ts ++
              dTl blank endSym mark k x.length ts
              = stepProg blank endSym mark (orcEnd endSym) (orcR k) (orc2R k) k
                  (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts := by
            rw [dFp, dTl, hdl, stepProg_split]
          have hTlS : dTlS blank endSym mark k x.length ts
              = applyActs blank (stepProg blank endSym mark (orcEnd endSym) (orcR k) (orc2R k) k
                  (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts) ts := by
            rw [dTlS, dFpS, ← applyActs_append, hsplit]
          rw [← hTlS] at hsEnc
          obtain ⟨t, htdef⟩ : ∃ t, dTlS blank endSym mark k x.length ts = t := ⟨_, rfl⟩
          rw [htdef] at hsEnc
          have hsEncS := hsEnc
          have hsEnc := hsEncS.base
          have hqOf : qOf t = q' := qOf_eq hsEnc
          have hpOf : pOf t = P' := pOf_eq hsEnc
          have hfOf : fOf t = p₁ := fOf_eq hsEnc
          have hrOf : rOf t = extendReach (x.drop s) p₁ (x.length + 1) m := rOf_eq hsEnc
          have hdOf : dOf t = D' := dOf_eq hsEnc
          have heOf : eOf t = E' := eOf_eq hsEnc
          rw [hrdef] at hsEnc hrOf hp2 hP'b hq'b hD'b hflag
          obtain ⟨SO, hSO⟩ : ∃ SO, secondOuterWork (x.drop s) k p₁ r
              ((x.drop s).length + 1) 1 0 = SO := ⟨_, rfl⟩
          rw [hSO] at hq'b hP'b hD'b
          obtain ⟨FO, hFO⟩ : ∃ FO, firstOuterWork (x.drop s) k (x.drop s).length
              ((x.drop s).length + 1) 1 = FO := ⟨_, rfl⟩
          obtain ⟨ER, hER⟩ : ∃ ER, extendReachWork (x.drop s) p₁ (x.length + 1) m = ER :=
            ⟨_, rfl⟩
          have hdsw : decomposeStepWork x k s = FO + (ER + SO) := by
            rw [decomposeStepWork]
            simp only [hfp, hrdef, hSO, hFO, hER]
          -- `p₁` と `r` の評価
          have hp₁ : 0 < p₁ := firstOuter_pos (x.drop s) k (x.drop s).length _ 1 p₁ m
            (by omega) hfp'
          have hmeq : m = p₁ + (k - 1) * p₁ :=
            firstOuter_snd (x.drop s) k (x.drop s).length _ 1 p₁ m hfp'
          have hp₁FO : p₁ ≤ FO := by
            have h1 : p₁ ≤ (k - 1) * p₁ := Nat.le_mul_of_pos_left p₁ (by omega)
            rw [← hFO]; omega
          obtain ⟨_, _, hwk2, hmr, hrle⟩ := frProg_spec (blank := blank) (startSym := startSym)
            (endSym := endSym) (mark := mark) (x := x) (k := k)
            (bound := (x.drop s).length) (Fo := (x.drop s).length + 1)
            (n := (x.drop s).length) (F := 0) (S := s)
            hk hend hmark hslt (le_refl _) horcB hE hfp'
          rw [hrdef] at hmr hrle
          rw [hER] at hrle
          have hrb : r ≤ k * FO + ER := by
            have hkp : k * p₁ ≤ k * FO := Nat.mul_le_mul_left k hp₁FO
            have hmk : m ≤ k * p₁ := by
              have : k * p₁ = (k - 1) * p₁ + p₁ := by
                have hkk : k = (k - 1) + 1 := by omega
                calc k * p₁ = ((k - 1) + 1) * p₁ := by rw [← hkk]
                  _ = (k - 1) * p₁ + p₁ := by ring
              omega
            omega
          have horcEt : orcE t = decide ((secondPeriod (x.drop s) k p₁ r).isSome = true) := by
            rw [orcE, heOf, hflag]
            rcases hsp : (secondPeriod (x.drop s) k p₁ r).isSome with _ | _ <;> simp
          by_cases hS : orcE (dTlS blank endSym mark k x.length ts)
          · -- 第 2 周期あり
            have hsome : (secondPeriod (x.drop s) k p₁ r).isSome = true := by
              rw [htdef, horcEt] at hS
              simpa using hS
            obtain ⟨p₂, hp₂⟩ : ∃ p₂, secondPeriod (x.drop s) k p₁ r = some p₂ :=
              Option.isSome_iff_exists.1 hsome
            have hPp₂ : P' = p₂ := hp2 p₂ hp₂
            rw [← hPp₂] at hp₂
            -- リセット
            have hclr : Enc blank startSym endSym mark x (s + q') (s + P' + q')
                ⟨D', q', 0, P', p₁, s, r⟩ (applyActs blank (ezLoop blank (eOf t)) t) := by
              rw [heOf]
              exact ezLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) E' (s + q') (s + P' + q') D' q' 0 P' p₁ s r t
                (by simpa using hsEnc)
            have hreset : Enc blank startSym endSym mark x s s ⟨0, 0, 0, 0, P', s, 0⟩
                (dRstS blank t) := by
              rw [dRstS, dRst, applyActs_append, hqOf, hpOf, hfOf, hrOf, hdOf]
              exact resetProg_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) hclr
            have horcCf : ∀ (s'' p'' : ℕ) (ts'' : Tapes sc),
                Enc blank startSym endSym mark x s'' (s'' + p'')
                  ⟨(k - 1) * p'', 0, 0, p'', P', s'', 0⟩ ts'' →
                (orcCf ts'' = true ↔ p'' < P') :=
              fun s'' p'' ts'' hEE => orcCf_spec hEE
            obtain ⟨hstlen, P'', hP''fit, hP''wk, hP''enc⟩ := stripProg2_spec (blank := blank)
              (startSym := startSym) (endSym := endSym) (mark := mark) (x := x) (k := k)
              (orcB := orcCf) (bound := P') (n := x.length) (F := P')
              hk hend hmark (le_refl _) horcCf (x.length + 1) s (dRstS blank t) hs hreset
            obtain ⟨s', hs'def⟩ : ∃ s', stripLoop2 x k P' (x.length + 1) s = s' := ⟨_, rfl⟩
            rw [hs'def] at hP''fit hP''enc
            obtain ⟨SLW, hSLW⟩ : ∃ SLW, stripLoop2Work x k P' (x.length + 1) s = SLW := ⟨_, rfl⟩
            rw [hSLW] at hstlen hP''wk
            have hstrEq : dStr blank endSym mark k x.length t
                = stripProg2 blank endSym mark orcCf k x.length (x.length + 1) (x.length + 1)
                    (x.length + 1) (dRstS blank t) := rfl
            have hstrS : Enc blank startSym endSym mark x s' (s' + P'')
                ⟨(k - 1) * P'', 0, 0, P'', P', s', 0⟩ (dStrS blank endSym mark k x.length t) :=
              hP''enc
            have hcleanS : Enc blank startSym endSym mark x s' s' ⟨0, 0, 0, 0, P', s', 0⟩
                (applyActs blank
                  (cleanProg blank k (pOf (dStrS blank endSym mark k x.length t)))
                  (dStrS blank endSym mark k x.length t)) := by
              rw [pOf_eq hstrS]
              exact cleanProg_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) (k := k) hstrS
            have hbodyS : Enc blank startSym endSym mark x s' s' ⟨0, 0, 0, 0, 0, s', 0⟩
                (dBodyS blank endSym mark k x.length t) := by
              have h := fzLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) P' s' s' 0 0 0 0 0 s' 0 _ (by simpa using hcleanS)
              rw [dBodyS, dBody, dCln, applyActs_append, applyActs_append, applyActs_append,
                hpOf]
              exact h
            have hpstr : pOf (dStrS blank endSym mark k x.length t) = P'' := pOf_eq hstrS
            have hs'le : s' ≤ x.length := by omega
            have hbodyES := hsEncS.frame (dBody_noSigned blank endSym mark k x.length t) hbodyS
            obtain ⟨hrc, hre⟩ := ih s' (dBodyS blank endSym mark k x.length t) hs'le hbodyES
            have hloop : decomposeLoop2 x k (fuel + 1) s = decomposeLoop2 x k fuel s' := by
              rw [decomposeLoop2]
              simp only [hfp, hrdef, hp₂, hs'def]
            have hwork : decomposeLoop2Work x k (fuel + 1) s
                = decomposeStepWork x k s + (SLW + decomposeLoop2Work x k fuel s') := by
              rw [decomposeLoop2Work]
              simp only [hfp, hrdef, hp₂, hs'def, hSLW]
            have hprog : decProg blank endSym mark k x.length (fuel + 1) ts
                = (dFp blank endSym mark k x.length ts ++
                    dTl blank endSym mark k x.length ts) ++
                  (dBody blank endSym mark k x.length t ++
                    decProg blank endSym mark k x.length fuel
                      (dBodyS blank endSym mark k x.length t)) := by
              rw [decProg, if_neg hend2, if_pos hprobe, if_pos hS, htdef]
              simp [List.append_assoc]
            have happ : applyActs blank
                (decProg blank endSym mark k x.length (fuel + 1) ts) ts
                = applyActs blank
                    (decProg blank endSym mark k x.length fuel
                      (dBodyS blank endSym mark k x.length t))
                    (dBodyS blank endSym mark k x.length t) := by
              rw [hprog, hsplit, applyActs_append, applyActs_append, ← hTlS, htdef, dBodyS]
            refine ⟨?_, ?_⟩
            · rw [hprog, hsplit, List.length_append, List.length_append, hwork, hdsw]
              rw [dBody, dRst, dCln]
              simp only [List.length_append, ezLoop_length, resetProg_length, cleanProg_length,
                fzLoop_length, heOf, hqOf, hpOf, hfOf, hrOf, hdOf, hpstr]
              have hE'1 : E' ≤ 1 := by rw [hflag]; split <;> omega
              obtain ⟨W2, hW2⟩ : ∃ W2, decomposeLoop2Work x k fuel s' = W2 := ⟨_, rfl⟩
              rw [hW2] at hrc ⊢
              obtain ⟨A, hA⟩ : ∃ A, 23 * k + 120 = A := ⟨_, rfl⟩
              obtain ⟨B, hB⟩ : ∃ B, 7 * k + 23 = B := ⟨_, rfl⟩
              rw [hA, hB] at hrc ⊢
              -- 各部品の評価
              have hstl : (dStr blank endSym mark k x.length t).length
                  ≤ (17 * k + 36) * SLW + (k + 4) := by
                rw [hstrEq]; exact hstlen
              -- `cleanProg` は `(2k+1) * P''`、`P'' ≤ 1 + SLW`
              have hcl : 3 * P'' + 2 * ((k - 1) * P'') = (2 * k + 1) * P'' := by
                obtain ⟨kk, hkk⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
                subst hkk
                simp only [Nat.add_sub_cancel]
                ring
              have hclP : (2 * k + 1) * P'' ≤ (2 * k + 1) * (1 + SLW) :=
                Nat.mul_le_mul_left _ hP''wk
              have hclE : (2 * k + 1) * (1 + SLW) = (2 * k + 1) + (2 * k + 1) * SLW := by ring
              -- リセットの償却
              have hres1 : 4 * q' + 2 * p₁ + 4 * P' + 2 * r + 2 * D' + 2 * E'
                  ≤ (4 * k + 16) * (FO + (ER + SO)) + 6 := by
                have e1 : 4 * q' ≤ 4 * SO := by omega
                have e2 : 2 * p₁ ≤ 2 * FO := by omega
                have e3 : 4 * P' ≤ 4 + 8 * SO := by omega
                have e4 : 2 * r ≤ 2 * (k * FO) + 2 * ER := by omega
                have e5 : 2 * D' ≤ 2 * ((k + 1) * (2 * SO)) := by omega
                have e6 : 2 * ((k + 1) * (2 * SO)) = (4 * k + 4) * SO := by ring
                have e7 : 2 * (k * FO) = (2 * k) * FO := by ring
                have e8 : (2 * k + 2) * FO + 2 * ER + (4 * k + 16) * SO
                    ≤ (4 * k + 16) * (FO + (ER + SO)) := by
                  have f1 : (2 * k + 2) * FO ≤ (4 * k + 16) * FO :=
                    Nat.mul_le_mul_right _ (by omega)
                  have f2 : 2 * ER ≤ (4 * k + 16) * ER := Nat.mul_le_mul_right _ (by omega)
                  have f3 : (4 * k + 16) * (FO + (ER + SO))
                      = (4 * k + 16) * FO + (4 * k + 16) * ER + (4 * k + 16) * SO := by ring
                  omega
                have e9 : 4 * SO + 8 * SO + (4 * k + 4) * SO = (4 * k + 16) * SO := by ring
                have e10 : (2 * k) * FO + 2 * FO = (2 * k + 2) * FO := by ring
                omega
              -- `fzLoop` の償却
              have hfz : 2 * P' ≤ 4 * (FO + (ER + SO)) + 2 := by
                have : 4 * SO ≤ 4 * (FO + (ER + SO)) := by
                  have := Nat.mul_le_mul_left 4 (show SO ≤ FO + (ER + SO) by omega)
                  omega
                omega
              -- `stepProg` の償却
              have hstep2 : (stepProg blank endSym mark (orcEnd endSym) (orcR k) (orc2R k) k
                  (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts).length
                  ≤ (6 * k + 100) * (FO + (ER + SO)) + (4 * k + 10) := by
                rw [hdsw] at hslen; exact hslen
              -- まとめ
              have hAsum : (6 * k + 100) * (FO + (ER + SO)) + ((4 * k + 16) * (FO + (ER + SO)) + 6)
                    + (4 * (FO + (ER + SO)) + 2)
                  ≤ A * (FO + (ER + SO)) + 8 := by
                have h1 : (6 * k + 100) * (FO + (ER + SO)) + (4 * k + 16) * (FO + (ER + SO))
                    + 4 * (FO + (ER + SO)) = (10 * k + 120) * (FO + (ER + SO)) := by ring
                have h2 : (10 * k + 120) * (FO + (ER + SO)) ≤ A * (FO + (ER + SO)) :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              have hAstrip : (17 * k + 36) * SLW + (2 * k + 1) * SLW ≤ A * SLW := by
                have h1 : (17 * k + 36) * SLW + (2 * k + 1) * SLW = (19 * k + 37) * SLW := by ring
                have h2 : (19 * k + 37) * SLW ≤ A * SLW := Nat.mul_le_mul_right _ (by omega)
                omega
              have hBfuel : B * (fuel + 1) = B * fuel + B := by ring
              have hAexp : A * (FO + (ER + SO) + (SLW + W2))
                  = A * (FO + (ER + SO)) + A * SLW + A * W2 := by ring
              -- 1 反復あたりの定数は `B = 4k+16` に収まる
              have hBB : (4 * k + 10) + 8 + (k + 4) + (2 * k + 1) ≤ B := by omega
              omega
            · rw [happ, hloop]
              exact hre
          · -- 第 2 周期なし
            have hnone : secondPeriod (x.drop s) k p₁ r = none := by
              rw [htdef, horcEt] at hS
              rcases hsp : secondPeriod (x.drop s) k p₁ r with _ | p₂
              · rfl
              · rw [hsp] at hS; simp at hS
            have hclr2 : Enc blank startSym endSym mark x (s + q') (s + P' + q')
                ⟨D', q', 0, P', p₁, s, r⟩ (applyActs blank (ezLoop blank (eOf t)) t) := by
              rw [heOf]
              exact ezLoop_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) E' (s + q') (s + P' + q') D' q' 0 P' p₁ s r t
                (by simpa using hsEnc)
            have hloop : decomposeLoop2 x k (fuel + 1) s = (s, p₁, r) := by
              rw [decomposeLoop2]
              simp only [hfp, hrdef, hnone]
            have hprog : decProg blank endSym mark k x.length (fuel + 1) ts
                = (dFp blank endSym mark k x.length ts ++
                    dTl blank endSym mark k x.length ts) ++ dSwap blank t := by
              rw [decProg, if_neg hend2, if_pos hprobe, if_neg hS, htdef]
              simp [List.append_assoc]
            refine ⟨?_, ⟨s, s, 0, 0, 0, ?_⟩⟩
            · rw [hprog, hsplit, List.length_append, decomposeLoop2Work]
              simp only [hfp, hrdef, hnone, Nat.add_zero]
              rw [dSwap]
              simp only [List.length_append, ezLoop_length, swapProg_length, heOf,
                hqOf, hpOf, hfOf, hdOf]
              rw [hdsw]
              have hE'1 : E' ≤ 1 := by rw [hflag]; split <;> omega
              obtain ⟨A, hA⟩ : ∃ A, 23 * k + 120 = A := ⟨_, rfl⟩
              obtain ⟨B, hB⟩ : ∃ B, 7 * k + 23 = B := ⟨_, rfl⟩
              rw [hA, hB]
              have hstep2 : (stepProg blank endSym mark (orcEnd endSym) (orcR k) (orc2R k) k
                  (x.drop s).length ((x.drop s).length + 1) (x.length + 1) ts).length
                  ≤ (6 * k + 100) * (FO + (ER + SO)) + (4 * k + 10) := by
                rw [hdsw] at hslen; exact hslen
              have hswap : 4 * q' + 3 * P' + 3 * p₁ + 2 * D' + 2 * E'
                  ≤ (4 * k + 14) * (FO + (ER + SO)) + 5 := by
                have e1 : 4 * q' ≤ 4 * SO := by omega
                have e2 : 3 * P' ≤ 3 + 6 * SO := by omega
                have e3 : 3 * p₁ ≤ 3 * FO := by omega
                have e4 : 2 * D' ≤ 2 * ((k + 1) * (2 * SO)) := by omega
                have e5 : 2 * ((k + 1) * (2 * SO)) = (4 * k + 4) * SO := by ring
                have e6 : 4 * SO + 6 * SO + (4 * k + 4) * SO = (4 * k + 14) * SO := by ring
                have e7 : 3 * FO + (4 * k + 14) * SO ≤ (4 * k + 14) * (FO + (ER + SO)) := by
                  have f1 : 3 * FO ≤ (4 * k + 14) * FO := Nat.mul_le_mul_right _ (by omega)
                  have f3 : (4 * k + 14) * (FO + (ER + SO))
                      = (4 * k + 14) * FO + (4 * k + 14) * ER + (4 * k + 14) * SO := by ring
                  omega
                omega
              have hAsum : (6 * k + 100) * (FO + (ER + SO)) + (4 * k + 14) * (FO + (ER + SO))
                  ≤ A * (FO + (ER + SO)) := by
                have h1 : (6 * k + 100) * (FO + (ER + SO)) + (4 * k + 14) * (FO + (ER + SO))
                    = (10 * k + 114) * (FO + (ER + SO)) := by ring
                have h2 : (10 * k + 114) * (FO + (ER + SO)) ≤ A * (FO + (ER + SO)) :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              have hBB : 4 * k + 10 + 5 ≤ B * (fuel + 1) := by
                have h2 : B ≤ B * (fuel + 1) := Nat.le_mul_of_pos_right _ (by omega)
                omega
              have hBfuel : B * (fuel + 1) = B * fuel + B := by ring
              omega
            · rw [hprog, hsplit, applyActs_append, ← hTlS, htdef, hloop, dSwap,
                applyActs_append, hqOf, hpOf, hfOf, hdOf]
              exact swapProg_enc (blank := blank) (startSym := startSym) (endSym := endSym)
                (mark := mark) (x := x) (r := r) hclr2

/-- **系（`decompose2` 全体のテープ実現とコスト）**。
まっさらな初期状態（`x` を載せた `V1`/`V2` のヘッドが添字 `0`、カウンタはすべて `0`）から
出発して、終状態は `Cs = (decompose2 x k).1`、`Cp = (decompose2 x k).2.1`、
`Cr = (decompose2 x k).2.2` を保持する。動作数は
`(23k+120) * decompose2Work x k + (7k+24)*(|x|+1)` 以下。
追加カウンタ3本についても、入口ではマーカーつきの値ゼロを要求する。 -/
theorem decompose2_on_tapes (hk : 3 ≤ k) (hend : endSym ∉ x) (hmark : mark ≠ blank)
    (ts : Tapes sc)
    (hE : EncS blank startSym endSym mark x 0 0 ⟨0, 0, 0, 0, 0, 0, 0⟩ ⟨0, 0, 0⟩ ts) :
    ((decProg blank endSym mark k x.length (x.length + 1) ts).length
        ≤ (23 * k + 120) * decompose2Work x k + (7 * k + 24) * (x.length + 1)
      ∧ (∃ a b D Q E, Enc blank startSym endSym mark x a b
          ⟨D, Q, E, (decompose2 x k).2.1, 0, (decompose2 x k).1, (decompose2 x k).2.2⟩
          (applyActs blank
            (decProg blank endSym mark k x.length (x.length + 1) ts) ts))) := by
  have h := decProg_spec (blank := blank) (startSym := startSym) (endSym := endSym)
    (mark := mark) (x := x) (k := k) hk hend hmark (x.length + 1) 0 ts
    (Nat.zero_le _) hE
  rw [decompose2, decompose2Work]
  refine ⟨?_, h.2⟩
  have h1 := h.1
  have h2 : (7 * k + 24) * (x.length + 1)
      = (7 * k + 23) * (x.length + 1) + (x.length + 1) := by ring
  omega

end Outer2d

/-! ## 16. 小例による健全性チェック -/

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
  **`stripProg2_spec : ≤ (17k+36) * stripLoop2Work x k bound fuel s + (k+4)`**
  （1 反復あたりの定数 `k+4` は、その反復の `firstOuterWork ≥ 1`（`firstOuterWork_pos`）
  に付け替えてある。また終状態の周期 `P` は `P ≤ 1 + stripLoop2Work` を満たす）
  （`PalPeg.GSDecompose2` の `stripLoop2` / `stripLoop2Work` をそのまま鏡写しにしている）。
  終状態は `Cs = stripLoop2 x k bound fuel s` を保持する「きれいな状態」
  `Enc x s' (s'+P) ⟨(k-1)P,0,0,P,0,s',0⟩`。後始末 `cleanProg`（`(2k+1)*P` 動作）で
  まっさらな状態 `Enc x s' s' ⟨0,0,0,0,0,s',0⟩` に戻せる。

### 完成（`decomposeLoop2` / `decompose2_on_tapes`）— §14

以下は符号つき補助カウンタ導入前の記録。現在の主定理は `EncS` のゼロ入口を
要求し、コスト上界は `(23k+120) * decompose2Work + (7k+24) * (|x|+1)`。
ここでの「オラクルなし」は外部引数がないという意味で、有限制御への
コンパイル完了を意味しない。

§15 に残していた 3 点はすべて解消した。

1. **オラクル `orcB` の一本化・除去**。`oProg_spec` / `fpProg_spec` / `frProg_spec` /
   `stripProg2_spec` の仮定を
   `horcB : ∀ p' ts', Enc x s (s+p') ⟨(k-1)p',0,0,p',F,S,R⟩ ts' → (orcB ts' = true ↔ p' < bound)`
   という**ループ状態上の条件**へ弱めた（`F`, `S`, `R` は `∀` の外）。これにより
   * `firstPeriod`（`bound = |v|`）では `orcEnd endSym ts = decide (Tape.read ts.V2 ≠ endSym)`、
   * 削除ループ（`bound = p₂`、`Cf = p₂`）では `orcCf ts = decide (pOf ts < fOf ts)`
   という**純粋な読み出し関数**で満たせる（`orcEnd_spec` / `orcCf_spec`）。
   同じ手口で第 2 相の `orc` / `orc2` も
   `orcR k ts = decide (rOf ts < pOf ts + qOf ts + 1 ∧ (k-1)*pOf ts ≤ qOf ts + 1)`、
   `orc2R k ts = decide (k * fOf ts ≤ qOf ts ∧ qOf ts ≤ rOf ts)` で実現した
   （`sProg_spec` / `sAbort_iff` / `soProg_spec` / `spProg_spec` / `stepProg_spec` の
   仮定を状態付きに弱め、第 2 相では `Cr = r` が不変であることを使う）。
   さらに第 2 周期の有無も、`soProg` の中断枝で `Ce` にフラグを立てる（`ceFlag`、1 動作）
   ことで純粋な読み出し `orcE ts = decide (0 < eOf ts)` になった。
   **オラクルは一つも残っていない。**

2. **第 2 相の後始末**。`soProg_spec` の結論を強め、終状態がつねに
   `Enc x (s+q') (s+P'+q') ⟨D', q', 0, P', first, S, r⟩` の形であること、および
   `q' ≤ q + secondOuterWork`、`P' ≤ p + q + 2*secondOuterWork`、
   `D' ≤ D + (k+1)*(q + 2*secondOuterWork)` を示した（入口 `p=1, q=0, D=0` では
   `p₂ ≤ 1 + 2*secondOuterWork`）。これを使って
   * `resetProg`（`4q' + 2p₁ + 4P' + 2r + 2D'` 動作）で削除ループの入口
     `Enc x s s ⟨0,0,0,0,p₂,s,0⟩` へ戻し、
   * `swapProg`（`4q' + 3P' + 3p₁ + 2D'` 動作）で第 2 周期なしの終状態
     `Enc x s s ⟨0,0,0,p₁,0,s,r⟩` にそろえる。
   どちらも反復あたり `≤ (4k+16) * decomposeStepWork + 4` に収まる。

3. **外側の帰納法**。`decProg`（`bottomProg` / `dFp` / `dTl` / `dBody` / `dSwap`）と
   **`decProg_spec`**：
   ```
   (decProg blank endSym mark k |x| fuel ts).length
     ≤ (19k+85) * decomposeLoop2Work x k fuel s + (4k+16) * fuel + (|x|+1)
   ```
   かつ終状態は `Cp = (decomposeLoop2 x k fuel s).2.1`、`Cf = 0`、
   `Cs = (decomposeLoop2 x k fuel s).1`、`Cr = (decomposeLoop2 x k fuel s).2.2`。
   系が **`decompose2_on_tapes`**（`fuel = |x|+1`, `s = 0`）：
   ```
   length ≤ (19k+85) * decompose2Work x k + (4k+17) * (|x|+1)
   ```
   燃料切れの枝も `decomposeLoop2 x k 0 s = (|x|,0,0)` を `bottomProg` で忠実に写しており、
   ステートメントに条件は付かない。
   1 反復あたりのオーバーヘッドは `|x|` に依存しない定数 `4k+16` である
   （`stepProg` の `k+3`、フラグ消去と `resetProg` の `8`、削除ループの `k+4`、
   `cleanProg` の `2k+1`）。`cleanProg` が扱う周期 `P` は
   `P ≤ 1 + firstOuterWork`（`oProg_spec` / `fpProg_spec` の `none` 枝）と
   `P ≤ 1 + stripLoop2Work`（`stripProg2_spec`）で仕事量へ押し込んであるので、
   `fuel` に比例する `Θ(|x|²)` 項は残っていない。

### 残るオラクル：なし

`soProg` は中断（＝第 2 周期の発見）の直後に `ceFlag`（`Ce` を 1 増やす 1 動作）を実行する。
第 2 相のあいだ `Ce` は `shiftPhase` のスクラッチとして使われるが出入りともに `0` であり、
フラグが立つのはループを抜ける最後の 1 回だけなので干渉しない。よって
`soProg_spec` / `spProg_spec` / `stepProg_spec` の結論は `Ce = 0` ではなく
`Ce = if (secondPeriod …).isSome then 1 else 0` となり、`decProg` は
`orcE ts = decide (0 < eOf ts)` という**テープの読み出し**だけで第 2 周期の有無を判定する。
`dRst` / `dSwap` は先頭で `ezLoop blank (eOf t)`（`≤ 2` 動作）を実行してフラグを消すので、
削除ループの入口も終状態も従来どおり `Ce = 0` である。
中断枝の 1 動作は `soProg_spec` の `(k+12) * secondOuterWork` の余裕に収まり、
フラグ消去の `≤ 2` 動作は 1 反復あたりの定数 `4k+16` に収まる。

### 最終的なコスト定数

```
decompose2_on_tapes :
  (decProg blank endSym mark k |x| (|x|+1) ts).length
    ≤ (19k+85) * decompose2Work x k + (4k+17) * (|x|+1)
```

`fuel` に比例する項（旧 `((4k+16)*(|x|+1)) * fuel`、`fuel = |x|+1` では `Θ(|x|²)`）は
消えたので、`decompose2Work x k = O(|x|)` が示せれば全体が `O(|x|)` になる。
-/

end PalPeg.GSPre
