import PalPeg.ProgLangSum
import PalPeg.RTQueueProg
import PalPeg.TextFeed

/-!
# `TextFeed` の有限制御プログラム化への部分移植 (`TextFeedProg`)

`PalPeg.TextFeed`（オラクル無し版, `Machine'`）の 1 ラウンドは
`startRound' = stepRight' ∘ fill' ∘ arrive'` で与えられる（走査段 8 本 + 待ち行列
10 本 = 18 本のテープを持つ）。本ファイルは `PalPeg.ProgLangSum` の一般の移送・直和
補題（`exec_transport` / `exec_map` / `Interp.sum` / `exec_sum_inl` / `exec_sum_inr` /
`exec_sum_seq`）を使って、`arrive'`（待ち行列への `snoc`、待ち行列側のみ）と
`stepRight'`（走査テープ `tT` を「現在の記号を書き戻して右へ」動かすだけ、走査側のみ）
を `Fin 18` 上の 1 個の構造化プログラムとして合成し、その実行を証明する。

**範囲の明示（重要）**：`fill'` は待ち行列側の値（`peek`）を読んで走査側のテープ
`tT` に書き込む、**両側にまたがる**単一操作である。`PalPeg.ProgLangSum` の
`Interp.sum` は「左右が互いに素な（相手のテープを読まない）解釈の直和」であり、
このような跨ぎ読み書きの単一動作をそのままでは表現できない（実機の作りでは、待ち行列
側の `headT`/`tailT` が値を決まったセルへ移した後、複数マイクロステップに分けて
初めて反対側へ伝わる——本ファイルはその複数ステップ合成までは踏み込まない）。
したがって本ファイルが完全に移植するのは `arrive'` と `stepRight'` の 2 操作であり、
`feedRoundProg` は「到着してからヘッドを 1 つ右へ動かす」（`fill'` を除いた部分）を
表す。これは `startRound'` の忠実な全体再現ではなく、`PalPeg.ProgLangSum` の直和
移送機構が実際に使える最大限の忠実な部分（両方向で独立に動く 2 操作の合成）である。

テープの並びは待ち行列 10 本を **先頭**、走査段 8 本を **末尾** に置く
（`Fin (10 + 8) = Fin 18`）。こうすると `feedRoundProg = Prog.seq (待ち行列側)
(走査側)` が `PalPeg.ProgLangSum.exec_sum_seq` にそのまま載る。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.RTQueue
open PalPeg.RTQueueTapes
open PalPeg.RTQueueProg (ActQ CondQ IQ CS csOf snocProg snocCS qsnoc_exec Performs ExecQ TSQ
  avecsQ avecsQ_length applyTrace_avecsQ)
open PalPeg.GSProg (Act8 Cond8 I8 inputFree_I8)

variable {sc : ℕ} {Terminal : Type}

/-! ## 1. 18 本テープの解釈：待ち行列 10 本 + 走査段 8 本 -/

/-- 待ち行列 10 本テープ（`IQ`）と走査段 8 本テープ（`I8`）の直和。
`Fin (10 + 8) = Fin 18` 上の解釈になる。 -/
noncomputable def IFR (blank endSym mark startSym : Fin sc) :
    Interp Terminal (ActQ sc ⊕ Act8) (CondQ sc ⊕ Cond8) (Fin sc) (10 + 8) :=
  Interp.sum (IQ (k := sc) Terminal) (I8 (Terminal := Terminal) blank endSym mark startSym)

/-! ## 2. `arrive'`：待ち行列への `snoc`（待ち行列側のみ） -/

/-- `arrive'` に対応する 18 本テープ上のプログラム：待ち行列側の `snocProg` を
直和の左枝へ写したもの。 -/
noncomputable def feedArriveProg (blank mark : Fin sc) (π : Role → Role) (c : CS)
    (a : Fin sc) : Prog (ActQ sc ⊕ Act8) (CondQ sc ⊕ Cond8) :=
  Prog.map (Sum.inl (β := Act8)) (Sum.inl (β := Cond8)) (snocProg blank mark π c a)

/-! ## 3. `stepRight'`：走査テープ `tT` を「書き戻して右へ」（走査側のみ） -/

/-- `stepRight'` に対応する走査側 1 動作：`tT` の現在の記号を書き戻し、右へ動く。 -/
def feedStepRightAct8 : Prog Act8 Cond8 := Prog.act (PalPeg.GSTapes.tT, true, Move.right)

/-- `stepRight'` に対応する 18 本テープ上のプログラム。 -/
noncomputable def feedStepRightProg (sc : ℕ) :
    Prog (ActQ sc ⊕ Act8) (CondQ sc ⊕ Cond8) :=
  Prog.map (Sum.inr (α := ActQ sc)) (Sum.inr (α := CondQ sc)) feedStepRightAct8

/-! ## 4. 合成：到着してから 1 つ右へ -/

/-- `startRound'` から `fill'` を除いた部分（両側で独立に走る 2 操作の合成）。 -/
noncomputable def feedRoundProg (blank mark : Fin sc) (π : Role → Role) (c : CS)
    (a : Fin sc) : Prog (ActQ sc ⊕ Act8) (CondQ sc ⊕ Cond8) :=
  Prog.seq (feedArriveProg blank mark π c a) (feedStepRightProg sc)

section Exec

variable {blank endSym mark startSym : Fin sc} {π : Role → Role}

/-- `stepRight'` の `Exec`：ちょうど 1 マイクロステップ。 -/
theorem feedStepRight_exec8 (T : Fin 8 → STape (Fin sc)) :
    Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank feedStepRightAct8 T
      [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
        (PalPeg.GSTapes.tT, true, Move.right) T] :=
  exec_act (inputFree_I8 (Terminal := Terminal) blank endSym mark startSym) _ T

/-- **`arrive'` の `Exec` への移送**：待ち行列側の `snoc` プログラムの実行
（`RTQueueProg.qsnoc_exec`）を、`ExecQ` （＝ 10 本テープ上の `Exec`）として取り出す。 -/
theorem feedArrive_execQ (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q)
    (hq : Inv q) :
    ∃ (n : ℕ) (qt' : QT sc) (π' : Role → Role) (L : List (Act sc)),
      ExecQ Terminal blank (snocProg blank mark π (snocCS q a) a) qt L ∧
      L.length = n ∧ n ≤ 26 ∧ Function.Injective π' ∧
      qt' ∘ π' = (RTQueueTapes.snocT blank mark q a ⟨qt ∘ π, cst⟩).qt ∧
      (RTQueueTapes.snocT blank mark q a ⟨qt ∘ π, cst⟩).cost = cst + n ∧
      Encodes blank mark (qt' ∘ π') (snoc q a) ∧ run blank qt L = qt' := by
  obtain ⟨n, qt', π', hperf, hb, hinj, hqt', hcost', henc⟩ :=
    qsnoc_exec (Terminal := Terminal) (blank := blank) (mark := mark) hπ hne
      (qt := qt) (q := q) a cst h hq
  obtain ⟨L, hE, hlen, hrun⟩ := hperf
  exact ⟨n, qt', π', L, hE, hlen, hb, hinj, hqt', hcost', henc, hrun⟩

/-- **本節の主定理**：`feedRoundProg` の `Exec`。18 本テープ上で「待ち行列への
`snoc`」に続けて「走査テープ `tT` を 1 つ右へ」を実行し、動作列は待ち行列側の
動作列 `L`（`snocProg` が実際に出す動作）の後ろに走査側の 1 動作を連結したもの
になる。テープ状態は待ち行列 10 本 (`TSQ qt`) と走査 8 本 (`T`) を並べたもの
(`Fin.append`) から始まる。 -/
theorem feedRound_exec (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) {L : List (Act sc)}
    (hE : ExecQ Terminal blank (snocProg blank mark π (snocCS q a) a) qt L)
    (T : Fin 8 → STape (Fin sc)) :
    Exec (IFR (Terminal := Terminal) blank endSym mark startSym) blank
      (feedRoundProg blank mark π (snocCS q a) a)
      (Fin.append (TSQ qt) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))
          (avecsQ blank L qt) ++
        List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ (run blank qt L)) T))
          [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
            (PalPeg.GSTapes.tT, true, Move.right) T]) := by
  have h1 : Exec (IQ (k := sc) Terminal) blank (snocProg blank mark π (snocCS q a) a)
      (TSQ qt) (avecsQ blank L qt) := hE
  have h2 := feedStepRight_exec8 (blank := blank) (endSym := endSym) (mark := mark)
    (startSym := startSym) (Terminal := Terminal) T
  have hround := exec_sum_seq
    (I1 := IQ (k := sc) Terminal)
    (I2 := I8 (Terminal := Terminal) blank endSym mark startSym) h1 h2
  rw [applyTrace_avecsQ] at hround
  simpa only [IFR, feedRoundProg, feedArriveProg, feedStepRightProg] using hround

/-- **停止と長さ**：`feedRoundProg` は `L.length + 1` マイクロステップで
ちょうど停止し、`L.length ≤ 26` なので `≤ 27` マイクロステップで停止する。 -/
theorem feedRound_halts (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) {L : List (Act sc)}
    (hE : ExecQ Terminal blank (snocProg blank mark π (snocCS q a) a) qt L)
    (hbound : L.length ≤ 26) (T : Fin 8 → STape (Fin sc))
    (l : List (Option Terminal)) (hl : l.length = L.length + 1) (x : Option Terminal) :
    (runInputs (IFR (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
        ([feedRoundProg blank mark π (snocCS q a) a], Fin.append (TSQ qt) T)).1 = [] := by
  have h1 : Exec (IQ (k := sc) Terminal) blank (snocProg blank mark π (snocCS q a) a)
      (TSQ qt) (avecsQ blank L qt) := hE
  have h2 := feedStepRight_exec8 (blank := blank) (endSym := endSym) (mark := mark)
    (startSym := startSym) (Terminal := Terminal) T
  have hround := exec_sum_seq
    (I1 := IQ (k := sc) Terminal)
    (I2 := I8 (Terminal := Terminal) blank endSym mark startSym) h1 h2
  have hround' : Exec (IFR (Terminal := Terminal) blank endSym mark startSym) blank
      (feedRoundProg blank mark π (snocCS q a) a) (Fin.append (TSQ qt) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))
          (avecsQ blank L qt) ++
        List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ (run blank qt L)) T))
          [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
            (PalPeg.GSTapes.tT, true, Move.right) T]) := by
    rw [applyTrace_avecsQ] at hround
    simpa only [IFR, feedRoundProg, feedArriveProg, feedStepRightProg] using hround
  have hlen' : (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))
        (avecsQ blank L qt) ++
      List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ (run blank qt L)) T))
        [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
          (PalPeg.GSTapes.tT, true, Move.right) T]).length = L.length + 1 := by
    simp [avecsQ_length]
  have := exec_halts hround' l (by rw [hl, hlen']) x
  simpa using this

theorem feedRound_bound (hπ : Function.Injective π) (hne : mark ≠ blank) {qt : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ) (h : Encodes blank mark (qt ∘ π) q)
    (hq : Inv q) :
    ∃ (n : ℕ) (L : List (Act sc)),
      ExecQ Terminal blank (snocProg blank mark π (snocCS q a) a) qt L ∧
      L.length = n ∧ n + 1 ≤ 27 := by
  obtain ⟨n, qt', π', L, hE, hlen, hb, _hinj, _hqt', _hcost', _henc, _hrun⟩ :=
    feedArrive_execQ (Terminal := Terminal) (blank := blank) (mark := mark) hπ hne a cst h hq
  exact ⟨n, L, hE, hlen, by omega⟩

/-! ## 5. `TextFeed` の `arrive'` / `stepRight'` との対応 -/

/-- **`arrive'` との対応**：`feedArriveProg` を走らせて到達する待ち行列側の状態
（`RTQueueTapes.snocT` を経由する `qt' ∘ π'`）は、`TextFeed.arrive'` が更新する
`Machine'.Q` / `Machine'.R` にちょうど対応する（`RTQueueProg.qsnoc_exec` が
`RTQueueTapes.snocT` との一致として証明している内容そのもの）。 -/
theorem feedArrive_matches_arrive' {Terminal : Type} (hπ : Function.Injective π)
    (hne : mark ≠ blank) {qt : QT sc} {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ)
    (h : Encodes blank mark (qt ∘ π) q) (hq : Inv q) :
    ∃ (qt' : QT sc) (π' : Role → Role),
      Function.Injective π' ∧
      qt' ∘ π' = (RTQueueTapes.snocT blank mark q a ⟨qt ∘ π, cst⟩).qt ∧
      Encodes blank mark (qt' ∘ π') (snoc q a) := by
  obtain ⟨n, qt', π', L, hE, hlen, hb, hinj, hqt', hcost', henc, hrun⟩ :=
    feedArrive_execQ (Terminal := Terminal) hπ hne a cst h hq
  exact ⟨qt', π', hinj, hqt', henc⟩

/-- **`stepRight'` との対応**：`feedStepRightAct8` が唯一の動作として書く
write+move ベクトルは、走査テープ `tT` を「現在の記号を書き戻して右へ」動かす、
つまり `TextFeed.stepRight'` が `ts tT` に施す `Tape.step blank (ts tT) (ts tT).focus .right`
にちょうど対応する（他の 7 本の走査テープは読んで停留するので不変）。 -/
theorem feedStepRight_matches_stepRight' {Terminal : Type} (T : Fin 8 → STape (Fin sc)) :
    actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
        (PalPeg.GSTapes.tT, true, Move.right) T
      = fun j => if j = PalPeg.GSTapes.tT then ((T j).focus, Move.right)
          else ((T j).focus, Move.stay) := by
  funext j
  simp only [actVec, PalPeg.GSProg.I8, PalPeg.GSProg.actOf8, touchVec]
  by_cases hj : j = PalPeg.GSTapes.tT <;> simp [hj]

end Exec

end PalPeg.TextFeedProg

#print axioms PalPeg.TextFeedProg.feedRound_exec
#print axioms PalPeg.TextFeedProg.feedRound_halts
#print axioms PalPeg.TextFeedProg.feedRound_bound
#print axioms PalPeg.TextFeedProg.feedArrive_matches_arrive'
#print axioms PalPeg.TextFeedProg.feedStepRight_matches_stepRight'
