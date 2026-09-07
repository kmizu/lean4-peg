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
  avecsQ avecsQ_length applyTrace_avecsQ ridx role role_ridx ridx_role execQ_act inputFree_IQ TC
  tcOf tailProg qtail_exec toS toS_step toS_focus act_comp_rename)
open PalPeg.RTQueueTapes (headT headT_encodes)
open PalPeg.GSProg (Act8 Cond8 I8 inputFree_I8)
open PalPeg.TextFeed (peek arrive' fill' stepRight')

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

/-! ## 7. `fill'`：待ち行列の先頭を覗いて `tT` へ書く（両側にまたがる拡張） -/

/-- 待ち行列側（`Fin 18` の中の）「現在 `Role.front` の役を担っているテープ」の
添字。`RTQueueProg` の他のプログラム（`checkProg` など）と同じく、論理的な役
`Role.front` を物理テープへ結びつけるのは呼び出し側が渡す回転置換 `π` である。 -/
noncomputable def frontIdx (π : Role → Role) : Fin 18 := Fin.castAddEmb 8 (ridx (π Role.front))

/-- 走査側（`Fin 18` の中の）`tT` の添字。 -/
noncomputable def tTIdx : Fin 18 := Fin.natAddEmb 10 PalPeg.GSTapes.tT

theorem frontIdx_ne_tTIdx (π : Role → Role) : (frontIdx π : Fin 18) ≠ tTIdx := by
  intro h
  have h1 : (frontIdx π : Fin 18).val < 10 := by
    simp only [frontIdx, Fin.castAddEmb_apply]
    exact (ridx (π Role.front)).isLt
  have h2 : 10 ≤ (tTIdx : Fin 18).val := by
    simp only [tTIdx, Fin.natAddEmb_apply, Fin.natAdd]
    omega
  rw [h] at h1
  omega

/-- 拡張した動作識別子：既存の（待ち行列 ⊕ 走査）に、`fill'` の跨ぎ書き込み 1 個を
足す。動作識別子自体は現在の回転置換 `π` を運ぶ（`Role → Role`）。条件識別子は
増やさない。 -/
abbrev Act18 (sc : ℕ) := (ActQ sc ⊕ Act8) ⊕ (Role → Role)

abbrev Cond18 (sc : ℕ) := CondQ sc ⊕ Cond8

/-- **`fill'` の跨ぎ書き込み**：待ち行列の（回転置換 `π` のもとでの）前方テープの
現在の読みを `tT` へ書き、前方テープ自身は同じ値を書き戻して右へ動く。`headT` の
2 動作目（前方テープの復元）と `fill'` の `tT` への書き込みを、読んだ値を共有する
1 マイクロステップへ融合したもの（`actOf` が全テープの読み `σ` を見られることを
使う）。 -/
noncomputable def fillVec (π : Role → Role) (σ : Fin 18 → Fin sc) : Fin 18 → Fin sc × Move :=
  fun j => if j = frontIdx π then (σ (frontIdx π), Move.right)
    else if j = tTIdx then (σ (frontIdx π), Move.stay)
    else (σ j, Move.stay)

/-- `IFR` を拡張した、`fill'` まで込みの 18 本テープの解釈。 -/
noncomputable def IFR2 (blank endSym mark startSym : Fin sc) :
    Interp Terminal (Act18 sc) (Cond18 sc) (Fin sc) 18 where
  actOf
    | Sum.inl a, x, σ => (IFR (Terminal := Terminal) blank endSym mark startSym).actOf a x σ
    | Sum.inr π, _, σ => fillVec π σ
  condOf c σ := (IFR (Terminal := Terminal) blank endSym mark startSym).condOf c σ

theorem inputFree_IFR (blank endSym mark startSym : Fin sc) :
    InputFree (IFR (Terminal := Terminal) blank endSym mark startSym) :=
  InputFree.sum (inputFree_IQ (k := sc) Terminal)
    (inputFree_I8 (Terminal := Terminal) blank endSym mark startSym)

theorem inputFree_IFR2 (blank endSym mark startSym : Fin sc) :
    InputFree (IFR2 (Terminal := Terminal) blank endSym mark startSym) := by
  intro a x σ
  cases a with
  | inl a => exact inputFree_IFR blank endSym mark startSym a x σ
  | inr π => rfl

/-- 待ち行列側（`ActQ sc`/`CondQ sc`）のプログラムを `Act18`/`Cond18` へ埋め込む。 -/
noncomputable def liftQ (p : Prog (ActQ sc) (CondQ sc)) : Prog (Act18 sc) (Cond18 sc) :=
  Prog.map (Sum.inl (β := (Role → Role))) id (Prog.map (Sum.inl (β := Act8)) (Sum.inl (β := Cond8)) p)

/-- 走査側（`Act8`/`Cond8`）のプログラムを `Act18`/`Cond18` へ埋め込む。 -/
noncomputable def liftS (p : Prog Act8 Cond8) : Prog (Act18 sc) (Cond18 sc) :=
  Prog.map (Sum.inl (β := (Role → Role))) id (Prog.map (Sum.inr (α := ActQ sc)) (Sum.inr (α := CondQ sc)) p)

/-- 待ち行列側の `Exec` の `IFR2` への移送。 -/
theorem liftQ_exec {blank endSym mark startSym : Fin sc} {p : Prog (ActQ sc) (CondQ sc)}
    {T : Fin 10 → STape (Fin sc)} {acts : List (Fin 10 → Fin sc × Move)}
    (h : Exec (IQ (k := sc) Terminal) blank p T acts) (rest : Fin 18 → STape (Fin sc)) :
    Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank (liftQ p)
      (extend (Fin.castAddEmb 8) T rest) (acts.map (extendVec (Fin.castAddEmb 8) rest)) := by
  have h1 := exec_sum_inl (I1 := IQ (k := sc) Terminal)
    (I2 := I8 (Terminal := Terminal) blank endSym mark startSym) h rest
  have h2 := exec_map (I₁ := IFR (Terminal := Terminal) blank endSym mark startSym)
    (I₂ := IFR2 (Terminal := Terminal) blank endSym mark startSym)
    (fa := (Sum.inl : ActQ sc ⊕ Act8 → Act18 sc)) (fc := (id : Cond18 sc → Cond18 sc))
    (fun _ _ => rfl) (fun _ _ _ => rfl) h1
  simpa only [liftQ] using h2

/-- 走査側の `Exec` の `IFR2` への移送。 -/
theorem liftS_exec {blank endSym mark startSym : Fin sc} {p : Prog Act8 Cond8}
    {T : Fin 8 → STape (Fin sc)} {acts : List (Fin 8 → Fin sc × Move)}
    (h : Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank p T acts)
    (rest : Fin 18 → STape (Fin sc)) :
    Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank (liftS p)
      (extend (Fin.natAddEmb 10) T rest) (acts.map (extendVec (Fin.natAddEmb 10) rest)) := by
  have h1 := exec_sum_inr (I1 := IQ (k := sc) Terminal)
    (I2 := I8 (Terminal := Terminal) blank endSym mark startSym) h rest
  have h2 := exec_map (I₁ := IFR (Terminal := Terminal) blank endSym mark startSym)
    (I₂ := IFR2 (Terminal := Terminal) blank endSym mark startSym)
    (fa := (Sum.inl : ActQ sc ⊕ Act8 → Act18 sc)) (fc := (id : Cond18 sc → Cond18 sc))
    (fun _ _ => rfl) (fun _ _ _ => rfl) h1
  simpa only [liftS] using h2

/-- **`fill'` に対応する完全な 1 ラウンド**：到着 → 前方テープの覗き見（`probe`）
→ 覗いた値を `tT` へ書きつつ前方テープを復元する跨ぎ動作（`fillVec`）→ 待ち行列の
`tail` の残り → 走査テープを 1 つ右へ。`startRound' = stepRight' ∘ fill' ∘ arrive'`
の全体に対応する。

**注意（回転置換について）**：`RTQueueProg` の待ち行列プログラムは、実行のたびに
論理役割 `Role` を物理テープへ結びつける回転置換が更新されうる（`qsnoc_exec` が
新しい `π'` を返す）。`probe`/`fillWrite`/`tail` は「到着」の**後**の物理配置
（`π1`）を使わねばならないので、`feedRoundProg'` は到着用の `π` と、到着後の
回転置換 `π1` を別々の引数として受け取る（`π1` は `feedArrive_execQ`/`qsnoc_exec`
が返す値を呼び出し側が渡す）。 -/
noncomputable def feedRoundProg' (blank mark : Fin sc) (π π1 : Role → Role)
    (q : Queue (Fin sc)) (a : Fin sc) : Prog (Act18 sc) (Cond18 sc) :=
  Prog.seq (liftQ (snocProg blank mark π (snocCS q a) a))
    (Prog.seq (liftQ (Prog.act (π1 Role.front, blank, Move.left) : Prog (ActQ sc) (CondQ sc)))
      (Prog.seq (Prog.act (Sum.inr π1 : Act18 sc))
        (Prog.seq (liftQ (tailProg blank mark π1 (tcOf (snoc q a))))
          (liftS feedStepRightAct8))))

/-- **`fillVec` の 1 マイクロステップの効果**：待ち行列 10 本 + 走査 8 本の
組み合わせテープに `fillVec π` を適用すると、待ち行列側は前方テープ
（役 `π Role.front`）を「読んで書き戻し、右へ」（`headT` の 2 動作目そのもの）、
走査側は `tT` に同じ値を書いて停留する（他は不変）。 -/
theorem fillWrite_step (blank : Fin sc) (π : Role → Role) (qt2 : QT sc)
    (T : Fin 8 → STape (Fin sc)) :
    (fun j => (Fin.append (TSQ qt2) T j).applyAction blank
        (fillVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) j))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right))
          (fun j => if j = PalPeg.GSTapes.tT
            then (T j).applyAction blank ((qt2 (π Role.front)).focus, Move.stay)
            else T j) := by
  have hfrontEq : (frontIdx π : Fin 18) = Fin.castAdd 8 (ridx (π Role.front)) := by
    simp only [frontIdx, Fin.castAddEmb_apply]
  have htTEq : (tTIdx : Fin 18) = Fin.natAdd 10 PalPeg.GSTapes.tT := by
    simp only [tTIdx, Fin.natAddEmb_apply]
  have hσfront : (Fin.append (TSQ qt2) T (frontIdx π)).focus
      = (qt2 (π Role.front)).focus := by
    rw [hfrontEq, Fin.append_left]
    simp [TSQ]
  have hfront : ∀ i : Fin 10, (Fin.castAdd 8 i = frontIdx π) ↔ i = ridx (π Role.front) := by
    intro i
    rw [hfrontEq]
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro h; subst h; rfl
  have hfrontFalse : ∀ k : Fin 8, (Fin.natAdd 10 k : Fin 18) ≠ frontIdx π := by
    intro k h
    rw [hfrontEq] at h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  have htTFalse1 : ∀ i : Fin 10, (Fin.castAdd 8 i : Fin 18) ≠ tTIdx := by
    intro i h
    rw [htTEq] at h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have htT : ∀ k : Fin 8, ((Fin.natAdd 10 k : Fin 18) = tTIdx) ↔ k = PalPeg.GSTapes.tT := by
    intro k
    rw [htTEq]
    constructor
    · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro h; subst h; rfl
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · show (Fin.append (TSQ qt2) T (Fin.castAdd 8 i)).applyAction blank
        (fillVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) (Fin.castAdd 8 i))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right))
          (fun j => if j = PalPeg.GSTapes.tT
            then (T j).applyAction blank ((qt2 (π Role.front)).focus, Move.stay) else T j)
          (Fin.castAdd 8 i)
    simp only [Fin.append_left, fillVec]
    rw [if_neg (htTFalse1 i)]
    by_cases hi : i = ridx (π Role.front)
    · rw [if_pos ((hfront i).2 hi), hσfront]
      subst hi
      simp only [TSQ, role_ridx]
      rw [act_apply, if_pos rfl, toS_step]
    · rw [if_neg (fun h => hi ((hfront i).1 h))]
      have hrole : role i ≠ π Role.front := fun h => hi (by rw [← ridx_role i, h])
      simp only [TSQ, act_apply, if_neg hrole]
      exact applyAction_focus_stay (toS (qt2 (role i)))
  · show (Fin.append (TSQ qt2) T (Fin.natAdd 10 k)).applyAction blank
        (fillVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) (Fin.natAdd 10 k))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right))
          (fun j => if j = PalPeg.GSTapes.tT
            then (T j).applyAction blank ((qt2 (π Role.front)).focus, Move.stay) else T j)
          (Fin.natAdd 10 k)
    simp only [Fin.append_right, fillVec]
    rw [if_neg (hfrontFalse k)]
    by_cases hk : k = PalPeg.GSTapes.tT
    · rw [if_pos ((htT k).2 hk), hσfront, if_pos hk]
    · rw [if_neg (fun h => hk ((htT k).1 h))]
      simp only [Fin.append_right, if_neg hk, applyAction_focus_stay]

/-- **完全な `feedRoundProg'` の `Exec`**：到着 → 前方テープの覗き見 → 跨ぎ書き込み
（`tT` への書き込みと前方テープの復元）→ `tail` の残り → 走査テープを 1 つ右へ、
という 5 段を `exec_seq`/`exec_act` で連結する。動作列の合計長は
`≤ 26 + 1 + 1 + 31 + 1 = 60`（`TextFeed.startRound'_cost` の `≤ 60` という上界と
ちょうど一致する）。 -/
theorem feedRound'_exec (hπ : Function.Injective π) (hne : mark ≠ blank) {qt0 : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ) (h : Encodes blank mark (qt0 ∘ π) q)
    (hq : Inv q) (T : Fin 8 → STape (Fin sc)) :
    ∃ (acts : List (Fin 18 → Fin sc × Move)) (π1 π2 : Role → Role) (qtFinal : QT sc),
      Function.Injective π1 ∧ acts.length ≤ 60 ∧ Function.Injective π2 ∧
      Encodes blank mark (qtFinal ∘ π2) (RTQueue.tail (snoc q a)) ∧
      Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
        (feedRoundProg' blank mark π π1 q a) (Fin.append (TSQ qt0) T) acts := by
  -- stage 1: arrive
  obtain ⟨n1, qt1, π1, L1, hE1, hlen1, hb1, hinj1, hqt1, hcost1, henc1, hrun1⟩ :=
    feedArrive_execQ (Terminal := Terminal) (blank := blank) (mark := mark) hπ hne a cst h hq
  have hArrive : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (liftQ (snocProg blank mark π (snocCS q a) a)) (Fin.append (TSQ qt0) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T))
        (avecsQ blank L1 qt0)) := by
    have h1 := liftQ_exec (blank := blank) (endSym := endSym) (mark := mark)
      (startSym := startSym) (Terminal := Terminal) hE1 (Fin.append (TSQ qt0) T)
    rwa [extend_castAdd_append] at h1
  -- stage 2: probe
  have hE2 : ExecQ Terminal blank
      (Prog.act (π1 Role.front, blank, Move.left) : Prog (ActQ sc) (CondQ sc))
      qt1 [⟨π1 Role.front, blank, Move.left⟩] := execQ_act (π1 Role.front) blank Move.left qt1
  set qt2 : QT sc := act blank qt1 (π1 Role.front) blank Move.left with hqt2def
  have hProbe : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (liftQ (Prog.act (π1 Role.front, blank, Move.left) : Prog (ActQ sc) (CondQ sc)))
      (Fin.append (TSQ qt1) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
        (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)) := by
    have h2 := liftQ_exec (blank := blank) (endSym := endSym) (mark := mark)
      (startSym := startSym) (Terminal := Terminal) hE2 (Fin.append (TSQ qt1) T)
    rwa [extend_castAdd_append] at h2
  have hmid1 : applyTrace blank (Fin.append (TSQ qt0) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T)) (avecsQ blank L1 qt0))
      = Fin.append (TSQ qt1) T := by
    nth_rewrite 1 [show (Fin.append (TSQ qt0) T : Fin 18 → STape (Fin sc))
      = extend (Fin.castAddEmb 8) (TSQ qt0) (Fin.append (TSQ qt0) T) from
      (extend_castAdd_append (TSQ qt0) (TSQ qt0) T).symm]
    rw [applyTrace_extend, applyTrace_avecsQ, extend_castAdd_append, hrun1]
  have hmid2 : applyTrace blank (Fin.append (TSQ qt1) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
        (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1))
      = Fin.append (TSQ qt2) T := by
    nth_rewrite 1 [show (Fin.append (TSQ qt1) T : Fin 18 → STape (Fin sc))
      = extend (Fin.castAddEmb 8) (TSQ qt1) (Fin.append (TSQ qt1) T) from
      (extend_castAdd_append (TSQ qt1) (TSQ qt1) T).symm]
    rw [applyTrace_extend, applyTrace_avecsQ, extend_castAdd_append]
    rfl
  -- stage 3: fillWrite
  have hFill : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (Prog.act (Sum.inr π1 : Act18 sc)) (Fin.append (TSQ qt2) T)
      [actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
        (Fin.append (TSQ qt2) T)] :=
    exec_act (inputFree_IFR2 blank endSym mark startSym) _ (Fin.append (TSQ qt2) T)
  set qt3 : QT sc :=
    act blank qt2 (π1 Role.front) (qt2 (π1 Role.front)).focus Move.right with hqt3def
  set Tscan3 : Fin 8 → STape (Fin sc) := fun j => if j = PalPeg.GSTapes.tT
    then (T j).applyAction blank ((qt2 (π1 Role.front)).focus, Move.stay) else T j
    with hTscan3def
  have hmid3 : applyTrace blank (Fin.append (TSQ qt2) T)
      [actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
        (Fin.append (TSQ qt2) T)]
      = Fin.append (TSQ qt3) Tscan3 := by
    show (fun j => (Fin.append (TSQ qt2) T j).applyAction blank
        (fillVec π1 (fun j' => (Fin.append (TSQ qt2) T j').focus) j)) = _
    exact fillWrite_step blank π1 qt2 T
  -- stage 4: the rest of `tail`
  have henc2 : Encodes blank mark (qt3 ∘ π1) (snoc q a) := by
    have hcomp1 : qt2 ∘ π1 = act blank (qt1 ∘ π1) Role.front blank Move.left :=
      act_comp_rename hinj1 blank qt1 Role.front blank Move.left
    have hcomp2 : qt3 ∘ π1
        = act blank (qt2 ∘ π1) Role.front ((qt2 ∘ π1) Role.front).focus Move.right :=
      act_comp_rename hinj1 blank qt2 Role.front (qt2 (π1 Role.front)).focus Move.right
    have hheadT : (headT blank (⟨qt1 ∘ π1, cst⟩ : RTQueueTapes.Run sc)).qt = qt3 ∘ π1 := by
      show act blank (act blank (qt1 ∘ π1) Role.front blank Move.left) Role.front
          ((act blank (qt1 ∘ π1) Role.front blank Move.left) Role.front).focus Move.right
        = qt3 ∘ π1
      rw [hcomp2, hcomp1]
    rw [← hheadT]
    exact headT_encodes henc1
  obtain ⟨n3, qt4, π2, hperf3, hb3, hinj2, hqt4, hcost4, henc4⟩ :=
    qtail_exec (Terminal := Terminal) (blank := blank) (mark := mark) hinj1 hne cst henc2
      (RTQueue.inv_snoc hq a)
  obtain ⟨L3, hE3, hlen3, hrun3⟩ := hperf3
  have hTail : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (liftQ (tailProg blank mark π1 (tcOf (snoc q a)))) (Fin.append (TSQ qt3) Tscan3)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
        (avecsQ blank L3 qt3)) := by
    have h4 := liftQ_exec (blank := blank) (endSym := endSym) (mark := mark)
      (startSym := startSym) (Terminal := Terminal) hE3 (Fin.append (TSQ qt3) Tscan3)
    rwa [extend_castAdd_append] at h4
  have hmid4 : applyTrace blank (Fin.append (TSQ qt3) Tscan3)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
        (avecsQ blank L3 qt3))
      = Fin.append (TSQ qt4) Tscan3 := by
    nth_rewrite 1 [show (Fin.append (TSQ qt3) Tscan3 : Fin 18 → STape (Fin sc))
      = extend (Fin.castAddEmb 8) (TSQ qt3) (Fin.append (TSQ qt3) Tscan3) from
      (extend_castAdd_append (TSQ qt3) (TSQ qt3) Tscan3).symm]
    rw [applyTrace_extend, applyTrace_avecsQ, extend_castAdd_append, hrun3]
  -- stage 5: stepRight
  have hStep : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (liftS feedStepRightAct8) (Fin.append (TSQ qt4) Tscan3)
      (List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
        [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
          (PalPeg.GSTapes.tT, true, Move.right) Tscan3]) := by
    have h5 := liftS_exec (blank := blank) (endSym := endSym) (mark := mark)
      (startSym := startSym) (Terminal := Terminal)
      (feedStepRight_exec8 (blank := blank) (endSym := endSym) (mark := mark)
        (startSym := startSym) (Terminal := Terminal) Tscan3) (Fin.append (TSQ qt4) Tscan3)
    rwa [extend_natAdd_append] at h5
  -- assemble
  have hgoal : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
      (feedRoundProg' blank mark π π1 q a) (Fin.append (TSQ qt0) T)
      (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T)) (avecsQ blank L1 qt0)
          ++ List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
            (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)
        ++ [actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
            (Fin.append (TSQ qt2) T)]
        ++ List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
          (avecsQ blank L3 qt3)
        ++ List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
          [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
            (PalPeg.GSTapes.tT, true, Move.right) Tscan3]) := by
    rw [feedRoundProg']
    have hStep2 : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
        (liftS feedStepRightAct8)
        (applyTrace blank (Fin.append (TSQ qt3) Tscan3)
          (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
            (avecsQ blank L3 qt3)))
        (List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
          [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
            (PalPeg.GSTapes.tT, true, Move.right) Tscan3]) := by
      rw [hmid4]; exact hStep
    have hDE := exec_seq hTail hStep2
    have hFill2 : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
        ((liftQ (tailProg blank mark π1 (tcOf (snoc q a)))).seq (liftS feedStepRightAct8))
        (applyTrace blank (Fin.append (TSQ qt2) T)
          [actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
            (Fin.append (TSQ qt2) T)])
        (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
            (avecsQ blank L3 qt3)
          ++ List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
            [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
              (PalPeg.GSTapes.tT, true, Move.right) Tscan3]) := by
      rw [hmid3]; exact hDE
    have hCDE := exec_seq hFill hFill2
    have hProbe2 : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
        ((Prog.act (Sum.inr π1 : Act18 sc)).seq
          ((liftQ (tailProg blank mark π1 (tcOf (snoc q a)))).seq (liftS feedStepRightAct8)))
        (applyTrace blank (Fin.append (TSQ qt1) T)
          (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
            (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)))
        ([actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
            (Fin.append (TSQ qt2) T)]
          ++ (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
              (avecsQ blank L3 qt3)
            ++ List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
              [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
                (PalPeg.GSTapes.tT, true, Move.right) Tscan3])) := by
      rw [hmid2]; exact hCDE
    have hBCDE := exec_seq hProbe hProbe2
    have hArrive2 : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank
        ((liftQ (Prog.act (π1 Role.front, blank, Move.left) : Prog (ActQ sc) (CondQ sc))).seq
          ((Prog.act (Sum.inr π1 : Act18 sc)).seq
            ((liftQ (tailProg blank mark π1 (tcOf (snoc q a)))).seq
              (liftS feedStepRightAct8))))
        (applyTrace blank (Fin.append (TSQ qt0) T)
          (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T)) (avecsQ blank L1 qt0)))
        (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
            (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)
          ++ ([actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
                (Fin.append (TSQ qt2) T)]
            ++ (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
                (avecsQ blank L3 qt3)
              ++ List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
                [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
                  (PalPeg.GSTapes.tT, true, Move.right) Tscan3]))) := by
      rw [hmid1]; exact hBCDE
    have hfinal := exec_seq hArrive hArrive2
    simpa only [Prog.seq, feedRoundProg', List.append_assoc] using hfinal
  refine ⟨_, π1, π2, qt4, hinj1, ?_, hinj2, henc4, hgoal⟩
  have e1 : (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T))
      (avecsQ blank L1 qt0)).length = n1 := by
    rw [List.length_map, avecsQ_length, hlen1]
  have e2 : (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
      (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)).length = 1 := by
    rw [List.length_map, avecsQ_length]
    rfl
  have e3 : (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
      (avecsQ blank L3 qt3)).length = n3 := by
    rw [List.length_map, avecsQ_length, hlen3]
  have e4 : ([actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
      (Fin.append (TSQ qt2) T)] : List (Fin 18 → Fin sc × Move)).length = 1 := rfl
  have e5 : (List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
      [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
        (PalPeg.GSTapes.tT, true, Move.right) Tscan3]).length = 1 := by
    rw [List.length_map]
    rfl
  have hlen_total : (List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt0) T))
        (avecsQ blank L1 qt0)
      ++ List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt1) T))
        (avecsQ blank [⟨π1 Role.front, blank, Move.left⟩] qt1)
      ++ [actVec (IFR2 (Terminal := Terminal) blank endSym mark startSym) (Sum.inr π1)
          (Fin.append (TSQ qt2) T)]
      ++ List.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt3) Tscan3))
        (avecsQ blank L3 qt3)
      ++ List.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt4) Tscan3))
        [actVec (I8 (Terminal := Terminal) blank endSym mark startSym)
          (PalPeg.GSTapes.tT, true, Move.right) Tscan3]).length
      = n1 + 1 + 1 + n3 + 1 := by
    simp only [List.length_append, e1, e2, e3, e4, e5]
  rw [hlen_total]
  omega

/-- **停止**：`feedRoundProg'` は `acts.length ≤ 60` マイクロステップで停止する
（`feedRound'_exec` が与える具体的な動作列に `exec_halts` を適用するだけ）。 -/
theorem feedRound'_halts (hπ : Function.Injective π) (hne : mark ≠ blank) {qt0 : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ) (h : Encodes blank mark (qt0 ∘ π) q)
    (hq : Inv q) (T : Fin 8 → STape (Fin sc)) :
    ∃ (π1 : Role → Role) (n : ℕ), n ≤ 60 ∧
      ∀ (l : List (Option Terminal)), l.length = n → ∀ (x : Option Terminal),
        (runInputs (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
            ([feedRoundProg' blank mark π π1 q a], Fin.append (TSQ qt0) T)).1 = [] := by
  obtain ⟨acts, π1, π2, qtFinal, hinj1, hlen, hinj2, henc, hex⟩ :=
    feedRound'_exec hπ hne a cst h hq T
  exact ⟨π1, acts.length, hlen, fun l hl x => exec_halts hex l hl x⟩

/-- **マイクロステップ上界の内訳**：`到着 ≤26` + `probe =1` + `跨ぎ書き込み =1`
+ `tail の残り ≤31` + `stepRight =1` `= 60`。これは `TextFeed.startRound'_cost`
自身が主張する償却上界 `≤ 60` にちょうど一致する。 -/
theorem feedRound'_bound {Terminal : Type} (hπ : Function.Injective π) (hne : mark ≠ blank)
    {qt0 : QT sc}
    {q : Queue (Fin sc)} (a : Fin sc) (cst : ℕ) (h : Encodes blank mark (qt0 ∘ π) q)
    (hq : Inv q) :
    ∃ (n1 n3 : ℕ), n1 ≤ 26 ∧ n3 ≤ 31 ∧ n1 + 1 + 1 + n3 + 1 ≤ 60 := by
  obtain ⟨n1, qt1, π1, L1, hE1, hlen1, hb1, hinj1, hqt1, hcost1, henc1, hrun1⟩ :=
    feedArrive_execQ (Terminal := Terminal) (blank := blank) (mark := mark) hπ hne a cst h hq
  set qt2 : QT sc := act blank qt1 (π1 Role.front) blank Move.left with hqt2def
  set qt3 : QT sc :=
    act blank qt2 (π1 Role.front) (qt2 (π1 Role.front)).focus Move.right with hqt3def
  have henc2 : Encodes blank mark (qt3 ∘ π1) (snoc q a) := by
    have hcomp1 : qt2 ∘ π1 = act blank (qt1 ∘ π1) Role.front blank Move.left :=
      act_comp_rename hinj1 blank qt1 Role.front blank Move.left
    have hcomp2 : qt3 ∘ π1
        = act blank (qt2 ∘ π1) Role.front ((qt2 ∘ π1) Role.front).focus Move.right :=
      act_comp_rename hinj1 blank qt2 Role.front (qt2 (π1 Role.front)).focus Move.right
    have hheadT : (headT blank (⟨qt1 ∘ π1, cst⟩ : RTQueueTapes.Run sc)).qt = qt3 ∘ π1 := by
      show act blank (act blank (qt1 ∘ π1) Role.front blank Move.left) Role.front
          ((act blank (qt1 ∘ π1) Role.front blank Move.left) Role.front).focus Move.right
        = qt3 ∘ π1
      rw [hcomp2, hcomp1]
    rw [← hheadT]
    exact headT_encodes henc1
  obtain ⟨n3, qt4, π2, hperf3, hb3, hinj2, hqt4, hcost4, henc4⟩ :=
    qtail_exec (Terminal := Terminal) (blank := blank) (mark := mark) hinj1 hne cst henc2
      (RTQueue.inv_snoc hq a)
  exact ⟨n1, n3, hb1, hb3, by omega⟩

end Exec

end PalPeg.TextFeedProg

#print axioms PalPeg.TextFeedProg.feedRound_exec
#print axioms PalPeg.TextFeedProg.feedRound_halts
#print axioms PalPeg.TextFeedProg.feedRound_bound
#print axioms PalPeg.TextFeedProg.feedArrive_matches_arrive'
#print axioms PalPeg.TextFeedProg.feedStepRight_matches_stepRight'
#print axioms PalPeg.TextFeedProg.fillWrite_step
#print axioms PalPeg.TextFeedProg.feedRound'_exec
#print axioms PalPeg.TextFeedProg.feedRound'_halts
#print axioms PalPeg.TextFeedProg.feedRound'_bound
