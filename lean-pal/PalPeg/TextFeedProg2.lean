import PalPeg.TextFeedProg

/-!
# オンライン走査フェーズのプログラム化 (`TextFeedProg2`)

`PalPeg.TextFeedProg` は `PalPeg.TextFeed` の **起動フェーズ**（`startT'`／
`startRound' = stepRight' ∘ fill' ∘ arrive'`）を 18 本テープ上の構造化プログラム
`feedRoundProg'` として移植した。本ファイルはその続きで、**オンライン走査フェーズ**
（`onlineT'`／`roundT' = runInT' … ∘ arrive'`）を同じ 18 本テープ上のプログラムに
する。

## 抽象側の形

```
runInT' … 0       M = M
runInT' … (j+1)   M = if Enabled v n (fillIf' … M).st
                      then runInT' … j (scanOne' … (fillIf' … M))
                      else fillIf' … M
roundT' … n a M   = runInT' … (n+1) … (gsRate k) (arrive' … a M)
onlineT' … (n+1) M = roundT' … (s+n) … (onlineT' … n M)
```

つまり 1 ラウンドは「到着（待ち行列への `snoc`）」＋「`gsRate k` 回の
『必要なら供給してから、可能なら走査を 1 歩』」である。

## 条件をテープ読みで実現する

`Enabled v n st = (st.q = |v| ∨ st.pos + st.q < n)` はゴースト量の比較だが、
供給の不変条件 `FeedInv'` のもとでは **ヘッドの読みだけ** で決まる：

* `st.q = |v|` ⇔ 走査テープ `tP` の読みが `endSym`（`endSym ∉ v` が必要）。
* `fillIf'` を通した **あと** では `st.pos + st.q < n` ⇔ `tT` の読みが空白でない
  （`blank ∉ Text` が必要）。

供給するかどうかの判定 `fillIf'` の条件 `st.pos + st.q = M.m ∧ M.m < n` も同様に

* `st.pos + st.q = M.m` ⇔ `tT` の読みが空白、
* `M.m < n` ⇔ 待ち行列が空でない ⇔ 前方テープの **1 動作のプローブ後** の読みが
  `mark` でない（`RTQueueTapes.headT_read`）

で読める。したがって条件識別子を 2 個 (`XCond.enabled` / `XCond.fillNow`) 足せば、
分岐はすべて「全ヘッドの読み `σ` の述語」になる（`Interp.condOf` の形）。

## 動作識別子の追加

`TextFeedProg.fillVec`（前方テープの読みを `tT` へ書きつつ前方テープを復元する
跨ぎ動作）に加えて、**供給しない**場合にプローブを打ち消す `restoreVec`
（前方テープの読みを書き戻して右へ、`tT` には触らない）を足す。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.TextFeedProg2

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.RTQueue
open PalPeg.RTQueueTapes
open PalPeg.RTQueueProg (ActQ CondQ IQ CS csOf snocProg snocCS qsnoc_exec Performs ExecQ TSQ
  avecsQ avecsQ_length applyTrace_avecsQ ridx role role_ridx ridx_role execQ_act inputFree_IQ TC
  tcOf tailProg qtail_exec act_comp_rename toS toS_step toS_focus)
open PalPeg.GSProg (Act8 Cond8 I8 inputFree_I8 scanProg TS)
open PalPeg.TextFeedProg (IFR IFR2 Act18 Cond18 liftQ liftS liftQ_exec liftS_exec fillVec
  frontIdx tTIdx inputFree_IFR2 fillWrite_step feedStepRightAct8)

variable {sc : ℕ} {Terminal : Type}

/-! ## 1. 追加の動作識別子・条件識別子と、その解釈 -/

/-- 追加の動作識別子。`fill π` は `TextFeedProg.fillVec π`（跨ぎ書き込み）、
`restore π` は「前方テープの読みを書き戻して右へ」（プローブの打ち消し）。 -/
inductive XAct where
  | fill (π : Role → Role)
  | restore (π : Role → Role)

/-- 追加の条件識別子。 -/
inductive XCond where
  /-- 「まだ 1 歩進める」（`Enabled`）：`tP` が `endSym` を読む、または `tT` が
  空白でない。 -/
  | enabled
  /-- 「いま供給すべき」：`tT` が空白を読み、かつ（プローブ後の）前方テープが
  `mark` でない（＝待ち行列が空でない）。 -/
  | fillNow (π : Role → Role)

/-- 18 本テープ上の動作識別子（オンライン版）。 -/
abbrev ActE (sc : ℕ) := Act18 sc ⊕ XAct

/-- 18 本テープ上の条件識別子（オンライン版）。 -/
abbrev CondE (sc : ℕ) := Cond18 sc ⊕ XCond

/-- 走査側（`Fin 18` の中の）`tP` の添字。 -/
noncomputable def tPIdx : Fin 18 := Fin.natAddEmb 10 PalPeg.GSTapes.tP

/-- プローブの打ち消し：前方テープに読んだ値を書き戻して右へ動く（他は不変）。 -/
noncomputable def restoreVec (π : Role → Role) (σ : Fin 18 → Fin sc) :
    Fin 18 → Fin sc × Move :=
  fun j => if j = frontIdx π then (σ (frontIdx π), Move.right) else (σ j, Move.stay)

/-- `IFR2` を拡張した、オンライン走査フェーズ用の 18 本テープの解釈。 -/
noncomputable def IFO (blank endSym mark startSym : Fin sc) :
    Interp Terminal (ActE sc) (CondE sc) (Fin sc) 18 where
  actOf
    | Sum.inl a, x, σ => (IFR2 (Terminal := Terminal) blank endSym mark startSym).actOf a x σ
    | Sum.inr (XAct.fill π), _, σ => fillVec π σ
    | Sum.inr (XAct.restore π), _, σ => restoreVec π σ
  condOf
    | Sum.inl c, σ => (IFR2 (Terminal := Terminal) blank endSym mark startSym).condOf c σ
    | Sum.inr XCond.enabled, σ => decide (σ tPIdx = endSym ∨ σ tTIdx ≠ blank)
    | Sum.inr (XCond.fillNow π), σ => decide (σ tTIdx = blank ∧ σ (frontIdx π) ≠ mark)

theorem inputFree_IFO (blank endSym mark startSym : Fin sc) :
    InputFree (IFO (Terminal := Terminal) blank endSym mark startSym) := by
  intro a x σ
  cases a with
  | inl a => exact inputFree_IFR2 (Terminal := Terminal) blank endSym mark startSym a x σ
  | inr b => cases b <;> rfl

/-! ## 2. `IFR2` のプログラムの持ち上げ -/

/-- `IFR2` 上のプログラムを `IFO` 上へ埋め込む。 -/
noncomputable def liftE (p : Prog (Act18 sc) (Cond18 sc)) : Prog (ActE sc) (CondE sc) :=
  Prog.map (Sum.inl (β := XAct)) (Sum.inl (β := XCond)) p

theorem liftE_exec {blank endSym mark startSym : Fin sc} {p : Prog (Act18 sc) (Cond18 sc)}
    {T : Fin 18 → STape (Fin sc)} {acts : List (Fin 18 → Fin sc × Move)}
    (h : Exec (IFR2 (Terminal := Terminal) blank endSym mark startSym) blank p T acts) :
    Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank (liftE p) T acts :=
  exec_map (I₁ := IFR2 (Terminal := Terminal) blank endSym mark startSym)
    (I₂ := IFO (Terminal := Terminal) blank endSym mark startSym)
    (fun _ _ => rfl) (fun _ _ _ => rfl) h

/-- 待ち行列側のプログラムの `IFO` への移送。 -/
theorem liftEQ_exec {blank endSym mark startSym : Fin sc} {p : Prog (ActQ sc) (CondQ sc)}
    {qt : QT sc} {acts : List (Fin 10 → Fin sc × Move)}
    (h : Exec (IQ (k := sc) Terminal) blank p (TSQ qt) acts) (T : Fin 8 → STape (Fin sc)) :
    Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank (liftE (liftQ p))
      (Fin.append (TSQ qt) T)
      (acts.map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))) := by
  have h1 := liftQ_exec (blank := blank) (endSym := endSym) (mark := mark)
    (startSym := startSym) (Terminal := Terminal) h (Fin.append (TSQ qt) T)
  rw [extend_castAdd_append] at h1
  exact liftE_exec h1

/-- 走査側のプログラムの `IFO` への移送。 -/
theorem liftES_exec {blank endSym mark startSym : Fin sc} {p : Prog Act8 Cond8}
    {qt : QT sc} {T : Fin 8 → STape (Fin sc)} {acts : List (Fin 8 → Fin sc × Move)}
    (h : Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank p T acts) :
    Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank (liftE (liftS p))
      (Fin.append (TSQ qt) T)
      (acts.map (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt) T))) := by
  have h1 := liftS_exec (blank := blank) (endSym := endSym) (mark := mark)
    (startSym := startSym) (Terminal := Terminal) h (Fin.append (TSQ qt) T)
  rw [extend_natAdd_append] at h1
  exact liftE_exec h1

/-! ## 3. 18 本テープの読み -/

section Reads

variable {blank endSym mark startSym : Fin sc}

@[simp] theorem append_scan (qt : QT sc) (T : Fin 8 → STape (Fin sc)) (i : Fin 8) :
    Fin.append (TSQ qt) T (Fin.natAddEmb 10 i) = T i := by
  rw [Fin.natAddEmb_apply, Fin.append_right]

@[simp] theorem append_queue (qt : QT sc) (T : Fin 8 → STape (Fin sc)) (j : Fin 10) :
    Fin.append (TSQ qt) T (Fin.castAddEmb 8 j) = TSQ qt j := by
  rw [Fin.castAddEmb_apply, Fin.append_left]

theorem focus_tPIdx (qt : QT sc) (ts : PalPeg.GSTapes.TapesState' sc) :
    (Fin.append (TSQ qt) (TS ts) (tPIdx : Fin 18)).focus
      = Tape.read (ts PalPeg.GSTapes.tP) := by
  rw [tPIdx, append_scan]; rfl

theorem focus_tTIdx (qt : QT sc) (ts : PalPeg.GSTapes.TapesState' sc) :
    (Fin.append (TSQ qt) (TS ts) (tTIdx : Fin 18)).focus
      = Tape.read (ts PalPeg.GSTapes.tT) := by
  rw [PalPeg.TextFeedProg.tTIdx, append_scan]; rfl

theorem focus_frontIdx (qt : QT sc) (T : Fin 8 → STape (Fin sc)) (π : Role → Role) :
    (Fin.append (TSQ qt) T (frontIdx π)).focus = (qt (π Role.front)).focus := by
  rw [frontIdx, append_queue]
  show (qt (role (ridx (π Role.front)))).focus = _
  rw [role_ridx]

end Reads

/-! ## 4. 条件のテープ読みによる実現 -/

section Conds

open PalPeg.TextFeed
open PalPeg.GSTapes (tP tT)

variable {blank startSym endSym mark : Fin sc} {v Text : List (Fin sc)} {k p₁ r n : ℕ}

/-- `padW` の先端セル（添字 `m`）は空白。 -/
theorem padW_getElem?_self (blank : Fin sc) (Text : List (Fin sc)) {m : ℕ}
    (hm : m ≤ Text.length) : (padW blank Text m)[m]? = some blank := by
  have hlen : (Text.take m).length = m := by simp only [List.length_take]; omega
  rw [padW, List.getElem?_append_right (by omega), hlen, Nat.sub_self,
    List.getElem?_replicate]
  exact if_pos (by omega)

/-- **`tT` の読みが空白 ⇔ 走査ヘッドが書き込み先端にいる**（`blank ∉ Text` が必要）。 -/
theorem read_tT_blank_iff {M : Machine' sc} (hblank : blank ∉ Text) (hn : n ≤ Text.length)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    Tape.read (M.ts tT) = blank ↔ M.st.pos + M.st.q = M.m := by
  have hmT : M.m ≤ Text.length := le_trans h.mle hn
  have hr := h.scan.txt.read_eq
  constructor
  · intro hb
    by_contra hne
    have hlt : M.st.pos + M.st.q < M.m := lt_of_le_of_ne h.hd hne
    rw [padW_getElem?_of_lt hmT hlt] at hr
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp hr
    have hmem : Tape.read (M.ts tT) ∈ Text := hx ▸ List.getElem_mem hi
    exact hblank (hb ▸ hmem)
  · intro he
    rw [he, padW_getElem?_self blank Text hmT] at hr
    exact (Option.some_inj.mp hr).symm

/-- **`tP` の読みが `endSym` ⇔ 一致長が `|v|`**（`endSym ∉ v` が必要）。 -/
theorem read_tP_end_iff {ts : PalPeg.GSTapes.TapesState' sc} {st : ScanState}
    (hend : endSym ∉ v) (hq : st.q ≤ v.length)
    (hE : PalPeg.GSTapes.Encodes' blank startSym endSym mark v Text k p₁ r ts st) :
    Tape.read (ts tP) = endSym ↔ st.q = v.length := by
  constructor
  · intro hb
    by_contra hne
    have hlt : st.q < v.length := lt_of_le_of_ne hq hne
    have h := PalPeg.GSTapes.read_P_lt' hE hlt
    obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
    have hmem : Tape.read (ts tP) ∈ v := hx ▸ List.getElem_mem hi
    exact hend (hb ▸ hmem)
  · intro he; exact PalPeg.GSTapes.read_P_end' hE he

/-- **待ち行列が空でない ⇔ 書き込み済みが到着済みより真に少ない**。 -/
theorem queue_nonempty_iff {M : Machine' sc} (hn : n ≤ Text.length)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    RTQueue.toList M.Q ≠ [] ↔ M.m < n := by
  have hlen : (Text.take n).length = n := by simp only [List.length_take]; omega
  rw [h.qlist]
  constructor
  · intro hne
    by_contra hle
    have : (Text.take n).drop M.m = [] := List.drop_eq_nil_of_le (by omega)
    exact hne this
  · intro hlt hnil
    have := List.length_eq_zero_iff.mpr hnil
    rw [List.length_drop, hlen] at this
    omega

/-- **待ち行列の先頭（空なら `mark`）が `mark` でない ⇔ 待ち行列が空でない**
（`mark ∉ Text` が必要）。プローブ後の前方テープの読みはこの値である
（`RTQueueTapes.headT_read`）。 -/
theorem head_ne_mark_iff {M : Machine' sc} (hmark : mark ∉ Text) (hn : n ≤ Text.length)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    (RTQueue.head? M.Q).getD mark ≠ mark ↔ M.m < n := by
  rw [← queue_nonempty_iff (startSym := startSym) (endSym := endSym) (v := v) (k := k)
    (p₁ := p₁) (r := r) hn h, RTQueue.head?_eq h.qinv]
  have hsub : ∀ x, x ∈ RTQueue.toList M.Q → x ∈ Text := by
    intro x hx
    rw [h.qlist] at hx
    exact List.mem_of_mem_take (List.mem_of_mem_drop hx)
  cases hl : RTQueue.toList M.Q with
  | nil => simp
  | cons x xs =>
      have hxT : x ∈ Text := hsub x (by rw [hl]; exact List.mem_cons_self ..)
      have : x ≠ mark := fun he => hmark (he ▸ hxT)
      simp [this]

end Conds

/-! ## 5. 供給ステップ（`fillIf'`）のプログラム -/

section FillStep

open PalPeg.TextFeed
open PalPeg.GSTapes (tP tT)

variable {blank endSym mark startSym : Fin sc}

/-- 前方テープの 1 動作プローブ（`RTQueueTapes.headProbe` そのもの）。 -/
noncomputable def probeProg (blank : Fin sc) (π : Role → Role) :
    Prog (Act18 sc) (Cond18 sc) :=
  liftQ (Prog.act ((π Role.front, blank, Move.left) : ActQ sc))

/-- 供給する側の枝：跨ぎ書き込み（`fillVec`）＋待ち行列の `tail`。 -/
noncomputable def fillBranchProg (blank mark : Fin sc) (π : Role → Role)
    (q : Queue (Fin sc)) : Prog (ActE sc) (CondE sc) :=
  Prog.seq (Prog.act (Sum.inr (XAct.fill π) : ActE sc))
    (liftE (liftQ (tailProg blank mark π (tcOf q))))

/-- **`fillIf'` に対応するプログラム**：プローブしてから、
「`tT` が空白 かつ 待ち行列が空でない」なら供給し、さもなくばプローブを打ち消す。 -/
noncomputable def fillStepProg (blank mark : Fin sc) (π : Role → Role)
    (q : Queue (Fin sc)) : Prog (ActE sc) (CondE sc) :=
  Prog.seq (liftE (probeProg blank π))
    (Prog.ite (Sum.inr (XCond.fillNow π) : CondE sc) (fillBranchProg blank mark π q)
      (Prog.act (Sum.inr (XAct.restore π) : ActE sc)))

/-- 待ち行列側の動作列を 18 本テープへ拡張して適用した結果。 -/
theorem queue_applyTrace (blank : Fin sc) (qt : QT sc) (L : List (Act sc))
    (T : Fin 8 → STape (Fin sc)) :
    applyTrace blank (Fin.append (TSQ qt) T)
        ((avecsQ blank L qt).map (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T)))
      = Fin.append (TSQ (run blank qt L)) T := by
  nth_rewrite 1 [show (Fin.append (TSQ qt) T : Fin 18 → STape (Fin sc))
    = extend (Fin.castAddEmb 8) (TSQ qt) (Fin.append (TSQ qt) T) from
    (extend_castAdd_append (TSQ qt) (TSQ qt) T).symm]
  rw [applyTrace_extend, applyTrace_avecsQ, extend_castAdd_append]

/-- **`restoreVec` の 1 マイクロステップの効果**：前方テープを「読んで書き戻して右へ」
（`headT` の 2 動作目）動かし、走査側は一切触らない。 -/
theorem restore_step (blank : Fin sc) (π : Role → Role) (qt2 : QT sc)
    (T : Fin 8 → STape (Fin sc)) :
    (fun j => (Fin.append (TSQ qt2) T j).applyAction blank
        (restoreVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) j))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right)) T := by
  have hfrontEq : (frontIdx π : Fin 18) = Fin.castAdd 8 (ridx (π Role.front)) := by
    simp only [frontIdx, Fin.castAddEmb_apply]
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
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · show (Fin.append (TSQ qt2) T (Fin.castAdd 8 i)).applyAction blank
        (restoreVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) (Fin.castAdd 8 i))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right)) T
          (Fin.castAdd 8 i)
    simp only [Fin.append_left, restoreVec]
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
        (restoreVec π (fun j' => (Fin.append (TSQ qt2) T j').focus) (Fin.natAdd 10 k))
      = Fin.append
          (TSQ (act blank qt2 (π Role.front) (qt2 (π Role.front)).focus Move.right)) T
          (Fin.natAdd 10 k)
    simp only [Fin.append_right, restoreVec]
    rw [if_neg (hfrontFalse k)]
    simp only [applyAction_focus_stay]

/-- プローブ後の前方テープの読み。 -/
theorem probe_focus {qt : QT sc} {π : Role → Role} {q : Queue (Fin sc)}
    (hinj : Function.Injective π) (henc : Encodes blank mark (qt ∘ π) q) :
    ((act blank qt (π Role.front) blank Move.left) (π Role.front)).focus
      = (RTQueue.head? q).getD mark := by
  have hc : (act blank qt (π Role.front) blank Move.left) ∘ π
      = act blank (qt ∘ π) Role.front blank Move.left :=
    act_comp_rename hinj blank qt Role.front blank Move.left
  have h1 : ((act blank qt (π Role.front) blank Move.left) (π Role.front))
      = (act blank (qt ∘ π) Role.front blank Move.left) Role.front := by
    have := congrFun hc Role.front
    exact this
  rw [h1]
  exact headT_read henc

/-- 供給の分岐条件のテープ読みによる評価。 -/
theorem cond_fillNow {v Text : List (Fin sc)} {k p₁ r n : ℕ} {M : Machine' sc}
    {qt : QT sc} {π : Role → Role} (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hn : n ≤ Text.length) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π) M.Q)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    (IFO (Terminal := Terminal) blank endSym mark startSym).condOf
        (Sum.inr (XCond.fillNow π) : CondE sc)
        (fun j => (Fin.append (TSQ (act blank qt (π Role.front) blank Move.left))
          (TS M.ts) j).focus)
      = decide (M.st.pos + M.st.q = M.m ∧ M.m < n) := by
  show decide ((Fin.append (TSQ (act blank qt (π Role.front) blank Move.left)) (TS M.ts)
        (tTIdx : Fin 18)).focus = blank ∧
      (Fin.append (TSQ (act blank qt (π Role.front) blank Move.left)) (TS M.ts)
        (frontIdx π)).focus ≠ mark) = _
  rw [focus_tTIdx, focus_frontIdx, probe_focus hinj henc]
  exact decide_eq_decide.mpr (and_congr (read_tT_blank_iff hblank hn h)
    (head_ne_mark_iff (startSym := startSym) (endSym := endSym) (v := v) (k := k)
      (p₁ := p₁) (r := r) hmark hn h))

/-- **`fillStepProg` の `Exec`**：`fillIf'` をちょうど実現する。供給する枝は
`プローブ 1 + 跨ぎ書き込み 1 + tail ≤ 31 = ≤ 33` マイクロステップ（抽象側の
`fill'` のコスト上界 `33` に一致）、供給しない枝は `2` マイクロステップ。 -/
theorem fillStep_exec {v Text : List (Fin sc)} {k p₁ r n : ℕ} {M : Machine' sc}
    {qt : QT sc} {π : Role → Role}
    (hne : mark ≠ blank) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hn : n ≤ Text.length) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π) M.Q)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    ∃ (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc) (π' : Role → Role),
      Function.Injective π' ∧ acts.length ≤ 33 ∧
      Encodes blank mark (qt' ∘ π') (fillIf' blank mark n M).Q ∧
      applyTrace blank (Fin.append (TSQ qt) (TS M.ts)) acts
        = Fin.append (TSQ qt') (TS (fillIf' blank mark n M).ts) ∧
      Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (fillStepProg blank mark π M.Q) (Fin.append (TSQ qt) (TS M.ts)) acts := by
  classical
  set T : Fin 8 → STape (Fin sc) := TS M.ts with hTdef
  set qt1 : QT sc := act blank qt (π Role.front) blank Move.left with hqt1
  -- プローブ
  have hProbeQ : ExecQ Terminal blank
      (Prog.act ((π Role.front, blank, Move.left) : ActQ sc)) qt
      [⟨π Role.front, blank, Move.left⟩] := execQ_act (π Role.front) blank Move.left qt
  have hProbe : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
      (liftE (probeProg blank π)) (Fin.append (TSQ qt) T)
      ((avecsQ blank [⟨π Role.front, blank, Move.left⟩] qt).map
        (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))) :=
    liftEQ_exec (endSym := endSym) (startSym := startSym) hProbeQ T
  have hmid1 : applyTrace blank (Fin.append (TSQ qt) T)
      ((avecsQ blank [⟨π Role.front, blank, Move.left⟩] qt).map
        (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T)))
      = Fin.append (TSQ qt1) T := by
    rw [queue_applyTrace]; rfl
  have hlen1 : ((avecsQ blank [(⟨π Role.front, blank, Move.left⟩ : Act sc)] qt).map
      (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T))).length = 1 := by
    rw [List.length_map, avecsQ_length]; rfl
  -- 供給後の待ち行列テープ（`headT` の 2 動作目まで）
  set qt2 : QT sc := act blank qt1 (π Role.front) (qt1 (π Role.front)).focus Move.right
    with hqt2
  have hcomp1 : qt1 ∘ π = act blank (qt ∘ π) Role.front blank Move.left :=
    act_comp_rename hinj blank qt Role.front blank Move.left
  have hcomp2 : qt2 ∘ π
      = act blank (qt1 ∘ π) Role.front ((qt1 ∘ π) Role.front).focus Move.right :=
    act_comp_rename hinj blank qt1 Role.front (qt1 (π Role.front)).focus Move.right
  have henc2 : Encodes blank mark (qt2 ∘ π) M.Q := by
    have hheadT : (headT blank (⟨qt ∘ π, 0⟩ : RTQueueTapes.Run sc)).qt = qt2 ∘ π := by
      show act blank (act blank (qt ∘ π) Role.front blank Move.left) Role.front
          ((act blank (qt ∘ π) Role.front blank Move.left) Role.front).focus Move.right
        = qt2 ∘ π
      rw [hcomp2, hcomp1]
    rw [← hheadT]
    exact headT_encodes henc
  have hfocus : (qt1 (π Role.front)).focus = peek blank M.R := by
    rw [probe_focus hinj henc]
    exact (RTQueueTapes.headT_read h.buf).symm
  -- 条件の評価
  have hcond := cond_fillNow (Terminal := Terminal) (startSym := startSym)
    (endSym := endSym) (v := v) (k := k) (p₁ := p₁) (r := r) hblank hmark hn hinj henc h
  by_cases hc : M.st.pos + M.st.q = M.m ∧ M.m < n
  · -- 供給する
    have hfill : fillIf' blank mark n M = fill' blank mark M := if_pos hc
    have hcondT : (IFO (Terminal := Terminal) blank endSym mark startSym).condOf
        (Sum.inr (XCond.fillNow π) : CondE sc)
        (fun j => (Fin.append (TSQ qt1) T j).focus) = true := by
      rw [hcond]; exact decide_eq_true hc
    -- 跨ぎ書き込み
    have hFillE : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (Prog.act (Sum.inr (XAct.fill π) : ActE sc)) (Fin.append (TSQ qt1) T)
        [actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
          (Sum.inr (XAct.fill π)) (Fin.append (TSQ qt1) T)] :=
      exec_act (inputFree_IFO blank endSym mark startSym) _ _
    have hTS : (fun j : Fin 8 => if j = PalPeg.GSTapes.tT
          then (T j).applyAction blank ((qt1 (π Role.front)).focus, Move.stay) else T j)
        = TS (fill' blank mark M).ts := by
      funext j
      show (if j = PalPeg.GSTapes.tT
          then (TS M.ts j).applyAction blank ((qt1 (π Role.front)).focus, Move.stay)
          else TS M.ts j) = _
      by_cases hj : j = PalPeg.GSTapes.tT
      · subst hj
        rw [if_pos rfl, hfocus]
        show (PalPeg.GSProg.toS (M.ts PalPeg.GSTapes.tT)).applyAction blank
            (peek blank M.R, Move.stay)
          = PalPeg.GSProg.toS (PalPeg.GSTapes.upd M.ts PalPeg.GSTapes.tT
              (Tape.step blank (M.ts PalPeg.GSTapes.tT) (peek blank M.R) Move.stay)
              PalPeg.GSTapes.tT)
        rw [PalPeg.GSTapes.upd_self, PalPeg.GSProg.toS_step]
      · rw [if_neg hj]
        show PalPeg.GSProg.toS (M.ts j)
          = PalPeg.GSProg.toS (PalPeg.GSTapes.upd M.ts PalPeg.GSTapes.tT
              (Tape.step blank (M.ts PalPeg.GSTapes.tT) (peek blank M.R) Move.stay) j)
        rw [PalPeg.GSTapes.upd_ne _ _ hj]
    have hmid2 : applyTrace blank (Fin.append (TSQ qt1) T)
        [actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
          (Sum.inr (XAct.fill π)) (Fin.append (TSQ qt1) T)]
        = Fin.append (TSQ qt2) (TS (fill' blank mark M).ts) := by
      rw [applyTrace_cons, applyTrace_nil, ← hTS]
      exact fillWrite_step blank π qt1 T
    -- tail
    obtain ⟨n3, qt3, π2, hperf3, hb3, hinj2, hqt3, _, henc3⟩ :=
      qtail_exec (Terminal := Terminal) (blank := blank) (mark := mark) hinj hne 0 henc2 h.qinv
    obtain ⟨L3, hE3, hlen3, hrun3⟩ := hperf3
    have hTail : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (liftE (liftQ (tailProg blank mark π (tcOf M.Q))))
        (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts))
        ((avecsQ blank L3 qt2).map
          (extendVec (Fin.castAddEmb 8)
            (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts)))) :=
      liftEQ_exec (endSym := endSym) (startSym := startSym) hE3 _
    have hmid3 : applyTrace blank (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts))
        ((avecsQ blank L3 qt2).map
          (extendVec (Fin.castAddEmb 8)
            (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts))))
        = Fin.append (TSQ qt3) (TS (fill' blank mark M).ts) := by
      rw [queue_applyTrace, hrun3]
    refine ⟨((avecsQ blank [(⟨π Role.front, blank, Move.left⟩ : Act sc)] qt).map
          (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T)))
        ++ ([actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
            (Sum.inr (XAct.fill π)) (Fin.append (TSQ qt1) T)]
          ++ (avecsQ blank L3 qt2).map
            (extendVec (Fin.castAddEmb 8)
              (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts)))),
      qt3, π2, hinj2, ?_, ?_, ?_, ?_⟩
    · have e3 : ((avecsQ blank L3 qt2).map
          (extendVec (Fin.castAddEmb 8)
            (Fin.append (TSQ qt2) (TS (fill' blank mark M).ts)))).length = n3 := by
        rw [List.length_map, avecsQ_length, hlen3]
      simp only [List.length_append, hlen1, e3, List.length_singleton]
      omega
    · rw [hfill]; exact henc3
    · rw [hfill, applyTrace_append, hmid1, applyTrace_append, hmid2, hmid3]
    · rw [fillStepProg]
      refine exec_seq hProbe ?_
      rw [hmid1]
      refine exec_ite_pos hcondT ?_
      rw [fillBranchProg]
      refine exec_seq hFillE ?_
      rw [hmid2]
      exact hTail
  · -- 供給しない
    have hfill : fillIf' blank mark n M = M := if_neg hc
    have hcondF : (IFO (Terminal := Terminal) blank endSym mark startSym).condOf
        (Sum.inr (XCond.fillNow π) : CondE sc)
        (fun j => (Fin.append (TSQ qt1) T j).focus) = false := by
      rw [hcond]; exact decide_eq_false hc
    have hRestE : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (Prog.act (Sum.inr (XAct.restore π) : ActE sc)) (Fin.append (TSQ qt1) T)
        [actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
          (Sum.inr (XAct.restore π)) (Fin.append (TSQ qt1) T)] :=
      exec_act (inputFree_IFO blank endSym mark startSym) _ _
    have hmid2 : applyTrace blank (Fin.append (TSQ qt1) T)
        [actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
          (Sum.inr (XAct.restore π)) (Fin.append (TSQ qt1) T)]
        = Fin.append (TSQ qt2) T := by
      rw [applyTrace_cons, applyTrace_nil]
      exact restore_step blank π qt1 T
    refine ⟨((avecsQ blank [(⟨π Role.front, blank, Move.left⟩ : Act sc)] qt).map
          (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) T)))
        ++ [actVec (IFO (Terminal := Terminal) blank endSym mark startSym)
            (Sum.inr (XAct.restore π)) (Fin.append (TSQ qt1) T)],
      qt2, π, hinj, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, hlen1, List.length_singleton]
      omega
    · rw [hfill]; exact henc2
    · rw [hfill, applyTrace_append, hmid1, hmid2]
    · rw [fillStepProg]
      refine exec_seq hProbe ?_
      rw [hmid1]
      exact exec_ite_neg hcondF hRestE

end FillStep

/-! ## 6. 走査の一歩を含むマイクロ反復（`runInT'` の 1 回） -/

section Micro

open PalPeg.TextFeed
open PalPeg.GSTapes (tP tT)

variable {blank endSym mark startSym : Fin sc}

/-- 走査側の動作列を 18 本テープへ拡張して適用した結果。 -/
theorem scan_applyTrace (blank : Fin sc) (qt : QT sc)
    (L : List (PalPeg.GSTapes.Act' sc)) (ts : PalPeg.GSTapes.TapesState' sc) :
    applyTrace blank (Fin.append (TSQ qt) (TS ts))
        ((PalPeg.GSProg.avecs blank L ts).map
          (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt) (TS ts))))
      = Fin.append (TSQ qt) (TS (PalPeg.GSTapes.applyActs' blank L ts)) := by
  nth_rewrite 1 [show (Fin.append (TSQ qt) (TS ts) : Fin 18 → STape (Fin sc))
    = extend (Fin.natAddEmb 10) (TS ts) (Fin.append (TSQ qt) (TS ts)) from
    (extend_natAdd_append (TS ts) (TSQ qt) (TS ts)).symm]
  rw [applyTrace_extend, PalPeg.GSProg.applyTrace_avecs, extend_natAdd_append]

/-- `fillIf'` は冪等（供給すると先端が 1 つ進むので、続けて供給条件は成り立たない）。 -/
theorem fillIf'_not_again (blank mark : Fin sc) (n : ℕ) (M : Machine' sc) :
    ¬ ((fillIf' blank mark n M).st.pos + (fillIf' blank mark n M).st.q
        = (fillIf' blank mark n M).m ∧ (fillIf' blank mark n M).m < n) := by
  unfold fillIf'
  split_ifs with hc
  · intro hcon
    have h1 : (fill' blank mark M).m = M.m + 1 := rfl
    have h2 : (fill' blank mark M).st = M.st := rfl
    rw [h1, h2] at hcon
    omega
  · exact hc

theorem fillIf'_idem (blank mark : Fin sc) (n : ℕ) (M : Machine' sc) :
    fillIf' blank mark n (fillIf' blank mark n M) = fillIf' blank mark n M := by
  conv_lhs => rw [fillIf']
  exact if_neg (fillIf'_not_again blank mark n M)

/-- 進めない状態からはラウンド内の残りの反復で何も起きない。 -/
theorem runInT'_stuck {v Text : List (Fin sc)} {k p₁ r n : ℕ} {M : Machine' sc}
    (hst : ¬ Enabled v n (fillIf' blank mark n M).st) :
    ∀ j, runInT' blank endSym mark v k p₁ r n Text j (fillIf' blank mark n M)
      = fillIf' blank mark n M := by
  intro j
  cases j with
  | zero => rfl
  | succ j =>
      rw [runInT', fillIf'_idem, if_neg hst]

/-- ラウンド内の反復は「1 回」と「残り」に分解できる。 -/
theorem runInT'_succ_left {v Text : List (Fin sc)} {k p₁ r n : ℕ} (j : ℕ) (M : Machine' sc) :
    runInT' blank endSym mark v k p₁ r n Text (j + 1) M
      = runInT' blank endSym mark v k p₁ r n Text j
          (runInT' blank endSym mark v k p₁ r n Text 1 M) := by
  rw [runInT']
  by_cases he : Enabled v n (fillIf' blank mark n M).st
  · rw [if_pos he]
    congr 1
    rw [runInT', if_pos he]
    rfl
  · rw [if_neg he, runInT', if_neg he]
    exact (runInT'_stuck (endSym := endSym) (k := k) (p₁ := p₁) (r := r) (Text := Text)
      he j).symm

/-- **`Enabled` のテープ読みによる評価**（`fillIf'` を通したあとの状態で）。 -/
theorem cond_enabled {v Text : List (Fin sc)} {k p₁ r n : ℕ} {M : Machine' sc} {qt : QT sc}
    (hend : endSym ∉ v) (hblank : blank ∉ Text) (hn : n ≤ Text.length)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M)
    (hnf : ¬ (M.st.pos + M.st.q = M.m ∧ M.m < n)) :
    (IFO (Terminal := Terminal) blank endSym mark startSym).condOf
        (Sum.inr XCond.enabled : CondE sc)
        (fun j => (Fin.append (TSQ qt) (TS M.ts) j).focus)
      = decide (Enabled v n M.st) := by
  show decide ((Fin.append (TSQ qt) (TS M.ts) (tPIdx : Fin 18)).focus = endSym ∨
      (Fin.append (TSQ qt) (TS M.ts) (tTIdx : Fin 18)).focus ≠ blank) = _
  rw [focus_tPIdx, focus_tTIdx]
  refine decide_eq_decide.mpr (or_congr (read_tP_end_iff hend h.qle h.scan) ?_)
  have hb := read_tT_blank_iff (startSym := startSym) (endSym := endSym) (k := k)
    (p₁ := p₁) (r := r) hblank hn h
  have hhd := h.hd
  have hmle := h.mle
  constructor
  · intro hne0
    have : M.st.pos + M.st.q ≠ M.m := fun he => hne0 (hb.mpr he)
    omega
  · intro hlt hb0
    have := hb.mp hb0
    omega

/-- **1 マイクロ反復のプログラム**：`fillIf'` ののち、進めるなら走査を 1 歩。 -/
noncomputable def microProg (blank mark : Fin sc) (k : ℕ) (π : Role → Role)
    (q : Queue (Fin sc)) : Prog (ActE sc) (CondE sc) :=
  Prog.seq (fillStepProg blank mark π q)
    (Prog.ite (Sum.inr XCond.enabled : CondE sc) (liftE (liftS (scanProg k))) Prog.skip)

/-- **1 マイクロ反復の `Exec`**：`runInT' … 1` をちょうど実現する。
マイクロステップ数は「供給 `≤ 33`」＋「進めるなら走査の一歩の動作数」。 -/
theorem micro_exec {v Text : List (Fin sc)} {k p₁ r n : ℕ} {M : Machine' sc}
    {qt : QT sc} {π : Role → Role}
    (hk : 0 < k) (hne : mark ≠ blank) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hn : n ≤ Text.length) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π) M.Q)
    (h : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    ∃ (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc) (π' : Role → Role),
      Function.Injective π' ∧
      acts.length ≤ 33 + (if Enabled v n M.st then stepCost' v k p₁ r Text M.st else 0) ∧
      Encodes blank mark (qt' ∘ π')
        (runInT' blank endSym mark v k p₁ r n Text 1 M).Q ∧
      applyTrace blank (Fin.append (TSQ qt) (TS M.ts)) acts
        = Fin.append (TSQ qt')
          (TS (runInT' blank endSym mark v k p₁ r n Text 1 M).ts) ∧
      Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (microProg blank mark k π M.Q) (Fin.append (TSQ qt) (TS M.ts)) acts := by
  classical
  obtain ⟨acts1, qt1, π1, hinj1, hlen1, henc1, hmid1, hex1⟩ :=
    fillStep_exec (Terminal := Terminal) (startSym := startSym) (v := v) (k := k)
      (p₁ := p₁) (r := r) hne hblank hmark hn hinj henc h
  set M1 : Machine' sc := fillIf' blank mark n M with hM1
  have hM1st : M1.st = M.st := fillIf'_st blank mark n M
  have hinv1 : FeedInv' blank startSym endSym mark v Text k p₁ r n M1 :=
    fillIf'_feedInv hne hn h
  have hstep1 : runInT' blank endSym mark v k p₁ r n Text 1 M
      = if Enabled v n M.st then scanOne' blank endSym mark v k p₁ r Text M1 else M1 := by
    rw [runInT', ← hM1, hM1st]
    rfl
  have hcond := cond_enabled (Terminal := Terminal) (qt := qt1) hend hblank hn hinv1
    (fillIf'_not_again blank mark n M)
  rw [hM1st] at hcond
  by_cases he : Enabled v n M.st
  · -- 走査を 1 歩
    have hrd : M1.st.q ≠ v.length → M1.st.pos + M1.st.q < M1.m := fillIf'_ready h (hM1st ▸ he)
    have hq : M1.st.q ≤ v.length := hinv1.qle
    have hscanA := PalPeg.GSProg.scanProg_exec (Terminal := Terminal) (blank := blank)
      (endSym := endSym) (mark := mark) (startSym := startSym) (v := v)
      (Text := padW blank Text M1.m) (k := k) (p₁ := p₁) (r := r) (ts := M1.ts) (st := M1.st)
      hk hne hstart hinv1.scan hq
    have hscan : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (liftE (liftS (scanProg k))) (Fin.append (TSQ qt1) (TS M1.ts))
        ((PalPeg.GSProg.avecs blank
            (PalPeg.GSTapes.program' blank endSym mark k M1.ts) M1.ts).map
          (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt1) (TS M1.ts)))) :=
      liftES_exec (endSym := endSym) (startSym := startSym) hscanA
    have hstep : runInT' blank endSym mark v k p₁ r n Text 1 M
        = scanOne' blank endSym mark v k p₁ r Text M1 := by rw [hstep1, if_pos he]
    have hmid2 : applyTrace blank (Fin.append (TSQ qt1) (TS M1.ts))
        ((PalPeg.GSProg.avecs blank
            (PalPeg.GSTapes.program' blank endSym mark k M1.ts) M1.ts).map
          (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt1) (TS M1.ts))))
        = Fin.append (TSQ qt1)
          (TS (runInT' blank endSym mark v k p₁ r n Text 1 M).ts) := by
      rw [scan_applyTrace, hstep]
      rfl
    have hcost : (PalPeg.GSTapes.program' blank endSym mark k M1.ts).length
        ≤ stepCost' v k p₁ r Text M.st := by
      have hc := scanOne'_cost (startSym := startSym) hk hne hend hn hrd hinv1
      have he1 : (scanOne' blank endSym mark v k p₁ r Text M1).R.cost
          = M1.R.cost + (PalPeg.GSTapes.program' blank endSym mark k M1.ts).length := rfl
      rw [he1, hM1st] at hc
      omega
    refine ⟨acts1 ++ (PalPeg.GSProg.avecs blank
        (PalPeg.GSTapes.program' blank endSym mark k M1.ts) M1.ts).map
          (extendVec (Fin.natAddEmb 10) (Fin.append (TSQ qt1) (TS M1.ts))),
      qt1, π1, hinj1, ?_, ?_, ?_, ?_⟩
    · rw [if_pos he, List.length_append, List.length_map, PalPeg.GSProg.avecs_length]
      omega
    · rw [hstep]
      exact henc1
    · rw [applyTrace_append, hmid1, hmid2]
    · rw [microProg]
      refine exec_seq hex1 ?_
      rw [hmid1]
      refine exec_ite_pos ?_ hscan
      rw [hcond]
      exact decide_eq_true he
  · -- 進めない
    have hstep : runInT' blank endSym mark v k p₁ r n Text 1 M = M1 := by
      rw [hstep1, if_neg he]
    refine ⟨acts1 ++ [], qt1, π1, hinj1, ?_, ?_, ?_, ?_⟩
    · rw [List.append_nil]; omega
    · rw [hstep]; exact henc1
    · rw [List.append_nil, hstep]; exact hmid1
    · rw [microProg]
      refine exec_seq hex1 ?_
      rw [hmid1]
      refine exec_ite_neg ?_ (exec_skip _)
      rw [hcond]
      exact decide_eq_false he

end Micro

/-! ## 7. ラウンド内の `gsRate k` 回の反復 -/

section RunIn

open PalPeg.TextFeed

variable {blank endSym mark startSym : Fin sc}

/-- 反復の右からの分解。 -/
theorem runInT'_succ_right {v Text : List (Fin sc)} {k p₁ r n : ℕ} :
    ∀ (j : ℕ) (M : Machine' sc),
      runInT' blank endSym mark v k p₁ r n Text (j + 1) M
        = runInT' blank endSym mark v k p₁ r n Text 1
            (runInT' blank endSym mark v k p₁ r n Text j M) := by
  intro j
  induction j with
  | zero => intro M; rfl
  | succ j ih =>
      intro M
      rw [runInT'_succ_left (j + 1) M, ih (runInT' blank endSym mark v k p₁ r n Text 1 M),
        ← runInT'_succ_left j M]

/-- ラウンド内の `j` 回の反復を表すプログラム。反復ごとの回転置換 `πF i` は
実行時にしか定まらないため、呼び出し側（`runInProgN_exec`）が与える。 -/
noncomputable def runInProgN (blank endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r n : ℕ) (M : Machine' sc) (πF : ℕ → Role → Role) :
    ℕ → Prog (ActE sc) (CondE sc)
  | 0 => Prog.skip
  | j + 1 =>
      Prog.seq (runInProgN blank endSym mark v Text k p₁ r n M πF j)
        (microProg blank mark k (πF j)
          (runInT' blank endSym mark v k p₁ r n Text j M).Q)

theorem runInProgN_congr (blank endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r n : ℕ) (M : Machine' sc) {πF πF' : ℕ → Role → Role} :
    ∀ (j : ℕ), (∀ i, i < j → πF i = πF' i) →
      runInProgN blank endSym mark v Text k p₁ r n M πF j
        = runInProgN blank endSym mark v Text k p₁ r n M πF' j
  | 0, _ => rfl
  | j + 1, hπ => by
      show Prog.seq (runInProgN blank endSym mark v Text k p₁ r n M πF j) _
        = Prog.seq (runInProgN blank endSym mark v Text k p₁ r n M πF' j) _
      rw [runInProgN_congr blank endSym mark v Text k p₁ r n M j
        (fun i hi => hπ i (by omega)), hπ j (by omega)]

/-- **ラウンド内の `j` 回の反復の `Exec`**。マイクロステップ数は
`j * (c + 35)`（抽象側の `j * (c + 33)` に対し、供給判定のプローブと
その打ち消しで 1 反復あたり最大 2 手だけ多い）。 -/
theorem runInProgN_exec {v Text : List (Fin sc)} {k p₁ r n c : ℕ}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hn : n ≤ Text.length)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c) :
    ∀ (j : ℕ) (M : Machine' sc) (qt : QT sc) (π : Role → Role),
      Function.Injective π → Encodes blank mark (qt ∘ π) M.Q →
      FeedInv' blank startSym endSym mark v Text k p₁ r n M →
      ∃ (πF : ℕ → Role → Role) (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc)
        (π' : Role → Role),
        Function.Injective π' ∧ acts.length ≤ j * (c + 35) ∧
        Encodes blank mark (qt' ∘ π')
          (runInT' blank endSym mark v k p₁ r n Text j M).Q ∧
        applyTrace blank (Fin.append (TSQ qt) (TS M.ts)) acts
          = Fin.append (TSQ qt')
            (TS (runInT' blank endSym mark v k p₁ r n Text j M).ts) ∧
        Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
          (runInProgN blank endSym mark v Text k p₁ r n M πF j)
          (Fin.append (TSQ qt) (TS M.ts)) acts := by
  intro j
  induction j with
  | zero =>
      intro M qt π hinj henc _
      exact ⟨fun _ => π, [], qt, π, hinj, by simp, henc, rfl, exec_skip _⟩
  | succ j ih =>
      intro M qt π hinj henc hinv
      obtain ⟨πF, acts, qtj, πj, hinjj, hlenj, hencj, hmidj, hexj⟩ := ih M qt π hinj henc hinv
      set Mj : Machine' sc := runInT' blank endSym mark v k p₁ r n Text j M with hMj
      have hinvj : FeedInv' blank startSym endSym mark v Text k p₁ r n Mj :=
        runInT'_feedInv hne hk hv hend hn j M hinv
      obtain ⟨acts', qt', π', hinj', hlen', henc', hmid', hex'⟩ :=
        micro_exec (Terminal := Terminal) (startSym := startSym) (p₁ := p₁) (r := r)
          hk hne hend hstart hblank hmark hn hinjj hencj hinvj
      have hstep : runInT' blank endSym mark v k p₁ r n Text 1 Mj
          = runInT' blank endSym mark v k p₁ r n Text (j + 1) M :=
        (runInT'_succ_right j M).symm
      set πF' : ℕ → Role → Role := Function.update πF j πj with hπF'
      have hcongr : runInProgN blank endSym mark v Text k p₁ r n M πF' j
          = runInProgN blank endSym mark v Text k p₁ r n M πF j :=
        runInProgN_congr blank endSym mark v Text k p₁ r n M j
          (fun i hi => by simp [hπF', ne_of_lt hi])
      refine ⟨πF', acts ++ acts', qt', π', hinj', ?_, ?_, ?_, ?_⟩
      · have hb : (if Enabled v n Mj.st then stepCost' v k p₁ r Text Mj.st else 0) ≤ c := by
          split_ifs with hE
          · exact hc Mj.st hinvj.qle
          · exact Nat.zero_le _
        have e : (j + 1) * (c + 35) = j * (c + 35) + (c + 35) := by ring
        rw [List.length_append]
        omega
      · rw [← hstep]; exact henc'
      · rw [← hstep, applyTrace_append, hmidj]; exact hmid'
      · show Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
          (Prog.seq (runInProgN blank endSym mark v Text k p₁ r n M πF' j)
            (microProg blank mark k (πF' j) Mj.Q))
          (Fin.append (TSQ qt) (TS M.ts)) (acts ++ acts')
        rw [hcongr]
        refine exec_seq hexj ?_
        rw [hmidj]
        simp only [hπF', Function.update_self]
        exact hex'

end RunIn

/-! ## 8. 1 ラウンド（到着 + `gsRate k` 回の反復） -/

section Round

open PalPeg.TextFeed

variable {blank endSym mark startSym : Fin sc}

/-- **オンライン 1 ラウンドのプログラム**：`roundT' = runInT' … ∘ arrive'` に対応。 -/
noncomputable def roundProg (blank endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r n : ℕ) (M : Machine' sc) (a : Fin sc) (π : Role → Role)
    (πF : ℕ → Role → Role) : Prog (ActE sc) (CondE sc) :=
  Prog.seq (liftE (liftQ (snocProg blank mark π (snocCS M.Q a) a)))
    (runInProgN blank endSym mark v Text k p₁ r (n + 1) (arrive' blank mark a M) πF
      (gsRate k))

/-- **1 ラウンドの `Exec`**：`roundT'` をちょうど実現する。マイクロステップ数は
`到着 ≤ 26` ＋ `gsRate k * (c + 35)`。 -/
theorem round_exec {v Text : List (Fin sc)} {k p₁ r n c : ℕ} {M : Machine' sc}
    {qt : QT sc} {π : Role → Role} {a : Fin sc}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hn : n < Text.length) (ha : Text[n]? = some a)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (hinj : Function.Injective π) (henc : Encodes blank mark (qt ∘ π) M.Q)
    (hinv : FeedInv' blank startSym endSym mark v Text k p₁ r n M) :
    ∃ (πF : ℕ → Role → Role) (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc)
      (π' : Role → Role),
      Function.Injective π' ∧ acts.length ≤ 26 + gsRate k * (c + 35) ∧
      Encodes blank mark (qt' ∘ π')
        (roundT' blank endSym mark v k p₁ r n Text a M).Q ∧
      applyTrace blank (Fin.append (TSQ qt) (TS M.ts)) acts
        = Fin.append (TSQ qt') (TS (roundT' blank endSym mark v k p₁ r n Text a M).ts) ∧
      Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (roundProg blank endSym mark v Text k p₁ r n M a π πF)
        (Fin.append (TSQ qt) (TS M.ts)) acts := by
  classical
  obtain ⟨n1, qt1, π1, hperf1, hb1, hinj1, _, _, henc1⟩ :=
    qsnoc_exec (Terminal := Terminal) (blank := blank) (mark := mark) hinj hne a 0 henc
      hinv.qinv
  obtain ⟨L1, hE1, hlen1, hrun1⟩ := hperf1
  have hArrive : Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
      (liftE (liftQ (snocProg blank mark π (snocCS M.Q a) a)))
      (Fin.append (TSQ qt) (TS M.ts))
      ((avecsQ blank L1 qt).map
        (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) (TS M.ts)))) :=
    liftEQ_exec (endSym := endSym) (startSym := startSym) hE1 (TS M.ts)
  have hmid1 : applyTrace blank (Fin.append (TSQ qt) (TS M.ts))
      ((avecsQ blank L1 qt).map
        (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) (TS M.ts))))
      = Fin.append (TSQ qt1) (TS (arrive' blank mark a M).ts) := by
    rw [queue_applyTrace, hrun1]
    rfl
  have hinv1 : FeedInv' blank startSym endSym mark v Text k p₁ r (n + 1)
      (arrive' blank mark a M) := arrive'_feedInv hne hn ha hinv
  obtain ⟨πF, acts2, qt2, π2, hinj2, hlen2, henc2, hmid2, hex2⟩ :=
    runInProgN_exec (Terminal := Terminal) (startSym := startSym) hk hne hv hend hstart
      hblank hmark (by omega : n + 1 ≤ Text.length) hc (gsRate k) (arrive' blank mark a M)
      qt1 π1 hinj1 (by exact henc1) hinv1
  refine ⟨πF, ((avecsQ blank L1 qt).map
      (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) (TS M.ts)))) ++ acts2,
    qt2, π2, hinj2, ?_, henc2, ?_, ?_⟩
  · have e1 : ((avecsQ blank L1 qt).map
        (extendVec (Fin.castAddEmb 8) (Fin.append (TSQ qt) (TS M.ts)))).length = n1 := by
      rw [List.length_map, avecsQ_length, hlen1]
    rw [List.length_append, e1]
    omega
  · rw [applyTrace_append, hmid1]
    exact hmid2
  · rw [roundProg]
    refine exec_seq hArrive ?_
    rw [hmid1]
    exact hex2

end Round

/-! ## 9. 全ラウンド（`onlineT'`） -/

section Online

open PalPeg.TextFeed

variable {blank endSym mark startSym : Fin sc}

/-- **オンライン走査フェーズ全体のプログラム**（`onlineT'` に対応）。
ラウンド `i` の到着用の回転置換 `π0F i` と、そのラウンド内の反復用の
回転置換 `πF i` は実行時にしか定まらないため、呼び出し側が与える。 -/
noncomputable def onlineProgN (blank endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r s : ℕ) (M0 : Machine' sc) (π0F : ℕ → Role → Role)
    (πF : ℕ → ℕ → Role → Role) : ℕ → Prog (ActE sc) (CondE sc)
  | 0 => Prog.skip
  | n + 1 =>
      Prog.seq (onlineProgN blank endSym mark v Text k p₁ r s M0 π0F πF n)
        (roundProg blank endSym mark v Text k p₁ r (s + n)
          (onlineT' blank endSym mark v k p₁ r Text s n M0)
          (Text.getD (s + n) blank) (π0F n) (πF n))

theorem onlineProgN_congr (blank endSym mark : Fin sc) (v Text : List (Fin sc))
    (k p₁ r s : ℕ) (M0 : Machine' sc) {π0F π0F' : ℕ → Role → Role}
    {πF πF' : ℕ → ℕ → Role → Role} :
    ∀ (n : ℕ), (∀ i, i < n → π0F i = π0F' i) → (∀ i, i < n → πF i = πF' i) →
      onlineProgN blank endSym mark v Text k p₁ r s M0 π0F πF n
        = onlineProgN blank endSym mark v Text k p₁ r s M0 π0F' πF' n
  | 0, _, _ => rfl
  | n + 1, h0, h1 => by
      show Prog.seq (onlineProgN blank endSym mark v Text k p₁ r s M0 π0F πF n) _
        = Prog.seq (onlineProgN blank endSym mark v Text k p₁ r s M0 π0F' πF' n) _
      rw [onlineProgN_congr blank endSym mark v Text k p₁ r s M0 n
          (fun i hi => h0 i (by omega)) (fun i hi => h1 i (by omega)),
        h0 n (by omega), h1 n (by omega)]

/-- **オンライン走査フェーズの `n` ラウンド全体の `Exec`**。
マイクロステップ数は `n * (gsRate k * (c + 35) + 26)`。 -/
theorem online_rounds {v Text : List (Fin sc)} {k p₁ r s c : ℕ}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c) :
    ∀ (n : ℕ) (M0 : Machine' sc) (qt : QT sc) (π : Role → Role),
      s + n ≤ Text.length → Function.Injective π →
      Encodes blank mark (qt ∘ π) M0.Q →
      FeedInv' blank startSym endSym mark v Text k p₁ r s M0 →
      ∃ (π0F : ℕ → Role → Role) (πF : ℕ → ℕ → Role → Role)
        (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc) (π' : Role → Role),
        Function.Injective π' ∧ acts.length ≤ n * (gsRate k * (c + 35) + 26) ∧
        Encodes blank mark (qt' ∘ π')
          (onlineT' blank endSym mark v k p₁ r Text s n M0).Q ∧
        applyTrace blank (Fin.append (TSQ qt) (TS M0.ts)) acts
          = Fin.append (TSQ qt')
            (TS (onlineT' blank endSym mark v k p₁ r Text s n M0).ts) ∧
        Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
          (onlineProgN blank endSym mark v Text k p₁ r s M0 π0F πF n)
          (Fin.append (TSQ qt) (TS M0.ts)) acts := by
  intro n
  induction n with
  | zero =>
      intro M0 qt π _ hinj henc _
      exact ⟨fun _ => π, fun _ _ => π, [], qt, π, hinj, by simp, henc, rfl, exec_skip _⟩
  | succ n ih =>
      intro M0 qt π hle hinj henc hinv
      obtain ⟨π0F, πF, acts, qtn, πn, hinjn, hlenn, hencn, hmidn, hexn⟩ :=
        ih M0 qt π (by omega) hinj henc hinv
      set Mn : Machine' sc := onlineT' blank endSym mark v k p₁ r Text s n M0 with hMn
      obtain ⟨hinvn, _⟩ := onlineT'_feedInv (s := s) (c := c) hne hk hv hend hc n M0
        (by omega) hinv
      obtain ⟨πF', acts', qt', π', hinj', hlen', henc', hmid', hex'⟩ :=
        round_exec (Terminal := Terminal) (startSym := startSym) (c := c)
          (a := Text.getD (s + n) blank) hk hne hv hend hstart hblank hmark
          (by omega : s + n < Text.length) (getD_eq (by omega)) hc hinjn hencn hinvn
      set π0F' : ℕ → Role → Role := Function.update π0F n πn with hπ0F'
      set πF'' : ℕ → ℕ → Role → Role := Function.update πF n πF' with hπF''
      have hcongr : onlineProgN blank endSym mark v Text k p₁ r s M0 π0F' πF'' n
          = onlineProgN blank endSym mark v Text k p₁ r s M0 π0F πF n :=
        onlineProgN_congr blank endSym mark v Text k p₁ r s M0 n
          (fun i hi => by simp [hπ0F', ne_of_lt hi])
          (fun i hi => by simp [hπF'', ne_of_lt hi])
      have hround : onlineT' blank endSym mark v k p₁ r Text s (n + 1) M0
          = roundT' blank endSym mark v k p₁ r (s + n) Text (Text.getD (s + n) blank) Mn :=
        rfl
      refine ⟨π0F', πF'', acts ++ acts', qt', π', hinj', ?_, ?_, ?_, ?_⟩
      · have e : (n + 1) * (gsRate k * (c + 35) + 26)
            = n * (gsRate k * (c + 35) + 26) + (gsRate k * (c + 35) + 26) := by ring
        rw [List.length_append]
        omega
      · rw [hround]; exact henc'
      · rw [hround, applyTrace_append, hmidn]; exact hmid'
      · show Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
          (Prog.seq (onlineProgN blank endSym mark v Text k p₁ r s M0 π0F' πF'' n)
            (roundProg blank endSym mark v Text k p₁ r (s + n) Mn
              (Text.getD (s + n) blank) (π0F' n) (πF'' n)))
          (Fin.append (TSQ qt) (TS M0.ts)) (acts ++ acts')
        rw [hcongr]
        refine exec_seq hexn ?_
        rw [hmidn]
        simp only [hπ0F', hπF'', Function.update_self]
        exact hex'

end Online

/-! ## 10. `feed_online'` のプログラム版 -/

section Final

open PalPeg.TextFeed

variable {blank endSym mark startSym : Fin sc}

/-- **主定理（オンライン走査フェーズのプログラム版）**：`TextFeed.feed_online'` の
機械を 18 本テープ上の構造化プログラム `onlineProgN` で置き換えたもの。

起動フェーズの終状態 `M0 = startT' …`（その待ち行列テープ表現 `qt`／回転置換 `π`
は `TextFeedProg.feedStartProgN_exec` が与える）から出発して、`n` ラウンドの
オンライン走査プログラムがちょうど実行でき、

* 待ち行列は `onlineT'` の抽象値を符号化し続け、
* 18 本のテープは `onlineT'` の到達状態のテープにちょうど一致し、
* マイクロステップ数は `n * (gsRate k * (c + 35) + 26)` 以下、
* ゴースト状態は `GSRealTime.onlineRun` に一致し、供給の不変条件が保たれる

（最後の 2 つは `TextFeed.feed_online'` そのもの）。

**抽象側との差**：抽象の上界は `n * (gsRate k * (c + 33) + 26)`。増分
`2 * gsRate k` は、「いま供給すべきか」をテープだけで判定するための前方テープの
プローブ（1 手）と、供給しない場合のその打ち消し（1 手）である。 -/
theorem feed_online_prog {u v Text : List (Fin sc)} {k p₁ r c : ℕ}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length)
    (qt : QT sc) (π : Role → Role) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π)
      (startT' blank mark Text u.length
        (initM' blank startSym endSym mark v Text k p₁ r)).Q) :
    ∃ (π0F : ℕ → Role → Role) (πF : ℕ → ℕ → Role → Role)
      (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc) (π' : Role → Role),
      Function.Injective π' ∧ acts.length ≤ n * (gsRate k * (c + 35) + 26) ∧
      Encodes blank mark (qt' ∘ π')
        (onlineT' blank endSym mark v k p₁ r Text u.length n
          (startT' blank mark Text u.length
            (initM' blank startSym endSym mark v Text k p₁ r))).Q ∧
      applyTrace blank
          (Fin.append (TSQ qt)
            (TS (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r)).ts)) acts
        = Fin.append (TSQ qt')
          (TS (onlineT' blank endSym mark v k p₁ r Text u.length n
            (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r))).ts) ∧
      Exec (IFO (Terminal := Terminal) blank endSym mark startSym) blank
        (onlineProgN blank endSym mark v Text k p₁ r u.length
          (startT' blank mark Text u.length
            (initM' blank startSym endSym mark v Text k p₁ r)) π0F πF n)
        (Fin.append (TSQ qt)
          (TS (startT' blank mark Text u.length
            (initM' blank startSym endSym mark v Text k p₁ r)).ts)) acts ∧
      (onlineT' blank endSym mark v k p₁ r Text u.length n
        (startT' blank mark Text u.length
          (initM' blank startSym endSym mark v Text k p₁ r))).st
        = onlineRun u v k p₁ r Text (u.length + n) ∧
      FeedInv' blank startSym endSym mark v Text k p₁ r (u.length + n)
        (onlineT' blank endSym mark v k p₁ r Text u.length n
          (startT' blank mark Text u.length
            (initM' blank startSym endSym mark v Text k p₁ r))) := by
  obtain ⟨s1, _, _, _⟩ := startT'_spec (blank := blank) (mark := mark) (v := v)
    (startSym := startSym) (endSym := endSym) (k := k) (p₁ := p₁) (r := r) hne rfl rfl
    (initM'_feedInv blank startSym endSym mark v Text k p₁ r) u.length (by omega)
  obtain ⟨g1, g2, _⟩ := feed_online' (u := u) hne hk hv hend hc n hn
  obtain ⟨π0F, πF, acts, qt', π', hinj', hlen', henc', hmid', hex'⟩ :=
    online_rounds (Terminal := Terminal) (startSym := startSym) (s := u.length) (c := c)
      hk hne hv hend hstart hblank hmark hc n _ qt π hn hinj henc s1
  exact ⟨π0F, πF, acts, qt', π', hinj', hlen', henc', hmid', hex', g1, g2⟩

/-- **停止**：`feed_online_prog` の与える動作列を出し切った次の 1 手で制御スタックは
空になる（`ProgLangLib.exec_halts`）。 -/
theorem feed_online_prog_halts {u v Text : List (Fin sc)} {k p₁ r c : ℕ}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length)
    (qt : QT sc) (π : Role → Role) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π)
      (startT' blank mark Text u.length
        (initM' blank startSym endSym mark v Text k p₁ r)).Q) :
    ∃ (π0F : ℕ → Role → Role) (πF : ℕ → ℕ → Role → Role) (N : ℕ),
      N ≤ n * (gsRate k * (c + 35) + 26) ∧
      ∀ (l : List (Option Terminal)), l.length = N → ∀ x : Option Terminal,
        (runInputs (IFO (Terminal := Terminal) blank endSym mark startSym) blank (l ++ [x])
          ([onlineProgN blank endSym mark v Text k p₁ r u.length
              (startT' blank mark Text u.length
                (initM' blank startSym endSym mark v Text k p₁ r)) π0F πF n],
            Fin.append (TSQ qt)
              (TS (startT' blank mark Text u.length
                (initM' blank startSym endSym mark v Text k p₁ r)).ts))).1 = [] := by
  obtain ⟨π0F, πF, acts, _, _, _, hlen, _, _, hex, _, _⟩ :=
    feed_online_prog (Terminal := Terminal) hk hne hv hend hstart hblank hmark hc n hn
      qt π hinj henc
  exact ⟨π0F, πF, acts.length, hlen, fun l hl x => exec_halts hex l hl x⟩

/-- **トレースの一致**：`n` ラウンドのオンライン走査プログラムを、動作列と同じ長さの
任意の入力記号列に沿って走らせると、実行される動作列は `feed_online_prog` が与える
動作列（＝待ち行列側の `avecsQ` と走査側の `avecs`、すなわち抽象側の動作列そのものを
18 本テープへ拡張したもの）にちょうど一致する。 -/
theorem feed_online_prog_trace {u v Text : List (Fin sc)} {k p₁ r c : ℕ}
    (hk : 0 < k) (hne : mark ≠ blank) (hv : 0 < v.length) (hend : endSym ∉ v)
    (hstart : startSym ∉ v) (hblank : blank ∉ Text) (hmark : mark ∉ Text)
    (hc : ∀ st : ScanState, st.q ≤ v.length → stepCost' v k p₁ r Text st ≤ c)
    (n : ℕ) (hn : u.length + n ≤ Text.length)
    (qt : QT sc) (π : Role → Role) (hinj : Function.Injective π)
    (henc : Encodes blank mark (qt ∘ π)
      (startT' blank mark Text u.length
        (initM' blank startSym endSym mark v Text k p₁ r)).Q) :
    ∃ (π0F : ℕ → Role → Role) (πF : ℕ → ℕ → Role → Role)
      (acts : List (Fin 18 → Fin sc × Move)) (qt' : QT sc),
      acts.length ≤ n * (gsRate k * (c + 35) + 26) ∧
      applyTrace blank
          (Fin.append (TSQ qt)
            (TS (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r)).ts)) acts
        = Fin.append (TSQ qt')
          (TS (onlineT' blank endSym mark v k p₁ r Text u.length n
            (startT' blank mark Text u.length
              (initM' blank startSym endSym mark v Text k p₁ r))).ts) ∧
      ∀ (l : List (Option Terminal)), l.length = acts.length →
        trace (IFO (Terminal := Terminal) blank endSym mark startSym) blank l
            ([onlineProgN blank endSym mark v Text k p₁ r u.length
                (startT' blank mark Text u.length
                  (initM' blank startSym endSym mark v Text k p₁ r)) π0F πF n],
              Fin.append (TSQ qt)
                (TS (startT' blank mark Text u.length
                  (initM' blank startSym endSym mark v Text k p₁ r)).ts))
          = acts := by
  obtain ⟨π0F, πF, acts, qt', π', _, hlen, _, hmid, hex, _, _⟩ :=
    feed_online_prog (Terminal := Terminal) hk hne hv hend hstart hblank hmark hc n hn
      qt π hinj henc
  exact ⟨π0F, πF, acts, qt', hlen, hmid, fun l hl => hex.trace_eq [] l hl⟩

end Final

/-! ## 11. 補遺：動作の直前に別の動作を差し込む構文変換 `insertPre`

「走査プログラムの特定の動作（たとえば `tT` を右へ動かす動作）の直前に供給動作を
融合して差し込む」形の移植も考えられる。そのための一般的な構文変換と、その
`Exec` 規則をここに与える。

**注意（本ファイルが採らなかった理由）**：`PalPeg.TextFeed` の抽象モデルでは、供給は
走査の動作列の内部ではなく **走査の一歩の直前** に `fillIf'` として置かれている
（`runInT'` の定義）。したがって忠実な移植は上の `fillStepProg`／`microProg` の形に
なり、`insertPre` は使っていない。 -/

section InsertPre

variable {A C Γ : Type} {t : ℕ} {I : Interp Terminal A C Γ t} {blank : Γ}

/-- `f a = some b` なる動作 `a` の直前に動作 `b` を差し込む構文変換。
`loop c a body`（＝ `while c do { act a; body }`）の場合は
`loop c b (seq (act a) body)`（＝ `while c do { act b; act a; body }`）になる。 -/
def insertPre (f : A → Option A) : Prog A C → Prog A C
  | .skip => .skip
  | .act a => match f a with
      | some b => .seq (.act b) (.act a)
      | none => .act a
  | .seq p q => .seq (insertPre f p) (insertPre f q)
  | .ite c p q => .ite c (insertPre f p) (insertPre f q)
  | .loop c a b => match f a with
      | some b' => .loop c b' (.seq (.act a) (insertPre f b))
      | none => .loop c a (insertPre f b)

@[simp] theorem insertPre_skip (f : A → Option A) :
    insertPre (C := C) f .skip = .skip := rfl

@[simp] theorem insertPre_seq (f : A → Option A) (p q : Prog A C) :
    insertPre f (.seq p q) = .seq (insertPre f p) (insertPre f q) := rfl

@[simp] theorem insertPre_ite (f : A → Option A) (c : C) (p q : Prog A C) :
    insertPre f (.ite c p q) = .ite c (insertPre f p) (insertPre f q) := rfl

theorem insertPre_act_some {f : A → Option A} {a b : A} (h : f a = some b) :
    insertPre (C := C) f (.act a) = .seq (.act b) (.act a) := by
  simp only [insertPre, h]

theorem insertPre_act_none {f : A → Option A} {a : A} (h : f a = none) :
    insertPre (C := C) f (.act a) = .act a := by
  simp only [insertPre, h]

theorem insertPre_loop_some {f : A → Option A} {a b' : A} {c : C} {body : Prog A C}
    (h : f a = some b') :
    insertPre f (.loop c a body) = .loop c b' (.seq (.act a) (insertPre f body)) := by
  simp only [insertPre, h]

/-- **差し込みの `Exec`（動作の場合）**：`insertPre f (act a)` はちょうど 2 手、
差し込まれた動作 `b` を先に、そのあと元の動作 `a` を実行する。 -/
theorem exec_insertPre_act (hI : InputFree I) {f : A → Option A} {a b : A}
    (h : f a = some b) (T : Fin t → STape Γ) :
    Exec I blank (insertPre (C := C) f (.act a)) T
      ([actVec I b T] ++
        [actVec I a (fun j => (T j).applyAction blank (actVec I b T j))]) := by
  rw [insertPre_act_some h]
  exact exec_seq (exec_act hI b T) (exec_act hI a _)

/-- 差し込みの対象でない動作はそのまま。 -/
theorem exec_insertPre_act_none (hI : InputFree I) {f : A → Option A} {a : A}
    (h : f a = none) (T : Fin t → STape Γ) :
    Exec I blank (insertPre (C := C) f (.act a)) T [actVec I a T] := by
  rw [insertPre_act_none h]
  exact exec_act hI a T

/-- 差し込みは逐次合成と可換（`Exec` の合成規則そのもの）。 -/
theorem exec_insertPre_seq {f : A → Option A} {p q : Prog A C} {T : Fin t → STape Γ}
    {A₁ A₂ : List (Fin t → Γ × Move)} (hp : Exec I blank (insertPre f p) T A₁)
    (hq : Exec I blank (insertPre f q) (applyTrace blank T A₁) A₂) :
    Exec I blank (insertPre f (.seq p q)) T (A₁ ++ A₂) := by
  rw [insertPre_seq]
  exact exec_seq hp hq

theorem exec_insertPre_ite_pos {f : A → Option A} {c : C} {p q : Prog A C}
    {T : Fin t → STape Γ} {acts : List (Fin t → Γ × Move)}
    (hc : I.condOf c (fun j => (T j).focus) = true)
    (hp : Exec I blank (insertPre f p) T acts) :
    Exec I blank (insertPre f (.ite c p q)) T acts := by
  rw [insertPre_ite]
  exact exec_ite_pos hc hp

theorem exec_insertPre_ite_neg {f : A → Option A} {c : C} {p q : Prog A C}
    {T : Fin t → STape Γ} {acts : List (Fin t → Γ × Move)}
    (hc : I.condOf c (fun j => (T j).focus) = false)
    (hq : Exec I blank (insertPre f q) T acts) :
    Exec I blank (insertPre f (.ite c p q)) T acts := by
  rw [insertPre_ite]
  exact exec_ite_neg hc hq

/-- 差し込んだループの脱出。 -/
theorem exec_insertPre_loop_stop {f : A → Option A} {c : C} {a b' : A} {body : Prog A C}
    {T : Fin t → STape Γ} (h : f a = some b')
    (hc : I.condOf c (fun j => (T j).focus) = false) :
    Exec I blank (insertPre f (.loop c a body)) T [] := by
  rw [insertPre_loop_some h]
  exact exec_loop_stop hc

end InsertPre

end PalPeg.TextFeedProg2
