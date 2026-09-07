import PalPeg.StageLifecycleProg
import PalPeg.ProgLangPersist2
import PalPeg.ProgLangSum
import PalPeg.FullMachineTapes
-- import PalPeg.InputEmbed
--   （現在 `PalPeg.PrepInstance` が `GSPreprocessProg` の改修中で壊れているため import できない。
--    §5 の `hPAL` は `InputEmbed.full_answer_mem_PAL_of_embed'` の結論そのものの形なので、
--    復旧後は import を戻して 1 行の系を足すだけでよい。）
import PalPeg.ClearAny
import PalPeg.InputCopySentinel

/-!
# 全体機械の 1 本の `Prog` 化 (`FullMachineProg`)

`ASSEMBLY_PLAN.md` §1–§4 の最後の一段。`FullMachineTapes.fullRound` /
`fullAnswer`（テープ意味論）と `ProgLangPersist2.progMachinePM`（持ち越し制御の
プログラム機械）を突き合わせ、`Main.pal_in_peg_of_structured` に流し込める形
`SAccepts input ↔ input ∈ PAL` を作る。

本ファイルの構成：

* §1 **大域テープ配置** `Fin T`（`T = 260`）。4 スロット × 段テープ 63 本 ＋
  大域入力 ＋ スロットごとのコピー最前線 4 本 ＋ 消去済み空白 ＋ 若年ラウンド用 ＋
  ラウンド予算。埋め込み `slotEmb i : Fin 63 ↪ Fin T` と、区画が互いに交わらないこと。
* §2 **スロットの分岐**。`stageInSlot n i` が `some` のときだけそのスロットの
  チャンクを走らせる（`slotSchedule_exec`）。
* §3 **ラウンド本体の直列化** `fullRoundProg` と `fullRoundProg_exec` /
  `fullRoundProg_effect`（8 区画の `Prog.seq` を `exec_seq` で合成）。
* §4 **ラウンドの帰納**：`progMachinePM_rounds_effect` の要求する形の 1 ラウンド仮定から
  `foldEffect` を `fullState` / `fullAnswer` と同一視する（`foldEffect_fullState`）。
* §5 **出口**：`pal_machine_SAccepts_iff`（`SAccepts input ↔ fullAnswer I input.length`）と
  `pal_SAccepts_iff_of`（`↔ input ∈ PAL`）、`pal_recognizedBy_of`。
  `hPAL` は `InputEmbed.full_answer_mem_PAL_of_embed'`（`n ≤ |input|` で
  `fullAnswer I n = true ↔ input.take n ∈ PAL`）がそのまま与える。

## 空語について（重要な設計上の観測）

`ProgLangPersist2.progMachinePA` は初期受理フラグを `false` に固定している
（`ofPhases … (startCtrlS prog, false)`）。`srun [] = sInit` なので、
**この機械は空語を必ず拒否する**。一方 `[] ∈ PAL` は真である。
したがって本ファイルの最終定理は `input ≠ []` を仮定する形になっている
（`SAccepts_nil : ¬ SAccepts []` も証明する）。
`Main.pal_in_peg_of_structured` が要求する `∀ w, SAccepts w ↔ w ∈ PAL` に届かせるには、
`progMachinePA` の初期フラグを `true`（＝`decide (IsPal [])`）にできるようにする
1 行の一般化が必要である。**これは本ファイルでは修正できない**（既存ファイルの変更禁止）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.FullMachineProg

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.ProgLang
open PalPeg.ProgLangPersist
open PalPeg.ProgLangPersist2
open PalPeg.FullMachineTapes

/-! ## 1. 大域テープ配置 -/

/-- 段 1 個ぶんのテープ本数（`ASSEMBLY_PLAN.md` §1.1：照合器 30 ＋ 中央 20 ＋ 準備 13）。 -/
def stageWidth : ℕ := 63

/-- 大域テープ本数。
`4 * 63`（4 スロット）＋ `1`（大域入力）＋ `4`（コピー最前線）＋ `1`（消去済み空白）
＋ `1`（若年ラウンド用）＋ `1`（ラウンド予算）。 -/
def T : ℕ := 4 * stageWidth + 8

theorem T_eq : T = 260 := rfl

/-- スロット `i` の段テープ `j` の大域添字。 -/
def slotIdx (i : Fin 4) (j : Fin stageWidth) : Fin T :=
  ⟨stageWidth * i.val + j.val, by
    have h1 := i.isLt; have h2 := j.isLt
    simp only [T, stageWidth] at *
    omega⟩

theorem slotIdx_val (i : Fin 4) (j : Fin stageWidth) :
    (slotIdx i j).val = stageWidth * i.val + j.val := rfl

theorem slotIdx_lt (i : Fin 4) (j : Fin stageWidth) :
    (slotIdx i j).val < 4 * stageWidth := by
  have h1 := i.isLt; have h2 := j.isLt
  simp only [slotIdx_val, stageWidth] at *
  omega

theorem slotIdx_injective (i : Fin 4) : Function.Injective (slotIdx i) := by
  intro j j' h
  have := congrArg Fin.val h
  simp only [slotIdx_val] at this
  exact Fin.ext (by omega)

/-- スロットごとの区画の埋め込み。 -/
def slotEmb (i : Fin 4) : Fin stageWidth ↪ Fin T :=
  ⟨slotIdx i, slotIdx_injective i⟩

/-- 別スロットの区画は交わらない。 -/
theorem slotIdx_ne_of_ne {i i' : Fin 4} (h : i ≠ i') (j j' : Fin stageWidth) :
    slotIdx i j ≠ slotIdx i' j' := by
  intro he
  have hv := congrArg Fin.val he
  have h1 := j.isLt; have h2 := j'.isLt
  have hne : i.val ≠ i'.val := fun hh => h (Fin.ext hh)
  simp only [slotIdx_val, stageWidth] at hv h1 h2
  rcases Nat.lt_or_ge i.val i'.val with hlt | hge
  · omega
  · have : i'.val < i.val := by omega
    omega

/-- 大域入力テープ。 -/
def inpIdx : Fin T := ⟨4 * stageWidth, by simp [T]⟩

/-- スロット `i` の入力コピー最前線テープ。 -/
def cpyIdx (i : Fin 4) : Fin T :=
  ⟨4 * stageWidth + 1 + i.val, by have := i.isLt; simp only [T]; omega⟩

/-- 消去済み（空白）配置を保つテープ。 -/
def blankTIdx : Fin T := ⟨4 * stageWidth + 5, by simp [T]⟩

/-- 若年ラウンド（`n < 32`）用の素朴テープ。 -/
def youngIdx : Fin T := ⟨4 * stageWidth + 6, by simp [T]⟩

/-- ラウンド予算カウンタ（`padTo` 用）。 -/
def budgetIdx : Fin T := ⟨4 * stageWidth + 7, by simp [T]⟩

theorem inpIdx_ne_slot (i : Fin 4) (j : Fin stageWidth) : inpIdx ≠ slotIdx i j := by
  intro h
  have := congrArg Fin.val h
  have := slotIdx_lt i j
  simp only [inpIdx] at *
  omega

theorem cpyIdx_ne_slot (i : Fin 4) (i' : Fin 4) (j : Fin stageWidth) :
    cpyIdx i ≠ slotIdx i' j := by
  intro h
  have hv := congrArg Fin.val h
  have := slotIdx_lt i' j
  simp only [cpyIdx] at hv
  omega

theorem cpyIdx_injective : Function.Injective cpyIdx := by
  intro i i' h
  have := congrArg Fin.val h
  simp only [cpyIdx] at this
  exact Fin.ext (by omega)

theorem cpyIdx_ne_inp (i : Fin 4) : cpyIdx i ≠ inpIdx := by
  intro h
  have := congrArg Fin.val h
  simp only [cpyIdx, inpIdx] at this
  omega

/-- **到着の目標テープ**：大域入力 1 本 ＋ 4 本のコピー最前線。
再始動するスロットのコピーテープはラウンド本体（`InputCopySentinel.sentinelInit`）が
空白配置から作り直すので、到着側は毎ラウンド 5 本すべてに書いてよい
（`FullMachineTapes.fullRound` の `cpy` も再始動の有無にかかわらず到着記号を 1 個追記する）。 -/
def tgtFull : Fin T → Bool :=
  fun k => decide (k = inpIdx) || decide (∃ i : Fin 4, k = cpyIdx i)

@[simp] theorem tgtFull_inp : tgtFull inpIdx = true := by simp [tgtFull]

@[simp] theorem tgtFull_cpy (i : Fin 4) : tgtFull (cpyIdx i) = true := by
  simp only [tgtFull, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨i, rfl⟩

@[simp] theorem tgtFull_slot (i : Fin 4) (j : Fin stageWidth) :
    tgtFull (slotIdx i j) = false := by
  simp only [tgtFull, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  refine ⟨fun h => inpIdx_ne_slot i j h.symm, ?_⟩
  rintro ⟨i', h⟩
  exact cpyIdx_ne_slot i' i j h.symm

/-! ## 2. スロットの分岐（`stageInSlot` のテープ側実現） -/

section Sched

variable {A C Γ : Type} {I : Interp (Fin 2) A C Γ T} {blank : Γ}

open PalPeg.StageTapes

/-- スロット 1 個ぶんのラウンド動作：担当段があるときだけチャンクを走らせる。 -/
def slotChunkProg (cAct : C) (chunk : Prog A C) : Prog A C :=
  Prog.ite cAct chunk Prog.skip

/-- **スケジュールのテープ側実現**。条件 `cAct` の読みが `(stageInSlot n i).isSome` に
一致していれば、`slotChunkProg` の 1 ラウンドの効果は `fullRound` の `slots i` 成分
（`match stageInSlot n i with | some S => I.srec S n | none => F.slots i`）に一致する。 -/
theorem slotSchedule_exec {sc : ℕ} {w : List (Fin sc)} {n : ℕ} {i : Fin 4} {cAct : C}
    {chunk : Prog A C} {Tp : Fin T → STape Γ} {Bs : ℕ}
    (Ifc : StageIface sc w) (F : FullT sc)
    (encSlot : StageT sc → (Fin T → STape Γ) → (Fin T → STape Γ))
    (hsched : I.condOf cAct (fun j => (Tp j).focus) = (stageInSlot n i).isSome)
    (hactive : ∀ S, stageInSlot n i = some S →
      ∃ acts, Exec I blank chunk Tp acts ∧ acts.length ≤ Bs ∧
        applyTrace blank Tp acts = encSlot (Ifc.srec S n) Tp)
    (hidle : stageInSlot n i = none → encSlot (F.slots i) Tp = Tp) :
    ∃ acts, Exec I blank (slotChunkProg cAct chunk) Tp acts ∧ acts.length ≤ Bs ∧
      applyTrace blank Tp acts
        = encSlot (match stageInSlot n i with
            | some S => Ifc.srec S n
            | none => F.slots i) Tp := by
  cases hs : stageInSlot n i with
  | none =>
      refine ⟨[], exec_ite_neg ?_ (exec_skip Tp), by simp, ?_⟩
      · rw [hsched, hs]; rfl
      · simp only [applyTrace_nil]
        exact (hidle hs).symm
  | some S =>
      obtain ⟨acts, hE, hlen, heff⟩ := hactive S hs
      refine ⟨acts, exec_ite_pos ?_ hE, hlen, ?_⟩
      · rw [hsched, hs]; rfl
      · simpa [hs] using heff

end Sched

/-! ## 3. ラウンド本体の直列化 -/

section RoundBody

variable {A C Γ : Type} {I : Interp (Fin 2) A C Γ T} {blank : Γ}

/-- プログラムの列の逐次合成。 -/
def seqList : List (Prog A C) → Prog A C
  | [] => Prog.skip
  | p :: ps => Prog.seq p (seqList ps)

/-- **直列化の実行補題**。`k` 番目のプログラムが「先頭 `k` 個ぶんを適用したテープ」から
ちょうど `as[k]` を実行するなら、全体はその連結を実行する。 -/
theorem seqList_exec :
    ∀ (ps : List (Prog A C)) (as : List (List (Fin T → Γ × Move)))
      (T0 : Fin T → STape Γ), ps.length = as.length →
      (∀ (k : ℕ) (hk : k < ps.length) (hk' : k < as.length),
        Exec I blank ps[k] (applyTrace blank T0 ((as.take k).flatten)) as[k]) →
      Exec I blank (seqList ps) T0 as.flatten := by
  intro ps
  induction ps with
  | nil =>
      intro as T0 hlen _
      have : as = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst this
      simpa [seqList] using exec_skip (I := I) (blank := blank) T0
  | cons p ps ih =>
      intro as T0 hlen hchain
      cases as with
      | nil => simp at hlen
      | cons a as =>
          have h0 : Exec I blank p T0 a := by
            have := hchain 0 (by simp) (by simp)
            simpa using this
          have hrest : Exec I blank (seqList ps) (applyTrace blank T0 a) as.flatten := by
            refine ih as (applyTrace blank T0 a) (by simpa using hlen) ?_
            intro k hk hk'
            have hnext := hchain (k + 1) (by simpa using Nat.succ_lt_succ hk)
              (by simpa using Nat.succ_lt_succ hk')
            have he : ((a :: as).take (k + 1)).flatten = a ++ (as.take k).flatten := by
              simp
            rw [he, applyTrace_append] at hnext
            simpa using hnext
          have := exec_seq h0 hrest
          simpa [seqList] using this

/-- **大域ラウンド本体**（`ASSEMBLY_PLAN.md` §2.4）：
4 スロットのチャンク → 退役スロットの消去チャンク → 再始動スロットの
コピー供給・番兵初期化 → 受理ビットの更新 → 予算の消化。 -/
def fullRoundProg (pSlot : Fin 4 → Prog A C) (pClear pCopy pAnswer pPad : Prog A C) :
    Prog A C :=
  seqList [pSlot 0, pSlot 1, pSlot 2, pSlot 3, pClear, pCopy, pAnswer, pPad]

/-- **大域プログラム**。持ち越し制御なので、トップレベルは
「毎ラウンド 1 動作の番兵 ＋ ラウンド本体」の無限ループ 1 本だけ
（`ProgLangPersist2.progMachinePM` がラウンド境界を与える）。 -/
def fullProg (cTrue : C) (padAct : A) (body : Prog A C) : Prog A C :=
  Prog.loop cTrue padAct body

/-- **ラウンド本体の効果**：8 区画の動作列の連結がラウンド全体の動作列であり、
その効果は各区画を順に適用したもの。 -/
theorem fullRoundProg_effect
    (pSlot : Fin 4 → Prog A C) (pClear pCopy pAnswer pPad : Prog A C)
    (as : List (List (Fin T → Γ × Move))) (T0 : Fin T → STape Γ)
    (hlen : as.length = 8)
    (hchain : ∀ (k : ℕ) (hk : k < 8) (hk' : k < as.length),
      Exec I blank
        ([pSlot 0, pSlot 1, pSlot 2, pSlot 3, pClear, pCopy, pAnswer, pPad][k]'(by simpa using hk))
        (applyTrace blank T0 ((as.take k).flatten)) as[k]) :
    Exec I blank (fullRoundProg pSlot pClear pCopy pAnswer pPad) T0 as.flatten := by
  refine seqList_exec _ as T0 (by simpa using hlen.symm) ?_
  intro k hk hk'
  exact hchain k (by simpa using hk) hk'

end RoundBody

/-! ## 4. ラウンドの帰納 -/

section Rounds

open PalPeg.StageTapes

variable {A C Γ : Type}

theorem foldEffect_append {Terminal : Type}
    (Fe : Terminal → (Fin T → STape Γ) → (Fin T → STape Γ))
    (Ge : Terminal → (Fin T → STape Γ) → Bool → Bool)
    (l₁ l₂ : List Terminal) (x : Bool × (Fin T → STape Γ)) :
    foldEffect Fe Ge (l₁ ++ l₂) x = foldEffect Fe Ge l₂ (foldEffect Fe Ge l₁ x) := by
  simp [foldEffect]

/-- **ラウンドの帰納**：ラウンドごとのテープ変換 `Fe` とフラグ更新 `Ge` が
（到達可能な符号化状態の上で）`fullRound` / `fullAnswer` を実現するなら、
`m` ラウンドの畳み込みは `fullState` / `fullAnswer` そのものである。 -/
theorem foldEffect_fullState {sc : ℕ} {w : List (Fin sc)}
    (Ifc : StageIface sc w) (bl leftSym : Fin sc) (rs : Restart)
    (Fe : Fin 2 → (Fin T → STape Γ) → (Fin T → STape Γ))
    (Ge : Fin 2 → (Fin T → STape Γ) → Bool → Bool)
    (Inv : ℕ → FullT sc → Prop)
    (encFull : ℕ → FullT sc → (Fin T → STape Γ))
    (init : FullT sc) (input : List (Fin 2))
    (hstepF : ∀ n, n < input.length → ∀ F, Inv n F →
      Fe (input.getD n 0) (encFull n F)
        = encFull (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hstepG : ∀ n, n < input.length → ∀ F b, Inv n F →
      Ge (input.getD n 0) (encFull n F) b = fullAnswer Ifc (n + 1))
    (hstepI : ∀ n, n < input.length → ∀ F, Inv n F →
      Inv (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hinit : Inv 0 init) :
    ∀ m, m ≤ input.length →
      foldEffect Fe Ge (input.take m) (false, encFull 0 init)
          = ((if m = 0 then false else fullAnswer Ifc m),
              encFull m (FullMachineTapes.fullState bl leftSym rs Ifc init m))
        ∧ Inv m (FullMachineTapes.fullState bl leftSym rs Ifc init m) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, hinit⟩
  | succ m ih =>
      intro hm
      obtain ⟨iheq, ihinv⟩ := ih (by omega)
      have hlt : m < input.length := by omega
      have htake : input.take (m + 1) = input.take m ++ [input.getD m 0] := by
        rw [List.take_add_one]
        congr 1
        rw [List.getElem?_eq_getElem hlt, List.getD_eq_getElem input 0 hlt]
        rfl
      refine ⟨?_, ?_⟩
      · rw [htake, foldEffect_append, iheq]
        show foldEffect Fe Ge [input.getD m 0]
            ((if m = 0 then false else fullAnswer Ifc m),
              encFull m (FullMachineTapes.fullState bl leftSym rs Ifc init m)) = _
        rw [foldEffect_cons, foldEffect_nil]
        simp only []
        rw [hstepF m hlt _ ihinv, hstepG m hlt _ _ ihinv]
        rw [if_neg (by omega), FullMachineTapes.fullState_succ]
      · rw [FullMachineTapes.fullState_succ]
        exact hstepI m hlt _ ihinv

end Rounds

/-! ## 5. 出口：`SAccepts` と `PAL` -/

section Exit

open PalPeg.StageTapes

variable {A C Γ : Type} [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ]
  {B : ℕ}

/-- 空語は必ず拒否される（初期受理フラグが `false` に固定されているため）。 -/
theorem SAccepts_nil (I : InterpF (Fin 2) A C Γ T) (prog : Prog A C)
    (encT : Fin 2 → Γ) (htape : 0 < T) (hB : 0 < B) (blank : Γ) :
    ¬ (progMachinePM I prog tgtFull encT htape hB blank).SAccepts [] := by
  rw [progMachinePM_SAccepts_iff I prog tgtFull encT htape hB blank []]
  simp

/-- **主定理（受理判定）**：1 ラウンドの意味論が `fullRound` / `fullAnswer` を実現するなら、
機械の受理はちょうど `fullAnswer I |input|` である（空語を除く）。 -/
theorem pal_machine_SAccepts_iff {sc : ℕ} {w : List (Fin sc)}
    (Ifc : StageIface sc w) (bl leftSym : Fin sc) (rs : Restart)
    (I : InterpF (Fin 2) A C Γ T) (prog : Prog A C) (encT : Fin 2 → Γ)
    (htape : 0 < T) (hB : 0 < B) (blank : Γ)
    (Fe : Fin 2 → (Fin T → STape Γ) → (Fin T → STape Γ))
    (Ge : Fin 2 → (Fin T → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Fin 2) (Tp : Fin T → STape Γ) (b : Bool),
      roundSemM I tgtFull encT blank (B - 1) (([prog], b), Tp) a = (([prog], Ge a Tp b), Fe a Tp))
    (Inv : ℕ → FullT sc → Prop) (encFull : ℕ → FullT sc → (Fin T → STape Γ))
    (init : FullT sc) (input : List (Fin 2))
    (hstepF : ∀ n, n < input.length → ∀ F, Inv n F →
      Fe (input.getD n 0) (encFull n F)
        = encFull (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hstepG : ∀ n, n < input.length → ∀ F b, Inv n F →
      Ge (input.getD n 0) (encFull n F) b = fullAnswer Ifc (n + 1))
    (hstepI : ∀ n, n < input.length → ∀ F, Inv n F →
      Inv (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hinit : Inv 0 init)
    (henc0 : encFull 0 init = fun _ => STape.blankTape blank)
    (hne : input ≠ []) :
    (progMachinePM I prog tgtFull encT htape hB blank).SAccepts input
      ↔ fullAnswer Ifc input.length = true := by
  rw [progMachinePM_SAccepts_effect I prog tgtFull encT htape hB blank Fe Ge hround input]
  rw [← henc0]
  have h := (foldEffect_fullState Ifc bl leftSym rs Fe Ge Inv encFull init input
    hstepF hstepG hstepI hinit input.length le_rfl).1
  rw [List.take_length] at h
  rw [h]
  have : input.length ≠ 0 := by
    intro h0
    exact hne (List.eq_nil_of_length_eq_zero h0)
  simp only [if_neg this]

/-- **出口定理**：`fullAnswer` が接頭辞の回文性と一致する（`InputEmbed` の
`full_answer_mem_PAL_of_embed'` がまさにこれを与える）なら、機械の受理言語は
空語を除いて `PAL` に一致する。 -/
theorem pal_SAccepts_iff_of {sc : ℕ} {w : List (Fin sc)}
    (Ifc : StageIface sc w) (bl leftSym : Fin sc) (rs : Restart)
    (I : InterpF (Fin 2) A C Γ T) (prog : Prog A C) (encT : Fin 2 → Γ)
    (htape : 0 < T) (hB : 0 < B) (blank : Γ)
    (Fe : Fin 2 → (Fin T → STape Γ) → (Fin T → STape Γ))
    (Ge : Fin 2 → (Fin T → STape Γ) → Bool → Bool)
    (hround : ∀ (a : Fin 2) (Tp : Fin T → STape Γ) (b : Bool),
      roundSemM I tgtFull encT blank (B - 1) (([prog], b), Tp) a = (([prog], Ge a Tp b), Fe a Tp))
    (Inv : ℕ → FullT sc → Prop) (encFull : ℕ → FullT sc → (Fin T → STape Γ))
    (init : FullT sc) (input : List (Fin 2))
    (hstepF : ∀ n, n < input.length → ∀ F, Inv n F →
      Fe (input.getD n 0) (encFull n F)
        = encFull (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hstepG : ∀ n, n < input.length → ∀ F b, Inv n F →
      Ge (input.getD n 0) (encFull n F) b = fullAnswer Ifc (n + 1))
    (hstepI : ∀ n, n < input.length → ∀ F, Inv n F →
      Inv (n + 1) (fullRound bl leftSym rs Ifc (n + 1) F))
    (hinit : Inv 0 init)
    (henc0 : encFull 0 init = fun _ => STape.blankTape blank)
    (hPAL : ∀ n, n ≤ input.length → (fullAnswer Ifc n = true ↔ (input.take n) ∈ PAL))
    (hne : input ≠ []) :
    (progMachinePM I prog tgtFull encT htape hB blank).SAccepts input ↔ input ∈ PAL := by
  rw [pal_machine_SAccepts_iff Ifc bl leftSym rs I prog encT htape hB blank Fe Ge hround
    Inv encFull init input hstepF hstepG hstepI hinit henc0 hne,
    hPAL input.length le_rfl, List.take_length]

/-- 機械の受理言語は厳密実時間で認識される（`ProgLangPersist2.progMachinePM_recognizedBy`）。 -/
theorem pal_recognizedBy_of (I : InterpF (Fin 2) A C Γ T) (prog : Prog A C)
    (encT : Fin 2 → Γ) (htape : 0 < T) (hB : 0 < B) (blank : Γ) :
    RecognizedBy { v | (progMachinePM I prog tgtFull encT htape hB blank).SAccepts v } :=
  progMachinePM_recognizedBy I prog tgtFull encT htape hB blank

end Exit

end PalPeg.FullMachineProg

/-
公理チェック（0 エラー・警告なし・`sorry` なし。
`propext / Classical.choice / Quot.sound` のみに依存）:

```
#print axioms PalPeg.FullMachineProg.T_eq
#print axioms PalPeg.FullMachineProg.slotIdx_ne_of_ne
#print axioms PalPeg.FullMachineProg.slotEmb
#print axioms PalPeg.FullMachineProg.tgtFull_slot
#print axioms PalPeg.FullMachineProg.slotSchedule_exec
#print axioms PalPeg.FullMachineProg.seqList_exec
#print axioms PalPeg.FullMachineProg.fullRoundProg_effect
#print axioms PalPeg.FullMachineProg.foldEffect_fullState
#print axioms PalPeg.FullMachineProg.SAccepts_nil
#print axioms PalPeg.FullMachineProg.pal_machine_SAccepts_iff
#print axioms PalPeg.FullMachineProg.pal_SAccepts_iff_of
#print axioms PalPeg.FullMachineProg.pal_recognizedBy_of
```
-/
