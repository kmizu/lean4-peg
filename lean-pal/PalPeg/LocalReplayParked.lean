import PalPeg.LocalReplaySwap
import PalPeg.LocalTick1
import PalPeg.LocalTick2
import PalPeg.LocalArrival
import PalPeg.GalilFrontier
import PalPeg.GalilChosenRadiusLe

/-!
# `LocalReplayParked`：replay 中の右ヘッドを「駐車した物理 view ＋ 未消化の再生量」で読む

`LocalReplaySwap` §7 の未解決点 1 の解消案 (b)。

* replay 中の抽象右ヘッドは `absR x = left^[m] (absHead' x.right x.pending)`。
  `m` は replay 役のテープの値（`LocalCounter.val`）。replay 中でなければ物理 view
  そのもの（§1）。
* replay の一致ティック（§3）はカウンタを `pop` するだけで右 view を **動かさない**。
  抽象の右一歩は `right (left^[m+1] p) = left^[m] p`（`right_left_iterate`）で実現され、
  その前提 `m + 1 ≤ position p` は不変量 `ParkedOK`（§2）が運ぶ。
* 再生終了（フラグが落ちて `m = 0`）では `absR` は物理 view に継ぎ目なく戻る
  （`absR_of_val_zero`、`absR_of_not_replaying`）。
* `replayStart`（§5）：抽象 `right := center` は `left^[R] (駐車 view) = center`
  （`fallback_landing` の `t.right = left^[R] (right s.right)` を `abs'` 越しに読んだもの）
  で成り立ち、右の鏡は不要。`left := center` だけが鏡 `mirL` を 1 本消費し、旧 `left`
  から `rewind_twin` で再構築する（予算 `rebuild_fits_replay`）。
* replay でないティック（§6）では `abs'' = abs'`、fallback 側の commit と
  ジョブは駐車 view に触れない（§7）。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.LocalReplayParked

open PalPeg.GalilScaffoldChainInputSupply
open PalPeg.GalilScaffoldTop
open PalPeg.GalilScaffoldController (Control)
open PalPeg.GalilScaffoldInputHead (PlaceHead)
open PalPeg.LocalState
open PalPeg.LocalCounter (Seg)
open PalPeg.LocalInputView (InputView)
open PalPeg.LocalArrival (absHead' abs' absState' Ahead feedL')
open PalPeg.LocalTick1 (Inv PolPos SearchFrame TickL1 matchVm scanStep1 scanStep2 matchScan
  matchCtl bgState)
open PalPeg.LocalReplaySwap (Twin Exc)

variable {P : ℕ}

/-! ## 0. 抽象ヘッド上の左右の逆関係 -/

/-- 原点でなければ右は左の逆。 -/
theorem right_left_of_pos {p : PlaceHead} (h : 0 < position p) :
    GalilScaffoldChainVerifier.right (GalilScaffoldInputHead.left p) = p := by
  rcases p with ⟨⟨f, ls, rs, q⟩, g⟩
  cases g with
  | true => rfl
  | false =>
      cases ls with
      | nil => simp [position] at h
      | cons a ls => rfl

/-- **駐車の核。**  `m + 1 ≤ position p` なら、`left^[m+1] p` から右に一歩で `left^[m] p`。 -/
theorem right_left_iterate {m : ℕ} {p : PlaceHead} (h : m + 1 ≤ position p) :
    GalilScaffoldChainVerifier.right (GalilScaffoldInputHead.left^[m + 1] p)
      = GalilScaffoldInputHead.left^[m] p := by
  rw [Function.iterate_succ_apply']
  apply right_left_of_pos
  have := (left_iterate m p (by omega)).1
  omega

/-! ## 1. 駐車抽象 `absR` / `abs''` -/

/-- replay 役テープの値。 -/
def rval (x : GalilVML P) : ℕ := LocalCounter.val (x.phys (x.roles .replay))

/-- 物理右 view の（`abs'` と同じ）読み。 -/
def physHead (x : GalilVML P) : PlaceHead := absHead' x.right x.pending

/-- **駐車抽象の右ヘッド。** -/
def absR (x : GalilVML P) : PlaceHead :=
  if x.ctl.replaying then GalilScaffoldInputHead.left^[rval x] (physHead x) else physHead x

/-- `abs'` の右ヘッドを `absR` に差し替えたもの。 -/
def abs'' (x : GalilVML P) : GalilVM := { abs' x with right := absR x }

def absState'' (x : GalilVML P) : GalilScaffoldTop.State GalilVM := ⟨x.ctl, abs'' x⟩

@[simp] theorem abs''_right (x : GalilVML P) : (abs'' x).right = absR x := rfl

theorem absR_of_not_replaying {x : GalilVML P} (hr : x.ctl.replaying = false) :
    absR x = physHead x := by
  unfold absR; rw [hr]; rfl

theorem absR_of_replaying {x : GalilVML P} (hr : x.ctl.replaying = true) :
    absR x = GalilScaffoldInputHead.left^[rval x] (physHead x) := by
  unfold absR; rw [hr]; rfl

/-- **再生終了は継ぎ目なし。**  値が 0 なら、フラグにかかわらず物理 view。 -/
theorem absR_of_val_zero {x : GalilVML P} (h0 : rval x = 0) : absR x = physHead x := by
  unfold absR; cases x.ctl.replaying
  · rfl
  · show GalilScaffoldInputHead.left^[rval x] (physHead x) = _
    rw [h0]; rfl

theorem absR_eq_iter {x : GalilVML P} (h : x.ctl.replaying = true ∨ rval x = 0) :
    absR x = GalilScaffoldInputHead.left^[rval x] (physHead x) := by
  rcases h with h | h
  · exact absR_of_replaying h
  · rw [absR_of_val_zero h, h]; rfl

theorem abs''_eq_abs' {x : GalilVML P} (hr : x.ctl.replaying = false) : abs'' x = abs' x := by
  show { abs' x with right := absR x } = abs' x
  rw [absR_of_not_replaying hr]; rfl

theorem abs''_eq_abs'_of_val_zero {x : GalilVML P} (h0 : rval x = 0) : abs'' x = abs' x := by
  show { abs' x with right := absR x } = abs' x
  rw [absR_of_val_zero h0]; rfl

/-! ## 2. 不変量 `ParkedOK` -/

/-- replay 中、再生量は駐車 view の位置を超えない（左反復が原点で潰れない）。 -/
def ParkedOK (x : GalilVML P) : Prop := x.ctl.replaying = true → rval x ≤ position (physHead x)

/-- 位置の読み替え：`position (absR x) + m = position (駐車 view)`。 -/
theorem position_absR {x : GalilVML P} (hr : x.ctl.replaying = true) (hok : ParkedOK x) :
    position (absR x) + rval x = position (physHead x) ∧
      arrived (absR x) = arrived (physHead x) := by
  rw [absR_of_replaying hr]
  exact left_iterate _ _ (hok hr)

/-- `ParkedOK` と抽象の `Frontier` 型の式：駐車 view の位置自体は右ヘッドの frontier
（`position_le_arrived`）で押さえられるので、`absR` の位置＋再生量も `2·arrived` 以下。 -/
theorem frontier_absR {x : GalilVML P} (hr : x.ctl.replaying = true) (hok : ParkedOK x) :
    position (absR x) + rval x ≤ 2 * arrived (absR x) := by
  obtain ⟨h1, h2⟩ := position_absR hr hok
  rw [h1, h2]
  exact position_le_arrived _

/-! ## 3. replay の一致ティック：`pop` だけ、view は動かない -/

/-- `scanStep1` から右一歩を抜いたもの。 -/
def scanStep1R (w : GalilVML P) : GalilVML P := { scanStep1 w with right := w.right }

/-- replay 中の一致ティックの VM 部分。 -/
def matchVmR (ch : ChainVM) (w : GalilVML P) : GalilVML P := scanStep2 ch (scanStep1R w)

theorem matchVmR_eq (ch : ChainVM) (w : GalilVML P) :
    matchVmR ch w = { matchVm ch w with right := w.right } := rfl

theorem stepLocal_scanStep1R (w : GalilVML P) : StepLocal w (scanStep1R w) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8, h9, h10, h11⟩ := LocalTick1.stepLocal_scanStep1 w
  exact ⟨h1, h2, h3, h4, h5, h6, viewLocal_refl _, h8, h9, h10, h11⟩

theorem stepLocalN_matchVmR (ch : ChainVM) (c : Control) (w : GalilVML P) :
    LocalTick2.StepLocalN 2 w { matchVmR ch w with ctl := c } :=
  LocalTick1.stepLocalN_trans 1 1 (LocalTick1.stepLocalN_one (stepLocal_scanStep1R w))
    (LocalTick1.stepLocalN_one (LocalTick1.stepLocal_scanStep2 ch c (scanStep1R w)))

/-- 抽象の一致ティックが見る scan 射影（右は `absR` の一歩）。 -/
def matchScanR (x : GalilVML P) (ch : ChainVM) : ScanVM :=
  ⟨GalilScaffoldInputHead.left (abs'' x).left,
   GalilScaffoldChainVerifier.right (absR x), ch⟩

/-- 右 view を差し替えた補助状態（`Ahead`/`canRight` が自明になる）。 -/
private def dummyR (x : GalilVML P) : GalilVML P := { x with right := { x.right with gap := false } }

private theorem roles_ne' {w : GalilVML P} (h : RolesInjective w) {c d : Ctr} (hcd : c ≠ d) :
    w.roles c ≠ w.roles d := fun he => hcd (h he)

/-- replay テープの値は一致ティックで 1 減る。 -/
theorem rval_matchVmR {x z : GalilVML P} (hinv : Inv x) (hf : SearchFrame x z)
    (hr : x.ctl.replaying = true) {m : ℕ} (hm : rval x = m + 1) (ch : ChainVM) (c : Control) :
    rval { matchVmR ch z with ctl := c } = m := by
  have hinj : RolesInjective x := hinv.roles
  have hinjz : RolesInjective z := by
    intro a b hab; apply hinj; rw [← hf.roles]; exact hab
  have hzp : z.phys (z.roles .replay) = x.phys (x.roles .replay) := by
    rw [hf.roles]
    exact hf.phys _ (roles_ne' hinj (by decide)) (roles_ne' hinj (by decide))
      (roles_ne' hinj (by decide))
  have hzr : z.ctl.replaying = true := by rw [hf.ctl]; exact hr
  show LocalCounter.val ((matchVm ch z).phys (z.roles .replay)) = m
  rw [LocalTick1.physMatch_replay hinjz ch, if_pos hzr, hzp]
  exact LocalCounter.val_pop hm

/-- **項目 2（右ヘッド）。**  駐車 view は動かず、`absR` は抽象の右一歩。 -/
theorem absR_matchVmR {x z : GalilVML P} (hinv : Inv x) (hf : SearchFrame x z)
    (hr : x.ctl.replaying = true) {m : ℕ} (hm : rval x = m + 1) (hok : ParkedOK x)
    (ch : ChainVM) (c : Control) (hflag : c.replaying = true ∨ m = 0) :
    absR { matchVmR ch z with ctl := c } = GalilScaffoldChainVerifier.right (absR x) := by
  have hv := rval_matchVmR hinv hf hr hm ch c
  have hph : physHead { matchVmR ch z with ctl := c } = physHead x := by
    show absHead' z.right z.pending = absHead' x.right x.pending
    rw [hf.right, hf.pending]
  have hle : m + 1 ≤ position (physHead x) := hm ▸ hok hr
  rw [absR_eq_iter (by rcases hflag with h | h; exact Or.inl h; exact Or.inr (hv.trans h)),
    hv, hph, absR_of_replaying hr, hm, right_left_iterate hle]

/-- **項目 2（状態全体）。**  駐車つき一致ティックは抽象の
`replayDec true (afterCompare …)` そのもの。 -/
theorem abs''_matchVmR {x z : GalilVML P} (hinv : Inv x) (hpol : PolPos x) (hf : SearchFrame x z)
    (hr : x.ctl.replaying = true) {m : ℕ} (hm : rval x = m + 1) (hok : ParkedOK x)
    (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle)))
    (ch : ChainVM) (c : Control) (hflag : c.replaying = true ∨ m = 0) :
    abs'' { matchVmR ch z with ctl := c }
      = replayDec true (afterCompare (abs'' x) (matchScanR x ch) (searchLens.get (abs' z))) := by
  have hinv' : Inv (dummyR x) :=
    ⟨hinv.roles, hinv.attached,
      ⟨hinv.views.1, hinv.views.2.1, hinv.views.2.2.1, hinv.views.2.2.2.1, hinv.views.2.2.2.2⟩,
      hinv.radiusShaped, hinv.lowerShaped, hinv.lengthShaped, hinv.shaped⟩
  have hf' : SearchFrame (dummyR x) (dummyR z) :=
    ⟨hf.left, hf.center,
      (by show ({ z.right with gap := false } : InputView) = { x.right with gap := false }
          rw [hf.right]), hf.pending, hf.fppWalker, hf.roles, hf.pol, hf.phys, hf.radiusMir,
      hf.lowerMir, hf.lengthMir, hf.fppBuf, hf.fppPc, hf.fppDone, hf.chain, hf.ctl, hf.fppMode,
      hf.fppFinalStage, hf.periodOnly⟩
  have hrep : (dummyR x).ctl.replaying = true →
      0 < LocalCounter.val ((dummyR x).phys ((dummyR x).roles .replay)) := by
    intro _
    show 0 < rval x
    omega
  have hahead : Ahead (dummyR x).right (dummyR x).pending := by
    intro hg; exact absurd hg (by simp [dummyR])
  have hcan : GalilScaffoldChainVerifier.canRight
      (absHead' (dummyR x).right (dummyR x).pending) := Or.inl rfl
  have key := LocalTick1.abs_matchVm hinv' hpol hf' hrep hper hahead hcan ch
  have hR := absR_matchVmR hinv hf hr hm hok ch c hflag
  have e1 : abs'' { matchVmR ch z with ctl := c }
      = { abs' (matchVm ch (dummyR z)) with right := absR { matchVmR ch z with ctl := c } } := rfl
  have hr' : (dummyR x).ctl.replaying = true := hr
  rw [e1, key, hr', hR]
  rfl

/-- `matchCtl` のフラグ：落ちるのは値が 0 のときだけ。 -/
theorem matchCtl_flag {S : Shared}
    (hex : ∀ s, S.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    {delay : ℕ} {o : Bool} {c : Control} (hc : c.replaying = true) {v : GalilVM}
    {t : PalPeg.Program.STape Seg} (hv : v.replay = LocalCounter.absCtr t true) :
    (matchCtl S delay o c v).replaying = true ∨ LocalCounter.val t = 0 := by
  show (c.replaying && !S.replayExhausted v) = true ∨ _
  rw [hc, hex, hv, LocalCounter.zero_iff]
  by_cases h : LocalCounter.val t = 0
  · exact Or.inr h
  · left; simp [h]

/-- **項目 2＋3：制御込みの replay 一致ティック。**  `matchCtl` がフラグを落とす
（再生終了）場合も含めて一つの式。 -/
theorem abs''_replayMatch {S : Shared}
    (hex : ∀ s, S.replayExhausted s = GalilScaffoldCounter.zero s.replay)
    {x z : GalilVML P} (hinv : Inv x) (hpol : PolPos x) (hf : SearchFrame x z)
    (hr : x.ctl.replaying = true) {m : ℕ} (hm : rval x = m + 1) (hok : ParkedOK x)
    (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle)))
    (ch : ChainVM) (delay : ℕ) (o : Bool) :
    abs'' { matchVmR ch z with ctl := matchCtl S delay o x.ctl (abs'' (matchVmR ch z)) }
      = replayDec true (afterCompare (abs'' x) (matchScanR x ch) (searchLens.get (abs' z))) := by
  refine abs''_matchVmR hinv hpol hf hr hm hok hper ch _ ?_
  have hv := rval_matchVmR hinv hf hr hm ch (matchVm ch z).ctl
  have hpz : (matchVmR ch z).pol .replay = true := by
    show z.pol .replay = true; rw [hf.pol]; exact hpol.2.2.1
  rcases matchCtl_flag (S := S) (delay := delay) (o := o) hex hr
      (v := abs'' (matchVmR ch z))
      (t := (matchVmR ch z).phys ((matchVmR ch z).roles .replay))
      (by show LocalCounter.absCtr _ ((matchVmR ch z).pol .replay) = _; rw [hpz]) with h | h
  · exact Or.inl h
  · right; rw [← hv]; exact h

/-- `ParkedOK` は駐車つき一致ティックで保たれる。 -/
theorem parkedOK_matchVmR {x z : GalilVML P} (hinv : Inv x) (hf : SearchFrame x z)
    (hr : x.ctl.replaying = true) {m : ℕ} (hm : rval x = m + 1) (hok : ParkedOK x)
    (ch : ChainVM) (c : Control) : ParkedOK { matchVmR ch z with ctl := c } := by
  intro _
  have hv := rval_matchVmR hinv hf hr hm ch c
  have hph : physHead { matchVmR ch z with ctl := c } = physHead x := by
    show absHead' z.right z.pending = absHead' x.right x.pending
    rw [hf.right, hf.pending]
  rw [hv, hph]
  have := hok hr
  omega

/-- `Inv` も保たれる（右 view は WF のまま）。 -/
theorem inv_matchVmR {x : GalilVML P} (hinv : Inv x) (ch : ChainVM)
    (hrep : x.ctl.replaying = true → 0 < LocalCounter.val (x.phys (x.roles .replay)))
    (hper : x.periodOnly = true → 0 < LocalCounter.val (x.phys (x.roles .cycle))) :
    Inv (matchVmR ch x) := by
  have h := LocalTick1.inv_matchVm hinv ch hrep hper
  exact ⟨h.roles, h.attached,
    ⟨h.views.1, h.views.2.1, hinv.views.2.2.1, h.views.2.2.2.1, h.views.2.2.2.2⟩,
    h.radiusShaped, h.lowerShaped, h.lengthShaped, h.shaped⟩

/-! ## 4. 到着は `absR` にも見えない -/

theorem absR_feedL' {x : GalilVML P} (hw : ViewsWF x) (a : Fin 2) (rest : List (Fin 2))
    (hp : x.pending = a :: rest) : absR (feedL' a rest x) = absR x := by
  have hph : physHead (feedL' a rest x) = physHead x := by
    show absHead' (LocalInputView.arrive a x.right) rest = absHead' x.right x.pending
    rw [PalPeg.LocalArrival.absHead'_arrive hw.2.2.1, hp]
  unfold absR
  rw [hph]
  rfl

theorem abs''_feedL' {x : GalilVML P} (hw : ViewsWF x) (a : Fin 2) (rest : List (Fin 2))
    (hp : x.pending = a :: rest) : abs'' (feedL' a rest x) = abs'' x := by
  show { abs' (feedL' a rest x) with right := absR (feedL' a rest x) } = _
  rw [PalPeg.LocalArrival.abs'_feedL' hw a rest hp, absR_feedL' hw a rest hp]
  rfl

theorem parkedOK_feedL' {x : GalilVML P} (hw : ViewsWF x) (a : Fin 2) (rest : List (Fin 2))
    (hp : x.pending = a :: rest) (hok : ParkedOK x) : ParkedOK (feedL' a rest x) := by
  intro hr
  have hph : physHead (feedL' a rest x) = physHead x := by
    show absHead' (LocalInputView.arrive a x.right) rest = absHead' x.right x.pending
    rw [PalPeg.LocalArrival.absHead'_arrive hw.2.2.1, hp]
  rw [hph]
  exact hok hr

/-! ## 5. `replayStart`：右は駐車、左だけ鏡 1 本 -/

/-- `GalilVML` ＋ `left` 用の鏡 1 本。 -/
structure Mirrored1 (P : ℕ) where
  vm : GalilVML P
  mirL : InputView

def MirInv1 (m : Mirrored1 P) : Prop := Twin m.mirL m.vm.center ∧ LocalInputView.WF m.mirL

def mirrorTick1 (act : LocalReplaySwap.ViewAct) (y : GalilVML P) (m : Mirrored1 P) :
    Mirrored1 P :=
  { vm := y, mirL := LocalReplaySwap.applyAct act m.mirL }

theorem mirInv1_mirrorTick1 {m : Mirrored1 P} (h : MirInv1 m) (hc : LocalInputView.WF m.vm.center)
    (act : LocalReplaySwap.ViewAct) {y : GalilVML P}
    (hy : y.center = LocalReplaySwap.applyAct act m.vm.center) :
    MirInv1 (mirrorTick1 act y m) := by
  refine ⟨?_, LocalReplaySwap.WF_applyAct act h.2⟩
  show Twin (LocalReplaySwap.applyAct act m.mirL) y.center
  rw [hy]; exact h.1.applyAct h.2 hc act

/-- **`replayStartVM` の駐車実装。**  カウンタは `commitReplay`、制御は `c`、`left` は鏡と
張り替え、`right` の物理 view は **そのまま**。 -/
def commitReplayParked (entry : ℕ) (c : Control) (m : Mirrored1 P) : Mirrored1 P :=
  { vm := { LocalTick2.commitReplay entry m.vm with left := m.mirL, ctl := c }
    mirL := m.vm.left }

/-- commit 後の replay 役テープは commit 前の radius 役テープ。 -/
theorem rval_commitReplay (entry : ℕ) {x : GalilVML P} (hinj : RolesInjective x) :
    rval (LocalTick2.commitReplay entry x) = LocalCounter.val (x.phys (x.roles .radius)) := by
  have hne1 : x.roles Ctr.radius ≠ x.roles Ctr.length := roles_ne' hinj (by decide)
  have hne2 : x.roles Ctr.radius ≠ x.roles Ctr.work := roles_ne' hinj (by decide)
  have hnm : x.roles Ctr.radius ∉ [x.roles Ctr.length, x.roles Ctr.work] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hne1, hne2⟩
  simp only [rval, LocalTick2.commitReplay, LocalRoles.moveRoles, LocalRoles.swapAt_dst]
  rw [LocalTick2.pushSlots_not_mem hnm,
    LocalTick2.resetSlots_not_mem (LocalTick2.roles_not_mem_ctrSlots hinj
      (by decide : Ctr.radius ∉ LocalTick2.replayCleared))]

theorem commitReplayParked_rval (entry : ℕ) (c : Control) {m : Mirrored1 P}
    (hinj : RolesInjective m.vm) :
    rval (commitReplayParked entry c m).vm = LocalCounter.val (m.vm.phys (m.vm.roles .radius)) :=
  rval_commitReplay entry hinj

theorem commitReplayParked_physHead (entry : ℕ) (c : Control) (m : Mirrored1 P) :
    physHead (commitReplayParked entry c m).vm = physHead m.vm := rfl

/-- **項目 4。**  鏡 1 本（`mirL`）で `replayStartVM`。`right := center` は
`hland : left^[R] (abs' x).right = (abs' x).center`（`fallback_landing` の export）から。 -/
theorem replayStartVM_commitReplayParked
    {mm : Mirrored1 P} (entry : ℕ) (c : Control)
    (hinj : RolesInjective mm.vm)
    (hpl : mm.vm.pol Ctr.length = true) (hpw : mm.vm.pol Ctr.work = true)
    (hclean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle mm.vm.dpBuf i))
    (hm : MirInv1 mm) (hpre : mm.vm.ctl.replaying = false)
    (hflag : c.replaying = true ∨ LocalCounter.val (mm.vm.phys (mm.vm.roles .radius)) = 0)
    (hland : GalilScaffoldInputHead.left^[LocalCounter.val (mm.vm.phys (mm.vm.roles .radius))]
      (abs' mm.vm).right = (abs' mm.vm).center) :
    replayStartVM entry (abs'' mm.vm) (abs'' (commitReplayParked entry c mm).vm) := by
  have hv := commitReplayParked_rval entry c hinj
  have hR : absR (commitReplayParked entry c mm).vm = (abs' mm.vm).center := by
    rw [absR_eq_iter (by rcases hflag with h | h; exact Or.inl h; exact Or.inr (hv.trans h)),
      hv, commitReplayParked_physHead]
    exact hland
  have ha := LocalTick2.abs_commitReplay (entry := entry) hinj hpl hpw hclean
  rw [abs''_eq_abs' hpre]
  have hL : absHead' mm.mirL mm.vm.pending = (abs' mm.vm).center := hm.1.absHead' _
  refine ⟨?_, hR, hL, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).replay = (LocalState.abs mm.vm).radius
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).radius = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).length = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).remaining
      = (LocalState.abs mm.vm).remaining
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).cycle = (LocalState.abs mm.vm).cycle
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).fpp = (LocalState.abs mm.vm).fpp
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).chain = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).search = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).lower = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).dp
      = GalilScaffoldControl.reset entry (LocalState.abs mm.vm).dp
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).periodOnly
      = (LocalState.abs mm.vm).periodOnly
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry mm.vm)).walker
      = (LocalState.abs mm.vm).walker
    rw [ha]

/-- commit 直後の `ParkedOK`：`R ≤ position (駐車 view)` から。 -/
theorem parkedOK_commitReplayParked (entry : ℕ) (c : Control) {mm : Mirrored1 P}
    (hinj : RolesInjective mm.vm)
    (hle : LocalCounter.val (mm.vm.phys (mm.vm.roles .radius)) ≤ position (abs' mm.vm).right) :
    ParkedOK (commitReplayParked entry c mm).vm := by
  intro _
  rw [commitReplayParked_rval entry c hinj, commitReplayParked_physHead]
  exact hle

/-- 同じものを `fallback_landing` の回文 export（`PalAt … (position p - R) R`）から。 -/
theorem parkedOK_commitReplayParked_of_pal (entry : ℕ) (c : Control) {mm : Mirrored1 P}
    (hinj : RolesInjective mm.vm) {raw : List (Fin 2)}
    (hpal : Manacher.PalAt (encoded raw)
      (position (abs' mm.vm).right - LocalCounter.val (mm.vm.phys (mm.vm.roles .radius)))
      (LocalCounter.val (mm.vm.phys (mm.vm.roles .radius)))) :
    ParkedOK (commitReplayParked entry c mm).vm :=
  parkedOK_commitReplayParked entry c hinj (chosenRadius_le_position hpal)

/-- commit 直後の `Frontier`（駐車抽象で）：`GalilFrontier` の不変量が成立。 -/
theorem frontier_commitReplayParked (entry : ℕ) (c : Control) {mm : Mirrored1 P}
    (hinj : RolesInjective mm.vm) (hc : c.replaying = true)
    (hpr : mm.vm.pol Ctr.radius = true)
    (hle : LocalCounter.val (mm.vm.phys (mm.vm.roles .radius)) ≤ position (abs' mm.vm).right) :
    Frontier (abs'' (commitReplayParked entry c mm).vm) := by
  intro k hk
  have hok := parkedOK_commitReplayParked entry c hinj hle
  have hrp : (commitReplayParked entry c mm).vm.ctl.replaying = true := hc
  have hrep : (abs'' (commitReplayParked entry c mm).vm).replay
      = GalilScaffoldCounter.ofNat (LocalCounter.val (mm.vm.phys (mm.vm.roles .radius))) := by
    show absCtrs (LocalTick2.commitReplay entry mm.vm) Ctr.replay = _
    rw [LocalTick2.absCtrs_commitReplay_replay hinj]
    show LocalCounter.absCtr _ (mm.vm.pol Ctr.radius) = _
    rw [hpr]; rfl
  rw [hrep] at hk
  have hk' := ofNat_inj hk
  have hv := commitReplayParked_rval entry c hinj
  have := frontier_absR hrp hok
  rw [abs''_right, ← hk', ← hv]
  exact this

/-! ### 5.1 鏡の再構築（旧 `left` の巻き戻し） -/

theorem WF_stepRightN : ∀ (n : ℕ) {v : InputView}, LocalInputView.WF v →
    LocalInputView.WF (LocalReplaySwap.stepRightN n v)
  | 0, _, h => h
  | n + 1, _, h => WF_stepRightN n (LocalInputView.WF_stepRight h)

/-- 張り替えで外に出た旧 `left` が `center` からの小旅行 `Exc r` なら、
`|r|` 回の右一歩＋gap 修正 1 回で `MirInv1` が戻る。 -/
theorem mirInv1_rebuild {vm : GalilVML P} {r : List (Option (Fin 2))} {v : InputView}
    (hx : Exc r v vm.center) (hw : LocalInputView.WF v) :
    MirInv1 ⟨vm, LocalReplaySwap.fixGap vm.center.gap
      (LocalReplaySwap.stepRightN r.length v)⟩ := by
  refine ⟨LocalReplaySwap.rewind_twin hx, ?_⟩
  show LocalInputView.WF (LocalReplaySwap.fixGap _ _)
  rw [LocalReplaySwap.fixGap_eq]
  exact WF_stepRightN r.length hw

/-- 再構築コストは再生ティック数に収まる。 -/
theorem rebuild_budget {R : ℕ} {r : List (Option (Fin 2))} (hR : 1 ≤ R) (hr : r.length ≤ R) :
    r.length + 1 ≤ R * LocalReplaySwap.delay :=
  LocalReplaySwap.rebuild_fits_replay hR hr

/-! ## 6. replay でないティックは `abs''` = `abs'` -/

theorem tickL1_replaying_false {S : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : GalilVML P} (h : TickL1 S q first delay x y) (hr : x.ctl.replaying = false) :
    y.ctl.replaying = false := by
  cases h with
  | wait z ch hm _ hav hs hch => rw [LocalTick1.bgState_ctl]; exact hr
  | count z ch hm hav hc hs hch => rw [LocalTick1.bgState_ctl]; exact hr
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      rw [LocalTick1.birthL_ctl]
      show (x.ctl.replaying && _) = false
      rw [hr]; rfl

/-- **項目 5。**  replay でない局所走査ティックは `abs''` でもそのまま scaffold `Tick`。 -/
theorem tickL1_abs''_nonreplay {S : Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : GalilVML P}
    (hbirth : ∀ (bb : Bool) (s : GalilVM),
      (S.onLetter (GalilScaffoldChainInputSupply.afterBirth bb s) ↔ S.onLetter s) ∧
      (S.leftFirst (GalilScaffoldChainInputSupply.afterBirth bb s) ↔ S.leftFirst s) ∧
      S.replayExhausted (GalilScaffoldChainInputSupply.afterBirth bb s) = S.replayExhausted s)
    (hinv : Inv x) (h : TickL1 S q first delay x y)
    (hr : x.ctl.replaying = false) :
    Tick (galilFrameS S q first) delay (absState'' x) (absState'' y) := by
  have ht := LocalTick1.tickL1_abs hbirth hinv h
  show Tick (galilFrameS S q first) delay ⟨x.ctl, abs'' x⟩ ⟨y.ctl, abs'' y⟩
  rw [abs''_eq_abs' hr, abs''_eq_abs' (tickL1_replaying_false h hr)]
  exact ht

/-- `LocalTick2` の commit は制御レコードに触れないので、フラグが落ちていれば
`abs''` = `abs'`。 -/
theorem abs''_commitShift {x : GalilVML P} (hr : x.ctl.replaying = false) (jR : Fin P) (bR : Bool)
    (w : GalilScaffoldChainWatch.State) :
    abs'' (LocalTick2.commitShift jR bR w x) = abs' (LocalTick2.commitShift jR bR w x) :=
  abs''_eq_abs' hr

theorem abs''_commitFallback {x : GalilVML P} (hr : x.ctl.replaying = false) (jF : Fin P)
    (bF : Bool) :
    abs'' (LocalTick2.commitFallback jF bF x) = abs' (LocalTick2.commitFallback jF bF x) :=
  abs''_eq_abs' hr

theorem abs''_commitRestart {x : GalilVML P} (hr : x.ctl.replaying = false) (entry : ℕ)
    (jL jW jD : Fin P) (bL : Bool) :
    abs'' (LocalTick2.commitRestart entry jL jW jD bL x)
      = abs' (LocalTick2.commitRestart entry jL jW jD bL x) :=
  abs''_eq_abs' hr

/-! ## 7. `replayStart` までの fallback 側は駐車 view に触れない -/

theorem tickL1_right_nonmatch {S : Shared}
    {x z : GalilVML P} (hs : LocalTick1.SearchLocal S false x z) (src ch : ChainVM)
    (c : Control) :
    (bgState src ch c z).right = x.right ∧ (bgState src ch c z).pending = x.pending :=
  ⟨(LocalTick1.bgState_right _ _ _ _).trans hs.frame.right,
    (LocalTick1.bgState_pending _ _ _ _).trans hs.frame.pending⟩

theorem commitShift_right (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State)
    (x : GalilVML P) : (LocalTick2.commitShift jR bR w x).right = x.right := rfl

theorem commitFallback_right (jF : Fin P) (bF : Bool) (x : GalilVML P) :
    (LocalTick2.commitFallback jF bF x).right = x.right := rfl

theorem commitRestart_right (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (x : GalilVML P) :
    (LocalTick2.commitRestart entry jL jW jD bL x).right = x.right := rfl

theorem commitReplay_right (entry : ℕ) (x : GalilVML P) :
    (LocalTick2.commitReplay entry x).right = x.right := rfl

theorem commitReplayParked_right (entry : ℕ) (c : Control) (m : Mirrored1 P) :
    (commitReplayParked entry c m).vm.right = m.vm.right := rfl

theorem dpStep_right (g : Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape)
    (x : GalilVML P) : (LocalTick1.dpStep g x).right = x.right := rfl

theorem dpRun_right (g : ℕ → Fin 12 → GalilScaffoldTape.Tape → GalilScaffoldTape.Tape) :
    ∀ (n : ℕ) (x : GalilVML P), (LocalTick1.dpRun g n x).right = x.right
  | 0, _ => rfl
  | n + 1, x => dpRun_right g n (LocalTick1.dpStep (g n) x)

theorem repLeft_right (target n : ℕ) (x : GalilVML P) :
    (LocalTick2.repLeft target n x).right = x.right := by
  rw [LocalTick2.repLeft_eq]

theorem repFppWalker_right (target n : ℕ) (x : GalilVML P) :
    (LocalTick2.repFppWalker target n x).right = x.right := by
  rw [LocalTick2.repFppWalker_eq]

/-! ## 8. 残っている名前つきの穴

* **replay 中の wait/count ティック。**  `TickL1.wait/count` は `S.centre (abs' x)`、
  `available (abs' x)`、`searchEffect … (abs' x)` を `abs'` で述べている。replay 中は
  `abs' ≠ abs''`（右ヘッドが違う）なので、`abs''` 版の `Tick` を得るには
  `TickL1` の仮定を `abs''` で言い直した変種が要る（`SearchFrame` は `right`/`phys`/`roles`/
  `ctl.replaying` を保つので `absR` 自体は不変）。一致ティックは §3 で完了。
* **`hland` の供給。**  `replayStartVM_commitReplayParked` は
  `left^[R] (abs' x).right = (abs' x).center`（`R` = radius 役テープの値）を仮定する。
  `fallback_landing` の export は replayStart **後**の `t.right = left^[R] (right s.right)`、
  `t.center = t.right` なので、fallback の各相（shift/copy/home/fpp/markEnd/choose/rewind）の
  局所実装が `right`（§7）と `center`、radius テープを保つことを走行に沿って運ぶ必要がある。
  局所実装が存在する部分（commit 群、`repLeft`、`repFppWalker`、`dpRun`、背景ティック）は §7。
* **旧 `left` の `Exc r` と `|r| ≤ R`** は仮定のまま（`mirInv1_rebuild`、`rebuild_budget`）。
  再構築中に `center` が到着以外で動かないことも未証明。
* **`commitReplayParked` の局所性。**  `left ↔ mirL` の張り替えはポインタの付け替えで、
  `StepLocal` の `ViewLocal` 形式には入らない（`LocalReplaySwap.swap2` と同じ扱い）。
* **`ParkedOK` の他ティックでの保存**：到着（`parkedOK_feedL'`）と replay 一致
  （`parkedOK_matchVmR`）以外は未証明（wait/count は `SearchFrame` で自明だが未記述）。

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.LocalReplayParked

#print axioms PalPeg.LocalReplayParked.right_left_of_pos
#print axioms PalPeg.LocalReplayParked.right_left_iterate
#print axioms PalPeg.LocalReplayParked.absR_of_val_zero
#print axioms PalPeg.LocalReplayParked.abs''_eq_abs'
#print axioms PalPeg.LocalReplayParked.position_absR
#print axioms PalPeg.LocalReplayParked.frontier_absR
#print axioms PalPeg.LocalReplayParked.stepLocalN_matchVmR
#print axioms PalPeg.LocalReplayParked.rval_matchVmR
#print axioms PalPeg.LocalReplayParked.absR_matchVmR
#print axioms PalPeg.LocalReplayParked.abs''_matchVmR
#print axioms PalPeg.LocalReplayParked.matchCtl_flag
#print axioms PalPeg.LocalReplayParked.abs''_replayMatch
#print axioms PalPeg.LocalReplayParked.parkedOK_matchVmR
#print axioms PalPeg.LocalReplayParked.inv_matchVmR
#print axioms PalPeg.LocalReplayParked.abs''_feedL'
#print axioms PalPeg.LocalReplayParked.parkedOK_feedL'
#print axioms PalPeg.LocalReplayParked.mirInv1_mirrorTick1
#print axioms PalPeg.LocalReplayParked.rval_commitReplay
#print axioms PalPeg.LocalReplayParked.replayStartVM_commitReplayParked
#print axioms PalPeg.LocalReplayParked.parkedOK_commitReplayParked_of_pal
#print axioms PalPeg.LocalReplayParked.frontier_commitReplayParked
#print axioms PalPeg.LocalReplayParked.mirInv1_rebuild
#print axioms PalPeg.LocalReplayParked.rebuild_budget
#print axioms PalPeg.LocalReplayParked.tickL1_abs''_nonreplay
#print axioms PalPeg.LocalReplayParked.dpRun_right
#print axioms PalPeg.LocalReplayParked.repLeft_right
