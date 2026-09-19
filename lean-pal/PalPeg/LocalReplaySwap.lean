import PalPeg.LocalSchedule
import PalPeg.LocalTick1

/-!
# `LocalReplaySwap`：`replayStartVM` の head copy を O(1) の view swap で実装する

`LocalSchedule` §5 は、`replayStartVM` の `right := center`（と `left := center`）を
歩くジョブで実装すると締切に間に合わないことを示し、§6.5 が `centerMirror` との
張り替えを提案した。本ファイルはそれを `LocalArrival.abs'` の上で完成させる。

発見と決定。

1. **`ViewSync` は `abs'` には弱すぎる。**  `abs'` の head は `near` と `far` の境界を
   見る（`far` は抽象 `incoming` に入る）。`cells`/`pos`/`gap` が一致しても
   `absHead'` は一致しない（`viewSync_not_absHead'`）。正しい同期は構造一致
   `Twin`（`twin_iff_absHead'`）。§1 で `Twin` がすべての view アクションで保たれる
   ことを示す。
2. **鏡は 2 本要る。**  一回の張り替えは鏡を 1 本消費する。`right` と `left` の
   両方を `center` にするので、鏡 `mirR`・`mirL` の 2 本（§2–§3）。
3. **`commitReplaySwap`**（§4）は `commitReplay` の後に 2 本の張り替え。
   `replayStartVM entry (abs' x) (abs' y)` を `hright`/`hleft` なしで示す。
4. **再構築（§5–§6）。**  張り替え後、旧 `left` は `center` から左に歩いただけの
   view なので、右に巻き戻せば `Twin` に戻る（`rewind_twin`、コスト = 巻き戻す
   セル数 + gap 修正 1）。**旧 `right` は戻らない**：`σ v = pos v + |near|` は
   すべての局所アクションで単調非減少で、`Twin` は `σ` を保つので、`σ` が
   `center` より大きい view は `center` が動かない限り二度と `Twin` にならない
   （`sigma_viewLocal_mono`、`never_twin_of_sigma_lt`）。右への本当の一歩は
   `σ` を 1 増やす（`sigma_moveRight_far`）。よって「2 本の鏡を旧 `left`/旧 `right`
   から再構築する」方式は `σ` の意味で 1 本分足りない —— 名前つきの未解決点（§7）。
5. 予算（§6）：巻き戻し `≤ R` セル + 1 は `R ≥ 1` で `R * 2048` に収まる。

**無条件 PAL ∈ PEG は未完.**
-/

set_option autoImplicit false

namespace PalPeg.LocalReplaySwap

open PalPeg.LocalInputView (InputView WF pos)
open PalPeg.LocalArrival (absHead' abs' feedL')
open PalPeg.LocalState (GalilVML)
open PalPeg.GalilScaffoldChainInputSupply (GalilVM)

/-! ## 1. `abs'` に対する正しい同期：`Twin` -/

/-- 二つの view の、`absHead'` が見る部分の構造一致。 -/
def Twin (v w : InputView) : Prop :=
  v.back = w.back ∧ v.focus = w.focus ∧ v.near = w.near ∧
    RTQueue.toList v.far = RTQueue.toList w.far ∧ v.gap = w.gap

theorem Twin.refl (v : InputView) : Twin v v := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Twin.symm {v w : InputView} (h : Twin v w) : Twin w v :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem Twin.trans {u v w : InputView} (h1 : Twin u v) (h2 : Twin v w) : Twin u w :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1,
    h1.2.2.2.1.trans h2.2.2.2.1, h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem Twin.absHead' {v w : InputView} (h : Twin v w) (q : List (Fin 2)) :
    absHead' v q = absHead' w q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold PalPeg.LocalArrival.absHead'
  rw [h1, h2, h3, h4, h5]

/-- **`Twin` はちょうど `absHead'` の一致。** -/
theorem twin_iff_absHead' (v w : InputView) (q : List (Fin 2)) :
    Twin v w ↔ absHead' v q = absHead' w q := by
  refine ⟨fun h => h.absHead' q, fun h => ?_⟩
  have hh := congrArg GalilScaffoldInputHead.PlaceHead.head h
  have hg := congrArg GalilScaffoldInputHead.PlaceHead.gap h
  refine ⟨congrArg GalilScaffoldInputHead.Head.left hh, congrArg GalilScaffoldInputHead.Head.focus hh, congrArg GalilScaffoldInputHead.Head.right hh, ?_, hg⟩
  have hi := congrArg GalilScaffoldInputHead.Head.incoming hh
  exact List.append_cancel_right hi

/-- **`ViewSync` では足りない。**  中身も位置も gap も同じだが、`near` と `far` の
境界が違う二つの view は、`absHead'` が異なる。 -/
theorem viewSync_not_absHead' :
    ∃ v w : InputView, WF v ∧ WF w ∧ LocalSchedule.ViewSync v w ∧
      absHead' v [] ≠ absHead' w [] := by
  let v : InputView := ⟨[], none, [], RTQueue.snoc RTQueue.empty 0, false⟩
  let w : InputView := ⟨[], none, [some 0], RTQueue.empty, false⟩
  have hv : WF v := RTQueue.inv_snoc RTQueue.inv_empty 0
  have hw : WF w := RTQueue.inv_empty
  have hl : RTQueue.toList (RTQueue.snoc (RTQueue.empty : RTQueue.Queue (Fin 2)) 0) = [0] := by
    rw [RTQueue.toList_snoc RTQueue.inv_empty, RTQueue.toList_empty]; rfl
  refine ⟨v, w, hv, hw, ⟨?_, rfl, rfl⟩, ?_⟩
  · show [] ++ none :: ([] ++ (RTQueue.toList (RTQueue.snoc RTQueue.empty 0)).map some)
        = [] ++ none :: ([some 0] ++ (RTQueue.toList RTQueue.empty).map some)
    rw [hl, RTQueue.toList_empty]; rfl
  · intro h
    have := congrArg (fun p : GalilScaffoldInputHead.PlaceHead => p.head.right) h
    simp [v, w, PalPeg.LocalArrival.absHead'] at this

theorem Twin.withGap {v w : InputView} (h : Twin v w) (b : Bool) :
    Twin { v with gap := b } { w with gap := b } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

theorem Twin.pos {v w : InputView} (h : Twin v w) : pos v = pos w := by
  unfold LocalInputView.pos; rw [h.1]

theorem Twin.arrive {v w : InputView} (hv : WF v) (hw : WF w) (h : Twin v w) (a : Fin 2) :
    Twin (LocalInputView.arrive a v) (LocalInputView.arrive a w) := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  show RTQueue.toList (RTQueue.snoc v.far a) = RTQueue.toList (RTQueue.snoc w.far a)
  rw [RTQueue.toList_snoc hv, RTQueue.toList_snoc hw, h.2.2.2.1]

theorem Twin.stepLeft {v w : InputView} (h : Twin v w) :
    Twin (LocalInputView.stepLeft v) (LocalInputView.stepLeft w) := by
  rcases v with ⟨b, f, n, q, g⟩
  rcases w with ⟨b', f', n', q', g'⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h5
  cases b with
  | nil => exact ⟨rfl, rfl, rfl, h4, rfl⟩
  | cons c r => exact ⟨rfl, rfl, rfl, h4, rfl⟩

theorem Twin.stepRight {v w : InputView} (hv : WF v) (hw : WF w) (h : Twin v w) :
    Twin (LocalInputView.stepRight v) (LocalInputView.stepRight w) := by
  rcases v with ⟨b, f, n, q, g⟩
  rcases w with ⟨b', f', n', q', g'⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only at h1 h2 h3 h4 h5
  subst h1 h2 h3 h5
  have hv' : RTQueue.Inv q := hv
  have hw' : RTQueue.Inv q' := hw
  cases n with
  | cons c rest => exact ⟨rfl, rfl, rfl, h4, rfl⟩
  | nil =>
      have e1 : RTQueue.head? q = RTQueue.head? q' := by
        rw [RTQueue.head?_eq hv', RTQueue.head?_eq hw', h4]
      cases hh : RTQueue.head? q' with
      | none =>
          have h0 : RTQueue.head? q = none := e1.trans hh
          simp only [LocalInputView.stepRight, h0, hh]
          exact ⟨rfl, rfl, rfl, h4, rfl⟩
      | some a =>
          have h0 : RTQueue.head? q = some a := e1.trans hh
          simp only [LocalInputView.stepRight, h0, hh]
          exact ⟨rfl, rfl, rfl, by rw [RTQueue.toList_tail hv', RTQueue.toList_tail hw', h4], rfl⟩

theorem Twin.moveRight {v w : InputView} (hv : WF v) (hw : WF w) (h : Twin v w) :
    Twin (LocalInputView.moveRight v) (LocalInputView.moveRight w) := by
  unfold LocalInputView.moveRight
  rw [← h.2.2.2.2]
  cases v.gap
  · exact h.withGap true
  · exact (h.stepRight hv hw).withGap false

theorem Twin.moveLeftV {v w : InputView} (h : Twin v w) :
    Twin (LocalInputView.moveLeftV v) (LocalInputView.moveLeftV w) := by
  unfold LocalInputView.moveLeftV
  rw [← h.2.2.2.2]
  cases v.gap
  · exact h.stepLeft.withGap true
  · exact h.withGap false

theorem Twin.repositionStep {v w : InputView} (hv : WF v) (hw : WF w) (h : Twin v w)
    (target : ℕ) :
    Twin (LocalInputView.repositionStep target v) (LocalInputView.repositionStep target w) := by
  unfold LocalInputView.repositionStep
  rw [h.pos]
  split_ifs
  · exact h.stepRight hv hw
  · exact h.stepLeft
  · exact h

/-! ### 1.1 view アクションの名前 -/

/-- `LocalState.ViewLocal` の 5 つの選択肢に名前を付けたもの。 -/
inductive ViewAct
  | stay
  | arrive (a : Fin 2)
  | right
  | left
  | repos (target : ℕ)

def applyAct : ViewAct → InputView → InputView
  | .stay, v => v
  | .arrive a, v => LocalInputView.arrive a v
  | .right, v => LocalInputView.moveRight v
  | .left, v => LocalInputView.moveLeftV v
  | .repos t, v => LocalInputView.repositionStep t v

theorem viewLocal_applyAct (act : ViewAct) (v : InputView) :
    LocalState.ViewLocal v (applyAct act v) := by
  cases act with
  | stay => exact Or.inl rfl
  | arrive a => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | right => exact Or.inr (Or.inr (Or.inl rfl))
  | left => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | repos t => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨t, rfl⟩)))

/-- すべての局所 view ステップは何らかの名前つきアクション。 -/
theorem viewLocal_exists_act {v w : InputView} (h : LocalState.ViewLocal v w) :
    ∃ act, w = applyAct act v := by
  rcases h with h | ⟨a, h⟩ | h | h | ⟨t, h⟩
  · exact ⟨.stay, h⟩
  · exact ⟨.arrive a, h⟩
  · exact ⟨.right, h⟩
  · exact ⟨.left, h⟩
  · exact ⟨.repos t, h⟩

theorem WF_applyAct (act : ViewAct) {v : InputView} (hv : WF v) : WF (applyAct act v) := by
  cases act with
  | stay => exact hv
  | arrive a => exact LocalInputView.WF_arrive hv a
  | right => exact LocalTick1.WF_moveRight hv
  | left => exact LocalTick1.WF_moveLeftV hv
  | repos t =>
      show WF (LocalInputView.repositionStep t v)
      unfold LocalInputView.repositionStep
      split_ifs
      · exact LocalInputView.WF_stepRight hv
      · exact LocalInputView.WF_stepLeft hv
      · exact hv

/-- **鏡の規律の核。**  同じアクションを真似れば `Twin` は保たれる。 -/
theorem Twin.applyAct {v w : InputView} (hv : WF v) (hw : WF w) (h : Twin v w)
    (act : ViewAct) : Twin (applyAct act v) (applyAct act w) := by
  cases act with
  | stay => exact h
  | arrive a => exact h.arrive hv hw a
  | right => exact h.moveRight hv hw
  | left => exact h.moveLeftV
  | repos t => exact h.repositionStep hv hw t

/-! ## 2. 二本の鏡を持つ包み -/

variable {P : ℕ}

/-- `GalilVML` ＋ `center` の鏡 2 本（`right` 用と `left` 用）。 -/
structure Mirrored2 (P : ℕ) where
  vm : GalilVML P
  mirR : InputView
  mirL : InputView

/-- 鏡の不変量：両方が `center` の `Twin` で、整形式。 -/
def MirInv (m : Mirrored2 P) : Prop :=
  Twin m.mirR m.vm.center ∧ Twin m.mirL m.vm.center ∧ WF m.mirR ∧ WF m.mirL

/-- **鏡つきティック。**  `vm` を `y` に進め、そのとき `center` が受けたアクション
`act` を両方の鏡にも流す。 -/
def mirrorTick (act : ViewAct) (y : GalilVML P) (m : Mirrored2 P) : Mirrored2 P :=
  { vm := y, mirR := applyAct act m.mirR, mirL := applyAct act m.mirL }

/-- **鏡の規律は不変量を保つ。** -/
theorem mirInv_mirrorTick {m : Mirrored2 P} (h : MirInv m) (hc : WF m.vm.center)
    (act : ViewAct) {y : GalilVML P} (hy : y.center = applyAct act m.vm.center) :
    MirInv (mirrorTick act y m) := by
  obtain ⟨hR, hL, wR, wL⟩ := h
  refine ⟨?_, ?_, WF_applyAct act wR, WF_applyAct act wL⟩
  · show Twin (applyAct act m.mirR) y.center
    rw [hy]; exact hR.applyAct wR hc act
  · show Twin (applyAct act m.mirL) y.center
    rw [hy]; exact hL.applyAct wL hc act

/-- 鏡つきティックの局所性：鏡も 1 アクションずつ。 -/
theorem mirrorTick_local (act : ViewAct) (y : GalilVML P) (m : Mirrored2 P) :
    LocalState.ViewLocal m.mirR (mirrorTick act y m).mirR ∧
      LocalState.ViewLocal m.mirL (mirrorTick act y m).mirL :=
  ⟨viewLocal_applyAct act _, viewLocal_applyAct act _⟩

/-! ### 2.1 到着：`feedL'` はすべての view を叩くので、鏡も叩く -/

def feedM (a : Fin 2) (rest : List (Fin 2)) (m : Mirrored2 P) : Mirrored2 P :=
  mirrorTick (.arrive a) (feedL' a rest m.vm) m

theorem mirInv_feedM {m : Mirrored2 P} (h : MirInv m) (hc : WF m.vm.center)
    (a : Fin 2) (rest : List (Fin 2)) : MirInv (feedM a rest m) :=
  mirInv_mirrorTick h hc (.arrive a) rfl

theorem abs'_feedM {m : Mirrored2 P} (hw : LocalState.ViewsWF m.vm) (a : Fin 2)
    (rest : List (Fin 2)) (hp : m.vm.pending = a :: rest) :
    abs' (feedM a rest m).vm = abs' m.vm :=
  PalPeg.LocalArrival.abs'_feedL' hw a rest hp

/-! ### 2.2 `center` を動かさないティック

`LocalTick1` の走査ティック（`SearchFrame.center`、`scanStep1/2`、`bgState`）と
`LocalTick2` のコミットはどれも `center` に触れない：`act = .stay`。 -/

theorem mirInv_stay {m : Mirrored2 P} (h : MirInv m) (hc : WF m.vm.center)
    {y : GalilVML P} (hy : y.center = m.vm.center) :
    MirInv (mirrorTick .stay y m) :=
  mirInv_mirrorTick h hc .stay hy

theorem tickL1_center {S : GalilScaffoldChainInputSupply.Shared} {q : ℕ} {first : Fin 9} {delay : ℕ}
    {x y : GalilVML P} (h : LocalTick1.TickL1 S q first delay x y) : y.center = x.center := by
  cases h with
  | wait z ch hm hr hav hs hch =>
      exact (LocalTick1.bgState_center _ _ _ _).trans hs.frame.center
  | count z ch hm hav hc hs hch =>
      exact (LocalTick1.bgState_center _ _ _ _).trans hs.frame.center
  | «match» z ch o hm hav hc hpol hrep hper hahead hcan hs hmt hch ho =>
      exact (LocalTick1.birthL_center _ _).trans hs.frame.center

theorem commitReplay_center (entry : ℕ) (x : GalilVML P) :
    (LocalTick2.commitReplay entry x).center = x.center := rfl

theorem commitRestart_center (entry : ℕ) (jL jW jD : Fin P) (bL : Bool) (x : GalilVML P) :
    (LocalTick2.commitRestart entry jL jW jD bL x).center = x.center := rfl

theorem commitShift_center (jR : Fin P) (bR : Bool) (w : GalilScaffoldChainWatch.State)
    (x : GalilVML P) : (LocalTick2.commitShift jR bR w x).center = x.center := rfl

theorem commitFallback_center (jF : Fin P) (bF : Bool) (x : GalilVML P) :
    (LocalTick2.commitFallback jF bF x).center = x.center := rfl

/-! ## 3. 二本の張り替え -/

/-- `right ↔ mirR`、`left ↔ mirL`。物理 view は 1 本も動かない。 -/
def swap2 (m : Mirrored2 P) : Mirrored2 P :=
  { vm := { m.vm with right := m.mirR, left := m.mirL }, mirR := m.vm.right, mirL := m.vm.left }

theorem abs'_swap2 {m : Mirrored2 P} (h : MirInv m) :
    abs' (swap2 m).vm
      = { abs' m.vm with right := (abs' m.vm).center, left := (abs' m.vm).center } := by
  show { LocalState.abs { m.vm with right := m.mirR, left := m.mirL } with
      left := absHead' m.mirL m.vm.pending
      center := absHead' m.vm.center m.vm.pending
      right := absHead' m.mirR m.vm.pending } = _
  rw [h.1.absHead', h.2.1.absHead']
  rfl

/-! ## 4. `commitReplaySwap` -/

/-- **`replayStartVM` の実時間実装**：カウンタ／バッファは `commitReplay`（2 ティック）、
head copy は 0 ティックの張り替え。 -/
def commitReplaySwap (entry : ℕ) (m : Mirrored2 P) : Mirrored2 P :=
  swap2 { m with vm := LocalTick2.commitReplay entry m.vm }

theorem mirInv_commitReplay {m : Mirrored2 P} (entry : ℕ) (h : MirInv m) :
    MirInv { m with vm := LocalTick2.commitReplay entry m.vm } := h

/-- **`hright`/`hleft` なしの `replayStartVM`。** -/
theorem replayStartVM_commitReplaySwap {m : Mirrored2 P} {entry : ℕ}
    (hinj : LocalState.RolesInjective m.vm)
    (hpl : m.vm.pol LocalState.Ctr.length = true) (hpw : m.vm.pol LocalState.Ctr.work = true)
    (hclean : ∀ i, LocalBuffers.Cleared (LocalBuffers.idle m.vm.dpBuf i))
    (hm : MirInv m) :
    GalilScaffoldChainInputSupply.replayStartVM entry (abs' m.vm) (abs' (commitReplaySwap entry m).vm) := by
  have hs := abs'_swap2 (mirInv_commitReplay (m := m) entry hm)
  have ha := LocalTick2.abs_commitReplay (entry := entry) hinj hpl hpw hclean
  unfold commitReplaySwap
  rw [hs]
  have hc : (abs' (LocalTick2.commitReplay entry m.vm)).center = (abs' m.vm).center := rfl
  refine ⟨?_, hc, hc, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).replay = (LocalState.abs m.vm).radius
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).radius = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).length = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).remaining
      = (LocalState.abs m.vm).remaining
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).cycle = (LocalState.abs m.vm).cycle
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).fpp = (LocalState.abs m.vm).fpp
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).chain = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).search = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).lower = _
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).dp
      = GalilScaffoldControl.reset entry (LocalState.abs m.vm).dp
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).periodOnly
      = (LocalState.abs m.vm).periodOnly
    rw [ha]
  · show (LocalState.abs (LocalTick2.commitReplay entry m.vm)).walker
      = (LocalState.abs m.vm).walker
    rw [ha]


/-- 張り替え直後、`right` と `left` は `center` の `Twin`（次の走査はここから）。 -/
theorem commitReplaySwap_twins {m : Mirrored2 P} (entry : ℕ) (hm : MirInv m) :
    Twin (commitReplaySwap entry m).vm.right (commitReplaySwap entry m).vm.center ∧
      Twin (commitReplaySwap entry m).vm.left (commitReplaySwap entry m).vm.center :=
  ⟨hm.1, hm.2.1⟩

/-! ## 5. 再構築：旧 `left` は巻き戻せる、旧 `right` は戻らない -/

/-! ### 5.1 旧 `left`：左への小旅行 `Exc` -/

/-- `v` は `c` から、`r`（`v` の focus から `c` 側へ向かう順）のセルだけ左に
歩いた view。 -/
def Exc (r : List (Option (Fin 2))) (v c : InputView) : Prop :=
  c.back = r.reverse ++ v.back ∧ v.focus :: v.near = r ++ c.focus :: c.near ∧
    RTQueue.toList v.far = RTQueue.toList c.far

theorem exc_nil_twin {v c : InputView} (h : Exc [] v c) (hg : v.gap = c.gap) : Twin v c := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [List.reverse_nil, List.nil_append] at h1 h2
  obtain ⟨hf, hn⟩ := List.cons.inj h2
  exact ⟨h1.symm, hf, hn, h3, hg⟩

theorem exc_of_twin {v c : InputView} (h : Twin v c) : Exc [] v c :=
  ⟨by rw [h.1]; rfl, by rw [h.2.1, h.2.2.1]; rfl, h.2.2.2.1⟩

/-- 一歩左に歩くと小旅行が 1 セル伸びる。 -/
theorem exc_stepLeft {r : List (Option (Fin 2))} {v c : InputView} (h : Exc r v c)
    {b : Option (Fin 2)} {rest : List (Option (Fin 2))} (hb : v.back = b :: rest) :
    Exc (b :: r) (LocalInputView.stepLeft v) c := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases v with ⟨vb, vf, vn, vq, vg⟩
  simp only at hb
  subst hb
  refine ⟨?_, ?_, h3⟩
  · show c.back = (b :: r).reverse ++ rest
    rw [h1]; simp
  · show b :: vf :: vn = (b :: r) ++ c.focus :: c.near
    simp only at h2
    rw [h2]; rfl

/-- 一歩右に歩くと小旅行が 1 セル縮む。 -/
theorem exc_stepRight {x : Option (Fin 2)} {r : List (Option (Fin 2))} {v c : InputView}
    (h : Exc (x :: r) v c) : Exc r (LocalInputView.stepRight v) c := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases v with ⟨vb, vf, vn, vq, vg⟩
  simp only at h1 h2 h3
  obtain ⟨hx, hn⟩ := List.cons.inj h2
  subst hx
  simp only [List.append_eq] at hn
  subst hn
  obtain ⟨y, ys, hy⟩ : ∃ y ys, r ++ c.focus :: c.near = y :: ys := by
    cases r with
    | nil => exact ⟨_, _, rfl⟩
    | cons a t => exact ⟨_, _, rfl⟩
  simp only [LocalInputView.stepRight]
  rw [hy]
  refine ⟨?_, ?_, h3⟩
  · show c.back = r.reverse ++ vf :: vb
    rw [h1]; simp
  · show y :: ys = r ++ c.focus :: c.near
    exact hy.symm

theorem exc_arrive {r : List (Option (Fin 2))} {v c : InputView} (hv : WF v) (hc : WF c)
    (h : Exc r v c) (a : Fin 2) :
    Exc r (LocalInputView.arrive a v) (LocalInputView.arrive a c) := by
  refine ⟨h.1, h.2.1, ?_⟩
  show RTQueue.toList (RTQueue.snoc v.far a) = RTQueue.toList (RTQueue.snoc c.far a)
  rw [RTQueue.toList_snoc hv, RTQueue.toList_snoc hc, h.2.2]

theorem gap_stepRight_of_near {v : InputView} (hn : v.near ≠ []) :
    (LocalInputView.stepRight v).gap = v.gap := by
  rcases v with ⟨b, f, n, q, g⟩
  cases n with
  | nil => exact absurd rfl hn
  | cons c rest => rfl

/-- `n` 回の右一歩。 -/
def stepRightN : ℕ → InputView → InputView
  | 0, v => v
  | n + 1, v => stepRightN n (LocalInputView.stepRight v)

/-- **巻き戻し。**  `r.length` 回の右一歩で `Exc r` は `Exc []` に戻り、gap は動かない。 -/
theorem exc_rewind : ∀ (r : List (Option (Fin 2))) {v c : InputView}, Exc r v c →
    Exc [] (stepRightN r.length v) c ∧ (stepRightN r.length v).gap = v.gap
  | [], v, c, h => ⟨h, rfl⟩
  | x :: r, v, c, h => by
      have hn : v.near ≠ [] := by
        intro h0
        have h2 := h.2.1
        rw [h0] at h2
        have := congrArg List.length h2
        simp at this
      obtain ⟨h', hg⟩ := exc_rewind r (exc_stepRight h)
      exact ⟨h', hg.trans (gap_stepRight_of_near hn)⟩

/-- gap を一つ合わせる（1 アクション、位置は動かない）。 -/
def fixGap (g : Bool) (v : InputView) : InputView :=
  if v.gap = g then v else if v.gap then LocalInputView.moveLeftV v else LocalInputView.moveRight v

theorem fixGap_local (g : Bool) (v : InputView) : LocalState.ViewLocal v (fixGap g v) := by
  unfold fixGap
  split_ifs
  · exact Or.inl rfl
  · exact viewLocal_applyAct .left v
  · exact viewLocal_applyAct .right v

theorem fixGap_eq (g : Bool) (v : InputView) :
    fixGap g v = { v with gap := g } := by
  unfold fixGap
  rcases v with ⟨b, f, n, q, vg⟩
  cases vg <;> cases g <;> rfl

/-- **旧 `left` からの鏡の再構築。**  `r.length` 回の右一歩 ＋ gap 修正 1 回で
`center` の `Twin`。 -/
theorem rewind_twin {r : List (Option (Fin 2))} {v c : InputView} (h : Exc r v c) :
    Twin (fixGap c.gap (stepRightN r.length v)) c := by
  obtain ⟨h1, _⟩ := exc_rewind r h
  rw [fixGap_eq]
  exact exc_nil_twin (v := { stepRightN r.length v with gap := c.gap }) h1 rfl

/-- 右一歩は `pos` が目標より小さいとき `repositionStep` そのもの（局所）。 -/
theorem repositionStep_of_lt {t : ℕ} {v : InputView} (h : pos v < t) :
    LocalInputView.repositionStep t v = LocalInputView.stepRight v := by
  unfold LocalInputView.repositionStep; rw [if_pos h]

/-- `Exc r v c` の距離：`pos c = pos v + |r|`。 -/
theorem exc_pos {r : List (Option (Fin 2))} {v c : InputView} (h : Exc r v c) :
    pos c = pos v + r.length := by
  unfold LocalInputView.pos; rw [h.1]; simp; omega

/-! ### 5.2 旧 `right`：`σ` の障害 -/

/-- `σ v = pos v + |near|`：`far` から取り出したセルの累計。 -/
def sigma (v : InputView) : ℕ := pos v + v.near.length

theorem Twin.sigma_eq {v w : InputView} (h : Twin v w) : sigma v = sigma w := by
  unfold sigma; rw [h.pos, h.2.2.1]

theorem sigma_stepLeft (v : InputView) : sigma (LocalInputView.stepLeft v) = sigma v := by
  rcases v with ⟨b, f, n, q, g⟩
  cases b <;> simp [sigma, LocalInputView.stepLeft, LocalInputView.pos]; omega

theorem sigma_stepRight_ge (v : InputView) : sigma v ≤ sigma (LocalInputView.stepRight v) := by
  rcases v with ⟨b, f, n, q, g⟩
  cases n with
  | cons c rest => simp [sigma, LocalInputView.stepRight, LocalInputView.pos]; omega
  | nil =>
      cases hh : RTQueue.head? q with
      | none => simp [sigma, LocalInputView.stepRight, hh]
      | some a => simp [sigma, LocalInputView.stepRight, LocalInputView.pos, hh]

/-- **`σ` はすべての局所 view アクションで単調非減少。** -/
theorem sigma_viewLocal_mono {v w : InputView} (h : LocalState.ViewLocal v w) :
    sigma v ≤ sigma w := by
  obtain ⟨act, rfl⟩ := viewLocal_exists_act h
  cases act with
  | stay => exact le_rfl
  | arrive a => exact le_rfl
  | right =>
      show sigma v ≤ sigma (LocalInputView.moveRight v)
      unfold LocalInputView.moveRight
      split_ifs
      · exact sigma_stepRight_ge v
      · exact le_rfl
  | left =>
      show sigma v ≤ sigma (LocalInputView.moveLeftV v)
      unfold LocalInputView.moveLeftV
      split_ifs
      · exact le_rfl
      · exact (sigma_stepLeft v).ge
  | repos t =>
      show sigma v ≤ sigma (LocalInputView.repositionStep t v)
      unfold LocalInputView.repositionStep
      split_ifs
      · exact sigma_stepRight_ge v
      · exact (sigma_stepLeft v).ge
      · exact le_rfl

/-- 本当の右一歩（`far` から 1 セル取る）は `σ` を 1 増やす。 -/
theorem sigma_moveRight_far {v : InputView} (hw : WF v) (hg : v.gap = true) (hn : v.near = [])
    (hf : RTQueue.toList v.far ≠ []) : sigma (LocalInputView.moveRight v) = sigma v + 1 := by
  rcases v with ⟨b, f, n, q, g⟩
  simp only at hg hn hf
  subst hg hn
  have hq : RTQueue.Inv q := hw
  obtain ⟨a, rest, hl⟩ : ∃ a rest, RTQueue.toList q = a :: rest := by
    cases hh : RTQueue.toList q with
    | nil => exact absurd hh hf
    | cons a r => exact ⟨a, r, rfl⟩
  have hh : RTQueue.head? q = some a := by rw [RTQueue.head?_eq hq, hl]; rfl
  simp [sigma, LocalInputView.moveRight, LocalInputView.stepRight, LocalInputView.pos, hh]

/-- `n` 個の局所 view ステップ。 -/
def ViewLocalN : ℕ → InputView → InputView → Prop
  | 0, v, w => w = v
  | n + 1, v, w => ∃ u, LocalState.ViewLocal v u ∧ ViewLocalN n u w

theorem sigma_viewLocalN_mono : ∀ (n : ℕ) {v w : InputView}, ViewLocalN n v w → sigma v ≤ sigma w
  | 0, v, w, h => by rw [show w = v from h]
  | n + 1, v, w, ⟨u, hu, hn⟩ => (sigma_viewLocal_mono hu).trans (sigma_viewLocalN_mono n hn)

/-- **旧 `right` は戻らない。**  `σ v > σ c` なら、`v` をどう局所的に動かしても、
`σ` が増えない（例：到着だけを受ける）`c'` の `Twin` にはならない。 -/
theorem never_twin_of_sigma_lt {v c : InputView} (hlt : sigma c < sigma v) (n : ℕ)
    {v' c' : InputView} (hv : ViewLocalN n v v') (hc : sigma c' = sigma c) : ¬ Twin v' c' := by
  intro ht
  have h1 := sigma_viewLocalN_mono n hv
  have h2 := ht.sigma_eq
  omega

/-! ## 6. 再構築の予算 -/

def delay : ℕ := LocalSchedule.delay

/-- 巻き戻し `≤ R` セル ＋ gap 修正 1 は、`R ≥ 1` の再生の `R * 2048` ティックに収まる。 -/
theorem rebuild_fits_replay {R d : ℕ} (hR : 1 ≤ R) (hd : d ≤ R) : d + 1 ≤ R * delay := by
  unfold delay LocalSchedule.delay; omega

theorem rebuild_fits_replay' {R : ℕ} (hR : 1 ≤ R) : R ≤ R * delay := by
  unfold delay LocalSchedule.delay; omega

/-! ## 7. 残っている名前つきの穴

* **第二の鏡の供給源。**  `commitReplaySwap` は鏡を 2 本消費する。§5.1 で旧 `left`
  （`Exc r`）は 1 本に戻せるが、旧 `right` は走査中に `far` からセルを取ったので
  `σ` が `center` を超え（`sigma_moveRight_far`）、`center` の `σ` が増えない限り
  二度と `Twin` にならない（`never_twin_of_sigma_lt`）。張り替え 1 回ごとに
  `σ ≤ σ(center)` の view が正味 1 本減るので、固定本数の view＋歩行だけの
  方式は閉じない。解消案：(a) 次の replay までに `center` が旧 `right` の位置
  以上に進むことを示す（Galil の fallback では一般に成り立たない）、
  (b) `abs'` の `right` を「物理 view ＋ 未消化の再生オフセット」で読む
  仮想カーソル抽象に変える（旧 `right` は再生終了時の抽象 `right` と同じ `σ`）、
  (c) `far/near` 境界を忘れる抽象（`ViewSync` で足りる）に scaffold 側を合わせる。
* `Exc` の維持は「`center` は到着以外で動かない」窓でしか示していない
  （`exc_arrive`、`exc_stepLeft`）。`LocalTick1` の走査・replay では
  `tickL1_center` によりそれで足りるが、shift ティックで `center` が右に動く
  区間と巻き戻しが重なる場合は未証明。
* 張り替え時点での `MirInv` を、実際の制御の走行（`LocalTick1`/`LocalTick2` の
  各ティックを `mirrorTick` で包んだもの）に沿って運ぶ証明は未着手。
  部品（`mirInv_mirrorTick`、`mirInv_feedM`、`tickL1_center`、各 commit の
  `*_center`）はそろっている。
* 旧 `left` の `Exc r` の `r.length ≤ R`（小旅行の長さが再生半径以下）は仮定
  （`rebuild_fits_replay.hd`）。

**無条件 PAL ∈ PEG は未完.**
-/

end PalPeg.LocalReplaySwap

#print axioms PalPeg.LocalReplaySwap.twin_iff_absHead'
#print axioms PalPeg.LocalReplaySwap.viewSync_not_absHead'
#print axioms PalPeg.LocalReplaySwap.Twin.applyAct
#print axioms PalPeg.LocalReplaySwap.viewLocal_exists_act
#print axioms PalPeg.LocalReplaySwap.mirInv_mirrorTick
#print axioms PalPeg.LocalReplaySwap.mirInv_feedM
#print axioms PalPeg.LocalReplaySwap.abs'_feedM
#print axioms PalPeg.LocalReplaySwap.tickL1_center
#print axioms PalPeg.LocalReplaySwap.abs'_swap2
#print axioms PalPeg.LocalReplaySwap.replayStartVM_commitReplaySwap
#print axioms PalPeg.LocalReplaySwap.commitReplaySwap_twins
#print axioms PalPeg.LocalReplaySwap.exc_stepLeft
#print axioms PalPeg.LocalReplaySwap.exc_stepRight
#print axioms PalPeg.LocalReplaySwap.exc_arrive
#print axioms PalPeg.LocalReplaySwap.rewind_twin
#print axioms PalPeg.LocalReplaySwap.exc_pos
#print axioms PalPeg.LocalReplaySwap.sigma_viewLocal_mono
#print axioms PalPeg.LocalReplaySwap.sigma_moveRight_far
#print axioms PalPeg.LocalReplaySwap.never_twin_of_sigma_lt
#print axioms PalPeg.LocalReplaySwap.rebuild_fits_replay
#print axioms PalPeg.LocalReplaySwap.rebuild_fits_replay'
