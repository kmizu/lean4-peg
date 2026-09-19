import PalPeg.GalilCheckpoints

/-!
# `PackedRun` — 各点で pack を運ぶ有限 run（括り出し）

## なぜこのファイルがあるか

`StepsI` / `StepsIM` / `StepsIMW` / `StepsIMG` … は**文字通り同一の定義**を
pack 述語（`IPack` / `IPackM` / `IPackMW` / `IPackMG`）だけ差し替えて書いたもので、
それぞれに `*_trans`（連結）と `*_of_*`（pack の弱化）が**同じ証明でコピペ**されている。
`CloseoutLPack5.stepsI_trans` / `CloseoutPackRun12.stepsIM_trans` /
`CloseoutCheckW.stepsIMW_trans` / `CloseoutPackRun30.stepsIMG_trans` は同じ 8 行である。

証明はコードである。共通部分を括り出し、**pack を引数にする**。
以後 pack の変種を作るときは、`*_trans` を書き直さずこの 2 本を呼ぶ。

`pack_concat`（`CloseoutLPack5`）は `GalilVM` 固定で上の層にあるので、その 6 行は
ここに取り込んだ。これで `PackedRun` は `GalilCheckpoints` だけに依存する最下層部品になり、
`σ` について一般（`GalilVM` に限らない）。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg

open PalPeg PalPeg.GalilCheckpoints PalPeg.GalilRunSkeleton
open GalilScaffoldTop

variable {σ : Type}

/-- **各点で `Pk` を満たす、`x` から `y` への長さ `k` の `F`-trace。**
`StepsI*` 族の共通形。 -/
def PackedRun (F : Frame σ) (delay : ℕ) (Q : State σ → Prop) (Pk : State σ → Prop)
    (k : ℕ) (x y : State σ) : Prop :=
  ∃ g : ℕ → State σ, g 0 = x ∧ g k = y ∧ Trace F delay Q g k ∧ ∀ i, i ≤ k → Pk (g i)

namespace PackedRun

/-- **pack つき run は連結できる。** `stepsI_trans` / `stepsIM_trans` /
`stepsIMW_trans` / `stepsIMG_trans` の共通部分。 -/
theorem trans {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {k₁ k₂ : ℕ}
    {x y z : State σ} (h₁ : PackedRun F delay Q Pk k₁ x y)
    (h₂ : PackedRun F delay Q Pk k₂ y z) :
    PackedRun F delay Q Pk (k₁ + k₂) x z := by
  obtain ⟨g₁, hg₁0, hg₁k, htr₁, hp₁⟩ := h₁
  obtain ⟨g₂, hg₂0, hg₂k, htr₂, hp₂⟩ := h₂
  have hj : g₁ k₁ = g₂ 0 := by rw [hg₁k, hg₂0]
  refine ⟨concat g₁ g₂ k₁, ?_, ?_, trace_concat htr₁ htr₂ hj, ?_⟩
  · rw [concat_le g₁ g₂ (Nat.zero_le _)]; exact hg₁0
  · rw [concat_end g₁ g₂ hj]; exact hg₂k
  · intro i hi
    by_cases hie : i ≤ k₁
    · rw [concat_le g₁ g₂ hie]; exact hp₁ i hie
    · have hsplit : i = k₁ + (i - k₁) := by omega
      rw [hsplit, concat_end g₁ g₂ hj]
      exact hp₂ (i - k₁) (by omega)

/-- **pack は弱めてよい。** `stepsIMG_of_stepsIM` 型の共通部分。 -/
theorem mono {F : Frame σ} {delay : ℕ} {Q Pk Pk' : State σ → Prop} {k : ℕ}
    {x y : State σ} (hmono : ∀ s, Pk s → Pk' s) (h : PackedRun F delay Q Pk k x y) :
    PackedRun F delay Q Pk' k x y := by
  obtain ⟨g, h0, hk, htr, hp⟩ := h
  exact ⟨g, h0, hk, htr, fun i hi => hmono _ (hp i hi)⟩

/-- **pack つき run の各点は pack を満たす。**（射影） -/
theorem pack_at {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {k : ℕ}
    {x y : State σ} (h : PackedRun F delay Q Pk k x y) :
    ∃ g : ℕ → State σ, g 0 = x ∧ g k = y ∧ ∀ i, i ≤ k → Pk (g i) := by
  obtain ⟨g, h0, hk, _, hp⟩ := h
  exact ⟨g, h0, hk, hp⟩

end PackedRun

#print axioms PackedRun.trans
#print axioms PackedRun.mono
#print axioms PackedRun.pack_at

/-! ## `Trace` に沿った不変量

`_run` 218 本 / `_steps` 74 本 / `_boot` 30 本は、どれも同じ帰納法を書き直している
（`CloseoutLPack2.lpack_steps` がその典型：`i` に帰納、底は boot、段は tick 補題）。
それを 1 本にする。`Trace` 上の dot 記法で `htr.carried h0 hstep` と書ける。 -/

namespace GalilCheckpoints.Trace

/-- **不変量は trace に沿って運ばれる。** 始点で成立し、各 tick で保存されるなら、
trace の各点で成立する。 -/
theorem carried {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {st : ℕ → State σ}
    {e : ℕ} (htr : Trace F delay Q st e) (h0 : Pk (st 0))
    (hstep : ∀ i, i < e → Tick F delay (st i) (st (i + 1)) → Pk (st i) → Pk (st (i + 1))) :
    ∀ i, i ≤ e → Pk (st i) := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ n ih => intro _; exact hstep n (by omega) (htr.tick n (by omega)) (ih (by omega))

/-- **`Q` も使える版**（tick 補題が trace の `good` を要求するとき）。 -/
theorem carried' {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {st : ℕ → State σ}
    {e : ℕ} (htr : Trace F delay Q st e) (h0 : Pk (st 0))
    (hstep : ∀ i, i < e → Q (st i) → Q (st (i + 1)) →
      Tick F delay (st i) (st (i + 1)) → Pk (st i) → Pk (st (i + 1))) :
    ∀ i, i ≤ e → Pk (st i) :=
  htr.carried h0 (fun i hi ht hp =>
    hstep i hi (htr.good i (by omega)) (htr.good (i + 1) (by omega)) ht hp)

end GalilCheckpoints.Trace

namespace PackedRun

/-- **boot ＋ tick から pack つき run を作る。** `*_steps` 系の結論そのもの。 -/
theorem of_tick {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {st : ℕ → State σ}
    {e : ℕ} (htr : Trace F delay Q st e) (h0 : Pk (st 0))
    (hstep : ∀ i, i < e → Tick F delay (st i) (st (i + 1)) → Pk (st i) → Pk (st (i + 1))) :
    PackedRun F delay Q Pk e (st 0) (st e) :=
  ⟨st, rfl, rfl, htr, htr.carried h0 hstep⟩

end PackedRun

#print axioms GalilCheckpoints.Trace.carried
#print axioms GalilCheckpoints.Trace.carried'
#print axioms PackedRun.of_tick

end PalPeg
