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
open GalilScaffoldTop GalilScaffoldChainInputSupply

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

/-! ## tick 述語つきの run

`StepsAll`／`PackedRun` は状態述語 `Q`／`Pk` しか運ばない。oracle の run が
**canonical**（restart しない、fallback の place は walker、`init`／`replayStart` はカーソル保持）
であることは各 **tick** の性質なので、tick 述語 `R` を足した版を用意する。`R := fun _ _ => True`
で元に戻る。 -/

/-- `StepsAll` に tick 述語 `R` を足したもの。 -/
inductive StepsAllR (F : Frame σ) (delay : ℕ) (Q : State σ → Prop)
    (R : State σ → State σ → Prop) : ℕ → State σ → State σ → Prop
  | zero (x : State σ) (hx : Q x) : StepsAllR F delay Q R 0 x x
  | succ {n : ℕ} {x y z : State σ} (hx : Q x) (h : Tick F delay x y) (hr : R x y)
      (hs : StepsAllR F delay Q R n y z) : StepsAllR F delay Q R (n+1) x z

theorem stepsAllR_of_stepsAll {F : Frame σ} {delay : ℕ} {Q : State σ → Prop} {n : ℕ}
    {x y : State σ} (h : StepsAll F delay Q n x y) :
    StepsAllR F delay Q (fun _ _ => True) n x y := by
  induction h with
  | zero x hx => exact .zero x hx
  | succ hx h _ ih => exact .succ hx h trivial ih

theorem stepsAllR_stepsAll {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {R : State σ → State σ → Prop} {n : ℕ} {x y : State σ}
    (h : StepsAllR F delay Q R n x y) : StepsAll F delay Q n x y := by
  induction h with
  | zero x hx => exact .zero x hx
  | succ hx h _ _ ih => exact .succ hx h ih

theorem stepsAllR_steps {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {R : State σ → State σ → Prop} {n : ℕ} {x y : State σ}
    (h : StepsAllR F delay Q R n x y) : Steps F delay n x y :=
  stepsAll_steps (stepsAllR_stepsAll h)

theorem stepsAllR_trans {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {R : State σ → State σ → Prop} {m n : ℕ} {x y z : State σ}
    (h1 : StepsAllR F delay Q R m x y) (h2 : StepsAllR F delay Q R n y z) :
    StepsAllR F delay Q R (m + n) x z := by
  induction h1 with
  | zero _ _ => simpa using h2
  | succ hx h hr _ ih => rw [Nat.succ_add]; exact .succ hx h hr (ih h2)

theorem stepsAllR_fn {F : Frame σ} {delay : ℕ} {Q : State σ → Prop}
    {R : State σ → State σ → Prop} {n : ℕ} {x y : State σ}
    (h : StepsAllR F delay Q R n x y) :
    ∃ g : ℕ → State σ, g 0 = x ∧ g n = y ∧ Trace F delay Q g n ∧
      ∀ i, i < n → R (g i) (g (i+1)) := by
  induction h with
  | zero x hx =>
    exact ⟨fun _ => x, rfl, rfl, ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => hx⟩,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @succ n x y z hx h hr _ ih =>
    obtain ⟨g, hg0, hgn, htr, hR⟩ := ih
    refine ⟨fun i => if i = 0 then x else g (i-1), by simp, by simpa using hgn, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      rcases i with _ | i
      · simpa [hg0] using h
      · simpa using htr.tick i (by omega)
    · intro i hi
      rcases i with _ | i
      · simpa using hx
      · simpa using htr.good i (by omega)
    · intro i hi
      rcases i with _ | i
      · simpa [hg0] using hr
      · simpa using hR i (by omega)

/-- tick 述語は連結できる。 -/
theorem canon_concat {R : State σ → State σ → Prop} {f g : ℕ → State σ} {e n : ℕ}
    (hfg : f e = g 0) (hf : ∀ i, i < e → R (f i) (f (i+1)))
    (hg : ∀ i, i < n → R (g i) (g (i+1))) :
    ∀ i, i < e + n → R (concat f g e i) (concat f g e (i+1)) := by
  intro i hi
  by_cases h1 : i + 1 ≤ e
  · rw [concat_le f g h1, concat_le f g (by omega : i ≤ e)]
    exact hf i h1
  · by_cases h2 : i ≤ e
    · have hie : i = e := by omega
      subst hie
      rw [concat_le f g le_rfl, concat_end f g hfg (n := 1), hfg]
      exact hg 0 (by omega)
    · obtain ⟨d, rfl⟩ : ∃ d, i = e + d := ⟨i - e, by omega⟩
      rw [concat_end f g hfg, show e + d + 1 = e + (d + 1) by omega, concat_end f g hfg]
      exact hg d (by omega)

/-- **各点で `Pk`、各 tick で `R` を満たす run。** -/
def PackedRunR (F : Frame σ) (delay : ℕ) (Q : State σ → Prop) (Pk : State σ → Prop)
    (R : State σ → State σ → Prop) (k : ℕ) (x y : State σ) : Prop :=
  ∃ g : ℕ → State σ, g 0 = x ∧ g k = y ∧ Trace F delay Q g k ∧
    (∀ i, i < k → R (g i) (g (i+1))) ∧ ∀ i, i ≤ k → Pk (g i)

namespace PackedRunR

theorem trans {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {R : State σ → State σ → Prop}
    {k₁ k₂ : ℕ} {x y z : State σ} (h₁ : PackedRunR F delay Q Pk R k₁ x y)
    (h₂ : PackedRunR F delay Q Pk R k₂ y z) : PackedRunR F delay Q Pk R (k₁ + k₂) x z := by
  obtain ⟨g₁, hg₁0, hg₁k, htr₁, hR₁, hp₁⟩ := h₁
  obtain ⟨g₂, hg₂0, hg₂k, htr₂, hR₂, hp₂⟩ := h₂
  have hj : g₁ k₁ = g₂ 0 := by rw [hg₁k, hg₂0]
  refine ⟨concat g₁ g₂ k₁, ?_, ?_, trace_concat htr₁ htr₂ hj, canon_concat hj hR₁ hR₂, ?_⟩
  · rw [concat_le g₁ g₂ (Nat.zero_le _)]; exact hg₁0
  · rw [concat_end g₁ g₂ hj]; exact hg₂k
  · intro i hi
    by_cases hie : i ≤ k₁
    · rw [concat_le g₁ g₂ hie]; exact hp₁ i hie
    · have hsplit : i = k₁ + (i - k₁) := by omega
      rw [hsplit, concat_end g₁ g₂ hj]
      exact hp₂ (i - k₁) (by omega)

theorem toPacked {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop}
    {R : State σ → State σ → Prop} {k : ℕ} {x y : State σ}
    (h : PackedRunR F delay Q Pk R k x y) : PackedRun F delay Q Pk k x y := by
  obtain ⟨g, h0, hk, htr, -, hp⟩ := h
  exact ⟨g, h0, hk, htr, hp⟩

theorem ofPacked {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop} {k : ℕ} {x y : State σ}
    (h : PackedRun F delay Q Pk k x y) : PackedRunR F delay Q Pk (fun _ _ => True) k x y := by
  obtain ⟨g, h0, hk, htr, hp⟩ := h
  exact ⟨g, h0, hk, htr, fun _ _ => trivial, hp⟩

theorem forget {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop}
    {R : State σ → State σ → Prop} {k : ℕ} {x y : State σ}
    (h : PackedRunR F delay Q Pk R k x y) : PackedRunR F delay Q Pk (fun _ _ => True) k x y := by
  obtain ⟨g, h0, hk, htr, -, hp⟩ := h
  exact ⟨g, h0, hk, htr, fun _ _ => trivial, hp⟩

theorem pack_last {F : Frame σ} {delay : ℕ} {Q Pk : State σ → Prop}
    {R : State σ → State σ → Prop} {k : ℕ} {x y : State σ}
    (h : PackedRunR F delay Q Pk R k x y) : Pk y := by
  obtain ⟨g, -, hk, -, -, hp⟩ := h
  rw [← hk]; exact hp k le_rfl

end PackedRunR

#print axioms stepsAllR_fn
#print axioms PackedRunR.trans


end PalPeg
