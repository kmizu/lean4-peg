import PalPeg.GalilScaffoldControl

/-!
# `LocalBuffers`：非局所的な全テープ一括リセットの局所化

`GalilScaffoldControl.reset` は

```
def reset {n : ℕ} (entry : ℕ) (_x : Machine n) : Machine n :=
  ⟨⟨entry, fun _ => GalilScaffoldTape.reset⟩, true⟩
```

と、`n` 本のテープを**同時に**新品へ差し替える。実時間機械の 1 ステップは有限制御の
局所操作しか行えないので、この `fun _ => Tape.reset` はそのままでは実装できない。

本ファイルはその局所化（local refinement）を与える。物理的には各論理テープを
**2 本組** `A B : Fin n → Tape` として持ち、`active : Bool` がどちらが「本物」かを指す。
抽象テープは常に active 側（`abs`）。

* `resetL` — active を反転し（O(1)）、遊休側に消去ジョブ `job := some 0` を立てる。
* `clearTick` — 遊休側の**全テープで 1 セルずつ**（並列に）消去を進める。
* `stepL` — プログラムの 1 ステップを active 側の束にだけ作用させる。

正しさは 3 本の `abs` 補題（`abs_resetL_of_clean` / `abs_clearTick` / `abs_stepL`）と、
進行補題 `clearTick_done`（`c = 1`、すなわち `W + 1` ティックで遊休側は完全に空白）で
与える。両者を合わせた実用形が `abs_resetL_clearTickN`。
-/

set_option autoImplicit false

namespace PalPeg
namespace LocalBuffers

open PalPeg.GalilScaffoldTape (Tape)

/-! ## 1. 1 セルずつの消去 -/

/-- 消去ジョブの残り仕事量：フォーカス以外の既知セル数。 -/
def size (t : Tape) : ℕ := t.left.length + t.right.length

/-- **1 ティック分の消去**：まだ右文脈が残っていればその手前の 1 セルを捨て、
右文脈が尽きたら原点方向へ 1 セル戻りながらフォーカスを空白にする。
原点（`left = right = []`）ではフォーカスを空白化して新品テープになる。 -/
def clearStep (t : Tape) : Tape :=
  match t.right with
  | _ :: rs => ⟨t.left, t.focus, rs⟩
  | [] =>
    match t.left with
    | _ :: ls => ⟨ls, 6, []⟩
    | [] => GalilScaffoldTape.reset

/-- 「消去済み」＝新品テープと構造的に等しい。 -/
def Cleared (t : Tape) : Prop := t = GalilScaffoldTape.reset

theorem clearStep_reset : clearStep GalilScaffoldTape.reset = GalilScaffoldTape.reset := rfl

theorem size_reset : size GalilScaffoldTape.reset = 0 := rfl

/-- 1 ティックでちょうど 1 セル分だけ仕事が減る。 -/
theorem size_clearStep (t : Tape) : size (clearStep t) = size t - 1 := by
  rcases t with ⟨l, f, r⟩
  cases r with
  | cons a rs => simp [size, clearStep]
  | nil =>
    cases l with
    | cons a ls => simp [size, clearStep]
    | nil => simp [size, clearStep, GalilScaffoldTape.reset]

/-- 仕事が尽きたテープは次の 1 ティックで新品になる。 -/
theorem clearStep_of_size_zero {t : Tape} (h : size t = 0) : Cleared (clearStep t) := by
  rcases t with ⟨l, f, r⟩
  cases r with
  | cons a rs => simp [size] at h
  | nil =>
    cases l with
    | cons a ls => simp [size] at h
    | nil => rfl

/-- `m` ティック分の消去。 -/
def clearN : ℕ → Tape → Tape
  | 0, t => t
  | m + 1, t => clearN m (clearStep t)

theorem clearN_succ (m : ℕ) (t : Tape) : clearN (m + 1) t = clearN m (clearStep t) := rfl

/-- **進行（1 本のテープ）**：仕事量が `W` 以下なら `W + 1` ティックで新品になる。
すなわち定数は `c = 1`。 -/
theorem clearN_cleared (W : ℕ) (t : Tape) (h : size t ≤ W) : Cleared (clearN (W + 1) t) := by
  induction W generalizing t with
  | zero =>
    have h0 : size t = 0 := Nat.le_zero.mp h
    simpa [clearN] using clearStep_of_size_zero h0
  | succ W ih =>
    have hs : size (clearStep t) ≤ W := by
      have := size_clearStep t
      omega
    simpa [clearN_succ] using ih (clearStep t) hs

/-! ## 2. 2 本組バッファ -/

/-- 物理表現：2 本組 `A`/`B`、どちらが本物かを指す `active`、遊休側で走る消去ジョブ
`job`（`none` ならジョブなし、`some m` なら `m` ティック経過）。 -/
structure Buffered (n : ℕ) where
  A : Fin n → Tape
  B : Fin n → Tape
  active : Bool
  job : Option ℕ

variable {n : ℕ}

/-- 抽象テープ束＝ active 側。 -/
def abs (x : Buffered n) : Fin n → Tape :=
  match x.active with
  | true => x.A
  | false => x.B

/-- 遊休側（消去ジョブの対象）。 -/
def idle (x : Buffered n) : Fin n → Tape :=
  match x.active with
  | true => x.B
  | false => x.A

/-- **局所リセット**：active の反転とジョブ起動だけ。有限制御の O(1) 操作。 -/
def resetL (x : Buffered n) : Buffered n :=
  { x with active := !x.active, job := some 0 }

/-- **消去 1 ティック**：遊休側の全テープを並列に 1 セルずつ消す。 -/
def clearTick (x : Buffered n) : Buffered n :=
  match x.job with
  | none => x
  | some m =>
    match x.active with
    | true => { x with B := fun i => clearStep (x.B i), job := some (m + 1) }
    | false => { x with A := fun i => clearStep (x.A i), job := some (m + 1) }

/-- `m` ティック分の消去。 -/
def clearTickN : ℕ → Buffered n → Buffered n
  | 0, x => x
  | m + 1, x => clearTickN m (clearTick x)

/-- **プログラム 1 ステップの持ち上げ**：active 側の束にだけ作用させる。 -/
def stepL (f : (Fin n → Tape) → (Fin n → Tape)) (x : Buffered n) : Buffered n :=
  match x.active with
  | true => { x with A := f x.A }
  | false => { x with B := f x.B }

/-! ## 3. `abs` 補題 -/

theorem abs_resetL (x : Buffered n) : abs (resetL x) = idle x := by
  cases h : x.active <;> simp [abs, idle, resetL, h]

theorem idle_resetL (x : Buffered n) : idle (resetL x) = abs x := by
  cases h : x.active <;> simp [abs, idle, resetL, h]

/-- **The reset of the ghost state**: switch to the other half *as a fresh bundle*.  Its abstract
tapes are new whatever the idle half held, so no cleanliness is asked of the state.  On the
physical machine the old contents stay where they are and are never read again; that is carried by
the representation relation, not by an erasing deadline. -/
def resetFresh (x : Buffered n) : Buffered n :=
  match x.active with
  | true => { x with B := fun _ => GalilScaffoldTape.reset, active := false, job := some 0 }
  | false => { x with A := fun _ => GalilScaffoldTape.reset, active := true, job := some 0 }

theorem abs_resetFresh (x : Buffered n) :
    abs (resetFresh x) = fun _ => GalilScaffoldTape.reset := by
  cases h : x.active <;> simp [abs, resetFresh, h]

/-- **リセットの正しさ**：遊休側が消去済みなら、局所リセットは抽象レベルで
`GalilScaffoldControl.reset` の `fun _ => Tape.reset` とちょうど一致する。 -/
theorem abs_resetL_of_clean {x : Buffered n} (h : ∀ i, Cleared (idle x i)) :
    abs (resetL x) = fun _ => GalilScaffoldTape.reset := by
  rw [abs_resetL]; funext i; exact h i

/-- 抽象テープは消去ジョブの進行から影響を受けない。 -/
theorem abs_clearTick (x : Buffered n) : abs (clearTick x) = abs x := by
  cases hj : x.job <;> cases h : x.active <;> simp [abs, clearTick, hj, h]

theorem abs_clearTickN (m : ℕ) (x : Buffered n) : abs (clearTickN m x) = abs x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [clearTickN, ih, abs_clearTick]

theorem active_clearTick (x : Buffered n) : (clearTick x).active = x.active := by
  cases hj : x.job <;> cases h : x.active <;> simp [clearTick, hj, h]

theorem job_clearTick {x : Buffered n} (h : x.job.isSome) : (clearTick x).job.isSome := by
  cases hj : x.job with
  | none => rw [hj] at h; exact absurd h (by simp)
  | some m => cases ha : x.active <;> simp [clearTick, hj, ha]

/-- 遊休側はちょうど `clearStep` だけ進む（並列・全テープ）。 -/
theorem idle_clearTick {x : Buffered n} (h : x.job.isSome) :
    idle (clearTick x) = fun i => clearStep (idle x i) := by
  cases hj : x.job with
  | none => rw [hj] at h; exact absurd h (by simp)
  | some m => cases ha : x.active <;> simp [idle, clearTick, hj, ha]

theorem idle_clearTickN {x : Buffered n} (m : ℕ) (h : x.job.isSome) :
    idle (clearTickN m x) = fun i => clearN m (idle x i) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [clearTickN, ih (job_clearTick h), idle_clearTick h]
    funext i
    rw [clearN_succ]

/-- **プログラムステップの正しさ**：active 側への作用は抽象レベルでそのまま見える。 -/
theorem abs_stepL (f : (Fin n → Tape) → (Fin n → Tape)) (x : Buffered n) :
    abs (stepL f x) = f (abs x) := by
  cases h : x.active <;> simp [abs, stepL, h]

theorem idle_stepL (f : (Fin n → Tape) → (Fin n → Tape)) (x : Buffered n) :
    idle (stepL f x) = idle x := by
  cases h : x.active <;> simp [idle, stepL, h]

/-! ## 4. 進行補題と実用形 -/

/-- **進行（全テープ並列）**：遊休側の各テープの仕事量が `W` 以下なら、`W + 1` ティックで
遊休側は完全に空白になる。定数は `c = 1`。 -/
theorem clearTick_done {x : Buffered n} {W : ℕ} (hj : x.job.isSome)
    (hW : ∀ i, size (idle x i) ≤ W) :
    ∀ i, Cleared (idle (clearTickN (W + 1) x) i) := by
  intro i
  rw [idle_clearTickN (W + 1) hj]
  exact clearN_cleared W (idle x i) (hW i)

/-- **局所化の総合**：前回のリセットから `W + 1` ティック（各テープの仕事量上界 `W`）
だけ消去を進めていれば、次の局所リセットは O(1) で、抽象レベルでは非局所な
`fun _ => Tape.reset` と一致する。 -/
theorem abs_resetL_clearTickN {x : Buffered n} {W : ℕ} (hj : x.job.isSome)
    (hW : ∀ i, size (idle x i) ≤ W) :
    abs (resetL (clearTickN (W + 1) x)) = fun _ => GalilScaffoldTape.reset :=
  abs_resetL_of_clean (clearTick_done hj hW)

/-- 抽象側の対応物が本当に `GalilScaffoldControl.reset` のテープ束であること。 -/
theorem control_reset_tapes (entry : ℕ) (m : GalilScaffoldControl.Machine n) :
    (GalilScaffoldControl.reset entry m).config.tapes = fun _ => GalilScaffoldTape.reset := rfl

theorem abs_resetL_matches_control {x : Buffered n} {W : ℕ} (entry : ℕ)
    (m : GalilScaffoldControl.Machine n) (hj : x.job.isSome)
    (hW : ∀ i, size (idle x i) ≤ W) :
    abs (resetL (clearTickN (W + 1) x)) = (GalilScaffoldControl.reset entry m).config.tapes := by
  rw [abs_resetL_clearTickN hj hW, control_reset_tapes entry m]

#print axioms clearN_cleared
#print axioms abs_resetL_of_clean
#print axioms abs_clearTick
#print axioms abs_stepL
#print axioms clearTick_done
#print axioms abs_resetL_clearTickN
#print axioms abs_resetL_matches_control

end LocalBuffers
end PalPeg
