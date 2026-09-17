import PalPeg.CloseoutPackRun26

/-!
# `WatchShiftG` の監査 — まず正の帰結を機械検査する

`CLAUDE.md` は `hws`（`CloseoutPackRun26.WatchShiftG`）を「偽」と記録しているが、
`False` を導く定理は repo に存在しなかった（`lean-pal/REFUTATION_AUDIT.md` §3）。
`final27` は 5 前提で、そこから `hws` を外すために `final29`（9 前提）→ `final30`
（8 前提）に膨らんだ。したがって `hws` が成立するなら正本は 8 → 5 になる。

そこで**まず証明を試みる**。`WatchShiftG` の第 2 連言は

```
4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
```

で、比較の着地 `wch` が `ChainStep.backDone` 由来の場合、その control は
`GalilScaffoldTopChainVM.watchControl v = ⟨moveRight v, reset, reset, reset, 0, true, false⟩`
（`GalilScaffoldTopChainVM:46`）であり、`distance = reset`、`value reset = 0`。
よってその着地では `WatchShiftG` は `4 * periodLength wch ≤ 0`、すなわち
`periodLength wch = 0` を**強制する**。

ここまでは仮定ゼロの計算である。そして `periodLength` は `moveRight` 越しに
**常に正**：

* `moveRight t` は `t.right = []` なら `⟨t.focus :: t.left, .blank, []⟩`（長さ
  `t.left.length + 1`）、`t.right = a :: rs` なら `⟨t.focus :: t.left, a, rs⟩`（長さ
  `t.left.length + 1 + rs.length`）。どちらも `≥ 1`。

したがって `WatchShiftG` は `backDone` 着地で `0 < periodLength` と
`periodLength = 0` を同時に要求する。**この 2 つの正の定理が本ファイルの内容**で、
偽であるという結論はそこから読む側が引けばよい（第 3 の定理としても置く）。

未構成のまま残しているのは **「`.back` chain を持つ状態の比較が `backDone` に着地する」
という配置の存在**だけである。モデル上の唯一の側条件は `backDone` の guard
`isFirst v.focus = true`。それが実 run で到達可能かは本ファイルでは主張しない。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.CloseoutWatchShiftAudit

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.CloseoutPackRun26

/-- **正の定理 1.**  `backDone` で生まれた watch の周期長は常に正。
`moveRight` はどちらの枝でも `left` を 1 つ伸ばす。 -/
theorem periodLength_watchControl_pos (v : GalilScaffoldChainPeriod.Tape)
    (ver : PlaceHead) (lag margin : Counter) :
    0 < periodLength ⟨⟨ver, watchControl v⟩, lag, margin⟩ := by
  show 0 < (GalilScaffoldChainPeriod.moveRight v).left.length
      + (GalilScaffoldChainPeriod.moveRight v).right.length
  unfold GalilScaffoldChainPeriod.moveRight
  cases v.right with
  | nil => simp
  | cons a rs => simp

/-- **正の定理 2.**  `backDone` で生まれた watch の `distance` は `reset`、値は `0`。 -/
theorem value_distance_watchControl (v : GalilScaffoldChainPeriod.Tape)
    (ver : PlaceHead) (lag margin : Counter) :
    value (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
      GalilScaffoldChainWatch.State).machine.control.distance = 0 := by
  show value GalilScaffoldCounter.reset = 0
  simp [GalilScaffoldCounter.reset, value]

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **帰結**: `WatchShiftG` は `backDone` 着地で `periodLength = 0` を強制する。
正の定理 1 と矛盾するので、そのような配置が存在すれば `WatchShiftG` は偽。
未構成のまま置いているのは `hcmp`（その配置の存在）だけである。 -/
theorem watchShiftG_false_at_backDone {w : List (Fin 2)} {x : State GalilVM}
    {v : GalilScaffoldChainPeriod.Tape} {ver : PlaceHead} {lag margin : Counter}
    (hW : WatchShiftG centre place entry q first w x)
    (hsn : ScanNR x) (hni : x.vm.chain ≠ ChainVM.idle)
    (s'' : GalilVM)
    (hcmp : (galilFrameS (PofC centre place entry w) q first).compare x.vm s'')
    (hland : s''.chain = ChainVM.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩) :
    False := by
  obtain ⟨-, hdist, -⟩ := hW hsn hni s'' hcmp ⟨⟨ver, watchControl v⟩, lag, margin⟩ hland
  rw [value_distance_watchControl v ver lag margin] at hdist
  have hpos := periodLength_watchControl_pos v ver lag margin
  have : (1 : ℤ) ≤ (periodLength (⟨⟨ver, watchControl v⟩, lag, margin⟩ :
      GalilScaffoldChainWatch.State) : ℤ) := by exact_mod_cast hpos
  omega

end

#print axioms periodLength_watchControl_pos
#print axioms value_distance_watchControl
#print axioms watchShiftG_false_at_backDone

end PalPeg.CloseoutWatchShiftAudit
