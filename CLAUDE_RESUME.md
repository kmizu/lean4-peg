## n331（2026-09-21）: `Computes` の場を順に埋める——レンズの引き戻しは補題 1 本、1 歩は 13 本、判定は 11 本

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リスト不変（義務 1 本）。リポジトリのコードは変えていない（スクラッチ検証のみ）。 |

**先に確かめたこと（作り直しを避けるため）**: `GalilSharedFunctional` に既に 3 つの関数形がある——`beginShiftFun` と `beginShiftFun_eq`（`shiftGuardVM s → beginShiftVM' s t → t = beginShiftFun s`）、`beginFallbackFun place` と `beginFallbackFun_eq`、`restartFun entry` と `restartFun_eq`。`Computes` の場そのものの形なので、そのまま使う。

**レンズの引き戻しは 1 本で済む（`$S/steps_fun.keep.lean`、EXIT=0・error 0）**: `Lens.rel R s t = R (get s) (get t) ∧ t = set s (get t)`（`GalilScaffoldTopLens:28`）なので、

**`lensRel_eq : (∀ v v', R v v' → v' = f v) → L.rel R s t → t = L.set s (f (L.get s))`**（公理ゼロ）。

下位 frame の関数性さえ出せば、`galilFrame` の各場はこれで上がる。

**1 歩の関数（13 本、すべて検査済み）**: `shiftOneFun`（chain の `.watch` が存在量化された `w` を固定）、`copyOneFun`（`Place.read walker` の `some a` が固定）、`copyEndFun`／`fppStartFun`／`homeStepFun`／`markBackFun`／`markForwardFun`／`chooseFun`／`fppResetFun`／`rewindOneFun`／`rewindPairFun`（どれも関係が `y = 式` かガード付きの `y = 式` なので、証明は `h` か `h.2`）、そして n329 の `fppSliceFun`／`fppDoneFun`。

**判定（11 本、すべて検査済み）**: n329 の `shiftGuardTest`／`restartGuardTest`／`canRightTest`／`onLetterTest`／`leftFirstTest` に加えて `matchedTest`／`shiftRemainingTest`／`copyRemainingTest`／`atLeftTest`／`atEndTest`／`markSetTest`／`atFirstTest`。

**残り**: `compare`（`compareFound`。`searchEffectFun`／`chainAtFun`／`backgroundFun` は検査済みなので組み立てるだけ）、`init`（`initVM` は 15 場を固定＝関数）、`replayStart`（`replayStartVM_unique` あり、関数はまだ）、`matchedPlace`（`galilFrame` の定義で既に関数形）。揃ったら `galilFrameFun` と `hcomputes` を作って投入する。

## n330（2026-09-21）: `Computes` の fallback 入口は目標だけでは決まらない（形式化の誤りを直した）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リスト不変（義務 1 本）、`unconditional` は付け替えていない。n329 で入れた `Computes` の場が 1 つ**証明不能な形**だったのを直した。 |

**状態: module build `PalPeg.ShadowedLocalFinal`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0、`forwardTick_of_machine` は標準公理・`tick_eq_tickFun` は `propext`／`Quot.sound`・無条件 PAL は未完。**

**何が間違っていたか**: n329 の `Computes F G t` は、frame が開いている 3 つの関係（`init`／`beginFallback`／`replayStart`）を「目標 `t` について」だけ要求していた。`init` と `replayStart` はそれで足りる——`initVM`（`GalilScaffoldTopReplay:20`）は `GalilVM` の 15 場すべてを等式で固定し、`replayStartVM_unique`（`ReplayStartGhost:224`）もある。**しかし `beginFallbackVM'` は違う。** `GalilSharedFunctional` には `beginFallbackVM'_not_unique` が**定理として**あり、同じ源から複数の目標に行ける（コピー元の place が自由）。目標を 1 つに決めるのは走行ではなく**方針** `GalilTickFair.Canonical.fallbackPlace`（`scan` から `copy` に着地したなら `y.vm.fpp.walker = rightPlace y.vm`）である。

**直し方**: `Computes F G Pin t` に方針の述語 `Pin : σ → Prop` を足し、`beginFallback : ∀ s, F.beginFallback s t → Pin t → t = G.beginFallback s` にした。`tick_eq_tickFun` は側条件 `hfallbackPinned : x.ctl.mode = scan → y.ctl.mode = copy → Pin y.vm` を取る。消費者 `forwardTick_of_machine` では `Pin s := s.fpp.walker = rightPlace s` を渡し、側条件は `hcanonical.fallbackPlace` そのもの。**`restartFirst` と `fallbackPlace` は `Canonical` の 3 場のうち 2 場で、どちらも「関係が複数の後継を許す所で方針が 1 つに決める」という同じ役目だった。**

## n329（2026-09-21）: 抽象 tick の関数形を投入し、物理側の前進義務を「1 本の関数を計算する」へ落とした

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リスト不変（義務 1 本）、`unconditional` は付け替えていない。`hforwardTick` の中身が「抽象関係の模倣」から「明示関数 `tickFun` の計算」へ落ちた。仮説の本数は同じ。 |

**状態: module build `PalPeg.ShadowedLocalFinal`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0、下の定理は標準公理のみ・無条件 PAL は未完。**（全体 build は n325 以降走らせていない。公理にも最終定理の経路にも触っていない。）

**新モジュール `PalPeg/TickFunction.lean`**（`ShadowedLocalFinal` → `Workbench` 経由で root の build 対象、`tick_eq_tickFun` は `propext`／`Quot.sound` のみ）:
* `FrameFun σ`: `Frame σ` の 33 個の関係・述語を関数と Bool 判定に置き換えたもの。
* `Computes F G t`: 関数が関係を計算する。frame が開いている 3 つ（`init`／`beginFallback`／`replayStart`）は**目標 `t` についてだけ**要求する（この 3 つは複数の後継を許す関係で、どれになるかは走行が決める）。
* `tickFun G F delay x`: モードで分岐し、`scan` では restart → 待機 → 計数 → 一致 → shift 入口 → fallback 入口 の順に Bool で分岐する。
* **`tick_eq_tickFun`**（24 構成子すべて）: `Computes F G y.vm` と `Tick F delay x y` と restart 優先の側条件から `y = tickFun G F delay x`。**関係に後継があるなら、それは関数の値である。**

**消費者へ繋いだ定理 `ShadowedLocalFinal.forwardTick_of_machine`**: `StarvedAbs`（`LocalSysConcrete.Starved` を抽象状態の上に書いたもの。`starvedAbs_absSC` は `Iff.rfl`）を使って、

```
(hstay : Enc x p → StarvedAbs x → Enc x (L0.apply p none))
(hstep : Enc x p → ¬ StarvedAbs x → Enc (tickFun (G w) (galilFrameS (PofC …) q first) 2048 x) (L0.apply p none))
⟹ hforwardTick の本体
```

restart 優先の側条件は `GalilTickFair.Canonical.restartFirst` から出す（`PofC` の `restart` 場は `restartVM entry` そのものなので、`Computes.restart` に定義どおり渡る）。側入力は `hcomputes`（関数が具体 frame を計算する）と `hguard`（`G.restartGuard` が立つなら `restartGuardVM`）。

**同日のスクラッチ（未投入、`$S/tests_fun.keep.lean`、EXIT=0・error 0・標準公理のみ）: frame の判定 5 個が Bool 関数になった。** `shiftGuardTest`／`restartGuardTest`（どちらも存在量化された watch 状態は chain の構成子が固定するので、`match s.chain` で計算できる）、`canRightTest`（`gap = false ∨ right ≠ [] ∨ incoming ≠ []`）、`onLetterTest`（右ヘッド位置が奇数かつ語の中。証人は `k = (位置+1)/2`）、`leftFirstTest`。どれも `… ↔ … = true`。**有限窓から読むもの**が具体的になった: chain のタグと watch の `lag`／`phase`／`broken`／`margin`／period テープの焦点記号、`periodOnly` と `cycle`、右ヘッドの gap・右スタック・incoming の空判定、左右ヘッドの位置。Lean の罠: `cases hchain : s.chain` は目標の `s.chain` を**すでに**置換するので、取り出した仮説に `rw [hchain]` は当たらない（`injection`／`rfl` を直接使う）。

**同日のスクラッチ 2（未投入、`$S/prog_run.keep.lean`、EXIT=0・error 0・標準公理のみ）: プログラム機械の走行が関数になった。** `executeFun`（1 命令。`read` は `cs.find?`、詰まれば不変）／`tickFun`（1 call）／`runFun`（call 列）と `run_eq_runFun : ReadFun code → Run code x bs y → y = runFun code bs x`（任意の code について）。`readFun_marked : ReadFun GalilFppMarkedCode.code`（`readFun_of_b (by decide)`、`maxRecDepth 40000` が要る）。これで fpp の場が埋まった: `fppHaltsTest q x := (fppRunFun q x.program).done`、`fppSliceFun`、`fppDoneFun`（`markNew`）と **`fppSlice_eq`／`fppDone_eq`**（`Computes` の `fppSlice`／`fppDone` 場そのものの形）。`fppSlice` と `fppDone` は同じ `q` 回走行の結果を `done` で分けているだけなので、判定 1 個と関数 2 個で足りる。

**残るのは `hcomputes` を埋めること。** `backgroundFun`／`searchEffectFun`／`chainAtFun`（`$S/scan_fun.keep.lean`、検査済み・未投入）が `background` の場を埋める。残りは `compare`（`compareFound`）、`matchedPlace`（`galilFrame` の定義で既に関数形）、shift／copy／home／markEnd／choose／rewind の各 1 歩、開いている 3 つの入口。

## n328（2026-09-21）: 物理機械は「後継を見つける」のではなく「渡された後継を計算して符号化する」

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リスト不変（義務 1 本）、`unconditional` は付け替えていない。消費者 `given_physicalMachine` の `hforwardTick` から**存在の証明義務が消えた**。仮説の本数は同じ。 |

**状態: module build `PalPeg.ShadowedLocalFinal`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0、`#print axioms given_physicalMachine` は標準 3 公理・無条件 PAL は未完。**（全体 build は n325 以降走らせていない。公理にも最終定理の経路にも触っていない。）

**何を直したか（消費者の型を上から読んで分かったこと）**: 旧 `hforwardTick` は `∃ successor, Enc successor (L0.apply p none) ∧ TickSucc … (absSC m) successor` を要求していた。つまり物理機械に「抽象 tick の後継が存在すること」まで証明させていた。ところが消費者の使用箇所では、その後継 `hsucc` は**既に引数として手元にある**（走行の状態なので trace か `plateauStep` が出している）。新しい形は

```
∀ m p successor, OnRun … m → ¬ frozenAt w m → Enc (absSC m) p →
  TickSucc (PofC …) q first 2048 (Canonical entry 2048) (Starved m.vm) (absSC m) successor →
  Enc successor (L0.apply blankSymbol p none)
```

で、機械の仕事は「渡された（一意な）後継を計算して符号化する」だけになった。`tickSucc_unique` は最後の読み手を失ったので、代わりに使う `tickSucc_congr_starved`（飢餓判定を同値なものに置き換える）に差し替えて削除。

**この形が効く理由（スクラッチ `$S/tick_fun.keep.lean`、EXIT=0・error 0・公理 `propext`／`Quot.sound`）**: 抽象 tick を状態の関数にする定理が通った。`FrameFun σ`（`Frame` の 33 個の関係・述語を関数と Bool 判定にしたもの）、`Computes F G t`（「関数が関係を計算する」。frame が開いている 3 つ——`init`／`beginFallback`／`replayStart`——は目標 `t` についてだけ要求）、`tickFun G F delay x`（モードで分岐し、scan では restart → 待機 → 計数 → 一致 → shift 入口 → fallback 入口 の順に Bool で分岐）、そして

**`tick_eq_tickFun : Computes F G y.vm → Tick F delay x y → (x.ctl.mode = scan → G.restartGuard x.vm → y = ⟨{x.ctl with clock := delay}, G.restart x.vm⟩) → y = tickFun G F delay x`**（24 構成子すべて）。

restart 優先の側条件は `GalilTickFair.Canonical.restartFirst` そのもの。つまり「trace が後継の存在を出し、機械が `tickFun` を計算し、`Canonical` と決定性が両者の一致を出す」という分担になる。

**投入していない理由**: `tickFun` はまだ読み手が無い（参照ゼロの宣言を作らない）。次に `Computes` を具体 frame `galilFrameS (PofC …)` について埋め（`searchEffectFun`／`chainAtFun`／`backgroundFun` は `$S/scan_fun.keep.lean` で検査済み、残りは compare と入口 2 つ）、`hforwardTick` を「機械が `tickFun` を計算する」へ落とす定理と一緒に投入する。

## n327（2026-09-21）: 点検 — 物理機械の山は「view の機械」ではなく「scan の計算できる局所 step」（調査のみ、コードは変えていない）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リスト不変（義務 1 本）、`unconditional` は付け替えていない。 |

**状態: 全体 build 成功（最新の全体 build は n325 の `BUILD=0`。n326 は module build のみ）・標準公理のみ・無条件 PAL は未完。**

**なぜ点検したか**: n326 で view の機械（融合 slot、blank からの初歩、`HeadRep`）は通ったが、2 回続けて消費者 `given_physicalMachine` の仮説は 1 本も埋まっていない。部品を積む前に義務と一次情報を読み直した。

**一次情報で確かめたこと**:
* 義務 `H_realizeCanonical`（`CloseoutFinalW:113`）は「**w に依らない 1 台**の `LocalStep` 機械があり、全ての非空 `w` と `PreTraceIMW`／`CanonTrace` な trace について `SAccepts w ↔ LatchTrue …`」。機械は抽象 tick を 1 歩ずつ追う必要は無いが、実時間で PAL を認識する計算そのものは要る（近道は無い）。
* 正本 Scala の `alias(target, source)`（`ScaffoldSearch.scala:32`）は `copyFrom`＝永続スタックのポインタ複製で O(1)。呼び出しは 9 箇所: chain 誕生の `lag := radius`・`margin := radius`（`ScaffoldChain:91–92`）、`last := boundary`・`boundary := distance`（`:145–146`）、`remaining := chain.h`（`ScaffoldGalil:303`）、`remaining := length`（`:315`）、`replay := radius`（`:427`）、探索の `lower／work := lowerBound`（`ScaffoldSearch:106–107`）、`work := lower`（`:134`）、`work := span`（`:144`, `:200`）。Lean の抽象 `Tick` も値のコピーとして写している（`beginShiftVM`: `remaining := ofNat h`、`restartVM`: `lower := last`・`search := begin last radius` など）。n304 の head コピーと同じ機械モデルの差（ポインタ機械 vs 実時間多テープ TM）。
* 局所層はこれを eager mirroring で解いている（`LocalMirror`: `take` は制御だけの操作、切り離した鏡の再構築は 1 tick 1 mark で犠牲の複製を消費）。締切は純算術で切り出し済み（`LocalBudget`／`LocalSchedule`: 場所クロック `delay = 2048`、2048 tick の窓で `radius` は高々 1 回しか変わらない、head の再配置だけは歩いて間に合わない → parked view）。
* しかし scan の局所 step は**計算できる形では存在しない**: 消費者の scan／replayStart／plateau の後継は `chosenStep`（`Classical.choice` で選んだ ghost）。`LocalTick1.TickL1`（`:777`）は関係で、wait／count／match のどの構成子も探索量子の局所後継の存在 `SearchLocal S b x z` と、**抽象のままの** `ChainVM` 上の `chainAt` を仮説に取る（`GalilVML.chain` は「still abstract」）。mismatch（shift 入口・fallback 入口）と restart の局所構成子は無い。
* よって物理機械が自前で持つべきものは: (i) 計算できる局所状態 `X`（`GalilVML` の view・カウンタ bank・鏡・buffer に、局所 chain `LocalChain.ChainL` を加えたもの）と抽象化 `absX : X → State GalilVM`、各モードの**関数としての**局所 step とその `Tick ∧ Canonical` への simulation、(ii) `X` とテープの対応（各成分は stack テープと queue なので n326 の機械と同じ部品）。n326 で `Enc` を `State GalilVM` の上に切り直したので、`X` は `Mirrored1` と一致しなくてよい。

**追記（同日、定義と grep で確認）: `SearchLocal` に producer は 1 つも無い。** `LocalTick1.SearchLocal S a x z`（`:262`）は 4 場の構造（`steps : StepLocalN searchSteps x z`、`frame : SearchFrame x z`、`inv`、`effect : searchEffect S a (abs' x) (searchLens.get (abs' z))`）で、出現は `LocalTick1` と `LocalReplayParked` の**仮説としてだけ**。`dpStep`／`dpRun`（DP 束への点ごとの `LocalBuffers.stepL`、`abs_dpStep`）は「64 個の局所 step で書ける」ことの証人で、docstring 自身が「その 64 個の関数が `SafeQuanta` を計算することは `SearchLocal.effect` に残した gap」と書いている。探索の各 mode（grow／lower／lowerHome／copy／home＝`PrepareControl.Tick`、run＝`SafeQuanta`、wait／double）を**状態から計算する関数**は無い。ghost 方式（n316）はこの穴を迂回していただけで、物理機械では最初に埋めるもの。

**スクラッチ（未投入、`$S/run_fun.keep.lean`、EXIT=0・標準 3 公理、どれも一発）: run 量子の関数形。** 抽象のプログラム機械 `GalilScaffoldControl.Tick` は関係で、詰まる場合（左端での左移動、`read` の表に無い記号）には後継が無い。関数形を書いた: `executeFun`（1 命令。`read` は `cs.find?`、詰まれば不変）、`tickFun code enabled x`（1 call）、`callsFun`（`finish` つきの call 列）、`quantumFun a s x`（64 call＋`advance a`）。定理は「関係の後継があれば関数の値に一致する」の向き: `execute_eq_executeFun`／`tick_eq_tickFun`（`ReadFun code` を使う）、`safeCalls_eq_callsFun`、**`safeQuanta_eq_quantumFun : SafeQuanta s x [a] t y → (t, y) = quantumFun a s x`**（`GalilTickFair.readFun_code`）。存在は trace から来て、関数は機械が計算し、等式は決定性から出る、という producer の形に合う。
* `finish`（`GalilScaffoldSearchFinish:21`）は run の完了時に `work := span`・`span := reset`・`quarter := 0` をする。コピーではなく**移動**（直後に source を reset）なので、局所側は `span`／`work` の役割と極性の交換＋新しい `span` テープへの `resetSeg` 1 回（`LocalCounter` の segmented unary は reset が 1 action）で済む見込み。局所層に `finish` の対応物は無い（grep で確認）。

**スクラッチ続き（未投入、`$S/search_fun.keep.lean`＝`run_fun` を含む 1 本、EXIT=0・標準 3 公理）: 探索の効果が丸ごと状態の関数になった。** `GalilScaffoldPrepareControl.tickFun`（prepare 系 9 構成子。guard は互いに排他なので `match mode`＋`if`）と `tick_eq_tickFun : Tick true x y → y = tickFun x`、`searchStepFun center a v`（全 11 mode: 不変 3、grow／double は `if positive work`、prepare 4 mode は `tickFun`、run は `quantumFun`、wait は `waitStep`）と **`searchStep_eq_searchStepFun : searchStep center a v v' → v' = searchStepFun center a v`**、`searchEffectFun P a s`（chain が idle なら `searchStepFun (P.place s) …`、そうでなければ探索不変）と **`searchEffect_eq_searchEffectFun`**。向きはどれも「関係の後継があれば関数の値に一致」。物理機械（と、間に局所層を挟む場合はその局所 step）が計算すべき探索部分の仕様関数がこれで 1 本に定まった。各枝の 1 歩は DP テープ 1 本への 1 action（`moveRight (write t s)`／`moveLeft`／`write`）＋カウンタの inc／dec＋walker の `Place.left` で、非局所なのは `finish` の `work := span`（移動）と `prepare`／`enter` の `work := lower`／`work := span`（コピー）。
* Lean の罠: `{x with a := …,` の後で改行して次の場を浅い字下げで書くと構文エラー（1 行に書く）。token-saver の hook は bash コマンド中の単語 `watch` を弾くので、その単語を含むパッチは Write でファイルにしてから当てる。

**スクラッチ続き 2（未投入、`$S/scan_fun.keep.lean`＝探索と chain を含む 1 本・408 行、EXIT=0・標準 3 公理）: scan の background tick が丸ごと状態の関数になった。** chain 側: `watchVerdict w : Option Bool`（period の記号と、1 つ進めた verifier の下の入力の一致。`Good`／`WatchBreak`／`BreakStep` の判定を 1 つの計算にしたもの）、`chainStepFun`（copy は `t.focus = 8`／`= 4` で分岐、back は `isFirst`、観察中の chain は `positive lag` と verdict で `caught`／broken／不変）、`chainMatchedFun`（`zero lag` と verdict で `immediate`／broken／`queued`）、`chainTickFun`、`chainAtFun`（idle かつ found なら `chainStart`）と、それぞれの「関係の後継があれば関数の値に一致」（`chainStep_eq_chainStepFun`／`chainMatched_eq_chainMatchedFun`／`chainTick_eq_chainTickFun`／`chainAt_eq_chainAtFun`）。まとめ: **`backgroundFun P s`** と **`backgroundS_eq_backgroundFun : backgroundS P q first s s' → s' = backgroundFun P s`**。`Tick.scan_wait`／`scan_count` の着地 VM はこの関数の値（制御は clock だけ）。
* `chainStart` は `lag := radius`・`margin := radius`（コピー 2 本）、`copyBit` は DP テープ 11（`answer`）を左へ読みながら `h` を inc・period テープへ `put`・`decFour margin`、walker は `Place.left`。どれも 1 歩あたり有界個の action。

**次の一手（変える）**: view の機械を広げるのをやめ、(i) のいちばん危ない 1 点を機械検査する — `scan_wait`（head もカウンタも動かさず、探索量子 1 個と chain 1 歩だけ）について、探索量子の局所後継を**関数として**書けるか。関数 `searchStepL : Bool → GalilVML P → GalilVML P` を mode ごとに書き、`SearchLocal S a x (searchStepL a x)` を示す。**（上のスクラッチで抽象側の仕様関数 `backgroundFun` まで出来た。）** 次は compare 側（`compareFound`: `afterCompare`／`afterMismatch`、入口 `beginShiftVM'`／`beginFallbackVM'` は Canonical で場所が決まる）を同じ向きで関数にし、scan の tick 全体を `scanTickFun` にまとめる。そのうえで、この関数を計算する機械（まず background: DP テープ・period テープ・カウンタ 5 本・verifier の view）の Rep 保存と一緒にリポジトリへ投入する。

## n326（2026-09-21）: 物理機械の仮説を抽象状態の上に切り直した（`Enc : State GalilVM → 物理配置 → Prop`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リストは不変（義務 1 本）、`unconditional` は付け替えていない。消費者 `ShadowedLocalFinal.given_physicalMachine` の物理側仮説の**形**を弱めただけで、仮説の本数は同じ。 |

**状態: 全体 build 成功（n325 の `BUILD=0` 以降は module build のみ: `PalPeg.ShadowedLocalFinal`・`PalPeg.Workbench` とも `BUILD=0`、error 0、sorry 0）・標準公理のみ（`#print axioms given_physicalMachine` = 標準 3 本）・無条件 PAL は未完。**

**何を変えたか（形式化の点検）**: 旧形は `Enc : Mirrored1 → 物理配置 → Prop` で、`hforwardTick` は「`Enc next p'` な `next : Mirrored1` を物理側が作れ」と要求していた。消費者の証明が `encoded` から読むのは `absSC encoded`（と、その関数である `Starved`・`ctl.output`）だけだったので、これは余計な縛り: 物理配置が `Mirrored1` の役割・極性・bank 配置の witness を毎歩作らされる。任意の抽象状態に `Mirrored1` の切断は無い（`ghostOf` は canonical counter・駐車形を要る）ので、`Enc := R ∘ absSC` という素直な定義では旧形を満たせなかった。
新形: `Enc : State GalilVM → Q × (Fin t → STape Γ) → Prop`（handoff §4.2 の `Rep`）。`hforwardTick : OnRun m → ¬frozenAt w m → Enc (absSC m) p → ∃ successor, Enc successor (L0.apply p none) ∧ TickSucc … (Starved m.vm) (absSC m) successor`、`hforwardFeed : InvC m → Enc (absSC m) p → Enc (absSC (feedC letter m)) (L0.apply p (some letter))`。後継の同定は既存の `tickSucc_unique` が消費者の中でやる。局所層 `m` は「run 上にいる」ことの運び手としてだけ残る。参照ゼロになった `starved_of_absSC_eq` は削除。

**n326 続き（表現の margin を規則の半径から切り離した。その場で一般化、変種なし）**: 消費者は「物理 1 歩＝抽象 tick 1 回／`feedC` 1 回」を要求するので、11 微小歩の slot は `LocalStepFusion.compStep_iterRule` で 1 歩に融合する。融合した規則の半径は `11·K` で、`compStep_iterRule` は全テープに `11·K ≤ pos` を要るが、`QueueRep K`／`MicroRep K`／`ViewRep K` は底の高さを規則の半径と同じ `K` でしか保証していなかった。表現の引数を margin として読み替え、`queueRule_sound`／`microRule_sound`／`microRun_sound`／`snocRun_sound`／`tailRun_sound`／`programRun_snoc`／`programRun_tail`／`idleRun_sound`／`slotTailRun_sound`／`viewMargin`／`viewDecisionStep`／`viewDecision_sound`／`viewTopsOfWindows_eq`／`viewSlot_sound`／`machineSlot` に `{margin} (hmarginLe : K ≤ margin)` を通した（結論は `Rep margin`）。`microRep_empty_of_seals`／`viewRep_empty_of_seals` は高さ `margin` の seal で述べ直した。未融合の init 経路（`programInit`／`viewInit_of_apply`／`machineInit`／`machineFirstLetter`）は `margin := K` のまま。module build `PalPeg.ConcreteLocalMachine`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0。**公理への接続は無い。進捗として数えない。**

**スクラッチ（未投入、消費者と一緒に入れる）**: `$S/blank_start.keep.lean` の `compStep_apply_blankEdge`: 全 blank・左端からの `compStep R` の 1 歩は、margin 無しで「head が `K` に立つ blank テープに `R.acts` を当てたもの」と `TEqG`。`inp w 0 = w[0]?` なので最初の物理 1 歩がいきなり feed で、`compStep_apply` の margin 前提が初歩に使えないことへの対処。融合機械では初期化の微小歩が要らなくなる（高さ `11·K` の seal は `viewRep_empty_of_seals` で空 view の表現）。

**時間モデルの不整合（未修正）**: `machineRule` は入力を `pending` に latch して次の slot で配る（1 slot 遅れ）。融合 1 歩＝`feedC` ちょうどにするには command を `commandOfLetter input`（その微小歩の入力）から取る。`viewSlot_sound` は step 0 の command しか読まないので、後の微小歩の command は自由。

**n326 続き 2（融合した slot。時間モデルの不整合を直した。公理への接続は無い・進捗として数えない）**: module build `PalPeg.ConcreteLocalMachine`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0、下の定理は標準 3 公理のみ。
* `LocalViewsMachine` を書き直した（441 → 271 行）。制御は `slot × 各 view の制御` だけ（`started`／`current`／`pending`／`latch` は消えた）。`machineRule` の command は**その微小歩の入力** `commandOfLetter input`。動かす機械は融合 `compStep (iterRule (machineRule …) 11)` で、実 1 歩＝1 slot、入力は slot の微小歩 0 に届く。これで「feed 1 歩＝全 view に `arrive a` ちょうど」になり、1 slot 遅れが消えた。
* `machineSlot_of_ideal`: ideal な 11 微小歩（`LocalStepFusion.idealRun`＝入力は最初の歩だけ、`idealIter_eq_idealRun`）と制御が一致しテープが `TEqG` な状態は、全 view が `viewApply (commandOfLetter input)` 後の `ViewRep margin`・未払い 0・slot 0。`machineSlot`: margin `iterRadius K 11 ≤ margin` の表現から実 1 歩（`compStep_iterRule`、各テープの margin は新しい `ViewRep.margin_le_pos`）。
* `machineFirstSlot`: **blank テープ・左端からの最初の実 1 歩は初期化の歩なしで 1 slot**。`LocalQueueInit.compStep_apply_blankEdge`（スクラッチから投入: 左端の blank からの sweep は head が半径に立つ blank からの sweep と `TEqG`、`sweep_blank_edge_shifted`）＋高さ `iterRadius K 11` の seal は空 view の表現（`viewRep_empty_of_seals`）。`hencInit`＋最初の `hforwardFeed` の view 成分の中身に当たる。
* 片付け: 未融合の init 経路（`sweep_blank_edge`／`programRule_acts_idle`／`currentOp_initControl`／`programInit`／`viewActs_init`／`viewNext_init`／`viewInit_of_apply`／旧 `machineInit`／`machineFirstLetter`／`machineIter*`／`registersAfter`／`latch`）は読む者がいなくなったので削除。

**n326 続き 3（消費者の `hforwardFeed` から局所層の `feedC` を消した）**: module build `PalPeg.ShadowedLocalFinal`・`PalPeg.Workbench` とも `BUILD=0`・error 0・sorry 0。`hforwardFeed` の結論は `Enc (GalilArriveChain.arriveState' letter (absSC m)) (L0.apply p (some letter))`。消費者の中で既存の `LocalSysConcrete.feed_abs_core`（`absState'' (feedC a m).vm = arriveState' a (absState'' m.vm)`、`ViewsWF`＋`pending = []` は `InvC` から）で戻す。`arriveState'` は抽象の 3 本の head（left／center／right）と chain の verifier の `incoming` に 1 文字足すだけ（`LocalTracking.arriveVM`／`GalilArriveChain.arriveChain`）。これで物理側の 2 本の前進仮説はどちらも抽象状態だけで述べられている。仮説の本数・公理リストは不変。

**n326 続き 4（`Enc` の head 成分。公理への接続は無い・進捗として数えない）**: 新モジュール `PalPeg/LocalHeadRep.lean`（`ConcreteLocalMachine` → `Workbench` 経由で登録、module build `BUILD=0`・error 0・sorry 0、標準 3 公理）。`HeadRep margin head state := ∃ v first, WF v ∧ ViewCells v ∧ absHead' v [] = head ∧ ViewRep margin v … ∧ 未払い 0`（抽象の `PlaceHead` は、view の 12 テープが表す整形式な view の抽象。届いていない文字は誰の `incoming` にも無いので pending は空）。`headRep_machineSlot`: 融合機械の実 1 歩は全 head に `headAfter input`（`some a` なら抽象の到着 `GalilTickArrive.arrivePH a`、`none` なら不変）。`headRep_machineFirstSlot`: blank テープからの最初の実 1 歩は空 view の head への到着。`arriveState'` が head にすること（`arriveVM_eq`）とちょうど同じ形。**まだ無いもの**: chain の verifier の head（`arriveChain`）、replay 中の right（`left^[r] parked`）、head 以外の全成分、tick の全分岐。

**次**: 同じ物理配置（`LocalViewsMachine.machineRule`、view 1 本 = 12 テープ）の上で、command を制御（モード）と窓から決める形に広げる（tick の 1 歩＝各 view に `stepRight`／`stepLeft`／`stay`）。抽象 head と `InputView` の対応（`absHead'`、`feedC` が view にすること）を一次情報で確認して `Enc` の head 成分を定義する。n304 の 3 義務（P1〜P3）は未着手。

## n325（2026-09-21）: 最後の報告点の後の tick にも局所後継ができた。抽象局所層への仮説はゼロ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リストは不変（義務 1 本）、`unconditional` は付け替えていない。局所経路の消費者（`ShadowedLocalFinal.given_physicalMachine`、旧名 `given_openModesAndPhysicalMachine`）から `hplateauNext` が消え、**抽象局所層に対する存在仮説は無くなった**。残っているのは物理機械の仮説（`htape`／`Enc`／`hencInit`／`hforwardTick`／`hforwardFeed`／`hencRep`／`hencOut`／`PhysFrozen`／`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`）と、供給できる側条件（`hfirst`／`hq`／`hor`／`hres`／`hChainVerifierSupply`、今回足した `0 < q`／`first ≠ 7`／`first ≠ 8`。実例 `0 1 0` では成立）。ActRule は未着手。 |

**状態: 全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。**

**何を証明したか**: 最後の文字の後、その文字の窓が終わるまで局所層は tick し続けるが、trace は最後の報告点で止まる。その先の抽象 tick は**存在**を示さないと ghost が止まって物理機械との対応が切れる。
* 新モジュール `PlateauInvariant`: `PlateauInv w x`（1 tick で閉じた不変量: scan、非 replay、`1 ≤ clock`、`¬restartGuardVM`、`position right = 2|w|−1`、`MInv`、`SoundScanNR`、`InvLPS` の origin からの `StepsIMWC`／`ShapedSteps`、切断の事実 `AllCanonical`／`ChainLastCan`／`replay = reset`／`SpanRep`／`0 ≤ radius`）、`plateauStep`（`∃ y, Tick ∧ Canonical ∧ (PlateauInv y ∨ 2|w| ≤ position y.right)`）、`plateauCompare`、`replayReset_of_plateauTick`。count tick は `backgroundS_exists`＋`Tick.scan_count`（`OracleRun.scanBackground_run_all` の帰納段と同じ組み方、`restartGuard_background` で guard が無いまま）、compare は `scanCompare_cases`、fallback の canonical な着地は `CanonicalFallbackInput.begin_at_mismatch`。**oracle の readiness の葉は `m := |w|`、`hmle := le_rfl` で最後の報告点にもそのまま当てはまる**（境界は `position ≤ 2m−1` と `position+1 < |encoded w|`、等号で通る）。
* `ShadowedLocalFinal`: `postPhase := PlateauInv … (absSC m) ∨ frozenAt w m`。`plateauInv_of_lastReport`（入口。n324 の 4 番目の連言＝各 checkpoint での oracle の不変量と、trace の事実 `countersCanonical_trace`／`FrontPack.rest`／`spanRepOnScanAndShift_alongTrace`／`radLedger_pt`）、`plateauNext`（`nextOK_ghostOf` に `r = 0`・`parked := y.vm.right`。plateau では `replay = reset` が保たれるので駐車形は自明）、`plateau_of_nextOK`（`chosenStep` の抽象は `GalilTickFair.tick_canonical_unique` で一致）。`given_shadowedLocalSystem` の `hpostOfLastReport` は oracle の不変量を受け取る。
* 片付け: `ReportPhase` は読む者がいなくなったのでモジュールごと削除（`position_right_of_atLast` は `PlateauInvariant` へ移動）。消費者の名前を実態に合わせて `given_physicalMachine` に変えた。
* 進め方: 同じ goal で 2 回接続ゼロが続いた時点で、設計を足すのをやめて「いちばん危ない 1 点」（葉の量化範囲が最後の報告点に届くか）をスクラッチで機械検査した。そこから 5 定理が全部一発で通った。

**投入時に残したコピペ（次に片付ける）**: `plateauCompare`／`plateauStep` の前置き（pack、`rightHead_of_packs`、`canRight_of_bound`）と chain の readiness の導出は `OracleRun.scanCycle_of_leaves`／`OracleReady.cycleOracleOn_of_readyLeaves` の中の `have` と同じ形。名前付き補題に切り出して両方から使う。

**次**: 物理機械。`Enc`・`PhysFrozen` の具体化と ActRule の分岐（`ActRule → compStep → LocalStep.realize`）。n304 の 3 義務（P1: L／C テープが fallback 相で R まで歩く、P2: reset 後の junk を読まない、P3: replayStart の鏡テープの役割交代）。

## n324（2026-09-21）: oracle の不変量を全 checkpoint で外に出した（plateau の run の材料）

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残。抽象局所層の仮説は `hplateauNext` だけ（まだ仮説のまま）。今回はその証明に要る材料を消費者の手元まで運んだだけ。物理機械の仮説と ActRule は未着手。 |

**なぜ要ったか**: plateau（最後の報告点の後、右ヘッドが `2n` に出るまで）には trace が無く、抽象 tick の**存在**が要る。部品は `OracleRun` に既にある（`settle`、`scanBackground_run`、`scanCompare_cases`、存在は `scan_tick_exists_PofC`）が、どれも oracle の不変量 `ScanOnPackedRunFromInvLPS`（`InvLPS` の origin と packed／shaped な run を運ぶ）を起点に取る。readiness の葉は n282 で全部放電済みで、chain の葉の条件 `position right + 1 < |encoded w| = 2n+1` は最後の報告点 `2n−1` でも成り立つ。ところが `canonicalPreTrace_exists` は `PreTraceIMW`・`CanonTrace`・checkpoint の scan モードしか外に出しておらず、`ReachAtOn` の継続節は `m < |w|` のときしか不変量を出さない（当時の消費者は次の目標へ進むだけで、最後の点の不変量を必要としなかった）。
* 調べたこと: `ReachAtOn` の producer は `OracleRun` の 3 箇所だけで、どれも報告状態の不変量 `hI'` が手元にある。`ShapedSteps` は 1 歩ごとに restart の証明書（`Restarted`／`StageEntry`）を運ぶので、外に出ている事実からの再構成は重い。
* やったこと: `ReachAtOn` の構造は変えず、報告点で外に出す述語 `Y` を強めた。`CloseoutCheckW.ReportOnPackedRun w y := y.ctl.mode = scan ∧ ScanOnPackedRunFromInvLPS w y.ctl y.vm`。6 ファイル 11 箇所の literal `(fun _ y => y.ctl.mode = Mode.scan)` をこの名前に置換、producer 3 箇所は `⟨hI'.1.1, hI'⟩`。`preTraceOnPackedRun_exists` と `canonicalPreTrace_exists` の結論に 4 番目の連言「各 checkpoint で `ScanOnPackedRunFromInvLPS`」を追加（3 番目の scan モードは残した）。
* **1 回目の全体 build は `BUILD=1`**（背景タスクの通知は exit code 0 だった。ログの `BUILD=` 行で気づいた）。`given_shadowedLocalSystem` の `hexists` が存在定理の結論を 3 連言の形で書き下していた。4 連言に直して `BUILD=0`。

**plateau: 機械検査済みの部品と、改めた設計（2026-09-21 夕、スクラッチ `$S/plateau_bg.keep.lean`、`EXIT=0`、標準 3 公理、未投入）**:
* 検査済み: `plateauBackground`（`ScanOnPackedRunFromInvLPS` ∧ `position right = 2|w|−1` から `clock−1` 回の count tick の `OracleTick` な run、ヘッドと `replay` 不変、着地は clock = 1・`¬restartGuard`・`canRight`、origin からの `StepsIMWC`／`ShapedSteps` つき）、`plateauCompare`（clock = 1 から `∃ y, Tick ∧ Canonical ∧ y.vm.right = right t.right`。matched／shift は `canonical_of_scan_nonCopy`、fallback は `scanCompare_cases` の「place を選べる形」に `CanonicalFallbackInput.begin_at_mismatch` の `rightPlace` の着地を渡す）、`plateauRun`（両方をつないで `position y.vm.right = 2|w|`）。**oracle の readiness の葉は `m := |w|`、`hmle := le_rfl` で最後の報告点にも当てはまる**（境界は `position ≤ 2m−1` と `position+1 < 2n+1`、等号で通る）。
* **改めた設計（下の「定理の形」より優先）**: run の関数を `Post` に持たせず、**1 tick で閉じた不変量**にする。`OracleRun.scanBackground_run_all` の帰納段（`:143–185`）が 1 歩を明示的に組んでいる: `backgroundS_exists` ＋ `Tick.scan_count`、`ShapedRun.restartGuard_background`（guard の無い状態は background の後も無い）、`outputRel_background`、`not_restartVM_background`、`oracleTick_of_noGuard (canonical_of_scan_nonCopy …)`。
  - `PlateauInv w x`: scan、非 replay、`1 ≤ clock`、`¬restartGuardVM`、`position right = 2|w|−1`、`MInv`、`SoundScanNR`、`∃ c₀ r₀ k kS, InvLPS ∧ StepsIMWC k … x ∧ ShapedSteps kS … x`、切断の事実（`AllCanonical`、`ChainLastCan`、`replay = reset`、`SpanRep`、`0 ≤ value radius`）。
  - 1 歩: `clock = 1` なら `plateauCompare`（着地は `2|w|` で `frozenAt`）、`clock > 1` なら count tick 1 回で `PlateauInv` に戻る（run の延長は `packRunR_MWR_marksFree` に `StepsAllR 1` を渡す）。
  - 切断: plateau では `replay = reset` が保たれるので駐車形は自明（`r = 0`、`parked := target.right`。`RightReplayMove` の `replayed`／`started` は非 replay・scan で起きない）。`AllCanonical`／`ChainLastCan` は `allCanonical_tick`／`chainLastCan_vmTick`（追加前提なしの tick 単位補題）、入口の符号は `entrySigns_of_scanTick`。後継は `nextOK_ghostOf`。
  - `Post w m := PlateauInv w (absSC m) ∨ frozenAt w m`。消費箇所（`:1188` 付近）の `Post (chosenStep m)` は、`chosenStep` の抽象が canonical な tick の target なので `GalilTickFair.tick_canonical_unique` で上の `y` と一致させる。入口 `hpostOfLastReport` は trace の事実（n324 の 4 番目の連言、`countersCanonical_trace`、`FrontPack.rest`、`spanRepOnScanAndShift_alongTrace`、`radLedger_pt`）。
  - この設計では `ReportPhase.reportPhase_tick` を読む者がいなくなる。投入時に確かめて、読む者がいなければモジュールごと消す。
  - 投入時のコピペ回避: `plateauBackground` の前置き（不変量の分解、pack、clock の上下界、`canRight`）と `scanCycle_of_leaves` の前置きを補題に切り出して共有する。chain の葉の証明は `OracleReady` の中の `have` を名前付き定理に切り出す。

**plateau の定理の形（n324 の最初の版。上の設計に置き換わった）**:
* `Post` は `List (Fin 2) → Mirrored1 → Prop` で trace を引数に取れない（`given_shadowedLocalSystem:433`）。なので `Post w m` は「`absSC m` は、ある canonical な plateau run の上にある」を**存在量化**で持つ: `∃ x₀ K g, ScanOnPackedRunFromInvLPS w x₀ ∧ ReportPoint w x₀ ∧ g 0 = x₀ ∧ (∀ i < K, Tick (g i) (g (i+1)) ∧ OracleTick …) ∧ (∀ i < K, (g i).vm.right = x₀.vm.right ∧ scan ∧ 非 replay) ∧ 2·|w| ≤ position (g K).vm.right ∧ ∃ i ≤ K, absSC m = g i`、または `frozenAt`。入口は `canonicalPreTrace_exists` の 4 番目の連言（n324）と `hpostOfLastReport` の `Needy … (Tc n) n`（truncation は `truncS 0 = id`）。
* run の存在: 起点の不変量は `¬ restartGuardVM` を含むので `settle` は不要。`scanBackground_run`（`clock − 1` 回の count tick、前提は `canRight right`＝報告点では `gap = false`、`OutputRel`、run 形の readiness 入力＝`OracleReady` の 2 葉で放電）→ `scanCompare_cases`（`clock = 1`、matched／shift／fallback の 3 通り、どれも右ヘッドが 1 歩右＝`position_right_of_atLast` で `2n`）。compare の tick が `OracleTick` であることは `scanCycle_of_leaves` の matched の場合と第 4 の葉（fallback の canonical な place `rightPlace`）の組み方を写す。
* 後継は `next := GhostSection.ghostOf … (g (i+1))`。`Tick`／`Canonical` は run から（`OracleTick` の `.canonical`）。切断の事実（`AllCanonical`、`ParkedRight`、入口の符号）は、trace 版の 3 定理（`countersCanonical_trace`、`parkedRight_trace`、`entrySigns_of_scanTick`）を「boot からの tick 列」の形へ**その場で一般化**して、`PackedFromBoot` の run ＋ plateau run に当てる（trace 版は `PreTrace` の `start` と `trace.tick` しか使っていない。`parkedRight_trace` だけ `frontPack_alongTrace`／`rewindCentre_trace` 経由なので run 形の `FrontPack` が要る）。
* `hplateauNext` の消費箇所（`:1188` 付近）の `Post` の保存は、`i < K` なら同じ run の `i+1`、`i = K` は `frozenAt`。

**次の一手**: 最後の checkpoint の不変量から `scanBackground_run`（clock = 1 まで）→ compare 1 回の canonical な run を組み、`Post` を「その run の上を追跡している」に強める。切断（`GhostSection.ghostOf`）に要る事実は tick の保存補題（`allCanonical_tick`、`parkedRight_tick`、`entrySigns_of_scanTick`）で run に沿って運ぶ。

## n323（2026-09-21）: 開いていたモード `scan` に局所後継ができた。仮説 `hscanNext` を消費者から外した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | 残。公理リストは不変（義務 1 本）、`unconditional` は付け替えていない。局所経路の消費者 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` の仮説から `hscanNext` が消えた。抽象局所層に残る仮説は `hplateauNext` だけ。物理機械の仮説（`htape`／`Enc`／`hencInit`／`hforwardTick`／`hforwardFeed`／`hencRep`／`hencOut`／`PhysFrozen` 系 3 本）と ActRule は未着手。 |

**状態: 全体 build 成功（`BUILD=0`、error 0、sorry 0。`GalilFrontier` を触ったので木全体を再 build）・標準公理のみ・無条件 PAL は未完。**

**何を証明したか**: 定理 `ShadowedLocalFinal.scanNext`。追跡されている scan 状態 `m` の tick target が「trace の次状態を、到着済みの文字まで truncation したもの」であるとき、`NextOK` を満たす局所後継がある。後継は源 `m` から計算せず、target の**切断**（`GhostSection.ghostOf`）として作る。抽象局所層は証明の ghost なので非局所でよい（n304）。
* 道筋（n316 の道 A）。消費者の型から読んで仮説を順に弱めた: n318（target の正体と `Canonical` を `Hloc` が受け取る）、n319（`NextOK` から `Post` 節を削除、`ReportPhase.reportPhase_tick`）、n320–n322（極性は読む者のモードでだけ求める。`localGood := mode ≠ scan → PolWF`、`PolWF` の `remaining`／`cycle` は shift、`fppWork` は copy。replay commit は `length`／`work` の極性を自分で立てる）。
* 新モジュール 4 本（全部 `scanNext` が消費。`ShadowedLocalFinal` の import から `Workbench` 経由でルートに届く）:
  - `GhostSection`: `ghostOf roles background c t parked`（ヘッドは `viewOfHead`、カウンタの銀行は `Function.extend roles …`、鏡は `mirrorOfTape`、バッファは `⟨tapes, tapes, true, none⟩`、walker は `viewOfPlace`）、`absState''_ghostOf`（カウンタが `Canonical`、`replay = ofNat r`、`right = left^[r] parked`、非 replay なら `r = 0` の下で `absState'' = ⟨c, t⟩`）、`physWF_ghostOf`（`PhysWF` ∧ `MirInv1`）、`polOf_of_nonneg`。`ctrOf` 系 6 宣言と `viewOfPlace` 系 3 宣言は旧 encoder `CloseoutCoreEnc2` から**移動**し、旧側は `export` で名前を保つ（`CloseoutCoreEnc2` は消費者の import 閉包に入っていなかった）。
  - `CountersCanonicalTrace`: 抽象が読むカウンタ 10 本は trace の全点で `Canonical`（`allCanonical_tick`、restart が `last` を `radius` に写すので chain 側の `ChainLastCan` も運ぶ）。
  - `ParkedRight`: `ParkedRight s := ∃ r parked, replay = ofNat r ∧ right = left^[r] parked ∧ r ≤ position parked` が trace の全点で成立。抽象の `right` は右スタックが空なら `incoming` から引くので `left (right p) = p` は一般に偽で、`Frontier` だけでは駐車 view を逆算できない。
  - `ScanEntrySigns`: `entrySigns_of_scanTick`。源の `SpanRep` と `0 ≤ radius` から、shift の入口（`remaining := ofNat h`、`cycle := reset`、`length += 2`）と copy の入口（`fpp.work := inc length`）の符号。
* コピペ回避: tick での `(right, replay)` の動きの分類 `RightReplayMove`／`rightReplayMove_of_tick` を `GalilFrontier` に置き、`frontier_tick` をその 4 場合から導く形に直した（120 行 → 25 行）。

**次の goal `hplateauNext`（定義と下流を読んだ。未着手）**: 受理は最後の窓 `((n−1)·L, n·L]` の latch で読まれる（`LocalTrackingLatch.tracking_latch_of_oracles`）ので plateau は高々 `nLocalL` tick だが、その間の抽象 tick の**存在**は要る（止まると `chosenStep` が `m` のままで `TickSucc` が立たない）。存在は `OracleRun.scan_tick_exists_PofC`（`SearchReady` と `ChainReady` から）で、run に沿う部品 `settle`／`scanBackground_run`（前提は `canRight right`、報告点では `gap = false` なので成立）／`scanCompare_cases` が oracle 側に既にある。案: 最後の報告点から右ヘッドが `2n` に出るまでの canonical な run の存在を 1 本立て、`Post` を「その run の上を追跡している」に強める。切断に要る事実は tick の保存補題（`allCanonical_tick`、`parkedRight_tick`、`entrySigns_of_scanTick`）で run に沿って運ぶ。採らなかった案: 報告点で ghost を凍らせる（物理機械が右へ 1 歩進んだ時点で `hencRep` が破れる）、延長語 `w ++ [a]` の trace を追跡させる（下流が `Pof w`／`H_letter` で `w` の frame に固定されていて改造が大きい）。

## n322（2026-09-21）: `remaining` の極性は shift、`fppWork` の極性は copy でだけ求める

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` の `Good next` は、shift の入口で `fppWork`、copy の入口で `remaining` を求めなくなった） |

**やったこと**: `PolWF` の各成分を読む者を利用箇所で確かめた（`remaining`＝`shiftCounters_of` と `shiftMagnitudes_of_trace`、どちらも shift。`fppWork`＝`copySide_of`、copy）。`CopyIdle` は符号の事実ではない（walker が none を読むか work がゼロ）ので、shift の入口で `fppWork` の符号は trace から取れない。読む者のモードで guard した。
* `LocalWF.PolWF := (mode = shift → pol remaining) ∧ pol radius ∧ pol length ∧ (mode = shift → pol cycle) ∧ (mode = copy → pol fppWork)`。
* コピペを避けた: `mode_shift_of_*` 7 本に copy 版を足さず、`EntryMode M := M = .shift ∨ M = .copy` を立てて `entryMode_of_tickL3`／`_copyStepL`／`_homeStepL`／`_markEndStepL`／`_chooseStepC`／`_rewindStepC`／`_ffpp`（shift か copy に着地するなら源も同じモード）へその場で一般化。`polWF_congr` は `∀ {M}, EntryMode M → y.mode = M → x.mode = M` を取る。`copySide_of` は `hmode` を取る。
* 技: 着地モードが定義の中に隠れていても `exact Mode.noConfusion hland` で落ちる（n317 の `show Mode.X = Mode.shift from …` の列挙が要らない）。`stepOf` 形の仮説は `have hland : (shiftStepW m).vm.ctl.mode = Mode.copy := hland` で言い直してから `unfold`。

**入口の符号（定義を読んだ）**: `afterMismatch` は `radius` だけ +1 で `length` はそのまま、`afterCompare` は `length` に +2。`beginShiftVM` は `remaining := ofNat h`・`cycle := reset`・`length := inc (inc length)`、`beginFallback` は `fpp.work := inc length`。なので入口の符号は、源の scan 状態の `SpanRep` と `0 ≤ value radius` から tick の場合分けで全部出る（スクラッチ `$S/entry_signs.keep.lean` に書いた。検証はこれから）。

## n321（2026-09-21）: replay commit は `length`／`work` の極性を自分で立てる。run 不変量は `PolWF` だけ

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` の `Good next` から `pol work`／`pol replay` が消えた） |

**やったこと**: `pol work` を読むのは replay commit（`LocalTick2.abs_commitReplay` の `hpw`）だけだった。そこは `length`／`work` を reset して push するだけなので、`LocalInitStep.initVml` と同じく極性を自分で正に立てればよい（`pol := fun c => if c = .length ∨ c = .work then true else movePol .radius .replay x.pol c`）。なぜ今まで前提だったか: `commitReplay` は `movePol` の置換だけを書いていて、push 先の極性を前提に回していた。
* `LocalTick2`: `absCtrs_commitReplay_stable`／`_replay` は `if_neg`、`_one` は `if_pos h6`（`hp` を除去）。`abs_commitReplay`／`replayStartVM_commitReplay` から `hpl`／`hpw` を除去。`LocalReplaySwap`／`LocalReplayParked`／`ReplayStartGhost` の同じ 2 前提も除去（他の呼び出し元は無い）。
* その結果、束の `pol work`／`pol replay` を読む者がいなくなった（利用箇所を全部確認）。途中で置いた `polarityBundle` を消して `localGood m := m.vm.ctl.mode ≠ .scan → PolWF m.vm`。相 step の保存は `LocalWF.polWF_congr` を直接使う。
* 効果: `search.work` の符号を trace で示す問題が消えた。

**極性の残り（定義を読んだ）**: `PolWF` の各成分を読む者は、`remaining`＝shift だけ（`shiftCounters_of`）、`cycle`＝shift だけ、`fppWork`＝copy だけ（`copySide_of`）、`radius`＝shift／rewind／replayStart、`length`＝shift／choose／rewind。`CopyIdle` は符号の事実ではない（walker が none を読むか work がゼロ）ので、shift の入口で `fppWork` の符号は取れない。次の一手: `remaining` を shift、`fppWork` を copy で guard し、`mode_shift_of_*` 系は「shift か copy に着地するなら源も同じモード」へその場で一般化する。入口で要るのは、shift: `remaining = ofNat h`・`cycle = reset`（`beginShiftVM`）、`length` は `SpanRep`＋`RadLedger.nonneg`。copy: `fpp.work = inc length`（`beginFallback`）、`length` は源の `SpanRep` と `spanRep_afterCompare`。

## n320（2026-09-21）: run 不変量の極性の束は scan 以外のモードでだけ求める

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` は残っているが、`Good next` は scan の着地では空虚になった） |

**やったこと**: 極性を誰が読むかを利用箇所で全部確かめた。読むのは 7 つの相 step（`LocalWF.realizes_seven` の `H_wf`、5 箇所、どれも `hmd : mode = X` を持つ）と `replayStartNext` だけで、scan では誰も読まない。scan の後継は切断（抽象が合う状態）で作るので、極性を保つ理由が無い。
* `ShadowedLocalFinal`: `polarityBundle m`（旧 `localGood` の中身: `PolWF` ∧ `pol work` ∧ `pol replay`）と `localGood m := m.vm.ctl.mode ≠ .scan → polarityBundle m`。`localGood_of_pol_eq` は `polarityBundle_of_pol_eq` に改名。相 step の保存は「源は scan でない」（`hnotScan`）から束を取り出して運ぶ。`init` と `replayStart` の着地は scan なので `fun hnotScanNext => absurd rfl hnotScanNext`（`replayStartNext` の `radius`／`replay` の極性交換の証明が消えた）。到着は `ctl_feedC` で源のモードに戻す。
* `LocalWF.realizes_seven`／`CloseoutCoreStep.realizes_seven_of_agree`／`CloseoutCoreAgree.realizes_seven_SL` の `H_wf` に `m.vm.ctl.mode ≠ .scan` の前提を足した（use site は `(by rw [hmd]; decide)`）。

**極性の残り（定義を読んだ）**: scan→shift と scan→copy の入口でだけ符号が要る。
* shift の入口（`beginShiftVM`、`GalilScaffoldTopShiftCycle:23`）: `remaining := ofNat h`、`cycle := reset`、`length := inc (inc length)`。copy の入口（`FppControl.beginFallback`、`GalilScaffoldChainFallback:404`）: `fpp.work := inc length`。fresh に入る分は tick の場合分けから直接読める。
* `length` は `GalilSpanCounter.SpanRep`（`value length = 2·value radius + 1`）が scan と shift の trace 点で成立（`BranchSupply.spanRepOnScanAndShift_alongTrace`）、`radius` は `RadLedger.nonneg`、`replay` は非 scan なら `ReplayRest` で reset。
* `search.work`（`Ctr.work`）だけ材料が無い。読むのは replay commit（`LocalTick2.abs_commitReplay` の `hpw`）だけで、そこは `length`／`work` を reset して push する。`LocalInitStep.initVml` は同じことをするとき極性を自分で正に立てている（`pol := fun c => if c = .length ∨ c = .work then true else x.pol c`）。`commitReplay` も同じ形にすれば `hpl`／`hpw` が要らなくなり、`pol work` は束から外せる。

## n319（2026-09-21）: 報告点の後の相は tick そのものが保つ。`NextOK` から `Post` 節を削った

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` は残っているが、両方とも `Post` 節のぶん弱くなった） |

**やったこと**: `NextOK` の最後の節 `Post w m → Post w next` は、消費が plateau 側 1 箇所だけなのに `chosenStep` が共有しているせいで scan 側でも証明が要った。定義を読むと、`ReportPoint`／`Refreshed` が読むのは 3 ヘッドと control の `replaying`・`output` だけ。なので trace を使わない抽象補題 1 本で両方に効く。
* 新モジュール `PalPeg/ReportPhase.lean`（`ShadowedLocalFinal` が import、`Workbench` 経由でルートに届く）:
  - `scanTick_kept_or_moved`: scan・非 replaying の状態からの tick は、3 ヘッドと `replaying`／`output`／`mode` を保つ（`scan_wait`／`scan_count`／`restart`）か、右ヘッドを 1 歩右へ動かす（`scan_match`／`scan_shift`／`scan_fallback`）。scan 以外の構成子は `cases h <;> first | (exfalso; simp_all; done) | skip` で先に落とす。
  - `position_right_of_atLast`: `position p = 2n − 1`（`0 < n`）なら `position (right p) = 2n`。偶奇で `gap = true` が消えるので `Sane` も `canRight` も要らない。
  - `reportPhase_tick`: refreshed な報告点 ∧ scan からの tick は、同じ相に着地するか、右ヘッドが `2·|w|` に出る。結論がちょうど `postPhase`。
* `ShadowedLocalFinal`: `NextOK`／`chosenStep`／`chosenStep_spec`／`good_chosenStep`／`ghostSteps` から `Post` 引数を除去。plateau の消費箇所は `hspec.1`（`Tick`）から `reportPhase_tick` で `postPhase` を出す。`replayStartNext` の `Post` 節の証明も削除。
* 進め方: スクラッチ（`$S/post_check.keep.lean`）で通してから、消費者と一緒にリポジトリへ入れた。

**`hscanNext` の残り**: target（trace の次状態の truncation）に対して `absState'' next.vm = target` ∧ `PhysWF` ∧ `MirInv1` ∧ `localGood` を満たす切断を作ること。材料: ヘッド・銀行・`Place`・バッファの切断と `parkedRight_trace`・`countersCanonical_trace`（全部スクラッチ）、鏡（投入済み）。未: 極性（`localGood` が求める `remaining`／`radius`／`length`／`fppWork`／`work`／`replay` の非負性を target で示す）、`Inv` の組み上げ。

## n318（2026-09-21）: scan の後継の仮説は、target が trace の次状態であることと `Canonical` を受け取る

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` は残っているが、`hscanNext` は弱くなった） |

**やったこと**: 部品を下から積むのをやめて消費者の型から読んだら、道 A の (5) の正体が分かった。`LocalRealizesScan.realizes_of_refined_tick_det` の中で `Hloc` に渡している target は実は `truncS (raw.length - j) (stOf (k+1))` で、`Tick` も `Refinement`（＝`Canonical`）も手元にあるのに、`Hloc` の型がそれを捨てていた。なぜ捨てていたか: `Hloc` は「任意の tick target に対して局所 step が tick である」という分岐別の局所 step 向けの形で書かれており、target の正体を使う消費者（切断）が当時無かった。そのせいで `hscanNext` は、追跡添字が最後の点かもしれない任意の target に対して `Tick` と `Canonical` を自前で作る形になっていた。
* `realizes_of_refined_tick_det` の `Hloc` をその場で一般化: `(∃ k j, Needy raw stOf k j m.vm ∧ k < lastTick ∧ t = truncS (raw.length - j) (stOf (k+1)))` と `Refinement (absState'' m.vm) t` を追加で受け取る。`realizes_of_tick_det` は内部で無視（署名は不変）。`CanonicalLocalRealizes.realizes_canonical` の `hLocal` も同じ 2 つを受け取る。
* 消費者 `given_openModesAndPhysicalMachine` の `hscanNext` が同じ 2 つを受け取る形になった。`init` と `replayStart` の呼び出しは無視するだけ。
* 効果: 切断 `next` が `absState'' next.vm = target` を満たせば、`NextOK` の `Tick` と `Canonical` は書き換えで出る。**道 A の (5)（`NextOK` の `Canonical`、`k < Tc` の未確認点）は消えた。**

**`Post` 節と plateau（定義を読んだだけ）**: `given_shadowedLocalSystem` では `Post` は自由パラメタ（入口 `hpostOfLastReport`、保存 `hpostTick`）。「報告点で凍らせて plateau を消す」案は採れない: `hfrozenQuiet` が凍結中の rep bit off を要求し、物理機械は語の終わりを知らず報告点の後も count → compare → 右へ 1 歩進むので、ghost だけ報告点で止めると `reportTest = true` と物理側が食い違う。`2n` で凍る現設計は意図的。plateau は「報告点 → count tick → compare 1 回で `2n`」で、trace が無いので抽象 tick の存在が要る（既存に `GalilTickFun.tick_exists`（`sharedFun` 版）と `GalilTickFair.fair_restart`。`sharedC` との対応は未確認）。

**道 A の残り**: (1) カウンタの `Canonical`（スクラッチ完成）、(2) 非負性 6 本、(3) 切断本体（ヘッド・鏡・銀行・`Place`・バッファは部品あり、組み上げと `Inv` が未）、(4) replaying の右ヘッド（`parkedRight_trace` スクラッチ完成）、(6) `scanNext` の組み立て（`Post` 節を含む）と仮説の除去。その後に `hplateauNext`。

## n317（2026-09-21）: run 不変量の `cycle` の極性を shift モード限定にした

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。存在仮説 `hscanNext`／`hplateauNext` は残っている） |

**やったこと**: `LocalWF.PolWF` の `cycle` 成分を `x.ctl.mode = .shift → x.pol .cycle = true` にした。消費者 `given_openModesAndPhysicalMachine` の存在仮説が要求する `Good next` がそのぶん弱くなった（scan の着地で `cycle` の極性を示さなくてよい）。
* **なぜ要ったか**: 正本 `ScaffoldChain.scala:156–160` の `matched()` は `periodOnly` なら `cycle.dec()` を無条件で実行し、「`cycle > 0`」は `checkPair`（`:117–127`）の assertion（2 半周期の継続不変量）でしか守られていない。trace 上で全状態の `cycle ≥ 0` を示すには Galil の周期性の議論が要る。一方、`cycle` の極性を実際に読むのは `shiftCounters_of` の 1 箇所だけで、shift 入口で `cycle := reset`・shift 中は inc だけなので shift モードの間は安く出る。
* 追加した宣言（全部消費者あり）: `mode_shift_of_tickL3`（`cases h`、着地モードは `exact absurd (show Mode.X = Mode.shift from hshift) (by decide)` を `first` で当てる。**着地モードが `copyDoneVm` などの定義の中に隠れているので `decide` も `simp_all` も届かない。`show` で defeq を明示する**）、関数 step 6 個の `mode_shift_of_copyStepL`／`homeStepL`／`markEndStepL`／`chooseStepC`／`rewindStepC`／`ffpp`（`unfold … at hshift; split at hshift`、`ffpp` は `hexists.choose_spec.1` と `mode_shift_of_tickL3`）、`ctl_feedC`。`polWF_congr` と `shiftCounters_of` は `hmode` を取る。`polWF_tickC` は外に使用者が無いが、`hmode` の仮説を足して残した。
* `ShadowedLocalFinal`: `localGood_of_pol_eq` に `hmodeShift`、shift の場合は `fun _ => hmode`、`init` と `replayStartNext` の着地は scan なので `cycle` の節は空虚、blank は `fun _ => rfl`、到着は `ctl_feedC`。
* 進め方: 先にスクラッチ複製（`$S/LocalWF.trial.lean`）で 5 箇所を直して通してからリポジトリへ反映した。

**(5) `NextOK` の `Canonical` の見通し（2026-09-21、定義を読んだだけ）**: `CanonicalLocalRealizes.realizes_canonical`（`:68`）の `hLocal` は、tracked・非 starved な `m` と任意の `target`（`Tick … (absState'' m.vm) target`）に対して `Tick … (absState'' (f m).vm)` ∧ `Canonical …` ∧ `PhysWF` ∧ `MirInv1` を求める（`NextOK` とほぼ同じ）。仮説の `target` は canonical とは限らないので、後継は `target` でなく **trace の次状態の truncation `truncS (n − j) (stOf (k+1))` を具体化したもの**にする。材料: `canonical_trunc`（`:56` 付近、trace の canonical な tick は truncation しても canonical。`restartVM_trunc`／`restartGuard_of_trunc` を使う）、`LocalSysConcrete.tick_of_need`（need が満たされていれば truncation 同士が tick）、`ShadowedLocalFinal.nextUsed_heldAfter`（非 starved なら次の used ≤ j）。未確認: `InvC` の `Tracked` は添字 `k` を縛らないので、非 starved な tracked 状態では `k < Tc` が出ること（`notStarved_of_need_heldAfter` の周辺に既にあるはず、要確認）。

**(3) 切断本体の部品: カウンタの銀行（2026-09-21、スクラッチ `$S/bank_check.keep.lean`、error 0、標準 3 公理、一発）**: `bankOf roles background counters := Function.extend roles (fun c => (ctrOf (counters c)).1) background`、`polOf counters c := (ctrOf (counters c)).2`。`roles` が単射なら `bankOf … (roles c) = (ctrOf (counters c)).1`（Mathlib の `Function.Injective.extend_apply`）、`Canonical` なら `LocalRoles.absL (bankOf …) roles (polOf …) c = counters c`（既存の `CloseoutCoreEnc2.absCtr_ctrOf`）、各役割のテープは `SegCtr`（`segCtr_ctrTapeSeg`）。`roles` は blank 状態のものを流用できる（`LocalBlankState.inv_blank` の `roles`）。**注意**: `ctrTapeSeg`／`ctrOf`／`absCtr_ctrOf` は旧 encoder の `CloseoutCoreEnc2`（`CloseoutCoreEnc` を import する重い旧経路）にある。リポジトリに入れるときは、この 5 宣言を `LocalCounter` の近くへ移して新経路が旧 encoder に依存しないようにする。切断の部品はこれで 3 つ: ヘッド（`$S/sec_check.keep.lean`）、鏡（`ReplayStartGhost.mirrorOfTape`、投入済み）、銀行。残り: `Place`（walker 2 本。`viewOfPlace` は旧 encoder にあり、`ProperView` を満たすかは未確認）、バッファ、全体の組み上げ。

**(3) `Place` の切断と (4) replaying の右ヘッド（2026-09-21、スクラッチ、error 0、標準 3 公理）**:
* `Place`: 既存の `CloseoutCoreEnc2.viewOfPlace` は番兵 `none` で閉じる形なので `ProperView (viewOfPlace p)` が帰納で出る（`$S/place_check.keep.lean`、公理依存なし）。バッファの切断は `⟨tapes, tapes, true, none⟩` で `LocalBuffers.abs` が `rfl`。
* **(4) で障害を 1 つ見つけた**: 抽象の `GalilScaffoldChainVerifier.right` は右スタックが空なら `incoming` から引くので `left (right p) = p` は一般に偽。`FrontPack.frontier`（`position right + replay ≤ 2·arrived`）だけでは、replaying の抽象右ヘッドから駐車 view を逆算できない。なぜ足りないか: `arrived` は左＋右スタックの長さで、`incoming` から引いた 1 歩は `left` で戻すと右スタックに入り元の状態と違う。必要なのは「右ヘッドは駐車点から `replay` 回左へ戻った形」という履歴の事実。
* 立てた trace 不変量（`$S/parked_check.keep.lean`）: `ParkedRight s := ∃ r parked, s.replay = ofNat r ∧ s.right = left^[r] parked ∧ r ≤ position parked`（control 非依存。非 replay は `replay = reset` で `r = 0`）。`parkedRight_trace`: `PreTrace` の全点で成立。
* **コピペを避けた形**: `frontier_tick`（`GalilFrontier:196`）と同じ場合分けを二度書かないため、tick での `(right, replay)` の動きの分類 `RightReplayMove c s t`（`rested`／`kept`／`replayed`／`started` の 4 構成子）と `rightReplayMove_of_tick`（仮説は `ReplayRest` だけ）を 1 本立て、`parkedRight_tick` はその 4 場合から出す。リポジトリに入れるときは `GalilFrontier` に置き、`frontier_tick` もこの分類から導く形に直す（`GalilFrontier` は深いので全体 build が要る）。
* trace 形の入力は全部既存: `BranchSupply.frontPack_alongTrace`（`rest`／`replayPos`／`rewind`）、`ReplayStartGhost.rewindCentre_trace`、`LocalReplayParked.right_left_iterate`、`ofNat_inj`。`i = 0` は `hP.start` で boot（`replay = reset`、`replaying = false`、`mode = init`）。
* 切断での使い方: 右 view := `viewOfHead parked`、`rval = r`（銀行の `replay` テープ）なら `absR = left^[r] parked = s.right`、`ParkedOK` は `r ≤ position parked`。truncation とは `ReplayStartGhost.truncPH_left_iterate` で可換。

**道 A の残り**（n316 の一覧から更新）: (1) カウンタの `Canonical` は trace の事実としてスクラッチで完成（`$S/lift_trace.keep.lean`、未投入）、(2) 非負性は `cycle` を外したので残り 6 本（`remaining`／`radius`／`length`／`fppWork`／`work`／`replay`、各モードの入口で要る分だけ）、(3) 切断本体と `abs''` の等式・`Inv`（ヘッドの切断は `$S/sec_check.keep.lean`）、(4) replaying の着地の右ヘッド、(5) `NextOK` の `Canonical`、(6) `scanNext`／`plateauNext` の組み立てと仮説の除去。

## n316（2026-09-21）: `hscanNext`／`hplateauNext` の方針 — 分岐ごとの局所 step でなく、抽象の着地を具体化した ghost を後継にする（調査のみ、コードは変えていない）

**全体 build 成功（最新は n315 の `BUILD=0`）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（未接続） |

**視点の変更**: n315 で分かったのは「ghost は自由なので、後継は抽象の着地に合うものを直接作ればよい」こと。scan は分岐が多く（wait／count／match／replay の match／restart／shift 入口／fallback 入口）、既存の局所部品（`LocalTick2.commitRestart`、`beginShift` の `shiftSlot`、`commitFallback` の `jF`）は割当や staging の名前付き仮説を大量に抱えている。分岐ごとに組むのをやめ、**抽象状態 → ghost の切断（section）**を 1 本作って、`next := 切断 (着地)` とする。`hscanNext` と `hplateauNext` の両方に効く。

**一次情報で確かめたこと**:
* `LocalState.abs`（`:189`）は場ごとの単純な写像: ヘッド 3 本（`absHead`）、`chain` はそのまま、カウンタ 10 本（`absCtrs`: cycle／remaining／radius／length／replay／fppWork／span／work／debt／lower）、fpp（mode／pc／`LocalBuffers.abs fppBuf`／done／walker は `absPlace fppWalker`／finalStage）、search（mode／finalStage／quarter）、dp（pc／`LocalBuffers.abs dpBuf`／done）、`periodOnly`、`walker := absPlace walkerView`。
* 切断の部品は旧 encoder 経路に既にある（`CloseoutCoreEnc2`）: `ctrOf`＋`absCtr_ctrOf`（`Canonical` なカウンタ）、`viewOfPH`（`absHead` の切断、`:122`）、`viewOfPlace`（`absPlace` の切断、`:144`）。鏡は n315 の `ReplayStartGhost.mirrorOfTape`。

**要確認（次にやる順）**:
1. 新経路は `abs'`／`abs''`（`absHead'`、`far`／`near` を見る版）を使う。`viewOfPH` が `absHead'` の切断にもなるか（`far := 空`、`near := right`、`pending := []` なら `incoming` は `far ++ pending` なので、`incoming` を `far` に載せる必要がある。`RTQueue` を list から作る構成子と `RTQueue.Inv` の補題を探す）。
   **→ 解決（2026-09-21、スクラッチ `$S/sec_check.lean`、控え `sec_check.keep.lean`、error 0・標準 3 公理）**: `PhysWF.pend` が `pending = []` を要求するので、各ヘッドの `incoming` は自分の `far` に載せる。`queueOfList l := l.foldl RTQueue.snoc RTQueue.empty`、`Inv (queueOfList l) ∧ toList (queueOfList l) = l`（一般の開始 queue で帰納、`RTQueue.inv_snoc`／`toList_snoc`／`inv_empty`／`toList_empty`）。`viewOfHead p := ⟨p.head.left, p.head.focus, p.head.right, queueOfList p.head.incoming, p.gap⟩` で `absHead' (viewOfHead p) [] = p` と `LocalInputView.WF (viewOfHead p)`。旧 `viewOfPH` は `far := empty` で `incoming` を `pending` に回す形なので、3 本のヘッドで `incoming` が違う新経路には使えない。
2. `PolWF`＋`work`／`replay` は正の極性を要求する。`ctrOf c` の極性は `c.neg.isEmpty` なので、着地でこの 7 本が非負であることが要る。trace 上の既存材料（`GalilLengthFloor.FPack.radius`、`CloseoutLenNonneg`、`RadLedger.canon`、`CPack.canon`）でどこまで出るか。全カウンタの `Canonical` も同様。
   **→ タダでは出ない（2026-09-21、grep と定義で確認）**: trace 上の `Canonical` の事実はカウンタごとにまばら（ファイル数: `length` 30、`radius` 14、`remaining` 7、`replay` 2、`cycle` 1、`search.debt` 47、`lower`／`search.span`／`search.work`／`fpp.work` は 0）。非負性も `GalilLengthFloor.FPack` が scan／shift の `radius`・`length` を持つ程度で、全モード・7 本ぶんは無い。演算の補題はある（`GalilScaffoldCounter.inc_canonical`／`dec_canonical`／`ofNat_canonical`、`reset` は自明）。
   * 観察: tracked 状態のカウンタは ghost のテープの抽象（`absCtr`）なので、`absCtr_canonical` により**常に** `Canonical`、`PolWF` の 7 本は**常に**非負。足りないのは「次の trace 状態でも成り立つ」の 1 歩だけ。
   * 道 A: 一括の trace 不変量 `AllCanonical ∧ 7 本非負` を新設し、Tick の全構成子（探索量子 `searchEffect`、chain、fpp プログラムの量子を含む）で保存を示す。一様だが、frame の関係を全部開く必要がある。
   * 道 B（混成）: `LocalTick1.TickL1`＋`LocalReplayParked` が既に覆っている分岐（wait／count／match／replay の match）はその局所後継を使い（`PhysWF`／抽象の一致の証明つき）、覆っていない分岐（restart／shift 入口／fallback 入口）だけ切断を使う。着地のカウンタは reset／ofNat／既存値のコピーが多く、`Canonical`・非負性が分岐ごとに直接読める見込み。
   * どちらを採るかは、`TickL1` の各構成子が要求する仮説（`SearchFrame` の存在、chain tick、`hcan`、`hahead` など）を読んでから決める。
   * **決定（2026-09-21）: 道 A。** `LocalTick1.TickL1`（`:777`）を読んだ結果、wait／count／match のどの構成子も `hs : SearchLocal S b x z`（探索量子の局所後継 `z` の存在）を要求しており、道 B でも探索部分の後継を自分で構成することになる。しかも覆っているのは matched だけで、mismatch（shift 入口・fallback 入口）と restart は無い。
   * **規模の探り（スクラッチ `$S/canon_probe.keep.lean`）**: `AllCanonical s`（10 本: cycle／remaining／radius／length／replay／lower／fpp.work／search.span／search.work／search.debt）に対して `cases h <;> first | exact hsource | skip` で残る構成子は **22 個**: fpp 系 9（`copy_one`／`copy_done`／`home_start`／`home_step`／`fpp_slice`／`fpp_done`／`markEnd_found`／`markEnd_step`／`choose_step`、`fppLens.rel` なので変わりうるのは `fpp.work` だけ）、rewind 系 4（`choose_select`／`rewind_one`／`rewind_pair`／`rewind_done`、`length`／`radius` の inc／reset／ofNat）、`init`／`replayStart`／`restart`（明示的な VM 関係）、`shift_one`（dec）、scan 系 5（`scan_wait`／`scan_count`／`scan_match`／`scan_shift`／`scan_fallback`、探索量子 `searchEffect` を含むのでここが重い）。非負性（7 本）は dec にガードが要るので別途（`shift_one` の `radius` は `RadLedger.shiftBud`）。
   * **スクラッチの進み（2026-09-21、`$S/canon_probe.keep.lean`、末尾は `sorry`）: 22 → 11。** 束ねた `Canonical` の不変量は既存に無い（構造の名前で確認。前に書いた「`search.debt` 47 件」は緩い正規表現の数え過ぎで、正確には 0）。閉じた 11 個: rewind 系 4（`obtain ⟨hstep, hframe⟩`／`⟨⟨_, hstep⟩, hframe⟩`、`rw [hstep] at hframe; subst hframe`、`inc_canonical`／`ofNat_canonical`／`Or.inr rfl`）、`copy_one`（`⟨⟨letter, _, hstep⟩, hframe⟩`、`dec_canonical`）、fpp 系の残り 6（`copy_done`／`home_start`／`home_step`／`markEnd_found`／`markEnd_step`／`choose_step`、同じ 2 パターンを `first` で当てて全場 `hsource` のまま）。`fallbackFrame`（`GalilScaffoldTopFallback:34`）で `work` を動かすのは `copyOne` の `dec` だけ。残り 11: `fpp_slice`／`fpp_done`、`init`／`replayStart`／`restart`、`shift_one`、scan 系 5。
   * **続き（2026-09-21、同じスクラッチ）: 11 → 6。** 任意の `Pw : Shared` では `init`／`replayStart`／`restart` が中身の無い関係なので、定理を具体の `GalilScaffoldChainInputSupply.sharedC onLetter leftFirst centre place entry`（`GalilFrontier:177`、`coupled_tick` と同じ形）に特殊化した。補題 `begin_canonical`（`GalilScaffoldSearchFinish.begin lower radius` は `span := reset`、`work := if zero lower then inc lower else lower`、`debt := ⟨radius.neg, radius.pos⟩` なので `hradius.symm`）。閉じた 5 個: `init`（`initVM entry s t` の 15 連言を `obtain`、各場は `h ▸ …`）、`replayStart`（構成子の引数順は `hm ho ho' hrel`）、`fpp_done`（`⟨⟨-, program, -, -, hstep⟩, hframe⟩`）、`fpp_slice`（`hstep` の右辺に `t` が出るので `subst` せず、`hwork := (congrArg FppControl.State.work hstep).trans rfl` と、各場 `by rw [hframe]; exact hsource.場`）、`shift_one`（`⟨⟨-, -, -, watch, -, hstep⟩, hframe⟩`、`cycle` は `inc` 2 回、`remaining`／`radius` は `dec`、`length` は `dec` 2 回）。**残り 6: `restart`（`lower := w.machine.control.last` なので chain 側の `last` の `Canonical` が要る）と scan 系 5（`searchEffect`）。**
   * **scan 系の棚卸し（2026-09-21、定義を読んだだけ）**: 既存の `GalilScaffoldTopSearch.backgroundS_fields`（`:231`）が background tick の場を列挙している（`radius`／`length`／`remaining`／`replay`／`fpp` は不変、`cycle` は chain 誕生で `reset` か不変、探索は `searchEffect P false s (searchLens.get s')`）。`searchEffect`（`:179`）は chain idle なら `searchStep`、そうでなければ探索不変。`searchStep`（`:152`）は `search.mode` で分岐: `idle`／`found`／`missed` は不変、`grow` は `growStep` か `prepare`、`lower`／`lowerHome`／`copy`／`home` は `PrepareControl.Tick`、`run` は `SearchRun.SafeQuanta`、`wait` は `Double.waitStep`、`double` は `Double.step` か prepare、いずれも `PreparePaced.afterAdvance`／`SearchRun.advance` を通る。`Canonical` の既存補題は下位機械ごとに部分的（出現数: `GalilScaffoldStagePrepare` 21、`GalilScaffoldDouble` 12（`canonical : Run s as t → …` あり）、`GalilScaffoldSearchRun` 10、`GalilScaffoldPreparePaced` 4（`spend_canonical`）、`GalilScaffoldSearchFinish` 2、`GalilScaffoldPrepareControl` 0）。scan 系 5 個はこれらを mode ごとに束ねる作業になる。compare 側（`scan_match`／`scan_shift`／`scan_fallback`）の場の補題は未確認。
   * **続き（2026-09-21、同じスクラッチ `$S/canon_probe.keep.lean`、末尾は `sorry`）: 主定理の残り 6 → 4。** 補題 `allCanonical_background`（`backgroundS_fields` で場を取り、`cycle` は `rw [hcycle]; split`（誕生なら `Or.inr rfl`）、探索 4 本は `searchCanonical` から）で `scan_wait`／`scan_count` を閉じた。補題 `searchCanonical : AllCanonical s → searchEffect P a s vq → Canonical vq.search.span ∧ … work ∧ … debt ∧ Canonical vq.lower` は、chain 非 idle の枝（`subst hsame`）と、`unfold searchStep at hstep; cases hmode : (searchLens.get s).search.mode <;> simp only [hmode] at hstep` のあと不変の 3 mode（`idle`／`found`／`missed`、`subst hstep`）が閉じた。**残り: 主定理の `restart`／`scan_fallback`／`scan_match`／`scan_shift` と、`searchCanonical` の 8 mode（`grow`／`lower`／`lowerHome`／`copy`／`home`／`run`／`wait`／`double`）。**
   * **続き（2026-09-21、同じスクラッチ）: 探索の 8 mode → 6＋半分。** 定義は単純だった（`GalilScaffoldDouble.enter`: `work := span`・`span := reset`、`waitStep`: 条件付きで `enter`、`Double.step`: `work` dec・`span` inc 2 回・`debt` は `quarter = 3` で inc、`GalilScaffoldSearchRun.advance`: `a` なら `debt` dec）。`SearchCan st := Canonical st.span ∧ Canonical st.work ∧ Canonical st.debt` と補助補題 3 本（`searchCan_advance`／`searchCan_waitStep`／`searchCan_doubleStep`、どれも `unfold`／`show` のあと `split`）で、`wait` と `double` の前半（`positive work` の枝、`split at hstep`）が閉じた。**残り: `grow`／`lower`／`lowerHome`／`copy`／`home`（`SearchVM.ofPrep (PreparePaced.afterAdvance a …)` を通る prepare 系）、`run`（`SearchRun.SafeQuanta`）、`double` の後半（prepare）。**
   * **続き（2026-09-21、同じスクラッチ）: prepare の 4 mode が閉じた。** `GalilScaffoldPrepareControl.Tick`（`:26`）は 9 構成子で、`work` は dec（`lowerBit`／`copyBit`）か `inc span`（`beginCopy`）か不変、`span`／`debt` は不変。`PrepCan p := Canonical p.work ∧ Canonical p.span ∧ Canonical p.debt`、`prepCan_tick`（`cases ht` して 9 個を個別に）、`prepCan_afterAdvance`。`SearchVM.toPrep`／`ofPrep`／`StagePrepare.runState` は場の並べ替えだけなので、`obtain ⟨landed, htick, hstep⟩ := hstep; subst hstep` のあと defeq で通る。使える既存補題: `GalilScaffoldGrow.add_canonical`（`growStep` の `add 8`／`add 2` 用）、`GalilScaffoldPrepareControl.prepare`（`:236`）は `work := lower`（`hsource.lower` が要る）。**探索部分の残り: `grow`（`growStep` か `prepare`）、`run`（`SafeQuanta`）、`double` の後半（`prepare`）。**
   * **続き（2026-09-21、同じスクラッチ）: 探索部分が全部閉じた。** `searchCanonical`（`searchEffect` が探索の 4 カウンタ span／work／debt／lower の `Canonical` を保つ）は `sorry` なし。`grow`／`double` の後半は `split at hstep` のあと `prepCan_growStep`（`GalilScaffoldGrow.add_canonical 8`／`2`）か `prepCan_prepare`（`work := lower`）、状態は `(p := (searchLens.get s).toPrep)` と明示しないと elaboration が通らない。`run` は `searchCan_finish`（`GalilScaffoldSearchFinish.finish` は mode を変えるか `work := span`・`span := reset`、`split` 4 段）→ `searchCan_safeCalls`（`SafeCalls` の帰納）→ `searchCan_safeQuanta`（`SafeQuanta` の帰納、`advance` を挟む）。**`sorry` が残るのは主定理の 4 構成子だけ: `restart`（chain 側の `last` の `Canonical` が要る）、`scan_match`／`scan_shift`／`scan_fallback`（compare 側。`backgroundS_fields` に当たる場の補題を探すか自分で書く）。**
   * **続き（2026-09-21、同じスクラッチ）: compare 側 3 個が閉じ、残りは `restart` の 1 個。** compare は完全に明示的だった（`GalilScaffoldTopSearch.compareFound`（`:205`）: `t = afterBirth born (if a then afterCompare s vs vq else afterMismatch s vs vq)`、`radiusAfter = inc radius`、`cycleAfter` は `periodOnly` なら dec、`afterCompare` は `length` inc 2 回、探索は `searchEffect`）。補題 `allCanonical_afterBirth`（`cases born`、誕生なら `cycle := reset`）と `allCanonical_compare`（`obtain … : compareFound P q first s t := hcompare`、`rw [hlanding]; apply allCanonical_afterBirth; cases a`）。2 歩目: `scan_match` は `hpl : t = replayDec c.replaying _`（`GalilScaffoldTopMerge:59`、`unfold replayDec; split`、`replay` dec）、`scan_shift` は `obtain ⟨watch, -, hlanding⟩ : beginShiftVM' _ t := hb`（`remaining := ofNat h`・`length` inc 2 回・`cycle := reset`。**`-` で chain の等式を消してから `obtain` すると依存消去で落ちるので、3 つ組で一度に取る**）、`scan_fallback` は `obtain ⟨landingPlace, hfallback, -⟩ : beginFallbackVM' _ t := hb`（`GalilScaffoldChainFallback.beginFallback`（`:404`）は `fpp.work := inc length`）。**22 構成子中 21 個が閉じた。残る `restart` は `lower := w.machine.control.last`・`search := begin last radius` なので、chain の watch 機械の中のカウンタ `last` の `Canonical` が要る（chain 側の不変量。`BranchSupply.ChainLagCanonical`（`:1783`）が何を持っているかを読む）。**
   * **`restart` の調査（2026-09-21、定義を読んだだけ）**: `BranchSupply.ChainLagCanonical`（`:1783`）が持つのは copy／back／watch の `lag` の `Canonical`＋非負だけで、`last` は無い。`GalilScaffoldCounter.positive c := !c.pos.isEmpty`（`:15`）なので、`restartVM` が与える `positive w.machine.control.last = true` から `neg = []` は出ない（`Canonical` は従わない）。chain の埋め込みカウンタを束ねた述語は `CloseoutCoreEnc2.CanonChain`（`:230`、watch／broken で `lag`／`margin`／`distance`／`boundary`／`last`）があるが、定義されているだけで trace に沿って示されたことは無い（使用は同ファイルのみ）。`last` の `Canonical` が仮説として現れる箇所: `GalilCycleNoShift:228`、`GalilFoundLandingL:232,365`、`CloseoutCoreEnc24:267`。導出している箇所: `GalilNoShiftStage:125–132`（特定の段）。**結論: `restart` を閉じるには chain 側の trace 不変量（少なくとも watch／broken の `last` の `Canonical`）を新設し、`ChainTick`／`chainAt` の全構成子で保存を示す必要がある。**

   * **chain 側の最初の 1 歩（2026-09-21、スクラッチ `$S/chain_probe.keep.lean`、error 0、公理 `propext`／`Quot.sound`）**: `last` を持つのは `GalilScaffoldChainConsume.State`（`distance`／`boundary`／`last`）。`consume`（`:28`）は一致なら `distance := inc distance`、境界イベントなら `last := boundary`・`boundary := inc distance`、不一致なら `broken := true` だけ。`ConsumeCan st := Canonical st.distance ∧ Canonical st.boundary ∧ Canonical st.last` は `consume` で保たれる。証明: `unfold consume; simp only; split_ifs` のあと候補 3 つを `first` で当てる（**`split` は内側の `match` を先に割ってしまい、`generalize` はパターンが合わなかった。`if` だけ割るなら Mathlib の `split_ifs`**）。未確認: watch 機械のほかの遷移（`chainShiftOne`、誕生・`immediate`、copy／back から watch への移行）で `machine.control` がどう初期化・更新されるか。
   * **続き（2026-09-21、同じスクラッチ）**: `GalilScaffoldChainWatch.State` は `machine`（`verifier`＋`control : ChainConsume.State`）／`lag`／`margin`。watch の tick は `Internal`（`idle`／`take`→`caught`）と `Outer`（`idle`／`queued`／`immediate`）の合成で、`control` を触るのは `caught`／`immediate` の `GalilScaffoldChainVerifier.consume`（中身は `ChainConsume.consume`）だけ。`WatchCan w := ConsumeCan w.machine.control` は `GalilScaffoldChainWatch.Tick` で保たれる（`cases htick; rename_i middle hinternal houter`、あとは構成子ごと。**`obtain ⟨hinternal, houter⟩ := htick` は中間状態に名前が付かず、`cases … with | @step …` は引数の数が合わなかった**）。未確認: `ChainVM` の高さの遷移（`ChainStep`／`ChainTick`／`chainAt`: copy→back→watch の移行で watch 状態がどう生まれるか、`chainShiftOne`、break、誕生 `chainStart`）。
   * **続き（2026-09-21、同じスクラッチ）: chain の高さの 2 関係が通った。** `ChainLastCan : ChainVM → Prop`（`.watch w`／`.broken w` で `WatchCan w`、他は `True`）は `GalilScaffoldTopChainVM.ChainStep`（`:58`、8 構成子）と `ChainMatched`（`:83`、6 構成子）で保たれる。error 0、公理 `propext`／`Quot.sound`、一発。根拠（定義で確認）: watch が生まれるのは `backDone` の `watchControl v`（`:54`、カウンタ 3 本とも `reset`）、`watchBreak`／`brokenIdle`／`brokenMatched` は `control` をそのまま運ぶ、`BreakStep`（`:26`）の着地は `⟨consume w.machine, w.lag, inc w.margin⟩`。未確認: `chainShiftOne`（`GalilScaffoldChainInputSupply:1478`、3 本とも `dec` なので `dec_canonical` で済むはず）、`chainAt`（`GalilScaffoldTopSearch:130`、誕生 `chainStart` は `.copy` なので `True`）、`beginShiftVM` の `immediate`、そして VM の Tick 22 構成子への持ち上げ。
   * **続き（2026-09-21、同じスクラッチ `$S/chain_probe.keep.lean`）: chain 側の部品が揃った。** `ChainTick a x z := ∃ y, ChainStep x y ∧ (if a then ChainMatched y z else z = y)`（`GalilScaffoldTopChainVM:118`）、`chainAt`（`GalilScaffoldTopSearch:130`）は「非 idle なら `ChainTick`」「idle かつ found でなければ idle のまま」「idle かつ found なら `chainStart`（`.copy` なので不変量は `True`）＋一致時は `ChainMatched`」の 3 枝。`chainLastCan_tick`、`chainLastCan_chainAt`（`rcases` で 3 枝、`cases a`）、`watchCan_chainShiftOne`（3 本とも `dec_canonical`）が一発で通った。error 0、公理 `propext`／`Quot.sound`。**残り: VM の Tick 22 構成子への持ち上げ**（不変量を `AllCanonical s ∧ ChainLastCan s.chain` にして、`canon_probe` の主定理に chain の場を足す。chain を動かすのは background／compare の `chainAt`、`beginShiftVM` の `immediate`（= `consume`）、`shift_one` の `chainShiftOne`、idle に戻す `init`／`replayStart`／`restart`／`beginFallback`。ほかは不変）。そのあと `restart` で `.broken w` の `last` の `Canonical` を取り出して `AllCanonical` の最後の 1 個を閉じる。
   * **完成（2026-09-21、スクラッチ `$S/lift_done.keep.lean`、`sorry` の警告 0、`#print axioms` は `propext`／`Quot.sound`）: カウンタの `Canonical` は tick で保たれる。** 2 本の定理（どちらも具体の `sharedC onLetter leftFirst centre place entry` の frame に対して）:
     * `allCanonical_tick : AllCanonical s → ChainLastCan s.chain → Tick … ⟨c, s⟩ ⟨c', t⟩ → AllCanonical t`（VM の 10 本。最後に残っていた `restart` は `s.chain = .broken w` と `ChainLastCan` から `Canonical w.machine.control.last` を取り出し、`begin_canonical` で閉じた）。
     * `chainLastCan_vmTick : ChainLastCan s.chain → Tick … → ChainLastCan t.chain`（22 構成子: `init`／`replayStart`／`restart`／`scan_fallback` は chain が idle に着地、`scan_wait`／`scan_count` は `backgroundS_fields` の `chainAt`、fallback 相と rewind は frame の等式で chain 不変、`shift_one` は `chainShiftOne`、compare は補題 `chainLastCan_compare`（`cases chainBorn … <;> cases a <;> exact hlanded`）、`scan_match` は `replayDec_chain`、`scan_shift` は `beginShiftVM'` の `immediate` = `consume`）。
     * つまずき: `case scan_wait hm hr hav hb` は「too many variable names」→ `case scan_wait => rename_i hb`。`restart` という名前の goal が 2 つ見えたのは、前半の定理の `sorry` がログに混じっていただけ。
     * **リポジトリには未投入**（消費者＝切断を使う `scanNext` と一緒に入れる。今入れると孤立定理）。trace 形（`PreTrace` に沿う帰納、boot で成り立つこと）もまだ。
     * **trace 形も通った（2026-09-21、同じスクラッチ、控え `$S/lift_trace.keep.lean`、error 0、標準 3 公理、一発）**: `countersCanonical_trace : PreTrace centre place entry q first w st Tc → ∀ i, i ≤ Tc w.length → AllCanonical (st i).vm ∧ ChainLastCan (st i).vm.chain`。boot（`hP.start`）は 10 本とも `Or.inr rfl`・chain は idle で `trivial`、帰納の step は `hP.trace.tick i hlt` に 2 本の tick 定理を `(onLetterVM w) leftFirstVM centre place entry q first 2048` で当てる（`PofC` の frame は `sharedC (onLetterVM w) leftFirstVM …` と defeq、`CloseoutRadPack3.coupledPack_trace` と同じ形）。これで道 A の (1)「着地のカウンタが全部 `Canonical`」は trace の事実として取れる。
   * **道具の注意**: bash コマンドの文字列に語 `watch` が入ると token-saver の hook が「Never-terminating command」で弾く。スクリプトは Write ツールでファイルに置いてから `python3 file` で実行する。

   * **(2) 非負性の調査（2026-09-21、正本と定義を読んだだけ）— `cycle` は全状態では示せない見込み、極性の要求をモード別にする。**
     * 正本 `ScaffoldChain.scala:156–160` の `matched()` は `periodOnly` なら `cycle.dec()` を**無条件で**実行する。「`cycle > 0`」を守っているのは `checkPair`（`:117–127`）の assertion（"chain continuation exhausted without dispatch"、2 半周期の継続不変量）だけ。trace 上で `periodOnly → 0 < cycle` を示すには Galil の周期性の議論が要る。Lean 側でもこれは仮説としてしか現れない（`LocalTick1:807` の `hper` ほか、trace の事実は無い）。
     * 一方、`cycle` の極性を実際に使うのは shift の関数 step だけ（`LocalTick3.ShiftCounters.cycPol`、`cycle` を inc 2 回）。shift 入口（`beginShiftVM`）で `cycle := reset`、shift 中は inc だけなので、**shift モードの間は `cycle ≥ 0` が安く出る**。scan モードの後継は切断なので極性は要らない。
     * **方針**: run 不変量 `localGood` の極性の要求を「その極性を使う関数 step のモード」に限定する。使用箇所（定義で確認済み）: shift は `remaining`／`radius`／`length`／`cycle`（`ShiftCounters`）、copy は `fppWork`（`CopySide.pol`）、choose は `length`（`ChooseWF.polLength`）、rewind は `length`／`radius`（`RewindWF`）、replayStart の commit は `length`／`work`（`hpl`／`hpw`）と `replay`（`movePol`）、init は `length`／`work` を自分で正にする。scan モードでは何も要らない。切断の後継は `ctrOf` の極性（`neg.isEmpty`）になるので、各モードの入口でそのカウンタが非負であることだけを trace から取る。
     * 残りの 6 本の dec とガード: `remaining`（`shift_one`、`remainingPos` でガード）、`radius`（`shift_one`、`RadLedger.shiftBud` で `remaining ≤ radius`）、`length`（`shift_one`、`SpanRep`）、`fpp.work`（`copy_one`、`¬ zero work`）、`search.work`（`growStep`／`Double.step`／`lowerBit` は `positive work`、`copyBit` は `zero work = false`）、`replay`（replay 中の一致。flag と counter の一致は `FrontPack.replayPos` の類を要確認）。

   * **モード別の極性の波及を測った（2026-09-21、リポジトリは未変更、スクラッチ複製 `$S/LocalWF.trial.lean`）**: `cycle` の極性を実際に読むのは `LocalWF.shiftCounters_of`（`:470`、`h.pol.2.2.2.1`）の 1 箇所だけ。`LocalWF.PolWF`（`:310`）の `cycle` 成分を `x.ctl.mode = .shift → x.pol .cycle = true` に変えると、`LocalWF` 内で落ちるのは 5 箇所: `polWF_of_tickL3`（`:321`）、`polWF_x0C`（`:379`）、`shiftCounters_of`（`:470`、`hmd` を取る）、`polWF_congr`（`:569`）、`localWF_x0C`（`:639`）。どれも「着地が shift なら source も shift」というモードの事実を足せば直る形。`ShadowedLocalFinal` 側は `localGood_of_pol_eq` の呼び出し（関数 step 7 個＋到着）と `replayStartNext` の `Good`（着地は scan なので `cycle` の要求は空虚）。必要になる補題: 関数 step ごとの「着地のモード」（`shiftStepW` は ctl 不変か `shiftDoneCtlW` で scan、`copyStepL`／`homeStepL`／`markEndStepL`／`chooseStepW`／`rewindStepW`／`ffppW`／`initStep`）と、`TickL3 x y → y.ctl.mode = .shift → x.ctl.mode = .shift`（`cases`）。

**道 A の残り作業の一覧（2026-09-21 時点、見積もりは付けない）**: (1) chain 側の `last` の `Canonical` を trace に沿って示し、`AllCanonical` の `restart` を閉じる、(2) 極性の要る 7 本（remaining／radius／length／cycle／fppWork／work／replay）の非負性を trace から、(3) 切断本体（`viewOfHead`＋`ctrOf`＋`viewOfPlace`＋`mirrorOfTape`＋バッファ）と `abs''` の等式・`Inv`、(4) replaying の着地の右ヘッド（source の駐車 view を引き継ぐ）、(5) `NextOK` の `Canonical`（trace の canonical な次状態の truncation を具体化）、(6) `scanNext`／`plateauNext` の組み立てと仮説の除去。

3. replaying の着地では `abs''.right = left^[rval] physHead`。非 replaying の着地は `viewOfPH target.right`、replaying の着地は source の駐車 view を引き継ぐ（replay の tick は物理 right を動かさず `rval` が 1 減るだけ、`LocalReplayParked §3`）。
4. `NextOK` の `Canonical`: 仮説が与える `target` は canonical とは限らない（restart guard が立っているときの `scan_wait` など）。後継は trace の canonical な次状態（`st (k+1)` の truncation）を具体化したものにする。`GalilTruncTick` の「tick は truncation と可換」と、`CanonicalLocalRealizes.realizes_canonical` が何を要求しているかを読む。
5. fpp walker の番兵（`PhysWF.walkerProper`）: `viewOfPlace` の出力が `ProperView` か。

**物理側への含意（隠さない）**: ghost が「抽象状態の切断」になると、抽象局所層は証明上の媒介にすぎなくなり、実質の内容は物理機械の側（`Enc`、`hforwardTick` ほか 9 本、ActRule の実装）に集まる。ここは未着手のまま。

## n315（2026-09-21）: tracked な replayStart 状態に局所後継があることを証明した。仮説 `hreplayStartNext` が消えた

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: `given_openModesAndPhysicalMachine` の仮説 `hreplayStartNext` が無くなり、定理 `ShadowedLocalFinal.replayStartNext` になった。
* 新モジュール `PalPeg/ReplayStartGhost.lean`（`ShadowedLocalFinal` が import、`Workbench` 経由でルートに入る）。
  * trace 側: `RewindCentre`（rewind／replayStart で `center = left^[r] right`、`radius = ofNat r`）、`rewindCentre_tick`、`rewindCentre_trace`、`notReplaying_of_tick_into_replayStart`（着地は `rewind_done` だけ。`LocalWF.PhaseMode` に replayStart が無いので既存の `NoReplay` からは直接出ない）。
  * ghost 側: `mirrorOfTape`、`replayCommitVm`（`LocalTick2.commitReplay`＋`left := center`＋鏡 3 本を新しいテープに付け直し）、`countersShaped_commitReplay`、`inv_replayCommitVm`、`replayStartVM_replayCommitVm`（`MirInv1` の仮説は不要）、`parkedOK_replayCommitVm`。
  * `replayStartVM_unique`（15 場を全部固定するので着地は一意）、`truncPH_left_iterate`。
* 組み立て `replayStartNext`: `hinv.track` から trace の添字を取り、`rewindCentre_trace`・`radLedger_pt`・`noReplay_run` で `hland`／`hradiusLe`／`hnotReplaying` を tracked 状態に運び、既存の `GalilTickFair.tick_replayStart_cases` で `htarget` を分解、一意性で `abs'' next.vm = landing`。`NextOK` の 6 場を埋める（`Good` は `radius`／`replay` の極性入れ替え、`Post` は `notFrozen_of_invC`）。
* **形式化のミスだった点**: 既存の `commitReplay` は役割を入れ替え・reset・push するのに鏡 `radiusMir`／`lowerMir`／`lengthMir` に触らず、局所層自身の不変量 `LocalTick1.Inv`（`MirrorsAttached`）を保たなかった（n313）。replayStart の局所 step は一度も `Inv` と突き合わされていなかった。
* 進め方の記録: 部品を 1 つずつスクラッチで機械検査し（n311〜n314）、最後に束ねてから移設した。移設は 2 ファイルとも一発で通った。つまずきは「構造体リテラルを 2 行に割ると parse error」が 3 回。

**`given_openModesAndPhysicalMachine` に残る仮説**: 供給可能（`hfirst`／`hq`／`hor`／`hres`／`hChainVerifierSupply`）、抽象局所層は存在仮説 2 本（`hscanNext`、`hplateauNext`）、物理機械（`htape`、`Enc`、`hencInit`、`hforwardTick`、`hforwardFeed`、`hencRep`、`hencOut`、`PhysFrozen`、`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`）。ActRule の実装は未着手。物理側に置いた義務: fallback 相の L／C の歩行（n305）、reset 後の junk を読まないこと（n306、n312）、replayStart の鏡テープ付け替え（n315）。

**次の goal**: `hscanNext`（tracked・非 starved な scan 状態に局所後継がある）。scan は wait／count／match／restart／shift 入口／fallback 入口の分岐を持つ。replayStart と同じ手順で、まず抽象の着地がどこまで一意か（`GalilTickFair.tick_canonical_unique`）と、既存の `LocalTick1.TickL1`／`LocalReplayParked` の scan 部品がどの分岐を覆っているかを一次情報で確かめる。

## n314（2026-09-21）: run 不変量 `localGood` に `work`／`replay` の極性を足し、保存を証明した

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。仮説 `hreplayStartNext` もまだ残っている） |

**やったこと**（n311 の計画の (b)）: `ShadowedLocalFinal.localGood m := PolWF m.vm ∧ m.vm.pol .work = true ∧ m.vm.pol .replay = true`。replay commit は `work` を push し（`hpw`）、`LocalRoles.movePol Ctr.radius Ctr.replay` で `radius` と `replay` の極性を入れ替えるので、commit 後も `PolWF` を保つにはこの 2 本が要る（n313）。
* 補題 `localGood_of_pol_eq`（極性に触らない step は不変量を保つ）。保存 3 箇所: 関数 step（`localGood_stepOf_localSteps`、init は `work → true`・`replay` 不変）、到着（`LocalWF.pol_feedC`）、blank（`LocalBlankState.blankVML` は `pol := fun _ => true` なので `rfl`）。`H_wf` へは `hinv.good.1`。
* **強くなった仮説（隠さない）**: 存在仮説 `hscanNext`／`hreplayStartNext`／`hplateauNext` は `Good next` を含むので、このぶん強くなった。

**残り**: (a) `RewindCentre` の trace 形（Tick 保存は n311 のスクラッチで検査済み）、(d) ghost の replayStart 後継で `NextOK`（鏡 3 本 `radiusMir`／`lowerMir`／`lengthMir` の更新込み、n313）。

**(d) の `Inv` はスクラッチで機械検査済み（2026-09-21、リポジトリには未投入・`NextOK` の producer と一緒に入れる）**。error 0、標準 3 公理。
* `mirrorOfTape t : Mirrored k := ⟨t, fun _ => t⟩`（テープそのものの複製。`attached` は `rfl`、`Shaped` は `⟨hv, fun _ => hv⟩`）。
* `replayCommitVm entry c x := let y := LocalTick2.commitReplay entry x; { y with left := x.center, ctl := c, radiusMir := mirrorOfTape (y.phys (y.roles .radius)), lowerMir := …(.lower), lengthMir := …(.length) }`。
* `CountersShaped (commitReplay entry x)`: `intro c`、`hshaped (LocalRoles.swapAt Ctr.radius Ctr.replay c)` を取り、`show` で `pushSlots _ (resetSlots _ x.phys) (x.roles (swapAt … c))` の形を出して `unfold pushSlots resetSlots`、`by_cases` 2 段で `segCtr_push`／`segCtr_reset`。
* `Inv (replayCommitVm entry c x)`: `⟨LocalRoles.moveRoles_injective hinv.roles, ⟨rfl, rfl, rfl⟩, ⟨views.2.1, views.2.1, views.2.2.1, views.2.2.2.1, views.2.2.2.2⟩, 鏡 3 本の Shaped, hshaped⟩`。
* スクラッチの場所（セッション限り）: `$S/ghost_check.lean`、`$S/rc_check.lean`（`RewindCentre` の Tick 保存）。

**抽象の等式もスクラッチで機械検査済み（2026-09-21、同じ `$S/ghost_check.lean`）**: `replayStartVM entry (abs'' x) (abs'' (replayCommitVm entry c x))`。仮説は `hinj`／`hpl`／`hpw`／`hpre : x.ctl.replaying = false`／`hflag`／`hland` で、`replayStartVM_commitReplayParked` にあった `hm : MirInv1` は不要（`left := x.center` が `rfl`）。形: `rval (replayCommitVm …) = rval (commitReplay …)` は `rfl`、あとは `rval_commitReplay`、`absR_eq_iter`、`abs''_eq_abs' hpre`、`refine ⟨?_, hR, rfl, rfl, …⟩`、残り 11 場は `show (LocalState.abs (LocalTick2.commitReplay entry x)).場 = _; rw [ha]; try rfl`（`rw` が自分で閉じる場があるので `try`）。

**`ParkedOK (replayCommitVm entry c x)` もスクラッチで機械検査済み**（同じファイル、error 0、標準 3 公理）: 仮説は `hinj` と `hradiusLe : val (x.phys (x.roles .radius)) ≤ position (abs' x).right`。後者は trace の `CloseoutRadPack.RadLedger.le`（`position center + value radius ≤ position right`、`CloseoutLPack6.radLedger_pt`）から。これで ghost 側の部品 3 つ（`Inv`・抽象の等式・`ParkedOK`）は揃った。

**trace 側の部品 2 つもスクラッチで機械検査済み（2026-09-21）**:
* `$S/rc_check.lean`（控え `rc_check.keep.lean`）: `RewindCentre` の Tick 保存に加えて trace 形 `∀ i, i ≤ Tc w.length → RewindCentre (st i).ctl (st i).vm`（`PreTrace` に沿う帰納。boot は `hP.start` で mode = init なので `Mode.noConfusion`、step は `hP.trace.tick i hlt`）。error 0、標準 3 公理。
* `$S/nr_check.lean`（控え `nr_check.keep.lean`）: `LocalWF.NoReplay x → Tick F delay x y → y.ctl.mode = .replayStart → y.ctl.replaying = false`。`LocalWF.PhaseMode` に replayStart が入っていないので既存の `NoReplay` からは直接出ない。`cases` で残るのは `rewind_done` だけ（制御は mode 以外不変）で、source の `NoReplay`（rewind は `PhaseMode`）から出る。公理は `propext` のみ。
* 組み立てで使う既存補題: `GalilThrottledRun.position_trunc`（`position (truncPH d p) = position p := rfl`）、`GalilTruncTick.truncPH_left`、`ShadowedLocalFinal.notFrozen_of_invC`（`hw : 0 < w.length` を取る）。

**組み立てのスクラッチ（2026-09-21、`$S/asm_check.lean`、控え `asm_stage2.keep.lean`）**: `import PalPeg.ShadowedLocalFinal` の上に部品 3 ファイルを束ね、`scratch_replayStartNext`（`hreplayStartNext` の本体と同じ文、`hw : 0 < w.length` つき）を段階的に書いている。通った段（末尾の `sorry` 1 つを除き error 0）:
1. `hinv.track` から `k j`、`hctl`、`hvm`（`unfold heldAfter` で添字は `min k (Tc w.length)`）、`hmodeTrace`、`RewindCentre` の trace 形から `r`／`hradiusTrace`／`hcentreTrace`、`CloseoutLPack6.radLedger_pt`（＋`leftLive_of_lpackM (hpreTrace.packs i hi).pack`）。
2. `hnotReplaying : m.vm.ctl.replaying = false`: `LocalWF.noReplay_run` を `heldAfter` に当て（消費者と同じ引数）、添字 0 は boot で `Mode.noConfusion`、正なら `Nat.exists_eq_succ_of_ne_zero` で 1 つ前を取り `scratch_notReplaying_of_tick_into_replayStart`。

3. （控え `asm_stage3.keep.lean`）`rw [abs''_eq_abs' hnotReplaying] at hvm` のあと、`hradiusEq`／`hrightEq`／`hcentreEq`（`(congrArg GalilVM.場 hvm).trans rfl`）、`hradiusVal : val (radius のテープ) = r`（`LocalWF.value_absCtr_of_positivePolarity`＋`hinv.good.1.2.1`＋`simp [value, ofNat]`＋`omega`）、`hland`（補題 `scratch_truncPH_left_iterate`: `left^[r] (truncPH d p) = truncPH d (left^[r] p)`、`truncPH_left` の帰納）、`hradiusLe`（`hradLedger.le` を `rw [hradiusTrace]` して `omega`、`position (truncPH d p) = position p` は `show` で defeq）。

4. （控え `asm_done.keep.lean`、358 行）**第 4 段も通り、`scratch_replayStartNext` が最後まで証明できた**（`EXIT=0`、`sorry` の警告 0、`#print axioms` は標準 3 公理のみ）。`GalilTickFair.tick_replayStart_cases`（既存）で `htarget` を分解、`replayPos landing` を `landingReplaying` に名前で取って制御リテラルを 1 行に（**構造体リテラルを 2 行に割ると parse error**）、`hflag` は `cases r`、`scratch_replayStartVM_unique`（`unfold replayStartVM at h h'; cases t; cases t'; simp_all`）で `abs'' next.vm = landing`。`NextOK` の 6 場: Tick は `suffices ∀ landed, landed = target → Tick … landed` の形で `congrArg (State.mk _) hnextVm`、`Canonical` は mode で 2 場が空虚・`keepsSearchCursor` は `replayStartVM` の最後の 2 連言、`PhysWF` は `⟨inv, parkedOK, hinv.phys.pend, hinv.phys.walkerProper⟩`、`MirInv1` は `⟨Twin.refl _, views.2.1⟩`、`Good` は `radius`／`replay` の極性を入れ替えて `⟨⟨hremaining, hreplay, hlength, hcycle, hfppWork⟩, hwork, hradius⟩`、`Post` は左枝が mode で偽・右枝は `notFrozen_of_invC`。

**次にやること**: スクラッチの宣言をリポジトリへ移し（`scratch_` を外して意味のある名前に。trace 側は `CloseoutRadPack3` の近く、ghost 側は `LocalReplayParked`、組み立ては `ShadowedLocalFinal`）、`given_openModesAndPhysicalMachine` の仮説 `hreplayStartNext` を外して呼び出し箇所（`:1190` 付近）を定理に差し替える。呼び出し箇所で `hw : 0 < w.length` が scope にあるかを確認する。

**(d) の旧メモ**（第 4 段の計画、済）: `hreplayStartNext` の組み立て（`htarget` を `cases`、`replayStartVM` の一意性、`truncPH_left` で `hland`、`hflag` は `target.ctl.replaying = replayPos` から）。

## n313（2026-09-21）: `hreplayStartNext` の producer (d) の設計（調査のみ、コードは変えていない）

**全体 build 成功（最新は n312 の `BUILD=0`）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（未接続） |

一次情報で確かめたこと:
* `Tick.replayStart`（`GalilScaffoldTop:166`）の着地は `⟨{c with mode := .scan, clock := delay, output := o, replaying := F.replayPos s'}, s'⟩` で `F.replayStart s s'`。`replayStartVM entry s t`（`GalilScaffoldTopReplay:33`）は 15 場を全部固定する**関数的な関係**なので、抽象の着地 `s'` は source から一意。
* `GalilTickFair.Canonical`（`:224`）が replayStart の tick に課すのは `keepsSearchCursor`（`periodOnly`／`walker` を保つ）だけで、`replayStartVM` の最後の 2 連言そのもの。
* `GalilTruncTick.truncPH_left`（`:32`）は無条件。よって trace の `center = left^[r] right` は `truncVM` を越えて `abs'' m.vm` に運べる（`hland` の供給）。
* `replayStartVM` の一意性補題は既存に無い（`GalilVM` に `ext` が登録されていないので `cases` して場ごとに示す）。

**(d) の設計**: 仮説が与える `htarget : Tick … (absState'' m.vm) target` を `cases` して `replayStartVM entry (abs'' m.vm) target.vm` と `target.ctl` の形を取り出す。ghost の後継は `next := ⟨{ commitReplay entry m.vm with left := m.vm.center, ctl := target.ctl }, m.vm.center⟩`（view のコピー、n305 と同じ手）。示すもの:
1. `abs'' next.vm` が `replayStartVM entry (abs'' m.vm) ·` を満たす（`replayStartVM_commitReplayParked` の証明を `left := center` 用に直す。`hm : MirInv1` は不要になる）→ `Tick.replayStart` を組み直して `NextOK` の Tick、`Canonical` は最後の 2 連言。
2. `PhysWF next.vm`: `Inv`（`commitReplay` 後の `roles`／`attached`／`shaped` — 既存補題の有無を要確認）、`ParkedOK`（`parkedOK_commitReplayParked`、`val radius ≤ position right` は `RewindCentre` から）、`pend`、`walkerProper`（`fppWalker` 不変）。
3. `MirInv1 next`: `Twin.refl`＋`WF center`。
4. `Good next`: `commitReplay` は `movePol Ctr.radius Ctr.replay` で極性を入れ替えるので、`PolWF` の `radius` を保つには入れ替え前の `pol .replay = true` が要る見込み。`localGood` に `.work` と `.replay` を足す必要があるかを `movePol` の定義で確かめる。
5. `Post w m → Post w next`: `postPhase` の左枝は `mode = scan` を要求するので、replayStart の source では前件が偽になるはず（要確認）。

**未確認 3 点を定義で潰した（2026-09-21 追記）**:
* **極性**: `LocalRoles.movePol src dst pol ℓ = pol (swapAt src dst ℓ)`（`:107`）。`commitReplay` は `movePol Ctr.radius Ctr.replay` なので、commit 後の `pol .radius` は commit 前の `pol .replay`。`PolWF` を保つには `pol .replay = true` が要る。`hpw` のために `pol .work = true` も要る。→ (b) は `localGood m := PolWF m.vm ∧ m.vm.pol .work = true ∧ m.vm.pol .replay = true`。phase step の極性補題は `pol` 全体の等式なので保存は同じ証明、`initVml` は `length`／`work` を `true` にして他は不変、blank の `pol` は要確認。
* **`postPhase`**（`ShadowedLocalFinal:836`）の左枝は `(absSC m).ctl.mode = Mode.scan` を要求するので replayStart の source では偽。右枝 `frozenAt w m` のときは `hreplayStartNext` の前件 `InvC` と `notFrozen_of_invC` で排除できる。
* **`Inv`（これが重い）**: `LocalState.MirrorsAttached`（`:169`）は `radiusMir.src = phys (roles .radius)`、`lowerMir.src = phys (roles .lower)`、`lengthMir.src = phys (roles .length)` を**テープの等式**で要求する。`LocalTick2.commitReplay` は役割を入れ替え、`replayCleared` のテープを reset し、`length`／`work` を push するのに、`radiusMir`／`lowerMir`／`lengthMir` に触らない（`initVml` は `lengthMir := pushAll` をしている）。よって `commitReplay` の着地は `LocalTick1.Inv` を保たない。`Inv (commitReplay …)` の既存補題も無い（あるのは `LocalAlloc.allocInv_commitReplay` と `LocalReplaySwap.mirInv_commitReplay` だけ）。ghost の後継は鏡 3 本も新しいテープに合わせて更新する形にし、`Shaped` を示す必要がある。

**順序**: (a) `RewindCentre` の trace 形 → (b) `localGood` の拡張 → (d)。どれも (d) が入って初めて消費者につながるので、1 回の作業でまとめて入れる。

## n312（2026-09-21）: replayStart の commit が `dpBuf` を新品の半分へ切り替える。4 本の定理から `hclean` が落ちた

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路は未接続。仮説 `hreplayStartNext` もまだ残っている） |

**やったこと**（n311 の計画の (c)）: `LocalTick2.commitReplay` の `dpBuf := resetL` を `LocalBuffers.resetFresh` にして、`abs_commitReplay`／`replayStartVM_commitReplay`／`LocalReplaySwap.replayStartVM_commitReplaySwap`／`LocalReplayParked.replayStartVM_commitReplayParked` から仮説 `hclean`（`dpBuf` の idle 半分が消去済み）を外した。n306 と同じ型: 背景消去 `clearTick` はどの局所 step も回していないので、2 回目の replayStart から成り立たない要求だった。`stepLocal2_commitReplay` は外に消費者が無く、fresh な切替は局所 step ではないので削除。
* 同じ形が `LocalTick2.commitFallback`（`fppBuf`、`:806` 付近）と restart 側（`:351`、`RestartStaged.clean`）に残っている。新経路の scan は `chosenStep`（存在仮説）なので今は消費者に出ていない。
* 失敗と修正: python の削除範囲が 1 段落広く `section ReplayAbs` の開始行まで消した。コンパイルエラー（`Invalid name after end`）で気づき、`git diff` で確かめて戻した。

**残り**（n311 の計画）: (a) `RewindCentre` の trace 形、(b) `localGood` に `pol .work` を足す、(d) ghost の replayStart 後継（`left := center`、`mirL := center`）で `NextOK` を示して `hreplayStartNext` を外す。

## n311（2026-09-21）: `hreplayStartNext` の分解（調査のみ、コードは変えていない）

**全体 build 成功（最新は n310 の `BUILD=0`）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（未接続） |

`hreplayStartNext` は tracked・非 starved な replayStart 状態 `m` に `∃ next, NextOK … m next` を求める。`NextOK`（`ShadowedLocalFinal:670`）= `Tick (absState'' m) (absState'' next)` ∧ `Canonical` ∧ `PhysWF next.vm` ∧ `MirInv1 next` ∧ `Good next` ∧ `(Post w m → Post w next)`。

既存の `LocalReplayParked.replayStartVM_commitReplayParked`（`:366`）を一次情報で読んだ結果、そのままでは使えない点が 4 つ:
1. **`MirInv1 next` が直後に成り立たない。** `commitReplayParked` は `left := mirL`、`mirL := 旧 left`。旧 `left` は `center` の twin ではない（Scala の run: rewind 末 `L=4 C=5 R=6`）。ghost は自由なので、n305 と同じく ghost の後継は `left := m.vm.center`、`mirL := m.vm.center`（view のコピー）にすれば `Twin.refl` で済む。鏡の再構築は `Enc` の側。
2. **`hclean`（`dpBuf` の idle が消去済み）。** n306 と同じ型。`LocalTick2.commitReplay` の `resetL` を `resetFresh` に替える（`commitReplay` は `LocalReplaySwap` も使うので波及を build で確かめる）。
3. **`hpw : pol .work = true`。** `PolWF` は `remaining`／`radius`／`length`／`cycle`／`fppWork` の 5 本で `.work` を持たない。`initVml` が `.work` を `true` にするので、`localGood` に足して運ぶ（極性補題は `pol` 全体の等式なので保存は同じ証明で済む）。
4. **`hland : left^[val radius] (abs' right) = (abs' center)`。** 今の trace pack には無い（`CentreRep` は表現だけ）。新しい trace 不変量「mode ∈ {rewind, replayStart} → `center = left^[value radius] right` ∧ `Canonical radius`」が要る。Tick の場合分けで保たれる形: `choose_select` で `center = right`・`radius = reset`、`rewind_pair` で `center := left center`・`radius++`、`rewind_one`／`rewind_done` は両方不変。`GalilScaffoldTopRewind:195` に rewind 内の run 形（`y.center = left^[m/2] x.center ∧ y.right = x.right`）が既にある。

**4 の Tick 保存はスクラッチで機械検査済み（2026-09-21、リポジトリには未投入・producer と一緒に入れる）**: `RewindCentre c s := c.mode = .rewind ∨ c.mode = .replayStart → ∃ r : ℕ, s.radius = ofNat r ∧ s.center = left^[r] s.right`、`RewindCentre c s → Tick (galilFrameS Pw q first) delay ⟨c, s⟩ ⟨c', t⟩ → RewindCentre c' t`。error 0、公理 `propext`／`Quot.sound`。形: `cases h <;> first | (intro hmode; exfalso; simp_all; done) | skip` で `choose_select`／`rewind_done`／`rewind_one`／`rewind_pair` の 4 つだけ残る。どれも `obtain ⟨hstep, hframe⟩ := hrel`（`rewind_one`／`rewind_pair` は `⟨⟨_, hstep⟩, hframe⟩`）、`rw [hstep] at hframe; subst hframe`。`choose_select` は `⟨0, rfl, rfl⟩`、`rewind_pair` は `⟨r + 1, by rw [hradius, GalilScaffoldCounter.inc_ofNat], by rw [Function.iterate_succ_apply', ← hcentre]⟩`（先に `show` で形を出す）、他 2 つは `⟨r, hradius, hcentre⟩`。抽象規則は `GalilScaffoldTopRewind:56–62` で確認済み（`right` はどれも触らない）。

**次の goal**: producer を一式で入れる。順に (a) trace 形（`PreTrace` に沿う、boot は mode = init で空虚、harness は `CloseoutRadPack3.coupledPack_trace`）、(b) `localGood` に `pol .work` を足す、(c) `LocalTick2.commitReplay` の `dpBuf` を `resetFresh` に、(d) ghost の replayStart 後継（`left := center`、`mirL := center`）で `NextOK` を示して `hreplayStartNext` を外す。

## n310（2026-09-21）: 関数である step（init と 7 つの phase）が極性の束を保つことを証明した。仮説 `hgoodPhaseStep` が消えた

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: `given_openModesAndPhysicalMachine` の仮説 `hgoodPhaseStep` が無くなった。`ShadowedLocalFinal.localGood_stepOf_localSteps`: `localGood m`、`mode ≠ scan`、`mode ≠ replayStart` から、`localSteps q first (initStep entry) scanStep replayStartStep` の step 後も `localGood`。仮説は tracked・非 starved を付けていたが、どの状態でも成り立つので条件ごと落とした。
* 材料は全部既存: `LocalWF.pol_copyStepL`／`pol_homeStepL`／`pol_markEndStepL`、`ffppW = ffpp dumS` なので `pol_ffpp dumS`、`chooseStepW`／`rewindStepW` は C 版と `rfl` で等しいので `pol_chooseStepC`／`pol_rewindStepC dumS`、`shiftStepW` は `pol_shiftStepL` と同じ形、`LocalInitStep.initVml` は `length`／`work` の極性を `true` にするだけ。
* 学び: `Ctr` は `PalPeg.LocalState.Ctr`。

**`given_openModesAndPhysicalMachine` に残る仮説**: 供給可能（`hfirst`／`hq`／`hor`／`hres`／`hChainVerifierSupply`）、抽象局所層は存在仮説 3 本（`hscanNext`／`hreplayStartNext`／`hplateauNext`、各々 `∃ next, NextOK …`）、物理機械（`htape`、`Enc`、`hencInit`、`hforwardTick`、`hforwardFeed`、`hencRep`、`hencOut`、`PhysFrozen`、`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`）。ActRule の実装は未着手。

**次の goal**: `hreplayStartNext`（tracked・非 starved な replayStart 状態に局所後継が存在する）。`LocalReplayParked.commitReplayParked`（§5、`left := center` は鏡 `mirL` を消費、`right` は駐車）が既にあるので、`NextOK` の各場（`Tick` の後継の抽象一致、`PhysWF`（`walkerProper` 込み）、`MirInv1`、`localGood`）を満たすかを定義で確かめる。`dpBuf` の reset は `resetL`＋`hclean` の形のままなので、n306 と同じ `resetFresh` への切替が要る見込みかどうかも一次情報で確認する。

## n309（2026-09-21）: shift 単位のカウンタの大きさを trace から証明した。仮説 `hgeomTracked` が消費者から丸ごと消えた

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: `given_openModesAndPhysicalMachine` の仮説 `hgeomTracked` が無くなった。構造 `LocalWF.Geom` と `geom_of_init` は削除、`LocalWF` は極性の束 `pol` だけ。
* 正本との突き合わせ: `ScaffoldGalil.stepShift`（`:324`）は符号付きカウンタを `dec()` するだけで `radius > 0` は要求しない。要求しているのは局所層（正の極性の側で pop する設計、`LocalTick3.ShiftCounters`）。
* `LocalWF.value_absCtr_of_positivePolarity`、`LocalWF.shiftMagnitudes_of_trace`: tracked な shift 状態で `RemPosL` なら `0 < val remaining ∧ 0 < val radius ∧ 2 ≤ val length`。copy 側は trace で idle、`remaining ≤ radius`、`length = 2·radius + 1`、`truncVM` はカウンタと `fpp` に触らない。
* trace 形の仮説 `H_shiftLedgerOnTrace` を `realizes_seven` 系 3 本に通し、`ShadowedLocalFinal` で放電: `CloseoutRadPack3.copyIdle_trace`、`CloseoutLPack6.radLedger_pt`（＋`CloseoutPackRun10.leftLive_of_lpackM`）の `shiftBud`、`BranchSupply.spanRepOnScanAndShift_alongTrace`。新しい仮説は残っていない。

**今日の `Geom`: 5 場 → 0**（n305 `chooseParked`／n306 `rewindClean` は偽の疑いが濃い仮説を形式化を直して外し、n307 `copyProper`／n308 `copyWork`／n309 `shiftMag` は本物の事実を証明して外した）。

**`given_openModesAndPhysicalMachine` に残る仮説**: 供給可能（`hfirst`／`hq`／`hor`／`hres`／`hChainVerifierSupply`）、抽象局所層（`hgoodPhaseStep`、`hscanNext`／`hreplayStartNext`／`hplateauNext`）、物理機械（`htape`、`Enc`、`hencInit`、`hforwardTick`、`hforwardFeed`、`hencRep`、`hencOut`、`PhysFrozen`、`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`）。物理側に置いた義務: fallback 相の間の L／C の歩行（n305）、reset 後の junk を読まないこと（n306）。

**次の goal**: `hgoodPhaseStep`（極性が init と 7 つの phase step で保たれる）。`pol_tickL3`／`pol_chooseStepC`／`pol_feedC` は既にあるので、`SL` の各 step 関数について同じ形が揃うかを確かめる。

## n308（2026-09-21）: copy の work カウンタの正値を trace から証明した。`Geom.copyWork` を消費者から外した

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: 仮説 `hgeomTracked` から場 `copyWork`（copy モードで `RemPosL` なら `0 < val (phys (roles .fppWork))`）が消えた。`Geom` は 1 場（`shiftMag`）。状態仮説（producer なし）を trace 形の仮説に置き換え、その仮説を消費者の中で放電したので、新しい仮説は残っていない。
* `LocalWF.val_fppWork_pos_of_copyRemaining`: 抽象の `fpp.work` が 0 でない ⇒ 局所テープの `val > 0`（`absCtr` は極性に依らず `val = 0` で zero）。
* `LocalWF.copyRemaining_of_trace`: tracked な copy 状態では `RemPosL` は copy 側。`truncVM` はカウンタに触らない（`rfl`）。
* `realizes_seven`／`CloseoutCoreStep.realizes_seven_of_agree`／`CloseoutCoreAgree.realizes_seven_SL` に trace 形の仮説 `H_shiftIdleInCopy : ∀ k, (stOf k).ctl.mode = .copy → ¬ ShiftRemaining (stOf k).vm` を通し、`ShadowedLocalFinal` で `BranchSupply.cpack_alongTrace` の `GalilCentreLive.CPack.idle`＋`GalilScaffoldChainInputSupply.shiftIdle_iff` から放電。添字 0 は boot（mode = init、`Mode.noConfusion`）、`Tc` 以降は `heldAfter` の `min`。
* 学び: 自由変数を含む goal に `decide` は使えない（`Expected type must not contain free variables`）。

**今日の `Geom`**: 5 場 → 1 場。`chooseParked`（n305）と `rewindClean`（n306）は偽の疑いが濃い仮説を形式化を直して外し、`copyProper`（n307）と `copyWork`（n308）は本物の事実を証明して外した。

**次の場 `shiftMag`**: `mode = shift → RemPosL x → 0 < val remaining ∧ 0 < val radius ∧ 2 ≤ val length`。`remaining` は n308 と同じ橋（`ShiftRemaining` ⇒ `val > 0`、cross case は `CloseoutRadPack3.copyIdle_trace`）。`radius > 0` と `2 ≤ length` は trace の `CloseoutPackRun23.ShiftGeom`／`SpanRep`（`value length = 2·value radius + 1`）を定義で確かめてから。

## n307（2026-09-21）: fpp walker の左番兵を run に沿って証明した。`Geom.copyProper` を消費者から外した

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: 仮説 `hgeomTracked` から場 `copyProper`（copy モードで `ProperView x.fppWalker`＝view の左端に番兵 `none` がちょうど 1 個）が消えた。`Geom` は 2 場（`shiftMag`／`copyWork`）。n305／n306 と違い、これは偽だから外したのではなく**本物の局所不変量を証明して外した**。
* `LocalSysConcrete.PhysWF` に場 `walkerProper : ProperView x.fppWalker` を追加。`LocalState.absPlace` が番兵を落とすので `InvC` からは出ない。`LocalTick1.Inv` に足さなかったのは、探索量子の frame 仮説 `SearchFrame.inv` まで強めてしまうから。
* 保存: `walkerProper_tickL3`（`cases` して copy だけ `properView_moveLeftV`、他は不変）、`birthL_fppWalker`＋`fppWalker_tickL1`（scan tick は walker に触らない、`frame.fppWalker`）、`physWF_feedC`（`arrive` は `far` しか触らない）、`physWF_initStep`、blank は `LocalBlankState.walkerProper_blank := rfl`。`x0C_physWF` と `pal_in_peg_of_shadowed_sysC` は blank の仮定 `hblankWalkerProper` を取り、`ShadowedLocalFinal` が `walkerProper_blank` を渡す。
* **強くなった仮説（隠さない）**: 存在仮説 `hscanNext`／`hreplayStartNext`／`hplateauNext` は `PhysWF next.vm` を含むので `walkerProper` のぶん強くなった。fallback 入口で `walker := R`（Scala `:314`）にする後継は `right` の view の anchoring が要る。

**次の場 `copyWork` の調査（読み取りのみ）**: `RemPosL = ShiftRemaining ∨ CopyRemaining`。cross case（copy モードで shift 側 `remaining > 0`）は trace 上で `GalilCentreLive.CPack.idle : c.mode ≠ Mode.shift → ShiftIdle s`（`BranchSupply.cpack_alongTrace`）が排除する。`GalilChainCoupling.CopyPack` は逆向き（copy 以外で `CopyIdle`）なので使えない。足りないのは「抽象 `fpp.work` が 0 でない ⇒ 局所テープの `val > 0`」の橋（`LocalTick3:525` は仮定で受けているだけ）。形: 状態仮説 `Geom.copyWork`（producer なし）を、trace 形の仮説「copy モードの trace 点で `ShiftIdle`」（producer あり）に置き換えて `ShadowedLocalFinal` で放電する。

## n306（2026-09-21）: rewind の reset が ghost で新品の半分へ切り替わる。`Geom.rewindClean` を消費者から外した

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: 仮説 `hgeomTracked : InvC … m → Geom m.vm` から場 `rewindClean`（rewind モードで fpp 二重バッファの idle 半分が消去済み）が消えた。`Geom` は 3 場（`shiftMag`／`copyWork`／`copyProper`）、`RewindWF` は 3 場。
* **なぜ偽の疑いが濃かったか**（`False` 定理は未作成）: 局所 step（`TickL1/2/3`、`LocalSysConcrete`）のどれも `LocalBuffers.clearTick` を回していない（`LocalTick2:896` 自身が「assumed, not scheduled」）。1 回目の `resetL` で idle に回った半分は消されないので、fallback が 2 回以上ある語（`abab` は 3 回）の 2 回目の `rewind_done` で成り立たない。
* **直し方**: `LocalBuffers.resetFresh`（新品の半分へ切替）と `abs_resetFresh`（無条件）。`rewindDoneVm`／`abs'_rewindDoneVm`／`TickL3.rewind_done` から `hclean` を削除。`tickL3_local` に `hnotReset`、消費者を失った `stepLocal_rewindDoneVm` は削除。handoff の指定（junk をその場で消さない、`TEqG`＝同じ head 位置・同じ読取りで運ぶ）に合わせた。物理側は active の反転だけで、junk を読まないことは `Enc` の側の義務。
* **不採用**: `clearTick` を各 step に入れて締切を証明する案。消去は距離ぶんの tick が要るが、次の reset は 1〜2 文字後に来うる（`a^n b a b`）。半分を k 本に増やしても、半径が毎回縮む列で未完了ジョブが溜まるので固定本数では足りない。
* `LocalTick2.commitFallback` と `commitReplay`（`dpBuf`）にも同じ `resetL`＋`hclean` の形が残っている。新経路の scan／replayStart は `chosenStep`（存在仮説）なので今は消費者に出ていない。

**次の場 `copyProper` の調査（読み取りのみ）**: `ProperView x.fppWalker`＝view の左端に番兵 `none` がちょうど 1 個。これは前の 2 つと違って**本物の局所不変量**。`LocalState.absPlace` が番兵を落とすので `InvC` からは出ない。仮説で受けるのでなく、run に沿って運ぶ束（`Inv.views`／`ViewsWF`、`tickL*_inv` で保存が証明済み）に入れるのが筋。既存の保存補題は左移動だけ（`LocalChain.properView_stepLeft`／`properView_moveLeftV`）。fppWalker を動かす局所 step は copy（`moveLeftV`）と到着（`arrive`）だけ。fallback 入口の `walker := R`（Scala `:314`）は scan の `chosenStep` の中に隠れているので、`right` の view の anchoring も要る。

## n305（2026-09-21）: choose の select が ghost でヘッドをコピーする。`Geom.chooseParked` を消費者から外した

**全体 build 成功（`BUILD=0`、error 0、sorry 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本）。`unconditional` は付け替えていない。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（局所経路 `ShadowedLocalFinal.given_openModesAndPhysicalMachine` は未接続） |

**証明して消費者へ接続したこと**: `given_openModesAndPhysicalMachine` の仮説 `hgeomTracked : InvC … m → Geom m.vm` から、偽の疑いが濃かった場 `chooseParked`（choose モード中ずっと `left = right`、`center = right`）が消えた。`Geom` は 4 場（`shiftMag`／`copyWork`／`copyProper`／`rewindClean`）、`ChooseWF` は 2 場（`notReplaying`／`polLength`）。
* `LocalTick3.chooseSelectVm c x := { chooseVm c x with left := x.right, center := x.right }`、`abs'_chooseSelectVm`（`hleft`／`hcenter` 無しで抽象 `choose` に一致。`hsplit` が `rfl`、あとは `abs'_bankTick` 2 回）。`TickL3.choose_select` の着地をこれに一般化。`tickL3_local`（`StepLocalN`、外に消費者なし）は `hnotSelect` 付き。
* `LocalRealizesScan.chooseSelectM m`（`mirL := m.vm.right`。鏡は新しい `center` の twin）を `chooseStepC`、`CloseoutCoreAgree.chooseStepW`、旧 encoder `CloseoutCoreEnc8/9/10` の仮説の場で共用（`chooseStepC = chooseStepW := rfl` は維持）。
* **物理側に残る義務**: fallback 相（copy／home／fpp／markEnd／choose）の間に物理 L／C テープが R まで歩くこと。これは `Enc` の側に置く。抽象 Tick がこの相で `left`／`center` に依らないことはスクラッチで機械検査済み（n304）、歩行の台帳は `SpanRep`＋`ScanInvariant`（n304）。

**学び**: 構造体リテラルの関数引数を次の行の浅い桁に置くと parse error（`unexpected token '{'; expected '}'`）。名前付き定義にして回避した。

**次の goal**: `Geom` の残り 4 場を、同じやり方で 1 場ずつ正本（`ScaffoldGalil.scala`）と突き合わせる。最初は `rewindClean`。

## n304（2026-09-21）: choose のヘッドコピーは「正本＝ポインタ別名、Lean の到達先＝TM」の機械モデル差。物理設計を決めた

**全体 build 成功（最新の全体 build は ba6aeec）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変（義務 1 本: `obligation_localRealization`）。Lean のコードは変えていない（調査と設計決定）。

| 公理 | 状態 |
|---|---|
| `obligation_localRealization` | 残（未接続） |

**実行で確かめたこと（Scala 正本、語 ab／aab／abab、probe は削除済み）**: choose モードの間は `L ≠ R`、`C ≠ R`（例: ab の tick 269–270 で `L=0 C=1 R=2`）。コピーは choose→rewind の 1 歩（tick 271 で `L=2 C=2 R=2`）。fallback 各相の長さは窓幅 `2·radius+1` に比例（R=6,L=0 で copy 7／home 8／fpp 10／mark_end 6／choose 4）。

**一次情報で確かめたこと**:
* 抽象側 `GalilScaffoldTopRewind.lean:56` の `choose` は `left := x.right, center := x.right` を select の 1 歩で代入。`GalilScaffoldTopFallback.lean` の copy／home／fpp／markEnd は VM の `left`／`center` を読みも書きもしない。
* よって `LocalWF.Geom.chooseParked`＝`LocalRealizesScan.ChooseWF.headsLeft/headsCenter`（choose モード中ずっと `absHead' left = absHead' right`）は、`InvC`（`abs''` が trace と厳密一致）と両立しない。**偽の疑いが濃い**（Lean の `False` 定理は未作成）。
* 根は機械モデルの差。正本 `docs/palindromes-in-peg/SCA_INPUT_HEADS.md:21`:「Copying a head aliases its focus, stack roots …」＝永続スタックのポインタ別名で O(1)。Lean の消費者 `CloseoutFinalW.H_realizeCanonical` が要求するのは `LocalStep … → realize`＝Kim–Park の実時間多テープ TM（`ProgramMachine.STape` は zipper、1 命令 1 セル）。ヘッドのコピーは原始操作ではない。
* `LocalTick2 §3`／`LocalTick3:43` の元設計は「コピーせず、L と C が自分のテープを R まで歩く（head-copy job）」。物理としては正しいが、`abs'` が物理 `left` を読むので、歩いている間 `InvC` が壊れる。これが `chooseParked` という偽の疑いが濃い仮説の出どころ。replayStart は `LocalReplayParked`（`absR`＝駐車 view＋再生量、鏡 `mirL`）で同じ問題を解決済みだが、choose には対応物が無い。

**設計決定（A を採る）**:
* (A) **fallback の各相（copy／home／fpp／markEnd／choose）の間に、物理の L と C を R まで歩かせる。** 距離は `2·radius` と `radius`、copy 相だけで `2·radius+1` tick あるので収まる。select の時点で全テープが R に居るので、遠くに取り残されるテープが無い。抽象はこの区間 `left`／`center` を読まないので、抽象値は ghost の控え（`Enc` が無視する場）で持つ。
* (B) R の twin を 2 本常駐させて select で役割交換 — 採らない。交換後の旧 L／旧 C は R から `2·r_j`／`r_j` 離れており、戻すのに O(r_j) tick 要るが、次の select は 1 文字後に来うる（`a^n b a b`）。固定本数では供給が尽きる。
* (C) ghost 層 `Mirrored1` をやめて抽象状態そのものを ghost にする — 採らない。局所→抽象の精密化（`TickL1/2/3`）を物理の高さでやり直すことになる。

**台帳は既存部品にある（2026-09-21 追記、定義で確認）**: copy 相の長さは `beginFallbackVM`（`GalilScaffoldTopFallbackCycle:19`）が `s.length` から決め、窓は `take (ℓ+1)`。`GalilSpanCounter.SpanRep s : value s.length = 2 * value s.radius + 1` は `CloseoutWatchPhase.spanRep_of_invLP` でタダ（`BranchSupply.SpanRepOnScanAndShift` もある）。位置は `CloseoutPackRun10.LPackM.scanGeom` の `ScanInvariant`（`leftPos : position l = center − radius`、`rightPos : position r = center + radius`）。よって歩く距離 `2·rad` は copy 相の tick 数 `2·rad+2` に収まる。未確認: `ScanInvariant` の `rad` と `s.radius` カウンタの同一視（`RadiusRep`）が同じ点で取れるか。

**設計 (A) の要をスクラッチで機械検査した（2026-09-21、リポジトリには未投入・消費者と一緒に入れる）**: `Tick (galilFrameS Pw q first) delay ⟨c, s⟩ ⟨c', t⟩` かつ `c.mode ∈ {copy, home, fpp, markEnd}` または `c.mode = choose ∧ c'.mode = choose` なら、任意の `l cc : PlaceHead` で `Tick … ⟨c, {s with left := l, center := cc}⟩ ⟨c', {t with left := l, center := cc}⟩`。error 0、公理は `propext`／`Quot.sound`。証明の形: `cases h` してモードで 9 構成子（copy_one／copy_done／home_start／home_step／fpp_slice／fpp_done／markEnd_found／markEnd_step／choose_step）に絞る。7 つは関係が `fppLens.rel`（`s.fpp` だけ読む）なので `obtain ⟨hstep, hframe⟩ := hrel; exact ⟨hstep, congrArg (fun v : GalilVM => {v with left := l, center := cc}) hframe⟩`、ガードは defeq で `exact hp`。`markBack` の 2 つは `rewindLens` 経由なので `obtain ⟨⟨hmarksLeft, hnext⟩, hframe⟩ := hrel; rw [hnext] at hframe; subst hframe; exact Tick.… _ _ _ hm hp ⟨⟨hmarksLeft, rfl⟩, rfl⟩`。
**波及の見積り**: `abs''` は 12 ファイル約 100 箇所、`absState''_eq`（replay でなければ `abs'' = abs'`）が fallback 相の `tickL3_*StepC` でも使われている。控えを入れるなら `abs''` の `left`／`center` を fallback 相だけ控えから読む形にし、`absState''_eq` に「fallback 相でない」を足す。

**方針の更新（2026-09-21、控えは要らない）**: `Enc` は自由データなので、`abs''`／`GalilVML` は変えずに **ghost の select 自体に view のコピーをさせる**（`{ chooseVm c x with left := x.right, center := x.right }`）。物理 L／C が fallback 相の間に歩く話は `Enc` の側だけに置く（fallback 相では「物理 L テープ = ghost の `left` を右へ k 歩進めたもの」と読む）。スクラッチで機械検査済み（error 0、標準 3 公理）: コピー入りの select の `abs'` は、`hleft`／`hcenter` 無しで抽象 `choose`（`rewindLens.set … left := right, center := right, length := ofNat 1, radius := reset`）に一致する。証明は `hsplit : abs' {chooseVm c x with left := x.right, center := x.right} = {abs' (bankTick chooseOps2 (bankTick chooseOps1 x)) with left := (abs' x).right, center := (abs' x).right} := rfl` のあと `rw [hsplit, abs'_bankTick hinj1 (chooseOps2_ok hp), abs'_bankTick hinj (chooseOps1_ok x)]; rfl`。
**編集計画（その場で一般化、変種は作らない）**: (1) `LocalTick3`: `TickL3.choose_select` の着地をコピー入りにして `hleft`／`hcenter` を落とす。`abs'_chooseVm`、`tickL3_inv`／`tickL3_abs`／`tickL3_replaying` の該当 case を直す。`tickL3_local`（`StepLocalN`、`LocalTick3` の外に消費者なし）は select を除く形にする。(2) `LocalRealizesScan`: `chooseStepC` の select 枝を `{ vm := …, mirL := m.vm.right }`（鏡は新しい `center` の twin でないといけない）、`ChooseWF` から `headsLeft`／`headsCenter` を削除、`mirInv1_chooseStepC` は `WF m.vm.right` から。(3) `LocalWF`: `Geom.chooseParked` を削除、`pol_chooseStepC`。(4) `CloseoutCoreAgree.chooseStepW`（`chooseStepC = chooseStepW := rfl` がある）を同じ形に。(5) 旧 encoder `CloseoutCoreEnc8`／`9`（`chooseStepW` を tape 命令に符号化、旧経路）は壊れる見込み。新経路（`ShadowedLocalFinal`）は `CloseoutCoreEnc7` までしか import していないことを確認してから、直すか退避するかを決める。

**次の具体 goal**: copy 相の局所 step に「`canRight` の間 L と C を右へ 1 歩」を足したとき、select 時点で `Twin left right ∧ Twin center right` になること（copy 相の tick 数 ≥ `position right − position left` の台帳が要る。抽象側の `position center + value radius = position right` の類を tracked state で確認する）。

## n303 — 突き合わせで見つかった形式化ミスの候補: 局所層の choose は `L := R`・`C := R` を実装していない

**方法（n302）の 2 回目（2026-09-21、Lean の変更なし）**: `hgeomTracked` の各場を Scala 正本と突き合わせた。

**確認できたこと（一次情報）**:
* Scala の `stepShift`(`:324`) と `stepCopy`(`:342`) は**同じカウンタ `remaining`** を使う（`beginChainShift` は `alias(remaining, chain.h)`、`beginFallback` は `alias(remaining, length); remaining.inc()`）。Lean は copy 側を `fpp.work` に分け、合成 frame の `remainingPos` を `H.remainingPos ∨ B.remainingPos` にした。交差の場合は trace 上で排除済み: shift モードで copy 側が立たないのは `CloseoutRadPack3.copyIdle_trace`（`PreTrace` だけから）、shift 以外のモードで shift 側が立たないのは `GalilCentreLive.CPack.idle : c.mode ≠ .shift → ShiftIdle s`（`BranchSupply.cpack_alongTrace`）。
* よって `Geom.copyWork` は追跡状態で導ける見込み: copy モード ∧ `RemPosL` ⇒（`ShiftIdle`）`CopyRemaining` ⇒ `LocalWF.work_of_copyRemaining`。`Geom.shiftMag` の `remaining > 0` も同様（`remaining_of_shiftRemaining`）。`radius > 0`・`2 ≤ length` は未確認（`ShiftGeom` に radius／length カウンタが無い）。

**偽の疑いが濃い（機械検査した反証は無い）**: `Geom.chooseParked`＝`ChooseWF.headsLeft／headsCenter`（`LocalRealizesScan:311`）は「choose モードの間 `absHead' left = absHead' right` かつ `absHead' center = absHead' right`」を要求する。追跡状態では `abs'` は trace の状態そのもの（切り詰め）なので、これは「trace の choose モードで抽象の `left = right`」を意味する。しかし Scala の `stepChoose`(`:393`) は選択の瞬間に `left.copyFrom(right)`・`center.copyFrom(right)` をしており、Lean の `rewindFrame.choose` も `y = {x with left := x.right, center := x.right, …}`（選択時に代入）。fallback の各相（copy／home／fpp／markEnd）は `left`・`center` に触らない（`fppLens`）。つまり choose モードの途中では一般に `left ≠ right`。**局所層の `chooseStepC` はヘッドのコピーを実装しておらず、「既に同じ位置にいる」ことを側条件に置いているだけ**で、その側条件は run 上で成り立たない疑いが濃い。

**含意**: `realizes_seven` の choose モードは偽の疑いが濃い側条件の上に立っている。ヘッドのコピーは K 局所な 1 歩ではできないので、物理表現の設計が要る。既存の仕掛けは replay 用の 1 本だけ（`Mirrored1.mirL` は center の twin で、`commitReplayParked` が `left ↔ mirL` の役割を入れ替える）。choose には `R` の twin が 2 本（`L` 用・`C` 用）要り、入れ替えた後の古いカーソルを次の choose までに `R` へ追い付かせる（fallback の各相は Θ(length) tick あるので償却できる見立て。未検証）。`spare` の本数の問題もこれと同じ根。

**次の一手**: (1) Scala を極小の語（fallback が起きる語）で走らせ、choose モードの tick で `left`／`center`／`right` の位置を出して上の疑いを実行で確かめる。(2) 確かめられたら、`Mirrored1` を「`R` の twin 2 本つき」に広げる設計を先に決める（handoff: 別々の物理配置で部品を作って後で統合する進め方には戻らない）。

## n302 — 進め方の変更: 残りの仮定は、証明に入る前に Scala 正本の該当行と突き合わせて形式化を検査する

**きっかけ（2026-09-21、コウタ）**: 「もうちょっと視点変えてすすめよう」「形式化のミスとかさ」「同じところぐるぐるまわらんように」。今日見つけた障害（飢餓テストの読みすぎ、`repC : Control → Bool`、`Geom` を run 不変量に入れた、模倣を全状態に要求、Post 相で ghost に tick を強制）は全部**自分の形式化のミス**で、1 個ずつ偶然に踏んで見つけていた。Post 相は挙動を 2 回推測で外した（n295→n296→n297）。

**方法**: `scala/pal/src/main/scala/pal/ScaffoldGalil.scala` は実行できる仕様。仮定を証明・公理化する前に、対応する Scala の行を読み（必要なら極小の語で走らせ）、Lean の述語の形がそれと合うかを先に確かめる。

**今回の突き合わせ結果（一次情報、行番号は ScaffoldGalil.scala）**:
* `:203-206` `quiescent = mode == Scan && !replaying && !right.head.canRight`、`caught = quiescent && !right.gap`、`report = caught && output`、`inputReady = quiescent && right.gap`。→ Lean の報告テスト（scan ∧ ¬replaying ∧ `R` が文字上 ∧ 次の文字が無い）と形が合う。
* `:255` `available = replaying || (if (advanceTrailingGap) right.canRight else right.head.canRight)`。Lean の `scanFrame.available := canRight s.right`（`GalilScaffoldTopScan:37`）は **`advanceTrailingGap = true` の版**（online 経路 `:545`）に当たる: 最後の文字の後ろの gap へは入力なしで進める。既定の `step`／`run`（`:486`、`false`）は `R` が最後の到着文字で止まる別の版。→ n297 の「報告の後、比較が左端で不一致になり shift／fallback に入る」は Scala の online 版でも同じ挙動で、Lean のモデルのミスではない。
* `:187-189` scan モードでは毎 tick `background()` が先に走る。Scala は文字待ちの間も背景仕事を進める。Lean の局所層は飢餓時に stutter する（切り詰めた pre-loaded trace と等しく保つための設計）。物理機械に「飢餓なら抽象を変えない」を要求するのはこの設計の帰結で、Scala と同じ機械を作るわけではない。
* `:273` `beginChainShift` は `length.inc()` を 2 回 → `Geom.shiftMag` の `2 ≤ length` の出所。

**次に突き合わせるもの**: `hgeomTracked` の各場 ↔ `stepShift`(`:324`)／`stepCopy`(`:342`)／`stepChoose`(`:393`)／`stepRewind`(`:409`)、`hscanNext`／`hplateauNext` ↔ `stepScan`(`:254`)、`spare` の本数 ↔ 局所層の commit（`RestartStaged` など）が同時に使う役割なしテープの最大数。

## n301 — 到達点の棚卸し: `given_openModesAndPhysicalMachine` に残る仮定は抽象層 5 本＋物理側 8 本

**状態（2026-09-21 未明）**: 最新の全体 build は `ba6aeec`（`BUILD=0`・`error` 0・`sorry` 0）。以後は module build `PalPeg.ShadowedLocalFinal` `BUILD=0`（最後は commit `b9accbd`、push 済み）。**全体 build 成功（`ba6aeec` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`。`unconditional` は未付け替え。

**n300 以降**: `ba6aeec` オラクル述語に述語パラメータ `Y`（報告点の状態についての追加事実）。旧経路は `True`、新経路は scan モード。canonical な pre-trace の存在定理が「`Tc m` の状態は scan モード」を言う。`b495751` `postPhase` の台地に `mode = scan`、`hplateauTick` → `hplateauNext`（局所後続の存在）。`09a208c` `localGood m := LocalWF m.vm`（`hgoodWF`・`hgoodInit` が消えた）。`dd236e4` `good_chosenStep`、`hgoodTick` → `hgoodPhaseStep`（init と 7 相の関数 step だけ）。`b9accbd` `hgoodFeed` → `hgeomFeed`（極性は `polWF_feedC`）。

**`ShadowedLocalFinal.given_openModesAndPhysicalMachine` の仮定（`#print axioms` 標準 3 本、`sorry` 0）**:
* `unconditional` で供給できるもの: `hfirst : first ≠ 4`・`hq : q ≤ 64`・`hor`（`cycleOracleOnPackedRun`、述語 `Y` つき）・`hres`・`hChainVerifierSupply`。
* 抽象局所層（具体データ `localGood`／`postPhase`／`frozenAt`／`ghostSteps`／`reportTest` の上）: `hgoodPhaseStep`、`hgeomFeed`、`hscanNext`、`hreplayStartNext`、`hplateauNext`。
* 物理機械（自由データ `Q Γ t K L0 blankSymbol q0 repQ outQ Enc PhysFrozen`）: `htape`、`hencInit`、`hforwardTick`（非凍結の run 状態で前方模倣、`TickSucc`）、`hforwardFeed`（追跡状態で）、`hencRep`（run 上で `reportTest` と一致）、`hencOut`（報告点でだけ）、`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`。

**公理として書き出す前の注意（未検証の懸念）**: `hgoodPhaseStep`／`hgeomFeed` は `LocalWF.Geom` の保存を含む。`LocalWF.lean` §8 は `Geom` を「単独の局所 step では保存されない、機械の不変量」と書いており、`InvC localGood` からだけでは帰納的でない可能性がある（特に shift モードで `RemPosL` が `CopyRemaining` だけで立つ場合の `shiftMag`）。偽の義務を公理にしないよう、書き出す前に `Geom` を追跡状態の抽象（trace の `ShiftGeom` など）から導けるかを 1 場ずつ確かめること。物理機械は未構成（`ActRule` 未実装）。

## n300 — 試行の結果: `ReachAtOn` に場を直に足すと旧経路が壊れる。述語パラメータで入れる

**試したこと（2026-09-21、未 commit・作業ツリーは元に戻した）**: n299 の手順どおり `ReachAtOn` の報告節に `y.ctl.mode = Mode.scan` を足し、`checkpoints_costOn_upto1`・`PreTraceIMW.scanAtReport`・`OracleRun.lean` の 3 箇所を直した。`CloseoutCheckW` 単体は error 0・module build `BUILD=0`。**全体 build は `BUILD=1`**（task の終了コードは 0 だった。ログの `BUILD=` 行で判定）: `CloseoutOracleW.lean:121` `reachAtIMW_of_reachAtC3R_W`。旧オラクル `GalilInvPlus3.ReachAtC3` の報告点にはモードの情報が無く、旧経路はこの場を供給できない。この補題は `h_oracleIMW_of_MC3_W` 経由で旧 final 8 本（`CloseoutFinalW`／`W3`／`W4`／`Ver`／`S2`／`Branch`×2／`Four`）が使うので、仮定を足して回るのは採らない。差分は scratchpad の `scanAtReport_direct.patch`（116 行）に退避し、2 ファイルは `git checkout --` で戻した。

**正しい入れ方（未実装）**: `CloseoutCheckW` の section 変数に「報告点の状態についてオラクルが追加で言うこと」`Y : List (Fin 2) → State GalilVM → Prop` を足し、`ReachAtOn` の報告節を `… ∧ Refreshed … ∧ Y w y ∧ …` にする。旧経路（`ReachAtIMW` など）は `fun _ _ => True`、新経路（`OracleRun`）は `fun _ y => y.ctl.mode = Mode.scan` を渡す。`PreTraceIMW` は触らず、canonical の存在定理（`CloseoutCheckW:468`）の結論に `∀ m, 1 ≤ m → m ≤ |w| → Y w (st (Tc m))` を足して `CloseoutFinalBranch.canonicalPreTrace_exists` → `ShadowedLocalFinal` の `htraceOf` へ運ぶ。明示引数 `… I R w` の後ろに `Y` が入るので、使用箇所は `CloseoutCheckW`（内部 29）・`OracleRun` 5・`CloseoutFinalBranch` 3・`ShadowedLocalFinal` 2・`PalInPegUnconditional` 2・`CloseoutOracleW` 2・`OracleReady` 1。最終定理の経路なので全体 build で検証する。

## n299 — 調査: 「報告点は scan モード」は証明鎖に実在する。足す場所の地図

**一次情報（2026-09-21、Lean の変更なし）**: 着地の不変量 `CloseoutCheckW.ScanOnPackedRunFromInvLPS`（`CloseoutCheckW:422`）の第 1 場は `ScanNR ⟨c, r⟩`（= scan ∧ ¬replaying）。`ReachAtOn`（`CloseoutCheckW:136`）の報告点 `y` を作っているのは `OracleRun.lean` の 3 箇所だけ（`:509` 報告位置にいる着地状態そのもの、`:633` 一致 tick の後、`:878` shift／fallback 経路の後）で、どれも同じ状態について着地の不変量（`⟨⟨hm, hr⟩, …⟩`／`hI'`）を手にしている。つまり `y.ctl.mode = .scan` は 3 箇所とも無償で出る。

**足す手順（未実装）**: (1) `ReachAtOn` の報告点の節に `y.ctl.mode = Mode.scan`（または `I w y.ctl y.vm`）を足す。(2) `OracleRun.lean:509／633／878` の 3 箇所でそれを供給する。(3) `CloseoutCheckW.checkpoints_costOn_upto1`（`:189`〜、大きな存在タプルの帰納）の報告節 `ReportPointAt … ∧ Refreshed …` に場を足し、タプルの分解箇所を直す。(4) `preTraceOnPackedRun_exists`（`:378`）／canonical 版（`:468`）と `PreTraceIMW`（または `PreTrace.report`）に `scanAtReport : ∀ m, 1 ≤ m → m ≤ |w| → (st (Tc m)).ctl.mode = .scan` を足す。`PreTraceIMW` に触れるファイルは 15 個（無名構成子 `⟨base, packs⟩` の箇所を grep で確認すること）。(5) 最終定理の経路なので全体 build で検証する。

**使い道**: `ShadowedLocalFinal.postPhase` の台地の枝に `mode = scan` を足せる。背景 tick・restart はモードとヘッドと出力を保ち、比較は `R` を `2|w|` へ進めて凍結に入るので、`hplateauTick` は「台地の scan 状態に `NextOK` な局所後続が存在する」（`hscanNext` を台地へ広げた形）と Tick の場合分けの補題に落とせる見立て（未証明）。

## n298 — 凍結相・台地相を橋に入れた。残る仮定の一覧と、`hplateauTick` の障害（報告点にモードの場が無い）

**状態（2026-09-21 未明）**: 最新の全体 build は `e0bb107`（`BUILD=0`）。以後は module build `PalPeg.ShadowedLocalFinal` `BUILD=0`（最後は commit `9299aac`、push 済み）。**全体 build 成功（`e0bb107` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`。`unconditional` は未付け替え。

**n297 以降に `ShadowedLocalFinal.given_openModesAndPhysicalMachine`（`#print axioms` 標準 3 本、`sorry` 0）へ接続したもの**:
* `10ea280` 物理の出力ビットの一致は抽象 run の報告点でだけ要求（`hreportIff`／`hstAbsAt`）。`micro_shadow` は core の等式・不変量・`Rep` だけ。
* `d4391dd` 橋の `Rep` を語添字に。
* `d54c2e8` `frozenAt w m`（`0 < |w| ∧ 2|w| ≤ position right`）、`freezeSteps`、`realizes_freeze`、`notFrozen_of_invC`。橋に渡す抽象後続の「留まる」旗は `Starved ∨ frozen`。
* `0c158db` `Rep` を二枝に: 非凍結は前方模倣（`hforwardTick` は `¬ frozenAt` の状態だけ）、凍結は物理側の不変量 `PhysFrozen w p`（`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`）。`hsimFeed` の源は追跡状態（最終報告点の後に文字は来ない）。
* `9299aac` `postPhase`（台地 = `ReportPoint ∧ Refreshed`、または凍結）。`hpostOfLastReport` は証明で消えた（最終報告点では全文字到着 ⇒ `truncS_zero`）。`hpostTick` は凍結の場合を証明し、台地の場合だけ `hplateauTick` に残した。

**残る仮定**: `hfirst`・`hq`・`hor`／`hres`／`hChainVerifierSupply`（`unconditional` で供給可能）、`Good` 系 4 本、`hscanNext`／`hreplayStartNext`、`hplateauTick`、物理側 `hencInit`／`hforwardTick`／`hforwardFeed`／`hencRep`／`hencOut`／`hfrozenEnter`／`hfrozenKeep`／`hfrozenQuiet`。自由データ: `Good`・`Enc`・`PhysFrozen`・物理機械。

**`hplateauTick` の障害（一次情報）**: `ReportPoint`／`GalilReportPrefix.ReportPointAt`／`GalilLedgerAssembly.ReportPointAt` のどれにも `mode` の場が無く、`CloseoutCheckW.ReachAtOn` も報告点の状態 `y` のモードを言わない。したがって台地の状態が scan モードだとは今の pre-trace からは言えず、`hplateauTick` は全モードの tick を問う形のまま。台地の tick を scan の tick（`chosenStep`）に限るには、オラクルの到達述語（`ReachAtOn`）に「報告点は scan モード」を足して `cycleOracleOnPackedRun` の証明鎖で供給する必要がある（大域側の作業）。

## n297 — 訂正: Post 相は scan だけではない（回文のとき最後の比較は左端で不一致）。三相の設計案

**一次情報（2026-09-21、Lean の変更なし）**: `GalilScaffoldTopScan:42` `matched s := read s.left = read s.right`、`GalilScaffoldInputHead:40` `read p := p.head.focus.map (fun a => if p.gap then 2 else letter a)`、`left p := ⟨if p.gap then p.head else moveLeft p.head, !p.gap⟩`。報告点の台地の後の比較で `R` は gap（`some 2`）へ進むが、`L` が最初の文字にいる場合（＝接頭辞全体が回文、出力 true の場合）`left L` は focus が `none` になり `read = none ≠ some 2` で**不一致** → scan_shift／scan_fallback → shift／fallback／fpp／replay に入る。**n296 の「Post 相は scan だけ」は偽**（回文の場合に破れる）。

**三相の設計案（未実装・仮説）**: (T) 追跡相 `k ≤ Tc |w|`（現状どおり）。(P) 台地相: `Tc |w|` の後、`R` が最後の文字 `2|w|−1` にいる間。ここは scan モードの tick だけ（scan_count の背景 tick と、`R` を gap へ進める比較 1 回）。`Post w m := ReportPoint w (absSC m) ∧ Refreshed … (absSC m)` とし、背景 tick での保存を `backgroundS_fields` から示す。局所後続の存在は `hscanNext` を台地相にも広げる。(F) 凍結相: `R` が gap `2|w|` に出た後。ghost は語を知っているので `position (abs m).right ≥ 2 * |w|` で飢餓（stutter）させる。このとき ghost の報告テストは偽（`atLast` が成り立たない）。物理側は「`R` の物理ヘッドが到着の先端の gap にいて pending が無い ⇒ 報告ビットは偽」という局所不変量だけで足りる（`R` の物理ヘッドは比較でしか右へ動かず、左へは動かない。replay は abs の `R` を左へ跳ばすが `replaying = true` なのでテストは偽）。

**橋に要る変更**: `pal_in_peg_of_shadowed_core` の `hstAbs`（`shadowAbs` = ghost の抽象）は凍結相では保てない（replay 中の refresh で物理の出力が変わる）。使い道は (a) `rep_sound` の転送（報告ビットが真の時点だけ）、(b) `rep_complete` の転送（`ReportPoint (shadowAbs s)` が真の時点だけ。凍結相は vm の `R` が `2|w|` なので偽）、(c) 台帳（追跡相の時点）。よって `Rep` を凍結相では「報告ビットが偽 ∧ vm 部分は凍結 ghost と同じ」に弱める形へその場で一般化できる見込みは、橋の 3 箇所を書き換えて確かめる必要がある。

## n296 — 訂正: n295 の案はそのままでは通らない（報告点は台地を成し、`Tc m` は最初の添字とは限らない）

**一次情報（2026-09-21、Lean の変更なし）**: `GalilCheckpoints.ReachAt`／`CycleOutM` は「`ReportPointAt raw m ∧ Refreshed` の状態に到達する `StepsAll` が存在する」としか言わない。報告点の状態は**台地**を成す: `R` が `2m−1` に着いた後、scan_count の背景 tick（clock 2048 の countdown）が続き、その間はヘッド・replay・出力が不変なので全部報告点。`Tc m` は台地のどこかの添字で、最初とは限らない。したがって n295／以前の (A) で鍵だと思った「最初性」は偽の疑いが濃い（機械検査した反証は無い）。n295 の「scan の飢餓テストを次の文字の到着に強める」案は、台地の途中（`k < Tc (m+1)` かつ `R = 2m+1`）で機械が止まり `Tc` に届かなくなるので採らない。**飢餓テストは現状（init／scan は `R`、shift の移動 tick は `C`・`L`・`right L`）のまま。**

**使える事実**: `PreloadL'.needLe` は既に狭義（`k < Tc (m+1)`）、`ledger_local` は need 関数で一般化済み。

**Post 相の見立て（仮説）**: 現在の飢餓テストのままで、最終報告点の後は scan モードの tick だけのはず: 台地の scan_count → gap `2|w|` へ進む比較 1 回（gap 同士なので一致するはず。要確認）→ scan_count → `canRight R` が偽で永久に飢餓。よって `Post w m` は「scan ∧ ¬replaying ∧ 全文字到着後」の意味述語にして、`hpostTick` を (i) Post の scan 状態に `NextOK` な局所後続が存在する、(ii) その後続も Post（比較が一致して mode が scan のまま）の 2 つに落とす。(ii) には「gap 同士の比較は一致する」の vm レベルの補題が要る。背景 tick が `ReportPoint ∧ Refreshed` を保存することは `backgroundS_fields` から出るはず（未証明）。

## n295 — 設計（未実装・仮説）: 報告点で次の文字の到着まで飢餓させれば Post 相の義務が消える

**一次情報（2026-09-21、Lean の変更なし）**: `LocalShadowRealize.pal_in_peg_of_shadowed_core` は `micro_shadow` の結論のうち `ans`／`started` の等式を捨てている（`obtain ⟨hcore, -, -, hinv, hrep⟩`）。Post 相で橋が使うのは `hrepL`（物理の報告ビット = ghost の報告テスト）と `hstAbs`（`shadowAbs` = ghost の抽象、`hreadOut` 経由）だけ。

**Post 相が重い理由**: 最終報告点の後も機械は tick を続け（`R` が最後の文字から gap へ、不一致なら shift／fallback／replay）、その間の状態は trace の外。報告ビットと出力の健全性を trace の外で言う不変量が無い。

**案**: scan の飢餓テストを「`R` の次の文字が到着している」（`canRight R ∧ canRight (right R)` 相当）に強める。すると最後の報告点（以後文字が来ない）で機械は永久に飢餓＝stutter し、Post 相の状態は報告点の状態そのもの。報告ビットは真のまま、出力は refresh された値のまま。`hpostTick` は前提 `¬ Starved` が成り立たず空虚、`Post w m` は「報告点の状態で飢餓」と定義できる。Scala 正本は文字の到着ごとに仕事をする online 機械なので、この方が仕様に近い。

**影響（要確認）**: (1) `hnotStarvedOfNeed`（need ≤ 到着 ⇒ 非飢餓）が報告点 `k = Tc m`・`j = m` で破れるので、台帳の need を「tick `k` の need は、`Tc m ≤ k` なら `m+1` 以上」に上げる。(2) `GalilLookRefined.PreloadL'`／`needLe` の上界は `i ≤ Tc (m+1) → need i ≤ m+1`（端点込み）。端点 `i = Tc m` の tick は報告 `m` に不要（状態 `Tc m` は tick `0..Tc m − 1` で到達）なので `i < Tc (m+1)` 版で足りるはずだが、`ledger_localL'` の証明が端点を使っていないかを読む必要がある。(3) `nextUsed`／`chainLook` の scan 側は前提が強くなるだけなので通るはず。(4) `CloseoutCoreEnc7.NotStarvedReads` の局所読みに `right R` の読みを足す。

## n294 — 橋から最終定理に届いていない仮定を削った。全体 build 成功

**状態（2026-09-21 未明）**: **全体 build 成功（この commit 時点、`BUILD=0`・`error` 0・`sorry` 0）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`（`Axioms.lean` の guard は全体 build で通過）。

**内容**: `GalilArriveChain.pal_in_peg_of_latch_realized`（未使用だった `_H_run` を取らない版。`pal_in_peg_of_latch'` はこれを呼ぶ）。`pal_in_peg_of_local_latch`／`pal_in_peg_of_local_core` から `Inv`・`delay`・`x0_inv`・`x0_ctl`・`inv_tick`・`inv_feed`・`stutter_of_starved`・`tick_of_not_starved`・`feed_abs` を削除、`pal_in_peg_of_shadowed_core` から `delay`・`x0_ctl`・`stutter_of_starved`・`tick_of_not_starved`・`feed_abs` を削除（不変量は `micro_shadow` 用に残る）。`pal_in_peg_of_shadowed_sysC` の最後の goal は台帳 1 個。

**これで `hpostTick` の Tick 部分が流れる先は前方模倣の糊（`TickSucc` の一意性）だけ。** 次は Post 相の `Rep`／`hpostTick` を、n293 に書いた本当の要求（最終報告点の後に物理の `rep ∧ out` が新しく真にならない）に合わせて弱められるかを `micro_shadow` の帰納で確かめる。

## n293 — 調査: 橋の抽象 run 仮定は最終定理で使われていない（`_H_run`）。Post 相の要求を見直す材料

**一次情報（2026-09-20 夜、Lean の変更なし）**: `GalilArriveChain.pal_in_peg_of_latch'` の引数 `_H_run : ∀ w, 0 < |w| → AbstractRun' …` は**未使用**（名前が `_` 始まり、本体は `H_realize`（`M.SAccepts w ↔ LatchTrue …`）と `H_ledger` だけを使う）。`LocalTrackingLatch.pal_in_peg_of_local_latch` の `x0_ctl`／`stutter_of_starved`／`tick_of_not_starved`／`feed_abs` は `abstractRun_of_oracles`（= `_H_run` の供給）にしか流れない。つまり最終定理は「局所 run の抽象が毎歩 tick／stutter／到着である」ことを要求していない。要求しているのは (1) ラッチの同値（`rep_sound`／`rep_complete` と出力の一致、遅い全時点）、(2) 台帳（最終報告点まで）。

**`hpostTick` の量化点検**: 今の `hpostTick` は Post 相の全モード・全時点で「抽象が canonical tick」を要求する。これは (a) 上の死んだ仮定 `tick_of_not_starved` と (b) 前方模倣の糊（`TickSucc` の一意性で ghost と物理を合わせる）の 2 箇所に流れている。(a) は橋から削れる。(b) は Post 相でも ghost と物理の抽象を合わせ続けるために要る。Post 相で本当に要るのは「w が回文でないとき、物理の `rep ∧ out` が最終報告点の後に真にならない」こと（ラッチは OR なので、報告点で出力が真なら後は何でもよい）。これは抽象機械の出力の健全性（`SoundScanNR`／`OutputRel`）を trace の外へ延ばす話で、未解決。

**次の一手の候補**: (i) 橋 4 層から死んだ仮定 4 本（`x0_ctl`・`stutter_of_starved`・`tick_of_not_starved`・`feed_abs`）をその場で削る（旧経路 `CloseoutCoreAudit` の呼び出しも合わせる）。(ii) Post 相の `Rep` を「報告ビットが偽のまま」型の弱い関係に替えられるか検討する。

## n292 — `obligation_localRealization`: 報告テストを意味で定義し `rep_sound`／`rep_complete` を消した（compact 前の到達点）

**状態（2026-09-20 夜）**: 全体 build の最新は `dd21451`（`BUILD=0`）。以後は module build のみ、最後は `PalPeg.ShadowedLocalFinal` `BUILD=0`（commit `7da6528`、push 済み）。**全体 build 成功（`dd21451` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`。`unconditional` は未付け替え。

**n291 以降**: `2c13ac3` 物理機械の読み出し（`hreadRep`／`hreadOut`、`hencRep`／`hencOut`）を run 上の状態だけに限定、報告テストを語添字に。`7da6528` `ShadowedLocalFinal.reportTest`（`decide (ReportPoint w x ∧ Refreshed … x)`、`reportTest_iff`）、`pal_in_peg_of_shadowed_sysC` 内部の `hlate`（報告点の遅さ）、`usedOfLastLetter_heldAfter`（trace 側仮定 `hreportUsed` の放電）。`given_openModesAndPhysicalMachine` から `repA`・`rep_sound`・`rep_complete` が消えた。

**`given_openModesAndPhysicalMachine` に残る仮定**: `hfirst : first ≠ 4`、`hq : q ≤ 64`、`hor`／`hres`／`hChainVerifierSupply`（`unconditional` で既存定理が供給）、`Good` 系 4 本（`hgoodWF`／`hgoodInit`／`hgoodTick`／`hgoodFeed`）、`hscanNext`／`hreplayStartNext`（追跡・非飢餓状態に `NextOK` な局所後続が存在）、`hpostOfLastReport`／`hpostTick`（`Canonical` 込み）、物理側 `hencInit`／`hforwardTick`／`hforwardFeed`／`hencRep`（run 上で `reportTest` と一致）／`hencOut`。自由データ: `Good`・`Post`・`Enc`・物理機械（`Q Γ t K L0 blankSymbol q0 repQ outQ`）。

**次の一手**: `Post` を具体化（候補: 最終報告点以降、抽象状態から canonical tick で到達した状態）して `hpostOfLastReport` を試す。`hpostTick` の量化を先に点検する。その後 `Good` を具体化し、残りを原子的な義務として書き出して `unconditional` を付け替える（コウタのヒント: 1 段下ろして公理を書き出して潰す）。偽の義務を公理にしないよう、書き出す前に 1 本ずつ証明を試す。

## n291 — `obligation_localRealization`: 橋を前方模倣・語添字・choice step に作り替えた。残りは報告点の特徴づけと物理機械

**状態（2026-09-20 夜）**: 全体 build の最新は `dd21451`（`BUILD=0`）。以後は module build と狙い build のみ（最後は `PalPeg.ShadowedLocalFinal` `BUILD=0`、commit `92437e0`）。**全体 build 成功（`dd21451` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`。`unconditional` はまだ付け替えていない。

**n290 以降に消費者鎖（`ShadowedLocalFinal.given_openModesAndPhysicalMachine`、`#print axioms` 標準 3 本）へ接続したもの**:
* `31edaba` `LocalShadowConcrete.OnRun`: 物理機械の模倣は run 上の状態（追跡中 ∨ Post 相）だけで要求。
* `e601b1e` `TickSucc`（飢餓なら不動、非飢餓なら `Tick ∧ Canon`）を run 上で導出して `hsimTick` に渡す。`hpostTick` の結論に `Canonical` を追加。
* `042c19e` 物理機械の仮定を前方模倣に置換: `Enc`／`hencInit`／`hforwardTick`／`hforwardFeed`／`hencRep`／`hencOut`。糊は `tickSucc_unique`（`GalilTickFair.tick_canonical_unique`）と `starved_of_absSC_eq`。
* `747d9af` 橋の抽象局所系を語で添字づけ（`pal_in_peg_of_local_latch`／`_local_core`／`_shadowed_core`／`H_ledger_of_local_oracles`／`_shadowed_sysC`／`given_shadowedLocalSystem`）。物理機械は語に依らないまま（`encC = snd`、等式は `rfl`）。
* `d868190` `NextOK`／`chosenStep`／`chosenStep_spec`／`ghostSteps`: scan／replayStart の step は choice。`hscanLocal`／`hreplayStartLocal` → 存在命題 `hscanNext`／`hreplayStartNext`。
* `92437e0` 報告テストを `repA : State GalilVM → Bool`（抽象を読む）に。旧 `repC : Control → Bool` は `Control` にヘッド情報が無く `rep_sound` を満たせない形だった。

**残る仮定**: `Good` 系 4 本（`hgoodWF`／`hgoodInit`／`hgoodTick`／`hgoodFeed`）、`hscanNext`／`hreplayStartNext`、`hpostOfLastReport`／`hpostTick`、`rep_sound`／`rep_complete`、物理側 5 本。自由データ: `repA`・`Good`・`Post`・`Enc`・物理機械。

**`repA` の調査（未実装）**: `PreTrace.trace.good` は `SoundScanNR`（scan ∧ ¬replaying で `OutputRel` = 出力の健全性だけ）。`ReportPoint` の `MInv` は trace 上ではチェックポイント `Tc m` の点でしか分かっていない（`MInv` を trace 全点で言う定理は無い）。`ScanInvariant` は `LPackM.scanGeom`（scan ∧ ¬replaying）から出る。よって局所テスト（scan ∧ ¬replaying ∧ `R` が最後の到着文字上）で `rep_sound` を出すには (A) 追跡相で「そのテストが真になる最初の添字が `Tc |w|`」という最初性、(B) Post 相の不変量「`R = 2|w|−1` ⇒ scan ∧ ¬replaying ∧ `ReportPoint ∧ Refreshed`」（背景 tick で保存、比較で `R` が離れたら戻らない）が要る。注意: 抽象の `R` は replayStart で左へ跳ぶので単調ではない。

## n290 — `obligation_localRealization`: 仮定 4 本を証明で消した。次は 1 段下ろして義務を書き出す（設計メモ）

**状態（2026-09-20）**: 全体 build の最新は `dd21451`（`BUILD=0`）。以後は module build のみ（`PalPeg.ShadowedLocalFinal` と、`Starved` に触れる 27 モジュールの狙い build、どちらも `BUILD=0`）。**全体 build 成功（`dd21451` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: 標準 3 本 ＋ `obligation_localRealization`。

**n289 以降に証明して消費者鎖から消した仮定**（`given_shadowedLocalSystem`／`given_openModesAndPhysicalMachine`、どちらも `#print axioms` は標準 3 本）: `hnextUsedOfNotStarved`（shift 入口は `usedVM_shiftEntry_le` ＋ `HeadBehindRight.usedPH_right_le_of_next_position_le`、着地 `k+1` の `shiftPay` 台帳と `watchLag` は trace 点で無条件）、`hbackRep`（`backVerifier_alongPreTrace`、`first ≠ 4` を新しく取る）、`hnotStarvedOfNeed`（`notStarved_of_need_heldAfter`）。commit `e67299d`・`af080ce`・`4391e31`・`35cd885`。

**飢餓テストを直した（`4391e31`）**: 旧 `Starved` はモード無視で `canRight` を `L`・`C`・`R`・`right L` 全部に要求していて、init 直後（`L = C = R` が先端）の scan 状態は need が到着済みでも飢餓になる（`hnotStarvedOfNeed` は偽の疑いが濃かった。機械検査した反証は無い）。新しい定義は init／scan で `R`、shift かつ `ShiftMoves`（frame の `remainingPos` と `rfl` で一致）で `C`・`L`・`right L`。局所読みの形は `CloseoutCoreEnc7.NotStarvedReads`。

**コウタのヒント（同日）**: 「もう localRealization だけやん。一段階下に落として、localRealization を成立させる axiom を書き出して潰していく」「難しく見えたときは視点を変える」。

**設計（未実装・仮説）— 関数の精密化をやめて前方模倣にする**: 残る仮定の `scanStep`／`replayStartStep` は自由変数で、具体関数が無い（`LocalTick1.TickL1` は `SearchLocal`・`chainAt` を含む関係）。関数を書く代わりに (1) `scanStep m := choose (∃ m', 局所後続 m m')`（抽象層は ghost なので noncomputable でよい）、(2) `Rep m p := ∃ m₀, Enc m₀ p ∧ m₀ ~ m`、`~` は「`absState''`・`ctl` が等しく両方 `PhysWF`／`MirInv1`／`Good`」、(3) 物理側の義務は前方模倣 `Enc m₀ p → ∃ m₀', Enc m₀' (L0.apply p none) ∧ 局所後続 m₀ m₀'`。`hsimTick` は `GalilTickFair.tick_canonical_unique`（`Tick ∧ Canonical` の後続は一意）から出る: 物理が計算した `m₀'` と `tickC m` は同じ抽象後続を持つ。`Starved`・`repC` は `abs''` と `ctl` しか読まないので `~` 不変。`LocalShadowRealize.micro_shadow` の `hsimTick` は既に `Inv w s a` を受け取るので、`pal_in_peg_of_shadowed_sysC` の `hsimTick` を「追跡中 or Post」の不変量つきに弱められる（その場で一般化）。Post 相にも `Canonical` を持たせる必要がある。

**書き出す義務の候補（原子・trace 形・状態局所で）**: 局所後続の存在（scan／replayStart、追跡状態で）、`Good` の保存（tick／feed）、`Good → LocalWF`、`Post` の 2 本、`rep_sound`／`rep_complete`、物理機械の存在命題 1 本（`∃ Q Γ t K L0 Enc …`、前方模倣 ＋ feed ＋ 読み出し 2 本）。`repC`・`Good`・`Post` は具体的な定義にしてから公理にする。

## n289 — `obligation_localRealization`: `hnextUsedOfNotStarved` を shift 入口 1 つまで狭めた（公理は未変化）

**状態（2026-09-20）**: 全体 build の最新は `dd21451`（`BUILD=0`・`error` 0・`sorry` 0）。以後の commit（…・`ab326d6`・`4476b48`・`a6280d0`）は module build `PalPeg.ShadowedLocalFinal` の `BUILD=0` のみ。**全体 build 成功（`dd21451` 時点）・標準公理のみ・無条件 PAL は未完。** 公理リストは不変: `propext`／`Classical.choice`／`Quot.sound` ＋ `obligation_localRealization`。

**証明して消費者鎖（`given_shadowedLocalSystem`／`given_openModesAndPhysicalMachine`）へ接続したもの**: `TickUsedLetters.usedVM_scanTick_le`（shift 入口以外の scan tick）、`usedVM_shiftOne_le`（shift の移動 tick は `C` を 1 歩・`L` を 2 歩、verifier は不動）、`usedVM_phaseTick_le`（init／scan／replayStart 以外の全 tick）、`LocalStarvedRight.usedPH_shiftHeads_le_of_notStarved`（飢餓テストの残り 3 読み）。`ShadowedLocalFinal.nextUsed_heldAfter` がこれらを当て、`hnextUsedOfNotStarved` は「scan かつ着地が shift」の場合だけを問う形になった。

**未接続・調査**: shift 入口（`beginShiftVM`: `immediate` が verifier を 1 歩進める）。調べた一次情報: guard は `zero w.lag = true`、着地の `ShiftPhaseChainLedger` は `position ver + lag = position right`。`usedPH` は「その頭が到達した最大位置」で決まり現在位置だけでは決まらない（`two_usedPH_of_rep` の右スタック項）ので、位置台帳だけでは足りない。候補: 大域の `needBound_alongPreTrace`（`i ≤ Tc (m+1) → needL' i ≤ m+1`）を `m+1 = usedPH (着地の right) ≤ j` で使い、`k+1 ≤ Tc (m+1)` を front ポテンシャルの単調性（shift 入口は `replaying = false`）から出す。未着手。

**発見（未適用）**: `BranchSupply.chainVerifierRepresents_alongTrace`／`chainLagCanonical_alongTrace` は mode guard なしで trace 全点に効き、`backVer`／`backLagField` が `hbackRep` の中身そのもの。`first ≠ 4` を取れば `hbackRep` は既存定理で放電できる。

**残る仮定（`given_openModesAndPhysicalMachine`）**: `scanStep`／`replayStartStep` と `hscanLocal`／`hreplayStartLocal`、`Good` 系 4 本、`hnextUsedOfNotStarved`（shift 入口のみ）、`hbackRep`（上の発見で放電可能）、`hnotStarvedOfNeed`、`Post` 系、`rep_sound`／`rep_complete`、物理機械（`L0`・`Rep`・`hsimTick`・`hsimFeed` ほか）。物理 ActRule は未実装。

## n288 — `obligation_localRealization`: 自分が入れた仮定 `hstarvedAtLastReport` は偽の疑いが濃い。橋の終端の扱いを直す必要がある

**状態（2026-09-20）**: 全体 build は `1f8e1c5` 時点で `BUILD=0`・`error` 0 件・`sorry` 0 件、その後の commit（`adfe7f9`・`75b1ef9`・`f86fa03`・`21dbd31`・`64e10d4`・`151aed4`）は module build `BUILD=0`。標準公理のみの guard は `unconditional` について `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization` のまま。**無条件 PAL は未完。**

**n287 以降に通したもの（どれも `unconditional` には未適用）**: `InvC` に走行で運ぶ不変量の場 `good` を追加（`H_wf` の量化を修正）、`given_openModesAndPhysicalMachine`（10 モード中 7 モードを `realizes_seven_SL` で放電、側条件は頭打ち canonical trace の事実で供給、`traceRightLe_heldAfter`）、3 モードの仮定を `realizes_canonical` で「局所 step は抽象の canonical な Tick」へ帰着、`blankVML` に予備 counter テープ（`tapeCount spare`）、`LocalInitStep`（`initVml`／`initStep`、`initVM_initVml`、`tick_initStep`、`physWF_initStep`、`premises_of_truncated_boot`）と `initLocal_heldAfter` で **`init` モードを放電**（開いているモードは `scan` と `replayStart`）。

**偽の疑いが濃い仮定（機械検査した反証は無い）**: `pal_in_peg_of_shadowed_sysC`／`given_shadowedLocalSystem`／`given_openModesAndPhysicalMachine` の `hstarvedAtLastReport`（最終報告点 `Tc |w|` に立つ追跡状態は必ず `Starved`）。一次情報: `ReportPointAt.atPrefix` は `position right = 2|w| − 1`（奇数なので `gap = false`）、`canRight p := p.gap = false ∨ …` なので右 head は `canRight`、left／center も入力の内側。よって最終報告点では **飢餓していない** はずで、機械は `Tc |w|` を越えて tick し続ける（次の不一致から fallback 一式まで、文字 `|w|+1` が要るところで初めて飢餓する）。この仮定は n287 で自分が「trace は最終報告点までしか Tick の列でない」ことへの対処として入れたもので、**対処の仕方が間違っていた**。上の 3 定理は定理としては正しいが、この仮定がある限り producer が立たない。

**その後（同日、commit `08c7ca9`・`97fb90b`）: この仮定は橋から除去した。** 台帳側（`LocalLedgerShift`）の `Sched.guard`／`habs`／`starved_need` を最終報告点までに限り（内側の証明は実際にその範囲しか使っていなかった）、`pal_in_peg_of_shadowed_sysC` の走行不変量を 2 相（最終報告点までは `TrackedAt`、その先は `Post`・`PhysWF`・`MirInv1`・`Good`）にした。置き換えた仮定は `hpostOfLastReport`（最終報告点に立つ追跡状態は `Post`）と `hpostTick`（`Post` かつ非飢餓なら局所 tick は抽象の Tick で `Post` と pack を保つ）。下の「直し方の案（延長語の trace）」は採らなかった：移送補題が 6 本以上要り、checkpoint の不一致も残るため。`grep` でライブラリ全体に `hstarvedAtLastReport` は 0 件。module build `PalPeg.ShadowedLocalFinal` は `BUILD=0`、全体 build はこの 2 commit の後には走らせていない。

**なぜ元の設計も同じ所で破れていたか**: `LocalLedgerShift.H_ledger_of_local_oracles` の `habs`／`starved_need` は全 micro-step `s` に量化し、`stOf (kOf s)` を最終報告点の先でも機械の抽象走行そのものとして要求する（＝無限に続く正しい trace を暗黙に仮定）。`PreTraceIMW` は最終報告点までしか与えない。

**直し方の案（未着手・設計のみ）**: 機械を語 `w` で走らせるとき、追跡する trace を **延長語 `w ++ [a]` の canonical preload trace** にする。機械は文字 `|w|+1` が要る tick の手前で必ず飢餓し（延長語の次の報告点 `position right = 2(|w|+1) − 1` は文字 `|w|+1` を消費済み、つまりそこへ至る tick の need は `|w|` を超える）、以後文字は届かないので永久に stutter する。したがって追跡は trace の端を決して越えない。prefix `m ≤ |w|` の事実（`PreloadL'`・cost・報告点）は延長語の trace が全部持っている。要確認: (1) 枠 `PofC … w` と `PofC … (w ++ [a])` は `onLetterVM raw` で語に依存するので、切り詰めた状態の上で一致すること、(2) 延長語の prefix `|w|` の報告点を切り詰めたものが語 `w` の `ReportPoint` であること、(3) 台帳 `LedgerObligation … w` をその走行に対して出すこと。`heldAfter` と `hstarvedAtLastReport` はこの設計では不要になる。

## n287 — `obligation_localRealization`: 消費者側の橋を 3 段通し、producer の無い量化を 4 件直した。公理は未接続のまま

**状態（2026-09-20）**: 全体 build 成功（`lake build --quiet PalPeg`、ログ末尾 `BUILD=0`・`error` 0 件・`sorry` 0 件、commit `95f160b` 時点。その後の `cd22894` は module build `PalPeg.ShadowedLocalFinal` が `BUILD=0`）。標準公理のみの guard は `unconditional` について `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization` のまま。**無条件 PAL は未完。下の定理は `unconditional` にまだ適用していない。**

**通した橋（どれも結論は `RecognizedByTotalPEG PAL`、標準 3 公理のみ）**:

| 定理 | ファイル | 何を消したか |
|---|---|---|
| `pal_in_peg_of_shadowed_core` | `LocalShadowRealize` | 局所状態を「抽象状態 × 物理状態」の lockstep にして、`pal_in_peg_of_local_core` の全状態の厳密等式 6 本（`enc_tick`／`enc_feed`／`rep_eq`／`out_eq`／`outL_abs`／`encC_init`）を `rfl` にした。物理機械の仕様は `hrepInit`／`hsimTick`／`hsimFeed`／`hreadRep`／`hreadOut` の 5 本 |
| `pal_in_peg_of_shadowed_sysC` | `LocalShadowConcrete` | 上を `LocalSysConcrete.sysC` に適用。不変量は走行形（状態 = `s` 歩後の走行状態、`TrackedAt … (arrL w s) (kOf … s)`）。台帳 `H_ledger`（`habs`・飢餓の両方向）を同じ不変量から放電 |
| `given_shadowedLocalSystem` | `ShadowedLocalFinal` | trace 側 9 仮定を canonical な preload trace（`CloseoutFinalBranch.canonicalPreTrace_exists`、今回切り出し）で放電。trace は最終報告点で頭打ちにした `heldAfter` で渡す |

**直した量化（どれも producer が無かった。機械検査した反証は無いので「偽の疑いが濃い」止まり）**:

1. `inv_feed`／`feed_abs` が任意の文字に量化 → 不変量を micro-step 番号つきにし、その slot の文字だけにした（`LocalTrackingLatch` 4 定理・`pal_in_peg_of_local_core`・`pal_in_peg_of_coreLocal`、in place）。`H_feed_track` は `tracked_feedC` で置き換わった。
2. `x0_inv` が空語にも量化 → 非空語だけに（`LedgerObligation` 自体が非空語にしか量化していない）。
3. `Realizes` と producer 群の `H_trace : ∀ k` → 上限 `lastTick` を入れた（`LocalSysConcrete`・`LocalRealizesScan`・`LocalRealizesPhase`・`LocalWF`・`CanonicalLocalRealizes`・`CloseoutCoreStep`・`CloseoutCoreAgree`、in place）。preload trace は最終報告点までしか Tick の列でない。
4. `InvC.track` の添字に上限が無く `NoReplay` を全添字で要る → `noReplay_run` は「最終 tick の後は一定」の trace を取る形にし、`heldAfter` で満たす。

`LocalSysConcrete.localSys_oracles` は削除した（呼び出し元なし、`pal_in_peg_of_shadowed_sysC` が役割を引き継ぎ、全添字 trace と任意文字 feed を仮定に取っていた）。

**`given_shadowedLocalSystem` に残る仮定（これが公理の中身の地図）**:

* 抽象局所側（頭打ち canonical trace の上）: `hrealizes : ∀ mode, Realizes …`、`hneedOfNotStarved`、`hnotStarvedOfNeed`、`hstarvedAtLastReport`、`rep_sound`、`rep_complete`、`hinitTrack`、初期状態 `blank` の `Inv`／`Twin`／`WF`。
* 物理側: `hrepInit`／`hsimTick`／`hsimFeed`／`hreadRep`／`hreadOut`（`hsimTick` は 1 物理歩 = `tickC M` 1 回。`LocalStepFusion.compStep_iterRule` が複数微小歩を 1 歩に融合する道具）。

**調査（証明ではない）**: `hrealizes` の既存 producer `CloseoutCoreAgree.realizes_seven_SL` は 7 モードぶんで、語に依らない `SL` の `init`・`scan`・`replayStart` は `id` の仮実装。前提 `H_wf : ∀ m, InvC … → LocalWF m.vm` は `InvC` から出ず（`LocalWF` = `PolWF ∧ Geom`、`Geom` は `LocalWF` のヘッダ自身が Residuals と明記）、producer が無い。**このまま刺さない**。具体的な `blank : GalilVML P` も未定義。

**次**: (1) 具体的な `blank` を定義して `hinitTrack`・`Inv`・`Twin`・`WF` を閉じる、(2) `LocalWF` を `Realizes` の前提側（走行不変量）へ移して `H_wf` の量化を直す、(3) `scan`／`init`／`replayStart` の局所 step を `CanonicalLocalRealizes.realizes_canonical` で `Realizes` に載せる。

## n286 — `obligation_localRealization`: 方針を消費者側からに変えた。融合定理 `compStep_iterRule` は通ったが、公理への接続はまだ無い

**状態（2026-09-20）**: 全体 build 成功（`lake build --quiet PalPeg`、ログ末尾 `BUILD=0`・`error` 0 件・`sorry` 0 件、新モジュールは `ConcreteLocalMachine` → `Workbench` 経由で登録済み）。標準公理のみの guard（`PalPeg/Axioms.lean`）は `unconditional` について `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization` のまま通過。無条件 PAL は未完（残り 1 公理 `obligation_localRealization`）。**この節の定理は 1 本も公理の消費者に繋がっていない。進捗として数えない。**

**なぜ方針を変えたか**: n285 以降、queue → view → views 機械を下から 10 モジュール積んだが接続はゼロだった。コウタの指摘（「接続がない時点でアプローチ疑え」「producer がないとき確実に形式化が間違ってる」）を受けて型を読み直した結果:

* `H_realizeCanonical`（`CloseoutFinalW:113`）を結論に持つ定理はリポジトリに 1 本も無い。最終組み立て `CloseoutFinalFour.given_preTraceIMW_on` は `pal_in_peg_of_structured` で `M.SAccepts w ↔ w ∈ PAL` を要求し、公理の仕事は「機械の受理 ↔ 抽象 trace の latch」。`latch_iff_pal_of_preTrace` があるので、公理の中身は実質「PAL を実時間で受理する `LocalStep` 機械の存在」そのもの。
* 局所層の既存の橋は `LocalTrackingLatch.tracking_latch_of_oracles`（機械の受理 ↔ 機械自身の影 trace `stAbs` の latch）→ `pal_in_peg_of_local_latch` → `LocalLatchRealize.pal_in_peg_of_local_core`。中間層は `LocalSysConcrete.sysC`（`X = Mirrored1 P`、1 局所 tick = 抽象 Tick 1 回、`Realizes` 10 モード＋`H_ready`＋`H_feed_track` が残差）、台帳は `LocalLedgerShift.H_ledger_of_local_oracles`（`habs`・飢餓同値が残差）。
* この橋の `enc_tick`／`enc_feed`／`rep_eq`／`out_eq`／`outL_abs` は**全状態への厳密等式**。実機の `sweep` は `TEqG` までしか一致せず、`Rep`（stack の底が存在量化）は物理状態から抽象状態を一意に決めないので、`X := 物理状態` で `absS` を関数として書けない。`outL_abs` は `tracking_latch_of_oracles` の中では走行上の状態（`(micro S w x0 s).core`）にしか使われていない。
* **次の具体 goal（未着手・設計のみ）**: `X := A × (Q × (Fin t → STape Γ))`、`tickL (a, p) := (S.tickL a, L0.apply blank p none)`、`feedC` も同様、`repL`／`outL` は物理制御の読み、`absS' (a, p)` は `absS a` の `ctl.output` を物理の読みで上書きしたもの。こうすると `enc_tick`／`enc_feed`／`rep_eq`／`out_eq`／`outL_abs` は全部 `rfl` になるはずで（**Lean では未確認**）、残る仮定は `Rep a₀ (q0, blank)`・`Rep` の tick／feed 保存・`Rep a p → repL a = repQ p.1 ∧ outL a = outQ p.1` になる。これが物理機械の仕様。

**今回通した定理（未接続）**: `PalPeg/LocalStepFusion.lean`。消費者の時間仕様は「局所 1 歩 = 抽象 Tick 1 回」（`need_not_starved`＋`Sched.progress`）で、抽象局所 tick は最大 67 局所操作（`LocalTick1`）。複数の微小歩を窓 `count * K` の 1 歩へ融合する:

* `windowAfter`／`windowAfter_readWin`: 大窓に命令列を仮想適用して読んだ内窓 = 実テープに命令列を適用した後の `readWin`。
* `idealStep`、`seqRule`／`seqRule_ideal`: 2 規則の直列を 1 規則に融合、指示する 1 歩は理想 2 歩と厳密に等しい。
* `iterRadius`（再帰定義で cast を避けた、`iterRadius_eq : = count * K`）、`iterRule`、`idealIter`、`iterRule_ideal`、**`compStep_iterRule`**: margin `iterRadius K count ≤ pos` の下で、実機 `compStep (iterRule R count)` の 1 歩は制御が理想 `count` 歩走行と等しく、テープは `TEqG` で一致。

**未完**: 上の積構成の橋、物理機械の master 制御・chain／探索／counter bank／10 モード、`Realizes` 残り、`habs`・飢餓同値、`rep_sound`／`rep_complete`。

## n285 — `obligation_localRealization`: 具体機械の上で enqueue／dequeue 1 回が固定長の微小プログラムになった（`snocRun_sound`／`tailRun_sound`）。公理への接続はまだ無い

**n285 続き（2026-09-20、入力 view 1 本の具体機械。公理への接続は無い・進捗として数えない）**: 全体 build は n285 の `BUILD=0` 以降走らせていない（公理も葉も不変）。module build `PalPeg.ConcreteLocalMachine` は `BUILD=0`・error 0、下の定理は標準 3 公理のみ・`sorry` 0。無条件 PAL は未完（残り 1 公理 `obligation_localRealization`）。物理配置: view 1 本 = 12 テープ（0–9 = queue 機械、10 = `focus :: back` の stack、11 = `near` の stack）、slot = 11 歩（0 歩目 = 判断、1–10 歩目 = queue job、`incLength` で padding）、slot counter は共有・job と gap bit は view の制御、`repositionStep` の方向は送り手が決める（`ViewCommand.stepRight`／`stepLeft`）。
* `LocalViewCells`: `ViewCells v := ∃ letters, cells v = none :: letters.map some` は `ViewLocal` の全操作で保存。`back = [] ↔ focus = none`、`near` は全部文字。番兵 `none` は底の seal と同一視でき、push されるのは文字だけ。
* `LocalViewDecision`: `viewApply_observed` — 1 コマンド = back／near の stack 操作各 1 回＋queue job 高々 1 個、gap bit と 3 記号（`ViewTops`）から決まる。
* `LocalViewLayout`: `ViewRep`、`viewTopsOfWindows_eq`（3 記号は back 中心・near 中心・front 役テープ中心の窓から読める）。
* `LocalViewStep`: `viewDecision_sound`（判断歩で 2 本の stack テープが `viewApply command v` のものへ）。
* `LocalViewSlot`: `viewNext`／`viewActs`（12 本の規則、`viewActs_length ≤ K`）、`ViewStep`（テープごとの margin 条件つき `TEqG`）、`viewSlot_sound`: `WF v`・`ViewCells v`・`ViewRep K v`・未払い 0 → 11 歩後 `ViewRep K (viewApply command v)`・未払い 0（slot は連結できる）。
* `LocalViewInit`: `ViewRep.back` の条件を `K ≤ bottom.length + 1` に直した（blank から 1 歩で作れる底は高さ K ちょうどで、`focus :: back` のテープは番兵 1 セルを含む。番兵は pop されない）。`viewInit_of_apply`: blank 12 本＋初期制御から 1 歩で `ViewRep K emptyView`（端での `sweep` を `sweep_blank_edge` で直接検証、`compStep_apply` の margin は先取りしない）。
* `LocalViewsMachine`: `machineRule : ActRule (Fin 2) _ Γc (viewCount * 12) K`（制御 = started × current × pending × slot × 各 view の制御。入力は 1 歩にしか来ず最初の 1 歩は初期化なので文字を latch する）、`machine_viewStep`（`viewStep_of_apply` の消費者）、`machineInit`、`machineSlot`、`machineIter_slotEnd`、**`machineFirstLetter`**: blank から実 12 歩（初期化 1 歩＋1 slot）で全 view が `ViewRep K (arrive a emptyView)`・未払い 0・slot 0・`pending = none`。handoff 第二成果のうち「blank から init＋入力到着」を同じ物理表現の実走行で通した。**scan 比較 1 回は未着手**（`commandOfLetter` の `none` 側がモードの command を入れる場所）。
* **未完**: master 制御とモードの command 選択（scan 比較から）、chain／探索／counter bank／10 モード、`TrackAt`、期限・latch、`realize_SAccepts`。

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | **変化なし。** 下の定理は入力 view 1 本の queue についての具体機械で、`H_realizeCanonical` を与える全体機械からはまだ使われていない。進捗として数えない |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 1 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization`（n282 から変化なし）。`snocRun_sound`／`tailRun_sound`／`microRun_sound` は標準 3 公理のみ、`sorry` 0。

**何を証明したか**: 入力 view が queue に対して行う 2 操作（`LocalInputView.arrive` ＝ `RTQueue.snoc`、`stepRight` ＝ `head?`＋`RTQueue.tail`）を、具体的な局所機械の固定長の走行にした。

* `snocRun_sound : RTQueue.Inv q → MicroRun … (snocProgram a) state final → MicroRep K q … → owed = 0 → MicroRep K (RTQueue.snoc q a) … ∧ owed = 0`（9 手）。`tailRun_sound` は `front ≠ []` の下で `RTQueue.tail q`（10 手）。**前提は `RTQueue.Inv q` だけ**で、終わりに未払いが 0 に戻るので連結できる。
* 機械は n284 の `queueRule`（8 本）に長さ counter の 2 本を足した `microRule`（10 本、`LocalQueueMicro`）。微小操作は `sub op`／`checkStart`／`incLength`。`microRule_sound`（sweep 前の健全性、`MicroRep` の保存）。n284 の証明は `queueRule_sound`（sweep 前）に切り出して再利用した。
* **`lenr ≤ lenf` の局所化**（`LocalQueueLength`）: 2 本の stack の高さ比較は局所的でなく、`rotStart` の `lenf := lenf + lenr` は単独 counter では O(1) に更新できない。符号つき counter を**遅延更新**する: `LengthCounter q c := c + lengthDebt q.state = lenf − lenr`、`lengthDebt` は reversing で `2·|f| + 2`。`rotStart` は `c` を触らず（開始時は `lenr = |front| + 1`）、reversing の `exec` ごとに 2 単位を借り（制御の `owed : Fin 3`）、`incLength` で 1 ずつ返す。`startsRotation_iff`: `¬ lenr ≤ lenf ↔ phase = idle ∧ c < 0`。counter は mark の stack 2 本（pos／neg）で、増減は反対側が空かの 1 bit で選ぶ（`marks_increment`／`marks_decrement`）。
* `LocalQueueProgram`: `runMicro_snoc`／`runMicro_tail`（抽象 queue 上で `snoc`／`tail` ＝微小操作列、`check_eq_sApply`）、`MicroRun`（`compStep_apply` が与える `TEqG` までの 1 歩の列）、`microRun_sound`（列に沿った反復。プログラムの形 `OwedOk` と各点の HM 前提 `PremisesAlong`）。HM の事実の出所は既存の `RTQueue.snoc_pinv`、`CloseoutCoreEnc22.tail_hrot`、`RTQueue.frontList_eq_append`、`eq_idle_of_rem_zero`。
* 整理: `ConcreteLocalMachine.lean`（2,155 行）を `LocalQueueLayout`／`LocalQueueMachine`／`LocalQueueLength`／`LocalQueueMicro`／`LocalQueueProgram` に分割（入口は `ConcreteLocalMachine.lean`）。

**n285 の続き（2026-09-20、検査済み・未接続）— 実機の走行にした**: `LocalQueueProgram` に `QueueJob = snoc a | tail`、`ProgramControl = QueueJob × Fin 11 × RTag × RotationPhase × Fin 3`、`programRule`（counter の下の微小操作に `microRule` の `nq`／`acts` をそのまま使い、counter を進める）、`programLocalStep := compStep programRule`、`programRun`（入力列に沿った実機の反復。入力は無視する）。**`programRun_snoc`／`programRun_tail`**: job の先頭から 9 歩／10 歩で `MicroRep K q …` が `MicroRep K (RTQueue.snoc q a) …`／`(RTQueue.tail q)` になり、未払いは 0。前提は `RTQueue.Inv q`（tail は `front ≠ []` も）。鍵は `LocalStep.apply` の制御成分の等式が `rfl`（margin 不要）なこと: `MicroStep` のテープ部分だけを margin 条件つきにして、実機の反復から `MicroRun` を無条件に作り（`microRun_of_programRun`）、margin は `microRule_sound` が各点で供給する。(1) はこれで済み。

**入力 view の調査（2026-09-20、一次情報・証明なし）**: 追跡すべき抽象側は `LocalState.GalilVML`（view 5 本 `left`／`center`／`right`／`walkerView`／`fppWalker`、counter bank `phys`＋`roles`、mirror 3 本、`ProgLang` の二重 buffer 2 本、chain は抽象 `ChainVM` のまま、制御）。1 歩は `StepLocal`、view の 1 歩は `ViewLocal` の 5 通り: 恒等・`arrive a`（＝`RTQueue.snoc`）・`moveRight`（gap bit の反転か `stepRight`）・`moveLeftV`（gap bit の反転か `stepLeft`）・`repositionStep target`（`pos v` と `target` の比較で `stepRight`／`stepLeft`）。`stepRight` は `near` が非空なら pop、空なら `head?`＋`RTQueue.tail`。`stepLeft` は `back` を pop して旧 focus を `near` に push。**物理表現の障害 2 点**: (a) `back`／`near` のセルは `Option (Fin 2)` で `none` は正規のセル（左端の番兵）、しかも `cellSym none = blank` なので、queue と違って「空かどうか」を記号から読めない。ただし内容の不変量「`cells v = none :: letters.map some`」（`none` は位置 0 だけ: `arrive` は `some a` しか足さず、初期 focus が `none`）を持てば、`back = [] ⇔ focus = none`、`near` は全部 `some` なので番兵方式で空判定できる。(b) `repositionStep` の `pos v < target` は位置の比較で局所的でない。抽象側がどう決めているか（mirror／counter）を読む必要がある。**次の具体 goal**: view の内容不変量を定義して 4 操作での保存を証明し、view の rule（`focus :: back` の stack・`near` の stack・queue の 10 本、制御に gap bit）を `microRule`／`programRule` の上に作る。

**初期化（2026-09-20、検査済み・未接続）**: 新規 `PalPeg/LocalQueueInit.lean`。`compStep_apply` は margin `K ≤ pos` を要るが機械は空白テープ・頭は左端から始まるので、最初の 1 歩は `sweep` を直接検証した（`pos_mvLN`／`pos_cPhase`／`rd_cPhase` などの部品補題は切り捨て減算つきの一般形で margin を要らない）。`sweep_blank_edge`: 左端の空白テープに action 無しの 1 歩を打つと、`mvL` が端で止まるぶん**頭が位置 K に移り、全部空白のまま**。番兵 `none` は空白記号なので、これは高さ K の番兵の底（`stackTape_of_blank`）。`programRule_acts_idle`（counter がプログラム末尾を過ぎていて未払い 0 なら全テープ action 無し）、`initControl`、**`programInit`**: `programLocalStep` の 1 歩で `(initControl, 空白テープ 10 本)` から制御そのまま・`MicroRep K RTQueue.empty …`。`realize` の初期テープも `STape.blankTape blank`（`LocalStepRealize:990`）なので、この形がそのまま使える。(2) はこれで済み。

**未完の部分**: (1) `MicroRun` を実機の走行にする: 制御に job と program counter を持たせた rule（`microRule` の `nq`／`acts` をそのまま使う）と `compStep_apply` で `MicroStep` を出す。(2) `MicroRep` の初期化（高さ K の底を敷く prologue、空の queue）。(3) `head?`（`stepRight` が読む先頭）を tape から読む。(4) view の残り（`back`／`focus`／`near`）と 3 本の view、chain（`LocalChain`）、探索、7 モード（`init = scan = replayStart = id` は仮実装）、入力配布。(5) `LocalStep.realize`／`realize_SAccepts` と `H_realizeCanonical`。

## n284 — `obligation_localRealization`: queue sub-step の具体的な局所機械とその正しさ（`queueRep_step`）。公理への接続はまだ無い

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | **変化なし。** 下の定理は queue 1 本の sub-step についての具体機械で、`H_realizeCanonical` を与える全体機械からはまだ使われていない（全体機械が存在しない）。進捗として数えない |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 1 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization`（n282 から変化なし）。`ConcreteLocalMachine.queueRep_step` は標準 3 公理のみ、`sorry` 0。

**何を証明したか**（`PalPeg/ConcreteLocalMachine.lean`、handoff §4 L2 の「第一成果」）: `queueRep_step : QueueRep K q control tapes → QueueRep K (sApply control.1 q) (step.1) (step.2)`、`step = (queueLocalStep Terminal hK).apply blankc (control, tapes) input`、`2 ≤ K`。具体的な局所機械の 1 ステップが、抽象 queue の 1 sub-step（`CloseoutCoreEnc25.sApply`、6 操作）に等しい。

* **機械**: `queueRule : ActRule Terminal QueueControl Γc 8 K`、`queueLocalStep := compStep queueRule`。テープ 8 本（`0`–`6` が役割 stack、`7` が valid counter）、制御 `QueueControl = SOp × RTag × RotationPhase`。`nq`／`acts` は制御と窓（各テープの中央セル `centreSym` と左隣 `belowSym`）だけの関数。`len_le` は `cellActsOfTop_length ≤ 2 ≤ K`。
* **有限観測**: `QueueView`（`Fintype`）。`deltaOf_eq_view`／`tagStep_eq_view`／`sealRoleOf_eq_view`／`rotationPhase_sApply`／`validCells_sApply`: stack 操作・role tag・封じるアドレス・次の phase・valid counter の操作は全部観測の関数。
* **物理表現**: `LaysS` は役割の中身の後ろに junk が続くので先頭セルから空判定ができない → **junk の先頭を `none`（番兵）にする** `LaysSealed`。`GalilVMEncode.blank = sOpt none` なので番兵は物理的には空白セル 1 個。junk が生まれる 3 箇所（`inval`／`exec` の `appending 0`、`install` の `done`）で 1 回 push（そこでは元の delta は `keep`）。`laysSealed_sApply`。読み取りは `queueView_eq_tops`（先頭 2 セル）。
* **tape**: `StackTape tape stack := ∃ debris, TEqG blankc tape (dTape stack debris)`（`compStep` の sweep は `STape` の項を文字どおりには返さないので `TEqG` まで）。既存に無かった `teqG_actOnG`／`teqG_actList`／`readWin_teqG` を追加。`dTape_cellApply`（セル操作 1 回＝先頭記号で選んだ 2 個以下の action）。
* **`QueueRep`**: 制御の phase ＝ `rotationPhase q.state`、`LaysSealed`、**junk の高さ ≥ K**（`compStep_apply` の margin `K ≤ pos`。`pos (dTape stack _) = stack.length` なので空の stack では破れる。junk は増えるだけで pop は junk に届かない）、7 本の `StackTape`、counter ＝ `validStack` を高さ ≥ K の sealed な底の上に。役割でないアドレスは `roleOf_surjective`（`decide`）で存在しない。
* **点検で直した不具合**: `inval` の `reversing` は `ok − 1`（`ok = 0` で 0 のまま）。抽象の `dApply pop [] = []` では無害だが、物理では counter の底を pop する。`validDeltaOfView` が counter のゼロ判定を読んで `keep` にする。
* **一次情報**: handoff が既存部品として挙げた `CloseoutCoreEnc25` は root から import されておらず build error 20 件だった（n283 で修理）。

**n284 の続き（2026-09-20、検査済み・未接続）— スケジュールの関数版**: `ConcreteLocalMachine.check_eq_sApply`（`RTQueue.check q = install ∘ exec ∘ exec ∘ (lenr ≤ lenf なら恒等、そうでなければ rotStart)`、前提は既存の `hrot : lenf < lenr → state = idle`）、`snoc_eq_sApply`（`rfl`）、`tail_eq_sApply`。`snoc`／`tail` は `sApply` の固定列で、途中の判定は `lenr ≤ lenf` の 1 回だけ。

**分割と、抽象レベルのプログラム等式（2026-09-20、検査済み・未接続）**: `ConcreteLocalMachine.lean`（2,155 行）を 4 module に分割した（`LocalQueueLayout`／`LocalQueueMachine`／`LocalQueueLength`／`LocalQueueMicro`、名前空間は `PalPeg.ConcreteLocalMachine` のまま、`ConcreteLocalMachine.lean` は入口）。全体 build `BUILD=0`。分割で 1 件だけ壊れた: 別ファイルになると `match` の補助定義（matcher）が共有されず、`simp only` だけでは閉じなくなった → 先に `cases`。新規 `PalPeg/LocalQueueProgram.lean`: `runMicro`（微小操作列の抽象効果）、`checkProgram`／`snocProgram a`／`tailProgram`、`runMicro_check`、**`runMicro_snoc : Inv q → runMicro (snocProgram a) q = RTQueue.snoc q a`**、**`runMicro_tail : Inv q → front ≠ [] → runMicro tailProgram q = RTQueue.tail q`**。`hrot` の出所は既存の `RTQueue.snoc_pinv`（`.rot`）と `CloseoutCoreEnc22.tail_hrot`。**次の具体 goal**: 機械側でプログラムを回す（制御に job と program counter を持たせ、`microRule` の `nq`／`acts` をそのまま使う rule にして、`microRule_sound` を列に沿って反復）。各点の前提: `hfront` は `tailPop` の時だけ（`Inv` の `lenf_eq` から）、`hstart`／`hrot` は `checkStart` の時だけ（`PInv`: `lenf_eq`＋`le : lenr ≤ lenf + 1`＋`rot`）、`owed = 0` はプログラムの形から。`microRule_sound` の前提を操作で guard した形に弱めてから使う。

**微小プログラムつきの機械の健全性を証明した（2026-09-20、検査済み・未接続）**: `ConcreteLocalMachine.microRule_sound`（sweep 前）: `MicroRep K q control tapes`（`QueueRep` ＋ `LengthCounter q (counter + owed)` ＋ pos／neg の mark テープ 2 本）の下で、全 10 本に margin があり、`nq = microControlAfter control q`、`acts` を当てた tape に `TEqG` な tape は `MicroRep K (microApply control.1 q) …` を満たす。`microApply`: `sub op` は `sApply op`、`checkStart` は `lenr ≤ lenf` でなければ `rotStart`、`incLength` は恒等。機械側の判定（phase = idle かつ negative テープ非空）が抽象側の `¬ lenr ≤ lenf` に一致することは `startsRotation_iff`＋`negative_iff_marks`。前提: HM の 3 事実（`front ≠ [] → 1 ≤ lenf`、idle で rear が長いとき `lenr = |front| + 1`、`hrot`）と微小プログラムの 2 事実（`incLength` 以外では `owed = 0`、`sub rotStart` は使わない）。**次の具体 goal**: プログラム列（`snoc a` ＝ `[sub (snocPush a), checkStart, sub exec, incLength, incLength, sub exec, incLength, incLength, sub install]`、`tail` も同様）を走らせると `MicroRep` の queue が `RTQueue.snoc`／`tail` になること（`check_eq_local` を使う）。その途中の各点で上の 5 前提が成り立つことを `RTQueue.Inv`／`PInv` から出す。ファイルが 2,200 行を超えたので、次に足す前に分割する（観測／番兵配置／tape／queue 機械／長さ counter／微小機械）。

**微小プログラムつきの機械を定義した（2026-09-20、検査済み。正しさは未着手）**: まず n284 の証明を再利用できる形に切り出した: `queueRule_sound`（**sweep の前**、`ActRule` の `nq`／`acts` のレベルの健全性: 表現の下で全テープに margin があり、次の制御は sub-step の制御で、`acts` を当てた tape に `TEqG` な tape は sub-step 後の queue を表す）。`queueRep_step` はその系（`compStep_apply` を最後に 1 回）。大きい機械の一部のテープ群として走らせるときはこの形を使う。そのうえで `microRule : ActRule Terminal MicroControl Γc 10 K`／`microLocalStep`: テープ `0`–`7` は `queueRule` をそのまま、`8`／`9` が長さ counter の pos／neg。`MicroOp = sub op | checkStart | incLength`、`MicroControl = MicroOp × RTag × RotationPhase × Fin 3`（最後が未払い `owed`）。`effectiveOp`（`checkStart` は phase = idle かつ negative テープ非空のときだけ `rotStart`）、`lengthMoveOf`（−1 は即 decrement、`incLength` は `owed > 0` のとき increment）、`owedAfter`（reversing の `exec` で 2）。**次の具体 goal**: `MicroRep`（`QueueRep` ＋ `LengthCounter q (c + owed)` ＋ counter 2 本の `StackTape`）と `microRule` の sweep 前の健全性。前提は HM の 2 事実、`exec` の前は `owed = 0`。

**第一成果の使用箇所を一次情報で確定した（2026-09-20）**: `LocalInputView.arrive a v = { v with far := RTQueue.snoc v.far a }`、`stepRight` は `near` が空のとき `RTQueue.head?`＋`RTQueue.tail v.far`。つまり queue 機械の消費者は入力 view の `arrive`／`stepRight` で、要るのは **`snoc`／`tail` 1 回＝機械の固定ステップ列**。局所機械まわりの 54 module（`CloseoutCore*`・`Local*`）は全部 tracked で olean あり（欠けていたのは `CoreEnc25` だけ）。`H_realizeCanonical` の文は handoff の要約どおり（有限 Q・Γ、固定 t・K・n の `LocalStep` で `SAccepts w ↔ LatchTrue …`）。

**符号つき counter の層（検査済み・未接続）**: `positiveMarks`／`negativeMarks`（mark の stack 2 本、片方は空）、`incrementDeltas`／`decrementDeltas`（反対側の stack が空かどうかの 1 bit で選ぶ、テープごとに 1 操作）、`marks_increment`／`marks_decrement`、`negative_iff_marks`（符号判定＝ negative stack が非空）。**設計の具体化**: reversing の `exec` の `+2` を 1 ステップでやると 1 テープに 2 操作要るので、制御に未払い `owed : Fin 3` を持たせ、微小操作 `incLength`（`owed > 0` なら 1 増やして `owed − 1`）に分ける。不変量は `LengthCounter q (c + owed)`。`check` のプログラムは `[checkStart, exec, incLength, incLength, exec, incLength, incLength, install]`（`checkStart` は「phase = idle かつ negative stack 非空なら rotStart」）。**次の具体 goal**: この微小プログラムを持つ `ActRule`（テープ 10 本）と `Rep`、`snoc`／`tail` 1 回＝固定ステップ数。

**長さ counter を証明した（2026-09-20、検査済み・未接続）**: `ConcreteLocalMachine.LengthCounter q c := c + lengthDebt q.state = lenf − lenr`（`lengthDebt` は reversing で `2·|f| + 2`、他は 0）。`lengthCounter_sApply`: sub-step で `c` は観測で選んだ有界な量 `lengthDeltaOfView`（`snocPush`／非空の `tailPop` で −1、reversing の `exec` の 2 分岐で +2、他は 0）だけ動く。前提は HM 不変量の 2 事実（`front ≠ [] → 1 ≤ lenf`、rotation 開始時 `lenr = |front| + 1`）。`startsRotation_iff`: `¬ lenr ≤ lenf ↔ phase = idle ∧ c < 0`。`check_eq_local`: `RTQueue.check` は phase と `c` の符号だけで分岐する `sApply` の固定列。これで `snoc`／`tail` の制御に非局所な判定は残っていない。**次の具体 goal**: この制御を機械にする（制御に微小プログラム counter、テープに `c` の pos／neg 2 本を足し、`QueueRep` に `LengthCounter` と 2 事実の出所 `RTQueue.Inv`／`PInv` を足して、`snoc`／`tail` 1 回＝機械の固定ステップ数、を示す）。以下は設計メモ（実装前）。

**（旧）長さ counter の設計**: `lenr ≤ lenf` は 2 本の stack の高さ比較で局所的でない。しかも `rotStart` は `lenf := lenf + lenr` で、単独の counter では O(1) に更新できない。そこで符号つき counter `c`（pos／neg の 2 stack、正規形、増減は先頭だけ読む）を**遅延更新**する: idle／appending／done では `c = lenf − lenr`、reversing `(ok f f' r r')` では `c + 2·|f| + 2 = lenf − lenr`。`rotStart` は `c` を触らない（開始時は必ず `lenr = lenf + 1` なので `c = −1`、`−1 + 2·lenf₀ + 2 = lenf₀ + lenr₀`）。reversing の `exec`（`revD` と `appStartD` の 2 分岐、観測で決まる）ごとに `c += 2`、`snocPush`／`tailPop` で `c −= 1`。判定は「phase = idle かつ `c < 0` なら `rotStart`」で足りる（idle でなければ `hrot` の対偶で `lenr ≤ lenf`）。要る不変量は `RTQueue.Inv`／`PInv`（idle で `lenf = |front|`、`lenf ≥ 1` when front 非空、操作前は `lenr ≤ lenf`）。

**未完の部分**: (1) `lenf − lenr` の符号 counter と、それで sub-step の**操作 `SOp` を選ぶ**スケジュール（`RTQueue.check`／`exec2`／`snoc`／`tail` を sub-step 列に分解した `CloseoutCoreEnc21.SStep` との対応。いまの制御は `op` を外から与えられている）。(2) `QueueRep` の初期化（高さ K の底を敷く prologue）。(3) queue 以外（chain `LocalChain`、入力配布、7 モード、`init = scan = replayStart = id` の仮実装の置き換え）。(4) `LocalStep.realize`／`realize_SAccepts` への接続と `H_realizeCanonical`。

## n283 — `obligation_localRealization` に着手: queue sub-step の分岐は有限観測 `QueueView` だけで選べる（未接続）。`CloseoutCoreEnc25` は build が通っていなかったので修理した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_localRealization` | **変化なし。** このノートの定理はまだどの機械からも使われていない（具体的な局所機械が存在しないため）。進捗として数えない |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 1 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization`（n282 から変化なし）。

**一次情報で分かったこと（重要）**: handoff が既存部品として挙げる `CloseoutCoreEnc25`（`RTag`／`sApply`／`deltaOf`／`laysS_sApply`）は **root から import されておらず、単体 build は error 20 件で失敗していた**（`CoreEnc24` までは通る）。原因は toolchain 由来の tactic のずれ 3 種: `match hst : q.state with` が goal の `q.state` を先に置換するので `rw [show invalDelta … q.state = …]` が当たらない（16 箇所 → `simp only [invalDelta, invalJunk]`／`[execDelta, execJunk]`）、`isDone_eq` の余分な `exact`、`snocPush` の `simp` に `junkOf` が不足。修理して error 0・`sorry` 0。**「ファイルがある」と「検査されている」は別**（CLAUDE.md の警告どおり）。

**何を証明したか**（`PalPeg/ConcreteLocalMachine.lean`、新規、`Workbench` の先頭 import 群に登録して root の build 対象にした）: handoff L2 の 1〜2。`deltaOf`／`tagStep` は抽象 queue 全体を受け取るが、実際に読むのは有限個の判定だけ。

* `RotationView`（`idle`／`done`／`reversing (forwardHead reverseHead) (reverseIsSingle)`／`appending (validIsZero) (forwardHead) (rebuiltNonempty)`）と `QueueView`（`frontEmpty`＋`rotation`）。どちらも `Fintype`・`DecidableEq`。
* `deltaOfView`／`tagStepOfView`: 観測だけから stack 操作と role tag の更新を選ぶ関数。
* `deltaOf_eq_view : deltaOf op q ρ = deltaOfView op (queueView q) ρ`、`tagStep_eq_view`。標準公理のみ。

**未完の部分（次の具体 goal）**: 観測の各 bit を**物理テープから読めるようにする表現**が無い。`LaysS q ρ L J` は `L (ρ ro) = sRoleList q ro ++ J (ρ ro)`（役割の中身の後ろに不要領域 `J` が続く）なので、stack の先頭を見ても「空かどうか」「先頭記号が本物か」は分からない（空なら先頭は junk）。必要なのは、`frontEmpty`／`forwardHead = none`／`reverseIsSingle`／`validIsZero`／`rebuiltNonempty` のそれぞれに対する局所的な担い手（sentinel か、更新とともに保つ counter の符号・ゼロ判定）と、それを含む `Rep` の場。これを決めてから `ActRule` の `nq`／`acts` を書く（handoff L2 の 3〜4）。`CloseoutCoreEnc22` の 9 本配置（`tViewQ = 9`）が何を持っているかの確認が先。

**n283 の続き（2026-09-20、未接続・検査済み）— 読み取り側を決めた**: 物理 stack は `dTape ((L n).map some) debris`（`CloseoutCoreEnc20.viewTapesQ`）でセルは `Option (Fin 2)`、`none` は未使用。そこで **junk の先頭を必ず `none`（番兵）にする**: `ConcreteLocalMachine.Sealed`／`LaysSealed q ρ stack junk`（`stack (ρ ro) = (sRoleList q ro).map some ++ junk (ρ ro)`、junk は空か `none` で始まる）。`topLetter`／`topIsSingle`（先頭 2 セル）と、制御が持つ `RotationPhase`、valid counter のゼロ判定から `queueViewOfTops` を作り、`queueView_eq_tops : queueView q = queueViewOfTops …` を証明した。

**書き込み側も証明した（2026-09-20、未接続・検査済み）**: `ConcreteLocalMachine.laysSealed_sApply`（sub-step が番兵つき配置を保つ。物理操作は `cellApply (deltaOf …) (封じる 1 bit)`、junk が生まれる 3 箇所で `none` を push、新しい junk は `sealedJunkOf`）と、読み取り側と合成した **`laysSealed_localSubStep`**: 操作・role tag・制御が持つ `RotationPhase`・valid counter のゼロ判定・役割 stack の先頭 2 セル、という**有限のデータだけ**から stack 操作・封じるアドレス・新しい role tag を選ぶ関数（`deltaOfView`／`sealRoleOfView`／`tagStepOfView`）が、抽象 sub-step `sApply` の配置を保つ。標準公理のみ・`sorry` 0・module build `BUILD=0`。まだ `ActRule` に包んでいない（窓 `Window Γ K` からの読み出しと `Act` 列への翻訳が未着手）ので、公理への進捗には数えない。

**tape が stack を表す層（2026-09-20、検査済み・未接続）**: `ConcreteLocalMachine.StackTape tape stack := ∃ debris, TEqG blankc tape (dTape stack debris)`。`compStep` の sweep は `STape` の項を文字どおりには返さないので、表現は `TEqG`（頭の位置と全セルの読みが同じ）まで。既存に無かった合同補題 `teqG_actOnG`／`teqG_actList`／`readWin_teqG`（`pos_applyAction`／`rd_applyAction` から）を足し、`StackTape.centreSym_eq`（`K ≤ stack.length` なら窓の中央＝`topSym stack`）、`StackTape.belowSym_eq`（左隣＝`topSym stack.tail`）、`StackTape.cellApply`（先頭記号で選んだ action 列を当てると新しい stack の tape）を証明。**物理表現の点検で分かったこと**: `compStep_apply` の margin `K ≤ pos` は `pos (dTape stack _) = stack.length` なので、空の stack では成り立たない。junk の底に `K` 個以上のセルを敷く（junk は封じるたびに増えるだけ、pop は junk に届かない）ことを `Rep` の場にする。**次の具体 goal**: `QueueRep`（制御＝`(op, tag, rotationPhase q.state)`、役割テープが `StackTape`、counter テープ、`LaysSealed`、junk の高さ ≥ K、全テープの margin）を定義し、`compStep_apply` で `queueLocalStep` の 1 ステップが `QueueRep (sApply op q)` に移ることを示す。役割でないアドレスの扱いは `roleOf tag` が `{0,…,6}` への全単射であること（`decide`）で消す。

**`ActRule` の項ができた（2026-09-20、検査済み。正しさの証明は未着手）**: `ConcreteLocalMachine.queueRule : ActRule Terminal QueueControl Γc 8 K`（`2 ≤ K`）と `queueLocalStep := compStep (queueRule …)`。テープ 8 本（`0`–`6` が役割 stack、`7` が valid counter）、制御 `QueueControl = SOp × RTag × RotationPhase`。`nq` は `tagStepOfView`／`nextPhaseOfView`、`acts` は `cellActsOfTop (deltaOfView …) (封じる bit) (focus)` と counter の `validDeltaOfView`、`len_le` は `cellActsOfTop_length ≤ 2 ≤ K`。観測は窓の中央セル（`centreSym`）とその左隣（`belowSym`）から `queueViewOfWindows` で作る。併せて `rotationPhase_sApply`（次の phase は観測の関数）、`validStack_sApply`（valid counter は観測で選んだ push／pop／keep で動く。`rotStart` は `ok = 0` から始まるので idle／done で空）、`queueViewOfTops_eq_syms` を証明。**次の具体 goal**: この項の正しさ＝`compStep_apply`（`TEqG`）で、`LaysSealed` と counter を表す 8 本の `dTape` から 1 sub-step 後の `dTape` へ移ること。要るのは `readWin` の中央と左隣が `dTape` の `topSym stack`／`topSym stack.tail` であること（`readWin_eq`／`rd`）と margin `K ≤ pos`。

**(i) は証明した（2026-09-20、未接続・検査済み）**: `ConcreteLocalMachine.dTape_cellApply`: `dTape (cellApply u sealing stack) (cellDebris …) = actList blankc (dTape stack debris) (cellActsOfTop u sealing (topSym stack))`、`cellActsOfTop_length ≤ 2`。tape action は stack の**先頭記号（tape の focus、`dTape_focus`）だけ**の関数。`topLetter_eq_sym : topLetter stack = symLetter (topSym stack)` で観測の先頭文字も focus から読める。一次情報: `GalilVMEncode.blank = sOpt none = cellSym none` なので番兵 `none` は物理的には空白セルそのもの（junk の上に空白を 1 つ挟む）。Lean では `seal` が予約語なので binder 名に使えない。残りは (ii) の 2 セル目（`topIsSingle` 用、`readWin_eq`／`rd` で左隣を読む）、(iii)、(iv)。

**次の具体 goal**: (i) `cellApply` を `CloseoutCoreEnc12.Act` の列に翻訳する（`dActs`／`pushActs … none`、長さ ≤ 2）、(ii) `readWin` の窓から `topLetter`／`topIsSingle` を読む、(iii) valid counter `ok` と `lenf − lenr` の unary counter テープとそのゼロ・符号判定、(iv) これらを `ActRule` の `nq`／`acts`／`len_le` にまとめて `compStep` の項を作る。以下は書き込み側に着手する前のメモ。

**（旧）次の具体 goal（書き込み側）**: `LaysSealed` が sub-step で保たれること（`laysS_sApply` の番兵版）。junk が生まれるのは `junkOf` の 3 箇所だけ（`inval` の `appending 0 _ (_ :: _)` と `exec` の `appending 0` で `ρ .fwd'`、`install` の `done` で `ρ .front`）で、そこで元の delta は `keep` なので、その stack に `none` を 1 回 push する（新しい junk ＝ `none :: 旧 stack`）。物理操作は「`Delta`（`Fin 2` の push／pop／keep）＋そのアドレスを封じるかの 1 bit」で表せば `toAddr_eq` を再利用できる。pop は常に空でない役割に対してだけ起きる（`tailD` は `front ≠ []`、`revD`／`appStartD`／`appD`／`invalDoneD` は pattern が非空を保証）ので junk を pop しない。valid counter `ok` と `lenf − lenr` の符号は別の unary counter テープで持つ（未設計）。

## n282 — 公理 `obligation_cycleOracleOnPackedRun` を証明して外した（2 → 1）。残る義務は `obligation_localRealization` だけ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | **証明して削除。** `PalInPeg.cycleOracleOnPackedRun`（定理、固定証人 `entry = 0, q = 1, first = 0`）＝ `OracleReady.cycleOracleOn_of_readyLeaves centreC placeC 0 1 0 (decodesC 0 w) …`。producer の最後の葉 `hmove` が無くなった |
| `obligation_localRealization` | 変化なし（未着手） |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件、`Axioms.lean` の guard を 1 公理に更新した上で通過）・標準公理のみ（3 本）・無条件 PAL は未完（残り 1 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_localRealization`（**本数 5 → 4、義務 2 → 1**）。`PalInPeg.cycleOracleOnPackedRun` と `OracleReady.cycleOracleOn_of_readyLeaves` は標準 3 公理のみ。`PalInPegUnconditional.lean` に残る `axiom` 宣言は `obligation_localRealization` の 1 本。

**何を証明したか**: 葉 `hmove` の最後の場合（shift 後のラウンドで不一致状態の chain が既に broken）。`FirstRoundGuard` を全ラウンド版 `BrokenGuard (b : Bool)`（`scan → periodOnly = b → broken なら restartGuardVM`）にし、`MinimalAcrossRestart.guard : ∀ b, BrokenGuard b c s` として run に載せた。tick（`brokenGuard_tick`）は `b` 汎用で、break の入口 2 つを callback で受ける。

* shift 後（`b = true`）の正 lag `WatchBreak`: watch は常に lag ゼロ（n281 の `Continuation`）なので起きない。
* shift 後の lag ゼロ `BreakStep`: `lateBreak_tailRound`。watch は追い付いていて背景 step で動かないので `distance = R`。fresh 側（`FreshC`・phase 4）は `four_of_freshC` で `4h ≤ R`。`Other'` 側（`5h ≤ R + cycle`）は、`cycle ≤ 1` なら `4h ≤ R`、`cycle ≥ 2` なら左の place が `[Lb, C]` の中にあるので、`matched_text`（matched 比較の文字＝左の文字）と `prediction_eq_left_of_period`（左の文字＝予測: 周期 → 回文の鏡像 → 検証済み窓）から「読んだ文字＝予測」となり break しない。`4h ≤ distance` からは n278 の `restartGuard_of_lateBreak`。
* `prediction_eq_left_of_period` は n280 の `shiftGuard_of_tail_caughtUp` の中身から切り出して両方が使う。
* 消費者: `not_broken_offGuard`（旧 `not_broken_firstRound` の全ラウンド版）→ `OracleReady` の `hMove` の broken 分岐 2 箇所。これで `hmove` を呼ぶ分岐が無くなり、仮説 `hmove` を `cycleOracleOn_of_readyLeaves` から削除した。前提は `Decodes`／`first ≠ 4`／`0 < q`／`first ≠ 7`／`first ≠ 8` だけで、固定証人では `decodesC` と `decide` で出る。
* 公理は `(entry q first)` 一般＋`first ≠ 4` の形だったが、使用箇所は `unconditional` の 1 箇所（`0 1 0`）だけだったので、定理は固定証人で述べた（`0 < q`・`first ≠ 7/8` を一般には仮定できないため）。

**`hmove` が消えるまでの経路（n272〜n282）**: idle（n272/n273）→ 第 1 ラウンド: 追い付いた watch（n274/n275）、仕事の残る chain（n276/n277、chain の時計）、既に broken（n278、`FirstRoundGuard`）→ shift 後: 予測外れ（n279、`TailRound`／`CycleBound`）、予測一致（n280、`Continuation`＝Scala `checkPair`）、lag ゼロ・phase 4（n281）、既に broken（n282、`BrokenGuard`）。

**未完の部分**: `obligation_localRealization`（`H_realizeCanonical centreC placeC entry q first`、局所実現）。handoff の順序 (2): 具体的な永続物理有限局所機械（`ActRule → compStep → LocalStep.realize`、`CoreEnc12/22/25`、`LocalChain`、`TEqG`/`Rep`）、最初の成果物は queue sub-step の `ActRule` を有限観測から。**未着手。**

## n281 — 葉 `hmove`: shift 後のラウンドの watch は常に lag ゼロ・phase 4。葉に残るのは「shift 後のラウンドで不一致状態の chain が既に broken」だけ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` の前提が「`periodOnly = true` かつ `∃ wb, s.chain = .broken wb`」になった（遅れている watch、phase ≠ 4 の watch は葉から消えた） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`OracleReady.cycleOracleOn_of_readyLeaves` と `RestartLowerRun.tailTick_cases` は標準 3 公理のみ。

**何を証明したか**: `Continuation` の 2 節に `zero w.lag = true ∧ w.machine.control.phase = 4` を足した。`beginShiftVM'` は guard（lag ゼロ・phase 4）の下でしか起きず、`immediate` は lag を変えない、`shiftOne` は counter だけ。chain tick での保存は `caughtUp_watch_tick`: lag ゼロの `Internal` は `idle`、matched は `Outer.immediate`（即 consume、Scala `matched()`）、phase 4 は `consume_phase_four` で吸収的。消費者は `tailTick_cases`（shift 後の不一致状態の live chain は、既に broken か、chain tick が lag ゼロ・phase 4 の watch を出すかのどちらか。copy／back は `TailRound` が排除）→ `OracleReady` の `hMove`。watch が出る側は n279（予測外れ）／n280（予測一致）が閉じる。

**未完の部分**: 葉 `hmove` の最後の場合 = shift 後のラウンドで不一致状態の chain が既に broken（restart guard 不成立）。計画（`CLAUDE_RESUME.md` 冒頭の「(c3) の計画」2.）: `FirstRoundGuard` を全ラウンドに広げる。shift 後は lag ゼロなので break は matched 比較の `BreakStep` だけ。`cycle ≥ 2` なら左の place が `[Lb, C]` の中で、`matched_text`＋周期＋鏡像＋窓から予測＝読んだ文字となり break しない。`cycle ≤ 1` なら `Other'`（`5h ≤ R + cycle`）から `4h ≤ R` で `restartGuard_of_lateBreak`。fresh 側（`FreshC`・phase 4）は `four_of_freshC` で直接 `4h ≤ R`。`obligation_localRealization` は未着手。

## n280 — 葉 `hmove`: shift 後のラウンドで、追い付いた watch（lag ゼロ・phase 4）が出てくる不一致は全部閉じた

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` の前提が「`periodOnly = true`、かつ chain tick の結果が lag ゼロの watch なら **phase ≠ 4**」になった（n279 の「予測が当たる場合」も葉から消えた） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`OracleReady.cycleOracleOn_of_readyLeaves` と `RestartLowerRun.shiftGuard_of_tail_caughtUp` は標準 3 公理のみ。

**何を証明したか**: Scala `ScaffoldChain.checkPair` の主張（lag ゼロなら `left == prediction ⇔ ¬ cycleEnd`）のうち必要な向きを run 不変量から証明した。`RestartLowerRun.shiftGuard_of_tail_caughtUp`: shift 後のラウンドで、追い付いた watch（phase 4）が右の文字を当てた不一致では shift guard が立つ。`shiftGuardVM` の定義上、`periodOnly` で guard が落ちうるのは `singlePositive cycle` だけなので、示すのは `cycle = 1`。消費者は `OracleReady` の `hMove`（`¬ shiftGuard` と矛盾）。

* n279 の `CycleBound` を `Continuation` に拡張した（全部消費済み）。scan かつ `periodOnly = true` の watch について: `Canonical cycle`、`cycle ≤ 2h`、`∃ Lb, Lb + R + cycle = C + 1 ∧ LeftEnd raw h Lb C`。shift 中は `cycle + 2·remaining ≤ 2h` と `LeftEnd raw h Lb (C + rem)`。**`Lb` はラウンド中動かない**（matched で `R+1, cycle−1`、`shiftOne` で `C+1, R−1, cycle+2`）。
* `LeftEnd raw h Lb E := 1 ≤ Lb ∧ Lb ≤ E ∧ PeriodOn e (2h) Lb E ∧ signedRead e (Lb − 1) ≠ e[Lb − 1 + 2h]?`。`Lb` は shift が出発した scan 回文の左端 `C₀ − R₀`、破れはその不一致そのもの（左の文字 ≠ 右の文字＝予測＝鏡像 `e[C₀−R₀−1+2h]`）。左の読みは `signedRead`（place 0 は `none`）なので破れもその形で持つ（リスト等式で書くと place 0 で偽になりうる）。`continuation_start` が `spanPeriod_of_window` と `prediction_eq_text` から供給。
* `cycle = 1` の証明: `cycle ≥ 2` なら不一致の左 place `C − R − 1` が `[Lb, C]` の中にあり、周期 → 回文の鏡像 → 検証済みの窓、で予測＝右の文字に等しくなって不一致と矛盾。`cycle ≤ 0` なら破れの place `Lb − 1` が scan 回文 `[C − R, C + R]` の中に入るが、そこは chain の周期を持つ（`spanPeriod_of_window`）ので `LeftEnd` の破れと矛盾。
* `two_semiperiods_le`（`4h ≤ distance ∨ Other'` と `cycle ≤ 2h` から `2h ≤ R`）を切り出して n279 の `move_of_tail_mispredict` と共有。`caughtUp_watch` は不一致比較が countdown を保つこと（`compare'_inv`）も返す。

**未完の部分**: 葉 `hmove` の `periodOnly = true` の残り（(c3)、未調査）: chain tick の結果が lag ゼロ・phase ≠ 4 の watch、遅れている watch（正 lag）、既に broken の chain。第 1 ラウンドでは順に `move_of_watch_short`／`move_of_working_*`（chain の時計）／`FirstRoundGuard` が対応した。`obligation_localRealization` は未着手。

## n279 — 葉 `hmove`: shift 後のラウンドで、追い付いた watch（phase 4）が予測を外す不一致を閉じた

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` に前提が 1 つ増えた（＝葉が狭くなった）: `s.periodOnly = true` に加えて「chain tick の結果が lag ゼロ・phase 4 の watch なら、その予測は右で読んだ文字に等しい」。予測を外す場合は葉から消えた |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`OracleReady.cycleOracleOn_of_readyLeaves` と `RestartLowerRun.move_of_tail_mispredict` は標準 3 公理のみ。

**何を証明したか**: `RestartLowerRun.move_of_tail_mispredict` → `RestartLower.move_of_prediction_break`（一般化した）→ `move_of_activePeriodBreak`。run 不変量 `MinimalAcrossRestart` に場を 2 つ足した。どちらもこの定理が消費する。

* `TailRound raw c s := scan → periodOnly = true → ScanMinimal (fun _ _ => False) raw s`。payload を `False` にすると `WatchMinimal` の `Sem` 側は `watch_moveMinimal` で `False` になるので、「shift 後は `TailMinimal` 側（`base ≤ R`）」と同値。copy／back も同じ理由で排除される。`tailRound_tick`: source の chain が idle でなければ `Move` 汎用の `modeMinimal_tick_packed`（`BirthMinimal` は `s.chain = .idle` が偽で空虚）、idle なら誕生が無い（誕生すれば target の `periodOnly = false`）ので target も idle、`shift_done` は `ShiftMinimal`。
* `CycleBound c s`: watch について、scan かつ `periodOnly = true` なら `cycle ≤ 2h`、shift なら `cycle + 2·remaining ≤ 2h`。`cycleBound_tick` は `beginShiftVM'`（`cycle := reset`, `remaining := ofNat h`）、`shift_one`（`cycle += 2`, `remaining −= 1`）、matched（`compare'_inv` の `cycleAfter`）、`shift_done`（`radiusShift` の `remaining = ofNat rem` と `positive = false` から `rem = 0`）。**run 上に `cycle` の上界はこれまで無かった**（`Other'` は `5h ≤ R + cycle`、`OnlyCredit` は `0 ≤ margin + cycle` でどちらも下界）。
* `2h ≤ R` の出所: `caughtUp_watch`（`caughtUp_facts` から `hfirstRound` を外した一般形。第 1 ラウンド版はそこから導く）が `4h ≤ distance ∨ Other'` を返す。前者は `4h ≤ R`、後者は `5h ≤ R + cycle` と `cycle ≤ 2h` で `3h ≤ R`。
* `move_of_prediction_break` は `4h ≤ R` と `ScanMinimal` を取っていたが、`4h` は `Sem` 側の最小性のためだけだった。`2h ≤ R` と最小性の供給関数 `hnoShortOf` を取る形にして、第 1 ラウンド（`scanMinimal_watch_no_short`）と shift 後（`TailMinimal`）の両方が同じ定理を使う。

**(c2) の設計（n279 の後、証明は未完。`Continuation` は検査済み・周期の場は未消費）**: `CycleBound` を `RestartLowerRun.Continuation` に拡張した。ラウンド中 `Lb = C − R − cycle + 1` は動かず（matched で `R+1, cycle−1`、`shiftOne` で `C+1, R−1, cycle+2`）、`[Lb, C]`（shift 中は `[Lb, C + rem]`）は周期 `2h`。shift 開始時の周期は `continuation_start`（`spanPeriod_of_window`、`Lb = C₀ − R₀`）。(c2) は shift guard の不成立が `singlePositive cycle` の一点（`shiftGuardVM` の定義で確認）なので `cycle = 1` を示せばよい。`cycle ≥ 2` なら `e[C−R−1] = e[C−R−1+2h] =`（回文の鏡像）`e[C+R+1−2h] =` 予測 `=` 右の文字、で不一致と矛盾。`cycle ≤ 0` なら `Lb − 1` が span `[C−R, C+R]` の中に入り span は周期 `2h`（`spanPeriod_of_window`）。**これと矛盾させるには不変量に「`Lb − 1` で周期が破れる」（前ラウンドの不一致＋ guard の予測一致＋鏡像から `e[Lb−1] ≠ e[Lb−1+2h]`）と `1 ≤ Lb` を足す必要がある。** 左の読みは `signedRead`（place 0 は `none`）なので、破れは `signedRead raw (Lb − 1) ≠ e[Lb−1+2h]?` の形で持つ。`matched_text` の不一致版（`¬ matched` から左右の文字が違う）も要る。

**未完の部分**: 葉 `hmove` の `periodOnly = true` の残り。(c2) 追い付いた watch（phase 4）が予測を当て、shift guard が立たない（＝`cycleEnd` でない）不一致。Scala `checkPair` は到達不能と主張（lag ゼロなら `left == prediction ⇔ ¬ cycleEnd`）、Lean では継続不変量が要る（未着手）。(c3) phase ≠ 4 の追い付いた watch、遅れている watch、既に broken の chain（未調査）。`obligation_localRealization` は未着手。

## n278 — 葉 `hmove`: 第 1 ラウンドで「不一致状態の chain が既に broken」は到達不能。第 1 ラウンドは全部閉じ、葉に残るのは `periodOnly = true` だけ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は、chain が idle でなく **`s.periodOnly = true`** である不一致状態だけを負う（前提 `(s.periodOnly = false → ∃ wb, s.chain = .broken wb)` を `s.periodOnly = true` に置き換えた。第 1 ラウンドの場合は葉から消えた） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件、`Axioms.olean` が `OracleReady.olean` より後に作り直されたことを確認）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`OracleReady.cycleOracleOn_of_readyLeaves` と `RestartLowerRun.not_broken_firstRound` は標準 3 公理のみ。

**何を証明したか**: Scala 正本 `ScaffoldGalil.background()` が `AssertionError("chain restart violates the confirmed-period invariant")` で主張している到達不能性を、run 不変量として証明した。`RestartLowerRun.FirstRoundGuard c s := c.mode = .scan → s.periodOnly = false → ∀ w, s.chain = .broken w → restartGuardVM s` を `MinimalAcrossRestart` の場 `guard` に追加（`firstRoundGuard_tick`）。消費者は `not_broken_firstRound` → `OracleReady` の `hMove` の第 1 ラウンド・broken 分岐（`¬ restartGuardVM s` と矛盾）。

* 一次情報で確認した事実: `ChainStep.brokenIdle` と `ChainMatched.brokenMatched` は broken を**保つ**。guard の立たない broken は永久に残るので、不変量で排除する以外に無い。broken の生まれ口は 2 つだけ（`not_step_to_broken`）。
* 正 lag の `WatchBreak`（background）: `no_watchBreak_firstRound`。chain の時計 `ClockAt` から `R < 4h`、verifier は右ヘッドより手前なので検査する place は scan 回文の内側かつ `C + 4h` 未満 → 予測＝テキスト。
* lag ゼロの `BreakStep`（matched 比較）: `lateBreak_firstRound`。`distance ≤ 4h − 2` なら予測＝テキスト（matched 比較が与える `R+1` の鏡像等式 `RestartBoundary.matched_text` を使う）、`distance = 4h − 1` は既存の `distance_ne_boundary`。よって `4h ≤ distance`、そこから `restartGuard_of_lateBreak`（`WatchLedger.balance` で margin ≥ 0、`WatchLedger.last_bounds` で `last > 0`、lag は 0）。
* 予測＝テキストの核: `RestartLowerRun.firstRound_watch_predicts` → `ChainBlockText.prediction_eq_text_of_window` → `bounce_eq_text`。材料は `FirstRoundWindow`（窓が現在の中心に固定）、`BlockTextAt`（block の文字＝中心の左のテキスト）、`MovePayload` の block 回文 `PalAt (C − H) H`、`CertAt` の `LeftPeriod`。n277 の時点で消費者の無かった `BlockTextAt`／`FirstRoundWindow`／`bounce_eq_text` はこれで全部消費された。
* `bounce_eq_text`／`prediction_eq_text_of_window` は「scan 回文全体」でなく「その 1 点の鏡像等式」を取る形にした（matched 比較の break では `R + 1` の鏡像しか手元に無い）。
* コピペを避けるため `distance_ne_boundary` の中身から `RestartBoundary.matched_text` を補題として切り出した（両方が使う）。

**未完の部分**: 葉 `hmove` の `periodOnly = true`（shift 後のラウンド。Scala `checkPair` に当たる継続不変量が run 上に無い、未調査）。`obligation_localRealization` は未着手。

**`periodOnly = true` の調査（一次情報、証明は未着手）**:

* Scala 正本（`ScaffoldChain.scala:108-176`）: shift は中心を `h` 動かし `shiftOne` ごとに `cycle += 2`（計 `2h`）、`matched()` ごとに `cycle.dec()`、`cycleEnd ⇔ cycle = 1`、`canShift = watch ∧ lag = 0 ∧ phase = 4 ∧ cycleEnd`。`checkPair` の主張: lag ゼロなら `left == prediction ⇔ ¬ cycleEnd`。
* Lean が run 上に持っているもの: `Coupled'.watch`（`CloseoutPackRun40:81`）の `Other'` ＝ `periodOnly = true ∧ 1 ≤ h ∧ 5h ≤ R + cycle`（scan）。**`cycle` の上界も「左の文字＝予測」も無い。**
* 分岐の見立て: (c1) 追い付いた watch が予測を外す → `RestartLower.move_of_prediction_break` がそのまま使える形だが、`hfour : 4h ≤ R` を `scanMinimal_watch_no_short` の `Sem` 側のためだけに要求している。`periodOnly` ラウンドでは `R ≥ 3h` までしか言えない見込みなので、「`periodOnly = true` なら `WatchMinimal` は `TailMinimal` 側（`base ≤ R`）」を run に載せるか、`cycle ≤ 2h` を載せる必要がある。(c2) 追い付いていて予測＝右の文字、`cycleEnd` でない → Scala は到達不能と主張。Lean では継続不変量（shift 前の span が周期 `2h` を持つので、`cycle − 1` 個ぶん左は周期的）が要る。(c3) `periodOnly` ラウンドで遅れている watch／broken: 未調査。
* (c1) の設計（一次情報で確認済みの事実に基づく。**証明は未着手**）:
  1. 「`periodOnly = true` なら `TailMinimal` 側」は `ScanMinimal (fun _ _ => False) raw s` と書ける（`Move := False` なら `Sem` 側は `watch_moveMinimal` で `False`、copy／back も `False`）。不変量は `scan → periodOnly = true → ScanMinimal (fun _ _ => False) raw s`。tick は source の chain が idle でなければ `modeMinimal_tick_packed`（`Move` 汎用、`BirthMinimal` は `s.chain = .idle` が偽で空虚）、idle なら誕生が無い（誕生すれば target の `periodOnly = false`）ので target も idle。`shift_done` は `ShiftMinimal`（`Move` に依らない）から `scanMinimal_shiftDone`。`BirthMinimal` は `∀ a vq` なので idle の source には使えない点に注意。
  2. `move_of_prediction_break` は `2h ≤ R` も要る（`move_of_activePeriodBreak` の `hhk`）。run 上の `Other'` は `5h ≤ R + cycle` だけで **`cycle` の上界が無い**（`OnlyCredit` も下界 `0 ≤ margin + cycle`）。Scala では `beginShift` で `cycle = 0`、`shiftOne` ごとに `+2`（`rem` は `−1`）、`matched` ごとに `−1` なので、`cycle + 2·rem ≤ 2h`（shift）／`cycle ≤ 2h`（scan）が不変量の候補。これと `Other'` で `3h ≤ R`。

## n277 — 葉 `hmove`: 追い付く前に壊れる watch（この tick の正 lag の break）を閉じた。第 1 ラウンドで残るのは「source の chain が既に broken」だけ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は、chain が idle でなく、かつ「`periodOnly = false` なら **不一致状態の chain が既に broken**」である場合だけを負う（`periodOnly = true` の場合は従来どおり全部） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。

**何を証明したか**: 量化範囲を見直した。chain tick の結果が broken になる経路のうち `watchBreak`（正 lag）は、**source 状態**の chain に仕事が残っている場合なので、source の時計 `ClockAt` から直接 `Rad < 4H` が出る（chain tick の結果は関係ない）。`RestartLowerRun.move_of_working_source`。共通部分は `move_of_bounded_chain`（`Sem` payload ＋ `Rad < 4·chainPeriod` → `move_of_activeBound`）に切り出し、`move_of_working_chain` もそれを使う形に直した。`chainTick_cases` は「source が既に broken ／ source に仕事あり ／ 結果に仕事あり ／ 追い付いた watch」の 4 分岐。

**run 不変量への追加（まだ消費者なし）**: `PalPeg/BlockText.lean`（新規、namespace `PalPeg.ChainBlockText`）と `RestartLowerRun.BlockTextAt`: 第 1 ラウンドの間、period block の文字列は中心の place の stream の 2 番目以降（＝中心の左のテキスト）。`WindowInv` は block の中身とテキストを結ぶ場を持っていなかった。

**未完の部分**: (c) `periodOnly = true`（Scala `checkPair` に当たる継続不変量が run 上に無い、未調査）。(d) 第 1 ラウンドで不一致状態の chain が既に broken（restart guard 不成立）。Scala 正本は `AssertionError` で到達不能と主張しており、Lean では到達不能性の証明が要る: 正 lag の break が起きないこと（追い付き中は予測が外れない）と、lag ゼロの break が `Rad + 1 ≤ 4H` では起きないこと（`distance_ne_boundary` は `distance = 4h − 1` の 1 点だけ）。どちらも `BlockTextAt`＋`Candidate` の回文＋chain の時計から出す見立てで、証明は未着手。`obligation_localRealization` は未着手。

## n276 — 葉 `hmove`: 仕事が残っている第 1 ラウンドの chain（copy／back／追い付き中の watch）を閉じた。第 1 ラウンドで残るのは broken だけ

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は、chain が idle でなく、かつ「`periodOnly = false` なら chain tick の結果が broken」である不一致状態だけを負う（`periodOnly = true` の場合は従来どおり全部） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。

**何を証明したか**: `RestartLowerRun.move_of_working_chain` → `move_of_activeBound`。`Rad < 4H` は chain の時間の台帳から:

* `PalPeg/ChainClock.lean`（新規）: chain 状態の関数 `chainWork`（copy: 残り bit×2 ＋ cells ＋ 1 ＋ lag、back: 左端までの歩数 ＋ 1 ＋ lag、watch: lag）と `chainPeriod`（copy 中は cells ＋ 残り bit − 1）。`chainWork_step`（1 歩で 1 減る・周期は不変）、`chainWork_matched`（一致で高々 1 増える）、`…_done`、`chainWork_chainStart`、`period_of_semWith`（payload の `H` ＝ `chainPeriod`。copy 中は `AnswerAhead` の一意性 `remainingBits_of_answerAhead`）、そして `clock_chainAt`: 不変量 `0 < W → W + E ≤ 2047·(4H − R)`（`E` は直前の一致からの時間）が chain tick 1 回で保たれる。一致 tick は `R+1`（`−2047`）と `E: 2047 → 0`（`+2047`）が相殺する。
* 誕生時 `R ≤ 2H`: `SearchStageHistory.found_radius_le`。`WindowBound` を `span ≤ 2H_prev + 2` に強め、最小候補 `H` は前段の窓に入らない（`candidate_rewindow`）ので `span ≤ 8H`、`Rad ≤ span/4`。`run_of_found`（`found` に入るのは `run` からだけ）。
* run 上: `ClockAt`／`clockAt_tick`／`birth_radius`、`MinimalAcrossRestart.clock`。時刻の上下界は `SearchStageRun.stageAt_field_packed` が返す `Field` から。
* 分岐の網羅: `RestartLowerRun.chainTick_cases`（chain 非 idle の chain tick の結果は broken／仕事あり／追い付いた watch のどれか）。

**未完の部分**: `hmove` の残りは (c) `periodOnly = true`（shift 後のラウンド。Scala `checkPair` に当たる継続不変量が run 上に無い）と (d) 第 1 ラウンドで chain tick の結果が broken（restart guard は source 状態について不成立。正 lag の break か、source が既に broken）。どちらも未調査で、証明は未着手。`obligation_localRealization` は未着手。

### `hmove` の第 1 ラウンド broken の調査（2026-09-20、調査のみ・証明は未着手）

**何が残っているか**: 不一致状態 `s`（scan、`periodOnly = false`、`¬ restartGuardVM s`）で chain tick（一致なし）の結果が `.broken`。経路は 2 つだけ: `brokenIdle`（`s.chain` が既に broken で guard 不成立）と `watchBreak`（この tick で正 lag の break）。lag ゼロの break（`ChainMatched.breaks`）は一致比較でしか起きない。

**Scala 正本の主張**: `ScaffoldGalil.background()` は chain が Broken なら `margin ≥ 0 ∧ last > 0 ∧ lag = 0` でなければ `AssertionError("chain restart violates the confirmed-period invariant")`。つまり「broken かつ guard 不成立」は到達不能と主張している。理由（紙の上）: (1) 追い付き中（lag > 0）は chain の時計で `Rad < 4H`、verifier が読む場所は走査済み span の中で、span は回文、左は `LeftPeriod`（`[C−4H, C]` で周期 `2H`）なので右側 `[C, C+Rad]` も周期 `2H` → 予測は外れない。(2) lag ゼロの break は `Rad + 1 ≤ 4H` では起きない（同じ理由。既存の `RestartBoundary.distance_ne_boundary` は `distance = 4h − 1` の 1 点だけを示していて、証明は `R + 1 = 4h` に特化している）ので、break の時点で `distance ≥ 4H`、よって `margin ≥ 0`・`last > 0`。

**足りない不変量（一次情報で確認）**: 予測記号は `bounce cc b xs` の添字で決まる。`P + 1 − 2h ≥ cen₀ + 1` なら `BlockOn` で `text[P+1−2h]` に直せる（`prediction_eq_text`）が、誕生直後（`P + 1 < cen₀ + 1 + 2h`）は **block の中身そのもの**とテキストの関係が要る。`WindowInv` の copy 節は `∃ ys, v = fill (start cc) ys` で `ys` は任意、back／watch 節も `blockTokens cc b xs` の `xs` とテキストを結ぶ場が無い。copy の各 bit は `present : read (left p) = some a`（walker の左）を書くので、「period テープの文字列 ＝ 中心の左のテキスト（`stream` の接頭辞）」を運ぶ不変量を `WindowInv` に足す必要がある。walker の位置（`chainStart` の `walker = P.place s`、`stream_index`）も要る。

**次の一手の候補**: (i) 上の block–text 不変量を `WindowInv`（copy／back／watch）に足す、(ii) `distance_ne_boundary` を `2h ≤ R + 1 ≤ 4h` に一般化（`hmirror` の添字計算を一般化するだけで、証明書と回文はそのまま使える）し、`R + 1 < 2h` は (i) で、(iii) 正 lag の `WatchBreak` が起きないこと（`not_good_of_watchBreak` の逆向き、(i)＋chain の時計）。3 つ揃えば `BrokenStage` を「scan で broken なら restart guard が立つ」に強められ、`hmove` の broken の場合は `¬ restartGuardVM s` と矛盾して消える。

`periodOnly = true`（shift 後のラウンド）は別件で未調査のまま。

## n275 — 葉 `hmove`: 第 1 ラウンドで追い付いた watch（`lag = 0`）を `phase` によらず全部閉じた（葉は 1 本のまま、前提がもう 1 つ狭まった）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は、chain が idle でなく、かつ chain tick の結果が「`periodOnly = false`・`lag = 0` の watch」**でない**不一致状態だけを負う |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。

**何を証明したか**（`phase ≠ 4` の場合。`phase = 4` は n274）

* `RestartLowerRun.move_of_watch_short` → `CanonicalFallbackInput.move_of_activeBound`（最小性の仮説は現在半径の形に一般化済み）。入力:
  * `Rad ≤ 4h`: mark 台帳に `phase < 4 → boundary − shiftDebt = phase·h` を足し（`MarkLedger.phase`、`advancePhase_val`、`consume_phase_four`、shift 入口は guard の `phase = 4` を渡す）、`WatchLedger.distance_lt_four` で `distance < 4h`。`lag = 0` なので `distance = Rad`。
  * `g ≤ lower` の排除: `LowerAt`（guard を `chain = idle ∨ periodOnly = false` に延長、`lowerGuard_source`。`BrokenStage` は shift mode の間 `periodOnly = true` を運ぶ）。
  * `lower < g < h` の排除: chain の payload `CanonicalSearchProgram.MoveAbove`（DP が自分で示す範囲。旧 `MoveMinimal` は `lower = 0` の場合）。run 上では `MovePayload raw s`／`modeMinimal_tick_lower`、そして第 1 ラウンドの chain が payload そのもの（shift 後の閾値つきの形でなく）を持つことを運ぶ新しい場 `FirstRoundSem`（`firstRoundSem_tick`、`semWith_chainAt` を再利用）。

**未完の部分**: `hmove` の残りは chain 非 idle で、chain tick の結果が (a) copy／back、(b) `lag ≠ 0` の watch、(c) `periodOnly = true` の watch、(d) broken（restart guard 不成立）の場合。(a)(b) は `Rad ≤ 4H` を出す chain の**時間の台帳**が要る（設計は n274 の下の「`Rad < 4h` 側の設計」の 2。`FirstRoundSem`／`LowerAt`／`MoveAbove` は (a)(b) でもそのまま使える形になっている）。(c) は Scala `checkPair` に当たる継続不変量が run 上に無い。(d) は未調査。`obligation_localRealization` は未着手。

## n274 — 葉 `hmove`: 追い付いた第 1 ラウンドの watch（`lag = 0`・`phase = 4`）の場合を閉じた（葉は 1 本のまま、前提がもう 1 つ狭まった）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は、chain が idle でなく、かつ chain tick の結果が「`periodOnly = false`・`lag = 0`・`phase = 4` の watch」**でない**不一致状態だけを負う |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。

**何を証明したか**

* 予測が外れた場合: `RestartLower.move_of_prediction_break` → `CanonicalFallbackInput.move_of_activePeriodBreak`（`Rad ≤ 4h` 不要）。入力は scan span の周期 `2h`（`spanPeriod_of_window`）、その最小性（run 不変量の `ScanMinimal`＋`scanMinimal_watch_no_short`）、fallback 窓の先頭がその周期を壊すこと。最後の点は `RestartBoundary.prediction_eq_text`（予測記号 ＝ `text[P+1−2h]`、`not_breakStep_of_text` から切り出して共有）と、窓の先頭 ＝ 直前に読んだ場所 `text[P+1]`（`stream_index`）と、span の回文性から。
* 予測が当たった場合: `RestartLowerRun.shiftGuard_of_caughtUp`。`phase = 4` から `4h ≤ distance`（`four_of_freshC`、`periodOnly = false` なので `Other'` 側は矛盾）、`WatchLedger.balance` から `margin = distance − 4h ≥ 0`、よって shift guard が立ち、葉の前提 `¬ shiftGuard` と矛盾する。このために chain の台帳（`WatchLedger`／`ChainLedger`）に **margin の canonical 性**を足した（`not_negative_of_nonneg`）。
* 共通部分は `RestartLowerRun.caughtUp_facts`、比較の構成は `CanonicalChainMinimal.compare_of_mismatch`（`shiftPeriodMinimal_packed` と共有）。

**未完の部分**: `hmove` の残りは chain 非 idle で、chain tick の結果が (a) copy／back、(b) `lag ≠ 0` の watch、(c) `phase ≠ 4` の watch、(d) `periodOnly = true` の watch、(e) broken（restart guard 不成立）の場合。調査で分かっていること（証明は未着手）: (a)(b)(c) は「`Rad < 4h`」の側で、`ChainLedger` の `lag − margin = 4·(copy 済み)`／`balance = 4h` は lag／margin の関係だけを持ち、`Rad < 4h` を出すには chain の**時間の台帳**（1 tick に chain 1 歩・2048 tick に一致 1 回、誕生時 `R₀ ≤ 2h`）が要る。その上で `move_of_activeBound` に渡す `MoveMinimal` は restart 後は `lower` を知っている形に弱める必要がある（`g ≤ lower` は `LowerAt` を chain 非 idle の第 1 ラウンドに延長して排除、`lower < g < h` は DP の最小性）。(d) は Scala の `checkPair`（2 半周期の継続不変量: 非終端では左の読み ＝ 予測）に当たる不変量が run 上に無い。`obligation_localRealization` は未着手。

### `hmove` の `Rad < 4h` 側の設計（2026-09-20、調査と準備のみ・この側の証明は未着手）

対象は chain tick の結果が copy／back、`lag ≠ 0` の watch、`phase ≠ 4` の watch（いずれも第 1 ラウンド `periodOnly = false`）。受け口は `CanonicalFallbackInput.move_of_activeBound`（`hmin` は `k = Rad` でしか使われていないので、現在半径の形 `∀ g, 0<g → g<h → 4g ≤ Rad → ¬HasPeriod (Span C Rad) (2g)` に一般化できる）。

**準備済み（n274 の後。全体 build `BUILD=0`・error 0 件を 2026-09-20 に確認、公理は標準 3 本＋義務 2 本で不変、コミット `7fb43ad`／`2670fb6`）**: (i) chain の payload を `CanonicalSearchProgram.MoveAbove raw C lower h`（`lower < g < h` だけ DP が排除）に替え、run 不変量は `ModeMinimal (RestartLowerRun.MovePayload raw s)` を運ぶ（`modeMinimal_tick_lower`）。`MoveMinimal` は `lower = 0` の場合。(ii) 下の 1 は実施済み: `LowerAt` の guard は `chain = idle ∨ periodOnly = false`（`lowerGuard_source`）、`BrokenStage` は shift mode の間 `periodOnly = true` を運ぶ。(iii) `move_of_activeScaledBound`／`move_of_activeBound` の `hmin` は現在半径の形に一般化済み。**これらを使う `Rad < 4h` 側の消費者定理はまだ無い**（2 と 3 が未着手）。

**足りないもの 3 つ**

1. `g ≤ lower` の排除を chain 非 idle の状態で使うこと。`LowerAt` の guard は今 `chain = idle`。第 1 ラウンドの間は中心も `lower` も動かず半径は増えるだけなので、guard を `chain = idle ∨ periodOnly = false` に延ばせる（誕生で `afterBirth` が `periodOnly := false`、`beginShift` で `true`。restart／init／replayStart は chain idle）。
2. `Rad ≤ 4h`（chain の時間の台帳）。候補の不変量: 仕事 `W`（copy: 残り bit ＋ 1 ＋ back の歩数 ＋ 1 ＋ lag、back: 左端までの歩数 ＋ 1 ＋ lag、watch: lag）に対して `0 < W → W ≤ 2047·(4H − Rad) − (2048 − clock)`。scan tick ごとに chain は 1 歩（`W−1`、右辺 `−1`）、一致 tick は `Rad+1`（`−2047`）と clock の巻き戻し（`+2047`）と `lag+1`（`W` は差し引き 0）。誕生時は `R₀ ≤ 2H`: 最小候補 `H` の窓 `S` について `StageHistory` の「前段の窓 `S/2` に候補無し」から `S < 8H`（`Candidate` は接頭辞 `4H+1` だけで決まる）、第 1 段は `S = 8·max(lower,1) ≤ 8H`、そして `Rad ≤ S/4`。copy 中の `H` は `SemWith` の `cells v + n = H + 1` から取れる。
3. `phase ≠ 4`（`lag = 0`）で `distance < 4h`: `FreshC` は下界しか言わない。`MarkLedger.aligned`（`boundary − shiftDebt = n·h`）を「`phase < 4 → n = phase`」に強めれば `distance = boundary + p − 1 < 4h`。2 の不変量は `0 < W` の間しか効かないので、`lag = 0`（`W = 0`）のこの場合は 3 が別に要る。

`periodOnly = true` の watch（Scala `checkPair` の継続不変量）と guard 不成立の broken は別件で未調査。

## n273 — 葉 `hmove` の chain idle 分岐を全部証明して接続（葉は 1 本のまま、前提は `s.chain ≠ .idle` に狭まった）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉 `hmove` は「chain が idle でない不一致状態」だけを負う形になった。chain idle の分岐（探索が段の途中の場合も、最終段で `missed` の場合も）は `RestartLowerRun.move_of_idle` が証明して内部で供給する |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`cycleOracleOn_of_readyLeaves`／`move_of_idle` は標準 3 本のみ。

**何を証明したか**（Python 実測で fallback の約 9 割を占める分岐）

* `PalPeg/SearchStageHistory.lean`（新規）: `StageHistory p lower R v` = 債務バランス `4·(debt + R) (+ quarter) = span (+ work)`（`double` のときだけ補正項）、`wait` での `0 ≤ debt`、候補無し窓 `∃ H, NoCandidate p lower H ∧ WindowBound v.search H`（`wait`: `span ≤ H`、`double`: `span + 2·work ≤ 2H`、`grow`: `span + 8·work ≤ 4H`、それ以外: `span ≤ 4H`）、`started`（`idle` モードに戻らない）。`stageHistory_begin`（第 1 段の窓は `H = 4·lower+3`: `Candidate` は `4h+1 ≤ 長さ` を要るので空虚）、`stageHistory_step`（`searchStep` の全モード。`run` が `wait`／`double` に抜ける瞬間に、失敗した段の窓 `take (span+1)` を `noCandidate_of_failed` で採用する）、`radius_le_window`（`BudgetInv` の credit から `debt` の下界 → 半径 `R ≤ H`。`grow`／`double` の算術は `omega`）。
* `PalPeg/SearchStageRun.lean`（新規）: `BudgetInv` を**中心の実 place** に固定して同梱した `StageAt`（既存の `Field` は place を忘れた `BudgetSome` しか運ばないので、DP 窓と `span` の対応が取れなかった）。`stageAt_tick`／`stageAt_shaped`／`stageAt_invLPS`（origin は `InvLPS` の `ReplayStage` が持つ `Restarted` から）／`stageAt_packed`。`dpPack_of_stage`: 段の途中でも `DpPack`（探索契約）が出る。`DpPack` の DP config は存在量化なので、`pc := 347` の config と `NoCandidate` から `Result` を作る。
* `CanonicalSearchBudget.budgetInv_restarted`: restart 着地の budget を呼び手が指定した place で返す（`budgetSome_restarted` はその系）。
* `RestartLowerRun.move_of_idle`: `lower` 以下は `LowerAt`（現在の半径）、`lower` より上は探索（段の途中は窓、最終段は DP 結果）。

**未完の部分**: `hmove` の chain 非 idle 分岐（copy／back、稼働中 watch、guard 不成立の broken）。調査で分かったこと（証明は未着手）: 既存の `move_of_preShift_packed`／`move_of_live_sem_packed` は `hquarter : Rad ≤ 4h` を**仮説として**取っており、その producer は無い。`Rad ≤ 4h` は「chain の誕生時 `R₀ ≤ 2h`（`found_radius_le_two_period`）＋ copy／back／追い付きの間に進む一致は高々数回」という**時間の台帳**から出る事実で、`RestartStageLedger.WatchLedger` の `balance = 4h` は lag／margin の関係だけで clock を持っていない。watch が追い付いた後（`lag = 0`）で guard が立たないのは予測が外れた場合で、そこは `CanonicalFallbackInput.move_of_activePeriodBreak`（`Rad ≤ 4h` 不要）が受け口になる。その入力（周期・最小性・break）の接続は未着手。`obligation_localRealization` は未着手。

## n272 — 葉 `hmove` の idle＋`missed` 分岐を証明して接続（葉の本数は 1 のまま、前提が 1 つ狭まった）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉は `hmove` の 1 本のまま。ただし `hmove` は前提 `¬ (s.chain = .idle ∧ vq.search.mode = .missed)` と `PackedFromBoot ⟨c₀,r₀⟩` を受け取る形になり、idle＋`missed` 分岐は `RestartLowerRun.move_of_idle_missed` が証明して内部で供給する |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。

**何をしたか**

* `CanonicalSearchProgram.LowerExcludedFrom raw C lower base`: `base` 以上の半径の span すべてで `δ ≤ lower` の周期 `2δ` が無い。`LowerExcludedAtBreak.lowerExcluded_of_break` はこの形（`base = d+1`、break を含む span）を出すようになり、前提 `d+1 ≤ 4(last+1)` は不要になった（`toLowerExcluded` が旧形に落とすときだけ使う）。
* run 不変量の載せ替え: `LowerAt` は「`∃ base ≤ 現在の半径`, `base ≤ 4(L+1)`, `LowerExcludedFrom … base`」、`LastExcluded raw C Rad w` は restart が見る半径 `Rad` を base にする。`BrokenStage` の payload は `Extra : ℕ → ℕ → Watch.State → Prop`（centre、半径）。
* `RestartLowerRun.no_lower_period_at_scan`: chain idle の scan 状態で、**現在の半径**の span に `δ ≤ lower` の周期が無い（fallback 移動不等式の `hlow`）。
* `CanonicalChainMinimal.move_of_idle_missed_packed` は `lower = reset` の代わりに `hlow` を取る。`OracleRun` の fallback 葉に `PackedFromBoot` を通した。

**未完の部分**: `hmove` の残り分岐（設計表は n271 直下の「`hmove` の設計」）。idle で探索が段の途中（`grow`／`lower`…`run`／`wait`／`double`）の分岐は既存部品が無く、新しい run 不変量 `StageHistory`（失敗した段の窓に `Candidate` が無い ∧ `Rad ≤ その窓`）と `value debt + Rad` の台帳が要る。`GalilSearchContractStage.no_span_period_of_stage` の核は「窓に `Candidate` が無い」だけを使っている（`hnone`）ので、帰着先はそこ。copy／back、稼働中 watch、guard 不成立の broken の各分岐も未着手。`obligation_localRealization` は未着手。

## n271 — 葉 `hshiftPeriodMinimal` を証明して `OracleReady` に接続（producer の葉は 2 → 1）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉が `hshiftPeriodMinimal`／`hmove` の 2 本から **`hmove` の 1 本**になった（`hshiftPeriodMinimal` は `RestartLowerRun.scanMinimal_packed` → `CanonicalChainMinimal.shiftPeriodMinimal_packed` が証明し、定理の仮説から外して内部で供給） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.PalInPeg.unconditional` は `propext`／`Classical.choice`／`Quot.sound`／`obligation_cycleOracleOnPackedRun`／`obligation_localRealization`（本数は変化なし）。`cycleOracleOn_of_readyLeaves` と `scanMinimal_packed` は標準 3 本のみ。

**葉の量化範囲を直した（過剰量化の疑い、9 例目）**: 葉 `hshiftPeriodMinimal` は任意の `InvLPS` origin に量化されていたが、`InvLPS` の `ReplayStage` は「`Restarted r Rad last` から来た」としか言わず、`lower = last > 0` の origin では `≤ last` の周期を排除する履歴が run の外にある。その形の葉は偽の疑いが濃い（機械検査した反証は無い）。公理の guard `ScanOnPackedRunFromInvLPS` は元から `PackedFromBoot ⟨c₀,r₀⟩` を持っているので、`OracleRun.cycleOracleOn_of_leaves`／`_of_fourLeaves` の shift 葉にそれを渡すだけで済んだ（公理の文は不変）。

**証明の経路**

* `CanonicalSearchProgram.LowerExcluded raw C lower`（n270 後に追加）: 再始動が入れる下界 `last` の意味。`RestartLower.lowerExcluded_at_break` が lag ゼロ break で出す（Fine–Wilf `no_period_across_break`＋旧 chain の最小周期＋break の 1 箇所不一致＋mark 台帳）。
* `RestartStageRun.BrokenStage` に guard 状態の追加 payload `Extra : ℕ → Watch.State → Prop`（centre 位置キー）を持たせ、`brokenStage_tick` の場合分けを再利用（コピペなし）。`restartStage` 用は `Extra := fun _ _ => True`。
* `RestartLowerRun.MinimalAcrossRestart`（run 不変量）: `ModeMinimal (fun _ _ => True)` ∧ `LowerAt`（scan・chain idle のとき `value lower = L → LowerExcluded raw C L`）∧ `BrokenStage (LastExcluded raw)`。3 つは相互依存（誕生は `LowerAt`、restart 時の `LowerAt` は `BrokenStage`、break 時の payload は `ScanMinimal`）なので 1 本の帰納 `minimalAcrossRestart_packed`。
* origin: `lowerAt_of_packedFromBoot`。boot からの packed run の 1 tick 目を `CloseoutStageBoot.invLPS_init` の着地と `GalilTickFair.tick_canonical_unique` で同定し（`lower = reset`）、そこから origin まで `minimalAcrossRestart_packed` を走らせる。
* 最小周期スタック（`Sem`／`WatchMinimal`／`ScanMinimal`／`ModeMinimal`／`BirthMinimal`）は payload `Move` でパラメータ化済み。`birthMinimals_packed` は `lower = reset` の代わりに `LowerExcluded` を取り、`MoveMinimal` は `lower = reset` のときだけ返す。`shiftPeriodMinimal_packed` は scan 状態の `ScanMinimal ∧ BirthMinimal` を入力に取る。`modeMinimal_tick_packed` を切り出して `budgetMinimal_tick` と共有。参照ゼロだった `birthFutureMinimal_packed` は削除。

**新規モジュール**（`OracleReady` から import。sorry なし）: `PalPeg/PeriodAcrossBreak.lean`、`PalPeg/LowerExcludedAtBreak.lean`、`PalPeg/RestartLower.lean`、`PalPeg/RestartLowerRun.lean`。

**未完の部分**: producer の残り葉は `hmove`（Galil の移動不等式、restart guard の下の比較不一致状態）。一次情報で分かったこと: idle＋`missed` 分岐の消費者 `CanonicalSearchHistory.dpPack_of_idle_missed_packed` は「**現在の半径 `Rad`** の span で `δ ≤ lower` の周期が無い」を要る。今の `LowerExcluded` は `k ≥ 4(lower+1)` の span しか言わないので足りない。break を含む span すべて（`k ≥ 再始動時の半径`）に強めた形が要る（`no_period_across_break` の前提 `δ + h ≤ d` は `last_bounds` が既に出している。強めた形の証明と run への載せ替えは未着手）。active chain 分岐は `CanonicalFallbackInput.move_of_activePeriodBreak`（`Rad ≤ 4h` 不要、周期＋最小性＋break）が既にあり、入力は `RestartLower.spanPeriod_of_window`／`scanMinimal_watch_no_short` と同じ材料。`hmove` も任意 origin に量化されているので `PackedFromBoot` を通す必要がある。`obligation_localRealization` は未着手。

### `hmove` の設計（2026-09-20、調査のみ・証明は未着手）

**帰着先はテキストの事実**: `GalilLeafDp.contract_of_dpPack` により、`hmove` の結論は「`Span raw C Rad` の周期 `p` は全部 `Rad < 2p`」から出る（`CanonicalFallbackInput.move_of_dpPack`）。`GalilSearchContract.search_contract_of_stage` の入力は (i) `Rad ≤ span'`、(ii) 窓 `(stream p).take (span'+1)` に `lower` より上の `Candidate` が無い、(iii) `hlow`: **現在の `Rad`** の span で `δ ≤ lower` の周期 `2δ` が無い。

**不一致時の chain `z` による分岐**（Python 実測: fallback 123 回のうち idle 115／watch 8）:

| 分岐 | 既存部品 | 足りないもの |
|---|---|---|
| idle＋`missed`（最終段） | `dpPack_of_idle_missed_packed` | (iii) を `lower > 0` で（`LowerExcluded` を「break を含む全 span」= `k ≥ 再始動時半径` に強める。`no_period_across_break` の `δ + h ≤ d` は `last_bounds` が出している） |
| idle＋段の途中（`grow`／`lower`…`run`／`wait`／`double`） | **無い**。`StageFailed` は「現在の DP が完了して失敗」を要るが、段の途中では DP テープは reset 済み | 新しい run 不変量 `StageHistory`: `∃ H, (∀ h, ¬Candidate ((stream p).take (H+1)) lower h) ∧ Rad ≤ H`。第 1 段は `H = 4·lower+3`（`Candidate` は `4h+1 ≤ 長さ` を要るので空虚に真）、段が失敗するたび `H := その段の span`。維持には `value debt + Rad = span/4`（`start` で `debt = −r₀`、grow は span+8／debt+2、match は radius+1／debt−1）と `debt ≥ 0`（`BudgetInv` の credit から。grow 中は `BudgetInv.grow` と `StageEntry 3r₀ ≤ 5·lower` から `Rad ≤ 1.75·max(lower,1)+1 ≤ 4·lower+3`）が要る。`BudgetInv` は `debt` と半径の関係を持っていない |
| copy／back（誕生直後） | `move_of_preShift_packed`（`lower = reset` と `MoveMinimal` 前提） | `lower` を知っている `MoveMinimal` の弱化（`g ≤ lower` は (iii) で、`lower < g < H` は DP で排除） |
| 稼働中の watch で shift guard 不成立 | `move_of_activePeriodBreak`（`Rad ≤ 4h` 不要）／`move_of_activeBound` | 周期・最小性・break の入力（`RestartLower.spanPeriod_of_window`／`scanMinimal_watch_no_short` と同じ材料） |
| broken で restart guard 不成立 | 未調査 | 未調査 |

`hmove` も任意の `InvLPS` origin に量化されているので `PackedFromBoot` を通す（`hshiftPeriodMinimal` と同じ）。Scala 正本は stage deadline を `IllegalStateException` で守っているだけで、`SCA_GALIL.md` は仕事量台帳を未検証と明記している。Lean 側の `CanonicalSearchBudget.BudgetInv` がその台帳で、`ready_of_invLPS_shaped` まで証明済み。

## n270 — 葉 `hrestartStage` を証明して `OracleReady` に接続（producer の葉は 3 → 2）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 公理自体は残る。producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉が `hrestartStage`／`hshiftPeriodMinimal`／`hmove` の 3 本から **`hshiftPeriodMinimal`／`hmove` の 2 本**になった（`hrestartStage` は `RestartCertificate.restartStage` が証明し、定理の仮説から外して内部で供給） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、`2026-09-20 に `lake build --quiet PalPeg` を再実行、error 0 件`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。** `#print axioms PalPeg.OracleReady.cycleOracleOn_of_readyLeaves` は `propext`／`Classical.choice`／`Quot.sound`。

**n269 の未完 3 点の決着**

* `NoBoundaryBreak` → **証明済み**（`RestartCertificate.noBoundaryBreak_packed`）。核は `RestartBoundary.not_breakStep_of_text`: 予測記号 `= bounce[(P+1−anchor) % 2h]`（`symbol_of_coreP`）`= text[P+1−2h]`（`BlockOn`）`= text[C−R−1+2h]`（scan の回文）`= text[C−R−1]`（左証明書）`= text[P+1]`（matched）なので `BreakStep` の `read ≠ some a` と矛盾。`RestartBoundary.distance_ne_boundary` が 3 つの添字等式を `ScanInvariant`＋`LeftCertificate`＋matched 比較から出す。左端（`C−R−1 ≤ 0`）では `read left = none` で matched が成立しないので場合分けで消える。
* 左証明書の運搬 → `RestartCertificate.CertAt`／`certAt_tick`／`certAt_packed`。誕生点は `candidate_periodOn`（`birthMinimal_packed` 経由、`lower` 不問）、中心が動かない間は chain の semantic datum に乗せる、shift 入口は全区間周期（`periodOn_right_succ`＋`periodOn_span_of_next`、`4h ≤ R` は `four_of_guard`）で着地中心に張り直す。**コピペを避けるため `CanonicalChainMinimal.Sem` を証明書について一般化**（`SemWith Cert`、`Sem raw C` はその instance、`sem_step`／`sem_matched`／`sem_tick`／`semWith_start`／`semWith_chainAt` は任意の `Cert`）。
* replay 中の `ScanInvariant` → **既に pack にあった**（`IPackMW.m2.scanGeomR`）。n269 で「pack に無い」と書いたのはウチの見落とし（`budgetMinimal_tick` が使っていた）。`scanInvariant_packed` にまとめた。`Canonical length` は `CPack.canon`（`cpack_steps`＋`hfloor_of_invLP2`＋`cpack_of_entry`、`CloseoutMarksPack` と同じ recipe）。

**新規モジュール（すべて `OracleReady` から推移的に import。sorry なし）**

| ファイル | 中身 |
|---|---|
| `PalPeg/RestartStageLedger.lean` | `MarkLedger`／`WatchLedger`／`ChainLedger`、`WatchLedger.stageEntry_of_break` |
| `PalPeg/RestartStageRun.lean` | `LedgerAt`／`ledgerAt_packed`、`BrokenStage`／`brokenStage_tick`／`brokenStage_packed`、`restartStage_packed` |
| `PalPeg/RestartBoundary.lean` | `not_breakStep_of_text`、`LeftCertificate`、`distance_ne_boundary` |
| `PalPeg/RestartCertificate.lean` | `CertAt`／`certAt_packed`、`scanInvariant_packed`、`noBoundaryBreak_packed`、`canonicalLength_packed`、**`restartStage`** |

**次の goal `hshiftPeriodMinimal` の設計（調査のみ・未実装。定義と型は読んだ、証明は 1 行も書いていない）**

* 葉と既存 `CanonicalChainMinimal.shiftPeriodMinimal_packed` の差は前提 1 個だけ: 既存は `s.lower = reset`、葉は `¬ restartGuardVM s`。`lower = reset` が効いているのは (a) `BudgetMinimal` の guard（`intro hy : y.vm.lower = reset`）と (b) 誕生点の `birthMinimals_packed`（`futureMinimal_of_candidate`／`moveMinimal_of_candidate` の `hlower : lower = 0`）。
* 既存部品: `GalilMinimalPeriod.no_short_period_of_minimal` は **`hlow : ∀ δ, 0 < δ → δ ≤ lower → ¬ HasPeriod (Span …) (2δ)` を仮説に取る一般形が既にある**（`lower = 0` 版はその特殊化）。`GalilPeriodNext.periodOn_fineWilf`、`GalilBreakNoBelow.noBelow_after_break_of_mismatch`（`q ≤ p` の排除）もある。
* 要る新しい run 不変量: `LowerExcluded raw C lower`（chain idle の scan 状態で、探索の `lower` 以下の半周期 `δ` は中心 `C` の十分大きい span の周期 `2δ` でない）。`lower = 0`（init／fallback／replayStart 後）では自明。broken restart では `lower = last`: 旧 chain の最小性証明書（`SemWith`/`TailMinimal`）＋ break の 1 点不一致 ＋ Fine–Wilf ＋ **n270 の `MarkLedger`（`last ≤ distance − h`、`boundary = last + h`）** から出す。span が break 点を含むこと: `k ≥ 4H > 4·last ≥ 4(d − 2h + 1) ≥ d + 1`（`d ≥ 4h`）。restart は中心を動かさず、idle の間は shift が無く、mismatch は fallback で `lower` を reset するので、不変量は restart から次の誕生まで中心固定で運べる。
* **P1 済み（2026-09-20、`lake env lean` で検査、未接続）**: `CanonicalSearchProgram.LowerExcluded raw C lower`（`4(lower+1) ≤ k` の span で `δ ≤ lower` の周期 `2δ` が無い）と `lowerExcluded_zero` を定義し、`futureMinimal_of_candidate` の前提 `lower = 0` を `LowerExcluded` に差し替えた（呼び出し側 `birthMinimals_packed` は `lowerExcluded_zero` を渡す）。`moveMinimal_of_candidate` は `4g ≤ k` しか取らないので `LowerExcluded` では足りず未変更（`hmove` 側の問題）。P2 の要点: `sem_matched` の `breaks` 枝は `SemWith` を broken 状態まで運ぶので旧 chain の証明書は restart 時点で手元にある。break tick で「`text[C+R−2h] ≠ text[C+R]`」を broken 状態の場として記録し（`BreakStep` の `read ≠ some a` と `BlockOn` から直接）、純粋補題（`periodOn_fineWilf`＋最小性＋不一致 ⇒ `δ ≤ last ≤ d − h` の周期 `2δ` は break 点を含む span に無い）で restart tick の `LowerExcluded` を出す。
* **P2 の部品（2026-09-20、すべて検査済み・`hshiftPeriodMinimal` へは未接続）**: `PeriodAcrossBreak.no_period_across_break`（Fine–Wilf＋最小性＋`periodOn_extend_dvd`）→ `LowerExcludedAtBreak.lowerExcluded_of_break`（入力: 旧 span の `PalAt C d`／`PeriodOn (2h) (C−d) (C+d)`／最小性／1 点不一致 `text[C+d+1−2h] ≠ text[C+d+1]`／`2h ≤ d`／`last + h ≤ d`／`d+1 ≤ 4(last+1)`）。台帳側は `MarkLedger.marks` の初期選言に `boundary ≤ 0` を足して `WatchLedger.last_bounds`（`4h ≤ d` なら `last + h ≤ d ∧ d+1 ≤ 4(last+1)`）を出した。**まだ無いもの**: (i) break tick で span 全体の周期 `PeriodOn (2h) (C−d) (C+d)` を作る補題（材料: `periodOn_of_blockOn`＋`periodOn_extend_left`＋`palAt_block_periodic` の `PalAt (C+h) h`＋scan の回文で中心またぎ）、(ii) 旧 chain の最小性（`SemWith`／`TailMinimal`）と 1 点不一致を broken 状態の場として運ぶ run 不変量、(iii) restart tick での `LowerExcluded` の確立と idle 区間での保存、(iv) `BudgetMinimal` の guard `lower = reset` の差し替え。
* **P2 追加（2026-09-20、検査済み・未接続）**: `LowerExcludedAtBreak.periodOn_span_of_halves`（右半分＝検証済みブロック、左半分＝scan の回文、中心またぎ＝`PalAt (C+h) h`）、`RestartLower.spanPeriod_of_window`（lag ゼロの `WatchWindow` から `PeriodOn (2h) (C−d) (C+d)`）、`RestartLower.break_mismatch_of_window`（`BreakStep` から `text[P+1−2h] ≠ text[P+1]`、`not_breakStep_of_text` の対偶）。これで `lowerExcluded_of_break` の入力のうち**旧 chain の最小性以外**は窓と台帳から出る。
* **設計上の発見（機械検査した反証は無いので「偽の疑い」）**: `Sem` の payload に入っている `MoveMinimal raw C H`（`∀ g < H, 4g ≤ k → ¬ HasPeriod (Span C k) (2g)`）は **restart で生まれた chain では偽の疑いが濃い**。`lower = last > 0` のとき、旧周期の倍数 `g ≤ last` は break 点を含まない小さい span（`4g ≤ k < d+1`）では本物の周期で、DP は `lower < g` の候補しか見ないので排除しない。`FutureMinimal` の側は `4H ≤ k`（`k` が break 点を含む）なので `LowerExcluded` で救える。帰結: 旧 chain の最小性を restart まで運ぶには `ModeMinimal`／`ScanMinimal`／`WatchMinimal` の payload を `FutureMinimal` だけ（＋ `LowerExcluded` の履歴）に分けて、`BudgetMinimal` の guard `lower = reset` を「idle の scan 状態で `LowerExcluded raw C (value lower)`」に差し替える一体の帰納が要る（`ModeMinimal` の誕生 hook が `LowerExcluded` を要り、restart tick の `LowerExcluded` が直前の `ModeMinimal` を要るので別々には回らない）。`MoveMinimal` は `hmove` 側だけで使うので、そちらは `lower` つきの弱い形に直す必要がある。
* **P2 本体（2026-09-20、検査済み・未接続、コミット `0695221`）**: `CanonicalChainMinimal` の最小周期スタックを `Move : ℕ → ℕ → Prop` でパラメータ化（`34fd415`、packed 定理は `Move := MoveMinimal raw` で内容不変）。`RestartLower.lowerExcluded_at_break`: window-packed な scan 状態の lag ゼロ break で、`ScanMinimal Move raw s`（任意の `Move`）＋`ChainLedger 0`＋`ScanInvariant`＋`RadiusRep`＋break 後 `margin ≥ 0`＋`distance ≠ 4h−1`＋`value last = L` から `LowerExcluded raw C L`。**残り**: (a) 運ぶ不変量 `J := ModeMinimal (fun _ _ => True) ∧ LowerAt ∧ BrokenLower`（`LowerAt`: idle の scan 状態で `s.lower = ofNat L → LowerExcluded raw C L`／`BrokenLower`: guard 状態で `value last = L → LowerExcluded raw C L`）の tick 補題と packed 帰納。init／replayStart は `lower = reset` なので `lowerExcluded_zero`、restart は `BrokenLower` から、誕生 hook は `futureMinimal_of_candidate`＋`LowerAt`、break tick は `lowerExcluded_at_break`（`hinterior` は `noBoundaryBreak_packed`、`hledger` は `ledgerAt_packed`）。(b) `shiftPeriodMinimal_at` を `J` から出して前提 `s.lower = reset` を外し、`OracleReady` の葉に接続。
* 手順: (P1) `futureMinimal_of_candidate`／`moveMinimal_of_candidate` の `hlower` を `hlow` 形に一般化 → (P2) `LowerExcluded` を packed run に沿って運ぶ（restart tick が本体）→ (P3) `BudgetMinimal` の guard を差し替え、`shiftPeriodMinimal_packed` の前提を葉の形にして `OracleReady` に接続。

**未完の部分**: producer の残り葉 `hshiftPeriodMinimal`（restart 後は `lower = last ≠ reset`。`CanonicalChainMinimal.shiftPeriodMinimal_packed` は `lower = reset` 前提で未接続、`≤ last` の周期の排除が要る）と `hmove`（Galil の移動不等式）。`obligation_localRealization` は未着手。

## n269 — `hrestartStage` を 1 仮説 `NoBoundaryBreak` まで還元（未接続）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 変化なし。葉 `hrestartStage` の producer `RestartStageRun.restartStage_packed` を書いたが、仮説 `NoBoundaryBreak` が残っており `OracleReady` へは**未接続** |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、3e6e411 時点。新 2 モジュールはルート未 import なので全体 build は再実行していない。モジュール build `PalPeg.RestartStageRun` は `BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**一次情報で確かめたこと（定義を読んだ）**

* `chainStart` は `lag := radius, margin := radius`。`copyBit` は `decFour margin`、matched は `inc lag`／`inc margin`、`BreakStep` は失敗 consume ＋ `inc margin`、`chainShiftOne` は `distance／boundary／last／margin` を一斉に `dec`。よって watch では **`distance + lag − margin = 4h`**（既存の `GalilScaffoldChainWatch.balance`）。
* found 時の半径は `≤ 2h`（`found_radius_le_two_period`）。だから **「誕生時に `4h ≤ R`」は偽**で、margin は負から始まる（過去の自分の計画メモの F1 は誤り）。
* guard の `margin ≥ 0` から出るのは `4h − 1 ≤ distance` まで。**境界 `distance = 4h − 1` では `R = 4h`・`last = 2h` で `StageEntry`（`3R ≤ 5·last`）は偽**。この状態が到達不能であること（周期領域内の matched 比較は break しない）を別に示す必要がある。これは Scala の `AssertionError("chain restart violates …")` が主張している内容と同じ。
* Python 参照実装の実測（`stage_probe`, `lagbreak2`）: restart 60 回超で `3R ≤ 5·last` 違反 0、正 lag の break 0、margin の最小観測値 1。有限テストであり証明ではない。

**書いたもの（すべて `lake env lean`／モジュール build で検査、sorry なし、標準 3 公理）**

* `PalPeg/RestartStageLedger.lean`: `MarkLedger h shiftDebt k`（forward: `d = boundary + p − 1`／backward: `d = boundary + h − 1 − p`、`boundary = last ∨ boundary = last + h`、`boundary − shiftDebt = n·h`、3 カウンタ canonical）と `MarkLedger.consume`／`shiftOne`／`beginShift`。`WatchLedger`（marks ＋ `balance = 4h` ＋ lag canonical・非負）。`ChainLedger` と `chainLedger_step`／`_matched`／`_chainAt`。**`WatchLedger.stageEntry_of_break`**: lag ゼロの break で、break 後 `margin ≥ 0` かつ `distance ≠ 4h − 1` なら `StageEntry Rad last ∧ Canonical last`。
* `PalPeg/RestartStageRun.lean`: `LedgerAt`／`ledgerAt_tick`／`ledgerAt_packed`（packed run の全点で台帳）。`BrokenStage`／`brokenStage_tick`（restart-first の `Canonical` の下で保存。guard 状態は次 tick で restart されるので broken の guard 状態は break 直後の 1 状態だけ）。`brokenStage_packed`、**`restartStage_packed`**（packed run の guard 状態の restart は `Restarted ∧ StageEntry` に着地。入力: `NoBoundaryBreak`、`ScanInvariant`、`Canonical length`）。

**未完の部分（区別して書く）**

* 仮説 `NoBoundaryBreak`（未証明）: packed run 上の matched 比較で `ChainStep s.chain (.watch w1) ∧ BreakStep w1 w'` なら `distance w1 ≠ 4h − 1`。証明の筋: 予測記号 `= bounce[(P+1−anchor) % 2h]`（`symbol_of_coreP`）`= text[P+1−2h]`（`BlockOn`）`= text[C−R−1+2h]`（`ScanInvariant` の回文）`= text[C−R−1]`（**左証明書** `PeriodOn (2h) (C−4h) C`）`= text[C+R+1]`（matched）。左証明書は誕生点で `GalilCandidatePeriod.candidate_periodOn`（`birthMinimal_packed` 経由、`lower` 不問）、shift 入口で全区間周期（`periodOn_span_of_next`、`R ≥ 4h` は `four_of_guard`）から作り、中心に沿って運ぶ新しい run 不変量が要る。
* replay 中（`replaying = true`）は `LPackM.scanGeom` が `ScanInvariant` を出さない。`restartStage_packed` は `ScanInvariant` を入力に取る形にした。`NoBoundaryBreak` の証明でも同じ問題が出る（replay 中の `ScanInvariant` は `OracleTick.replayStage` の `Restarted … 0 reset` から replay 区間に沿って運ぶ必要がある）。
* 葉 `hrestartStage` の形（`OracleRun.settle`／`CanonicalReplay.comparison` の呼び出し側）に `ScanInvariant`／`Canonical length` を渡す変更は未着手。

## n268 — canonical 方針を restart-first に戻した（no-restart は `hmove` と両立しない）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 型の tick 述語が `GalilTickFair.Canonical`（no-restart）から `ShapedRun.OracleTick entry`（restart-first の `Canonical` ＋ fresh search の再入点）に。producer `OracleReady.cycleOracleOn_of_readyLeaves` は標準公理のみのまま、葉は `hrestartStage`（新）／`hshiftPeriodMinimal`／`hmove`。**公理は減っていない。** |
| `obligation_localRealization` | `CanonTrace` が参照する `Canonical` が restart-first になった。`tick_canonical_unique`／`canonical_trunc` は新方針で再証明済み |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**なぜ変えたか**: n256 で葉 `hrestart`／`hreplayStart` を消すために「oracle の run は restart しない」としたのはウチの判断で、それが時間評価の根拠を壊していた。Lean でも Python でも break 後は `chain ≠ idle` で search が凍るので、broken のまま走ると次の fallback の半径 `R` が移動量 `d` に対して非有界になる。診断（`docs/palindromes-in-peg/diagnose_no_restart_fallback.py` と同じ計装、診断語の 40 文字 prefix＋周期語に欠陥を入れた 12 語）:

| 方針 | fallback 数 | `R > 4d` | fallback 時の chain |
|---|---|---|---|
| restart あり（正本） | 123 | 0 | idle 115／watch 8、AssertionError 0 |
| restart なし | 124 | 1（`R=25, d=6`、broken） | idle 108／broken 8／watch 8 |

Lean の形式反証は無いので旧 `hmove`（no-restart）は「偽の疑いが濃い（Python 診断で再現）」と記録する。

**何をしたか**

* `GalilTickFair.Canonical`: `noRestart` → `restartFirst`（`Fair` と同じ節）。guard の下では `restartVM` は不可能（`not_restartVM_of_noGuard`）。`canonical_of_restart` 追加、`tick_canonical_unique` は guard で場合分け。`CanonicalLocalRealizes.canonical_trunc` は `restartGuard_of_trunc`／`restartVM_trunc` で再証明（`Tick` 前提が不要になった）。
* `ShapedRun`: `ShapedSteps` の restart 節を「restart は `Restarted ∧ StageEntry ∧ scan ∧ clock = 2048` に着地」に。`restartGuard_background`（背景 tick は guard を立てない: 背景の break は正 lag だけ）。`OracleTick entry w`（canonical ＋ restart／replayStart の着地）を packed path の tick 述語に（`CloseoutCheckW` の `R` を語で添字づけ）。
* `OracleRun`: 運ぶ述語 `I` に `¬ restartGuardVM` を追加。`settle`（full-clock の scan 着地で guard が立っていれば restart tick、heads／centre／replay は不変、`MInv`／`Refreshed` は移送）を一致比較の着地に挿入。cost は `matchPiece` の `wait` が 1 増えるだけ（`≤ 2048`）。shift 着地は watch、fallback／replay 着地は葉／`segment` が `¬ guard` を返す。
* `CanonicalReplay.comparison`／`segment`: 比較ごとに `settle`。tick 数は `N ≤ rem·2049`（`R ≤ 4d` の下で `≤ 8·2048·d`）。
* `CanonicalSearchReady.field_alongShaped`／`CanonicalSearchHistory.atState_tick`: restart 着地で `field_restarted`／`atState_restart`。chain readiness（`birthCopy_packed`）は新方針でも通る。
* 削除: `CanonicalPeriod.lean`（「canonical trace 上で `lower = reset`」は restart-first では偽）、`ReadyTransport.lean`（参照ゼロ）。

**次の goal**: `hrestartStage`。材料: `Restarted` の各場は pack から（`centreRep`／`scanGeom(R)`／`radiusScan`）、`Canonical last`／`0 ≤ last`／`3·Rad ≤ 5·last` は chain の ledger（`GalilScaffoldChainRestart.run_order`／`run_canonical`、`GalilScaffoldChainSweep.four_boundaries`）を packed run 上の watch の履歴（`WindowInv`）に接続して出す。その後 `lower = last` の履歴（`≤ last` の周期の排除、Fine–Wilf＋break）で `hshiftPeriodMinimal`／`hmove` の idle 分岐。

## 2026-09-19: inline draft reverted; checkpoint

ユーザー指示で未完成・未検証の cycle inline proof を撤去し、既存の2公理による
最終定理へ戻した。`CanonicalChainMinimal` の shift 最小性、search/chain readiness、
fallback/replay、および周期境界の証明は保持。cycle と local realization は未解消。

**次の作業で要確認:** Scala/Python は broken chain で search を restart するが、
Lean の `GalilTickFair.Canonical.noRestart` は禁止する。Python 正本の broken-restart
分岐だけを省いた実行で、入力 prefix `abaaaaababaaabaaaaabaaaaabaaaaabaaaa`、
centre=45、radius=25、fallback move=6、chain=broken を観測した。
従って、この実行では `radius ≤ 4*move` は不成立。これは Python 診断であって
Lean の packed-run 到達可能性の証明ではなく、cycle 公理そのものの反証とも断定しない。
この条件の相違を解決せず、残差を単なる接続作業と扱わないこと。

検証: `cd lean-pal && lake build` 成功（9705 jobs）。
`#print axioms PalPeg.PalInPeg.unconditional` は標準3公理＋上記2公理。
`shiftPeriodMinimal_packed` は標準3公理のみ。`sorryAx` なし。
新規 import の位置エラーを `Workbench.lean` で修正してから全体 build を再実行した。
Python 診断もコミット対象のスクリプトで再現済み。

## n264 — canonical fallback のコピー元を Scala の右ヘッドへ修正

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。canonical policy と fallback 葉のpinを修正したため義務の意味は変わる。これは以前の公理を証明したことではない。 |
| `obligation_localRealization` | 未解消。参照する canonical policy が同様に変わる。 |

- Scala正本 `scala/pal/src/main/scala/pal/ScaffoldGalil.scala:309` の `beginFallback()` は line 314 で **`walker.copyFrom(right)`** を実行する。旧canonical条件 `u.fpp.walker = u.walker` は、Leanでは保存される旧search cursorを選んでおり、このコピー元と違っていた。`prepareWindow()` の `walker.copyFrom(center)` との混同を訂正した。
- `GalilTickFair.rightPlace` は右ヘッドのfocus・left stack・gapを既存 `lettersOf` でdecodeする。`Canonical.fallbackPlace`、`canonical_of_scan_copy`、`OracleRun` と `OracleReady` のfallback葉を `u.fpp.walker = rightPlace u` に変更。
- `tick_scan_noRestart_unique` を「fallbackで保存されるselector」で一般化して証明の重複を回避。旧 `Fair` は過去の条件付き定理のためsearch cursorのpinを維持し、**Scalaそのものだという説明を撤回**。新canonical一意性はright-head selectorで証明済み。
- `fallbackAt_rightPlace` が新しいpinを満たす入口を構成する。`fallback_right_not_searchPin` は、コピー長の境界を満たす入口で新旧pinが一致しないことをLeanで証明する（標準公理のみ）。この反例をbootからの到達可能性やPAL公理全体の反証と取り違えない。
- `beginFallbackVM'` のコピー長境界は変更していない。抽象VMではsearchとFPPのwalkerを別フィールドで持つため、その全体モデルをScalaとの状態同一性だとは主張しない。

**検証状態: 修正後の一意性・新旧pinの不一致は単体Lean検査成功。全体buildと最終公理監査を再実行中。無条件PALは未完、残り2公理。**

## n263 — boot 起点の canonical prefix は探索下限ゼロ、oracle の周期葉へ接続

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。ただし運ぶ述語の起点を boot 到達済み `InvLPS` に限定したため、義務は以前より弱い。公理を証明した／減らしたわけではない。周期葉へは `lower = reset` を構成して渡す。 |
| `obligation_localRealization` | 未解消、変更なし。 |

- `CanonicalPeriod.tick_lower_zero` は restart を除く各 tick で下限ゼロを保存する。search/phase は保存、init/replayStart は reset。`trace_lower_zero` と `packed_lower_zero` で任意長の有限 prefix に持ち上げた。`preTrace_lower_zero` はその系。
- `noBelow_first_canonical` は **有限の boot 起点 packed prefix** と既存の幾何学的 `Entry`・DP `Result` から最初のshiftに必要な最小周期性を示す。`hlow` は下限ゼロから消える。完成済み `PreTrace` を前提にすると oracle の構成へ循環するので、prefix だけで証明した。
- `CloseoutCheckW.PackedFromBoot` を追加し、`ScanOnPackedRunFromInvLPS` の origin にその証拠を保持。boot constructor は既存の1 tickを使い、oracle の各着地は同じ起点を引き継ぐ。最終消費者の結論は変わらない。
- `OracleRun.cycleOracleOn_of_leaves` は originまでのprefixと比較点までのprefixを連結し、`packed_lower_zero` を **実際に使用**。`OracleReady` の `hshiftPeriodMinimal` は `s.lower = reset` を受け取れるようになった。
- 未解決: 現在の watch の周期と DP Result・ReadOrigin を結ぶ構成、繰り返しshiftへの最小性の運搬。さらに readiness、ChainReady、fallback/replay、具体的局所機械。下限ゼロだけでこれらが閉じるとは主張しない。

**検証状態: n263 のmodule build成功（`/tmp/pal-boot-oracle.log`, `BUILD=0`）、全体build成功（`/tmp/pal-full-boot-20260919.log`, `BUILD=0`）。無条件PALは未完、残り2公理。**

## n262 — 受理結果と状態一致を区別し、最終消費者を短縮

先輩の「fable のアプローチがミスっている可能性、2前提を難しく考えすぎているふし」
との指摘を受け、前提の内容から再確認した。

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 宣言・型とも変更なし、未解消。 |
| `obligation_localRealization` | 宣言・型とも変更なし、未解消。ただし「非決定的な全 trace との一致は不可能」という n260 の根拠は誤りだった。型が要求しているのは受理結果の一致で、状態列の一致ではない。 |

- `GalilLookRefined.reported_throttledLG'` は従来の ledger 証明を1入力・1 trace に切り出したもの。既存 `ledger_throttledLG'` はその系に置換し、証明を重複させていない。
- `CloseoutFinalFour.latch_iff_pal_of_preTrace` は `PreTraceB` と消費者が既に持つ `hNeed` から、**canonical 性なしに** `LatchTrue … ↔ w ∈ PAL` を証明する。旧 `PreTraceB` だけの全称前提が真だと主張するものではない。
- `given_preTraceIMW_on` はこの iff を実際に使い、入力ごとに1本の trace を取り出して `pal_in_peg_of_structured` へ直接接続する。全入力にわたる trace の `choose` と、消費されない `_H_run` のための `AbstractRun'` 構成を除去。最終定理の型と witness は維持。
- canonical な exact tracking は局所実現を証明する **一つの十分な方法** であり、受理結果だけの義務から必要性は導けない。n261 で指摘した無限 trace / finite prefix の差も、その exact-tracking 経路の接続課題であり、目標定理そのものの必須前提ではない。
- `CloseoutFinalW` と `PalInPegUnconditional` の「producer は原理的に無い」という説明を訂正。引き継ぎ文にも訂正を明記。

- 周期葉の監査: `result_least` は `lower` より大きい候補の最小性しか返さない。既存 `GalilNoBelowFirst.noBelow_first_of_result` は別途 `hlow`（`0 < δ ≤ lower` の周期排除）を要求する。引き継ぎの「DP result を運ぶだけ」はこの条件を省略している。canonical policy では restart が無いので boot から `lower = reset` を運ぶ簡略化の余地があるが、現行 oracle の起点は任意 `InvLPS` であり、そのままゼロと仮定してはならない。未証明の残差として記録する。

**検証状態: n262 の全体 build 成功（`/tmp/pal-full-latch-20260919.log`, `BUILD=0`）。独立した公理監査も成功（`/tmp/pal-axioms-20260919.log`, `BUILD=0`）。新規補題は標準公理のみ、`unconditional` には従来の2独自公理が残る。無条件 PAL は未完。**

## n261 — canonical tick の一意性と、切り詰められた局所 trace への接続

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 未解消。既存の4葉は変更していない。 |
| `obligation_localRealization` | 未解消。`tick_canonical_unique`、`canonical_trunc`、`realizes_canonical` を構成し、canonical な局所 successor と trace の successor の一致を証明した。具体的な局所 step、その物理不変量、word-independent な有限テープ符号化はこの定理の結論には含まれない。 |

- `GalilTickFair.tick_scan_noRestart_unique` に既存 scan 証明を共通化。`tick_fair_scan_unique` と新しい `tick_canonical_unique` が同じ核を使う。
- `CanonicalLocalRealizes.canonical_trunc` は実際の tick について任意の `truncS d` で canonical 性を保存する。単に canonical 性があると仮定し直してはいない。背景・一致比較では broken chain の保存、shift では watch/broken の矛盾、fallback では search の idle/grow の矛盾で restart を除く。
- `LocalRealizesScan.realizes_of_refined_tick_det` に既存の successor 同定証明を共通化。旧 `realizes_of_tick_det` は `Refinement := True` の系。新しい `realizes_canonical` は canonical truncation と一意性を使う系であり、未証明の `H_scanDet` を要求しない。ただし canonical な局所 tick を実際に作る `hLocal` は依然として必要。
- `Axioms.lean` に上記3定理の標準公理のみの guard を追加。`unconditional` の残り2公理の guard は維持。
- 引き継ぎ §3 の「一意性で閉じる」は successor の同定についてのみ確認できた。`LocalLatchRealize.pal_in_peg_of_local_core` は `L0` / `enc_tick` / `enc_feed` 等を引数としており、今回の証明から具体的 `LocalStep` が得られたわけではない。
- 接続時の量化範囲にも注意: `realizes_canonical` は既存 `Realizes` と同じく全 `k` の trace tick を受け取る。一方 `CanonTrace` / `PreTraceIMW` は最終報告点までの有限 prefix である。この差を埋める bounded tracking または適切な延長も、最終公理から本定理を利用する際に必要。
- oracle の `hfresh` については、`ReadyPacedS` の量化対象が全 `PacedL` リストであり、実機の比較間隔より広いことに注意（`CloseoutReadyStage.ReadyIface` の説明と `StageRunPhase` / `StageEntryBudget`）。**現行の `hfresh` の反証はしていない。**

**検証状態: n261 の全体 build 成功（`/tmp/pal-full-20260919-fixed.log`, `BUILD=0`）。新規3定理の標準公理 guard 成功。無条件 PAL は未完（残り2公理）。**

## n259 — `hchain` を「packed run の scan 状態で `ChainReady`」（`StepsIMW` 形）に切り直し

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hchain` の切り直し。旧形は `InvLPS` 起点からの shaped run **全点**（copy／fallback 相の中も含む）で `ChainReady` を要求していた。新形は `InvLPS … c₀ r₀ → StepsIMW … k ⟨c₀,r₀⟩ y → y.ctl.mode = .scan → ChainReady y.vm.chain`——`BranchSupply.ChainVerifierSupplyAlongTrace`（trace の scan 点で `VerRep ∧ LagCan`、producer 済み）と同じ形。`scanBackground_run` は背景 tick の中間状態を `packRunR_MW_marksFree` で packed run に載せて葉に渡す（右ヘッド不動なので位置条件は自明）。葉は 4 のまま（`hfresh`／`hchain`／`hshiftPeriodMinimal`／`hfallback`） |
| `obligation_localRealization` | 変化なし（次: `∀ PreTraceB` を canonical trace に限定する切り直し） |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

## n258 — `hfallback` の量化子を直し（着地 `u` は葉が選ぶ `∃`）、最終 witness の `q` を 1 に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hfallback` の切り直し。旧形は `scanCompare_cases` が `beginFallback_exists`（**空の place** `⟨[], false⟩` を選ぶ）で作った任意の着地 `u` を葉に渡し「そこから完走せよ」と要求していた（量化子が逆、GPT-6 の指摘）。新形は不一致の源（`c s vq z`、guard 立たず）から `∃ u, beginFallback s1 u ∧ ∃ c' s' kk r fb replay, …` を葉が返し、tick は oracle 側が `Tick.scan_fallback` で作る（`scanCompare_cases` の fallback 枝は `∀ u, beginFallback s1 u → Tick …` を返す）。本物の構成（`scan_fallback_cycle_All`／`fallback_restarted_soundNR`）は右ヘッドから decode した非空 place を自分で選ぶので、この形なら繋がる。葉は 4 のまま（`hfresh`／`hchain`／`hshiftPeriodMinimal`／`hfallback`） |
| `obligation_localRealization` | 変化なし |

`PalInPegUnconditional.unconditional` の witness を `0 0 0` → `0 1 0`（`q = 1`）に変更: fallback 構成の定理群は `0 < q` を要求するので `q = 0` では葉が原理的に埋まらなかった。`first = 0` は変えず。

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

## n257 — `hminv`（run 全点の `MInv`）を運ぶ述語の場に移し、残差を shift 入口の周期最小性 1 点（`hshiftPeriodMinimal`）に局所化

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉は 4 のまま（`hfresh`／`hchain`／**`hshiftPeriodMinimal`**／`hfallback`）だが、`hminv`（`InvLPS` 起点からの shaped run **全点**で `MInv`）が消え、**この `hminv` は偽だった**（n253 でウチが書いた葉。run 全点には fallback 入口（copy 相）の着地も含まれ、そこでは中心が死んでいるので `MInv` は立たない。核は `CloseoutPackRun4.minv_false_at_mismatch`、しかも `CloseoutLPack5.MInvG` で一度直した穴の再発。葉自体を `False` に落とす定理は未構成なので「偽の疑いが濃い」と記録。GPT-6 の指摘（コウタ経由、2026-09-19）で確認した。同じ指摘の残り——`hfallback` の `u` が `∀`（`scanCompare_cases` が空 place を選ぶ）、最終 witness の `q = 0` vs fallback 構成の `0 < q`、`hchain` の run 全点量化——は n258 で直す）、代わりの葉は **状態局所**: shift 入口（guard 立ち・比較不一致の状態）で watch chain の周期 `periodLength wg` が span `Span w C (n − C)` の最小周期であること（`∀ p, 0 < p → p < 2·periodLength wg → ¬ HasPeriod … p`）。`MInv` 自体は `CloseoutCheckW.ScanOnPackedRunFromInvLPS` の場として運ぶ（boot は `InvLPS` の `Inv.minv`／`InvK.minv`、一致比較は `minv_match`＋`minv_afterBirth`（既存）、shift 出口は `leftmost_shift`（`GalilLiveCentreShift`）で `hdead`＝`not_live_of_mismatch`、`hlive`＝出口の `ScanInvariant`、`hmin`＝新しい葉、fallback は `hfallback` の結論に `MInv w c' s'` を足した） |
| `obligation_localRealization` | 変化なし（GPT-6 の指摘＝過剰量化の疑いを受けて、消費側からの逆算を並列で調査中。n174 の診断と同型） |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**何をしたか**

* `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に `MInv w c r` を追加（`Refreshed` の直後）。`scanOnPackedRunFromInvLPS_of_invLPS` は `hI.1.1.1.1.1`（`Inv ∨ ∃ k, InvK`）の両分岐の `.minv` で埋める。
* `OracleRun`: `scanCycle_of_leaves`／`cycleOracleOn_of_leaves`／`cycleOracleOn_of_fourLeaves` から `hminv` を削除。比較状態の `MInv` は `minv_same`（`scanCycle_of_leaves` の不一致分岐の結論に `t.replay = s.replay` を追加）で作り、`hshift`／`hfallback` の前提に `MInv w c s`、結論に `MInv w c' s'` を追加。`hland` は着地の `MInv` を受け取り運ぶ述語に詰める。`shiftLeaf` は `hminvS`（入口の `MInv`）と `hperiodMin` を取り、出口で `leftmost_shift` により `MInv` を返す。
* `OracleReady.cycleOracleOn_of_readyLeaves`: `hminv` → `hshiftPeriodMinimal`（統一した葉文）。
* 並列化を解禁（コウタ 2026-09-19「サブエージェント解禁していいけど、コミュニケーションコストがでかそうなのは任せない」）: 読み取り専用の地図作り 4 本（`hfresh`／`hchain`／`hfallback`／`localRealization`+`Fair`）を workflow で同時実行。lean プロセスは同時 2 本まで、`lake build` は 1 本。

**`hshiftPeriodMinimal` の帰着先**: 周期最小性は found 時の DP decode（`GalilMinimalPeriod.result_least`／`GalilSearchResult.search_result_at_tick`）が chain 誕生時に与える情報で、watch 相を通じて period テープに保存される。`hchain` の copy 相（誕生時の `∃ n, CopyInv`）と同じ起点データなので、両者は「誕生時の decode を chain の一生で運ぶ不変量」1 本にまとめるのが筋。

## n256 — 運ぶ述語に restart 無しの run（`ShapedRun.ShapedSteps`）を足し、`hrestart`／`hreplayStart` の 2 葉を消した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | producer `OracleReady.cycleOracleOn_of_readyLeaves` の葉が 6 → **4**（`hfresh`／`hchain`／`hminv`／`hfallback`）。`hrestart`（restart 着地の datum）と `hreplayStart`（replayStart 着地の datum）は**消えた**: oracle 自身の run は restart を出さず（broken chain は broken のまま tick する）、replayStart は fallback の着地 `Restarted raw t 0 reset` にしか無いので、運ぶ述語 `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に「`InvLPS` 起点からの shaped run」を足し、readiness datum を `ReadyTransport.readyField3_of_invLPS_shaped`（`hfresh` だけから）で運ぶ |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**何をしたか**

* `ShapedRun.lean`（新規 module、n255 の末尾で `OracleReady` から分離）: `ShapedSteps`（scan-mode tick は `restartVM` でない、`replayStart` tick は `Restarted w _ 0 reset ∧ scan ∧ clock = 2048` に着地する run）、`restartVM_shape`／`chainTick_broken`／`chainAt_broken`／`not_restartVM_background`／`not_restartVM_compare`／`watchSegE_shaped`、今回追加の `not_restartVM_of_chainAt`（chain tick が broken を残さないなら restart でない）／`not_restartVM_of_chainAt_target`（着地の chain が chain tick の結果なら restart でない）／`not_restartVM_of_radius`（radius が変われば restart でない）。
* `ReadyTransport.lean`（新規）: `readyField3_alongShaped`（shaped run に沿った `ReadyFieldP3` の transport、`hfresh` だけ）と `readyField3_of_invLPS_shaped`（`InvLPS` 起点の `ReplayStage` が記録する fresh restart の datum を `WatchSegE` 区間（shaped）で起点まで運び、そこから shaped run 全点へ）。
* `CloseoutCheckW.ScanOnPackedRunFromInvLPS` に `∃ j', ShapedSteps … j' ⟨c₀, r₀⟩ ⟨c, r⟩` を追加（boot の着地は長さ 0）。
* `OracleRun`: `scanBackground_run` が背景 tick の shaped run も返す（`not_restartVM_background`）；`scanCycle_of_leaves`／`cycleOracleOn_of_leaves` の `hready`／`hchain`／`hminv` は **shaped run 上**の量化に弱めた；一致比較の着地は `not_restartVM_of_chainAt_target`、shift 入口は guard の `.watch` から `not_restartVM_of_chainAt`、fallback 入口は radius の `inc` から `not_restartVM_of_radius`；`shiftUnits_S`／`shiftLeaf`／`hshift`／`hfallback` の結論に相の shaped run を追加（shift 相は mode が shift なので条件は空虚）。
* `OracleReady`: `searchReady_of_invLPS_shaped (hfresh) (hI₀) (hsh) (hm)` で `hready` を放電。`readyField3_alongRun`／`readyField3_of_invLPS_steps`／`searchReady_of_invLPS_steps` は参照ゼロになったので削除。

**残り 4 葉の帰着先**（n255 の表から `hrestart`／`hreplayStart` を除いたもの）: `hfresh` は DP の較正（`stageDebt`／`dpDemandS`、最初の stage は slack 0 で `dpDemand 0 8 = 1 ≤ 2`）；`hchain` copy 相と `hminv` shift 相は found 時の decode（`GalilSearchResult.search_result_at_tick`／`later_stage_found_result`）；`hfallback` は `fallback_restarted_soundNR` の側条件（`ShiftIdle`／`Canonical length`／`heven`／`0 < q`／`first ≠ 7, 8`）＋ replay 区間の構成（既存 `replay_segment_construct` は偽の `hpres`／`hquiet` を取るので、`ReadyFieldP3` 版に切り直す）。着地に shaped run が要るのは replayStart tick 1 本だけで、その着地は `fallback_restarted_All` の `Restarted raw t 0 reset`。

## n255 — `hready` を原子の葉 3 本に分解（`OracleReady.searchReady_of_invLPS_steps`）、PR #72 を main に merge

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 葉 `hready`（`InvLPS` 起点からの run の chain idle な scan 状態で `SearchReady`）を定理化: `OracleReady.searchReady_of_invLPS_steps (hfresh) (hrestart) (hreplayStart)`。乗り物は `CloseoutPreload39.ReadyFieldP3 n`（今の readiness ＋ paced な未来全部の readiness）で、`readyField3_tick` が restart／replayStart の着地以外の全 tick で運ぶ（`BigPack2M''` 仮説は証明が `aux.front.notInit` しか使っていなかったので `mode ≠ init` に一般化）。起点の datum は `InvLPS.2 : ReplayStage`（fresh restart からの `WatchSegE` 履歴）で `hfresh` を transport。残る原子: `hfresh`（`Restarted w r Rad last ∧ StageEntry Rad last ∧ mode scan ∧ clock 2048 → ∃ n, ReadyFieldP3 n ⟨c, r⟩`＝具体 DP の stage 予算に対する較正）、`hrestart`／`hreplayStart`（fresh 起点から到達する restart／replayStart tick の着地の datum ＝ 着地が `Restarted ∧ StageEntry` であること ＋ `hfresh`）。`OracleReady.cycleOracleOn_of_readyLeaves (hP) (h4) (hfresh) (hrestart) (hreplayStart) (hchain) (hminv) (hfallback)` が oracle の producer（標準公理のみ）。`OracleRun` の `hready` は `y.ctl.mode = scan` に限定（使う場所は全部 scan 状態）。既存塔の判定: `readyField3_entry_of_datum` は `NoReturn`（一般には偽）を取るので使えず、`postRunC_galil_of_boot`（Preload36）の `StageChain` 経路は boot datum と `16 ≤ mw` が残差。PR #72（n245〜n254）を main に merge（`433ec7e`） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**残り 6 葉の帰着先（n255 追記）**: `hchain` の copy 相は誕生時の `∃ n, CopyInv answer reset walker (start cc) h`（`AnswerAheadDecode.copyInv_of_found`: `denote answer = output h`／`head answer = h`／`focus = 8`／`Candidate (stream p take (span+1)) lower h`）を要り、`hminv` の shift 相は `leftmost_shift` の周期最小性（`∀ g < h, ¬Candidate`）を要る。どちらも **found 時の DP 出力の decode**で、既存: `GalilSearchResult.search_result_at_tick (hP : Decodes P) … (hR : Restarted raw r Rad last) (hstage : 3·Rad ≤ 5·k) (hseg : WatchSegE … c0 r cF sF) (hsF : chain idle) (hcF : clock 1) (hq : searchEffect P true sF vq) (hfound) : (∃ k h, Result (stream take (8·max k 1+1)) k 0 (denote vq.dp.config) ∧ pc = 346 ∧ pos 11 = h ∧ Candidate … h ∧ (∀ g < h, ¬Candidate …) ∧ sF.search.mode = run) ∨ (第 1 段で run を抜けた)`（第 1 段）、後段は `search_later_stage'`／`later_stage_found_result`／`laterStage_dpEntry`。つまり `hchain`／`hminv` は「fresh restart からの chain idle 区間の found」＝`hfresh` と同じ起点データ（`Restarted ∧ StageEntry`＋`ReplayStage` の履歴）で決まる。運び方: `WindowInv.copy` に `∃ n, CopyInv` を足し、`windowInv_start`（誕生）で `copyInv_of_found` を使う——その入力（`Result`）を `windowRunPack_tick` 経由で `packRunR_MW_marksFree` に thread する（found 比較の decode は run 形で供給）。`hfallback` の replay 区間は `hready` と同じ datum で背景 tick が出る。

## n254 — shift 相の葉を放電（`OracleRun.shiftLeaf`）、新 oracle は run 形の葉 4 本に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | `OracleRun.cycleOracleOn_of_fourLeaves (hP) (h4) (hready) (hchain) (hminv) (hfallback)`（標準公理のみ）。shift 相の葉は `shiftLeaf` で定理化: 比較状態の pack から `four_of_guard`（4h ≤ 半径）、入口状態の pack の窓（`periodLength_of_coreP`＋`periodLength_consume`、`Coupled'.block`）から `0 < h`、`GalilShiftPack.shiftHeads_of_scan`＋`shift_heads_counters`＋`shift_run_chain` で chain shift run、`shiftUnits_S`（`shift_run_lift` を 1 単位ずつ `tick_pull`／`shift_transfer`／`tick_S_of_tick` で `galilFrameS` へ、`StepsAll (SoundScanNR)`）、出口は `shiftExit_S`（`shift_done` を直接構成、`refresh` を露出）、着地の `SoundScanNR` は remaining 尽きた shift 状態の pack の `LPackM2.shiftGeom` → `shiftGeom_exit` → `outputRel_of_refresh`。葉 `hshift`／`hfallback` は「比較データ形」（`searchEffect`／`chainAt`／guard／entry／tick を明示、prefix は `StepsIMW`）に切り直し（tick の `cases` を避ける）。残る葉: `hready`（chain idle での `SearchReady`）／`hchain`（`ChainReady`）／`hminv`（`MInv`）／`hfallback`（fallback＋replay） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

**次（n254 の見立て）**: 残り 4 葉のうち `hready`（chain idle での `SearchReady`）と `hchain` の copy 相（`∃ n, CopyInv`、誕生時の `copyInv_of_found` は found 時の DP 出力の decode 事実 `hDenote`／`hHead`／`hFocus`／`Candidate` を要る）は**同じ探索側の run 不変量**に帰着する: `InvLPS` 起点（`search = begin last radius`、`searchReady_of_begin`）から compare 1 回ごとに debt が 1 減り（`searchReady_run_true_iff`）、DP は予算内に終わる（`dp_quanta_safe`／`calibrated_quanta_safe`、`StageEntry : 3·Rad ≤ 5·last`）——これを run に沿って持ち回る `RdPaced` の producer `PostRun`／`RestartS2` を書くのが本丸。`hminv` の shift 相は `leftmost_shift`（`¬Live`／`Live (C+h)`／周期の最小性 `GalilMinimalPeriod.result_least`）、`hfallback` は `fallback_restarted_soundNR`（側条件 `ShiftIdle`／`Canonical length`／`heven`／`first ≠ 7,8`／`0 < q`）＋ replay 区間の新構成（既存の replay 構成子は偽の `hpres`／`hquiet` を取る）。

**`hready` の既存塔（n254 追記）**: `CloseoutPreload40.HpresAt P c s := ∀ a v, chain idle → (a → clock ≤ 1) → searchEffect P a s v → SearchReady v`（pointwise の保存則）。`CloseoutPreload41.hpresAt_along_soundScanNR (hr : BigResid6) (het : H_extraTick3) (hme : H_marksEntry') (hIC : InvLPC) (hjx) (hbx : BigPack2M'') (hf : ReadyFieldP4 (n+1) x) (hentry) (hentry') : HpresRepAt x`（`SoundScanNR` run の各 scan 点で `HpresAt`）。起点の `SearchReady`（`Inv.search`／`searchReady_restarted`）と `HpresAt` の各点保存で `hready` が出る。塔の入力: `ReadyFieldP4`（fuel 付き readiness datum、boot は Preload39）、`hentry`／`hentry'`（restart／replayStart 直後の `ReadyFieldP3`）、`BigResid6`（`bigResid6_of_lpackM2`）、`H_extraTick3`（`h_extraTick3_of_h_extraTick4`）、`H_marksEntry'`（`h_marksEntry'_of_layout`）。`.run` 入口の帰納は `CloseoutPreload36.postRunC_galil_of_boot (hres : RestartOnBroken P) (hsup : ScanSupplyInv) (hboot : EntryDatum) (hch : StageChain)`（`StageChain` に沿った `DpSafeStage`）。**次はこの塔を新 oracle の `hready`（`InvLPS` 起点・`Steps` 各点・chain idle）に合わせて 1 本の定理に束ねる。**

**`hready` の塔の入口条件（n254 追記 2）**: `CloseoutPreload39.readyField3_entry_of_datum (hclk) (hR : Restarted) (hSE : StageEntry) (hcl : CentreLongRun) (hnr : NoReturn) (hdep : EntryDepthG) (hD) : ReadyFieldP3 (dpEntryG …) ⟨c, r⟩` と `readyField3_along_run (hr : StepsAll (BigPack2M'') m x y) (hf : ReadyFieldP3 n x) (hentry) (hentry') : ReadyFieldP3 n y`、`readyField3_to_ready`。ただし `NoReturn u`（`ReachL` の非 run 状態は全部 `ReachP`）は Preload8 の記述どおり一般には偽で、producer `noReturn_of_avoidRun` は「`.run` に一度も入らない」退化ケースのみ。**使う経路は Preload36 `postRunC_galil_of_boot (hres : RestartOnBroken P) (hsup : ScanSupplyInv F 2048 I) (hp : I p) (hclk) (hboot : EntryDatum k mw pre p p0) (hmw : 16 ≤ mw) (hch : StageChain k mw mw' evs tail p0 pn) (hpaced) : EntryDatum … ∧ 16 ≤ mw' ∧ (… ∨ DpSafeStage (search pn) tail)`**（`RestartOnBroken` は `CloseoutPreload33.restartOnBroken_sharedC` で証明済み）と Preload40／41（`ReadyFieldP4`、`hpresAt_along_soundScanNR`）。束ね方: `InvLPS` 起点を `EntryDatum` に読み替え（`Restarted` の `begin last radius`）、oracle が構成する run を `StageChain` に分解して各 `.run` 入口の `DpSafeStage` を得、`ReadyFieldP3/4` の各点保存で chain idle の `SearchReady` を出す。`16 ≤ mw`（窓が小さい restart）と `ScanSupplyInv`／`I` が新しい側条件の候補。

## n253 — 新 oracle の一致分岐を証明（`OracleRun.scanCycle_of_leaves`、run 形の葉 3 本のみ）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun` | 一致分岐が閉じた: `scanCycle_of_leaves (hP : Decodes) (h4 : first ≠ 4) (hm1) (hmle) (hI : ScanOnPackedRunFromInvLPS w c s) (hp : right ≤ 2m−1) (hready) (hchain) (hminv) : CycleOutOn … w m c s ∨ (right < 2m−1 ∧ ∃ t, StepsAll (SoundScanNR) (clock−1) ⟨c,s⟩ ⟨{c with clock := 1}, t⟩ ∧ heads 不変 ∧ 不一致)`。報告点にいる状態はそれ自身が報告（`Refreshed` は運ぶ述語が持つ）、下にいれば `scanBackground_run`（背景 tick）→ `scanCompare_cases`（比較）で、一致なら右 +1 の同形状態（`packRunR_MW_marksFree` で pack、`minv_match`／`minv_afterBirth` で `MInv`、1 `Piece` の `CostedRun`、`mu` 減少）か報告。残る入力は run 形の葉 3 本: `hready`（chain idle での `SearchReady`）、`hchain`（`ChainReady`）、`hminv`（`MInv`）——いずれも「`InvLPS` 起点からの `Steps` の各点」で量化（状態全体への過剰量化はしていない）。不一致分岐（shift 相／fallback＋replay）は次 |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### n253 addendum — oracle 全体が run 形の葉 5 本に還元された（`OracleRun.cycleOracleOn_of_leaves`）

`cycleOracleOn_of_leaves (hP : Decodes) (h4 : first ≠ 4) (hready) (hchain) (hminv) (hshift) (hfallback) : CycleOracleOn … (ScanOnPackedRunFromInvLPS …) w`（標準公理のみ）。葉はすべて「`InvLPS` 起点 `⟨c₀,r₀⟩` から `Steps k` で到達する状態」で量化:
1. `hready`: chain idle な状態で `SearchReady (searchLens.get vm)`（chain 生存中は不要）。
2. `hchain`: `ChainReady chain`（idle／broken 自明、copy は `CopyInv`、back は `canRight ver`＋`OnBlock`、watch は `chainReady_watch_of_watchWindow`）。
3. `hminv`: `MInv w ctl vm`（背景 `minv_same`、一致 `minv_match`＋`minv_afterBirth`、shift は `leftmost_shift`、fallback は `minv_after_fallback`）。
4. `hshift`: clock 1 の ScanNR 状態からの shift 入口 tick の先から、`StepsAll (SoundScanNR) n` で refresh 済み ScanNR 着地へ。右ヘッドは比較後の位置（＝元 +1）、中心は真に右、`n ≤ adv + 1`（`ShiftEv.ticks_le`）。部品: `GalilScaffoldTopShiftCycle.scan_shift_cycle`（`ChainShiftRun` から shift 相全体を構成、`galilFrame` の Steps → `tick_S_of_tick` で `galilFrameS`）、`shift_run_chain`、着地の `SoundScanNR` は shift_done 直前の pack（`packRunR_MW_marksFree` を非 scan 終端に適用）の `LPackM2.shiftGeom` → `shiftGeom_exit` → `outputRel_of_refresh`。
5. `hfallback`: copy 入口 tick の先から `fb + replay` tick で refresh 済み ScanNR 着地へ。右ヘッドは元 +1、中心は `+ (kk + 1 − r)`（`r ≤ kk`）、`fb ≤ 12704(kk+1−r)+4012`、`replay ≤ 8·2048·(kk+1−r)`（`FallbackEv`）。部品: `fallback_restarted_soundNR`（`Restarted 0 reset` まで `StepsAll (SoundScanNR)`）＋ replay 区間の新構成（既存 `replay_segment_construct`／`match_round` は偽の `hpres`／`hquiet` を取るので使えない。run 形の `hready` から書き直す）。

背景 tick・比較・pack・`CostedRun`・`mu`・報告点は全部 `scanCycle_of_leaves`／`cycleOracleOn_of_leaves` の中で済んでいる。公理 `obligation_cycleOracleOnPackedRun` は 5 葉が定理になった時点で消える（葉を公理に割らない: 本数を増やさない）。

## n252 — `obligation_cycleOracle`（`CycleOracleMC3`）を run 形 `obligation_cycleOracleOnPackedRun` に切り直し（旧形は着地に chain idle を要求しており偽の疑いが濃い）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracleOnPackedRun`（新） | 旧 `obligation_cycleOracle`（`CycleOracleMC3`）と差し替え。`CycleOutMC3` の報告分岐は `m < |w| → 次の報告点 `2(m+1)−1` までに `InvLPS` に着地` を要求し、`InvLPS` は `Restarted`／`InvScan.chainIdle` により **chain が idle**。Scala 正本では chain は fallback（`ScaffoldGalil.scala:320`）か broken からの restart（`:233`）でしか idle に戻らず、`matched()` は Watch のまま `consume()` を続ける（`ScaffoldChain.scala:161`）。よって `aaaa…` のように chain が生き続ける入力では旧形は満たせない。**機械検査済みの反証は無い**（`REFUTED` とは書かない）。新形は `CloseoutCheckW.CycleOracleOn (ScanOnPackedRunFromInvLPS)`: 「`InvLPS` 起点からの packed run 上の非 replay な scan 状態（`ScanNR ∧ ∃ 起点 j, InvLPS 起点 ∧ StepsIMW j 起点 x`）から、報告点 `2m−1` に達するか、`mu` を減らして同じ形の状態に着地する」。消費側の checkpoint 再帰 `checkpoints_costIMW_upto1` は運ぶ述語を `hor` に渡して受け取るだけだったので、`CloseoutCheckW` を述語 `I` で一般化（`ReachAtOn`／`CycleOutOn`／`CycleOracleOn`／`reachOn_fuel`／`reachOn_from`／`checkpoints_costOn_upto1`／`H_bootOn`／`preTraceOn_exists`）し、旧名（`ReachAtIMW`…`preTraceIMW_exists`）は `InvLPS` instance として残した（下流の旧系統は無変更）。新 trace 生成は `preTraceOnPackedRun_exists (hboot : H_bootIMW) (hor)`（boot 側の義務は増えない: `scanOnPackedRunFromInvLPS_of_invLPS` が `j = 0` で出す）。`CloseoutFinalFour.given_preTraceIMW`（trace 生成を抽象化した最上位）を切り出し、`given_needBound` はその系。`given_scanLandingObligations` は `hor` を新形で取り `h4` を落とした（`packRunR_MW_marksFree` は oracle の証明側へ移る） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 新 oracle の証明計画（必要な部品だけ）

1 回の oracle 呼び出しは「clock 分の背景 tick ＋ 比較 1 回（＋ shift 相／fallback＋replay）」で `mu` を 1 以上減らす（比較で右ヘッド +1、shift／fallback で中心が右へ）。chain の死は不要。
- run の存在: `OracleRun.scan_tick_exists_PofC`（`SearchReady` ＋ `ChainReady`）／`phase_tick_exists_PofC`（`PhaseEnabled`）。`ChainReady` は `IPackMW.win`（`WindowRunPack`）から（watch は `chainReady_watch_of_watchWindow`）。
- pack: run が出来たら `packRunR_MW_marksFree` で `StepsIMW`（着地は非 replay かつ右ヘッド ≤ 2M−1 が条件）。
- `SoundScanNR`: 背景は `outputRel_background`、比較は `outputRel_of_refresh`＋`scanInvariant_matched`、fallback は `fallback_restarted_soundNR`。
- 報告点: `ReportPointAt` の `scanInv` は `LPackM.scanGeom`、`centre : MInv` は別途運ぶ（`minv_same`／`minv_match`／`minv_afterBirth`／`leftmost_shift`／`minv_after_fallback`）。`Refreshed` は比較 tick の `ho`。
- `CostedRun`: 1 比較 = 1 `Piece`（`wait := clock−1`, `cmp := true`, `place := 着地の右ヘッド`）。
- 未解決の入力: chain idle 区間での `SearchReady`（`RdPaced` の producer `PostRun`／`RestartS2` は未証明）。

### 新 oracle の証明の分解（n252 addendum、必要な部品の所在）

1 呼び出し = 「背景 tick × (clock−1) → 比較 1 回 → (shift 相 ｜ fallback＋replay)」。各部品:
1. **chain 側の tick 存在** `ChainReady`: idle／broken は自明、copy は `∃ n, CopyInv`（誕生 `AnswerAheadDecode.copyInv_of_found`、1 歩 `GalilBranchInvariants.copyInv_step`）、back は `WindowInv.back`（`VerAt`／`LagAt` → `canRight ver`）＋ `OnBlock`（`BlockInv`、`blockInv_steps` で run 全点）、watch は `OracleRun.chainReady_watch_of_watchWindow`。
2. **search 側の tick 存在** `SearchReady`（chain idle のときだけ必要、chain 生存中は `searchEffect` が恒等）: `RdPaced` の閉包 `readyClosure_S2 (hpost : PostRun) (hS : RestartS2)` の **producer が無い**（`hpres` の沼、DP のタイミング層の配線）。**これが oracle 証明の唯一の未証明入力**。構成子には run 形 `hready : ∀ k y, StepsAll … k x y → y.vm.chain = idle → SearchReady (searchLens.get y.vm)` として渡す。
3. **run の組み立て**: 背景は `GalilScaffoldTopProgressS.backgroundS_exists` ＋ `Tick.scan_count`（`backgroundS_fields` で heads／center／replay 不変、`outputRel_background` で `SoundScanNR`）、比較は `compare_progress_gen` 相当を 3 択（match／`scan_shift`／`scan_fallback`）に開いて構成、phase は `OracleRun.phase_tick_exists_PofC`（`ShiftEnabled` は `LPackM2.shiftGeom`）。
4. **pack**: 出来た `StepsAll (SoundScanNR)` に `packRunR_MW_marksFree`（終端は ScanNR かつ右 ≤ 2m−1）。
5. **`MInv`**（`ReportPointAt.centre`）: 背景 `minv_same`、一致 `minv_match`、誕生 `minv_afterBirth`、shift `leftmost_shift`、fallback `minv_after_fallback`。
6. **`CostedRun`**: 比較 1 回 = `Piece`（`wait := clock−1`, `cmp := true`, `place := 着地の右ヘッド`）; shift は `ShiftEv`、fallback は `FallbackEv`。
7. **`mu` 減少**: 一致で右 +1、shift で中心 +h、fallback で中心が右へ（`leftmost_after_fallback`）。

次に書く定理（`OracleRun`）: `scanBackground_run` — ScanNR 状態から `clock−1` 個の背景 tick の `StepsAll (SoundScanNR)` を構成し、heads／center／replay／remaining が不変で clock が 1 になることを返す（`hready`／`hchain` は run 形の仮説）。

## n251 — `ChainReady` から `Good` を外した（正 lag の watch は必ず tick できる）／run 構成の API 確定

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | run の存在が chain 側で無条件になった: `GalilTickFun.ChainReady (.watch w)` の場を `positive lag → canRight verifier ∧ ∃ a, symbol focus = some a`（読みが当たれば `Internal.take`、外れれば `watchBreak`）に緩め、`.broken` は `True`（`brokenIdle`／`brokenMatched` で常に進む）。`GalilBranchInvariants.chainStep_watch_total`／`chainTick_watch_total` も同じ仮説に。`Good` を持つ producer は `readyWatch_of_good` で変換（`chainReady_of_blockInv`／`chainReady_of_chainOk`）。**run 構成の API**: scan は `GalilTickFun.scan_tick_gen (P) … hshift hfall hsearch hchain`（frame 汎用）、init／restart／replayStart は `*_tick_gen`、phase モード（shift／copy／fpp／home／markEnd／choose／rewind）は `GalilTickFun3.phase_tick_gen (P) (hx : PhaseEnabled q first x)`——全部 `P := PofC …` で使える。`tick_exists`／`tick_exists_R`／`tick_exists_P`／`runFun_steps` は `sharedFun`（fallback 先を `place s` に固定した frame）用なので `CycleOracleMC3`（frame `PofC`＝`sharedC`、fallback は `beginFallbackVM'`）には直接使えない。`PofC` 側の `hfall` は証人 `place s` と `(stream (place s)).length ≤ position right`（`Decodes`＋`CentreRep` から）で出す |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### `Enabled`（scan）の各場の供給元

| 場 | 供給元 |
|---|---|
| `1 ≤ clock` | `Bounded`／tick の構成子（clock は `delay` から減る） |
| `replaying = false` | `ScanNR`（replay 中は `tick_exists_R` の `ReplayEnabled`: 左右の読みが一致） |
| `∀ a, ∃ v, searchEffect P a s v` | `GalilBranchInvariants2.searchEffect_exists`（`SearchReady`）／`GalilOracleLeaves2.hsearch_C` |
| `ChainReady s.chain` | `WindowRunPack.window`（`WindowInv`）: copy は `CopyInv`、back は `OnBlock`＋`canRight ver`、watch は `LagAt`（正 lag ⇒ `position ver < position right` ⇒ `canRight ver`、`canRight_of_bound`）＋`symbol_of_coreP`（bounce の添字は常に `some`）＋`WatchBlock`＝`OnBlock` |

### 次

`FoundExitLPS`（`CloseoutWatchRound31.cycleOutMC3_of_foundExitLPS` の入力）を `WindowRunPack` の上で構成する:
found tick（`CloseoutFoundRoute1.found_first_tick` の形）→ 決定的 run（上の API）→ 着地の分類（`scan_shift`：`shiftPal_of_windowRunPack`／`scan_fallback`／`restart`）→ `Inv`（`restarted`／`fallback_restarted_All`）。停止性は右ヘッド位置（各比較で +1、上限 `2m−1`）と clock。

### 実装（n251 の続き）

`PalPeg/OracleRun.lean`（登録済み・標準公理のみ）: `scan_tick_exists_PofC (c s) (hm : scan) (hclk : 1 ≤ clock) (hr : replaying = false) (hsearch : SearchReady (searchLens.get s)) (hready : ChainReady s.chain) : ∃ st', Tick (galilFrameS (PofC …) q first) 2048 ⟨c, s⟩ st'`（`scan_tick_gen` ＋ `beginShift_exists`／`beginFallback_exists`／`searchEffect_exists`／`chainAt_exists`）と `phase_tick_exists_PofC (hx : PhaseEnabled q first x)`。copy 相の `ChainReady.copy`（`∃ n, CopyInv t h p v n`＝DP 答えテープの残り `n` と place の残り `n`）は誕生時に `startShape'_of_decodes`（`AnswerAhead`／`PlaceAhead`）から。
`OracleRun.chainReady_watch_of_watchWindow (hW : WatchWindow raw cen₀ (position r) cc b xs (.watch w)) (hrep) (hpres) (hcan : canRight r) : ChainReady (.watch w)`: `LagAt` で verifier は右ヘッドの手前、`CoreP` で表現＋`OnBlock`、`symbol_of_coreP`＋`bounce_length` で焦点記号は常に `some`。これで `WindowRunPack` の watch 状態は右ヘッドが動ける限り `scan_tick_exists_PofC` の `hready` を満たす。

### found 経路の run 構成（設計、n251 確定版）

found tick 後の chain の一生を `PofC` frame で構成する。各 tick の存在は `scan_tick_exists_PofC`（scan）／`phase_tick_exists_PofC`（phase）。
1. **watch 相**（copy／back は `GalilPrepConstruct.prep_segment_construct` が明示的に構成する）: 不変量は `WindowRunPack`（`windowRunPack_tick`、源に `LPackM`／`LPackM2`／`AuxPack`）＋ `SearchReady`（chain 生存中は `searchEffect` が探索を進めないので不変、`readyPacedS_effect_*` の `hidle` 参照）。`ChainReady` は `chainReady_watch_of_watchWindow`（右ヘッドの `canRight` が要る＝報告点 `2m−1` の手前）。
2. **終端の分類**（比較 tick、clock 1）: 一致 → 続行（右ヘッド +1、`position right ≤ 2m−1` で停止性）；不一致＋guard → `scan_shift`（`ShiftEnabled` は `LPackM2.shiftGeom` から、shift 後は scan に戻り `WindowRunPack` 継続）；不一致＋¬guard → `fallback_restarted_All`（`hg : ¬ shiftGuardVM (afterMismatch …)`、`heven`＝DP 窓長の偶数性、`hi : ShiftIdle`）が restart 直後の `Restarted raw t 0 reset` まで run を作る；break（`brokenMatched`／`breaks`）→ lag ゼロなら `restart` tick で `Restarted`、正 lag なら chain は死んだまま次の不一致で fallback。
3. **着地**: `Restarted` ＋ `SpanRep` ＋ `CopyPack` → `invLPC_of_landed` → `InvLPS`（`replayStage_of_inv`）→ `cycleOutMC3_of_centre`（`mu` は辞書式: 中心前進 or 同中心で右ヘッド前進）。報告点 `2m−1` に達したら `ReachAtC3`。

### 次に書く定理（正確な文、n251）

`GalilRoundConstruct.scan_half` は継続 round 用（`SInv`: lag ゼロ、`hmid` で round 内の一致が予測される）。
found 直後の**新鮮 watch**（`prep_segment_construct` の出口: lag = `inc radius`、追いつき中）には使えないので、
`OracleRun` に新鮮 watch の segment 構成子を書く:
```
theorem freshWatch_segment (centre place entry q first) (raw) :
  ∀ (fuel : ℕ) (c : Control) (s : GalilVM),
    FreshInv raw c s →                       -- scan ∧ ¬replaying ∧ 1 ≤ clock ≤ 2048 ∧ BigPack2MG7W'' ⟨c,s⟩
                                             --   （IPackMW.win で WindowRunPack、chain は watch か broken）∧ SearchReady (searchLens.get s)
    (2 * raw.length - position s.right) * 2049 + c.clock ≤ fuel →
    ∃ (n : ℕ) (c1 : Control) (s1 : GalilVM),
      ScanSeg (PofC centre place entry raw) q first 2048 n c s c1 s1 ∧ FreshInv raw c1 s1 ∧
      s1.center = s.center ∧
      (¬ canRight s1.right ∨ LastLetterEnd c1 s1 ∨
        (c1.clock = 1 ∧ canRight s1.right ∧ read (left s1.left) ≠ read (right s1.right)))
```
中身: 背景 tick は `scan_tick_exists_PofC`（`hready` は `chainReady_watch_of_watchWindow`、broken は `True`）で存在し
`FreshInv` は `bigPack2MG7W''_tick_M`＋`windowRunPack_tick`（`hSP` は `shiftPal_of_windowRunPack`）で保存、
`SearchReady` は chain 生存中は不変。一致比較は segment に含めて続行（右ヘッド +1 で fuel 減少）。
終端 3 択のあと: 不一致∧`shiftGuardVM (afterMismatch …)` → `scan_shift`（`ShiftEnabled` は `LPackM2.shiftGeom`）、
不一致∧¬guard → `fallback_restarted_All`、`¬canRight` → 報告点。

## n250 — モデル欠陥 `M-watchBreak` を修正（`ChainStep.watchBreak`／`ChainMatched.brokenMatched`）、全体 build 緑

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | **証明可能になった**（証明はこれから）。n249 のとおり `CycleOutMC3` は run の存在を主張し、正 lag の watch が予測を外す状態に Lean の `ChainStep` は後続を持たなかった（`ChainStepGap`、機械検査済み）。`GalilScaffoldTopChainVM` に `WatchBreak w := positive lag ∧ canRight ver ∧ ∃ a, symbol focus = some a ∧ read (right ver) ≠ some a` と `ChainStep.watchBreak (w) (hb : WatchBreak w) : ChainStep (.watch w) (.broken ⟨⟨right ver, control⟩, lag, margin⟩)`、`ChainMatched.brokenMatched (w) : ChainMatched (.broken w) (.broken ⟨machine, inc lag, inc margin⟩)` を足した（Scala `consume()`／`matched()` 通り）。`ChainStepGap.chainStep_exists_at_positive_lag_mismatch` が gap の閉鎖を記録（`Canonical.model_gap_watchBreak_closed`）。`#print axioms unconditional` は変わらず標準 3 ＋ `obligation_cycleOracle`／`obligation_localRealization` |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 何を変えたか（71 ファイル、定理は 5 本だけ新規: `not_good_of_watchBreak`／`watchBreak_arrive`／`watchBreak_trunc`／`lagLe_break`／`lagLe_breaks`——全部既存の `cases` を通すための対）

- `ChainStep`／`ChainMatched` の `cases` に alternative を追加（`.broken` 行きは不変量が `True`／空虚）。`chainStep_unique`／`chainMatched_unique`（2 ファイル）は `Internal.idle`（`positive lag = false`）／`take`（`Good`）と `WatchBreak` の排他。
- 終端比較を扱う定理群（`foundRouteMC_noshift'(_Inv)`／`life_restarted`／`found_life`／`found_to_found`／`chain_life` …、`FoundCycle`／`BreakEnd`／`ShiftTailC`／`NoShiftTailC(0/L)`／`hcont` 型）は、正 lag の break だと結論（restart）が偽になるので、終端 watch に `zero w3.lag = true` を仮説／成分として一括追加（regex、`hz3`）。producer 側（`GalilRoundConstruct`／`GalilMidRoundFallback`）は `RoundInv.wit` の `hzw` を渡すだけ。`rounds_break` は `scanSeg_only` で自前に導くので不要。
- `GalilTrailAssembly.LagLe`: broken chain の lag を `reset` と読む（`lagOf`）。break 前 `ver + lag ≤ r`・`lag ≥ 1` ⇒ break 後 `right ver ≤ r`（`lagLe_break`）。`ChainBudget.pos`（先読み予算）が broken の verifier にも要るため空虚化はしない。
- `GalilArriveChain`／`GalilTruncTick`: 到着・切り詰めとの可換（`watchBreak_arrive`／`watchBreak_trunc`、`breakStep_*` の対）。verifier を動かす Scala 通りの break 先だと切り詰め補題が自然に通る（`usedChain` が読んだ cell を数える）。
- dead 塔の切り離し: `unconditional` の閉包外で、構成子追加により**偽になった**補題（`CloseoutWatchRound2.watchClosed : WatchClosedC`「背景 tick は watch を watch に保つ」／`distance_mono_false`／`CloseoutTickFalse.step_ne_broken`）を含む round 塔（`CloseoutWatchRound*`／`WatchPhase*`／`TerminalN`／`MismatchCompare`／`TickFalse`／`LagAll`）を build から外した: Workbench 登録 9 本を削除、`Canonical.lean` の alias 11 本（`mismatchCompare_*`／`shiftEntry_exists`／`copyIdle_congr`／`shiftRun_exists_from_round`／`shiftAtMismatch_from_round`／`backgroundTick_keeps_watch`／`backgroundTick_is_identity_at_lagZero`／`step_never_breaks`／`landingReady_from_parts`／`chainReady_from_round`／`distance_eq_radius`／`radius_nonneg`）と import 4 本を削除。ファイルは未削除（build 対象外、後で削除）。
- `ChainReady`（`GalilTickFun`）の `positive lag → Good` 場はまだ残っている（run の存在に不要になったので次に緩める）。

### 次

`obligation_cycleOracle`: n248 の計画どおり `WindowRunPack` の上で found 経路（`FoundExitLPS`）を構成する。
run の存在は `GalilTickFun.tick_exists`（`Enabled`）で、`ChainReady.watch` の `positive lag → Good` を `watchBreak` で外す。

## n249 — `obligation_cycleOracle` の前に `M-watchBreak` を直す（run の存在が欠陥に当たる）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし。ただし**順序が確定**: `CycleOutMC3` は「`InvLPS` から次の着地までの run が存在する」主張で、found 後の chain の一生（copy → back → watch、正 lag で追いつき）を通る。正 lag の watch で予測が外れると Lean の `ChainStep` には後続が無い（`PalPeg.ChainStepGap.no_chainStep_at_positive_lag_mismatch`、機械検査済み）。Scala `ScaffoldChain.step()` はそこで `consume()` → `Mode.Broken`（`ScaffoldChain.scala:136,178`）。DP が周期を決める窓は `stream.take (8·max k 1 + 1)` で、右腕がそれより長ければ外れうる（Scala に分岐がある理由）。**よって `M-watchBreak` を直すまで `CycleOutMC3` は証明不能**（run が止まる状態が到達可能） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 の木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 直し方（一次情報: `GalilScaffoldTopChainVM.lean:26-75`）

`ChainMatched.breaks (w w') (hb : BreakStep w w')` は lag ゼロ経路の break。`ChainStep` に
正 lag 版を足す:
```
| watchBreak (w) (hp : positive w.lag = true) (hng : ¬ Good w) :
    ChainStep (.watch w) (.broken ⟨consume w.machine, w.lag, w.margin⟩)   -- 目標状態は Scala に合わせて確認
```
影響: `ChainStep` に触れるファイル 80、`watchStep` の出現 109。ほとんどは `cases` に
`.broken` 行きの alternative が 1 つ増えるだけ（`WindowInv .broken = True`、`SumRel .broken = True`、
`WatchOK` は broken で空虚、`Coupled.idleOut` は mode guard、`chainStep_unique` は `Good`／`¬Good` で排他）。
`ChainReady`（`GalilTickFun`）の `positive lag → Good` 場は消せる（run の存在に不要になる）。
手順: 構成子を足して `lake build --quiet PalPeg` の error 一覧を作業リストにする。

### 実装（n249 の続き、作業中・未コミット）

`GalilScaffoldTopChainVM.lean` に 2 構成子を足した（core ファイル単体は `lake env lean` で `BUILD=0`）:
```
| watchBreak (w) (hp : positive w.lag = true) (hng : ¬ GalilScaffoldChainWatch.Good w) :
    ChainStep (.watch w) (.broken ⟨⟨GalilScaffoldChainVerifier.right w.machine.verifier, w.machine.control⟩, w.lag, w.margin⟩)
| brokenMatched (w) : ChainMatched (.broken w) (.broken ⟨w.machine, inc w.lag, inc w.margin⟩)
```
根拠（Scala 一次情報）: `consume()` は先に `verifier.right()`、不一致なら `mode = Broken` で `false`
（`distance`／`period`／`lag` は触らない）；`matched()` は `margin.inc()` のあと Watch∧lag=0 以外は
`lag.inc()`；restart guard は `Broken ∧ margin ≥ 0 ∧ last > 0 ∧ lag == 0`（`ScaffoldGalil.scala:230-231`）
なので正 lag の broken chain は fallback まで生き続ける。
壊れる箇所のパターン: (A) `ChainStep` の `cases` に `watchBreak` 行き `.broken` の alternative
（不変量は `.broken` で `True`／空虚）、(B) `ChainMatched` の `cases` に `brokenMatched`、
(C) `chainStep_unique`／`chainMatched_unique` は `Internal` の `idle`（`positive lag = false`）／`take`（`Good`）
と `hp`／`hng` で排他、(D) `ChainStepGap.no_chainStep_at_positive_lag_mismatch`（＋`Canonical.model_gap_watchBreak`）
は**偽になる**ので削除して「gap は閉じた」に書き換える。作業リストは `lake build --quiet PalPeg` の error 一覧。
- 進捗（作業中）: 低層 11 モジュール＋中層（TrailChain／TrailAssembly／CopyPhase*／BranchSupply／
  TickFalse／PreludeDone／PreludeEnds）を修正済み。break 終端の定理群（`foundRouteMC_noshift'(_Inv)`／
  `rounds_break`／`life_restarted`／`found_life`／`found_to_found` …）は正 lag の break で結論（restart）が
  偽になるので、終端比較の仮説に `(hz3 : zero w3.lag = true)` を全ファイル一括で足した（regex、29 ファイル）。
  `CloseoutTickFalse.step_ne_broken` は `hOk : WatchOk Ok` を取るように（`WatchOk` は反証済みの死路）。
- dead 塔の切り離し: `unconditional` の import 閉包（598 モジュール）の外にある Workbench 登録 9 本
  （`CloseoutLagAll`／`CloseoutSegCheckpoint`／`CloseoutWatchRound26`／`51`／`53`／`FoundPackCorrected`／
  `FoundPackRefute`／`ReachesWatchFromRun`／`RoundHistory`）は、構成子追加で**偽になった**補題
  （`CloseoutWatchRound2.watchClosed : WatchClosedC`「watch は背景 tick で watch のまま」、
  `distance_mono_false`）を含む round 塔（`CloseoutWatchRound*`／`WatchPhase*`／`TerminalN`／
  `MismatchCompare`／`TickFalse`）を引き込んでいたので登録を外した（ファイルは未削除、build 対象外）。
  `WatchClosedC` はモデル欠陥 `M-watchBreak` の上でだけ真だった。
- 台帳 `GalilTrailAssembly.LagLe` は broken chain の lag を `reset` と読む（`lagOf (.broken w) = some (verifier, reset)`）:
  break 前 `ver + lag ≤ r`・`lag ≥ 1` から break 後 `right ver ≤ r`（`lagLe_break`）。`ChainBudget.pos`（先読み予算）は
  broken の verifier にも要るので空虚化はしない。

## n248 — `obligation_cycleOracle`: found 経路の既存入口は死んでいる（修理しない）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし（地図の続き）。`hfound` の既存入口 `CloseoutFoundRoute1.foundExit_compare_final20` は **約 25 個の名前付き前提**（`ChainTickable`＝`WatchOk` 経由で反証済み、`StageEntryC`＝`fuel` 場が偽（n181）、`ShiftBreakOracleC`／`ShiftRoundAtC`／… の round 機構）を取る。round 機構は n233 で左端の番兵に壊れることも分かっている。**この塔は修理せず、found 経路を一から `WindowRunPack` の上に組む** |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 の木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### `FoundRouteMC2`（`GalilOracleMC2:374`、inductive）が要求するもの

found tick の着地 `⟨c', t⟩`（segment の終端、`SegReachedW`）から:
* `report`（`ReachAtC2`: 報告点 m に着く）、または
* `shift`／`noShift`: `FoundCost`（`StepsAll (SoundScanNR) k ⟨c',t⟩ ⟨cT,sT⟩ ∧ CostedRun`）＋ `MInv`（最左 live 中心）＋ `Restarted`＋`FoundResidual`（mode scan・clock 2048・`StageEntry`・`Frontier`・`ReplayRest`・`ShiftIdle`）＋`SpanRep`＋中心前進＋`position sT.right ≤ 2m−1`、または
* `broke`: run＋`CostedRun`＋`InvLP2`＋`CentreRep`＋中心同じ＋右ヘッド前進。

一次部品 `GalilScaffoldTopLifeRestart.life_restarted`／`FoundLoop.found_to_found` は run の**形**（segment `bs ++ dm :: cs`、rounds、最後の segment、壊れる比較）を仮説に取る「形が与えられれば台帳が出る」定理。**欠けているのは形の存在**＝決定的な機械を found tick から回して、最初の不一致（shift／fallback）か break（restart）に着くまでの run を構成すること。

### 組み方（次のセッションの一手目）

1. run の存在: `GalilTickFun.tickFun`（choice で 1 つ選ぶ）の反復で `Steps k x (iterate tickFun k x)`。`SoundScanNR` の注釈は `OutputRel` の tick 保存から。
2. found tick 後の chain は `WindowRunPack.window`（`ChainWindowRun`）が run に依らず記述する（n238–n246）。copy → back → watch の相は `WindowInv` の分岐そのもの。
3. 着地の分類は `Tick` の構成子で機械的: `scan_shift`（guard 成立→`ShiftPal` は `shiftPal_of_windowRunPack` で既にある）／`scan_fallback`／`restart`（broken）。`life_restarted` の後半（restart tick → `Restarted`）を流用。
4. `MInv`（`Leftmost`）は `GalilLiveCentre*`（2026-09-16、scan segment・fallback・replay の保存）にある。

## n247 — `obligation_cycleOracle` の地図（葉の塔は `hpres`（偽）の上に建っている）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_cycleOracle` | 変化なし（地図のみ、定理は足していない）。下の表が一次情報（`grep "^theorem"` と署名の実読） |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、n246 と同じ木）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 消費者から見た形

`obligation_cycleOracle entry q first : ∀ w, 0 < |w| → CycleOracleMC3 (PofC centreC placeC entry w) q first w`。
`CycleOracleMC3 P q first raw := ∀ m c r, 1 ≤ m → m ≤ |raw| → InvLPS P q first raw c r → position r.right ≤ 2m−1 → CycleOutMC3 …`、
`CycleOutMC3 := ReachAtC3（報告点 m に着く）∨ ∃ cT sT k L, StepsAll (SoundScanNR) k ⟨c,r⟩ ⟨cT,sT⟩ ∧ CostedRun ∧ InvLPS cT sT ∧ mu sT < mu r ∧ position sT.right ≤ 2m−1`。
つまり「`InvLPS` から次の `InvLPS`（`mu` 減少）か報告点まで、機械の run を**構成**する」。

### 既存の塔（`CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`）

| 葉 | 現状の producer | 状態 |
|---|---|---|
| `hlift : InvL → InvLPS`（bridge） | `Inv` 枝は `replayStage_of_inv`、`InvScan` 枝は `hstage_of_scanBranch (hsc : H_stageScan)` | `H_stageScan` は**反証済み**（`InvScan` は radius に触れない）。再切り出し `InvScanS`（`CloseoutStageSupply`）／`InvSS`（`CloseoutInvScanS`） |
| `hreadyB`（`ReadyIface` ＋ Φ at `InvLPC`） | `readyIface_readyPacedS` ＋ `readyPacedS_restarted`（`CloseoutReadyStage`） | 閉じそう（未接続） |
| `hpresRepAt`（`HpresRepAt` at every `InvLPC`） | **なし**（`CloseoutOracle7` ヘッダが理由を明記） | producer ゼロ |
| `hshape : StartShape` | `startShape'_of_decodes` は **`StartShape'`**（replay 中・`ReplayStageD` 付き） | `StartShape` は**偽**（CLAUDE.md §3b）。塔がこの形を要求する限り塔は使えない |
| `hstage : ReplayStageInv` | **なし** | producer ゼロ |
| `hended` / `hlastMatch` / `hlastMismatch` | `GalilLeafReport.hended_C`／`GalilOracleMC4.hlastMatch_C'`／`GalilLeafReport.hlastMismatch_C` | 全部 `hpres : SearchReady → searchEffect → SearchReady` を取る。**偽**（`CloseoutPresRefute.hpres_fails_at_zero_debt`: debt 0 で破れる）。`hlastMismatch_C` は加えて `LastMismatchReport`（producer なし） |
| `hmismatch` | `GalilLeafDp.hmismatch_of_residues'` | 側入力 `hdp'`（`MismatchDp`）／`hbud`（`StageBudgetAt`）／`hfb`／`hpos`（producer 未確認） |
| `hfound` / `hfoundBg` / `hfoundReplay`（`FoundRouteMC2`／`FoundInReplayRouteMC2`） | **なし** | producer ゼロ。found 経路そのもの |

### 判断

葉の塔は `hpres`（偽）の上に建っていて、`hshape` も偽の形。**塔を修理するより、`ReadyClosure`
（`GalilReplaySpan.ReadyClosure`: `ready`／`seg`／`restart` の 3 場、`CloseoutPreload11.readyClosure_S2`
が `PostRun` ＋ `RestartS2` から出す）の上で `InvLPS → 次の着地` を直接構成する。**
一次部品: `restarted_next_found`（`GalilScaffoldTopReadyFound`）、`life_restarted`／`found_to_found`
（`GalilScaffoldTopLifeRestart`／`FoundLoop`）、`fallback_restarted_All`
（`GalilScaffoldTopFallbackRestartAll`）、`prep_segment_construct_of_found`、`SegReachedW`
（`segment_of_invLP`）。次の一手は `hshape` の消費点（`CloseoutOracle5:249`、found-in-replay 経路）
を読んで `StartShape'` で足りるかを機械で確認すること。

## n246 — **公理 3 → 2**: `obligation_shiftPalResiduesAlongRun` を証明して削除

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | **消えた。** `#print axioms PalPeg.PalInPeg.unconditional` は `[propext, Classical.choice, Quot.sound, obligation_cycleOracle, obligation_localRealization]`（`Axioms.lean` の guard 更新済み、`lake env lean` で直接確認）。残差は run 上の pack `WindowPack.WindowRunPack`（`ChainWindowRun`／`Coupled'`／scan・shift での `CentreRep`／`RadiusRep` 台帳）から読み出せる: `WindowPack.shiftPal_of_windowRunPack (hpack : LPackM) (hx : WindowRunPack) (hcan : canRight right) (hs : ScanNR) : ShiftPal`。`2h ≤ R` は `Coupled'.watch` の両枝（fresh: `FreshC` ＋ phase 4 → `four_of_freshC`、post-shift: `CloseoutPackRun40.four_of_other'`）から `four_of_guard : 4h ≤ radius`。pack は `IPackMW` の新しい場 `win : Decodes (PofC …) → WindowRunPack` として oracle の鎖（`StepsIMW`／`CycleOutIMW`／`H_bootIMW`／`PreTraceIMW`）を自動で流れる。run 形の消費者 `packRunR_MW_marksFree` は `hShiftPalAlongRun` の代わりに `hP : Decodes` を取り（`given_scanLandingObligations` は `decodesC entry w`）、tick ごとに `hn.ipackM.win hP` から `ShiftPal` を出す。trace 形 `obligation_shiftPalAlongTrace` は `PreTraceIMW.packs j` の `win` から定理に |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`）・標準公理のみ（3 本）・無条件 PAL は未完（残り 2 公理）。**

### 何を足し、何を消したか

- 新: `PalPeg/WindowPack.lean` — `WindowRunPack`（5 場）、`windowRunPack_boot`／`_of_invLPC`（起点）、`four_of_freshC`／`four_of_guard`（guard 点の `4h ≤ radius`）、`source_watch_of_guard`（guard が立つ着地の源 chain は watch、`backDone` の新鮮 watch は phase 0 で矛盾）、`shiftPal_of_windowRunPack`、`ledger_tick`（24 構成子）、`windowRunPack_tick`。全部標準公理のみ。
- 変更: `IPackMW` に `win` 場（`CloseoutPackW`）。`ipackMW_tick`／`bigPack2MG7W''_tick`／`_tick_M` が `windowRunPack_tick` で運ぶ。`ipackMW_of_invLPC`（起点）と `h_bootIMW_of_bootIPack`（boot の i = 0, 1）が供給。`chainWindowRun_tick` の側仮説は mode guard 付きに弱め、`canRight` は tick 構成子の `available`（非 replay）と `FrontPack`（replay: `canRight_of_frontPack`）から。
- 消した: 公理 `obligation_shiftPalResiduesAlongRun`、`obligation_shiftPalAlongRun`、`obligation_shiftPalResiduesAlongTrace`、`given_scanLandingObligations` の `hShiftPalAlongRun`、参照ゼロの `bigPack2MG7W_of_bigPack2MG7`、`ShiftPalAlongTrace.chainIdle_after_init`（`BranchSupply` の import を切るため。`ShiftPalAlongTrace` は `BranchSupply` → `CloseoutCheckW` → `CloseoutPackW` を経由していたので、`CloseoutPackW` が `WindowPack` を import すると循環した）。

### 次

残り 2: `obligation_cycleOracle`（`CycleOracleMC3`、found 経路の葉 `hshape`／`hfound`／`hfoundBg`／`hfoundReplay`／`hpresRepAt` は producer ゼロ ＝ 形式化のミスとして再切り出し）と `obligation_localRealization`（`H_realizeLIMW'`）。

## n245 — 公理進捗: `ChainWindowRun` の `Tick` 保存 `WindowTick.chainWindowRun_tick`（24 構成子）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓を運ぶ run 不変量 `ChainWindowRun` が **`galilFrameS` の 1 tick（24 構成子全部）で保たれる**ことを証明（`WindowTick.chainWindowRun_tick`、標準公理のみ）。周辺事実は仮説で取る: `Decodes (PofC …)`（`decodesC` でタダ）、`AuxPack`（`idleOut` で非 scan/shift/init の chain idle、`copyP` で `shift_one` の `remainingPos` 選言を潰す）、`CentreRep`、右ヘッドの `Represents`/`focus ≠ none`、scan かつ `clock = 1` での `canRight right`、scan での `RadiusRep radius R' ∧ position right = center + R'`。scan 側 4 構成子は `chainWindowRun_background_case`（`backgroundS` 展開: chain 1 歩／idle／誕生）・`_match_case`（一致比較の `afterCompare`＋`matchedPlace`）・`_shift_case`（不一致 → `shiftGuardVM` → `beginShiftVM'`、`Good w` は guard の記号一致と `WindowInv` の lag 0 窓から `good_of_guard`）・`_shiftOne_case`（`shiftLens.rel` 越しの `shiftTick`）。残り: `Steps` 帰納で周辺事実を run に沿って供給する層（`auxPack_steps` は各到達点の `CentreLive` を要求、`RadiusRep` は `Restarted`＋`radius_rep_inc`）と、guard 点での残差取り出し（`2h ≤ R` の cycle 算術） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 起きたこと（機械の出力）

- `lake env lean PalPeg/WindowTick.lean` → `BUILD=0`、`sorryAx` なし、7 定理すべて `[propext, Classical.choice, Quot.sound]`。
- `import PalPeg.WindowTick` を `Workbench.lean` の `WindowRun` 直後に登録、`lake build --quiet PalPeg` → `BUILD=0`。
- 直したもの（前ノートの型検査エラー 7 件）: `open A (x) B (y)` は 1 行に書けない（分割）／`rewindLens_rel_chain` の `rw` 後の `rfl`／`compare_target_heads` の未使用 implicit 3 つ／`rw [← hy, …]` の向き／`shiftOne_case` の `htright` に `rfl`、`right_position s.center hcanC'`（`shiftLens.get` 越しの `canRight` は defeq）／`match_case`・`shift_case` 呼び出しの `hmode := rfl`／fpp・rewind 構成子の idle 分岐は `apply chainWindowRun_of_idle; rw [lens]; exact hidle …` の 3 行に展開。

## n244 — 公理進捗: run 層の窓不変量 `ChainWindowRun` と VM 遷移ごとの transport 8 本

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓を run に沿って運ぶ `State GalilVM` 上の不変量 `WindowRun.ChainWindowRun`（`WindowInv`＋右ヘッド `R = position s.right`＋中心のずれ: scan で `center = cen₀ + k·h`、shift 中は `center + remaining = cen₀ + (k+1)·h`）と、VM 遷移ごとの transport が揃った（全部標準公理のみ）: `chainWindowRun_of_idle`／`_of_broken`／`_chainStep`（background の chain 1 歩）／`_birth`／`_birth_matched`（誕生）／`_matched`（一致比較: `ChainStep` → `ChainMatched`、右ヘッド +1）／`_shift`（不一致 → `immediate`、phase 0 の新鮮 watch は guard の phase 4 と矛盾）／`_shiftOne`／`_shiftDone`。残るのは `Tick` ごとの組み立て（`backgroundS`／`compareFound`／`beginShiftVM'`／`shiftOne` の展開と周辺事実）と `Steps` 帰納、そして残差の取り出し |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `Tick` 組み立てに要る周辺事実（run 層が供給するもの）

| 事実 | 使う遷移 | 供給元候補 |
|---|---|---|
| `Coupled.idleOut`（非 scan/shift/init で chain idle） | rewind 等 | `AuxPack.coupled`（`auxPack_steps`） |
| `CopyPack`（`mode ≠ copy → CopyIdle`） | `shift_one`/`shift_done` の `remainingPos` | `AuxPack.copyP` |
| `CentreRep raw s` | 誕生・shift 1 歩 | `InvLPC` 起点＋`centreRep_congr` |
| `Represents s.right.head ∧ focus ≠ none`、`canRight s.right` | 比較 | `Inv.input`／`Extra7.scanAvail`／replay は `Frontier` |
| `RadiusRep s.radius R' ∧ position s.right = center + R'` | 誕生 | `Restarted`＋`radius_rep_inc`（scan 区間の不変量、要確認） |
| 中心記号 `x[center]? = some (P.centre s)` | 誕生 | `decodesC`＋`CentreRep`（`read_represent`・`represented_read`） |

## n243 — 公理進捗: chain の一生の不変量 `WindowInv` と 5 つの transport（DP の形の葉なし）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の窓 `WatchWindow` を chain の一生（誕生 `chainStart` → copy → back → watch）を通して運ぶ chain 側の不変量 `WindowInv.WindowInv` と、全遷移の transport が揃った（`windowInv_start`／`_step`（`ChainStep`）／`_matched`（`ChainMatched`）／`_immediate`（shift 入口）／`_shiftOne`、標準公理のみ）。**`AnswerAhead`／`PlaceAhead`／`StartShape` などの DP の形の葉は使わない**——ブロックの中身 `b xs` は `copyEnd` で決まり、`backDone` で `coreX_born` が制御を作る。残るのは run 層（`Tick` ごと）への持ち上げと、中心のずれ `cen = cen₀ + k·h`・`2h ≤ R`・`ScanInvariant`／`canRight` の供給 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `WindowInv raw cen₀ R cc : ChainVM → Prop`

| 枝 | 中身 |
|---|---|
| `idle`／`broken` | `True` |
| `copy … v lag _ ver` | `VerAt raw cen₀ ver ∧ LagAt lag ver R ∧ ∃ ys, v = fill (start cc) ys` |
| `back v _ lag _ ver` | `VerAt raw cen₀ ver ∧ LagAt lag ver R ∧ ∃ b xs, flat v = blockTokens cc b xs` |
| `watch w` | `∃ b xs, WatchWindow raw cen₀ R cc b xs (.watch w)` |

誕生: verifier ＝ 中心ヘッド（`VerAt`）、lag ＝ 半径カウンタ（`lagAt_radius`）。
`copyBit` は `fill_append`、`copyEnd` は `fill_last_focus`＋`flat_block`、`backStep` は
`flat_moveLeft`、`backDone` は `rewound_of_flat`＋`coreX_born`（窓は空虚）、watch は n242 の補題。

### 次の一手（run 層）

`Tick` ごとの持ち上げ: `scan_wait`／`scan_count`（`backgroundS` の `chainAt false` ＝ `ChainStep`）、
`scan_match`（`compareFound` の `chainAt true` ＝ `ChainStep` → `ChainMatched`、誕生は第 3 選言）、
`scan_shift`（`ChainStep` → `beginShiftVM` の `immediate`）、`scan_fallback`（chain idle）、
`shift_one`（`chainShiftOne`）、他のモードは chain idle。中心のずれは scan で `cen₀ + k·h`、
shift 中は `center + remaining = cen₀ + (k+1)·h`。

## n242 — 公理進捗（訂正 3）: `WatchWindow` の制御を `SamePrediction` 版 `CoreP` に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の文面は不変（`WatchWindow` の名前で参照）。中身の `CoreX`（制御 ＝ `run (ready …) pre` そのもの）は `chainShiftOne` が sweep カウンタ（distance/boundary/last）を `dec` するので shift 以降は偽——`SamePrediction m.control (run … pre)`（period テープと進行方向だけ）＋`broken = false` の `CoreP` に置き換えた。予測記号は `GalilScaffoldChainPrediction.continued_prediction`（「カウンタを調整した継続は元の予測器の位相を保つ」）で従来どおり出る。**これで `WatchWindow` は chain の全遷移で保たれる形になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか（`ShiftPalAlongTrace`、全部標準公理のみ）

| 定理 | 内容 |
|---|---|
| `CoreP` / `coreP_of_coreX` | `CoreX` の弱化と、誕生時（`coreX_born`）からの変換 |
| `symbol_of_coreP` | 予測記号（`continued_prediction` 経由、右端の余裕不要） |
| `coreP_consume` | `Good` 付き consume で保存（`coreX_consume` の `SamePrediction` 版） |
| `coreP_chainShiftOne` | `chainShiftOne` で保存（defeq） |
| `window_consume_of_good` | `Good` 付き consume: verifier +1・窓 +1・`CoreP` |
| `watchWindow_step` / `watchWindow_outer` / `watchWindow_shiftOne` | background（`Internal`）／一致比較（`Outer … true`: `queued` は `lagAt_inc`、`immediate` は consume）／shift 1 歩 |

### 次の一手

chain の一生の不変量 `WindowInv raw cen₀ R cc : ChainVM → Prop`（idle: True／copy: `VerAt`＋`LagAt`＋
`∃ ys, v = fill (start cc) ys`／back: `VerAt`＋`LagAt`＋`∃ b xs, flat v = blockTokens cc b xs`／watch:
`∃ b xs, WatchWindow`／broken: True）と、`ChainStep`／`ChainMatched`／誕生（`chainStart`）／
`immediate`（shift 入口）／`chainShiftOne` の transport。**DP の形の葉（`AnswerAhead`／`PlaceAhead`／
`hshape`）は不要**——ブロックの中身 `b xs` は `copyEnd` で決まる。その後 run 層（`Tick` ごと）へ。

## n241 — 公理進捗（訂正 2）: `WatchWindow` の窓を「verifier が消費した接頭辞」に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差の文面は不変（guard 点は lag ゼロなので verifier ＝ 右ヘッド）。`WatchWindow` の定義を `BlockOn … (cen₀+1) (position ver)`（消費接頭辞）に直した——n240 の形（`BlockOn … R`、右ヘッドまで）は **lag > 0 の間の run 不変量としては過剰**（`chainW_matched` は窓の終端 `E` を変えずに右ヘッド `R` だけ進める）。この形なら chain 自身の歩みだけで維持できる: `take`／`immediate` は持参する `Good`（予測 ＝ 次の読み）で窓が 1 つ伸び（`blockOn_succ_of_symbol`）、`queued` は不変、shift（`chainShiftOne`）も不変 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### producer の設計（一次情報で確認したもの）

* 誕生: `chainAt` の第 3 選言で chain は `chainStart answer (P.centre s) walker s.center s.radius`（`.copy`）。
  `backDone` で `.watch ⟨ver, watchControl v⟩` になり、`CoreX` は `coreX_born`（DP の形の葉は不要:
  `Represents ver.head`・存在・`position ver + 1 = anchor` だけ）、`LagAt` は `lagAt_radius`、
  窓 `BlockOn … (cen₀+1) cen₀` は空虚。中心記号は `Decodes`＋`read_represent`＋`represented_read`
  （`InvLPC` の `CentreRep`）から `(encoded raw)[position s.center]? = some (P.centre s)`。
* 一致比較: `ChainMatched.watch (ho : Outer w true w')`——`queued`（lag +1、`lagAt_inc`）か
  `immediate`（`Good` 持参で窓 +1）。background: `ChainStep.watchStep (Internal)`（`watchWindow_step`）。
* shift: `beginShiftVM` の `immediate`（窓 +1、guard の予測一致）と `shift_one` の `chainShiftOne`
  （sweep カウンタと margin だけ、窓と lag は不変）。
* `2h ≤ R`: 新鮮な shift は guard の margin（`4h ≤ R`）、継続 round は cycle 算術
  （shift 直後 `R + 1 − h ≥ 3h + 1`、round 中は増えるだけ）。

## n240 — 公理進捗（訂正）: 残差の chain データを `ChainW` から 3 場の `WatchWindow` に絞った

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | n238 の残差は `ChainW … cen₀ …`（margin 等式込み）を要求していたが、**これは最初の shift 以降は偽**（下記）。producer が使う 3 場（`LagAt`／`BlockOn`／`CoreX`、誕生中心 anchor）だけを要求する `ShiftPalAlongTrace.WatchWindow` に置き換えた。**公理は弱くなり、`periodOnly = true` の shift 入口でも真たりうる形になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### なぜ `ChainW` では偽だったか（一次情報）

`GalilScaffoldChainInputSupply.chainShiftOne`（`:1478`）は shift 1 歩ごとに `margin` を `dec` し、
`beginShiftVM` の `immediate` は `inc margin` と verifier +1。`ChainW` の `.watch` 枝の等式
`value margin + 4h = R − C` は `C` を**現在の中心**（shift ごとに `+h`）に取れば保たれるが、
`BlockOn`／`CoreX` の anchor は**誕生中心**（`bounce cc b xs` の位相）。1 つの `C` で両方は
満たせないので、誕生中心を `C` にした `ChainW` は最初の shift 以降は成り立たない。
自分で書いた残差の過剰な主張——`chainShiftOne` を読んで気づいた（機械検査した反証は無い）。

### 何を証明したか

| 定理 | 内容 |
|---|---|
| `ShiftPalAlongTrace.WatchWindow` | `.watch w ↦ LagAt w.lag ver R ∧ BlockOn … (cen₀+1) R ∧ CoreX … (cen₀+1) w.machine`、他は `False` |
| `ShiftPalAlongTrace.watchWindow_of_chainW` | `ChainW … cen₀ R R …` の `.watch` 枝から（誕生直後、shift 前） |
| `ShiftPalAlongTrace.watchWindow_step` | `Internal` 1 歩（`idle` は不変、`take` は verifier +1・lag −1、`Good` は `take` が持参） |
| `freshShiftLedger_of_chainW`／`_scan` | 仮説を `WatchWindow` に差し替え。`_scan` は `chainW_step`／`chainStep_unique`／`LandingData` が不要になった（`ChainStep` の `.watch` 構成子は `watchStep` だけ） |

### 残差（run 層に要求するもの）の現在形

不一致比較の直前 `z` で shift guard が立つなら
`∃ cc b xs cen₀ k R, position z.vm.center = cen₀ + k·h ∧ WatchWindow w cen₀ (cen + R) cc b xs z.vm.chain ∧
ScanInvariant w cen R … ∧ canRight z.vm.right ∧ x[cen₀] = cc ∧ 2h ≤ R`。
producer は `WatchWindow` を run に沿って運ぶ: 誕生（`chainW_start`＋`blockOn_of_candidate` →
`watchWindow_of_chainW`）、background（`watchWindow_step`）、一致比較（窓 +1: `coreX_consume`＋
`blockOn_succ_of_symbol` 形）、shift 相（`immediate`＋`chainShiftOne`: `LagAt` は verifier +1、
`BlockOn`／`CoreX` は不変——`chainShiftOne` は sweep カウンタと margin しか触らない）。

## n239 — 後始末: 参照ゼロになった `ShiftInv` 入口の組み立て群を削除、docstring を現状に

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 変化なし（n238 の窓 1 本のまま）。次は run 層の producer |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

削除（参照ゼロ・round 機構経由の旧経路。n232 の git 履歴に残る）:
`shiftInv_of_watch_entry`／`pred_immediate`／`immediate_lag_unbroken`／`coreX_immediate`／
`palNext_of_centre`／`shiftPal_of_chainNotWatch`。残した部品は全部 `freshShiftLedger_of_chainW`
が使う（`symbol_of_coreX`／`blockOn_succ_of_symbol`／`cells_run`／`periodLength_of_coreX`／
`block_last_of_blockOn`／`palAt_block_of_centre`／`bounce_getElem?_symm`／`periodOn_of_blockOn`／
`palAt_mirror`／`periodOn_extend_left`／`palAt_shift_half`／`palAt_block_periodic`）。
`ShiftPalAlongTrace` の冒頭と `Workbench` の該当節を n238 の形に書き換えた。

### 次の一手（run 層の producer）

窓の残差を run に沿って運ぶ pack 場を足す:
`ChainWindowAt raw s := ∃ cc b xs cen₀ k R bud, position s.center = cen₀ + k·h ∧
ChainW raw cen₀ (cen+R) (cen+R) bud false cc b xs s.chain ∧ x[cen₀] = cc ∧ 2h ≤ R`
（chain が watching のとき）。維持: 一致比較 `chainW_matched`、background `chainW_step`、
shift 相（右ヘッド不動・chain は lag 0 で idle）、誕生 `chainW_start`＋`blockOn_of_candidate`
（found／replay 両経路とも `Candidate` を持つ）。

## n238 — 公理進捗: `obligation_shiftPalResiduesAlongRun` を窓 1 本に置換（偽の第 2 連言と `H_readsShift` が消えた）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 3 連言（`H_readsShift`／`H_freshShiftAtShiftEntry`／窓）→ **1 連言**: 不一致比較の直前で shift guard が立つ点 `z` に、誕生中心 `cen₀` に anchor した `ChainW` の窓（現在の中心は `cen₀ + k·h`、窓は右ヘッドまで）＋`ScanInvariant`＋`canRight`＋`x[cen₀] = cc`＋`2h ≤ R`。`periodOnly` の区別なし。n233 で偽（条件付き）と分かった `H_freshShiftAtShiftEntry` と、round 機構の `H_readsShift` は**公理から消えた**。`ShiftPal` は round 機構（`shiftPal_of_run_B`／`RoundScan`）を経由せず、窓の周期構造から直接出る |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか

| 定理 | 内容 |
|---|---|
| `ShiftPalAlongTrace.palAt_shift_half` | 半径 `h` の回文は周期 `2h` で `h` だけ右へ写る |
| `ShiftPalAlongTrace.palAt_block_periodic` | 誕生中心から `h` 刻みの全中心 `cen₀ + (j+1)h` はブロック回文（`j = 0` は `palAt_block_of_centre`、以降は `palAt_shift_half`） |
| `ShiftPalAlongTrace.freshShiftLedger_of_chainW`（一般化） | 誕生 anchor の窓＋`cen = cen₀ + k·h`＋`2h ≤ R` から `FreshShiftLedger` の 5 成分。margin には触れない |
| `ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan`（一般化） | 比較前の窓から（chain の 1 歩を `chainW_step`＋`chainStep_unique` で渡す） |
| `obligation_shiftPalAlongRun` / `obligation_shiftPalAlongTrace` | 窓の残差 → `shiftPal_of_freshShiftLedger` で `ShiftPal`。trace 形は `canRightAtScanOrShift_alongTrace` で `canRight` を取る |

削除（参照ゼロ）: `shiftPal_alongRun`／`shiftPal_alongTrace`／`roundBundle_alongTrace`
（round 機構経由の旧経路）、`freshShiftLedger_of_landing`（`LandingData` 射影のデモ）。

### なぜこれで正しいか（一次情報）

* 窓 `ChainW … cen₀ …` は一致比較で 1 つ伸び（`GalilReplaySpan.chainW_matched`）、shift は右ヘッドを
  動かさない（`beginShiftVM`／`shiftOne` は `center`・`left` だけ）。誕生 anchor は変わらない。
* 現在の中心 `cen₀ + k·h` の右 `h` の回文は `palAt_block_periodic`、`h < i` は現在の回文で鏡映して
  窓の周期で進める。左端の不一致は語レベルの主張に影響しない。
* Scala `ScaffoldChain.checkPair` の assert（継続中は予測一致、`cycleEnd` でだけ不一致）とも整合。

### 残差（run 層に要求するもの）と producer 候補

| 残差 | producer 候補 |
|---|---|
| `ChainW`（誕生 anchor）を不一致比較の直前まで運ぶ | replay 生まれ: `CloseoutWatchRound48/50/53`（`LandingData` の transport、ただし `C := position t.center` で shift を越えると anchor がずれる → `cen₀` 固定に直す）。found 生まれ: `GalilReplaySpan.blockOn_of_candidate`＋`chainW_start`（誕生時）＋同じ transport |
| `x[cen₀] = cc` | 誕生時の `Candidate`（`candidate_bounce` の `hc0 : w[0]? = some c`、`blockOn_of_candidate` の `hcen`） |
| `2h ≤ R` | 新鮮な shift: guard の margin（`4h ≤ R`）。継続 round: 半径は `R + h` ずつ増える |
| `ScanInvariant`／`canRight` | `LandingData`／`LiveScanChain`／`WatchSegE.match` の `ha` |

## n237 — 公理進捗: 第 3 連言を「不一致比較直前の窓＋中心記号」に置き換えた（操作 B）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言が `FreshShiftLedger` から、その**十分条件である一次事実**——不一致比較直前 `z.vm` の `ChainW … (position z.vm.center) (cen+R) (cen+R) bud false cc b xs z.vm.chain`＋`ScanInvariant … R`＋`canRight`＋中心記号 `(encoded w)[cen]? = some cc`（`shiftGuardVM s'` の下で）——に置き換わった。橋は `ShiftEntryFromLanding.freshShiftLedger_of_chainW_scan`（標準公理のみ）。trace 形定理も同形に。**本数は 3 のまま、中身は run 層に既にある形（`LandingData` の射影）になった** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 次の一手（設計が確定した）

`GalilRoundPeriod.ReadOrigin`／`roundScan_entry` は `hroom : radius + 2 ≤ center` を仮説に取る
——round 機構は最初から左端を除外している（第 2 連言が偽だった理由）。一方、窓の議論は
左端でも成り立ち、**`periodOnly = true` の shift 入口でも同じ**: 誕生中心 `cen₀` に anchor した
`ChainW` の窓は一致比較で伸び（`chainW_matched`）、shift は右ヘッドを動かさないので保たれる。
現在の中心 `cen' = cen₀ + k·h` について、shift 先 `cen' + h` の半径 `h` の回文はブロックの
周期構造（`bounce` は `b` と `cc` の両方で対称）から出る。

したがって **3 連言全部を「不一致比較直前の誕生 anchor 窓」1 本に置き換えられる**:
`∃ cc b xs cen₀ k R bud, position z.vm.center = cen₀ + k·(|xs|+1) ∧ ChainW w cen₀ … ∧ ScanInvariant ∧ canRight ∧ x[cen₀] = cc ∧ 2(|xs|+1) ≤ R`。
`FreshShiftLedger` の producer を `cen₀`/`k` で一般化し（margin の代わりに `2h ≤ R` を取る）、
`shiftPal_of_freshShiftLedger` で `ShiftPal` を直接出す——`shiftPal_of_run_B`（round 機構）を
経由しない。偽の第 2 連言と `H_readsShift` は公理から消える。

## n236 — 公理進捗: 第 3 連言の guard を `¬ matched s'` に狭めた（操作 A・公理は弱化）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言が不一致比較（`¬ (galilFrameS …).matched s'`）でだけ `FreshShiftLedger` を要求する形になった。消費者 `shiftPal_of_freshShiftLedger` は `ShiftPal` の前提から `¬matched` を持っているので何も失わない。一致比較の着地（`afterCompare`、chain は `ChainMatched` 越し）を主張から外した |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

編集 5 箇所: `shiftPal_of_freshShiftLedger`／`shiftPal_alongTrace`／`shiftPal_alongRun`（`ShiftPalAlongTrace`）、
run 形公理と trace 形定理（`PalInPegUnconditional`）。`Axioms.lean` の guard は変化なし（3 本）。

## n235 — 公理進捗: 第 3 連言の wrapper `freshShiftLedger_of_landing`（`LandingData` から）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger w z.vm s'` が、比較前・clock 1 の状態の `CloseoutWatchRound42.LandingData`＋`canRight`＋中心記号 `x[cen] = cc`＋`compareFound`（不一致枝）から出る（`ShiftEntryFromLanding.freshShiftLedger_of_landing`、標準公理のみ）。比較量子の中の chain の 1 歩は `chainW_step`＋`chainStep_unique` で渡した。**第 3 連言に残る run 層の入力は「不一致比較の直前で `ChainW` 形の窓と中心記号を持つ」だけ** |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 次の一手

1. 第 3 連言の guard を `¬ matched s'` に狭める（消費者 `shiftPal_of_freshShiftLedger` は
   `ShiftPal` の前提から `¬matched` を持っている——操作 (A)、公理は弱くなる）。
2. 第 3 連言を「不一致比較の直前で `ChainW` 形の窓（`z.vm.chain`）＋`position z.vm.right = cen + R`＋
   `ScanInvariant`＋`canRight`＋`x[cen] = cc`」に置き換える（操作 (B)）。producer 候補は
   replay 経路の `LandingData`（射影するだけ）と found 経路の `blockOn_of_candidate`＋`chainW_start`。

## n234 — 公理進捗: 第 3 連言 `FreshShiftLedger` の producer（左端でも真）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の中身 `FreshShiftLedger w s s'` が、`ChainW` 形の窓（比較後の chain）＋中心記号 `x[cen] = cc`＋比較後の右ヘッド 3 事実から 1 本の定理で出る（`ShiftPalAlongTrace.freshShiftLedger_of_chainW`、標準公理のみ）。**左端の不一致でも成り立つ**（n233 で偽と分かった第 2 連言と違い、5 成分とも語レベルで左端に触れない）。残るのは `LandingData` からの wrapper（次） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 部品（全部 `shiftInv_of_watch_entry` と共用）

| 定理 | 内容 |
|---|---|
| `block_last_of_blockOn` | `x[cen + 2h]? = some cc`（`bounce` の末尾は `cc`） |
| `palAt_block_of_centre` | `PalAt x (cen + h) h`（ブロック回文。`palNext_of_centre` から切り出し） |
| `palAt_mirror` | `PalAt x C R → PalAt x (C+d) r → d + r ≤ R → PalAt x (C−d) r` |
| `periodOn_extend_left` | 周期区間を左へ 1 つ伸ばす |
| `freshShiftLedger_of_chainW` | 5 成分: `palAt_mirror`（`hIn`）／`periodOn_mirror`＋`periodOn_extend_left`（`hLeft`）／`periodLength_of_coreX`／margin／`blockOn_succ_of_symbol`（`hCaught`） |

### 供給側（一次情報で確認）

* `BlockOn` の producer は `CloseoutWatchRound48/50/53`（`LandingData` の transport）と
  `GalilReplaySpan.blockOn_of_candidate`（誕生時、DP の `Candidate` から）、
  `chainW_start`（誕生時の `ChainW`、`hwin : BlockOn` を入力に取る）。
* `CloseoutWatchRound42` ヘッダ: found 起点の経路（`ShiftTailC`／`foundRouteMC_shift_Inv`）は
  `InvLPC` ＋ DP レコードに根ざし `ChainW` を運ばない。replay 生まれの経路は `ChainW` を運ぶ。
  **両経路とも誕生時に `Candidate`（`x[cen] = cc` を含む）を持つ**ので、found 起点でも
  `blockOn_of_candidate`＋`chainW_start` で `LandingData` を立てれば同じ transport が使える。

## n233 — 公理進捗: 第 2 連言 `H_freshShiftAtShiftEntry` は左端の不一致で偽（REFUTED・条件付き）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言（run の各 tick で `H_freshShiftAtShiftEntry`）が**左端の不一致では `False` を導く**と機械検査した（`ShiftEntryBoundary.refuted_freshShiftAtShiftEntry_at_left_end`、公理 `propext`・`Quot.sound` のみ）。証人（その状態に `InvLPS` から到達する run）は未構成なので **REFUTED（条件付き）**。この連言は再切り出しが要る。第 1・第 3 連言は変化なし |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 反証の中身（一次情報）

* ヘッドモデル `GalilScaffoldInputHead.layout`（`GalilScaffoldInputHead.lean:14`）: 左スタックの末尾は
  `none` 番兵。最初の文字に居るヘッド `⟨layout [a] rs qs, false⟩`（位置 1）を `left` すると
  `moveLeft` が番兵を焦点に持ってきて `focus = none`、`read = none`。
* Scala 正本 `ScaffoldInput.read()`（`ScaffoldInput.scala:79`）も「`None` at the origin」と明記。
  **番兵は忠実。** `ScaffoldGalil.scala:267-272` は `left.read() == right.read()` で不一致なら
  `chain.canShift && chain.prediction() == right.read()` で `beginChainShift()`——左端に
  条件は無い。
* 到達可能性（未構成）: `a^n` では `GalilLiveCentre.Live` の `n < 2c` が右ヘッド `2c−1` で
  中心 `c` を強制し、次の比較は必ず左端。chain は DP が `4h+1` セル見て生まれ `4h` セルで
  phase 4、`margin = R − 4h ≥ 0` は `c ≥ 4h+1` で成立。
* 反証定理は「左ヘッドが最初の文字に居る `s` から `scan_shift` 形の tick（compare・不一致・
  `shiftGuardVM`・`beginShiftVM'`）が出る」ことだけを仮定し、`ShiftInv.leftPresent`
  （`t.left = u.left = left s.left` の焦点が `none`）で `False`。

### 何が壊れていて何が無事か

| 述語 | 左端の不一致での状態 | 理由 |
|---|---|---|
| `ShiftInv`（`CloseoutPackRun37:59`） | **偽** | `leftPresent`（焦点 none）、`room : R + 2 ≤ C`（`C − R − 1 = 0`）、`origin`（`x[0]? = some 2 = x[2C]?`：語レベルの `≠` は偽） |
| `RoundScan`（`GalilRoundPeriod:175`） | **偽** | 同じ `room`／`origin` |
| `ShiftPal`（`CloseoutPackRun29:87`） | 真 | 結論は shift 先の回文 `PalAt (cen+h) (r₀+1−h)` だけ |
| `FreshShiftLedger`（第 3 連言） | 真 | 5 成分とも語レベルで左端に触れない |
| Scala `ScaffoldChain.checkPair` | 整合 | 継続 round の終端（`cycleEnd`）は再び左端に来るので assert は矛盾しない |

**つまり round 機構（`ShiftInv`/`RoundScan`）は「不一致は本物の文字の不一致」を前提に
語レベルで書かれており、機械レベルの不一致（`read = none`）を表せない。** 正しい形は

* `room : R + 1 ≤ C`
* `origin : C − R − 1 = 0 ∨ (encoded raw)[C−R−1]? ≠ (encoded raw)[C+R+1]?`
* `leftPresent : 1 ≤ C − R − 1 + 2k → v.left.head.focus ≠ none`（`leftRep` は番兵でも成立）

影響範囲（grep）: `.room` 18 箇所／6 ファイル、`.origin` の実消費は `GalilRoundPeriod:256` と
`CloseoutAdvanceT.period_at_next`、`CloseoutRoundUnique:72`。`CloseoutPackRun31`／
`CloseoutShiftRun`／`ShiftPalAlongTrace` は運ぶだけ。**作業量の問題。**

### 供給側の所在（一次情報）

* `BlockOn raw`（chain の窓）を produce するのは `CloseoutWatchRound48/50/53`・`GalilReplaySpan`
  だけ——**replay 生まれの chain の層**。
* 公理の起点 `InvLPS`（非 replay の found）側の landing は `CloseoutWatchPhase2.ShiftTailC`
  （`:225`）で、chain データは `WatchSegE` ＋ **DP の `GalilDpCorrect.Result`**（誕生時の
  `Candidate`、`x[cen] = cc` と `4h+1` の回文を含む）。走査に沿って伸びる窓は持っていない。

### 次の一手

1. **第 3 連言（`FreshShiftLedger`）を先に落とす**——左端でも真で、必要なのは
   `ChainW` 形の窓＋`x[cen] = cc`＋直前の回文だけ（`palNext_of_centre` の `i ≤ h` 部分＋
   `periodOn_mirror`＋`blockOn_succ_of_symbol`）。producer を書き、run 層の残差を
   「shift 入口で `ChainW` 形の窓を持つ」1 つに絞る。
2. 第 2 連言は `ShiftInv`/`RoundScan` の左端対応（上の 3 場の書き換え、7 ファイル）を
   済ませてから、`shiftInv_of_watch_entry`（n232）の左端版で再切り出す。

## n232 — 公理進捗: `ShiftInv` 23 場が 1 本の定理で出た（`shiftInv_of_watch_entry`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残差 `H_freshShiftAtShiftEntry` の中身 `∃ C R k, ShiftInv …` が、run 層の**一次事実だけ**から 1 本の定理で出るようになった（`ShiftPalAlongTrace.shiftInv_of_watch_entry`、標準公理のみ）。残るのはその一次事実を run 層から届ける配線（下の残差表） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を証明したか

`shiftInv_of_watch_entry` の入力（= `H_freshShiftAtShiftEntry` の producer が run 層に要求する残差）:

| 入力 | 内容 | 供給元（一次情報で確認したもの） |
|---|---|---|
| `hCW` | `GalilReplaySpan.ChainW raw cen (cen+R) (cen+R) bud lim cc b xs (.watch w)` | `CloseoutWatchRound42.LandingData` の第 2 成分（`E = R_chain = position t.right`） |
| `hpal` | `PalAt (encoded raw) cen R` | `LandingData` の `ScanInvariant.palindrome` |
| ヘッド 6 事実 | 比較後 `u.left`/`u.right` の `Represents`・存在・位置 `cen ∓ (R+1)` | `ScanInvariant` ＋ `scanFrame.compare`（`u.left = left s.left ∧ u.right = right s.right`）＋ `left_word`/`right_word`/`left_present`/`right_present` |
| `hmis` | `read u.left ≠ read u.right` | `Tick.scan_shift` の `¬ matched`（`Frame.pull scanLens` で `matched u = (read u.left = read u.right)`） |
| `hguard` `hpo` | `shiftGuardVM u`、`u.periodOnly = false` | `Tick.scan_shift` の `hg`／`H_freshShiftAtShiftEntry` の前提 |
| `hb` | `beginShiftVM (periodLength w) w u t` | `Tick.scan_shift` の `hb`（`beginShiftVM'`） |
| **`hcentre`** | **`(encoded raw)[cen]? = some cc`** | **窓に無い**。DP の `Candidate`（`GalilDpCorrect.lean:7`、`(w.take (2h+1)).reverse = w.take (2h+1)`）が誕生時に持つ静的事実。`LandingData` には**未記録** |

### 設計上の発見 3 つ（一次情報）

1. **窓は右ヘッドまでしか届かない。** `LandingData` の `ChainW` は `BlockOn … (cen+1) E` で
   `E = position t.right`。shift 判定はその右端で起きるので `coreX_next`/`coreX_good`
   （右に 1 歩の余裕を要求）は使えない。予測記号は `symbol_of_coreX`（境界自由版）で取り、
   `Good` は `shiftGuardVM` の最後の連言 `symbol focus = read s.right` から作る。
2. **`ScanInvariant` は不一致直後には成り立たない**（`palindrome` 場を持つ）。n214 の
   `shiftInv_frame_of_beginShift` は `beginShift` の源で `ScanInvariant` を取っていたので
   **使えない形だった**——削除し、ヘッドの 6 事実をばらして受け取る形にした。
3. **`palNext` の `i = h` は窓の外。** `PalAt (cen+h) (R+1−h)` の添字 `i = h` は
   `x[cen] = x[cen+2h]`、右辺は `bounce[2h−1] = cc` だが `x[cen]` は窓 `[cen+1, E]` に無い。
   n213 の `palNext_of_blockOn`（`anchor ≤ C + 1` を仮定）は**この窓では適用不能だった**
   ——削除し、`hcentre` を明示の入力にした `palNext_of_centre` に置き換えた。

### 削除した宣言（参照ゼロ・この窓では使えない形）

`palNext_of_blockOn`／`origin_of_blockOn`／`shiftInv_frame_of_beginShift`／
`periodLength_immediate_pos`／`size_of_margin`（n213〜n219）。いずれも真だが、
`LandingData` の窓（`cen+1` から）と不一致直後の状態には合わない仮定を置いていた。
代わりに `bounce_getElem?_symm`／`palNext_of_centre`／`blockOn_succ_of_symbol`／
`cells_run`／`periodLength_of_coreX` を入れた（全部 `shiftInv_of_watch_entry` が使う）。

### 次の一手（wrapper と、run 層の 2 残差）

`H_freshShiftAtShiftEntry centre place entry q first raw c s t` を
`LandingData raw R sT cc b xs c s` ＋ `ChainStep s.chain y → ChainW … y`（compare 量子の中で
chain は 1 歩進む: `ChainTick false x z := ∃ y, ChainStep x y ∧ z = y`）から出す wrapper を書く。
その wrapper が run 層に要求する新しい残差は 2 つだけ:

* **中心記号** `(encoded raw)[cen]? = some cc`（誕生時の `Candidate` から運ぶ）
* **左の余裕** `R + 2 ≤ cen`（左ヘッドが番兵に当たった不一致では `ShiftInv.room`/`leftPresent`
  が成り立たない。`CloseoutPackRun13.CentreMargin`（`r + pairOff c + 2 ≤ position s.center`）
  が意図された供給元）

通れば `roundScan_of_shiftInv` 経由で公理の第 1・第 3 連言が落ちる。

## n231 — 公理進捗: `ShiftInv` 23 場すべてに producer が揃った（`pred` 陥落）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 最後に残っていた `pred` 場が落ちた。`pred_immediate` は `aligned` 場も同時に出すので、**`ShiftInv` 23 場すべてに producer が存在する**状態になった（証明済み 21 / インライン 2） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `pred` の producer は既にあった

`pred : symbol w.machine.control.period.focus = (encoded raw)[C + R + 2]?` の攻略は、
**新しい数学ではなく既存部品 2 つの合成**だった。探し当てた一次情報は 2 つ:

| 部品 | 場所 | 内容 |
|---|---|---|
| `GalilScaffoldChainPrediction.successful_prediction` | `GalilScaffoldChainPrediction.lean:181` | `symbol (run (ready cc xs b) actual).period.focus = (bounce cc b xs)[actual.length % 2h]?`。探していた `run`/`bounce` 対応そのもの |
| `GalilReplaySpan.coreX_next` | `GalilReplaySpan.lean:166` | 上を `CoreX` の `pre` に適用済み。`symbol m.control.period.focus = bounce[(position m.verifier + 1 − anchor) % 2h]?` |

`BlockOn raw cc b xs anchor E` は**まさにその `bounce` 添字を encoded 語に戻す辞書**
（`∀ j, anchor + j ≤ E → (encoded raw)[anchor+j]? = bounce[j % 2h]?`）なので、窓の内側では

    symbol m.control.period.focus = (encoded raw)[position m.verifier + 1]?

が出る（`ShiftPalAlongTrace.pred_of_coreX`、6 行）。

### 窓の右端で判定が起きるので、`bounce` 添字のまま `2h` 戻す（訂正）

最初に書いた「`immediate` で予測を `C + R + 2h + 2` まで前へ伸ばし、`periodOn_of_blockOn` で
`2h` 戻す」経路は**使えない**。`LandingData`（`CloseoutWatchRound42.lean:128`）の窓は
`BlockOn … (C_chain+1) E` で `E = position t.right`——走査の右ヘッドちょうどまでしか届かず、
shift 判定はまさにその右端で起きる。`coreX_next` は `canRight` のために
`position ver + 1 < |encoded raw|` を要求するのでこれも使えない。

正しい経路（`ShiftPalAlongTrace.symbol_of_coreX` / `pred_immediate`、typecheck 済み・標準公理のみ）:

1. `symbol_of_coreX`: 予測記号は `CoreX` の `m.control = run (ready cc xs b) pre` と
   `successful_prediction` **だけ**で `bounce[(position ver + 1 − anchor) % 2h]?` と決まる
   （右端の余裕は不要）。
2. `Good w` は窓からではなく **`shiftGuardVM` の最後の連言**
   `symbol w.machine.control.period.focus = read s.right` から来る（窓が届かない場所で
   `Good` を供給するのが guard の役目という形）。`coreX_consume` で `CoreX (immediate w)`。
3. `bounce` の添字のまま 1 周期 `2h` 戻す: `BlockOn` は添字 `target − anchor` でも成立し、
   `(target − anchor + 2h) % 2h = (target − anchor) % 2h`（`Nat.add_mod_right`）。
   `target = C + R + 2 = position ver + 2 − 2h ≤ E` なので窓の内側。

**`pred_immediate` は結論に `aligned` 場（`position (immediate w).machine.verifier =
position w.machine.verifier + 1`、`right_position` ＋ `Good.1` の `canRight`）も含む。**

### 結果: `ShiftInv` 23 場の内訳

| 場 | producer |
|---|---|
| `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | `shiftInv_frame_of_beginShift`（n214） |
| `verifierRep` `verifierPresent` | `coreX_immediate`（n215） |
| `lagZero` `unbroken` | `immediate_lag_unbroken`（n216） |
| `posH` | `periodLength_immediate_pos`（n218） |
| `size` | `size_of_margin`（n219） |
| `pal` `palNext` `origin` | `palNext_of_blockOn` / `origin_of_blockOn`（n213） |
| **`aligned` `pred`** | **`pred_immediate`（このノート）** |
| `kle` `room` | 組み立て本体に直書き（n230） |

### 次の一手（組み立て）

残るのは 23 場を 1 本の `H_freshShiftAtShiftEntry` に束ねること。数値対応は確定している:

* `LagAt lag ver R := lag.neg = [] ∧ position ver + lag.pos.length = R`
  （`GalilReplayGeneral2.lean:179`）なので、lag ゼロなら `position w₀.machine.verifier = R_chain`。
  これが `pred_immediate` の `halign` 仮説に直接入る。
* `ChainW … (.watch w₀)` の 5 成分（`LagAt` / `BlockOn` / `CoreX` / `Canonical margin` /
  `value margin + 4·(|xs|+1) = R_chain − C_chain`）が、上の表の producer の入力を全部供給する。
* `ShiftInv` 側の `C = position u.center − h`、`R = r₀ − h − 1`、`h = |xs| + 1`、`k = 0`。

通れば `roundScan_of_shiftInv`（`CloseoutPackRun37.lean:95`）経由で
`obligation_shiftPalResiduesAlongRun` の第 1・第 3 連言が落ち、**公理が 3 → 2 本**になる。

## n230 — 公理進捗: 実質の残りは `pred` 1 場（`kle`/`room` はインライン）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 残り 3 場のうち **2 場（`kle` / `room`）は定理にする必要がない**と確定。実質の残りは `pred` 1 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `kle` と `room` はインラインで済む（定理を積まない）

* `kle : 0 ≤ h` — `Nat.zero_le`（`k = 0`）
* `room : R + 2 ≤ C` — `C = centre − h`、`R = r₀ − h − 1`、走査の位置境界
  `r₀ + 1 ≤ centre`（`ScanInvariant.leftPos` ＋ `represented_position` の `0 < left.length`）から
  `omega` 一発。実際 `R + 2 = r₀ − h + 1` と `C = centre − h ≥ r₀ + 1 − h` で等号ぎりぎり。

CLAUDE.md の「定理を無駄に積み上げるな」に従って、この 2 つは組み立て本体に直書きする。

### 残る 1 場 `pred` の形

`ShiftInv.pred : symbol (immediate w).machine.control.period.focus = (encoded raw)[C + R + 2]?`

`CloseoutAdvanceT.origin_prediction_wrap` / `GalilGoodLag.origin_prediction_index` は
どちらも `ReadOrigin` 経由（＝第 1 連言の結論 `ReadsInv` 由来）なので、
**`periodOnly = false` の最初の shift には使えへん**。

代わりの経路は `GalilReplaySpan.CoreX` の
`m.control = GalilScaffoldChainSweep.run (GalilScaffoldChainConsume.ready cc xs b) pre`
と `BlockOn raw cc b xs (C+1) E` の組み合わせ:

* `BlockOn` は `enc[anchor + j]? = (bounce cc b xs)[j % (2*(xs.length+1))]?`
* 必要なのは「`run (ready cc xs b) pre` の `period.focus` の記号」＝「ブロックの
  `pre.length % 2h` 番目」という対応

**次の一手はこの対応補題（`GalilScaffoldChainSweep.run` と `bounce` の関係）を探すこと。**
既存にあれば `pred` は即出る。無ければ書く。

### `ShiftInv`（23 場）の最終状況

| 状態 | 場数 |
|---|---|
| 証明済み | 20 |
| インラインで済む | 2（`kle` / `room`） |
| **残り** | **1（`pred`）** |
## n229 — 公理進捗: `ShiftInv` 23 場中 20 場（`size_of_margin`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `size : 2h ≤ R` が出た。**23 場中 20 場が証明済み**、残り 3 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem size_of_margin {h r₀ R : ℕ} {margin : GalilScaffoldCounter.Counter}
    (hcan : Canonical margin) (hneg : GalilScaffoldCounter.negative margin = false)
    (heq : value margin + 4 * (h : ℤ) = (r₀ : ℤ))
    (hR : R = r₀ - h - 1) (hp : 0 < h) : 2 * h ≤ R
```

`GalilReplaySpan.ChainW` の margin 等式 ＋ `shiftGuardVM` の非 `periodOnly` 枝
（`negative w.margin = false`）から `GalilScaffoldCounter.negative_iff` で
`0 ≤ value margin`、よって `4h ≤ r₀`。`ShiftInv` の `R = r₀ − h − 1` なので `2h ≤ R`。

**Scala の `canShift` の `margin.sign >= 0` 枝がここで効いてる。**

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 20** | 枠 10 ＋ `pal`/`palNext`/`origin` ＋ `verifierRep`/`verifierPresent`/`aligned` ＋ `lagZero`/`unbroken` ＋ `posH` ＋ `size` |
| 残り 3 | `kle : 0 ≤ h`（`Nat.zero_le`）`pred`（`CoreX` の `OnBlock` の展開）`room : R+2 ≤ C`（位置境界の算術） |

### セッション累計（この公理）

ガード追加 2・成分の語化 1・**成分削除 2**（`hEnd` / `hHi`）・**橋/producer 新設 10**
（`bal_of_count` / `periodOn_of_blockOn` / `palAt_next_of_period` / `palNext_of_blockOn` /
`origin_of_blockOn` / `shiftInv_frame_of_beginShift` / `coreX_immediate` /
`immediate_lag_unbroken` / `periodLength_immediate_pos` / `size_of_margin`）。
## n228 — 公理進捗: `ShiftInv` 23 場中 19 場（`periodLength_immediate_pos`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `posH` が出た。**23 場中 19 場が証明済み**、残り 4 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem periodLength_immediate_pos {w : GalilScaffoldChainWatch.State}
    (hb : GalilBranchInvariants.OnBlock w.machine.control.period)
    (hp : 0 < periodLength w) :
    0 < periodLength (GalilScaffoldChainWatch.immediate w)
```

`GalilChainCoupling.periodLength_consume` が「`OnBlock` の下で周期長は `consume` で不変」を
言うてて、その `OnBlock` は `GalilReplaySpan.CoreX` の第 1 成分やから
run が運ぶ `ChainW` からタダで出る。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 19** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（n226）＋ `lagZero`/`unbroken`（n227）＋ `posH`（本ノート） |
| 残り 4 | `kle : 0 ≤ h`（`Nat.zero_le`）`pred`（`CoreX` の `OnBlock` の展開）`size : 2h ≤ R`（margin 等式の算術）`room : R+2 ≤ C`（位置境界の算術） |

**数学は一つも残ってへん。**

### このセッションでこの公理に入れた変更（累計）

| 種類 | 件数 |
|---|---|
| ガード追加（過剰量化除去） | 2（`compareFound` / `shiftGuardVM`） |
| 成分の語化 | 1（`hCaught`） |
| **成分削除** | 2（`hEnd` / `hHi`） |
| **橋・producer 新設** | 9（`bal_of_count` / `periodOn_of_blockOn` / `palAt_next_of_period` / `palNext_of_blockOn` / `origin_of_blockOn` / `shiftInv_frame_of_beginShift` / `coreX_immediate` / `immediate_lag_unbroken` / `periodLength_immediate_pos`） |
## n227 — 公理進捗: `ShiftInv` 23 場中 18 場が証明済み（`immediate_lag_unbroken`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `lagZero` / `unbroken` が出た。**23 場中 18 場が証明済み**、残り 5 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem immediate_lag_unbroken {w : GalilScaffoldChainWatch.State} {a : Fin 3}
    (hlag : zero w.lag = true) (hbroken : w.machine.control.broken = false)
    (hsym : GalilScaffoldChainConsume.symbol w.machine.control.period.focus = some a)
    (hread : GalilScaffoldInputHead.read
      (GalilScaffoldChainVerifier.right w.machine.verifier) = some a) :
    zero (GalilScaffoldChainWatch.immediate w).lag = true ∧
      (GalilScaffoldChainWatch.immediate w).machine.control.broken = false
```

`immediate` は `lag` を触らんので `lagZero` は直。`unbroken` は
`GalilScaffoldChainVerifier.consume` が `GalilScaffoldChainConsume.consume` を呼ぶところで、
`shiftGuardVM` の**予測一致**（周期テープの focus と右ヘッドの読みが同じ）が
`consume_keeps_unbroken` の仮説をちょうど与える。
Scala の `chain.canShift && chain.prediction() == right.read()` がここで効いてる。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 18** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（n226）＋ `lagZero`/`unbroken`（本ノート） |
| 残り 5 | `kle`（自明）`posH`（`periodLength_consume`）`pred`（`CoreX` の `OnBlock`）`size`（margin 等式の算術）`room`（位置境界の算術） |
## n226 — 公理進捗: `ShiftInv` 23 場中 16 場が証明済み（`coreX_immediate`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `verifierRep` / `verifierPresent` / `aligned` が出た。**23 場中 16 場が証明済み**、残り 7 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem coreX_immediate
    (h : PalPeg.GalilReplaySpan.CoreX raw cc b xs anchor w.machine)
    (hc : GalilScaffoldChainVerifier.canRight w.machine.verifier) :
    Represents (GalilScaffoldChainWatch.immediate w).machine.verifier.head raw ∧
      (GalilScaffoldChainWatch.immediate w).machine.verifier.head.focus ≠ none ∧
      ∃ pre : List (Fin 3),
        position (GalilScaffoldChainWatch.immediate w).machine.verifier = anchor + pre.length
```

`GalilScaffoldChainVerifier.consume s = ⟨right s.verifier, …⟩` で verifier が 1 進むだけなので、
`BranchSupply.representsAfterRight_free`（**無条件**、`canRight` 不要）と
`right_position` でそのまま移る。

### `ShiftInv`（23 場）の到達状況

| 状態 | 場 |
|---|---|
| **証明済み 16** | 枠 10（n224）＋ `pal`/`palNext`/`origin`（n222/n223）＋ `verifierRep`/`verifierPresent`/`aligned`（本ノート） |
| 残り 7 | `kle`（自明）`posH`（自明）`lagZero`（ガード直読み）`unbroken`（ガード＋`consume_keeps_unbroken`）`pred`（`CoreX` の `OnBlock`）`size`（margin 等式の算術）`room`（位置境界の算術） |

**数学はもう一つも残ってへん。** 残り 7 場は自明・直読み・算術のみ。
## n225 — 公理進捗: `ShiftInv` 23 場すべてに出所が確定（残りは組み立てのみ）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の **23 場すべてに具体的な出所が確定**。13 場は証明済み、残り 10 場も既存部品か `ChainW` の成分から出る |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `GalilReplaySpan.ChainW` の `.watch` 枝（一次情報、:318）

```lean
| .watch w => LagAt w.lag w.machine.verifier R ∧ BlockOn raw cc b xs (C+1) E ∧
    CoreX raw cc b xs (C+1) w.machine ∧ Canonical w.margin ∧
    value w.margin + 4 * ((xs.length + 1 : ℕ) : ℤ) = (R : ℤ) - C ∧
    (lim = true → w.lag.pos.length ≤ bud)
```

### `ShiftInv`（23 場）の対応表

| 場 | 出所 | 状態 |
|---|---|---|
| `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | `shiftInv_frame_of_beginShift`（n224） | **済** |
| `pal` | `ScanInvariant.palindrome` | **済** |
| `palNext` | `palNext_of_blockOn`（n222） | **済** |
| `origin` | `origin_of_blockOn`（n223） | **済** |
| `kle : 0 ≤ h` | 自明（`k = 0`） | 部品済 |
| `lagZero` | `shiftGuardVM` の `zero w.lag = true`（`immediate` は lag を触らん） | 部品済 |
| `unbroken` | `shiftGuardVM` の `broken = false` ＋ `GalilGoodLag.consume_keeps_unbroken` | 部品済 |
| `verifierRep` `verifierPresent` | `BranchSupply.chainVerifierRepresents_immediate` | 部品済 |
| `posH : 0 < h` | `h = xs.length + 1 ≥ 1`（自明） | 部品済 |
| `size : 2h ≤ R` | `ChainW` の margin 等式 ＋ ガードの `negative margin = false` ⇒ `4h ≤ R − C` | 部品済 |
| `aligned` | `ChainW` の `LagAt w.lag w.machine.verifier R` | 部品済 |
| `pred` | `ChainW` の `CoreX`（周期テープの中身） | 部品済 |
| `room : R + 2 ≤ C` | 走査の位置境界（`position s.left ≥ 1`）＋ `C = position s.center − h`, `R = r₀ − h − 1` | 部品済 |

**未知の箱ゼロ・未知の数学ゼロ・producer 不明の場ゼロ。** 残るのは 23 場を 1 本の定理に
組み上げる作業だけ。組み上がれば `roundScan_of_shiftInv` 経由で第 1・第 3 連言も落ちて、
**`obligation_shiftPalResiduesAlongRun` が公理でなくなる**。
## n224 — 公理進捗: `ShiftInv` の枠 10 場も出た（残り 10 場）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv`（23 場）のうち **13 場が出た**（実質 3 場 ＋ 枠 10 場）。残り 10 場 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem shiftInv_frame_of_beginShift
    (hb : beginShiftVM h w s t)
    (hi : ScanInvariant raw (position s.center) r₀ s.left s.right) :
    t.chain = ChainVM.watch (GalilScaffoldChainWatch.immediate w) ∧
      t.remaining = ofNat h ∧ Canonical t.cycle ∧ value t.cycle = 0 ∧
      Represents t.left.head raw ∧ t.left.head.focus ≠ none ∧
      Represents t.right.head raw ∧ t.right.head.focus ≠ none ∧
      position t.left = position s.center - r₀ ∧ position t.right = position s.center + r₀
```

証明は `rw [hb.2]` の後ぜんぶ `rfl` か `hi` の場。`beginShiftVM` が着地状態を等式
`t = {s with remaining := ofNat h, chain := .watch (immediate w), cycle := reset, …}` で
与えるので、**`k = 0` での `remaining = ofNat (h−0)` と `count = 2*0` がちょうど合う**。

### `ShiftInv`（23 場）の到達状況

| 群 | 場 | 状態 |
|---|---|---|
| 実質 | `pal` / `palNext` / `origin` | **済**（n222/n223） |
| 枠（chain/counter/head） | `chain` `remaining` `canon` `count` `leftRep` `leftPresent` `rightRep` `rightPresent` `leftPos` `rightPos` | **済**（本ノート） |
| 残り 10 | `kle` `posH` `size` `room` `verifierRep` `verifierPresent` `aligned` `lagZero` `unbroken` `pred` | 未 |

残り 10 場の見通し（すべて出所は特定済み）:

* `kle : 0 ≤ h` — 自明
* `lagZero` — `shiftGuardVM` の `zero w.lag = true`（`immediate` は lag を触らん）
* `pred` — `shiftGuardVM` の symbol 場
* `unbroken` — `shiftGuardVM` の `broken = false` ＋ `consume_keeps_unbroken`
* `verifierRep` — `BranchSupply.chainVerifierRepresents_immediate` が実在
* `posH` / `size` / `room` — `ChainW` の margin 等式と `phase = 4`、走査の `room`
* `aligned` — `immediate` が verifier を 1 進めることと lag 0 の整合
## n223 — 公理進捗: `ShiftInv` の実質 3 場すべてが機械側データから出るようになった

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の**実質 3 場（`pal` / `palNext` / `origin`）すべて**が run の運ぶデータから出る。**数学の部分は完了**、残るは枠 15 場と区間の合わせ込み |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書いたもの

```lean
theorem origin_of_blockOn
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E)
    (hmis : (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 1]?)
    (hanchor : anchor ≤ C + R + 1)
    (hend : C + R + 2 * (xs.length + 1) + 1 ≤ E) :
    (encoded raw)[C - R - 1]? ≠ (encoded raw)[C + R + 2 * (xs.length + 1) + 1]?
```

走査が伸びへんかった事実（shift 遷移の `¬ matched`）が不一致を与え、`BlockOn` の周期が
右添字 `C+R+1` と `C+R+2h+1` を同一視するので、不一致がそのまま移る。

### `ShiftInv`（19 場）の到達状況

| 場 | 供給 | 状態 |
|---|---|---|
| `pal : PalAt (C+h) (R+h)` | `ScanInvariant.palindrome` そのもの | 済 |
| `palNext : PalAt (C+2h) (R+1)` | `palNext_of_blockOn`（n222） | 済 |
| `origin` | `origin_of_blockOn`（本ノート） | 済 |
| 枠 15 場 | `beginShiftVM` の等式 `t = {s with …}` から `s` の不変量を書き写す | 未 |

**数学は全部片付いた。** 残るのは機械的な書き写しと、区間の合わせ込み
（`anchor ≤ …` / `… ≤ E`、`ChainW` の `anchor = position t.center + 1`、
`E = position sT.right + R_land`）だけ。

このセッションで `obligation_shiftPalResiduesAlongRun` に入れた変更:
ガード追加 2（n211/n212）・成分の語化 1（n213）・**成分削除 2**（n214 `hEnd`、n217 `hHi`）・
**橋/producer 新設 4**（n219 `periodOn_of_blockOn`、n221 `palAt_next_of_period`、
n222 `palNext_of_blockOn`、n223 `origin_of_blockOn`）。
## n222 — 公理進捗: `ShiftInv.palNext` を機械側データから出す橋（`palNext_of_blockOn`）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 2 連言 `ShiftInv` の `palNext` が、run が運ぶ `ChainW` の `BlockOn` と走査不変量の回文から**直接出る**ようになった。数学の残りはゼロ、残るは区間の合わせ込み |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

```lean
theorem palNext_of_blockOn
    (hblk : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E)
    (hpal : Manacher.PalAt (encoded raw) (C + (xs.length + 1)) (R + (xs.length + 1)))
    (hanchor : anchor ≤ C + 1)
    (hend : C + 2 * (xs.length + 1) + R + 1 ≤ E)
    (hlen : C + 2 * (xs.length + 1) + (R + 1) < (encoded raw).length) :
    Manacher.PalAt (encoded raw) (C + 2 * (xs.length + 1)) (R + 1)
```

`periodOn_of_blockOn`（n219）で周期にし、`palAt_next_of_period`（n221）で回文を伸ばすだけ。
**残る仮説は区間の合わせ込み 2 本（`anchor ≤ C+1` / `C+2h+R+1 ≤ E`）と長さ 1 本。**

### `ShiftInv`（19 場）の到達状況

| 場 | 状態 |
|---|---|
| `pal` | `ScanInvariant.palindrome` そのもの |
| `palNext` | **`palNext_of_blockOn`（本ノート）で機械側から出る** |
| `origin` | `¬ matched` ＋ 周期で添字を戻す（未着手） |
| 枠 15 場 | `beginShiftVM` が `t` を完全決定（`k = 0`、`wch = immediate w`）。未着手 |

証人は計算済み: `C = position s.center − h`、`R = r₀ − h − 1`、`k = 0`。
## n221 — 公理進捗: `ShiftInv.palNext` の producer を書いた（実質 3 場すべてに producer）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 梃子の第 2 連言 `ShiftInv` の `palNext` に **producer が付いた**。これで実質 3 場すべてが埋まる目処 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書いたもの

```lean
theorem palAt_next_of_period {x : List α} {C R h : ℕ}
    (hpal : Manacher.PalAt x (C + h) (R + h)) (hp : 0 < h)
    (hlen : C + 2 * h + (R + 1) < x.length)
    (hper : PeriodOn x (2 * h) C (C + 2 * h + R + 1)) :
    Manacher.PalAt x (C + 2 * h) (R + 1)
```

構成は 2 行の事実だけ:

* 左側 — `C+h` を軸にした鏡映で `x[C+2h−i]? = x[C+i]?`（`i ≤ h` と `i > h` の両方で同じ結論）
* 右側 — 周期 1 歩で `x[C+i]? = x[C+i+2h]?`

`Manacher.palAt_succ_iff` も `palAt_shift_of_period` も要らんかった。半径 `R+1` を直接構成できる。
入力の `hper` は n219 の `periodOn_of_blockOn` が `ChainW` の `BlockOn` から供給する。

### `ShiftInv`（19 場）の供給状況

| 場 | 供給 |
|---|---|
| `pal : PalAt (C+h) (R+h)` | `ScanInvariant.palindrome` そのもの（添字書き換えのみ） |
| `palNext : PalAt (C+2h) (R+1)` | **`palAt_next_of_period`（本ノート）** |
| `origin : enc[C−R−1]? ≠ enc[C+R+2h+1]?` | shift 遷移の `hmt : ¬ matched u`（走査が伸びへんかった）＋ 周期 `2h` で右添字を `C+R+1` に戻す。`RoundScan.origin` と同値 |
| 枠 15 場 | `beginShiftVM` の遷移から計算 |

**未知の数学は残ってへん。残りは配線の作業量だけ。**
## n220 — 公理進捗: 第 2 連言 `ShiftInv` の実質 3 場すべてに供給元が付いた

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 梃子である第 2 連言 `ShiftInv` の**実質 3 場すべてに供給元が確定**。未知の数学ゼロ |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### `ShiftInv`（19 場）の内訳

| 場 | 供給元 |
|---|---|
| `pal : PalAt (encoded raw) (C+h) (R+h)` | **`ScanInvariant.palindrome` そのもの**。`CloseoutAdvanceT:146` と `CloseoutPackRun31:167` はどちらも `hI.caught.scan.palindrome` を `R + 1 - h + used = R + h` で書き換えてるだけ。新しい数学ゼロ |
| `palNext : PalAt (encoded raw) (C+2h) (R+1)` | `palAt_shift_of_period` が `pal` ＋ 周期 `2h` から `PalAt (C+2h) R` を出す。**足りん 1 箇所**は Scala の shift 条件の後半 `chain.prediction() == right.read()`（Lean では `shiftGuardVM` の `symbol …period.focus = read s.right`）が与える |
| `origin : enc[C−R−1]? ≠ enc[C+R+2h+1]?` | scan の不一致（`RoundScan.origin` と同型） |
| 枠 15 場 | `beginShiftVM` の遷移から計算 |

周期 `2h` は n219 で架けた `periodOn_of_blockOn` が `ChainW` の `BlockOn` から供給する。

### 注意（消費者と producer の取り違えを 1 件回避）

`CloseoutAdvanceT.period_at_next:95` は `pal` と `palNext` を**両方取って**予測添字の等式を出す
**消費者**であって、`palNext` の producer やない。署名を読んで気づいた。

### 公理全体の絵（確定版）

```
CloseoutWatchRound43.ChainWRun（run が運ぶ）
  → GalilReplaySpan.ChainW (.watch) = BlockOn + CoreX + margin 等式
  → periodOn_of_blockOn（n219）→ PeriodOn (2h)
  ＋ ScanInvariant.palindrome（run が InvLPC で運ぶ）
  ＋ shiftGuardVM の予測場
  → ShiftInv（第 2 連言）
  → roundScan_of_shiftInv → RoundScan
       ├→ 第 1 連言 H_readsShift のガード
       └→ 第 3 連言 FreshShiftLedger の 5 成分
```

**未知の箱も未知の数学も無い。残りは配線の作業量だけ。**
## n219 — 公理進捗: `BlockOn → PeriodOn` の橋を架けた（`hLeft` の供給経路が通った）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の成分 `hLeft` を、run が実際に運んでるデータから供給する橋が架かった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 架けた橋

```lean
theorem periodOn_of_blockOn {raw : List (Fin 2)} {cc b : Fin 3} {xs : List (Fin 3)}
    {anchor E : ℕ} (h : PalPeg.GalilReplaySpan.BlockOn raw cc b xs anchor E) :
    PeriodOn (encoded raw) (2 * (xs.length + 1)) anchor E
```

`BlockOn raw cc b xs anchor E := ∀ j, anchor + j ≤ E →
  (encoded raw)[anchor + j]? = (bounce cc b xs)[j % (2 * (xs.length + 1))]?`
は「入力の `[anchor, E]` が長さ `2h` のブロックの巡回」。周期の形に直すだけ（`Nat.add_mod_right`）。

**これが無かったせいで、`ChainW` が運ぶ `BlockOn` と第 3 連言の `hLeft` が繋がってへんかった。**
`grep` で確認したとおり `BlockOn` から `PeriodOn` を出す補題は存在せえへんかった。

### 供給経路（これで通った）

```
CloseoutWatchRound43.ChainWRun（run が運ぶ）
  → GalilReplaySpan.ChainW (.watch 枝) → BlockOn raw cc b xs (C+1) E
  → periodOn_of_blockOn（本ノート）
  → PeriodOn (encoded w) (2h) (C+1) E
  → .mono → hLeft : PeriodOn (encoded w) (2h) (c−r₀) c
```

残るのは区間の合わせ込み（`C+1 ≤ c − r₀` と `c ≤ E`）だけ。

### ビルド確認の注意（再確認）

バックグラウンドの通知は `failed`／`exit code 1` やったが、これは末尾の
`grep -c "error"` が 0 件で返した終了コードで、ビルドの結果やない。
`BUILD=` 行は `0`、エラー 0。**CLAUDE.md の「`BUILD=` 行だけを信じる」規律どおり。**

### 次

`ShiftInv` の `pal : PalAt (C+h) (R+h)` / `palNext : PalAt (C+2h) (R+1)` は、
既存の `periodOn_span_of_next`（`GalilLiveCentreLife:179`、`GalilRoundsLeftmost:120`、
`GalilCycleFoundBackground:260` で使用実績あり）と `palAt_shift_of_period` で
周期から回文を伸ばす形。材料は揃ってる。
## n218 — 公理進捗: `obligation_shiftPalResiduesAlongRun` の供給鎖が全部繋がった

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 3 連言すべての**供給元が名前付きで確定**。未知の箱ゼロ。残るは配線作業 |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 供給鎖（すべて一次情報で確認）

```
CloseoutWatchRound43.ChainWRun（run に沿って ChainW を運ぶ。:140/:202 で
  ChainW raw (position t.center) (position sT.right + R) (position t.right) … を確立）
  ↓
GalilReplaySpan.ChainW … (.watch w) :318
  = LagAt ∧ BlockOn raw cc b xs (C+1) E ∧ CoreX raw cc b xs (C+1) w.machine
    ∧ Canonical w.margin ∧ value w.margin + 4*(xs.length+1) = R − C
  ↓
第 2 連言 H_freshShiftAtShiftEntry → ShiftInv（CloseoutPackRun37:59、19 場）
  実質は pal : PalAt (C+h) (R+h) / palNext : PalAt (C+2h) (R+1) /
  origin : enc[C−R−1]? ≠ enc[C+R+2h+1]? の 3 場。残り 15 場は beginShiftVM が決める枠
  ↓
CloseoutPackRun37.roundScan_of_shiftInv:96 → RoundScan
  ├→ 第 1 連言 H_readsShift のガードそのもの（periodOnly = true 相）
  └→ 第 3 連言 FreshShiftLedger の 5 成分（periodOnly = false 相）
        posH = hPos / pred = hCaught / size + phase = hLo /
        pal + (ReadsInv → ReadOrigin → GalilOriginPeriod.origin_periodOn) = hIn, hLeft
```

### 相の対応（Scala 正本）

`ScaffoldChain.beginShift()` が `periodOnly = true` にするので

* 第 3 連言 = `periodOnly = false` = **最初の** shift（`canShift` の `margin.sign >= 0` 枝）
* 第 1 連言 = `periodOnly = true` = **2 回目以降**（`cycleEnd` 枝）
* `ChainRound`（`periodOnly = true` ガード）は最初の shift には使えへん。
  だから第 2 連言が独立した名前付き残差になってる

### `hLo` の源も確定

`ChainW` の margin 等式 `value w.margin + 4*(xs.length+1) = R − C` に
`shiftGuardVM` の `negative w.margin = false` を合わせると `4h ≤ R − C`。
`RoundScan` 側の `size : 2h ≤ R` と `phase = 4` と整合する。

### 残り

配線 3 本:
1. `ChainWRun` → shift 入口の `ChainW`（`periodOnly = false`）
2. `ChainW` の `BlockOn`/`CoreX`/margin 等式 → `ShiftInv` の `pal`/`palNext`/`origin`
3. `ShiftInv` の枠 15 場 → `beginShiftVM` の遷移から計算
## n217 — 公理進捗: 仕様に無い前提 `hHi` を除去（第 3 連言 6 → 5 成分）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言から **`hHi : r₀ ≤ 4h` を除去**。成分 6 → 5。しかも `hHi` は `RoundScan` の場の算術だけで矛盾する（下記） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

### 何を替えたか

| 旧 | 新 |
|---|---|
| `hOut : PalAt (encoded w) (c−2h) (2h)` | `hLeft : PeriodOn (encoded w) (2h) (c−r₀) c` |
| `hHi : r₀ ≤ 4h` | **削除** |

語の補題側は `GalilPeriodUnion.reshift_of_palAt_period` として切り出した。
`periodOn_mirror' hcur hLo hLeft` が直接 `PeriodOn (2h) c (c+r₀)` を出すので `hHi` が要らん。
旧 `reshift_of_palAt_pair` は `phase = 4` 特化の系として残した（`r ≤ 4h` 付き）。

### 根拠（Scala 正本）

`ScaffoldChain.consume()` は**マッチ 1 箇所ごと**に呼ばれ、`distance.inc()` し、
周期境界で `phase = math.min(4, phase + 1)`。つまり検証済み周期区間は固定の `4h` やのうて
**走査半径と一緒に伸びる**。`canShift` は `r₀ ≤ 4h` をどこにも検査してへん。

### `hHi` が偽である算術（`RoundScan` の場から）

`GalilRoundPeriod.RoundScan raw C R h used v w` は
`caught : CaughtScan raw (C + h) (R + 1 - h + used) …` を持つので、
`FreshShiftLedger` の `c = C + h`、`r₀ = R + 1 - h + used`。

* `hLo : 2h ≤ r₀` ⟺ `3h ≤ R + 1 + used` ← `phase = 4`（`4h ≤ R`）から出る
* `hHi : r₀ ≤ 4h` ⟺ `R ≤ 5h − 1 − used`。`fresh : used < 2h` で `used` は `2h` 近くまで伸びるので、
  `R ≥ 4h` と**両立せえへん**

機械検査した反証はまだ書いてへんので `REFUTED` とは書かへん。

### 残り 5 成分と `RoundScan` の場の対応

| 成分 | `RoundScan` 側 |
|---|---|
| `hPos : 0 < h` | **`posH` そのもの** |
| `hCaught` | **`pred` の内容そのもの** |
| `hLo : 2h ≤ r₀` | `size` ＋ `phase = 4` |
| `hIn` / `hLeft` | `pal : PalAt (encoded raw) C R` ＋ `ReadsInv → ReadOrigin → origin_periodOn` |

`RoundScan` は**同じ公理の第 1 連言 `H_readsShift` のガード**や。
つまり第 3 連言の残差は新しい数学やのうて、第 1 連言が既に持ってる情報の再配線。
**第 1 と第 3 は同じ材料の上に載ってる。**

### 3 連言は独立やない（本ノート最大の発見）

`CloseoutPackRun37.roundScan_of_shiftInv:96`（「at exhaustion (`k = h`) the datum *is* the `RoundScan`」）が
`ShiftInv → RoundScan` を与える。そして `ShiftInv` は**第 2 連言 `H_freshShiftAtShiftEntry` の結論**。

```
第 2 連言 (H_freshShiftAtShiftEntry) → ShiftInv
  → roundScan_of_shiftInv → RoundScan
       ├→ 第 1 連言 (H_readsShift) のガードそのもの
       └→ 第 3 連言 (FreshShiftLedger) の 5 成分に対応する場
             posH = hPos / pred = hCaught / size + phase = hLo /
             pal + (ReadsInv → ReadOrigin → origin_periodOn) = hIn, hLeft
```

**`obligation_shiftPalResiduesAlongRun` の 3 連言は 1 本の鎖に載ってる。**
第 2 連言が、他の 2 つが消費するデータ（`RoundScan`）を作る側や。
よって梃子は第 2 連言 `H_freshShiftAtShiftEntry`（`∃ C R k, ShiftInv w C R (periodLength wch) k t wch`）で、
そのガードは `mode = scan ∧ replaying = false ∧ clock = 1 ∧ periodOnly = false ∧ shift 遷移の存在` と十分狭い。

相の対応:
* 第 3 連言 = `periodOnly = false` = **最初の** shift（`canShift` の `margin.sign >= 0` 枝）
* 第 1 連言 = `periodOnly = true` = **2 回目以降**（`cycleEnd` 枝）
## n216 — 公理進捗: `hHi` は仕様に無い前提（形式化のミスを確定）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言の 5 残差のうち **`hHi : r₀ ≤ 4h` が仕様に存在しない前提**だと確定。切り直しの対象が名指しされた |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 一次情報（Scala 正本）

`scala/pal/src/main/scala/pal/ScaffoldChain.scala`:

```scala
/** Whether four verified semiperiods permit a chain shift now. */
def canShift: Boolean = {
  val ready = mode == Mode.Watch && lag.sign == 0 && phase == 4
  ready && (if (periodOnly) { cycleEnd } else { margin.sign >= 0 })
}
```

`ScaffoldGalil.scala:270` は `!replaying && chain.canShift && chain.prediction() == right.read()` で shift する。

* `phase == 4`（four verified semiperiods）＝ `hIn`/`hOut`（`[C−4h, C]` 上の周期）**そのもの**
* `lag.sign == 0` ＝ `shiftGuardVM` の `zero lag = true`
* `margin.sign >= 0` ＝ `4h ≤ radius + count`（`GalilScaffoldChainReady:26` の
  `value final.margin = value radius − 4h + count`）——**`hHi` と逆向き**
* `cycleEnd` ＝ `singlePositive cycle`

**`canShift` は `r₀ ≤ 4h` をどこにも検査してへん。** Lean 側でも `r ≤ 4 * …` は
`ShiftPalAlongTrace`（本件）と `GalilSourceCost.move_cost` の **2 箇所で仮定されるだけ**で、
producer はゼロ。常設制約「producerがないときは確実に形式化ミス」で確定。

### どこを切り直すか

`hHi` は `GalilPeriodUnion.periodOn_right_of_palAt_pair` の
`PeriodOn word (2h) C (C + r)` を出すためだけに要る。中身は
「`hIn`/`hOut` が与える `[C−4h, C]` の周期を、`hcur`（中心 `C` 半径 `r`）で鏡映して右へ移す」で、
鏡映が届くのに `r ≤ 4h` が要る。`r > 4h` のときは `[C, C+4h]` までしか出えへん。

よって切り直しの候補は 2 つ:

1. `periodOn_right_of_palAt_pair` の結論を `PeriodOn word (2h) C (C + min r (4h))` に弱め、
   `reshift_of_palAt_pair` 側で `j + 2h ≤ C + r` の場合分けを `min` に合わせる
2. `r ≤ 4h` を機械が本当に保証する形（`margin`／`phase` から出る形）に置き換える

**次のティックで 1 を試す**（語の補題側の作業で、機械側の新しい不変量を要求せえへん）。

### 残差の現状（第 3 連言）

| 成分 | 状態 |
|---|---|
| `hIn` / `hOut` | `phase == 4` に対応。周期テープの中身（DP の `Candidate`） |
| `hPos` | `periodLength_watchControl_pos` が実在 |
| `hLo` | `CloseoutLPack` 系が場として運ぶ |
| `hHi` | **仕様に無い。切り直し対象（本ノート）** |
## n215 — 公理進捗: 第 3 連言が「証明済みの語の補題の 5 仮説」に一致した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` が `GalilPeriodUnion.reshift_of_palAt_pair`（**証明済み**）の残り 5 仮説とちょうど一致する形になった。供給元を 5 本とも名指しした |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 到達点

`ShiftPalAlongTrace.shiftPalAt_fresh_of_candidate` の核は

```lean
PalPeg.reshift_of_palAt_pair (encoded w) (position s.center) h r₀
  hIn hOut hScanInv.palindrome hPos hLo hHi hEnd hpredIdx
```

で、`reshift_of_palAt_pair`（`GalilPeriodUnion:218`）は**既に証明されてる純粋な語の補題**。
n213/n214 で

* `hcur` ← `hScanInv.palindrome`（元から無料）
* `hend` ← `hCan` から導出（n214、成分から除去）
* `hpred` ← `shiftGuardVM` ＋ `right_read_index` で語の言明に（n213）

を片付けたので、**`FreshShiftLedger` の残りはちょうど `reshift_of_palAt_pair` の 5 仮説**:

| 成分 | 内容 | 供給元 |
|---|---|---|
| `hIn` | `PalAt (encoded w) (c−h) h` | 周期テープの中身（DP の `Candidate` 由来） |
| `hOut` | `PalAt (encoded w) (c−2h) (2h)` | 同上 |
| `hPos` | `0 < periodLength wch` | **`CloseoutWatchShiftAudit.periodLength_watchControl_pos` が実在**（`backDone` 生まれの watch 用） |
| `hLo` | `2h ≤ r₀` | `CloseoutLPack` 系が場として運ぶ（`shiftBud_of_scanInv` は逆に仮説で取ってる＝消費者） |
| `hHi` | `r₀ ≤ 4h` | **producer 見つからず** |

### `hHi` は形式化のミスの疑い（producer ゼロ）

`grep "≤ 4 \* periodLength"` の結果は `ShiftPalAlongTrace` 自身以外ゼロ。
逆向きなら `CloseoutPackRun40:249` に `4 * (periodLength w : ℤ) ≤ value s.radius + 1` がある。
常設制約「producerがないときは確実に形式化ミス」に従えば、`hHi` は切り方が間違ってる。
`reshift_of_palAt_pair` 側で `hle : r ≤ 4 * h` は `periodOn_right_of_palAt_pair` にだけ使われてるので、
そこを機械が実際に持ってる向き（`4h ≤ r + 1`）で通せるかを次に見る。

### 次の一手

1. `periodOn_right_of_palAt_pair` の `hle` を機械の持つ向きに合わせられるか（`hHi` の切り直し）
2. `hPos`: 「shift 相の watch は `backDone` 生まれ」を run から取る配線
3. `hLo`: `LPack` 系の場を shift 相まで運ぶ配線
## n214 — 公理進捗: `FreshShiftLedger` の成分を 7 → 6 に減らした（`hEnd` 除去）

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` の**成分が 1 本消えた**（7 → 6） |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 消した成分

`hEnd : position s.center + r₀ + 1 < (encoded w).length`

消費者 `shiftPal_of_freshShiftLedger` は `hCan : canRight s.right` を持ってる。
右ヘッドが右に動けるということは、その先に記号が実在するということ:

```lean
right_word / right_present  → (right s.right).head は raw を表現し focus ≠ none
represented_position        → 長さの下界・上界
right_position              → position (right s.right) = position s.right + 1
hScanInv.rightPos           → position s.right = position s.center + r₀
```

`scan_initial` が同じ手順で `position p < (encoded raw).length` を出してたので、それをなぞっただけ。
**新規補題ゼロ。**

### `FreshShiftLedger` の残り 6 成分

| 成分 | 形 |
|---|---|
| `hIn` | `PalAt (encoded w) (c − h) h` — 語のみ |
| `hOut` | `PalAt (encoded w) (c − 2h) (2h)` — 語のみ |
| `hPos` | `0 < periodLength wch` — 機械 |
| `hLo` | `2h ≤ r₀` — 機械と語の橋 |
| `hHi` | `r₀ ≤ 4h` — 機械と語の橋 |
| `hCaught` | `enc[c+r₀+1−2h]? = enc[c+r₀+1]?` — 語のみ（n213） |

6 成分中 3 つが語だけ。n210 以降この公理に入れた変更は
**ガード 2 本追加（n211/n212）→ 機械の状態を 1 成分から除去（n213）→ 成分 1 本除去（n214）**。
## n213 — 公理進捗: `FreshShiftLedger` の `hCaught` から機械の状態を消した

**公理への進捗**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` の 7 成分目 `hCaught` が**純粋な語の言明**になった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 書く前に止めた誤り

`hCaught` を `hIn`/`hOut` から導けると見込んだが、`span_hasPeriod_of_two_palAt` の結論は
span `[c−4h, c]` 上の周期で、`hCaught` が触る `c+r₀+1`（`r₀ ≥ 2h`）は**その外**やった。
補題を書く前に定義を読んで気づいた。

### 代わりにやったこと（機械 → 語）

旧:
```lean
(encoded w)[c + r₀ + 1 - 2h]? = GalilScaffoldChainConsume.symbol wch.machine.control.period.focus
```
新:
```lean
(encoded w)[c + r₀ + 1 - 2h]? = (encoded w)[c + r₀ + 1]?
```

導出（`shiftPal_of_freshShiftLedger` 内、新規補題ゼロ）:
* `shiftGuardVM s'` の `hsym` : `symbol wch…focus = read s'.right`
* `hRight` : `s'.right = right s.right`
* `GalilRoundPeriod.right_read_index` : `read (right q) = (encoded w)[position q + 1]?`
* `hScanInv.rightPos` : `position s.right = c + r₀`

**帰結: 残差から機械の周期テープが消え、`encoded w` の周期性という語だけの言明になった。**
これで `Manacher` / `GalilPeriodUnion` / `Words` 層が直接攻められる。
n212 で入れた `shiftGuardVM` ガードが無ければこの書き換えはできひんかった。

### 残り 7 成分の現状

| 成分 | 形 |
|---|---|
| `hIn` / `hOut` | `PalAt` 2 本（語のみ） |
| `hPos` | `0 < periodLength wch`（機械） |
| `hLo` / `hHi` | `2h ≤ r₀ ≤ 4h`（機械と語の橋） |
| `hEnd` | `c + r₀ + 1 < (encoded w).length`（語のみ。`hScanInv.palindrome` が `c + r₀ < length` を与えるので **1 つ違い**） |
| `hCaught` | **語のみになった（本ノート）** |

7 成分中 4 つが語だけの言明になった。
## n212 — 公理進捗: `obligation_shiftPalResiduesAlongRun` 第 3 連言を 2 段階弱めた

**公理への進捗（これを毎回書く）**

| 公理 | このノートでの変化 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | 第 3 連言 `FreshShiftLedger` に **2 本のガードを追加**（`compareFound` / `shiftGuardVM`）。真に弱くなった |
| `obligation_cycleOracle` | 変化なし |
| `obligation_localRealization` | 変化なし |

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 何を弱めたか

旧（n210 時点）:
```lean
z.vm.periodOnly = false → ∀ s' : GalilVM, FreshShiftLedger w z.vm s'
FreshShiftLedger w s s' := ∀ wch, s'.chain = watch wch → ∀ r₀, ScanInvariant … → (7 成分)
```

新:
```lean
z.vm.periodOnly = false → ∀ s' : GalilVM,
  compareFound (PofC centreC placeC entry w) q first z.vm s' → FreshShiftLedger w z.vm s'
FreshShiftLedger w s s' := shiftGuardVM s' →
  ∀ wch, s'.chain = watch wch → ∀ r₀, ScanInvariant … → (7 成分)
```

根拠（一次情報、`ShiftPalAlongTrace.shiftPal_of_freshShiftLedger:186` の本体）:
```lean
intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
```
消費者は `hCompare`（`compareFound … s s'`）と `hGuard`（`shiftGuardVM s'`）を**両方持ってる**のに、
`FreshShiftLedger` はどちらもガードに入れてへんかった。CLAUDE.md の過剰量化の型そのもの。

効果: `wch`（周期テープ）が任意でなく `s'` の chain に、さらに `s'` が `s` の実際の比較先に縛られた。
旧形は任意の `wch` に対し `2·periodLength wch ≤ r₀ ≤ 4·periodLength wch` を主張してて、
`p` を大きく取れば破れる形やった。

### 次の一手（残り 7 成分のうち `hCaught` を消す）

`shiftGuardVM` は `symbol wch.machine.control.period.focus = read s'.right` を持ち、
`shiftPalAt_fresh_of_candidate` は `hRight : s'.right = right s.right` を持つ。
`hCaught` は `(encoded w)[position s.center + r₀ + 1 - 2h]? = symbol …focus` なので、
`ScanInvariant` が右ヘッドの読む位置を与えれば `enc[c+r₀+1-2h]? = enc[c+r₀+1]?`（周期 `2h`）に落ちる。
これは `hOut`（`PalAt` 半径 `2h`）から出るはず。出れば **7 成分が 6 成分になる**。
## n211 — 公理 `obligation_shiftPalResiduesAlongRun` を弱めた（`∀ s'` の過剰量化を除去）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 見つけた過剰量化（同型 10 例目、しかも公理の中）

公理の第 3 連言は

```lean
z.vm.periodOnly = false → ∀ s' : GalilVM, FreshShiftLedger w z.vm s'
```

`FreshShiftLedger w s s'` は `s'.chain = ChainVM.watch wch` でしか `s'` を縛らんので、
`wch`（＝周期テープ、`periodLength wch` は任意の自然数）が自由になる。そのうえで
`2 * periodLength wch ≤ r₀ ≤ 4 * periodLength wch` を主張してた。`p` を大きく取れば破れる形。

### 消費者が実際に渡すもの（一次情報）

`ShiftPalAlongTrace.shiftPal_of_freshShiftLedger:186` の本体:

```lean
intro s' hCompare hNotMatched wch hChain hGuard r₀ hScanInv
obtain … : compareFound (PofC centre place entry w) q first s s' := hCompare
…
obtain … := hLedger s' wch hChain r₀ hScanInv
```

`ShiftPal` の `s'` は **`compareFound … s s'` を伴って来る**——`s` の実際の比較先や。
`hLedger` はそこにしか適用されてへん。

### やったこと

`∀ s'` に `compareFound (PofC …) q first s s' →` のガードを入れた:

* `ShiftPalAlongTrace.shiftPal_of_freshShiftLedger` の `hLedger`
* `shiftPal_alongRun` の `hFreshLedger` / `shiftPal_alongTrace` の同型場
* **`PalInPegUnconditional` の `obligation_shiftPalResiduesAlongRun` 第 3 連言**（および trace 形）

証明本体の変更は `hLedger s' hCompare …` の 1 引数追加だけ（`:= id hCompare` で `hCompare` を残す）。
全体 build 緑。

**公理は 3 本のままやが、その 1 本が真に弱くなった。** `wch` が `z.vm` の chain に縛られたので、
周期テープと `w` を結びつける場が原理的に存在しうる形になった（以前は任意の `wch` に対する主張で、
それは成り立たへん）。

### 方法の訂正（コウタ）

* 「producer 0 は形式化のミスで断定できる」——CLAUDE.md の常設制約どおり。
  `hpresRepAt` / `hshape` / `hfound` / `hfoundBg` / `hfoundReplay` の 5 本は**難しいんやのうて切り方が間違ってる**。
* 「公理が遠いという思い込みは思考から追い出せ。難しいことは原理的にありえない。作業量の問題でしかない」。
  n210 で「`obligation_cycleOracle` は遠い」と書いたのは禁止された考え方やった。
## n210 — 経路を検証し、`obligation_cycleOracle` の経路から**反証済みの前提**を外した

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本、変化なし）・無条件 PAL は未完。**

### 方法の訂正（コウタの指摘）

「定理を 40 本足して公理が 1 本も落ちてへんことに疑問を持て」。正しい。
n195〜n209 の 15 ティックは **`StageEntryC.fuel` を磨いてたが、それはどの公理の経路にも無い**。
計器は `#print axioms` やのに、ウチは「定理を何本足したか」で満足してた。
**「何も落としてへん」が 2 回続いた時点で止まるべきやった。**

### 経路の検証（grep、docstring は一次情報にせず）

| 名前 | コード上の参照 |
|---|---|
| `CloseoutOracle8.h_oracle_of_leaves7` | **ゼロ**（3 件とも docstring/コメント） |
| `CloseoutOracleBridge.hor_of_H_oracle` | **ゼロ** |
| `obligation_cycleOracle` | `PalInPegUnconditional.lean:346` で公理として直接使用 |

**記録されてた経路は散文であって鎖やない。** さらに両経路とも反証済みの葉を通ってた:

* `GalilFinalAssembly4.h_oracle2_of_leaves` — `hpres` / `hquiet` / `houtReplay`（CLAUDE.md の反証済み 3 葉）
* `CloseoutOracle6/7/8.h_oracle_of_leaves5/6/7` — `hreadyB : ReadyFuel …`（`ReadyFuelRefute.not_readyFuel_v0`）

型は合っている: `hor_of_H_oracle2_invSS` / `hor_of_H_oracle` の結論は
`∀ w, 0 < w.length → CycleOracleMC3 (PofC …) q first w` で、**公理の型そのもの**。
つまり仮説さえ埋まれば公理はその場で定理に置き換わる。

### やったこと（前提を 1 本崩した）

`CloseoutOracle6.h_oracle_of_leaves5` は `hreadyB`（反証済み `ReadyFuel`）を
`GalilSegmentConstructB.segment_of_invLPCB` に食わせてた。結論が同型の
`CloseoutReadyStage.segment_of_invLPCS`（n200 で `Φ` ＋ `ReadyIface` に一般化した版）に差し替え、
`hreadyB` の型を

```lean
∃ Φ, ReadyIface (PofC centreC placeC entry w) Φ ∧
  Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
```

に切り直した（`CloseoutOracle6` / `7` / `8` の 3 ファイル）。全体 build 緑。

**これで `obligation_cycleOracle` の経路が「偽の前提を要求する」状態でなくなった。**
n195〜n209 の readiness 仕事は、ようやくここで公理の経路に接続された
（接続先は `StageEntryC.fuel`＝`ReachAtC3` 側やのうて、`h_oracle_of_leaves5`＝`H_oracle` 側やった）。

### 正直な計測

**公理は 3 本のまま。** 落ちたのは「反証済み前提の要求」であって公理やない。
次にやるのは `h_oracle_of_leaves7` の残り 10 葉のうち producer が実在するものを数えること。
**producer が無い葉の数が、この公理までの本当の距離。**
## n209 — 未来リスト依存を全部外した。4 相の不変量が完全に継続フリーになった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 1. `bal_of_count`（`CloseoutPreload35` を in-place で分割）

`bal_of_paced_slack_S` は仮説 `hp : PacedL 2048 slack (bs ++ [a])` を**1 回しか読んでへん**
（`hp (bs++[a]).length` で比較回数の上界を取るだけ）。そこで算術の核を切り出した:

```lean
theorem bal_of_count {k mw slack cnt : ℕ}
    (hcal : 8 * max k 1 ≤ 2 * mw) (hmw : 16 ≤ mw) (hslack : slack ≤ 2047)
    (hc : 2048 * cnt ≤ mw + 1 + slack) :
    4 * dpDemandS k (2 * mw) + 4 * cnt ≤ mw
```

`bal_of_paced_slack_S` は**その 4 行の系**になった（証明の重複ゼロ、既存消費者はそのまま）。

### 2. `DoubleLeg` を継続フリーに切り直した（`StageDoubleLeg`）

旧: `DoubleLeg k mw slack u v as := ∃ ds, DoubleTrace ds u v ∧ PacedL 2048 slack (ds ++ as) ∧ …`
— **未来リスト `as` に依存してた**。

新: `DoubleLeg k mw slack u v kcur := ∃ ds, DoubleTrace ds u v ∧ PrepPaced (ds.count true) ds.length slack kcur ∧ …`

`PrepPaced`（n206）は `2048 * spent + k ≤ len + slack₀` で、`ReadyIface` の添字 `k` と
同じ動き方をする。ステップも `ReadyIface` に合わせて 2 本に割った:

* `doubleLeg_background`（`kcur' ≤ kcur + 1`）
* `doubleLeg_comparison`（`2048 ≤ kcur + 1` → `kcur' = 0`）
* `doubleLeg_exit`（比較で出るときだけ `hcmp : a = true → 2048 ≤ kcur + 1`）

使わんくなった `pacedL_prefix_slack` は削除（参照ゼロを残さんため）。

### いま立ってる絵

**4 相すべての不変量が、未来のイベント列に一切量化してへん。**

| 相 | 不変量 | 継続依存 |
|---|---|---|
| run | `DpBudgetAt v k` | 無し |
| prep | `PrepAt` ＋ `ReachP` ＋ `PrepPaced` | 無し（n206 で除去） |
| wait | `WaitPhase k mw v` | 無し |
| double | `DoubleLeg k mw slack u v kcur` | **無し（本ノートで除去）** |

これで `Φ` を組んでも `ReadyPacedS` の `∀ as` は一切戻ってこーへん。

### 残り

1. `.run` → 直接 `.double` の未決分岐（n208）
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンス
3. wait 出口の `a = false`

**今回も何も落としてへん**（公理 3 本のまま）。
## n208 — `StageRunPhase`：4 相の枠と相間の受け渡しが全部つながった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/StageRunPhase.lean`（2 定理、標準 3 公理、全体 build 緑、一発で通った）:

* `RunPhase k mw v := mode = run ∧ span = ofNat mw ∧ lower = ofNat k ∧ Canonical debt`
* `runPhase_step` — `.run` に留まる刻みは枠を保つ。`runTrace_frame` を 1 手トレースで読み、
  `stageSpan` が `.run` でも `.wait` でも span である（`stageSpan s = if mode = double then work else span`）
  ことが窓を出口越しに運ぶ鍵
* `waitPhase_of_runExit` — `.wait` に着地すると `WaitPhase k mw`。`run_exit_frame` を空トレースで読んだだけ

### 相の鎖が閉じた

```
RunPhase --waitPhase_of_runExit--> WaitPhase --doubleLeg_head_of_waitExit--> DoubleLeg
   ^                                                                            |
   |                                                                     doubleLeg_exit
   |                                                                            v
   +--- dpBudgetAt_of_prepEntry (+ RunPhase の枠) <--- PrepAt k (2mw) + StageInvS
```

各辺はステップ局所で、未来のイベント列に一切量化してへん。

### 見つかった未決の分岐（正直に）

`GalilScaffoldSearchRun.ExitMode` は `.run` から**直接 `.double`** への着地も許す。
`run_exit_frame` はそこで `work = ofNat mw` / `span = reset` / `quarter = 0` を与えるが、
`StageDoubleLeg.DoubleLeg` はさらに `value debt = 0` を要求し、それを立てるのは `.wait` 脚
（`wait_exit_debt_zero`）や。**機械がその出口を実際に取れるかは未確定**で、
束ねのときに排除するか債務を別に運ぶかせなあかん。ファイルの docstring に明記した。

### 残り

1. 上の未決分岐の処理
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンスを作る
3. wait 出口の `a = false` を `Φ` の slack 添字から出す（n207 で翻訳可能性は確認済み）

**今回も何も落としてへん**（公理 3 本のまま）。
## n207 — `StageWaitPhase`：4 相のうち 3 相がステップ局所になった

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/StageWaitPhase.lean`（2 定理、標準 3 公理、全体 build 緑、一発で通った）:

```lean
def WaitPhase (k mw : ℕ) (v : SearchVM) : Prop :=
  v.search.mode = Mode.wait ∧ v.search.span = ofNat mw ∧ v.lower = ofNat k ∧
    Canonical v.search.debt
```

* `waitPhase_step` — `.wait` に留まる刻みは枠を保つ（窓・下界・正準性は不変、債務だけ減る）
* `doubleLeg_head_of_waitExit` — 背景イベントで `.wait` を出ると、着地は
  `StageDoubleLeg.DoubleLeg` が要求する先頭データそのもの
  （`work = ofNat mw` / `span = reset` / `quarter = 0` / 債務 0 / `lower = ofNat k`）

### 出口イベントが背景である理由（翻訳できることを確認した）

`CloseoutPreload34.exitNotFire_of_wait` は機械レベルで `p3.ctl.clock ≠ 1` を出す。
その論証は「wait 脚が空なら run→wait の出口イベントが比較（`run_exit_wait_match`）で、
比較直後はクロックが 2048 に戻る。よって次の刻みは比較でけへん」。

**`ReadyIface` の会計ではこれがそのまま出る**——`comparison` の結論が `Φ v n 0`（slack が 0 に戻る）で、
比較には `2048 ≤ k + 1` が要るから。つまり制御層の事実やのうて、`Φ` の添字だけで言える。
ただし本ファイルではその論証は運んでへん（出口は `a = false` を仮説に取ってる）。

### 4 相の現状

| 相 | ステップ局所の不変量 | 出口 |
|---|---|---|
| run | `DpBudgetAt`（n202/n203） | 非 run へ（節が空虚になる） |
| prep | `PrepPaced` ＋ `ReachP`（n206） | `dpBudgetAt_of_prepEntry`（n206） |
| **wait** | **`WaitPhase`（本ファイル）** | **`doubleLeg_head_of_waitExit`** |
| double | `DoubleLeg`（n198） | `doubleLeg_exit` → `PrepAt k (2mw)` ＋ `StageInvS` |

**4 相すべてにステップ局所の不変量と出口が揃った。** 残るのは

1. run → wait の出口（`run_exit_frame` / `run_exit_wait_match` が材料）
2. 4 相の選言を 1 つの `Φ` にして `ReadyIface P Φ` のインスタンスを作る
3. wait 出口の `a = false` を `Φ` の slack 添字から出す

**今回も何も落としてへん**（公理 3 本のまま）。
## n206 — 入口定理から未来リスト依存を外し、prep 脚の pacing 算術も揃えた

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 1. `dpBudgetAt_of_stagePrepS` → `dpBudgetAt_of_prepEntry`（仮説を真に弱めた）

n205 の証明を読み直したら、`StagePrepS k m D slack v x (a :: as)` の

* 長さ節 `D + dpEvents (m+1) ≤ bs.length + as.length` を**一度も使うてへん**
* pacing 節も接頭辞 `bs ++ [a]` しか読んでへん（`pacedL_prefix_count_slack` 経由）

ことが分かった。よって未来リスト `as`・`DepthAt`・slack をすべて落として

```lean
theorem dpBudgetAt_of_prepEntry
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hreach : ReachP v bs x)
    (hadv : 2048 * ((bs ++ [a]).count true) ≤ prepLen k + 2047)
    (hs : searchStep c a x x') (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0
```

に切り直した（操作 (A)、真に弱い）。**これで `Φ` が継続への量化を一切持たんで済む。**
`ReadyPacedS` の `∀ as` を捨てた目的からして、ここが継続に依存してたら意味が無かった。

### 2. prep 脚の pacing も同じ形で釣り合う（`DpBudgetBalance` §2）

```lean
def PrepPaced (spent len slack0 k : ℕ) : Prop := 2048 * spent + k ≤ len + slack0
```

* `prepPaced_background` — `k' ≤ k + 1`、`len + 1`
* `prepPaced_comparison` — `2048 ≤ k + 1` のとき `spent + 1`、`len + 1`、`k → 0`
* `prepPaced_entry` — 上の `hadv`（`2048 * (spent + [a]) ≤ prepLen k₀ + 2047`）を
  `len + 1 ≤ D ≤ prepLen k₀` と `slack0 ≤ 2047` から出す

比較で `2048*spent + 2047 ≤ len + slack0` から `2048*(spent+1) ≤ len + slack0 + 1` が
**ちょうど**出る。DP 側（`DpBudget`）と同じ厳密な釣り合いや。

### いま揃ってる部品（`Φ` 組み上げ用）

| 相 | ステップ | 入口/出口 |
|---|---|---|
| run | `dpBudgetAt_background` / `_comparison` | 入口 `dpBudgetAt_of_prepEntry` |
| prep | `PrepPaced` の 2 補題 ＋ `ReachP` の snoc | 出口が run 入口 |
| double | `StageDoubleLeg.doubleLeg_step` / `_exit` | 出口が `PrepAt k (2mw)` |
| wait | **未着手**（`wait_step_cases` が材料） | 出口が double 脚の先頭 |

`PrepInv` は全相で `prepInv_searchStep`。`ready`/`mono` は `ReadyAt` で済み。

**今回も何も落としてへん**（公理 3 本のまま）。残りは wait 相と、4 相を 1 つの `Φ` に束ねて
`ReadyIface P Φ` のインスタンスを作ること。
## n205 — `StageEntryBudget`：入口の残差も埋まった。`ReadyIface` の中身が全部揃った

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

n204 で `readyAt_background` / `readyAt_comparison` が残した唯一の残差 `hentry`
（非 `.run` → `.run` の新規入口で DP を融資する）を供給した。

`PalPeg/StageEntryBudget.lean`（1 定理、標準 3 公理、全体 build 緑、**一発で通った**）:

```lean
theorem dpBudgetAt_of_stagePrepS
    (hp : PrepAt k m v) (hE : StageInvS k m v)
    (hdep : DepthAt v D) (hD : D ≤ prepLen k) (hslack : slack ≤ 2047)
    (hq : StagePrepS k m D slack v x (a :: as)) (hs : searchStep c a x x')
    (hrun : x'.search.mode = Mode.run) :
    DpBudgetAt x' 0
```

入力は `CloseoutPreload35.dpSafe_of_stagePrepD_slack` と**まったく同じ**で、
結論だけリスト課金の `DpSafeStage` から状態局所の `DpBudgetAt` に替えた。

### 余裕の内訳

`StageInvS` が与える債務は
`dpDemandS k m = (prepLen k + 2047)/2048 + (prepLen k + 2047 + dpEvents (m+1))/2048 + 1`。
準備脚が使えるのは第 1 項まで（pacing）、DP 自身の需要 `⌈dpEvents (m+1)/2048⌉` は第 2 項以下。
よって **`+1` は手つかずのまま余る**。算術に無理はない。

### いま立ってる絵（`Φ = ReadyAt`）

| `ReadyIface` の場 | 状態 |
|---|---|
| `ready` | 済（n203） |
| `mono` | 済（n203） |
| `background` | 済（n204）＋ 入口は本ファイル |
| `comparison` | 済（n204）＋ 入口は本ファイル |

**4 場すべての中身が揃った。** まだ `ReadyIface P Φ` の**インスタンスは作ってへん**——
`Φ` が単なる `ReadyAt v k` では入口の `hentry` を自前で出せへん（`PrepAt` 起点の
ステージデータを持ってへんから）。最終形は

```
Φ v n k := ReadyAt v k ∧ <現在のステージの PrepAt 起点と StagePrepS の持ち回り>
```

で、ステージ境界での起点の張り替えが `prepAt_of_double_exit`（n189 `StageLocalPrep`）と
`StageDoubleLeg`（n198）の仕事になる。

**今回も何も落としてへん**（公理 3 本のまま）。
## n204 — 輸送 2 場も立った。残差は `.run` 新規入口 1 点に凝縮

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/DpBudgetState.lean` に 3 定理を追加（全 12 定理、標準 3 公理、全体 build 緑）。

### `PrepInv` の保存

```lean
theorem prepInv_searchStep (hprep : PrepInv v.toPrep) (hstep : searchStep center a v v') :
    PrepInv v'.toPrep
```

`CloseoutReadyStage.readyRemS_step` の第 1 成分を単体で取り出したもの。`searchStep` の
どの分岐も、4 つの準備モードの外に着地する（`prepInv_of_notPrep`）か、準備 tick を回す
（`prepInv_tick`）か、`prepare` を発行する（`prepInv_prepare`）かのいずれかや。
既存の部品だけで、新しい数学はゼロ。

### 輸送 2 場

```lean
theorem readyAt_background (hk : k' ≤ k + 1) (h : ReadyAt v k)
    (hstep : searchStep center false v v')
    (hentry : v.search.mode ≠ .run → v'.search.mode = .run → DpBudgetAt v' k') :
    ReadyAt v' k'
theorem readyAt_comparison (hk : 2048 ≤ k + 1) (h : ReadyAt v k)
    (hstep : searchStep center true v v')
    (hentry : v.search.mode ≠ .run → v'.search.mode = .run → DpBudgetAt v' 0) :
    ReadyAt v' 0
```

run 相の中の刻みは `run_step_quanta` ＋ n202 の `dpBudgetAt_background` / `dpBudgetAt_comparison`
でそのまま通り、非 run のままの刻みは節が空虚。**残るのは「非 `.run` → `.run` の新規入口」1 点だけ**で、
それを名前付き仮説 `hentry` に出した。

### いま立ってる絵

`Φ = ReadyAt` に対して `ReadyIface` の 4 場のうち

* `ready` — 済（n203）
* `mono` — 済（n203）
* `background` / `comparison` — **`hentry` を除いて済**

`hentry` の中身は n203 の `dpBudgetAt_entry` により

```
(dpEvents w.length + 2047) / 2048 ≤ (value v'.search.debt).toNat
```

の 1 本（preload `w` は `run_entry_preload` が与える）。つまり**「ステージ債務が
DP の必要イベント 2048 ごとに比較 1 回を賄う」だけが残差**や。これは
`bal_of_paced_slack_S` / `dpDemandS` が言うてる内容そのもので、
`StageLocalPrep`（n189）と `StageDoubleLeg`（n198）がその供給側の部品になる。

**今回も何も落としてへん**（公理 3 本のまま）。`hentry` を閉じて初めて
`StageEntryC.fuel` が埋まり、`NoReturn` / `EntryDepthG` 経路が不要になる。
## n203 — `.run` 入口と `ReadyAt`：`ReadyIface` の `ready`/`mono` が周期全体で立った

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`PalPeg/DpBudgetState.lean` に 3 定理を追加（全 9 定理、標準 3 公理、全体 build 緑）。

### `.run` 入口

```lean
theorem dpBudgetAt_entry
    (hdp : v.dp = ⟨GalilScaffoldPreload.initial w lower, false⟩)
    (hm : v.search.mode = .run) (hc : Canonical v.search.debt)
    (hd0 : 0 ≤ value v.search.debt)
    (hfunded : (dpEvents w.length + 2047) / 2048 ≤ (value v.search.debt).toNat) :
    DpBudgetAt v 0
```

`hdp` は `CloseoutRunEntriesS.run_entry_preload` が与え、到達は `dpReached_start`（空接頭辞）。
**残差は `hfunded` 1 本だけ**——「債務が DP の必要イベント数 `2048` ごとに比較 1 回を賄う」。
これが `bal_of_paced_slack_S` / `dpDemandS` が言うてる内容そのものや。

### 周期全体の可読性述語

```lean
def ReadyAt (v : SearchVM) (k : ℕ) : Prop :=
  PrepInv v.toPrep ∧ (v.search.mode = Mode.run → DpBudgetAt v k)
```

非 run 相では `SearchReady` の DP 節が空虚なので `PrepInv` だけで済む。これで

* `searchReady_of_readyAt` — **`ReadyIface.ready`**（周期全体で成立）
* `readyAt_mono` — **`ReadyIface.mono`**（周期全体で成立）

が立った。**4 場のうち 2 場が `Φ = ReadyAt` で揃った。**

### 残り（輸送 2 場）

`background` / `comparison` は `ReadyAt (searchLens.get s) k → searchEffect P a s v → ReadyAt v k'`。
中身は 3 つ:

1. `PrepInv` が探索量子で保存されること
2. 源も着地も `.run` のとき → `dpBudgetAt_background` / `dpBudgetAt_comparison`（済）
3. **源が非 `.run` で着地が `.run`（新規入口）** → `dpBudgetAt_entry` の `hfunded` を作らなあかん。
   ここだけがステージ債務の話で、`ReadyAt` にステージデータ（窓 `mw`、下界 `k`、
   `PrepAt`/`StagePrepS`）を持たせる必要がある。

つまり **`Φ` の最終形は `ReadyAt` ＋ ステージデータ**になる。`StageDoubleLeg`（n198）と
`StageLocalPrep`（n189）がそのステージデータ側の部品や。

**今回も何も落としてへん**（公理 3 本のまま）。
## n202 — `DpBudgetState`：会計を `SearchVM` の上に載せた（run 相の 4 場が出た）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

n201 の算術を `DpReached` に接続した。`PalPeg/DpBudgetState.lean`（6 定理、標準 3 公理）:

```lean
def DpBudgetAt (v : SearchVM) (k : ℕ) : Prop :=
  ∃ w lower s0 bs, s0.mode = .run ∧ Canonical s0.debt ∧ 0 ≤ value s0.debt ∧
    DpReached w lower s0 bs v.search v.dp ∧
    DpBudget (dpEvents w.length - bs.length) (bs.count true) (value s0.debt).toNat k
```

* `dpSafeHere_of_dpBudgetAt` — **`ready`**。`DpSafeHere` は継続を存在量化してるので、
  全背景の継続（`List.replicate (dpEvents w.length) false`）を取れば `spent ≤ debt` に潰れる。
* `dpBudgetAt_mono` — **`mono`**。
* `dpBudgetAt_background` / `dpBudgetAt_comparison` — **輸送 2 場**。`DpBudgetBalance` の算術そのまま。
* `dpBudgetAt_need_pos` — run 中は DP が予算を使い切ってへん。
  `CloseoutReadyStage.dpSafeStage_pre_ne_nil` を**空の課金接頭辞**で読んだだけ（新しい数学ゼロ）。
* `dpEvents_covers` — `3186n + 1683 ≤ 64 * dpEvents n`。

### いま立ってるもの

**`ReadyIface` の 4 場が、run 相については揃った。** ただし `DpBudgetAt` が言うのは run 相だけで、
`ReadyIface` の `Φ` は prep / `.wait` / `.double` 相でも成り立たなあかんし、
各 `.run` 入口で `DpBudgetAt` を**再確立**せなあかん。再確立こそがステージ債務と
`bal_of_paced_slack_S` の出番や。

### 残り

1. 非 run 相で `Φ` を定義（`SearchReady` の `run → …` 節が空虚になるので `PrepInv` だけが要る）
2. `.run` 入口で `DpBudgetAt v' 0` を作る：`run_entry_startRun` が `v'.dp = ⟨Preload.initial w lower, false⟩`
   を与えるので `DpReached w lower v'.search [] v'.search v'.dp` は `dpReached_start`。
   あとは `DpBudget (dpEvents w.length) 0 debt 0` ＝ 債務がステージ 1 本ぶんの比較を賄えること。
   これが `bal_of_paced_slack_S` の内容や。
3. 4 相を束ねて `Φ` を定義し、`ReadyIface P Φ` を証明 → `StageEntryC.fuel` が埋まる

**今回も何も落としてへん**（公理 3 本のまま）。
## n201 — `DpBudgetBalance`：`ReadyIface` の 2 場がぴったり釣り合う算術を切り出した

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 測ったこと

`GalilBranchInvariants2.DpSafeHere:295` は継続 `as` を**存在量化**してるので、`as` を全部 false に
取れば「DP 開始以降の比較回数 ≤ 開始時債務」に潰れる。つまり `ready` が要求するのは
**局所的な債務超過なし**だけで、`DpSafeStage`（リスト依存）ほど強くない。

そのうえで `ReadyIface` の 2 つの輸送場の収支を並べると:

| 場 | ガード | DP の残り必要イベント `need` | slack `k` | 債務 |
|---|---|---|---|---|
| `background` | — | `-1` | `≤ k + 1` | 不変 |
| `comparison` | `2048 ≤ k + 1` | `-1` | `→ 0` | 比較 1 消費 |

背景では `need + k` の和が保存され、比較（ガードにより `k = 2047` でしか起きん）では
和がちょうど `2048` 減る。よって

```
spent + ⌈(need + k) / 2048⌉ ≤ debt
```

は**両方の刻みで厳密に保存される**。機械の至る所に 2048 が出てくる理由がこれや。

### 書いたもの

`PalPeg/DpBudgetBalance.lean`（5 定理、標準 3 公理、全体 build 緑）:

* `DpBudget need spent debt k := spent + (need + k + 2047) / 2048 ≤ debt`
* `dpBudget_spent` — `ready` が要る `spent ≤ debt`
* `dpBudget_mono` — slack を下げるのは弱める
* `dpBudget_background` / `dpBudget_comparison` — 2 場ぶんの保存
* `dpBudget_comparison_needs_full_slack` — **ガードが鋭いことの証人**。
  `k = 2046` では `DpBudget 2 0 1 2046` は成り立つのに、比較後の `DpBudget 1 1 1 0` が破れる。
  つまり `ReadyIface.comparison` の `2048 ≤ k + 1` は `2047 ≤ k + 1` に弱められへん。

（最初 `dpBudget_comparison_sharp` として `¬ DpBudget (need-1) 1 0 0` を書いたが、
これは `hneed` を使わん自明な文で「鋭さ」を何も示せてへんかった。linter の未使用警告で気づいて
本物の証人に差し替えた。）

### これが `ReadyPacedS` と違う点

`ReadyPacedS` は同じ上界を `PacedL 2048 k as`（任意の継続）から得る。`PacedL` は
**リストの先頭からの累積**上界なので、長い背景で予算を貯めてから一気に撃つ列
（`replicate (2048*m) false ++ replicate m true` は `PacedL 2048 0`）を許すが、機械は出せへん。
`DpBudget` は**現在の slack** に対して述べるので、そういうスケジュールは最初から入らへん。

### 残り

この算術を `DpReached` / `SearchVM` / `ReadyIface` に接続すること。**まだ接続してへんので
何も落ちてへん**（公理 3 本のまま）。次は

1. `need` を `dpEvents w.length - bs.length` として `DpReached w lower s0 bs v.search v.dp` に結ぶ
2. `spent` を `bs.count true`、`debt` を `value s0.debt` に結ぶ
3. run 相の 1 刻みで `DpReached` が伸びること（背景・比較とも）を確認
4. prep / wait / double 相（`StageDoubleLeg` 済み）と合わせて `Φ` を定義し `ReadyIface` の 4 場を証明
## n200 — `StageEntryC.fuel` を `ReadyIface` の存在形に切り直した（継ぎ目が run 線に届く形になった）

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本、`Axioms.lean` のラチェット健在）・
無条件 PAL は未完。**

n199 の訂正どおり道を戻して、n195 の計画 1〜3 を実行した。

### 1. `ReadyIface` を `CloseoutReadyStage` §4 末尾に移した

`PalPeg/ReadyInterface.lean` は**削除**（Workbench の登録も）。定義が 4 つの証人
（`readyPacedS_ready` / `_mono` / `_effect_false` / `_effect_true`）の真下に来たので、
別ファイルに置く理由が無くなった。コピペを残さんため。

### 2. 5 定理を `Φ` ＋ `ReadyIface P Φ` で再証明（その場で一般化、22 パッチ）

`watchSegE_constructS` / `segment_of_invLPCS` / `readyPacedS_watchSegE`（→ **`readyIface_watchSegE`** に改名）/
`reachAtC3_of_target_matchS` / `reachAtC3_of_crossS`。
本文の変更は 4 補題呼び出しを 4 場に置き換えただけ。外部呼び出しは 3 箇所
（`CloseoutSegCheckpoint` / `CloseoutContracts` / `CloseoutPreload`）で、
`readyIface_readyPacedS P` を渡して従来どおりの挙動を回復。

### 3. `StageEntryC.fuel` を切り直した

```lean
-- 旧
fuel : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
-- 新
fuel : ∃ Φ : SearchVM → ℕ → ℕ → Prop,
  ReadyIface P Φ ∧ Φ (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)
```

`readyIface_readyPacedS` で旧形は新形に入るので**真に弱い**（操作 (A)）。
`StageEntryC` を構成してる箇所は**ゼロ**（全部仮説として受け取るだけ。継ぎ目やから当然）、
`.fuel` の使用は `reachAtC3_of_crossF_C` の 1 箇所だけやったので、切り直しの波及はそこだけ。

### なぜこれが効くのか

`ReadyPacedS` は `PacedL 2048 k` の**全**リストに量化する。`PacedL` は累積の上界なので、
背景で予算を貯めて一気に比較を撃つスケジュールを許すが、実機は比較を `clock = 1` でしか撃たず
直後に `clock := 2048` に戻すのでそれを出せへん。`ReadyIface.comparison` の `2048 ≤ k + 1` が
そのクロック規律そのものやから、**クロック添字の run 局所な `Φ` はこの場を正当に満たせる**。

### 残り

**`Φ` を実際に供給すること。** ステージ周期不変量（`StageDoubleLeg` が 1 相、
prep 相は `StagePrepS` が既にステップ局所）をクロック添字で組み、`ReadyIface` の 4 場を証明する。

**今回も公理は落ちてへん**（3 本のまま）。落ちたのは `StageEntryC.fuel` の強さだけ。
`NoReturn` / `EntryDepthG` を取る `runEntriesS_of_namedG` 経路は第 1 ステージ用として温存してある。
## n199 — n196 の判断は間違い。`ReadyIface` は producer を助ける。`EntryDepthG` も起点依存

**状態: 全体 build 成功・標準公理のみ（3 本）・無条件 PAL は未完。このターンは Lean 編集なし。**

### 1. `EntryDepthG` も `NoReturn` と同型（過剰量化の 9 例目）

一次情報 `CloseoutPreload5.EntryDepthG:607`:

```lean
def EntryDepthG (u : GalilVM) (D : ℕ) : Prop :=
  ∀ bs v v' c a, ReachL (searchLens.get u) bs v → searchStep c a v v' →
    v.search.mode ≠ .run → v'.search.mode = .run → bs.length + 1 ≤ D
```

restart 起点 `u` から到達する**すべての** `.run` 入口が `D ≤ prepLen k` 手以内、と主張してる。
第 2 ステージの入口は `prepLen k + mw + …` 手目やから、**第 2 ステージが存在した時点で破れる**。

よって `runEntriesS_of_namedG` は起点依存の仮説を **2 本**（`NoReturn` と `EntryDepthG`）
取っており、どちらも第 1 ステージでしか成り立たん。
機械検査した反証はまだ無いので `REFUTED` とは書かへん。

### 2. `ReadyPacedS` 自体が怪しい（疑い。反証はまだ無い）

`DpSafeStage v as`（`CloseoutReadyStage:93`）は

```lean
as = pre ++ post ∧ 3186*w.length+1683 ≤ 64*(bs ++ pre).length ∧
  ((bs ++ pre).count true : ℤ) ≤ value s0.debt
```

——`as` の先頭 `≈ dpEvents(2mw+1) ≈ 100·mw` 手の**比較回数**が債務（`≈ 2·max k 1`）以内、を要求する。

一方 `PacedL 2048 slack as := ∀ n, 2048 * (as.take n).count true ≤ n + slack` は**累積**の上界で、
「長い背景のあとに比較をまとめて撃つ」バーストを許す
（例: `replicate (2048*m) false ++ replicate m true` は slack 0 で paced）。
実機の制御はバーストを出せへん——比較は `clock = 1` でしか起きず、直後に `clock := 2048` に戻る。

`ReadyPacedS v n 0 = ∀ as, n ≤ as.length → PacedL 2048 0 as → SearchReadyS v as` の `n` は
**下界**なので、バースト列も全部対象に入る。バーストを跨ぐステージの `DpSafeStage` は
比較回数が債務を超えて破れるはず。**つまり `ReadyPacedS` は機械が絶対に出さんスケジュールにまで
量化しており、偽の疑いが濃い。** 前身の `ReadyFuel` が偽やったのと同じ病。

### 3. n196 の訂正（ウチの判断ミス）

n196 で「`ReadyIface` による `Φ` 抽象化は producer を 1mm も助けへん」と書いた。**間違いやった。**

`ReadyIface` の場を読み直すと:

```lean
comparison : 2048 ≤ k + 1 → s.chain = ChainVM.idle →
  Φ (searchLens.get s) (n + 1) k → searchEffect P true s v → Φ v n 0
```

**比較は slack が満杯（`k = 2047`）のときしか許されへん。** これがまさにバーストを禁じる
クロック規律や。つまり `ReadyIface` は最初から「機械が実際に出すスケジュール」だけを要求してる。
`ReadyPacedS` がそれを満たすのは、`ReadyPacedS` が（おそらく）強すぎる＝偽やから。
**クロック添字の run 局所な `Φ` なら、`ReadyIface` を正当に満たせる。**

n195 は正しい道具を、間違った理由で作った。n196 はそれを、不十分な理由で捨てた。両方ウチの判断ミスや。

### 次（道が戻った）

1. `watchSegE_constructS` と 4 消費者を `Φ` ＋ `ReadyIface P Φ` で再証明（n195 の計画どおり）。
2. `StageEntryC.fuel` を `∃ Φ, ReadyIface P Φ ∧ Φ …` に切り直す。
3. ステージ周期不変量（`StageDoubleLeg` はその 1 相）を **clock/slack 添字**で組み、`Φ` として供給する。
   slack ≤ 2047 は制御の `2048 ≤ clock + k` が与えるので、純 `SearchVM` の `∀ as` では出えへんかった
   ものがここで出る。
4. `runEntriesS_of_namedG` 経路（`NoReturn` ＋ `EntryDepthG`）は第 1 ステージ専用として温存。

**今回も何も落としてへん**（公理 3 本のまま）。
## n198 — `StageDoubleLeg`：ステージ周期 4 相のうち double 相をステップ局所にした

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

`EntryInv Q` は不変量に `searchStep` を 1 手ずつ渡し、**任意の**イベント列に量化するので、
`Q` は「いま自分がいる脚」を丸ごと名指しでけへん。既存の
`CloseoutPreload17.double_spends` と `CloseoutPreload35.postRunF_round_trip_S` は
どちらも `.double` 脚を `bs.length = mw` ごと仮説に取る。そこをステップ局所に切り直した。

`PalPeg/StageDoubleLeg.lean`（5 定理、標準 3 公理、全体 build 緑）:

* `doubleTrace_snoc` — `DoubleTrace` は前方 cons なので、末尾で伸ばすには別の帰納法が要る
* `doubleTrace_frame` — `ds` 手後に work は `ds.length` 減り span は `2*ds.length` 増える。
  **`ds.length ≤ mw` はここから出る**（仮定せんでええ）
* `pacedL_prefix_slack` — 既存 `pacedL_prefix_of_append` は slack 0 固定。`.double` 脚は
  クロック位相が任意の所で始まるので slack 版が要った
* `DoubleLeg k mw slack u v as` — 不変量。pacing を**脚の先頭 `u` から**測るのが要点で、
  `bal_of_paced_slack_S` が脚全体の比較回数を読むため、現在時刻の状態述語では間に合わへん
* `doubleLeg_step` / `doubleLeg_exit` — 1 手の 2 分岐。work が残れば不変量が続き、
  使い切れば `PrepAt k (2*mw)` ＋ `StageInvS k (2*mw)` に落ちる

### 残り

ステージ周期は 4 相（`.run` / `.wait` / `.double` / preparation）。**double 相だけ**が
ステップ局所になった。残り 3 相と、それらを `EntryInv` の `Q` に組み上げるところは未着手。
**今回も何も落としてへん**（公理 3 本のまま、`NoReturn` も残ったまま）。

### 次

1. prep 相は `StagePrepS` がそのままステップ局所（`stagePrepS_next` ＋
   `dpSafe_of_stagePrepD_slack`）。4 相のうちこれで 2 相。
2. `.wait` 相：`wait_step_cases` が後続を `.wait ∨ .double` に限定し、`.double` へ出るときに
   `wait_exit_double` が `DoubleLeg` の先頭データ（`work = ofNat mw` / `span = reset` /
   `quarter = 0` / `debt = 0`）を与える。`WaitTrace` の snoc/frame を `DoubleTrace` と
   同じ形で作ればよい。
3. `.run` 相：`RunTrace` と `run_exit_frame`。`run_exit_wait_match` が出口の event を縛る。
4. 4 相の選言を `Q` にして `EntryInv Q`。入口節は `run_entry_startRun` により prep 相以外は空虚。
## n197 — `StageCycleSearch`：一周を制御層から切り離した。全域性が残りの全部

**状態: 全体 build 成功（`BUILD=0`、エラー 0）・標準公理のみ（3 本）・無条件 PAL は未完。**

### 既にあったもの（書く前に見つけた）

`PalPeg/CloseoutRunEntriesS.lean` に汎用ドライバが既にあった:

* `run_entry_startRun:87` — `.run` に入る直前のモードは **`.home` に限る**。
  よって run/wait/double/lower/lowerHome/copy の全相で `RunEntryS` は空虚。
* `EntryInv Q:212` / `runEntriesS_of_inv:220` — `searchStep` で保存され各 `.run` 入口で
  `DpSafeStage` を出す `Q` があれば、**`as` の長さにも比較回数にも条件なしで**
  `RunEntriesS as v`。`EntryInv` の実体化はまだ無い（ドライバはある、`Q` が無い）。

空虚性補題を自分で書きかけてたが、`run_entry_startRun` がそれやった。**書かんで済んだ。**

### このターンで書いたもの

`PalPeg/StageCycleSearch.lean`（1 定理、標準 3 公理、全体 build 緑）。

`CloseoutPreload35.postRunF_round_trip_S` は frame 仮説を 5 本（`hsup` / `hsc` / `hp` /
`hclk` / 全ストリームの pacing）取るが、その全部が

```lean
have hph := prefixPhase_of_scan_inv hsup hsc hp hclk.1 hclk.2
have hpa : PacedL 2048 2047 (bs ++ [a3]) := pacedL_suffix_2047 hpaced hph
```

の 1 事実を出すためだけに使われてる。そこで 5 本を `PacedL 2048 2047 (bs ++ [a3])`
1 本に差し替えた `stageCycle_of_runEntry` を切った。**仮説は真に弱い**（操作 (A)）。
結果、一周（`.run` 入口 → run/wait/double 脚 → `PrepAt k (2*mw)` ＋ `StageInvS k (2*mw)`）が
frame・control・`GalilVM` を一切含まん純 `SearchVM` の定理になった。

これが必要な理由: `EntryInv Q` は**任意の**イベント列と**任意の** `searchStep` 後続に量化するので、
`Q` が実機の `ScanTrace` を持つことはできひん。

### 残り（これが全部）

**全域性**: 任意の paced なイベント列を脚（`RunTrace rs` / `WaitTrace ws` / `bs.length = mw`）に
分解すること。`stageCycle_of_runEntry` は脚をまだ仮説として取る。これが出れば

```
Q（ステージ周期不変量）→ EntryInv Q → runEntriesS_of_inv → RunEntriesS（∀ as）
  → readyField2_entry_of_datum から NoReturn が落ちる → StageEntryC.fuel
```

が通る。**今回は何も落としてへん**（公理 3 本のまま、`NoReturn` も残ったまま）。

### 次

1. ステージ周期不変量 `Q` を定義する。2 つの選言（prep 相 = `StagePrepS`、
   run/wait/double 相 = 脚の途中）で、後者は `run_entry_startRun` により入口節が空虚。
2. `EntryInv Q` の prep 半分は `dpSafe_of_stagePrepD_slack` ＋ `stagePrepS_next` で出る。
3. run/wait/double 半分が本体。`searchStep` は各相で関数（`double_step_pos` /
   `wait_step_cases` / `run_step_quanta` はどれも `subst hs` で進む）なので、
   脚の分解は決定的に取れるはず。まずそこを測る。
## n196 — n195 の診断は間違いやった。`NoReturn` が producer の壁（一次情報で確定）

**状態: 全体 build 成功（このターンは編集なし）・標準公理のみ（3 本）・無条件 PAL は未完。**

### n195 の訂正

n195 で「`ReadyPacedS` の `∀ as` が過剰量化で、それが `StageEntryC.fuel` の壁」と書いた。
**過剰量化の測定自体は正しい（消費者は 4 補題しか通らず、任意リストに具体化しない）が、
それは producer の壁やない。**

一次情報 `CloseoutPreload37.readyField2_entry_of_datum:199`:

```lean
have hp : ReadyPacedS (searchLens.get r) (dpEntryG (value last).toNat D) 0 :=
  readyPacedS_restarted hR _ 0
    (fun as hlen hpaced => runEntriesS_of_namedG hR hSE hcl hnr hdep hD as hlen hpaced)
```

`∀ as` は `runEntriesS_of_namedG` が既に捌いてる。詰まってるのは仮説 `hnr : NoReturn u` や。
**`ReadyIface` による `Φ` 抽象化は consumer 側の記録としては有効やが、producer を 1mm も助けへん。**
15 ファイル超の改修に入る前に測って助かった。

### `NoReturn` の正体（`CloseoutPreload6.runEntriesS_of_namedG:231`）

`hnr` の使用は 3 箇所、全部同じ形 `(hnr bs v hreach hne) : ReachL … bs v → ReachP … bs v`。
渡し先は 2 本だけ:

* `CloseoutPreload5.entry_shape:498` — `ReachP` → prep 形（`PrepTrace v0 n v` ＋ 窓の較正）
* `CloseoutPreload5.entry_debt:529` — `ReachP` → 入口債務 `stageDebt Rad k − (bs++[a]).count true`

どちらも `ReachP` を `phase_reach hR hcl hp` に食わせてるだけ。
`NoReturn` は **「restart 起点 `u` からの `ReachL` を `ReachP` に変える変換器」以外の仕事をしてへん。**
偽になる理由も同じで、`.run` を一度通ったら `u` 起点の `ReachP` は破れる。

### `PrepAt` 基底版は既にある

`CloseoutPreload35.dpSafe_of_stagePrepD_slack:145` の中身が一次情報:

```lean
obtain ⟨W, lower, hW, hpreload⟩ := entry_preload_at_prep hp hreach hs hrun
obtain ⟨hcan, hdv⟩          := entry_debt_at_prep   hp hreach hs hrun
```

`entry_preload_at_prep` / `entry_debt_at_prep` が `entry_shape` / `entry_debt` の `PrepAt` 基底版で、
**`NoReturn` を取らへん**。2 つの到達述語は同じ形で基底だけ違う:

| | 到達関係 | 基底 | 追加仮説 |
|---|---|---|---|
| `QG u k D`（Preload6） | `ReachL` | restart `u` | **`NoReturn`**（偽） |
| `StagePrepS k m D slack w`（Preload35:127） | `ReachP` | `PrepAt` 状態 `w` | なし |

### それでも単純な差し替えは効かへん（ここが本当の壁）

`StagePrepS` は `ReachP` やから `.run` を通れへん。`stagePrepS_next` は `hne : v'.mode ≠ run` を要求する。
よって **1 つの `PrepAt` から伸びるのは 1 ステージ分だけ**。
`RunEntriesS as v` は `as` 全体に沿った**すべての** run 入口で `DpSafeStage` を要求するので、
ステージを跨ぐには基底を置き直さなあかん。その置き直しが `CloseoutPreload10.prepAt_of_double_exit`
（`.double` 出口で `PrepAt k (2m)` を再確立）であり、それを鎖にしたのが
`CloseoutPreload36.StageChain` や。

つまり n194 で「2 本の線が食い違う」と書いたものの正体は、抽象化の不足やなくて
**「任意の paced リストに対してステージ鎖が張れるか」という全域性**やった。

### 次（この順）

1. **全域性補題**: `PrepAt k m v` と十分長い paced `as` から `StageChain k m mw' evs tail` を構成する。
   材料は `CloseoutPreload35.postRunF_next_entry:429`（run 入口から次の入口）と
   `doubleTrace_det:489`（double 相の決定性）。`RunEntriesS` の `∀ center v', searchStep …` に
   応えるには決定性が要るので、まず `doubleTrace_det` の届く範囲を測る。
2. 1 が出れば `postRunC_galil_of_boot` で `RunEntriesS` が出て、`runEntriesS_of_namedG` から
   `NoReturn` が落ちる。**公理の下の偽の前提が 1 本減る**（操作 (C)）。
3. `readyField2_entry_of_datum` → `StageEntryC.fuel` は配線済みなのでそのまま通る。
4. 残る boot 段（`k ≤ 1`、窓 8、slack 0）は `CloseoutPreload28` 経路で別途。

`ReadyInterface.lean` は消さへん。consumer 側の過剰量化の測定は事実として正しく、
`StageEntryC.fuel` を将来切り直すときの記録として残す。ただし **今のところ何も落としてへん**。
## 2026-09-19 n195: `ReadyPacedS` は過剰量化だった（測定済み）——インターフェイスを切り出した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

### 測定（n194 の宿題）

`CloseoutReadyStage` 全域で `ReadyPacedS` の使い方を数えた。
`watchSegE_constructS` / `segment_of_invLPCS` / `readyPacedS_watchSegE` /
`reachAtC3_of_crossS` / `reachAtC3_of_target_matchS` ——**全部**が次の 4 本だけを通る:

| 補題 | 何をする |
|---|---|
| `readyPacedS_ready` | `SearchReady` を取り出す（証人は `List.replicate n false` 1 本） |
| `readyPacedS_mono` | 添字を弱める |
| `readyPacedS_effect_false` | **背景量子 1 手**に沿って運ぶ |
| `readyPacedS_effect_true` | **比較量子 1 手**に沿って運ぶ |

**任意のリストに具体化している箇所は 1 つも無い。**
`ready` は固定の証人 1 本、`effect_*` は 1 要素の前置だけ。よって

    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as

の `∀ as` は**消費者に対して過剰量化**（CLAUDE.md の 8 例と同じ型）。
これが効くのは `ReadyPacedS` が `CloseoutContracts.StageEntryC.fuel` だからで、
run 基底の readiness 線（`CloseoutPreload28/35/36`）は
**機械が取らないリストへの量化を原理的に出せない**（`CloseoutPreload36` の
「What this is and is not」）。

### 切り出したもの

`PalPeg/ReadyInterface.lean`（新規、1 構造体 ＋ 1 定理、標準 3 公理）:

    structure ReadyIface (P : Shared) (Φ : SearchVM → ℕ → ℕ → Prop) : Prop where
      ready      : Φ v n k → SearchReady v
      mono       : n ≤ n' → k' ≤ k → Φ v n k → Φ v n' k'
      background : k' ≤ k+1 → s.chain = idle → Φ (get s) (n+1) k →
                     searchEffect P false s v → Φ v n k'
      comparison : 2048 ≤ k+1 → s.chain = idle → Φ (get s) (n+1) k →
                     searchEffect P true s v → Φ v n 0

    theorem readyIface_readyPacedS (P) : ReadyIface P ReadyPacedS

4 場は既存 4 補題そのまま。**これが測定の形式的な記録**——
インターフェイスは `CloseoutReadyStage` が証明する内容より弱くなく、
`CloseoutReadyStage` が使う内容より強くない。

### まだ何も外れていない（正直な状態）

`watchSegE_constructS` とその 4 消費者を抽象 `Φ` に対して**再証明していない**。
機械的（4 つの補題呼び出しを 4 つの場に置き換えるだけ）だが長い。
それが済むまでこのファイルは何も落とさない。

### 次

1. `watchSegE_constructS` を `Φ` ＋ `ReadyIface P Φ` で再証明
2. `segment_of_invLPCS` / `readyPacedS_watchSegE` / `reachAtC3_of_crossS` を追従
3. `StageEntryC.fuel` を `∃ Φ, ReadyIface P Φ ∧ Φ …` に切り直す
4. run 線（`Preload28/35/36`）が run 添字の `Φ` を供給する

## 2026-09-19 n194: **n189 の書き方を訂正**＋2 本の線の食い違いが本当の壁

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。コードは変更していない（訂正と診断のみ）。**

### 訂正（自分の誇張）

n189 で「準備相を歩きから切り離した／段境界を越える状態局所の背骨を作った」と書いたが、
**`CloseoutPreload28/35/36` の線はもともと状態局所だった。** 一次情報:

    CloseoutPreload35.dpSafe_of_stagePrepD_slack
      (hp : PrepAt k m v) … (hq : StagePrepS k m D slack v x (a :: as)) …

`StagePrepS _ _ _ _ w v as := ∃ bs, ReachP w bs v ∧ …` の基点 `w` が
**`PrepAt` 状態そのもの**（段の `begin` ではない）。段境界では
`prepAt_of_double_exit` が `PrepAt` を再成立させるので、この `ReachP` は往復で切れない。

`StageLocalPrep`（n189）が実際に足したのは 2 つだけ:
* 包装（`PrepPhase` = `PrepAt` ＋ `PrepTrace` ＋ 非 `.run`）
* `preloadAt_of_prepPhase` ——較正仮説
  `((stream s.walker).take (span+1)).length = stageWindow1 k` を落とした
  （消費者が読むのは `W.length ≤ m + 1` だけで、これは `List.length_take` でタダ）

**診断そのもの（`PostRun` / `NoReturn` がなぜ落ちないか）は有効。** 誇張したのは
「新しく作った」の部分。

### 本当の壁: 2 本の線が噛み合っていない

| 線 | `ReachP` の基点 | 状態 | 出せるもの |
|---|---|---|---|
| 旧（`Preload6/8/11/37`） | 段の `begin` ／ restart からの `ReachL` | `NoReturn` は偽、`PostRun` は producer なし | `ReadyPacedS`（**状態量化**）を `readyField2_entry_of_datum` で |
| 新（`Preload28/35/36`） | `PrepAt` 状態（境界で再成立） | **証明できる**（n190〜n193 で算術も詰めた） | run に沿った `DpSafeStage` のみ |

`CloseoutPreload36` 自身が「What this is and is not」でこう書いている——
run 帰納は機械自身の状態しか届かないので `PostRunPh` / `PostRunC` は作れない。

**食い違いの場所は `CloseoutContracts.StageEntryC.fuel : ReadyPacedS`。**
`ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as → SearchReadyS v as` は
**任意のペース付きリスト**に量化していて、新しい線は原理的にこれを出せない。

### 次にやること（公理への最短路）

`ReadyPacedS` が消費者に対して過剰量化していないかを測る
（CLAUDE.md の過剰量化 8 例と同じ検査）。消費者は
`CloseoutReadyStage.segment_of_invLPCS` / `readyPacedS_watchSegE` /
`reachAtC3_of_crossS` で、どれも **run に沿った watched segment** を作るために使う。
run 形に切り直せるなら、新しい線が `StageEntryC` を直接埋める。
切り直せないなら、旧線の `PostRun` を倒すしかない。**まずこれを測る。**

## 2026-09-19 n193: 算術の穴 2 は「boot 段だけ」に落ちた——しかも boot は slack 0

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean` §2 に 1 本追加（標準 3 公理）:

    boot_windows_covered (hj : 1 ≤ j) : 16 ≤ 8 * 2 ^ j

### 筋が通った

boot では `lower = 0` で `grow` に入るので第 1 段の窓は `mw₀ = 8 * max 0 1 = 8`、
以降は倍々（`8, 16, 32, …`）。n192 のしきい値 `16` で
**第 2 段以降は全部覆われる**。残るのは boot 段 1 つだけ。

そしてその boot 段は **slack 0**——一次情報
`GalilScaffoldController.initial delay = ⟨.init, delay, false, false, false, false⟩`
（`GalilScaffoldController.lean:109`）で `clock = 2048`、slack `= 2048 - clock = 0`。
slack 0 の需要は `CloseoutPreload28.dpDemand`（`+2047` が無い方）で、その balance
`bal_of_paced_slack` が要るのは **`8 ≤ mw` だけ**。`mw₀ = 8` はちょうど満たす。

| 段 | 窓 | slack | 使う balance | しきい値 | 状態 |
|---|---|---|---|---|---|
| 第 1（boot） | 8 | **0** | `CloseoutPreload28.bal_of_paced_slack` | `8 ≤ mw` | 材料あり |
| 第 2 以降 | 16, 32, … | 任意 | `CloseoutPreload35.bal_of_paced_slack_S` | `16 ≤ mw`（n192） | **覆われた** |

**まだ組んでいない**: boot 段を `CloseoutPreload28` 経路で通し、第 2 段で
`CloseoutPreload36.postRunC_galil_of_boot` に接続する配線。
`CloseoutPreload36` §4 の **boot datum**（第 1 `.run` 入口の `EntryDatum`）も未証明。

### 算術の穴の現況（更新）

| # | 穴 | 状態 |
|---|---|---|
| 1 | `depth_exceeds_prepLen` | **閉（n190）** |
| 2 | slack 2047 の 2 単位 | **boot 段のみ、かつ boot は slack 0 で経路あり（n191〜n193）** |
| 3 | 段境界のイベント供給（`StageLegs` の `hlen`） | 未着手 |

## 2026-09-19 n192: しきい値 `32 → 16` を本線に入れた——`postRunF_step` の残差は `k ≤ 1` の**第 1 段だけ**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n191 の `16 ≤ mw` を複製で持つのをやめ、`CloseoutPreload35.bal_of_paced_slack_S`
**そのもの**のしきい値を下げた（証明は同じ＋`16 ≤ mw < 20` の 4 窓を
`interval_cases`。`omega` は 2 つの `/2048` を含む tight な系で不完全）。
下流の `postRunF_round_trip_S` / `postRunF_round_trip_galil_S` / `postRunF_step` と
`CloseoutPreload36`（10 箇所）も `16 ≤ mw` に緩めた。

### 効き方

`CloseoutPreload35` §7 は `hmw : 32 ≤ mw` を
**「機械の run とモード註釈の外にある唯一の仮説」**と書いていた。
`postRunF_step` は較正 `8 * max k 1 ≤ mw` を持つので:

| しきい値 | 覆われる段 | 残差 |
|---|---|---|
| `32`（旧） | `k ≥ 4` | `k ≤ 3` |
| **`16`（新）** | **`k ≥ 2`** | **`k ≤ 1`** |

さらに `mw0 = 8 * max k 1` で窓は倍々になるので、`k ≤ 1` でも
**第 1 段（窓 8）だけ**が残る——第 2 段は窓 16 で覆われる。

`PalPeg/StageBudgetShift.lean` §2 は複製を消して、この残差の記録だけにした:

    window_covered_of_k (hcal : 8 * max k 1 ≤ mw) (hk : 2 ≤ k) : 16 ≤ mw
    window_residual    (hcal : 8 * max k 1 ≤ mw) (hmw : mw < 16) : k ≤ 1 ∧ 8 ≤ mw

### `D ≤ prepLen k` は 2 箇所で意味が違う（n190 の補足）

* `CloseoutPreload6.runEntriesS_of_namedG` の `D`: **restart から**測るので
  grow 相の `max k 1` ティックと `prepare` dispatch を含む → `prepLen k` を超える
  （`depth_exceeds_prepLen`）。n190 の `budget_adv_shift` がここを直す
* `CloseoutPreload35.dpSafe_of_stagePrepD_slack` の `D`: **`PrepAt` 入口から**
  測るので準備相のティックだけ → `prepLen k` で正しい。**ここは直す必要がない**

## 2026-09-19 n191: 2 つめの算術の穴を `32 ≤ mw` → `16 ≤ mw` に縮めた（残りは `k ≤ 3`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean` §2（3 定理追加、標準 3 公理のみ）:

    bal_of_paced_slack_S16 … (hmw : 16 ≤ mw) … :
      4 * dpDemandS k (2*mw) + 4 * (bs ++ [a]).count true ≤ mw
    window_covered_of_k (hcal : 8 * max k 1 ≤ 2*mw) (hk : 4 ≤ k) : 16 ≤ mw
    window_residual (hcal : …) (hmw : mw < 16) : k ≤ 3 ∧ 4 ≤ mw

### 記録が両端とも間違っていた

`CloseoutPreload35` §3 は残差を「4 窓 `8 ≤ mw < 32`」と記録していたが、
**同じ入力**（`prepLen_le` / `dpEvents_win_le` / 窓全体のペーシング）で
`16 ≤ mw` から成立する。`32` は保守的な当て推量だった。
`mw ≤ 3` は `8 * max k 1 ≤ 2*mw` が `4 ≤ mw` を強制するので空虚。
**真の残差は `4 ≤ mw ≤ 15`、較正 `4 * max k 1 ≤ mw` で言い換えると `k ≤ 3`。**

`16` はこの入力に対して sharp: `mw = 15` では最悪の
`(prepLen k, dpEvents (2mw+1), count)` が balance `16 > 15` を与える。
余裕が 2 以下なのは `mw ∈ {16,17,18,20,21,22}` だけ（`mw=16` と `mw=20` で 0）。

証明は `mw < 20` / `mw ≥ 20` で分割。前者は `4 * max k 1 ≤ mw ≤ 19` から
`max k 1 ≤ 4` が出るので `interval_cases mw` で 4 ケース。
後者は `omega` が直接通る（`16 ≤ mw` のままでは `omega` が
2 つの `/2048` を含む tight な系で落ちる——反例は無い、不完全性）。

### 算術の穴の現況

| # | 穴 | 状態 |
|---|---|---|
| 1 | `depth_exceeds_prepLen`（`D ≤ prepLen k` が満たせない） | **閉（n190）** |
| 2 | slack 2047 の 2 単位（`CloseoutPreload35` §3） | **`k ≤ 3` に縮小（n191）** |
| 3 | 段境界のイベント供給 | 未着手 |

## 2026-09-19 n190: 記録済みの否定的結果（`depth_exceeds_prepLen`）を予算の緩和で閉じた

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageBudgetShift.lean`（新規、3 定理、標準 3 公理のみ）:

    budget_adv_nat_shift {k Rad adv m} (hstage : 3 * Rad ≤ 5 * k)
      (hadv : 2048 * adv ≤ prepLen k + max k 1 + 1)      -- ← 緩めた
      (hm   : 2048 * m ≤ prepLen k + dpEvents (stageWindow1 k) + 2048) :
      adv + m + Rad ≤ 2 * max k 1
    budget_adv_shift      -- ℤ 版（結論は stageDebt Rad k）
    budget_adv_of_shift   -- 旧 budget_adv を含むことの確認

### 何が閉じたか

`CloseoutPreload7.depth_exceeds_prepLen`（機械検査済み）は
**`CloseoutPreload6.runEntriesS_of_namedG` の側条件 `D ≤ prepLen k` が
満たせない**ことを言っていた: 実際の入口深さは
`max k 1 + 2 + (prepLen k - 1) = prepLen k + max k 1 + 1`
（`depth_le_prepLen_shifted`）で、`prepLen k` より真に大きい。
grow 相の `max k 1` ティックと `prepare` dispatch を数え落としていた。

`D ≤ prepLen k` の唯一の使い道は `budget_adv` の `2048 * adv ≤ prepLen k` なので、
そこを**実際の深さちょうど**に緩めた。結論は不変。

### 両側とも tight

* `k ≥ 9`: 緩い上界（`prepLen_le` / `dpEvents_stage_le`）で足りる——
  `3·2048·(adv+m+Rad) ≤ 11548k + 6429 ≤ 12288k` は `k ≥ 9` と同値
* `k ≤ 8`: 9 個の具体ケース。`k = 1, 2, 3, 5, 6` では**余裕がちょうど 0**

（数値確認: `k = 0..5000` と `10^5, 10^6, 10^7` で成立。余裕は `k=9,10` で 1、
`k=20` で 2、`k=100` で 13、`k=10^6` で 120809。）

### 読み方

これは readiness 連鎖の**算術の穴 3 つのうち 1 つ**。残り 2 つ:
`CloseoutPreload35` §3（`8 ≤ mw < 32` の 4 窓、slack 2047 で 2 単位吸収できない）と、
段境界でのイベント供給。**公理は減っていない**（穴は公理の下にある）。

## 2026-09-19 n189: 準備相を「歩き」から切り離した——段境界を越える状態局所の背骨

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/StageLocalPrep.lean`（新規、4 定理、**全部 `[propext, Quot.sound]` のみ**）:

| 定理 | 内容 |
|---|---|
| `prepPhase_start` | `PrepAt k m v → PrepPhase k m 0 v` |
| `prepPhase_step` | `.run` に入らない 1 手で保存（`k`/`m` 不変、`n` だけ増える） |
| **`prepPhase_of_double_exit`** | **段境界で再成立**（`.double` 出口だけから） |
| `preloadAt_of_prepPhase` | dispatch で DP の preload、窓は `w.length ≤ m + 1` |

    def PrepPhase (k m n : ℕ) (v : SearchVM) : Prop :=
      (∃ e, PrepAt k m e ∧ PrepTrace e n v) ∧ v.search.mode ≠ Mode.run

### なぜこれが要るか（n187〜n189 の診断の決着）

`PostRun`（`CloseoutPreload8:253`）と `NoReturn`（`CloseoutPreload5:599`）は
**同じ欠陥**で、どちらも producer が無い:

* `NoReturn u := ∀ bs v, ReachL u bs v → v.mode ≠ .run → ReachP u bs v`
  ——`run → wait → double → prepare` の往復を通った歩きは `ReachP` ではないので**偽**
* `PostRun := ∀ v as, v.mode = .run → DpSafeStage v as → RunEntriesS as v`
  ——`.run` 入口で台帳を丸ごと作り直せと言っている

両方の根は `StagePrep2`（`CloseoutPreload11:293`）の第 1 節
`ReachP w bs v`——**その段の `begin` からの歩き**。機械は最初の `.run` 入口で
そこを永久に離れるので、次の段では再成立しない。

**しかし消費者が実際に使うのは状態局所の事実だけ**（`CloseoutPreload2.preloadAt_of_prepRun`
が要るのは「新鮮な `.lower` 入口 `e`」と「`PrepTrace e n v`」の 2 つ）。
`CloseoutPreload10.PrepAt k m` がその新鮮な入口で、
`prepAt_of_double_exit` が**段境界でそれを再成立させる**（歩き不要）。
だから `PrepPhase` は往復を越えられる。

### 副産物: 較正仮説が 1 つ消えた

`preloadAtEntry_of_trace` は
`((stream s.walker).take (span+1)).length = stageWindow1 k` を要求していたが、
消費者 `CloseoutPreload11.dpSafe_entry_km` が読むのは `W.length ≤ m + 1` だけ。
これは `List.length_take` でタダ。`preloadAt_of_prepPhase` は較正を取らない。

### 残り（ここには入れていない）

段境界での**リスト側の帳簿**——ペーシング、イベント供給
（`dpEvents (m+1) ≤ as.length`）、負債。これが `CloseoutPreload35` §3 の
`8 ≤ mw < 32` の 4 窓の算術と同じ場所。

## 2026-09-19 n188: `.run` 相で `RunEntriesS` が縮む原子を作った（`PostRun` 整礎化の第一歩）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/PostRunInduction.lean`（新規、1 定理、標準 3 公理のみ）:

    runEntriesS_cons_of_run (hm : v.search.mode = Mode.run)
      (hnext : ∀ center v', searchStep center a v v' → RunEntriesS as v') :
      RunEntriesS (a :: as) v

`RunEntryS center a v v' as` の第 2 仮説が**源の mode が `.run` でない**ことを要求するので、
源が `.run` なら空虚。残るのは行き先の `RunEntriesS as v'` だけ。

**これが `PostRun` を整礎帰納に置き換えるための原子。** `runEntriesS_of_stageInv2`
（`CloseoutPreload11:296`）が `PostRun` を必要とするのは `as` への帰納が `.run` 入口で
**縮まない**からで（`hpost v' as hr hsafe` を同じ `as` に使っている）、
`.run` 相でもイベントは消費されるのでこの補題で縮む。

### 既にある材料（n187/n188 で確認）

| 部品 | 場所 |
|---|---|
| `.run` 相のトレース | `CloseoutPreload13.RunTrace:79` |
| `.run` 相の 1 手の中身 | `CloseoutPreload13.run_step_quanta:85` |
| `.run` 出口のデータ（債務・`ExitMode`・次相の span/work） | `CloseoutPreload13.run_exit_frame:146` |
| 次の `.run` 入口の datum | `CloseoutPreload35.postRunF_next_entry`（§5） |
| 1 入口 → 次入口 | `CloseoutPreload35.postRunF_step`（§6） |
| **`.run` 相で `as` が縮む** | **`PostRunInduction.runEntriesS_cons_of_run`（n188）** |

### 残り

* 整礎帰納の組み立て（`as.length` で測る）
* **per-stage の供給条件**（各 stage 入口で残りイベントが `dpEvents (m+1)` 以上）——
  これは run に沿ってしか言えないので、`PostRun` を trace/run 形に切り直す必要がある（n187）
* `8 ≤ mw < 32` の 4 窓の算術（n186）

## 2026-09-19 n187: **`PostRun` に producer が無い理由が割れた**（落とした供給条件）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

コウタの指摘「**producer がないときは確実に形式化ミス**」を当てはめた。

    PostRun := ∀ v as, v.search.mode = .run → DpSafeStage v as → RunEntriesS as v

**`∀ v as` が run にも供給条件にも縛られていない。** 消費者が持っているのに
文が落としているものが 2 つ:

| 消費者（`StagePrep2` / `runEntriesS_of_restartS2`） | `PostRun` |
|---|---|
| `PacedL 2048 0 (bs ++ as)` | **無い** |
| `D + dpEvents (m+1) ≤ bs.length + as.length`（列が十分長い） | **無い** |

**短さで落ちることは既に機械検査済み**: `CloseoutPreload3.not_runEntriesS_eight`
（節タイトル「`RestartEntryS` is false: **the paced list may be too short**」）。
8 番目のイベントで `.run` に入ると残りが `[]` になり `DpSafeStage (w p8) []` の
課金プレフィックスが空 → `dpSafeStage_pre_ne_nil`。
**同じ証人が `PostRun` も落とす。**（`REFUTED` とはまだ書かない）

### なぜ帰納が止まっていたか

    StageInv2 k m D w v as := StagePrep2 k m D w v as ∨ RunEntriesS as v

`runEntriesS_of_stageInv2` は `as` に帰納するが、`.run` 入口で `hpost v' as hr hsafe` を
使うので **`as` が縮まない**。`.run` 相でもイベントは消費されるので本来は
`as.length` の整礎帰納で閉じられるはずだが、**各 stage 入口で「残りが十分長い」が要る**。
それが落とした供給条件で、**run に沿ってしか言えない**。

→ **`PostRun` は trace/run 形に切り直す。** CLAUDE.md の「global 形は原理的に落ちない」
がそのまま当てはまる（`hav` / `hpack` / `hpres` / `RunEntriesAtBegin` に続く 5 例目）。

### 次

1. `PostRun` の反証を書く（`not_runEntriesS_eight` の証人を流用）
2. run 形 `PostRunAlongRun` に切り直す
3. `runEntriesS_of_stageInv2` を整礎帰納で書き直し `hpost` を外す

## 2026-09-19 n186: `PostRunF` 帰納の**具体的な穴**が出た（`8 ≤ mw < 32` の窓）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`CloseoutPreload35` の冒頭（一次情報）が穴を明記していた:

> §3 the `.double` exit satisfies `StageInvS` when `32 ≤ mw`
> (`bal_of_paced_slack_S`, `stageInvS_of_double_exit`); **the four windows
> `8 ≤ mw < 32` do not absorb the two extra units at slack `2047`**

帰納段 `postRunF_step`（§6）と次入口の構成 `postRunF_next_entry`（§5）は**ある**。

### 穴の大きさ

窓は restart で `mw = 8 * max k 1`、`.double` で倍々。だから
`8 ≤ mw < 32 ⟺ k ≤ 3` の初期 stage だけ。`k ≥ 4` なら `8k ≥ 32` で §3 が閉じる。
**境界ケースは 4 つ**。

### もう 1 つの穴: 帰納の基底

`postRunF_step` は帰納段で、**基底（boot / restart 後の最初の `.run` 入口の datum）を
出す定理は見つかっていない**。`CloseoutPreload.run_entry_preload:130` は
`.run` 入口の DP 機械の同定という局所事実で、基底ではない。

### 次（優先順、`PROOF_STACK.md` に記録）

1. `8 ≤ mw < 32` の 4 窓を `dpDemandS` の算術で詰める
2. 基底を探す/作る（restart 直後の最初の `.run` 入口）
3. 1 ＋ 2 ＋ `postRunF_step` で `PostRunF` の帰納を閉じ `PostRun` へ

**これが `shiftPalResiduesAlongRun` と `cycleOracle` の共通の底の最後。**

## 2026-09-19 n185: `PostRun` / `RestartS2` の地図（`readiness` 部分系、最深部）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n184 で `StageEntryC` を修理したので、次の底は `RdPaced` の producer
`CloseoutPreload11.readyClosure_S2` が取る `PostRun` ＋ `RestartS2`。探した結果:

* `PostRun`（`CloseoutPreload8:253`）の変種の鎖は揃っている
  （`postRunP_of_postRun` / `postRunC_of_postRunP` / `postRunPh_of_postRunP` /
  `postRunC_of_postRunPh` / `postRunC'_of_double_leg`）が、**全部「変種 → 変種」**
* 帰納段 `CloseoutPreload35.postRunF_step` と脚のデータ `CloseoutPreload36.StageLegs` はある
* **基底が無い**（`PostRun*` を仮説なしで出す定理は 1 本も無い）
* `RestartS2`（`CloseoutPreload11:320`）も **producer 無し**
* `CloseoutPreload` は 1〜41 の 41 ファイル。**プロジェクト最深部**

`CloseoutPreload41` の冒頭は replay 半分の所見で、まだ基底に到達していない。

**次**: `postRunF_step` ＋ `StageLegs` の帰納が何で止まっているかを
`CloseoutPreload35` / `36` の冒頭で確認する。

### いまの全体像（公理 3 本）

| 公理 | 底 | 状態 |
|---|---|---|
| `obligation_shiftPalResiduesAlongRun` | found 経路 → `StageEntryC`（**修理済み n184**）→ `RdPaced` → `PostRun` ＋ `RestartS2` | 基底待ち |
| `obligation_cycleOracle` | 同上（底を共有、n176） | 同上 |
| `obligation_localRealization` | run 機構が fairness を捨てている（n174）。`Fair` の実質 2 場には witness あり（n172）／`keepsSearchCursor` は定理で無償化（n173） | 別系統 |

## 2026-09-19 n184: **`StageEntryC` の偽の場を修理した**（置換先は既に存在していた）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n181 で反証した `StageEntryC.fuel` を差し替えた:

    -  fuel : ReadyFuel   (searchLens.get r) (headRank r.right * 2048 + c.clock) (headRank r.right)
    +  fuel : ReadyPacedS (searchLens.get r) (headRank r.right * 2048 + c.clock) (2048 - c.clock)

そして `reachAtC3_of_crossF_C` の中身を
`CloseoutReportCase.reachAtC3_of_crossF` から
**`CloseoutReadyStage.reachAtC3_of_crossS`** に向け直した。

### 新しい定理はゼロ本（4 回連続）

`reachAtC3_of_crossS`（`CloseoutReadyStage:945`）と `reachAtC3_of_target_matchS`（`:841`）は
**既に書かれていた**。`CloseoutReadyStage` の冒頭 docstring が
「§5–§6 re-prove … `reachAtC3_of_crossF` on `ReadyPacedS`」と書いていて、
**それは計画ではなく完了報告だった**（宣言の存在を `grep "^theorem"` で確認済み）。

`.fuel` の消費者は `CloseoutContracts:90` の **1 箇所だけ**だったので、
差し替えは 3 行（場の型・呼び先・import）で済んだ。

### スタック管理の効果（コウタの「stackで管理はよかったんかも」への答え）

| n | 出来事 | 新規に書いた定理 |
|---|---|---|
| n175 | **公理 4 → 3** | **0** |
| n177 | `ReplayStage` が捨てられていたのを発見・修理 | 0 |
| n181 | `StageEntryC.fuel` を反証 | 0（証人は全部既存） |
| n184 | `reachAtC3_of_crossS` が既にあった | 0 |

その前（n148〜n164）は **44 本書いて計器は 1 本も動かなかった**。
`PROOF_STACK.md` に「**書く前に探す**」を規律として書いたのが転換点。

**ただし「終わりが見えた」とはまだ書かない。** 見えてきたのは残り作業の形であって、
計器は 3 本のまま。

### 残り

| 公理 | 底 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` ＋ `obligation_cycleOracle` | found 経路の入口 `StageEntryC` が**修理できた**ので、次は `RdPaced`/`ReadyPacedS` の producer。`CloseoutPreload11.readyClosure_S2` の底は `PostRun` ＋ `RestartS2` |
| `obligation_localRealization` | run 機構が fairness を捨てている（n174）。`Fair` の実質 2 場には witness あり（n172） |

## 2026-09-19 n183: `ReadyFuel` の API 全体に `ReadyPacedS` の双子がある（切り直しは機械的）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n182 の置換表を一次情報で確認したら、`CloseoutReadyStage` に対応物が**全部**そろっていた
（`_ready` `_mono` `_effect_false` `_effect_true` `_restarted` `_watchSegE`）。

### なぜ `ReadyPacedS` は反証されないか（本質）

    ReadyFuel   v n K := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
    ReadyPacedS v n k := ∀ as, n ≤ as.length → PacedL 2048 k as  → SearchReadyS v as

* 第 2 指標が **マッチ予算 `K`（`headRank`＝入力長に比例）** から
  **クロック由来の slack `k`（`2048 ≤ c.clock + k`）** に変わった
* 結論が `SearchReadyB`（`DpSafeRem`＝残り全部）から
  `SearchReadyS`（`DpSafeStage`＝**stage で切った**）に変わった

**「債務 2 で入力長ぶんのマッチを払え」という要求が消えている。**
これが n181 の反証を受け付けない理由であり、
`CloseoutPreload11.readyClosure_S2` が実際に producer を出せている理由。

### 切り直しの残り作業（完全に特定済み、`PROOF_STACK.md` に手順）

1. `StageEntryC.fuel` → `RdPaced c r`（`StageEntryS`）
2. `CloseoutReportCase` の 2 定理を置換表で再証明
   （`readyPacedS_watchSegE` の結論は `∃ k'` で 1 段包んであるので `obtain` を 1 つ挟む）
3. `reachAtC3_of_crossF_C` と found 経路の入口を追従
4. producer は `readyClosure_S2`（底は `PostRun` ＋ `RestartS2`）

## 2026-09-19 n182: 切り直しの設計が確定（`ReadyFuel` → `ReadyClosure`、置換は 1:1）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n181 で `StageEntryC.fuel`（＝`ReadyFuel`）を反証したので、消費者が**実際に何を使って
いるか**を読んだ（`CloseoutReportCase:380-390`）:

    readyFuel_mono → readyFuel_watchSegE → readyFuel_ready → SearchReady (searchLens.get s1)

**取り出しているのは `SearchReady` だけ。** `ReadyFuel` は「区間に沿って `SearchReady` を
運ぶ乗り物」で、その乗り物が偽だった。**正しい乗り物は既にある**——
`GalilReplaySpan.ReadyClosure:5621`:

    ready   : ∀ c s, Rd c s → SearchReady (searchLens.get s)
    seg     : ∀ es c c' s t, WatchSegE … → t.chain = .idle → Rd c s → Rd c' t
    restart : ∀ c u Rad last, … → Restarted … → StageEntry … → Rd c u

`readyFuel_watchSegE`（`CloseoutReportCase:87`）と `ReadyClosure.seg` は**仮説の形が
そのまま同じ**（`WatchSegE` ＋ `t.chain = idle`）。置換は 1:1 で、`ReadyClosure` 側は
燃料の算術が無いぶん**簡単**。

| 旧（偽） | 新 |
|---|---|
| `ReadyFuel … (headRank …)` | `Rd c r` |
| `readyFuel_watchSegE` / `_ready` / `_restarted` | `hcl.seg` / `hcl.ready` / `hcl.restart` |
| `readyFuel_mono` | **不要** |

### 手順（`PROOF_STACK.md` に記録）

1. `StageEntryC` → `StageEntryS := InvLPS ∧ Rd c r`
2. `CloseoutReportCase` の 2 定理を新通貨で再証明
3. `reachAtC3_of_crossF_C` を追従
4. found 経路の入口の `StageEntryC` を差し替え
5. `Rd := RdPaced` なら `CloseoutPreload11.readyClosure_S2` が producer。
   その底は `PostRun` ＋ `RestartS2`（次の的）

**これは (A)（弱化）ではなく偽の契約の修理。** `StageEntryC` を要求していた定理は
全部「空虚に真」なだけで使えない状態だった。

## 2026-09-19 n181: **`ReadyFuel` を機械検査で反証した** — `StageEntryC` は切り直しが要る

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`PalPeg/ReadyFuelRefute.lean`（新規、1 定理、標準 3 公理のみ）:

    not_readyFuel_v0 (n : ℕ) (hn : n ≤ paced.length) :
      ¬ GalilSegmentConstructB.ReadyFuel v0 n (paced.count true)

`v0` は restart 直後の探索（`search = begin reset reset`、`Canonical`・`0 ≤ value`・
`StageEntry 0 reset` がすべて成立）。`paced` は `CloseoutRunEntriesPaced` の
`advances 2048 2048 (av.map (·, true))`。

**証人は 1 つも新規に作っていない。** `CloseoutRunEntriesPaced` の
`v0` / `paced_shape` / `step1`〜`step8` / `p7_not_run` / `p8_run` / `p8_debt` / `rest_count` を
そのまま使った。`K` を `paced` 自身のマッチ数に取ったので数え上げも不要（`le_rfl`）。

### 帰結: `StageEntryC.fuel` は偽（もう「疑い」ではない）

    StageEntryC.fuel : ReadyFuel (searchLens.get r) (headRank r.right * 2048 + c.clock)
                                 (headRank r.right)

`readyFuel_mono` は `K' ≤ K` で弱くなる向きなので、`paced.count true`（= 3）以上の `K` では
**すべて偽**。`headRank p = 2 * (p.head.right.length + p.head.incoming.length) + …`
（`GalilLeafEnds:66`）は入力長に比例するので、数文字の入力で 3 を超える。

**`StageEntryC` を要求する found 経路の入口
（`CloseoutPrepInputs3.prepInputs3_of_found_or_later`）は、この契約では閉じない。**

### 切り直しの形（一次情報が指している先）

正しい通貨は `CloseoutReadyStage.RunEntriesS`（`RunEntryS` が `DpSafeRem` ではなく
**`DpSafeStage`**——stage の終わりで切った版を使う、`:318`）。
`CloseoutPreload11.runEntriesS_of_restartS2:327` が既にそれを出している
（`Restarted` ＋ `StageEntry` ＋ `CentreLongAt` ＋ `DepthAt` ＋ `PostRun` から、
条件は `D + dpEvents(…) ≤ as.length` ＋ `PacedL 2048 0 as`）。

### 今日の「形式化のミスを疑う」の 4 件目

| # | 場所 | 中身 |
|---|---|---|
| 1 | `localRealization` | `Trace`/`Steps`/`StepsAll` が fairness を捨てている（n174） |
| 2 | `PackRunRMW` | `ReplayStage` を `hI.1` で捨てていた（n177、**直した**） |
| 3 | `ReadyFuel` の素朴形 | 2 つとも既に反証済みだった（n178） |
| 4 | `StageEntryC.fuel` | **反証した**（n181） |

## 2026-09-19 n180: **`StageEntryC.fuel` は偽の疑いが濃い**（`REFUTED` とは書かない）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

`ReadyFuel` を一次情報で展開した:

    ReadyFuel v n K   := ∀ as, n ≤ as.length → as.count true ≤ K → SearchReadyB v as
    SearchReadyB v as := ReadyRem v as ∧ RunEntriesAll as v
    RunEntry … as     := … → v'.mode = .run → DpSafeRem v' as
    DpSafeRem v as    := ∃ … s0 bs, … ∧ ((bs ++ as).count true : ℤ) ≤ value s0.debt ∧ …

**`.run` 入口の債務が以後のマッチを全部払えと要求している。**
`StageEntryC.fuel`（`CloseoutContracts:68`）の `K` は `headRank r.right`（右ヘッドの残り段数）。
一方 `CloseoutRunEntriesPaced` の監査が確定させた `.run` 入口の債務は **2**
（`initialDebt reset = reset` ＋ grow tick 1 回の `+2`）。

**`headRank ≥ 3` になる入力で `StageEntryC.fuel` は成り立たないはず。**
`RunEntriesAtBegin` / `RunEntriesPaced 2048` が偽である理由と同型で、両方とも機械検査済み。

**`REFUTED` とは書かない**——`StageEntryC.fuel` について `False` を導く機械検査済みの
定理はまだ無い。

### n176 の見立てを訂正する

n176 で「残る差は `ReadyFuel` 1 つ」と書いたが、**埋めるべき穴ではなく偽の契約である
可能性が高い**。found 経路の入口 `prepInputs3_of_found_or_later` が `StageEntryC` を取って
いる以上、そこも切り直しが要る。

正しい通貨は `RunEntriesS`（`CloseoutReadyStage:444`、`DpSafeStage` で**stage で切った**版）で、
`CloseoutPreload11.runEntriesS_of_restartS2` が既にそれを出している。

### ついでの発見

`GalilLeafPres.RunEntriesAll` と `GalilReplaySpan.RunEntriesAllD` は**同じ定義の重複**。
`ReadyFuelD` の docstring も「`GalilSegmentConstructB.ReadyFuel`, restated」。
通貨は実質 2 つ（`…All` 系と `…S` 系）。

## 2026-09-19 n178: `ReadyFuel` の素朴な形は 2 つとも機械検査で偽（探して助かった）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

n177 で `StageEntryC = InvLPS ＋ ReadyFuel` の `InvLPS` 側を無償にしたので、
残る `ReadyFuel` を攻めようとした。**書く前に producer を探したら、両方偽だった。**

| 候補 | 状態 |
|---|---|
| `GalilReplaySpan.RunEntriesAtBegin` | **偽**（`CloseoutReadinessAudit.not_runEntriesAtBegin`） |
| `GalilReplaySpan.RunEntriesPaced 2048` | **偽**（`CloseoutRunEntriesPaced`） |

`readyFuel_of_stage`（`GalilReplaySpan:3764`）は `ReplayStage` ＋ `RunEntriesAtBegin` から
任意の `n K` で `ReadyFuelD` を出すが、第 2 入力が偽なので使えない。

理由（一次情報）: `RunEntriesAllD` は `.run` 入口で残り全部に `DpSafeRem` を要求し、
`DpSafeRem v as → as.count true ≤ value v.debt`。**固定の債務でいくらでも長い tail を
払え**と言っている。pacing は比較の頻度を縛るが回数は縛らない。

**正しい形**は同ファイルが明記している `RunEntriesPacedS`——
イベント列を stage の終わりで切り、`count true ≤ stageDebt Rad` を側条件に足す。
`stageDebt Rad k = 2 * max k 1 - Rad`（`CloseoutPreload11:109`）で、
`CloseoutPreload11` が `stageDebt` ＋ `stageCredit` の会計を展開している。

**これが `hpres` の正体で、残り 3 本のうち 2 本が共有する底の最後の 1 つ。**

### この session の (C)/(A) の記録

| n | 操作 | 効果 |
|---|---|---|
| n145 | 6 → 4 に戻した | 本数 |
| n175 | trace 形を run 形から導出 | **4 → 3**（新規定理ゼロ） |
| n177 | `PackRunRMW` を `InvLPS` に上げた | 公理の文が弱くなった（`ReplayStage` は捨てられていた） |
| n178 | `ReadyFuel` の偽の形 2 つを確認 | **無駄な証明を回避** |

## 2026-09-19 n177: `obligation_shiftPalResiduesAlongRun` の仮説を `InvLPC` → `InvLPS` に強めた（公理は弱くなる）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 3。
無条件 PAL は未完、§10.5 は未達。**

### 見つけたもの: `ReplayStage` は欠けていたのではなく**捨てられていた**

`CloseoutOracleW.h_oracleIMW_of_MC3_W:148` は `hI : InvLPS` を持っているのに
**`hI.1`（`InvLPC` の部分）だけ**を `PackRunRMW` に渡していた。
`InvLPS = InvLPC ∧ ReplayStage`（`GalilInvPlus3:86`）なので、
**`ReplayStage` はその場で無償**だった。CLAUDE.md §3 が `hstage` を「残り葉」として
挙げていたが、この経路では既に手元にある。

### やったこと（(A) の操作）

`PackRunRMW` の origin 仮説を `InvLPC` → `InvLPS` に上げ、下流に伝播:

| ファイル | 変更 |
|---|---|
| `CloseoutOracleW` | `PackRunRMW` の def、`reachAtIMW_of_reachAtC3R_W`、`cycleOutIMW_of_cycleOutMC3R_W`、`h_oracleIMW_of_MC3_W`（`hI.1` → `hI`）、`packRunR_MW` の本体 |
| `CloseoutMarksPack` | 2 つの producer の本体（`hIC := hInvLPS.1`）＋ `packRunR_MW_marksFree` の `hShiftPalAlongRun` 仮説 |
| `CloseoutFinalBranch` | `given_scanLandingObligations` の `hShiftPalAlongRun` 仮説 |
| `PalInPegUnconditional` | 公理と定理の仮説 |

trace 形の導出（n175）も `st 1` で `InvLPS` が要るようになったが、
**`CloseoutFoundRoutes.replayStage_of_inv` が `Inv` から無条件で `ReplayStage` を出す**ので
`inv_of_boot_tick` の `hInv` からタダ。

### なぜこれが前進か

`StageEntryC = InvLPS ＋ ReadyFuel`（`CloseoutContracts:65`）。
found 経路の入口（`prepInputs3_of_found_or_later`）は `StageEntryC` を要求する。
**`InvLPS` が手に入ったので、残る差は `ReadyFuel` 1 つだけ**になった。
`SegReachedW` の方は `GalilInvPlus.segment_of_invLP` ＋ 既に閉じている `hlive`/`hends` で出る。

公理は 3 本のまま（本数は動かないが、`obligation_shiftPalResiduesAlongRun` の文は
**弱くなった**——より強い仮説を取るようになった）。

## 2026-09-19 n175: **計器が動いた。公理 4 → 3。**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット更新。
公理は 3。無条件 PAL は未完、§10.5 は未達。**

    'PalPeg.PalInPeg.unconditional' depends on axioms: [propext,
     Classical.choice,
     Quot.sound,
     PalPeg.PalInPeg.obligation_cycleOracle,
     PalPeg.PalInPeg.obligation_localRealization,
     PalPeg.PalInPeg.obligation_shiftPalResiduesAlongRun]

### 何をしたか: **trace 形を run 形から導いた**

`obligation_shiftPalResiduesAlongRun`（`InvLPC` 起点の `Steps` 上）と
`obligation_shiftPalResiduesAlongTrace`（`PreTraceIMW` の trace 上、`1 ≤ j ≤ Tc`）は
**中身が同じ 3 残差**だった。trace は `st 0 = boot w` から始まるので、
**`st 1` で `InvLPC` が立てば trace 形は run 形の特殊化**になる。

`st 1` の `InvLPC` は**既存部品だけ**で組めた（`BranchSupply.cpack_alongTrace` と同じ recipe）:

| 部品 | 役割 |
|---|---|
| `GalilTrailFront.inv_of_boot_tick` | **与えられた** boot tick の着地で `Inv` ＋ `SpanRep`（存在形の `invLPC_init` ではなく、trace 自身の `st 1` について言う） |
| `PreTrace.trace.good 1` | `OutputRel` |
| `GalilOracleDischarge.invS_of_inv` ＋ 上 | `InvL` |
| `GalilGlueBLeaves.entryCounters_of_inv` | `EntryCounters` |
| `GalilOracleMC2.invLPC_of_boot` | `InvLP2` ＋ `CentreRep` → `InvLPC` |
| `Inv.rest` ＋ `GalilInvPlus2.centreRep_of_restarted` | `CentreRep` |
| `GalilTrailFront.steps_between` | `st 1` から `st j` への `Steps`（`1 ≤ j ≤ Tc`） |

`w = []` のときは `Tc 0 = 0`（`PreTrace.tc0`）なので 3 つとも空虚。

### 新しい定理はゼロ

**1 本も新規に書いていない。**`PalInPegUnconditional.lean` の中で既存部品を繋いだだけ
（約 40 行）。コウタの「定理ふえすぎてへん？」の直後にこれが出たのは偶然ではなく、
**既存部品を探す姿勢に切り替えたから**見つかった。

### 残り 3 本

| 公理 | 内容 |
|---|---|
| `obligation_shiftPalResiduesAlongRun` | `H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `FreshShiftLedger`（run 形。**trace 形はこれに吸収された**） |
| `obligation_cycleOracle` | `CycleOracleMC3` |
| `obligation_localRealization` | `H_realizeLIMW'`（局所実現。壁は n174 の「run 機構が fairness を捨てている」） |

## 2026-09-19 n174: **壁の正体 — run 機構が全階層で fairness を捨てている**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

コウタの「壁にあたったら、形式化のミスを疑う」に従って `localRealization` の壁を掘った。

### 壁

    structure Trace (F) (delay) (Q) (st) (e) : Prop where     -- GalilCheckpoints:46
      tick : ∀ i, i < e → Tick F delay (st i) (st (i+1))
      good : ∀ i, i ≤ e → Q (st i)

**`Tick` しか記録しない。`Fair` は 1 場もない。** `Steps` / `StepsAll` も同じ。
`PreTrace.trace` はこの `Trace` なので、trace は非決定的な tick の列でしかない。

一方 `LocalSysConcrete.Realizes` は「局所 step **関数** `f` が trace の次状態に着地する」
を要求する。**決定的な関数に、非決定的な trace と一致せよと言っている。**
だから producer が原理的に作れない。コウタの見立て通り、これは形式化のミス。

### 直すのに要るもの（3 択、blast radius 付き）

| 案 | 内容 | 影響 |
|---|---|---|
| **(1) run 機構を装飾** | `Trace` / `Steps` / `StepsAll` に fair 版を足し、`checkpoints_cost_upto1` を fair 版にする | `Trace` 220 箇所・`Steps` は更に多い。**最大** |
| **(2) 公理を上げる** | `obligation_cycleOracle` を「fair な pre-trace が存在する」形に差し替える | `CycleOracleMC3` は `h_oracleIMW_of_MC3_W` でも使うので、そちらが別に必要になり**本数が増える恐れ** |
| **(3) `PreTraceB` に `fair` 場を足し、`preTraceB_exists` と `checkpoints_cost_upto1` だけを fair 化** | 中間。`stepsAll_fn`（`GalilCheckpoints:51`）の fair 版が要る | `PreTraceB` の producer は 3〜4 箇所（実測済み）。**最小** |

**推奨は (3)。** 理由: `Trace` は 2 場の単純な構造体で、fair 版は
`∀ i, i < e → Fair entry delay (st i) (st (i+1))` を並べるだけ。
`stepsAll_fn` は `StepsAll → ∃ g, Trace` なので、fair 版 `StepsAll` から fair 版 `Trace` へ
同じ帰納法で通る。`checkpoints_cost_upto1` は区間を貼り合わせるだけなので
fairness は連言で運べる。

### ただし (3) でも 4 → 3 にはならない（正直に）

`Fair` が閉じるのは `Realizes` の**決定性の半分**。
**局所 step の構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc`）は別の仕事で、
`LocalTick2.commitReplay` の `LocalTick1.Inv` 保存補題が起点
（`LocalTick2.lean` には `Inv` に関する補題が**1 本もない**——実測）。

### この session でやったこと（計器は 4 のまま）

* 公理 6 → 4 に戻した（n145）。以後増やしていない
* `PalPeg/RoundHistory.lean` 35 宣言で `H_readsShift` を run 全点で出す機械を完成
  （44 まで増やして 9 本削った——うち 4 本は既存の再発明）
* `Fair` の 3 場の内訳を割り、第 3 場が `Tick` からタダであることを**定理で**証明（n173）
* CLAUDE.md の古い記述を 1 箇所訂正（`initVM`/`replayStartVM` の `periodOnly`/`walker`）
* 自分の嘘 2 件を訂正、`sorry` を書きかけて止めたのを記録

## 2026-09-19 n173: `Fair` の第 3 場が `Tick` からタダであることを**定理で**示した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`GalilTickFair.keepsSearchCursor_of_tick`（標準 3 公理のみ）:

    Tick (galilFrameS (sharedC onLetter leftFirst centre place entry) q first) delay ⟨c, s⟩ y →
    (c.mode = Mode.init ∨ c.mode = Mode.replayStart) →
      y.vm.periodOnly = s.periodOnly ∧ y.vm.walker = s.walker

`initVM`（`GalilScaffoldTopReplay:20`）と `replayStartVM`（`:33`）の定義そのものの
15 連言の最後 2 つが `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` なので、
`tick_init_cases` / `tick_replayStart_cases` で取り出すだけ。

**CLAUDE.md §2 の記述を散文でなく定理で直した。**
`Fair` の実質は 2 場（`restartFirst` ＋ `fallbackPlace`）で、どちらも witness がある
（`fair_restart` / `fallbackAt_walker_self`）。

**4 → 3 の道で「強めたオラクルが供給すべきもの」は 3 場から 2 場に減った。**
公理は 4 本のまま。

## 2026-09-19 n172: `Fair` は 3 場すべて witness がある——公理を強める根拠が立った

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`GalilTickFair` に 3 場ぶんの witness が**既に揃っている**（一次情報で確認）:

| `Fair` の場 | witness | 側条件 |
|---|---|---|
| `keepsSearchCursor` | `initVM_keeps_cursor:474` / `replayStartVM_keeps_cursor:486`。**さらに定義自体に入っている**ので `Tick` からタダ | なし |
| `fallbackPlace` | **`fallbackAt_walker_self:466`**——search 自身の walker に着地する fallback が満たす（`FppControl.beginFallback` の `walker := p`、`GalilScaffoldChainFallback:410`） | `(stream s.walker).length ≤ position s.right` |
| `restartFirst` | `fair_restart:454` | なし（guard 下で restart が存在する） |

**帰結: fair な run は存在し、`tick_fair_unique` でそれは一意。**
だから `obligation_cycleOracle` の文に「run は `Fair`」を入れるのは
**モデルの忠実性の要求**であって、無根拠な強化ではない。

### ただし 4 → 3 にはまだ足りない（正直に）

`Fair` が閉じるのは `Realizes` の**決定性の半分**（`H_scanDet` / `H_initFun` / `H_rsFun`）。
**局所側の構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc` ＋ `H_rewindWF` /
`H_chooseWF` ＋ fpp の 1 量子）は残る。`LocalRealizesScan` の冒頭が
「`LocalReplayParked.commitReplayParked` が `H_replayStartLoc` の意図された witness だが
`LocalTick2.commitReplay` に `LocalTick1.Inv` 保存の補題がまだ無い」と書いている。

**つまり `localRealization` を外すには局所 step の構成作業が必要で、
それは `Fair` とは別の仕事。** 公理は 4 本のまま。

### 2 本の筋の残りを並べる（両方とも「配線／構成」で、新しい数学ではない）

| 筋 | 残り | 規模の手がかり |
|---|---|---|
| `H_readsShift`（第 1 残差） | `first_round` の 30+ 仮説を run から供給 | CLAUDE.md §3 の found 経路（`hfound`/`hfoundBg`/`hfoundReplay`、「未着手、最大の残り」） |
| `obligation_localRealization` | `Fair` を trace に通す ＋ 局所 step 3 本の構成 | `LocalTick2.commitReplay` の `Inv` 保存補題が起点 |

## 2026-09-19 n171: **`Fair` の 3 場の内訳を割った——1 場はタダ、1 場は形式化のミス**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

`Fair`（`GalilTickFair:195`）は 3 場。4 → 3 の道でこれを供給しないといけないので、
1 場ずつ一次情報で測った。

| 場 | 状態 |
|---|---|
| `keepsSearchCursor` | **タダ**。`initVM`（`GalilScaffoldTopReplay:20`）と `replayStartVM`（`:33`）の定義の 15 連言の最後 2 つが `t.periodOnly = s.periodOnly ∧ t.walker = s.walker`。`tick_init_cases` / `tick_replayStart_cases` で取り出すだけ |
| `fallbackPlace` | `beginFallbackVM'`（`GalilScaffoldTopGuards:45`）が place `p` を「`(stream p).length ≤ position s.right`」だけで縛っている。**実機は search の walker から一意に計算する** → `t.fpp.walker = t.walker` を定義に足せば消える。**形式化のミス** |
| `restartFirst` | `restartGuardVM`（`GalilSharedFunctional:146`）が `chain = .broken w` を要求するので、**broken chain のない区間では空虚**。Scala は restart 優先（`ScaffoldGalil`） |

### CLAUDE.md を訂正した

§2 の「(e) `beginFallbackVM'`（着地場所）、`initVM`/`replayStartVM`（`periodOnly`, `walker`
自由）が非関数的」は**古い**。`initVM`/`replayStartVM` は既に両方を固定している。
**この誤った記述を信じて「fair を供給するのは 3 場ぶん」と見積もっていた。**

### 帰結（4 → 3 の道の見積もり改訂）

供給すべきは実質 2 場、しかもうち 1 場（`fallbackPlace`）は
**`beginFallbackVM'` の定義に 1 連言足せば消える**。
残るのは `restartFirst` だけで、それは broken chain のある区間に限られる。

**「Fair を通すのは大工事」という見積もりは過大だった。**

## 2026-09-19 n170: **コウタの「定理ふえすぎてへん？」に答えて 44 → 35 に削った**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### 答え: 増えすぎていた。9 本は要らなかった

44 宣言足して**計器は 1 本も動いていない**。プロジェクトの基準ではこれは足場を積んだだけ。
使用箇所を実測して 9 本削った。

**参照ゼロ（5 本）**:

| 消したもの | 理由 |
|---|---|
| `watch_eq_of_mismatch_lagZero` | `ChainStep` 版に置き換わったのに両方残していた |
| `outer_eq_of_false` | 上の唯一の消費者が死んで連鎖 |
| `chain_shift_period_focus` | 「`hprediction` に要るかも」で**推測で**足したが要らなかった |
| `h_readsShift_of_run` | `shiftPhaseHistory_readsShift` に置き換わった |
| `chainShiftRun_of_steps` | carrier が tick ごとに運ぶ方式にしたので不要 |

**既存の再発明（4 本）**——これが一番痛い:

| 消した自作 | 既にあったもの |
|---|---|
| `positive_false_of_zero` | `GalilMismatchCaught.positive_false_of_zero:67`（**文言まで同一**） |
| `internal_eq_of_lagZero` | `CloseoutWatchRound4.internal_eq_of_zero:240` |
| `chainStep_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainStep_watch_of_lagZero:91` |
| `chainTick_false_watch_eq_of_lagZero` | `CloseoutMismatchCompare.chainTick_false_idle:46` |

### さらに: `CloseoutMismatchCompare` を先に読むべきだった

あのファイルは**不一致比較の構成を全部持っている**:

    chainTick_false_idle / compare_mismatch_of_lagZero / compare_mismatch_of_round
    chainStep_watch_of_lagZero / compare_chain_of_mismatch / beginShift_of_guard
    shiftAtMismatchM_of_round

とくに `compare_chain_of_mismatch:99` は「lag ゼロの不一致比較で
`vs.chain = .watch w` ∧ `vs.left = left s.left` ∧ `vs.right = right s.right`」を
**まとめて**出す——ウチが `shiftPhaseHistory_of_scanShift` で苦労して導いた 3 事実そのもの。
**CLAUDE.md の「既にあるものを探す」を守れていなかった。**

### 教訓（`PROOF_STACK.md` に追記）

新しい補題を書く前に、**扱う概念の名前で `grep -n "^theorem"` を関連ファイルに掛ける**。
とくに `Closeout*` は同じ問題を既に扱っている可能性が高い。
今回は `CloseoutMismatchCompare` / `CloseoutWatchRound4` / `GalilMismatchCaught` の 3 本を
先に読めば 4 本書かずに済んだ。

## 2026-09-19 n169: `Fair` が閉じるのは「決定性の半分」——残るのは局所側の構成

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

n168 の段取り 4 を一次情報で検証した。`LocalRealizesScan` の残り義務:

| mode | 決定性の半分 | 局所の半分 |
|---|---|---|
| `rewind` / `choose` | **閉**（`tick_det_rewind` / `tick_det_choose`） | `H_rewindWF` / `H_chooseWF` |
| `init` | `H_initFun` | `H_initLoc` |
| `replayStart` | `H_rsFun` | `H_replayStartLoc` |
| `scan` | **`H_scanDet`** | **`H_scanLoc`** |

`PalPeg/GalilTickFair.lean` に**そのまま合う 3 本が証明済み**:

    tick_fair_scan_unique        (:308)
    tick_fair_init_unique        (:381)
    tick_fair_replayStart_unique (:400)

どれも `hm : c.mode = …` ＋ 両 tick の `Fair` から `y₁ = y₂` を出す。

**結論: `Fair` は決定性の半分を閉じる。そこが「原理的に作れない」部分だった。**
残るのは局所側の**構成**（`H_scanLoc` / `H_initLoc` / `H_replayStartLoc` ＋
`H_rewindWF` / `H_chooseWF` ＋ fpp の 1 量子）で、不可能ではない。

`scan` の非決定性の原因も特定済み: `Tick.restart` が 5 つの scan 構成子と競合すること
（`Fair.restartFirst` が潰す）と `SafeQuanta` / `chainAt` が関係であること
（`GalilTickDet.safeQuanta_unique` / `chainAt_unique` が潰す）。**どちらも `Fair` 側で済んでいる。**

### この session の総括（計器は動いていない）

* 公理 **4 本**（n132 で 6 に増やしたのを n145 で 4 に戻した。以後増やしていない）
* 新規 `PalPeg/RoundHistory.lean` **44 宣言**——`H_readsShift` を run 全点で出す機械が完成
  （残りは `first_round` の配線＝ found 経路）
* `obligation_localRealization` の診断: `PreTrace` が `Fair` を記録していないので
  決定的な局所 step に非決定的な trace と一致せよと要求していた。
  `Fair` は証明済みだが `Local*` で未使用
* trace の出どころは `obligation_cycleOracle` なので、その文に `Fair` を入れれば
  決定性の半分が閉じる（**4 → 3 の道**）
* 自分の嘘 2 件を訂正（「残差化で弱くなった」は嘘 / build 通知の誤読）
* `sorry` を書きかけて実行前に止めた

## 2026-09-19 n168: **trace の出どころは `obligation_cycleOracle` — 4 → 3 の道が見えた**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`preTraceB_exists`（`GalilFinalBaseNeed:193`）を一次情報で読んだ。trace は

    hor : CycleOracleMC (PofC centre place entry w) q first w
    → checkpoints_cost_upto1 … hor …
    → ⟨st, Tc, …⟩

で作られている。**trace の tick 列は `obligation_cycleOracle`（4 本のうちの 1 本）が
供給する run そのもの。**

### 帰結: 1 本の文を強めて 1 本を丸ごと消せる

| 操作 | 効果 |
|---|---|
| `obligation_cycleOracle` の文に「run の各 tick は `Fair`」を入れる | 1 本の中身が強くなる |
| `obligation_localRealization` が**公理から外れる** | **本数 4 → 3** |

**これは (C)（本数が減る操作）。** 強める側は妥当: `Fair` は Scala の優先順位と固定値を
表すもの（CLAUDE.md §2）なので、**実機の run は定義上 `Fair`**。
オラクルの仕事は run を提示することなので、提示する run が fair であることは
モデルの忠実性の要求そのもの。

### 段取り（`PROOF_STACK.md` に記録）

1. `PreTraceB` に `fair` 場を足す
2. `preTraceB_exists` の `hor` を `Fair` 版オラクルに差し替え、`checkpoints_cost_upto1` から運ぶ
3. `obligation_cycleOracle` の文に `Fair` を追加
4. `Realizes` の scan / init / replayStart を `tick_fair_unique` で閉じる
5. `H_realizeLIMW'` の `∃ … L` を構成して `obligation_localRealization` を**外す**

**未検証**: 4 が本当に閉じるか。CLAUDE.md §1 は「phase 側は閉、scan/init/replayStart が
非決定性で閉じない」と書いているので `Fair` を入れれば閉じる見込みだが、実証はまだ。

## 2026-09-19 n167: `localRealization` に producer がいない理由の診断

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

コウタの指摘「localRealization も一見難しく見えてるだけ。producer がいないってことは
モデル化を何か間違ってる」を追った。

### 確認できた事実（一次情報）

1. `Realizes`（`LocalSysConcrete:285`）は「mode の局所 step **関数** `f` が
   trace の次状態に着地する」を要求する
2. trace `stOf` は `PreTrace` の `trace` 場（`Tick (st i) (st (i+1))`）でしか縛られていない。
   **`Tick` は非決定的**（`GalilTickDet`、CLAUDE.md §2 に 5 分岐）
3. `Fair` を足すと一意: **`GalilTickFair.tick_fair_unique`（`:429`）は証明済み**、
   docstring は「with no reachability pack at all」
4. **`Fair` は `PalPeg/Local*.lean` のどこでも使われていない**
   （`grep -rln "Fair" PalPeg/Local*.lean` が空）

### 推論（未検証・機械検査した反証は無い）

`Realizes` は「決定的な関数に、非決定的な trace と一致せよ」と要求していることになり、
producer が原理的に作れない。**直し方の候補**: `PreTrace`（または `PreTraceB` / `InvC`）に
`Fair` の場を足す。`PreTraceIMW` は上位で**仮説**として現れるので、
場を足すと義務は**弱くなる**（(A) の操作）。

構成側（実 run から trace を作るところ）が `Fair` を供給できるかは別途確認が必要。
CLAUDE.md §2 自身が「構成側の witness と局所 step が `Fair` を満たすことを別途確認」と
書いている——つまり**この作業は当初から予定されていて、未着手のまま**だった。

### 2 本の筋の比較（どちらも未着手部分がある）

| 筋 | 状態 |
|---|---|
| `H_readsShift`（第 1 残差） | **部品は全部揃った**（`RoundHistory` 44 宣言）。残りは `first_round` の 30+ 仮説を run から供給する配線＝ CLAUDE.md §3 の found 経路（「未着手、最大の残り」） |
| `obligation_localRealization` | 診断は付いた（上）。`PreTrace` に `Fair` を足す構造変更＋構成側の `Fair` 供給 |

## 2026-09-19 n166: **自分が撒いた過剰量化を直した**（`roundCarrier_tick` の側条件）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

n164 で書いた `roundCarrier_tick` の側条件が**過剰量化していた**。
CLAUDE.md の「消費者がその分岐で何を要求しているかを読む」を自分のコードで破っていた。

| 側条件 | 旧（過剰） | 新（使う分岐だけ） |
|---|---|---|
| `singlePositive cycle = false` | 全 scan 点 | scan → **scan** の枝だけ |
| `canRight right` | 全 scan 点 | scan → **shift** の枝だけ |
| chain が watch | 全 target scan 点 | scan → **scan** の枝だけ |
| `replaying = false` | 全点 | **scan** 点だけ |
| `CopyIdle` | 全点 | **shift** 点だけ |

とくに 1 行目は**ラウンド終端で偽**になる: `shiftGuardVM` は `periodOnly` のとき
`singlePositive cycle = true` を要求するので、shift に入る点では周期が終端。
旧の形は「全 scan 点で周期が終端でない」と言っていたので、
**ラウンド境界を含む区間には適用できなかった**。

run 沿いの `hSide` も `∀ m z z', Steps … m x z → Tick … z z' → …` の形にして、
遷移先の mode で場合分けできるようにした。

**これは (A)（guard を狭める）の操作で、本物の弱化。** 公理はまだ 4 本。

## 2026-09-19 n165: 基底の橋（`first_round` の `Entry` → `OriginAt`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **44 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

* `periodLength_after_shift` — shift 後の watch の周期は shift の歩数。3 段:
  `chain_shift_periodLength`（公理ゼロ）→ `GalilChainCoupling.periodLength_consume`
  （`immediate` 1 手、側条件 `WatchBlock`）→
  **`CloseoutWatchRound45.period_of_beginShift`**（既存。`beginShiftVM h w` と
  `beginShiftVM'` の `h` が一致する）
* `originAt_of_firstShiftEntry` — `first_round` の `Entry` を `OriginAt` にする
  （`CloseoutOriginRounds.originAt_of_entry` ＋ 上の周期一致）

**これで `H_readsShift` の鎖は基底から run 全点まで部品が揃った。**

### 計器を動かすために残っていること（正直に）

`first_round` は仮説が 30 個以上ある（found 経路の全部）。それを run から供給するのが
CLAUDE.md §3 の `hfound` / `hfoundBg` / `hfoundReplay`——「**未着手、最大の残り**」と
自分で書いていた項目そのもの。`h_readsShift_alongSteps` の側条件も既存 pack から
出る見込みだが**未検証**。

**つまり `H_readsShift` は「部品は全部ある・配線が残っている」状態。**
公理はまだ 4 本。

## 2026-09-19 n164: **`H_readsShift` を run の全点で組めた**（`RoundHistory` 42 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PROOF_STACK.md` 手順 1〜11 が全部繋がった:

    scanShift_parts / shiftDone_parts  — Tick の場合分けをデータ抽出に閉じ込める
    roundCarrier_tick                  — 4 遷移を振り分けて carrier を 1 tick 運ぶ
    roundCarrier_of_steps              — run に沿って運ぶ
    h_readsShift_alongSteps            — run の全点で H_readsShift

`scanShift_parts` / `shiftDone_parts` は「scan→shift の tick は `scan_shift` だけ」
「shift→scan の tick は `shift_done` だけ」を 23 構成子の照合で示したもの。
行き先の control を一次情報（`GalilScaffoldTop:110-172`）で全部確認した:

| 構成子 | 行き先 mode |
|---|---|
| `scan_wait` / `scan_count` / `scan_match` / `restart` | source と同じ（scan） |
| `scan_shift` | `.shift` |
| `scan_fallback` | `.copy` |
| `shift_one` | source と同じ（shift） |
| `shift_done` | `.scan`（VM は不変） |

### 計器を動かすために残っていること

`h_readsShift_alongSteps` の 2 つの入力:

1. **起点の `RoundCarrier`** — scan 相なら `RoundHistory`（起点の `OriginAt` が要る）。
   chain 誕生直後は `OriginAt` がまだ無く、最初の shift で
   `GalilScaffoldTopFirstRound.first_round`（**無条件**）が `Entry` を出す。
   **ここが基底。**
2. **側条件** — 区間の全点が scan / shift 相 ∧ 非 replay ∧ `CopyIdle`、
   scan 点では周期が終端でない・右ヘッドが読める・chain が watch。
   これは既存の pack（`Extra7` / `AuxPack` / `LPackM`）から出る見込み（未検証）

## 2026-09-19 n163: 結合 carrier `RoundCarrier` と `H_readsShift` の取り出し

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **37 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

    RoundCarrier P q first delay w c s :=
      (c.mode = Mode.scan  → RoundHistory P q first delay w c s) ∧
      (c.mode = Mode.shift → ShiftPhaseHistory w s)

    h_readsShift_of_roundCarrier   : RoundCarrier … → H_readsShift w c s
    originShift_of_roundCarrier    : RoundCarrier … → OriginShift w c s

**これが目標の形**: `RoundCarrier` を run / trace の全点で持てれば
`obligation_shiftPalResidues*` の第 1 残差（`H_readsShift`）が公理から外れる。

### 途中で `sorry` を書きかけて止めた（記録）

tick 振り分けを書こうとして `| _ => sorry` を含むスクリプトを組み立てたが、
実行前に気づいて破棄した（スクリプトは `skip` を出力してファイルを書いていない）。
原因は `RoundHistory` の射影を `obtain ⟨wch, hwch⟩` で取ろうとしたこと——
実際は 12 成分の存在命題で、`onlyMatchedRun_of_roundHistory` を通さないといけない。
**急いで通すために `sorry` を置くのは禁止。** 確定できる分だけ入れた。

### 残り

1. `roundCarrier_tick` — 4 遷移を `Tick` の構成子で振り分ける。
   `scan_wait` / `scan_count` / `scan_match` は `roundHistory_tick`、
   `scan_shift` は `shiftPhaseHistory_of_scanShift`、
   `shift_one` は `shiftPhaseHistory_tick`、`shift_done` は `roundHistory_of_shiftDone`。
   各構成子の**行き先の control** を一次情報で確認してから書く（mode の判定に要る）
2. 基底 — `scan_fallback` / `restart` では carrier は原理的に保たれない。
   新しいラウンドの `OriginAt` は `first_round`（無条件）が出す

## 2026-09-19 n162: **ラウンドの 4 つの相遷移が全部揃った**（`RoundHistory` 34 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

| 遷移 | 定理 |
|---|---|
| scan → scan | `roundHistory_tick` |
| scan → shift（`scan_shift`） | **`shiftPhaseHistory_of_scanShift`（n162）** |
| shift → shift（`shift_one`） | `shiftPhaseHistory_tick` |
| shift → scan（`shift_done`） | `roundHistory_of_shiftDone` |

`scan_shift` 遷移の内訳（全部一次情報から）:

* `s'.chain = .watch wch` ← `ChainTick false x z` は `ChainStep x z`
  （`GalilScaffoldTopChainVM:92`）で `.watch` から出る構成子は `watchStep` だけ（`:66`）。
  lag ゼロなら `Internal` は恒等（`chainTick_false_watch_eq_of_lagZero`、n162）
* `singlePositive s1.cycle = true` ← guard の `if periodOnly then singlePositive cycle = true`
  節。`afterMismatch` は `cycle` / `periodOnly` を触らない（`afterMismatch_cycle` /
  `afterMismatch_periodOnly` はどちらも `rfl`）
* `hPredict` ← guard の `symbol …period.focus = read s'.right` ＋ `afterMismatch_right`
* `beginShiftVM (periodLength wch) wch …` ← `beginShiftVM'` の定義から（`w = wch` は chain で一意）
* 基底の `ChainShiftRun … 0 …` は `.stop`、frame は `(shiftLens.set_get s2).symm`

ついでに `MatchedRunSnoc.compare_mismatched_parts` の結論に
`vs.left` / `vs.right` / `ChainTick false t.chain vs.chain` を足した
（消費者がいなかったので破壊的変更なし）。

### 残り: 結合 carrier と run 沿いの帰納

    RoundCarrier P q first delay w c s :=
      (c.mode = Mode.scan  → RoundHistory P q first delay w c s) ∧
      (c.mode = Mode.shift → ShiftPhaseHistory w s)

* tick 保存は上の 4 遷移を `Tick` の構成子で振り分けるだけ
* **`H_readsShift` は scan 相では空虚**（guard が `mode = shift`）、
  shift 相で `remaining` が尽きた点は `shiftPhaseHistory_readsShift`
* **基底が残る**: `scan_fallback` で copy 相に落ちると chain が作り直されるので
  carrier は保たれない。そこは `GalilScaffoldTopFirstRound.first_round`（無条件）が
  新しい `OriginAt` を出す点。**ここが最後**

## 2026-09-19 n161: `shift_done` 遷移（`ShiftPhaseHistory` → `RoundHistory`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **31 宣言**。

`roundHistory_of_shiftDone`: shift 相が終わると次のラウンドの `RoundHistory` が立つ。
`shift_done` は VM を変えない（`GalilScaffoldTop:136`）のでこの状態がそのまま次の起点。
7 つの場の出どころ:

| 場 | 出どころ |
|---|---|
| `OriginAt w s` | `shiftPhaseHistory_originAt` |
| `s.periodOnly = true` | `beginShiftVM` が置いた値。`shiftLens` の外なので shift 相で不変 |
| `s.chain = .watch v` | `ShiftPhaseHistory` |
| `zero v.lag = true` | `chain_shift_lag`（`immediate` は lag を変えない） |
| `WatchBlock v` | `chain_shift_period` ＋ `onBlock_verifier_consume` |
| `Canonical s.radius` / `Canonical s.length` | `shift_run_canonical` |

そのために `RoundHistory` に `WatchBlock w₀` を、`ShiftPhaseHistory` に
`zero wch.lag = true` / `s2.periodOnly = true` / `Canonical s1.radius` を足した。

### 残り 1 個: `scan_shift` 遷移（`RoundHistory` → `ShiftPhaseHistory`）

tick が与えるもの（`GalilScaffoldTop:123`）: `hm` / `h`（available）/ `hc : clock = 1` /
`hcmp` / `hmt`（不一致）/ `hr : replaying = false` / `hg : P.shiftGuard s'` /
`hb : P.beginShift s' s''`。

`PofC` では `P.shiftGuard = shiftGuardVM`、`P.beginShift = beginShiftVM'`。
比較の分解は `MatchedRunSnoc.compare_mismatched_parts`。
必要な場はすべて `RoundHistory` の射影（`onlyMatchedRun_of_roundHistory`）と
guard から出る見込み。**これが繋がれば `H_readsShift` が run 全点で出る。**

## 2026-09-19 n160: shift 相の carrier（`ShiftPhaseHistory`）とその tick 保存

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は **30 宣言**（全部標準 3 公理以内、3 本は公理ゼロ）。

* `ShiftPhaseHistory w s` — `roundSeg_of_run` の仮説を束ねた shift 相の履歴
* `shiftPhaseHistory_originAt` — `remaining` が尽きた点で `OriginAt`（次ラウンドの起点）
* `shiftPhaseHistory_readsShift` — 同じ点で **`H_readsShift`**
* `shiftPhaseHistory_tick` — shift 相の 1 tick で伸びる

`RoundHistory` は `ScanSeg` を持つので scan 相しか覆わない。ラウンドは
scan 相 ＋ shift 相なので、**2 つの carrier の選言**を run に沿って運ぶ形になる。

### 残り（相の遷移 2 つ ＋ 結合 carrier）

| 遷移 | 要るもの |
|---|---|
| `scan_shift`（`RoundHistory` → `ShiftPhaseHistory`） | `hTerminal`（`scanSeg_only` の `periodOnly` ＋ guard）／`hCanRight`（`Extra7`）／`hPredict`（guard ＋ `watch_eq_of_mismatch_lagZero`）／`hLengthCanonical`（**済**）／`hRight`・`hLeft`（比較）／`hBeginShift`（`beginShiftVM'`）／**`WatchBlock w₀`（`RoundHistory` に足す必要がある）** |
| `shift_done`（`ShiftPhaseHistory` → `RoundHistory`） | `shiftPhaseHistory_originAt`（**済**）＋ `roundHistory_start` |

**`RoundHistory` に `WatchBlock w₀` を足すのが次の一手。**

## 2026-09-19 n159: **`H_readsShift` がラウンド起点の `OriginAt` から出る鎖が繋がった**

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器はまだ動いていない。**

`PalPeg/RoundHistory.lean` は 24 宣言。`PROOF_STACK.md` 手順 8・9・11 が済んだ。

    roundSeg_of_run        : RoundSeg w s₀ sEnd
    originAt_next_of_run   : OriginAt w sEnd          （手順 9）
    h_readsShift_of_run    : H_readsShift w c sEnd    （手順 11）

つまり **ラウンド起点の `OriginAt` ＋ そのラウンドの run の材料**から
`H_readsShift` が出る。全部標準 3 公理のみ。

`roundSeg_of_run` の第 1 節（`periodLength v = periodLength w₀`）は 3 段の合成:

* scan 相 → `periodLength_onlyMatchedRun`
* `immediate` 1 手 → `GalilChainCoupling.periodLength_consume`
  （側条件 `WatchBlock` も `periodLength_onlyMatchedRun` が返す）
* shift 相 → `chain_shift_periodLength`（公理ゼロ）

### 計器を動かすために残っていること

`H_readsShift` を **trace / run の全点で**得るには、`RoundHistory`（＝ラウンド起点の
`OriginAt`）を run に沿って引き継ぐ帰納が要る:

* 基底: chain 誕生時の `OriginAt` ← `GalilScaffoldTopFirstRound.first_round`（**無条件**）
* 帰納: `originAt_next_of_run`（**済**）でラウンドごとに引き継ぐ
* ラウンド境界の検出: run のどこが `scan_shift` かを特定する（`RoundHistory` の
  `hScanWatchAll` 側条件と `shift` 相の `hShiftAll` 側条件をどう供給するか）

**これが最後の壁。** 計器（`#print axioms`）はまだ 4 本。

## 2026-09-19 n158: **ラウンド 1 周を run から組めた**（`compareRounds_one_of_run`）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`PROOF_STACK.md` 手順 7 が済んだ。`PalPeg/RoundHistory.lean` は 21 宣言。

    compareRounds_one_of_run :
      OnlyMatchedRun (toOnly s₀ w₀) n (toOnly s1 wch) →
      singlePositive s1.cycle = true → canRight s1.right →
      read (right s1.right) = symbol wch…period.focus →
      Canonical s1.length →
      vs.right = right s1.right → vs.left = left s1.left →
      beginShiftVM (periodLength wch) wch (afterMismatch s1 vs vq) s2 →
      ChainShiftRun (shiftLens.get s2).shift (immediate wch) (shiftLens.get s2).cycle k
        (shiftLens.get sEnd).shift v (shiftLens.get sEnd).cycle →
      positive (shiftLens.get sEnd).shift.remaining = false →
      sEnd = shiftLens.set s2 (shiftLens.get sEnd) →
      sEnd.chain = ChainVM.watch v →
      CompareRounds (periodLength wch) (toOnly s₀ w₀) 1 (toOnly sEnd v)

**フレーム（`P` / `q` / `first` / `delay`）に依らない。** run から取り出した材料だけで閉じる。
`CompareRounds.next` の `lengthCounter` は `inc (inc s1.length)` に決まり、
`hlen` は `inc_canonical` 2 回、`hrun : ShiftRun` は `shiftRun_of_chain` でタダ、
手数 `k = periodLength wch` は `chainShiftRun_length_eq`、
末尾の射影の形は `toOnly_shiftEnd_eq`。

### 残り（`PROOF_STACK.md` 手順 8〜11）

8. `RoundSeg w s₀ sEnd` にする（第 1 節 `periodLength v = periodLength w₀` は
   `periodLength_onlyMatchedRun` ＋ `periodLength_consume` ＋ `chain_shift_periodLength` の合成）
9. `CloseoutRoundSeg.originAt_of_roundSeg` → 次のラウンド起点の `OriginAt`
10. `roundHistory_start` で次のラウンドの `RoundHistory`
11. `CloseoutReadsOrigin.originShift_of_roundSeg` → `OriginShift`
    → `h_readsShift_of_originShift` → **`H_readsShift`**

## 2026-09-19 n157: shift 末尾の射影の形も確定（`RoundHistory` 20 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`toOnly_shiftEnd_eq`（一発で通った）。`CompareRounds.next` の `rest` の始点は
`⟨t'.center, t'.left, right t.right, v, cycle, t'.radius⟩` という明示の組
（`GalilScaffoldChainReadOrigin:1008`）で、run から作るには `toOnly sEnd v` が
これに一致しないといけない。

一致の根拠（一次情報）:

* `toOnly s w = ⟨s.center, s.left, s.right, w, s.cycle, s.radius⟩`（`GalilScaffoldTopOnly:20`）
* `shiftLens.get` は `⟨⟨center, left, remaining, radius, length⟩, chain, cycle⟩` なので
  center / left / radius / cycle は `shiftLens` の中、**`right` は外**
* `right` は shift 相で不変（`shiftLens_frame_steps`）、shift 入口の値は
  比較の `vs.right = right s1.right`

**これで `PROOF_STACK.md` 手順 11 段の部品はすべて揃った（20 宣言）。**

## 2026-09-19 n156: `shift` の手数が初期値で決まることを証明（`RoundHistory` 19 宣言）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`chainShiftRun_length_eq`:

    a.remaining = ofNat h → ChainShiftRun a w cycle k b v finish →
    positive b.remaining = false → k = h

`CompareRounds.next` は shift 相をちょうど `h` 手として要求するのに、run からは
「shift mode に留まった手数 `k`」しか分からないので `k = h` が要る。
`GalilScaffoldTopInvariant.shift_run_remaining` は「ちょうど `h` 手なら尽きる」の向きだけで
**逆向きが無かった**ので作った。`shiftTick` は `remaining := dec s.remaining`
（`GalilScaffoldChainInputSupply:1442`）で、`ChainShiftRun.next` は
`positive s.remaining = true` を要求するから手数は初期値で一意。

### `PalPeg/RoundHistory.lean` の 19 宣言（全部標準 3 公理以内、うち 3 本は公理ゼロ）

| 群 | 宣言 |
|---|---|
| ラウンド履歴 | `RoundHistory` / `roundHistory_start` / `roundHistory_tick` / `roundHistory_of_steps` / `onlyMatchedRun_of_roundHistory` |
| shift 相の収集 | `chainShiftRun_snoc` / `chainShiftRun_snoc_shiftOne` / `chainShiftRun_tick` / `chainShiftRun_of_steps` / `chainShiftRun_length_eq` |
| period テープ | `chain_shift_period` / `chain_shift_periodLength` / `chain_shift_period_focus` / `periodLength_onlyMatchedRun` |
| 比較の watch | `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false` / `watch_eq_of_mismatch_lagZero` |
| 形の一致 | `shiftEntry_shape` / `shiftLens_frame_tick` / `shiftLens_frame_steps` |

**`PROOF_STACK.md` の手順 11 段に必要な部品は全部そろった。残るのは組み立てだけ。**

## 2026-09-19 n155: shift 入口の形が `round_next` の要求とぴったり一致することを確定

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`shiftEntry_shape`（`PalPeg/RoundHistory.lean`、18 宣言目）。一発で通った。

`round_next` と `CompareRounds.next` は shift 相の起点を
`⟨s1.center, left s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩` という
**明示の形**で要求する。これが run の実状態と一致することを一次情報で照合した:

* `ScanVM` は `left` / `right` / `chain` の 3 場だけ（`GalilScaffoldTopScan:26`）なので
  `scanLens.set` は center / radius / length を触らない
* `afterMismatch s vs vq = {searchLens.set (scanLens.set s vs) vq with radius := radiusAfter s}`
  （`GalilScaffoldTopSearch:52`）、`radiusAfter s = inc s.radius`（無条件）
* `beginShiftVM h w s t` は `remaining := ofNat h` / `length := inc (inc s.length)` /
  `chain := .watch (immediate w)` / `cycle := reset` を置く（`GalilScaffoldTopShiftCycle:23`）

**必要な側条件は比較の `vs.left = left s1.left` だけ。**
ついでに `(shiftLens.get s2).chain = .watch (immediate wch)` と
`(shiftLens.get s2).cycle = reset` も出るので、`chainShiftRun_of_steps` の基底
（`.stop`）がそのまま立つ。

## 2026-09-19 n154: 組み立てに足りない部品がゼロになった

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`shiftLens_frame_tick` / `shiftLens_frame_steps` を追加。
`shiftOne` は `Lens.rel`（`GalilScaffoldTopLens:28`：
`R (L.get s) (L.get t) ∧ t = L.set s (L.get t)`）なので、第 2 成分がちょうど
「lens の場以外は変わらない」。これを `Lens.set_set` で `Steps` に沿って合成した。
これが `round_next` の結論の形（`shiftLens.set s2 ⟨t', .watch v, cycle⟩`）に
run の状態を合わせるのに要る最後の部品だった。

**`PalPeg/RoundHistory.lean` は 17 宣言。全部標準 3 公理以内（3 本は公理ゼロ）。
`PROOF_STACK.md` の `roundSeg_of_run` 手順 11 段のうち、部品が無いものはもう無い。**

### この session でここまでに積んだ足場（全部標準公理のみ、全体 build 緑）

| 部品 | 役割 |
|---|---|
| `RoundHistory` ＋ `roundHistory_start` / `_tick` / `_of_steps` | ラウンドの履歴（`ScanSeg` ＋ 起点の `OriginAt` ＋ `Canonical`）を run に沿って運ぶ |
| `onlyMatchedRun_of_roundHistory` | 履歴から `CompareRounds.next` の第 1 引数と末尾の `Canonical` を取り出す |
| `chainShiftRun_snoc` / `_snoc_shiftOne` / `_tick` / `_of_steps` | shift 相を run から集める（`round_next` の `hchain`） |
| `chain_shift_period` / `_periodLength` / `_period_focus` | period テープは shift を通して不変 |
| `periodLength_onlyMatchedRun` | period テープの長さは scan 相のラウンドで不変 |
| `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false` / `watch_eq_of_mismatch_lagZero` | lag ゼロの不一致比較で watch は不変（`hpred` の橋） |
| `shiftLens_frame_tick` / `_steps` | shift 相では `shiftLens` の外は不変 |

**計器（`#print axioms`）はまだ 4 本のまま。** 上は全部 (C)（公理を減らす操作）の前段。

## 2026-09-19 n153: `round_next` の入力 15 個すべての出どころが確定した

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

最後に残っていた `hlen : Canonical s1.length` の出どころは
`GalilScaffoldTopSegmentHeads.scanSeg_counters`
（`ScanSeg → (Canonical s.radius → Canonical t.radius) ∧ (Canonical s.length → Canonical t.length)`）。
`RoundHistory` に `Canonical s₀.radius ∧ Canonical s₀.length` を足して起点で持たせ、
`onlyMatchedRun_of_roundHistory` が末尾の `Canonical` も返すようにした。

**`PROOF_STACK.md` に `roundSeg_of_run` の組み立て手順を 11 段すべて書いた。**
足りない小補題は **1 個だけ**:

> shift 末尾の状態 `y` について `y.vm = shiftLens.set s2 (shiftLens.get y.vm)`
> （`round_next` の結論の形に合わせるため）。`shiftOne` は `Lens.rel` なので
> 第 2 成分が `t = L.set s (L.get t)`＝「lens の場以外は変わらない」。
> これを `Steps` に沿って合成するだけ。

## 2026-09-19 n152: ラウンド境界の入力があと 1 個（`hlen`）になった

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

`PalPeg/RoundHistory.lean` が 15 宣言に。追加 5 本:

### `periodLength_onlyMatchedRun` — scan 相のラウンドは period テープの長さを変えない

`periodLength_consume`（`GalilChainCoupling:210`）は**無条件ではなく** `OnBlock` を側条件に
取るが、`OnBlock` は `consume` で保たれる（`GalilBranchInvariants.onBlock_verifier_consume`）
ので**起点 1 点だけ**あればよい。起点の `WatchBlock` は
`CloseoutRoundReads.blockInv_of_chainPosInv2` から出る。

これで `RoundSeg` の第 1 節 `periodLength wch' = periodLength wch` の材料が全部そろった
（shift 相は n149 の `chain_shift_periodLength`、公理ゼロ）。

### `watch_eq_of_mismatch_lagZero` — `hpred` の橋

`round_next` の `hpred` は**compare 前**の watch について言うのに、shift guard は
`afterMismatch s1 vs vq` 上で評価されるので**compare 後**の watch を見る。
この差は lag ゼロなら消える:

* `Internal` の `take` は `positive lag = true` を要求 → lag ゼロなら `idle` のみ
* 不一致比較の事象は `b = false`、`Outer s false t` は `idle` のみ
  （`queued` と `immediate` はどちらも `b = true`）

補助: `positive_false_of_zero` / `internal_eq_of_lagZero` / `outer_eq_of_false`。

### 入力表の現状（`PROOF_STACK.md`）

`GalilScaffoldTopRoundS.round_next` の入力 15 個のうち **14 個が確認済み**。
**残る未確認は `hlen : Canonical s1.length` の 1 個だけ**（`LPackM2` / `RadLedger` 側）。

## 2026-09-19 n151: ラウンド境界に無かった `ChainShiftRun` の収集を作った

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 2 本（`PalPeg/RoundHistory.lean`、これで同ファイル 10 宣言）

* `chainShiftRun_tick` — shift 相の 1 tick で `ChainShiftRun` が伸びる。
  shift mode の `Tick` は `shift_one` と `shift_done` だけで、残り 21 構成子は
  mode guard で落ちる。行き先も shift mode なら `shift_done` も落ちる
  （`GalilScaffoldTop:136` が mode を `.scan` に戻す）。
  `CopyIdle` が要るのは合併フレームの `remainingPos` が `H ∨ B` だから
* `chainShiftRun_of_steps` — run に沿って伸ばす（`roundHistory_of_steps` と同じ形）

**これで n149 の入力表の `✗`（存在しない）が埋まった。**
`GalilScaffoldTopRoundS.round_next` の入力 15 個のうち **14 個が出どころ確認済み**、
未確認は 2 個（`hpred` の `afterMismatch` の right、`hlen : Canonical s1.length`）。

### 次にやること（`PROOF_STACK.md` に記録）

`round_next` を run から呼ぶ組み立て（`roundSeg_of_run`）。
その第 1 節 `periodLength wch' = periodLength wch` には「ラウンド内で `periodLength` が
保たれる」が要る:

* shift 相は `chain_shift_periodLength`（**済・公理ゼロ**）
* scan 相は `periodLength_consume` を使うが、**これは無条件ではなく block 側条件を取る**
  （`CloseoutRoundUnique:221` の使い方で確認）。側条件は
  `CloseoutRoundReads.blockInv_of_chainPosInv2` 経由で出る見込み（**未検証**）

## 2026-09-19 n150: `ChainShiftRun` を後ろから伸ばす（ラウンド境界の残り 1 個の半分）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 2 本（`PalPeg/RoundHistory.lean`）

* `chainShiftRun_snoc` — `ChainShiftRun s w cycle n t v finish` ＋ 1 手の許可条件 →
  `ChainShiftRun s w cycle (n+1) (shiftTick t) (chainShiftOne v) (inc (inc finish))`。**公理ゼロ**
* `chainShiftRun_snoc_shiftOne` — `(galilFrameS P q first).shiftOne u t` 1 手を吸収

`ChainShiftRun` は `next` で前から積む inductive なので run を歩きながら積むには
後ろから伸ばせないといけない——`OnlyMatchedRun` と同じ問題で、
`MatchedRunSnoc.onlyMatchedRun_snoc` と同じ形で解いた。

### 一次情報で確認した形（`PROOF_STACK.md` に転記）

* `shiftOne`（`GalilScaffoldTopShift:42`）は **`ChainShiftRun.next` の 1 手そのもの**
* `beginShiftVM h w s t`（`GalilScaffoldTopShiftCycle:23`）は
  `chain := .watch (immediate w)` / `remaining := ofNat h` / `cycle := reset` を置くので、
  **shift 入口の `ChainShiftRun … 0 …` は `.stop` でタダ**
* 合併フレームの `remainingPos` は `H ∨ B`（`GalilScaffoldTopMerge:65`）なので
  copy 側を殺すのに `CopyIdle` が要る
* 終端判定は `chain_shift_exhausts`（`GalilScaffoldTopInvariant:46`）

### 設計判断

`Tick` の 23 構成子の場合分けを**この補題では書かなかった**。消費者側でどうせ
場合分けするから（`ShiftPhaseDeterminism.tick_shift_det:54` がその形で全部書いている）。
CLAUDE.md「変によく考えず定理ふやすのやめよ」に従って、shift 1 手の中身だけを扱う。

### 残り

`ShiftHistory` の tick 保存（shift mode の `Tick` 23 構成子の場合分け。21 個は
mode guard で落ち、`shift_done` は行き先 mode で落ちる）。それができたら
`round_next` の入力 15 個が全部そろって `RoundSeg` が run から出る。

## 2026-09-19 n149: period テープは shift を通して不変（＋ラウンド境界の残りは 1 個に特定）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない。**

### 新規 3 本（`PalPeg/RoundHistory.lean` 内）

* `chain_shift_period : ChainShiftRun s w cycle n t v finish → v.machine.control.period = w.machine.control.period` — **公理ゼロ**
* `chain_shift_periodLength : … → periodLength v = periodLength w` — **公理ゼロ**
* `chain_shift_period_focus : … → symbol v…period.focus = symbol w…period.focus`

理由は一次情報で確認: `chainShiftOne`（`GalilScaffoldChainInputSupply:1478`）が変えるのは
`distance` / `boundary` / `last` / `margin` **だけ**で period テープに触らない。
`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と同じ帰納法。

### ラウンド境界の残りは `ChainShiftRun` の収集 1 個（入力表は `PROOF_STACK.md`）

`GalilScaffoldTopRoundS.round_next` の入力を run からそろえる作業を 1 つずつ照合した。
15 個のうち **13 個は出どころが確認済み**（`RoundHistory` / `scan_shift` tick 構成子 /
`shiftGuardVM` / `Extra7.scanAvail` / `AuxPack` / `shift_done`）、
2 個が未確認（`hpred` の `afterMismatch` の right、`hlen : Canonical s1.length`）、
**1 個が存在しない**:

    hchain : ChainShiftRun ⟨s1.center, left s1.left, ofNat h, inc s1.radius,
                            inc (inc s1.length)⟩ (immediate w) reset h t' v cycle

これは shift 相（`shift_one` × h ＋ `shift_done`）を run から集める carrier が要る。
**found 経路の `CloseoutWatchRound33` / `37` も `ChainShiftRun` を仮説として取っている**
（`ShiftRoundInvCL` / `ShiftOriginRestCL` は open な `def`）ので、ここは共通の穴。
設計 `ShiftHistory` を `PROOF_STACK.md` に記録した。

## 2026-09-19 n148: `RoundHistory` — ラウンドの履歴を運ぶ不変量（公理は 4 本のまま）

**全体 build 成功（`BUILD=0`、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。計器は動いていない**（これは (C) の前段の足場）。

### 新規 `PalPeg/RoundHistory.lean`（5 宣言、標準 3 公理のみ）

    RoundHistory P q first delay w c s :=
      ∃ n c₀ s₀ w₀, ScanSeg P q first delay n c₀ s₀ c s ∧
        OriginAt w s₀ ∧ s₀.periodOnly = true ∧
        s₀.chain = ChainVM.watch w₀ ∧ zero w₀.lag = true

* `roundHistory_start` — ラウンド起点そのもの（`ScanSeg.stop`）
* `roundHistory_tick` — scan 相の 1 tick で伸びる（`MatchedRunSnoc.scanSeg_snoc_tick`）
* `roundHistory_of_steps` — run に沿って伸びる（側条件は `hScanWatchAll`）
* `onlyMatchedRun_of_roundHistory` — 下層の射影を取り出す（`CompareRounds.next` の第 1 引数）

**区間抽出（`CloseoutSegment.ScanToScan`）は使っていない。**

### なぜこれが要るか（測定済みの negative）

ラウンド境界（`scan_shift`）で read origin を貼り替えるには
`CompareRounds h (toOnly s w₀) 1 (toOnly s' v)`——**ラウンド 1 周ぶんの履歴**が要る
（`CloseoutRoundSeg.originAt_next_of_roundSeg`）。1 手の `Tick` からは作れないので、
**状態局所な不変量では閉じない**。だから履歴（`ScanSeg`）を持ち歩く。

### 次の小ブロック（特定済み・未着手）

`CompareRounds.next` の残り入力のうち、**`periodLength` が shift を通って保存される**
という補題が**存在しない**:

    chain_shift_period : ChainShiftRun s w cycle n t v finish → periodLength v = periodLength w

`chain_shift_lag`（`GalilScaffoldTopRounds:19`）と `chain_shift_phase`
（`GalilScaffoldChainReadOrigin:451`）が同じ帰納法で書かれているので、
`chainShiftOne` が period テープの `left.length + right.length` を変えないことを
示せば同型に通る。`periodLength (immediate w) = periodLength w` は既に 5 箇所で使われている。

### 今回やった honest な訂正

`lake build` を `(… ; echo BUILD=$?)` で包んでいたのでサブシェルの終了コードは
`echo` の 0 になる。**background task の通知の「exit code 0」を build 成功と読んで
一度間違えた**（実際は `BUILD=1`、docstring 直後に `set_option … in` を置いた構文エラー）。
以後 `BUILD=` の行を必ず読む。

## 2026-09-19 n147: **訂正** — 「中身は strictly weaker」は嘘やった

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### 何を間違えたか

n145 と n146 で「公理の本数は 4 のまま、**中身は元より弱い**」と書いた。
`ShiftPal` 公理については**これは嘘**。

* 旧: `obligation_shiftPalAlongTrace` — 結論 `ShiftPal` そのもの
* 新: `obligation_shiftPalResiduesAlongTrace` — 残差 3 つ
* 定理は `残差 3 つ → ShiftPal`。**つまり残差は `ShiftPal` を含意する = 論理的には強い。**
  逆向き（`ShiftPal → 残差`）は無い。

「結論を前提に置き換えたら弱くなる」は成り立たない。**弱くなるのは guard を
狭めたときだけ。** 自分の言葉を検査せずに 2 回書いた。

### 弱くなった部分（こっちは本物）

| 変更 | 弱くなったか | 理由 |
|---|---|---|
| `obligation_shiftPalAlongRun` → `…AtWatchAlongRun` | **○ 本物** | chain が watch の点だけに guard を狭めた。非 watch は `shiftPal_of_chainNotWatch` で定理 |
| `…AtWatchAlongRun` に `canRight z.vm.right` を追加 | **○ 本物** | 消費者が持っている場を仮説に入れた（過剰量化の解消） |
| `ShiftPal` → 残差 3 つ（run 形・trace 形とも） | **× 逆に強い** | 残差が `ShiftPal` を含意する |

### では残差化は前進なのか

**前進ではあるが、「弱くなった」という理由ではない。** 正しい理由は 3 つ:

1. **`ShiftPal` は global 形では偽の疑いが濃く producer が無かった**（n112）。
   残差 3 つはどれも **producer が特定済み**（`readsShift_at_actual` /
   `first_round` / `candidate_palAt`）
2. 残差は**機械レベルの事実**で、入力語についての回文の主張を含まない方向に動いている
   （n147 で `FreshShiftLedger` の 2 回文は `candidate_palAt` で消える見込み）
3. **本数は増えていない**（4 のまま）

### 公理の操作で許される 3 種類（以後これで判定する）

| 操作 | 弱くなるか | 本数 |
|---|---|---|
| (A) guard を消費者が供給する場まで狭める | **弱くなる** | 変わらず |
| (B) 結論を「十分な primary な前提」に置き換える | **弱くならない**（強い） | 変わらず。前進は「証明可能性」 |
| (C) サブ前提を定理として証明して公理から外す | **弱くなる** | **減る**（これが本命） |

n145/n146 は (A) と (B) を混ぜて (B) も「弱い」と書いた。これが誤り。

## 2026-09-19 n146: run 形 `ShiftPal` も残差 3 つに（公理は 4 本のまま、中身はさらに弱い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### やったこと

`obligation_shiftPalAtWatchAlongRun`（watch 点での `ShiftPal` そのもの）を
`obligation_shiftPalResiduesAlongRun`（残差 3 つ）に置き換えた。**本数は増えていない。**

**n147 訂正**: この置き換えは**弱化ではない**（残差は `ShiftPal` を含意する）。
弱くなったのは `canRight` を仮説に入れた部分だけ。

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,
     obligation_localRealization,
     obligation_shiftPalResiduesAlongRun,     -- ← 今回弱めた
     obligation_shiftPalResiduesAlongTrace]

**これで 2 本の `ShiftPal` 公理は完全に同内容**（量化の形だけが run / trace で違う）:

| 残差 | 中身 | producer 候補 |
|---|---|---|
| `H_readsShift` | shift 相のラウンド読み出し | `RoundSegFromRun.readsShift_at_actual`（構成 run / 実 run の対 ＋ `OriginAt` が要る） |
| `H_freshShiftAtShiftEntry` | shift 入口の最初のラウンド | `GalilScaffoldTopFirstRound.first_round`（`Entry` 形なので橋が要る） |
| `FreshShiftLedger` | 準備直後の watch の台帳 | n141〜n144 で 3 種類まで還元済み |

### 新しい定理 `ShiftPalAlongTrace.shiftPal_alongRun`

`CloseoutBundleRun.shiftPal_of_run_B` の適用。**run 形で新たに要る入力はゼロ**だった:

| 入力 | 出どころ |
|---|---|
| chain が idle | `CloseoutShiftLocalFree.chainIdle_of_invS`（`InvLPC` の `InvS`） |
| `AuxPack` | `CloseoutPackRun2.auxPack_steps` ＋ `InvLPC` の 3 場（`coupled`/`front`/`copyPack_of_invLPC`）＋ `GalilOracleLeaves2.hlive_of_invLPC` |
| `canRight right` | **消費者が持っていた**（下記） |

### `canRight` は過剰量化だった（CLAUDE.md の兆候そのもの）

`hShiftPalAlongRun` の唯一の消費者 `CloseoutMarksPack.packRunR_MW_marksFree` は
帰納段で `hn : BigPack2MG7W'' … (g n)` を持っており、その
`extra : Extra7` の `scanAvail` が scan・非 replay 点でちょうど
`canRight (g n).vm.right` を与える。**前の形はそれを捨てていた。**
`packRunR_MW_marksFree` と `CloseoutFinalBranch.given_scanLandingObligations` の
`hShiftPalAlongRun` 仮説に `canRight z.vm.right →` を足しただけで、
call site は `(hn.extra.scanAvail hs.1 hs.2)` で無償。

### 次の当たり（未検証）

`H_readsShift` と `CloseoutRoundReads.ReadsRound` は**mode guard だけが違う**:

    ReadsRound    : mode = scan  → replaying = false → periodOnly = true → …
    H_readsShift  : mode = shift → replaying = false → periodOnly = true →
                    positive remaining = false → …（結論は同一の `ReadsInv`）

しかも `CloseoutRoundReads.ReadsRun`（mode guard なしの形）が既にあって
`readsRound_of_readsRun` で `ReadsRound` を無償で出す。**`ReadsRun` を
`RoundBundle` の場にできれば `H_readsShift` も無償になる**——CLAUDE.md の
「guard を狭く切ると義務が増える」の同型 9 例目の可能性。次はこれを検査する。

## 2026-09-19 n145: **公理を 4 本に戻した**（n132 の原子化は後退だった）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4。
無条件 PAL は未完。§10.5 は未達。**

### コウタの指摘（受けた）

* 「え？なんでいつのまにか前提ふやしてるの」「4 つに減らしたやろ」
* 「前提を増やしてどうするねん。せっかく機械的に進捗示すためにこっちが指示したのに」
* 「前提が難しいなら、その前提のサブ前提を証明せなあかん」

n132 で `obligation_shiftPalAlongTrace` を 3 原子に割って **4 → 6 にした**。
CLAUDE.md の「公理は 1 場ずつの原子に分解する」を根拠にしたが、
**計器の読みは本数**なので、これは数字を悪くしただけ。さらにそれを
「後退ではなく割れた状態」と書いて正当化した——そこが甘かった。

### 規律（これ以降）

1. **公理の本数は増やさない。** 4 が上限で、減らす方向にしか動かさない。
2. **前提が難しいときは、その前提のサブ前提を定理として証明する。**
   新しい公理にはしない。**公理の文が弱くなるだけ**にする。
3. 「原子に割ったから後退ではない」式の正当化をしない。

### 現在の 4 本（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,                    -- CycleOracleMC3（found 経路）
     obligation_localRealization,               -- H_realizeLIMW'（局所実現）
     obligation_shiftPalAtWatchAlongRun,        -- watch 点で ShiftPal（run 形）
     obligation_shiftPalResiduesAlongTrace]     -- trace 形の残差 3 つを束ねたもの

**元の 4 本と中身が違う**（n147 で訂正: 下の 2 つ目は**弱くなっていない**）:

* `obligation_shiftPalAlongRun` → `…AtWatchAlongRun`（chain が watch の点だけ。
  非 watch は `shiftPal_of_chainNotWatch` で空虚）
* `obligation_shiftPalAlongTrace`（`ShiftPal` 丸ごと）→ `…ResiduesAlongTrace`
  （`H_readsShift` ＋ `H_freshShiftAtShiftEntry` ＋ `FreshShiftLedger` の 3 残差）。
  とくに 3 つ目は `ShiftPal` 丸ごとから「period テープの中身／半径と周期の大小／
  period テープの位相」の 3 種類まで還元済み（n141〜n144、下に
  `shiftPal_of_freshShiftLedger` → `shiftPalAt_fresh_of_candidate` →
  `reshift_of_palAt_pair` → `periodOn_*` の鎖が全部入っている）

**これが「サブ前提を証明して公理の文を弱める」の実例。**

## 2026-09-19 n144: `hCaught` の正体 — chain の予測証明書（回文からは出ない）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### `hCaught` を展開すると

`shiftPalAt_fresh_of_candidate` の中で導いた 2 つを並べる:

* `hsym'`（**ガードから出る**）: `symbol wch…period.focus = (encoded w)[pos + r₀ + 1]?`
  （`shiftGuardVM` の予測節 ＋ `right_read_index` ＋ `ScanInvariant.rightPos`）
* `hCaught`（**残差**）: `(encoded w)[pos + r₀ + 1 − 2h]? = symbol wch…period.focus`

合わせると `(encoded w)[pos + r₀ + 1 − 2h]? = (encoded w)[pos + r₀ + 1]?`。

**`pos + r₀ + 1` は現在の回文の右端 `pos + r₀` の 1 つ外**。だから
`periodOn_right_of_palAt_pair` が出す `PeriodOn (encoded w) (2h) pos (pos + r₀)` では
**原理的に届かない**（`j + 2h ≤ pos + r₀` までしか主張しない）。
`reshift_from_right` が `hright` の最後の 1 添字を別に要求するのはそのため。

### したがって `hCaught` は「chain の予測証明書」

意味は「period テープの焦点（＝chain が次に来ると予測している記号）が、
入力の `2h` 手前の記号と一致する」——**period テープが入力と `2h` ずれて整合している**こと。

* `periodOnly = true` 側ではこれが `RoundScan.pred`
  （`symbol focus = (encoded raw)[C + R + 2 + used − 2h]?`、終端で添字が `C + R + 1`
  ＝ `pos + r₀ + 1 − 2h` に一致。n142 の測定どおり）
* `periodOnly = false` 側は `RoundScan` が使えない（n143: `cycle` 凍結）ので、
  **準備直後の period テープの整合を運ぶ場**が要る

**回文からは出ない**（新しく読んだ記号についての主張なので）。
DP の `Candidate` は period テープの**中身**を保証するが、
「いまどの位相を指しているか」は chain の台帳の話。

### 残差 5 本の性格が確定した

| 残差 | 性格 | 出どころ |
|---|---|---|
| `hIn` / `hOut` | period テープの**中身**（DP の `Candidate`） | `prep_watch_start_least` ＋ `palAt_pair_of_candidate` |
| `hLo` / `hHi` | 半径と周期の**大小** | `found_radius_le_two_period` ＋ 伸び |
| `hCaught` | period テープの**位相** | 準備直後の整合を運ぶ場（`RoundScan.pred` の `periodOnly = false` 版） |

3 種類に分かれた。**`hCaught` だけが新しい場**で、残り 4 つは既存の定理からの配線。

## 2026-09-19 n143: **訂正** — `RoundScan` は `periodOnly = false` では偽。`ChainRound` のガードは必要だった

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### n142 の推測は間違いだった（一次情報で潰した）

n142 で「`RoundScan` に `periodOnly` の場が無いので `ChainRound` の
`periodOnly = true` ガードは**定義上の選択**」と書いた。**これは誤り。**

一次情報:

* `GalilScaffoldTopSearch:77` — `afterBirth true s = {s with periodOnly := false, cycle := reset}`
  （誕生で `cycle` が 0 になる）
* `GalilScaffoldTopSearch:41` — `cycleAfter s = if s.periodOnly then dec s.cycle else s.cycle`
  （**cycle は `periodOnly = true` のときだけ減る**）

したがって **`periodOnly = false` の間、`value cycle` は誕生時の `0` に凍結**される。
`RoundScan.count : value v.cycle = (2h : ℤ) − used` に `0` を入れると `used = 2h` で、
`RoundScan.fresh : used < 2 * h` と**矛盾**する。

**`RoundScan` は `periodOnly = false` の状態では常に偽。**
`ChainRound` の `s.periodOnly = true →` ガードは**必要**だった。

### 帰結: `periodOnly = false` 側には別の進行カウンタが要る

`cycle` が凍結しているので、最初の shift における「周期境界にいること」は
**watch 自身の `distance` / `boundary` / `last` / `phase`** で追う必要がある。
これが n138 で言った「`RoundScan` の `periodOnly = false` 版」の実体。

**`shiftPalAt_fresh_of_candidate`（n141）の 5 残差が正しいインタフェースである根拠**:
`hIn` / `hOut` / `hLo` / `hHi` / `hCaught` は **`cycle` に一切触れていない**。
`hCaught` は `symbol period.focus = (encoded w)[…]?` という watch 側の事実だけ。
だから `cycle` が凍結していても成立し得る。

### 次に測るべきこと

`GalilScaffoldChainConsume.consume` の
`phase := if boundaryEvent then advancePhase s.phase else s.phase` と
`boundary := if boundaryEvent then distance else s.boundary` /
`last := if boundaryEvent then s.boundary else s.last` の更新から、
`phase = 4` が「period テープを 4 回の境界イベント分たどった」ことを言う。
そこから `hCaught`（焦点が入力の `2h` 手前を指す）が出るか。

**`cycle` を使う道は閉じた**（凍結しているので情報を持たない）。
`distance`/`boundary`/`last`/`phase` の 4 つが唯一の進行情報。

## 2026-09-19 n142: `hCaught` は終端での `RoundScan.pred` と同じ添字（`RoundScan` に `periodOnly` の場は無い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 測定 1: 添字が一致する

`GalilRoundPeriod.RoundScan` の
`pred : symbol w.machine.control.period.focus = (encoded raw)[C + R + 2 + used − 2h]?`
は、`position s.center = C + h`・`r₀ = R + h` を入れると
`shiftPalAt_fresh_of_candidate` の `hCaught` の添字
`position s.center + r₀ + 1 − 2h` = **`C + R + 1`** と一致する
（終端 `used = 2h − 1` のとき。`terminal_palindrome` も同じ書き換えをしている）。

**つまり `hCaught` は新しい場ではなく、`RoundScan.pred` の終端形。**

### 測定 2: `RoundScan` に `periodOnly` の場は無い

`RoundScan` の全 12 場（`chain` / `caught` / `canon` / `count` / `fresh` / `size` /
`posH` / `pal` / `room` / `origin` / `pred`）は幾何と台帳だけで、
**`periodOnly` に触れる場は 1 つも無い**。

`CloseoutPackRun31.ChainRound` の `s.periodOnly = true →` ガードは
**定義上の選択**であって `RoundScan` が要求しているものではない。

### 残る本当の差（`periodOnly = false` 側）

`shiftPal_of_chainRound` は `hend : singlePositive s.cycle = true`（ガードの
`periodOnly = true` 枝）から `terminal_iff` 経由で `used = 2h − 1` を得ている。
`periodOnly = false` 枝のガードは `negative wch.margin = false` で、**`used` を固定しない**。

Scala 正本（CLAUDE.md の記録: `ScaffoldGalil.scala:254`）でも `canShift` は
`periodOnly` のとき `singlePositive cycle` を要求し、そうでないときは margin を見る。
したがって最初の shift では `used` は cycle では固定されず、
**`phase = 4`（4 回の boundary event）が進行の指標**になる。

**次に測るべきはここ**: `phase = 4` ＋ `negative margin = false` から
`used` の位置（＝周期境界にいること）が出るか。`GalilScaffoldChainConsume.consume` の
`phase := if boundaryEvent then advancePhase s.phase else s.phase` と
`distance`/`boundary`/`last` の更新が一次情報。

### 今日の到達点（まとめ）

* 反証済み `hpack` 節 4 / 節 7 を found 経路から**除去**（`(hwatch : PrepLandingWatchC …)` は 0 本）
* 過剰仮定の弱化 6 件（`split4/3_of_prefix` / `fallbackLanding_of_pack` /
  `fallbackTick_of_watchTick` / `reshift_from_right` / `WatchMismatchNoShiftC` の guard）
* 公理の原子化（`shiftPalAlongTrace` → 3 原子）と狭化（run/trace 両方を **watch 点**に）
* fresh 側 `ShiftPal` の数学の芯完成（`periodOn_mirror'` / `periodOn_of_palAt_pair` /
  `periodOn_right_of_palAt_pair` / `reshift_of_palAt_pair` / `shiftPalAt_fresh_of_candidate`）
* 過去の自分の記述の訂正 6 件（`first_round`／`fresh_shift_entry`／`PalInPegUnconditional`
  の docstring／`LagPos` 不要／`shiftPal_of_readOrigin` の docstring／「found 半径正」の需要 3→2）

## 2026-09-19 n141: fresh 側 `ShiftPal` の**数学的な芯が完成**（4 段、全部標準公理）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 完成した芯

    PalPeg.reshift_of_palAt_pair (word : List (Fin 3)) (C h r : ℕ)
      (hin   : Manacher.PalAt word (C − h) h)          -- DP の Candidate（内側）
      (hout  : Manacher.PalAt word (C − 2h) (2h))      -- DP の Candidate（外側）
      (hcur  : Manacher.PalAt word C r)                -- ShiftPal の hScanInv.palindrome
      (hstep : 0 < h) (hsmall : 2h ≤ r) (hle : r ≤ 4h)
      (hend  : C + r + 1 < word.length)
      (hpred : word[C+r+1]? = word[C+r+1−2h]?)         -- shiftGuardVM の予測節
      : Manacher.PalAt word (C + h) (r + 1 − h)        -- ShiftPal の結論の第 3 節そのもの

### 4 段（今日の作業、すべて `PalPeg.GalilPeriodUnion` / `GalilScaffoldChainInputSupply`）

| 段 | 定理 | 効いた気づき |
|---|---|---|
| 0 | `reshift_from_right` の弱化（n139） | `hold` は半径 `radius` ではなく `step` 分で足りた（本体での使用は 2 行だけ） |
| 1 | `periodOn_mirror'` | 既存 `periodOn_mirror` は右→左。要るのは左→右で、証明は対称 |
| 2 | `periodOn_of_palAt_pair` | 中心が `d` ずれた 2 回文の鏡映が `2C − 4d − i` で一致 |
| 3 | `periodOn_right_of_palAt_pair` | `PeriodOn.mono`（`r ≤ 4d`）＋ 段 1 |
| 4 | `reshift_of_palAt_pair` | 末尾 1 添字（`j + 2h = C+r+1`）を予測で埋めて `reshift_from_right` へ |

**新しい数学はもう無い。** 残るのは配線 3 本:

1. `hin` / `hout` — この watch の周期テープが DP の `Candidate` から来たという**履歴**。
   材料は `GalilPrepLeast.prep_watch_start_least`（`watchStart ver c ys b credits` ＋
   `Candidate w lower h` ＋ `ys.length + 1 = h`）と
   `CloseoutWatchPhase3.palAt_pair_of_candidate`。
2. `hpred` — `shiftGuardVM` の最終節 `symbol w.machine.control.period.focus = read s.right`
   を添字形 `word[C+r+1]? = word[C+r+1−2h]?` へ。
   `periodOnly = true` 側は `hI.pred` がこの形を持っている（`CloseoutPackRun31:190` 付近）。
3. `2h ≤ r ≤ 4h` — found 時の `found_radius_le_two_period`（`radius ≤ 2h`）＋
   その後の一致比較ぶんの伸びを run に沿って運ぶ台帳。

## 2026-09-19 n140: fresh 側 `hright` の材料を全部特定した（`periodOn_*` と `found_radius_le_two_period`）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### `hright` の正体

`reshift_from_right` の `hright` は、`GalilPeriodUnion.PeriodOn` と**同じ形**:

    PeriodOn x p a b := ∀ i, a ≤ i → i + p ≤ b → x[i]? = x[i + p]?

fresh 側で要るのは `PeriodOn (encoded w) (2h) (position s.center) (position s.center + r₀ + 1)`
——**現在の中心より右**で周期 `2h`。

### 既にある部品（一次情報で確認）

| 定理 | 内容 |
|---|---|
| `GalilPeriodUnion.periodOn_mirror (hpal : PalAt x C k) (hp : p ≤ k) (h : PeriodOn x p C (C+k)) : PeriodOn x p (C−k) C` | **右→左**。要るのは逆向き（左→右）だが証明は対称 |
| `GalilPeriodUnion.periodOn_union` | 重なる 2 区間の周期を合併 |
| `GalilPeriodUnion.encoded_periodOn_even` | `encoded` 上の偶数周期 |
| `CloseoutWatchPhase3.palAt_pair_of_candidate` | `Candidate` → `PalAt (pos−h) h` ∧ `PalAt (pos−2h) (2h)` |
| **`GalilReplayBudgetProof.found_radius_le_two_period`** | **found 時に `value sF.radius ≤ 2*h`**（＋`Candidate`＋最小性＋`1 ≤ h`）を**無条件で**出す |

### 効くこと

`found_radius_le_two_period` の `r₀ ≤ 2h` が、**「周期が回文全体を覆う」ための境界**。
`Candidate` が保証するのは place stream の接頭辞 `take (4h+1)` の回文性で、
`r₀ ≤ 2h` ならその範囲が現在の回文を覆う。つまり n139 で「未特定」とした
`hsmall : 2h ≤ r₀` と合わせると **found 時点では `r₀ = 2h`**。

ただし `ShiftPal` が評価されるのは found より**後**（誕生した chain の最初の shift）で、
そこまでに一致比較のぶん `r₀` が伸びている。したがって必要なのは

    found 時の r₀ = 2h  ＋  その後の一致比較ぶんの伸び

を run に沿って運ぶ台帳。これが fresh 側 `ShiftPal` の最後の芯。

### 次の具体手順

1. `periodOn_mirror` の左→右版（証明は対称、`Manacher.mirror_getElem?` を使う）
2. `palAt_pair_of_candidate` の 2 回文 → `PeriodOn (encoded w) (2h) (pos−2h) pos`
   （`periodOn_union` ＋ `encoded_periodOn_even`）
3. 1 を当てて `PeriodOn (encoded w) (2h) pos (pos+r₀)`、末尾 +1 は予測（`shiftGuardVM` の
   最終節 `symbol period.focus = read s.right`）
4. `reshift_from_right` に流して `PalAt (encoded w) (pos + h) (r₀ + 1 − h)`

**新しい数学はない。既存の `periodOn_*` 層と `found_radius_le_two_period` の配線。**

## 2026-09-19 n139: `reshift_from_right` の `hold` は半径 `step` 分で足りた（fresh 側の origin が DP から出る）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 弱化（一次情報で測って実施）

`GalilScaffoldChainInputSupply.reshift_from_right` は
`hold : Manacher.PalAt word center radius` を取っていたが、
本体での使用は **2 行だけ**（`:1153`/`:1155`）で、`PalAt word center step` を
作るためにしか使っていなかった。仮定をそこまで弱め、呼び出し側 3 箇所
（`CloseoutPackRun31:178`、`GalilScaffoldChainReadOrigin:657`、
`GalilScaffoldChainInputSupply:2748`）を inline の縮小で通した。全体 build 緑。

**意味**: 「origin の回文」は半径 `radius` 分は要らず、**周期長 `h` 分だけあれば足りる**。
そして `GalilDpCorrect.Candidate w lower h` の第 3 節
`(w.take (2h+1)).reverse = w.take (2h+1)` はまさに中心 `h`・半径 `h` の回文。
`CloseoutWatchPhase3.palAt_pair_of_candidate` がそれを
`PalAt (encoded raw) (pos − h) h` の形で出す。

**`periodOnly = true` 側は `RoundScan` が前ラウンドの origin を運んでいたが、
fresh 側は DP の `Candidate` が直接 origin をくれる——運ぶ必要がなかった。**

### fresh 側 `ShiftPal` の残差（`reshift_from_right` の引数ごとに測った）

| 引数 | fresh 側の出どころ | 状態 |
|---|---|---|
| `hold : PalAt word (pos−h) h` | `palAt_pair_of_candidate` 第 1 成分 | **揃った**（今回） |
| `hcurrent : PalAt word pos r₀` | `ShiftPal` の仮説 `hScanInv.palindrome` | **揃っている** |
| `hstep : 0 < h` | `Candidate` の `lower < h` | **揃っている** |
| `hsmall : h ≤ r₀ − h`（＝ `2h ≤ r₀`） | 未特定 | **要る**（台帳 1 本） |
| `hend : pos + r₀ + 1 < length` | 入力長の台帳 | 要る |
| `hright : 右側で周期 `2h`` | `Candidate` の 2 回文（半径 `h` と `2h`、`palAt_pair_of_candidate` が両方出す）の重なり | **材料あり** |

**`hright` が本体。** `periodOnly = true` 側は `hI.pal`（前ラウンド origin、半径 `R`）の
鏡映（`Manacher.mirror_getElem?`）＋ `hI.pred` で出していた。fresh 側は
`Candidate` が中心を `h` ずらした 2 つの回文をくれるので、**重なりから周期 `2h` が出る**——
純粋な語の組合せ論で、`GalilPeriodUnion.periodOn_union`（重なりが p 個以上ある
2 つの周期区間の合併）が既にある層。

**残りは「2 回文 → 周期 2h → 右側の周期性」1 本と `2h ≤ r₀` の台帳 1 本。**

## 2026-09-19 n138: 残る `ShiftPal` 2 本の中身を特定した（chain 台帳の 1 場）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 一次情報で測ったこと

| 定理 | 結論 | `ShiftPal` に使えるか |
|---|---|---|
| `CloseoutPackRun31.terminal_palindrome` | `PalAt (encoded w) (C + 2h) (R + 1)` | **使える**（`periodOnly = true` 側で実際に使われている） |
| `GalilScaffoldTopFreshEntry.fresh_shift_entry` | `∃ o, Entry … ∧ …`（origin 台帳） | **使えない**——`PalAt` ではない |
| `CloseoutWatchPhase3.palAt_pair_of_candidate` | `PalAt … (pos − h) h ∧ PalAt … (pos − 2h) (2h)` | 座標が中心の**左側**で、`ShiftPal` は `pos + h` を要求 |

**訂正**: `shiftPal_of_readOrigin` の docstring は `periodOnly = false` 分岐の内容を
「`GalilScaffoldTopFreshEntry`」と書いていたが、そのファイルの 2 定理
（`fresh_shift_entry` / `found_shift_entry`）はどちらも `Entry`（origin 台帳）を結論とし、
`PalAt` を出さない。**shift 入口の台帳の話で、`ShiftPal` ではなかった。**
（過去の自分の docstring を一次情報にしない——今日 5 回目）

### `terminal_palindrome` の構造から分かる、必要な材料

`terminal_palindrome` は `RoundScan` の場から組み立てている:

* `hI.caught.scan.palindrome` — **現在の回文** `PalAt (encoded w) (C + h) (R + h)`
* 終端条件（`terminal_iff` ← `singlePositive s.cycle`）
* 予測（`symbol period.focus = read (right s.right)`）

このうち**現在の回文は `ShiftPal` 自身の仮説 `hScanInv : ScanInvariant w (position s.center) r₀
s.left s.right` が持っている**。終端条件は `periodOnly = false` 側では
`negative wch.margin = false` に置き換わる。

### したがって残る内容は 1 場だけ

**「run に沿って、watch している chain の周期テープ長 `periodLength wch` は
その中心における入力の本物の周期である」**

これは `Candidate`（DP の結論、`GalilDpCorrect` で無条件証明済み）＋
「この watch の周期テープはその `Candidate` から作られた」という**履歴の事実**。
`periodOnly = true` 側では `RoundScan` がその履歴を運んでいる。
`periodOnly = false` 側（誕生後の最初の shift）にはそれを運ぶ場がまだない。

**次の仕事**: `RoundScan` の `periodOnly = false` 版（margin 基準・準備直後）を
chain 台帳の 1 場として立て、`GalilPrepLeast.prep_watch_start_least`
（`watchStart ver c ys b credits` ＋ `Candidate w lower h` ＋ `ys.length + 1 = h`）から
run に載せる。**新しい数学ではなく、履歴を運ぶ場を 1 つ足す仕事。**

## 2026-09-19 n137: run 形も watch 点に狭めた（同じ 1 定理で 2 本）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

`ShiftPalAlongTrace.shiftPal_of_chainNotWatch`（n136）を `obligation_shiftPalAlongRun` にも
当てた。**同じ 1 つの定理が run 形と trace 形の両方を狭めた。**

| 旧 | 新（狭まった公理） |
|---|---|
| `obligation_shiftPalAlongRun` | `obligation_shiftPalAtWatchAlongRun`（`∀ wv, z.vm.chain = .watch wv →` を追加） |
| `obligation_shiftPalAtFreshChainAlongTrace` | `obligation_shiftPalAtFreshWatchAlongTrace`（同型） |

どちらも旧版は**定理になった**（`by_cases` で watch / 非 watch に割って、非 watch 側は空虚）。

### 現在の 6 本（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,                       -- CycleOracleMC3（found 経路）
     obligation_freshShiftAtShiftEntryAlongTrace,  -- trace 各 tick で H_freshShiftAtShiftEntry
     obligation_localRealization,                  -- H_realizeLIMW'（局所実現）
     obligation_readsShiftAlongTrace,              -- trace 各点で H_readsShift
     obligation_shiftPalAtFreshWatchAlongTrace,    -- watch 点で ShiftPal（trace 形）
     obligation_shiftPalAtWatchAlongRun]           -- watch 点で ShiftPal（run 形）

### 残る `ShiftPal` 2 本の中身（測定済み）

`periodOnly = true` 側は `CloseoutPackRun31.shiftPal_of_chainRound` が
`ChainRound`（`:204`、`periodOnly = true` を guard に持つ）から閉じている。
残るのは **`periodOnly = false` ＋ watch** の場合で、そこでは `shiftGuardVM` の分岐が
`singlePositive s.cycle = true` ではなく **`negative wch.margin = false`** になる。

到達可能性の確認: 誕生 watch は `phase = 0` だが、4 回の boundary event で `phase = 4` に
達し得る。その間 `periodOnly` は `beginShift` まで `false` のままなので、
**「新しく準備した chain の最初の shift」がこの場合**。空虚ではなく実質がある。

内容は「DP が見つけた周期が入力の本物の周期である」——n114 で探索側（`GalilDpCorrect`）は
無条件に証明済みと測定してあるので、新しい数学ではなく `margin` 側の `RoundScan` 相当を
立てる層の配線。**`ChainRound` の `periodOnly = false` 版（margin 基準）が次の仕事。**

## 2026-09-19 n136: `ShiftPal` は chain が watch でない限り**空虚**（lag も「found 半径正」も不要）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 主定理（標準公理、`sorry` ゼロ）

    ShiftPalAlongTrace.shiftPal_of_chainNotWatch
      (hNotWatch : ∀ wv, s.chain ≠ ChainVM.watch wv) : ShiftPal centre place entry q first w s

**`CopyOrBack` も `CopyInv` も `LagPos` も「found 時の半径が正」も要らない。**

### なぜ lag が関係なかったか（n134/n135 の見立ての訂正）

`shiftGuardVM` は `w.machine.control.phase = 4` を要求する。
`GalilScaffoldChainConsume.State` のフィールド順は
`period, distance, boundary, last, phase, forward, broken`（`:15`）で、
`ChainStep.backDone` が置く `watchControl v = ⟨moveRight v, reset, reset, reset, 0, true, false⟩`
の **5 番目 `0` が `phase`**。つまり誕生 watch は `phase = 0`。

1 tick 後も 4 にならない:

* `Outer.queued` は machine を触らない → phase 0
* `Outer.immediate` は `consume` を通すが
  `phase := if boundaryEvent then advancePhase s.phase else s.phase` で
  `advancePhase 0 = ⟨min 4 1, _⟩ = 1`、不一致枝は `broken := true` で phase 不変
  （`CopyPhaseNoShift.consume_phase_ne_four`）
* `ChainMatched.breaks` の行き先は `.broken` で watch でない

`.idle` からは誕生しても `chainStart = .copy`、`.broken` からは `.broken`、
`.copy` からは `.copy`/`.back`——**どれも watch でない**。
支えは `CopyPhaseNoShift.tick_watch_phase_ne_four_of_notWatch`（構成子の形だけ）。

**n134 で `LagPos` を、n135 で「found 半径正」を要求すると測ったが、どちらも不要だった。**
一次情報（`watchControl` のフィールド順）を見て初めて分かった。
「壁に当たったら形式化のミスを疑う」がそのまま効いた。

### 公理の狭まり

`obligation_shiftPalAtFreshChainAlongTrace`（定理になった）
→ `obligation_shiftPalAtFreshWatchAlongTrace`（公理、**追加条件つき**）:

    ∀ wv : GalilScaffoldChainWatch.State, (st j).vm.chain = ChainVM.watch wv → ShiftPal …

本数は 6 のままだが、**中身は「chain が既に watch の点」だけに縮んだ**。
残るのは「準備し終えた周期が入力の本物の周期」という DP 正当性の帰結（n114 で
探索側は無条件に証明済みと測定）。

### 副産物: 「found 時の半径が正」の需要が 3 → 2 に減った

n135 で「1 本潰すと 3 箇所に効く」と書いた側条件のうち、
**`LagPos` 経由の 1 箇所は消えた**（`phase` で落ちるので lag が不要）。
残るのは `reachesWatchPhase_or_segEnd_at_foundBirth_canonical` と
`first_round` / `chain_life` の既存仮定。

## 2026-09-19 n135: `LagPos` を trace に載せる道の測定（`IPackMW` に lag 場は無い）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6。
無条件 PAL は未完。§10.5 は未達。**

### 測定 1: `PreTraceIMW` は lag を運んでいない

`IPackMW`（`CloseoutPackW:64`）＝ `LPackM` ＋ `LPackM2`。
`LPackM`（`CloseoutPackRun10:140`）の場は `lrepM`（左ヘッドの表現）と
`scanGeom`（`ScanInvariant`）の 2 つだけで、**chain の lag に触れる場は無い**。

したがって `obligation_shiftPalAtFreshChainAlongTrace` を `.watch` 相に狭めるには
`LagPos (st j).vm.chain` を別途調達する必要があり、**いま狭めても差し引きゼロ**。

### 測定 2: lag が要るのは `.back` 相だけ（線引きが細かくなった）

| `s.chain` | `ShiftPal` の空虚性 | lag 仮定 |
|---|---|---|
| `.idle` | 空虚（誕生しても `.copy`、しなければ `.idle`） | **不要** |
| `.copy` | 空虚（`FoundPackRefute.chainTick_copy_not_watch`） | **不要** |
| `.broken` | 空虚（`ChainStep.brokenIdle`） | **不要** |
| `.back` | 空虚（`backDone` の watch は lag を継承） | **要る** |
| `.watch` | 本体 | — |

`shiftPal_of_copyOrBack`（n134）は `.copy` と `.back` を束ねて lag を要求しているが、
**`.copy` 側だけなら lag 無しで済む**。必要なら分けられる。

### 測定 3: 「found 時の半径が正」は**導出されていない**（アセンブリ全体の仮定）

`GalilScaffoldTopFoundLife`（`:28`）は `hRpos : 0 < R` を**明示の仮定として取っている**
（`R` は `ScanInvariant` の半径）。`GalilScaffoldTopFirstRound.first_round` も
`hrp : 0 < value radius` を仮定で取る。CLAUDE.md の記憶欄「仮定：Decodes、delay=2048、
3·Rad≤5·k、**found 半径正**、窓長偶数」と一致する。

**この 1 つの側条件が今日 3 箇所で出た**:

1. `ReachesWatchFromRun.reachesWatchPhase_or_segEnd_at_foundBirth_canonical` の
   `hRadiusPos : 0 < value radius`（n125）
2. `LagPos` を誕生点で立てるため（n134/n135、`.back` 相の空虚性）
3. `first_round` / `chain_life` の既存仮定

つまり**これを 1 本潰すと 3 箇所に効く**。逆に言えば、いまはどこにも producer が無い。
真偽の見立て: `Candidate w lower h` は `4h+1 ≤ w.length` かつ `h ≥ 1` を要求するので
place stream に 5 記号以上が要り、walker は scan と共に進むから半径も進んでいるはず——
**だが `radius` と `place stream` の長さを結ぶ場は未確認**。次に見るならそこ。

## 2026-09-19 n134: `periodOnly = false` 分岐の空虚な半分を落とした

**`PalPeg.ShiftPalAlongTrace.shiftPal_of_copyOrBack` — 標準公理、`sorry` ゼロ、単体 build EXIT=0。**
（全体 build は未実行。公理は 6 のまま。無条件 PAL は未完、§10.5 は未達。）

### 証明したもの

    theorem shiftPal_of_copyOrBack (hPhase : CopyOrBack s.chain) (hLag : LagPos s.chain) :
        ShiftPal centre place entry q first w s

**`CopyOrBack`（lag 正）の点では `ShiftPal` は空虚に成り立つ。** 理由:
`ShiftPal` は比較の行き先 `s'` に `shiftGuardVM s'` を要求し、それは
`zero w.lag = true` を含む。しかし copy/back から 1 手で生まれる watch は lag を
そのまま受け継ぐ（`backDone`）か `inc` する（`Outer.queued`）ので、誕生 chain の正 lag が
保たれて guard が落ちる。`Outer.immediate` と `ChainMatched.breaks` は
どちらも `zero lag = true` を要求するので正 lag では使えない。

支えは `CopyPhaseNoShift.tick_not_watch_or_posLag`（事象によらない版、今回追加）。

### 効く範囲（`periodOnly = false` 分岐の場合分け）

| `(st j).vm.chain` | `ShiftPal` |
|---|---|
| `.idle` | **空虚** — 誕生しても `.copy`、しなければ `.idle`。どちらも watch ではない |
| `.copy` / `.back`（lag 正） | **空虚** — `shiftPal_of_copyOrBack`（今回） |
| `.broken` | **空虚** — `ChainStep.brokenIdle` で `.broken` のまま |
| `.watch` | **本体** — 準備した周期が入力の本物の周期であること（DP 正当性の帰結のはず） |

つまり `obligation_shiftPalAtFreshChainAlongTrace` は
**`.watch` 相だけに狭められる**。

### 残る側条件

狭めるには trace の各点で `LagPos (st j).vm.chain`（copy/back 相の lag が正）が要る。
`PreTraceIMW` が各点で運ぶ `IPackMW` に lag の場があるかは**未確認**。
無ければ新しい義務になるので、その場合は差し引きゼロ——**先に `IPackMW` を確認すること。**

## 2026-09-19 n133: 3 原子の producer を一次情報で測った（CLAUDE.md の記述は楽観的だった）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 6（n132 の分解後）。
無条件 PAL は未完。§10.5 は未達。**

### 訂正: `first_round` は `H_freshShiftAtShiftEntry` を出さない

CLAUDE.md と `PalInPegUnconditional` の表は「`H_freshShiftAtShiftEntry`（←`first_round`）」と
書いていたが、**一次情報を読むと違う**:

* `GalilScaffoldTopFirstRound.first_round` の結論は
  `(∃ k, Steps …) ∧ e.chain = .watch v ∧ zero v.lag = true ∧ e.periodOnly = true ∧
   ∃ o' : ReadOrigin raw, Entry raw o' (toOnly e v) ∧ …`
  ——**origin/`Entry` 形**。
* `H_freshShiftAtShiftEntry` が要るのは `∃ C R k, ShiftInv w C R (periodLength wch) k t wch` で、
  `ShiftInv`（`CloseoutPackRun37:59`）は 13 場（`kle` / `posH` / `size` / `room` /
  `remaining` / `canon` / `count` / `leftRep` / `leftPresent` / `leftPos` / `rightRep` / …）の
  **幾何と台帳**。

`Entry` → `ShiftInv` の橋が要る。**1 適用では落ちない。**
同様に `obligation_readsShiftAlongTrace` の候補 `RoundSegFromRun.readsShift_at_actual` も
前ラウンド起点の `OriginAt` ＋ 構成 run / 実 run の対を要求する（n125 で測定済み）。

**過去の自分の記述（CLAUDE.md の「経路と残り」欄）を一次情報として使わない**——
今日 4 回目の同じ教訓。

### 見えた筋: `obligation_shiftPalAtFreshChainAlongTrace` は**半分が空虚**

`ShiftPal` は `∀ s', compare s s' → ¬matched s' → ∀ wch, s'.chain = .watch wch →
shiftGuardVM s' → …` の形。`periodOnly = false` の点で chain の相を場合分けすると:

| `s.chain` の相 | 状況 |
|---|---|
| `CopyOrBack`（lag 正） | **空虚**——`CopyPhaseNoShift.not_shiftGuardVM_of_copyOrBack_tick` が
  「compare の行き先に shift guard は立たない」を証明済み |
| `.watch`（準備完了、まだ shift していない） | **本体**——「準備した周期が入力の本物の周期」 |

後者は DP 正当性（n114 で「探索側は無条件で証明済み」と測定済み）の帰結のはずで、
新しい数学ではなく層の配線。**`ShiftPal` の `periodOnly = false` 分岐は
「copy/back なら空虚、watch なら DP 正当性」に割れる。**

次はこの割り方を実装して、空虚な側を落とす。

## 2026-09-19 n132: トップダウンに切り替え — `obligation_shiftPalAlongTrace` を 3 原子に割った

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット更新済み・緑。
公理は 4 → 6（1 本を 3 原子に割ったため）。無条件 PAL は未完。§10.5 は未達。**

### コウタの指摘（受けた）

* 「変によく考えず定理ふやすのやめよ」——今日だけで新規ファイル 6 本。
  CLAUDE.md に自分で「これ以上増やす前に、既にあるものを探す」と書いていながら守れていなかった。
  実際に効いたのは**削除・弱化**の方（`hwatch` の除去は「足した」のではなく依存を切った結果）。
* 「今残ってる前提を証明するためにトップダウンで」「せっかく機械的に残り前提検査
  できるようにしたんだから」——**found 経路の作業は `obligation_cycleOracle` の部分木の中**
  なので `#print axioms` の針が動かない。計器を使う形に戻す。

### やったこと

`PalInPegUnconditional.lean` の `axiom obligation_shiftPalAlongTrace` を
**`ShiftPalAlongTrace.shiftPal_alongTrace` の適用に置き換え**、足りない引数を
その場で原子的な `axiom` に切り出した。

| 新しい原子 | 中身 | producer 候補 |
|---|---|---|
| `obligation_readsShiftAlongTrace` | trace 各点で `H_readsShift` | `RoundSegFromRun.readsShift_at_actual` |
| `obligation_freshShiftAtShiftEntryAlongTrace` | trace 各 tick で `H_freshShiftAtShiftEntry` | `GalilScaffoldTopFirstRound.first_round` |
| `obligation_shiftPalAtFreshChainAlongTrace` | `periodOnly = false` 点での `ShiftPal` | 未特定 |

**2 つの側条件は文脈から出た**（新しい公理にならなかった）:

* `0 < w.length` — `w = []` なら `Tc 0 = 0`（`PreTrace.tc0`）で `1 ≤ j ≤ Tc w.length` が空虚
* `1 ≤ Tc w.length` — `PreTraceB.tc1`（`Tc 1 = 1`）＋ `PreTrace.mono`

### 現在の針（実測）

    [propext, Classical.choice, Quot.sound,
     obligation_cycleOracle,
     obligation_freshShiftAtShiftEntryAlongTrace,
     obligation_localRealization,
     obligation_readsShiftAlongTrace,
     obligation_shiftPalAlongRun,
     obligation_shiftPalAtFreshChainAlongTrace]

数は増えたが、これが CLAUDE.md の「公理は 1 場ずつの原子に分解する
（束ねると『1 個外す』が測れない）」。次は `obligation_shiftPalAlongRun` にも
同じ手（`CloseoutBundleRun.shiftPal_of_run_B`）を当て、そのあと原子を 1 本ずつ潰す。

## 2026-09-19 n131: `WatchMismatchNoShiftC` のガードを「tick できる相」に広げた

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

n130 で「正しい弱化先は `CopyOrBack ∨ watch`」と書いた線をそのまま実装した。

### 新規 `PalPeg/CopyPhaseNoShift.lean`（すべて標準公理）

| 定理 | 内容 |
|---|---|
| `tick_false_not_watch_or_posLag` | copy/back の background 1 手の行き先は、watch でないか、**lag が正の** watch |
| `not_shiftGuardVM_of_copyOrBack_tick` | **copy/back 相では不一致の行き先に shift guard が立たない** |
| `watchMismatchNoShift_parts_of_copyOrBack` | `WatchMismatchNoShiftC` の 2 節が copy/back 相でそろう |
| `TickablePhase` / `LiveScanTickable`（def） | 「tick できる相」＝ lag 正の `CopyOrBack` か watch |
| `liveScanTickable_ne_idle` | それは非 idle |

第 2 節の内訳:
* `.copy` から出た 1 手は `.copy` か `.back` で **watch ではない**（`chainStep_copy_shape`）
* `.back` から `backDone` で生まれた watch は **lag をそのまま受け継ぐ**
  （`chainStep_back_shape'`）。誕生 chain の lag は正なので `shiftGuardVM` の
  `zero w.lag = true` が落ちる

### ガードの差し替え

`CloseoutWatchRound22.WatchMismatchNoShiftC` の guard を
`LiveScanWatch c1 s1` → `CopyPhaseNoShift.LiveScanTickable c1 s1` に変更。
producer `CloseoutWatchRound23.watchMismatchNoShiftC_of_split` は**選言対応**にした:

* watch 相 → 従来どおり `TerminalRunFallbackGC` 経由
* copy/back 相 → `watchMismatchNoShift_parts_of_copyOrBack`（新しい直接経路）

変換補題 `CloseoutWatchRound22.liveScanTickable_of_liveScanWatch` を置いて、
既存の `LiveScanWatch` 消費者（Round22 / Round36）を通した。

**import の向き**: `CopyPhaseNoShift` は `CopyPhaseTickMatched` だけを import する
（`FoundPackRefute` を入れるとビルドサイクル——あれは `CloseoutFoundRoute1` を引く）。
その形なら `CloseoutWatchRound22` から import できる。

### 次

`WatchFallbackC` / `FallbackReachS` / `LandingRestartReachF` の guard も同じく
`LiveScanTickable` に広げる。そうすると `reachesWatchPhase_or_segEnd` の**第 2 枝**
（準備完了前の不一致）が `FoundExitLPS.landedS` に着地でき、節 4 の供給が閉じる。

## 2026-09-19 n130: `LiveScanWatch` ガードの線引きが確定した（`CopyOrBack ∨ watch` が正しい弱化先）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### 放電できたもの（検証済み）

| 定理 | 元の仮定 | 実際に使っていたもの |
|---|---|---|
| `CloseoutWatchRound21.fallbackLanding_of_pack` | `LiveScanWatch c1 s1` | `mode = scan ∧ replaying = false`（clock と watch を `obtain ⟨hm, hr, -, -⟩` で捨てていた） |
| `CloseoutWatchRound22.fallbackTick_of_watchTick` | `s1.chain = .watch w` | `s1.chain ≠ .idle`（watch は `≠ idle` を出すためだけ） |

`CloseoutWatchRun.LiveScanNonIdle`（`mode ∧ ¬replaying ∧ 1 ≤ clock ∧ chain ≠ idle`）と
`liveScanNonIdle_of_liveScanWatch` を追加。

### 弱化を試して**戻した**もの（正直な記録）

`WatchFallbackC` / `WatchMismatchNoShiftC` / `WatchFallbackCostC` / `LandingRestartReachF` /
`FallbackReachS` の guard を `LiveScanNonIdle` に弱める sweep を当てたが、
`CloseoutWatchRound23.watchMismatchNoShiftC_of_split` が
`TerminalRunFallbackGC`（`LiveScanWatch` guard を持つ watch ラウンドの機械）から
`WatchMismatchNoShiftC` を作っているので通らない。**これは形式化のミスではなく本物のギャップ。**

さらに **`≠ idle` だけでは足りない**ことも分かった:
`WatchMismatchNoShiftC` の第 1 節「`∃ z, ChainTick false s1.chain z`」は、
`ChainStep` が `.copy` から出るのに `CopyInv`（`t.focus = 8`、`t.left ≠ []`、
`read (left p) = some a`）を要求するので、任意の非 idle chain では出ない。

### 正しい弱化先（次に書くもの）

    CopyOrBack s1.chain ∨ (∃ w, s1.chain = ChainVM.watch w)      -- 「tick できる相」

この guard なら両節とも出る。材料は全部ある:

| 節 | copy/back 側の材料 |
|---|---|
| `∃ z, ChainTick false s1.chain z` | `CopyPhaseTick.copyOrBack_tick_false_exists` |
| `∀ vs vq, ChainTick false … → ¬ shiftGuardVM (afterMismatch …)` | `.copy` なら `FoundPackRefute.chainTick_copy_not_watch`；`.back` から `backDone` で生まれた watch は lag が正なので `shiftGuardVM` の `zero w.lag = true` が落ちる（`CopyPhaseTickMatched` の `LagPos` 系） |

つまり `watchMismatchNoShiftC_of_split`（watch 経路）の**兄弟**として
copy 相版の producer を書けばよい。`TerminalRunFallbackGC` を経由しない。

### 診断の定着（今日 4 件目）

**`LiveScanWatch` を取る定理は、まず本体での使われ方を数える。**
`obtain ⟨…, -, -⟩` で捨てているなら過剰。今日これで 4 件落ちた
（`split4_of_prefix` / `split3_of_prefix` / `fallbackLanding_of_pack` /
`fallbackTick_of_watchTick`）。**ただし「使っている」場合は本物**——
`TerminalRunC` / `TerminalRunFallbackC` / `watchMismatchNoShiftC_of_split` は弱められない。

## 2026-09-19 n129: 節 4 の供給 — `SegEnd` 枝は fallback へ。`LiveScanWatch` ガードの棚卸し

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### 放電済み（今回）

`CloseoutWatchRound21.fallbackLanding_of_pack` の `hlive : LiveScanWatch c1 s1` は
**過剰**だった——`obtain ⟨hm, hr, -, -⟩ := hlive` で clock と watch を捨てており、
使っていたのは `mode = scan` と `replaying = false` だけ。その 2 つに弱めて
呼び出し側 4 箇所（Round21/29/31/36）を通した。全体 build 緑。

### 次の設計判断（材料は揃っている）

`ReachesWatchFromRun.reachesWatchPhase_or_segEnd` の**第 2 枝**（準備完了前に不一致）を
`FoundExitLPS.landedS` に着地させたい。材料:

* 第 2 枝が返すのは `WatchSegE … es cP sP c' s'` ＋ `SegEnd P c' s'` ＋ `CopyOrBack s'.chain`
  ＋ `c'.mode = .scan` ＋ `c'.replaying = false`
* `SegEnd` は live 構成では `.mismatch` のみ（clock = 1、`canRight`、不一致）
* `FoundPackCorrected.no_shift_from_copyChain` が「`.copy` 相では shift guard が立たず
  `scan_fallback` へ」を証明済み
* `FoundExitLPS` は `exit` と `landedS` の 2 構成子で、fallback 着地は `landedS`

受け皿は `CloseoutWatchRound31.FallbackReachS` だが、その guard が `LiveScanWatch c1 s1`。

**訂正（自分の見立ての修正）**: これを「`s1.chain ≠ .idle`」まで弱めるのは**行き過ぎ**。
`ChainStep` が `.copy` から出るには `CopyInv`（`t.focus = 8`、`t.left ≠ []`、
`read (left p) = some a`）が要るので、「chain が 1 手進める」
（`WatchMismatchNoShiftC` の第 1 節）は任意の非 idle では出ない。
**正しい弱化先は「tick できる相」** :

    CopyOrBack s1.chain ∨ (∃ w, s1.chain = ChainVM.watch w)

`CopyOrBack` は `CopyInv` を含むので第 1 節が `copyOrBack_tick_false_exists` で出る。
第 2 節（不一致後に shift guard が立たない）は `.copy` 相では
`FoundPackRefute.chainTick_copy_not_watch` でむしろ**簡単**。

`LiveScanWatch` を guard に持つ定義の棚卸し（弱化候補）:

| 定義 | ファイル |
|---|---|
| `WatchFallbackC` | `CloseoutWatchRound21:85` |
| `WatchMismatchNoShiftC` / `WatchFallbackCostC` | `CloseoutWatchRound22:131` / `:143` |
| `LandingRestartReachF` | `CloseoutWatchRound29:104` |
| `FallbackReachS` | `CloseoutWatchRound31:246` |

**`TerminalRunC` / `TerminalRunFallbackC` の `LiveScanWatch` は本物**（watch 無しで
ラウンドは回らない）。弱化してはいけない。

### 診断の定着

**`LiveScanWatch` を取る定理は、まず本体での使われ方を数える。**
`obtain ⟨…, -, -⟩` で捨てているなら、その分は過剰。今日これで 3 件
（`split4_of_prefix` / `split3_of_prefix` / `fallbackLanding_of_pack`）が落ちた。

## 2026-09-19 n128: `hpack` の**両方の偽の節**（4 と 7）を found 経路から消した

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

n127 で節 4（`PrepLandingWatchC`）を消した。n128 で節 7（`BreakLandingC`）も同じ手で消えた。
**`FoundPackRefute` が反証した 2 つは、どちらも同じ 1 つの欠陥だった**——
`∀ es c2 s2, WatchSegE … cP sP c2 s2 → …` が `es = []`（＝`WatchSegE.stop`）を含むので、
誕生状態 `sP` 自身について主張してしまう。誕生直後の chain は `.copy` なので偽。

### 直し方（節 4 と節 7 で同一）

**着地に `(∃ w, s2.chain = ChainVM.watch w) →` のガードを足す。** それだけ。
消費者はそのガードを既に持っているか（`RoundsRouteLPraw` / `BreakRouteLPraw` は
`es.length = 2*hh+2` と `∃ ww, s2.chain = .watch ww` を渡す）、`hland` の出力から取れる。

ガードを足した定義（すべて trailing `∀`）:

| 定義 | ファイル |
|---|---|
| `ShiftTailC` | `CloseoutWatchPhase2:247` |
| `NoShiftTailC` | `CloseoutWatchPhase2:347` |
| `NoShiftTailC0` / `NoShiftTailC0L` | `CloseoutWatchPhase3:150` / `:382` |
| `BreakLandingC` | `CloseoutWatchRound5:409` |
| `BreakLandingLedgerC` | `CloseoutWatchRound10:208` |

### 反証の扱い

`FoundPackRefute.breakLandingC_false_of_foundCompareCtx` は**ガード無しの旧形**についての
定理として残した（`refuted_BreakLandingUnguardedC` を新設して、それを取る形に変更）。
現行のガード付き `BreakLandingC` には当たらない。**削除せず、なぜガードが要るかの記録として残す。**

### 帰結

`CloseoutFoundRoute1` の `hpack` 7 節のうち、**反証済みだった 2 節（4 と 7）が両方とも
真の形になった**。節 4 は `∃ es c2 s2, WatchSegE ∧ LiveScanWatch c2 s2`
（＝`ReachesWatchPhase` ＋ 制御 3 節）、節 7 はガード付き `BreakLandingC`。

公理の本数は変わらない（`hpack` は公理ではなく `obligation_cycleOracle` の部分木内部の
仮定）。**変わったのは、その部分木が偽の仮定を 1 つも通らなくなったこと。**

## 2026-09-19 n127: 反証済み `PrepLandingWatchC`（`hpack` 節 4）を found 経路から**消した**

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

コウタの指摘 2 つがそのまま当たった:

* 「難しく考えなさんな。未解決問題とはいえ難問というより単純に規模が大きいだけの問題」
* 「producer がいないってことはモデル化を何か間違ってる」

### 何が間違っていたか

`CloseoutWatchRound23.split4_of_prefix` は `hliveP : LiveScanWatch cP sP`
（＝誕生状態の chain が `.watch`）を取っていたが、**本体で 1 回しか使っておらず、
しかも `sP.chain ≠ ChainVM.idle` を取り出すためだけ**だった。誕生直後の chain は
`.copy` なので `.watch` は偽（`FoundPackRefute`）、しかし**非 idle は真**で、
`FoundCompareCtxC` が `ch ≠ ChainVM.idle` を конъюнкт として直接持っている。

`CloseoutWatchRound40` の docstring は「`exitSplit4C_of_tick` は `.watch` を要求するが
`ChainW` は `.copy`/`.back` のこともある」と書いて**新しい仮定を立てる方向へ逃げていた**。
仮定を弱めるのが正しかった。**自分の過去の記述を判断材料にした失敗の再発。**

### 効いた置き換えは 2 種類だけ

| 消費者が要求していたもの | 実際に使っていたもの | 出どころ |
|---|---|---|
| `LiveScanWatch cP sP`（誕生状態が watch） | `sP.chain ≠ .idle` | `CloseoutWatchRound2.chain_ne_idle_of_foundCompareCtx`（新規、タダ） |
| 全着地で `LiveScanWatch`（`hlive`） | その着地の watch だけ | `∀` にガードとして追加（`TerminalRunShiftC` は元から同じガードを持っていた） |

**producer が無かったのは、`ShiftTailC` の末尾 `∀` にガードが無く、それを供給するのが
`TerminalRunShiftC`（ガード付き）だったから。** 橋渡しのためだけに `hlive` が要り、
その `hlive` が `hwatch` を要求していた。ガードを揃えたら鎖ごと消えた。

### 変更（全体 build 緑）

* `CloseoutWatchPhase2.ShiftTailC` — 末尾 `∀ es c2 s2` に watch ガードを追加
* `watchSegE_live_control` を `CloseoutWatchRound7` → `GalilScaffoldTopWatchSegE`（定義ファイル）へ移動。
  `WatchSegE` の素の構造的事実なのに下流に埋まっていて上流から使えなかった
* `split4_of_prefix` / `exitSplit4C_of_tick`（Round23）、`split3_of_prefix` /
  `exitSplit3C_of_tick`（Round19）、`exitSplit4C_of_liveScanWatch`（Round42）— 仮定を弱化
* `shiftExitTailC_of_parts` / `breakExitTailC_of_parts`（Round5）、
  `breakExitTailLC_of_parts`（Round10）、`mismatchShift_to_shiftRoute`（Round25）、
  `shiftTailC_of_dataL`（Round37）/ `dataL'`（Round41）— `hlive` を**引数ごと削除**
* `foundExit_of_split3` / `_split3S` / `_split3F` の 3 変種 — **到達 watch 着地版**に置換
  （`foundExit_of_split3_atReachedWatch` ほか）。仮定は
  `∃ es c2 s2, WatchSegE … cP sP c2 s2 ∧ LiveScanWatch c2 s2`
* `CloseoutFoundRoute1` の `hpack` 束の**節 4 を同じ形に差し替え**
* Round14/15 は `hwatch` を完全に失った

### 帰結

**`(hwatch : PrepLandingWatchC …)` の宣言は `PalPeg/` 全体で 0 本になった**
（残る参照は `open` 行と docstring のみ）。found 経路は反証済みの仮定に依存しなくなり、
代わりに要求するのは `∃ es c2 s2, WatchSegE ∧ LiveScanWatch c2 s2`——これは
`FoundPackCorrected.ReachesWatchPhase` ＋ `watchSegE_live_control` そのもので、
n125/n126 で作った `ReachesWatchFromRun.reachesWatchPhase_or_segEnd_at_foundBirth` の
**第 1 枝が出す**。第 2 枝（`SegEnd` で早期終了＝準備中の不一致）の配線が次の仕事。

公理の本数は変わらない（`hpack` は公理ではなく `obligation_cycleOracle` の部分木内部の
仮定だった）。**変わったのは、その部分木が偽の仮定を通らなくなったこと。**

## 2026-09-19 n126: `PalInPegUnconditional.lean` の docstring が腐っていた（表 9 行 vs `axiom` 4 本）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

コウタの指摘「4 本って書いてることとちゃうやん」で発覚。照合結果:

| 出どころ | 数 |
|---|---|
| `#print axioms PalPeg.PalInPeg.unconditional` | **4**（`shiftPalAlongRun` / `shiftPalAlongTrace` / `cycleOracle` / `localRealization`） |
| `grep "^axiom " PalPeg/PalInPegUnconditional.lean` | **4**（`:85` `:96` `:104` `:109`） |
| `CLAUDE.md:102` | **4** |
| **同ファイルの docstring の表** | **9 行**（← ズレていたのはここだけ） |

`obligation_verifierRunAlongRun` / `matchLanding_alongTrace` / `shiftEntryLanding_alongTrace` /
`chainBackLag_alongTrace` / `shiftExitLedger_alongTrace` / `rewindMargin_alongTrace` の 6 行が、
**既に存在しない公理を載せたまま**だった（`axiom` 宣言ゼロ、参照は docstring のみ）。
経路メモは捨てずに「公理としては消えた 6 本」節へ移した。

**CLAUDE.md の「ファイル自身の docstring も一次情報ではない」に自分で引っかかった。**
n116 で `CloseoutRealize1.lean` について同じことを書いたのに、正本の入口ファイルで
同じ腐り方をさせていた。**数えるときは `grep "^axiom "` か `#print axioms`。**
表を書き換えるときは同時に `axiom` 宣言と突き合わせる。

## 2026-09-19 n125: live chain 版の区間構成ができた — clock の余裕は要らなかった（n124 の訂正 2 段）

**全体 build 成功（EXIT=0、エラー 0、`sorry` ゼロ）。ラチェット緑。公理は 4 義務のまま。
無条件 PAL は未完。§10.5 は未達。**

### まず訂正 2 段（自分の見積もりが 2 回とも外れた）

**訂正 1（n124 が甘かった）**: 「残る外部入力 4 つのうち最後の 1 つ
`clock の余裕 n < cP.clock` は予算層の話」と書いたが、`watchSegE_backgroundRun_live`
（`.count` / `.wait` だけで作る区間）が走れるのは高々 2047 手で、準備に要る `2h+2` 手は
`h ≤ 1022` の入力にしか収まらない。一次情報:

* `WatchSegE.count` は `1 < c.clock` を要求し `clock := c.clock - 1`（`GalilScaffoldTopWatchSegE.lean:26`）
* `WatchSegE.match` は `c.clock = 1` を要求し `clock := delay`(=2048) に戻す（同 `:33`）

**訂正 2（訂正 1 のあと考えすぎた）**: そこから「`ReachesWatchPhase` の無条件形は
成り立たない、選言に作り直して消費者も書き換えが要る」と書いた。**これは考えすぎ。**
既存の idle chain 版 `GalilSegmentConstructB.watchSegE_constructB` は `n < c.clock` を
**要求していない**——clock を構成の中で処理し、結論は既に
`es.length = n ∨ SegEnd P c' t` という 2 択になっている。呼び出し側が渡す `n` は
`headRank r.right * 2048 + c.clock`（入力が尽きるまでの全機械ステップ数）。

**live chain 版も同じ形でよかった。** 新しい概念は要らない。
異なる操作的意味論を持つ機械同士の対応を、既にある型に合わせて写すだけ。

### 今日証明したもの（すべて標準公理、`sorry` ゼロ）

**`PalPeg/ChainReachesWatchFromFound.lean`（新規）**

| 定理 | 内容 |
|---|---|
| `chainReachesWatch_of_found` | found 文脈から「長さ `2h+2` の任意のイベント列で watch に着く」 |

`found_to_watchStart_least` の `dm`（中央の事象）は**引数**なので、`list_split_mid` が
出す実際の中央要素ごとに定理を当て直す。そのとき `h` が揺れないことを保証するのが
`hCursor : (denote y.config).pos 11 = h`（DP 出力カーソル）。**これが無いと `h` の
一意性が言えず、「長さ `2h+2`」という主張そのものが `dm` 依存になって壊れる。**
誕生 chain と `chainStart` の同一視は `chainMatched_unique`。

**`PalPeg/CopyPhaseTickMatched.lean`（新規）** — `.match` を区間に載せるための前提

| 定理 | 内容 |
|---|---|
| `LagPos`（def） | chain の lag が正（`.copy` / `.back` 相でだけ内容がある） |
| `lagPos_tick` | `LagPos` は 1 tick で保たれる（事象によらず） |
| `lagPos_chainStart` / `lagPos_of_chainMatched_chainStart` | 誕生時の lag は `radius = ofNat (r0+1)` で正 |
| `chainStep_back_shape'` | `.back` の 1 手は lag を保った `.back` か lag を受け継いだ `.watch` |
| `backChain_tick_true_exists` | **`.back` 相でも一致事象の `ChainTick` は存在する**（lag 正のとき） |
| `copyOrBack_tick_true_exists` | `CopyOrBack` ＋ lag 正なら一致事象でも 1 手ある |
| `copyOrBack_tick_true` | 一致事象でも相は copy/back か watch に閉じる |

**以前 `sorry` を書きかけた場所の本当の障害はここだった。** `.back` から `backDone` で
生まれた watch に `ChainMatched` を当てるには `Outer w true w'` が要り、その 2 枝は
`queued`（`zero w.lag = false`）と `immediate`（`zero w.lag = true` ∧ `Good w`）。
`Good` は誕生時には出ない（`WatchOkRefute.watchOk_false`）。しかし
**誕生した chain の lag は正**（`chainStart … radius` が `lag = margin = radius` を置き、
copy/back の `ChainStep` は lag を触らず `ChainMatched` は `inc` するだけ）なので
`Outer.queued` が無条件に使え、`Good` は要らない。
同じ正値が `ChainMatched.breaks`（`BreakStep` は `zero w.lag = true` を要求、
`GalilScaffoldTopChainVM:27`）も排除する。

**不変量は `positive` で書くこと。** `zero lag = false` では `inc` で保たれない
（`⟨[], [()]⟩` の `inc` は `reset`）。`positive` なら保たれる。

**`PalPeg/LiveSegmentConstruct.lean`（新規）** — `constructB` の live chain 版

| 定理 | 内容 |
|---|---|
| `match_step_live` | 一致比較 1 手分の証人（`WatchSegE.match` の側条件をすべて作る） |
| `watchSegE_constructLive` | **live chain 版の区間構成。clock の余裕は要らない** |

探索側の帳簿（`ReadyFuel` / `hsearch`）は live chain では**丸ごと不要**——
`searchEffect P a s v` は `s.chain ≠ .idle` の枝で `v = searchLens.get s` に潰れ、
`chainBorn` も `false` になるので誕生も起きない。`SegEnd` の 5 枝のうち live で
実際に出るのは `.mismatch` だけ（`.ended` は `.wait` で素通しして chain を進める方が得、
`.found` / `.foundBackground` は探索が不活性、`.lastLetter` は入力側の都合）。

**`PalPeg/ReachesWatchFromRun.lean`（新規）** — 橋

| 定理 | 内容 |
|---|---|
| `reachesWatchPhase_or_segEnd` | **`ReachesWatchPhase` ∨ `SegEnd` で早期終了**（clock の余裕なし） |
| `prepLandingWatchC_or_segEnd` | 節 4 の正しい形まで（到達した側） |

### 次にやること

1. found 文脈から `reachesWatchPhase_or_segEnd` の 3 入力を作る配線:
   `CopyOrBack sP.chain`（`copyOrBack_of_chainMatched_chainStart` ＋ `copyInv_of_found`）、
   `LagPos sP.chain`（`lagPos_of_chainMatched_chainStart`）、
   `hChainReachesWatch`（`chainReachesWatch_of_found`）。
   `FoundCompareCtxC`（`CloseoutWatchRound2:270`）が `ChainMatched (chainStart … sF.radius) ch` と
   `sP = afterBirth true (afterCompare …)` を持っているので材料は揃っている。
   **残る側条件は `sF.radius = ofNat (r0+1)`**（`found_to_watchStart_least` が
   `ofNat (r0+1)` 形を要求し、`LagPos` も `positive sF.radius` を要求する）。
   これは radius 台帳の話で、found 時点で radius が正の canonical counter であること。
   `hmP` / `hrP` / `hcP`（`1 ≤ cP.clock`）は `foundExit_compare_final20` に既にある。
2. その 2 択を `foundExit_compare_final18` の節 4 / 節 7 に配線する。**消費者側を
   書き換える必要がある**（`hpack` の `∀` 形は `FoundPackRefute` で反証済み）。
3. 4 義務のうち最短は `obligation_shiftPalAlongTrace`。`ShiftPalAlongTrace.
   shiftPal_alongTrace` が既に正しい形で、残差は `H_readsShift` / `H_freshShiftAtShiftEntry` /
   `hFreshBranch` の 3 本。ただし `H_readsShift` の producer
   `RoundSegFromRun.readsShift_at_actual` は前ラウンド起点の `OriginAt` と
   構成 run / 実 run の対を要求するので、1 手では落ちない。



































## 2026-09-19 n124: 節 4 / 節 7 の供給経路が繋がった — 残るは `AnswerAhead` の復号 1 本

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 今日繋げた経路（すべて標準公理、`sorry` ゼロ）

    FoundCompareCtxC
      → copyOrBack_of_chainMatched_chainStart      （CopyPhaseTick）
      → CopyOrBack sP.chain
      → watchSegE_backgroundRun_live               （CopyPhaseTick、帰納の本体）
      → 「watch 到達」∨「n 手走破でまだ copy/back」
      → reachesWatchPhase_of_backgroundRun         （FoundPackCorrected）
      → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch          （節 4 の正しい形）
        reachesWatchPhase_of_breakLandingAtReachedWatch（節 7 も同じ供給）

### 残る外部入力は 4 つ、うち 3 つは found 文脈にある

| 入力 | 出どころ | 状態 |
|---|---|---|
| chain が `n` 手で watch に着く | `GalilPrepLeast.found_to_watchStart_least` | **既存**（イベント列の中身を問わない） |
| clock の余裕 `n < cP.clock` | 誕生時の clock は `delay = 2048`、`n = 2h+2` | 予算層 |
| `PlaceAhead walker n` | `GalilPrepLeast.found_copy_walk_least` の `CopyWalk` | 既存（取り出しは未実装） |
| **`AnswerAhead answer n`** | `GalilScaffoldChainAnswer.found_output` の復号 | **未実装（次の 1 本）** |

### `AnswerAhead` の復号（次にやること）

`found_output` は `SafeQuanta` ＋ `Result` から

    denote (y.config.tapes 11) = GalilDpCounters.output h ∧
    head (y.config.tapes 11) = h ∧ (tapes 11).focus = 8 ∧ (tapes 11).left ≠ []

を与える（標準公理）。一方

    output h i = if i = 0 then 4 else if i ≤ h then 8 else 6
    denote t   = read (t.left.reverse ++ t.focus :: t.right)
    head t     = t.left.length
    AnswerAhead t n := ∃ ls, t.focus :: t.left = List.replicate n 8 ++ 4 :: ls

なので、`t.left.reverse` は index 0..h-1 で `[4, 8, …, 8]`、つまり
`t.left = [8, …, 8, 4]`（8 が `h-1` 個）、`t.focus` は index `h` で `8`。
したがって `t.focus :: t.left = List.replicate h 8 ++ 4 :: []` で
**`AnswerAhead t h` が `ls = []` で成り立つ**。

証明は `denote` の index 等式からリスト等式を復元する機械的な作業
（`List.ext_getElem?` 系）。**これが節 4 / 節 7 の供給に残る唯一の未実装。**

### `StartShape` は使わないこと

`GalilLeafStartShape.not_startShape` が**あらゆる `Shared` について**反証済み
（`∀ s : GalilVM` が無制約で、`.found` 状態の任意の VM に DP の形を要求する）。
`AnswerAhead` / `PlaceAhead` は `found_copy_walk_least` / `found_output` から取ること。

## 2026-09-19 n123: live chain 版区間構成の材料一覧（これで全部）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

次のセッションが `GalilSegmentConstructB.watchSegE_constructB` の live chain 版を
書くときに要るものを、**全部一次情報で確認して**並べる。

### chain 側（すべて既存、標準公理）

| 定理 | 場所 | 内容 |
|---|---|---|
| `copy_step_exists` | `GalilBranchInvariants:350` | `CopyInv` から `ChainStep` の存在 |
| `copyInv_step` | `GalilBranchInvariants:369` | `CopyInv … (n+1)` は 1 手で `CopyInv … n` |
| `copy_run_to_back` | `GalilBranchInvariants:383` | copy 相は `n+1` 手で `.back` に着き `OnBlock v'` を渡す |
| `chainReady_of_blockInv` | `GalilChainReadyProgress:59` | `BlockInv` ＋ 各相の追加事実から `ChainReady` |
| `found_to_watchStart_least` | `GalilPrepLeast:121` | `SafeQuanta` ＋ `Result` から `ChainTicks (bs ++ dm :: cs) x1 (.watch (watchStart …))`（イベント列の中身は任意） |

### 今日足した差分（`PalPeg/CopyPhaseTick.lean`、標準公理）

| 定理 | 内容 |
|---|---|
| `chainStep_copy_shape` | `.copy` から出る `ChainStep` の行き先は `.copy` か `.back` |
| `chainMatched_exists_copy_or_back` | その両方に `ChainMatched` の構成子がある |
| `copyChain_tick_exists` | よって `ChainTick a` は一致ビット `a` によらず存在する |
| `copyChain_tick_not_idle` | 行き先は idle にならない（次段の `WatchSegE.match` の側条件） |

### run 側（既存、模倣する対象）

| 定理 | 場所 | 内容 |
|---|---|---|
| `watchSegE_constructB` | `GalilSegmentConstructB:124` | **idle chain 版**。結論は `(es.length = n ∨ SegEnd P c' t)` |
| `watchSegE_constructS` | `CloseoutReadyStage:544` | 同上（`ReadyPacedS` 版） |
| `watchSegE_events` | `GalilScaffoldTopWatchSegE:170` | 区間から `ChainTicks es s.chain t.chain`（`chain ≠ idle` が要る） |
| `chainTicks_unique` | `GalilScaffoldTopChainUnique:87` | `ChainTicks` は行き先を一意に決める |

### 到達後（今日実装、`PalPeg/FoundPackCorrected.lean`）

    reachesWatchPhase_of_chainTicks → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch（節 4 の正しい形）
      → BreakLandingAtReachedWatch / reachesWatchPhase_of_breakLandingAtReachedWatch（節 7）

### 書くべきもの（唯一の残り）

`watchSegE_constructB` の **live chain 版**。変更点は 3 つだけ:

1. 不変量 `s.chain = ChainVM.idle` を「`s.chain` が `.copy` で `∃ n, CopyInv …`」に替える
   （`copyInv_step` で運ぶ）。
2. 構成子は `matchIdle` / `countR` / `matchIdleR` の代わりに `match` / `count` / `wait`
   （`WatchSegE.match` の側条件は `s.chain ≠ .idle` だけ、`copyChain_tick_not_idle` で維持）。
3. chain の 1 手は `copyChain_tick_exists` から取る（`WatchOk` 経由は不可、反証済み）。

`MInv` と `ScanInvariant` は chain に触れないので `constructB` の扱いをそのまま使える。

## 2026-09-19 n122: live chain 版区間構成の材料も既にある（`copy_step_exists`）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

n121 で「live chain 版 `watchSegE_construct` が唯一の残り」と測った。その構成に要る
**chain 側の全域性**も既存だった:

* `GalilBranchInvariants.copy_step_exists`（`:350`）— `CopyInv t h p v n` から
  `∃ y, ChainStep (.copy t h p v lag margin ver) y`（**copy tick の全域性**）
* `GalilBranchInvariants.onPrefix_start` / `onPrefix_put` — `OnPrefix` の維持
* `GalilChainTickable`（`:186`, `:201`）にも `.copy` からの `ChainStep` 構成がある

したがって live chain 版の帰納は

| 必要なもの | 出どころ |
|---|---|
| chain の 1 手（`.copy` 相） | `copy_step_exists`（`CopyInv` から） |
| `WatchSegE.match` の側条件 | `s.chain ≠ .idle` のみ（`GalilScaffoldTopWatchSegE:34`） |
| `MInv` / `ScanInvariant` の維持 | chain に触れないので `constructB` と同じ扱い |
| 結論の選言 | `(es.length = n ∨ SegEnd P c' t)` をそのまま踏襲 |

で組める。**残っているのは `CopyInv` を誕生から区間に沿って運ぶ部分と、
`constructB` の並行版を書く作業（~150 行の帰納法）。**

`WatchOk` 経由の `chainOk_tick_false` は使えない（`WatchOk` は反証済み、
`WatchOkRefute.watchOk_false`）。`CopyInv` 経由で行くこと。

## 2026-09-19 n121: `ReachesWatchPhase` の最後の 1 ピースは「live chain 版の区間構成」

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 測ったこと

区間構成の既存定理は 2 本:

* `CloseoutReadyStage.watchSegE_constructS`（`:544`）
* `GalilSegmentConstructB.watchSegE_constructB`（`:124`）

どちらも

    s.chain = ChainVM.idle → … →
    ∃ es c' t r', WatchSegE P q first delay es c s c' t ∧ … ∧ t.chain = ChainVM.idle ∧ …
      ∧ (es.length = n ∨ SegEnd P c' t)

**`chain = idle` を要求し、かつ保存する**——つまり**誕生前の相専用**。

**誕生後（`.copy` 相）の live chain 版は存在しない。** これが `ReachesWatchPhase` に
残る唯一のピース。

### 良い知らせ

* 結論の形 `(es.length = n ∨ SegEnd P c' t)` は**まさに必要な選言**
  （「`n` 手走る」か「区間が終わる」）。設計はそのまま使える。
* `GalilLiveCentreReplay.MInv` は **chain に触れない**（replay と中心の事実だけ）。
  `ScanInvariant` も同様。したがって live chain 版は構造的に並行で、
  `matchIdle` / `countR` / `matchIdleR` の代わりに `match` / `count` / `wait` を使うだけ。
* `WatchSegE.match` が要求するのは `s.chain ≠ .idle` だけ（`GalilScaffoldTopWatchSegE:34`）で、
  `.copy` 相はそれを満たす。chain は誕生後 idle に戻らない。

### `ReachesWatchPhase` の残り（これで全部）

    live chain 版 watchSegE_construct（未実装、~150 行、既存 constructB の並行版）
      → 長さ 2h+2 の区間
      → reachesWatchPhase_of_chainTicks（今日実装、標準公理）
      → ReachesWatchPhase
      → prepLandingWatchC_at_reachedWatch / BreakLandingAtReachedWatch（今日実装）
      → hpack の壊れていた 2 節の正しい形

chain の中身（`found_to_watchStart_least`）も、shift に行けないこと
（`no_shift_from_copyChain`）も、橋（`reachesWatchPhase_of_chainTicks`）も済んでいる。

## 2026-09-19 n120: `hpack` 7 節の監査完了 — **壊れているのはちょうど 2 節、同じ欠陥**

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

`CloseoutFoundRoute1.foundExit_compare_final20` の `hpack`（7 節の束）を
1 節ずつ定義に当たって測った結果:

| # | 節 | 判定 | 理由 |
|---|---|---|---|
| 1 | `PrepInputsG3` | **健全** | `ChainMatched (chainStart …) sP.chain` を言う。誕生直後の `.copy` と整合 |
| 2 | `MismatchExitG` | **健全** | `GalilPrepMatch.PrepChain s1.chain` で guard（prep 相向けに設計されている） |
| 3 | `FallbackReachS` | **健全** | `LiveScanWatch c1 s1` を**仮説**に取る（watch でなければ空虚） |
| 4 | `PrepLandingWatchC` | **偽** | `∀ es c2 s2, WatchSegE … → ∃ w, s2.chain = .watch w`。`WatchSegE.stop` で `sP` 自身に当たる |
| 5 | `PrepBirthLagC'` | **健全** | 誕生データ（`sP = afterBirth true (afterCompare …)`）を仮説に取る |
| 6 | `LandingFreshC'` | **健全** | `s1.chain = .watch w` を**仮説**に取る |
| 7 | `BreakLandingC` | **偽** | `∀ es c2 s2, WatchSegE … → s2.chain = .watch (freshWatch …)`。同じ形 |

**壊れているのはちょうど 2 節で、どちらも同じ形**——
「`∀ (WatchSegE 区間)` の結論で watch を要求する」。`WatchSegE.stop cP sP` が
無条件に存在するので、その `∀` が誕生状態 `sP` 自身に当たる。

機械検査（`PalPeg/FoundPackRefute.lean`、標準公理のみ）:

    hpack_false_of_foundCompareCtx          （節 4）
    prepLandingLiveC_false_of_foundCompareCtx（節 4 の親戚 `PrepLandingLiveC`）
    breakLandingC_false_of_foundCompareCtx   （節 7）
    hpack_false_of_foundReachable            （到達可能性込み）

### 直し方（節 4 は実装済み、節 7 は同型）

`FoundPackCorrected.ReachesWatchPhase`（`∀` → `∃`）に付け替え、到達先で主張する。
節 4 については `prepLandingWatchC_at_reachedWatch` が既存 producer
（`CloseoutWatchRound10.prepLandingWatchC_of_short`）をそのまま当てる形で実装済み。
節 7 も同じ形に直せる（`BreakLandingC` の結論を到達先 `(c2, s2)` で主張する）。

**5 節は触らなくてよい。** 健全な 5 節を巻き添えで書き換えないこと。

## 2026-09-19 n119: `ReachesWatchPhase` の chain 側は既に証明済み — 残りは「誕生後 `2h+1` tick を scan で走れるか」

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### chain 側（既存、無条件）

`GalilPrepLeast.found_to_watchStart_least`（および `GalilScaffoldTopChainEntry.found_to_watchStart`）は、
`SafeQuanta` ＋ `GalilDpCorrect.Result` から

    ∃ h c ys b, Candidate w lower h ∧ read p = some c ∧ ys.length + 1 = h ∧
      (denote y.config).pc = 346 ∧ (denote y.config).pos 11 = h ∧
      ∀ bs cs, bs.length = h → cs.length = h+1 →
        ∃ x1, （x1 は chainStart …（または ChainMatched 1 歩））∧
          ChainTicks (bs ++ dm :: cs) x1 (.watch (watchStart ver c ys b …))

を与える。**イベント列 `bs` / `cs` の中身には条件が無い**（長さだけ）。
そして `SafeQuanta` ＋ `Result` は `GalilScaffoldSearchRun.calibrated_quanta_safe` が
無条件に出す（n114）。

**つまり「誕生した chain は `2h+1` tick で watch になる」は既に証明済み。**

### 残りは run 側の条件（そしてそれは無条件ではない）

`ReachesWatchPhase` に必要なのは、その `2h+1` tick が**実際に走ること**＝
`WatchSegE` が誕生から `2h+1` 手続くこと。`WatchSegE` の構成子はすべて
`c.mode = .scan` を要求するので、途中で scan を離れたら区間が切れる。

**そして途中で scan を離れる経路が実在する。** copy/back 相の chain は `.watch` では
ないので `shiftGuardVM`（`s.chain = .watch w` を要求）が立たず、不一致が来たら
`Tick.scan_shift` は使えず `scan_fallback` になる
（既存の定理 `not_shiftGuard_afterMismatchB`、CLAUDE.md §3c に記録あり）。

したがって正しい形は**選言**:

    「誕生後 `2h+1` tick 走って chain が watch になる」
      ∨ 「その前に不一致が来て fallback に落ちる（chain は捨てられる）」

found 経路のラウンド機構は**前者の枝でだけ**適用できる。
`FoundPackCorrected.ReachesWatchPhase` は前者を名指したもので、
`prepLandingWatchC_at_reachedWatch` がその到達先で既存 producer を当てる。

### 次にやること

1. 選言の後者（fallback 枝）を `foundExit_compare_final20` の結論側で吸収する形に切り直す。
2. `hpack` の残り 6 節（`MismatchExitG` / `FallbackReachS` / `PrepBirthLagC'` /
   `LandingFreshC'` / `BreakLandingC` / `PrepInputsG3`）を**同じ目で**洗う——
   誕生直後の状態に watch 相の性質を要求していないか。
   （`PrepInputsG3` は `ChainMatched (chainStart …) sP.chain` を言うので整合的。
   `LandingFreshC` は Round 44 で既に反証済み。）

## 2026-09-19 n118: **found 経路が閉じなかった根本原因**（`PrepLanding*` 一族が誕生直後に watch を要求）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 機械検査した事実（`PalPeg/FoundPackRefute.lean`、標準公理のみ）

| 定理 | 内容 |
|---|---|
| `chainMatched_copy_stays_copy` | `ChainMatched` は `.copy` から `.copy` にしか行かない |
| `chainStart_is_copy` | `chainStart` は `.copy`（`rfl`、公理ゼロ） |
| `prepLandingLiveC_watch_start` | `PrepLandingLiveC cP sP` → `∃ w, sP.chain = .watch w` |
| `hpack_false_of_foundCompareCtx` | `FoundCompareCtxC` ＋ `PrepLandingWatchC` → `False` |
| `prepLandingLiveC_false_of_foundCompareCtx` | `FoundCompareCtxC` ＋ `PrepLandingLiveC` → `False` |
| **`hpack_false_of_foundReachable`** | **`InvLPC` ＋ `SegReachedW` ＋ found 比較 → `False`** |

### 根本原因

`CloseoutWatchRun.LiveScanWatch c s` の最終節は `∃ w, s.chain = .watch w`。
`PrepLandingLiveC` / `PrepLandingWatchC` はどちらも
`∀ es c2 s2, WatchSegE … cP sP c2 s2 → …` の形で、`WatchSegE.stop cP sP` が
無条件に存在するため `es = []` 実例で **`sP` 自身が watch であること**を強制する。

ところが found 比較直後の `sP` の chain は `chainStart …`（`.copy`）から
`ChainMatched` で 1 歩進んだもので、**`ChainMatched` は構成子の形を保つ**
（`.copy → .copy` / `.back → .back` / `.watch → .watch` / `.watch → .broken`、
`GalilScaffoldTopChainVM:69`）から、必ず `.copy`。

**つまり found 経路の設計は「chain は誕生直後から watch している」を前提にしている。**
モデルは Scala 正本どおり `chain.start()` が `.copy` 相を作り、周期を写し、巻き戻し、
それから `.watch` になる。1 tick では届かない。

**これが found 経路が閉じなかった根本原因**と見られる。`hpack`（7 節の束）を
証明しようとしていた作業は、偽の命題を証明しようとしていた。

### 直し方の方向（未実施）

`PrepLanding*` を `sP`（found 比較直後）ではなく、**chain が `.watch` になった後の
landing** で主張する。`CloseoutWatchRound10.prepLandingWatchC_of_short` は
watch 始点 ＋ clock 上界から `PrepLandingWatchC` を出すので、正しい場所では真。
`FoundCompareCtxC` から watch 相までを繋ぐ区間（copy → back → watch）を
別に持つ必要がある。

### 副次的な修理

`CloseoutFoundRoute1` はビルド不能だった（`:238` の `StepsAll.zero` 型不整合、
モデル修正 `M-periodOnly` の取り残し）。直した（`afterBirth` はヘッドを触らないので
`OutputRel` / `ScanInvariant` / `chain` は congruence で移る）。
これで `foundCompareCtxC_of_found` が使えるようになり、到達可能性込みの反証が書けた。

## 2026-09-19 n117': **`hpack` は REFUTED（条件付き）** — 機械検査済み

`PalPeg/FoundPackRefute.hpack_false_of_foundCompareCtx`（標準公理 `propext`/`Quot.sound` のみ）:
`FoundCompareCtxC` の証人 ＋ `PrepLandingWatchC` から `False`。決め手は
**`ChainMatched` が構成子の形を保つ 1 歩の関係**であること
（`.copy → .copy` / `.back → .back` / `.watch → .watch` / `.watch → .broken`、
`GalilScaffoldTopChainVM:69`）で、`chainStart` は `.copy`（`:41`）だから
`ch` は `.watch` になれない。

**未構成の証人は `FoundCompareCtxC`** なので `REFUTED（条件付き）`。
また `CloseoutFoundRoute1` 自体はビルドが壊れている（`:238`、`StepsAll.zero` の型不整合）。

下は反証前の記録。

## 2026-09-19 n117: found 経路の `hpack` は**偽の疑いが濃い**（節どうしが衝突している）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 一次情報で見たこと

`CloseoutFoundRoute1.foundExit_compare_final20` の `hpack` は

    ∀ cP sP a ls rs qw gap,
      FoundCompareCtxC centre place entry q first w c r cP sP → w = … →
      PrepInputsG3 … cP sP ∧ MismatchExitG … ∧ FallbackReachS … ∧
      PrepLandingWatchC … cP sP ∧ PrepBirthLagC' … ∧ LandingFreshC' … ∧
      (∀ sF, BreakLandingC … sF cP sP)

**節 4 `PrepLandingWatchC` は `sP.chain` が watch であることを強制する。**
定義（`CloseoutWatchRound7:123`）は

    ∀ es c2 s2, WatchSegE P q first 2048 es cP sP c2 s2 → ∃ w, s2.chain = .watch w

で、`WatchSegE.stop cP sP` は無条件に存在するから `es = []` 実例で `s2 = sP` となり
`∃ w, sP.chain = .watch w` が出る（これは既存の定理
`CloseoutWatchRound8.prepLandingWatchC_watch_start` そのもの）。
同ファイル `:341` には `not_prepLandingWatchC_of_idle`
（「無制限の `PrepLandingWatchC` は idle 始点で偽。**この述語は書かれていない前提を
持っている**」）という反証まで既にある。

**ところが guard の `FoundCompareCtxC`（`CloseoutWatchRound2:270`）は
`sP = afterBirth true (afterCompare sF ⟨…⟩ vq)`、すなわち `sP.chain = ch` で、
`ch` は `ChainMatched (chainStart …) ch ∧ ch ≠ .idle` を満たす**任意**の chain。
`chainStart` は `.copy` なので `ch` は `.copy` でありうる。** つまり
found 比較の**直後**（chain が生まれたばかり）に `sP.chain` が watch であることを
要求している。chain は 1 tick に 1 歩しか進まないので、これは成り立たないはず。

### 位置づけ

* `hpack` は 7 節の**束**。CLAUDE.md「葉を束に畳み込むと偽になりうる」の典型。
  しかも `hpack` という名前は**前にも偽になっている**（`CloseoutPackRefute.hpack_false`）。
* `PrepLandingWatchC` 自身は偽ではない。正しい場所（chain が watch になった後の
  landing）で使えば真で、producer もある（`CloseoutWatchRound10.prepLandingWatchC_of_short`、
  watch 始点 ＋ clock 上界から）。**束ねる場所が間違っている。**

**`REFUTED` とは書かない**（`False` を導く機械検査済みの定理がまだ無い）。
反証のレシピ: `FoundCompareCtxC` の証人を 1 つ作り（`WatchSegE` / `searchEffect` /
`refresh` の証人が要る、ここが手間）、`ch` を `chainStart …` の直後の `.copy` に取る。
そのうえで `prepLandingWatchC_watch_start` を当てれば `.copy = .watch w` で矛盾。

### 次に触るときの指示

**`hpack` を束のまま証明しようとしない。** 7 節を個別に、それぞれ正しい guard の下で測る。
特に `PrepLandingWatchC` / `PrepBirthLagC'` / `LandingFreshC'` は
「chain が watch になった後」の述語なので、found 比較直後の `sP` で要求するのは誤り。
（`LandingFreshC` は Round 44 で既に反証され `LandingFreshC'` に割られている——
同じ場所で同じ種類の誤りが繰り返されている。）

## 2026-09-19 n116: **ファイルの docstring が未実装の定理を完了として書いていた**（監査上の発見）

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

### 何を見つけたか

`PalPeg/CloseoutRealize1.lean` の冒頭 docstring は §1〜§6 の 6 節を列挙しており、
そのうち

> §6 `pal_in_peg_of_progPal` — the *direct* `Prog` route, which bypasses the
> latch (and therefore all of `CloseoutPackRun*`) entirely via
> `PalPeg.pal_in_peg_of_structured`.

は「latch を——したがって `CloseoutPackRun*` 全体を——迂回する直接経路」と読める。
`hC`（`obligation_localRealization`）の壁を丸ごと回避できる話に見える。

**実際にはこのファイルは 89 行・宣言 2 つしかない**（`H_realizeSMG2'` と
`h_realizeSMG2'_of_LIMG2'`）。§3〜§6 は**存在しない**。書いた当時の計画を、
完了したかのような文体で docstring に書いていた。

docstring を実態に合わせて訂正した（§1/§2 は「実装済み」、§3〜§6 は「構想のみ、未実装」、
特に §6 は「存在しない。迂回路があると思って探すと時間を失う」と明記）。

### 位置づけ

CLAUDE.md は「散文の論証・他ファイルのヘッダ・類推・過去の自分の記述は一次情報として
扱わない」と定めている。今日それに違反した例が 3 つ出た:

1. n114 — CLAUDE.md §3 の「found 経路は未着手」を信じた（実際は DP 側が無条件で証明済み）
2. n115 — 同様に `PrepInputsG3` を葉だと思った（実際は producer が標準公理で存在）
3. n116（これ）— **ファイル自身の docstring** が未実装の定理を完了として書いていた

**3 番目が一番危険**で、「このファイルにこう書いてある」は普通なら信頼できるはずの情報源に
見える。**宣言の存在は `grep "^theorem"` で確認する。docstring の節番号を数えない。**

### `hC` の現状（実測）

* `CloseoutRealize1.h_realizeSMG2'_of_LIMG2'` — 実装済み（標準 3 公理）。
  `LocalStep` の証人は付随的で、任意の厳密実時間 `StructuredMachine` で足りる、を
  `H_realizeLIMG2'` について示す。
* ただし最上位が使うのは `H_realizeLIMW'` で、そこへの連結は**未確認**。
* `Workbench` §4 の記録（`TextFeed*` 153 モジュールが正本に 1 本も届いていない）は有効。


## 2026-09-19 n115: found 経路の `hpack` 7 節のうち少なくとも 2 節は既に無条件で産出済み

**全体 build 成功（EXIT=0）。公理は 4 義務のまま。無条件 PAL は未完。§10.5 は未達。**

`hor`（`obligation_cycleOracle`）の found 葉の最上位は
`CloseoutFoundRoute1.foundExit_compare_final20` で、その `hpack` は 7 節の束:

| 節 | producer | 公理 |
|---|---|---|
| `PrepInputsG3` | **`CloseoutLaterEntry.prepInputs3_of_found_C`** | 標準 3 のみ（実測） |
| `MismatchExitG` | 未確認（`CloseoutPrepInputs2:145` に定義） | — |
| `FallbackReachS` | 未確認 | — |
| `PrepLandingWatchC` | **`CloseoutWatchRound10:153`** | 未実測 |
| `PrepBirthLagC'` | 未確認 | — |
| `LandingFreshC'` | 未確認 | — |
| `BreakLandingC` | 未確認 | — |

`prepInputs3_of_found_C` は `StageEntryC` ＋ `SegReachedW` ＋ tick のデータ ＋
`PostCompareG` から `PrepInputsG3` を**無条件で**出す
（`prepInputs3_of_found_or_later` は `Classical.choice` すら使わない）。

**つまり found 経路は「未着手」ではなく、部品が散らばったまま束が組まれていない状態。**
`hpack` は 7 節の**束**なので、CLAUDE.md の「葉を束に畳み込むと偽になりうる」の
対象でもある。次に触るときは 7 節を個別に測ること。

### このセッションで 2 回やった同じ誤り

n114 と n115 はどちらも「CLAUDE.md の散文（過去の自分の記述）を信じて
『未着手』『最大の残り』と報告し、一次情報を見たら既に証明されていた」という形。
**地図を更新する前に断定しない。** 部品の不在は grep 1 回では示せない。

## 2026-09-19 n114: 探索（DP）側は**無条件で証明済み**だった — 自分の前の報告を訂正

**全体 build 成功（EXIT=0）。公理は 4 義務のまま変化なし。無条件 PAL は未完。§10.5 は未達。**

### 訂正

n113 のあと「`cycleOracle` の found 経路は未着手、探索の `Result` を run から供給する
のが最大の残り」と書いた。**これは誤り。** CLAUDE.md §3 の散文
（「`hfound`/`hfoundBg`/`hfoundReplay` ← 未着手、最大の残り」）を一次情報として
扱ってしまった。CLAUDE.md 自身が禁じている振る舞い
（「散文の論証・他ファイルのヘッダ・類推・**過去の自分の記述**は一次情報として
扱わない」）をやった。

### 一次情報で確認したこと（すべて標準 3 公理のみ、`#print axioms` 実測）

| 定理 | 内容 |
|---|---|
| `GalilDpCorrect.initial_correct` | **無条件**。fresh な物理プリロードから走らせると `∃ y qs, Completed GalilDpCode.code (initial w lower) qs y ∧ Result w lower 0 y` |
| `GalilDpCorrect.Result` | 「OUTPUT が `first` 以上の**最小**候補を符号化している（`Candidate` と最小性つき）」または「候補が存在しないことを正しく報告」 |
| `GalilMinimalPeriod.result_least` | `Result` ＋ `pc = 346` から `∃ k, Candidate ∧ pos 11 = k ∧ 最小性` |
| `GalilScaffoldSearchRun.dp_quanta_safe` / `calibrated_quanta_safe` | **無条件**。run 相の探索状態と較正済み予算から `SafeQuanta s ⟨Preload.initial w lower, false⟩ used t ⟨v,true⟩ ∧ t.mode ≠ .run ∧ Result w lower 0 (denote v)` |
| `GalilTickFair.readFun_code` | **`decide` で証明済み**（`ReadFunB` 経由）。これで `safeQuanta_unique` が探索量子の決定性を与える |

さらに `calibrated_quanta_safe` / `dp_quanta_safe` は既に
`GalilScaffoldStagePrepare`（:207, :304）、`GalilBranchInvariants2`（:251）、
`GalilScaffoldChainFallback`（:1848）で**消費されている**。

### したがって

**探索の正しさ（DP が最小周期を出すこと、量子化しても結果が同じこと、決定的であること）
は既に無条件で証明され、ステージ層まで配線されている。**

`CloseoutPrepInputs3.PrepInputsG3` が `SafeQuanta` ＋ `Result` を**仮説として束ねている**
のは、ステージ層とそこの間が繋がっていないだけ。つまり found 経路の残りは
「新しい数学」ではなく**層と層の配線**。

`first_round` が要る `Candidate` も `result_least` から出る。

### 次

`GalilScaffoldStagePrepare` の結論と `CloseoutPrepInputs3.PrepInputsG3` の間を繋ぐ。
これが通れば `hor` の found 葉と、`shiftPal*` の基底（新鮮な chain の第 1 shift、
`first_round`）の両方に効く。


## 2026-09-19 n113: 偽の疑いが濃い公理を run 形／trace 形に差し替えた（3 → 4）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。ラチェット緑（4 義務に更新）。
無条件 PAL は未完。計画書 §10.5 は未達。**

    'PalPeg.PalInPeg.unconditional' depends on axioms: [propext,
     Classical.choice, Quot.sound,
     obligation_cycleOracle, obligation_localRealization,
     obligation_shiftPalAlongRun, obligation_shiftPalAlongTrace]

### なぜ増やしたか

n112 で `obligation_shiftPalAtScanStates`（一状態述語 `BigPack2MG7W` の形）が
**偽の疑いが濃い**と分かった。放置すると「公理 3 個」という数字が進捗の指標として
機能しない。CLAUDE.md「偽の前提で数字を作らない」に従い、**数が増えても真であろう
形に割った**。

| 新しい公理 | 形 | 消費者 |
|---|---|---|
| `obligation_shiftPalAlongRun` | `InvLPC w c r` 起点から `Steps` で到達する scan 状態 | `packRunR_MW_marksFree`（`h_oracleIMW_of_MC3_W` 経由） |
| `obligation_shiftPalAlongTrace` | `PreTraceIMW` の trace の scan 点（`1 ≤ j ≤ Tc`） | `BranchSupply` の 5 定理（`scanLandingObligations_alongTrace_of_matchRest` ほか） |

どちらも**履歴が run で固定される**ので、旧版の欠陥（状態述語から履歴の事実を要求する）は無い。

### 危うくもう 1 個過剰量化を撒くところだった

trace 形の公理を最初 `PreTraceIMW` の仮説**なし**で書きかけた。そうすると
`st` が無制約関数になって `∀ z, … → ShiftPal z.vm` と同値に潰れる——
`hav` が偽になったのとまったく同じ形（過剰量化 13 例目、自分で撒く 5 例目になるところ）。
書いた直後に気づいて `PreTraceIMW` を仮説に入れた。**trace 形を書くときは
`PreTrace*` を仮説に入れたか必ず確認する。**

### 放電器は用意してある

| 公理 | 放電器 | 残差 |
|---|---|---|
| `shiftPalAlongTrace` | `ShiftPalAlongTrace.shiftPal_alongTrace` | `H_readsShift`（trace 形）＋ `H_freshShiftAtShiftEntry`（tick 形）＋ `periodOnly = false` 分岐 |
| `shiftPalAlongRun` | `CloseoutBundleRun.shiftPal_of_run_B` | 同じ 3 つ（run 形） |

`AuxPack` と `canRight` はどちらも既存の trace 補題で放電済み。
`H_readsShift` は `RoundSegFromRun.readsShift_at_actual` が実状態で出す
（`OriginAt` → `roundSeg_at_actual` → `originShift_of_roundSeg` → `h_readsShift_of_originShift`）。

### 触ったファイル

`BranchSupply`（5 署名を trace 形に、適用 1 箇所）、`CloseoutMarksPack`
（`packRunR_MW_marksFree` を run 形に）、`CloseoutFinalBranch`
（`given_scanLandingObligations`）、`PalInPegUnconditional`（公理 2 本）、`Axioms`（ラチェット）。


## 2026-09-19 n112: **`obligation_shiftPalAtScanStates` は偽の疑いが濃い**（進捗計器の訂正）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。ラチェット緑。公理は 3 義務。
無条件 PAL は未完。計画書 §10.5 は未達。
そして下に書くとおり、その 3 個のうち 1 個は偽の疑いが濃い。**

### 何を測ったか

`obligation_shiftPalAtScanStates` の文はこう:

    ∀ w x, BigPack2MG7W centreC placeC entry q first w x → ScanNR x →
      ShiftPal centreC placeC entry q first w x.vm

`ShiftPal w s` の結論は

    Manacher.PalAt (encoded w) (position s.center + periodLength wch) (r₀ + 1 - periodLength wch)

で、`periodLength wch` は chain の**周期テープの長さ**。つまり
「chain が持っている周期が、入力語 `w` の本物の周期である」という**履歴の事実**を
主張している。

そこで guard `BigPack2MG7W` の場を一次情報で全部展開した:

| 場 | 中身 | 入力語 `w` に触れるか | chain に触れるか |
|---|---|---|---|
| `IPackMW.pack = LPackM` | `lrepM`（左ヘッドが `w` を表現）／`scanGeom`（`ScanInvariant w …`） | ○ | **×** |
| `IPackMW.m2 = LPackM2` | `scanGeomR` / `shiftGeom` / `rrep` / `centreRep` / `centreOrder` | ○ | **×** |
| `AuxPack.coupled = Coupled` | `idleOut` / `block : BlockInv s.chain` / `sum : SumRel s.chain (value s.radius)` / `watch : WatchOK s.chain …` | **×** | ○（ただし**カウンタだけ**） |
| `AuxPack.front = FrontPack` | front ポテンシャル | × | × |
| `AuxPack.copyP = CopyPack` | `mode ≠ copy → CopyIdle s` | × | × |
| `CentreLive` | `mode = rewind → pair → 0 < position s.center` | × | × |
| `Extra8` | `rewindMargin`（marksTape/left）／`scanAvail`（`canRight right`） | × | × |

一次情報:
`CloseoutPackRun10:140`（`LPackM`）、`CloseoutPackRun23:99`（`LPackM2`）、
`CloseoutPackRun2:105`（`AuxPack`）、`GalilChainCoupling:359`（`Coupled`）、
`GalilBranchInvariants:425`（`BlockInv`）、`GalilChainCoupling:190`（`SumRel`）、
`GalilChainCoupling:199`（`WatchOK`）、`GalilRewindSafe:50`（`CentreLive`）、
`CloseoutPackRun46:67`（`Extra8`）。

**`w` に触れる場はどれもヘッド（`Represents` / `ScanInvariant` / `RRep` / `CentreRep` /
`ShiftGeom`）の話で、chain に触れる場はどれもカウンタ（`distance` / `lag` /
`periodLength` と `radius` / `cycle` / `remaining` の数値関係）の話。
chain の周期テープの中身と入力語 `w` を結びつける場が 1 つも無い。**

`shiftGuardVM` が足すのも `symbol (period.focus) = read s.right` の **1 記号**だけで、
窓全体が周期を持つことは言わない。よって周期テープが出鱈目でも guard は通り、
結論の `PalAt` は一般に成り立たない。

### 位置づけ

これは `hpack` が偽だったのと**同じ欠陥**（`CloseoutPackRefute.hpack_false`:
「run 沿いの束を一状態述語として書いており `ChainPosInv2` からは出ない」）。
CLAUDE.md 自身が `ShiftPal` を過剰量化の 5 例のうちの **1 番目**として挙げていた。
`BigPack2MG7W` という guard を付けたのは是正のつもりだったはずだが、
上のとおりその guard は chain と `w` を一切結びつけていない。

**`REFUTED` とは書かない**（`False` を導く機械検査済みの定理がまだ無い）。
反証のレシピ: `BigPack2MG7W` の証人を 1 つ作り、chain だけを
`periodLength = 1` の watch に差し替える（どの場も chain の周期テープの中身を
縛らないので pack は保たれる）。そのうえで `PalAt (encoded w) (C+1) r₀` が破れる
`w` を選ぶ。手間は `compare` の証人（`searchEffect` を含む）の構成。

### 正しい経路は run 形（既に作ってある）

`CloseoutBundleRun.shiftPal_of_run_B` が run 形の `ShiftPal` 産出器で、
`InvLPC` の起点が idle chain なので `packRunR_MW_marksFree` の中でそのまま使える。
残差は `H_readsShift`（→ n111 の `readsShift_at_actual` で実状態で出る）と
`H_freshShiftAtShiftEntry`（狭めた版、`first_round` から）。

**したがって「公理 3 個」という数字は、そのうち 1 個が偽の疑いが濃い以上、
このままでは進捗の指標として信用できない。** 次にやるべきは数を減らすことではなく、
`hSP` を run 形に差し替えること（数は一時的に増える）。


## 2026-09-19 n111: `ScanToScan`（区間抽出）を迂回できる — `scanSeg_snoc_tick`

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。公理は 3 義務のまま変化なし
（`obligation_cycleOracle` / `obligation_localRealization` /
`obligation_shiftPalAtScanStates`）。無条件 PAL は未完。計画書 §10.5 は未達。**

### 測定（一次情報を読んだ結果）

`obligation_shiftPalAtScanStates` の残差は `CloseoutRoundSeg` によれば 2 つ
（`RoundSeg` ＝ `CompareRounds h _ 1 _` と `H_fresh`）で、どちらも
`GalilScaffoldTopRoundS.round_next` / `GalilScaffoldTopFirstRound.first_round` が
要求する **`ScanSeg`（run の区間）** に帰着する。区間を run から抽出するのが
CLAUDE.md §1 の壁 (1)（`ScanToScan`、`CloseoutSegment`）。

さらに `CloseoutOriginRounds` のヘッダは、**`hSP` の残差と `hor` の found 経路の葉
`ShiftRoundC` は同じもの**だと定理にしている。つまり 2 つの壁ではなく 1 つ。

### 迂回路が通った

`ScanSeg` は `wait` / `count` / `match` の 3 構成子が `Tick` の
`scan_wait` / `scan_count` / `scan_match` と 1 対 1（`scanSeg_steps` がその対応を作る）。
障害は inductive が**前からしか積めない**ことだけやった。

`PalPeg/MatchedRunSnoc.lean`（新規、全定理が標準公理のみ）:

| 定理 | 内容 |
|---|---|
| `onlyMatchedRun_snoc` / `_head` / `_trans` | 射影側の末尾伸長・先頭剥がし・連結 |
| `matchedSeq_snoc_background` / `_compare` | VM 側（`MatchedSeq`）の末尾伸長 |
| `scanSeg_snoc_wait` / `_count` / `_match` | 制御つき（`ScanSeg`）の末尾伸長 |
| `compare_matched_parts` | `compareFound` ＋ `matched` ＋ watch から `galilFrame` 側の比較と `afterCompare` を取り出す（tick 逆向きの核） |
| **`scanSeg_snoc_tick`** | **run の 1 tick を `ScanSeg` に吸収。`Tick` の 24 構成子を全部潰して出口は 3 つだけ** |
| `restartNeedsBroken_of_restartVM` | 上の側条件を具体枠で放電 |

`scanSeg_snoc_tick` の 3 つの出口:

1. `ScanSeg` が 1 手伸びる
2. mode が scan を離れる（`scan_shift` / `scan_fallback` ＝ ラウンド境界）
3. chain が watch でなくなる（終端の一致比較で chain が壊れる場合）

側条件 `singlePositive cycle = false` は `RoundScan.fresh` ＋ `terminal_iff` から無償。

### `ScanToScan` は要らない公算が大きい（反証はまだ無い）

`CloseoutSegment` は「`SpanRep` は `ScanToScan` の下流」と書いていたが、`SpanRep` は
n109〜n110 で `BranchSupply.spanRepOnScanAndShift_alongTrace` により **tick ごとに**
証明できた。`RoundSeg` も同型で、区間を抽出せずに tick ごとに積めば足りるはず。

なお `ScanToScan` は「任意の scan→scan 健全 run が `ScanSeg` ＋ `Rounds` に分解する」と
全称量化しており、`ScanSeg.match` が `hwatch`（chain が watch）を要求する一方で
**idle chain の一致比較も合法な `Tick`** である以上、**偽の疑いが強い**。
機械検査した反証はまだ無いので `REFUTED` とは書かない。

### 続き（同日、`scanSeg_of_steps` 以降）

`scanSeg_snoc_tick` を `Steps` に沿って回して run 不変量に仕立てた:

* `scanSeg_of_steps` — scan ＋ watch の区間に沿って `ScanSeg` が伸びる
  （出口 2 / 3 は呼び手の不変量が潰す）
* `onlyMatchedRun_of_steps` — その末尾で **実際の状態の** `OnlyMatchedRun`
  （`CompareRounds.next` の第 1 引数そのもの）
* `compare_mismatched_parts` — ラウンド境界（`scan_shift`）で `round_next` に渡す
  `vs` / `vq` / `hcmp` / `hmis` / `hq` を `compareFound` から取り出す

さらに `PalPeg/ShiftPhaseDeterminism.lean`（新規、全定理が標準公理のみ）:

| 定理 | 内容 |
|---|---|
| `refresh_det` | 出力の更新は一意 |
| `shiftOne_det` | 1 単位の shift は行き先を一意に決める |
| `tick_shift_det` | shift 相の tick は一意（`Fair` 不要） |
| `steps_shift_det` | 中間が全部 shift 相なら同じ長さの 2 本は同じ状態に着く |
| `steps_shift_exit_unique` | **shift 相の出口は状態も長さも一意**（長さを仮定しなくてよい） |

### `round_next` の入力はすべて出どころが付いた

| `round_next` の入力 | 出どころ |
|---|---|
| `hseg : ScanSeg` | `scanSeg_of_steps`（新規） |
| `w0` / `hp0` / `hs0` / `hz0`（ラウンド起点） | ラウンド不変量 |
| `hm1` / `hr1` / `hc1`（終端の制御） | `scan_shift` tick の構成子 |
| `w` / `hs1`（終端の watch） | 不変量 |
| `hav : canRight s1.right` | tick の `replaying ∨ available` |
| `vs` / `vq` / `hcmp` / `hmis` / `hq` | `compare_mismatched_parts`（新規） |
| `hend : singlePositive cycle = true` | `RoundScan.terminal_iff` |
| `hpred` | `shiftGuardVM` の最終連言 |
| `hlen : Canonical s1.length` | `CPack.canon` |
| `hg` / `s2` / `hb` / `hs2` | `scan_shift` tick の `hg` / `hBegin` |
| `hi2 : CopyIdle s2` | `AuxPack.copyP` |
| `hchain : ChainShiftRun` | `shiftRun_exists_round` ＋ `shift_run_chain`（ラウンド不変量だけから出る） |
| `o` / `ho : refresh` | `CloseoutFoundRoute1.exists_refresh`（refresh は全域） |

**残るのは配線と、構成した着地と run の実際の着地の同一視。** 後者の差は shift 相
だけで（scan 側は `onlyMatchedRun_of_steps` が実際の状態で直接出す）、
`steps_shift_exit_unique` で `Fair` なしに閉じられる。


## 2026-09-19 n110: `obligation_marksEntry` を放電（公理 4 → 3）

**全体 build 成功（EXIT=0、エラー 0、`sorry` なし）。`PalPeg/Axioms.lean` のラチェット緑。
`PalInPeg.unconditional` の公理は
`[propext, Classical.choice, Quot.sound, obligation_cycleOracle,
obligation_localRealization, obligation_shiftPalAtScanStates]` の 3 義務。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 何が起きたか

`hme : ∀ w, H_marksEntry' (PofC centreC placeC entry w) q first` の消費者は
`CloseoutOracleW.packRunR_MW` の **2 箇所だけ**で、どちらも `MarksInv'` を作るため
だけにあった（`CloseoutMarksPack` の冒頭が既にそう書いていた）。

ところが `CloseoutPackRun17.marksInv'_of_run'` は **`H_marksEntry'` なしで**
run の全点に `MarksInv'` を与える定理で、その 4 入力が `InvLPC` の origin では
すべて無償だった:

| 入力 | 出どころ |
|---|---|
| `first ≠ 4` | 側条件。`first = 0` なので `by decide` |
| `hfl`（scan 状態で `0 ≤ value length`） | `GalilInvPlus2.hfloor_of_invLP2`。`InvLPC.1` がそのまま `InvLP2` |
| `hwin`（copy 状態で `WindowInOrigin`） | `CloseoutPackRun25.windowInOrigin_alongRun`。origin は scan なので origin 側の前提が空虚 |
| `CPack q c r` | `GalilCentreLive.cpack_of_entry` ＋ `CloseoutMarksFree.entryCounters_of_invLPC` |

`windowInOrigin_alongRun` が `Fair` なしで通るようになったのは n107 のモデル修正
`M-fallbackPlace`（`beginFallbackVM'` が fallback 先の窓長を `position right` で抑える）
のおかげ。つまり **n107 のモデル忠実性の修正がそのまま義務 1 個を消した。**

### 追加/変更したもの

* `CloseoutMarksPack.packRunR_MW_marksFree`（新規、標準 3 公理）—
  `packRunR_MWP` と本体は同じで、`hpk`（反証済みの `ChainPack`）の代わりに
  `marksInv'_of_run'` を使う。前提は `h4 : first ≠ 4` と `hSP` だけ。
* `CloseoutFinalBranch.given_scanLandingObligations` — `hme` パラメータを削除し
  `h4 : first ≠ 4` に置換（`packRunR_MW` → `packRunR_MW_marksFree`）。
  兄弟の `given_landingObligationsAlongRun` /
  `given_landingObligationsSansRadiusLedger` は歴史的経路なので触っていない。
* `PalPeg/PalInPegUnconditional.lean` — `axiom obligation_marksEntry` を削除、
  呼び出しを `(by decide)` に。
* `PalPeg/Axioms.lean` — ラチェットを 3 義務に更新。

### 教訓

**`hme` は最初から独立した義務ではなかった。** `CloseoutMarksPack` の冒頭は
「`hme` は `hpack` の中にある」と書いていたが、正しくは **`hme` は run の中にある**。
`hpack`（反証済み）を経由する必要すらなかった。
`marksInv'_of_run'` は `hme` を落とすために作られた定理として既に存在していたのに、
「`hme` の producer は `hpack` だけ」という**過去の自分の記述**を一次情報として
扱っていたせいで 1 日以上見落としていた。

### 残り 3 義務（難易度は宣言しない）

| 公理 | 内容 | 既知の経路 |
|---|---|---|
| `obligation_shiftPalAtScanStates` | scan 状態で `ShiftPal` | `CloseoutBundleRun.shiftPal_of_run_aux`。残差は run 形の `ChainPositionInvariantWithShiftPhase` ＋ `H_readsShift` ＋ `H_freshShift` ＋ `periodOnly = false` 分岐（`H_fresh`）。`hcan` は `BranchSupply.canRightAtScanOrShift_alongTrace` で**放電済み** |
| `obligation_cycleOracle` | `CycleOracleMC3` | `CloseoutOracleBridge.hor_of_H_oracle` ＋ `CloseoutOracle8.h_oracle_of_leaves7`（11 葉、CLAUDE.md §3） |
| `obligation_localRealization` | `H_realizeLIMW'` | producer なし（5 機械の鎖の 2→3 段） |


## 2026-09-19 n109: `SpanRep` の正しい guard は `scan ∨ shift`（一次情報で確定）

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。
`sorry` を含む下書きは挿入していない。）

### 一次情報で確認した `length` / `radius` の遷移

    afterCompare_radius : (afterCompare s vs vq).radius = inc s.radius     （TopInvStep:20）
    afterCompare_length : (afterCompare s vs vq).length = inc (inc s.length)（TopInvStep:21）
    afterMismatch_radius : (afterMismatch s vs vq).radius = inc s.radius    （TopRoundS:93）
    afterMismatch_length : (afterMismatch s vs vq).length = s.length        （TopRoundS:94）
    beginShiftVM : length := inc (inc s.length)、radius 不変               （TopShiftCycle:24）
    beginFallbackAt : length / radius ともに不変                            （SharedFunctional:76）
    rewindFrame.choose : length := ofNat 1、radius := reset                （TopRewind:56）
    replayStartVM : length := ofNat 1、radius := reset                      （TopReplay:29）

したがって `SpanRep s := value length = 2 * value radius + 1` は:

| 相 | 状態 |
|---|---|
| boot（`init`） | **偽**（両方 reset なので `0 = 1`） |
| scan（一致比較） | 保存（`afterCompare` は length +2 / radius +1） |
| scan → shift | **不一致で壊れ、`beginShift` の length +2 で回復**（`spanRep_shift` の入口形が `⟨…, inc radius, inc (inc length)⟩` なのはこれ） |
| shift | 保存（`shiftTick` は length −2 / radius −1、`spanRepS_shiftTick`） |
| scan → copy（fallback） | **壊れたまま**（`beginFallbackAt` は counters を触らない） |
| copy / home / fpp / markEnd / choose | 壊れたまま（counters 不変） |
| choose → rewind | `length := 1`、`radius := 0` で回復 |
| rewind 奇数側 | 壊れる（`rewindOne` は length のみ inc） |
| replayStart → scan | **前提なしで再確立**（`length := 1`、`radius := 0`） |

**よって正しい guard は `c.mode = Mode.scan ∨ c.mode = Mode.shift`。**
`RadiusExactOffRewindPhase` のような「除外リスト」ではなく「許可リスト」になる。
`EntryCounters` が要るのは scan 状態だけなので、これで十分。

    def SpanRepOnScanAndShift (c : Control) (s : GalilVM) : Prop :=
      c.mode = Mode.scan ∨ c.mode = Mode.shift → PalPeg.GalilSpanCounter.SpanRep s

guard が scan/shift だけなので、24 ケースのうち実際に仕事があるのは 7 つ:

    init          spanRep_of_init（側入力: boot の radius = reset ∧ length = reset）
    scan_wait     spanRep_background
    scan_count    spanRep_background
    scan_match    spanRep_afterCompare ＋ replayDec ＋ afterBirth_length/radius
    scan_shift    afterMismatch ＋ beginShiftVM の合成（下記）
    shift_one     spanRepS_shiftTick（`shiftLens_set_radius` / `_length` で持ち上げ）
    shift_done    counters 不変
    replayStart   spanRep_of_fallback（**前提なし**）

残り 16 ケースは行き先の mode が scan / shift でないので guard で空虚、
または `restart`（counters 不変）。

### 実装上の 1 つの引っかかり（次のターンの最初の作業）

`scan_match` で `a = true`（一致分岐）を取り出す必要がある。
`compareFound` の第 6 成分は `(a = true ↔ (galilFrame …).matched (scanLens.set s vs))` で、
tick が持っているのは `hmt : (galilFrameS …).matched s'`。
`s'` の scan 射影が `vs` 由来なので一致するはずだが、**橋渡しの補題を先に探す**
（`radiusExact_after_compare` は radius が両分岐で inc なので `a` を場合分けせずに
済んでいた。`SpanRep` は length が分岐で違うので `a` が必要）。

`scan_shift` 側は `a = false`（不一致）で、`afterMismatch` の length 不変 ＋
`beginShiftVM` の length +2 ＋ radius の inc で `SpanRep` が回復する:
`length = 2·radius + 1` → `length + 2 = 2·(radius + 1) + 1`。

## 2026-09-19 n108: `marksEntry` は `SpanRep`（mode guard 付き）1 点に帰着した

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### `marksEntry` を回避する経路（`H_marksEntry'` を使わない）

`CloseoutMarksFree.marksInv'_of_marksRun` は `H_marksEntry'` **なしで** `MarksInv'` を
run に沿って与える。入力は 4 つ:

| 入力 | 状態 |
|---|---|
| `first ≠ 4` | 側条件（`first = 0` なので `by decide`） |
| `CPack q x.ctl x.vm` | **タダ**: `cpack_of_entry q (invS_of_inv hInv) hEC`（`GalilTrailRad.live_pack_trace` の証明が `st 1` で `hInv` / `hEC` を実際に作っている） |
| `x.ctl.mode = Mode.scan` | **タダ**: `init_tick_target_is_scan`（`st 1` は scan） |
| `MarksRun … raw x` | 2 半分（下記） |

`MarksRun` の 2 半分:

| 半分 | 状態 |
|---|---|
| `WindowInOrigin`（copy 状態） | **タダ**（`CloseoutPackRun25.windowInOrigin_alongRun`、n107） |
| `EntryCounters`（scan 状態） | 分解すると 4 節（下記） |

### `EntryCounters` の 4 節 — 3 つは今日の成果でタダ

    EntryCounters raw r := ∃ Rad,
      ScanInvariant raw (position r.center) Rad r.left r.right ∧
      RadiusRep r.radius Rad ∧ SpanRep r ∧ Canonical r.length
    （`GalilGlueBLeaves:74`）

| 節 | 出どころ |
|---|---|
| `ScanInvariant …` | **タダ**: `LPackM.scanGeom` / `LPackM2.scanGeomR`（trace は各点で `IPackMW` を持つ）。`Rad` はここから取る |
| `RadiusRep r.radius Rad`（＝`Canonical radius ∧ value radius = Rad`） | **タダ**: `RadLedger.canon` ＋ `BranchSupply.radiusExactOffRewindPhase_alongTrace`（**今日証明**）＋ `ScanInvariant.rightPos`（`position right = position center + Rad`） |
| `Canonical r.length` | **タダ**: `CPack.canon` |
| `SpanRep r`（`value length = 2 * value radius + 1`） | **残り 1 点** |

### 残り 1 点: `SpanRep` の mode guard 付き tick 搬送

`GalilSpanCounter` は遷移ごとの補題を既に持っている:

    spanRep_afterCompare / spanRep_background / spanRep_shift / spanRep_rounds /
    spanRep_restart / spanRep_of_init / spanRep_of_fallback /
    spanRepS_shiftTick / spanRepS_shiftRun / spanRep_replayDec

**無いのは `Tick` の 24 構成子に対する 1 本と、run/trace 搬送。**
そして rewind 相では破れる（`length` は毎 tick +1、`radius` は 2 tick ごとに +1 なので
`length = 2·radius + 1` はペア境界でしか成り立たない）。つまり
`RadiusExactOffRewindPhase`（今日書いた）と**同じ形の mode guard** が必要:

    def SpanRepOffRewindPhase (c : Control) (s : GalilVM) : Prop :=
      c.mode ≠ Mode.choose → c.mode ≠ Mode.rewind → c.mode ≠ Mode.replayStart →
        value s.length = 2 * value s.radius + 1

出口の `replayStartVM` は `length := ofNat 1`、`radius := reset` なので
`spanRep_of_fallback` と同型で前提なしに再確立する（`radiusExact` と同じ理屈）。

**これが `marksEntry` を落とす最後の 1 本。** 今日 2 回書いた形
（`radiusExactOffRewindPhase_tick` / `headsRepresent_tick`、どちらも 24 ケース）と
同じ作業で、材料（遷移ごとの補題）は既に全部ある。

## 2026-09-19 n107: `M-fallbackPlace` を修正し `WindowInOrigin` を `Fair` なしに（`marksEntry` の実体が確定）

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### `M-fallbackPlace`（修正済み・全体 build 緑）

Scala 正本の `beginFallback` は search の walker place からコピーし、その walker は
到着済みの入力しか見ていない。Lean の `beginFallbackVM'` は `p` を無制限にしていた。

    def beginFallbackVM' (s t) := ∃ p, beginFallbackVM p s t ∧
      (GalilScaffoldPlace.stream p).length ≤ position s.right

**`p = s.walker` ではなく境界にしたのが要点。** `p = s.walker` は DP の walker との
結合が必要で `FallbackRestart` 系（`chosenRadius` を `p` で書く大きい定理群）に
波及する。境界なら `position_represent`（`GalilScaffoldChainFallback:110`、
**等式で既存**）からそのまま出て、しかも `WindowInOrigin` に必要なのは境界だけ。

配線: 分解 29 箇所（自動置換）、producer 3 定理、`FallbackRestart` 系 5 箇所、
`arrive` / `trunc` の保存義務 4 箇所（`position_arrive` / `position_trunc` は `rfl`）、
`GalilSharedFunctional` / `GalilTickFair` の 4 箇所。

### `WindowInOrigin` は `Fair` なしで run 全域に出る

    windowInOrigin_of_beginFallback   着地でそのまま（境界 ＋ beginFallbackAt_walker）
    windowInOrigin_tick_free          1 tick（copy へ入るのは scan_fallback だけ）
    windowInOrigin_alongRun           run 全域

`(stream t.fpp.walker).length = (stream p).length ≤ position s.right = position t.right`。
**`WalkerInOrigin` も `Fair` も経由しない。** n104 で「`FairSteps` が穴」と書いた所は
`Fair` を定理にするのではなく**迂回できた**。

（`M-initCursor` の副産物として `walkerInOrigin_of_run` も `Steps` 形になっているが、
`WindowInOrigin` はそれさえ要らなくなった。）

### `marksEntry` の実体が確定: marks テープの幾何 1 点

`CloseoutMarksFree.marks_steps_free` は `H_marksEntry'` なしで `MarksInv'` を運ぶ。
必要なのは `first ≠ 4` と `MarksRun`（2 半分）で、

| 半分 | 状態 |
|---|---|
| `WindowInOrigin`（copy 状態） | **タダ**（`windowInOrigin_alongRun`、今回） |
| `EntryCounters`（scan 状態） | `entryCounters_of_invLPC` 経由。ただし `InvLPC` は**cycle 起点**の不変量で、run の各 scan 状態には無い |

側入力もほぼ揃っている:

    CPack q (st 1).ctl (st 1).vm  ← cpack_of_entry q (invS_of_inv hInv) hEC
                                     （`GalilTrailRad.live_pack_trace` の証明が
                                       `st 1` で `hInv` / `hEC` を実際に作っている）
    (st 1).ctl.mode = Mode.scan   ← init_tick_target_is_scan

**残るのは `H_marksEntry'` そのもの**（`CloseoutPackRun16:165`）:

    H_marksEntry' P q first := ∀ c s, c.mode = Mode.choose → c.odd = true →
      (galilFrameS P q first).markSet s → MarksEntry' first s

    MarksEntry' first s := ∃ f, 1 ≤ f ∧ f ≤ mh s ∧
      denote (marksTape s.fpp) f = first ∧ mh s + 1 ≤ position s.left + f

つまり「`choose` 相で marks ヘッドがマーク上にあるとき、FIRST マークが
`f ≤ mh s` にあって `mh s + 1 ≤ position left + f`」——**marks テープの版面の幾何**。
`CPack.choose`（`mh s ≤ 2 * position s.right`）と marks テープの内容
（`GalilFppMarkedLayout.marks`）から出るはずで、`GalilCentreLive.layout_end`
（`:123`）が同種の補題。

**注意: `∀ c s` の形（過剰量化）。** 到達しない状態まで量化しているので、
まず trace 形に切り直してから測る（`CLAUDE.md` の規律）。

## 2026-09-19 n106: モデル欠陥 `M-initCursor` を修正（`Fair` の 3 場のうち 1 つが定理に）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### `M-initCursor`（修正済み・全体 build 緑）

Scala 正本の `stepInit` / `stepReplayStart` は `walker`（search の copy cursor）も
`periodOnly` も触らない。ところが Lean の `initVM` / `replayStartVM`
（`GalilScaffoldTopReplay:20,28`）は `GalilVM` の 15 場のうち 13 場しか縛らず、
この 2 つを**自由**にしていた。その分を `Fair.keepsSearchCursor` が仮定として抱え、
`marksEntry` の残差 `WindowInOrigin` が `FairSteps` を要求する原因になっていた。

末尾に `t.periodOnly = s.periodOnly ∧ t.walker = s.walker` を追加。

**消費者は 1 箇所も壊れなかった。** Lean の anonymous constructor は右結合の `∧` の
末尾を `-` 1 個で吸収するので、`obtain ⟨-, …, hch, -⟩ : initVM entry s s'` のような
既存パターンは 13 → 15 連言でもそのまま通る。直したのは producer 9 箇所だけ
（`GalilScaffoldTopReplay` / `TopScanRun` / `GalilTickFun` / `GalilTickDet` /
`GalilTickFair` / `CloseoutFairWitness` / `LocalTick2` / `LocalReplaySwap` /
`LocalReplayParked`）。

**モデル欠陥を記録していた定理が、修正で偽になった**ので差し替えた:

    initVM_not_unique / replayStartVM_not_unique / tick_init_not_det /
    tick_replayStart_not_det   （GalilTickDet、削除）
      → initVM_keepsSearchCursor / replayStartVM_keepsSearchCursor（正しい向き）

`GalilTickFair.tick_fair_init_unique` / `tick_fair_replayStart_unique` は
`Fair.keepsSearchCursor` を**読まなくなった**（`initVM` の射影で足りる）。
`GalilTickDet` の非決定性 (e) の init / replayStart 側は閉じた。

### `Fair.fallbackPlace` は着手して巻き戻した（記録）

`beginFallbackVM' s t := ∃ p, beginFallbackVM p s t`（`TopGuards:38`）の `p` を
Scala どおり `s.walker` に固定する試み:

    def beginFallbackVM' (s t) := ∃ p, beginFallbackVM p s t ∧ p = s.walker

分解パターン 27 箇所は機械的に直る（`⟨pl, ht⟩ : beginFallbackVM'` →
`⟨pl, ht, -⟩`、23 ファイルを自動置換で処理できた）。**しかし producer 側が重い**:
`GalilScaffoldTopFallbackCycleS` の `chosenRadius` 系の大きい定理が `p` を
自由な引数として取り、結論全体を `p` で書いているので、`hp : p = … .walker` を
足すと呼び出し側まで波及する。緑を壊さないため巻き戻した。

**次の一手**: `beginFallbackVM p s t` 自体に `t.walker = p` を足す案もある
（`beginFallbackVM'` の型は変わらないので 27 箇所は無傷）。ただし
`GalilTickFair.beginFallback_walker`（`t.walker = s.walker`）が偽になるので、
`WalkerInv` の走り方を確認してから入れる。

### 残る `Fair` の 2 場

| 場 | Scala 正本 | 入れ方 |
|---|---|---|
| `fallbackPlace` | `beginFallback` は search の walker place からコピー | 上記（`beginFallbackVM` 側に寄せる） |
| `restartFirst` | `transition` の前置きで broken chain の restart が mode step より先 | `Tick` の scan 構成子に `¬ restartGuardVM s` を足す |

3 場が全部定理になれば `FairSteps` が `Steps` から出て、`WindowInOrigin` が落ちて
`marksEntry` が消える（4 → 3）。

## 2026-09-19 n105: `marksEntry` はモデルの忠実性に帰着する（`Fair` を公理に隠さない）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### `Fair` の 3 場（`GalilTickFair:195`）

    restartFirst      : mode = scan → restartGuardVM x.vm →
                        y.ctl = {x.ctl with clock := delay} ∧ restartVM entry x.vm y.vm
    fallbackPlace     : mode = scan → y.ctl.mode = copy → y.vm.fpp.walker = y.vm.walker
    keepsSearchCursor : mode = init ∨ mode = replayStart →
                        y.vm.periodOnly = x.vm.periodOnly ∧ y.vm.walker = x.vm.walker

`WindowInOrigin`（`marksEntry` の唯一の残差）の producer
`CloseoutPackRun28.walkerInOrigin_of_run` は `FairSteps` を要求し、
`walkerInv_tick` が各 tick で `Fair` を読む。

### 2 つの道があり、片方は不正直

**(A) oracle を強めて `PreTrace` に `Fair` を持たせる。**
trace は `preTraceIMW_exists` が `H_bootIMW` ＋ `H_oracleIMW` から作る。
`H_oracleIMW` は `obligation_cycleOracle`（`CycleOracleMC3`）から来ているので、
`Fair` を要求すると**`cycleOracle` の内容が強くなる**。
公理の数は 4 → 3 になるが、それは n96 で自分がやった誤りと同型
（数だけ減らして内容を強化）。**採らない。**

**(B) モデルを Scala に忠実にして `Fair` を定理にする。**
`Fair` の 3 場はすべて「Scala がやっていることを Lean の非決定性が落としている」分:

| 場 | Scala 正本 | Lean の現状 |
|---|---|---|
| `keepsSearchCursor` | `stepInit` / `stepReplayStart` は `walker` も `periodOnly` も触らない | `initVM` / `replayStartVM` が両方**自由** |
| `fallbackPlace` | `beginFallback` は search 自身の walker place からコピー | `beginFallbackVM'` は着地場所が**自由** |
| `restartFirst` | `transition` の前置きで broken chain の restart が mode step より**先** | `Tick` に優先順位が**無い**（`restart` と `scan_wait` が競合） |

つまり `Fair` は**モデル欠陥 3 件の集合**であり、`M-periodOnly` / `M-watchBreak` と
同じ種類。CLAUDE.md §2 の当時の方針は「モデルは編集せず（使用箇所 300 超）`Fair` を
定義して一意性を証明」だったが、その `Fair` がいま `marksEntry` を塞いでいる。
**`marksEntry` を正直に落とすには (B) しかない。**

### (B) の具体形（次の一手）

1. `initVM` に `s'.walker = s.walker ∧ s'.periodOnly = s.periodOnly` を追加
   （`GalilScaffoldTopReplay:20` 付近、`replayStartVM` も同様）。
   → `Fair.keepsSearchCursor` が定理になる。
2. `beginFallbackVM'` の `∃ p` を search の walker に固定
   （`beginFallbackVM (P.place s')` 相当）。→ `Fair.fallbackPlace` が定理。
3. `Tick` の scan 構成子に `¬ restartGuardVM s` を足す。
   → `Fair.restartFirst` が定理（`GalilTickDet` の (a) も閉じる）。

影響は `initVM` / `replayStartVM` / `beginFallbackVM'` / `Tick` の使用箇所で、
`M-periodOnly`（誕生時の `periodOnly` リセット）と同規模の見込み。
`M-periodOnly` は実際に入って全体 build 緑になっているので、手順は確立している。

### (1) のコストを下げる実装上の観察（今日確認）

`initVM`（`GalilScaffoldTopReplay:20`）は 13 連言で、**`t.fpp = s.fpp` を既に持つ**
（fpp walker は保存されている）。足りないのは `periodOnly` と `walker` の 2 つ。

Lean の anonymous constructor は右結合の `∧` を途中で `-` 1 個で吸収できるので、
**新しい連言を末尾に足せば既存の分解パターンは壊れない**。実例:

    obtain ⟨-, -, -, -, -, -, -, -, -, hch, -⟩ : initVM entry s s' := hInit

は 11 項で 13 連言を分解している（11 番目の `-` が 11〜13 を吸収）。
15 連言にしても同じパターンが通る。**壊れるのは producer 側だけ**（新しい 2 つを
供給する必要がある）。だから (1) は「消費者 300 箇所」ではなく
「producer 数箇所」の作業。

`t.search = GalilScaffoldSearchFinish.begin reset s.radius` が search をリセットする
ので、`walker` が `search` の射影なら (1) の `walker` 側は既に決まっている可能性がある
（未確認。`GalilVM` の場一覧を見て `walker` が独立場かを先に確かめる）。

## 2026-09-19 n104: 公理 5 → 4（`centreMargin` 吸収）＋ 残り 4 個の難易度順と `marksEntry` の実体

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 4 個の原子的義務を axiom として持つ
（`cycleOracle` / `localRealization` / `marksEntry` / `shiftPalAtScanStates`）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理の推移（今日）

```
11 相当 → 10 → 9 → 8 → 7 → 5 → 4
  bg / chainBackLag / shiftExitLedger / matchRest / verifierRunAlongRun / centreMargin
```

### `centreMargin` は新規証明ゼロで `marksEntry` に吸収された

`CloseoutPackRun16.MarksInv'` の第 2 成分が
`position left + r + pairOff c ≤ position center` ——`RCouple` が持っていない向き。
第 1 成分 ＋ `¬ atFirst` から `two_le_left_of_marksInv'` が `2 ≤ position left`。
`Tick.rewind_one` / `rewind_pair` は `hf : ¬ atFirst s` を**構成子として持つ**。

`¬ atFirst` guard を 3 層に入れた:

    LTickLeaves.rewindLeft / LTickLeavesN.rewindLeft   CloseoutLPack3 / PackRun11
    Extra8.rewindMargin                                CloseoutPackRun46（first を引数に）
    RewindMarginAt / ChainBackLagAndShiftExitLedgerAt.rewindMargin   BranchSupply

`LTickLeavesG` / `LTickLeavesO` 系は未 guard のまま（触る必要なし）。
`rewindMarginAt_alongTrace` は `two_le_left_of_marksInv'` 1 行になった。

**訂正**: n96 の「`rewindMargin` を `CentreMargin` 1 葉に縮めた」は数だけの削減で
内容は強化だった（guard なしでは `1 ≤ position left` しか出ないので `+1` 分強すぎ）。
**過剰量化の 11 例目・自分で撒いた 4 例目。**

### 残り 4 個の難易度順（簡単なものから）

| 順 | 公理 | 残差 | 障害 |
|---|---|---|---|
| 1 | `marksEntry` | `WindowInOrigin`（copy 状態）1 つ | **`FairSteps`**（下記） |
| 2 | `shiftPalAtScanStates` | `ShiftPal` | `ChainOk` の再設計（`WatchOk` は反証済み） |
| 3 | `cycleOracle` | `CycleOracleMC3` | found 経路の葉（§3） |
| 4 | `localRealization` | `H_realizeLIMW'` | producer なし |

### `marksEntry` の実体は `Fair` である（今日確定）

`CloseoutMarksFree.marks_steps_free` は `H_marksEntry'` なしで
`CPack` / `WPack` / `MarksInv'` を run に沿って運ぶ。必要なのは `first ≠ 4` と
`MarksRun`（2 半分）で、`marksRun_of_window` により

| 半分 | 状態 |
|---|---|
| `EntryCounters`（scan 状態） | **タダ**（`entryCounters_of_invLPC`） |
| `WindowInOrigin`（copy 状態） | producer は `CloseoutPackRun28.walkerInOrigin_of_run` |

`WalkerInOrigin s := (stream s.walker).length ≤ position s.right`（`PackRun25:53`）、
`WindowInOrigin s := (stream s.fpp.walker).length ≤ position s.right`（`PackRun17:62`）、
橋は `windowInOrigin_of_fair`（`PackRun25:57`）。

`walkerInOrigin_of_run` の入力:

    hplace : ∀ u, (stream (place u)).length ≤ position u.right   -- placeC は具体関数
    hdelay : 2 ≤ delay                                           -- 2048
    hcan   : … replaying = true → canRight z.vm.right            -- CloseoutReplayCanRight でタダ
    hx     : WalkerInv x.ctl x.vm                                 -- boot 形（walker 空）
    hz     : FairSteps …                                          -- ★ここだけが穴

**`PreTrace.trace` は素の `Trace`（`Steps`）で `Fair` を持たない。**
`Tick` 単体は非決定的（`beginFallbackVM'` の着地場所、`initVM`/`replayStartVM` の
`periodOnly`/`walker` が自由）なので、`Fair` なしでは walker が任意に置かれうる。
だから `WindowInOrigin` は原理的に `Fair` を要する。

**次の一手**: `PreTrace` / `PreTraceIMW` に `Fair` を持たせる（oracle 側の証人が
`Fair` を満たすことを確認する）。`GalilTickFair` は `Tick ∧ Fair` の一意性まで
証明済みなので、材料は揃っている。これは `marksEntry` を落とす唯一の道。

## 2026-09-19 n103: `headsRepresent` を `MarksInv'` 基底へ（内容の訂正）＋ `CentreMargin` に偽の疑い

**全体 build 成功（EXIT=0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ（数は不変）。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 内容の訂正（数は減らない）

n96 で「`rewindMargin` を `CentreMargin` 1 葉に縮めた」と書いたのは**強化**だった。
`RCouple` は `position center ≤ position left + r + pairOff` の向きしか持たないので、
`2 ≤ position left` から `CentreMargin`（`r + pairOff + 2 ≤ position center`）は出ない。
**数だけ見て「縮めた」と書いてはいけない。**

`headsRepresent_tick` の側入力を `CentreMargin` 由来の `hCentreTwoLe` から
`MarksInv'` ＋ `RCouple` に差し替えた（どちらも真に弱い）:

* `Tick.rewind_pair` は `hf : ¬ atFirst s` を**構成子として持つ**（`GalilScaffoldTop:164`）
* `CloseoutPackRun16.two_le_left_of_marksInv'` がその `hf` から `2 ≤ position left`
* `RCouple`（`rcouple_alongTrace`、葉なし）で `2 ≤ position center`

追加: `BranchSupply.marksInv_alongTrace`（`H_marksEntry'` から trace 全域へ、
`marksInv'_of_run` ＋ `steps_of_trace`、boot は `init` 相）。

これで **`CentreMargin` の消費者は `Extra'.rewindMargin` 系 1 本だけ**になった。

### 決定的な発見: `MarksInv'` は `RCouple` の**逆向き**を持っている

`CloseoutPackRun16:191` の `MarksInv'` は 2 成分:

    MarksInv' first c s := c.mode = Mode.rewind →
      (∃ f, 1 ≤ f ∧ f ≤ mh s ∧ denote (marksTape s.fpp) f = first ∧
        mh s + 1 ≤ position s.left + f) ∧
      (∃ r, s.radius = ofNat r ∧ position s.left + r + pairOff c ≤ position s.center)

**第 2 成分が `position left + r + pairOff ≤ position center`** ——`RCouple` が持って
いない向きそのもの。だから `2 ≤ position left`（第 1 成分 ＋ `¬atFirst`）と
合わせると

    r + pairOff + 2 ≤ position left + r + pairOff ≤ position center

で **`CentreMargin` が丸ごと出る**。つまり

* **`¬atFirst` で guard した `CentreMargin` は `MarksInv'` から無償**
  （＝既存の公理 `obligation_marksEntry` に完全に吸収される）
* guard なしでは第 1 成分から `1 ≤ position left` しか出ない
  （`one_le_left_of_marksInv'`）ので `r + pairOff + 1 ≤ position center` まで。
  **現行の（guard なしの）`CentreMargin` は `+1` 分だけ強すぎる**

### `obligation_centreMargin_alongTrace` に偽の疑い（未検査・要確認）

`rewindMarginAt_alongTrace` は `CentreMargin` から**guard なしの**
`RewindMarginAt c s := c.mode = Mode.rewind → 2 ≤ position s.left` を出す。
ところが `CloseoutPackRun16` は 2 本を区別している:

    one_le_left_of_marksInv' : MarksInv' → mode = rewind → 1 ≤ position left
    two_le_left_of_marksInv' : MarksInv' → mode = rewind →
                               (marksTape s.fpp).focus ≠ first → 2 ≤ position left

**`2` は `¬atFirst` の下でしか主張されていない。** `atFirst`（＝ rewind の歩きが
FIRST に到達した最後の状態、次の tick は `rewind_done`）では `position left = 1`
でありうる。もしそれが到達可能なら `RewindMarginAt` は偽で、したがって
`CentreMargin`（それより強い）も偽。

**これは `canRNext` と同型（「着地/端の状態まで量化した」）。** 確認手順:
`rewind_done` の直前状態で `position left = 1` を作れるかを `MarksInv'` の定義
（`CloseoutPackRun16:191`）から検査する。作れれば機械検査済みの反証を書き、
`RewindMarginAt` を `¬atFirst` で再 guard する。

### 再 guard の影響範囲（実測）

    rewindMargin : … → 2 ≤ position left        8 箇所
      CloseoutLPack4:207 / PackRun11:368 / PackRun43:82 / PackRun3:117 /
      PackRun45:85 / PackRun46:68 / BranchSupply:2200,2519
    rewindLeft : … → 0 < position (left s.left)  2 箇所（CloseoutLPack3:279 / PackRun11:107）
    producer `rewindLeft := fun hm => left_pos_of_two (… .rewindMargin hm)`  4 箇所
      CloseoutLPack4:259 / PackRun11:460 / PackRun43:175 / PackRun8:439

消費点は `lpackM3_tick` の `rewind_one` / `rewind_pair` ケースで、そこには
tick 自身の `hf : ¬atFirst` が来ている。よって再 guard は機械的だが 14 箇所以上。

## 2026-09-19 n102: `centreMargin` の放電経路が確定（部品は全部既にある）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**（このエントリは調査結果のみ。）

### 一次情報で確定したこと

1. **`rewindOne` / `rewindPair` はどちらも `x.marks.left ≠ []` を構成子として持つ**
   （`GalilScaffoldTopRewind:59,61`）。「rewind の歩きが原点前で止まる」側条件は
   **tick が既に持っている**（「側条件は構成子が持っている」4 例目）。
2. **`Tick.rewind_one` / `rewind_pair` は `hf : ¬ F.atFirst s` を持つ**
   （`GalilScaffoldTop:162,164`）。`galilFrameS` の `atFirst` は
   `(marksTape s.fpp).focus = first`（`rewindFrame.atFirst`）。
3. **`CloseoutPackRun16.two_le_left_of_marksInv'` が既に存在する**:

       MarksInv' first c s → c.mode = Mode.rewind →
         (marksTape s.fpp).focus ≠ first → 2 ≤ position s.left

   つまり **(2) の `hf` と合わせて `2 ≤ position left` がそのまま出る。**
4. `RCouple`（`rcouple_alongTrace` で**葉なし**）が `position left ≤ position center`
   を持つので、`2 ≤ position center` も同時に出る。
5. `MarksInv'` は trace の各点で `CloseoutPackRun16.marksInv'_of_run`
   ＋ `steps_of_trace` から出る（boot は `init` 相なので `h1 : m ≠ rewind` が満たされる）。
   入力は `H_marksEntry'`＝**既存の公理 `obligation_marksEntry`**。

### 帰結: `CentreMargin` は消せる（`marksEntry` に吸収）

`CentreMargin`（`r + pairOff c + 2 ≤ position center`）の消費者は 2 つだけ:

| 消費者 | 本当に要るもの |
|---|---|
| `rewindMargin_of_centreMargin` → `LTickLeavesN.rewindLeft` | `2 ≤ position left` |
| `headsRepresent_tick` の `hCentreTwoLe`（`rewind_pair` ケースのみ） | `2 ≤ position center` |

**`CentreMargin` は両方より真に強い**（`RCouple` は `position center ≤ position left +
r + pairOff` の向きしか持たないので、`2 ≤ position left` から `CentreMargin` は出ない）。
n96 の「`rewindMargin` を `CentreMargin` 1 葉に縮めた」は**数は減ったが内容は強くなっていた**。

必要な改修は 2 点で、どちらも `¬atFirst` guard を入れるだけ:

* `headsRepresent_tick` の側入力を `hCentreTwoLe` から
  `MarksInv' first x.ctl x.vm` ＋ `RCouple x.ctl x.vm` に差し替える
  （`rewind_pair` ケースには `hf : ¬atFirst` が来ている）
* `RewindMarginAt` を `c.mode = Mode.rewind → ¬ atFirst s → 2 ≤ position s.left` に
  再 guard する（消費者は `rewind_one` / `rewind_pair` の tick なので `hf` がある）

これで `obligation_centreMargin_alongTrace` は落ちて **5 → 4**。

### `marksEntry` 自身の残差（`CloseoutMarksFree`）

`marks_steps_free` は `H_marksEntry'` なしで `CPack` / `WPack` / `MarksInv'` を run に
沿って運ぶ。必要なのは `first ≠ 4` と `MarksRun`（2 半分）:

| 半分 | 状態 |
|---|---|
| `EntryCounters`（scan 状態） | **タダ**（`entryCounters_of_invLPC`、`InvLP := InvL ∧ EntryCounters`） |
| `WindowInOrigin`（copy 状態） | **真の入力**（これが `marksEntry` の実体） |

つまり残り 5 個のうち `centreMargin` と `marksEntry` は**1 つの残差
`WindowInOrigin`（copy 状態、run 形）に統合される**見込み。

## 2026-09-19 n101: 公理 7 → 5（`matchRest` ＋ `verifierRunAlongRun`）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 5 個の原子的義務を axiom として持つ
（`centreMargin` / `cycleOracle` / `localRealization` / `marksEntry` /
`shiftPalAtScanStates`）。無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理の推移

```
11 相当 → 10 → 9 → 8 → 7 → 5
  bg 場              放電（CentreLedger ← LPackM3）
  chainBackLag       放電（不変量を全構成子に広げた）
  rewindMargin       → centreMargin に縮小（RCouple はタダ）
  matchLanding + shiftEntryLanding → matchRest 1 つに合流
  shiftExitLedger    放電（HeadsRepresent ＋ ShiftGeom ＋ RadiusExact）
  matchRest          放電（4 場とも）
  verifierRunAlongRun 放電（run 形 → trace 形に切り直し）
```

### `MatchRest` の 4 場の決着

| 場 | 決着 |
|---|---|
| `canRNext` | **偽**（`MatchRestRefute.matchRest_alongTrace_false`）。着地側の 1 歩分に切り直し |
| `repV` | `VerRun` の第 1 成分そのもの → `ChainVerifierRepresents` |
| `replayPay` | `ChainPositionInvariantWithShiftPhase.payload` の guard を `ScanNR` → `mode = scan` に広げたら**義務ごと消滅** |
| `repVmid` | `ChainVerifierRepresents` を 1 手進めるだけ |

`replayPay` が存在した理由: `payload` の guard が `ScanNR`（`mode = scan ∧
replaying = false`）で replay 中の台帳が抜けていた。guard を広げたら源で両分岐が出た。
**「狭く切った guard」の 8 例目。** 副産物として `bg` / `matchLand` の `ScanNR` 仮説と
そこでしか使われていなかった `(o b : Bool)` が全部落ちた。

### `VerRun` は run 形だったから出なかった

`CloseoutVerSide.VerRun` は `Steps` 到達可能な**任意の**状態に量化していた
（`Tick` は決定的でないので trace からは出ない）。trace の点で述べた
`BranchSupply.ChainVerifierSupplyAlongTrace` に切り直すと

    VerRep  ← ChainVerifierRepresents の .watch 場
    LagCan  ← ChainLagCanonical の .watch 場

でどちらも搬送済み。**過剰量化の 10 例目。run 形と trace 形は別物。**

### 鍵: `right` は入力端で no-op

    canRight p = (gap = false ∨ head.right ≠ [] ∨ head.incoming ≠ [])
    moveRight h = match h.right with | a :: rs => … | [] => match h.incoming with | [] => h | …

`¬canRight p` なら `gap = true` かつ右も incoming も空で `moveRight h = h`。
`representsAfterRight_free` でこれを示したので **`ChainVerifierRepresents` は
`canRight` の供給を一切要らない**。`verRep_next` が `canRight` を取っていたのは
無条件版を書いていなかったからで、障害ではなかった。

### 残り 5 個の分析

| 公理 | 内容 | 次の一手 |
|---|---|---|
| `centreMargin` | rewind 相で `r + pairOff c + 2 ≤ position center` | **marks テープの下限が必要**（下記） |
| `marksEntry` | `H_marksEntry'`（rewind 入口の marks 不変量） | `centreMargin` と同じ壁 |
| `shiftPalAtScanStates` | scan 状態の `ShiftPal` | `ChainOk` の再設計（`WatchOk` 反証済み、n74 系） |
| `cycleOracle` | `CycleOracleMC3` | §3 の葉（found 経路が最大） |
| `localRealization` | `H_realizeLIMW'` | producer なし。難易度は宣言しない |

**`centreMargin` の位置づけ（今日確定）**: `GalilCentreLive.CPack` は既に marks テープの
束縛を**場として運んでいる**:

    CPack.rewind : c.mode = Mode.rewind → mh s + (if c.pair then 1 else 0) ≤ 2 * position s.center
    （`mh s = GalilScaffoldTape.head (marksTape s.fpp)`）

これは `position center` の**下限**を与えるので `CentreLive`（`0 < position center`）は
そこから出る（`centreLive_of_pack`）。ところが `CentreMargin` に必要なのは
`position right ≥ 2·r + pairOff + 2`、すなわち **`mh` の下限**（rewind の歩数 `r` が
marks テープの FIRST までに収まること）で、`CPack` の場はすべて `mh` の**上限**。
よって新しい場（rewind 中に `2·value radius + pairOff + 4 ≤ mh s` に相当するもの）が要る。
`radiusExact` が rewind 中も保存されること（`position center + radius = position right`、
`0 < position center` が要る＝`CentreLive`）は既に材料がある。

## 2026-09-19 n100: `MatchRest` は主張が強すぎた — `canRNext` を反証し `repV` を放電（4 場 → 2 場）

**全体 build 成功（EXIT=0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 7 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 公理 8 → 7（`shiftExitLedger` 放電）

`obligation_shiftExitLedger_alongTrace` を `BranchSupply.shiftExitLedgerAt_alongTrace`
で放電。新規入力は既存の公理 `obligation_centreMargin_alongTrace` だけ。

    canRight center   HeadsRepresent ＋ 中心の位置上界（RadLedger.le ＋ .nonneg）
    Sane center       LPackM2.shiftGeom が直接持っている
    radiusExact       RadiusExactOffRewindPhase（shift 相は rewind guard の外）

原因は `LPackM2.centreRep` の guard が `rewind ∨ replayStart` だけだったこと
（`LagCan` と同じ「狭く切った」パターン、6 例目）。

側条件が 2 つ「タダ」になった:
1. `radiusExact_after_shiftOne` の `1 ≤ value radius` は算術に使われていなかった
2. `0 < head.left.length` は `represented_position`（`Represents` ＋ `focus ≠ none`）から直接

### `MatchRest.canRNext` は偽だった（機械検査済み・REFUTED 条件付き）

`PalPeg.MatchRestRefute.matchRest_alongTrace_false`
（`PreTrace` ＋ `0 < |w|` ＋ trace 全域の `MatchRest` → `False`。標準公理のみ）。

    canRNext : canRight (right s.right)     -- mode guard すら無し

`ReportPointAt.atPrefix` は報告点で `position right = 2|w| − 1` を**等式**で与える。
`not_canRight_iff`（`¬canRight p ↔ position p = 2|w|`）より 2 歩分の余裕は原理的に無い。

コウタの診断そのまま:「反証ができたとしたら、定理の内容がまずかったんやろ」
「定理の主張が強すぎたが一番ありそう」。

| | |
|---|---|
| 書いた義務 | 源状態で **2 歩分**（trace 全域・guard なし） |
| 実機の要求 | compare 前に `canRight right`（**1 歩分**、Scala `available`） |
| 消費者の要求 | **着地状態**の `canRight t.right`（1 歩分） |

正しい切り方: `matchLand` / `entryLand` の**仮説**に `canRight t.right` を移し、
消費者 `chainPosInv2_tick_of_landingObligationsAt` が
`y.ctl.mode = scan ∨ shift → canRight y.vm.right` を取る。本線はこれを
`BranchSupply.canRightAtScanOrShift_alongTrace` で埋める（新規入力ゼロ）。
旧 global/`Steps` 経路には過剰量化の供給を明示仮定として足し、
名前に過剰量化を出した（`hCanRightAtAnyScanOrShiftState`）。

### `MatchRest.repV` も放電（新規入力ゼロ）

`CloseoutVerSide.VerRun` の第 1 成分が `VerRep w z.vm.chain` そのもの。
`steps_of_trace` で trace の scan 状態に落ちる。
**`MatchRest` は 4 場 → 2 場**（`repVmid` / `replayPay`）。

### 次の 2 手（`obligation_matchRest_alongTrace` を消すため）

1. **`repVmid`**（1 `ChainStep` 先の verifier 表現）。`ChainStep` は**7 構成子**
   （`idle` / `brokenIdle` / `copyBit` / `copyEnd` / `backStep` / `backDone` / `watchStep`）。
   `.watch` を作るのは `backDone`（verifier = `.back` の `ver`、不変）と
   `watchStep`（`Internal`: `idle` は不変、`take` は `right`）。
   よって **`ChainPositionLedger` と同じ 3 相を覆う `VerRep` 全相版**を作り、
   誕生（`chainStart` の verifier = `s.center`）を `HeadsRepresent.centre`（証明済み）
   から出せば、`repV` / `repVmid` だけでなく
   **`obligation_verifierRunAlongRun` 自体も落ちる見込み**（7 → 5）。
   移動補題は既にある: `CloseoutVerRep.verRep_next` / `verRep_of_chainPos`。
2. **`replayPay`**（replaying 時の payload）。3 節のうち `canR` は
   `canRightAtScanOrShift_alongTrace`、`radLe` は `radiusLe_of_radLedger` で**タダ**。
   残るのは `ChainPositionLedger s.chain (position s.right)` で、これは
   `ChainPositionInvariantWithShiftPhase.payload` の guard が `ScanNR`
   （＝ `replaying = false`）に切られているために抜けている。
   **guard から `replaying = false` を外す**のが筋（また「狭く切った guard」）。

## 2026-09-19 n99: 公理 9 → 8、そして中心ヘッドの遷移表（`CentreRep` 広げ用）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 8 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 9 → 8: インターフェースを広げただけ（コピー 0 行）

`CloseoutPackRun48` の `h_matchP2_of_target` / `h_shiftEntry2_of_target` は
`hres`（global な `H_matchRes2` / `H_shiftRes2`）を**源状態 `(c, s)` でだけ**使う。
署名を `MatchRes2 w c s` に変えて本体は `intro` と `have R` の 2 行だけ直した
（70 行の本体はそのまま）。global 版は 5 行のラッパー。

両方の入力が同じ `MatchRes2` と確定したので、`obligation_matchLanding_alongTrace` と
`obligation_shiftEntryLanding_alongTrace` を `obligation_matchRest_alongTrace` 1 つに
統合した（`BranchSupply.matchRes2_alongTrace` /
`scanLandingObligations_alongTrace_of_matchRest`）。

### 公理の推移

```
11 相当（束を分解した換算） → 10 → 9 → 8
  bg 場              放電（CentreLedger ← LPackM3）
  chainBackLag       放電（不変量を全構成子に広げた）
  rewindMargin       → centreMargin に縮小（RCouple はタダ）
  matchLanding + shiftEntryLanding → matchRest 1 つに合流
```

### 次: `CentreRep` を広げて `shiftExitLedger` を落とす

`shiftExitLedger` の `CentreLedger` は `canRight center ∧ Sane center ∧ radiusExact`。
`Sane` は `SanePack.saneC` でタダ、`radiusExact` は tick 全 24 ケース済み（n96）。
残るのは `canRight s.center` で、それには `Represents s.center.head w` が要る。
`LPackM2.centreRep` の guard は `rewind ∨ replayStart` だけ（`Run23:105`）——
また「狭く切った」パターン。

**中心ヘッドの遷移表（一次情報で確認、これが探すのに手間な部分）**

| tick | center |
|---|---|
| `init`（`initVM`、`TopReplay:20`） | `= right s.right` |
| `shift_one`（`shiftTick`、`ChainInputSupply:1445`） | `= right s.center` |
| `choose_select`（`rewindFrame.choose`、`TopRewind:56`） | `= x.right` |
| `rewind_pair`（`rewindFrame.rewindPair`、`TopRewind:62`） | `= left x.center` |
| `replayStart`（`replayStartVM`） | `= s.center`（不変） |
| `markBack` / `markForward` / `rewindOne` / `fppReset` | **不変**（`fpp` だけ） |
| fpp 相 8 遷移（`fppLens`） | **不変** |
| `backgroundS` / `compare`（`afterCompare_center`）/ `beginShift` / `beginFallback` / `restart` / `shift_done` | **不変** |

必要な移動補題は既にある: `right_word` / `right_present`（`canRight` を要する）、
`left_word`（`focus ≠ none` だけ）。

側入力もタダ: `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）
＋ `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）
→ `canRight_of_position_bound`。

**注意 2 点**
1. `initialHead raw = ⟨⟨none, [], [], raw⟩, true⟩` で focus が `none` なので
   **boot では `CentreRep` は偽**（`AuxPack` と同じ）。`1 ≤ i` から始める。
2. `choose_select` は `center := x.right` なので**右ヘッドの表現も同時に要る**。
   `LPackM2.rrep` の guard は `OffScan c.mode`、scan では `scanGeom` が与える。
   中心と右の 2 つを同時に運ぶ帰納になる。

### 要確認（切り方の疑い）

`MatchRest.canRNext : canRight (right s.right)` は無条件だが、Scala 正本
`ScaffoldGalil.scala:255` の `available = replaying || right.canRight` が比較自体を
守っているので、入力が尽きた時点では比較が起きない。**最終位置で `canRNext` が
本当に要るのかを確かめる**（要らないなら `m < w.length` で守るべき）。

また `MatchRest.repV` は `VerRun` の第 1 成分と同内容なので、
`obligation_verifierRunAlongRun` から供給できる（`MatchRest` が 4 場 → 3 場に縮む）。

## 2026-09-19 n98: `matchLanding` と `shiftEntryLanding` は `MatchRest` 1 つに合流する

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 9 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 合流の発見

`CloseoutPackRun48` を読んだら:

```
H_shiftRes2 w := ∀ c s s' t, mode = scan → ChainPositionInvariantWithShiftPhase w c s →
    compare s s' → ¬ matched s' → shiftGuardVM s' → beginShiftVM' s' t → MatchRes2 w c s
h_shiftEntry2_of_target (hres : H_shiftRes2 …) : H_ShiftEntryChainLedger …   (:374)
h_matchP2_of_target     (hres : H_matchRes2 …) : H_MatchLandingChainLedger … (:243)
```

**両方の入力が同じ `MatchRes2 w c s`。** そして
`CloseoutPackRun49.matchRes2_of_lpackM3`（:448）が
`LPackM3`（§5e で運べる）＋ `LTickLeavesN`（タダ）＋ `LTickLeaves3`（`shiftExitLedger`
以外タダ）＋ **`MatchRest`** から `MatchRes2` を出す。

つまり `obligation_matchLanding_alongTrace` と
`obligation_shiftEntryLanding_alongTrace` の **2 公理が `MatchRest` 1 つに合流する**
（9 → 8）。

### `MatchRest` の 4 場と現状

| 場 | 内容 | 状態 |
|---|---|---|
| `repV` | chain の verifier が入力を表現 | **`VerRun`（axiom で保持）** |
| `repVmid` | verifier を 1 `ChainStep` 進めた先でも表現 | `right_word` / `right_present` で出るはず |
| `replayPay` | `replaying = true` のときの source の payload | `ChainPositionInvariantWithShiftPhase.payload` は `ScanNR`（＝非 replaying）で守られているので別途 |
| `canRNext` | `canRight (right s.right)` | **最終位置で偽の疑い**（下記） |

### 要確認 — `canRNext` の切り方

`canRight_next_of_bound` は `m < w.length`（**厳密**）と `position p ≤ 2m − 1` を要する。
いま持っている予算は `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）なので
`position (right right) ≤ 2|w|` となり、**最終位置（`m = |w|`）では `canRight` が偽**。

`MatchRest.canRNext` は無条件なので、**最終位置で本当に要るのかを確かめる**。
要らないなら `m < w.length` で守るべき＝切り方の間違い。
（`Run48:439` は shift 入口の `chainPos_immediate` に `R.canRNext` を渡している。
shift 入口は不一致 ＋ shift guard で起きるので、最終位置で起きうるかを Scala 正本
`ScaffoldGalil.canShift` で確認すること。）

### 次の一手（順番）

1. `h_matchP2_of_target` / `h_shiftEntry2_of_target` を**状態局所化**する
   （どちらも `hres` を `(c, s)` でだけ使う。`bg_at_of_supply` と同じ形）。
2. `MatchRest` を trace 形の 1 公理にまとめ、`matchLanding` / `shiftEntryLanding` の
   2 公理を消す（**9 → 8**）。
3. `canRNext` の切り方を Scala 正本で確認し、必要なら `m < w.length` で守る。
4. `shiftExitLedger` は `CentreRep` を shift 相へ運ぶ仕事。
   `CloseoutPackRun21` 自身が「`FrontPack.rewind` の `Sane s.center` を
   `CentreRep w s` に強化すべき」と書いている（`Run21:52` 付近）。これも「狭く切った」パターン。

### 今日のパターン集（全部「難解」ではなかった）

| 症状 | 正体 |
|---|---|
| producer が無い | 不変量を**狭く切っていた**（`LagCan` は `.watch` 相だけ） |
| 同じ導出が各所にある | **分類器に対する補題が無い**（`chainAt` を手開きしていた） |
| 「幾何が要る」と感じる | **リストの長さの算術**だった（`position p = 2·|left| ± 1`） |
| 前提が 1 単位足りない | **義務の切り方**が間違っている（guard が抜けている） |
| 束ねた前提数が少ない | 偽の前提を隠している（`hpack` / `hav`） |

## 2026-09-19 n97: 公理を 1 個放電（10 → 9）＋ 「狭く切った不変量」が詰まりの正体

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 9 個の原子的義務を axiom として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### ラチェットで初めて公理が減った

`obligation_chainBackLag_alongTrace` を削除し `BranchSupply.chainBackLagAt_alongTrace`
で置き換えた（**新規入力ゼロ**）。`Axioms.lean` の guard も 10 → 9 に更新。

### コウタの基準で診断した結果（2 つの構造的な問題だけだった）

> 「producer がないのは何か間違っているとおもう。単なる機械のエミュレートが正しい証明やん。
> そこが難解なら何かがミスっている」「純粋に作業量が多いならわかる」
> 「構成的にできればあとは本当に作業になる」

**(a) 不変量が狭く切られていた。**
`CloseoutPackRun48.LagCan` は `.watch` 相だけ。実機の lag は `chain.start()` で
`radius` から作られ `inc`/`dec` でしか動かないので `Canonical` と非負は構成から自明。
全構成子に広げた `ChainLagCanonical` を作ったら落ちた。

**(b) 分類器に対する補題が無く各所で手開きしていた。**
`compareFound` の 8 番目の成分 `chainAt`（`GalilScaffoldTopSearch:130`）が
tick の chain 効果の分類器そのもの:

```
chainAt a found … x z :=
  (x ≠ .idle ∧ ChainTick a x z) ∨ (x = .idle ∧ found = false ∧ z = .idle) ∨
  (x = .idle ∧ found = true ∧ (if a then ChainMatched (chainStart …) z else z = chainStart …))
```

`lpackM3_tick` はこれを各ケースで手で開いていた（`Run49:162–290` の約 60 行、
`lagCan` 用と `chainPos` 用に二重化）。**分類器に対する補題 1 本
（`chainLagCanonical_chainAt`）で chain の不変量が全部乗った。**

さらに `fppLens` / `rewindLens` はどちらも `chain` を含まないので、fpp 相 8 遷移と
rewind/choose 相 6 遷移は `chainLagCanonical_of_chainEq` 1 本で潰れた。

**難解な箇所は 1 つも無かった。** 詰まっていたのは可読性と構造の問題だけ。

### 同じパターンが次にも当てはまる — `CentreRep`

`obligation_shiftExitLedger_alongTrace` の `CentreLedger` は
`canRight center ∧ Sane center ∧ radiusExact`。`Sane` は `SanePack.saneC` でタダ、
`radiusExact` は tick 全 24 ケース済み（n96）。残るのは `canRight s.center` で、
それには `CentreRep`（中心ヘッドが入力を表現）が要る。

**`LPackM2.centreRep` の guard は `rewind ∨ replayStart` だけ**（`Run23:105`）。
`LagCan` と同じ「狭く切った」パターン。`Represents` はテープ内容の性質でヘッド移動で
保たれる（`right_word` / `left_word` が既にある）ので、広げるのは機械的。

側入力は**タダ**: `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）
＋ `position right ≤ 2|w| − 1`（`rightHeadPos_le_alongTrace`）→ `canRight` は
`canRight_of_position_bound` で出る。中心が動くのは `init`（`= right s.right`）/
`shift_one`（`= right s.center`）/ `replayStart`（`= s.center`）/ `choose_select`
（`center.copyFrom(right)`）/ rewind（`= left s.center`）の 5〜6 ケースだけ
（`fppLens` は center を含まない）。

**注意（同時帰納になる）**: `CentreRep (st (i+1))` は `right_word` に
`canRight (st i).vm.center` を要し、それは `CentreRep (st i)` から出る。
`i` に関する 1 本の帰納の中で導けばよい。

### 先に確かめること — `MatchRest.canRNext` は最終位置で偽の疑い

`obligation_matchLanding_alongTrace` の経路は
`CloseoutPackRun49.matchRes2_of_lpackM3`（`LPackM3` は運べる）＋ `MatchRest` の 4 場。
そのうち `canRNext : canRight (right s.right)` は
`canRight_next_of_bound` に `m < w.length`（**厳密**）を要する。
いま持っている予算は `position right ≤ 2|w| − 1` なので、
`position (right right) = position right + 1 ≤ 2|w|` となり**最終位置で `canRight` が偽**。
**`MatchRest` に乗る前に、最終位置で `canRNext` が本当に要るのかを確かめること。**
（要るなら `MatchRest` の切り方が間違っている＝また「狭く/広く切った」問題。）

### 残り 9 個

`matchLanding` / `shiftEntryLanding` / `shiftExitLedger` / `rewindMargin` /
`shiftPalAtScanStates` / `verifierRunAlongRun` / `marksEntry` / `cycleOracle` /
`localRealization`。

## 2026-09-19 n96: 目標を固定し公理を原子化（10 個）— `bg` 場を放電、経路を全原子に記録

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 10 個の原子的義務を `axiom` として持つ。
無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

### 進捗の計器が変わった

コウタの提案で `PalInPeg.unconditional : RecognizedByTotalPEG PAL` を**閉じた項**として
置き、足りない義務を `axiom` にした。`PalPeg/Axioms.lean` の
`#guard_msgs in #print axioms` がラチェットになっている。

**公理は 1 場ずつの原子に分解した。** 束ねると「1 個外す」が測れないため。
数は 6（束）→ 10（原子）に増えたが、束を分解した等価な数は 11 で、
`bg` 場の放電で 1 つ減っている。

### 今回放電したもの（すべて新規入力ゼロ or 既存 axiom のみ）

| 放電 | 鍵 |
|---|---|
| `bg` 場（scan landing 3 つのうち 1 つ） | `CentreLedger` ← `LPackM3`、`canRight`・半径上界はタダ |
| `LPackM3` の trace 搬送（1 手目以降） | 4 葉パックのうち 3 つがタダ |
| `AuxPack`（1 手目以降） | `Coupled`/`CopyPack` は boot からタダ（tick が側条件なし）、`FrontPack` は 1 手目以降 |
| `LTickLeaves3.initLedger` / `.replayLedger` | `initVM` の `center = right`、`LPackM2.centreRep` |
| `CentreLedger` の `canRight center` / `Sane center` | `RadLedger.le` ＋ `rightHeadPos_le_alongTrace` ＋ `SanePack.saneC` |
| `shift_done` の `canRight` と半径上界 | 終端報告点から front ポテンシャルで後ろ向き伝播 |
| `Extra7.scanAvail`（＝`hee`/`het`） | 同上（CLAUDE.md の「偽の疑い」は誤りだった） |

### 10 原子の経路は `PalPeg/PalInPegUnconditional.lean` の docstring に表で埋め込んだ

要約: producer が無いのは `chainBackLag` / `rewindMargin` / `localRealization` の 3 つ。
`shiftExitLedger` は `radiusExact` を shift 相へ運ぶ仕事（材料は §5d に揃っている）。
`matchLanding` は `MatchRest` の 4 場に割れ、`repV` は `VerRun`、残り 3 つが新残差。
`marksEntry` の `EntryCounters` は `RadiusRep`（＝`radiusExact` と同内容）を含むので
**`shiftExitLedger` と材料を共有する**。

### この近傍のタダ飯は尽きた

残り 10 原子はどれも実作業。ただし足場は揃った:
* 目標が閉じた項 1 個に固定され、ラチェットが後退を検出する
* 義務はすべて **trace 形**（global 形は原理的に落ちないと判明済み）
* 名前が中身を表すので同じ部品を二度探さない

## 2026-09-19 n95: `AuxPack` は boot で偽 — `lpackM3_steps` は boot 根では使えない（機械検査）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 6 義務を axiom として持つ。無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CentreLedger` の等式（`radiusExact`）を自前で運ぶ前に、既存の
`CloseoutPackRun49.lpackM3_tick` が同じ保存を全 tick 形について証明済みなので、
`lpackM3_steps` に乗れないかを確認した。**乗れない。**

```
-- PalPeg/AuxPackNotAtBoot.lean
theorem not_auxPack_at_boot (w : List (Fin 2)) : ¬ AuxPack (boot w).ctl (boot w).vm :=
  fun hAuxPack => hAuxPack.front.notInit rfl
```

`AuxPack` は `FrontPack` を場に持ち、`FrontPack.notInit : c.mode ≠ Mode.init`。
boot の制御は `initial 2048 = ⟨.init, …⟩` なので衝突する。
`lpackM3_steps` は `hLv : ∀ i ≤ Tc w.length, … ∧ AuxPack (st i).ctl (st i).vm ∧ …` を
取るが `st 0 = boot w` なので **`hLv 0` が充足不能**。
つまりこの定理は boot 根の trace には適用できない（偽の前提を要求しているのと同じで、
前進として数えられない）。

### `LPackM3` を運ぶための選択肢

1. 添字を `1 ≤ i` に制限する（`mode ≠ init` は 1 手目以降は定理:
   `BranchSupply.mode_ne_init_alongTrace_afterFirstStep`）
2. `AuxPack` の場を mode で守る
3. cycle 起点（`InvLPC` の scan 状態）から運ぶ ——
   `CloseoutOracleW.packRunR_MW` が実際にやっていること（`auxPack_steps` を
   `hlive_of_invLPC` ＋ `InvLPC` 起点の `AuxPack` から回す）

**1 が一番安い**（`FrontPack` は `frontPack_alongTrace` で 1 手目以降タダ。
残るは `Coupled` と `CopyPack`）。

### 教訓

`lpackM3_steps` は build が通っていて `#print axioms` も標準公理のみだが、
**前提が充足不能なので誰も使えない**。これは「build が通る」「公理が綺麗」では
検出できない種類の不良で、**前提の充足可能性を確認しないと前進と誤認する**。
`unconditional` の axiom 方式にした理由がまさにこれ:
目標から逆に辿るので、使えない補題は自然に浮かび上がる。

## 2026-09-19 n94: 目標 `PalInPeg.unconditional` を作り、残り 7 義務を `axiom` として明示

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）。既存の旗艦定理は標準公理のみ。
`PalInPeg.unconditional` は残り 7 義務を `axiom` として持つ。無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### コウタの提案（そのまま採用）

* 「unconditional はつくっておいて、前提の and でうめりゃいいのでは。その前提を
  いったん axiom にしといて外していく」
* 「トップダウンにまずそれを書いておいてビルド通すために前提をいったん axiom に
  しておく。で、検証したい前提ごとに axiom をはずして全部外せたら証明完了」

### 実装

`PalPeg/PalInPegUnconditional.lean`:

```
theorem unconditional : RecognizedByTotalPEG PAL :=
  given_globalScanLandings 0 0 0
    (obligation_shiftPalAtScanStates 0 0 0) (obligation_marksEntry 0 0 0)
    (obligation_cycleOracle 0 0 0) (obligation_localRealization 0 0 0)
    (obligation_backgroundLandingPayload 0 0 0) (obligation_matchLandingPayload 0 0 0)
    (obligation_shiftExitPayload 0 0 0)
```

`#print axioms unconditional` がそのまま TODO リストになる:

```
[propext, Classical.choice, Quot.sound,
 obligation_backgroundLandingPayload, obligation_cycleOracle,
 obligation_localRealization, obligation_marksEntry,
 obligation_matchLandingPayload, obligation_shiftExitPayload,
 obligation_shiftPalAtScanStates]
```

### ラチェット（`PalPeg/Axioms.lean`）

`#guard_msgs in #print axioms PalPeg.PalInPeg.unconditional` を置いた。

* 義務を 1 個証明して `axiom` を外すと **guard が壊れて更新を強制される**（前進の記録）
* うっかり新しい穴を開けても guard が壊れる（気づける）
* **guard が標準 3 公理だけになったとき §10.5 達成**が機械検査される

これで「前提が何本か」を数える曖昧さが消えた。**進捗は `unconditional` の公理リストの
長さ**という 1 つの機械検査可能な数になった。

### 報告の仕方を変える

これまでの「標準公理のみ」は既存の旗艦定理についての主張として維持するが、
目標定理については **「残り N 義務を axiom として明示」** と書く。
`unconditional` があることを「無条件 PAL 完成」と誤読させないこと。

### ルートは 4 本

`PalPeg.PalInPeg`（目標と部分結果）/ `PalPeg.Canonical`（主線の索引）/
`PalPeg.Workbench`（未配線の部品）/ `PalPeg.Axioms`（監査とラチェット）。

## 2026-09-19 n93: `CentreEq` の遷移保存を 8 本 landing — rewind 相だけが heads を動かす

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CentreEq s := (position s.center : ℤ) + value s.radius = position s.right`
（＝`CloseoutPackRun47.CentreLedger` の第 3 節）の遷移保存を、一次情報で確認した分だけ
機械検査した（`PalPeg/BranchSupply.lean` §5d、8 本すべて一発で通った）。

| 定理 | 遷移 | 効果 |
|---|---|---|
| `centreEq_boot` | boot | `center = right`、`radius = 0` |
| `centreEq_init` | `initVM` | `center = right`、radius 保持（init 相で 0） |
| `centreEq_background` | `backgroundS` | 3 つとも不変 |
| `centreEq_beginShift` | `beginShiftVM'` | 3 つとも不変 |
| `centreEq_beginFallback` | `beginFallbackVM'` | 3 つとも不変 |
| `centreEq_restart` | `restartVM` | 3 つとも不変 |
| `centreEq_replayStart` | `replayStartVM` | **前提なしで再確立**（`center = right`、`radius = reset`） |
| `centreEq_of_eq_heads` | 汎用 | `center = right ∧ radius = 0 → CentreEq` |

### レンズで切り分けた結論（重要）

* `fppLens.get s = s.fpp` のみ（`TopVM:53`）→ **fpp 相の 8 遷移**
  （`copyOne`/`copyEnd`/`fppStart`/`homeStep`/`fppSlice`/`fppDone`/`atEnd`/`markForward`）は
  center/radius/right を**触らない**ので `CentreEq` は自明に保存される。
* `rewindLens.get s = ⟨s.fpp, s.left, s.center, s.right, s.length, s.radius⟩`（`TopVM:73`）
  → **`markBack` / `rewindOne` / `rewindPair` の 3 遷移だけ**が heads と radius を動かす。
* `matchedPlace` は `t = (if b then {s with replay := dec s.replay} else s)`
  （`TopMerge:59`）で右ヘッドを動かさない。右ヘッドが進むのは `compare`（`afterCompare`）で、
  そこでは `radiusAfter = inc` が同時に効くので保存される。

### 帰結: mode guard で残差ゼロになる見込み

rewind 相（`choose` / `rewind`）を除外し、`replayStart` も除外した

```
CentreEqG c s := c.mode ≠ Mode.choose → c.mode ≠ Mode.rewind →
                 c.mode ≠ Mode.replayStart → CentreEq s
```

なら、**壊れる 3 遷移はすべて行き先が除外領域**で、出口の `replayStartVM` が
前提なしで再確立するので、**追加の葉なしで tick 保存が示せる**見込み。
（`markBack` の行き先 mode が `choose` であることは `Tick`（`GalilScaffoldTop:109`）の
構成子表で確認済み。）

### 次のセッションの手順

1. `CentreEqG` を定義し `centreEqG_tick` を `cases` で書く（24 構成子）。
   除外領域が行き先の場合は `intro` の第 1〜3 引数で矛盾（`by decide`）。
   残りは §5d の 8 本と fppLens の射影（`Frame.pull` の定義を確認）で埋まる。
   **注意**: `cases ht` は非変数の状態では dependent elimination に失敗するので、
   状態を変数に一般化した補助補題にしてから `cases` する（n91 で確立した型）。
2. `centreEqG_trace` を帰納で出す（`chainPosInv2_trace` と同じ形）。
3. `CentreLedger` が全 scan 状態で出る → `BgStartP2` → `bg` 場が `hver` に合流。
   `shiftDoneLedger` も落ちる。`hme` の `EntryCounters` 半分も `RadiusRep` 経由で落ちる。

## 2026-09-19 n92: `CentreEq` 不変量の tick ごとの分析 — 次のセッションはこれを書く

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`LTickLeaves3` の残り 2 場のうち `shiftDoneLedger` の本体は等式

```
CentreEq s := (position s.center : ℤ) + value s.radius = position s.right
```

を shift 相でも持つこと。**`LPackM2` に radius を縛る場は無い**（場は `packM`
（`lrepM`/`scanGeom`）・`scanGeomR`・`shiftGeom`・`rrep`・`centreRep`・`centreOrder` の
6 つだけ）ので、`RadLedger.le`（`≤`）からは出ない。

### 一次情報で確認した遷移ごとの効果

| tick 形 | center | radius | right | `CentreEq` |
|---|---|---|---|---|
| boot（`initVM0`） | `= right` | `reset`（0） | — | **成立** |
| `init`（`initVM`、`TopReplay:20`） | `= right s.right` | `= s.radius`（init 相で 0） | `= right s.right` | **保存**（n91 で機械検査済み） |
| `scan_wait` / `scan_count`（`backgroundS`） | 不変 | 不変 | 不変 | **自明に保存** |
| `scan_match`（`afterCompare` ＋ `matchedPlace`） | 不変 | **`radiusAfter = inc`（無条件）** | +1 | **保存** |
| `shift_one`（`shiftTick`、`ChainInputSupply:1445`） | `right s.center`（+1） | **`dec s.radius`（−1）** | 不変 | **保存** |
| `shift_done` | VM 不変 | VM 不変 | VM 不変 | **自明に保存** |
| `replayStart`（`replayStartVM`、`TopReplay:28`） | `= s.center` | `reset`（0） | `= s.center` | **成立**（center = right） |
| `scan_shift`（`beginShiftVM'`） | ? | ? | ? | **未確認** |
| fallback / rewind 系（`beginFallbackVM'`、`markBack`、`rewindOne`、`rewindPair`） | 中心を動かす | ? | ? | **未確認（ここが本体）** |
| copy / home / fpp / markEnd / choose | fpp walker と period テープのみのはず | — | — | **未確認（不変なら自明）** |

```
-- PalPeg/GalilScaffoldChainInputSupply.lean:1445
def shiftTick (s : ShiftState) : ShiftState :=
  ⟨right s.center, right (right s.left), dec s.remaining, dec s.radius, …⟩
```

### 次のセッションの手順（明確）

1. `CentreEq` を定義し、`centreEq_boot` を `rfl` 級で示す。
2. 上の表の「保存」行を機械検査する（`backgroundS_fields` / `afterCompare_radius` /
   `shiftTick` / `initVM` / `replayStartVM` の射影補題は既にある）。
3. 「未確認」行を一次情報で埋める。**`beginFallbackVM'` と rewind 系が本体**
   （中心を動かすので、radius と右ヘッドの関係を再確立する必要がある）。
   ここは `Manacher`/`PalAt` 層の材料（`GalilLiveCentre*`、`GalilPeriodUnion`）が効く可能性。
4. `centreEq_trace` が出れば:
   * `shiftDoneLedger` が落ちる（`CentreEq` ＋ n89 の無料 2 節）
   * `CentreLedger` が全 scan 状態で出る（`LPackM3` を経由せず）
   * → `BgStartP2` → `bg` 場が `hver` に合流
   * `hme` の `EntryCounters` 半分も `RadiusRep`（＝`Canonical radius` ＋
     `value radius = rad`、後者は `CentreEq` ＋ `ScanInvariant.rightPos`）で落ちる

**つまり `CentreEq` 1 本で `bg` と `hme` の両方が進む。** これが今の最短経路。

### 残っているもう 1 場

`backLag : ∀ v h lag margin ver, s.chain = .back v h lag margin ver →
Canonical lag ∧ 0 ≤ value lag`。`LagCan` は `.watch` 相なので別物。
chain の `.back` 相の lag 形状で、`ChainStep.copyEnd` が `.copy` の lag を
`.back` に持ち込むところで確立される。`CloseoutChainPack` / `CloseoutChainSideR` に
同名の場があるので、そこの証明を見ること。

## 2026-09-19 n91: `LTickLeaves3` は 4 場 → 2 場（`initLedger` もタダ）＋ 古い記憶の訂正

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### 訂正: `radiusAfter` は無条件に `inc`

CLAUDE.md / 記憶に「`compareVM`/`compareFound` に `radiusAfter`（**search 活性 ∧ chain
idle なら不変**、さもなくば inc）を追加」と書いてあったので、
`CentreLedger`（`position center + value radius = position right`）が全 scan 状態では
偽ではないかと疑った。**一次情報を見たら違った**:

```
-- PalPeg/GalilScaffoldTopSearch.lean:37
def radiusAfter (s : GalilVM) : Counter := GalilScaffoldCounter.inc s.radius
```

**無条件の `inc`。** `backgroundS` は右ヘッドも radius も変えない
（`backgroundS_fields` の `hr : t.right = s.right`、`hrad : t.radius = s.radius`）ので、
等式は background で自明に保存され、matched compare では右ヘッドと radius が同時に +1。
よって `CentreLedger` が全 scan 状態で成り立つ設計は整合している。

**教訓**: 過去の自分の記述（CLAUDE.md・メモリ）を一次情報として使わない。疑ったら定義を開く。

### `LTickLeaves3.initLedger` はタダ

`initVM entry s t`（`GalilScaffoldTopReplay:20`）は `t.right = right s.right`、
`t.center = right s.right`、`t.radius = s.radius` を固定する。つまり
**`t.center = t.right`** なので等式は `value t.radius = 0` に落ち、それは
`RadLedger.initZero`。`canRight t.center` / `Sane t.center` は `t.center = t.right` と
**次状態が scan 相**（`Tick.init` の行き先）から §5 の無料補題で出る
（`initLedger_of_trace`）。

`t` は `initVM` で全成分が決まるわけではない（`periodOnly` などは自由）が、
`CentreLedger` が読むのは `center`/`radius`/`right` の 3 つだけで `initVM` が固定するので
trace 上の `st (i+1)` から移せる。

実装上の注意: `cases ht` は `ht : Tick F 2048 (st 0) (st 1)` のように**非変数**の
状態に対しては dependent elimination に失敗する。状態を変数に一般化した補助補題
（`key : ∀ x y, Tick … x y → x.ctl.mode = Mode.init → …`）にしてから `cases` する。
残りの 23 構成子は `| _ => simp_all` で落ちる（各構成子が mode を固定しているため）。

### `LTickLeaves3` の現状

| 場 | 状態 |
|---|---|
| `replayLedger` | **タダ**（n89） |
| `initLedger` | **タダ**（今回） |
| `backLag`（`.back` 相の lag 形状） | 残る |
| `shiftDoneLedger`（shift_done での `CentreLedger`） | 残る。等式 `value radius = r` が本体 |

`shiftDoneLedger` の等式について: `ShiftGeom`（rem = 0）は
`position right = position center + r` を与え、`RadLedger.le` は
`value radius ≤ r` の向きしか出ない。逆向き（`r ≤ value radius`）が要る。
`LPackM2` の場に radius を縛るものがあるか未確認。

### 次の一手

1. `LPackM2` の全場を列挙して、shift 相で radius を縛る場があるか確認する。
2. なければ `shiftDoneLedger` は真の残差。`backLag` と合わせて 2 場。
3. 2 場が埋まれば `LPackM3` が trace に載り、`CentreLedger` → `BgStartP2` → `bg` 場が
   `hver` に合流する（`hme` の `EntryCounters` 半分も同時に落ちる可能性が高い）。

## 2026-09-19 n90: `CentreLedger` の等式の出処は `EntryCounters` の `RadiusRep`

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n89 で `CentreLedger` は等式
`position center + value radius = position right` 1 本に縮んだ。その出処が確定した。

```
GalilGlueBLeaves.EntryCounters w s :=
  ∃ Rad, ScanInvariant w (position s.center) Rad s.left s.right ∧
         RadiusRep s.radius Rad ∧ SpanRep s ∧ Canonical s.length
RadiusRep counter rad := Canonical counter ∧ value counter = rad
ScanInvariant.rightPos : position r = center + radius
```

差をとれば等式（`BranchSupply.centreEq_of_entryCounters`、標準公理のみ）。
`centreLedger_of_entryCounters` で `CentreLedger` が `EntryCounters` ＋ `CentreRep` から
完全に出る（`canRight center` と `Sane center` は n89 でタダ）。

### なぜ `RadLedger` では足りないのか（重要）

`RadLedger.le` は `position center + value radius ≤ position right` で**不等号**。
探索が活性のあいだ右ヘッドだけ進む場合があるので（`compareVM` の `radiusAfter` は
「search 活性 ∧ chain idle なら不変」）、等式は一般には成り立たない。
**正確さを担保するのは `RadiusRep`**（半径カウンタの値が `Rad` に等しい）。
だから `CentreLedger` は「どの scan 状態でも」ではなく、
`EntryCounters` が成り立つ状態（`Inv` ＋ `SpanRep`、`InvLPC` の各点）で使うもの。

### 残差の現状（`bg` 場まで）

`bg` ← `bg_at_of_supply`（状態局所、n88）の 4 入力:

| 入力 | 状態 |
|---|---|
| `hrepR` | **タダ**（`LPackM2.packM.scanGeom` / `scanGeomR`） |
| `hrepV` | `hver`（`VerRun`）の第 1 成分 |
| `hL` | `hver` の第 2 成分 |
| `hstart`（`BgStartP2`） | `bgStartP2_of_centre` の 3 入力のうち `canRight s.right` と半径台帳は**タダ**、`CentreLedger` は **`EntryCounters` ＋ `CentreRep` に帰着** |

つまり `bg` 場の残差は **`EntryCounters` ＋ `CentreRep` を chain 誕生点（scan かつ idle chain）で持つこと**に縮んだ。

### 次の一手

1. `EntryCounters` を trace の scan 状態で供給する経路を確定する。
   `GalilGlueBLeaves.entryCounters_of_inv (h : Inv raw c r) (hS : SpanRep r)` があるので、
   `Inv` と `SpanRep` が trace の scan 点で取れるかを調べる
   （`CloseoutMarksFree.entryCounters_of_invLPC` は `InvLPC` からは取れると書いている）。
2. `CentreRep` は `LPackM2.centreRep` の guard が `rewind ∨ replayStart` なので
   scan では取れない。scan 相の中心ヘッド表現の供給元を探す
   （`MInv` か `ScanInvariant` の left/right から中心を復元できるか）。
3. `LTickLeaves3` の残り 3 場（`backLag` / `initLedger` / `shiftDoneLedger`）は
   `LPackM3` 経路用。`bg` を `EntryCounters` 経路で直接落とすなら `LPackM3` は不要になる。

## 2026-09-19 n89: 中心ヘッドも動ける — `CentreLedger` は**等式 1 本**に縮んだ

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`CloseoutPackRun47.CentreLedger s := canRight s.center ∧ Sane s.center ∧
(position s.center : ℤ) + value s.radius = position s.right` の 3 節のうち **2 節が落ちた**
（`PalPeg/BranchSupply.lean` §5b）。

| 節 | 出処 | 状態 |
|---|---|---|
| `Sane s.center` | `GalilTrailSane.SanePack.saneC`（`CloseoutLPack6.sanePack_pt` が `PreTrace` ＋ `LeftLive` だけで trace 全点に） | **タダ** |
| `canRight s.center` | `position center ≤ position right`（`RadLedger.le` ＋ `.nonneg`）＋ `rightPos_le_trace`（n87）＋ `CentreRep`（`LPackM2.centreRep`） | **タダ**（`centreCanRight_of_trace`） |
| `position center + value radius = position right` | — | **残る（等式）** |

### `LTickLeaves3.replayLedger` もタダ

`replayLedger : c.mode = Mode.replayStart → canRight s.center ∧ Sane s.center` は
上の 2 節そのもの。`LPackM2.centreRep` の guard は `rewind ∨ replayStart` なので
replayStart で使える（`replayLedger_of_trace`）。

### 等式について（なぜ独立なのか）

`RadLedger.le` は `≤` しか与えず、`ScanInvariant.rightPos`（`position right =
position center + rad`）と合わせても `value radius ≤ rad` の向きしか出ない
（`PosPayload2.radLe` も同じ向き）。**逆向き（半径カウンタが正確に距離を測る）は
独立した不変量**で、それが `LPackM3.centreLedger` の中身。boot で成立
（`position center = position right`、`radius = 0`）し、background で保存され、
3 つの landing（init / shift_done / replayStart）で再確立される。

### `LTickLeaves3` の現状（`LPackM3` を trace に載せるための唯一の残り）

| 場 | 状態 |
|---|---|
| `backLag`（`.back` 相の lag 形状） | 残る。`LagCan` は `.watch` 相なので別物 |
| `initLedger`（init 遷移先の `CentreLedger`） | 残る。boot 直後なので計算で出るはず |
| `shiftDoneLedger`（shift_done での `CentreLedger`） | 残る。**等式の再確立が本体** |
| `replayLedger` | **タダになった**（今回） |

### 次の一手

1. `initVM` の定義を読んで `initLedger` を計算で落とす（boot 直後、`center = right`、
   `radius = 0` から等式は自明のはず）。
2. `backLag` を `.back` 相の構成から出す。
3. `shiftDoneLedger` の等式を `ShiftGeom`（rem = 0）から出す。
4. 揃えば `LPackM3` が trace に載り、`CentreLedger` → `BgStartP2` → `bg` 場が
   `hver` に合流する。

## 2026-09-19 n88: `canRight` は trace 全域でタダ — `Extra7`（`hee`/`het`）も同時に落ちる

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n87 の `shiftCan_of_trace` は shift 相専用に書いていたが、論法は mode に依存しない。
一般化した結果、**`canRight` は「右ヘッドが入力を表現している trace 点」でタダ**になった。

| 新しい定理（`PalPeg/BranchSupply.lean` §5） | 内容 |
|---|---|
| `canRight_at_trace` | `Represents` ＋ `focus ≠ none` があれば `canRight (st i).vm.right`（`1 ≤ i`） |
| `frontPack_of_trace` | `FrontPack` は trace の 1 手目以降タダ（`tick_mode_ne_init` ＋ `frontPack_trace`） |
| `scanCanRight_of_trace` | **scan 相の `canRight` ＝ `CloseoutPackRun46.Extra7.scanAvail`。つまり `hee` / `het` の中身がタダ** |

`Extra7.scanAvail := mode = scan → ¬replaying → canRight right` なので、
`scanCanRight_of_trace` はそれより強い（replaying でも成立）。
CLAUDE.md §3 が「`hee`/`het` の残差（scan 状態で `canRight`）は**偽の疑いが強い**」と
書いていたのは、`Inv.input` が右ヘッドの位置を縛らないことを根拠にしていた。
**位置を縛るのは `Inv` ではなく front ポテンシャルと終端の報告点だった。**

側条件 `htc : 1 ≤ Tc w.length` は `PreTraceB.tc1 : Tc 1 = 1` と `PreTrace.mono` から出る
（`1 = Tc 1 ≤ Tc w.length`）。

### `bg` 場の分解（§7）

`CloseoutPackRun48.h_bgP2_of_supply` は 4 入力すべてを源状態でだけ使う（`Run48:186–192`）。
状態局所版 `bg_at_of_supply` を置いた。入力の現状：

| 入力 | 状態 |
|---|---|
| `hrepR`（右ヘッドが入力を表現） | **タダ**（`LPackM2.packM.scanGeom` / `scanGeomR`） |
| `hrepV`（verifier が入力を表現） | `hver`（`VerRun`）の第 1 成分 |
| `hL`（`LagCan`） | `hver` の第 2 成分 |
| `hstart`（`BgStartP2`、chain 誕生の形） | **残る**。`CloseoutPackRun47.bgStartP2_of_centre` が `canRight s.right`（**タダになった**）＋ 半径台帳（**タダ**）＋ `CentreLedger` から出す |

**残る唯一の穴は `CentreLedger`**（`LPackM3.centreLedger`）。`LPackM3` を trace に載せる
には 4 葉パックのうち `LTickLeaves3`（`backLag` ＋ init/shift_done/replayStart の 3 台帳）
だけが要る（他 3 つは `auxPack_steps` / `CloseoutPackW.lticksN_of_lpackM2_W` /
`lTickLeaves2_of_shiftPalG` でタダ）。

### 次の一手

1. `LTickLeaves3` の 4 場を埋める（`backLag` は `LagCan` から、3 台帳は各 landing の幾何）。
2. `LPackM3` を trace に載せる → `CentreLedger` → `BgStartP2` → `bg` 場が `hver` に合流。
3. 同様に `matchLand` を `MatchRes2`（`matchRes2_of_lpackM3` ＋ `MatchRest`）から。
   `MatchRest.repV`/`repVmid` は `hver` と同型、`canRNext` は `canRight (right s.right)`
   なので `CloseoutCanRightBound` の 2 歩版（`:76`）で出るはず。
4. 残れば `entryLand` だけ。

## 2026-09-19 n87: `shiftDone` 義務を**完全に放電** — 新規入力ゼロ

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`BranchAt.shiftDone`（＝旧 `H_shiftDoneRad2`）の 2 節が両方とも消えた。

### 半径台帳（n86）

`RadLedger.le : position center + value radius ≤ position right` ＋
`ScanInvariant.rightPos` の差。`RadLedger` は `CloseoutLPack6.radLedger_pt` が
`PreTrace` ＋ `LeftLive` だけで trace 全点に与える。

### `canRight s.right`（今回）

**終端の報告点から後ろ向きに伝播する。**

1. `PreTrace.report` → `GalilLedgerAssembly.ReportPointAt.atPrefix`:
   `position (st (Tc |w|)).vm.right = 2|w| − 1`
2. front ポテンシャル（`GalilRunTrace.front s = position right + value replay`）は
   tick で単調（`GalilFrontMono.front_tick_mono`）→ `front_mono_trace`（trace 指標の帰納）
3. `position right ≤ front`（`FrontPack.replayPos` / `.rest` だけから）→ `position_le_front`
4. 終端では `front = position right`（`CloseoutFrontExtra.front_eq_position`、
   `ReportPointAt.notReplaying`）
5. よって `position (st i).vm.right ≤ 2|w| − 1` が trace 全域で成立（`rightPos_le_trace`）
6. `CloseoutCanRightBound.canRight_of_position_bound` に `m = |w|` で流す。
   shift 相の右ヘッドの `Represents`/`focus ≠ none` は
   **`LPackM2.shiftGeom` の `RRep`** が持つ（`LPackM2` は `PreTraceIMW.packs .m2`）

**鍵になった補題（新規・一発で通った）**:
`tick_mode_ne_init` — **`Tick` には `mode := .init` へ行く構成子が無い**
（`GalilScaffoldTop:109` の全構成子の行き先 mode は scan/shift/copy/home/fpp/markEnd/
choose/rewind/replayStart か「変えない」）。だから trace は 1 手目以降 `init` に戻らず
（`mode_ne_init_of_trace`）、`GalilTrailRad.frontPack_trace` が trace の各点で使える。
`i = 0` は `mode = init ≠ shift` で除外される（`initial delay = ⟨.init, …⟩`）。

`Steps` 版（`CloseoutFrontExtra.position_le_of_front_steps`）ではなく **trace 指標**で
書く必要があった: 中間状態の `CentreLive` を `centreLive_trace` は trace の点でしか
与えないのに対し、`Steps` 版は任意の到達状態を量化するから。

### 最上位

`CloseoutFinalBranch.pal_in_peg_final43` — Prop 引数 6 本
（`hSP` `hme` `hor` `hC` `hres` `hver`）。残差は `BranchRes3` の **3 場**
（`bg` / `matchLand` / `entryLand`）＋ `hver`。**義務の実数 8。**

### 本数の誠実な読み方

| 定理 | Prop 引数 | 義務の実数 | 形 |
|---|---|---|---|
| `final39`（正本） | 7 | 7 | 分岐 3 本は **global**（放電不能） |
| `final43` | 6 | 8 | 分岐 3 場は **run/trace 形**（放電可能） |

義務の実数では `final39` の 7 が最小なので**正本は据え置き**。ただし `final39` の
`hbgP`/`hmatchP`/`hsdP` は global なので原理的に放電できず、実際に詰めるのは `final43` 側。

### 次の一手 — `bg` と `matchLand`

`H_bgP2` の docstring が明記している：「Everything chain-side now follows from
`chainPos_step`; what is left at the source is the chain-start shape
(`s.chain = idle`) together with `ConsumeAvail`」。`CloseoutPackRun48.h_bgP2_of_supply`
の 4 入力のうち

* `hrepR`（右ヘッドが入力を表現）← **`LPackM2.packM.scanGeom` でタダ**
* `hrepV`（verifier が入力を表現）← **`hver`（`VerRun`）の第 1 成分**
* `hL`（`LagCan`）← **`hver` の第 2 成分**
* `hstart`（`BgStartP2`）← `CloseoutPackRun47.bgStartP2_of_centre` が
  `canRight s.right`（scan 相、`Extra7`）＋ 半径台帳（済）＋ `CentreLedger`
  （`LPackM3.centreLedger`）から出す

**ただし Run48 のこれらの入力は「任意の scan 状態 ＋ `ChainPosInv2`」形なので、
そのままでは `hrepV` が偽の疑いが強い。trace 形に書き換えてから使うこと。**
うまく行けば `bg` / `matchLand` が `hver` に合流し、`final43` は
`hSP` `hme` `hor` `hC` `entryLand` `hver` の **義務 6 本**（`final39` の 7 を下回る）。

## 2026-09-19 n86: `shiftDone` 義務の半径台帳は**タダ** — `RadLedger` から出る

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。正本の最上位は引き続き `pal_in_peg_final39`（7 前提）。**

### 放電できたもの

`BranchAt.shiftDone`（＝旧 `H_shiftDoneRad2`）は

```
canRight s.right ∧ ∀ rad, ScanInvariant w (position s.center) rad s.left s.right →
  value s.radius ≤ (rad : ℤ)
```

の連言だが、**後者は新規入力ゼロで出る**：

* `CloseoutRadPack.RadLedger.le : position s.center + value s.radius ≤ position s.right`
* `ScanInvariant.rightPos : position s.right = position s.center + rad`
* 差をとって `value s.radius ≤ rad`（`BranchSupply.radLe_of_radLedger`）

そして `RadLedger` は **`CloseoutLPack6.radLedger_pt` が `PreTrace` ＋ `LeftLive` だけで
trace の全点に与える**（`radLedger_boot` は定理、`LeftLive` は `leftLive_of_lpackM`）。
つまり `needIMW'_le_R` の中で内部調達でき、前提として現れない。

### 追加した部品（`PalPeg/BranchSupply.lean` §3–§4）

* `radLe_of_radLedger` / `shiftDone_of_radLedger`
* `BranchRes` — 4 場のうち `shiftDone` を **`shiftCan`（`canRight s.right` のみ）** に縮めた構造
* `branchAt_of_res` — `BranchRes` ＋ `RadLedger` → `BranchAt`
* `chainPosInv2_trace` — `ChainPosInv2` を **trace 指標**で運ぶ（`lpackM3_steps` と同形の帰納）
* `BranchResTrace` / `needIMW'_le_R` — `RadLedger` を内部調達する `needL'` 上界

**なぜ trace 指標にしたか**: `BranchRun` は `Steps` で到達する**すべての**状態を量化するが、
`Tick` は関係なので trace 外の状態も含む。一方、放電の材料（`RadLedger`、`LPackM2`）は
`radLedger_pt` / `PreTraceIMW.packs` が **trace の点 `st i`** でしか与えない。
`chainPosInv2_steps_run` を使う経路は `steps_of_trace` で trace の鎖しか渡さないので、
trace 指標で十分かつ供給と噛み合う。

### 最上位

`PalPeg/CloseoutFinalBranch.pal_in_peg_final42` — Prop 引数 6 本
（`hSP` `hme` `hor` `hC` `hres` `hver`）。`final41` との違いは `hres` が
`BranchResTrace`（`shiftDone` の半径台帳を落とした 4 場）であること。

**正直な読み方**: Prop 引数は 6 のままで、減ったのは `shiftDone` 場の**半分**。
義務の実数は 9 → 8.5 相当。正本は引き続き `pal_in_peg_final39`（7 本、束ねていない）。

### 次の一手 — `shiftCan`（`canRight s.right` at shift_done）

経路は見えている：

* `CloseoutClockFront.canRight_of_run`（:152）は **mode 条件なしで** `canRight y.vm.right`
  を出す。必要なのは
  - `hg : ∀ m z, Steps … m x z → FrontPack z.ctl z.vm` — `GalilTrailRad.frontPack_trace`
    が trace から与える（`CloseoutLPack6:290` が既に使っている）
  - `hx0 : front x.vm = 0`, `hxc : x.ctl.clock = delay` — boot の値
  - `hrep`/`hpres`（右ヘッドの `Represents` と `focus ≠ none`）— shift 相では
    **`LPackM2.shiftGeom` の `RRep`** が持つ
  - `hn : n < delay * (2 * w.length)` — run 長の予算。**ここが唯一の未確認**。
    `PreTrace.cost` / `Tc` の上界と突き合わせること。
* これが通れば `shiftCan` も消え、`BranchRes` は `bg` / `matchLand` / `entryLand` の 3 場になる。

## 2026-09-19 n85: 4 分岐義務を run 形に弱めた — `∀ c s` では原理的に放電できない

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。正本の最上位は引き続き `pal_in_peg_final39`（7 前提）。**

### 何をしたか

`CloseoutPackRun41` の 4 分岐義務（`H_bgP2` / `H_matchP2` / `H_shiftEntry2` /
`H_shiftDoneRad2`）はどれも `∀ (c : Control) (s : GalilVM), …` で**任意の状態**を
量化している。ところが `chainPosInv2_tick` の本体を読むと、**4 本とも自分の `(c, s)` で
しか使っていない**（Run41 の旧 :289/:292/:296/:301/:318 の 5 箇所、すべて `hbg c s` の形）。

1. **状態局所化**（`CloseoutPackRun41` を編集、後方互換）
   * `BranchAt w c s` — 4 義務を 1 状態に束ねた構造
   * `chainPosInv2_tick_at` — 旧 `chainPosInv2_tick` の本体、`BranchAt` を取る
   * `branchAt_of_global` — global 4 本から `BranchAt` を作る
   * `chainPosInv2_tick` — 旧の名前と型のままのラッパー（**既存の呼び出し側は無改造**）
2. **run 形化**（新規 `PalPeg/BranchSupply.lean`）
   * `BranchRun w x := ∀ m z, Steps … m x z → BranchAt w z.ctl z.vm`
   * `branchRun_of_global`（global → run 形、**逆は無い**）
   * `chainPosInv2_steps_run` — `ChainPosInv2` を run 形の義務で運ぶ
     （再指標化は `Steps.succ ht`、`CloseoutBundleRun.roundBundle_steps_run` と同形）
   * `shiftLocalS_of_branchRun` / `needIMW'_le_B`（3 段の本体は n83 で括り出した
     `ShiftLocalRun.needIMW'_le_of_shiftLocal` に載せた）
3. **最上位**（新規 `PalPeg/CloseoutFinalBranch.lean`）
   * `pal_in_peg_final41` — Prop 引数 6 本（`hSP` `hme` `hor` `hC` `hB` `hver`）

### なぜ run 形でなければならないか（これが本質）

4 義務を放電する材料は run に沿ってしか存在しない：

* `LPackM2.shiftGeom`（`CloseoutPackRun23:103`）— `H_shiftDoneRad2` の `canRight` と
  半径上界はここから出る（`CloseoutShiftDoneP.canR_of_shiftGeom` /
  `radEq_of_shiftGeom_done`）。`LPackM2` は run の各点に `IPackMW.m2` としてある。
* chain 側台帳 `ChainPos`（Run41、Run38 の `SrcPos` を吸収）— `chainPos_step` /
  `chainPos_matched` で run を運ばれる。
* 入力供給（verifier が入力を表現する）— `CloseoutVerSide.VerRun` が run 形で束ねている。

**任意の状態にこれらは無い。だから `∀ c s` の形のままでは原理的に放電できない。**
これは `hpack` が偽だったのと同じ病の裏返し: `hpack` は run の事実を一状態述語として
書いたので**偽**になり、4 分岐義務は一状態述語の族を global に量化したので
**放電不能**になっていた。正しいのはどちらでもなく、**run に沿って量化する**こと。

### 本数の誠実な読み方 — `final41` は正本ではない

`pal_in_peg_final41` の Prop 引数は 6 本だが、**`hB` は 4 義務の束**である。
義務の実数で数えれば 9（run 形 4 ＋ `hver` ＋ `hSP`/`hme`/`hor`/`hC`）で、
`final39` の 7 より多い。**前進は本数ではなく「global → run 形」の弱化**であって、
義務が減ったわけではない。だから：

* **正本の最上位は引き続き `pal_in_peg_final39`（7 本、束ねていない）。**
* `pal_in_peg_final41` は**放電の作業場**として `Workbench` §2 に登録。

（Prop 引数の本数＝前提の本数ではない、という CLAUDE.md の規律をここでも適用した。
束ねて数字を作らない。）

### 次の一手

`BranchRun` の 4 場を run の各点で実際に放電する：

1. `shiftDone` ← `LPackM2.shiftGeom`（run の各点にある）＋ 区間予算
   ＋ `CloseoutShiftDoneP.canR_of_shiftGeom` / `radEq_of_shiftGeom_done`。
   **これが一番近い。** `LPackM2` は `PreTraceIMW.packs i hi |>.m2` で取れる。
2. `bg` / `matchLand` ← `ChainPos` の run 搬送（`chainPos_step` / `chainPos_matched`）。
   側入力の `ConsumeAvail` は全状態版が偽（`ConsumeAvailRefute.hav_false`）なので
   `CloseoutWatchSupply.chainPos_step_of_supply` ＋ `VerRun` を使う。
3. `entryLand` ← `ShiftPos2` の確立（`beginShiftVM'` の 1 consume）。

放電できた分だけ `BranchRun` の場が減り、全部落ちれば `final41` は
`hSP` `hme` `hor` `hC` `hver` の 5 本になる。

### 注意（引き継ぎ）

* `AuxPack` は **boot では成り立たない**（`AuxPack.front.notInit : mode ≠ init`）。
  だから `LPackM3` を boot 根の run に載せる道は無い。`AuxPack` は常に cycle 起点の
  `InvLPC` から `CloseoutPackRun2.auxPack_steps` で立てる。
* `CloseoutPackRun36.lticksN_of_lpackM2_pt` は `BigPack2MG`（＝`IPackMG` ＋ `Extra'`）を
  要るので W 経路では使えない。**W 版 `CloseoutPackW.lticksN_of_lpackM2_W` を使うこと。**
* `CloseoutBranchRes.shiftLocalS_of_run_res` はまだ `hfour` を取る（n83 以前）。
  残差経路では `ShiftLocalRun.shiftLocalS_of_run'` に載せ替える。

## 2026-09-19 n84: 3 分岐前提は同じ 1 つの run 形事実に合流する — 9 → 5 の筋

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

n83 で正本を 7 前提（`pal_in_peg_final39`）にしたあと、7 本それぞれの producer を
実見した（表は `lean-pal/PART_INDEX.md` §2a）。**残差は producer が 1:1 で化けるだけで
本数は減らない。** 減らすには残差を共有させるしかない。残差を並べて分かったこと:

### 発見 1: `ShiftGeom` は run 上でタダ

`hsdP`（`H_shiftDoneP`）は `CloseoutPackRun38:316` では**恒等**（`H_shiftDoneRes` は
`H_shiftDoneP` そのもの）だが、`CloseoutShiftDoneP.posPayload_of_shiftGeom`（:70）が
実質の分割を与える:

* `canR` ← `canR_of_shiftGeom`（`ShiftGeom` ＋ 区間予算 `position right ≤ 2m−1`）
* `radLe` ← `hrad`
* `pos` / `verNext` ← **`ChainSideAt`**（:61）

そして **`ShiftGeom` は `LPackM2` の場**（`CloseoutPackRun23:103`
`shiftGeom : c.mode = Mode.shift → ShiftGeom w s`）。`LPackM2` は
`IPackMW.m2`（`CloseoutPackW:67`）として run の各点にある。**つまりタダ。**

### 発見 2: 3 本の残差は同一の chain 側 verifier 台帳に合流する

| 前提 | 残差の chain 側の中身 |
|---|---|
| `hbgP` → `H_bgRes` | `SrcPos`（`saneVer` ＋ `backPos`）＋ `start`（idle 起点）＋ `verNext` |
| `hmatchP` → `H_matchRes` | `SrcPos` ＋ 起点の payload ＋ 同型の節 |
| `hsdP` → `ChainSideAt` | `pos`（`position verifier + lag = position right`）＋ `verNext` |

`ChainSideAt` の 2 節は `PosPayload` の `pos` / `verNext` と同一。そして
`CloseoutPackRun41:17` が明記している: **「`ChainPos` replaces Run38's `SrcPos`
(its `saneVer`/`backPos` are two of the clauses)」**、`:201`「which also absorbs
Run38's `SrcPos`」。

`ChainPos` は run を運ばれる: `chainPos_step`（Run41:101）/ `chainPos_matched`。
その唯一の側入力が `ConsumeAvail` で、
**全状態への量化版は偽**（n83、`ConsumeAvailRefute.hav_false`）だが
`CloseoutWatchSupply.chainPos_step_of_supply` が 4 つの局所供給事実に分解し、
`CloseoutVerSide.VerRun`（**run 形**）がそれを束ねている。

### 結論: 目標は `final38`（`CloseoutFinalVer`）の 9 → 5

`pal_in_peg_final38` の 9 前提は
`hSP` `hme` `hor` `hC` `hbgP2` `hmatchP2` `hentry2` `hsdP2` `hver`。
中 4 本（Run41 版の分岐前提）は `CloseoutPackRun48` に放電器があり、
その入力は上記の chain 側台帳＋`LPackM2`/`LPackM3` の場なので、
**run 形（`VerRun` と同じ形）に直せば `hver` 1 本に合流する** → `hSP` `hme` `hor` `hC`
`hver` の **5 前提**。

`final39`（7、Run34 版）はこの合流に乗らない（`ChainPosInv'` に shift 相の場が無く、
`ChainPosInv.payload` は `ScanNR` で守られていて shift 相をまたげない ——
`CloseoutPackRun38:290` の `chainPosInv_payload_vacuous_shift` がそれを記録している）。
**だから正本は当面 `final39`（7）だが、本数を下げる作業は `final38` 側で行う。**

### 具体的な手順（次のセッションの最初の一手）

1. `LPackM3` を run に載せる。4 葉パックのうち 3 つは既にタダ:
   * `AuxPack` ← `CloseoutPackRun2.auxPack_steps`（`CentreLive` ＋ 起点の `AuxPack`）
   * `LTickLeavesN` ← **`CloseoutPackW.lticksN_of_lpackM2_W`**（`BigPack2MG7W` ＋ `LPackM2`）
   * `LTickLeaves2` ← **`CloseoutPackW.lTickLeaves2_of_shiftPalG`**（同 ＋ `hSP`）
   （`CloseoutPackRun36.lticksN_of_lpackM2_pt` は `BigPack2MG`＝`IPackMG`＋`Extra'` を
   要るので W 経路では使えない。**W 版を使うこと。**）
   残るのは `LTickLeaves3`（`backLag` ＋ `initLedger` / `shiftDoneLedger` / `replayLedger`）。
2. `CloseoutPackRun49.matchRes2_of_lpackM3` で `MatchRes2` を出す（残差 `MatchRest`）。
3. `MatchRest.repV` / `repVmid` は `VerRun` の中身と同一なので `hver` に合流させる。
   `replayPay` / `canRNext` は `PosPayload2` と右ヘッド供給なので `LPackM2` から出るか確認。
4. Run48 の 4 放電器の入力を run 形に書き換える（**現状の「任意の scan 状態 ＋
   `ChainPosInv2`」形の `hrepV` は偽の疑いが強い**。`ChainPosInv2` は verifier の
   内容を縛らない）。
5. `CloseoutFinalVer.pal_in_peg_final38` の中 4 本を放電して `final41`（5 前提）を張る。

### 併せて記録した警告

`CloseoutBranchRes.shiftLocalS_of_run_res` はまだ `hfour` を取る（n83 より前の版）。
`hfour` は不要になったので、残差経路を使うときは
`ShiftLocalRun.shiftLocalS_of_run'` 側に載せ替えること。

## 2026-09-19 n83: `hfour` 放電 — 正本の最上位は 7 前提（`pal_in_peg_final39`）

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### 結果

| 定理 | 前提数 | 偽の前提 |
|---|---|---|
| **`CloseoutFinalFour.pal_in_peg_final39`（新・正本）** | **7** | **なし** |
| `CloseoutFinalW.pal_in_peg_final30`（一代前） | 8 | なし |
| `CloseoutFinalVer.pal_in_peg_final38`（新・別系統） | 9 | なし |
| `CloseoutFinalS2.pal_in_peg_final31` | 9 | **`hav`** |
| `CloseoutFinalW3.pal_in_peg_final36` | 5 | **`hpack`** |
| `CloseoutFinalW4.pal_in_peg_final37` | 4 | **`hpack`** |

`final39` の 7 前提（`#check` で型を実見して確認、余計な隠れ前提なし）:
`hSP` `hme` `hor` `hC` `hbgP` `hmatchP` `hsdP`。`final30` から `hfour` だけが消えた形。

### `hfour` はなぜ消えたか — 何も足していない

`CloseoutPackRun40.ChainPosInv'` は `CloseoutPackRun34.ChainPosInv` の `coupled` 場を
`Coupled`（`Other`、2h）から `Coupled'`（`Other'`、5h ＋ 正半周期）に強めただけの構造。

* `watchShiftS_of_chainPosInv'`（`Run40:407`）は `H_fourOther` を**取らない**。
  `Other'` は `Coupled'.watch` の場から `compare'_inv` 経由で出てくるので
  `four_of_other'`（`Run40:368`）が直接効く。
* `chainPosInv'_tick`（`Run40:435`）が要求する分岐前提は `H_bgP` / `H_matchP` /
  `H_shiftDoneP` の **3 本だけで `final30` と同一**。
* boot は `coupled'_of_idle`（`Run40:87`）で無条件。

新規 `PalPeg/ShiftLocalRun.lean` がこれを run に載せる（`chainPosInv'_of_idle`、
`chainPosInv'_steps`、`shiftLocalS_of_chainPosInv'`、`shiftLocalS_of_run'`、
`needIMW'_le_W'`）。

### 偽の前提の発見（`hav`、過剰量化の 8 例目）

`final31` は `hfour` を落とすかわりに

```
(hav : ∀ (w : List (Fin 2)) (st : ℕ → State GalilVM) (i : ℕ), ConsumeAvail (st i).vm.chain)
```

を取っていた。`st` は**無制約な関数**なので `∀ z : ChainVM, ConsumeAvail z` と同値。
`ConsumeAvail z := ∀ wch, z = .watch wch → canRight (right wch.machine.verifier)` で、
`right p` は gap を反転するから、`gap = false` かつ右も incoming も空な verifier では
`canRight (right p) = (true = false) ∨ ([] ≠ []) ∨ ([] ≠ [])` が偽。
証人は既存の `GalilWatchOkInst.bornVer`。反証は `PalPeg.ConsumeAvailRefute.hav_false`
（標準公理のみ、`sorryAx` なし）。**`final31` は無価値。**

`bornVer_can : canRight bornVer` は成り立つ（`gap = false` なので第 1 選言）。
偽になるのは**一歩進めた後**の `canRight (right bornVer)` である。

### コピペの括り出し（コウタの指示どおり、計測から始めない）

* `RadPack` → `TrailF` → `needL'` の 3 段は **4 回**書かれていた
  （S＝`CloseoutShiftS`、S3＝`CloseoutWatchSupply`、S4＝`CloseoutVerSide`、＋今回）。
  本体は `hsh : ∀ i ≤ Tc w.length, ShiftLocalS … (st i)` しか使っていないので、
  `ShiftLocalRun.radPack_pt_of_shiftLocal` / `trailF_pt_of_shiftLocal` /
  `needIMW'_le_of_shiftLocal` として **1 度だけ**書いた。
* `pal_in_peg_final5MW` / `5MW2` / `5MW3` / `5MW4` は `needL'` の上界を作る 1 行を除いて
  **同一の 45 行**。`CloseoutFinalFour.pal_in_peg_of_needLe` がその 45 行で、上界自体を
  `hneed` として取る。以後の版は 4 行の instantiation。
  **既存 4 版の載せ替えは未実施**（別コミットにする。今やると 600 モジュールの再ビルドと
  同時に 4 ファイルを触ることになる）。

### `final38`（9 前提）を残す理由

前提数では `final39` に劣るが、分岐前提が Run41 系（`H_bgP2` / `H_matchP2` /
`H_shiftEntry2` / `H_shiftDoneRad2`）で、`CloseoutPackRun48` の 4 放電器
（`h_bgP2_of_supply` / `h_matchP2_of_target` / `h_shiftEntry2_of_target` /
`h_shiftDoneRad2_of_supply`）が効く**唯一の**経路。`final39` の 3 本を落とすには
こちらを詰める。`hpack` は `CloseoutVerSide` が run 形の `VerRun` に置き換えてあり、
`CloseoutFinalW5.pal_in_peg_final5MW4` がそれを受けていたが**最上位が張られていなかった**
（それを張ったのが `CloseoutFinalVer`）。

### 次の一手

Run48 の 4 放電器の入力はまだ「任意の scan 状態 ＋ `ChainPosInv2`」形で、
`hrepV`（verifier が入力を表現）はその形では**偽の疑いが強い**（`ChainPosInv2` は
verifier の内容を縛らない）。`VerRun` と同じ **run 形**に直してから使う。
それができれば `final38` の 4 分岐前提が `hver` 1 本に落ち、
`hSP` `hme` `hor` `hC` `hver` の **5 前提**になる。

### 教訓

* 「`hfour` が壁」と 1 日以上数えていたが、証明は `CloseoutPackRun40` にあり、
  `CloseoutPackRun41:213` の docstring が「so `H_fourOther` is a theorem」と書いていた。
  **地図が無いと既存の部品を取り落とす**（`Canonical.lean` / `Workbench.lean` に登録済み）。
* `hfour` を落とした既存の 3 版はどれも偽の前提を代わりに取っていた。
  **前提数だけ比べてはならない。型を見て、各前提に反証が無いかを確かめる。**

## 2026-09-19 n82: `hfour` は既存の部品で消える — `four_of_other'` が `H_fourOther` そのもの

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`final30` の 8 前提の 1 つ `hfour : ∀ w, H_fourOther centreC placeC entry q first w` を
実際に追ったら、**既に証明済みの定理があった**。

### 在り処

* `PalPeg/CloseoutPackRun40.lean:368` — `four_of_other'`
  ```
  theorem four_of_other' (hx : Coupled' x.ctl x.vm) (hs : ScanNR x)
      (hcmp : compare x.vm s'') (hmt : ¬ matched s'') (hg : shiftGuardVM s'')
      (hch : s''.chain = .watch wch)
      (hO : Other' x.vm.periodOnly x.ctl.mode (value x.vm.radius) (value x.vm.cycle)
        (value x.vm.remaining) (periodLength wch)) :
      4 * (periodLength wch : ℤ) ≤ value wch.machine.control.distance
  ```
  これは `H_fourOther`（`CloseoutPackRun34:342`）の結論そのもの。

* 違いは結合の強さだけ:
  - `Other`（`GalilChainCoupling:353`）= `po ∧ (shift → 2h ≤ R+C+Rem) ∧ (¬shift → 2h ≤ R+C)`
  - **`Other'`**（`CloseoutPackRun40:56`）= `po ∧ 1 ≤ h ∧ (shift → 5h ≤ R+C+Rem) ∧ (¬shift → 5h ≤ R+C)`

  議論（docstring より）: `5h ≤ R + C`、`C ≤ 1`（shift guard の `singlePositive cycle` から
  `value_le_one_of_single`）、`distance = R`（`SumRel` ＋ lag ゼロ）、`1 ≤ h` で `4h ≤ distance`。
  `other_of_other'` で `Other' → Other` も既にある。

* **`ChainPosInv2` は既に `Coupled'` を含む。** `PalPeg/CloseoutPackRun41.lean:213` の
  docstring が明記している: 「`ChainPosInv2`: `Coupled'`（Run40、**so `H_fourOther` is a
  theorem**）」。

* `Coupled'` は run を運ばれる: `coupled'_of_idle`（`Run40:87`）で boot、
  `coupled'_tick`（`Run40:149`）で tick 保存、`coupled'_toCoupled`（`Run40:84`）で弱化。

### 次の一手（即実行できる）

`final30` の `hfour` を落とす。`hfour` の消費者は `CloseoutPackRun34.watchShiftS_of_chainPosInv`
で、そこは既に `ChainPosInv` を取っている。`ChainPosInv2`（`Coupled'` を含む）版に載せ替えれば
`four_of_other'` がそのまま効き、`hfour` は消える。**8 → 7。**

注意: `ChainPosInv2` からの `ChainPack` は**偽**（`CloseoutPackRefute.hpack_false`）なので、
`ChainPosInv2` を使うこと自体は問題ないが、そこから `ChainPack` を取る経路には乗らない。
必要なのは `Coupled'` の場だけ。

### 教訓（コウタの指摘どおり）

「最上位の 8 前提も既存の部品で書けるかもしれんやろ」「そこを疑えよ」。実際そうだった。
`hfour` は 1 日以上「壁」として数えられていたが、証明は `CloseoutPackRun40` にあり、
しかも `CloseoutPackRun41` の docstring が「so `H_fourOther` is a theorem」と書いていた。
**地図（`PalPeg/Canonical.lean` / `Workbench.lean`）に残り 7 前提の在り処も入れること。**

## 2026-09-19 n81: `M-watchBreak` 修正を 35 ファイルまで進めて revert — 義務の形を過剰量化で書き間違えた

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

### やったこと

`ChainStep.watchBreak`（正 lag の背景 break）と `ChainMatched.brokenMatched` を入れて
Scala 正本 `ScaffoldChain.step()` / `matched()` に忠実にし、構成子分岐を 35 ファイル分
修理した。その過程で得られたもの：

* `chainStep_watch_total_of_symbol` — **`Good` を仮定しない後続状態の存在**。
  必要なのは「verifier が右に動ける」と「period の焦点が記号を持つ」だけ。
  これが `ChainTickable` / `hready` の解錠にあたる。
* `internal_breakStepPos_false`（`Internal` と `BreakStepPos` は排他）、
  `breakStepPos_unique`（break の行き先は一点）。
* 修正で**真に偽になった**もの: `broken_stays`（`brokenMatched` でカウンタが動く）、
  `CloseoutTickFalse.step_ne_broken`、`WatchClosedC`、`distance_mono_false`。
  いずれも「watch または broken」の選言へ弱めるのが正しい形。
* lag 台帳 `LagLe`（`position verifier + lag ≤ r`）は背景 break で**ちょうど 1 だけ破れる**
  （Scala の `consume()` は `verifier.right()` を済ませてから `mode = Broken` にし
  `lag.dec()` を飛ばす）。`NoBgBreak` として義務化した。

### なぜ revert したか（自分の誤り）

ラウンド系の下流に撒いた義務を

```
(hnobg : ∀ (w' : GalilScaffoldChainWatch.State) v, ¬ BreakStepPos w' v)
```

と書いた。**`w'` を任意に量化している。** `BreakStepPos` は「正 lag ＋ 不一致」なので
そういう `w'` は確実に存在し、**この前提は偽**。付けた定理は全部空虚になる。
`CLAUDE.md` に自分で書いた過剰量化の欠陥の 7 例目。偽の前提を撒いたまま進めるのが
最悪なので緑に戻した。`GalilTrailAssembly` の `NoBgBreak (st i).vm.chain`（状態局所）が
正しい形で、ラウンド系も同じく状態局所にしなければならない。

実作業は `bb11acb` に履歴として残っているので、そこから再開できる（revert は `616c6e5`）。

### 8 前提の見立て

| 前提 | 状態 |
|---|---|
| `hSP` | **`M-watchBreak` 修正で通る見込みが高い**（`chainStep_watch_total_of_symbol` が既にある） |
| `hC`（局所実現） | 最大の未知。`TextFeed*` 153 ＋ `Prog*` 119 本が閉包外。`CloseoutRealize1` は証人が付随的と示すので層自体が不要な可能性もある。**未判定** |
| `hor`（oracle） | 葉 11 本、found 経路が未着手 |
| `hme` | 残差 `WindowInOrigin` 1 本 |
| 4 供給（`hfour` `hbgP` `hmatchP` `hsdP`） | `*Res` 残差 4 本に落ちるが producer が無い |

8 → 7 は `M-watchBreak` 修正（構成子分岐 48 箇所 ＋ 状態局所の threading）で見えている。
その先の `hor` の found 経路と `hC` が本体。

### 構造的な推奨: Scala を functional に直して Lean へ関数として写す

**モデル欠陥が 2 日で 2 件出た**（`M-periodOnly`、`M-watchBreak`）。どちらも
「Scala は全域関数、Lean は帰納的関係」という非対称から来ている。
**関係は場合を落とせるが全域関数は落とせない。**

`ScaffoldChain.step` / `consume` / `matched` を純関数として書き直し（Scala 側の
functional 化は許可済み）、Lean 側もそこから関数として写して、遷移関係はその関数から
導く形にすれば、この種の欠陥が構造的に起きなくなる。今の地図と欠陥 2 件を見た上で、
**これが最も効く一手**。

## 2026-09-19 n80: モデル欠陥 `M-watchBreak` を特定・機械検査 — `WatchOk` が偽である根本原因

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

`WatchOk` の反証（n79）の原因を Scala 正本と突き合わせて掘った結果、**モデル欠陥**だった。

### Scala 正本（`scala/pal/src/main/scala/pal/ScaffoldChain.scala:136,178`）

```scala
def step(answer: TapeView): Unit = {                    // 背景の 1 量子
  mode match {
    case Mode.Copy  => stepCopy(answer)
    case Mode.Back  => stepBack()
    case Mode.Watch if lag.sign > 0 => if (consume()) { lag.dec() }   // ← ここ
    case Mode.Idle | Mode.Watch | Mode.Broken => ()
  }
}
private def consume(): Boolean = {
  verifier.right()
  val token = period.read()
  if (!verifier.read().contains(token.takeRight(1))) { mode = Mode.Broken; false }
  else { distance.inc(); …; period.move(direction); true }
}
def matched(): Unit = {                                 // 新しい place が合流
  margin.inc(); if (periodOnly) cycle.dec()
  if (mode == Mode.Watch && lag.sign == 0) consume() else lag.inc()
}
```

`consume()` は **`step()`（正 lag）と `matched()`（lag ゼロ）の両方から呼ばれ、
どちらでも不一致なら `Mode.Broken` に落ちる。**

### Lean 側の欠落

`ChainStep` には `.watch → .broken` の構成子が無い（`watchStep` は `Internal w w'` を
取り、`Internal` は `.idle`（lag ゼロ）と `.take`（正 lag ＋ `Good`）の 2 つだけ）。
break は `ChainMatched.breaks` にあるが、その `BreakStep` は **`zero w.lag = true`** を
要求するので **lag ゼロ経路のみ**。つまり `step()` 経路（正 lag）の break が欠けている。

機械検査済み（`PalPeg/ChainStepGap.lean`、標準公理のみ・`sorryAx` なし）：

* `no_chainStep_at_positive_lag_mismatch (hp : positive w.lag = true)
  (hng : ¬ Good w) : ¬ ∃ z, ChainStep (.watch w) z`
* `no_chainTick_false_at_positive_lag_mismatch` — 背景量子（`a = false`）でも同じ

**現行モデルでは、正 lag で period と入力が食い違う watch に後続状態が存在しない。**
Scala ではそこで `Broken` に落ちる。

### これが `WatchOk` が偽である理由

`ChainStep` が break できないので、正 lag での背景遷移は `Internal.take` しかなく、
それは `Good` を要求する。だから `WatchOk.good` は「正 lag では period と入力が常に
一致する」と主張することになる。それは Galil の chain の設計（**予測が外れたら壊れる**。
周期区間の終端検出はまさにその break で行う）に正面から反する。**`WatchOk` は偶然
偽なのではなく、モデルの欠落を埋めるために書かれた偽の仮定だった。**

### 直し方と影響範囲

```
| watchBreak (w w') (hb : BreakStepPos w w') : ChainStep (.watch w) (.broken w')

def BreakStepPos (w w') : Prop :=
  positive w.lag = true ∧ canRight w.machine.verifier ∧
  ∃ a, symbol w.machine.control.period.focus = some a ∧
    read (right w.machine.verifier) ≠ some a ∧
    w' = ⟨consume w.machine, w.lag, w.margin⟩
```

`step()` は break 時に `lag.dec()` も `margin.inc()` もしない（`if (consume()) { lag.dec() }`、
`margin.inc()` は `matched()` 側）ので lag と margin は据え置き。

影響範囲: `ChainStep`/`ChainMatched` の構成子で分岐する箇所は **202**。`M-periodOnly`
修正（300 超）と同規模の機械的作業。これを入れれば `ChainTickable` の正直な形
（ready **または** broken）が `WatchOk` なしで証明できるようになり、`hSP` の
唯一の残り障害 `hready` が消える見込み。

### 付随して分かったこと

`WatchOk` を仮定する定理は全部空虚になった: `GalilChainTickable` の全定理、
`GalilReplayGeneral` の 7 本、`GalilOneFallback`、`CloseoutTickFalse.chainOk_tick_false`。
`WatchOk` に言及するファイルは 24。

## 2026-09-19 n79: `WatchOk` を無条件で反証 — `hSP` の壁の正体が確定した

**全体 build 成功（EXIT=0・エラー 0・sorryAx 0）・標準公理のみ・無条件 PAL は未完。
計画書 §10.5（前提ゼロ）は未達。**

再編でできた地図を使って `hSP` の唯一の残り障害 `hready : ChainTickable` に当たった。
まず**インスタンスを構成しようとして** `WatchOk.born` で詰まり、障害が偽の形だったので
反証に回った（`PalPeg/WatchOkRefute.lean`）。

### 反証

`watchOk_false {Ok} (hOk : WatchOk Ok) : False` — 引数は反証対象のみ、公理は
`propext`/`Quot.sound`、`sorryAx` なし。`no_watchOk : ¬ ∃ Ok, WatchOk Ok`。

論法: `born` は **lag と margin を任意に量化して** `Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩`
を与える。`good` は正の lag で `Good` を要求し、`Good` は period テープの焦点記号と
入力右ヘッドの記号の**一致**を要求する。`born` の仮説（`canRight ver`、`OnBlock v`）は
その 2 つを一切関係づけないので、lag を正に取って不一致な証人を入れれば矛盾する。

証人はカーネル計算で確定（`#eval`。自分のコード読みは信用しない）:
`symbol (GalilScaffoldChainPeriod.moveRight bornBlock).focus = some 0`、
`read (right bornVer) = some 2`、`positive ⟨[0],[]⟩ = true`。

既存の `GalilWatchOkInst.no_watchOk_instance` は `WatchOk` に**加えて**無条件の
`∀ w, Ok w → Good w` を仮定した組を否定するもの（`born` を `lag = reset` で使う）。
本件は lag を正に取って `WatchOk.good` だけを使い、**`WatchOk` 単体**を否定する。

### 原因は `ChainOk` の設計（過剰量化の 6 例目）

```
def ChainOk (Ok : WState → Prop) : ChainVM → Prop
  | .back v _ _ _ ver => OnBlock v ∧ canRight ver      -- lag/margin を無視
```

`ChainStep.backDone` は `.back v h lag margin ver` から
`.watch ⟨⟨ver, watchControl v⟩, lag, margin⟩` へ遷移して lag/margin を継承する。
`ChainOk` が `.back` の lag/margin を無視する限り、`ChainStep` での閉性には
**任意 lag/margin での `Ok`** が要る。それが `born` であり、それが `good` と衝突する。

**これは「名前付き葉が偽になるのは、唯一の消費者が到達しない状態まで量化しているとき」
という同じ欠陥の 6 例目。** 実機で生まれた watch の lag/margin は `.copy` 相が積んだ値で
あって任意ではない。

### 次

`hready` を消すには `ChainOk` を再設計する:

```
| .copy t h p v lag margin ver => (∃ n, CopyInv t h p v n) ∧ canRight ver ∧ <誕生義務>
| .back v h lag margin ver     => OnBlock v ∧ canRight ver ∧ Ok ⟨⟨ver, watchControl v⟩, lag, margin⟩
```

`.back` に誕生義務を場として持たせれば `backDone` は自由になり、`born` は `WatchOk` の場から
消える。新たに必要になるのは `copyBit`（`margin ↦ decFour margin`、`v ↦ put v a`）と
`copyEnd`（`v ↦ write v (.last b)`）での義務の保存。`Good` の供給元は
`CloseoutWatchRound53.good_of_pos`（`ChainW` から `Good`）。

## 2026-09-19 n78: 証明をコードとして再編 — 根を 3 本に、`PackedRun` を括り出し

**全体 build 成功・標準公理のみ・無条件 PAL は未完。計画書 §10.5（前提ゼロ）は未達。**

コウタの指摘「コードベース全体把握してないのに断言するのやめろ」「ちゃんとメンテ可能な形に
再編してから物を言え」「このファイルやモジュールにはこの証明があるという頭の地図が作れないと
いくらやっても足踏みになる」を受けて、断定をやめて再編した。**証明は 1 行も意味を変えていない。**

### 実測（推測でなく機械で取った）

| 指標 | 値 |
|---|---|
| モジュール | 1143 |
| 行 | 331,884 |
| `theorem`/`lemma` | 12,613（`def` 4,246 / `structure` 393 / `inductive` 218） |
| 正本 `final30` の推移 import 閉包 | **526** |
| 閉包の外 | 617（うち登録済み 583） |
| 本体が完全一致する証明 | 162 群・419 定理・余剰 **2,483 行**（全体の 0.75%） |
| 誰も import せず名前も参照されないモジュール | 28（5,635 行・158 定理） |

層ごとの閉包との関係: `TextFeed*` は **153 本すべて閉包外**、`Prog*` は 119 本が閉包外
（閉包内の 6 本は `Galil*Program*` 系で別物）、`GS*` 13 本・`*Tapes` 15 本も閉包外。

### 再編（根を 3 本に）

`PalPeg.lean` は 1101 本の import を並べていた。これを 3 本にした。

* `PalPeg.Canonical` — 正本の鎖（閉包 526 本）＋意味のある別名 24 本。
  `lake build PalPeg.Canonical` で正本だけを速くビルドできる。
* `PalPeg.Workbench` — 作ったが未配線の 64 本の根（閉包 583 本）。
  **主定理との関係を層ごとに明記**。
* `PalPeg.Axioms` — 公理監査。

新根の閉包 1135 ⊇ 旧登録 1101、**欠落 0**（機械照合済み）。落としていない。

### 括り出し（`PalPeg/PackedRun.lean` 新規、σ 一般・最下層）

`StepsI` / `StepsIM` / `StepsIMW` / `StepsIMG` / `StepsIMG2` / `StepsIO` は
**文字通り同一の定義**を pack 述語だけ差し替えて 6 回書いたもので、`*_trans` は
6 本とも同じ 8 行、`*_of_*`（pack 弱化）は 3 本とも同じ 5 行だった。

`PackedRun F delay Q Pk k x y := ∃ g, g 0 = x ∧ g k = y ∧ Trace F delay Q g k ∧
∀ i ≤ k, Pk (g i)` を `GalilCheckpoints` だけに依存する σ 一般の部品として定義し、
`PackedRun.trans`（連結）/ `PackedRun.mono`（pack の弱化）/ `PackedRun.pack_at` の 3 本に括った。
`pack_concat`（`CloseoutLPack5`、`GalilVM` 固定・上の層）の 6 行はここに取り込んだ。

6 つの `Steps*` は定義を `PackedRun … pack …` に書き換え（4 行 → 2 行）、
`*_trans` 6 本は `PackedRun.trans h1 h2` の 1 行に、`*_of_*` 3 本は `PackedRun.mono` に委譲。
**文は 1 文字も変えていない。** 以後 pack の変種を作るときは `*_trans` を書き直さない。

### 削除

`PalPeg/Probe1.lean` 1 本のみ（`attribute [ext]` と `#check` と自明な `example` だけ、
定理 0、未登録、主定理と無関係）。**デッドコードかどうかは主定理との関係でしか判定できない**
ので、参照ゼロの 28 本のうち残り 27 本は関係を読んで全部残した。特に
`CloseoutClockFront`（`canRight_of_run` / `extra7_of_run`）と
`CloseoutWatchRound53`（`good_of_pos` ＝ `WatchOk.good` の内容）は**今の壁に直接効きそう**で、
未参照のまま転がっていた。

### 撤回した断定

「正本は `final30`（8 前提）で、8 が正直な床」と書いたが、確認したのは `final30` `final31`
`final33` `final36` `final37` の 5 本だけで、47 本を数えていない。`final32` `final34`
`final35` は grep が空振りしたのに理由を調べていない。**この断定は撤回する。**
前提の数は Prop 引数の本数では測れない（`∀ w, H_x w` は 1 本に見えて族、instance は自動放電）。
数えるべきは「producer が無い前提」であり、それは型を見て初めて決まる。

編集の規律は `CLAUDE.md` の「証明はコードである — lean-pal 編集の規律」に書いた。

## n81 (2026-09-19) `ShiftAtMismatchM` を**証明した** — Round 30 の piece 1〜4 が閉じた

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`roundOne_of_segRun_M`（`Rounds … 1` の構成器）の唯一の残差 `ShiftAtMismatchM` を、
**運ばれる不変量だけから証明した**（`CloseoutMismatchCompare.shiftAtMismatchM_of_round`）。

`CloseoutWatchRound30` が「piece 1」と呼んで NAMED leaf にしていた事実——不一致比較の
無効 chain tick が watch を保つ——も定理になった。**ラウンド終端では lag がゼロ**
（`RoundScan.caught.lagZero`）なので、`Internal.idle` ＋ `ChainStep.watchStep` ＋
`ChainTick false` = step で恒等になる。

`CloseoutMismatchCompare.lean`（新規、8 定理）: `chainTick_false_idle`、
`compare_mismatch_of_lagZero`（**不一致比較を構成**）、`compare_mismatch_of_round`、
`chainStep_watch_of_lagZero`、`compare_chain_of_mismatch`（与えられた比較の双対）、
`copyIdle_congr`、`beginShift_of_guard`、**`shiftAtMismatchM_of_round`**。

前提は全部運ばれる不変量: 終端の `RoundScan` ＋ 周期の紐付け、`used + 1 = 2h`、
`Canonical s1.length`（`CPack.canon`）、`CopyIdle s1`（`AuxPack.copyP`）、
中心不変量 ＋ `CentreRep`。

**Round 30 の 6 部品のうち 1〜4 が PROVED。** 残りは piece 5（origin 台帳）と
piece 6（`Rounds … mm` と終端 `ScanSeg`）。次は `roundOne_of_segRun_M` の残る入力
（`ChainTickable` / `WatchClosedC` / `RoundDataC`）の現状を測る。

## n80 (2026-09-19) **正直な最上位は `final30`（8 前提・反証済みゼロ）** — `final37` の 4 は偽を 1 つ含む

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`hpack` が偽と分かったあと用途を追跡して判明した：**`pal_in_peg_final30`（`CloseoutFinalW`）
は `hpack` を必要としない。** 8 前提 `hSP` `hme` `hor` `hC` `hfour` `hbgP` `hmatchP` `hsdP` で、
自身の docstring が「eight hypotheses, none refuted」と書いている。`#print axioms` は標準 3
公理のみ（本ターン再確認）。`final37` が 8 → 4 に減らした経路（`final5MW3` の `hpk`）は
**偽の前提を通っていた**。したがって**正直な最良状態は `final30` の 8 前提**で、
`final37` の 4 前提は「4 つの証明可能な前提」ではない。

### `final5MW3` 経路の修理（捨てずに直した）

`CloseoutVerSide.lean`: `shiftLocalS_of_chainPack` が読む 4 場（`inv`/`repR`/`repV`/`lagCan`）
に分解し（`shiftLocalS_of_parts`）、`repR` は run 自身の `LPackM2`（pre-trace の pack）から
出るので、`hpack` の寄与は `repV` ＋ `lagCan` だけと確定。それを **run 形**で名付けたのが
`VerRun`（`chainPosInv2_of_idle` では反証できない）。`shiftLocalS_of_verRun` /
`radPack_ptS4` / `trailF_ptS4` / `needIMW'_le_W4` / `verRun_of_hpack`。

`CloseoutFinalW5.lean`: **`pal_in_peg_final5MW4`** = `final5MW3` の `hpk` を
`hver : ∀ w st, st 0 = boot w → VerRun … w (st 0)` に置換。標準公理のみで通る。

ただし `final37` の他の `hpack` 用途（4 供給の導出と `packRunR_MWP`）は `VerRun` では
覆えない。それらは `final30` では前提として明示されているので、`final30` に戻るのが正しい。

### 追記（同ターン）— `hSP` を run 形に、`CopyIdle` の偽の前提も除去

`roundBundle_steps` の側入力は `∀ z : State GalilVM`（全状態）で量化されていて、
`CopyIdle` は copy 相で偽だった（`hpack` と同じ欠陥）。`hci` の使用箇所は
`shiftRound_tick` の `shift_one` 分岐 1 箇所だけで、そこには `c.mode = Mode.shift` が
scope にある。3 ファイル（`CloseoutPackRun37` / `CloseoutAdvanceT` /
`CloseoutRoundBundle`）で `hci` を `x.ctl.mode = Mode.shift → CopyIdle x.vm` に修正。

`CloseoutBundleRun.lean`（新規）: `roundBundle_of_idle`（**idle chain で束が成立**——
cycle の `InvLPC` 起点がこれ）、`roundBundle_steps_run`（側入力を run の状態に量化）、
`shiftPal_of_run`（`hSP` の内容を run から出す）。

さらに `CopyIdle` の残差は**タダ**だった: `AuxPack.copyP` が
`CopyPack c s := c.mode ≠ Mode.copy → CopyIdle s` で `shift ≠ copy`。`AuxPack` は
`auxPack_steps` で run 搬送され `packRunR_MW` が既に走らせている
（`copyIdle_shift_of_auxPack` / `shiftPal_of_run_aux`）。

さらに `ChainPosInv2` も**不要**だった。`roundBundle_tick` の `hinv` は 3 箇所とも
`blockInv_of_chainPosInv2` 経由で `BlockInv s.chain` だけを使い、それは
`Coupled.block` ＝ `AuxPack.coupled` の場。よって `roundBundle_tick_B` /
`roundBundle_steps_B` / `shiftPal_of_run_B` は `ChainPosInv2` を取らない。

**`hSP` の残差は run 形の 2 つ ＋ fresh 分岐**: `H_readsShift`（⟸ `OriginShift` ⟸
`Rounds`）、`H_freshShift`（⟸ `first_round`）、`periodOnly = false` の `ShiftPal`。
`BlockInv`/`CopyIdle`/`canRight` は全部 `BigPack2MG7W` の場から無料。

**正直な評価**: 前提数の削減ではなく構造の直し。台帳のルールでは `OPEN` のまま。
意味があるのは 3 つとも「run データの組み立て」に帰着し、その組み立て器
（`Rounds` ← `roundOne_of_segRun_M`、`first_round`）が名前付き葉を持たない定理である点。

### これからの道筋（`final30` の 8 前提）

`hSP` は `RoundBundle` ＋ `OriginShift` ＋ `H_freshShift` に還元済み（`ShiftRun` piece 4 は
本ターン PROVED）。`hme` は `marks_steps_free` が運ぶが残差は `WindowInOrigin`（モデル欠陥 (e)、
横移動）。`hor` は 11 葉 ＋ `hsc`。`hC` は未分解。`hfour`/`hbgP`/`hmatchP`/`hsdP` は tick 補題で、
結論が tick の目標状態に束縛されるので `hpack` のようには反証できない。

## n79 (2026-09-19) **`hpack` は偽だった** — 最上位 4 前提のうち 1 つを反証

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final37` の第 4 前提
`hpack : ∀ w c s, ChainPosInv2 w c s → ChainPack q first w c s` は**成立しない**。
機械検査済み（`PalPeg/CloseoutPackRefute.lean`）。

`ChainPosInv2` の場は 3 つだけ（`Coupled'`、非 idle chain の payload、shift 台帳）で、
`chainPosInv2_of_idle` は chain が idle なら**任意の `w` `c` `s`** に対してそれを与える。
ところが `ChainPack` は run の事実を主張する：

- `scanBound : c.mode = .scan → ∃ m, 1 ≤ m ∧ m < w.length ∧ position s.right ≤ 2m−1`
  は `w.length ≤ 1` で**充足不能**（PAL は 1 文字語を含み、run の開始点は
  `Tick.init` の着地＝scan モード・idle chain）
- `centreCanR : canRight s.center` は**モード前提なし**で、中心頭が入力末尾に達した
  状態（走査完了時）で偽

反証: `hpack_false_at_short_word` / `chainPack_false_at_short_word` /
`hpack_false_at_exhausted_centre`。

**原因（2 層）**: 直接原因は `ChainPack` が「run に沿って確立される事実の束」を
一状態述語として書き、前提を一状態不変量にしていること（`ChainPack` 自身の docstring が
「established **along the run**」と書いている）。その原因は、以前このセッション系列で
別葉だった `ScanBudget`（`CloseoutFinalPack` の `hbudget`）を束のフィールド `scanBound` に
**畳み込んだ**こと。台帳の自分のルール「未解消の前提を構造体フィールドへ移しただけなら
OPEN のまま」に照らせば前進ゼロで、しかも `ScanBudget` 自体が既に同じ反例で偽だった。

**直し方（論証）**: `ScanBudget` の唯一の用途は `matchRes2_of_chainPack` で
`canRight_of_position_bound` により `canRight s.right` を得ることだけ。必要なのは
チェックポイント `m` ではなく `canRight`。そして `canRight` も一状態の事実ではない。
よって正しい形は束を `Steps` に沿って運ぶこと——`CloseoutRoundBundle.RoundBundle`
（`roundBundle_tick` / `roundBundle_steps`）と同じ構成。boot 状態では全ヘッドが入力原点に
あるので `canRight` は全部成立し、各 tick はヘッドを保つか 1 進めるだけ。

### 追記（同ターン）— 修理の第 1 段

`CloseoutBudgetFree.lean`: `scanBudget_of_front_run`（偽だった `scanBound` の**本物の
producer**。`position_le_of_front_run` が cycle の出口上界を run に沿って遡らせる。
`Extra7` から `hee`/`het` を消したのと同じ機構）、`avail2_of_front_run`、
`ChainSideW`（修理された前提の形）、`chainSideW_of_hpack`。

`CloseoutChainSideR.lean`: `ChainSideR` = `ChainSide` − `scanBound`、
`chainSide_of_chainSideR`、`chainPack_of_chainSideR`、`chainSideR_of_chainSide`。

**正直な評価**: 実証された矛盾（`w.length ≤ 1` での `scanBound`）は消えたが、
`ChainSideR` は依然 run の事実を 3 場の前提の下で主張するので真にはなっていない。
「矛盾している」→「導出できない」に変わっただけ。前提を run 搬送パック
（`BigPack2MG7W''`）に変えるのが本筋で、各場の供給元は台帳に対応表で記録した。
残差は `walkerPin`/`walkerOrigin`（モデル欠陥 (e)）。

**最上位の正直な状態**: `pal_in_peg_final37` の型は正しく `#check` は 4 引数、
`#print axioms` は標準 3 公理。しかし 4 前提のうち `hpack` は**偽**なので、これは
「4 つの証明可能な前提」ではない。計画書 §10.5（前提ゼロ）は未達であり、この経路では
到達できない。`hpack` を run 沿いの束に置き換えるのが次の主要作業。

## n78 (2026-09-19) `H_readsShift` は「shift 完了時の read origin」に還元 — `hSP` の残差が 2 つとも同じ通貨に

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

最上位は `pal_in_peg_final37`（`CloseoutFinalW4`）の **4 前提**（`hSP` `hor` `hC` `hpack`）のまま。
`#check` で 4 引数、`#print axioms` は `[propext, Classical.choice, Quot.sound]` を再確認。
計画書 §10.5（前提ゼロ）は**未達**。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### 先に立てた論証

`H_readsShift` の消費点は `readsRound_tick` の `Tick.shift_done` **1 箇所のみ**。
そこに何が足りないかを 3 方向から測った：(1) `ReadsInv` は等式なので `chainShiftOne` の
カウンタ減算で壊れ運べない、(2) `SweptOff` は `Offset` なので shift を生き延びるが
bounce→`encoded` の辞書が 1 周期対しか遡れず累積継続を変換できない（その変換が
`rounds_origin` の帰納法そのもの）、(3) `good_of_periodOn` も入力が `Entry` で同じ壁。
残るのは一つ、**ラウンド開始の read origin**。

### やったこと（`PalPeg/CloseoutReadsOrigin.lean` 新規、7 定理）

`readsRun_of_originAt`（`OriginAt → ReadsRun`：`round_of_originAt` が `used = 0` の
`RoundScan` ＋ `ReadsInv` を返し、`roundScan_unique` が任意の `RoundScan` の `used` を
`0` に強制する）、`readsRound_of_originAt`、`h_readsShift_of_originAt`、
`h_readsBirth_of_originAt`、`roundBundle_tick_O`（束の tick の葉を `OriginShift` に置換）、
`originShift_of_roundSeg`。

`H_readsShift` は `positive s.remaining = false`（shift 完了）を前提に追加して再定式化
（`CloseoutRoundUnique`、呼び出し側 1 箇所修正）。shift 途中の chain は部分 shift 済みの
watch で `Entry` を満たさないので、この前提なしでは偽になる。

### 状態

`H_readsShift` は **REFORMULATED**（供給未完なので OPEN のまま）。新 NAMED `OriginShift` は
`originAt_of_rounds`（証明済み）が controller `Rounds` から供給し、その `Rounds` は
`CloseoutWatchRound9` が無条件に構成する。つまり `hSP` の残差 2 つ
（`OriginShift` と `H_freshShift`）は**どちらも「run の断片を `ReadOrigin` に組み上げる」
同じ通貨**で、`hor` の found 経路系（`CloseoutWatchRound5.ShiftRoundC`）と同一。

### 追記（同ターン）

`h_readsShift_of_rounds`: controller `Rounds` ＋ 第 1 ラウンドの `Entry` から
`H_readsShift` が 1 行で出る。基底の `first_round` は名前付き葉を持たない定理、
`Rounds` は `roundOne_of_segRun` が構成（残差は `ShiftAtMismatchC` のみ）。
**負の結果**: `H_freshShift` は `OriginAt` からは出ない — `OriginAt` は `used = 0`
（`value s.cycle = 2h`）を固定するので `shiftInv_entry` が要る
`singlePositive s.cycle = true` と両立せず、fresh chain の初回 shift は
`used = 2h − 1` で起きる。`H_freshShift` は `first_round` 自身の義務。

### 追記 2（同ターン）— `ShiftAtMismatchC` を反証して再定式化

`roundOne_of_segRun` の唯一の残差 `ShiftAtMismatchC` は**過剰主張**だった。`SegEndS` の
第 3 出口は「cycle 終端 ∨ 不一致」の選言で、消費者は不一致側で cycle 終端を知らんのに、
葉の結論が `singlePositive s1.cycle = true` を主張していた。Scala 正本
（`ScaffoldGalil.scala:254`）では `canShift` が `if periodOnly then singlePositive cycle`
を含むので、**周期中の**不一致では機械は shift せず `beginFallback()` に行く。

`CloseoutShiftMismatch.lean`（新規）: `shiftAtMismatchC_false_at_nonterminal`（反証、
非終端 `RoundScan` の `terminal_iff` に接地）、`ShiftAtMismatchN`（cycle 終端を前提へ）、
`shiftAtMismatchN_of_C`、`roundOne_of_segRun_N`（終端出口が 2 種を区別し、新しい場合は
機械の `beginFallback`＝oracle の `hmismatch` 分岐）。既存の `roundOne_of_segRun` は
壊していない。

**同一の欠陥が 5 例目**（`ShiftPal` / `H_advanceT` / `MatchTickC` / `hpos` /
`ShiftAtMismatchC`）。新しい葉を測るときは、まず**消費者がその分岐で何を知っているか**
を先に読む。

### 追記 3（同ターン）— 自己訂正: `ShiftAtMismatchN` もまだ過剰主張だった

`N` の結論には予測一致 `read (right s1.right) = symbol w.machine.control.period.focus`
が残っていて、終端 `RoundScan` ではこれは入力依存の等式
`(encoded raw)[C+R+1]? = (encoded raw)[C+R+2h+1]?` に等しい（破れたら `beginFallback()`）。
`CloseoutWatchRound30.ShiftRoundAtC'` が既に正しい形（guard をトリガーとして前提に取る）
を持っていたので、それに合わせた。

`ShiftTrigger`（機械の `beginChainShift` 条件）、`ShiftAtMismatchM`（入力依存の 2 事実を
前提に移し、葉は機械的部品だけ）、`roundOne_of_segRun_M`（終端出口を 3 分割: break /
shift / fallback）。全部標準公理のみ・sorryAx なし。

**次の一手**: `ShiftRun` の存在（Round 30/33 の piece 4）。`ShiftRun.next` が要求するのは
`positive s.remaining = true` の算術と 3 つの `canRight`。中心は `C → C+h`、左ヘッドは
`C−R−1 → C−R−1+2h` で、`RoundScan.size : 2h ≤ R` より両方 `[C−R, C+R]` の内側。
`ScanInvariant` の `Represents` ＋ `size` から `h` の帰納法で構成できる。

### 追記 4（同ターン）— piece 4（`ShiftRun` の存在）を構成した

`ShiftAtMismatchM` に残った唯一の非自明な部品は**入力依存ではなかった**。
右移動が塞がるのは最終 gap セルちょうど（`GalilEndOfInput.not_canRight_iff`）なので、
`ShiftRun.next` の 3 つの `canRight` は厳密な位置上界にすぎない。

`CloseoutShiftRun.lean`（新規）: `canRight_of_lt`、`right_step`、`shiftRun_exists`
（`n` の帰納法）、`shiftRun_exists_entry`（shift 入口形）。
**`ShiftRunC` / `ShiftRunCL` / piece 4 は PROVED。**

残る供給は運ばれてる状態不変量だけ: 中心頭は `CloseoutPackRun21.CentreRep`
（`InvLPC` の場）、左頭は `RoundScan.caught.scan`。位置上界は `RoundScan.rightPos` ＋
`not_canRight_iff` ＋ `size : 2h ≤ R` の算術。**次は中心頭の位置と `C` の関係**
（`RoundScan` の場にはない）。

### 追記 5（同ターン）— piece 4 をラウンドから直接出した

`shiftRun_exists_round`: 終端 `RoundScan` ＋ `CentreRep`（`InvLPC` の場）だけから
`ShiftRun` の存在が出る。運ばれる中心不変量
`ScanInvariant raw (position s.center) rad s1.left s1.right` が
（`leftPos`/`rightPos` でヘッドから `(center, radius)` が一意に決まるので）
中心頭を `C + h` に固定し、`RoundScan.rightPos` が右頭を `C + R + 2h` に置き、
`GalilEndOfInput.position_le` がそれを `2 * raw.length` で抑え、
`size : 2h ≤ R` が中心の `h` 歩と左頭の `2h` 歩の両方に余裕を残す。
`left_word` / `left_present` / `left_position` で左頭を 1 歩左へ。
**piece 4 は完全に閉じた**（新しい仮定ゼロ）。

### 訂正

前ターンの「次は `segment_to_checkpoint` を `hsegmentM` の消費者に配線」は外れ。
`hsegmentM` は `h_oracle_of_leaves*` の葉から既に落ちている（`segment_of_invLPC` が
`hreadyB` に置換済み）。`segment_to_checkpoint` が閉じたのは `hmismatch` の `hpos` 残差側。

## n77 (2026-09-19) 最上位 4 前提を維持しつつ残差を 3 つの壁に統合、`hor` に初めて producer を付与

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

最上位は `pal_in_peg_final37`（`CloseoutFinalW4`）の **4 前提**（`hSP` `hor` `hC` `hpack`）。
計画書 §10.5（前提ゼロ）は未達。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### 残る独立な壁は 3 つ

| 壁 | 内容 | 帰着 |
|---|---|---|
| **`ScanToScan`**（run の区間分解） | scan-to-scan の run が `ScanSeg` ＋ `Rounds` に分解する | `hSP` のラウンド境界と最初のラウンド、`hor` の found 葉（`ShiftRoundC`）、`SpanRep` 輸送 |
| **`hC`** | `H_realizeLIMW'`、局所機械の実現 | 未分解 |
| **`hpack`** のモデル欠陥 (e) 部分 | `marks` / `hwin` — `beginFallbackVM'` の着地場所が存在量化 | `Fair` かモデル変更が必要 |

### `hSP` の分解（`ShiftPal` → 束 ＋ 2 葉）

`shiftPal_of_readOrigin` の入力は `ChainRound` ＋ `canRight s.right` ＋ `H_fresh` だけになった。
運ぶ 5 場を `CloseoutRoundBundle.RoundBundle` にまとめ、`roundBundle_tick` で組み上げて
コンパイラに残差を検証させた。

| 場 | tick | 残差 |
|---|---|---|
| `ChainRound` | `chainRound_tick_S` | なし（`H_shiftDone` は束自身の `ShiftRound` から） |
| `ReadsRound` | `readsRound_tick_S` | `H_readsShift`（`SweptOff` 基底化で消える） |
| `ShiftRound` | `shiftRound_tick_A` | `H_freshShift` |
| `PeriodShape` | `periodShape_tick`（23 形） | なし |
| `NoReplayWatch` | `noReplayWatch_tick`（23 形） | なし |

証明した葉: `H_matched`（過剰量化）、`H_born`（phase 0 vs 4）、`H_advance`（`ReadsInv`）、
`BlockInv`（`ChainPosInv2`）、`H_birth` の誕生半分（`PeriodShape`）、
`H_birthR`/`H_readsBirth`（`NoReplayWatch`）、**`H_advanceT`**（palindrome 2 枚の鏡映 ＋
`continued_prediction` の mod 形）。
`WatchShift`（**偽**）は 1 節しか使われておらず `canRight s.right` に置換。

### `hor` に初めて producer を付けた

**訂正**: 「`h_oracle_of_leaves''` が `hor` を産出する」は誤り。tree 中の
`h_oracle_of_leaves*` は**全部** `GalilFinalAssembly.H_oracle`（`CycleOracleMC`、
origin/着地とも `InvL`）を結論とし、`hor` は `CycleOracleMC3`（origin/着地とも
`InvLPS`）で別物。

`CloseoutOracleBridge.hor_of_H_oracle` が橋（差は 2 つ：不変量と、中心進行 vs `mu` 進行）。
`CloseoutOracle8.h_oracle_of_leaves7` で `H_oracle` の葉を **13 → 11**
（`hbudget` と `hrs` を閉じた。鍵は **`Decodes` がタダ** — `decodesC` が証明済み）。

### 訂正した自分の誤り（このセッション）

1. 「`BigPack2MG7W''` に 5 場足す配線で `hme` が落ちる」→ 落ちない（`wpack_tick` が毎 tick `hwin` を要求）
2. 「`hended`/`hlastMatch` は閉」→ **閉じてない**。producer の側入力 `hpres` が偽（`searchReady_run_true_iff`、機械検査: `CloseoutPresRefute`）
3. 「`hor` に producer がある」→ 無い（型名は同じでも結論が違う）
4. 「原点はラウンド単位でしか運べない」→ `Offset` 形なら shift 相を生き延びる（`SweptOff`）
5. 「`H_advanceT` は窓の外」→ palindrome が 2 枚あるので窓の内側

**教訓**: 型名の一致で producer を判断せず、**定義を展開して origin と結論の不変量を照合する**。
CLAUDE.md §1 に記録した。

## n76 (2026-09-19) 最上位を 8 → 4 前提に。`hsc`/`hws`/`hsl`/`hni` は反証、`hbudget`/`hav`/`hstart`/`hee`/`het`/`hfl`/`hme` は run 束の場へ

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

### 最上位: 8 前提 → 4 前提

**`pal_in_peg_final37`（`CloseoutFinalW4`）は 4 前提**: `hSP`（scan 状態の `ShiftPal`）、
`hor`（`CycleOracleMC3`）、`hC`（`H_realizeLIMW'`）、`hpack`（`ChainPosInv2 → ChainPack`）。
残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

### この区間で効いた 1 つの技法

**単一状態の性質は、別前提ではなく run が運ぶ束（`ChainPack`）の場に置く。**
`hav`（`ConsumeAvail`）、`hstart`（`BgStartP2`）、`hbudget`（位置上界）、`hfl`（`0 ≤ length`）は
すべてこれで落ちた。位置上界が単一状態の性質だと気づいた時点で `hbudget` は 5 分で落ちた
（その直前にウチは「見込みなし」と書いていた。誤り）。

### 反証した前提（4 つ）

| 前提 | 反例・理由 |
|---|---|
| `hsc`（`H_stageScan`） | `InvScan` の 11 場は `s.radius` に触れないが `ReplayStage` は `Canonical radius` を要求 → `InvLPS` に再切り出し |
| `hws`（`WatchShiftG`）/ `hsl`（`H_shiftLocalG` の一部） | `ChainStep.backDone` で生まれたばかりの watch は `distance = reset` なので `4 * periodLength ≤ distance` を破る |
| `hni` | `initVM` は `chain = .idle` を与え、`invLPC_init` は `mode = .scan` に着地する（空虚） |

### 主要な新規

| 名前 | ファイル | 内容 |
|---|---|---|
| `front_eq_position` / `extra7_of_front_steps_pack` | `CloseoutFrontExtra` | `hee`/`het` を `front = position right + value replay` の単調性で。34 分岐の右ヘッド解析は不要だった |
| `LagAll` + `lagAll_step`/`lagAll_matched` | `CloseoutLagAll` | lag の canonical + 非負が `ChainStep ∪ ChainMatched` で閉じる |
| `lenNonneg_of_span_radius` | `CloseoutSpanTick` | `hfl` を `SpanRep` + `RadiusRep` から。`shiftTick` は `length` を 2 減らすが `radius` も減るので関係は保存される |
| `windowInOrigin_tick_pin` / `walkerInv_tick_pin` | `CloseoutWinTick` / `CloseoutWalkerTick` | `Fair` 依存はどちらも 1 箇所・状態対の等式 1 本だけ。pin に置換して逐語保存 |
| `ChainPack`（約 25 場） | `CloseoutChainPack` | run が運ぶ中央の束。`q`/`first` は構造体引数 |
| `bigPack2MG7W''_tick_M` / `packRunR_MWP` | `CloseoutMarksPack` | `hme` は `hpack` の `marks` 場に包含されていた |

### 訂正した自分の誤り

1. 「`extra7_of_run` は 1 行で配線できる」→ できない（`PackRunRMG2` に位置上界がない）
2. 「`length` は減らない」→ `shiftTick` が `dec (dec s.length)`。代入の grep はレコード更新を見落とす
3. 「`hfl` は tick 不変量でない」→ `spanRepS_shiftTick` が存在する
4. 「`hbudget`/`hme` に見込みなし」→ どちらも落ちた
5. 「単一ファイル build が通れば十分」→ 構造体の引数を変えたら必ず全体 build（`ChainPack` の arity 変更で全体が 11 error / sorryAx 5 になった）
6. 「`hor` は producer ゼロで原理的に到達不能」→ 誤り。`h_oracle_of_leaves''` が 14 葉から産出し、13 葉版 `CloseoutOracle7` は build 済み・未登録だった
7. 「`Fair` の除去には構造変更が必要」→ 参照は各 1 箇所
8. 「`BigPack2MG7W''` に 5 場を足す配線で `hme` が落ちる」→ 落ちない。`wpack_tick` は着地の `hwin` を毎 tick 要求し、`hwin` を場にする道は `beginFallbackVM'` の着地場所 `p` が存在量化されたまま（モデル欠陥 (e)）なので閉じている

### 次

`hpack` の残差は `ChainSide`（`CloseoutChainPack:241`）。`lagCan`/`backLag` は `LagAll` で閉、
残りは `repV`/`repVmid`/`scanBound`、および `marks`（モデル欠陥 (e) に触れる）。

## n75 (2026-09-19) `hbs`/`hls`/`hsl` を定理化して最上位を 8 前提に、`M-periodOnly` をモデルに実装、`hsc` は反証して再切り出しへ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規登録: `CloseoutCandOrient`、`CloseoutShiftLocalFree`、`CloseoutStageScan1`、`CloseoutPackRun51`、`CloseoutBirthFrame`、`CloseoutPeriodOnlyRegression`。sorry なし。

### 最上位: 11 前提 → 8 前提

`pal_in_peg_final25`（`CloseoutPackRun51`）。`final24` の 11 前提のうち 3 つが**義務ではなかった**ことを確認して供給した。

- `hsl`（`H_shiftLocalG`）: `InvLPC` のどの状態も chain は idle。`Inv.rest` が `Restarted` を出し、その第 1 連言が `r.chain = .idle`。scan 側は `InvScan.chainIdle`。chain が idle なら `ShiftLocalG` の全場は `beginShiftVM'` の watch 前提を要求するので空虚（`shiftLocalG_of_chainIdle`）。→ `CloseoutShiftLocalFree.chainIdle_of_invS` / `h_shiftLocalG`。
- `hbs`/`hls`（`H_bootShift`/`H_landShift`）: 同じ理由。`initVM0` が `chain := .idle` を置き、`initial` からの唯一の tick `Tick.init` がそれを保つ。既に `CloseoutPackRun6` に定理としてあった。

残る 8: `hSP`, `hws`, `hee`, `het`, `hme`, `hsc`, `hor`, `hC`。

### `hsc`（`H_stageScan`）は偽。再切り出しの第 1 段を証明

`H_stageScan` は「`InvScan` を満たす**すべて**の状態で `ReplayStage`」を要求する。`InvScan`（`GalilReplaySegment:317-341`）の 11 場は `s.radius` に一言も触れないのに、`ReplayStage` の `Restarted` は `RadiusRep r.radius Rad`＝`Canonical r.radius` を要求する。`Counter = ⟨pos neg : List Unit⟩` なので、任意の `InvScan` 住人の `radius` だけを値 `0` の非正準表現 `⟨[()],[()]⟩` に差し替えると 11 場は全部生き残り `ReplayStage` だけ壊れる。

修正は既知の型の再切り出し `InvScanS := InvScan ∧ ReplayStage`（`InvScan → InvScanO`、`SearchReady → SearchReadyB` と同じ手）。産出側は既にデータを持っていた: `replay_after_fallback` は `Restarted raw t 0 reset` と `c.clock = 2048` を前提に持ち、`WatchSegE` を返しながら `stage` 場だけ捨てていた（`GalilReplaySegment:310` の docstring がその旨を記録している）。`CloseoutStageScan1.replayStage_of_seg` / `replayStage_of_replay_after_fallback` で拾い直した。

### `M-periodOnly`: モデルの欠陥を実装して全体に通した

Scala `ScaffoldChain.start()` は `periodOnly = false` **かつ** `cycle.reset()` を行うが、Lean のモデルはどちらも落としていた。誕生条件は `found = true` ではなく「その遷移で新しい chain が実際に始まること」なので `chainBorn (found) (x : ChainVM) := x.isIdle && found`、状態側を `afterBirth born s`（`GalilScaffoldTopSearch:70,77`）で包む。`compareFound`/`backgroundS` の遷移先をこれで包んだ。

- 抽象側の破損は**射影を 1 個挟むだけ**の型ずれで、`GalilFrontier`、`GalilReplayRest`、`GalilScaffoldTopRoundS`、`GalilScaffoldTopFirstRound`、`GalilScaffoldTopFoundLife`、`GalilScaffoldTopLifeRestart`、`GalilScaffoldTopFoundLoop`、`GalilScaffoldTopFallbackCycleS`、`GalilScaffoldTopFallbackRestart`、`GalilScaffoldTopOutputRound`、`GalilScaffoldTopFallbackAll`、`GalilScaffoldTopOutputCycle`、`GalilTickFun`、`GalilTickFun2`、`GalilCycleNoShift`、`LocalReplaySwap`、`LocalReplayParked`。`GalilScaffoldTopSegmentHeads.watchSegE_heads` だけは単調形 `t.periodOnly = true → s.periodOnly = true` に弱めた。
- 伝播を止めた補題が 2 本。(1) `not_shiftGuard_afterMismatchB`（`GalilScaffoldTopFallbackCycleS`）: 誕生時は `chainStart` が `.copy` を返すのに `shiftGuardVM` は `.watch` を要求するので、誕生の有無にかかわらず guard は立たない。これで `¬ shiftGuardVM (afterMismatch …)` を仮定に持つ 20 ファイルへの伝播が消えた。(2) `refresh_afterBirth_iff`（`GalilScaffoldTopSearch`）: `P.onLetter = onLetterVM raw` と `P.leftFirst = leftFirstVM` の下で `refresh` は `afterBirth` 不変。`outputRel_matched_refresh'` 系の呼び出しをそのまま生かせる。
- 局所側は `LocalTick1` に `birthL` / `abs_birthL` / `inv_birthL` / `stepLocal_birthL` / `matchCtl_congr` を入れ、`bgState` に誕生元 chain を渡し、局所歩数 `c₁` を 66 → 67（match 分岐が `searchSteps + 3`）に上げて `tickL1_local` / `tickL1_inv` / `tickL1_abs` を再証明。
- `tickL1_abs` は新たに側条件 `hbirth`（`onLetter`/`leftFirst`/`replayExhausted` が `afterBirth` 不変）を取る。`Shared` の 3 場は抽象関数なので一般には示せないが、具体 `PofC` では `onLetterVM` が `position s.right`、`leftFirstVM` が `position s.left`、`replayExhaustedVM` が `s.replay` しか読まず、`afterBirth` はその 3 つを触らないので定理になる（`CloseoutBirthFrame.hbirth_PofC`）。
- 回帰テスト `CloseoutPeriodOnlyRegression.birth_resets` は修正前は失敗し修正後は通る。

### `hee` の残差は真偽未確定（偽の疑いが強い）

`H_extraEntry7` の残差は `∀ c r, InvLPC w c r → position r.right ≠ 2*w.length`。`Inv`（`GalilRunInv:29-49`）の 10 場のうち右ヘッドに触れるのは `input : Represents r.right.head raw` だけで、これは**内容を縛るが位置を縛らない**。入力を食い切った状態（`Tick.scan_wait` が回る状態）でも全場が成立しうる。攻め口は (a) `w = []` で `2*w.length = 0` と初期位置 `0` が一致する反例、(b) `InvLPC` への右ヘッド余裕場の追加（`hsc` と同じ再切り出し）。台帳に記録した。

### 既に反証済み（回帰テストとして常駐）

`H_candOrient`（裸の prefix→suffix `Candidate` 移送）は偽。証人 `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`。`CloseoutCandOrient.unrestricted_transport_false`。正しい橋は同一窓＋反転の `GalilDpSuffix.candidate_iff`。

### `hme` への合成: `hcan` は `CPack` から出る（`CloseoutReplayCanRight`）

`CloseoutPackRun28.walkerInOrigin_of_run`（`WalkerInOrigin` の産出元、そこから `hme`）は義務 `hcan`＝「到達可能な各状態で `replaying = true` なら右ヘッドが動ける」を持っていた。これは仮定ではなく合成で出る。

- `FrontPack.replayPos`（`GalilFrontMono:98`）: `replaying = true → ∃ m, replay = ofNat (m+1)`。
- `FrontPack.frontier`: `Frontier s`＝`position right + m ≤ 2 * arrived right`。
- 右へ動けないなら終端 gap で右スタック空＝`PopsIncoming`。`consume_not_replaying_false`（`GalilFrontier:342`）がこれと正の replay カウンタから `False` を出す。
- **`CPack.front : FrontPack c s`**（`GalilCentreLive:152`）。`CloseoutPackRun25.wpack_of_fair` は既に `CPack` を持ち回っており、`cpack_tick` の唯一の入力 `hfl` もその仮定にある。

よって `cpack_steps` で `CPack` を歩数に沿って運べば `hcan` は定理（`hcan_of_cpack`）。新規入力なし。

## 2026-09-19 wave 10 — `ShiftLocalG` も消えた: **8 前提・反証済みゼロ**（`pal_in_peg_final30`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final30`（`lean-pal/PalPeg/CloseoutFinalW.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、
**`WatchShiftG` も `ShiftLocalG` もコードに現れない**。

`final29` の `hsl : ∀ w y, ShiftLocalG … w y` も偽だった（`ShiftLocalG` の全場の
前提は `beginShiftVM'` で、`beginShiftVM` は `s''.chain = .watch w` のみ要求する
ので、`ChainStep.backDone` 生まれの `distance = reset` の watch が前提を満たしつつ
`4 * periodLength ≤ distance` を破る）。

弱化ではなく**削除**した。wave 8 で trail 橋を `ChainPosInv` に載せ替えた結果
`IPackMG.shift` を読む者が誰もいなくなったため。`Run30` から直接落とすと旧鎖
`final17 → … → final25` が壊れる（実測・ロールバック済み）ので非破壊複製:

- `CloseoutPackW` — `IPackMW := LPackM ∧ LPackM2`、`BigPack2MG7W`、`ipackMW_tick`
- `CloseoutCheckW` — `StepsIMW` 〜 `preTraceIMW_exists`
- `CloseoutOracleW` — **`packRunR_MW`（shift 仮説ゼロ）**、boot、oracle、`needL'`
- `CloseoutFinalW` — `H_realizeLIMW'`、**`pal_in_peg_final30`**

`hC` は `PreTraceB` を取る形（`H_realizeLIMW'`）に変えた。`LatchTrue` は
`stLG' τF w st (Tc w.length)` だけを読み run pack に触れないので、これが自然な領域。

`final30` の 8 前提（すべて未反証）: `hSP`, `hme`, `hor`, `hC`,
`hfour`, `hbgP`, `hmatchP`, `hsdP`。後ろ 4 つは Run34 の guarded 分岐仮説で
`chainPosInv_tick` が 23 形状中 20 を閉じており残り 3 形状分。

**wave 6 からの推移**: 8（`hsc` 偽）→ 7 → 5（`hws` 偽）→ 9（`hsl` 偽）→
**8（反証済みゼロ）**。数の増減より「偽の前提が残っているか」が判定基準。

## 2026-09-19 wave 9 — 偽の `hws` が最上位から消えた（`pal_in_peg_final29`）

**全体 build 成功（EXIT=0、エラー 0、sorryAx 0）・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final29`（`lean-pal/PalPeg/CloseoutWeakFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、**`WatchShiftG` は
もう現れない**。前提は 9 個で `final27`（5 個）より多いが、**偽の前提が
ゼロ**になった。数より正しさ。

`hws : ∀ w y, WatchShiftG … w y` は偽（`CloseoutPackRun32` の caveat:
`ChainStep.backDone` で生まれた watch は `distance = reset` なので
`4·periodLength ≤ distance` が破れる）。2 つの弱化で消した:

1. **trail 側**（wave 8）: `pal_in_peg_final5MG2T` が trail 橋の全体を
   `ChainPosInv` の上で走らせる（`ChainPosInv → shiftLocalS_of_run →
   radPack_ptS → trailF_ptS → needIMG2'_le_S`）。boot の `ChainPosInv` は
   chain が idle なので無料。
2. **pack 側**（wave 9）: `packRunR_MG27P` は `hws` を 1 箇所でしか使わず、
   そこが必要とするのは `ShiftLocalG`。`WatchShiftG` はそれを含意するだけ
   （`shiftLocalG_of_watchShiftG`）なので、`ShiftLocalG` を直接取れば
   厳密に弱い前提になる（`packRunR_MG27L`）。

`final29` の 9 前提: `hSP`, `hsl`（`ShiftLocalG`）, `hme`, `hor`, `hC`,
`hfour`, `hbgP`, `hmatchP`, `hsdP`。後ろ 4 つは Run34 の guarded 分岐仮説で
すべて `shiftGuardVM` 付き・unmatched 限定。`hsl` の 4 場のうち `move` は
wave 7 の `Extra7` で既に無料。

新規: `CloseoutShiftS`, `CloseoutShiftFinal`, `CloseoutShiftWeak`,
`CloseoutWeakFinal`（全て標準公理のみ）。

## 2026-09-19 wave 7 — `hee`/`het` を無条件化、最上位は **5 前提**

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final27`（`lean-pal/PalPeg/CloseoutExtraFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、残る仮定は 5 つ:
`hSP`, `hws`, `hme`, `hor`, `hC`。

`hee`（`H_extraEntry7`）と `het`（`Extra7` の tick 保存）は、いずれも
`packRunR_MG27` の `hprefix` を作るためだけに存在した。その `hprefix`（run の
各 scan/非 replaying 状態で `canRight`）は、**front ポテンシャルに乗って伝わる**:

- `front s = position s.right + value s.replay` は `CentreLive` run 上で単調
  （`GalilFrontMono.front_stepsAll_mono`、既存）。
- `FrontPack.rest = ReplayRest` より非 replaying 状態では `replay = reset`、
  すなわち `front s = position s.right`。
- よって出口 `y` が非 replaying かつ cycle の上界を持てば
  `position x.right = front x ≤ front y = position y.right ≤ 2m-1`。

右ヘッド自身の単調性（34 ケースの `Tick` 解析）は一切不要。`extra7_of_bound` の
残り 2 入力は `LPackM.scanGeom` の `ScanInvariant` から出る（発火条件が
`Extra7` の語る条件と完全一致）。帰納の循環は `bigPack2MG7''_tickE` が
`Extra7` を「構築済み pack の関数」として受け取ることで解消。

呼び出し側は全て上界を持つ: 進行分岐は `CycleOutMC3` の定義、checkpoint 分岐は
`ReportPointAt` の `notReplaying`/`atPlace`/`pos`/`le`。

新規: `CloseoutFrontExtra`, `CloseoutExtraFree`, `CloseoutExtraOracle`,
`CloseoutExtraFinal`（全て標準公理のみ）。

**訂正**: wave 5 の「`hee`/`het` の残差は偽の疑いが強い」は誤り。偽なのは
「任意の状態で `canRight`」であって、run 文脈では真。

## 2026-09-19 wave 6 — `hsc` 完全除去、最上位は **7 前提**

**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final26`（`lean-pal/PalPeg/CloseoutStageFinal.lean`）は
`[propext, Classical.choice, Quot.sound]` のみに依存し、残る仮定は 7 つ:
`hSP`, `hws`, `hee`, `het`, `hme`, `hor`, `hC`。

wave 5 の `pal_in_peg_final25`（8 前提）から `hsc`（`H_stageScan`）が消えた。
`hsc` は wave 5 で反証済みだったが、**再切り出しすら不要**だった:

1. 主経路上の消費者は `cycleOracleIMG2_of_cycleOracleMC3R`（`CloseoutPackRun36:673`）
   だけで、そこが `hstage_of_scanBranch` を呼び `InvLPC → InvLPS` に持ち上げている。
2. その持ち上げの `Inv` 側は `replayStage_of_inv` で既に無条件（`CloseoutOracleI2:179`）。
3. `CycleOutMC3` は**両出口で `InvLPS` を返している**（`GalilInvPlus3:193, :212`）。
   `hIS.1` で捨てていただけ。
4. boot も `Inv` 分岐に着地する（`GalilFinalAssembly4.invLPC_init:94` の `hI : Inv`）。

よって Run36 §2 のチェックポイント再帰を `InvLPS` 上で再走させれば
`hstage_of_scanBranch` は一度も呼ばれない。`preTraceIMG2S_exists` の結論
`PreTraceIMG2` は Run36 の同名 structure そのものなので下流は無改造。

新規（全て標準公理のみ）: `CloseoutStageRecur`, `CloseoutStageCheck`,
`CloseoutStageBoot`, `CloseoutStageOracle`, `CloseoutStageFinal`。
PR #65 マージ済み。残差の正本は `lean-pal/CLOSEOUT_LEDGER.md`。

**次の狙い**: `hee`/`het`/`hws` の共通核は `canRight`（`extra7_of_bound` で
位置上界から出せるが、`PackRunRMG2` の `hprefix` に位置上界が無い）。
`hme` は `ChooseLayout` の run 不変性に還元できる（`marksEntry'_of_layout` は
**副条件なし**、`CloseoutPackRun16`）。

## n20 (2026-09-17 朝) 葉の放電・偽仮定 4 件・非決定性

## n74 (2026-09-19 未明) 外部レビューを受けて**台帳導入**・`H_candOrient` 反例確定・自分の誤報 1 件を訂正・oracle から `hpres` 消滅

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規登録: `CloseoutCandOrient`、`CloseoutWatchRound52`、`CloseoutPackRun49`、`CloseoutOracle6`、`CloseoutWatchRound53`、および `GalilReplaySpan.lean` への**追記のみ**の §24。sorry なし。

### 進め方の是正（`lean4-peg-closeout-followup-2026-09-17.md` を受けて）

外部レビューの指摘を妥当と認める。**「新ファイル＋新しい `finalN`＋build 緑」を単独では前進として数えない。** `final13 → final24` の番号増加は義務の減少を意味しない。
新設した **`lean-pal/CLOSEOUT_LEDGER.md`** が残差の正本（区分: `OPEN`/`REFUTED`/`REFORMULATED`/`PROVED`/`INTEGRATED`）。
未解消の前提を `H_x → H_y`・構造体フィールド・instance・別 oracle へ移しただけなら `OPEN` のまま。
`#print axioms` は推移的公理依存の検査であって、引数に置いた前提の成立は検証しない。

### REFUTED を 1 件、Lean で確定

`H_candOrient`（裸の prefix→suffix `Candidate` 移送）は**偽**。証人 `W = [0,0,0,0,0,1]`, `n=5`, `lower=0`, `h=1`（`W.take 5` の接頭辞 3/5 は回文、`W.drop 3 = [0,0,1]` は非回文）。
`PalPeg/CloseoutCandOrient.lean`: `prefix_ok`、`suffix_bad`、**`unrestricted_transport_false`**、対比として正しい橋 `correct_bridge`（= `GalilDpSuffix.candidate_iff`、同一窓 + 反転）。標準公理のみ。回帰テストとして常駐させ、旧契約名が消えても反例が残るようにした。
なお `Extra.cand` は既に主経路から削除済み（n67/n69）なので、この反例は削除が正しかったことの裏付け。

### 自分の誤報の訂正

n72 で「`WatchFreshAtC` は文脈だけで閉じた」と書いたのは**誤り**。`CloseoutWatchRound52` により、着地の chain は `copy`（`chainStart` は `ChainVM.copy`、`ChainMatched` は構成子を保つ）であって `watch` ではないので、`WatchFreshAtC … cP sP` は**前提が充足不能＝空虚**（`landing_chain_copy`:120、`landing_not_watch`:135、`watchFreshAtC_vacuous`:148）。watch 誕生は着地の `2h+3` prep tick 後で、そこでの clock は fresh でない。→ 誕生時刻版 `WatchBirthFreshC` が `OPEN`。純益は、**反証済みの `WatchFreshC` schema と `watchClockC_of_fresh` が経路から外れた**こと（`WatchClockAtC` は birth ごとに証明可能な形）。

### oracle: 反証済みの普遍葉が経路から消えた

`GalilReplaySpan.lean` §24（追記のみ、既存宣言は不変）: `HpresRun`、`hpresRun_mono`、`found_resultRP`、`idle_countdown3RP`、`idle_compare3RP`、`replay_construct3RP`、`replay_after_fallback_general''RP` — 不変版の 6 つの `hpres` 使用箇所を全部放電。`CloseoutOracle6`: `invScanO_of_replay_generalR'`、`cycleOracleMC2C_of_piecesP'`、**`h_oracle_of_leaves5`**。
**`hpres`/`hpresRep`（普遍形、`hpres_false_at` が反証）は oracle のどこにも現れなくなった。** ただし後継の `hpresRepAt`/`hpresT` は「供給可能」であって**まだ供給されてへん**＝台帳では `REFORMULATED`。実供給は `CloseoutOracle7` で試行中。

### その他

- `CloseoutPackRun49`: `LPackM3` = `LPackM2` + `centreLedger` + `lagCan`、`lpackM3_tick`（全 23 分岐）。`MatchRes2` の成分は `repR`/`saneR`/`canR`/`repNext`/`radNext`（中心台帳が `rad = value radius + 1` を厳密に固定）/`startLedger`/`lagCan`/`backLag` が閉。残 `repVmid`/`replayPay`/`repV`/`canRNext`。
- `CloseoutWatchRound53`: **`WatchTailC` は定理**（`watchTailC_of_coreX`:213）。credit の形は不安定だが**形の対が安定**（`WRel`: `queued` か `immediate`）、run 長は不変なので `ChainWRun` の測度修正は不要。入力は Round50 の呼び出し側に既にあり新規の未解決なし。`ClockOneC` は `MatchCoreC`（純粋に機械レベル）1 つから従う。
- **build 失敗の記録**: 一つ前の全体 build は EXIT=1 / errors=4。全部 `Lean exited with code 139`（SIGSEGV）で、サブエージェントが `lean -o` で `.olean` を上書きしたことによる成果物の競合。証明の失敗ではない。再実行で緑。今後、全体 build 中は共有 `.lake` への書き込みを行わせない。
- `M-periodOnly`（chain 誕生時に `periodOnly = false` と `cycle.reset()` が漏れている）の先送りを解除し、隔離 worktree で専任担当を開始。boolean 一個の代入では不十分で、誕生条件は「その遷移で新しい chain が実際に誕生すること」（`found = true` ではない）。


## n73 (2026-09-19 未明) chain 台帳の葉が 3 つ閉・fallback replay は `Mode.scan` + `replaying` フラグ・oracle 橋が閉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun48`、`CloseoutPreload41`、`CloseoutWatchRound50`）、sorry なし、build ログ `build_n73c.log` EXIT=0。
- **pack（`ChainPosInv2` の葉）**: `CloseoutPackRun48`: **訂正** `LagNonneg` は自動でない（`value : Counter → ℤ` で空 `pos` の `dec` は −1、`lagNonneg_not_of_canonical` :27）が、`LagCan`（:35、watch で `Canonical lag ∧ 0 ≤ value lag`）は**自己保存**（`lagCan_step` :51（`take` の `positive` ガードが減分を払う）、`lagCan_matched` :74）→ 場を 1 つ足せばよい。**より良い経路**: `ConsumeAvail` が参照されるのは `Internal.take`（ガード `positive lag`）と `Outer.immediate`（ガード `zero lag`）だけなので、`chainPos_step_of_supply`（:107）は**源自身の `canRight s.right` だけ**で済み、**`H_bgP2` から供給の葉が消滅**（`h_bgP2_of_supply` :172）。葉 (2) 閉（`h_matchP2_of_target` :250、供給は目標 payload 自身の `canR`）、葉 (4) 閉（`chainPos_immediate` :330 + `h_shiftEntry2_of_target` :365）、葉 (5) は chain 内容を持たず 2 つの素の pack 場（`h_shiftDoneRad2_of_supply` :418）。残: `MatchRes2` の成分（`repVmid`/`backLag`/`replayPay`/`saneR`/`radNext`/`startLedger`）と新規場 `CentreLedger`（scan で `canRight center ∧ Sane center ∧ pos center + value radius = pos right`；`scan_match` で両辺 +1、`shift_done` は `shiftGeom`+`shiftGeom_exit` から再確立、ヘッド半分は `CentreRep` のモードガードを scan に広げる）→ `CloseoutPackRun49`（`LPackM3`）進行中。
- **readiness/oracle（訂正）**: `CloseoutPreload41`: **「fallback replay は `Mode.replay`」は誤り** — `GalilReplaySpan.idle_countdown3`(:1484–87)/`idle_compare3`(:1737) はどちらも `c.mode = .scan` で走り `c.replaying = true` は**フラグ**。`ReadyFieldP3` は `replaying` に言及せんので `paced`/`paced0` がそのまま適用でき、**新しい節は不要**（`ReadyFieldP4 := ReadyFieldP3`）。`hpresAt_replaying`(:86)、`hpresAt_countdown`(:97)/`hpresAt_compare`(:104)（`HpresAt` の 2 ケースと一致）。`hpresRep` 自体は普遍（∀ s a v）なので `hpres_false_at` が反証 → 制限形 `HpresRepAt`(:148)。**橋は閉**: `stepsAll_bigPack2M''_of_soundScanNR`(:117、`packRunR_M''` の内側帰納を再走して run を昇格)、`hpresAt_along_soundScanNR`(:155) が `HpresRepAt` を供給（残は restart/replayStart の再入 2 つのみ）。残るは `GalilReplaySpan` に制限形を受ける primed 版を**追加**する編集（~9 署名 / 6 使用箇所、3 重化されたブロック）→ 進行中（`GalilReplaySpan` への追記 + `CloseoutOracle6`）。
- **watch**: `CloseoutWatchRound50`: **`WindowEndC` は仮定ゼロで閉**（`windowEndC_free` :86；`LandingData` の `ScanInvariant` が `Represents t.right.head raw` を持つので `position_le_of_represents` で `pos t.right ≤ 2|raw| < |encoded raw|`）。`ClockOneC` の match 側は 2 葉に: `WatchTailC`(:207) と `MatchQuantumC`(:254)。閉じた補助: `chainW_setE`/`chainW_setBud`、`chainW_bump`（:166、着地では窓端と右ヘッドが一致するので `E` は `R → R+1` と伸びる）、`inc_dec_comm`/`inc_decFour_comm`、**`bump_step`（:181、`copyBit`/`copyEnd`/`backStep`/`backDone` で credit の可換性を証明）**、`chainWRun_bump`（:219）。**訂正**: 「`inc lag`/`inc margin` は後段に読まれん」は copy/back までで、`.watch` では credit は場の加算でなく `Outer.queued`（`zero lag = false` のとき）/`Outer.immediate`（実際の consume）に分岐し、`queued` 後の `Internal` は `positive s.lag` を見る（`inc` が `reset` lag で反転）→ `WatchTailC` は `coreX_good` 経由。
- 進行中: `CloseoutPackRun49`、ReplaySpan primed 版、`CloseoutWatchRound50`、`52`。
- **偽だった主張の訂正**: 「`0 ≤ value lag` は表現から自動」→ 偽。「replay は `Mode.replay` 状態」→ `Mode.scan` + フラグ。
- 残: n72 と同じ、pack は `MatchRes2` 2 成分 + `CentreLedger`、oracle は `hpres` 消去の編集 + 既知の葉一覧。


## n72 (2026-09-19 未明) oracle の `hpres` は scan 側のみ放電・`WatchFreshC` は全区間量化で偽（着地形は文脈から閉）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutOracle5`、`CloseoutWatchRound51`）、sorry なし、build ログ `build_n72b.log` EXIT=0。
- **oracle**: `CloseoutOracle5`: `reachAtC2_of_target_matchP`（:64、`GalilOracleMC2.reachAtC2_of_target_match` を `HpresAt` で再証明；唯一の使用箇所 `MC2:544` は chain idle の scan 着地で `clock = 1`、まさに `HpresAt` の側条件）、`cycleOracleMC2C_of_piecesP`（:160、`hpres` を `hpresRep`（普遍、fallback replay 専用）と `hpresT`（到達可能性限定）に分割）、`h_oracle_of_leaves4`（:274）。**`hpres` は未放電**で、残差 `hpresRep` は `Mode.replay` 状態（`GalilReplaySpan:1480–1900` の `replay_construct3`/`idle_countdown3`/`idle_compare3`）にあり、`ReadyFieldP3` は `Mode.scan` 条件付きなので `hpresAt_along_run` が届かん → readiness に replay 節（`CloseoutPreload41` 進行中）。もう 1 つ小さい隙: `hpresT` の配線に run 述語の橋（oracle の `StepsAll … (SoundScanNR raw)` vs Preload40 の `BigPack2M''`）。
  - **oracle 葉の現況**: 閉 = `hex`, `hsearch`, `hends`, `hbudget`, `hrs`, `hended`, `hlastMatch`, `hstr`。残 = `hpresRep`, `hstage`（`ReplayStageInv`、mid-replay restart の `3·radius ≤ 5·last`）, `hshape`（`StartShape` は偽 → `StartShape'`）, `hlastMismatch`（最終文字分岐 + `EntryRefreshed`）, `hmismatch`（`hdp` → `MismatchDp`+`StageBudgetAt`、`hpos` → 区間予算；`hfb` 閉）, `hfound`/`hfoundBg`（着地不変量に `Restarted`/`StageEntry` + found tick からの経路構成、**最大の未着手**）, `hfoundReplay`（未着手）, `hreadyB`（着地での `RunEntriesAll`）。
- **watch（2 つの訂正）**: `CloseoutWatchRound51`: (a) `FoundCompareCtxC` は `cF.clock = 1` と `cP = {cF with clock := 2048}` を持つので **fresh clock は found tick でなく着地**（`foundCtx_landing_clock` :44）、文脈に `WatchSegE … cF sF cP sP` は無く輸送は `(cP, sP)` から始めるしかない。(b) **`WatchFreshC`（Round49:87）は偽** — 全 watch 区間を量化して `cb.clock = 2048` を主張するが `WatchSegE.stop` は任意の clock で成立（`not_watchFreshC` :68）。`WatchClockC`（Round47:111）も `watchClockC_of_fresh` 経由でこの欠陥を継承 → **`final19` の葉は着地形に切り直す必要**（`CloseoutWatchRound52` 進行中）。着地限定形 `WatchFreshAtC`（:78）は **文脈だけで閉**（`watchFreshAtC_of_ctx` :86、`cP.clock = 2048` は場、birth の `BlockInv` は `blockInv_matched`∘`blockInv_chainStart`）。`prepPaceC_of_seg`（:105）は `PrepSegLenC`（:99、長さ `2h+3`・マッチ数 `m` の着地区間）1 つを残して閉。`PrepBirthLagC'` の残りは台帳恒等式 `value w0.lag = value sF.radius + m` で、着地区間の chain tick が `prepEvents sm dm bs cs` と一致することを言えば `prep_value` で出る。
- 進行中: `CloseoutPackRun48`、`CloseoutPreload41`（replay 節）、`CloseoutWatchRound50`（`WindowEndC`/`ClockOneC`）、`52`。
- **偽だった主張の訂正**: 「fresh clock は found tick にある」→ 着地。「`WatchFreshC` は成り立つ」→ 全区間量化で偽。
- 残: n71 と同じ（watch は着地形への切り直し、oracle は上記一覧）。


## n71 (2026-09-19 未明) 相跨ぎで較正の穴が解消（`h ≤ 681` 不要）・マッチ時計 2 葉が閉じて `final19`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound48`、`CloseoutWatchRound49`）、sorry なし、build ログ `build_n71b.log` EXIT=0。
- **watch（較正の穴を解消）**: `CloseoutWatchRound48`: copy/back 相を複数クロック窓に跨がせる `ChainWatchReachM`（:175）、`reachM_run`（:189）、**`chainWatchReachM_of_background`（:230、跨ぎ回数は無制限、run 長は毎 tick 減る）**。`landing_run`（:126）は窓予算だけで閉じ**クロックが入らん**ので、n68 で問題になった `h ≤ 681` の要求は**消滅**。残 2 葉: `WindowEndC`（:116、`position sT.right + R < |encoded raw|`、旧 `PhaseWindowC` の生き残り）、`ClockOneC`（:159、clock 1 で match なら clock 2048・半径 `R+1` に転送、mismatch なら round 自身の出口 `X`；未閉部分は新規マッチ位置の `BlockOn` と `ChainMatched`（`inc lag`/`inc margin`）を run の残りと可換にすること）。消費側は Round42 の `ReplayBornRoundC` を**半径自由**にした `ReplayBornRoundC'`（:265）に直すだけで、`liveChainRoundC_of_reachM`（:281）が両分岐を同じ経路に流す。
- **watch（マッチ時計）**: `CloseoutWatchRound49`: `fresh_advances_pace`（:61、`2048·#true ≤ length`、`advances_le_compares` + `compare_budget`）、`pace_of_length`（`2048·#true ≤ len ↔ 2047·#true ≤ #false`）、**`watchClockC_of_fresh`（:95、`WatchClockC` 閉）**、**`prepClockC_of_length`（:117、`2048·m ≤ 2h+2` は `2h+3` 版からパリティで無料）**、**`foundExit_compare_final19`**（:141、`WatchClockC` → `WatchFreshC`）。**訂正**: `CloseoutPreload22.ClockInv delay c` は位相 `1 ≤ clock ≤ delay` だけで計数恒等式ではない（`run_invariant` は `#true + clock' = clock + 2048·fires` なので `clock < 2048` だと余分に 1 回 fire できる）→ 新鮮さ `clock = 2048` が本質的に要る。
- **収束**: 残る watch 葉 `WatchFreshC`・`PrepPaceC`・`PrepBirthLagC'` は**全部同じ対象**（found tick から着地までの `WatchSegE`、開始時の時計が fresh）に帰着 → `CloseoutWatchRound51` 進行中。
- 進行中: `CloseoutPackRun48`、`CloseoutOracle5`（`h_oracle_of_leaves'''`）、`CloseoutWatchRound50`（`WindowEndC`/`ClockOneC`）、`51`。
- **偽だった主張の訂正**: 「`ClockInv` から計数不等式が出る」→ 位相だけ、新鮮さが要る。
- 残: pack `hSP`/`hws` 供給 + `Extra7` 残差 2 + `hme`/`hsl`/`hsc`/`hbs`/`hls`/`hC`; readiness `hOP` のみ; watch found→着地 segment + `WindowEndC`/`ClockOneC` + `ReplayBornRoundC'` + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n70 (2026-09-19 未明) readiness が最後の消費先 `hpres` に接続・`final18`・`0 < lag` は機械と矛盾

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun47`、`CloseoutWatchRound47`、`CloseoutPreload40`）、sorry なし、build ログ `build_n70c.log` EXIT=0。
- **readiness（接続完了）**: `CloseoutPreload40`: `searchReadyS_of_readyPacedS`、`HpresAt`（:74、chain idle + (`a = true → clock ≤ 1`) + `searchEffect` ⇒ `SearchReady v`）、`searchReadyB_of_readyField3`（:81、`ReadyFieldP3 (n+1)` の scan 状態から）、`hpresAt_along_run`（:100）、`h_oracle_hpres_of_readiness`（:123）。**2 つの構造的事実**: (a) `GalilOracleMC3.h_oracle_of_leaves''` の `hpres` は普遍法則で `GalilLeafPres.hpres_false_at` が反証済み → 状態限定形でしか放電できん、(b) `ReadyPacedS` は `SearchReadyS`（`ReadyRemS = PrepInv ∧ DpSafeStage`）で閉じており `SearchReadyB`（`ReadyRem ∧ RunEntriesAll`）ではないが、`hpres` の結論は素の `SearchReady` なので `DpSafe` 変換は不要。残 `hOP`（`GalilOracleMC3` を点ごとの葉で受ける `h_oracle_of_leaves'''`）→ `CloseoutOracle5` 進行中。これが済めば **readiness 層は `final24` 経路に未解決の消費先を持たん**。
- **pack（訂正）**: `CloseoutPackRun47`: 「`ChainPos.watch` に `0 < value lag` を足す」は**機械と矛盾**（`Outer.immediate` は `zero lag = true` がガード、`lagPos_contradicts_immediate` :91；`take` も `value lag = 1` から lag 0 の `.watch` に落ちる、`take_lag_vanishes` :63）。正しい形は `LagNonneg`（:105）+ **1 セル先の供給**: `consumeAvail_of_next_supply`（:114）は目標側の右ヘッド（そこでの `canR` は `PosPayload2` の場そのもの）から出す。`bgStartP2_of_centre`（:163）で `BgStartP2` を `CentreLedger`（:153、中心ヘッドの present + 半径の**等式**）に還元（`scanGeomR` の `ScanInvariant` は不等式しか与えず、`CentreRep` は rewind/replayStart にガードされてる）。
- **watch**: `CloseoutWatchRound47`: `sumRel_ticks`/`sumRel_internal`（半径台帳の輸送、閉）、**`watchDrainC'_of_clock`**（:119、`m' := es2.count true`、`d1 := 0`）、**`foundExit_compare_final18`**（:166、`hdrain` → `hclock : WatchClockC`）。残 2 葉は同型のマッチ時計事実: `WatchClockC`（`2047·#true ≤ #false`）と `PrepClockC`（`2048·#true ≤ 2h+2`、prep 流の長さは `2h+3`）→ `CloseoutWatchRound49` 進行中。
- 進行中: `CloseoutPackRun48`、`CloseoutOracle5`、`CloseoutWatchRound48`（相跨ぎ）、`49`。
- **偽だった主張の訂正**: 「watching chain は `0 < lag`」→ `immediate` のガードと矛盾。
- 残: pack `hSP`/`hws` 供給 + `Extra7` 残差 2 + `hme`/`hsl`/`hsc`/`hbs`/`hls`/`hC`; readiness `hOP` のみ; watch 相跨ぎ + `ReplayBornRoundC` + マッチ時計 2 葉 + `PrepBirthLagC'` + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n69 (2026-09-19 未明) `pal_in_peg_final24`（Extra は `scanAvail` のみ、残差 2 つ）・**周期 `h` は非有界**（`ChainWatchPhaseC` の形が誤り）・readiness の tick は残差ゼロ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun46`、`CloseoutPreload39`）、sorry なし、build ログ `build_n69b.log` EXIT=0。
- **pack**: `CloseoutPackRun46`: `Extra7`（:70、`scanAvail` のみ）/`Extra8`（`rewindMargin` + `scanAvail`）、読み手を全部再証明（本体不変）、**`pal_in_peg_final24`**（:319）。仮定: `hSP`（`BigPack2MG7` 上）, `hws`, `hee : H_extraEntry7`, `het`（素の `Extra7` tick）, `hme`, `hsl`, `hsc`, `hor : CycleOracleMC3`, `hbs`, `hls`, `hC`。**`ready`/`failed`/`cand` を全部削除した結果、`ReadyFieldP`/`ReadyPacedS`/readiness 連鎖は pack 経路から完全に消滅**。残差はちょうど 2 つ:
  - 入口: `∀ c r, InvLPC w c r → position r.right ≠ 2 * w.length`（右ヘッドの end-of-input）
  - tick: `(mode ≠ scan ∨ clock = 1) → y.mode = scan → y.replaying = false → canRight y.vm.right`（`scan_match` の clock 1、`shift_done`、`replayStart` でのみ発火）
- **watch（較正の訂正）**: scout 調査の結果、**chain の周期 `h` は非有界**（入力とともに伸びる；`found_radius_le_two_period` は半径を周期で抑えるだけで逆は無い、`GalilReplayBudgetProof:19–22`、`GalilReplaySpan:116–118`）。よって `ChainWatchPhaseC`（`CloseoutWatchRound43:120`、copy/back 相が 1 クロック窓 2048 に収まる）は**一般には偽**で、`chainWatchPhaseC_of_window`（Round46:189）が `h ≤ 681` で止まったのは正しい。機械側は問題なく、Scala は 1 tick に 1 `stepCopy`/`stepBack`（`ScaffoldChain.scala:178–187`）で相は複数の比較周期を跨ぐ。→ obligation を跨ぎ可能な形に書き直す（`CloseoutWatchRound48` 進行中: clock 1 の match tick で継続、mismatch なら相を抜けて round 自身の shift/fallback 出口へ）。
- **readiness**: `CloseoutPreload39`: `paced` の idle 条件を外すのは偽（`scan_count` が clock を減らすので凍結ビューでは slack が買えん）。正しいのは **slack 0 の節** `paced0`（比較着地は `clock := 2048` なので常にこれ）: `ReadyFieldP3`（:57）、`readyField3_entry_of_datum`（:75、入口は chain に言及せず free）、`readyField3_background`/`_shift`/**`readyField3_tick`**（:157、残差は `hentry`/`hentry'` のみでどちらも入口定理が点ごとに放電）、`readyField3_along_run`（:244）。**`hact` は消滅**。`Extra.ready` が消えた今、readiness の唯一の消費先は `CycleOracleMC3` の `hpres`（`SearchReadyB`）→ `CloseoutPreload40` 進行中。
- 進行中: `CloseoutPackRun47`（`ChainPos'` + 葉 2–5）、`CloseoutPreload40`、`CloseoutWatchRound47`（prep 輸送・時計台帳）、`48`。
- **偽だった主張の訂正**: 「copy/back 相は 1 クロック窓に収まる」→ 偽（`h` 非有界）。「`paced` の idle 条件は外せる」→ 偽、slack 0 の節に分ける。
- 残: pack `hSP`/`hws` の供給 + 上記 2 残差 + `hme`/`hsl`/`hsc`/`hor`/`hbs`/`hls`/`hC`; readiness `hpres` 接続; watch 相跨ぎ + `ReplayBornRoundC` + prep 2 葉 + tie + `RestartLandingDataC`; core debris 配線・有限制御。


## n68 (2026-09-19 未明) `Extra.ready` も死に場・`hshift` 放電・`ShiftPeriodC` は葉でなかった・`final17`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 6 本登録（`CloseoutPreload38`、`CloseoutPackRun45`、`CloseoutWatchRound45`、`46`、`CloseoutPackRun44`）、sorry なし、build ログ `build_n68d.log` EXIT=0。
- **pack（監査）**: `CloseoutPackRun45`: **`Extra5.ready`/`Extra6.ready` は `final22` 経路のどのモードでも読まれん**（読み手は `scanAvail` と `rewindMargin` のみ）。`Extra5S`/`Extra6S`（scan/shift 相対 `ready`）、読み手を全部再証明（本体不変）、`extraTick5S_of_readyField2`（`ready` 半分を `readyField2_tick` から）、`pal_in_peg_final23`（:359、仮定の本数・形は final22 と同じ）。**ギャップ**: `readyField2_tick` が要求する `BigPack2M''` は削除済みの DP 場を持つ `Extra3` を含むので `BigPack2MG6S''` から供給できん（pack を使うのは `notInit` 1 点だけ）→ `ready` ごと削除する `Extra7`/`final24`（`CloseoutPackRun46` 進行中）。
- **readiness**: `CloseoutPreload38`: `scan_shift` は比較量子を 1 つ消費し（`hcmp` は `compareFound`）clock を 2048 にするので slack 0 = 比較後の値 → **`hshift` 放電**（`readyField2_shift` :51）、`readyField2_tick'`（:88）、`readyField2_along_run`（:114）。残 `hact`（active chain 時の paced 台帳）は `paced` の idle 条件を外せば消える → `CloseoutPreload39` 進行中。
- **pack（`WatchShiftS` 供給）**: `CloseoutPackRun44`: `position_le_of_represents`（:47）、`consumeAvail_of_supply`（:74、葉 (1) を `LagPos`（watching chain で `0 < lag`）1 つに）、`h_bgP2_of_start`（:126、葉 (2) を `BgStartP2`（source chain idle の場合のみ）に）。`LagPos` は `ChainPos` の watch 節に組み込むのが正しい（`CloseoutPackRun47` 進行中）。
- **watch**: `CloseoutWatchRound45`: **`ShiftPeriodC` は葉でなかった**（`ShiftRoundDataL` の `chain` 場と `remaining` 場から `period_of_beginShift` :81 で導出）、`watchStart_distance_zero`/`_broken_false`（birth では無料）、`PrepBirthLagC'`/`WatchDrainC'` の分割、**`foundExit_compare_final17`**（:219、`LandingFreshC` 消滅）。残 2 葉（prep 区間輸送、時計台帳）→ `CloseoutWatchRound47` 進行中。`CloseoutWatchRound46`: `chainW_true_of_window`（:106、`lim = false` の着地を明示予算 `2|xs| + 4 + (R_head − C)` で `lim = true` に格上げ）、`reach_watch`（:150）で **`n ≤ 2|xs| + 4 + (R_head − C)` が無条件**。残 1 葉 `PhaseWindowC`（:170）: `2|xs| + 4 + d ≤ 2047`。**未解決の較正問題**: `R_f ≤ 2h` はあるが `h` の上界が無く、`h ≤ 681`（= `d ≤ 1363`）が要る。`h` が入力とともに伸びるなら `delay = 2048` 内に copy/back 相が収まらん → Scala で copy/back 相が 1 比較周期に収まるのか、多周期に跨るのかを調査中（scout）。
- 進行中: `CloseoutPackRun46`（`Extra7`）、`47`、`CloseoutPreload39`、`CloseoutWatchRound47`、scout（周期上界と相の跨り）。
- 残: n67 と同じ + 較正（`h` の上界）。


## n67 (2026-09-18 深夜) `pal_in_peg_final22`（DP 関連が経路から消滅）・`ChainPosInv2` で先読み不要・`ChainWatchReachC` は歩数 1 葉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound43`、`CloseoutPackRun41`、`CloseoutPackRun43`）、sorry なし、build ログ `build_n67b.log` EXIT=0。
- **pack（死に場の削除）**: `CloseoutPackRun43`: `Extra5`（:73、`ready` + `scanAvail`）、`Extra6`（:80、`Extra'` − `failed`/`cand`）、`extra6_of_extra5`、読み手を `Extra6` 上で再証明（本体は不変: `lticksN_of_lpackM2_pt6`、`ipackMG2_tick_pt6`、`bigPack2MG6''_tick`、`packRunR_MG26`）、**`pal_in_peg_final22`**（:323）。仮定本数は final20 と同じ（`hSP`, `hws`, `hee`, `het`, `hme`, `hsl`, `hsc`, `hor`, `hbs`, `hls`, `hC`）で `hee`/`het` の形だけ変更、**`DpFieldP` と `H_candOrient` はこの経路から完全に消滅**。残差: `H_extraEntry5` は end-of-input（`pos R ≠ 2|w|`）1 つ、`H_extraTick5P` は `scanAvail` 転送（`scan_match`/`shift_done`/`replayStart` でのみ発火）+ `ready` 転送。**指摘**: `Extra5.ready` は無条件 `SearchReady` だが `ReadyFieldP` は scan 限定なので直結できん → `Extra5S`（scan/shift 相対）で繋ぐ（`CloseoutPackRun45` 進行中）。
- **pack（`WatchShiftS` 供給）**: `CloseoutPackRun41`: `ChainPos z R`（:62、live chain の 3 形それぞれで `canRight ver ∧ Sane ver ∧ pos ver + lag = R`）が Run38 の `SrcPos` を包含し**先読みを不要化**、`chainPos_step`/`chainPos_matched`（`ChainStep`/`ChainMatched` を通す）、`PosPayload2`/`ChainPosInv2`（:215）、`chainPosInv2_tick`（:272、**`shift_one` は無条件で閉**（`right` は `shiftLens` に無い）、init/replayStart/restart/scan_fallback・全 off-mode も閉）、`watchShiftS_of_chainPosInv2`（:357、`H_fourOther` も先読みも不要）。残 5 葉は全部入力供給型: `ConsumeAvail`（移動後 verifier の `canRight`）、`H_bgP2`、`H_matchP2`、`H_shiftEntry2`、`H_shiftDoneRad2`（半径台帳 + `canRight R` のみ）→ `CloseoutPackRun44` 進行中。
- **watch**: `CloseoutWatchRound43`: `chainWatchReachC_of_background`（:215）、`background_chainStep`、`ChainWRun`、`landing_step`（bundle 全転送）、`phase_run`。残 1 葉 `ChainWatchPhaseC`（:120、copy/back → watch の歩数 `n ≤ 2047`）: `lim = false` の `ChainW` は予算節が vacuous なので窓データ（`n ≤ xs.length + 1`、`BlockOn`）から出す → `CloseoutWatchRound46` 進行中。
- 進行中: `CloseoutPackRun44`、`45`、`CloseoutPreload38`（`hshift`）、`CloseoutWatchRound45`（lag 0 再基底化）、`46`。
- 残: pack `hSP`/`hws` の供給 + `Extra5S` 化 + `hplace`/`first ≠ 4`; readiness `hshift` + 帰納組立; watch `ReplayBornRoundC`/`ChainWatchPhaseC`/`PrepBirthLagC'`/`WatchDrainC'`/`ShiftPeriodC`/片 3–6 の L 版/tie/`RestartLandingDataC`; core debris 配線・有限制御。


## n66 (2026-09-18 夜) `Extra3.failed`/`cand` は死に場と確定・`LandingFreshC` 反証・readiness 入口が残差ゼロ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPackRun42`、`CloseoutWatchRound44`、`CloseoutPreload37`）、sorry なし、build ログ `build_n66c.log` EXIT=0。
- **pack（重要な監査結果）**: `CloseoutPackRun42`: `Extra4`（`parked` を場に昇格、`failed` を stage 相対形に、`cand` を DP の prefix 向きに）、`extra3_of_extra4`、`H_extraEntry4`/`H_extraTick4P`、`pal_in_peg_final21`（:277、`hO : H_candOrient` 追加）。**ただし監査で `Extra3.failed` と `cand` はどの消費側も読まんことが判明**: `Extra3` は `extra'_of_extra3` 経由でしか消費されず、`Extra'` の読み手（`canR_of_partsM`、`lticksN_of_big6`/`_big6G`/`_lpackM2_pt`、`extra3_scanAvail_tick`）は `scanAvail` と `rewindMargin` しか触らん。DP の実消費は `MismatchDp`（`GalilLeafDp:123`）が自前で `StageFailed` を出して `GalilOracleMC3.hdp` に渡す経路。→ **2 場を削除**する `Extra5`/`final22`（`CloseoutPackRun43` 進行中）で `H_candOrient` と `DpFieldP` の 6 分岐が丸ごと消える見込み。
- **watch（訂正）**: `CloseoutWatchRound44`: **`LandingFreshC`（Round41:151）は偽** — `h` が普遍量化で制約は `beginShiftVM h w' …` だけ（どの `h` でも充足）なので `periodLength w' = h` が `0 = 1` を強制。分割形 `LandingFreshC'`（:82、`h` 自由な転送 3 節）+ `ShiftPeriodC`（:90、`h` を選ぶ側の period 節）、`landingFreshC_of_parts`（:100）。`SumRel (.watch w) R` は `broken = true` で vacuous、さもなくば `distance + lag = R`（`sumRel_watch_broken`/`_of_unbroken`）。`WatchDrainC` は birth での `distance = 0` 節が要り、それは `PrepBirthLagC` 側に載せる。`CloseoutWatchRound45`（再基底化 + `PrepBirthLagC'`/`WatchDrainC'`）進行中。
- **readiness**: `CloseoutPreload37`（再実装）: `ReadyFieldP2 n`（:46、`ready`/`readyS`/`paced`/`shifting`；shift 中は `searchEffect` が発火せんので idle 前提なしで保存）、`readyField2_tick`（:105、fuel は単調 `n ≤ n'`）、**`readyField2_entry_of_datum`（:194、残差ゼロ）**: clock 2048 で `Restarted`/`StageEntry`/`CentreLongRun`/`NoReturn`/`EntryDepthG`/`D ≤ prepLen k` のみから（`readyPacedS_restarted` + `runEntriesS_of_namedG`）、**`ScanRealized`/`PostRunC`/`ScanSupplyInv` 不使用なので vacuous でない**。fuel は `dpEntryG k D`（0 では `not_runEntriesS_eight` で偽）。残 1 葉: `hshift`（`scan_shift` tick、`CloseoutPreload38` 進行中）。
- 進行中: `CloseoutPackRun41`（payload 残差）、`43`（死に場削除）、`CloseoutPreload38`、`CloseoutWatchRound43`（copy/back→watch）、`45`。
- **偽だった主張の訂正**: 「`LandingFreshC` は転送で閉じる」→ `h` の量化で偽、分割要。
- 残: pack `hSP`/`hws`/`Extra5` 化/`hplace`/`first ≠ 4`; readiness `hshift` + 帰納組立; watch `ReplayBornRoundC`/`ChainWatchReachC`/`PrepBirthLagC'`/`WatchDrainC'`/`ShiftPeriodC`/片 3–6 の L 版/tie/`RestartLandingDataC`; core debris 配線・有限制御。


## n65 (2026-09-18 夜) chain ブロック符号化 `chainRepD`（shift 1 手は ≤ 2 手）・replay 生まれ chain は 4 分割が使える

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound42`、`CloseoutCoreEnc24`、`CloseoutWatchRound41`）、sorry なし、build ログ `build_n65b.log` EXIT=0。
- **core**: `CloseoutCoreEnc24.chainRepD`（:221、watch chain を `mkChain` で: verifier `viewOfHead`、period テープ、6 カウンタ `lag/margin/h/distance/boundary/last` を `ctrTapeD`（`replicate n mark ++ [sep]` + 符号ビット `ctrPol`、`spare` = distance テープ））、`absChain_chainRepD_watch`（`Canonical` 下で忠実）、**`chainShiftBoundedD`**（:402、実際の上限は **≤ 2 手**、`chainTapes_shift`）、`restC_of_chainRepD`（`restC_of_rep` の形）。`chainShiftOne` が変えるのは `margin/distance/boundary/last` の 4 つだけで各 1 `dec`、コピーも改名も無し。**2 つの残差（いずれも証明不能、要契約修正）**: (1) `ChainShiftBounded chainRep` は `c` を `w` と独立に量化してて偽（実際に使う `c := .watch w` の形のみ真）、(2) debris 無しの関数的 `rep` は不可（mark を pop すると右に blank が残り、削除するマイクロ動作が無い）→ カウンタテープに debris 引数 `d` が要る（`dTape`/`dbg` と同機構）。`Lay`/`shiftVm_tapeActKQ_run` への `d` の配線は `CloseoutCoreEnc23` の編集が要る（次 wave）。
- **watch**: `CloseoutWatchRound42.liveChainRoundC_of_life`（残 `ReplayBornRoundC` + `ChainWatchReachC`）。**発見**: Round23 の 4 分割（`exitSplit4C_of_tick`）は replay 生まれの `.watch` 着地でも **found tick 無しで使える**（入力は `LiveScanWatch` と無条件の `WatchPrefixC` だけ）。found tick が要るのは route 消費側 —`roundsRouteLP_of_tail`/`breakRouteLP_of_tail` が食う `ShiftTailC`/`NoShiftTailC` の頭が「非 replay の found 比較 + `StageEntryC` からの `WatchSegE` + `InvLPC`」で、replay 生まれ chain（birth は `replaying = true` の found 量子、`ChainW` 起点）には偽。DP candidate は再供給可能だが `InvLPC`/stage 入口の根付けは不可 → `ReplayBornRoundC`（replay found 量子を頭にした `ShiftTailC` 類似）。`ChainWatchReachC`（copy/back → watch、機械的）は `CloseoutWatchRound43` 進行中。
- **watch (lag 0)**: `CloseoutWatchRound41`: 大域 `MismatchLandingLagZeroC` は偽なので消費側が実際に到達する着地に制限した `MismatchLandingLagZeroL`(:90) を `mismatchLandingLagZeroL_of_ctx`(:165) で放電、`shiftTailC_of_dataL'`(:215)、**`foundExit_compare_final16`**(:250、`hlag0` 消滅)。`R_f ≤ 2h` は仮定でなく導出（`StageEntryC.stage` → `ReplayStage` → `Restarted`/`StageEntry` → `found_radius_le_two_period`、`h` は `pos 11` で同定）。新たな文脈 3 葉: `PrepBirthLagC`(:115、`FoundCompareCtxC` に載せる)、`WatchDrainC`(:138、`PrepLandingLiveC`)、`LandingFreshC`(:151、`PrepLandingWatchC`) → `CloseoutWatchRound44` 進行中。
- 進行中: `CloseoutPackRun41`（payload 残差）、`42`（`Extra4` → final21）、`CloseoutPreload37`（fuel 付き `ReadyFieldP2`、`ScanRealized` 不使用で再実装）、`CloseoutWatchRound41`（lag 0、検証中）、`43`。
- 残: n64 と同じ + core の debris 引数配線。


## n64 (2026-09-18 夜) `Extra3.failed` は restart 着地で偽（stage 相対形へ）・readiness の消費先は `ReadyFieldP` と `hpres` だけ・replay 中に生まれた chain の round

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun39`、`CloseoutWatchRound40`）、sorry なし、build ログ `build_n64.log` EXIT=0。
- **pack（訂正）**: `CloseoutPackRun39.DpStage`/`DpFieldP`（scan で `parked`/`pc347`/`stage`、shift で `found`）、`dpField_to_failed`（scan 全状態で無条件）、`dpField_to_cand`（shift 状態で DP の成功 `Candidate`；`Extra3.cand` の形は **prefix/suffix の向き**の差 `H_candOrient` が要る）、`dpField_tick`（`init`/`scan_wait`/`scan_count`（parked search は不活性）閉、残 `hmatch`/`hshiftEntry`/`hshiftOne`/`hshiftDone`/`hreplayStart`/`hrestart`）。**`Extra3.failed` は restart 着地で偽**（`restartVM` が `dp := reset entry`、`pc = entry`；`hpres_false_at` と同型）→ `Extra3.failed` を「parked 後に failed」の stage 相対形に弱める必要。
- **readiness（配線の確定）**: scout の結果、readiness の消費先は `Extra3.ready`（`ReadyFieldP`、普遍 `SearchReady`）と `CycleOracleMC3` の `hpres`（`SearchReadyB`）のみ。`H_stageScan`/`H_bootShift`/`H_landShift` は readiness を読まん。普遍 `PostRunC`/`PostRunPh` は run 帰納から出んので、`postRunC_galil_of_boot` の run 限定 `DpSafeStage`/`EntryDatum` を `ReadyFieldP.hentry`（restart/replayStart 再入の `RunEntriesS`）に接続する（`CloseoutPreload37` 進行中）。
- **watch**: `CloseoutWatchRound40.chainRoundRouteC_of_life`（:131、残 `LiveChainRoundC`）、`chainW_shape`（`.copy ∨ .back ∨ .watch`）、着地から `LiveScanChain`/`OutputRel`/`Leftmost`/`ReplayLanding`/`SpanRep`/中心単調は導出。**発見**: 既存の split/経路（`exitSplit4C_of_tick`、`roundsRouteLP_of_tail`、`fallbackReachS_of_context`、`chain_life`）は全部 found tick 起点（`ShiftTailC`、`InvLPC` からの `foundRouteMC_*`、DP `Candidate` の `watchStart`）で、replay 中に生まれた chain（着地は `InvScan.chainIdle` を満たさん）には直接使えん → `ChainW` chain の copy/back → watch → shift/break の round（`CloseoutWatchRound42` 進行中）。
- 進行中: `CloseoutPackRun41`（payload 残差）、`CloseoutCoreEnc24`（`chainRep`）、`CloseoutWatchRound41`（lag 0 を found 半径予算から）、`42`、`CloseoutPreload37`。
- **偽だった主張の訂正**: 「`Extra3.failed`（`pc = 347`）は全 scan 状態で成立」→ restart 着地で偽。
- 残: n63 と同じ + `Extra3.failed` 弱化 + `H_candOrient` + `DpFieldP` の 6 分岐。


## n63 (2026-09-18 夜) `Coupled'`（sharp `5h`）で `H_fourOther` が定理・core 初期配置 + run 版・lag 0 は found 半径予算経由

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutCoreEnc23`、`CloseoutPackRun40`、`CloseoutWatchRound39`）、sorry なし、build ログ `build_n63b.log` EXIT=0。
- **pack**: `CloseoutPackRun40.Other'`（:56、`periodOnly ∧ 1 ≤ h ∧ (shift → 5h ≤ R+C+Rem) ∧ (¬shift → 5h ≤ R+C)`；shift 出口は `R = R₀+1, C = 0, Rem = h` で fresh guard `4h ≤ R₀` から `k ≤ 5` が上限）、`Coupled'`、**`coupled'_tick`（:127、全分岐無仮定）**、`coupled'_steps`、**`four_of_other'`**（`H_fourOther` の内容が定理）、`ChainPosInv'`、`watchShiftS_of_chainPosInv'`（`H_fourOther` 不要）、`chainPosInv'_tick`（残は Run34 の payload 3 残差のみ → `CloseoutPackRun41` 進行中）。
- **core**: `CloseoutCoreEnc23.laysS_initial`（空 queue で `SBound ∧ SInj ∧ LaysS ∧ RTQueue.Inv`）、`qLay_initial`（`InitialQueues m`）、`restC` は `rep` が未解釈なので `ChainShiftBounded rep`（:177）でしか縛れん（`CloseoutCoreEnc24` で `chainRep` を具体化中）、**`shiftVm_tapeActKQ_run`**（:284、run 添字の配置族 `lay i`/`dbg i`、各段 ≤ K=28、残 head margins）。`TapeActK` 本体（有限制御）は未。
- **watch**: `CloseoutWatchRound39`: `MismatchLandingLagZeroC` は大域では**偽**（`chainStart` が `lag = radius` を種にする; `R_f = 3069, h = 512` で pre-lag 1 の guard 通過着地、`budget_counterexample`）、実着地では真: `pre_lag_le_one`、`watchSegE_zero_lag`、`fresh_phase4_budget`（`4h ≤ R_now`）、`lag_zero_of_budget`（birth lag `R_f + m`、drain ≥ `2047·m' + d1`、prep `2048·m ≤ 2h+2`、**`R_f ≤ 2h`** ⇒ lag 0）、`landing_lag_zero_of_budget`（:182）。`RoundsL` 一般化（24 ファイル再移植）は却下、葉を found 半径上界入力形に（`CloseoutWatchRound41` 進行中）。
- 進行中: `CloseoutPackRun39`（DP 場）、`41`、`CloseoutCoreEnc24`、`CloseoutWatchRound40`（`ChainRoundRouteC`）、`41`、scout（readiness の消費先）。
- **偽だった主張の訂正**: 「live 着地で lag 0 は clock 構造だけから」→ found 半径予算 `R_f ≤ 2h` が要る。
- 残: n62 と同じ、pack は `ChainPosInv` payload 3 残差 + `ShiftLocalS` 再配線、core は `chainRep` + head margins + 有限制御。


## n62 (2026-09-18 夜) **モデル欠陥: chain 誕生で `periodOnly` が `false` に戻らん**（修正保留）・`H_shiftDone` 放電・readiness 帰納 `postRunC_galil_of_boot`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun37`、`CloseoutPreload36`）、sorry なし、build ログ `build_n62b.log` EXIT=0。
- **モデル欠陥（要修正、Scala が正本）**: Scala `chain.start()`（`ScaffoldChain.scala:90`）は `periodOnly = false` にするが、Lean の `chainAt`/`chainStart`（`GalilScaffoldTopChainVM.lean:41`、`GalilScaffoldTopSearch.lean:69`）は `s.periodOnly` を触らず、`restartVM`/`replayStartVM` も保持、`beginShiftVM` だけが `true` にする。結果: restart 後の fresh chain は stale `periodOnly = true` で走り、`shiftGuardVM`（`GalilScaffoldTopGuards.lean:27`、`if periodOnly then singlePositive cycle else negative margin = false`）が stale な cycle を見て **Scala なら許す shift を Lean が拒む**、`cycleAfter`（`GalilScaffoldTopSearch.lean:41–42`）も誤って減る。`Fair.keepsSearchCursor`（GalilTickFair:201）は init/replayStart しか pin しない。**最小修正**: `afterCompare`（`GalilScaffoldTopSearch.lean:47`）で chain 誕生（found = true）時に `periodOnly := false`。参照 99 ファイル、壊れやすい補題群: `*shiftGuard*`（9 ファイル）、`*Cycle*`/`cycleAfter`（~10）、`afterCompare`（~7）。**専用 wave で実施**（走行中 agent が古いモデル上なので、完走後に編集 → 全 build → 破損修復）。修正後は `chainRound_tick` の `H_birth` 分岐が vacuous になる。
- **pack**: `CloseoutPackRun37`: `ShiftInv`/`ShiftRound`（shift 相不変量）、`roundScan_of_shiftInv`（尽きたら `RoundScan (C+h) (R+h) h 0`、`terminal_palindrome` 経由、残差なし）、**`h_shiftDone_of_shiftRound`**（`H_shiftDone` 放電）、`shiftInv_entry`/`shiftInv_step`、`shiftRound_tick`（22 分岐、残 `H_advanceT`（終端 consume 後の予測、`mod 2h` 形）、`H_freshShift`（`periodOnly = false` での初回 shift、`GalilScaffoldTopFreshEntry`））。比較中に生まれた chain は phase 0 で guard の phase 4 と矛盾（`chainAt_false_born`）。`H_birth` は上記モデル欠陥そのもの。`ReadsInv`（origin `o`/`extra` で `w0.machine.control = run o.shifted.machine.control extra`）、`h_advance_of_readsInv`（`H_advance` を導出）、`readsInv_immediate`（`scan_match` 段）；残 `shift_done` での `ReadsInv` 入口と `H_advanceT`。
- **readiness**: `CloseoutPreload36.EntryDatum`（`.run` 入口 datum、DP 節不要）、`StageLegs`/`StageChain`、`entryDatum_step`、**`postRunC_galil_of_boot`**（:157、全後続入口で datum + `32 ≤ mw'` + `DpSafeStage`）、`postRunC_galil_of_initial`（`clockInv_initial`）。残: boot datum、`32 ≤ mw0`（`mw0 = 8·max k 1` なので `k ≥ 4`；`k ≤ 3` は最初の 1–2 stage が別扱い）、全流の pacing、stage ごとの供給前提、`RunEntriesS` の組立。**注意**: 普遍形 `PostRunC`/`PostRunPh` は全 `SearchVM` 上の量化なので run 帰納から出ず、`H_stageScan`/`H_bootShift`/`H_landShift` はどれも readiness を消費してへん → readiness の成果がどの最上位仮定に繋がるかを scout で確認中。
- 進行中: `CloseoutPackRun39`（DP 場）、`40`（`Other` 強化）、`CloseoutWatchRound39`（lag 0 判定）、`40`（`ChainRoundRouteC`）、`CloseoutCoreEnc23`（初期配置）、scout（readiness 消費先）。
- 残: n61 と同じ + モデル修正 wave。


## n61 (2026-09-18 夜) `ChainEnd` は「round 完了」でなく「生存」・`ChainPosInv` は残差 3 つ・`H_fourOther` は `WatchOK` から出ない

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound38`、`CloseoutPackRun38`）、sorry なし、build ログ `build_n61b.log` EXIT=0。
- **watch（訂正）**: `CloseoutWatchRound38.restartLandingC_of_landing`（:94、`InvLPC` は導出、残 `RestartLandingDataC`（`RadiusRep`/`SpanRep`/`Canonical`/`ReplayStage`/`CostedRun`/右上界；`BrokeAndRestarted` は pre-restart 状態としか結ばれず着地まで `WatchSegE` が届かん））、`chainEndLandingC_of_route`（:162、残 `ChainRoundRouteC`）。**訂正**: `ChainEnd`（GalilReplaySpan:1308）は chain が round を終えたのでなく span 末まで**生存**する（`t.chain ≠ .idle`、`ChainW … B`）。shift/break の場合分けは無く、`roundsRouteLP_of_tail`（`ShiftTailC` は found tick 状態上の契約）では供給できん → 生きた `ChainW` chain の round 経路（着地からのコスト込み）が要る。
- **pack**: `CloseoutPackRun38`: `posPayload_background`（残 `BgRes`: 元 verifier の `Sane`、chain 開始時の head 事実、1-tick 先読み `verNext`）、`posPayload_match`（`pos` は `ChainTick true` を通して閉、残 `MatchRes`: `SrcPos`/`saneR`/`canRNext`/`radNext`/`replayPay`/`verNext`）、`posPayload_shiftDone`（残差 = shift モード状態での payload そのもの、`ChainPosInv` は shift を跨がん → `shift_one` を通す shift モード payload が要る）。**`H_fourOther` は `WatchOK` の帰結でない**（`other_guard_lower`: `2h−1 ≤ distance` が sharp、`R = 2h−1, C = 1` が `Other`+guard を満たす）。機械では未到達の見込み（fresh guard `R ≥ 4h` → shift `−h` → countdown `C: 0→2h→1`、match 中 `R+C` 一定で実 guard は `R ≥ 5h−1`）→ `Other` の `2h` を強めて shift 出口補題を再証明（`CloseoutPackRun40` 進行中）。
- 進行中: `CloseoutPackRun37`（`ChainRound` 誕生）、`39`（`Extra3.cand/failed` の DP 場）、`40`、`CloseoutPreload36`（`PostRunC` 帰納）、`CloseoutWatchRound39`（lag 0 判定）、`CloseoutCoreEnc23`（初期配置・`restC`）。
- **偽だった主張の訂正**: 「`ChainEnd` = chain の round 完了」→ 生存。「`4h ≤ distance` は `WatchOK.Other` から」→ 出ない。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 3 残差 + `Other` 強化 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness 帰納組立 + 小窓; watch lag 0 判定 + 片 3–6 の L 版 + tie + `RestartLandingDataC`/`ChainRoundRouteC` + `FallbackCostInputsC`/`RegionBudgetC` + 家族 1–3 の `ShiftRoundAtC`; core 初期配置・`restC`・有限制御。


## n60 (2026-09-18 夜) readiness 帰納段 `postRunF_step` 成立（`32 ≤ mw`）・`ReplayRunW` 無条件・`take` 経路は `Rounds` に乗らん

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound36`、`CloseoutWatchRound37`、`CloseoutPreload35`）、sorry なし、build ログ `build_n60c.log` EXIT=0。
- **readiness**: `CloseoutPreload35.dpSafe_of_stagePrepD_slack`（:145、`StagePrepS … slack`、`StageInvS`/`dpDemandS`（`dpDemand + 2` 以下））、`postRunF_round_trip_galil_S`（:301、残 **`32 ≤ mw`**: 追加 2 単位のコスト 8 が slack 2047 で `8 ≤ mw < 32` では吸収できん）、`postRunF_next_entry`（:419、dispatch → prep 脚 → 次 `.run` 入口で frame・`Canonical`・`DpSafeStage`・拡張 `ScanTrace`）、**`postRunF_step`**（:502、`.run` 入口 → 次 `.run` 入口、全脚 `IdleLeg`、`idleLeg_doubleTrace`/`doubleTrace_det`）。残: 帰納の組み立て（boot datum + step → `PostRunPh` → `PostRunC` on `galilFrameS`、`CloseoutPreload36` 進行中）、`RunEntriesS` の wait/double/prep 脚（入口 tick 以外 vacuous）、小窓 `k < 4`。
- **watch**: `CloseoutWatchRound36.ReplayRunW`（:75、replay run / `ChainEnd` / `BrokeAndRestarted` の 3 形）、`replayRunW_of_decodes`（:99、**`ReplayOutC`/`ReplayNoBusyC` 不要**）、`fallbackReachS_of_context'`（`watchFallbackCostC_of_context`/`ReplayRunC` 不要に）、`foundExit_compare_final15`（:246、残 `ChainEndLandingC`（Round15 `roundsRouteLP_of_tail` で供給）・`RestartLandingC`（`invLP_of_landing_replay` + restart 形）、`CloseoutWatchRound38` 進行中）。`CloseoutWatchRound37`: **`ShiftTailC`/`roundsRouteLP_of_tail`/`Rounds.next` は単一 `w` を束縛**するので `take` 経路（`w' ≠ w`）は `Rounds` に乗らん → `MismatchLandingLagZeroC`（:112、live な不一致 shift 着地で lag 0）が新葉、または `Rounds.next` を `Internal w w'` に一般化（`CloseoutWatchRound39` で判定中）。`ShiftRoundInvCL`/`ShiftOriginRestCL`、`shiftBreakRunCL_of_tail`、`shiftOriginCL_of_ctx`、`mismatchShiftRouteL_of_tick`、Round37 版 `foundExit_compare_final15`（:303、仮定: `μ`、`ShiftCopyIdleC`、`ShiftRunCL`、`ShiftRoundInvCL`、`∀h ShiftBreakOracleC`、`∀h ShiftBreakFitC`、`ShiftOriginRestCL`、`MismatchClassifierTieC`、`MismatchLandingLagZeroC`；`ShiftRoundAtC` は家族 1–3 用に残る）。
- 進行中: `CloseoutPackRun37`（`ChainRound` 誕生）、`38`（`ChainPosInv` 残分岐）、`CloseoutPreload36`、`CloseoutWatchRound38`、`39`。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 4 葉 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness 帰納組立 + 小窓; watch lag 0 判定 + 片 3–6 の L 版 + tie + `ChainEndLandingC`/`RestartLandingC` + `FallbackCostInputsC`/`RegionBudgetC` + 家族 1–3 の `ShiftRoundAtC`; core 初期配置・`restC`・有限制御。


## n59 (2026-09-18 夕) `pal_in_peg_final20`（`BigResid6G`/`H_packOnRunG`/trace 葉が消滅、pack 残は `hSP`+`hws`）・`ShiftLagZeroC` 反証→`ShiftRoundDataL`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound33`、`CloseoutPackRun36`）、sorry なし、build ログ `build_n59b.log` EXIT=0。
- **pack**: `CloseoutPackRun36.IPackMG2`（:73）= `IPackMG ∧ LPackM2`。`lticksN_of_lpackM2_pt`（:90、`LTickLeavesN` は `BigPack2MG x + LPackM2 x` から**点ごとに**出るので葉でない）、`lTickLeaves2_of_shiftPalG`、`bigPack2MG2''_tick`（rewind-on-FIRST は `replayStart` 着地の `LPackM2` を直接）、§2 trace 層（Run30 §3 の写し）、`h_trailI_MG2`、`H_realizeLIMG2'`（`H_realizeLIMG'` より弱い）、`lpackM2_of_invLPC`、`packRunR_MG2`、`cycleOracleIMG2_of_cycleOracleMC3R`、**`pal_in_peg_final20`**（:712）。仮定: `hSP : ∀ w x, BigPack2MG2 … x → ScanNR x → ShiftPal w x.vm`、`hws : WatchShiftG`、`H_extraEntry3/Tick3`、`H_marksEntry'`、`H_shiftLocalG`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIMG2'`。`hSP` は `ChainRound`（Run31、`CloseoutPackRun37` 進行中）、`hws` は `ChainPosInv`（Run34、`CloseoutPackRun38` 進行中）+ `ShiftLocalS` 再配線が供給元。
- **watch（訂正）**: `CloseoutWatchRound33`: `ShiftLagZeroC` は**偽**（`w.lag = 1` の `Internal.take` で `caught w` が lag 0 で着地し guard を通る；`backDone` で lag が溜まり background tick で 1 ずつ減るので clock 2 で lag 1 → clock-1 compare で lag 1 は到達可能）。`compare_of_take`、`not_shiftLagZeroC`（そういう状態の存在を仮定）、修正データ **`ShiftRoundDataL`**（:129、pre `w`/post `w'`、`Internal w w' ∧ vs.chain = .watch w'`、guard/`beginShiftVM h w'` は `w'` 上）。Round7 の `ShiftRoundData`（従って Round30 `ShiftRoundAtC'`、`ShiftTailC` の旧形）は `take` 経路で到達不能。`ShiftPeriodC` は `h` が消費側（`ShiftTailC`）で存在量化なので `h := periodLength w'` を選べて消滅。`ShiftRoundAtCL'`（:200）、`shiftRoundAtCL_of_tick`（:283、片 3–6 のみ: `ShiftCopyIdleC`、`ShiftRunCL`、`ShiftOriginCL`、`ShiftBreakRunCL`）。`CloseoutWatchRound37`（`ShiftRoundDataL` → `ShiftTailC` → final15）進行中。
- 進行中: `CloseoutPackRun37`、`38`、`CloseoutPreload35`（stage 継続）、`CloseoutWatchRound36`（`ReplayRunW`）、`37`。
- **偽だった主張の訂正**: 「clock-1 不一致で lag は 0」→ 偽（lag 1 の `take`）。
- 残: pack `hSP`（`ChainRound` 4 葉）+ `hws`（`ChainPosInv` 4 葉 + `ShiftLocalS` 再配線）+ `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness prepare 継続; watch 片 3–6 の L 版 + tie + `ReplayRunW` + `FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n58 (2026-09-18 夕) `ShiftPal` は `RoundScan` から（`ReadOrigin` 不要）・`WatchShiftS`/`ShiftLocalS` 再切り出し・break run の iteration 構成

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound34`、`CloseoutPackRun31`、`CloseoutPackRun34`）、sorry なし、build ログ `build_n58.log` EXIT=0。
- **pack (`ShiftPal`)**: `CloseoutPackRun31.ChainRound`（:183、watching chain ⇒ `GalilRoundPeriod.RoundScan w C R (periodLength wch) used s wch`、`ReadOrigin` の中身は既にループ不変量に還元済み）、`terminal_palindrome`（:134、終端 `RoundScan` + `canRight` + 予測 = 右記号 ⇒ `PalAt (C+2h) (R+1)`、C と C+h の 2 回鏡映 + `reshift_from_right`）、`shiftPal_of_readOrigin`（:265、`ChainRound` + `WatchShift`（`canRight` のみ使用））。`chainRound_tick`（:340）: init/restart/replayStart・非 scan・`scan_wait/count`（lag 0 の `Internal` は恒等）・`scan_match` 非終端（`roundScan_step`）・終端（chain は `Good` でなく破れる）閉。残: `H_shiftDone`（shift 出口での次 round の誕生 = 本体）、`H_advance`（`roundScan_step` 自身の名前付き仮定、round の `Reads` trace 要）、`H_birth`/`H_fresh`（fresh chain データ；`periodOnly` は `restartVM` でも `false` に戻らんので restart 後の fresh chain は `H_birth` 側）、`H_matched`（matched 目標での `ShiftPal` は導出不能だが `shiftEntry_of_guard` は `¬matched` しか使わん）。`CloseoutPackRun37` 進行中。
- **pack (`WatchShiftS`)**: `CloseoutPackRun34`: `WatchShiftS`（:60、`¬matched ∧ shiftGuardVM` 付き payload）。**消費側は `beginShiftVM'` 目標で guard なしに `ShiftLocalG` を読む**（`halfBound_of_ipackMG`、`shiftVerSane_ptMG`；`beginShiftVM'` は `shiftGuardVM` を含意せん）→ `ShiftLocalS`（:82、全場に `¬matched ∧ shiftGuardVM`）、`shiftLocalS_of_watchShiftS`、`RShiftNextMS`、読み手の再切り出し `halfBound_of_shiftLocalS`/`shiftOrd_tickS`（`scan_shift` は `hmt`/`hg` を持つ）。`PosPayload`（:313）+ `ChainPosInv`（:330、`Coupled` の `sum` が `distance + lag = radius`）、`four_of_freshC`（phase 4 + `FreshC` ⇒ `4h ≤ distance`）、`watchShiftS_of_chainPosInv`（:364）、`chainPosInv_tick`（20/23）。残: `H_fourOther`（post-shift `Other` 半分での `4h ≤ distance`、`guard_budget` は `h ≤ R+1` のみ）、`H_bgP`/`H_matchP`/`H_shiftDoneP`（`CloseoutPackRun38` 進行中）。次: `IPackMG` を `ShiftLocalS` で再々配線（Run30 の鏡像）。
- **watch**: `CloseoutWatchRound34`: 片 6 `shiftBreakRunC_of_tail`: 「欠落 iteration」`rounds_construct_break`（:67、`rounds_construct_of_measure` を `BreakEnd` に制限）を無条件で構成、`BreakEnd` から refresh・broken chain・3 カウンタ（`rounds_break` + `RoundInv.Entry` + `read center ≠ none`）。残 `ShiftRoundInvC`（post-shift 状態の `RoundInv h raw`）、`ShiftBreakOracleC`（`BreakEnd` か測度減少の 1 round、`InputEnd`/`GuardFail` の除外点）、`ShiftBreakFitC`（head 上界 `≤ 2m−1`、Round11 の `hfit`）。片 5 `shiftOriginC_of_ctx`: `RoundInv` から `org`/`Entry` 転送、残 `ShiftOriginRestC`（`org.center = pos sF.center`、`Aligned`（fresh origin、`shifts = 0`）、`pos 11 = h`、period 下界の `HasPeriod (Span …)` 形）。
- 進行中: `CloseoutPackRun36`（`IPackMG2`）、`37`、`38`、`CloseoutPreload35`（stage 継続）、`CloseoutWatchRound33`（lag/period）、`36`（`ReplayRunW`）。
- 残: pack `IPackMG2`/`ShiftLocalS` 再配線 + `ChainRound` 4 葉 + `ChainPosInv` 4 葉 + `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness prepare 継続; watch 片 1/2 + `ShiftRoundInvC`/`ShiftBreakOracleC`/`ShiftBreakFitC`/`ShiftOriginRestC` + tie + `ReplayRunW` + `FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n57 (2026-09-18 夕) readiness 往復が `galilFrameS` 上で自前仮定のみに・`ReplayNoBusyC` は偽（replay 中も chain は始まる）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPreload34`、`CloseoutWatchRound35`）、sorry なし、build ログ `build_n57b.log` EXIT=0。
- **readiness**: `CloseoutPreload34.exitNotFire_of_wait`（:163）: wait 脚が空でなければ最後の tick は `true`（`idleLeg_wait_last`）で clock := 2048（`scanTrace_single_true_clock`）、空なら run 出口 tick 自体が fire（`run_exit_wait_match`: `finish` は `zero debt = false` でしか `.wait` に入らん）。**`postRunF_round_trip_galil'`**（:199）: `.run→.wait→.double→dispatch` が `galilFrameS` 上で往復の自前仮定のみ。次: `prepare → 次 .run 入口`（`dpSafe_of_stagePrepD` を slack 2047 で言い直し、`PostRunF` datum の再成立 = 帰納段、`CloseoutPreload35` 進行中）。
- **watch（訂正）**: `CloseoutWatchRound35.replayOutC_of_landing`（:61、無条件: `ReplayLanding.rest` の半径 0 `ScanInvariant` + `watchSegE_right_position/center` で `count true = R > 0`、`watchSegE_outputM`）。**`ReplayNoBusyC` は一般に偽**: shift は replay 中無効（Scala `ScaffoldGalil.scala:270`、Lean `scan_shift.hr`）だが、watch chain は found 量子で `chain.start()`（Scala `:226-228`、Lean `compareFound`/`backgroundS` の `chainAt … (mode = .found)`）に `replaying` guard がなく、replay 中に chain が始まる。Lean/Scala の乖離ではない。`ReplayNoShiftC`（:85、replay 中の tick は scan に留まる）は無条件。→ `replayRunC_of_decodes` は replay 定理の 3 分岐（replay run / `ChainEnd` / `BrokeAndRestarted`）全部を消費する形に（`ReplayRunW`、`CloseoutWatchRound36` 進行中）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`36`（`IPackMG2`）、`CloseoutPreload35`、`CloseoutWatchRound33`（lag/period）、`34`（片 5/6）、`36`。
- **偽だった主張の訂正**: 「replay 中は chain が始まらん（`ReplayNoBusyC`）」→ 偽。
- 残: n56 と同じ、readiness は prepare 継続のみ、watch は `ReplayRunW` + 片 1/2/5/6 + tie + `FallbackCostInputsC`/`RegionBudgetC`。


## n56 (2026-09-18 午後) R>0 の watch fallback は存在（`ReplayedLandingRestartC` 反証）→ `FoundExitLPS`・`final14`・`final19`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutWatchRound32`、`CloseoutWatchRound31`、`CloseoutPackRun35`）、sorry なし、build ログ `build_n56c.log` EXIT=0。
- **watch（訂正）**: `CloseoutWatchRound31`: 判定 (B)。`chosenRadius` は右ヘッドで終わる最長奇回文で chain と無関係、Scala は watch 中 `canShift ∧ prediction == right.read()` が破れたら常に fallback → 反例 `c·(abb)^8·a` + `a`（chain h=3 phase 4、予測 `b ≠ a`、encoded 接尾辞 `a#a` で R=1）。`replayedLanding_not_restart`（:180、R>0 着地 + `ReplayRun` + `LandingRestart` → False、`Rad = R`、`last = reset` で `3R ≤ 0`）、`replayedLandingRestartC_iff`。代わりに **`FoundExitLPS`**（:230、`InvLPS` 着地 + 中心前進）、`cycleOutMC3_of_foundExitLPS`（`cycleOutMC3_of_centre` で消費可）、`FallbackReachS`/`fallbackReachS_of_context`（R>0 枝は `InvLPS`: `InvLP` + `CopyPack` + `CentreRep` + `ReplayStage`）、**`foundExit_compare_final14`**（:377、着地側の仮定なし）、`_of_context`。残る上流: `WatchMismatchNoShiftC`（Round23 で放電済）、`EntryCostC`（Round26 閉）、`FallbackCostPieceC`/`ReplayRunC`（Round28: `FallbackCostInputsC`/`RegionBudgetC`/`ReplayOutC`/`ReplayNoBusyC`、`CloseoutWatchRound35` 進行中）。`CloseoutWatchRound32`: 片 1 は tick から出ない（`watch_after_compare`: lag 正なら `Internal.take` で `caught w`）→ `ShiftLagZeroC`；片 2 は `h` が外部固定 → `ShiftPeriodC`；片 3 `shiftCopyIdleC_of_copyPack`、片 4 `shiftRunC_of_scanInv`（`ShiftScanInvC`）。`CloseoutWatchRound33`（lag/period）・`34`（片 5/6）進行中。
- **pack**: `CloseoutPackRun35.lpackM2_at_traceG`（trace 上の `LPackM2`、`TraceLeaves = LTickLeavesN ∧ AuxPack ∧ ShiftPal`）、`pal_in_peg_final19`（:114、`hall` → `hLv` + `H_packOnRunG`）。**`H_packOnRunG` は循環**（pack 状態は `CycleOracleIMG` の任意 `InvLPC` 起点の run、trace はそこから作る）→ 非循環案 `IPackMG2 := IPackMG ∧ LPackM2` を run pack に持ち込む再配線（`CloseoutPackRun36` 進行中、final20）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`36`、`CloseoutPreload34`（`H_exitNotFire`）、`CloseoutWatchRound33/34/35`。
- **偽だった主張の訂正**: 「watch 不一致からの fallback は R=0」→ 偽（R>0 あり）。「`hall` は trace 限定で消える」→ 循環。
- 残: pack `IPackMG2` 再配線 + `ShiftPal` + `WatchShiftS` + `hplace` + `hentry` + `Extra3.cand,failed` + `first ≠ 4`; readiness `H_exitNotFire` + prepare 継続; watch 片 1/2/5/6 + tie + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n55 (2026-09-18 午後) `pal_in_peg_final18`（`BigResid6G` 消滅）・`LegsCoupled` 放電・`WalkerInOrigin` 全分岐保存

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutPackRun32`、`CloseoutPreload33`、`CloseoutPackRun33`、`CloseoutPackRun28`）、sorry なし、build ログ `build_n55c.log` EXIT=0。
- **pack**: `CloseoutPackRun33.bigResid6G_of_lpackM2`（:101、5 契約を `BigPack2MG` 上で同じスクリプトで再証明、どれも `ShiftLocal.mode` を読まん）、**`pal_in_peg_final18`**（:126）。仮定: `hall : ∀ w x, BigPack2MG … x → LPackM2 w x.ctl x.vm`、`hws : ∀ w y, WatchShiftG …`、`H_extraEntry3/Tick3`、`H_marksEntry'`、`H_shiftLocalG`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIMG'`。`hall` は trace 状態への限定で消せる見込み（`CloseoutPackRun35` 進行中）。`CloseoutPackRun32`: `ChainScanInv`/`chainScanInv_tick`（19/23）、`WatchShiftG` は無ガード目標で偽（`backDone` 直後 distance = 0）→ `shiftGuardVM` 目標に限定した `WatchShiftS` + 位置不変量 `ChainPosInv`（`CloseoutPackRun34` 進行中）。`CloseoutPackRun28`: `WalkerInv`（init/Bounded/Fresh の 3 相、`replayStart` は R を左へ動かすので `Fresh` 相が要る）、`walkerInv_tick`（全 26 分岐）、`walkerInv_of_fair`、**`walkerInOrigin_of_run`**（`wpack_of_fair` の `hwalk` そのもの）。残: `hplace : |stream (place s)| ≤ pos R`（`placeC` なら `C ≤ R`）、`2 ≤ delay`（2048 で真）、replaying 中の `canRight R`。
- **readiness**: `CloseoutPreload33.legsCoupled_galil`（:240）: `IdleLeg`（chain idle・search mode 付き 1-tick `ScanTrace` の列）、`scanTrace_single_searchStep`（per-tick 結合、`tick_scan_cases`）、`idleLeg_runTrace`/`idleLeg_waitTrace`、`scanTrace_append`、`RestartOnBroken`（`sharedC` で放電）。`postRunF_round_trip_galil`（:267、4 脚の `SearchVM` は `searchLens.get` で導出）。残 **`H_exitNotFire : p3.ctl.clock ≠ 1`** 1 つ（`CloseoutPreload34` 進行中）。
- 進行中: `CloseoutPackRun31`（`ShiftPal`）、`34`（`WatchShiftS`）、`35`（`hall` → final19）、`CloseoutPreload34`、`CloseoutWatchRound31`（R>0 判定）、`32`（`ShiftRoundAtC'` 片 1–4）。
- 残: pack `hall`/`ShiftPal`/`WatchShiftS`/`hplace`/`hentry`/`Extra3.cand,failed`/`first ≠ 4`; readiness `H_exitNotFire` + prepare 継続; watch 6 片 + tie + R>0 + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n54 (2026-09-18 午後) `pal_in_peg_final17`（ガード付き `IPackMG` で全層再配線、追加ガード不要）・`ShiftRoundAtC'` producer 骨格

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound30`、`CloseoutPackRun30`）、sorry なし、build ログ `build_n54b.log` EXIT=0。
- **pack**: `CloseoutPackRun30`: `IPackMG`（`shift : ShiftLocalG`）、`BigPack2MG`/`BigPack2MG''`、`BigResid6G`（5 契約は `BigPack2MG` 上、`rShiftNext : RShiftNextMG` は `∀ y, WatchShiftG y` で閉）、`lpackN_tickG`、`bigPack2MG''_tick`、`packRunR_MG`、trace 層 `StepsIMG/ReachAtIMG/CycleOutIMG/CycleOracleIMG/PreTraceIMG`、trail `halfBound_of_ipackMG`（`ScanNR` 付き）・`shiftOrd_ptG`/`verSane_ptG`・`h_trailI_MG`、`H_realizeLIMG'`、**`pal_in_peg_final17`**（:848）。仮定: `BigResid6G`, `H_extraEntry3/Tick3`, `H_marksEntry'`, `H_shiftLocalG`, `H_stageScan`, `CycleOracleMC3`, `H_bootShift`, `H_landShift`, `H_realizeLIMG'`。`.shift.*` を非 scan 状態で読む trace 補題は無い。`BigResid6G` は `BigResid6` から出ない → `bigResid6G_of_lpackM2`（`CloseoutPackRun33` 進行中）。
- **pack (`WatchShiftG`)**: `CloseoutPackRun32`（未登録、次 build）: `ChainScanInv`（一歩先の watch に対する `WatchPayload`）、`watchShiftG_of_chainScanInv`、`chainScanInv_tick`（19/23 閉、残 `H_bg`/`H_match`/`H_shiftDone`）。**発見**: `WatchShiftG` は無ガードの目標で偽（`backDone` で生まれた watch は distance = reset = 0 なので次の比較で `4h ≤ distance` が破れる）→ payload を `shiftGuardVM` 目標（phase 4, lag 0）に限定する再切り出しが要る。その上で位置不変量（`distance + lag = radius`、verifier = `pos right − lag`）。
- **watch**: `CloseoutWatchRound30.ShiftRoundAtC'`（:75、トリガー = frame の compare での post-compare guard）、`shiftRoundAtC'_of_tick`（:170、6 片: `ShiftChainStableC`（`ShiftRoundData` が post-tick chain を `w` のまま束縛する設計問題）、`ShiftPeriodC`、`ShiftCopyIdleC`、`ShiftRunC`、`ShiftOriginC`、`ShiftBreakRunC`）、`mismatchShiftRouteC'_of_shiftRoundAtC'`（残 `MismatchClassifierTieC`）、`foundExit_compare_final13'`。`CloseoutWatchRound32`（片 1–4）進行中。
- 進行中: `CloseoutPackRun28`（`WalkerInOrigin`、コンパイル待ち）、`31`（`ShiftPal`）、`33`、`CloseoutPreload33`（`LegsCoupled`）、`CloseoutWatchRound31`（R>0 判定）、`32`。
- **偽だった主張の訂正**: 「`WatchShift(G)` は無条件で全 compare 目標に成立」→ `backDone` 直後で偽、`shiftGuardVM` 目標に限定要。
- 残: pack `BigResid6G` 組立 + `ShiftPal` + `WatchShiftG` 再切り出し + `WalkerInOrigin` + `hentry` + `Extra3.cand/failed` + `first ≠ 4`; readiness `LegsCoupled` + prepare 継続; watch 6 片 + tie + R>0 + replay/cost 4 葉; core 初期配置・`restC`・有限制御。


## n53 (2026-09-18 午後) `BigResid6` は `LPackM2`-on-pack + `WatchShift` だけで組めた

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun29`）、sorry なし、build ログ `build_n53.log` EXIT=0。
- **pack**: `CloseoutPackRun29.bigResid6_of_lpackM2`（:143）: `BigResid6` を `∀ x, BigPack2M x → LPackM2 …` と `∀ y, WatchShift y` のみから（Run19/20/21/23/24 の断片を合成）。`shiftEntry_of_guard`（:94）: `ShiftGeom` の heads/`Sane`/positions/`remaining` は pack から、回文本体は `ShiftPal`（:82、`1 ≤ h ≤ r₀+1 ∧ PalAt (pos C + h) (r₀+1−h)`、`reshift_palindrome` の中身だが `ReadOrigin`/`OnlyScan`/`Trace` の round データが要る）1 葉；`lTickLeaves2_of_shiftPal`。`lpackM2_on_pack_of_run`（:171）は葉の毎状態成立と `H_packOnRun`（`BigPack2M` 状態は run 上のどれかの `st i`）を要る；`bigResid6_of_run`。
- 進行中: `CloseoutPackRun28`（`WalkerInOrigin`）、`30`（`IPackMG` 再配線 → final17）、`31`（`ShiftPal` via `ChainRound`）、`32`（`WatchShiftG` via `ChainScanInv`）、`CloseoutPreload33`（`LegsCoupled` on `galilFrameS`）、`CloseoutWatchRound30`（`ShiftRoundAtC'` producer）、`31`（R>0 fallback 判定）。
- 残: n52 と同じ、pack は `ShiftPal` + `WatchShift(G)` + `H_packOnRun` + `IPackMG`。


## n52 (2026-09-18 午後) **訂正: `ShiftLocal` は shift 着地で偽**（`ShiftLocalG` へ）・`final13`（`hLR` 消滅）・`Canonical` 閉・`ReplayRunC`/`FallbackCostPieceC`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 5 本登録（`CloseoutPackRun26/27`、`CloseoutWatchRound28/29`、`CloseoutPreload32`）、sorry なし、build ログ `build_n52b.log` EXIT=0。429 で落ちた 8 agent は SendMessage で再開して全部完走。
- **pack（訂正）**: `CloseoutPackRun26`: `ShiftLocal` は**反証**。全 `scan→shift` tick は chain `.watch (immediate w)`, `zero w.lag` で着地し（`shift_landing`）`Internal.idle` が有効（`internal_enabled_at_landing`）、heads 不一致なら `afterMismatch` が `compareFound` 目標でその watch を保つ（`compare_watch_target`）ので `ShiftLocal.mode` は偽（`shiftLocal_false_at_landing` :148、pack 仮定なし）、`watchShift_false_at_landing`。修正: `ShiftLocalG`（:197、4 場を `ScanNR := mode = scan ∧ replaying = false` でガード、`mode` 場は削除）、`WatchShiftG`、`rShiftNextG_of_pack`、`RShiftNextG`、橋 `shiftLocal_of_shiftLocalG`/`h_shiftLocalC_of_G`、ガード付き tick 複製 `shiftOrd_tickG`/`saneTickG`。**`pal_in_peg_final16`**（:523）: `hsl : H_shiftLocalG`（他は final15 と同一）。ただし `BigResid6.rShiftNext` は未ガードのまま（`IPackM.shift : ShiftLocal` が `StepsIM/ReachAtIM/CycleOracleIM/PreTraceIM`（Run10/12/14/18）と `shiftEntry_ptM/shiftVerSane_ptM/halfBound_of_ipackM` に直結）→ `IPackMG` 再配線を `CloseoutPackRun30` で進行中。`CloseoutPackRun27`: `ReadyFieldP`（`ready` + chain idle 時の `ReadyPacedS … 0 (2048−clock)`、slack はクロックが補充）、`readyField_tick`（`scan_wait/count/match`、`init` 閉）、残 `hentry`（`restart`/`replayStart`/`shift_done` 再入で `RunEntriesS` = `readyPacedS_restarted` の `hE`、**readiness との接続点**）。
- **watch**: `CloseoutWatchRound29`: `LandingRestartReachF`（fallback 枝のみ）、`landingRestartReach_fallback`（R=0 無条件）、消費側の `hLR` 依存は fallback 枝のみと確認、**`foundExit_compare_final13`**（:264、`hfb`+`hLR` → `hfbF`）。残 `ReplayedLandingRestartC`（R>0 の post-replay 着地は `InvScan` で `Restarted` は `3R ≤ 0` を強制 → 怪しい；`CloseoutWatchRound31` で R=0 か `FoundExitLPS` かを判定中）。`CloseoutWatchRound28`: `replayRunC_of_decodes`（残 `ReplayOutC`（replay 着地の `OutputRel`）、`ReplayNoBusyC`（`¬ChainEnd ∧ ¬BrokeAndRestarted`、replay 中の found tick が chain を生むので着地データでは除外不能））、`fallbackCostPieceC_of_inputs`（`costedRun_fallback_replay` を R 一様に、残 `FallbackCostInputsC`（供給元: `FoundCompareCtxC`/`fallback_landing_len_le`/`PrepInputsG3`/`MismatchDp`/replay 分岐 1）、`RegionBudgetC`（`GalilOracleMC4` の `≤ 2m−2`）、`1 ≤ m`）。`CloseoutWatchRound30`（`ShiftRoundAtC'` producer）進行中。
- **readiness**: `CloseoutPreload32`: `canonical_runTrace`/`canonical_waitTrace` 閉（`safeCalls_debt` + `dec_canonical`）、`postRunF_round_trip'`（:143、残 `LegsCoupled` :117 = `a2 = false ∧ ScanTrace` の 4 脚延長；generic frame では `State σ → SearchVM` がないので `galilFrameS` 上の per-tick 結合 `background_event_false`/`compare_event_false_of_mismatch` からしか出ない → `CloseoutPreload33` 進行中）。
- **compact 前の agent の完走**: `GalilLeafDp`（`hdp` の ∀ 形は反証、`StageFailed` へ；登録済み）、`CloseoutCoreStep`（M3、登録済み）。
- **偽だった主張の訂正**: 「`ShiftLocal`（`mode = scan` 場付き）は tick で保存される」→ shift 着地で偽。「`ReplayedLandingRestartC` は着地から出る」→ R>0 では `3R ≤ 0` を強制、要判定。
- 残: pack `IPackMG` 再配線 + `shiftEntry` + `WalkerInOrigin` + `hentry` + `Extra3.cand/failed` + `first ≠ 4`; readiness `LegsCoupled` + prepare 継続; watch `ShiftRoundData` producer + `ReplayedLandingRestartC` 判定 + `ReplayOutC`/`ReplayNoBusyC`/`FallbackCostInputsC`/`RegionBudgetC`; core 初期配置・`restC`・有限制御。


## n51 (2026-09-18 未明) `LPackM2` で `BigResid6` の 4 契約が閉（shift 入口 1 葉）・`PostRunF` 往復・`EntryCostC` 閉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutWatchRound26`、`CloseoutPreload31`、`CloseoutPackRun23`、`CloseoutWatchRound27`）、sorry なし、build ログ `build_n51c.log` EXIT=0。
- **pack**: `CloseoutPackRun23.LPackM2`（:99）= `LPackM` + `scanGeomR` + `shiftGeom`（`ShiftGeom` :87、round 進行中の幾何: `remaining = ofNat rem`、目的中心 `pos C + rem` 相対の heads、`PalAt`）+ `rrep`（`OffScan` モード shift…choose）+ `centreRep`（rewind ∨ replayStart）+ `centreOrder`（rewind で `pos L ≤ pos C`）。`lpackM2_tick`（:173、全 23 分岐、`LPackM` 半分は `lpackN_tick` 再利用）: `scanGeomR`/`rrep`/`centreRep`/`centreOrder` は全 tick **無条件**、`shiftGeom` は `shift_one`/出口閉、**唯一の葉 `LTickLeaves2.shiftEntry`**（:150、`scan_shift` 着地での `ShiftGeom` = `reshift_palindrome` at 中心 `pos C + periodLength`、半径 `radius+1−periodLength`）。`lpackM2_boot`（無条件）、`lpackM2_steps`。契約: `scanGeomReplay_of_lpackM2`/`shiftDoneGeom_of_lpackM2`/`rrepChoose_of_lpackM2`/`centreReplay_of_lpackM2`（:447–470）で `H_scanGeomReplay`/`H_shiftDoneGeom`/`RRepChoose`/`H_centreReplay` 全放電。→ `BigResid6` は `LPackM2`-on-pack + `WatchShift` + `shiftEntry` に（`CloseoutPackRun29` で組み立て中）。
- **readiness**: `CloseoutPreload31.PostRunF`（:64、`PostRunPh` + `.run` 入口 frame + 到達可能 `ScanTrace` 位相節、`ScanRealized` なし）、`postRunF_of_postRunPh`、**`postRunF_round_trip`**（:110、`.run→.wait→.double→dispatch` で `PrepAt ∧ StageInvD ∧ walker = c' ∧ 8·max k 1 ≤ 2mw`、`hbal` 導出済み）。残: `hsc`（run+wait 脚上の `ScanTrace` 延長、機械事実）、`hs2`（wait 出口 tick は false）、`hcan1/hcan0`（`Canonical` 保存）→ `CloseoutPreload32` 進行中。`postRunC_of_postRunF` は不成立（`PostRunC` の `.run` 状態に frame がない）。続き: `prepare → 次 .run 入口`（`StagePrep2` の `PacedL 2048 0` を slack 2047 で言い直す）。
- **watch**: `CloseoutWatchRound26.entryCostC_of_ctx`（:44）: `EntryCostC` 閉（`FoundCompareCtxC` + 入口の `EntryCounters`/`OutputRel`/`clock ≤ 2048`）。`CloseoutWatchRound27`: `¬MismatchGuardFails` の witness `vs` は `vs.right` が自由で `compare_scan_unique` に結べん → frame の compare で量化する `MismatchGuardFailsC`（:79）、`guard_of_mismatchShift`（:97、post-compare 状態での guard + `beginShiftVM'` 発火）。**発見: `ShiftRoundAtC`（Round7:384）は木のどこにも producer がない名前付き契約**。pre-compare の `shiftGuardVM s1` は post-compare guard から導出不能（chain 状態と `read s1.right` vs `read (right s1.right)` が違う）→ `ShiftRoundAtC` を post-compare guard で言い直して `ShiftRoundData` の producer を作るのが正道（`CloseoutWatchRound30` 進行中）。
- 進行中: `CloseoutPackRun26`（`ShiftLocal` ガード）、`27`（予算付き ready）、`28`（`WalkerInOrigin`）、`29`（`shiftEntry` + `bigResid6_of_lpackM2`）、`CloseoutPreload32`、`CloseoutWatchRound28`（`ReplayRunC`/コスト片）、`29`（`LandingRestartReach`）、`30`。
- 残: pack `shiftEntry` + `WatchShift` + `WalkerInOrigin` + `Extra3` 3 場 + `first ≠ 4`; readiness `hsc/hs2/hcan` + prepare 継続; watch `ShiftRoundData` producer + `FallbackCostPieceC`/`ReplayRunC` + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n50 (2026-09-18 未明) `foundExit_compare_final12`（4 分割消費）・`WindowInOrigin` は search cursor 不変量 `WalkerInOrigin` に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutWatchRound25`、`CloseoutPackRun25`）、sorry なし、build ログ `build_n50b.log` EXIT=0。
- **watch**: `CloseoutWatchRound25.foundExit_compare_final12`（:173）: `final11` の仮定 + `MismatchShiftRouteC` のみ、`exitSplit4C_of_tick` + `watchPrefixC_of_unique` で分割、家族 1–3 は定数 `ExitSplit3C` で `final9` へ、家族 4 は `mismatchShift_tick`（:100、`¬MismatchGuardFails` から guard 通過の disabled tick が存在し `beginShiftVM'` が発火）→ `mismatchShift_to_shiftRoute`（:136、`ShiftTailC` へ）→ `roundsRouteLP_of_tail` → `roundsExit_of_LP` → `foundExit_of_compare3`。`WatchPrefixC`・`WatchMismatchNoShiftC` は放電済み。残 `MismatchShiftRouteC`（:120、`ShiftRoundAtC` のトリガーを不一致 shift 着地の記録に置換した形；`shiftGuardVM s1` は着地で読み、記録された guard は `afterMismatch s1 vs vq` 上で読むので、`vs` を frame の `compare` に `compare_scan_unique` で結ぶ必要；`CloseoutWatchRound27` 進行中）。
- **pack**: `CloseoutPackRun25`: `Fair.fallbackPlace` は `t.fpp.walker = t.walker`（search 副プロセス自身の cursor）であって `stream (P.place s)` ではない。`windowInOrigin_of_fair`（:56、`WalkerInOrigin y.vm` から 1 rewrite）、`windowInOrigin_left`、`windowInOrigin_tick`、`FairSteps`、`wpack_of_fair`（:120、`hwalk : FairSteps 到達可能な copy 状態で WalkerInOrigin`）。残 `WalkerInOrigin s := |stream s.walker| ≤ pos R`: search 副プロセスの不変量（boot で `emptyPlace`、init/replayStart は `Fair.keepsSearchCursor`、`prepare` で `walker := center = P.place s` かつ `|stream (P.place s)| ≤ pos R`、以後左へのみ、R は右へのみ）→ `CloseoutPackRun28` 進行中。
- 進行中: `CloseoutPackRun23`（`LPackM2`）、`26`（`ShiftLocal` ガード判定 + `final16`）、`27`（予算付き ready）、`28`、`CloseoutPreload31`（`PostRunF`）、`CloseoutWatchRound26`（`EntryCostC`）、`27`（`MismatchShiftRouteC`）。
- 残: n49 と同じ、watch は `MismatchShiftRouteC` + コスト 3 葉 + `LandingRestartReach`、pack は `WalkerInOrigin`。


## n49 (2026-09-18 未明) **訂正: `ScanRealized` は `ScanSupplyInv` と矛盾（Preload24〜29 の `hreal` 定理は vacuous）**・`Extra3` 部分閉・watch コスト閉包 3 葉

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutPreload30`、`CloseoutPackRun22`、`CloseoutWatchRound24`）、sorry なし、build ログ `build_n49b.log` EXIT=0。
- **readiness（訂正）**: `CloseoutPreload30.scanRealized_absurd`（:72）: `ScanSupplyInv F 2048 I → ScanRealized F I → False`。`ScanRealized` は全 `bs : List Bool` を量化しており、`prefixPhase_of_scan_inv` で任意脚が `PrefixPhase`（`len ≤ 2048·count + 2047`）になるが `bs = replicate 2048 false` で破れる。**結果: `hreal` を取る全定理（Preload24 `runEntriesS_of_stageInv2C`…`round_trip_entries`、Preload28 `runEntriesS_of_stageInvD`/`_double_exitD`、Preload29 `postRunD_of_machine(_galil)`）は vacuous**。n45〜n47 の「readiness は `ScanRealized` 1 つ」「9 割」は過大評価。正直な置き換え: `PostRunPh`（:102、`PostRunP` を slack 2047 で、prep 接頭辞の `PrefixPhase` は**到達可能**な接頭辞のみ）、`postRunPh_of_postRunP`/`postRunC_of_postRunPh`（実現性節なし）。`.found`/`.missed` 出口は閉（吸収）。`.wait→.double→prepare` の往復は `PostRunC` の前提から合成できない: (1) `DpSafeStage` に frame（`span = ofNat mw`, `lower = ofNat k`, 較正, DP preload）がない、(2) `.double` 出口の流れは接尾辞なので slack ≤ 2047 に 4 脚分の `ScanTrace` クロック事実が要る。`runP_exit_debt_at_exit_scan` は無傷。次: `PostRunF`（framed・到達可能接頭辞、`CloseoutPreload31` 進行中）。
- **pack (`Extra3`)**: `CloseoutPackRun22`: entry は `ready`/`cand` 閉、`scanAvail` は原点で `pos R ≠ 2|w|` 1 事実、`failed` は DP テープ（`pc = 347`）の事実で `InvLPC` 外。tick は pack 相対形 `H_extraTick3P`（`BigPack2M'' x → Tick x y → Extra3 y`、`bigPack2M''_tick` が実際に使う形）: `scanAvail` は `scan_match`（次の入力文字の到着 = 動いた R での `canRight`）と `shift_done`/`replayStart` 再入以外閉；`ready` は `scan_count`/`scan_match` で bare `SearchReady` が既知の偽 `hpres` → 予算付き `SearchReadyS`/`ReadyPacedS` を pack に要；`cand` は `scan_shift`（`shiftGuardVM` から `Candidate` の producer なし）；`failed` は DP テープ。
- **watch**: `CloseoutWatchRound24.watchFallbackCostC_of_context`（:189）: `WatchFallbackCostC` を `EntryCostC`（stage 入口→着地の costed run、`FoundCompareCtxC` の `WatchSegE` + found tick から）、`FallbackCostPieceC`（`costedRun_fallback_replay/zero` の出力形、DP `Result`/`hlow`/`chosenRadius`/`hfb` + `GalilOracleMC4` 区間予算が入力）、`ReplayRunC`（`replay_after_fallback_general''_R_of_decodes` の第 1 分岐）の 3 葉に。run 連結・cost 合成・centre 上界・R>0 の `InvLP` は閉。
- 進行中: `CloseoutPackRun23`（`LPackM2` 4 場）、`25`（`WindowInOrigin`）、`26`（`ShiftLocal` ガード + `final16`）、`CloseoutPreload31`（`PostRunF`）、`CloseoutWatchRound25`（4 番目の家族）。
- **偽だった主張の訂正**: 「readiness の残りは `ScanRealized` の具体化だけ」→ `ScanRealized` 自体が矛盾、`hreal` 定理は空。「`Extra3` は機械事実で閉じる」→ `ready`/`cand`/`failed` は pack の場（予算付き ready、`Candidate`、DP テープ）を要る。
- 残: readiness `PostRunF` 往復 + 4 脚 `ScanTrace` クロック; pack `LPackM2` 4 場 + `WatchShift` + `WindowInOrigin` + `Extra3` 3 場 + `first ≠ 4`; watch 4 番目の家族 + コスト 3 葉 + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n48 (2026-09-18 未明) `shiftVm_tapeActKQ` K=28（`hrot`/`near ≠ []` 消滅）・`H_marksEntry'` は run 限定で `WindowInOrigin` 1 点・出口分割 4 通り

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 4 本登録（`CloseoutCoreEnc22`、`CloseoutPackRun17`、`CloseoutPackRun24`、`CloseoutWatchRound23`）、sorry なし、build ログ `build_n48c.log` EXIT=0。
- **core**: `CloseoutCoreEnc22`: `tViewQ = 9`、`encTapesQ rep lay dbg m`（Enc19 の `encTapesD` の 6 cursor block を `viewTapesQ` に拡張）、`tail_chainLe`（`RTQueue.tail` は ≤ 6 SStep の定数）、`chain_actList`（n sub-step ⇒ 各番地 ≤ 2n）、`moveRightQ_actList`（全分岐 ≤ 14/番地、`near ≠ []` 不要）、**`shiftVm_tapeActKQ`（:673）: K = 28**（左 2×14、中央 14、尾 ≤ 4；較正 64 内）。**`hrot` は仮定でなくなった**（`tail_hrot`: `RTQueue.Inv` から `pot_len` + `eq_idle_of_rem_zero` で導出、`PInv` は `RTQueue.lean:223`）。残仮定: `RTQueue.Inv m.vm.left.far/.center.far`、block 0/1 の初期 `LaysS/SInj/SBound`、chain block `restC/hrestC`（≤ 4）、head margins。未着手: `TapeActK` 構造形（配置を `m` の関数に）、有限制御。
- **pack**: `CloseoutPackRun17`: `WindowInOrigin s`（copy 状態で `|stream walker| ≤ pos R`）が唯一の新仮定（`beginFallbackVM'` の着地が存在量化なので `Tick` から不可視、`Fair` の witness = `P.place s` で真）。`WPack`/`wpack_tick`/`wpack_steps`、`chooseLayout_of_wpack`（**偶数長は不要**: cell 0 は `4` を読むので `first ≠ 4` で除外、`first ≠ 7/8` と同型）、`chooseLayout_of_run`、`marksEntry'_of_run`、`marksInv'_of_run'`、`corners_of_marks'_run`（`sharedC` run 上、`CPack` 付き、**`H_marksEntry'` 不要**）。残: (a) `WindowInOrigin` を `Fair` witness から（`CloseoutPackRun25` 進行中）、(b) `first ≠ 4` を最上位へ、(c) 大域 `H_marksEntry'` は証明不能 → 消費側を run 限定形へ、(d) 結果は `galilFrameS (sharedC …)` 上。
- **pack (rShiftNext)**: `CloseoutPackRun24.rShiftNext_of_pack`（:81）: `WatchShift`（:43、非 idle chain の compare 目標 `s''` に対し `mode=scan ∧ ¬replaying`、`canRight`、`4·periodLength ≤ distance`、`distance ≤ 2·rad`、verifier の `canRight/Sane`）1 葉。pack は `Coupled.watch = WatchOK`（round 上界）しか持たん → `AuxPack` に chain–scan 結合場を追加要。**警告**: `compareFound` に mode guard がなく `beginShiftVM'` は `chain = .watch _` しか要らんので、shift モードで `Internal` step が有効なら `ShiftLocal.mode`（`mode = scan` 要求）は偽 → `rShiftNext`/`H_shiftLocalC` は現行の形では shift 状態で証明不能の疑い。修正: `ShiftLocal` の各場（または `WatchShift`）を `mode = scan ∧ replaying = false` でガード（scan tick はそれしか使わん）。
- **watch**: `CloseoutWatchRound23`: 3 分割の家族は排他でない（guard 通過の不一致 = 機械の本物の `beginChainShift` 出口）ので **`ExitSplit4C`**（Shift / Break0 / FallbackG（`MismatchGuardFails`）/ `TerminalRunMismatchShiftC`）に強化、`exitSplit4C_of_tick`、`watchMismatchNoShiftC_of_split`（FallbackG から無条件）、`exitSplit3C_of_4`。残: 4 番目の家族の消費（shift 着地経路へ合流、`CloseoutWatchRound25` 進行中）、`WatchFallbackCostC`（`CloseoutWatchRound24` 進行中）。
- 進行中: `CloseoutPackRun22`（`Extra3`）、`23`（`LPackM2` 4 場）、`24`（`rShiftNext`）、`25`、`CloseoutPreload30`（`PostRun` 帰納）、`CloseoutWatchRound24/25`。
- 残: pack `LPackM2` 4 場 + `rShiftNext` + `WindowInOrigin` + `Extra3` + `first ≠ 4` threading; readiness `PostRun` 帰納 + `ScanRealized`; watch 4 番目の家族 + コスト閉包 + `LandingRestartReach`; core 初期配置・`restC`・有限制御。


## n47 (2026-09-18 未明) `BigResid6` の 5 契約が pack の場不足 4 点に還元・`PostRunD` 組み立て・`WatchFallbackC` 分解

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 5 本登録（`CloseoutPackRun19/20/21`、`CloseoutPreload29`、`CloseoutWatchRound22`）、sorry なし、build ログ `build_n47e.log` EXIT=0。
- **pack**: `rInitPackM` は**無条件**（`AuxPack.front.notInit` で pack は `init` に居らん、`CloseoutPackRun21.rInitPackM_of_pack`）。`rScanInvR` は `replaying = false` で無料（`LPackM.scanGeom`）、`replaying = true` は `H_scanGeomReplay`（Run19:74）；`rShiftDoneScan` は `H_shiftDoneGeom`（Run19:85、実体は `reshift_palindrome` の round 主張）；`rChoosePackL` は `RRepChoose`（Run20:55、`choose_left_eq_right` で `t.left = s.right`、`rrepChoose_of_pos` で `Represents R ∧ 0 < pos R`）；`rReplayPackM` は `H_centreReplay`（Run21:122、`replayStart_heads` で L=C=R=旧 C、`Fair` 不要）。**4 葉とも「`LPackM` に場が無い」型** → `CloseoutPackRun23`（`LPackM2 := LPackM ∧ scanGeomR ∧ shiftGeom ∧ rrepChoose ∧ centreRep`、`lpackM2_tick`）進行中。`bigResid6_of_leaves`（Run19:117）で残り `rShiftNext` と合わせて `BigResid6` を組む。
- **readiness**: `CloseoutPreload29`: `PostRunD F I`、`postRunD_of_machine`（仮定 `ScanSupplyInv`・`ScanRealized`・`PostRunC`）、`postRunD_of_machine_galil`。**小窓は非残差**（Scala `stepGrow` は単位 8 span セル → 全 `.double` 入口で `mw ≥ 8·max k 1`、`eight_le_of_cal`）。残: `PostRun`/`PostRunC` の機械証明（stage 帰納本体、`CloseoutPreload30` 進行中）、`ScanRealized`。
- **watch**: `CloseoutWatchRound22.watchFallbackC_of_context`（:176）で `WatchFallbackC` を `WatchFallbackResidC = WatchMismatchNoShiftC ∧ WatchFallbackCostC` に分解、tick pack 4 つは着地から輸送（`tickPack_of_landing`）。**訂正**: 「不一致なら shift できない」は偽。shift 出口も不一致で、chain が右の記号を予測する場合（Scala `stepScan` は外側不一致分岐でのみ `canShift ∧ prediction == right.read()` を見る、Lean の disabled tick は `Internal` で left/right を読まん）。残差 (a) は shift/fallback 分類器（`MismatchExitG` 形、`CloseoutWatchRound23` 進行中）、(b) はコスト閉包。
- 進行中: `CloseoutPackRun17`（`ChooseLayout`）、`22`（`Extra3`）、`23`（`LPackM2`）、`CloseoutPreload30`、`CloseoutCoreEnc22`（glue）、`CloseoutWatchRound23`。
- 残: pack `rShiftNext` + `LPackM2` 4 場 + `H_marksEntry'` + `Extra3`; readiness `PostRun` 帰納 + `ScanRealized`; watch `WatchMismatchNoShiftC`/`WatchFallbackCostC`/`LandingRestartReach`/`MismatchExitG`; core glue・`hrot`・有限制御。


## n46 (2026-09-18 未明) final15: rewind の角が pack から消えた（`H_marksEntry'` 1 点）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun18`）、sorry なし、build ログ `build_n46.log` EXIT=0。
- **pack**: `pal_in_peg_final15`（`CloseoutPackRun18` line 258）。仮定: `BigResid6`（不変）、`H_extraEntry3`/`H_extraTick3`（`Extra3` = `Extra'` − `rewindMargin`、rewind 角なし 4 場）、**新** `H_marksEntry' (PofC …) q first`、以下不変 `H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIM'`。`BigPack2M''` は `MarksInv' first` を派生場として持つ（`marksInv'_of_run` を `InvLPC` 起点で、`marksInv'_tick` を毎 tick）。`first` は `galilFrameS` の section 変数なので追加 threading なし。要注意点: FIRST セル上の rewind 状態では `MarksInv'` は `1 ≤ pos L` しか与えず `BigPack2M` に忘却できない → `bigPack2M''_tick` を分岐: セル外は忘却して `lpackN_tick`/`rShiftNext` 再利用、セル上の tick は `rewind_done` のみ（`tick_rewind_atFirst`）、`LPackM` はその分岐固有のスクリプト、`replayStart` 着地の `ShiftLocal` は `AuxPack.coupled.idleOut` + `CloseoutPackRun6.shiftLocal_of_chainIdle` で vacuous。`CentreMargin`/final14 経路は不要になった（残すが使わない）。
- 進行中: `CloseoutPackRun17`（`ChooseLayout` → `H_marksEntry'`）、`CloseoutPackRun19`（`rScanInvR`/`rShiftDoneScan`）、`CloseoutPackRun20`（`rChoosePackL`）、`CloseoutPackRun21`（`rInitPackM`/`rReplayPackM`）、`CloseoutPreload29`（`PostRunD`）、`CloseoutCoreEnc22`（glue）、`CloseoutWatchRound22`（`WatchFallbackC`）。
- 残: pack `BigResid6` 6 契約 + `H_marksEntry'` + `H_extraEntry3/Tick3`; watch/readiness/core は n45 と同じ。


## n45 (2026-09-18 未明) `.double` 出口義務が Scala の形（`StageInvD`）で脚長 `mw` のまま閉じた

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPreload28`）、sorry なし、build ログ `build_n45.log` EXIT=0。
- **readiness**: `StageInvD k m v := dpDemand k m ≤ debt`（`dpDemand k m := prepLen k / 2048 + (prepLen k + dpEvents (m+1)) / 2048 + 1`、比較単位、`Rad`/`stageCredit` 不使用 = Scala の「run 脚は自分の比較分の負債があればよい」）。鍵: `dpSafe_entry_km` は半径/credit 形を `(slack + dpEvents |W|)/2048 + 1 ≤ debt` の導出にしか使っておらず、`dpSafe_of_stagePrepD` はそこへ直行（`budget_adv2` 迂回）。`runEntriesS_of_stageInvD`（stage 帰納）、`stageInvD_of_double_exit`（`double_exit_debt_ge` + `prepAt_of_double_exit`）、**`runEntriesS_of_double_exitD`**（`runEntriesS_of_double_exitC` と同結論、脚長 `bs.length = mw` で真、`hstage`/`hcal`/半径形 `hE` 消滅）。残 `hbal : 4*dpDemand k (2mw) + 4*count ≤ mw` はペーシングから放電: `bal_of_paced`（入口位相、`8·max k 1 ≤ 2mw` のみ）、`bal_of_paced_slack`（任意位相 `slack ≤ 2047`、`8 ≤ mw` 要）。n37〜n43 の `.double` 脚問題はこれで決着（Lean の義務形が初回 run 用の半径形だったのが原因）。次: `PostRunD`（`.double` 節を `StageInvD` 形に）と `postRunD_of_machine`（`CloseoutPreload29` 進行中、残るのは `ScanRealized` の `galilFrameS` 具体化と窓 4〜7 の位相）。
- 進行中: `CloseoutPreload29`、`CloseoutCoreEnc22`（glue）、`CloseoutPackRun17`（`ChooseLayout`）、`CloseoutPackRun18`（`final15`）、`CloseoutWatchRound22`（`WatchFallbackC`）。
- 残: n44 と同じ、readiness は `ScanRealized` 具体化のみ。


## n44 (2026-09-18 未明) 影コピー queue で回転が全番地 ≤ 2 手・`MarksEntry` は place-1 で偽→ガード付き `MarksInv'`・`FallbackRouteW` は `WatchFallbackC` に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 3 本登録（`CloseoutCoreEnc21`、`CloseoutPackRun16`、`CloseoutWatchRound21`）、sorry なし、build ログ `build_n44c.log` EXIT=0。
- **core**: `CloseoutCoreEnc21`: 7 役割 `SRole`（Enc20 の 6 + `shadow`）、影は状態から派生（reversing/appending 中は `r'` を写す、`.done` で `f`、idle で `front`）。ウチの「`g = popped ++ front` + カウンタ」案は実時間予算を破る（size-1 queue に `2m+1` の discard が溜まり 2 回目の回転が `PInv.rot` を破る）ので、idle の `tail` は front と shadow を両方 pop（各 1 手）して `g = front` 厳密に。`LaysS q ρ L J`（junk を live の下に置く配置、消去は役割改名で無料）。`SStep`（snocPush/tailPop/inval/rotStart/exec/install）、`snoc_steps`/`tail_steps`（`hrot : lenf < lenr → state = idle` の下で `ReflTransGen`）、`rotRolesS`（fwd ↦ shadow, rev ↦ rear, rear ↦ fwd, shadow ↦ rev）、`sstep_lays`（全 SStep が Delta 族）、**`moveRightS_actList`**（全 SStep で全番地 actList ≤ 2）。Enc20 の逃げ道 `ρ'.fwd = ρ.rear` は `ρ'.fwd = ρ.shadow` として実現。残: glue（`encTapesQ`/`shiftVm_tapeActKQ`、`tViewQ = 9`、`CloseoutCoreEnc22` 進行中）、`hrot` の放電（HM 不変量）、live/junk を判別する有限制御。
- **pack**: `CloseoutPackRun16`: 無ガード `MarksEntry` は place-1 の角で**偽**（`marksEntry_false_at_place_one`: `pos R ≤ 1 → ¬MarksEntry`；`marksEntry_false_of_whole_prefix`）。ガード付き `MarksEntry'`（`mh+1 ≤ pos R + f`）は `ChooseLayout first s`（`denote = update (marks w) 1 first ∧ 1 ≤ mh ≤ w.length ∧ w.length ≤ pos R`）から無条件（`marksEntry'_of_layout`）。`MarksInv'` は全 24 分岐で保存（`marksInv'_tick`）、角 `rewindLeft_of_marksInv'`（`0 < pos (left L)`）、`rewindCentre_of_marksInv'`、`corners_of_marks'`。残: `ChooseLayout` の産出（コピー walker が原点を越えない `w.length ≤ pos R` と偶数長；`CloseoutPackRun17` 進行中）。`final15`（ガード付き角を元の `LTickLeavesN.rewindLeft` に直結、`CentreMargin`/final14 を迂回；`CloseoutPackRun18` 進行中）。
- **watch**: `CloseoutWatchRound21.fallbackRouteW_of_tick`（line 121）: `FallbackRouteW` を `WatchFallbackC`（line 77）+ `0 < q`, `first ≠ 7, 8` の下で産出。`fallbackLanding_of_pack`（watch 中 clock-1 不一致からの fallback tick は `1+(n+1)` tick で着地、R=0 なら `Inv`、R>0 なら `ReplayLanding`、`SpanRep`、中心厳密前進）。**発見**: `GalilInvPlus.fallback_pack_span` は `chain = .idle` を要らない（idle 要求は `SegReached.idle` 由来のみ）。`WatchFallbackC` の中身: (a) 不一致状態の tick pack `ShiftIdle ∧ MInv ∧ FallbackCounters ∧ FallbackTick ∧ OutputRel`（実質 `FallbackTick` = watch 不一致で `¬shiftGuardVM`）、(b) stage 入口からのコスト閉包（`StepsAll … ∧ CostedRun` と R>0 の `InvLP`）。`CloseoutWatchRound22` 進行中。
- **readiness**: `CloseoutPreload28`（倍化後 stage 不変量 `StageInvD` を Scala の形 `debt ≥ 0` で）進行中。Scala 照合: `stepWait` は `debt.sign == 0` のときだけ `doubleWindow()`（`wait_exit_debt_zero` は忠実）、Scala が主張する不変量は `debt ≥ 0` のみ（`IllegalStateException` 2 箇所）。`.double` 出口での「stage 予算再成立」は Scala にない → Lean の定式化ミス。
- **偽だった主張の訂正**: 「影コピーは `popped` カウンタで管理」→ 予算を破る。「無ガード `MarksEntry` は真」→ place-1 で偽。
- 残: pack `BigResid6` 6 契約 + `ChooseLayout`; watch `WatchFallbackC`/`LandingRestartReach`/`MismatchExitG`/存在形 RoundsExit・BreakExit; readiness `StageInvD`・`ScanRealized` 脚構成; core glue・`hrot`・有限制御・`restC`・`nq/hctl`・`CounterPark`/`FlagPark`; `H_realizeLIM'`; `CycleOracleMC3` 葉。


## n43 (2026-09-18 未明) `.double` 義務の真の障害は基底負債（除数は無関係）

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPreload27`）、sorry なし、build ログ `build_n43.log` EXIT=0。
- **readiness**: `stageCredit8`（除数 8）で `budget_adv2_nat8`/`budget_adv2_8` は同じ入力で閉じる。しかし `double_len_of_leg8`: 十分な脚長は `mw + 4·max k 1 + 4c + 7`、`double_len_needs8`: 必要条件 `mw + 4·max k 1 + 4c + 4 ≤ L + 4·Rad`。`L = mw` では `Rad ≥ max k 1 + c + 1` を強制（`double_len_forces_rad8`）、`Rad = 0` で反証（`double_len_false_of_rad_zero8`）。**除数は無関係**: 任意の credit `cr ≥ 0` で `8·max k 1 + 4c + 4 ≤ L + 4·Rad` が必要（`double_len_needs_any`）、`L = mw = 4·max k 1, Rad = 0` で反証（`double_len_false_any`）。除数 16 でも `mw < 12·max k 1 + 8c + 7` で破綻。**真の障害**: 基底負債 `stageDebt Rad k = 2·max k 1 − Rad`（4 tick/単位で 8·max k 1 tick 分）を `wait_exit_debt_zero` がリセットし、`mw ≥ 4·max k 1` tick の脚では再獲得できない。除数は `mw − 4·max k 1` の超過分にしか効かない。候補: (a) `.wait` 出口で負債を保持、(b) `Rad ≥ max k 1 + c + 1` を側条件（Preload26 と同値）、(c) `.double` 脚 ≈ `2·mw`（Preload25）。Scala で stage 負債の初期化と wait 出口の扱いを照合中（scout）。`PostRunC8` は未作成（節が偽なので）。
- **偽だった主張の訂正**: 「`stageCredit` の除数を 8 にすれば `.double` 義務は無条件で閉じる」（n40）→ 偽。障害は基底負債と wait リセット。
- 進行中: `CloseoutPackRun16`（`MarksEntry`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutWatchRound21`（`FallbackRouteW`）、Scala 照合 scout。
- 残: n42 と同じ、readiness は「基底負債の扱いを Scala に合わせる」に変更。


## n42 (2026-09-18 未明) `WatchPrefixC` は無仮定の定理 → `foundExit_compare_final11`

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutWatchRound20`）、sorry なし、build ログ `build_n42.log` EXIT=0。
- **watch**: `watchPrefixC_of_unique`（`CloseoutWatchRound20` line 172）は全 `P q first cP sP` で**無仮定**（`LiveScanWatch`/`Fair` 不要）。`refresh_unique`、`compare_scan_unique`（`scanLens.get_set` + `GalilTickDet.chainTick_unique` + `scanVM_ext`）、`watchSeg_step_unique`（構成子族は重ならない：`wait` は `¬canRight`、`count`/`match` は `canRight` で `1 < clock` vs `clock = 1`）、`watchSeg_prefix`（第 1 走行への帰納）。`GalilTickDet` の `Tick` 非決定性（restart stutter・fallback 着地・init/replayStart）は `WatchSeg` に入らない。`foundExit_compare_final11`（line 180）= final10 から `hpre` 除去。残契約: `FallbackRouteW`（`CloseoutWatchRound21` 進行中）、`LandingRestartReach`、`MismatchExitG`、存在形 RoundsExit/BreakExit。
- 進行中: `CloseoutPackRun16`（`MarksEntry`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`（`stageCredit8`）、`CloseoutWatchRound21`。
- 残: n41 と同じ、watch は `WatchPrefixC` 消滅。


## n41 (2026-09-18 未明) `CentreMargin` は MARKS テープ不変量経由で `MarksEntry` 1 点に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun15`）、sorry なし、build ログ `build_n41.log` EXIT=0。
- **pack**: `MarksInv first c s`（rewind 中: FIRST セル `f ≥ 1` が MARKS ヘッド以左で `mh s + 2 ≤ pos L + f`、かつ `pos L + r + pairOff ≤ pos C`）。`centreMargin_of_marksInv`、`marksInv_tick`（全 `galilFrameS` tick で保存、`rewind_one/pair` は `focus_eq`/`left_head`/`position_left` で閉、他は vacuous、`choose_select` だけが `MarksEntry` を消費）、`centreMargin_of_marks`（rewind 外始動の run 全状態）。**残る仮定は `H_marksEntry P q first` 1 点**（`choose_select` 時点で `mh s + 2 ≤ pos R + f`、FIRST がセル 1 なら `mh s + 1 ≤ pos R`）。注意: 無ガードの `CentreMargin` は `rewind_done` でも `2 ≤ pos L` を要求するので、入力 1 文字目から始まる回文を選ぶ場合を除外している可能性 → `CloseoutPackRun16` で真偽判定（偽ならガード付き `MarksEntry'` へ、`GalilScaffoldTopFallbackAll` の FIRST = `head − 2r` から導出を試みる）、進行中。
- 進行中: `CloseoutPackRun16`、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`（`stageCredit8`）、`CloseoutWatchRound20`（`WatchPrefixC`）。
- 残: n40 と同じ、pack は `MarksEntry` に置換。


## n40 (2026-09-18 未明) `.double` 義務の根本原因は `stageCredit` の除数・`ExitSplit3C` は `WatchPrefixC` 1 葉に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPreload26`、`CloseoutWatchRound19`）、sorry なし、build ログ `build_n40b.log` EXIT=0。
- **readiness**: `CloseoutPreload26`: `doubleCarry mw c := (mw+4c+10)/4`、`PostRunC' carry`（round-trip の `.double` 節で `hlen : bs.length = mw`、不足分を半径に繰り入れ `3*(Rad + carry) ≤ 5*k`）、`postRunC'_of_double_leg`/`postRunC'_double_spends`。ただし側条件 `3*(Rad + doubleCarry) ≤ 5*k` は導出不能（`mw ≲ 20k/3` を強制）。**根本原因**: `stageCredit k m = (m − 8·max k 1)/4`（`CloseoutPreload11`:66）が甘すぎる。長さ `mw` の `.double` 脚が稼ぐのは ≈ `mw/4`、要求は `stageCredit k (2mw)` ≈ `mw/2`、しかも `.wait` が負債を 0 に戻す（`wait_exit_debt_zero`）ので蓄積しない。**修正は除数 8**（`budget_adv2_nat` は要求 ≈ `m/41` で閉じる）。`CloseoutPreload27`（`stageCredit8`、`budget_adv2_nat8`、`double_len_of_leg8`、`PostRunC8`）進行中。
- **watch**: `CloseoutWatchRound19.exitSplit3C_of_tick`（line 191）で `ExitSplit3C` 放電、`foundExit_compare_final10`（line 206）。新仮定 1 つ: `WatchPrefixC P q first cP sP`（line 95、prep 着地からの任意 2 本の `WatchSeg` 走行は接頭辞比較可能）。`ExitSplit3C` は ∀/∨ 交換なので `WatchSeg` の `background`/`compare`/`searchEffect` が関係的な限り導出不能。機械上は段決定性（`GalilTickFair` の `*_unique` 群）から従う。`CloseoutWatchRound20`（`watchPrefixC_of_unique` → `final11`）進行中。補題 `watchSeg_not_canRight`（尽きは吸収）、`watchSeg_stuck_of_mismatch`（clock-1 不一致は `stop` のみ）。
- 進行中: `CloseoutPackRun15`（`CentreMargin`）、`CloseoutCoreEnc21`（影コピー queue）、`CloseoutPreload27`、`CloseoutWatchRound20`。
- **偽だった主張の訂正**: 「`.double` 出口義務の側条件は負債持ち越しで消える」→ 消えない（除数が原因）。
- 残: n39 と同じ、readiness は `stageCredit8` 化、watch は `WatchPrefixC` 産出。


## n39 (2026-09-18 未明) 6-stack 役割表: 回転開始は無料、代償は `f := front` の複製へ

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutCoreEnc20`）、sorry なし、build ログ `build_n39.log` EXIT=0。
- **core**: `QRole`/`Lays q ρ L`（役割表、`queueTapes6_roleList` で `queueTapes6` = 恒等役割表）。`Delta`(keep/pop/push) は `dTape` 上で無条件に各番地 ≤ 2 手（`dActs_length`）。**回転開始 `rear := []` は役割付け替えのみ**（`rotStart_actList`: 全番地 actList `[]`）。Enc19 の `not_bounded_rot_rear` は 4 テープ層だけの否定と確定。`exec`/`invalidate`/`tail` も Delta 族。**ただし** `front_fwd_sep`（`SInv` より `f = front.drop ok`、`0 < ok` で別名禁止）+ `not_bounded_install_fwd`: 空スタックへの `fwd` 設置（`f := front` の複製）は生セル数の手数が要る。代償が「消去」から「複製」へ移っただけ。未否定経路は `ρ'.fwd = ρ.rear` 1 本。
- 次（`CloseoutCoreEnc21`、進行中）: 影コピー方式。appending 中に新 front と影 `g` へ二重 push（別番地なので各 ≤ 2 手）、`tail` は front だけ pop、`g = popped ++ front` を不変量に持ち、回転時は `g` を反転源に役割付け替え（無料）して先頭 `popped` 個を捨ててから反転。HM の `ok` 簿記と同じ 2 倍ペースに吸収。
- 進行中: `CloseoutPackRun15`（`CentreMargin`）、`CloseoutPreload26`（`PostRunC'`）、`CloseoutWatchRound19`（`ExitSplit3C`）。
- 残: n38 と同じ。


## n38 (2026-09-18 未明) final14: rewind の角を `CentreMargin` 1 葉に

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 1 本登録（`CloseoutPackRun14`）、sorry なし、build ログ `build_n38.log` EXIT=0。
- **pack**: `pal_in_peg_final14`（`CloseoutPackRun14` line 300）。仮定は final13 と同一で `H_extraEntry''`/`H_extraTick''` のみ差し替え（`Extra''`: `rewindMargin` → `centreMargin`）。`LTickLeavesN'`（`rewindLeft` を `CentreMargin c s` に）、`LTickLeavesN'.toN` は `RCouple c s` を要するが run 上では定理（`rcouple_of_invLPC`）。`lpackN'_tick` は `lpackN_tick` との合成のみ（22 分岐は再走せず）。`BigPack2M'` は `RCouple` を派生場として持ち `BigPack2M` に忘却するので `BigResid6` は不変。
- 進行中: `CloseoutPackRun15`（`CentreMargin` を `marksTape s.fpp` の FIRST 位置不変量から）、`CloseoutPreload26`（`PostRunC'`: `.double` 出口の負債持ち越し形）、`CloseoutWatchRound19`（`ExitSplit3C` 放電）、`CloseoutCoreEnc20`（6-stack 回転）。
- 残: n37 と同じ（`CentreMargin` が `rewindMargin` を置換）。


## n37 (2026-09-18 未明) rewindMargin は削除不能→CentreMargin 1 葉・`.double` 脚の正確な閾値

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 2 本登録（`CloseoutPackRun13`、`CloseoutPreload25`）、全モジュール sorry なし、build ログ `build_n37b.log` EXIT=0。
- **pack**: `rewindMargin` 葉（`LTickLeavesN.rewindLeft`）は**削除不能**。`CloseoutPackRun13.rewind_left_step`: rewind に留まる tick は L を必ず 1 左へ動かす（`rewindOne`/`rewindPair` とも `left := left x.left`）。前夜の「rewind は R だけ動かす」は誤読で、毎 tick 動くのは L、2 tick に 1 回が C。代わりに `RCouple`（`pos L ≤ pos C ≤ pos L + radius + pairOff`）を全 tick 無仮定で保存（`rcouple_tick`、rewind 外始動の run では定理 `rcouple_of_run`）し、`CentreMargin`（rewind 中 `radius + pairOff + 2 ≤ pos C`）1 葉から `rewindMargin` と `GalilRewindSafe.CentreLive` の両方を供給（`corners_of_centreMargin`）。`CentreMargin` は MARKS テープの「FIRST が原点 gap より右」で `Tick` から不可視、未証明。次: `rewindLeft` を `CentreMargin` に差し替えた `LTickLeavesN'` で `lpackN'_tick` → `final14`（`CloseoutPackRun14`、進行中）。
- **readiness**: `postRunC_of_machine` の `.double` 脚数値義務 `4*(stageDebt+stageCredit+1)+4*count+3 ≤ mw` は脚長 `L = mw` では**偽**（`CloseoutPreload25.double_len_false_of_rad_zero`、Rad=0 で反証）。十分条件は `double_len_of_leg`: `L ≥ 2*mw + 4*count + 7`。Scala 正本（`ScaffoldSearch.scala:144,147,275`）は double 相を**正確に `mw` tick**で抜ける（`alias(work, span)` → `Mode.Double` → work 空で `prepareWindow()`）。したがって偽なのは機械ではなく **`PostRunC`（`CloseoutPreload24`）の `.double` 出口義務の定式化**：倍化後の窓のコストを出口時点で一括請求しているが、Scala は次の run 相で償却する。次: `.double` 出口義務を「負債の持ち越し」形（`stageDebt` を次 run の `DpCharged` に繰り入れ）に書き直して `PostRunC'` を定義し、`runP_exit_debt_at_exit_scan` と接続。wait 脚→`DepthAt` は閉（`depth_supply_of_wait_leg`/`stage_supply_after_wait`）。`ScanRealized` の `galilFrameS` 具体化は未達。
- **core**: `CloseoutCoreEnc20`（6-stack `RTQueue` + role swap 回転）進行中、未登録。
- **偽だった主張の訂正**: 「rewind は L を動かさない（rewindMargin は vacuous）」→ 偽。「`.double` 出口で倍化窓のコストが払い済み」→ 偽（Scala は `mw` tick で抜け、次 run で償却）。
- 残: pack `BigResid6` 6 契約 + `CentreMargin`; watch `FallbackRouteW`/`ExitSplit3C`/`LandingRestartReach`/`MismatchExitG`/存在形 RoundsExit・BreakExit/StepsAll 決定性; readiness `PostRunC'` 再定式化・`ScanRealized` 脚構成; core `moveRightQ_actList`・`restC`・`nq/hctl`・`CounterPark`/`FlagPark`; `H_realizeLIM'`; `CycleOracleMC3` 葉。


## n36 (2026-09-18 未明) final13・scanLeft 葉削除・PostRunC・shiftVm K=64・キュー配置

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 12 本登録（`CloseoutPackRun11–12`、`CloseoutPreload19–24`、`CloseoutCoreEnc17–19`、`CloseoutScanMargin4`）。
- **pack**: `pal_in_peg_final13`（`CloseoutPackRun12`）。Lean の `read` は gap で sentinel `2`、原点のみ `none`（Scala と一致：gap は `"s"`、原点 `None`）→ 原点比較は必ず不一致、`scan_match` は `position L = 1` から発火しない（`ScanMargin4.no_scanMatch_at_pos_one`）。`scanLeft` 葉は「無条件版は偽・matched 前提つきは真」なので葉から完全削除（`LTickLeavesN`、`lpackN_tick`、PackRun11）。`Extra'`＝`Extra` − `scanMargin`（反証済）。残仮定 9：`BigResid6`（`rInitPackM`/`rScanInvR`/`rShiftDoneScan`/`rChoosePackL`/`rReplayPackM`/`rShiftNext`）、`H_extraEntry'`/`H_extraTick'`（角は `rewindMargin` のみ、PackRun13 進行中）、`H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIM'`。Scala 全 tick 追跡（`a`,`aa`,`aab`,`aba`,`abab`）で「mode=scan かつ L=原点」の tick は 0 件、`PlaceHead.left` の例外は到達不能。
- **readiness**: `PostRun` → `PostRunP`（paced）→ `PostRunC`（clock 位相形、Preload24）。閉じたもの：`.run` 相のイベント長 ≤ `dpEvents`（測度は `DpSafeStage.pre`、Preload15）、`StagePrep` 切り直し（16）、`.wait` は `.run` に戻らず債務が測度（14）、`.double` 消化 `double_complete`（17）、時計位相 `PrefixPhase`（18/19：`PacedL` は上界のみ＝下界は `LiveL`）、`LiveL` はマッチクロック保存則から（20）、帳簿同定 `scanTrace_eq_runTrace`（21）、`searchStep` の boolean＝`ScanTrace` 事象、`ClockInv` は Tick 不変（22）、右ヘッド供給 `ScanSupplyInv`（`Extra.scanAvail` 経由、23）、`slack ≤ 2047` を位相から（24）。残：`.double` 脚の数値義務、wait 脚長→`DepthAt` 変換、`ScanRealized`（Preload25 進行中）。
- **核**: `shiftVm_tapeActK`（K≥4、Enc17；ミラー 7 番地込み）。`moveRight` は現配置では pop 不可能（偽）→ debris 配置 `dTape`（pop 1 手・push 2 手、Enc18）→ `encTapesD` 上 `shiftVm_tapeActK'`（Enc19、`near ≠ []` 側条件）。回転開始は 4 本 cursor では有界不可（`not_bounded_rot_rear`）→ 6 スタック＋役割置換（Enc20 進行中）。
- **偽だった主張の訂正**: 「Lean の compare に左端停止則がない＝モデル不備」（ScanMargin3）は過剰判定、不備なし。「`∀ s, F.available s`」は偽（`ScanSupplyInv` で置換）。「`rear := []` は消去」は誤読（役割付け替え）。

## n35 (2026-09-17 夜) final12・final9・PostRunP・chooseVm K=64・原点角の実態

**全体 build 成功・標準公理のみ・無条件 PAL は未完。** 新規 21 本を登録（`CloseoutPackRun7–10`、`CloseoutPreload12–17`、`CloseoutCoreEnc13–16`、`CloseoutWatchRound14–18`、`CloseoutScanMargin1–3`）、`GalilFoundLandingL`/`GalilInvPlus2` に着地 `Inv` を export する `_Inv` 版を追記（既存宣言不変、`GalilInvPlus2` に import 1 行追加）。
- **pack**: `pal_in_peg_final12`（`CloseoutPackRun9`）：`IPackO`（MInv/PalAt なし、`lrep`+`scanGeom`）で `StepsI…PreTraceI` 全 7 定義を再カット、`H_trailI` は定理（`h_trailI_O`）で放電。残仮定 9（`BigResid5O` 6 契約 = 旧 7 − `rShiftDoneMinv`、`H_extraEntry/Tick`、`H_shiftLocalC`、`H_stageScan`、`CycleOracleMC3`、`H_bootShift`、`H_landShift`、`H_realizeLIO'`）。`lpackO_tick` は minv コーナー削除で欠落なし。`CloseoutPackRun10`：strict は `scan ∨ rewind` に限定（`lrepM`）、`scan_shift/fallback` は `Represents` のみで閉じ、`shift_done` は `leftPresent` で再取得。
- **原点角（重要）**: `Extra.scanMargin`（`r+2 ≤ C`）は 1 文字語の初期 scan 状態で反証（`CloseoutScanMargin2`）。`lrep` 下では `position L = 0` は到達不能（`lrep_pos`）、真の角は `position L = 1` からの比較 tick で `focus = none` になる（`ScanMargin3`）。Scala 実走で確認：原点では `left.read() == None` → 必ず不一致 → fallback、例外なし（`aab`,`aaab`,`abab`,`aabaa` 全接頭辞一致）。Lean の `compare` も同じ。残る欠落は `scan_match` の `scanLeft` 葉 1 つ（右が letter でも `position L = 1` は `ScanInvariant` から排除できない：gap 一致の扱いを tick 追跡で確定中）。
- **watch 経路**: `foundExit_compare_final9`（`CloseoutWatchRound18`）：3 way 出口（shift／入力枯渇／外側不一致 `FallbackRouteW`）。`FallbackRouteLP` は producer なしの契約と判明、watch 版 `FallbackRouteW` も契約。`LandingRestartReach` は fallback 分岐のみ、`hLR` は round/break 分岐から除去（`final8`）。`watchSegE_of_watchSeg` 追加。残契約：`FallbackRouteW`、`ExitSplit3C`、`LandingRestartReach`、`MismatchExitG`、`RoundsExit`/`BreakExit` の存在型化。
- **readiness**: `PostRun`→`PostRunP`（paced 版、置換無料、`CloseoutPreload17`）。`.run` 相：`run_exit_frame`（Preload13；`.double` 出口は `work = ofNat m`、span は reset）、`RunTraceP` 債務上界（14）、イベント長 ≤ `dpEvents`（15、測度は `DpSafeStage.pre`）、`StagePrep` 切り直し（16）、`.wait` は `.run` に戻らず債務が測度（14）、`.double` 消化レグ `double_complete`/`double_leg_entries`（17）。残：時計相 `slack ≤ 2047`、`.wait` レグ長、`hE`（Preload18 進行中）。
- **核**: カウンタ reset は役割切替不要（`applyAction` 1 発、`CloseoutCoreEnc13`）；`chooseVm` は全番地で `TapeActK`（K≥2）完成（`chooseVm_tapeActK`、Enc16；lengthMir は 2 発）。`Seg→Γc` 埋め込みとスロット番地（Enc14）、`shift1/padRN` と `actList` の可換条件（Enc15；左マージンは `padRN` から出ない＝`pos(phys j)+1`）。残：`shiftVm`（left/center/chain カーソル）、有限制御 `nq`/`hctl`、`CounterPark`/`FlagPark` 実体、`shiftPick` の view 2 手。
- **偽だった主張の訂正**: 「`.double` へ span 不変で抜ける」（work に移る）、「wait は 1 tick で run に戻る」（戻らない）、「`padRN` の余白で左マージン」（右側なので寄与ゼロ）、「lengthMir 1 発」（2 発）、「scan_match で右 letter → `position L ≥ 2`」（偽）。

## n34 (2026-09-17) 合成 step・段 2 添字化

`CloseoutCoreEnc12`（1 抽象 tick＝高々 K=64 マイクロ動作の合成、番兵 `Option Γc`、`TEqG`）、`CloseoutPreload11`（段 readiness を `(k,m)` で再証明、倍化は自弁）、`CloseoutPackRun6`（boot/init `ShiftLocal` 閉）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n33 (2026-09-17) final11・台帳化・段 2 添字化

`pal_in_peg_final11`（`IPackG` 差し替え完了、`MInv` は scan 限定；残 `BigResid5G` 7＋extra、boot/init の `ShiftLocal` は閉）。watch 経路：`NoShiftTailC0` を台帳形へ（`foundRouteMC_noshift_L`）、交差 report の live-chain 版（`reachAtC3_of_crossW'`）。段 readiness：`NoReturn`/`StageBoundary` 偽→2 添字 `(k,m)` 化進行中、短入力は `dpSafeStage_entry_real` で解決。core：多くの step は 1 tick 1 マイクロ動作でない→合成 step（K=c）へ設計修正中。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n32 (2026-09-17) MInv 設計修正・watch 残渣の欠落事実確定

`CloseoutPackRun4`：`rMismatchMinv` 偽（不一致着地で中心は死ぬ）→ `LPack.minv` を scan 限定に切り直し中（`PackRun5`）。`CloseoutWatchRound8`：残りの真の欠落＝準備中比較ゼロの全着地版、`freshWatch` 構文一致→台帳化、exit の restart 証人、DP 窓一意性、shift 後 rounds 構成（`WatchRound9/10` 進行中）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n31 (2026-09-17) 債務再較正・core ActPieces

`CloseoutPreload6`（準備中 advance 込みで入口債務を再較正、`k ≤ 2045` 消滅、残 `CentreLongRun`/`NoReturn`/`EntryDepthG`）、`CloseoutCoreEnc10`（幅 9 本閉、窓 13 は `ActPieces` へ）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n30 (2026-09-17) final10・watch/core 残渣の切り直し

`pal_in_peg_final10`（`CloseoutPackRun3`：`BigPack2`＝`Extra`（DP 最大性・候補周期・段余裕）付き、残 `BigResid5` 9 契約）、`CloseoutWatchRound7`（残 7）、`CloseoutPreload5`（入口債務は準備中 advance 分の再較正が必要と判明）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n29 (2026-09-17) final9・core 窓の step 単位還元

`pal_in_peg_final9`（`CloseoutPackRun2`：入口残余ゼロ、残 `BigResid4` 12 経路契約）、`CloseoutWatchRound5`（tail は 6 契約に）、`CloseoutCoreEnc9`（phase 窓は 12 `winOn`＋5 原子＋9 `widthStep` に）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n28 (2026-09-17) final7・PackRun・core 残債の細分化

`pal_in_peg_final7`（`CloseoutPackRun`：`BigPack` で `PackRun` を証明、残 `BigResid` 12 経路契約）。`CloseoutWatchRound6`（台帳契約 8→4）、`CloseoutCoreEnc7/8`（`widthFeed`/`encInjective7` 偽→修理、phase 7 は `branchRead`/`winOn`/`widthEnc1` に細分化）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n27 (2026-09-17) OracleI・watch rounds・core 窓関数

`CloseoutOracleI/I2`（`IPack` 着地は `ShiftLocal` のみ、`H_lrepC` 閉、残 `PackRun`＝走行保存）、`CloseoutWatchRound3/4`（`foundExit_compare_final4`、残 tails と台帳契約）、`CloseoutPreload4`（`RestartTrace` 偽→entry 版、残 3 契約）、`CloseoutCoreEnc6`（恒等 3 モード閉、残 phase 7 の `DetWin`）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n26 (2026-09-17) final6・watch 相・段切り台帳の修正

`pal_in_peg_final6`（`BootIPack`/`H_oracleI`/`H_realizeLI'`、`H_trailI` は定理化 `CloseoutLPack6`）。`foundExit_compare_final`（`CloseoutWatchRound2`、残 `MatchTickC`/`LandingReadyC`/`TerminalTailsC'`）。段切り台帳を `stageWindow1`・`RdPaced` 長さ下限で修正、`readyClosure_C` は `RestartTrace` 1 つ残し。core は `CoreLocal` 項構成済み、残債はモード別窓関数 ×10 と feed 配置。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n25 (2026-09-17) watch 相の構成・LPack 葉・core 残債

`CloseoutWatchRun/Round`（watch 相の燃料帰納構成、1 round 構成；残 `RoundDataC`/`TerminalTailsC`）、`CloseoutLPack3/4`（23 構成子分岐、残 `LTickLeaves4`＝run レベルで輸送予定）、`CloseoutCoreEnc3`/`Preload`/`RunEntriesS`（`CoreLocal` 項構成、`RunEntriesS` 全列で閉、残 `PreloadAtEntry`）、`GalilReplaySpan ''_R_of_decodes`（抽象台帳 `ReadyClosure`、`hpres`/`RunEntries*` 消滅）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n24 (2026-09-17) 第2波続き：段切り readiness・LPack・core 符号化

`CloseoutReadyStage`（`SearchReadyS`/`ReadyPacedS`：予算上限なしの区間構成、`hpres` 不要）、`CloseoutLPack/2`（`TrailF` は `LPackTick` 1 tick 保存＋shift 入口条件に還元）、`CloseoutPrepInputs3`/`LaterQuantum`/`LaterEntry`（found の DP データは named なしで閉）、`CloseoutWatchPhase/2`（found 経路は `ShiftTailC`/`NoShiftTailC`＝watch 相の実走行のみ残）、`CloseoutCoreEnc/2`/`CoreAgree`/`RightBounds`（K=1 窓局所性、語依存除去、chain 表現；queue 配置と margin は修正版へ）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n23 (2026-09-17) 計画第2波：契約・found 3葉・core・債務監査

`CloseoutContracts`（StageEntryC/SegResult/CostedRouteC/FoundExit/CheckpointRunC）、found 3葉は `FoundExit` 型で `RoundsRouteLP`/`BreakRouteLP`（watch 相の per-instance 構成）まで還元、`PrefixCost` は点ごと版に修正。`RunEntriesPaced`/`ReplayFitsStage` 偽（`CloseoutRunEntriesPaced`/`CloseoutDebtAudit`）→ 段切り readiness `SearchReadyS` へ再定式化中。`TrailF` は `LPack`（左ヘッド走行 pack）1 つに集約。core は `Q/Γ/t` 具体化、`AgreeOn`×7・`encC`・窓局所性が残り。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n22 (2026-09-17) 計画 §8 第1波 A–E 完了

`RunEntriesAtBegin` 偽（`CloseoutReadinessAudit`）→ `RunEntriesPaced`（`GalilReplaySpan ''_fuel'`）。`Fair` witness（`CloseoutFairWitness`）。`RadLedger`（`CloseoutRadPack`、`startLe` 閉、`shiftCR` は remaining=0 で要修正）。core は `CoreLocal` 束に還元（`CloseoutCoreAudit`：閉じた `LocalStep` 項なし、語依存あり）。横断 report は `InvLPS`+入口予算で閉（`CloseoutReportCase`）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n21 (2026-09-17 朝) Fair 完成・hpres/StartShape 置換・TrailF は RadPack に集約

`GalilTickFair`（`Tick ∧ Fair` 一意）、`StartShape'`、`ReadyFuel`、`GalilLeafFb/Dp/Pos`、`GalilTrailRad`、`LocalWF`（局所 7/10）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

`pal_in_peg_final4`（`H_oracle2`/`H_needLB'`/`H_realizeLB'`）。葉: `hends`/`hended`/`hlastMatch`/`ReplayBudgetR`/`RestartShape` 閉、`hquiet`/`houtReplay`/`hpres`/`hpos` は偽と判明し置換中。抽象 Tick の非決定性（`GalilTickDet`）→ `Fair` 方針。`TrailF` は `RadPack` 1 つに集約。局所モード 6/10 閉。詳細はルート CLAUDE.md 進捗節。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## n19 (2026-09-17) 5 エージェント統合・作業停止

GalilLexMeasure / GalilFinalAssembly3 / GalilNeedBound / GalilLookRefined / GalilNoShiftStage / GalilChainCoupling / LocalTrackingLatch / GalilReplaySpan を登録。lookahead を遅れ量依存にして needL' を Trail 不変量に還元、hbudget を無仮定で証明、shift 無し break の段入口を証明、ReplaySpan は偽（反例 aaaaabaaaab）で ReplayBudget+RestartShape に置換、局所ラッチ追跡から PAL を oracle 付きで導出。残りは ReplayBudget 条項 2・3、H_trail、hcopy/hcenR 接続、H_oracle 葉、局所 oracle 4 系統（詳細はルート CLAUDE.md の進捗節）。**全体 build 成功・標準公理のみ・無条件 PAL は未完。**

## 2026-09-17 追記（最終定理 `pal_in_peg_final` の骨組み — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilFinalAssembly.lean`（登録・build 0 errors・標準公理のみ）: `pal_in_peg_final : RecognizedByTotalPEG PAL`。**残る名前付き仮定は 6 個に確定**:
- (A) `H_oracle`：各語で cost 付き prefix oracle `CycleOracleMC`（区間構成の葉・出口ごとの `CostedRun`）
- (B) `H_truncTick`（未着文字を切っても tick が成り立つ）、`H_suf`（FIFO は語の接尾辞）、`H_needLe`（checkpoint m+1 前の消費 ≤ m+1）、`H_base`（`Tc 1 ≤ 2050`）
- (C) `H_realize`：局所 `LocalStep` 機械（ラッチ・stutter・2^18 手/文字）の受理 ↔ `LatchTrue`
（`H_letter`/`H_first`/`H_empty`/`needS 0`/`Preload.tc0/mono`/`O_cost`/報告点は証明済み。）
同時に登録: `GalilCostedFound`（found サイクルの `CostedRun`、shift あり・なし）、`GalilReplayGeneral2`（replay 中 chain の再証明、`WatchOk` 撤廃；残 `ReplaySpan`＝replay 中に found した周期ブロックが着地回文の周期であること — 真偽要検証、偽なら replay 中の break→restart を許す必要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-17 追記（台帳の骨組み完成・大量の穴埋め — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ（Opus 5 での再開分、2 回目のまとめ）:
- **台帳の骨組みが閉じた**: `GalilLindley`（Lindley 漸化式 ≤ backlog、`run_on_time`）、`GalilLedgerCentres`（語だけの中心列 `Cw`、`cw_pal`）、`GalilLedgerQ64`（K=10 最小、`alpha' = 8M+12704`, `beta' = 4M+8026+shiftCost`, `2(α'+β')+1 = 90617`）、`GalilLedgerAssembly(2)`（`ledgerObligation_of_oracles'`：O-check/O-base/O-step/O-cost → `LedgerObligation`）、`GalilThrottledRun`（到着待ちで stutter する抽象走行、`O_step_throttled`（仕事量 2Δ+1）、`ledger_throttled`；残 `TruncTick`・`SufVM`・`Preload`）、`GalilLedgerThrottled`（τ = 2^18：`2·90617 ≤ 2^18`；局所 `nLocal` を 2^18 に）、`GalilLatchTracking`（受理＝ラッチ、`pal_in_peg_of_latch`）、`GalilArriveChain`（到着が chain verifier にも届く、`NoStart` 撤廃、`pal_in_peg_of_latch'`）、`GalilTickArrive`。
- **checkpoint と区間コスト**: `GalilReportPrefix`（任意 prefix の報告点、replay 後も）、`GalilCheckpoints`（`CycleOracleM` → 単一走行上の単調 checkpoint 時刻）、`GalilOracleM`（`cycleOracleM_of_pieces`、報告点後の再開は無仮定）、`GalilRunTrace`（サイクル記録、frontier 単調）、`GalilFrontMono`（frontier は tick ごとに非減少、`cycleOracleL'_of_pieces`；残 `CentreLive`）、`GalilIntervalCost`/`GalilPlaceEvents`/`GalilOneFallback`/`GalilTraceCost`（`PlaceEvent`・`ShiftEv`・`FallbackEv`、場所ごと fallback ≤ 1、`checkpoints_cost`：m ≥ 1 の区間コスト）、`GalilCostedFallback`（走査区間・目標一致・fallback+replay の `CostedRun`）。
- **H_run の穴**: `GalilOracleLocal`（局所形 `InvL`/`LocalReport`）、`GalilFoundRadiusBound`＋`GalilLaterRadius`（`radius ≤ 4090h−2052` を全 stage で穴なし：debt 台帳の打消し）、`GalilPrepClock`（準備区間を任意 clock で）、`GalilPrepMatch`（**`hmatch` は一般に偽** → 準備中の不一致は fallback：`prep_segment_construct_or_fallback`、`fallback_from_prep`）、`GalilCatchUpDistance`（`4h ≤ distance` ⇔ shift guard）、`GalilEarlyBreak`＋`GalilBreakTerminal`（`StageEntry` 完全放電）、`GalilReplayGeneral`（**空虚と判明**：`WatchOk`+`hgood` 矛盾、`GalilWatchOkInst.no_watchOk_instance`；`SpanCore`/`span_watch_tick` で再証明中）、`GalilGlueBLeaves`＋`GalilInvPlus`（`InvLP`＝`InvL`＋カウンタ、全 landing で保存、`SegReachedW`、`fallbackRouteP_of_mismatch''`）。
- **H_realize 局所層**: `LocalArrivalTiming`（**`hfast` 偽**：scaffold は fallback 中 scan 停止 → ラッチ方式へ）、`LocalReplaySwap`（2 本 swap は閉じない：`never_twin_of_sigma_lt`）→ `LocalReplayParked`（replay 中の右頭＝停めたビューの `left^[残 replay]`、左ミラー 1 本で足りる）、`LocalTick3`（shift/fallback 各モードの局所 tick、c₃ = 66）。
**走行中**: found の cost 付き走行、replay 中 chain の再証明、`CentreLive`、`TruncTick`、τ 汎用の到着待ち走行。**無条件 PAL ∈ PEG は未完**。

## 2026-09-17 追記（Opus 再開分：局所 oracle・ラッチ還元・台帳の橋の設計 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilOracleLocal`（`InvL = InvS ∧ OutputRel`、`LocalReport`（現在状態からの報告）、`run_from_invL`、`H_run_of_oracleL`、`cycleOracleL_of_pieces`）、`GalilFoundRadiusBound`（第 1 stage `radius ≤ 2h ≤ 4090h−2052`、後段は `n < 4h`；残 `htime`/`hprev`/`hbar` 外注中）、`GalilPrepClock`（準備区間を任意 clock・比較混在で構成、`2h+2 < delay` 撤廃；残 `hmatch`・`1 ≤ lag0`）、`GalilCatchUpDistance`（**`4h ≤ distance` は候補からは出ず shift guard の margin ≥ 0 と同値**：shift 分岐で `places_of_guard`・`phase_of_guard`）、`GalilEarlyBreak`＋`GalilBreakTerminal`（break は一致比較なので終端でしか起きない ⇒ `stageEntry_after_found_closed`：`StageEntry` 完全放電）、`LocalArrivalTiming`（`Ahead` は位置上界から；**`hfast`（1 文字ごとに 1 place）は偽**：scaffold は fallback/shift/replay 中に scan が止まる）、`GalilLatchTracking`（**受理＝ラッチ**：最新文字位置の非 replay refresh の出力；`latch_sound`/`latch_complete`、最終定理 `pal_in_peg_of_latch`（仮定 `AbstractRun`・`H_realize`（受理↔`LatchTrue`）・`H_ledger`（回文なら T(w) までに refresh 済み報告点）・`H_empty`））、`LocalReplaySwap`（2 本ミラー swap は正しいが旧右ビューは再利用不能（`never_twin_of_sigma_lt`）→ 右頭は「停めた物理ビューの `left^[残 replay]`」と読む設計 (b) を外注中）、`GalilReplayGeneral`（`hquiet` 撤廃：replay 中 found → `FoundLanding`（`ReplayChainSeg` で replay 完走、chain 稼働中 landing）；残 `StartOk`・`WatchOk`/`hgood`）。

**台帳の橋（Plan 結論）**: `C m` は語だけで定義（位置 2m−1 の最左 live 中心、`m ≤ C m`・単調・回文なら `C |w| = |w|`）。`d (m+1)` = 報告点 m→m+1 の抽象 tick 数。到着で絞られた走行の遅延は Lindley 漸化式で `backlog d c m` に上から抑えられ、backlog 0 ⇒ `S m ≤ (m+1)τ`（τ = ticksPerSymbol、`T w = (|w|+1)τ`）。**定数が不整合**：`nLocal = 4096` では足りず `c ≈ 45296` → τ = 2^17 に；`stage_meets_barrier` の M ≥ 9600 は q=64 版の係数補題（K=10, M ≥ 240）で回避；chain shift 費用を 6 つ目の和分項に。補題順: cw 系 → q64 係数 → `runL_trace`（landing 列）→ **`report_at_prefix`（任意 prefix m の報告点到達）** → **`interval_decomp`（6 和分解）** → hledger' → **`tick_arrive_comm`**／到着絞り走行 → `lindley_le_backlog` → `ledgerObligation`。最大リスク：到着待ちは実機では `scan_wait` 背景 tick（search は進む）なので、pre-loaded 走行との一致ではなく「到着絞り走行そのもの」で checkpoint を定義すること。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（停止前の最終バッチ — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ（usage limit 復帰後のバッチ）: `GalilPrepTrace`（prep 補題を `ChainTicks` トレース基準に、`ReplayChainSeg` からも供給可）、`GalilEmptyWord`（`H_empty`：`accept' q := outQ q ∨ q = initQ`、`init` モードには戻らない）、`LocalSchedule`（DP/fpp 消去・ミラー再構築の期限；**replay 後の右頭複写は 1 セル/tick 歩行では半径 > 2049 で不可能**（`walk_schedule_infeasible`）→ 中心同期ミラー・カーソルとの `vmViewSwap`（0 tick、`abs_vmViewSwap` 証明済）に設計変更）、`GalilOracleGlueB`（`hmismatch` 放電：`fallbackRoute_of_mismatch`、残 `FallbackCounters`（偶数窓長）と `FallbackTick`）、`GalilLastLowerBreak`（`3h ≤ last` は `4h ≤ distance` に還元＝phase 4 と同じ穴）、`GalilChainTickable`（`ChainOk` 不変量、`chainTickable_unless_break`、`no_break_during_replay`）、`LocalAlloc`（予備 3 本・P = 13 で役割単射保存）、`GalilOracleGlueA`（`hsegment` 放電（残 `hout/hlive/hends`）、`lastMatch_report`；**発見**：`GlobalReport` は `Control.initial` からの走行を要求するので、再帰途中では接頭辞が無い → oracle は局所形 `CycleOracle`（`ReportReach`）に再配線すべき）、`GalilPreludeEnds`（**発見**：`chainStart` の初期 lag は `radius` なので `PreludeEnds` の上界は `radius + 2h+2`；`prelude_done_before_extent'` は新義務 `radius ≤ 4090h − 2052` を要求）、`LocalChain`（chain のテープ化：`ChainL`、`absChain`、全 `ChainStep`/`ChainMatched` 構成子の単一動作ステップと模倣、`c₂ = 4`、`alias(last, boundary)` は役割回転＋detach ミラー；残 `SpareSynced`/`Refilled`/`Fed`/`ProperView` の保存）、`LocalTick1`（scan の wait/count/match の局所 tick、c₁ = 66、`tickL1_abs`・`tickL1_local`・`tickL1_inv`；残 `SearchLocal.effect`・chain tick・`Ahead` の保存）、`GalilOracleGlueC`（`hfound` 放電：`foundRoute_of_pieces` で `RealStop` 5 分岐・round 終端 5 分岐を全部処理、葉仮定約 30 個を列挙；`hfoundBg` は `prep_segment_construct` が `clock = delay` を要求するため未（`clock ≥ 2h+3` 版が要る））。

**次回の再開手順**: (1) `CycleOracle`（局所形）への再配線と GlueA/B/C の葉仮定の放電（多くは `InvS` に `OutputRel`・`FallbackCounters`・`Aligned` を足すだけ）、(2) `hquiet` を `ReplayChainSeg` 経路に置換、(3) `4h ≤ distance`（catch-up 台帳）、`radius ≤ 4090h−2052`、`prep_segment_construct` の clock 緩和、(4) 局所層：`TickL1`、`TickL` 全構成子＋stuttering 模倣、`vmViewSwap` を `GalilVML` に組込、O5 の到着タイミング、`LocalChain` を `GalilVML.chain` に接続。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（本日の到達点まとめ・作業停止前 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

**状態**: `lake build --quiet PalPeg` 0 errors、`PalPeg.lean` 約 690 import、新規モジュール約 100 本（全て標準公理のみ、`sorry` なし）。usage limit のため一時停止。次回は下記「残作業」から再開。

**トップダウン骨組み（確定）**
- 最終定理 `pal_in_peg_of_tracking : Tracking M … → RecognizedByTotalPEG PAL`（`GalilRealizeOfTracking`）と `pal_in_peg_of_oracles`（`GalilRunSkeleton`）。`ScaffoldRun` の述語は `True` に弱化済み（最終定理は走行の内容を使わない）。
- **H_run** = `CycleOracleG`（`GalilRunSkeleton`）の放電。`GalilOracleDischarge.cycleOracle_of_pieces` が全終端の場合分けを済ませ、残りは名前付き仮定 11 個：`hex`（具体 Shared の replayExhausted）、`hsearch`/`hpres`（search 共走の存在・保存＝`SearchReady`、`GalilSearchReadyInv` で `RunEntries` に還元、第 1 stage は `GalilRunEntries`、後段は `GalilSearchWait`）、`hquiet`（replay 中に found にならない — **偽**：`GalilReplayFound`；対処は `GalilReplayChainSeg`（replay 中に chain が動く区間帰納）で `replay_after_fallback` を置換すること）、`houtReplay`（replay 後の出力健全性）、`hsegment`/`hended`/`hlastMatch`/`hlastMismatch`（区間終端→報告点：`GalilOracleGlueA` 外注中）、`hmismatch`（`GalilOracleGlueB` 外注中）、`hfound`/`hfoundBg`（`GalilOracleGlueC` 外注中）。
- 供給側の補題は揃っている：区間構成 3 種＋`lastLetter` 終端、`FoundCycle`/`FallbackCycle` 接着、`foundCycle_step'`（landing 記録・半径同定）、`cycle_found_noshift`、`cycle_found_*_bg`、`fallback_landing`（全輸出）、`inv_after_fallback'`、`replay_after_fallback`（→`InvScan`）、`fallback_from_watch`（round 途中の不一致）、`round_scan_construct`/`roundEnd_midFallback`、`GalilRoundPeriod`（ℓ+π=2C の同一性で `Good`/`hbreak` 完全放電）、`shiftPack_concrete`、`prep_segment_construct`＋`prep_then_watch_construct`、`GalilWatchPhase`（phase=4 は消費数 4h から；残り `htrace`・`hcount`）、`GalilPreludeDone`（残 `PreludeEnds`）、`GalilRadiusConsumed`/`GalilLastRadius`（`StageEntry` 放電、残 `Aligned` の配線と `3h ≤ last`）、L1–L11 全部。
- **H_realize** = `Tracking`。骨組み `LocalTracking.tracking_of_oracles`（O1–O6；O7 は消滅）。局所層：`LocalCounter`/`LocalRoles`/`LocalMirror`（radius・lower・length のミラー）/`LocalBuffers`/`LocalInputView`/`LocalBudget`/`LocalState`（`GalilVML`・`abs`）/`LocalArrival`（到着不可視の `abs'`、`Ahead`）/`LocalTick2`（restart 系 4 コミット）/汎用 `LocalStepRealize`（K 局所 step ⇒ `StructuredMachine`）。未：`LocalTick1`（scan tick）、`LocalChain`（chain のテープ化）、`LocalSchedule`（ジョブ期限、replay 後の頭複写は 1 セル/tick では間に合わず view swap 設計が必要）、`LocalAlloc`（役割単射・空きテープ）、`H_empty`（`initial.output = false` なので accept を `outQ ∨ q = initQ` に）、O5（到着タイミング・報告点）、chain の `last`/`periodLength` テープとの接続。
- **実時間台帳**：義務 1–5・7・8 形式化済み（機械仮定つき）、義務 6＝`MInv`。`hledger` の 5 和分解は未。

**モデル修正（本日）**: `periodLength` の +1 削除（Scala 準拠、具体 P で life 系が空虚やった）。**モデルの事実**: 背景 tick でも found → chain 起動（`hbg` 偽）、replay 中でも found → chain 起動（`hnfR` 偽）、round 途中の不一致は fallback（`shiftGuardVM` は `singlePositive` 要求）、`Restarted` は replay 後には成立せず `InvScan` で再帰。

**残作業（優先順）**: (1) GlueA/B/C の着地と `hquiet` を `ReplayChainSeg` 経路に置換 → `CycleOracleG` 完全放電 → `H_run` 完了。(2) `SearchReady` の `RunEntries` を stage ごとに再索引（連結全体は debt 非単調で偽）。(3) 局所層：`LocalTick1`/`LocalChain`/`LocalSchedule`/`LocalAlloc`、`TickL` の全構成子と stuttering 模倣、O5 の到着タイミング、`H_empty`。(4) `PreludeEnds`・`htrace`/`hcount`・`3h ≤ last`・`Aligned` 配線の小穴。

## 2026-09-16 追記（RunInv2・PrepConstruct・LocalTick2 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunInv2.lean`（`inv_after_fallback'`：`R = 0 → Inv`、`0 < R → LandingReplay`；残る仮定 `hfrT`＝`Frontier` は `fallback_landing` に `t.right = left^[R] (right s.right)` を輸出させれば消える）、`GalilPrepConstruct.lean`（`prep_segment_construct`：copy h・分岐・back h+1 ＝ 2h+2 の背景 tick を `WatchSegE` として構成（`active_background_exists`：非 idle chain の各 `ChainStep` は背景 tick 1 つで実現可能）；`hh : 2h+2 < delay` はこの構成の都合（モデルは copy 中の比較も許す）、`hphase = 4` は watch 中に確立されるので未）、`LocalTick2.lean`（restart 系の局所コミット：`commitRestart`（1 step：役割再指定・`resetSeg`・`resetL`・ミラー detach・極性反転）、`commitReplay`（2 step）、`commitShift`（2 step）、`commitFallback`（2 step）；`abs_commit*` と `restartVM_commitRestart`/`replayStartVM_commitReplay`/`beginShiftVM_commitShift`；残: `length` のミラー（`work := inc length`）、chain 局所化との接続（`last`/`periodLength` を持つテープ）、役割単射の再確立と空きテープ割当、ジョブの期限）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（H_run 骨組み完成・補題群 12 本 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunSkeleton.lean`（`CycleOracle(G)` ⇒ `run_from_restarted`（測度 `2|w|−position center`）⇒ `H_run_of_oracleG` ⇒ `pal_in_peg_of_oracles`；残り＝oracle の放電）、`GalilBootVM.lean`（`initVM0`、`H_run_of_oracle_boot`）、`GalilRewindSafe.lean`（`RewindPhase` で mode ガード；`CentreLive`（rewind 中に中心が原点に達しない、MARKS 印の性質）が唯一の仮定）、`GalilPreludeDone.lean`（`prelude_done_before_extent`；`PreludeEnds`＝copy/back の tick 数 2h+2 が仮定）、`GalilShiftPack.lean`（`shiftPack_concrete`：`0<h ≤ radius` と `ScanInv` から `ShiftRun` 構成；`hlock` は使用点で自明）、`GalilReplayFound.lean`（**replay 中の found は Scala でも Lean でも起きる**：replayStart で search 再開、第 1 stage ≤ 504 tick ≪ 2047；`SearchHalted` 版の報告点補題）、`GalilReplaySegment.lean`（`replay_after_fallback`：r·delay tick の replay 区間、landing は `InvScan`（`Restarted` は search の条件で不成立）；仮定 `SearchQuiet`）、`GalilFoundLanding.lean`（`foundCycle_step'`：landing 制御記録・半径同定、`stageEntry_after_found`；仮定 `Aligned`（`Inv` に入れる）、`hend3/hcenterS`、`hlow`）、`GalilRoundPeriod.lean`（**同一性 ℓ+π = 2C**：左読みと chain 予測は原点中心の鏡像 ⇒ 終端前は予測が常に正しく（`Good`）、終端では origin の不一致対で必ず破れる（`hbreak` 完全放電）；`hmid` の残りは「round 途中で scan が不一致にならない」ではなく、**途中不一致は起こりうる**（周期が延びない入力）→ `RoundEnd` に 4 つ目の終端（fallback）が要る）、`GalilSearchWait.lean`（`searchRun_waiting`、`runEntries_of_later_stage`、`runEntries_two_stages`；連結全体の `RunEntries` は debt 非単調で偽、stage ごとに再索引が必要）、`GalilCycleNoShift.lean`（shift 無し found サイクル 3 本）、`LocalTracking.lean`（追跡骨組み `tracking_of_oracles`（O1–O7）；**発見** O4/O4b が矛盾：抽象 `Tick` に到着規則が無いので、到着は抽象で不可視にする設計（abs の incoming = far ++ pending）が必要）。区間構成 3 種に `lastLetter` 終端を追加済み。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（接着・背景起動・fallback landing・追跡還元 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilReportReplay.lean`（replay 後の報告点 `scaffoldRun_report_after_replay`；仮定 `hnfR`＝replay 中に search が found にならない（調査中）、`hhead/hlast`）、`GalilCycleGlue.lean`（`fallbackCycle_of_constructions`・`foundCycle_of_constructions`：区間構成 3 本から前提束を組立；**構造的穴** `hland`：`life_restarted` は準備区間 `bs ++ dm :: cs`（copy h・分岐・back h+1）を要求するが L7b は空の準備区間を出す → `GalilPrepConstruct` 外注中）、`GalilCycleFoundBackground.lean`（`life_from_prep_*`（found tick を外した life）、`cycle_found_stepsAll_bg/_minv_bg`：背景 tick で chain 起動する found サイクル）、`GalilFallbackLanding.lean`（`fallback_landing`：制御記録・`Restarted`・`hpal/hmax`・`replay = ofNat R`・`ShiftIdle`・chain idle を一括輸出；`leftmost_after_fallback_landing`）、`GalilRealizeOfTracking.lean`（`Tracking M …`＝M の走行が 1 本の scaffold 走行を追跡して報告点で出力一致 ⇒ `pal_in_peg_of_tracking : RecognizedByTotalPEG PAL`；`H_realize` の ∀y 形は `Refreshed` 無しでは導けないが `pal_in_peg_of_galil`（結合存在形）経由で不要）。新たな穴: shift 前に period が破れる「shift 無し found サイクル」（`GalilCycleNoShift` 外注中）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L9 Inv・1 round の scan 構成 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunInv.lean`（`Inv` 10 項目のうち stage/block/search/input は `Restarted` から無料（`restarted_unique`）、`inv_init` は完全放電、`inv_after_fallback` は `chosenRadius = 0` 限定（**発見**: 正の半径では landing が `replaying = true` なので `Inv` に replay 版が要る）、`inv_after_found` は `FoundResidual`（mode・stage・frontier・replayRest・shiftIdle）を仮定、`RewindSafe`・`frontier_replayRest_steps`）、`GalilRoundConstruct.lean`（`scan_half`：measure 付きで 1 round の scan を構成（燃料なし）、`round_scan_construct`＝`hround` そのもの；`hidx` は不要（lag 0 では `Internal` は idle のみ、一致比較は `chainMatched_watch_total` の二分法）；残る仮定 `hmid`（終端前は一致＋Good）・`hbreak`・`hpack`（`ShiftPack`）・`hsinv`・`hmeasure`）。外注中 13 本（replay 区間、fallback landing の輸出、found landing の制御記録と半径同定、`RewindSafe`、`hmid/hbreak`、`hpack`、`hcaught`、接着、背景起動 found、wait 相持ち上げ、局所層 TickL1/TickL2）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（後段 stage'・mismatchOther・LocalState — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilSearchResult.search_later_stage'`（後段 stage の `.run` 突入で preload 恒等式・`Canonical debt`・count ≤ debt・予算を追加；残: wait 相 `enter_boundary` の `searchStep` への持ち上げと `es` の分割）、`GalilMismatchCaught.lean`（`match_of_palAt`、`run_lag_zero`（lag 0 は watch tick で不変）、`lag_zero_before_bound`（2k+2 tick で追いつく）、`no_mismatch_before_caught`（候補の回文延長は `2h`）、`mismatchOther_impossible(_of_candidate)`；残る仮定 `hcaught`＝不一致時に chain が既に watch である＝copy/back 前奏の完了）、`LocalState.lean`（`Ctr` 10 種、`GalilVML P`（InputView 5 本（search walker も）、分節カウンタ bank＋roles/pol、radius/lower ミラー、DP/fpp 二重バッファ、chain は抽象のまま）、`abs`/`absState`、`abs_job_irrelevant`・`abs_resetL_dp/fpp`・`abs_radius_mirror_negate`・`absCtrs_move`、局所性 `StepLocal`/`Local`）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（RunEntries 第 1 stage・hbg は偽 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilRunEntries.lean`（`runEntries_of_calibrated`：`Restarted` 形の search から calibrated 第 1 stage の `RunEntries`（長さ仮定は等式：debt 側条件が余剰イベントに非単調なため）；後段 stage（wait/double 経由）は `search_later_stage` に preload 恒等式・debt 条件を追加要求中）、`GalilBackgroundNotFound.lean`（**`hbg` は偽**：DP quantum はイベント非依存で背景 tick でも `.found` に達し、`backgroundS` が `chainStart` を据える（`chainAt_background_found`）。対処: L7a に `SegEnd.foundBackground` を追加、found サイクル補題の背景起動版 `cycle_found_*_bg` を外注中）。外注中: L9 `Inv`、replay 後の報告点、mismatch は catch-up 後のみ、1 round の scan 構成、サイクル接着、局所層 `LocalState`。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L4/L7/L11 完了・局所層 6 部品・汎用実現補題 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ:
- L7a `GalilSegmentConstruct.lean`（`watchSegE_construct`：chain-idle 区間を燃料で構成、終端は `SegEnd`＝入力尽き/不一致/found；新仮定 `hbg`＝背景イベントで search が found にならない）、L7b `GalilSegmentConstruct2.lean`（`watchSeg_construct`、終端 `WatchStop`＝ended/mismatchWatch/mismatchOther/broke/outOfFuel；`Good`（lag 正）と `Ctx.hpres` は仮定）、L7c `GalilSegmentConstruct3.lean`（`rounds_construct_inv`：`RoundInv`（`rounds_leftmost` の束）を保って m round → `RoundEnd`＝break/入力尽き/guard 失敗；1 round の scan 半分は oracle `hround`、`roundInv_good` は `hidx`（span の 2 つ右まで周期）を要求）。
- L4 `GalilReportReach.lean`（`report_of_last_consume`：最後の文字を消費する一致比較の直後が報告点、`scaffoldRun_report_of_last_consume` は `H_run` の形そのもの；不一致＋shift 経路は `shift_done` 後、不一致＋fallback 経路は replay 完了後の一致比較まで報告点にならない（`Refreshed`・`notReplaying` が失敗、正しい））。
- L3 補強 `GalilReplayRest.lean`（`replayRest_tick`：全 24 構成子で保存、`replayStart` は `radius = ofNat r` を要求）、L11 完結 `GalilRadiusConsumed.lean`（`Aligned o`（`ofOnly`・`rounds_origin` から無料）、`radius_le_distance`、`foundCycleStage_final`：`3h ≤ last` と break データだけで `StageEntry`）、`GalilFppRunSupply.lean`（`fpp_scheduled` の停止走行から `Supplies`、`fppEnabled_along_phase`）、`GalilRunEntries.lean`（`RunEntries` 放電、詳細は次エントリ）。
- 局所層: `LocalInputView.lean`（`RTQueue`（Hood–Melville、登録済）を再利用、`InputView` は back/focus/near/far、`reposition_reaches`：距離 d の頭複写＝d 局所 tick、`two_views_absHead`）、`LocalBudget.lean`（`clear_fits_stage`、`counter_rebuild_fits_stage`、`radius_changes_slowly`：2048 tick 内に radius 変化 ≤ 1；`lag/margin` は copy 相を跨いで detach 不可、`work` は二重バッファ必須、`restart` の radius 保存は仮定）、汎用 `LocalStepRealize.lean`（`LocalStep`（K 局所）→ `realize : StructuredMachine … (n·(7K+2))`、`realize_srun`/`realize_SAccepts` 無条件；意味論は `readWin_eq`/`pos_sweep`/`rd_sweep`（`K ≤ pos` の余白が必要、`STape` は片側無限））。
**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L3 Frontier・fpp quantum — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilFrontier.lean`（L3：`Frontier s`（`position right + replay ≤ 2·arrived`）、`frontier_replayStart(_scan)`、`frontier_tick`（具体 frame の全 25 構成子で保存；仮定 `ReplayRest`＝replaying フラグが下りてれば replay カウンタは reset、`hrep`＝replayStart 時の再播種）、`consume_not_replaying`：新文字を pop する tick は replay 中でない）、`GalilFppQuantum.lean`（`Safe`/`Reach`/`Legal`、`run_exists_of_reachSafe`、`fpp_run_exists(_of_legal)`；pc の範囲外は `marked_targets_lt` で排除済み、残るは `Legal`＝marked プログラムのテープ内容不変量、あるいは FPP 正当性定理の走行から直接引く）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L11 GalilLastRadius — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLastRadius.lean`（登録・build 0 errors・標準公理のみ）: 境界台帳 `Aligned`・`aligned_word`・**`sweep_gap`**（未破断の掃引で `distance + 1 ≤ last + 2h`、`+1` の厳密さが break 場所を吸収）、`offset_gap`・`break_gap`（shift・break で不変）、`stageEntry_of_gap`（`3h ≤ last ∧ Rad ≤ last+2h → 3·Rad ≤ 5·last`）、`foundCycleStage`。残る唯一の隙間 `RadiusConsumed Rad c : Rad ≤ distance + 1`（半径−距離のロックステップ不変量、基底は `ReadOrigin.startBefore` の shift 版 `position start + shifts·h ≤ center` が必要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L6・局所層 Roles/Mirror — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilSearchReadyInv.lean`（L6：`DpSafeRem`（残イベント数で再索引した `DpSafeHere`）、`ReadyRem`、`searchReady_begin/restarted/step/run`、`searchEffect_exists_of_restarted`；残る唯一の仮定 `RunEntries`＝`.run` 突入 tick で preload 恒等式と残イベント予算が成立すること、calibrated stage 補題との接続が未）、`LocalRoles.lean`（役割置換 `moveRoles`＋1 本の `resetSeg` で `dst := src; src := reset`、`absL_move`）、`LocalMirror.lean`（同期ミラー `pushAll/popAll/resetAll` は各テープ 1 動作、`absCtr_mirror`、`negate_via_pol`（= `initialDebt`）、再構築は犠牲複製 `don` を pop しつつ spare に push（`read_costs_value`：単頭では読取が値を壊す obstruction を定理化）、`rebuild_done`）。外注中: L3・L7a/b/c・L11・後段 stage・fpp quantum・`RunEntries` 放電、局所層 InputView/Budget、汎用 LocalStepRealize。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L5/L10・L8 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilChainReadyProgress.lean`（L5 `chainReady_of_blockInv`：`BlockInv` 超過分は copy の `CopyInv`、back の `canRight`、watch の `Good`/`canRight`、broken 排除のみ；L10 `found_cycle_center_progress`：中心は正確に `(m+1)·h` 前進（`MInv` 不要）、`fallback_cycle_center_progress`：`cen+1 ≤ 新中心`（境界 `2r = position` の除外 `hrn` が追加仮定））、`GalilTickFun3.lean`（L8 `PhaseEnabled`（shift/copy/home/fpp/markEnd/choose/rewind の前提）、`phase_tick_exists`、`EnabledP`/`tick_exists_P` で全モード被覆；fpp は Machine 9 の quantum 存在を仮定＝未存在の補題）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（L1/L2・局所層 Counter/Buffers — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilEndOfInput.lean`（L1 `not_canRight_iff`：`¬canRight ↔ position = 2|w|`、L2 `last_letter_position`：最後の文字を pop する移動で `2|w|−1`、`position_le`）、`LocalCounter.lean`（分節 unary カウンタ：`push/pop/resetSeg` は 1 書込＋1 移動、`absCtr`、`absCtr_reset = reset`、極性反転 `neg_flip`；頭は最上マークの一つ上（frontier）に置く設計）、`LocalBuffers.lean`（`Buffered n`：二重バッファ、`resetL` は O(1)、`clearTick` で idle 側を並列 1 セル/tick 消去、`clearTick_done`（W+1 tick）、`abs_resetL_matches_control`：`GalilScaffoldControl.reset` と一致）。外注中: L3・L5/L10・L6・L8・L11、局所層 Roles/Mirror/InputView/Budget、汎用 LocalStepRealize。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（periodLength 修正の追従完了 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilShiftH.lean`（`shift_h_eq_pos11`：shift の h ＝ DP の `pos 11`、`interior_eq_pos11`）・`GalilSearchResult.lean`（`periodLength_watchStart = ys.length+1`）を新定義に追従、`GalilStructuredSkeleton.lean` の `ScaffoldRun` を `galilFrameS`・`SoundScanNR` に変更（サイクル補題の形と一致）。全体 build 0 errors。外注中: L1/L2（入力尽き位置）、L3（frontier）、L5/L10、L6（`SearchReady` 保存）、L8（残モードの全域性）、L11（`Rad ≤ last+2h`）、局所層 `LocalCounter`、汎用 `LocalStepRealize`。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（主ループ Cycles・periodLength 修正・2 設計書 — 全体 build は 2 ファイル修正中・標準公理のみ・無条件 PAL は未完）

登録: `GalilMainLoopMInv.lean`（`FoundCycle`/`FallbackCycle` 前提束、継続スタイルの `Cycles`、`foundCycle_step`/`fallbackCycle_step`/`cycles_stepsAll_minv`、`leftmost_one`、`init_minv`；found 側の `Restarted` は `life_restarted` の前提が広いので前提束に同梱）、`GalilShiftH.lean`。
**モデル修正**: `GalilScaffoldTopGuards.periodLength` の `+1` を削除（FRONT セルを数えていた；Scala `beginChainShift` は DP の h＝複写ビット数で shift）。修正前は具体 `P := galilShared … beginShiftVM'` で `hint : interior.length+1 = h` と `hb` が両立せず life/rounds 系が**空虚**やった（抽象 `P` では無矛盾）。`GalilShiftH`/`GalilSearchResult` の周辺補題を追従修正中。
**H_run 構成計画（要点）**: `run_from_restarted` を測度 `2|w| − position center` の整礎再帰で。`Restarted` 状態の不変量束 `Inv` = Restarted・MInv・OutputRel・mode=scan/¬replay/clock=2048・StageEntry・SearchReady・BlockInv・Decodes・入力配置・ShiftIdle。3 分岐: 入力尽き（報告点＝最後の文字を pop した tick 直後、`¬canRight ↔ position = 2|w|`）／found／fallback。骨組み側の必須修正: `ScaffoldRun` を `galilFrameS`・`SoundScanNR` に。欠落補題 L1（`¬canRight ↔ position=2|w|`）L2（最後の pop で `2|w|−1`）L3（frontier 不変量）L4（区間の切詰め）L5（`ChainReady` ← `BlockInv`+`good_of_periodOn`）L6（`SearchReady` 保存＝debt 台帳、研究級）L7（区間構成 4 分岐、決定性不要）L8（shift/fallback モードの全域性）L9（`Inv` 再確立）L10（中心の前進）L11（`StageEntry`＝`GalilLastRadius`）。
**局所化計画（要点）**: 新層 `PalPeg/Local*`（既存無変更）、`GalilVML`・`TickL`・`abs`・stuttering 前方模倣＋2048 tick 内の進行補題。op1 reset＝区切り印 1 セル書込（分節 unary）、op2 死ぬ源の複写＝役割置換、生きる源＝常時同期ミラー＋背景再構築、op3 debt＝ミラー＋極性ビット、op4 `ofNat h`＝役割移動、op5 プログラム reset＝二重バッファ＋背景消去、op6/7 walker・頭複写＝カーソル専用入力複写テープ（実時間キュー）＋再配置ジョブ。見積 ≈3400 行。最大リスク: read-barrier と入力ビューの実時間キュー。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（局所性調査・restart 忠実性・EnabledR — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors: `GalilTickFun2.lean`（`clock_pos_invariant`：どの Tick も clock を 0 にしない、`replay_match_of_minv`：replay 中の比較は `MInv` から必ず一致、`EnabledR`・`tick_exists_R`・`enabledR_of_minv`）、`GalilChainEncode.lean`（`Sym2` 25 種、`encodeChain`（8 テープ）、`encodeAll_injective`）、`GalilSearchResult.lean` 追加分（`search_later_stage`・`later_stage_found_result`：後段 stage の帰納ステップ；全体の帰納は `.wait` 相の debt 台帳（実時間台帳そのもの）と `false` 詰め物の非可換で未閉）。
**H_realize の構造的障害（局所性調査）**: Tick の大半は O(1) 局所やが、7 種の効果が非局所 — `Counter.reset`（Θ(値)）、カウンタ複写（`work := span`、`lower := last`、`chainStart` の radius 二重化）、`initialDebt`（テープ反転）、`ofNat h`、`GalilScaffoldControl.reset`（全 12/9 テープ消去）、`beginFallback` の `walker := p`（Place 全体複写）、`initVM`/`replayStartVM` の頭 3 重複写。Scala 回路はこれらを O(1) ポインタ代入（`Ref.select`）で行う**ポインタ模型**で、テープ機械としては未償却。対処は「消去・複写を 1 セル/tick の遅延モード（`.clearing`/転送関係）に置換」というモデル改修で、上位補題に波及する。汎用「K-局所 step ⇒ StructuredMachine」補題（`LocalStepRealize`）は外注中。
**restart の忠実性（Scala 調査）**: `restartVM` の `lower := last` は `ScaffoldGalil.scala:230-238` と一致、窓 `8·max(k,1)` も一致、`3·Rad ≤ 5·lower` は機械の guard ではなく監査契約（`GalilContracts.scala:207`）。欠けるのは連鎖不変量 `Rad ≤ last + 2h`（`GalilLastRadius` 外注中）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（restart の設計仮定は偽 — 全体 build は SearchResult 改修中で一時保留・標準公理のみ・無条件 PAL は未完）

`GalilRestartStage.lean`（登録、標準公理のみ）: clock = delay は fallback/found 両 restart で `rfl`、init は `Control.initial` から継承（G1）。**G2: `3·Rad ≤ 5·value last` は found サイクル後の restart で偽**（反例 `(orgRadius,h,m,n,k) = (0,1,0,10,3)` 等）。`last` は連鎖の credit カウンタ（≈3h、減るだけ）で、半径は round 数 m・最終区間 n で増える。`search_result_at_tick`/`found_to_found` の `hstage` は現状放棄不可能な仮定。対処候補: (a) `Restarted` に stage 障壁を持たせ各サイクルで再証明（現状の `last` 意味では不成立）(b) `restartVM` の lower を連鎖 credit ではなく確認済み半径系の量に変える（Scala 正本の確認中）。`GalilSearchContractStage.lean`（登録）: `search_contract_of_stage` は `r ≤ span` が必要。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（tickFun・lag 正の Good・台帳 4/7/8 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

登録・build 0 errors・標準公理のみ: `GalilTickFun.lean`（`sharedFun`（Shared を関数版で固定）、`ChainReady`/`ScanEnabled`/`Enabled`、`tick_exists`、`tickFun`＋`tickFun_spec`、`runFun_steps`；除外: shift/copy/…/rewind モードの全域性補題無し、scan で clock=0、replay 中の不一致、broken chain は restart guard で被覆）、`GalilGoodLag.lean`（`good_of_periodOn`・`good_run_of_periodOn`：round の `PeriodOn` から lag 正でも `Good`、残る仮定は span 包含 `hidx`・`canRight`・`Reads`）、`GalilLedgerObligations2.lean`（義務 4 `fallback_cost_move` n ≤ 12704δ+4012、義務 7 `telescope_busy`/`realtime_of_telescope`、義務 8 `buffer_transparent`/`pal_in_peg_of_galil_buffered`、`hledger_of_obligations`：5 和分解の下で区間台帳）。方針メモ: scaffold は clock 駆動（delay 固定）なので実時間性は構成的、台帳は「報告点に間に合う」＝`H_run` の中身に畳み込まれる。次: `Enabled` の replay 拡張・clock≥1、Tick の局所性調査（`H_realize` の要）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（DP 共走の結果取り出し — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilSearchResult.lean`（登録・build 0 errors・標準公理のみ）: `SearchInv`（区間に沿った `SearchRun`）、`searchInv_watchSegE`、`search_result_at_tick`（restart 状態から idle 区間を経た found tick で `Result (take (8·max k 1+1)) k 0`・pc 346・pos 11 = 最小候補 h、または「前段 stage が非 found で終了」の escape）、`missed_pc_347`。隙間: (a) shift の h と pos 11 の同一視（`GalilShiftH` 外注中）、(b) 現在半径と stage 窓の較正（`GalilSearchContractStage` 外注中）、(c) 後段 stage の found（同エージェントに追加依頼）、(d) restart 時の `c0.clock = 2048` と `3·Rad ≤ 5·k`（設計仮定、未証明）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（分岐網羅 (iii)(iv) — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBranchInvariants2.lean`（登録・build 0 errors・標準公理のみ）: (iii) `PrepInv`（LEFT 印がテープ 7/10 で頭の左）を `prepare` で成立・全 `Tick` で保存、`prep_tick_exists`；(iv) `DpReached`/`DpSafeHere`（SafeQuanta 到達可能性）、`safeQuanta_exists_of_reached`（残予算で停止まで走り `Result` を出す）、`quantum_exists_of_reached`、`searchStep_exists`・`searchEffect_exists`（`SearchReady` の下で全モード）。残: `SearchReady` を top 側（`prepare` 発火・preload 入口）から配線、`hchain` 側は `BlockInv`、Tick 決定性は不要化の方針（`tickFun` は存在だけ使う）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（GalilVM のテープ符号化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilVMEncode.lean`（登録・build 0 errors・標準公理のみ）: 記号 `Sym`（14 種）、`encodeVM : GalilVM → Fin 41 → STape Sym`、`encodeState`（tape 0 = clock）、有限制御 `CtlFin`（`Fintype`）、`encode_injective`（`(encodeCtl x, x.vm.chain, encodeState x)` が単射）。残: `chain : ChainVM` の符号化（`Token` 11 種の `Fintype` と watch/verifier/consume 状態のテープ化）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（モデルの条件性の発見 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

調査結果: Lean の `GalilScaffoldChainWatch.Internal` には lag 正のときの period break 構成子が無く（Scala `ScaffoldChain.scala:182` にはある）、`Good` は全上位補題の背景ステップ前提に埋め込まれた**暗黙の仮定**。モデルは「不忠実」ではなく「条件付き」（lag 正で消費が不一致にならない走行に限定）。対処: 新構成子を足さず、round の `PeriodOn`（span は周期 2h の回文）から「verifier の読取位置が span 内なら `Good`」を証明する（`GalilGoodLag.lean` を外注中）。scan 不一致が period break より先に起きる Galil の性質そのもの。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（Shared の関数化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilSharedFunctional.lean`（登録・build 0 errors・標準公理のみ）: `beginShiftVM'` は一意（`beginShiftVM'_unique`）・`shiftGuardVM` の下で存在、`beginShiftFun`＋spec；`beginFallbackVM'` は本質的に非関数的（walker が任意、`beginFallbackVM'_not_unique`）だが `place s` で固定すれば一意（`beginFallbackFun place`）；`restartVM entry` は一意・`restartGuardVM` の下で存在（`restartFun`）。`H_realize` の道筋: (1) テープ符号化（実行中）(2) Shared 固定（済） (3) `tickFun`（次） (4) `Prog` 化・固定 B (5) 前方模倣。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（分岐網羅 (i)(ii)・台帳義務 3 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBranchInvariants.lean`（登録・build 0 errors・標準公理のみ）: `OnBlock/OnPrefix/WatchBlock/CopyInv/BlockInv`、`BlockInv` は `chainStart` で成立し `ChainStep/ChainMatched/ChainTick/ChainSteps` で保存（transfer 補題の `Q` としてそのまま使える）、`watch_good_or_break`・`chainMatched_watch_total`（`WatchReady` の下で全域）、`copy_step_exists`・`copy_run_to_back`・`back_step_exists`。残: `Internal.take` に break 構成子が無い（lag 正の背景 tick で `Good` を入力供給から示す必要）、`canRight` は実時間入力供給、back 歩行の停止、`CopyInv` の到達可能性、(iii)(iv)。
`GalilSearchContract.lean`（登録・標準公理のみ）: `search_contract_of_idle_search`（DP 結果 `hres`（idle 分岐 pc=347）と `hlow` の下で `galil_move_of_contract` の契約そのもの）、`galil_move_of_idle_search`（k ≤ 4δ）。義務 3 は `hres`/`hlow` に還元（`cycle_found_minv` と同じ仮定）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（cycle_found_minv — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLiveCentreCycle2.lean`（登録・全体 build 0 errors・標準公理のみ）: `cycle_found_minv` — restart 状態から idle 区間・found tick・chain の一生を経て次の restart 状態まで `MInv` を運ぶ（`cycle_found_stepsAll` の `MInv` 版、追加仮定は `hex`・語の分解・`hM0`・DP 結果 `hres/hpc/hout/hlow`）。fallback 側は `cycle_fallback_minv` 済み。次: サイクル列の帰納（`StepsAll ∧ MInv` を Restarted→Restarted で反復）と報告点到達。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（台帳義務 1・2・5 の Lean 化 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLedgerObligations.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: 義務 1 `stage_deadline`（`stageCost ≤ K·ell ∧ ≤ M·(2r−rad)`、K≥400・M≥24K の一様版；残る機械仮定 `hcost`）、義務 2 `verifier_catchup`（到着/サービス模型 `vlag`、追いつき 2·lag0、半径 4h 以内；残る仮定 `hmodel`）、義務 5 `replay_cost_le_window`（`galil_move_of_contract` を実窓に適用、残る仮定 `hreplay` と探索契約＝義務 3）、組立 `hd_of_interval_ledger`/`realtime_of_interval_ledger`（区間台帳 `d ≤ α·δ+β` ⇒ `realtime_of_predictable` の `hd`）。未: `hledger` の組立（義務 3・4・6・8）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（CC：life_minv — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilLiveCentreLife.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `life_minv` — found tick → 準備区間 → watch → 最初の shift → rounds → 最終区間 → break → restart 直後まで `MInv` を運ぶ（`hscan` は `position sF.center` 中心、`hraw` で語を分解、`hex` 追加、rounds の `replaying` は `hr1`）。完全性の機械側は残り「主ループ合成（found/fallback サイクルで `MInv` を一周させ、報告点まで到達）」のみ。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（トップダウン骨組み — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilStructuredSkeleton.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `pal_in_peg_of_galil`（`StructuredMachine M`・`Pof/qof/firstOf/delay`・`H_letter`・`H_first`・`H_report`・`H_empty` から `RecognizedByTotalPEG PAL`）。`ReportPoint`（非 replay・`ScanInvariant`・`MInv`・右頭が `2|w|−1`）と `Refreshed` を定義し、`output_iff_pal`（`refresh_exact` から報告点の出力 ↔ `w ∈ PAL`）を証明済み。残る実質は `H_report` ＝「scaffold の走行が報告点に到達する」（H_run）と「M の受理がその出力と一致する」（H_realize）の 2 つに分割中。以後はこの仮定リストを潰す。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 9：restart 後の lower 履歴 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBreakNoBelow.lean`（Sonnet 外注、登録・全体 build 0 errors・標準公理のみ）: `noBelow_after_break`（span [a,b0] に p 未満の周期が無く、[a,b] で周期 p が破れれば、[a,b] に p 以下の周期が無い）と `noBelow_after_break_of_mismatch`（不一致対から直接）。`break_not_period` と合わせ、restart 時の「lower 以下の周期が無い」不変量は純粋部分が閉じた。残りは機械側の合成（`life_minv`）と骨組み。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 8：break の周期破れ — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilBreakPeriod.lean`（Opus 外注、登録・全体 build 0 errors・標準公理のみ）: `break_not_period`（round の起点 `o : ReadOrigin raw`、終端比較状態 `s`、`hend : singlePositive s.cycle = true`、外側一致 `hmatch` の下で `¬ PeriodOn (encoded raw) (2h) (start+1) (position (right s.right))`）、`break_witness`（存在形）、`break_symbols_differ`、`break_prediction_mismatch`、純粋補題 `no_period_of_break`。既存の `matched_restart` は `broken = true` しか出さず、破れを起こす不一致は内部で消費されていたので、`check_pair` と `read_prediction_window` から再構成した。これで restart 後の lower 履歴（「span に lower の周期 2h が無い」）の材料が揃った。方針転換: 以後はトップダウン（`StructuredMachine` 骨組みを明示仮定付きで先に書き、残り仮定だけを外注）。**無条件 PAL ∈ PEG は未完**。

## 2026-09-16 追記（並列バッチ 7：報告点の接続 — 全体 build 成功・標準公理のみ・無条件 PAL は未完）

`GalilReportComplete.lean`（Opus 外注、ルート登録・全体 build 0 errors・標準公理のみ）: `leftFirst_iff_pal`（報告点 `position s.right = 2k−1`・非 replay・`ScanInvariant`・`MInv` の下で `leftFirstVM s ↔ IsPal (raw.take k)`）と `refresh_exact`（`refresh (galilFrame P q first)` の出力 `o = true ↔ IsPal (raw.take k)`）。これで「中心不変量 `MInv` が保たれていれば報告点の出力は回文フラグと一致」が閉じ、出力の完全性は `MInv` の維持（`life_minv`・主ループ合成）に還元された。**無条件 PAL ∈ PEG は未完**（残り: `life_minv`、restart 後の lower 履歴、主ループ MInv 合成、分岐網羅 (i)–(iv)、台帳義務 1・2・5、`StructuredMachine` 実現）。

# Claude Code 再開用 — PAL ∈ PEG の Lean 証明

更新: 2026-09-14（JST）。ユーザーから「現在の進捗を書き出して、あとでClaude Codeがresumeできるように」と依頼され、証明追加を止めて作成した。

## 最初に押さえること

## Resume checkpoint — 2026-09-15、Claude Code 再開

追記（2026-09-16 午前、並列バッチ 6）：AA `GalilRoundsLeftmost.lean`（**`rounds_leftmost`**：`Rounds` 帰納で各終端比較の `MInv`＋「2h 未満の周期なし」を継承、`periodOn_congr`）、BB `GalilNoBelowFirst.lean`（`noBelow_first`／`_of_result`：最初の終端比較の最小性）、DD `GalilPrepLeast.lean`（`prep_watch_start_least`：chain の半周期 h ＝ DP 出力 `(denote y.config).pos 11`、`found_output` で定義的一致；`result_pc_of_candidate`、`no_candidate_below_of_least`、`prep_least_no_candidate`）。全体 build 成功・標準公理のみ。外注中：CC `GalilLiveCentreLife.lean`（`life_minv`：found tick → 準備 → watch → 最初の shift → 周回 → 最終区間 → 破れ → restart で `MInv` 保存）。無条件 PAL は未完。

追記（2026-09-16 午前、並列バッチ 5）：V `GalilPeriodNext.lean`（`periodOn_restrict`／`periodOn_mul`／`periodOn_extend_dvd`（`0 < P` と長さ条件を追加）／`periodOn_fineWilf`／**`noBelow_next`**：周回間の最小性継承）、W `GalilPeriodSpan.lean`（`periodOn_span_of_next`／`hasPeriod_span_of_next`：右半分の周期＋現在と次の回文 ⇒ span 全体の周期 2h）、X `GalilReadOriginPeriod.lean`（`ReadOrigin.reshift_period`／`reshift_periodOn`）、Y `GalilCandidateWindow.lean`（`candidate_window_mono`、`no_candidate_below_least`）、Z `GalilOriginPeriod.lean`（`ReadOrigin.shifted_position`／`shifted_unbroken`／`origin_period`／`origin_periodOn`／**`origin_periodOn_right`**：各 origin の終端比較で右半分＋新 place の周期 2h、空トレースで `joined_input_period`）。すべてルート import 済み・標準公理のみ。外注中：AA `GalilRoundsLeftmost.lean`（`rounds_leftmost`：`Rounds` 帰納で `MInv`＋「2h 未満の周期なし」を各終端比較へ）、BB `GalilNoBelowFirst.lean`（`noBelow_first`／`_of_result`：最初の終端比較の最小性を DP 最小性＋origin の周期から）。進捗ボード artifact を v3 に更新。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 4）：U `GalilScaffoldTopProgressS.lean`（`backgroundS_exists`（探索 step と chain 効果の存在から background の存在）、`compare_progress_S`、`scan_tick_exists`：scan・`1 ≤ clock`・`replaying = false`・探索／chain の存在仮定の下で次 tick が存在。replay 中の不一致には `restart` しか無いので `replaying = false` を仮定）、S `GalilMinimalPeriod.lean`（`palAt_pair_of_period`、`result_least`（`Result` の証人 k は最小候補）、`no_short_period_of_minimal`：span の周期 2h＋DP 最小性（窓 `take (k+1)`）＋lower 以下の周期なし ⇒ 2h 未満の周期なし、Fine–Wilf 経由；元の `no_candidate_of_result` は偽（反例 `0^9`）で `result_least` に修正）。外注中：V（`noBelow_next`）、W（`periodOn_span_of_next`）、X（`reshift_period`：終端比較で検証済み区間の周期 2h を `joined_input_period` から）、Y（`candidate_window_mono`、`no_candidate_below_least`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16 深夜、並列バッチ 3）：L `GalilLiveCentreCycle.lean`（`cycle_fallback_minv`：Restarted＋`MInv`＋`SpanRep` → idle 区間 → 不一致 → fallback 一周 → `Restarted`＋`SpanRep`＋`MInv`）、T `GalilLiveCentreSegs.lean`（`minv_watchSeg`／`minv_scanSeg`）、N `GalilFallbackCost.lean`（`fallback_ticks_le`：fallback 一周（copy→replayStart）の tick 数 n ≤ 1588·(ℓ+1)+836；FPP の量子数上界を `FppOutcomeLe` で運ぶ再証明。台帳義務 4 の Lean 化）、Q の調査結果は ASSEMBLY_PLAN「分岐網羅の義務」節。**不変量 (3) の修正**：shift 直後の短い span に「lower 以下の周期なし」を要求すると反例あり ⇒ 終端比較時（半径 ≥ 2h）の「2h 未満の周期なし」（`NoBelow`）を FW で継承（ASSEMBLY_PLAN に記録）。外注中：S（`no_short_period_of_minimal`）、U（`backgroundS_exists`／`compare_progress_S`／`scan_tick_exists`）、V（`noBelow_next`：FW による周回間の継承）、W（`periodOn_span_of_next`：右半分の周期＋現在と次の回文 ⇒ span 全体の周期 2h）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、並列バッチ 2：chain shift の材料）：Opus/Sonnet 並列で新モジュール：`GalilLiveCentreMismatch.lean`（`not_live_of_mismatch`：不一致 ⇒ 中心は次の place で死ぬ）、`GalilSegmentCount.lean`（`watchSegE_steps_length`＝イベント数 tick、`watchSegE_clock_le`、`scanSeg_steps_ge`）、`GalilShortPeriod.lean`（`no_short_period_drop`／`_shift`：群補題 `hasPeriod_minimal_of_suffix` で shift 後も短周期なし、`hasPeriod_take_drop`／`drop_drop`）、`GalilCandidatePeriod.lean`（`candidate_hasPeriod`、`candidate_palAt`、`candidate_periodOn`：DP 候補 ⇒ [C−4h, C] の周期 2h）。自分で `GalilLiveCentreShift.lean`（`Span`、`leftmost_shift`：C 死亡＋C+h 生存＋span に 2h 未満の周期なし ⇒ C+h が最左、`live_shift_of_palAt`）。`ReadOrigin` には `reshift_palindrome`（round 終端で中心 o.center+2h・半径 o.radius+1 の回文）と `joined_input_period`（検証器が読んだ範囲の周期 2h）が既にある。実行中の外注：L（fallback 一周の `MInv` 合成 `cycle_fallback_minv`）、Q（tick の全域性の調査）、N（fallback 一周の tick 上界）、S（`no_short_period_of_minimal`：Fine–Wilf で「span の周期 2h＋DP 最小性＋lower 以下の周期なし ⇒ 2h 未満の周期なし」、`palAt_pair_of_period`、`no_candidate_of_result`）、T（`minv_watchSeg`／`minv_scanSeg`）。全モジュールはルート import 済み。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、`Live` の厳密化と周期区間の和集合）：`Live raw n c` に「左端 ≥ 1」（`n < 2*c`）を追加（原点の gap（index 0）に達した回文は機械では不一致扱い＝候補から外れるので、モデルと一致させた）。`leftmost_fallback` に `hrn : 2*r < n+1` を追加（B は `chosen_spec` から供給）、`live_of_scanInvariant` は `leftPresent` から左端 ≥ 1 を導出。Opus D: `GalilPeriodUnion.lean`（`PeriodOn x p a b`、`periodOn_union`（重なり ≥ p の周期区間の和集合）、`hasPeriod_slice_iff`、`encoded_periodOn_even`（符号化語の周期は偶数）、`periodOn_mirror`（回文中心での鏡映））。全モジュールをルート import、全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の機械側：区間・fallback・replay、並列化開始）：コウタの許可で Opus サブエージェント並列を開始。A: `GalilLiveCentreSeg.lean`（`leftmost_scanEvents`、`leftmost_watchSegE`／`watchSeg`／`scanSeg`、`scanSeg_heads`）、B: `GalilLiveCentreFallback.lean`（`leftmost_after_fallback`：`fallback_restarted` の輸出＋`span_covers`＋`position_represent` で fallback 後の新中心が最左の生存中心）、C: `GalilPeriodCentre.lean`（`hasPeriod_of_isPal_drop`、`isPal_drop_of_hasPeriod`、`isPal_span_of_palAt`、`palAt_of_isPal_span`、`span_hasPeriod_of_two_palAt`、`palAt_shift_of_period`、`no_centre_below_period`：chain shift の数学）。自分で `GalilSpanCounter.lean`（`SpanRep`：length = 2·radius+1 の各遷移での保存、`span_covers`）と `GalilLiveCentreReplay.lean`（`MInv raw c s`：replay 中は「replay カウンタ＝保存位置までの距離」＋保存位置で `Leftmost`、非 replay 中は右ヘッド位置で `Leftmost`；`minv_match`、`minv_matchR`（尽きた時点で右ヘッドが保存位置）、`minv_watchSegE`、`minv_after_fallback`）。全モジュールはルート import 済み、標準公理のみ。残り：不一致 ⇒ 中心死亡の補題、fallback 一周の `MInv` 合成、chain shift の機械側（周期 2h の供給と最小周期性）、restart、報告点。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、完全性の核＝最左の生存中心）：新モジュール `GalilLiveCentre.lean`（ルート import 済み）：`Live raw n c`（右 place n で中心 c が生きている＝`PalAt (encoded raw) c (n−c)`）、`Leftmost raw n C`（C が最左の生存中心）、`live_pred`、`live_of_scanInvariant`、`leftmost_match`（一致比較で保存）、`leftmost_fallback`（C が n+1 で死んだとき、窓が旧半径以下を全て覆えば fallback の最大半径 r による新中心 n+1−r が最左の生存中心）、`leftmost_report`（letter place 2k−1 で `IsPal (raw.take k) ↔ C = k`）。これが台帳義務 6（中心不変量）の数学側。残り：機械の fallback（`fallback_restarted` の最大性＋窓長 ≥ 2·旧半径+1 の供給、`length` カウンタと半径の関係）、chain shift（最小周期で中心 C+h へ）、restart／replay、報告点の接続。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予算プローブの実測結果）：`RealtimeGalil`（FIFO service = 2×predictability = 6338 遷移／文字、q=64 派生値）で 42 語（ランダム 30・60、偶数回文 40・80、奇数回文 41・81、二重回文 81・161、a^80、(ab)^40、(ab)^30 b (ba)^30、(aab)^40 aa、(aabab)^20 a (babaa)^20 長さ 201）の全接頭辞を判定：**見逃し 0、全接頭辞正答**（TOTAL_MISMATCHES=0）。`REALTIME_BUDGET = 2048` ではなく派生値 6338 での実測で、派生議論の範囲内。最初の重い版（長さ 240 まで＋drain 実行）は 28 分で打ち切り。プローブは一時ファイルで、テスト木から退避済み（`scala/pal` の `sbt test` 時間を増やさないため；scratchpad に `WorkBoundProbeSuite.scala` と `probe2_results.log`）。これは有限テストであり、任意長の証明ではない。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、予測可能性 ⇒ 実時間の抽象定理）：新モジュール `GalilPredictability.lean`（ルート import 済み、Mathlib のみ依存）：`backlog d c`（毎ラウンド 2c のサービス、ラウンド i に仕事 d i 到着の FIFO 残量）、`work d j i`（ラウンド j+1..i の到着仕事）、`exists_last_zero`（busy 区間の始点）、`backlog_telescope`、`backlog_zero_of_bounds`（全窓 j+1..i の仕事が 2c(i−j) 以下なら残量 0）、`work_bound_of_centres`（中心 C が単調・非遅延 m ≤ C m、仕事 d(m+1) ≤ c·(C(m+1)−C m+1) なら、C i = i の i について全窓の仕事 ≤ 2c(i−j)）、**`realtime_of_predictable`**（その仮定の下で正答ラウンドの残量 0＝`GALIL_CLOCK.md` §Predictability の台帳義務 7 を Lean 化）、`wrapper_exact`（追いついていれば源の答え、遅れていれば 0 を返すラッパーは、源が健全・完全で正答時 C i = i なら全ラウンドで正確）。残る契約は台帳義務 1〜6（仕事 d の費用上界、中心の単調・非遅延、正答時 C i = i）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、Galil の move 補題の組合せ論部分）：新モジュール `GalilMoveLemma.lean`（ルート import 済み）：`hasPeriod_of_isPal_take`（回文 x の長さ k の回文接頭辞 ⇒ x は周期 |x|−k を持つ）、`window_hasPeriod_of_chosen`（fallback 窓 T が回文なら T は周期 |T|−(2·chosenRadius T+1)＝中心前進量の 2 倍を持つ）、`isPal_take_of_hasPeriod`（逆向き：周期 p ⇒ 長さ |x|−p の接頭辞が回文）、`chosenRadius_ge_of_period`（窓の周期 p（|T|−p 奇数）⇒ chosenRadius ≥ (|T|−p−1)/2：fallback は周期の半分を超えて中心を進めない＝完全性側の材料）、`fallback_window_period`（窓 = 新記号 x :: 回文 P（|P| = 2k+1）のとき P は周期 |P|+1−2r = 2δ（δ = k+1−r は中心前進量）を持つ）、**`galil_move_of_contract`**（探索契約「P は k/2 以下の周期を持たない」の下で k ≤ 4δ：Galil の move 不等式を契約 1 個に還元）。Galil の move 不等式 k ≤ 4δ は、これに「半径の半分以下の周期は chain が既に捕捉している」という探索契約（完全性側、未着手）を足せば従う。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、実時間台帳の紙スケッチ）：`ASSEMBLY_PLAN.md` に「実時間台帳の紙スケッチ」節を追加（8 義務：stage 締切／DP 発見と追いつき／**Galil の move 不等式 k ≤ 4δ（Lean 未存在・仕様側も留保）**／fallback 費用／replay／**中心不変量（完全性の核、未着手）**／telescoping／SCA ラッパー）。Lean の較正は `delay_calibration`（K=63、M=2048）、Scala 派生は K=10、M=256、service 6338。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、経路比較・要判断）：無条件 PAL への 2 経路の現状。**旧経路（直接 SCA 構成、codex／GPT-5.6 が 09-07〜09-10 に推進）**：数学側の実時間予算（`Consumption x 8 b`、`PassPeriodSum`、`prefix_verifier_deadline`）は無条件で証明済み。最終定理 `pal_SAccepts_iff_embed`／`_embed9`（`FullMachineProg.lean`、HEAD には存在、作業ツリーでは `FullMachineProg.lean`／`StageLifecycleProg.lean` が未コミットのまま削除）は、具体機械側の仮定 `D : DecompOnTapes`、`hcost`／`hadvance`（走査費用）、`hpow`、`hinitS`（前処理初期状態）、`hround`／`hstepF`／`hstepG`／`hstepI`（具体 Prog がラウンド効果を実現）を残す＝有限制御の差し込みが大量に未完。**現行経路（Scala 忠実モデル、09-14〜）**：オンライン制御器の soundness は本日 `StepsAll (SoundScanNR)` で主ループ 2 周まで閉じたが、Scala 正本自身が「certified real-time recognizer ではない／仕事量台帳は未検証」と明記しており、固定 B の `StructuredMachine` に落とす実時間上界は紙の上でも未確立（予算 2048 の実測プローブ実行中）。判断事項：どちらの経路で無条件を狙うか（旧経路＝残りは差し込み作業だが量が多い／現行経路＝台帳の証明が先で、偽の可能性もある）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、主ループ 2 周の全状態で出力健全、および実時間に関する重要な発見）：新モジュール `GalilScaffoldTopOutputCycle.lean`（ルート import 済み）：`cycle_found_stepsAll`（`Restarted` → idle 区間 → found tick → chain の一生 → restart tick：`found_life`／`life_restarted` と同じ仮定の下で、全状態で `SoundScanNR`、終端は restart 後の状態）、`cycle_fallback_stepsAll`（`Restarted`＋`ShiftIdle` → idle 区間 → 不一致 → fallback 一周 → `Restarted raw t 0 reset`：全状態で `SoundScanNR`）。主ループの帰納は `stepsAll_trans` の反復なので、soundness 側は「各 checkpoint でどちらの周に入るか（分岐網羅）」を除いて閉じた。**重要**：Scala 正本 `docs/palindromes-in-peg/SCA_GALIL.md` は自身を「not a completed PAL PEG or a certified real-time recognizer」「A report made while behind is zero; proving the bound is what would exclude missed positives」「The proposed ledger here remains unverified」と明記し、`TRANSLATION_STRATEGY.md`（2026-09-06）は四段の機械翻訳を「実験であって現行の主経路ではない」としている。Lean の最終定理 `pal_in_peg_of_structured` は固定 B micro-step／文字の `StructuredMachine` を要求するため、この仕様の上では仕事量上界（Galil の nonchain 補題＋stage 締切の台帳）を証明せん限り無条件 PAL に到達できない。予算 2048 の実測プローブ（`scala/pal/src/test/scala/pal/WorkBoundProbeSuite.scala`、一時ファイル・コミット対象外）を実行中。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、init と restart tick の健全性）：新モジュール `GalilScaffoldTopOutputInit.lean`（ルート import 済み）：`outputRel_transfer`（右ヘッドと出力が同じなら移送）、`soundScanNR_vm`、`outputRel_position_one`（右ヘッド位置 1 なら任意の出力が健全：1 文字接頭辞は回文）、`init_stepsAll`（init tick は `SoundScanNR` の 1 tick 走行、終端 `Restarted (a :: rest) t 0 reset`）、`stepsAll_keep_tick`（制御と右ヘッドを保つ tick＝restart tick で健全走行を延長）。これで init／idle 区間／found→chain の一生／restart／不一致→fallback の各部品が `StepsAll (SoundScanNR raw)` で揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完。次: 主ループ 1 周（idle 区間＋found＋一生＋restart／idle 区間＋不一致＋fallback）の合成、主ループ帰納、フロンティア基準への変換、出力完全性。

追記（2026-09-16、fallback 一周の全状態で出力健全）：新モジュール `GalilScaffoldTopFallbackRestartAll.lean`（ルート import 済み）：`SoundScanNR raw st := mode = scan → replaying = false → OutputRel`（replay 中は右ヘッド基準の健全性が成り立たないので条件つき）、`soundScanNR_of_soundScan`、`fallback_restarted_All`（`fallback_restarted` の述語つき走行版＋`chosenRadius = 0 → refresh 節`）、`fallback_restarted_soundNR`（`onLetter = onLetterVM raw`、`leftFirst = leftFirstVM`、始点の `OutputRel` から、不一致比較→fallback→scan 再入の全状態で `SoundScanNR`、終端は `Restarted raw t 0 reset`；再入時 replaying=false なら r=0 で refresh 節と `Restarted` の走査不変量から `output_sound`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、fallback 一周を状態述語つき走行に）：新モジュール `GalilScaffoldTopFallbackAll.lean`（ルート import 済み、`FallbackS`／`FallbackCycleS` からの機械的移植）：`NoScan st := st.ctl.mode ≠ .scan`、`stepsAll_transfer_generic'`、`stepsAll_transfer_fallback_S`／`_fpp_S`／`_markEnd_S`／`_rewind_S`（各相の走行を `StepsAll NoScan` で `galilFrameS` へ転送）、`copy_home_start_All`／`fpp_then_markEnd_All`／`choose_then_rewind_All`／`fallback_chain_All`（copy → replayStart まで `StepsAll NoScan`）、`fallback_to_scan_All`（任意の Q について「非 scan で Q」「再入状態で Q」⇒ 一周の全状態で Q；`r = 0 → refresh 節` を新たに輸出）、`scan_fallback_cycle_All`（不一致比較から scan 再入まで、始点・終点の Q を仮定して全状態で Q；`chosenRadius = 0 → refresh 節` 輸出）。これで `SoundScan`（replay 中は無条件では成り立たないので replaying=false 条件つきに落とす必要あり：`SoundScanNR`）を fallback 一周に通せる材料が揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、chain の一生の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputLifeAll.lean`（ルート import 済み）：`scanSeg_mode`、`first_shift_stepsAll`（`round_next` の終端比較＋shift 相を切り出し：`hend`／`hpred`／`hlen` 不要、`hz : zero w.lag = true` を仮定、1+(h+1) tick の全状態で `SoundScan`）、`life_stepsAll`（found tick → 準備 `WatchSegE` → watch `WatchSeg` → 最初の shift → `Rounds` m 周 → 最終 `ScanSeg` → 破れ比較まで、`found_life` の内側の仮定＋`OutputRel cF sF`・found 時の `ScanInvariant`・最初の shift 終端の `Entry`・破れ比較後の `ScanInvariant` から、走行の**全状態**で scan モード時の出力が右ヘッド基準で健全）。全体 build 成功・標準公理のみ・無条件 PAL は未完。次: fallback 一周（copy/home/fpp/markEnd/rewind/replayStart は非 scan なので空、replay 区間は `SoundScan` が右ヘッド基準で成立するが意味付けはフロンティア基準へ要変換）と init、主ループでの接続、出力完全性。

追記（2026-09-16、再 shift 周回の全状態で出力健全）：新モジュール `GalilScaffoldTopOutputRound.lean`（ルート import 済み）：`SoundScan raw st := st.ctl.mode = .scan → OutputRel raw st.ctl st.vm`、`stepsAll_transfer_generic`（`steps_transfer_generic` の `StepsAll` 版：M モード内の状態は Q、E モードは tick を持たない）、`shift_stepsAll_S`／`shift_phase_stepsAll_S`（shift 相を `StepsAll` で `galilFrameS` へ転送、出口の Q は refresh の健全性）、`round_stepsAll`（`round_next` と同じ仮定＋区間頭の不変量・`OutputRel`・shift 終端の不変量 ⇒ 一周 k+1+(h+1) tick の全状態で `SoundScan`）、`rounds_stepsAll`（`Entry` から m 周の全状態で `SoundScan`、`rounds_origin` で次周の不変量）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、refresh 点と全状態の出力健全性）：新モジュール `GalilScaffoldTopOutputLife.lean`（`outputRel_of_refresh'`／`_S'`：任意の制御へ、`entry_scanInvariant`（`Entry` から走査不変量）、`outputRel_matched_refresh`（一致比較で半径 +1 と健全性）、`watchSegE_output_inv`／`watchSeg_output_inv`（終端の不変量つき）、`rounds_output`（再 shift m 周で `OutputRel` 保存：各周の走査は `Entry` の不変量、shift 終端の refresh は `rounds_origin` の次の origin の不変量））と `GalilScaffoldTopOutputTrace.lean`（`StepsAll F delay Q k x y`：全状態が Q を満たす走行、`stepsAll_steps`／`_head`／`_last`／`_trans`／`_mono`／`stepsAll_of_steps`、`SoundOut raw st := OutputRel raw st.ctl st.vm`、`matched_invariant`、`watchSegE_stepsAll`／`scanSeg_stepsAll`／`watchSeg_stepsAll`：区間の**全状態**で出力が右ヘッド基準で健全）。ルート import 済み。注意：`OutputRel` は右ヘッド位置基準なので、shift 中・replay 中（右ヘッドが入力フロンティアより後ろ）の出力の意味付けは別途フロンティア基準の関係が要る（実時間供給と一緒に扱う）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、出力の健全性）：新モジュール `GalilScaffoldTopOutputSound.lean`（ルート import 済み）：`OutputRel raw c s`（output=true ⇒ 右ヘッド位置 2k−1 の接頭辞 `raw.take k` は回文）、`outputRel_of_refresh`（`refresh_sound` の包装）、`scanInvariant_matched`、`watchSegE_output`／`scanSeg_output`／`watchSeg_output`（`ScanInvariant` を運びつつ区間に沿って `OutputRel` を保存：background は出力とヘッドを変えず、各一致比較で半径 +1 の不変量から `refresh` の健全性）、`report_sound`（右ヘッドが gap 上でなく `OutputRel`＋`ScanInvariant` なら output=true ⇒ 読んだ接頭辞は回文）。残り：区間外の refresh 点（shift 終端・replayStart・init）の `OutputRel` 供給、出力の完全性（回文なら true）、分岐網羅、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（2026-09-16、init と不一致前提の供給）：新モジュール `GalilScaffoldTopInitRestart.lean`（ルート import 済み）：`afterCompare_remaining`、`watchSegE_remaining`（区間は shift counter を保つ＝`ShiftIdle` 保存の材料）、`initialHead raw`（先頭 place 手前の gap 上・語は未着）、`initialHead_right_represents`／`_focus`／`_position`（`right` で先頭 place、位置 1、`Represents`）、`init_restarted`（`init` tick を `galilFrameS` に：L=R=C＝先頭 place、`Restarted (a :: rest) t 0 reset`、位置 1、remaining／replay 不変）、`segment_mismatch_ready`（`Restarted` からの chain idle 区間の終端で R 可用なら、`right s.right` は `Represents`・実記号、length 正準、remaining 保存、`ScanInvariant`（半径 Rad＋一致数）＝`fallback_next_found` の前提）。これで init → 走査 → 最初の不一致 → fallback → replay＋探索 → found → chain の一生 → restart → … の各接続部が `galilFrameS` 上で揃った（replay 中の found・後段 stage・missed・空語は未対応）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 分岐網羅（各 scan 状態で必ず次の tick が存在し、上記のいずれかの区間に入ること）と主ループの帰納、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（2026-09-16、不一致 → 次の found）：新モジュール `GalilScaffoldTopFallbackFound.lean`（ルート import 済み）：`fallback_next_found` — `fallback_restarted`＋`restarted_next_found` の合成（`delay = 2048`、`Decodes P`）。chain idle の不一致比較から fallback 一周を経た状態 t（`replay = ofNat r`）に対し、t から chain idle の `WatchSegE`（replay 中の tick を含む）で終端 idle・一致数 ≥ 1・clock 1 に達し、そこでの一致比較で探索が found なら `FoundReady` と（第 1 stage の found なら）直前 run・DP `Result`（lower 0）・Candidate、または区間内の非 found exit。これで主ループの二つの再入口（restart 後、fallback 後）から次の found 状態までが揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init tick → 最初の走査（初期 `ScanInvariant` 半径 0、search `begin reset radius`）→ 最初の不一致（L の左端）→ fallback の接続；replay 中の found・後段 stage・missed は未対応；`3·Rad ≤ 5·k`、found 時の半径正は仮定）。

追記（2026-09-16、fallback → restart 状態）：`Restarted` を緩和（`0 < Rad` を外し `positive last` を `0 ≤ value last` に）、`restarted_next_found` に `hpos : 0 < Rad + es1.count true`（found 時の半径正）を仮定として追加、`found_to_found` に対応する `hpos'` を追加。`replayStart_tick`／`fallback_to_scan_S`／`scan_fallback_cycle_S` の結論に `t.search = begin reset reset`、`t.lower = reset` を輸出。新モジュール `GalilScaffoldTopFallbackRestart.lean`（ルート import 済み）：`leftMoves_eq`、`stream_ne_nil`、`fallback_restarted` — chain idle の不一致比較から fallback 一周を経た状態 t について、右ヘッドの `represent` 分解 `⟨a :: xs, gap⟩` が存在し、`Restarted raw t 0 reset`（chain idle・中心 `Represents`・`ScanInvariant` 半径 0・radius reset・length 1・`search = begin reset reset`）、`t.replay = ofNat r`、`position t.center = position (right s.right) − r`、`PalAt (encoded raw) (…) r` と窓内最大性（下層 `fallback_replay`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `fallback_restarted`＋`restarted_next_found` で「不一致 → fallback → replay＋探索区間 → found」を合成；init tick からの初期不変量；replay 中の found は未対応；`3·Rad ≤ 5·k`、found 時の半径正は仮定）。

追記（同日、replay 中の tick と区間の一般化）：`TopSearch` に `replayDec b s`（`matchedPlace` の replay 減算）と射影補題、`matchedPlace_replayDec`、`scan_match_S'`／`scan_match_idle_S'`（replaying の有無を問わない一致比較 tick：`available` は `replaying ∨ canRight`、到達制御は `replaying := c.replaying && !replayExhausted (replayDec …)`、到達 VM は `replayDec c.replaying (afterCompare …)`）を追加。`WatchSegE` に replay 中の構成子 `countR`（replaying・clock>1・chain idle）と `matchIdleR`（replaying・clock 1・R 可用・chain idle・非 found・replay 減算）を追加し、`watchSegE_steps`／`append`／`trans`／`events`／`ne_idle`／`searchRun`／`advances`／`center`／`clock`（`replaying` 保存の結論は削除）／`search_not_found`／`heads`／`watchSeg_of_E` を更新。これで replayStart 後の replay 区間（探索は同時に進む）も chain idle 区間として扱える。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: fallback 後の状態から replay 区間の存在と `ScanInvariant raw c r` の再構成（下層 `fallback_replay`／`replay_scan`）、その後の探索区間→found への接続で「不一致 → fallback → replay → 探索 → found」の経路；init tick からの初期不変量；replay 中の found（chain start）は未対応）。

追記（同日、chain idle の不一致 → fallback 一周）：新モジュール `GalilScaffoldTopFallbackCycleS.lean`（ルート import 済み）：`scan_fallback_cycle_S` — `P := galilShared onLetter leftFirst shiftGuardVM beginShiftVM' beginFallbackVM' rs centre place entry` の `galilFrameS` 上で、scan（clock 1・replaying false）から不一致比較（`compareFound` の witness：探索 step `searchEffect false`、chain 効果 `chainAt false`（idle なら idle のまま、found なら chainStart）、`¬ shiftGuardVM`）で `beginFallback`（FPP 準備・chain idle・search idle）に入り、`fallback_to_scan_S` で scan に復帰：L=R=C は `left^[r] (right s.right)`（r = `chosenRadius` の窓）、`replay = ofNat r`、`radius = reset`、`length = ofNat 1`、chain idle、`replaying := decide (0 < r)`。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: replay 区間（`replaying = true` の比較列：`available` は常時、一致で `replay` 減算、尽きたら `replaying := false`）の定義と探索事象、その後の chain idle 区間への接続、init tick からの初期不変量、fallback 後の `ScanInvariant`（選ばれた中心の回文性＝`chosenRadius` の仕様）と replay の一致保証）。

追記（同日、fallback 経路の `galilFrameS` 化）：新モジュール `GalilScaffoldTopFallbackS.lean`（ルート import 済み）：`steps_transfer_fallback_S`／`fpp_S`／`markEnd_S`／`rewind_S`（pull frame の相 run を `tick_S_of_tick` 経由で `galilFrameS` へ）、`copy_home_start_S`／`fpp_then_markEnd_S`／`choose_then_rewind_S`／`fallback_chain_S`／`fallback_to_scan_S`（元定理の本文を機械的に置換：copy モードの `beginFallback` 状態から replayStart tick を経て scan モードへ、L=R=C は選ばれた中心、`replay = ofNat r`、`radius = reset`、`length = ofNat 1`、chain idle、`replaying := decide (0 < r)`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain idle の不一致比較 tick `scan_fallback_S`（`compareFound` の第 2／3 枝＋`beginFallbackVM`）と `fallback_to_scan_S` の合成、replay 区間（`replaying = true` の比較列）の定義と探索事象、init tick からの最初の走査不変量）。

追記（同日、replay の減算＝忠実性修正）：`galilFrame.matchedPlace` は scan frame 経由で `s' = s`（replay counter を減らさない）だったので、Scala `matchedPlace` の `if (replaying) replay.dec()` を反映して `matchedPlace b s t := t = (if b then {s with replay := dec s.replay} else s)` に修正（`replaying := c.replaying && !replayExhausted s''` と整合）。`scan_match_S`／`scan_match_idle_S`／`found_start_match`／`compare_progress`／`scan_match_merge` は `replaying = false` の下で更新。全体 build 成功・標準公理のみ・無条件 PAL は未完。**未解決の下層前提（メモ）**：(i) `3·Rad ≤ 5·k`（restart 時の走査半径と `last` の関係、第 1 stage の debt 障壁）は下層 `first_stage_safe` 以来の仮定；(ii) found 時の半径 `0 < r0`（`stage_found_supplied`）は replay 後の半径 0 の found を排除できていない（restart 後は Rad ≥ 1 で満たす）。

追記（同日、主ループの一周）：新モジュール `GalilScaffoldTopFoundLoop.lean`（ルート import 済み）：`found_to_found` — `life_restarted` と `restarted_next_found` の合成。found 状態 `⟨cF, sF⟩`（`found_life` の静的前提）から、chain の一生・restart・chain idle の探索区間・次の found 比較まで `galilFrameS` の `Steps` が通り、次の found 状態 s1' で `FoundReady` が再成立、かつ（第 1 stage の found なら）直前 run・DP `Result`（k = value last）・Candidate、または第 1 stage が区間内で非 found exit。`Decodes P`、`delay = 2048`、`3·Rad ≤ 5·k` を仮定。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: init／replay から最初の found 状態へ（`Restarted` の `positive last` を `0 ≤ value last` に緩めて lower = 0 を許す）、後段 stage（wait/double）、missed／fallback 枝、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain の一生 → restart 直後）：新モジュール `GalilScaffoldTopLifeRestart.lean`（ルート import 済み）：`watchSeg_counters`（chain 条件なしの counter 正準性保存）、`life_restarted` — `found_life` と同じ前提（found 状態の静的前提＝`FoundReady` の中身、found tick、準備期間、watch 期間、終端不一致＋shift、m ラウンド、区間＋破れ比較）に `entry` と `hres : ∀ s t, restartVM entry s t → P.restart s t` を加え、破れ状態からの restart tick（`Tick.restart`）で、found 状態から restart 直後の状態 `{e3 with chain := .idle, lower := last, search := begin last e3.radius, dp := reset entry e3.dp}` までの `galilFrameS` の `Steps` と `∃ Rad, Restarted raw r Rad last`（中心は `rounds_centerRep`＋`scanSeg_center`、`ScanInvariant` は `rounds_restart` の結論を位置 `org.center+(m+1)h` に合わせ、length の正準性は prep／watch／shift／rounds／区間の各保存補題で輸送）。これで `life_restarted` → `restarted_next_found` により「found 状態 → 次の found 状態（`FoundReady`）」が閉じた（第 1 stage で found する場合；`3·Rad ≤ 5·k` は仮定）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 一周の合成定理 `found_to_found`、init／replay から最初の `FoundReady`／`Restarted` へ、missed／wait／double・fallback 枝、出力の完全性、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、restart 後 → 次の found 状態）：新モジュール `GalilScaffoldTopReadyFound.lean`（ルート import 済み）：`Decodes P`（`P.centre`／`P.place` は中心ヘッドの `represent ⟨a :: ls,gap⟩ …` から記号と place を読む；`P.place` は中心のみに依存）、`FoundReady P raw s`（`found_life` の静的前提：中心の分解、`ScanInvariant`、radius 値・正準、length 正準、R > 0、復号）、`Restarted raw r Rad last`（restart 直後の事実：chain idle、中心 `Represents`・実記号、`ScanInvariant` 半径 Rad、`RadiusRep`、length 正準、Rad > 0、`search = begin last radius`、`lower = last`、last 正準・正）、`restarted_next_found`：`Restarted` な r から clock 2048 で chain idle の `WatchSegE es1` を経て、終端 idle の状態 s1 での一致比較（clock 1）で探索が found に至れば、`FoundReady P raw s1` が成り立ち、かつ（第 1 stage 終端なら）直前 run・`Result`（窓 `8·max k 1 + 1`、k = value last）・Candidate、または第 1 stage が区間内で非 found exit。`3·Rad ≤ 5·k` は仮定。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `FoundReady sF` ＋ `found_life` の動的前提 ＋ restart tick ⇒ `Restarted` の定理（`life_restarted`）、両者の合成で found→found の一周）。

追記（同日、中心・ヘッド・counter の輸送）：`chain_life`／`found_life` の結論に `Entry raw org (toOnly e v)`（ラウンド開始時の入口不変量）を追加。新モジュール（すべてルート import 済み）：`GalilScaffoldTopCentre.lean`（`represents_decompose`：`Represents` かつ focus ≠ none なら `represent ⟨a :: ls, gap⟩ (rs.map some) q` の形、`place_read_some`、`scanSeg_center`、`rounds_centerRep`：m ラウンド後の中心ヘッドは `Represents`・実記号・位置 `org.center + m*h + h`）、`GalilScaffoldTopSegmentHeads.lean`（`watchSegE_heads`：chain 条件なしで `ScanEvents`・periodOnly・radius＝一致数・counter 正準性保存、`scanSeg_counters`）、`GalilScaffoldTopRoundsCounters.lean`（`rounds_counters`：ラウンドは radius／length の正準性を保つ、`shift_run_canonical`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 「found 状態の不変量」`FoundReady`（中心の `represent` 分解、`ScanInvariant`、radius 値・正準、length 正準、`P.centre`／`P.place` の復号）を定義し、`found_life` → restart tick → idle 区間 → `idle_segment_found_first` で次の found 状態でも `FoundReady` が成り立つ「一周」定理；`3*rad ≤ 5*k`（restart 半径と `last` の関係）は下層でも未証明の前提として明示）。

追記（同日、found tick の特定）：新モジュール `GalilScaffoldTopIdleFound.lean`（ルート import 済み）：`map_fst_map_pair`、`advances_replicate_false`、`idle_segment_found_first` — `Search.start(lower)` 直後（clock 2048、chain idle、`P.place r = ⟨a :: ls,gap⟩`、`r.search = begin lower radius`、lower 正準 k、radius 正準 rad、`3*rad ≤ 5*k`）から chain idle の `WatchSegE es1`（終端も idle）と、その次の tick の探索 step（比較なら `aF = true` かつ clock 1、background なら `aF = false`）が found に至るとき、(左) その tick が第 1 stage の終端：`vq.dp = ⟨dpv, true⟩` に DP `Result`、直前の探索は run、Candidate と半周期の存在（＝`found_life` の入口）、または (右) 第 1 stage が区間内の L ≤ |es1| で run 以外・found 以外の mode（missed／wait／double）で既に終わっていた（後段 stage の found；下層 `later_stage_chain` の領分）。証明は inactive 探索の padding（`searchRun_pad`）で `search_first_stage` を適用し、`stage_prefix_mode`／`searchRun_unique`／`watchSegE_search_not_found` で三分岐。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick の出口（`restart_tick`：`begin last radius`、clock delay、chain idle）とこの定理、`found_start_match`／`backgroundS_idle` と `found_life` の接続；wait/double 後段 stage；missed のときの走査継続と fallback）。

追記（同日、chain idle の比較 tick と区間の事実）：`WatchSegE.match` は scan 側の `ChainTick` 前提（非 idle）なので chain idle 区間に比較 tick を含められなかった。`scan_match_idle_S`（chain idle・探索が found に至らない一致比較：`compareFound` の第 2 枝で chain は idle のまま）を `TopSearch` に追加し、`WatchSegE` に構成子 `matchIdle` を追加、`watchSegE_steps`（`galilFrameS` の `Steps`）を新設、`watchSeg_of_E` は非 idle 前提つきに。`watchSegE_append`／`trans`／`events`／`ne_idle`／`searchRun`／`advances` を更新。新モジュール `GalilScaffoldTopSegmentFacts.lean`（ルート import 済み）：`watchSegE_center`（中心保存）、`watchSegE_clock`（事象列＝`advances delay c.clock`、終端 clock＝`MatchClock.run`、mode・replaying 保存）、`searchRun_pad`（inactive な探索は任意事象で不変）、`watchSegE_search_not_found`（終端 idle の区間では途中のどの時点でも探索は found でない：found なら chain が始まり idle に戻らない）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart 出口＋idle 区間＋found tick から、padding で `search_first_stage` を適用し `stage_prefix_mode`／`watchSegE_search_not_found` で found tick＝第 1 stage の終端を特定、`found_life` の入口（`Result`・Candidate）を供給；第 1 stage が wait/double で終わる枝は `later_stage_chain`）。

追記（同日、第 1 stage の構造化と接頭辞）：`search_first_stage` を構造化（`es = as ++ bs ++ usedQ ++ rest`、各相の `SearchRun`、`v0` grow・work = |as|、`PacedPrepared (ofNat k) … v1.toPrep bs v2.toPrep`、`v1` grow・work 非正・lower = ofNat k、`v2` run、`SafeQuanta v2.search v2.dp usedQ v3.search v3.dp`、`v3` 非 run、DP `Result`、found → Candidate）。新モジュール `GalilScaffoldTopStagePrefix.lean`（`searchStep_unique`／`searchRun_unique`（決定性）、`searchRun_grow_prefix`、`pacedRun_split`、`pacedRun_cons_prepMode`、`safeQuanta_prefix_run`）と `GalilScaffoldTopFirstStagePrefix.lean`（`zip_replicate_append`、`pacedPrepared_split`、`safeQuanta_nil`、`searchRun_prefix_eq`、`stage_prefix_mode`：第 1 stage の事象列 `as ++ bs ++ usedQ` の任意の真の接頭辞の後で探索は found でなく、最後の 1 事象の直前では run）。両方ルート import 済み。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick の出口から chain idle の `WatchSegE` を取り、`search_first_stage`＋`stage_prefix_mode` で「最初に found になる tick」＝`usedQ` の終端を特定し、その tick が比較なら `found_start_match`、background なら `backgroundS_idle` で chain が始まることを `found_life` の入口に接続；missed／wait／double・fallback 枝）。

追記（同日、restart 後の第 1 stage の実走行）：新モジュール `GalilScaffoldTopFirstStage.lean`（ルート import 済み）：`searchRun_split`、`toPrep_search_eq`、`search_first_stage` — `Search.start(lower)` 直後（scheduler `begin lower radius`、lower 正準で値 k、radius 正準で値 rad、`3*rad ≤ 5*k`）から、chain idle 区間の実走行 `SearchRun ⟨a :: ls,gap⟩ es v0 v'` で、事象列 es が可用性列 av の `advances 2048 2048` であり、長さが `max k 1 + (2k+2|w|+7) + runBudget(8·max k 1)` 以上なら、`es = used ++ rest` に分割でき、`used` の終端 v3 で探索は run 以外の mode、`v3.dp = ⟨dpv, true⟩` に DP `Result w k 0`（w は中心から `8·max k 1 + 1` 個の窓）、found なら Candidate と半周期の存在。証明は `first_stage_chain_run` の存在結果を `searchRun_growing`／`pacedGrowing_unique`／`searchRun_prepared`／`searchRun_quanta` で実走行に同一視。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick（`restart_tick`）の出口状態から `search_first_stage` の前提（`begin last radius`、chain idle、clock = delay = 2048）を供給し、found のときは `used` の終端 tick で chain が始まる（比較 tick なら `found_start_match`、background なら `backgroundS_idle`）ことと `found_life` を接続；missed／wait／double の枝、fallback 枝）。

追記（同日、探索段階の同一視）：新モジュール `GalilScaffoldTopSearchStage.lean`（ルート import 済み）：`toPrep_ofPrep` 等の往復補題、`searchRun_growing`（grow・work = n の状態からの n tick の `SearchRun` は `PacedGrowing`、終端は grow・work 0、quarter／lower 保存）、`pacedGrowing_unique`、`PrepMode`／`tick_prepMode`／`searchStep_prep`、`searchRun_paced`（全 enabled の下層 `PacedRun` を実走行が状態ごとに辿る：`tick_unique`）、`searchRun_prepared`（grow・work 零からの dispatch＋本体＝下層 `PacedPrepared` の終端 p に到達）、`safeQuanta_single`、`searchRun_quanta`（下層 `SafeQuanta … used …` を実走行が辿り、残り `rest` はその後：`safe_calls_unique`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: これらと `first_stage_chain_run`／`begin_entry`／`watchSegE_advances`／`advances_take` を合成した「restart 後の第 1 stage」上層定理：区間の事象列を `as ++ bs ++ used ++ rest` に分割し、`used` の終端で探索が exit mode・DP `Result`・found なら Candidate）。

追記（同日、background での chain start）：Scala の `background` は探索 quantum の後に found なら **任意の scan tick で** `chain.start()` する（比較 tick に限らない）ので、`backgroundS` を「ヘッド不変・探索 step（advance なし）・chain 効果は `chainAt false found …`（active なら無効 tick、idle かつ found なら `chainStart`、idle かつ非 found なら idle）・他フィールド不変」に書き直し、`backgroundS_fields`／`backgroundS_chainTick`（active chain なら `ChainTick false`）／`backgroundS_idle`（idle chain の 2 分岐）を用意。`watchSeg_events`／`watchSegE_events` は `s.chain ≠ .idle` 前提つき（`ChainTicks` の結論のため）に変更し、`prep_watch_start`／`first_round`／`found_life` の呼び出しに前提を供給。`chainTick_ne_idle'`。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `SearchRun` と下層段階 run の同一視モジュール、background 起点の chain start（`sm = false`）版 `prep_watch_start`）。

追記（同日、chain idle 区間の探索の駆動）：新モジュール `GalilScaffoldTopSearchRun.lean`（ルート import 済み）：`SearchRun center es v v'`（`searchStep` の列）、`searchRun_append`、`chainTick_ne_idle`（chain tick は idle に戻らない）、`watchSegE_ne_idle`／`watchSegE_idle_start`（区間の終端で chain idle なら開始も idle＝区間内で chain start なし）、`watchSegE_searchRun`（終端 idle の `WatchSegE es` は、`P.place` が中心のみに依存する前提で、探索を `SearchRun (P.place s) es` として駆動する）、`watchSegE_advances`（区間の事象列 es は可用性列 av に対する `advances delay c.clock (av.map (·, true))` に等しい：下層の段階補題が消費する事象形）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `SearchRun` を下層の `PacedGrowing`／`PacedPrepared`／`SafeQuanta` と同一視（`growStep` は関数、`tick_unique`／`run_unique`、`safe_quanta_unique`）して `first_stage_chain_run` の結論を実走行に移し、restart tick → found tick を一本化）。

追記（同日、探索共走過程の上層統合）：`GalilVM`／`SearchVM` に探索の walker place（`walker`）を追加。`GalilScaffoldTopSearch.lean` に `SearchVM.toPrep`／`ofPrep`（`PrepareControl.State` との往復、`runState`）、`searchStep center a v v'`（Scala `background` の探索 1 step＋`advanceMatch` の debt 減算 `a`：idle/found/missed は不変、grow は `growStep` か `prepare` の dispatch、lower/lowerHome/copy/home は `PrepareControl.Tick true`、run は `SafeQuanta … [a]`（64 呼び出し＋advance）、wait は `advance a (waitStep true …)`、double は `advance a (Double.step …)` か `prepare`）、`searchEffect P a s vq`（chain idle なら `searchStep (P.place s) a`、chain active なら不変）、`backgroundS`（scan 側 background＋advance なしの探索 step）を定義し、`compareFound` の quantum 節と `galilFrameS.background` を置換（`searchQuantum`／`searchIdle` は不使用に）。`backgroundS_fields`（background tick の各フィールド）、`searchEffect_run`／`searchEffect_active`。下流（`MatchedSeq`／`ScanSeg`／`WatchSeg`／`WatchSegE`／`round_next`／`terminal_shift_steps`／`rounds_break`／`chain_life`／`found_life`／`found_start_match`）の `hq` 仮定と background 型を差し替え。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain idle 区間の探索の段階（`PacedGrowing`→`PacedPrepared`→`SafeQuanta`→wait/double）を `searchStep` の列から復元して `first_stage_chain_run`／`restart_first_stage` に接続し、restart → found tick（`found_life` の入口）を一本化）。

追記（同日、init／replay／fallback の忠実性修正）：Scala の `stepInit`（`search.start(zero)`）、`stepReplayStart`（chain idle、`radius.reset()` 後に `search.start(zero)`）、`beginFallback`（`search.mode = Idle`、`chain.mode = Idle`）に合わせ、`initVM entry`／`replayStartVM entry`（`t.chain = .idle`、`t.search = begin reset s.radius`／`begin reset reset`、`t.lower = reset`、`t.dp = Control.reset entry s.dp` を追加）と `beginFallbackVM`（`chain := .idle`、`search := {s.search with mode := .idle}`）を強化。`galilShared … centre place entry` に DP entry を追加し、`init_tick`／`replayStart_tick`／`fallback_to_scan`／`scan_fallback_cycle` の自由な `ch : ChainVM` を除去（終状態の chain は `.idle`）。全体 build 成功・標準公理のみ・無条件 PAL は未完。**残りの主要作業（設計メモ）**：(1) 探索共走過程の上層統合：現在の `searchQuantum`（run モードの 64 呼び出し＋`advance a`）／`searchIdle`（run 以外は不変）は Scala の `background` の「run 以外でも 1 step」（grow／lower／lowerHome／copy／home／wait／double）を含まない。下層には `GalilScaffoldPrepareControl.Tick`（paced 準備）、`StagePrepare.PacedGrowing`／`Double.Run`／`WaitInterrupt.Run`、`first_stage_chain_run`／`later_stage_chain`／`restart_first_stage`／`begin_entry`／`replay_stage_entry` が揃っており、`SearchVM`（scheduler `SearchFinish.State`＋`dp`＋`lower`）の 1 tick を mode 別にこれらへ対応づける `searchTick a` を定義して `compareFound` の quantum 節を置換する必要がある。(2) restart tick → `SearchSeg`（chain idle の走査区間、探索 tick 付き）→ found tick（`found_life` の入口）／missed／不一致→fallback。(3) init と replay 後の `ScanInv` の確立、fallback 経路（`fallback_chain`＋`replayStart_tick`）と `ScanInv`。(4) 出力の完全性（中心の正しさ＝Galil の大域不変条件）。(5) 実時間入力供給（`right.gap`／`inputReady`、1 入力あたりの tick 数の有界性）。(6) `galilFrameS` の `StructuredMachine` 化と `SAccepts ↔ PAL`。

追記（同日、found tick からの一本化）：新モジュール `GalilScaffoldTopFoundLife.lean`（ルート import 済み）：`found_life` — found 状態 `⟨cF, sF⟩`（scan・replaying false・clock 1・R が読める・chain idle・中心 `represent ⟨a :: ls,gap⟩ (rs.map some) q`・`ScanInvariant` 半径 R（value radius = R、R > 0）・counter 正準・探索 quantum が found で終わり DP `Result`・`P.centre sF` が中心記号、`P.place sF` が中心 place・外側一致・`ChainMatched (chainStart …) ch`・`refresh`）から、`∃ h ys b, Candidate ∧ ys.length+1 = h ∧ ∀ bs cs（長さ h, h+1）, 準備期間 `WatchSegE (bs ++ dm :: cs)` → watch 期間 `WatchSeg` → 終端不一致＋shift → `Rounds m` → 区間 n ＋破れ比較 ⇒ `galilFrameS` の `Steps` が found 状態から broken 状態まで通り、`restartVM` の前提条件（`org.center = position sF.center`、中心 `+(m+1)*h`）が成立`。初期条件（`ScanInv` の found tick 通過、準備期間の `ScanEvents`、radius＝lag の一致 `prep_value`、`canonical_nat` による `sF.radius = ofNat (r0+1)`）は内部で供給。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: restart tick（`restart_tick`）から次の探索へ、探索 idle 期間の走査（chain idle・found でない区間）、found 前の `ScanInv` の確立（init／replay から）、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、単一フレームへの統合）：`galilFrameS` の `compare` を `compareVM` から `compareFound`（chain start を含む比較：chain が active なら `ChainTick`、idle かつ探索が found で終われば `chain.start()`＋一致 credit、idle で found でなければ idle のまま）に置き換え、`galilFrameF` を廃止して `found_start_match` も `galilFrameS` の tick に。中心記号・中心 place の読み出し `centre`/`place` は `Shared` のフィールド（`P.centre`/`P.place`）に移し、`galilShared … rs centre place` と各補題（`replayStart_tick`／`fallback_to_scan`／`restart_tick`／`scan_fallback_cycle`／`init_tick`／`compare_progress_concrete`）に引数追加。`scan_match_S`・`WatchSeg`/`WatchSegE` の `match`・`ScanSeg`（`chainTick_source_ne_idle` で導出）・`round_next`/`terminal_shift_steps`/`rounds_break` は「chain が idle でない」前提を付けて `compareFound` の第 1 枝を使う。これで found tick から chain の一生（`chain_life`）まで同じフレーム上の `Steps` で繋がる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick → 準備期間（`prep_watch_start`）→ `chain_life` の一本化と初期条件供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain start と準備期間、忠実性修正）：(1) 忠実性修正：Scala の `background` は探索 quantum の後に `chain.start()` を呼び、chain は answer tape の現在値を読む。`GalilScaffoldTopFound.lean` の `compareFound`／`found_start_match` は quantum 前の `s.dp` の tape 11 を snapshot していたので、quantum 後の `vq.dp.config.tapes 11` に修正（`found_to_watchStart` の `y.config.tapes 11` と整合）。(2) `found_shift_entry`／`first_round`／`chain_life` の `∃ h ys b, Candidate ∧ ys.length+1 = h ∧ split ∧ …` を `∀ h ys b, Candidate → ys.length+1 = h → …` に変更（`fresh_watch_entry` の存在量化を経由せず、chain start 側が出す h・ys・b をそのまま渡せる）。(3) 新モジュール `GalilScaffoldTopWatchSegE.lean`（ルート import 済み）：`WatchSegE es`（事象列を添字にした一般走査区間）、`watchSeg_of_E`、`watchSegE_append`（任意位置で分割）、`watchSegE_trans`、`watchSegE_events`、`prep_watch_start`：found 探索（`SafeQuanta` … found）と一致した start tick（`ChainMatched (chainStart (y.config.tapes 11) c p ver (ofNat (r0+1))) ch`）のあと、事象列 `bs ++ dm :: cs`（長さ h・1・h+1）の `WatchSegE` の終端で chain は `.watch (watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents true dm bs cs)))`（`found_to_watchStart`＋`chainMatched_unique`／`chainTicks_unique`）。これは `first_round` の開始条件 `v0.chain = .watch s0` を供給する。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: found tick → 準備期間 → `chain_life` を `WatchSegE` の分割で一本化、`ScanInvariant`／radius の初期条件の供給、restart 以降、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain 一生分の合成）：新モジュール `GalilScaffoldTopChainLife.lean`（ルート import 済み）：`chain_life` — found 側前提（`found_rounds_restart` と同じ）のもと、`WatchSeg` の watch 期間＋終端不一致＋最初の shift（`first_round`）、`Rounds m`（`rounds_lift`）、最後の走査区間 n ＋破れる終端比較（`rounds_break`）を合成し、(i) `galilFrameS` の `Steps` で found 直後の状態から broken 状態 `afterCompare s3 vs3 vq3` へ到達、(ii) `∃ org : ReadOrigin raw` で `org.interior.length+1 = h`、`org.center = position cen`、`org.shifts = 0`、中心 `org.center+(m+1)*h`・半径 `org.radius+1+m*h-h+n+1` の `ScanInvariant`、broken、margin 非負、`last` 正、lag 零、`RadiusRep`、`begin … .work`、`Canonical last`（＝`restartVM` の前提）。注意: 文中の `let` が「unknown free variable」を起こしたので、`raw`／`final`／`s0` は展開して書く。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: chain start（found tick）の上層供給と `WatchSeg` の開始状態の接続、restart tick 以降の探索、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、最初の一周）：新モジュール `GalilScaffoldTopWatchSeg.lean`（`WatchSeg`：chain の状態を問わない一般の走査区間、`watchSeg_steps`＝`galilFrameS` の `Steps`、`watchSeg_events`＝tick ごとの `Bool` 列で `ChainTicks`／`ScanEvents`、中心・periodOnly 保存、radius は一致数だけ増加、counter の正準性保存）と `GalilScaffoldTopFirstRound.lean`（`terminal_shift_steps`：終端不一致比較＋shift を `Steps (1+(h+1))` に；`first_round`：`found_rounds_restart` と同じ found 側前提のもと、`WatchSeg` の watch 期間（開始 chain＝`watchStart cen c ys b final`）＋終端不一致（phase 4・lag 零・予測一致）＋shift ⇒ `galilFrameS` の `Steps`、終状態は watching・lag 零・periodOnly、かつ `Entry raw o' (toOnly e v)`（`o'.interior.length+1 = h`、`o'.shifts = 0`））。両方ルート import 済み。これで `first_round` → `rounds_lift`（m 周）→ `rounds_break`（破れ）が一本につながる材料が揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 三者を合成した chain 一生分の定理、found tick（chain start）の上層供給、restart 後の探索、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、found からの `Entry`）：`GalilScaffoldTopFreshEntry.lean` に `found_shift_entry` を追加：`found_rounds_restart` と同じ前提（found 探索、中心 `represent`、半径正準・正、prep の一致列、watch 期間の `Run`、phase 4、lag 零、`ScanInvariant`、予測一致、counter 正準、終端不一致）に実機の `ChainShiftRun ⟨cen, left l, ofNat h, radiusCounter, lengthCounter⟩ (immediate t') reset h …` を与えると、shift 後状態に `Entry raw o`（`o.interior.length+1 = h`、`o.center = position cen`、`o.radius = scanRadius`、`o.shifts = 0`、中心が読める）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、最初の shift の `Entry`）：新モジュール `GalilScaffoldTopFreshEntry.lean`（ルート import 済み）：`fresh_shift_entry` — `scan_prediction_shift` と同じ前提（fresh start `ready c xs b`、Represents、位置、`ScanInvariant`、phase 4、lag 零、予測一致、counter の正準性、prep credits、終端不一致）に、実機が行った `ChainShiftRun`（同じ開始状態）を加えると、`chain_shift_unique` で解析側の shift と同一視され、`entry_of_only` により shift 後の状態 `⟨endpoint.center, endpoint.left, right outer, watchEnd, cycleEnd, endpoint.radius⟩` に `Entry raw o` が成立（`o.interior.length+1 = xs.length+1`、`o.center = position s.machine.verifier`、`o.radius = radius`、`o.shifts = 0`、中心が読める）。これで `rounds_lift`（m ラウンド）→ `rounds_break`（破れ枝）の入口が下層から供給できる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 上層状態から `fresh_shift_entry` の前提を供給する「最初の一周」補題（found→prep→watch 期間→終端不一致→shift）、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、破れ枝＝`rounds_restart` の上層化）：新モジュール `GalilScaffoldTopRoundBreak.lean`（ルート import 済み）：`chainTick_true_broken`（lag 零で一致 tick が破れたら記録される watch は `immediate w` かつ `BreakStep`）、`afterCompare_only'`（watching/broken を問わず一致比較の射影は `onlyCompareNext`）、`afterCompare_chain`、`rounds_break`：`Rounds m` ＋ 走査区間 n ＋ 終端の一致比較で chain が破れる（`vs.chain = .broken w'`）とき、(i) `galilFrameS` の `Steps` で `afterCompare s1 vs vq`（output は `refresh`）に到達、(ii) `Entry raw org (toOnly s w0)` かつ中心が読める限り、下層 `rounds_restart` の結論（累積中心・半径での `ScanInvariant`、broken、margin 非負、`last` 正、lag 零、`RadiusRep`、`begin … .work`、`Canonical last`）が実状態で成立。これは `restartVM` の前提そのもの。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立（found→watch→最初の shift と `entry_of_only`）、restart 後の探索と found tick 供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、m ラウンドの連結）：`shift_phase_S`／`round_next` の shift 出口の output を存在量化から `refresh (galilFrameS …) 終状態 c1.output o` を仮定した明示の `o` に変更（`shift_steps_S` に転送部分を分離）。これで次ラウンドの開始制御が具体的に決まる。新モジュール `GalilScaffoldTopRounds.lean`（ルート import 済み）：`chain_shift_lag`（chain shift は lag を保つ）、`compareRounds_append`、`Rounds P q first delay h m c s c' s'`（`round_next` のデータを m 回、各回は直前の shift 出口の制御から開始）、`rounds_lift`：periodOnly・lag 零の watching 開始から、`Steps (galilFrameS)` の存在と `CompareRounds h (toOnly s w0) m (toOnly s' w')`（終状態も watching・lag 零・periodOnly）。`rounds_origin` と組めば `Entry` が m ラウンド保存される。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `Entry` の初期成立（found→watch 開始との接続）、終端一致で chain が破れる枝＝`rounds_restart`、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、一周＝`CompareRounds` の 1 段）：`beginShiftVM` の radius 二重加算（比較の `afterMismatch` で既に +1）を除去し、`shift_round` の前提を `⟨s1.center, s1.left, ofNat h, s1.radius, inc (inc s1.length)⟩`（`CompareRounds.next` の `inc t.radius` と同形）に。新モジュール `GalilScaffoldTopRoundS.lean`（ルート import 済み）：`shiftRun_of_chain`、`shift_phase_S`（shift 期間を `galilFrameS` 上の `Steps` に：`steps_transfer_generic` を Inv＝`CopyIdle ∧ s = shiftLens.set s2 v0` で使い、frame 再パラメータ化と `tick_S_of_tick`）、`afterMismatch_*` 射影補題、`round_next`：periodOnly・lag 零の watching 状態から、走査区間（`ScanSeg`）＋終端の不一致比較（`cycleEnd`・予測一致・guard・`beginShiftVM`）＋`ChainShiftRun` h 単位で、(i) `galilFrameS` 上の `Steps (k+1+(h+1))` で scan モードに戻り、(ii) 射影が `CompareRounds h (toOnly s w0) 1 (toOnly 終状態 v)`（`.next … (.stop _)`）になる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: m ラウンドの連結と `rounds_origin` による `Entry` 保存、終端が一致で chain が破れる枝（`rounds_restart`）、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、消費のタイミングの修正）：Scala では `prediction()` は chain 消費の前に評価され、`chain.matched()`（lag 零なら即時消費）は一致時は `matchedPlace`、shift 時は `beginChainShift` の中で起きる。これに合わせ `scanFrame.compare` の chain 効果を `ChainTick (decide (read (left L) = read (right R)))`（一致なら消費込み、不一致なら背景のみ）にし、`beginShiftVM` は `chain := .watch (immediate w)`（入口で消費）、`shiftGuardVM` の periodOnly 側は `singlePositive cycle`（不一致時は cycle 未減算）に戻した。`compare_lift`/`break_lift`/`grun_lift`/`compare_parts`/`compare_progress`（`hw : ∀ a, ∃ ch', ChainTick a …`）を更新。`shift_round`/`scan_shift_cycle` の `ChainShiftRun … (immediate w) reset h …` は `CompareRounds.next` の `hchain` と同形。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 走査区間＋終端 shift 比較＋`shift_round` を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` を保存）。

追記（同日、比較結果の分岐と二重計上の修正）：Scala との照合で 2 点修正。(1) `canShift` の `cycleEnd` は `matched()` の `cycle.dec` の前の値で判定され、一致時の `length += 2`（`matchedPlace`）が未反映だった → 比較の到達状態を一致ビットで分け、`afterCompare`（radius+1・periodOnly なら cycle−1・length+2、`GalilScaffoldTopSearch` に移動）と `afterMismatch`（radius+1 のみ）とし、`compareVM`/`compareFound` は `if a then afterCompare else afterMismatch`；`shiftGuardVM` の periodOnly 側は減算後の `zero cycle`（canonical なら減算前の `singlePositive` と同値）。`scanInv_compare_matched` の length canonical は `inc_canonical` ×2。(2) `beginChainShift` の `chain.matched()` は比較の `ChainTick true` で既に計上済みなのに `beginShiftVM` が再び `immediate` を掛けていた → chain はそのまま（periodOnly:=true・cycle リセットのみ）。`scan_shift_cycle`/`shift_round` の前提は `ChainShiftRun … w reset h …`（`CompareRounds.next` の `hchain` と同形：そこでの `immediate t.watch` が本コントローラの比較後の w）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一致比較列と走査区間）：新モジュール `GalilScaffoldTopMatchedSeq.lean`（ルート import 済み）：`MatchedSeq n s t`（background のカウント tick と、chain が watching のまま・継続セルが末尾でない一致比較 n 回）、`compare_parts`/`matched_parts`、`background_only`（lag 零の背景 tick は射影不変）、`matchedSeq_only`（periodOnly・lag 零で `OnlyMatchedRun (toOnly s w) n (toOnly t w')` に射影）。新モジュール `GalilScaffoldTopScanSeg.lean`（ルート import 済み）：`ScanSeg`（コントローラの走査区間：wait/count/一致比較、clock 付き）、`scanSeg_steps`（`galilFrameS` の `Steps` へ）、`scanSeg_matchedSeq`、`scanSeg_only`（コントローラ実行 ⇒ 下層の `OnlyMatchedRun`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 区間末尾の `cycleEnd` 比較＋`shift_round` を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` 不変量を保存、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、only-compare 射影）：新モジュール `GalilScaffoldTopOnly.lean`（ルート import 済み）。`toOnly s w`（統合 VM の `OnlyCompareState` 射影）、`chainTick_true_immediate`/`chainTick_false_idle`（lag 零では有効 tick＝`immediate`、無効 tick＝不変）、`afterCompare_only`（periodOnly・lag 零での一致比較の到達状態の射影＝`onlyCompareNext`）を証明。`GalilScaffoldTopMatchedSeq.lean`（`MatchedSeq`：カウント tick と一致比較 n 回の列、`matchedSeq_only`：`OnlyMatchedRun` への射影）はドラフト中（未 import）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、periodOnly と cycle の反映）：Scala `canShift`（Watch∧lag 零∧phase 4∧（periodOnly なら `cycleEnd`＝`singlePositive cycle`、さもなくば margin ≥ 0））と `matched()` の `if (periodOnly) cycle.dec()`、`beginShift()` の `periodOnly = true; cycle.reset()` を反映：`GalilVM` に `periodOnly : Bool` を追加、`cycleAfter s` を定義して `compareVM`/`compareFound`/`afterCompare` の到達状態に `cycle := cycleAfter s` を追加、`shiftGuardVM` を Scala 通りに書き直し（`freshShiftGuard` は periodOnly=false の場合）、`beginShiftVM` で `periodOnly := true`。下層には `RestartState`（chainMode/periodOnly/restarts/clock を持つ Codex 期のコントローラ射影）と `dispatchOnlyMatch`・`restart`・`CompareRounds`（`OnlyMatchedRun` ＋ 末尾 `cycleEnd` ＋ `ShiftRun`/`ChainShiftRun` の m ラウンド）があり、`onlyCompareNext`（ヘッド移動・`immediate`・cycle−1・radius+1）は本コントローラの一致比較（periodOnly・lag 零）と一致する。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 統合 VM の走査＋shift 一周を `CompareRounds.next` に対応づけ、`rounds_origin` で `Entry` 不変量を一周保存、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、一致比較での不変条件保存）：Scala `advanceMatch()` は `radius.inc()` も行う（`debt.dec()` と両方）と確認したので `radiusAfter s := inc s.radius` に修正（前段の設計メモは撤回：`ScanInv.radius` はそのまま正しい）。新モジュール `GalilScaffoldTopInvStep.lean`（ルート import 済み）：`afterCompare s vs vq`（`compareVM`/`compareFound` が作る到達状態）とその射影補題、`scanInv_compare_matched`（R 可用・外側記号一致・ヘッド移動の一致比較で `ScanInv` は半径 r+1 で保存：`scan_events_invariant`＋`inc_value`）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 不一致比較（shift 入口・fallback 入口）と shift 一周・fallback 一周での `ScanInv` の変化（中心と半径の更新）、found tick の供給、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、比較 tick の radius 更新）：`GalilScaffoldTopSearch` に `ChainVM.isIdle`・`searchActive`（Scala `!mode.inactive`：idle/found/missed 以外）・`radiusAfter s`（search 活性かつ chain idle なら radius そのまま＝`advanceMatch`、さもなくば `inc`）を追加し、`compareVM`/`compareFound` の到達状態を `{… with radius := radiusAfter s}` に変更（`scan_match_S`/`found_start_match` も更新）。全体 build 成功・標準公理のみ・無条件 PAL は未完。**設計メモ**：`ScanInv.radius`（value radius = 走査半径）は search 活性中の一致では成り立たない（Scala は `advanceMatch` で search 側の debt に積む）。正しい不変条件は「value radius ＋（search 活性∧chain idle のとき search 開始以降の一致数）＝ 走査半径」の形で、search の `debt`/`span` との対応（`SearchFinish.begin`/`advance`）を読んで決める必要がある。次はここから。

追記（同日、shift 一周の接続）：新モジュール `GalilScaffoldTopShiftRound.lean`（ルート import 済み）。`shift_round`：`found_supplied_restart` が結論する形の `ChainShiftRun ⟨s1.center, s1.left, ofNat h, inc s1.radius, inc (inc s1.length)⟩ (immediate w) reset h endpoint watchEnd cycleEnd` を前提に、`beginShiftVM h w` の入口から `chain_shift_exhausts` と `scan_shift_cycle` で scan → shift → scan の一周（1+(h+1) tick）を `galilFrame` 上で得る。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 比較 tick の radius カウンタ更新（Scala：search 活性かつ chain idle なら `advanceMatch`、さもなくば `radius.inc()`）を `compareVM`/`compareFound` に加え、`ScanInv` の一周保存を証明、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、scan モード不変条件と shift の消尽）：新モジュール `GalilScaffoldTopInvariant.lean`（ルート import 済み）。`ScanInv raw s r`（下層の供給補題が比較 tick で仮定するもの：`ScanInvariant` を中心位置で、radius カウンタ＝走査半径かつ canonical、length canonical、中心ヘッドは入力の `represent` 形）を定義。`shift_run_remaining`/`chain_shift_exhausts`（remaining=h からの h 単位 shift で remaining が尽きる：`scan_shift_cycle` の `hz`）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `found_supplied_restart` の結論 `ChainShiftRun` を `scan_shift_cycle` に渡す `shift_round`、`ScanInv` の一周保存、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、入口の具体化）：新モジュール `GalilScaffoldTopGuards.lean`（ルート import 済み）。`shiftGuardVM`（watching な chain で `freshShiftGuard` かつ周期の予測記号＝R の読み）、`periodLength`（周期テープから半周期長 h）、`beginShiftVM'`/`beginFallbackVM'`（存在量化した入口効果）を定義し、`beginShift_exists`/`beginFallback_exists` から `compare_progress_concrete`（この具体入口を `galilShared` に与えた `galilFrame` で、scan モードの比較 tick は必ず存在）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間から shift guard）：新モジュール `GalilScaffoldTopWatchGuard.lean`（ルート import 済み）。`watch_tick_unique`/`watch_run_unique`（`Watch.Run` の決定性）、`ready_distance`、`watch_period_guard`：found tick の `ScanInvariant`、prep 期間の `ScanEvents (sm :: bs ++ dm :: cs)`、`watchStart` から watching のまま終わる watch 期間の `GRun`（chain 未破れ）から、イベント列 ws を取り出し、lag が尽き（`watchLag ws initialRadius = 0`）距離が 4h 以上なら、コントローラ自身の watch 状態で `freshShiftGuard = true`・距離＝走査半径・`ScanInvariant` が成り立つ（`watch_grun_supply` → `watch_shift_supply` → `shift_ready`、下層の証人は決定性でコントローラの状態に同定）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: shift guard の残り条件（予測記号＝右読み）と `scan_shift_cycle` の入口前提への接続、fallback guard、found tick 自身の `ScanEvents` 供給、一周の連結、大域不変条件、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、watch 期間の供給）：新モジュール `GalilScaffoldTopWatchSupply.lean`（ルート import 済み）。`watch_grun_supply`：`watchStart cen c ys b final`（lag=`ofNat initialRadius`）から始まり watching のまま終わる `GRun` から、イベント列 ws・`Watch.Run`・`VerifyRun.Run ⟨cen, ready c ys b⟩ (watchConsumes ws initialRadius) t'.machine`・`t'.lag = ofNat (watchLag ws initialRadius)`・ヘッドの `ScanEvents` を取り出す（`watch_shift_supply` の `hrun`/`hexhausted`/`hwatch` の形）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、watch 期間の chain tick と検証器実行）：新モジュール `GalilScaffoldTopWatchRun.lean`（ルート import 済み）。`broken_stays`（破れた chain は破れたまま、credit も受けない）、`chainTicks_watch_run`（watching のまま終わる chain tick 列は `Watch.Run`）、`verify_run_append`、`positive_ofNat_iff`/`zero_ofNat_iff`、`watch_run_verify`（lag が単進 `ofNat lag` の `Watch.Run` は検証器を `watchConsumes bs lag` 回消費し lag は `watchLag bs lag`：`Internal.take`/`Outer.immediate`/`Outer.queued` の算術が下層 `watchTick` と一致）を証明。これは `verify_watch_run_events` の逆向きで、コントローラ側の `GRun` から `watch_shift_supply` の `hrun`（`VerifyRun.Run ⟨cen, ready c ys b⟩ (watchConsumes ws r) z`）を作るための橋。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `GRun`（watch 期間）→ `grun_events` → `chainTicks_watch_run` → `watch_run_verify` を `watch_shift_supply` に繋いで shift guard の成立を得る、fallback guard の具体化、大域不変条件、実時間供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、prep 期間の連結）：新モジュール `GalilScaffoldTopPrep.lean`（ルート import 済み）。`prep_to_watch`：found な探索の後、chain が（同 tick の一致 sm で credit された）`chainStart` から始まる走査の一般実行 `GRun` のイベント列が `bs ++ dm :: cs`（copy h・終端・back h+1）なら、`grun_events`・`chainTicks_unique`・`found_to_watchStart` により終了時の chain は `watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents sm dm bs cs))` に一致（ヘッドは同じイベント列の `ScanEvents` に従う）。これでコントローラの走査 tick 列から下層の watch 入口（`found_supplied_restart`/`watch_shift_supply` の前提の形）が得られる。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: watch 期間の `GRun` から `watchConsumes`/`watchLag` 型の前提を出して `watch_shift_supply` に接続、shift guard・fallback guard の具体化（`freshShiftGuard`・`FallbackGuard`）、大域不変条件（中心の正しさ）、実時間入力供給、`StructuredMachine` 化、`SAccepts ↔ PAL`）。

追記（同日、chain tick の決定性）：新モジュール `GalilScaffoldTopChainUnique.lean`（ルート import 済み）。`internal_unique`/`outer_unique`（watch の内部・外部 step は状態で決まる）、`break_not_good`/`break_outer_absurd`（破れは即時消費の失敗そのもので、`Outer true` と両立しない）、`chainStep_unique`（copy は答えセル、back は FIRST、watch は lag/Good で決まる）、`chainMatched_unique`、`chainTick_unique`、`chainTicks_unique`（同じイベント列・同じ開始状態の chain tick 列は一致）を証明。これで `found_to_watchStart` の到達状態は prep 期間の chain 状態そのもの（`grun_events` の `ChainTicks` と同定できる）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、一般走査実行のイベント抽出）：新モジュール `GalilScaffoldTopGeneralEvents.lean`（ルート import 済み）。`grun_events`（`GRun` から tick 単位のイベント列を取り出し、ヘッドは `ScanEvents`、chain は同じ列の `ChainTicks` に従う：`joint_run_events` の `ChainVM` 版）。これが下層の供給補題（`ScanEvents` と `prepEvents` 型の credit 実行を前提に取るもの）への接続口。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、任意の chain での走査実行）：新モジュール `GalilScaffoldTopGeneralRun.lean`（ルート import 済み）。`GScan`（L/R・`ChainVM`・clock）と `GTick`（`JointTick` の `ChainVM` 一般化：R 不可用なら idle、clock>1 なら count、clock=1 で一致比較、chain は `ChainTick false/true`）、`GRun` を定義し、`grun_lift`（有効/無効イベント列上の `GRun` は scan frame の `Steps`、clock は 1..delay、replaying=false、odd/pair 不変）を証明。これで prep 中（copy/back）や idle/broken の chain を伴う走査 tick 列も scan frame に載る（イベントは tick 単位：`ScanEvents`/`prepEvents` と同じ粒度、copy step は 1 tick に 1 回）。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、found → chain.start の比較）：新モジュール `GalilScaffoldTopFound.lean`（ルート import 済み）。`chainAt a found …`（比較時の chain 効果：通常は `ChainTick a`、chain が idle で search quantum が found に達したら `chainStart` してから一致なら credit）、`compareFound`（scan 射影の移動＋search quantum＋`chainAt`）、`galilFrameF`（`galilFrame` の compare を `compareFound` に）を定義し、`found_start_match`（idle な chain・found に達する quantum・一致比較 ⇒ `galilFrameF` の `scan_match` で chain が `chainStart` の credited 状態に）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、Broken 後の restart tick）：新モジュール `GalilScaffoldTopRestart.lean`（ルート import 済み）。`restartVM entry`（chain が `.broken w` で margin 非負・last 正・lag 零のとき、chain idle・lower:=last・search:=`begin last radius`・DP プログラム `reset entry`）を `Shared.restart` に与え、`restart_tick`（scan モードで `Tick.restart`、clock リセット）を証明。`joint_break_restart` の結論がこの前提そのもの。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、統合 VM の chain 載せ替え）：`GalilVM`/`ScanVM`/`ShiftVM` の `watch : Watch.State` を `chain : ChainVM` に置き換えた。`ChainVM`・`ChainStep`・`ChainMatched`・`ChainTick`・`BreakStep` の定義を早い段階の新モジュール `GalilScaffoldTopChainVM.lean`（ルート import 済み）へ移し、`chainTick_of_watch_false`/`chainTick_of_watch_true`（watching な chain の tick ＝ `Watch.Tick`）と `chainTick_of_break`（破れ＝`Internal.idle` の後 `ChainMatched.breaks` で `.broken`）を証明。`scanFrame` の background/compare は `ChainTick false/true`、`shiftFrame.shiftOne` は watching な chain の `chainShiftOne`、`count_lift`/`compare_lift`/`break_lift`/`joint_run_lift`/`shift_phase_vm`/`scan_shift_cycle`/`compare_progress`/`replayStart_tick`/`init_tick`/`fallback_to_scan` を `s.chain = .watch w` 前提で言い直し。`Top.Tick` に `restart` 構成子（scan モードで `F.restart s s'`、clock リセット）と `Frame.restart`/`Shared.restart` を追加し、レンズ引き戻し・転送・`galilShared` の全モジュールを更新。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `restartVM`（Broken → `search.start(last)`・chain idle・DP リセット）の tick、found → `chainStart` を background に組み込む、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、chain 入口＝`watchStart`）：新モジュール `GalilScaffoldTopChainEntry.lean`（ルート import 済み）。`run_lag_ofNat`（credit 実行の lag は単進カウンタで単調増加）と `found_to_watchStart`：found な DP 探索（`found_start_back`）から、`chain.start()` と同 tick の credit sm、copy 歩行（一致列 bs）、終端 tick（credit dm）、back 歩行（一致列 cs）を `ChainTicks (bs ++ dm :: cs)` で辿ると、到達する watch 状態が下層の `watchStart ver c ys b (run (start (ofNat (r0+1))) (prepEvents sm dm bs cs))` に一致（半周期長 `ys.length+1 = h` は `Candidate` の `4h+1 ≤ |w|` から）。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: `ChainVM` を `GalilVM` に載せ替え `background`/compare を `ChainTick` で定義、`ChainMatched.breaks` からの restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、prep 中の走査クレジット）：`ChainStep.watchStep` を `Internal`（背景消費）に、`ChainMatched.watch` を `Outer true`（`chain.matched()`：margin+1、lag 零なら即時消費、さもなくば lag+1）に分離（`Watch.Tick w true` ＝ 両者の合成）。新モジュール `GalilScaffoldTopChainCredits.lean`（ルート import 済み）で `ChainTick a`（背景 step の後に一致なら credit）と `ChainTicks`、`creditsOf`、`step_copy`/`step_idle` を定義し、`copy_ticks`（copy 歩行＋一致列 bs ⇒ credit 状態は `run (creditsOf margin lag) (bs.map (true,·))`）と `back_ticks`（back 歩行＋一致列 cs、lag は正の単進カウンタなので最後の credit は `Outer.queued` ⇒ `run … (cs.map (false,·))`）を証明。これで `prepEvents` の各成分が `ChainVM` 上の tick 列に対応した。全体 build 成功・標準公理のみ・無条件 PAL は未完（次: 開始 tick と終端 tick を含む `found_to_watchStart`（`GalilScaffoldTopChainEntry.lean` でドラフト中、未 import）、`ChainVM` の `GalilVM` への載せ替え、restart、大域不変条件、実時間供給、一本化、`SAccepts ↔ PAL`）。

追記（同日、found → watch）：新モジュール `GalilScaffoldTopChainStart.lean`（ルート import 済み）。`found_to_watch`：DP 探索が found で終わると（`found_start_back`）、`chainStart` から h 回の copy step・copy 終端・h+1 回の back step、計 h+(h+2) 個の `ChainStep` で `watch` モードに入り、その制御は `GalilScaffoldChainConsume.ready c ys b`（`ys ++ [b]` が半周期＝中心の次から h 個の場所）、lag=radius、margin=radius−4h（走査クレジットの割り込みなし版）。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `ChainVM` を `GalilVM` の `watch` フィールドの代わりに載せて `background`/compare を `ChainStep`/`ChainMatched` で定義し直す（scan frame の `Watch.Tick` 前提を `ChainVM` 経由に一般化）、prep 中の走査クレジット割り込み版、restart（Broken → `search.start(last)`）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、chain のモード VM）：新モジュール `GalilScaffoldTopChain.lean`（ルート import 済み）。Scala `ScaffoldChain` の Idle/Copy/Back/Watch/Broken を `ChainVM` として転写し、`chainStart`（found 時の `chain.start()`：period を FRONT+中心記号に、walker/verifier を中心に、lag=margin=radius）、`watchControl`（Back 終了時の制御＝`ready` の形）、`ChainStep`（`stepCopy`：答えテープの 1 セルごとに h+1・margin−4・walker 左・period に複写、LEFT で tail mark を書いて Back；`stepBack`：FRONT まで戻って 1 つ右へ進み Watch；Watch の無効 tick）、`ChainMatched`（`chain.matched()`：Copy/Back では lag+1・margin+1、Watch では有効 tick か破れ）、`ChainSteps` を定義。`copy_steps`/`back_steps` で下層の `GalilScaffoldChainPeriod.Copy`/`Back` 歩行と一致することを証明。全体 build 成功・標準公理のみ・無条件 PAL は未完。

追記（同日、search 共走過程の frame）：新モジュール `GalilScaffoldTopSearch.lean`（ルート import 済み）。`searchQuantum a`（一致イベント a に対する 1 quantum＝`SafeQuanta … [a]`：64 回の安全な DP 呼び出しと `advance a`）、`searchIdle`、`compareVM`（scan 射影上の比較＋一致ビット a＋search 射影上の quantum か idle、他は不変）、`galilFrameS`（`galilFrame` の compare を `compareVM` に置換）を定義し、`tick_S_of_tick`（比較を含まない全 tick は `galilFrameS` でも tick）と `scan_match_S`（scan 側一致比較＋search quantum ⇒ `galilFrameS` の `scan_match`）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: init/replayStart の search 再始動の VM 効果、found → chain 開始（`found_supplied_restart`）と破れ後 restart の `galilFrameS` 上の接続、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、search 成分の VM 取り込み）：`GalilVM` に `search`（`SearchFinish.State`）・`dp`（DP 機械 12 テープ）・`lower` を追加し `searchLens` を定義（既存レンズ・証明は `{s with …}` のため無変更、`init_tick`/`replayStart_tick` のリテラルのみ修正）。全体 build 成功・標準公理のみ。init/replayStart の search 再始動（`search.start(zero)`＝`begin reset radius`＋DP プログラムのリセット）はまだ VM 効果に含めていない（次に追加）。無条件 PAL は未完。

追記（同日、出力健全性の統合 VM 版）：新モジュール `GalilScaffoldTopOutput.lean`（ルート import 済み）。`leftFirstVM`（L の位置が 1）と `onLetterVM raw`（R が k 文字目＝符号化位置 2k−1）を定義し、`output_sound`/`refresh_sound`（`ScanInvariant` のもとで refresh された出力が true なら先頭 k 文字は回文：`scan_output` を統合 VM の refresh に接続）を証明。出力の完全性（接頭辞回文なら出力 true）は「現在の中心が正しい」という Galil の大域不変条件そのもので、局所補題では閉じない。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: search 成分の統合 VM への取り込みと破れ後 restart、大域不変条件（中心の正しさ・`ReadOrigin`・restart 条件の一周保存）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、比較 tick の進行性）：`GalilScaffoldTopScan` の `scanFrame.compare` を「chain watch の `Tick true` か `BreakStep`（`JointBreak` の chain 側：lag 零・検証器可・周期記号と入力の不一致で消費し margin+1）」の選言に広げ、`break_lift`（`JointBreak` も出力 refresh つきの `scan_match`）を追加。新モジュール `GalilScaffoldTopBranches.lean`（ルート import 済み）で `compare_progress`（scan モード・clock 1・replaying=false・R 可用で、chain が tick か破れ、shift/fallback の入口効果が存在すれば、一致（`scan_match`）・shift（`scan_shift`）・fallback（`scan_fallback`）のいずれかの tick が必ず存在し、遷移先は scan/shift/copy）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: chain 破れ後の restart（`joint_break_restart` の条件から search 再開）と search 成分の統合 VM への取り込み、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保ち、出力＝接頭辞回文）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、chain watch tick の存在）：新モジュール `GalilScaffoldTopWatch.lean`（ルート import 済み）。`watch_tick_exists`（`Internal`（lag 正なら消費）と `Outer`（lag 零なら再消費、さもなくば queue）の両消費に必要な `Good` 条件のもとで `Watch.Tick s true t` が存在）と `watch_tick_false`（無効 tick は lag 正の消費が `Good` なら存在）を証明。`Good` が成り立たない場合が chain の破れ（`JointBreak` は lag 零・即時消費側の破れ）。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 比較 tick での三枝の網羅（一致＝`JointTick.compare`、不一致＋guard＝shift、不一致＋¬guard＝fallback、chain 破れ＝restart）、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保つ）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、JointRun の持ち上げ）：新モジュール `GalilScaffoldTopJointRun.lean`（ルート import 済み）。`joint_run_lift`（有効イベント n 個の `JointRun` を、clock が 1..delay・replaying=false・各カウント tick で R が `canRight` の前提のもと、scan frame（`ScanVM`）の n tick の `Steps` に持ち上げ：clock>1 ではカウント、clock=1 で一致比較＋出力 refresh；終了時の clock は joint 側と一致、odd/pair 不変）を証明。`steps_pull scanLens` と `steps_transfer_scan` で `galilFrame` に載る。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 三枝分岐の網羅（`JointBreak`・`FallbackGuard` から shift/fallback 入口前提を供給し、一致／shift／fallback のどれかが必ず起きることを示す）、大域不変条件（`ScanInvariant`・`ReadOrigin`・restart 条件を一周ごとに保つ）と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、init と scan 実行の転送）：新モジュール `GalilScaffoldTopScanRun.lean`（ルート import 済み）。`init_tick`（init モードから 1 tick で scan モード・output=true、R 右・L/C を R に複写・length+1）、`scan_tick_stays`（scan frame の tick は scan モードと `replaying=false` を保つ：shift/fallback 入口は空）、`steps_transfer_scan`（scan frame の `Steps` 全体を `galilFrame` へ、frame の再パラメータ化つき）を証明。これで init を含む全モードの tick／実行が `galilFrame` 上に載った。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `JointRun`（有効イベント列）を scan frame の `Steps` に持ち上げる `joint_run_lift`（clock 1..delay の不変条件）、三枝分岐の網羅（`JointTick`/`JointBreak`/`FallbackGuard` から入口前提を供給）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan→fallback→scan の一周）：新モジュール `GalilScaffoldTopFallbackCycle.lean`（ルート import 済み）。`beginFallbackVM p`（`beginFallback` の VM 効果：FPP 状態を `FppControl.beginFallback program p length` に）を定義し、`scan_fallback_cycle`（scan モード・clock 1・replaying=false から、比較→不一致→shift guard 不成立→`beginFallback` の入口 tick に `fallback_to_scan` を連結：計 1+(n+1) tick で scan モード復帰、L=R=C は入口時の R から r 個下の中心、replay=r・radius=0・length=1・`replaying ↔ 0<r`、`ShiftIdle` 保存）を `galilFrame (galilShared …)` 上で証明。これで Scala コントローラの scan からの三枝（一致・shift・fallback）すべてが統合 VM 上で scan に戻る形になった。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: init 枝、`Steps` 版 scan 転送（count/wait の列）、三枝を選ぶ分岐の網羅（`JointTick`/`JointBreak`/`FallbackGuard` から入口前提を供給）、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan→shift→scan の一周）：新モジュール `GalilScaffoldTopShiftCycle.lean`（ルート import 済み）。`beginShiftVM h`（`beginChainShift` の VM 効果：remaining:=h・radius+1・length+2・watch:=`immediate`・cycle リセット）を定義し、`scan_shift_cycle`（scan モード・clock 1・replaying=false から、比較→不一致→shift guard→`beginShift` の入口 tick、`ChainShiftRun` n 単位、remaining 尽きて scan へ復帰、計 1+(n+1) tick、出力 refresh、`CopyIdle` 前提）を `galilFrame` 上で証明。`ChainShiftRun` と guard・入口の成立は `ReadOrigin`（`CompareRounds`）側から供給する前提。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: fallback 入口の具体化（`beginFallbackVM`：`FppControl.beginFallback` と `right_place`）と scan→fallback→scan の一周、init 枝、`Steps` 版 scan 転送、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、scan 枝の併合）：`Shared` に `shiftGuard`/`beginShift`/`beginFallback` を移し（`galilFrame` はこれらを `P` から取る）、`galilShared` はそれらをパラメータで受ける形に変更。新モジュール `GalilScaffoldTopScanMerge.lean`（ルート import 済み）で `scan_match_merge`（引き戻し scan frame の一致比較 tick を `galilFrame` の `scan_match` に、出力 refresh はレンズ等式で `t` に戻す）と `scan_transfer`（replaying=false のもとで scan frame の wait/count/match tick は `galilFrame` の tick；shift/fallback 入口は scan frame では空）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Steps` 版 scan 転送、shift/fallback 入口の VM 効果の具体化（`beginShift`：remaining:=h・radius+1・length+2・watch:=immediate・cycle リセット、`beginFallback`：`FppControl.beginFallback` と `right_place`）、init 枝、scan→shift→scan / scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、replayStart と fallback の scan 復帰）：新モジュール `GalilScaffoldTopReplay.lean`（ルート import 済み）。`Shared` の具体値 `galilShared`（`initVM`：R 右・L/C を R に複写・length+1、`replayStartVM`：replay:=radius・R/L/C:=C・radius リセット・length:=1、`replayPosVM`/`replayExhaustedVM`；chain/search の再始動は watch 成分に委ねる）と `positive_ofNat` を定義し、`replayStart_tick`（replayStart モードから 1 tick で scan モード・clock リセット・`replaying = positive radius`、出力は非 replay のときだけ refresh）と、`fallback_chain` に連結した `fallback_to_scan`（copy モードの `beginFallback` 状態から scan モード復帰まで一本：L=R=C が旧 R の r 個下の中心、replay=r、radius=0、length=1、`replaying ↔ 0<r`、`ShiftIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の統合 VM への転送と shift/fallback 入口（`FallbackGuard` から `beginFallback` 状態を作る VM 効果）、init 枝、scan→shift→scan / scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fallback 一周の連結）：新モジュール `GalilScaffoldTopCopyChain.lean`（ルート import 済み）。`copy_home_start`（`FppControl.fallback_prepared` を `fpp_control_run_lift`→`steps_pull`→`steps_transfer_fallback` で `galilFrame` に載せ、copy モードの `beginFallback` 状態から 2|w|+3 tick で fpp モード・準備済みプログラム実行中へ）と、それに `fpp_then_markEnd`・`choose_then_rewind` を連結した `fallback_chain`（copy モードから replayStart モードまで一本：`r = chosenRadius w` として L は R から 2r・C は r 戻り、length=2r+1・radius=r・FPP リセット・`ShiftIdle` 保存。前提は window 非空・|w| 偶数・FIRST ∉ {7,8}）を証明。これで Scala の fallback 経路（Copy→Home→Fpp→MarkEnd→Choose→Rewind→ReplayStart）が統合 VM 上で端から端まで繋がった。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: replayStart/init 枝の実体化、scan の転送と shift/fallback 入口（`FallbackGuard`→`beginFallback` の VM 効果）、scan→shift→scan と scan→fallback→scan の一周、大域不変条件と実時間入力供給、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、choose→rewind→replayStart の連結）：`GalilScaffoldTopVM` に `choose_phase_vm`/`rewind_phase_vm` を追加。新モジュール `GalilScaffoldTopRewindChain.lean`（ルート import 済み）で `iterate_inc_ofNat`、`oddAt_false`、`marks_val`（cell 1..|w| は 7 か 8）と、`choose_then_rewind`（choose モード・`odd=false`・MARKS が `marks w` の cell 1 を FIRST にしたもの・ヘッド |w|・|w| 偶数・FIRST ∉ {7,8} のとき、`r = chosenRadius w` として (|w|−(2r+1)+1)+(2r+1) tick で replayStart モードへ到達、L は R から 2r 戻り・C は r 戻り・length=2r+1・radius=r・FPP リセット、`ShiftIdle` 保存）を `galilFrame` 上で証明。選択セルが `chosenRadius`（最長の奇数長回文接頭辞）に一致することは `marks_cell`・`chosen_spec`・`chosen_greatest` で示した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: copy/home の連結（`fallback_prepared`）、replayStart/init 枝、scan の転送と shift/fallback 入口、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fpp→markEnd の連結）：新モジュール `GalilScaffoldTopFallbackChain.lean`（ルート import 済み）。`run_done_absorb`（halt 後の実行は不動）と `fpp_outcome_program`（fpp phase で halt したプログラムは `fpp_scheduled` の `⟨v,true⟩` に一致：実行の分割と決定性）、`markNew_tape`/`marks_after_fpp`（halt 後の MARKS は `marks w` の cell 1 を FIRST に置き換えたもの、ヘッドは 2）、`marks_no_end`/`marks_end`（cell 1..|w| は END でなく cell |w|+1 が END）を証明し、`fpp_phase_vm`（`Run` を返すよう拡張）・`steps_transfer_fpp`・`markEnd_phase_vm`・`steps_transfer_markEnd` を `galilFrame` 上で連結した `fpp_then_markEnd`（fpp モードの準備済みプログラムから n+1+|w| tick で choose モード・`odd=false`・MARKS ヘッドは cell |w|、fpp の他フィールド不変、`ShiftIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: choose→rewind→replayStart の連結（`marks_cell` で選択セルを `chosenRadius` に同定）、copy/home の連結（`fallback_prepared`）、scan の転送と shift/fallback 入口、init/replayStart 枝、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、markEnd の Steps 転送）：新モジュール `GalilScaffoldTopSteps3.lean`（ルート import 済み）。出口集合 E 内の tick も転送でき E が閉じている形の `steps_transfer_generic'` を証明し、`marks_choose_transfer`（marksFrame の choose モード tick は `choose_step` のみで、MARKS の markBack/markSet は fpp レンズ読みと rewind レンズ読みで一致）と `step_markEnd`・`step_marks_choose` により `steps_transfer_markEnd`（`ShiftIdle` 保存）を導出。これで shift/copy-home/fpp/markEnd/choose-rewind の 5 系統の `Steps` が `galilFrame` 上に転送できる。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan の転送（`compare_lift`/`count_lift` の `galilFrame` 版）、init/replayStart 枝、scan の shift/fallback 入口、`galilFrame` 上で init→scan→…→scan の一周を連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、汎用 Steps 転送）：新モジュール `GalilScaffoldTopSteps2.lean`（ルート import 済み）。`steps_transfer_generic`（レンズ・部品 frame・モード集合 M・出口集合 E・不変条件 Inv を取り、「M 内の tick は M か E へ」「E からは tick 不能」「M 内の tick は転送可」から `Steps` 全体を転送）を証明し、`empty_rel` タクティクで空関係の構成子を落とす `no_tick_fallback`（fpp から）・`no_tick_fpp`（markEnd から）・`no_tick_rewind`（replayStart から）と、`ModeStep` 由来の `step_fallback`/`step_fpp`/`step_rewind` を用意して、`steps_transfer_fallback`・`steps_transfer_fpp`・`steps_transfer_rewind`（いずれも `ShiftIdle` 保存）を導出。`GalilScaffoldTopMerge` の fallback/fpp/markEnd/rewind の transfer は出力パラメータ f g について一般化。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: markEnd の `Steps` 転送（出口 choose で `choose_step` が残るため定常コントローラ形で扱う）、scan の転送、init/replayStart 枝、scan の shift/fallback 入口、一周の連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、Steps 転送と不変条件）：新モジュール `GalilScaffoldTopSteps.lean`（ルート import 済み）。モード横断の不変条件 `CopyIdle`（copy モード外では FPP の複写カウンタが尽きている：走者読み不可 ∨ work 零）と `ShiftIdle`（shift モード外では remaining 非正）を定義し、`tick_pull_shape`（レンズ経由の tick の到達状態は `L.set s v` の形：22 構成子）から `copyIdle_shift`・`shiftIdle_fpp`・`shiftIdle_rewind`（他レンズの tick は不変条件を保つ）を導出。`no_scan_tick_shift`（shift frame では scan モードから tick できない）と frame の再パラメータ化を使い、`steps_transfer_shift`（shift モードで始まる shift frame の `Steps` は丸ごと `galilFrame` の `Steps`、`CopyIdle` 保存）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: fallback/fpp/markEnd/rewind/scan の `Steps` 転送、init/replayStart 枝、scan の shift/fallback 入口、`galilFrame` 上で init→scan→…→scan の一周を連結、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、Frame 併合）：新モジュール `GalilScaffoldTopMerge.lean`（ルート import 済み）。共有パラメータ `Shared`（onLetter/leftFirst/init/replayStart/replayPos/replayExhausted）と、各モードのレンズ引き戻し frame からフィールドを取り寄せた統合 `galilFrame P q first`（remainingPos は shift 読みと copy 読みの選言）を定義。`wrong_mode` タクティク（`exfalso; simp_all; done`）で他モードの構成子を落とし、`shift_transfer`・`fallback_transfer`・`fpp_transfer`・`markEnd_transfer`・`rewind_transfer`（各モードの引き戻し frame の `Tick` は `galilFrame` の `Tick`、markBack は fpp レンズ読みから rewind レンズ読みへ書き換え）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `scan_transfer`（replaying=false 前提）、init/replayStart 枝の実体化、scan の shift/fallback 入口、phase 定理群を `galilFrame` 上で連結して init から scan 復帰までの一周、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、統合 VM）：新モジュール `GalilScaffoldTopVM.lean`（ルート import 済み）。Scala コントローラの VM 側部品（L/C/R ヘッド、chain watch、cycle/remaining/radius/length/replay カウンタ、FPP 状態）を一つの `GalilVM` に集め、`scanLens`/`shiftLens`/`fppLens`/`rewindLens` の 4 レンズ（3 則はすべて rfl）を定義。`steps_pull` により `shift_phase_vm`・`fpp_phase_vm`・`markEnd_phase_vm` を統合 VM 上で導出。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 4 つの引き戻し frame を一つの `galilFrame` に併合するモード別の一致補題、init/replayStart 枝、scan の shift/fallback 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、VM 統合のためのレンズ）：新モジュール `GalilScaffoldTopLens.lean`（ルート import 済み）。`Lens σ σ'`（get/set と get_set・set_get・set_set 則）で部品側の `Frame σ'` を統合 VM 上の `Frame σ` に引き戻す `Frame.pull`（各関係は射影上で成立し、残りの σ は不変）を定義し、`tick_pull`（部品 frame の `Tick` は引き戻した frame の `Tick`、コントローラ記録は同一）を 22 構成子すべてについて、`steps_pull`（`Steps` も同様）を証明（公理は propext のみ）。これで `ScanVM`/`ShiftVM`/`FppControl.State`/`RewindVM` 上の各 phase 定理が、それぞれのレンズを通して一つの統合 VM 上に載る。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 統合 VM の具体定義と各レンズ、init/replayStart 枝、scan の shift/fallback 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、choose/rewind 側 Frame 実体化）：新モジュール `GalilScaffoldTopRewind.lean`（ルート import 済み）。`RewindVM`（FPP 状態＋L/C/R ヘッド＋length/radius）と `rewindFrame first`（choose=L/C を R に複写・length=1・radius=0、rewindOne=MARKS 左・L 左・length+1、rewindPair=さらに C 左・radius+1、fppReset=`GalilScaffoldControl.reset 320`）を定義。`oddAt`（k 回トグル後の odd）と `pairAt`（m 歩後の pair）で、`choose_walk`/`choose_phase`（選択セルが k 個左なら k+1 tick で rewind モード・`pair=false`・L=C=R・length=1・radius=0・ヘッドは選択セル）、`rewind_walk`/`rewind_phase`（FIRST が m 個左なら m+1 tick で replayStart モード、L は m 回・C は m/2 回左、length は m 回・radius は m/2 回 inc、FPP リセット）を証明。これで init と replayStart 以外の全モード枝がコントローラ `Tick` に接続。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: replayStart/init 枝、scan の `scan_shift`/`scan_fallback` 入口、各枝 VM の統合（一つの σ）、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、markEnd 側 Frame 実体化）：新モジュール `GalilScaffoldTopMarks.lean`（ルート import 済み）。FPP プログラムの物理テープ 8 を MARKS として `marksTape`/`markStep`、`MarksSame`（MARKS ヘッド位置以外の全保存：mode・走者・work・段フラグ・pc・done・他テープ・テープ内容）、`marksFrame first`（atEnd=focus が END(5)、markForward=右移動、markBack=左移動（左端でない）、markSet=focus が 8 か FIRST、atFirst）を定義。`markEnd_walk`（END でないセル k 個を右へ歩く k tick、ヘッド +k、内容保存）と `markEnd_phase`（ヘッドから k 先に最初の END があれば k+1 tick で choose モード・`odd=false`・ヘッドは END の 1 つ手前）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: choose/rewind/replayStart 枝（L/C/R ヘッドとカウンタを含む VM が必要）、scan の `scan_shift`/`scan_fallback` 入口、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fpp 側 Frame 実体化）：新モジュール `GalilScaffoldTopFpp.lean`（ルート import 済み）。`marked_wellFormed`（FPP マーク付きコード全命令の `WellFormed`、`decide`）、`control_run_unique`（`GalilScaffoldControl.Run` の決定性）、`control_run_split`、`markNew`（halt 後の `marks.move(1); write(FIRST); move(1)`）、`fppFrame q first`（fppSlice=quantum 個の有効 tick で未 halt、fppDone=quantum 個以内で halt しマーク）を定義。`fpp_slices`（m スライス後の不変条件）から `fpp_phase_lift`（スケジュール済みの実行が M·q tick 内で halt するなら、コントローラは fpp から markEnd へ到達し、走者・work・段フラグは不変）と `fpp_phase_scheduled`（`fpp_scheduled` の `1584·|w|+830` 命令上界を q で割ったスライス数で具体化）を証明。これで scan・shift・copy/home・fpp の四枝が接続。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan の `scan_shift`/`scan_fallback` 入口、markEnd/choose/rewind/replayStart 枝、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、fallback 側 Frame 実体化）：新モジュール `GalilScaffoldTopFallback.lean`（ルート import 済み）。`FppControl.State` をそのまま VM とし、`fallbackFrame`（remainingPos=walker 読み可∧work 非零、copyOne=`copyBit`、copyEnd=`copyEnd`、atLeft=SOURCE focus が LEFT、homeStep=`sourceLeft`、fppStart=`startRun`）を定義。`FppControl.Mode.toController`（copy↦copy、home↦home、run↦fpp）で `fpp_control_lift`（有効な `FppControl.Tick` はすべて対応するコントローラ `Tick` で、記録は mode 以外不変）と `fpp_control_run_lift`（n tick の `Run` ⇒ `Steps n`）を証明。これで scan・shift・copy/home の三枝がコントローラ `Tick` に接続した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の `scan_shift`/`scan_fallback` 入口と fpp/markEnd/choose/rewind/replayStart の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、shift 側 Frame 実体化）：新モジュール `GalilScaffoldTopShift.lean`（ルート import 済み）。`ShiftVM`（`ShiftState`＋chain watch＋cycle）と `shiftFrame`（remainingPos=`positive remaining`、shiftOne=C 右 1・L 右 2・radius−1・length−2・`chainShiftOne`・cycle+2）を定義し、コントローラ `Tick` の n 回反復 `Steps` を導入。`shift_run_lift`（`ChainShiftRun … n …` ⇒ n 回の `shift_one`、コントローラ記録は不変）、`shift_exit_lift`（remaining 非正で `shift_done`、出力 refresh）、`shift_phase_lift`（shift 開始から scan 復帰まで n+1 tick）を証明。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: scan 枝の `scan_shift`/`scan_fallback` 入口（`JointBreak`・shift guard）と fallback 枝（`FppControl` 等）の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、走査側 Frame 実体化）：`GalilScaffoldTop.Frame` に `background`（各 transition で mode step の前に走る chain/search の背景 tick）を追加し、`scan_wait`/`scan_count` がそれを通すよう修正。新モジュール `GalilScaffoldTopScan.lean`（ルート import 済み）：`ScanVM`（L/R ヘッド＋chain watch、clock はコントローラ側）と `scanFrame onLetter leftFirst`（available=`canRight`、compare=ヘッド移動＋`Watch.Tick true`、matched=L/R 読み一致、background=`Watch.Tick false`）を定義し、`count_lift`（`JointTick.count` ⇒ `Tick.scan_count`）と `compare_lift`（`JointTick.compare` ⇒ `Tick.scan_match`、出力は `onLetter`/`leftFirst` で refresh）を証明。これで `GalilScaffoldChainFallback` の統合 tick がコントローラ `Tick` の走査枝に接続した。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: shift/fallback 各枝の Frame 実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、コントローラ tick 骨組み）：新モジュール `GalilScaffoldTop.lean`（ルート import 済み）。Scala `ScaffoldGalil.transition` の `stepInit`〜`stepReplayStart` を、VM 側の効果（ヘッド・カウンタ・search・chain・fpp）を `Frame σ` の述語 31 個（init/available/compare/matched/shiftGuard/matchedPlace/…/replayStart/replayPos）に抽象化した上で、制御レベルの分岐・clock 規約・output/replaying/odd/pair の更新・mode 遷移を具体的に持つ `Tick F delay : State σ → State σ → Prop`（22 構成子）として転写。`tick_mode`（各 tick の mode は不変か `ModeStep` の辺）と `tick_bounded`（clock は正のとき −1 か delay へのリセットのみ、`Bounded delay` 保存）を証明。これで `GalilScaffoldController.BoundedControl` を有限制御成分として載せる形が固まった。今後は `Frame` を既存の `JointTick`/`JointBreak`/`FppControl`/`SearchFinish` 等で実体化し、`GalilScaffoldStructured.machine` を複数プログラム＋この制御に持ち上げる。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Frame` の実体化、複数プログラムの一本化、`SAccepts w ↔ w ∈ PAL` の合成）。

追記（同日、コントローラ有限制御）：新モジュール `GalilScaffoldController.lean`（ルート import 済み）。Scala `ScaffoldGalil.Mode` の 10 モード（init/scan/shift/copy/home/fpp/markEnd/choose/rewind/replayStart）を `Mode`（`Fin 10` との同型で `Fintype`）として転写し、`mode = Mode.X` 代入 11 箇所をそのまま `ModeStep` の辺に、`Reaches`（反射推移閉包）と `reaches_scan`（全モードが scan に戻る：fallback 環と shift 環が唯一の出口）、`no_step_to_init` を証明。Scala の `Control` レコード（mode/clock/output/replaying/odd/pair）を `Control` に転写し、clock ≤ matchDelay の `BoundedControl delay` を `Mode × Fin (delay+1) × Bool⁴` との同型で `Fintype` にした。これが `StructuredMachine` の有限制御に載せるコントローラ成分。公理依存なし。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `stepScan`〜`stepReplayStart` の本体を Lean の tick 関係として転写し、`GalilScaffoldStructured.machine` を複数プログラム＋この制御に持ち上げて `SAccepts w ↔ w ∈ PAL` を合成）。

追記（同日、StructuredMachine 橋渡し）：新モジュール `GalilScaffoldStructured.lean`（ルート import 済み）。任意の scaffold プログラム `code : List (Instruction n)` を `StructuredMachine Unit (Fin (code.length+1) × Bool) (Fin 9) n 1`（有限制御＝clamp した pc と done フラグ、空白 `6`、入力 1 記号につき 1 micro step、入力記号は無視して tick の拍だけを与える）として実現する `machine hn code entry` を定義し、`tick_sim`（`GalilScaffoldControl.Tick code true x y` ⇒ `sMicroStep` が符号化構成上で一致）、`run_sim`（`Run code x (replicate m true) y` ⇒ `srun` 一致）、`saccepts_iff`（reset 構成からの m tick 実行の done フラグが `SAccepts (replicate m ())`）を sorry なしで証明。これでプログラム層（`GalilScaffoldControl`）と `Main.pal_in_peg_of_structured` が要求する機械型が初めて直結した。ただし Galil 全体は複数プログラム＋コントローラ＋実入力供給の合成であり、この橋は単一プログラム分。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: コントローラ全体を一本の `StructuredMachine` に落とし、`SAccepts w ↔ w ∈ PAL` を合成すること）。

追記（同日、出力完全性）：`GalilScaffoldChainFallback.lean` に `pairs_even`/`encoded_even`（符号化語の偶数位置はすべて区切り `2`）、`encoded_of_prefix_palindrome`（`prefix_palindrome_of_encoded` の逆：先頭 k 文字の回文 ⇒ 符号化語上で中心 k・半径 k−1 の `Manacher.PalAt`）、`scan_output_complete`（`ScanInvariant` が中心 k・半径 k−1 なら L=1・R=2k−1 の出力位置に立つ）を sorry なしで証明。これで走査の出力条件は健全性（`scan_output`）と完全性の両向きが揃った。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: `Main.pal_in_peg_of_structured` に渡す具体 `StructuredMachine` と `SAccepts ↔ PAL` の最終合成）。

追記（同日、破れ枝）: `GalilScaffoldChainFallback.lean` に統合 tick の「破れ」枝を追加。`JointBreak delay s t`（clock=1・右ヘッド可・走査側一致・lag 零・検証器 consume で不一致）とその事実集 `joint_break_facts`（broken=true、lag 不変、margin=inc、last/distance 不変、clock=delay、scan_matched）、`credits_margin_canonical`（前処理クレジットで margin の canonical 性が保たれる）、そして `joint_break_restart`（`joint_shift_supply` の供給結果 + `shift_ready` の freshShiftGuard から、破れ直後に restart 条件〈broken・lag 零・margin 非負・last 正・last canonical・成長〉が成り立つ）を sorry なしで証明。`#print axioms` は標準 3 公理のみ。全体 build 成功・標準公理のみ・無条件 PAL は未完（残り: 出力完全性、`Main.pal_in_peg_of_structured` への最終合成）。

**最新（2026-09-15、続き）：fresh shift → 任意回の再 shift → 終端 restart → 次 tick を実状態上で一気通貫。** `GalilScaffoldChainReadOrigin.lean` に追加：`shift_run_unique`/`chain_shift_unique`（決定性）、`Entry`（起点の再開入口不変量：OnlyScan/OnlyCredit/RadiusRep/machine=shifted/left=resumeLeft/center head 表現と位置）、`CompareRounds h s m s'`（一致周期 `OnlyMatchedRun` → cycleEnd＋右予測一致 → h 回の `ShiftRun`/`ChainShiftRun` 実行、の m ラウンド）、`rounds_origin`（Entry が保存され center/radius が m·h 進み shifts が m 増える帰納）、`rounds_restart`（末尾の左右一致・予測失敗枝で `Search.start` 入口条件）、`entry_of_only`（fresh `OnlyOrigin` ＋ shift 結果 ⇒ Entry）、`fresh_rounds_restart`（`scan_prediction_shift` の全前提から、ShiftRun/ChainShiftRun と「任意の m ラウンド＋終端一致 ⇒ center = 開始位置+(m+1)h、radius' = radius+1+m·h−h での restart 条件」）、`ReadOrigin.dispatch_match`、`read_terminal_dispatch_next_tick`（phase 前提・steps 前提なし版）、`rounds_dispatch_next_tick`（m ラウンド後の終端一致 → `dispatchOnlyMatch` → `restartInputTick` → 次 tick の scan/idle/restarts+1/clock/program/grow）。`scan_prediction_shift` の結論に `origin.center = position s.verifier`、`origin.radius = radius`、`4h ≤ distance (immediate t)` を輸出追加。全て標準公理のみ、`lake build PalPeg.GalilScaffoldChainReadOrigin` 8658 jobs 成功。未接続：周期途中の不一致（fallback 枝）、cycleEnd で左右不一致かつ予測不一致の枝、`CompareRounds` の各ラウンドの guard（右可用性・予測一致・length counter 正規性）を実 controller の tick から供給すること、実 restart の program.reset/lower alias/clock、物理 refinement、出力/締切、無条件 PAL。

追記（同日）：`ReadOrigin` に `phase : watched.control.phase = 4` を追加し、`phase_four_consume`/`phase_four_run`/`chain_shift_phase` で再 shift 越しに保存。`ReadOrigin.shift_guard`：Entry からの一致周期の末尾（cycleEnd・右可用・右＝予測）で、Scala `Chain.canShift`（periodOnly 側）の decoded 条件 lag=0・phase=4・左右不一致を導出。chainMode=watch / periodOnly は controller field として外部前提のまま。

追記（同日、fallback 側）：新モジュール `GalilScaffoldChainFallback.lean`（ルート import 済み）。`FallbackGuard`（matched 枝でも shift 枝でもない）と `fallback_window`：right head の `Represents` と length counter から、fallback の DP 窓が `w = (stream ⟨xs, right.gap⟩).take (ℓ+1)`（`raw = xs.reverse ++ rs ++ q`）で決まり、`place_ready` により fpp SOURCE の copy/home 後の内容が `bounded (w.map symbol)` になることを接続。これは後で `scan_prediction_shift` の `hw` が要求する形。**接続地図（次セッション用）**：(a) compare 側は `CompareRounds`/`rounds_dispatch_next_tick`/`shift_guard`/`FallbackGuard` で三枝が揃った。(b) fallback の残り：SOURCE 準備後の fpp プログラム実行（`GalilFppCode.code`、`GalilFppGeneration.process_all`、`GalilFppMarkSimulation.prepared_marks` は `List (Fin 4)` 入力）→ MarkEnd → Choose → Rewind → ReplayStart（Scala `ScaffoldGalil.scala` 355–440 行）→ fresh scan の `Run` と `scan_prediction_shift` の前提（`Candidate w lower h`、`hprepLag`/`hprepMargin`、`hstart`）の供給。MarkEnd/Choose/Rewind/ReplayStart の scaffold レベルの Lean モデルは未着手。(c) `PrepareControl`/`prepare_then_dp` は search 側 DP カーネル（`kernels.dp`、center 起点、LOWER）であって fpp ではないので混同しないこと。

追記（同日、Choose の意味論）：`GalilScaffoldChainFallback.lean` に `pairs_reverse_stream`/`encoded_of_represent`/`position_represent`/`stream_index`（right head から左へ読む stream と `encoded raw` の添字対応：`T[i] = e[position − i]`）、`stream_prefix_palindrome`（stream の奇数長 2r+1 の回文接頭辞 ⟺ `PalAt e (position − r) r`）、`chosenRadius`（Scala `stepChoose` の最長奇数 mark）、`choose_rewind`（新 center は head の r 下、radius r、かつ head で終わる最長奇数回文であること）。fpp の mark（`prepared_marks` の `(w.take b).reverse = w.take b`）を `Fin 3 → Fin 4` の埋め込みで stream の接頭辞回文へ移す橋と、Rewind/ReplayStart の head 操作（`copyFrom`/`left`）の decoded モデルは未接続。

追記（同日、fpp 合成）：`fallback_fpp_choose`：fallback 窓 `w = T.take (ℓ+1)` に対し、既存の `GalilFppPrepareLayout.marked_fpp w`（9 テープ fpp プログラムの実行終了時、mark テープ = w の回文接頭辞）と `chosenRadius w` を合成し、選ばれた奇数 mark が実際に立っていること、`PalAt e (|T|−r) r`（新 center は right head の r 下）、および窓内の最長性を一括で導出。`choose_rewind_window`/`window_take` も追加。**残る開口部**：scaffold の zipper SOURCE（`fallback_window` の `bounded (w.map symbol)`、`Machine 12`）と fpp の関数テープ `GalilFppPrepareInit.initial w`（`source w`、`Config 9`）の表現橋、Rewind/ReplayStart の head 操作の decoded モデル、replay scan、そして ReplayStart 後の background search（`prepare_then_dp`）から fresh watch（`scan_prediction_shift` の前提）への供給。

追記（同日、表現橋）：`fppInitial w`（9 テープ zipper、SOURCE = `bounded (w.map symbol)`）、`fppInitial_denote`（`denote` で `GalilFppPrepareInit.initial w`）、`fpp_realized`（`realize_completed` で `marked_fpp_exact_cost` を zipper 側へ：`Program.Completed` の実行、終了 pc=0、SOURCE 不変、mark テープ = `marks w`、歩数 ≤ 1584|w|+830）。zipper↔関数テープの橋は `Program.Completed` の粒度で閉じた。残り：`stepFpp` の quantum 刻み（`Control.Run`／`RawSchedule` 相当、DP 側 `GalilScaffoldDpCost.scheduled_correct` の fpp 版）、`fallback_window` の SOURCE（12 テープ `Machine 12` の tape 7）と `fppInitial`（9 テープ）の対応、Rewind/ReplayStart。

追記（同日、スケジューリング）：`fpp_scheduled`：`Control.scheduled_completed` で、命令機会が 1584|w|+830 回以上与えられれば `Control.Run GalilFppMarkedCode.code ⟨fppInitial w,false⟩ bs ⟨v,true⟩` で停止し mark が揃う（DP 側 `scheduled_correct` の fpp 版）。Scala `stepFpp` の quantum 刻みへの対応は `Control.Run` の粒度。残り：Copy/Home/Fpp 相の 9 テープ decoded controller（`PrepareControl` の fpp 版）で `beginFallback` から `fppInitial w` への到達、Rewind/ReplayStart。

追記（同日、fallback controller）：`FppControl`（9 テープ decoded controller：`Mode` copy/home/run、`State`、`beginFallback`（fpp reset・walker := right・remaining := length+1・SOURCE に LEFT）、`Tick` copyBit/copyEnd/sourceLeft/startRun、`Run`、`source_copy`/`source_home`）と `fallback_prepared`：`beginFallback old p length` から `2|w|+3` tick で run モードに入り、program がちょうど `⟨fppInitial w,false⟩`（`fpp_scheduled` の開始機械）。全 fallback 部品が揃った：`FallbackGuard` → `beginFallback` → `fallback_prepared` → `fpp_scheduled` → `fallback_fpp_choose`。次はこれらを right head（`Represents raw`）で一本に合成する `fallback_end_to_end`、その後 Rewind/ReplayStart の head 操作。

追記（同日、fallback 一本化）：`marks_cell`（`marks w i = 8 ⟺ 0<i≤|w| ∧ IsPal (w.take i)`）と **`fallback_end_to_end`**：compare 状態の right head（`Represents raw`、focus あり）と length counter から、`beginFallback` → `FppControl.Run`（2|w|+3 tick）で `⟨fppInitial w,false⟩` → `Control.Run`（機会 ≥ 1584|w|+830）で停止・mark = 窓の回文接頭辞 → 選ばれた奇数 mark が立ち、`PalAt (encoded raw) (position s.right − r) r` かつ窓内最長。Rewind の到達 center が `position right − r` であることまで意味論として固定。残り：Rewind/ReplayStart の head 操作（`copyFrom`/`left`）と counter 更新の decoded モデル、replay scan、background search → fresh watch。

追記（同日、replay）：`signedRead_pos` と **`replay_scan`**：新 center の head（`Represents`、位置 c、`r+1 ≤ c`）と `PalAt (encoded raw) c r` から、r 回の外側比較が全て一致し `ScanInvariant raw c k l r'`（k ≤ r）と `LeftMoves h k l` を帰納で復元（Scala の replay 中は shift/fallback が起きない、の Lean 側）。次：`fallback_end_to_end` と合成する `fallback_replay`（right head から r 回左へ動いた center head の存在：`Represents ∧ 位置 ≥ 1 → focus あり` の補題が要る）、その後 background search（`prepare_then_dp`）→ fresh watch。

追記（同日、fallback→replay 合成）：`present_of_position`（表現された head が位置 ≥ 1 なら focus あり）、`left_moves_exists`（位置 ≥ n+1 なら n 回の左移動が存在し表現保存）、**`fallback_replay`**：compare 状態の right head から、fallback の最長奇数回文の中心 head `h`（`LeftMoves right r h`、位置 `position right − r`）が存在し、replay の r 回比較で `ScanInvariant raw c k l r'`（k ≤ r）が復元される。fallback 枝は「入口 → fpp → 選択 → 巻き戻し → replay 復元」まで Lean 上で一本。残り：replay 完了後の background search（`prepare_then_dp` の `Result`/`Candidate`）から fresh watch（`scan_prediction_shift` の前提：`Candidate w lower h`、`hprepLag`/`hprepMargin`、`hstart`、`Run s bs t` の phase 4）への供給、Rewind/ReplayStart の counter 更新（length/radius/replay）の decoded 表現。

追記（同日、fresh watch 入口）：`fill_snoc_shape`（period tape の `fill` の形）、`copy_walk_period`（`ChainAnswer.CopyWalk` → `ChainPeriod.Copy`、period tape を `fill` で同時構成）、**`fresh_watch_entry`**：search が `.found` に達し DP `Result` を持つとき、`Candidate w lower h`、半周期 `ys ++ [b] = ((stream p).drop 1).take h`（|ys|+1 = h）、`Period.Copy` で `⟨(ys.map plain).reverse ++ [.first c], .plain b, []⟩`、tail mark 後の `Back (h+1)` で **`(ready c ys b).period`**、そして任意の外側一致イベント（|bs| = h、|cs| = h+1）に対する `prepare_paced` の credits（`final = run (start radius) (prepEvents sm dm bs cs)`、lag 非零）。これは `scan_prediction_shift` の `hs`（ready 制御）・`hprepLag`/`hprepMargin`・`hcopyLength`・`hc` の供給元。未接続：`ready` の他フィールド（counter reset/phase 0）を Scala `Chain.start` の decoded 状態として置く定義、verifier = center head（`hh`/`hstart`）の明示、そして Watch の実 `Run`（入力駆動）を SearchRun/tick から供給する部分。

追記（同日、found→restart 合成）：`watchStart cen c ys b final`（Scala `stepBack` 直後の decoded watch 状態：verifier = center head、`ready c ys b`、credits の lag/margin）と **`found_rounds_restart`**：search の found ＋ DP `Result`（center place ⟨a::ls,gap⟩ の窓）から、`fresh_watch_entry` で chain 側前提（ready 制御・半周期・Candidate・credits・center 位置）を全部埋めて `fresh_rounds_restart` を適用。外部前提として残るのは実 watch `Run s0 bs t'`（phase 4・lag 0）、fresh shift 時点の `ScanInvariant`／右可用性／予測一致／counter 事実。これで「search found → 準備 → watch → fresh shift → 再 shift × m → 終端 restart」が一本。未接続：watch `Run` 自体を tick から供給（Watch の Tick/Outer は既存、外側 scan の一致イベントと入力到着の interleave）、restart 後の background search と `SafeQuanta` の接続、fallback 後の replay 完了から search 開始（`search.start(zero)`）への接続、出力/締切、物理 refinement、無条件 PAL。

追記（同日、Candidate→bounce）：`palindrome_prefix_index` と **`candidate_bounce`**：DP `Candidate w lower h`（2h+1・4h+1 の回文接頭辞）、`w[0] = c`、半周期 `ys ++ [b] = (w.drop 1).take h` から `(w.drop 1).take (4h) = bounce c b ys ++ bounce c b ys`（純粋な添字論、標準公理のみ）。これは `caught_shift_guard`/`prepared_shift_guard` が要求する `Reads cen (bounce ++ bounce) q` の記号列側。残り：scan の回文（`PalAt e center radius`、4h ≤ radius）と `stream_index` の鏡映で verifier の右 4h 読みが窓の左 4h と一致すること（head からの Reads 存在補題が要る）、その Catch から watch `Run` の phase 4・lag 0 到達。

追記（同日、watch Run 供給）：`good_of_consume`（unbroken な consume ⇒ `Watch.Good`）、`verify_watch_run`（`VerifyRun.Run s n t` unbroken ⇒ `Watch.Run ⟨s, ofNat (n+k), margin⟩ (replicate n false) ⟨t, ofNat k, margin⟩`：内部 take のみ、lag が 1 読みごとに減る）、`verify_run_position`、**`found_watch_run`**：Codex の `found_window_safe`（found ＋ `Reach` ＋ 回文 ⇒ verifier の n ≤ min(radius, 4h) 読みが unbroken）と合成し、`watchStart` から `Watch.Run`（外側イベントなし）で lag が v−n、unbroken・表現保存・distance = n、4h ≤ n なら phase 4（`watch_phase`）。これで `found_rounds_restart` の外部前提 `hrun`/`hphase`/`hzero` の「外側一致イベントが interleave しない場合」の供給ができた。残り：外側一致（`true` tick、lag/margin の queued/immediate）の interleave と lag = v の一般会計（Codex の `prepared_balance`/`shift_ready`）、fresh shift 時点の `ScanInvariant`／右可用性／予測一致の供給、restart 後・replay 後の search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、外側イベント interleave）：`watchTick`/`watchConsumes`/`watchLag`（tick ごとの consume 数と lag：lag>0 なら内部 take、`true` なら lag=0 で immediate・そうでなければ queued）、`verify_run_add`（`VerifyRun.Run` の分割）、**`verify_watch_run_events`**：任意の外側イベント列 `bs` と初期 lag に対し、`watchConsumes bs lag` 本の unbroken な consume があれば `Watch.Run ⟨s, ofNat lag, ofNat margin⟩ bs ⟨t, ofNat (watchLag bs lag), ofNat (margin + count true)⟩`。これで watch の `Run` は「その本数の unbroken 読みが存在する」ことに帰着した（`found_window_safe` は 4h まで保証）。残り：fresh shift 時点の `ScanInvariant`／右可用性／予測一致の供給（scan 側の一致イベントと `bs` の同一視）、lag 会計の一般化（Codex `prepared_balance`/`shift_ready`）、search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、watch 相の供給）：`incN`/`incN_value`/`incN_canonical`、`verify_watch_run_events` を任意 margin counter に一般化（外側イベントごとに `inc`）。`ScanEvents`（watch 中の scan 側：`true` = 一致比較で `scan_matched`、`false` = 静止）と `scan_events_invariant`。**`watch_shift_supply`**：chain 開始時の `ScanInvariant`（radius r₀ = value radius）、prep 中と watch 中の `ScanEvents`、`watchConsumes` 本の unbroken 読み、lag 枯渇（`watchLag = 0`）から、`Watch.Run s0 ws t'`・`value s0.lag = r₀ + prep 一致数`・lag 0・distance = scanRadius・（4h ≤ scanRadius なら phase 4）・`ScanInvariant raw (position cen) scanRadius l₂ rr₂` を一括導出（`prep_value` で lag と scan radius の会計を同一視）。これで `found_rounds_restart` の外部前提のうち watch 相の分が「同じイベント列」から出る。残り：fresh shift 時点の右可用性・予測一致・counter 事実（radiusCounter = scanRadius+1 等）の供給と `found_rounds_restart` への最終合成、restart 後・replay 後の search 起動、出力/締切、物理 refinement、無条件 PAL。

追記（同日、最終合成）：`credits_lag_canonical` と **`found_supplied_restart`**：`found_rounds_restart` の watch 相前提を `watch_shift_supply` で埋めた版。外部前提は、chain 開始時の `ScanInvariant`（radius r₀ = value radius）、prep 中と watch 中の `ScanEvents`（scan と chain が同じイベント列を見ること）、`watchConsumes` 本の unbroken 読み、lag 枯渇、4h ≤ scanRadius、shift 枝の入力側条件（右可用・予測＝右読み・左右不一致）、counter 表現のみ。結論は `∃ t', Watch.Run (watchStart …) ws t' ∧ t'.machine = z ∧ lag 0 ∧ ∃ endpoint…, ShiftRun ∧ ChainShiftRun (immediate t') ∧ ∀ m n…（再 shift × m → 終端 restart 条件）`。残り：restart 後・replay 後の search 起動（`SafeQuanta` と `search.start`）、周期途中の不一致（chain broken → restart）の scan レベル接続、出力/締切、物理 refinement、無条件 PAL。

追記（同日、出力の意味論）：`pairs_odd`/`encoded_odd`（`encoded raw` の奇数位置 2i+1 は `letter raw[i]`）、`letter_inj`、`prefix_palindrome_of_encoded`（`PalAt (encoded raw) k (k−1) → IsPal (raw.take k)`）、**`scan_output`**：`ScanInvariant raw c r l rr` で L が位置 1（Scala `left.isFirst`）、R が位置 2k−1（k 番目の文字上）なら `IsPal (raw.take k)`。Scala の `output = left.isFirst` の健全性側。完全性側（接頭辞が回文なら scan がそこに到達する）は `Assembly.answer_length_iff_mem_PAL` 等の仕様レベルに対応し、scaffold レベルでは未接続。

追記（同日、staged search との接合）：`stage_found_supplied`：`GalilScaffoldStagePrepare.prepared_exit` の探索実行 `SafeQuanta (runState p q) p.program cs u y` が `.found` で終わり `y` に DP `Result` があるとき、`found_supplied_restart` がそのまま適用できることの接合。これで Codex の「準備 → run → found/missed/次 stage」（時間予算つき）と、ウチの「found → chain → shift/再 shift → restart」が同じ状態の上で繋がった。残る大物：`prepared_exit` の found 出口から `Result` を取り出す（`dp_quanta_safe` の存在実行と実際の実行の同一視、または `prepared_exit` に Result を輸出させる）、restart（`restart_input_tick` の `.grow`）から次の `PacedPrepared` へ、fallback/replay 完了から `search.start(zero)` へ、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、探索の決定性）：`execute_unique`（`WellFormed` な命令の zipper 側 `Execute` は決定的：read 表の `Nodup`）、`control_tick_unique`（`dp_wellFormed` で DP コードの `Control.Tick` が決定的）、`safe_calls_unique`/`safe_quanta_unique`/`safe_quanta_append`/`safe_quanta_cons_run`、**`dp_run_result`**：DP 予算（3186|w|+1683 ≤ 64|cs|、count true ≤ debt）を持つ実際の `SafeQuanta s ⟨Preload.initial w lower,false⟩ cs u y` は `dp_quanta_safe` の停止実行そのものであり、`y = ⟨v,true⟩` かつ `Result w lower 0 (denote v)`。これで `stage_found_supplied` の `hv` は実行から取り出せる（`prepare_complete` の `program.config = Preload.initial w lower ∧ done = false` と合わせる）。残り：restart（`.grow`）→ 次の `PacedPrepared`、fallback/replay 完了 → `search.start(zero)`、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、found ↔ 候補）：`RunInvariant`（`run` ↔ 未停止、停止後は `found ↔ pc = 346`）、`safe_calls_invariant`/`safe_quanta_invariant`（`SafeCalls`/`SafeQuanta` に沿って保存、`finish_run_iff`・`found_iff` を使用）、**`run_found_candidate`**：DP 予算つきの実 `SafeQuanta s ⟨Preload.initial w lower,false⟩ cs u y` は `y = ⟨v,true⟩`・`Result`・`u.mode ≠ run`・`u.mode = found ↔ ∃ k, Candidate w lower k`。これで `stage_found_supplied` の `hu`/`hv` は「実行が found で終わった」事実そのものから出る。残り：`prepare_complete` の出口（`program.config = Preload.initial w lower`）と `runState` の接合定理、restart（`.grow`）→ 次の `PacedPrepared`、fallback/replay 完了 → `search.start(zero)`、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、stage → chain）：**`stage_run_chain`**：`prepare_complete` の出口 `t`（run、`program = ⟨Preload.initial w lower,false⟩`）と実際の `SafeQuanta (runState t q) t.program cs u y`（DP 予算つき）から、`y = ⟨v,true⟩`・`Result`・`u.mode ≠ run`・`found ↔ 候補あり`、そして found なら `stage_found_supplied` の chain 入口。残り：restart（`.grow`、`GalilScaffoldGrow`）→ `PacedPrepared` の dispatch、fallback/replay 完了 → `search.start(zero)`、found 後の chain と scan の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、第 1 stage との接合）：**`first_stage_chain`**：Codex の `StagePrepare.first_stage_safe`（grow → `PacedPrepared` → 実 DP 実行、`advances 2048 2048 es` の時計対応、`3·radius ≤ 5·r`）の出力に `stage_found_supplied` を当てる。`t.mode = found` かつ `p.mode = run` なら DP 候補と半周期（ひいては `found_supplied_restart` の全鎖）。これで「探索の第 1 stage（時計付き）→ found → chain → shift/再 shift → 終端 restart」まで同じ状態の上で接続。残り：`p.mode = run` を `PacedPrepared` から導出、restart（`restart_input_tick` の `.grow`）から第 2 stage 以降（`NextStage`）へ、fallback/replay 完了 → `search.start(zero)`、found 後の scan と chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、準備の決定性）：`Prep` 名前空間：`Same`（debt 以外の場の同値）、`tick_same`（`PrepareControl.Tick` は `Same` に沿って移送）、`tick_unique`（enabled tick は決定的：mode／work の正負／テープ focus／walker の読みで排他）、`run_unique`、`paced_same`（全 enabled の `PacedRun` は debt 以外で plain `Run` と一致）、**`paced_prepared_mode`**：`PacedPrepared (ofNat lower) center s bs p` で `|bs| = 2·lower+2|w|+7`、`s.span = ofNat span` なら `p.mode = run ∧ p.program.config = Preload.initial w lower ∧ done = false`。`first_stage_chain` の `p.mode = run` 前提はこれで落とせる（`u.span` の値が `PacedGrowing` から要る）。残り：restart（`.grow`）→ 第 2 stage 以降、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、stage 接合の完成）：`paced_growing_span`（grow tick ごとに span +8）、**`first_stage_chain_run`**（`p.mode = run` を `paced_prepared_mode` から導出した版）、**`later_stage_chain`**：Codex の `later_stage_safe`（`.double` から `Double.Run` → `restoreState` → `PacedPrepared` → 実 DP 実行、時計 `advances 2048 clock es`）の found 出口に `stage_found_supplied` を当てる（span は `Double.span_of_run` で供給）。これで第 1 stage・後段 stage の両方から chain 入口へ繋がった。残り：restart（`restart_input_tick` の `.grow`）から `later_stage_safe` の入口（`.double`、work = |as|、span 0、debt 条件）への遷移、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement、無条件 PAL。

追記（同日、restart → 第 1 stage）：`initialDebt_value`/`initialDebt_canonical`、**`begin_entry`**（`Search.start` 直後の scheduler `begin lower radius` は grow・`work = ofNat (max k 1)`・span 0・`value debt = −radius`・Canonical）、**`restart_first_stage`**：`restoreState b0 (begin lower radius)` から `first_stage_chain_run` を適用し、restart 後の探索（grow → 準備 → DP → found）から chain 入口まで。`restart_input_tick` の scheduler が `begin last radius` であることは `restart` の定義から読めるが、`restartInputTick`/`receiveRestart`/`restartScanTick` が search を触らないことの明示補題はまだ（次）。残り：その明示、fallback/replay 完了 → `search.start(zero)`（`begin_entry` で同型に接続可）、scan/chain の同一イベント列の供給元、出力の完全性、物理 refinement（RawTick `Represents` と `Control.Machine` の橋は `restart_input_tick` が輸出）、無条件 PAL。

追記（同日、restart tick の scheduler）：**`restart_input_tick_scheduler`**：`restartInputTick entry delay replaying trailing input s = some t` なら `t.search = startSearch entry last radius arrived.search`（`arrived := receiveRestart s input`）、scheduler = `begin last radius`、program = `RawTick.reset entry …`。これで `rounds_dispatch_next_tick`（終端一致 → dispatch → restart tick）の出口が `begin_entry`／`restart_first_stage` の入口（`begin lower radius`）に文字通り繋がる。残り：`RawTick.Machine`（heap 実装）と `Control.Machine 12` の `Represents` 橋を `restoreState` の program に通すこと、fallback/replay 完了 → `search.start(zero)`、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、prepare の物理実現）：`RawPrep` 名前空間：`written_heap`/`moved_heap_other`（heap frame）、`represents_write`/`represents_write_right`/`represents_left`/`represents_start`（抽象テープ操作の raw 対応、`HeapProgram.written_represents`/`moved_right`/`moved_left` から）、**`prepare_tick_raw`**（`PrepareControl.Tick` は heap 機械上で fresh セル高々 1 個で実現され `RawTick.Represents` を保つ、他セル不変）、**`prepare_run_raw`**（`PrepareControl.Run` は distinct な fresh 番地列に沿って実現）。これで `restart_input_tick` が輸出する `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` から、抽象 stage（`prepare_complete`）の出口 `⟨Preload.initial w lower,false⟩` を表す raw 機械が得られ、DP 実行は `RawSchedule.realize_run` で raw 側へ写せる。残り：`prepare` dispatch（`reset 320` と LOWER 書き込み）の raw 対応、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、prepare dispatch の物理実現）：**`RawPrep.prepare_raw`**（`prepare x lower center` の program = `reset 320` ＋ LOWER への write-right は heap 機械上で `RawTick.reset` ＋ `written`/`moved` で実現、fresh セル 1 個、他セル不変）と **`RawPrep.prepared_run_raw`**（`PreparedRun lower center s n t` は distinct な fresh 番地 n 個で実現され、出口 `t.program`（`prepare_complete` なら `⟨Preload.initial w lower,false⟩`）を表す raw 機械が存在）。DP 実行側は `RawSchedule.realize_run`（`Control.Run` → raw `Run`、fresh 番地列）で対応済み。残り：`SafeQuanta` の機械列を `Control.Run`/`GuardedRun` として取り出して `realize_run` へ渡す接合、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、DP 実行の物理実現）：`safe_calls_control_run`/`control_run_append`/`safe_quanta_control_run`（`SafeQuanta` の機械列は有効フラグ列 `es`（|es| = 64|as|）に対する `Control.Run`）、`dp_wellFormed_lookup`、**`quanta_raw`**：`RawSchedule.realize_run` により、実探索 `SafeQuanta s x as t y` は `Represents raw x` な heap 機械上で fresh 番地列（64|as| 個）に沿って `RawSchedule.Run` として実現され、終端は `Represents raw' y`。`prepared_run_raw` の出口 raw 機械をここに渡せば、restart → 準備 → DP → found までが raw 側でも一本。残り：restart tick の `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` から `prepared_run_raw` へ渡す際の番地 fresh 性（heap の有限性 `FiniteHeap` から fresh 番地列を取る補題）、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、stage の物理実現）：`RawPrep` に `moved_finite`、`fresh_addresses`（有限 heap から distinct な fresh 番地列を任意個）、`prepare_tick_raw`/`prepare_run_raw`/`prepare_raw`/`prepared_run_raw` に `FiniteHeap` 保存を輸出、`paced_run_raw`/`paced_prepared_raw`（`PacedPrepared` の raw 実現）。`paced_growing_program`（grow は program 不変）と **`stage_raw`**：`s.program` を表す有限 heap の raw 機械から、`PacedGrowing → PacedPrepared → SafeQuanta` の stage 全体が fresh 番地列に沿って raw 側で実現され、終端は `⟨v,true⟩` を表す（`Represents`）。`restart_input_tick` の `Represents t.search.program ⟨⟨entry,reset⟩,true⟩` を入口にすれば、restart 後の探索は raw 側でも `stage_raw` で一本。残り：raw 番地列と Scala の実 heap 割り当て（`Allocator`/`Bounded`）の対応、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、Scala 割り当てとの橋）：**`bounded_finite`**（Codex の `Allocator` の `Bounded` 不変量 ⇒ `FiniteHeap`）と **`blocks_fresh`**（現在 node 以降の m 個の連続 `block (node+1+i) 64 slots` の連結は長さ 64·m・distinct・fresh）。これで `stage_raw`/`quanta_raw` の fresh 番地列を Scala の実割り当て（tick node ごとの 64 セルブロック）で供給できる。残り：scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

追記（同日、統合 tick）：**`JointState`/`JointTick`/`JointRun`**（scan の左右 head・chain の `Watch.State`・match clock を 1 つの遷移に：不可用 tick／カウントダウン／clock=1 で発火する一致比較、chain 側は同じ tick の `Watch.Tick`）と **`joint_run_events`**：1 つの `JointRun` から同一のイベント列で `Watch.Run` と `ScanEvents` が出て、`true` の個数と終了 clock が Codex の `MatchClock.run delay clock avail` に一致。これが「scan/chain の同一イベント列の供給元」。shift／fallback の比較枝は別関係（`shift_guard`・`FallbackGuard`）で扱う。残り：`JointRun` から `watch_shift_supply` 相当を出す系（次）、出力の完全性、無条件 PAL。

追記（同日、統合 tick からの供給）：**`joint_shift_supply`**：`JointRun` 1 本（`watchStart` から、match clock `delay`/`clock0`、可用列 `avail`）と lag 枯渇から、同一イベント列 `events`（`count true = (MatchClock.run delay clock0 avail).2`）で `Watch.Run`、`value s0.lag = r₀ + prep 一致数`、distance = scanRadius、（4h ≤ scanRadius なら phase 4）、`ScanInvariant raw (position cen) scanRadius t.left t.right`、終了 clock。`watch_shift_supply` の「同一イベント列」前提が `JointRun` の定義そのものに帰着した。残り：`JointRun` の各 tick の `Watch.Tick`（`Good` = 予測と入力の一致）を入力側から供給する扱い（これは shift 枝の分岐条件そのもの）、出力の完全性、無条件 PAL。

追記（同日、replay 後の探索入口）：`begin_entry` を `k = 0` を含む形へ一般化（`zero lower` なら `work = inc lower = ofNat 1 = ofNat (max 0 1)`）、**`replay_stage_entry`**：`ReplayStart` の `search.start(zero)`（`begin (ofNat 0) reset`）は grow・work 1・span 0・debt 0。`restart_first_stage` と同型に `first_stage_chain_run` へ渡せる（radius 0 なので `3·radius ≤ 5·k` は自明）。残り：`RawTick.Machine` と `Control.Machine 12` の `Represents` 橋を program に通すこと、scan/chain の同一イベント列の供給元、出力の完全性、無条件 PAL。

**最新（2026-09-15、Claude Code）：再 shift を起点から起点へ回せる形にした。** 新モジュール `lean-pal/PalPeg/GalilScaffoldChainReadOrigin.lean`（ルート import 済み）。`Offset k c d`（control が参照 sweep `run ready pre` の counter 一様 −k、period/forward/broken 一致）を定義し、`consume`/`run`/`ChainShiftRun` で保存されることを証明（`Offset.run`/`Offset.shift`）。`OnlyOrigin` の fresh watch `Run` 依存を外した `ReadOrigin`（`pre`/`reads`/`shifts`/`offset`/三 counter Canonical/`length : 2(k+2)h ≤ |pre|`）を定義し、`check_pair`/`joined_reads`/`joined_input_period`/`reshift_compare`/`reshift_palindrome`/`matched_checked`/`matched_restart` を Reads ベースで移植（`read_prediction_window`/`read_check_pair`/`read_compare_restart`、`sweep_last_lower` は m 周期版 `last` 下界）。`ReadOrigin.ofOnly`（fresh 起点＋distance≥4h ⇒ shifts=0 の起点）と **`ReadOrigin.reshift_origin`**（一周期の一致比較＋cycleEnd＋右予測一致 ⇒ center+h, radius+h, shifts+1 の起点と、その resumed 端点の OnlyScan/OnlyCredit/RadiusRep）を証明。`lake build PalPeg.GalilScaffoldChainReadOrigin` 8658 jobs 成功・標準公理のみ。Codex 最終定理 `reshift_initialized` のビルド失敗も修正済み。次は `OriginRun`（複数ラウンドの実行関係）で不変量を帰納し、終端枝（`matched_restart`）と接続する。全 controller / 実 restart 全更新 / 無条件 PAL は未完。

**修正**：Codex 最終ターン（9/14 09:59）の `OnlyOrigin.reshift_initialized`（`GalilScaffoldChainInputSupply.lean` 約3014行）は `hnew` の `simpa` が算術正規化でずれてビルド失敗していた。`hpos` と `omega` で `rw` する形に直し、`lake build PalPeg.GalilScaffoldChainInputSupply` が exit 0、同定理の公理は propext/Classical.choice/Quot.sound。全体 build は未再実行。

**進行中の設計（次の実装）**：再 shift 後に起点を再構成するため `OnlyOrigin` を fresh watch の `Run` 依存から外す。
- 新フィールド：`pre : List (Fin 3)`、`reads : Reads start.verifier pre watched.verifier`、`shifts : ℕ`（これまでの shift 回数 k）、`control : Offset (k*h) watched.control (run (ready token interior boundary) pre)`（SamePrediction ∧ broken 一致 ∧ phase 一致 ∧ distance/boundary/last の値が −k·h）、三 counter の Canonical、`length : 4h + k*h ≤ pre.length`。`ticks/watchRun/startPosition` は削除（`endPosition` は残す）。
- 根拠：`chainShiftOne` は distance/boundary/last を一様に −1 し period/phase を保つ（`chain_shift_values`）。`consume` の counter 更新は last:=boundary、boundary:=distance、distance:=inc なので一様オフセットと可換。よって shift 後の control は `run ready pre` の一様オフセットに正確に等しい。
- 移し替える補題：`watch_previous_window`（Reads + `successful_cycles` + `reads_index` で証明し直す）、`shifted_prediction_window`、`shifted_check_pair`、`only_history_check_pair`、`watch_last_lower`（m 周期版：`round_trip` を m 回で `(2m−1)h ≤ last`）、`watch_shift_last_positive`、`history_terminal_last/canonical`、`only_compare_restart`。Run 版は run_trace から導く薄い wrapper として残す。
- 新定理 `OnlyOrigin.reshift_origin`：`reshift_after_matches`＋`reshift_compare`＋`reshift_initialized` から `center' = center+h, radius' = radius+h, k' = k+1, pre' = pre ++ actual(2h)` の起点を構成し、その resumed 端点の OnlyScan/OnlyCredit/RadiusRep を返す。これで only=true の再 shift を帰納で回せる。
- 全 controller / 実 restart 全更新 / 無条件 PAL は未完。

## Resume checkpoint — 2026-09-14、今回の引き継ぎ

**最新：現在半径R+hを継続実行から導出**：OnlyOrigin.reshift_after_matchesを追加。shift入口OnlyScan(c+h,R+1−h)と同じ初期machine/left、OnlyMatchedRun n、cycleEndからn+1=2hを導き、実counterのRadiusRep(R+h)、OnlyCredit、再shift後PalAt(c+2h,R+1)を一括証明。現在scan半径を独立前提にしない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ39463終了済み。次は実center表現/length counterと合わせ同じ再shift microsteps/終了OnlyScanを構成し、次OnlyOriginへ更新。全controller/無条件PAL未完。

**最新：実履歴から再shift後の回文性を導出**：OnlyOrigin.reshift_palindromeを追加。現在OnlyScan(c+h,R+h)、同じTrace/LeftMoves、cycleEnd/右可用/予測一致から最後consumeを実行し、joined_input_periodを実verifier終点まで供給。旧scanと短回文継承によりPalAt(c+2h,R+1)を証明。独立した新PalAt/右周期/短DP候補/終点位置は要求しない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ42505終了済み。現在OnlyScanのc+h,R+hはまだ前提で、継続比較帰納からの座標/半径同期と再shift実行/新OnlyOriginの構成が残る。全controller/無条件PAL未完。

**最新：shift前後を通す実入力周期を導出**：OnlyOrigin.joined_input_periodを追加。joined_reads→successful_cycles→hasPeriod_take→reads_indexにより、旧center<jかつj+2h≤現在verifier位置の全範囲でencoded raw[j]=encoded raw[j+2h]。実Traceとbrokenfalseだけから導き、独立period前提なし。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ51466終了済み。次はreshift_compareの最後consume後Traceへ適用し、current verifierと外側rightの座標対応/現在PalAtを介してreshift_from_rightへ接続。再shift新起点/全controller/PALは未完。

**最新：shiftをまたぐ実read列を元ready予測へ接続**：OnlyOrigin.joined_readsを追加。同じorigin watchのpreと、shift後の成功Trace extraをverifier位置不変で連結し、Reads start(pre++extra)currentと元readyからの同列成功を導出。shiftでdistance counterが変わってもSamePrediction/broken保存から成功を逆向きに移す。全体build9121 jobs成功/exit 0、新補題公理propext/Quot.sound、ジョブ25852終了済み。次はjoined列のsuccessful_cycles＋reads_indexから旧watchと継続全体の右側周期性を導きreshift_from_rightへ接続。再shift新起点/全controller/PALは未完。

**最新：再shiftの短回文は旧centerから継承**：reshift_from_rightを追加。旧PalAt(c,R)、一周期後のPalAt(c+h,R+h)、h≤R、右側周期性/終端範囲からPalAt(c+2h,R+1)を証明。必要な短PalAt(c,h)は旧回文の制限から内部導出し、新DP Candidateを要求しない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ53232終了済み。右側周期性はまだ前提で、実2h Traceから旧watch区間まで含めて供給する接続が残る。一周期後のscan座標/半径対応も履歴から組み立てる必要がある。全PAL未完。

**最新：再shift比較の終端実記号と一周期履歴を接続**：OnlyOrigin.reshift_compareの結論を強化。同じGoodから読んだaを取得し、Trace(extra++[a])と比較後LeftMovesを返し、cycleEndからその長さ=2hを導出。追加の成功列や長さ仮定は不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ39267終了済み。左右不一致なので旧centerのscanをradius+1へ延長したとは扱わない。次はこのちょうど2hの成功履歴と再shiftの新center/周期窓を接続して新PalAt/OnlyOriginを再構成。全PAL未完。

**最新：再shift終端比較の不一致/consume成功を同時導出**：OnlyOrigin.reshift_compareを追加。固定起点と同じOnlyScan/Trace/LeftMoves、cycleEnd、右可用、実右read=予測から、実左≠右・Good watch・合法1consume・broken=falseを一括導出。checkPair/予測token存在は内部供給。左右一致優先枝には入らないことを実headで確定。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ30848終了済み。mode/watch/phase4/replay=falseを含むcanShift dispatch、再shift後PalAt/周期window/起点更新は未完。全PAL未完。

**最新：再shiftのcredit収支を接続**：Scala beginChainShiftはchain.matched()→beginShift(cycle reset)→shiftの順。reshift_only_creditで旧OnlyCredit＋cycle正規形/cycleEndから、matched.margin.incの非負性を導出し、同じChainShiftRun(immediate w,reset cycle)終点へOnlyCreditを供給。比較前margin≥0というfresh専用前提は再shiftでは不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ86278終了済み。再shiftの新PalAt/周期window/OnlyOrigin更新・同じ実行の合法性/全controller/PALは未完。下記の「再shift収支未完」はこのcredit部分に限り更新済み。

**最新：終端dispatch→次tick到着/restart/時計を接続**：旧terminal_dispatch_restartをterminal_dispatch_next_tickへ置換。OnlyOrigin/同じ履歴から終端一致dispatchを通し、Option到着込みrestartInputTickにbind。拡張rawの半径+1 scan、Idle/回数/到着後可用性での時計/空program/growを一括証明。delay>1が必要。旧集約のheap/lower/work結論はこの新集約では省略（下位restart/startSearch定理に保持）。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ87529終了済み。全controller mode/全head/報告出力/成功watch到達性/他分岐/無条件PALは未完。

**最新：到着・実head可用性・restart・同tick時計を統合**：scanAvailable（Scala同様replaying || trailing設定でplace/head可用性を選択）、receiveRestart（Option入力）、restartInputTick/restart_input_tickを追加。到着有無の両方で拡張raw上scan、Idle、restarts+1、到着後rightから算出した時計、空program/growを証明。delay>1のbroken-chain scan枝の射影であり、全mode dispatch/報告output/walker等全head/heapの入力Ref対応は未完。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ43307終了済み。次は終端比較から次tickのこの関数へ接続し、後続検索準備・他分岐・全controllerへ進む。無条件PAL未完。

**最新：restart同tickのscan時計更新を接続**：Scala runはbackground→stepScanの順。restartScanTick/restart_scan_tickを追加し、restart後に既存MatchClock.runを同tickのavailabilityで1回進める。delay>1なら比較0回、利用可能なら時計delay−1、不可ならdelay、scan保存/Idle/growを証明。局所restartのclock=delayをtick終了値と誤認しないこと。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ58581終了済み。availabilityは現状Bool前提で、実replay/advanceTrailingGap/head可用性からの計算と到着込みtickへの統合は未完。restartScanTickはdelay>1でのみ比較を省略できる射影。全controller/他分岐/無条件PAL未完。

**最新：restart直前の入力到着を保存**：compareArrivalで射影中のcenter/left/right/verifierへ同じ到着aを追加。OnlyRestartReady.arrivalが拡張raw上のscanと全restart条件を保存。restartArrival/restart_after_arrivalで到着後もrestart成功、拡張入力上scan/Idle/clock/回数/program reset/heap保存を証明。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ96159終了済み。初回record構文/射影展開を修正済み。到着しないtick、broken時背景no-opとclock実順序、他head（walker等）を含む全controllerへのrefinementは未完。無条件PAL未完。

**最新：guard付き終端dispatch→restartを直接合成**：terminal_dispatch_restartを追加。OnlyOrigin＋同じ現在履歴/OnlyScan/Credit/RadiusRep、watch/only/cycleEnd/可用性/左右一致から、(dispatchOnlyMatch s).bind(restart entry delay)の成功とscan半径+1/Idle/回数/clock/空program/heap保存/grow等を一括証明。OnlyRestartReadyと距離下界は内部導出（origin watched.phase=4使用）。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ20124終了済み。これは二局所遷移の合成であり、Scalaの次tickまでの入力到着や背景・時計スケジュールを飛ばして証明したわけではない。そのinterleave・到達性・他分岐・全controller/無条件PALは未完。

**最新：caught only一致枝に実guard dispatchを追加**：RestartStateへperiodOnlyを追加、dispatchOnlyMatchでwatch/only/lagzero/canRight/cyclepositive/checkPair/左右一致を検査。dispatch_only_matchはOnlyOrigin＋同じOnlyScan/Trace/LeftMovesからlag/cycle/checkPairを内部供給し、有効更新matchedRestartStateを返す。mode watch/only true/可用性/左右一致は実枝の前提。Noneはこの枝の非適用であり言語拒否ではない。canRightのDecidableを定義展開で供給し計算可能性を維持。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ12807終了済み。初回Decidable不足とsimpによる左右書換え不一致は修正済み。全背景tick/再shift/fallback/到達性/無条件PALは未完。

**最新：比較失敗flag→chain Broken→restartを局所接続**：Scala consumeの不一致時mode=Brokenとmatchedの順序を再確認。matchedRestartState（有効なcaught only一致枝の射影）とrestart_after_matchを追加。onlyCompareNextのbrokenからchainModeを計算し、OnlyRestartReadyだけでrestart成功/scan保存/Idle/時計/回数/検索resetへ接続。独立chainMode=broken前提はこの合成では不要。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ3624終了済み。matchedRestartStateは有効枝の更新関数で、旧mode/only/lag/左右一致のdispatchを自身では検査しない。その合法性は既存比較定理から供給する必要がある。背景tickの入力到着/時計順序、全controller/他分岐/無条件PALは未完。

**最新：局所restart遷移を統合**：InputSupplyにChainMode/RestartState（対象フィールドの射影）/restart/restart_readyを追加。chainMode=brokenとOnlyRestartReadyから全guardを通過し、同じscan保存、検索start、chain Idle、restarts+1、clock=delay、program空テープ対応/heap保存/lower=last/grow/work=lowerを一括証明。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ93194終了済み。初回record更新構文とsimp残ゴールは修正済み。これはScala backgroundのrestart対象フィールドのdecoded射影であり、全controller refinementではない。OnlyCompareState.watch.control.brokenと新chainModeの対応、実背景tickへの組込み、次の検索実行、他分岐・到達性・物理refinement/無条件PALは未完。

**最新：終端last Canonicalの独立前提を除去**：history_terminal_canonicalで同じready Watch.Run→ChainShiftRun→Trace→最後consume（失敗含む）のlast正規形を導出。only_compare_restart/only_matched_restart/OnlyRestartReadyの結論にlast Canonicalを追加し、OnlyRestartReady.start_searchのhc引数を削除。scan_prediction_shift経由の生成契約にもそのまま伝播。全体build9121 jobs成功/exit 0、新補題公理propext/Quot.sound、ジョブ94523終了済み。これで前回発見したlower非負の正規形不足は同じ履歴で解消。次は検索startと外側chain Idle/restarts++/clock更新の統合。成功watch/準備の全controller到達性、他分岐、物理refinement/無条件PALは未完。

**最新：OnlyRestartReady→検索startを接続、lower guardの不足を明示**：OnlyRestartReady.start_searchを追加。同じ終端last/radiusをstartSearchへ渡し、lower/radius非負とcenter.read存在、program reset/heap保存/lower/work/grow/debt等を一括証明。last.positiveだけではnegative=falseを言えないため、lastのCanonicalを追加前提として要求。これは残る履歴接続であり、隠してはいけない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ5799終了済み。次はchain_shift_control_canonical＋Restart.run_canonical/consume_canonicalから終端last Canonicalを同じ履歴で導出しOnlyRestartReadyへ含める。外側chain Idle/clock/restarts更新、全controller/PALは未完。

**最新：検索startのprogram/lower/schedulerを統合**：SearchFinishにSearchState(n,slots)（raw program、lower counter、既存scheduler）、startSearch(entry,lower,radius)、startSearch_positiveを追加。RawTick.resetとbeginを同時実行し、正lowerなら空テープ/PC開始/done=trueへの対応、heap保存、lower=work、grow/spanreset/debt=-radius/finalfalse/quarter0を一括証明。全体build9121 jobs成功/exit 0、同定理公理propext/Quot.sound、ジョブ30279終了済み。Counterはdecoded値でphysical alias encodingまでは未証明。次はOnlyRestartReadyからこの更新を適用して外側chain Idle/restarts++/clock resetへ接続。SearchStateは検索startの射影で、既存全controllerとのrefinementはまだない。全PAL未完。

**最新：Scala program.resetの共有heap側操作を追加**：ScaffoldProgram.scala:103のresetを確認し、GalilScaffoldRawTickにreset entry x（heap保存、全private tape roots none/focus6、pc=entry、done=true）、reset_represents、reset_heapを追加。任意旧状態からlist-levelの空private tapes/開始PC/停止状態への対応を証明。全体build9121 jobs成功/exit 0、reset_representsの公理propext/Quot.sound、ジョブ54923終了済み。これはdecoded raw heap機械上のresetで、実circuit field書込みへのrefinementではない。次はSearchFinish.beginとlower aliasを同じ検索restart状態にまとめ、OnlyRestartReadyを入口条件としてchain Idle/clock=matchDelay更新へ接続。Scalaのbackground restartはchain Brokenかつmargin≥0,last>0,lag=0でsearch.start(last)→chain Idle→restarts++→clock reset。全controller/PALは未完。

**最新：準備creditの実更新列から入口収支を供給**：scan_prediction_shiftの入口CanonicalState/balance=4hを直接引数から削除。prepRadiusの正規形、start/done/copy/backのmatched列、copy列長=h、s.lag/s.marginが同じCredits.run(start prepRadius)(prepEvents ...)の終点である等式を受け、run_canonical/prepared_balanceから内部導出するよう更新。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ5456終了済み。等式と準備イベントの実controller対応は依然外側で供給が必要。成功Watch.Run/DP窓/radius対応・実restart/再shift/fallback/全controller/PALは未完。

**最新：比較時margin条件を準備収支から導出**：scan_prediction_shiftのt.margin Canonical/非負の直接引数を、入口sのCanonicalStateとbalance s=4hへ置換。同じRunのrun_canonicalとcaught_margin、およびphaseから導いたdistance下界/lagzeroで比較時margin条件を内部供給。既存prepared_balanceと接続できる署名。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ83582終了済み。準備の実終点がsであることの同一性とbalance供給はまだ外側で必要（準備全体到達性を証明したわけではない）。成功watch/実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：半径下界も比較前phase guardから内部導出**：scan_prediction_shiftのhsize（2h≤radius）を削除し、比較前t.phase=4へ置換。同じwatch_phase_distanceとwatch_progress、初期lag/比較回数/終了lagzeroからdistance=radiusを使ってhsizeを内部導出。返り値のrestart継続契約から追加phase guardも削除し、同じ最後の予測tickの進行収支から必要距離を供給。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ33603終了済み。成功watch/DP窓/初期lagとradius対応/counter正規形/fresh marginなどは依然入口前提。実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：phase4逆方向を証明し距離仮定を置換**：Predictionにconsume_phase_mono/run_phase_mono/before_four_phase/watch_phase_distanceを追加。readyからの同じ成功Watch.Runでphase=4→distance≥4h。4h−1長の成功予測prefixのphase=3、成功列のprefix一意性、phase単調性による矛盾。scan_prediction_shiftのrestart継続契約は独立distance≥4hからimmediate t.phase=4へ変更し、同じhextから下界を内部導出。全体build9121 jobs成功/exit 0・標準公理のみ（最終ジョブ80324終了）。初回失敗はconsume場合分け/bounce展開/appendの正規化を修正済み。下記の「phase4逆方向未完」は旧履歴。成功watchの到達性や半径hsize等の全controller供給、実restart/再shift/fallback/物理refinement/無条件PALは未完。

**最新：予測比較の返り値へrestart接続を統合**：`OnlyRestartReady`（scanとbroken/margin/last/lag/center/radius/Search.begin.work条件、実reset遷移ではない）を定義。scan_prediction_shiftの結論をさらに強化し、生成した同じendpoint/watchEnd/cycleEndからの任意OnlyMatchedRun nと終端一致について、OnlyRestartReadyを返す継続契約を追加。OnlyOriginは内部生成、only_matched_restartへ空履歴/生成入口を直接供給。distance≥4h、終端cycleEnd/canRight/一致は継続契約の条件。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ52740終了済み。予測→shift→一致区間→終端restart入口は一つの条件付き定理に接続済み。未完：実guardからdistance下界、成功watch等の入口到達性、再shift/fallback、reset/idle/clockを含む実restart、全controller/物理refinement/無条件PAL。

**最新：同じ予測shiftからOnlyOriginも構成**：scan_prediction_shiftに実左右不一致hmismatchを追加（Scala shift枝の条件）。結論へOnlyOriginの存在とstart=s/watched=immediate t/shifted=watchEnd/shiftEnd=endpoint/resumeLeft=endpoint.left/interior=xs/steps=xs.length+1/finish=cycleEndを追加。最後の予測tickを含む同じWatch.Run、同じChainShiftRun、実終了scanとcenter位置から構成し、OnlyOriginを別途仮定しなくてよくなった。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ88644終了済み。次はこの返り値をonly_matched_restartへ直接接続。distance≥4hのguard導出、成功watch/DP窓/counter/margin前提の全controller供給、実restart/再shift/fallback/無条件PALは未完。

**最新：予測比較→shift→比較入口まで既存定理を強化**：`scan_prediction_shift`の署名を更新。radius/length counterのCanonical、比較前t.marginのCanonical/非負を追加し、既存PalAt/同じShiftRun/ChainShiftRun/終了counter/OnlyScanに加えOnlyCredit/RadiusRep/空Trace/LeftMoves/center.read存在を返す。追加tickのmargin.incからfresh収支条件を内部供給し、shift_only_entryへ接続。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ96400終了済み。OnlyOrigin構築と同じshift起点でのonly_matched_restart合成はまだ必要。成功Watch.Run/DP窓/半径下界/counter正規形/margin条件の全controllerからの供給、実restart/再shift/fallback/無条件PALも未完。

**最新：終了scan前提をshift生成から供給**：`shift_to_only_initialized`を追加。旧scan/shift後PalAt/caught watch/初期counter正規形/fresh margin非負から、shift_to_onlyで同じShiftRun/ChainShiftRun/終了scanを生成し、shift_only_entryへ渡す。終点のOnlyScan/Credit/RadiusRep/空Trace/0歩LeftMoves/center.read存在を一括返す。終了scan自体は新定理の引数にない。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ19239終了済み。shift後PalAt、caught watch、初期counter/margin条件は未除去。次はscan_prediction_shift由来のPalAt/終端watchとOnlyOriginを同じ起点にそろえて、only_matched_restartまで合成。実restart/再shift/fallback/全controller/無条件PALは未完。

**最新：shift終点から比較入口を一括構成**：`shift_only_entry`を追加。同じShiftRun/ChainShiftRun(reset cycle)から、実終点のOnlyCompareStateにOnlyScan、OnlyCredit、RadiusRep、空Trace、0歩LeftMoves、center.read存在を一括供給。shift初期counter正規形/値/減算範囲、fresh margin非負、終了scanとcaught watch条件は依然要求する。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ23907終了済み。次はshift_to_only等の生成した終了scanをこの入口へ渡し、OnlyOriginとonly_matched_restartを同じ起点で接続。起点到達性/実restart/再shift/fallback/全PAL未完。

**最新：終端checkPairも内部導出**：`only_matched_restart`を追加。OnlyOriginとOnlyMatchedRunから継続比較をcheckedへliftし、同じ終点履歴で終端checkPairも導出、only_compare_restartへ合成。定理の引数に独立checkPairはない。shift回数=interior.length+1、distance≥4h、入口OnlyScan/Credit/RadiusRep/Trace/LeftMoves/center.read存在、終端cycleEnd・canRight・左右一致は要求する。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ35698終了済み。次はOnlyOrigin/入口状態の構成と実restart更新、または残る再shift/fallback枝。全PAL未完。下記の「次は終端checkPair」は完了した履歴。

**最新：各比較のcheckPair仮定を除去**：InputSupplyに固定入口`OnlyOrigin`（同じ成功watch/shift、旧scan不一致、表現/位置/半径下界/再開scan）と`OnlyOrigin.check_pair`、`OnlyMatchedRun`、`only_matched_checked`を追加。OnlyMatchedRunにはcanRight/cycleEnd=false/左右一致だけを要求し、checkPairは要求しない。固定起点からTrace/LeftMoves/OnlyScan等を帰納更新して各stepのcheckPairを導出し、既存OnlyCompareRunへliftする。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ10297終了済み。次は同じ起点で終端checkPairも内部導出してonly_compare_restartへ合成。OnlyOriginの到達性・成功Watch.Run・距離guard・入力到着・再shift/fallback・実restart更新・全controller/PALは未完。OnlyOriginは既存の入口前提をまとめたもので、入口前提自体を証明したわけではない。

**最新：比較区間→終端restart入口**：`only_compare_restart`を追加。同じready Watch.Run/ChainShiftRunと入口Traceから、OnlyCompareRunの任意n回＋終端一致後のscan、broken、margin非負、last正、lagzero、center.read存在、実radiusのRadiusRep/非負、SearchFinish.begin.work=lastを一括導出。center.readは区間入口で仮定し、区間不変から終点へ運ぶ。全体build9121 jobs成功/exit 0・標準公理のみ、ジョブ8097終了済み。実restartのprogram.reset/idle/clock更新そのものは未モデル化。各比較guard、ready成功watch、distance≥4hなどの起点条件も依然前提。次は固定入口からcheckPairを供給するか実restart全更新へ接続する。無条件PAL未完。

**さらに最新（比較区間の帰納）**：InputSupplyに`OnlyCompareState`/`onlyCompareNext`/`OnlyCompareRun`/`only_compare_history`を追加。非終端only一致比較の任意n回について、center不変、同じbaseからの実Trace、LeftMoves、OnlyScan(radius+n)、OnlyCredit、実counterのRadiusRepを一括保存。入口履歴extraから終点履歴長extra.length+nも導出。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ59012終了済み。これはdecoded比較区間の帰納であり、OnlyCompareRunの各stepにcanRight/cycleEnd=false/checkPair同値/左右一致を要求する。固定shift起点の`only_history_check_pair`からstep guardを供給する接続、到着イベント、終端dispatch/実restart、全controllerは未完。次はこの区間関係を既存の起点条件と終端分岐につなぎ、guardを独立前提のまま残さないこと。

**引き継ぎ後の再開追記（この段落を優先）**：`GalilScaffoldChainInputSupply.only_terminal_radius`を追加。終端一致で同じscan半径+1、broken、margin非負に加え、実counter.incのRadiusRepとnegative=falseを合成した。全体`lake build`9121 jobs成功・exit 0、同定理の公理はpropext/Classical.choice/Quot.sound。ジョブ84268は終了済み。下の「今回は文書だけ」「終端radius接続が次」は保存時点の履歴となった。次はcenter不変と実restart更新、固定入口の比較区間帰納。全PAL未完。

この節が下記の多数の「最新」「次」より優先。今回は引き継ぎ文書のみ更新し、証明コードは変更していない。

- **達成済みの境界**：Scala準拠のdecodedな局所実行について、予測一致→shift→OnlyScan入口、継続一致のTrace/LeftMoves/OnlyScan/OnlyCredit保存、終端一致でscanが伸びchainがbrokenになる条件を接続。最後の実装は実radius counterを表す`RadiusRep`と、`only_history_matched`のcounter.inc保存。
- **未達の境界**：固定した入口から全比較区間を回す帰納、実restart全更新、全オンラインcontroller、物理実装へのrefinement、出力/締切、無条件PAL定理。`Main.pal_in_peg_of_structured`は依然として具体機械の正しさを要求する条件付き定理。
- **検証記録**：直前作業の全体`lake build`は9121 jobs成功・exit 0、追加定理の公理監査は標準公理のみ。今回そのbuildは再実行していない。今回の`git diff --check`成功、プロセス確認で実行中のLean/buildなし。

### 再開直後の具体的な作業

1. `lean-pal/PalPeg/GalilScaffoldChainInputSupply.lean`の`only_scan_terminal_match`（約2194行）、`only_terminal_restart_conditions`（約2228行）、`RadiusRep`〜`only_history_matched`（約2263–2328行）を読む。
2. 終端一致にも同じ実radiusCounterのincと`RadiusRep(radius+1)`を接続し、`radius_rep_nonnegative`からSearch.startのradius guardを得る。`RadiusRep`は現在終端定理より後ろにあるので、定義を前へ移すか後ろに合成定理を置く。
3. 比較区間でcenter不変・read存在を保持する。shift直後のcenter条件は`shift_run_center`/`shift_search_guards`から取得できるが、その後の実状態への保存は別途必要。
4. 固定入口から`only_history_check_pair`と`only_history_matched`を帰納で回し、最後の一致/repeated shift/fallbackを同じcontroller実行へ接続する。独立した成功履歴やguardを新たな仮定として置くだけでは完了扱いにしない。

### 残る重要な前提・落とし穴

- fresh watchの成功Run、初期lag/radius/DP窓と実centerの対応を全controllerから供給する必要がある。
- `distance ≥ 4h → phase4`はあるが、実guardから必要な下界を得る逆方向は未接続。
- fresh非負marginからの`OnlyCredit`初期化はある。only=trueで再shiftする場合の一般化は未完。
- `SearchFinish.begin`はスケジューラ射影のみ。program.reset、lower alias、chain idle、clock resetを含む完全なSearch.startではない。
- Scalaは左右一致を先に判定する。cycleEndで左≠予測でも左右一致ならscanは伸び、chainだけbrokenになって次tick restartへ進む。
- encoded位置0のgapと、物理headのfocusなし/readなしを混同しない。sentinelには`signedRead`を使う。
- replayはradiusを0へ戻すので、全状態でradius正と仮定しない。時計のLean側delay2048とScalaの時間校正も全体接続が残る。

### 参照と検証の最短経路

- 主作業：`GalilScaffoldChainInputSupply.lean`。補助：`GalilScaffoldChainPrediction.lean`、`GalilScaffoldCounter.lean`、`GalilScaffoldSearchFinish.lean`。
- 仕様の根拠：`scala/pal/src/main/scala/pal/ScaffoldGalil.scala`と`ScaffoldChain.scala`（対応Circuit版も参照）。
- `cd /home/mizushima/repo/lean4-peg/lean-pal`で`lake build`。Leanジョブは同時に1本。依存更新に`lake env lean`だけを使ってもoleanは更新されない。
- repo直下で`git diff --check`。多数のuntracked Leanファイルと既存削除を含むため、worktree全体をそのまま引き継ぐ。commit済みファイルだけでは再開できない。
- サブエージェント不使用。部品数で進捗を表さず、実際に除去した仮定・接続した実行区間を報告する。

## 従来の基本方針

- **最終目標は無条件の `PAL ∈ PEG`。まだ未完成。** DP単体や局所接続の完成を大定理の完成と報告しない。
- repo: `/home/mizushima/repo/lean4-peg`。Lean作業ディレクトリ: `lean-pal/`。
- 現在の構成の根拠は **Scalaの実装**。新しい別算法や旧4スロット方式を勝手に主経路にしない。
- ユーザーはサブエージェント禁止、速度と実質的な接続を重視。既存部品の置換・整理は許可されているが、無関係な作業を壊さない。
- 非常に大きいdirty worktreeで、多数の重要ファイルがuntracked。`git reset --hard`、`git clean`、一括checkoutをしない。今回commitはしていない。
- ローカルの現物が正。古い`PROGRESS.md`や`docs/palindromes-in-peg/HANDOFF.md`本文は歴史資料。現状は本書と`lean-pal/ASSEMBLY_PLAN.md`冒頭を優先する。
- 記憶ツールはユーザーが削除済み。再導入や探索は不要。

## 現在地の要約（今回の保存時にソース照合済み・ここを優先）

**最新：実radius counterを一致履歴へ接続。** InputSupplyに `RadiusRep`（counter Canonical/value=自然数半径）、`radius_rep_inc`、`radius_rep_nonnegative`、`shift_radius_rep` を追加。shift_radius_repは同じShiftRunと初期正規形/値/減算範囲から終了RadiusRepを構成。`only_history_matched`へ実radiusCounter/RadiusRepを引数追加し、同じ比較でincしたcounterのRadiusRep(radius+1)も履歴/OnlyScan/OnlyCreditと一緒に返すよう更新。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

次は最後の比較（chainがbrokenになるがscanは伸びる枝）にもradius.incを同じ形で付け、実Search.startへ半径非負を供給する。centerは継続比較で不変であることを外側状態に保持する必要がある。現モデルはradius counterの対応を持つが、全controllerのmode/時計/初期化を証明してはいない。全PALは未完。

**最新：同じshift終点のcenter/半径入口条件。** InputSupplyに `shift_run_center`（入口center表現/focusから終了centerのRepresents/focus/position開始+n）、`shift_search_guards` を追加。後者は同じShiftRun、初期ShiftCanonical、n≤初期radius値から、終了center.read≠noneと終了radius.negative=falseを同時に導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回の帰納ケースで外側tを参照したchange不一致はshiftTick限定展開で修正。

これはshift直後の条件。restart時はその後の一致比較でradiusを増やし、centerは不変なので、同じ実counterをその区間も追跡する接続が残る。現OnlyScanは自然数radiusを持つが外側の実radius counterをフィールドに保持していない。program reset/lower alias/idle/clock、全比較帰納/全PALも未完。

**最新：Search.startの検索状態更新と終端lastを接続。** `GalilScaffoldSearchFinish.lean` に `begin lower radius` と `begin_positive` を追加。既存State上でmode=grow/finalStage=false/span=reset/work=(lower zeroならinc、それ以外lower)/debt=initialDebt radius/quarter=0。positive lowerならwork=lower等を証明。`only_terminal_restart_conditions` の結論を拡張し、同じ終端lastをbeginへ渡したworkがそのlastに等しいことも返す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のpositiveからzero=falseのsimp残ゴールはBool場合分けで修正。

Scala確認：Search.startはlower非負だけでなくradius非負・center.read存在を要求。**beginは検索スケジューラ状態の射影であり、program.reset、lower別名参照、chain.mode=Idle、clock reset、上記入口guardの全実行をまだ表していない。** 新たに全restartが閉じたとは扱わない。次は現center/半径counterの到達不変条件とprogram/control側resetを合わせるか、未接続の全比較帰納を進める。全PALは未完。

**最新：only最終一致のrestart条件を同じ終端へ一括合成。** InputSupplyに `history_terminal_last`（同じwatch/shift/Traceの現在machineが実readをconsumeした後のlast正値。read noneも対応）と `only_terminal_restart_conditions` を追加。後者は同じOnlyScan/OnlyCredit/cycleEnd/checkPair/実左右一致から、**終了ScanInvariant、broken=true、margin.negative=false、last.positive=true、lag.zero=true** を同じimmediate currentについて同時に返す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはfresh ready開始watchのdistance≥4hとh回shift、同じ成功継続Traceを前提にしたrestart直前条件。**Search.start(last)、chain idle化、clock resetという実restart操作自体には未接続。** 入口guard・only再shiftの一般化・比較履歴全体の到達帰納、全controller/全PALは未完。次はScalaの実restart更新にこれら条件とscan保存を渡すか、phase4からdistance下界を導いて入口前提を減らす。

**最新：margin収支を履歴延長と終端へ合成。** `only_history_matched` にOnlyCredit前提を追加し、同じ実読出しaによるTrace/LeftMoves/OnlyScanの延長に加え、更新後OnlyCreditも返すよう変更。`only_scan_terminal_match`にもOnlyCreditを受け、従来のscan成功/broken/lagzero/cyclezero/margin+1に加えて、同じimmediate状態のmargin.negative=falseを返すよう更新（両署名変更）。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残るrestart条件は、watch_shift_last_positiveを同じ終端consumeへ合成するlast正値と、実restart呼出し・Search状態更新。OnlyCredit入口はshift_only_creditがfresh非負marginから供給するが、全呼出しのguard由来やonly再shift収支は未完。全PALは未完。

**最新：only区間のmargin＋cycle収支。** InputSupplyに `OnlyCredit`（margin Canonicalかつvalue margin+value cycle≥0）、`chain_shift_margin_canonical`、`shift_only_credit`、`only_credit_step`、`only_credit_terminal` を追加。reset cycleからの同じn回shiftで、入口margin≥0/Canonicalなら終了OnlyCreditを構成。以後immediate（失敗含む）とcycle.decの同時更新で保存。cycleEnd=true/Canonicalから最後のimmediate.margin.negative=falseを導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。固定reset添字への直接帰納とvalueの過剰展開のエラーは一般化補題/限定rewriteで修正済み。

**未合成：** OnlyCreditを現在のonly_history_matchedの履歴と同時に保持し、only_scan_terminal_matchの結果へ組み合わせること。last正値はwatch_shift_last_positiveから同じ終端へ渡す。入口margin非負はfresh guard向けで、only再shiftには別収支が必要。実restart/全controller/全PALは未完。

**最新：同じ成功watch→shift後last正値。** InputSupplyに `watch_last_lower` と `watch_shift_last_positive` を追加。ready開始成功Watch.Runのdistance≥4hから、実成功語の二往復prefixを取り出しlast≥3hを導出。後者は同じwatch終点からh回のChainShiftRunを経た後、任意の追加consume語（失敗含む）のlast.positive=trueを返す。Ordered/Canonical/last>hを独立前提にせず同じTraceから内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**残る条件：** distance≥4hとready開始成功Watch.Runは前提。実phase4 guardから距離下界を導く逆方向、only再shift時の履歴一般化は未完。margin非負の累積収支と最終失敗の同じ実状態への接続、restart/全PALも未完。

**最新：shift後から失敗consumeまでlast正値を保存。** InputSupplyに `chain_shift_order`、`chain_shift_control_canonical`、`chain_shift_future_last` を追加。同じChainShiftRunがlast/boundary/distanceを同じ回数減らすのでOrderedと各Canonicalを保存。入口last値>shift回数なら、任意の追加consume語（最後の失敗も含む）後のlast.positive=trueを既存Restart.run_order/run_canonicalから導出。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**入口のlast>hはまだ前提。** fresh phase4時のlast下界、または同じ二往復prefixから供給する必要がある。再shiftでのonly周期収支も別途必要。margin非負の累積収支、最終失敗との同一履歴合成、restart実行・全PALは未完。

**最新：cycleEnd一致枝の同時更新。** InputSupplyに `only_scan_terminal_match` を追加。OnlyScan、cycleEnd=true、checkPair同値、実左右一致から、radius+1のScanInvariant、watch.immediate後broken=true/lagzero、cycle.dec後zero=true、margin値+1を同時に導出。左≠予測とcycle値1は内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

この枝は成功OnlyScanへ戻さず、scan成功/chain失敗として扱う。**まだrestartに必要なmargin≥0とlast>0を供給していない。** 継続中のmargin増加総数とshift前後のlast/境界更新を同じ履歴へつなぐ必要がある。次tickの実restart、最後の予測一致shift/不一致fallback、全PALは未完。

**最新：最後の比較で外側一致・chain失敗の枝。** Scala ScaffoldGalilの257–304行を再確認：左右一致を最優先しmatchedPlace→chain.matched、そうでなければ予測一致＋canShiftでshift、残りfallback。cycleEndでcheckPairが左≠予測を保証していても、左右が一致する枝はあり得る。この場合、回文は伸びるがchain consumeは失敗する。

InputSupplyに `caught_scan_terminal_match` を追加。CaughtScan、外側right合法、実比較左≠予測、実左右一致から、終了ScanInvariant(radius+1)、合法verifier1-step、終了broken=trueを同時に証明。verifier右readと外側右readの一致は同位置/同入力から内部導出し、予測tokenがnoneでも対応。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**次：** only_history_check_pairとcycleEnd=trueからこの左≠予測を供給し、同時margin.inc/cycle.dec/lag保存と次tickのrestart条件（margin≥0,last>0,lagzero）をつなぐ。最後の比較すべてをshift/fallback扱いにしない。継続全体の帰納・実mode/時計・全PALは未完。

**最新：checkPair/cycle実判定から履歴延長。** `only_history_matched` の署名を変更。独立したhprediction/hremainを削除し、`singlePositive cycle=false` と `only_history_check_pair` が返す比較同値を受ける形へ更新。予測一致はその同値から、extra.length+1<periodはOnlyScanのcycle収支・dispatch同値から内部導出して既存の履歴同時延長へ渡す。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

checkPair同値自体は引数で、直前定理から同じ状態に供給する設計。次はこの二つを旧watch/shiftを固定した継続履歴の帰納へ一括合成し、最後cycleEnd=trueのdispatch・不一致fallbackを扱う。実only/mode/時計と全PALは未完。

**最新：同じ履歴からcheckPairのcycle条件を導出。** InputSupplyに `only_history_check_pair` を追加。同じ成功watch/shift/旧scan不一致/再開scan、現在OnlyScan、v.machine→現在machineのTrace(extra)、再開left→現在leftのLeftMovesから、**cycle.positive=true ∧（次の実左read=現在実token ↔ cycle.singlePositive=false）** を導出。成功extraはTrace.controlと現在unbrokenから、比較済み左移動は既存履歴＋次の合法左一歩から内部供給。cycleEndとの対応はonly_scan_dispatchを使用。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これで前段の「hprediction/hremainを同じ履歴から供給」が可能になったが、全controllerのassert安全性は未完成。次はcycleEnd=falseの実一致比較でonly_history_matchedへ渡し、最後cycleEnd=trueのdispatchと不一致fallbackを同じ実行へ接続する。現在の入口/再開scan/only flag/時計の実到達性、全PALは未完。

**最新：only一致比較の履歴を同時延長。** InputSupplyに `left_moves_append` と `only_history_matched` を追加。OnlyScan(used=extra.length)、同じbase→現在machineのTrace(extra)、初期左head→現在左headのLeftMoves(extra.length)から、一致比較の実読出しaを取得し、Trace(extra++[a])・LeftMoves(extra.length+1)・更新後OnlyScanを同じ一歩で返す。aはGoodから得た実verifier読出しで、任意の予測文字を入力に捏造しない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残るのはhpredictionとhremainをshifted_check_pair/only_scan_dispatchから同じ履歴に対して供給すること。Trace.control/OnlyScan.unbrokenから成功extra前提を導け、LeftMovesへ次の左一歩を追加してcheckPairへ渡せる。入口は空Trace/LeftMovesとscan_prediction_shiftのOnlyScan。実accepted/fallbackの分岐、mode/時計/全PALは未完。

**最新：最後の予測比較→shift→OnlyScanを主定理へ合成。** `scan_prediction_shift` の署名を更新。比較後のradiusCounter/lengthCounterとradiusCounter値=旧R+1を引数に追加。結論は新PalAtに加え、同じ終点のShiftRun・ChainShiftRun（開始watchは **immediate t**、cycleはreset）・remaining.zero・終了radius/length値・OnlyScan(period=2h,used=0)。従来の独立Reads列を返す結論から置き換えた（Readsが必要ならshift_scan_resumeを使う）。repo内の他の参照はなく、全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

最後の予測tickを追加した同じWatch.RunのTraceからverifierのRepresents/focus/brokenfalseを取得し、caught_positionと外側right位置から同位置を内部導出。新PalAtもwatch_shift_palindromeから内部供給。そのままshift_to_onlyへ接続したため、OnlyScan入口のこれらを独立前提として渡す必要はなくなった。

**残る主前提：** ready開始の成功Watch.Run/同じDP窓と候補/旧ScanInvariant/初期lagと半径収支/2h≤R/終了lagzero/最後の予測一致。実centerとして開始verifierを使う配置対応、実guardからこれらの生成、only継続履歴の帰納・最後dispatch・時計/物理回路・全PALは未完。次はOnlyScanの比較履歴を保持し、shifted_check_pair→only_scan_matchedを同じ実行で帰納する。

**最新：合法shift構成→OnlyScanを一括化。** InputSupplyに `shift_to_only` を追加。旧ScanInvariant、新PalAt、h>0/h≤R、外側right合法、比較後radius counter=R+1、catch済みwatch条件から、同じ終点t/v/finishに対するShiftRun・ChainShiftRun・remaining.zero・終了radius値R+1−h/length−2h・OnlyScan(period=2h,used=0)を一括構成。終了ScanInvariantやcycle値を外から仮定し直さず、shift_scan_counters→shift_run_chain→shift_only_scanで内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

残る入口前提は新PalAtとcatch済みwatchの右位置/lagzero/brokenfalse等。これらはscan_prediction_shift/最後の予測tickの既存結論から同一状態で合成する必要がある。さらにaccepted比較履歴の帰納、cycle最後dispatch、実mode/時計/全controller/全PALは未完。

**最新：同じshift終点→OnlyScan入口。** InputSupplyに `shift_only_scan` を追加。beginShiftでresetされたcycleから同じChainShiftRunをn>0回進めた終点t/v/finishについて、t.center/t.leftそのものの終了ScanInvariant、入口verifier表現/右位置/lagzero/brokenfalseから、**OnlyScan(period=2n, used=0)** を構成。cycleの値/Canonicalとshift後verifier条件は既存の同じRunから内部供給。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

終了ScanInvariantはまだ前提だが、任意の別leftではなく同じshift終点t.leftへ固定した。次はshift_scan_countersが返す同じtのScanInvariantとshift_run_chainをこの入口へ一括合成し、accepted比較列の履歴（extra/LeftMoves）を保持してcheckPair→only_scan_matchedの帰納へ進む。mode flag/時計/最後dispatch/全PALは未完。

**最新：一致比較とcycle減算の同じ一歩。** InputSupplyに `OnlyScan`（CaughtScan＋cycle Canonical/value=period−used/used<period）、`only_scan_dispatch`、`only_scan_matched` を追加。dispatchはpositive=trueとsinglePositive=true↔used+1=periodを導出。matchedはused+1<periodの一致比較で、scan半径+1/左右移動/verifier immediateとcycle.dec/used+1を同時に保存する。最後の残り1比較は別dispatch枝で、保存定理の範囲外。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはonlyモード区間のdecoded不変条件で、mode flagや時計/イベント選択そのものは未モデル化。**次：** resetからの同じshift後CaughtScan/cycle=2hをOnlyScan used=0へ接続、shifted_check_pairと同じprefix履歴を保持したaccepted比較列の帰納、最後のdispatch/不一致fallback。hpredictionとhremainはonly_scan_matchedで依然前提。全PALは未完。

**最新：scanとcaught verifierの一致比較不変条件。** InputSupplyに `CaughtScan`（ScanInvariant、同じ入力verifier表現/focus、右headとの同位置、lagzero、brokenfalse）、`caught_scan_matched`、`shift_caught_scan` を追加。前者は左read=予測と実一致比較からGoodを内部導出し、radius+1/left.left/right.right/watch.immediateの同じ更新後にCaughtScanを保存。後者は同じChainShiftRunのverifier/lag/broken保存を使い、与えられた終了ScanInvariantと入口verifier条件からshift後CaughtScanを作る。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**残り：** cycle/onlyはCaughtScanに未包含。caught_scan_matchedの左read=予測をshifted_check_pairから同じ状態で供給し、accepted比較列の帰納へまとめる必要がある。shift_caught_scanのScanInvariantと右headはまだ引数で、実shift終点との同一性は呼出側で結ぶ。時計/入力到着を含む全controller/全PALは未完。

**最新：実一致比較→成功consume。** InputSupplyに `matched_left_prediction` を追加。verifier/outerの同じ入力Represents・focus存在・同位置・外側right合法と、「比較済み左read=実予測token」「比較済み左read=移動後外側right read」から、Watch.Good、実VerifyRunの1-step、broken保存を同時に導出。外側の実read存在から予測token有効性を内部導出するので、Good/予測someを別途仮定しない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

これはshifted_check_pairのk<2h枝と実一致比較から、成功継続を一文字延長するための部品。**未完：** 両定理の同一状態への合成、only継続の各tickで左/右/verifier/lag/cycleを同期する帰納、fallback/最終比較のdispatch、全PAL。新定理のverifierとouter同位置等は依然前提。

**最新：checkPairの現在左座標を実移動から導出。** InputSupplyに `LeftMoves`（各左移動前focus存在）、`left_moves_position`（同じ入力Represents保存とposition終了+n=開始）、`bounded_left_moves`（n≤開始positionから合法列を構成、終点番兵も可）、`left_moves_read` を追加。`shifted_check_pair` の署名を変更し、現在leftのRepresents/座標を直接仮定するのをやめ、shift終了ScanInvariantとそこからextra.length+1回のLeftMovesを受けて内部導出する。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

**未完：** hresumeの実shift終点との同一性、left移動と同じ継続比較の右/verifier消費数・cycleの同期、成功追加語の帰納構成、only/guard全体。LeftMoves単独は同じtickで右も動くcontrollerではない。全PALは未完。旧「現在左head座標を前提」という記述は上記に更新する。

**最新：実左read対実period tokenのcheckPairを合成。** InputSupplyに `shifted_check_pair` を追加。同じ成功Watch.Run/ChainShiftRun、旧ScanInvariant/実左右不一致、ready入口、開始verifier=center、watch終了=c+R+1、2h≤R、成功追加語extra（長さ<2h）、現在左headのRepresentsと座標から、**実左read=実次予測token ↔ extra.length+1<2h** を導出。旧右窓対応はshifted_prediction_windowから内部供給、番兵もrepresented_signed_read経由で対応。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。

この定理はcheckPairの文字比較部分の合成であり、まだcontrollerの無条件assert安全性ではない。**残る前提：** 継続中の現在左head座標を同じ実行から導くこと、extraの成功をaccepted比較の帰納で保つこと、cycle=2h−extra.length/only/watch/lagzeroの同期、開始・終了verifierと外側scanの同一時系列。次はこの比較結果をcycleEnd判定と同期し、一致比較から次の成功consumeを構成する。全PALは未完。

**最新：shift後の各実tokenと旧右窓。** ChainPredictionの `continued_prediction` はcounter調整後の成功追加語から、通算pre.length+extra.lengthのmod添字で実tokenを返す。InputSupplyに `chain_shift_continued_prediction` と `shifted_prediction_window` を追加。後者は同じready開始成功Watch.Run→同じChainShiftRun→成功追加consume語を接続し、extra.length<2hなら、実次token=encoded raw[旧watch終了位置−2h+extra.length+1]を導出。予測窓対応そのものを独立した前提にしていない。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のgetElem?直前改行の構文エラーは修正済み。

**残り：** 成功追加consumeは前提。実only比較が一致ならこの成功を延長できること、左headの各比較座標、cycle値、最後の旧不一致の同じscanへの同期を合成する必要がある。shift長nと周期hの同一性もこの汎用定理自体は要求しない（呼出側で一致させる）。checkPair全体、全online/全PALは未完。

**最新：shift後のconsume成功と実Runを転送。** ChainPredictionに `consume_same_broken` / `run_same_broken`（SamePredictionと開始broken一致から同じ語の終了broken一致）。InputSupplyに `chain_shift_broken` / `chain_shift_future_success` / `chain_shift_supplied_run` を追加。最後は同じChainShiftRun、shift前verifierからの合法Reads、同じ語のshift前controlでの成功から、shift後machineの実VerifyRun.Run・同じ終了verifier・broken=falseを構成する。verifier保存はchain_shift_valuesから内部供給。全体build9121 jobs成功/exit 0、新しい主要定理はpropext/Quot.soundのみ、最終ジョブ終了済み。

**まだ条件付き：** 転送元の追加語の成功と合法Readsは前提。実only継続がその語を読むこと、供給/比較・cycle/checkPairの同一時系列は未証明。予測列を勝手に入力として供給して全online成功と見なさない。次は成功周期prefixから各継続予測を導き、左比較と同じ実右読出しを条件分岐へ接続する。全PALは未完。

**最新：shiftのcounter変更を跨ぐ予測保存。** ChainPredictionに `SamePrediction`（period/forward一致）、`consume_same_prediction`、`run_same_prediction` を追加。同じseen/語に対してperiod/forwardはcounter/phase/brokenの違いによらず同じ（不一致読出しも含む）。InputSupplyに `chain_shift_prediction` と `chain_shift_future_prediction` を追加し、同じChainShiftRun前後のperiod/forward保存、そこから同じ任意の追加consume語後の実予測token一致を導出。全体build9121 jobs成功/exit 0、両主要保存定理はpropext/Quot.soundのみ。初回のconsume内match/if分岐不足は修正、最終ジョブ終了済み。

**残り：** 実only継続で読む語と周期prefixの同一性・成功性、各kのtokenと旧右窓対応への合成、left/cycle/guard同期。SamePrediction自体はbroken保存や成功実行の存在を主張しない。ready開始の成功prefix定理と、shift後状態がそのperiod/forwardを共有することを使って接続する。全online/全PALは未完。

**最新：実period token→旧右窓。** ChainPredictionに `successful_next`（同じ開始状態から二つの成功語の長短を使い、短いrun終了period token=長い語の次文字）と `successful_prediction`（ready開始成功actual終了token=bounce[actual.length mod 2h]）を追加。InputSupplyの `watch_prediction_window` は同じ成功Watch.Run、開始Represents/focus、終了変位n≥2hから、**実終了period token=encoded raw[end−2h+1]** を導出。周期式だけだった前段から実tokenに接続した。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ終了済み。

適用範囲はfresh ready開始の成功watch終点。**shift後はdistance等を変更しているので、同じready開始runとそのまま同一視できない。** 次はperiod/forwardが同じならconsume後のperiod/forward/予測も同じという射影保存を使い、shift後継続各kのtokenへ拡張する。最初のtokenのshift保存はchain_shift_values.periodから供給可能。終了位置と旧scan最後の比較同期、only/cycle/全guard、全PALは未完。

**最新：周期語と同じ実入力の旧右窓を接続。** InputSupplyに `watch_input_cycle` と `watch_previous_window` を追加。前者はready開始の同じ成功Watch.Runから、各実読出しword[start+i+1]がbounce[i mod 2h]に等しいことと終了変位nを導出。後者は終了変位n≥2hで、1≤k≤2hについてbounce[(n+k−1) mod 2h]=word[end−2h+k]を導出する。これが継続比較に渡す旧右窓対応。全体build9121 jobs成功/exit 0、標準公理のみ、ジョブ終了済み。

**残る差：** この段階の「次の予測」は周期語の添字式。実period headが各継続consume前にそのtokenを返すこと（shiftでperiodが保存されること自体は証明済み）を証明する必要がある。watch終了=end=c+R+1を最後のshift比較と同期し、scan_continuation_pairへ合成する部分も残る。成功Watch.Runは依然前提。only/cycle/実guard/全PALは未完。

**最新：実scan不一致→番兵込み継続比較。** InputSupplyに `represented_signed_read`（focus存在不要、Representsだけで実read=signedRead(position)）、`left_signed_read`（実leftのread=signedRead(旧position−1)）、`scan_radius_lt`、`scan_failed_signed`、`scan_continuation_pair` を追加。最後は実ScanInvariant・合法right・実左右不一致から、旧PalAt/R<c/語レベル不一致を内部導出してcontinuation_pair_signedへ合成する。予測と旧右窓の対応、2h≤R、k範囲は依然前提。全体build9121 jobs成功/exit 0、標準公理のみ、最終ジョブ終了済み。初回のsimp条件消去失敗はsimp onlyで修正済み。

この更新で旧記述の「実head.readとsignedReadの対応」「実scanからR<c」「旧不一致の語レベル供給」は接続済み。**残り：shift後の各比較headが指定座標へ来る同一run、予測列と旧右窓の対応、cycle値/only時系列/checkPairの全guard、全online/全PAL。** 次は成功watch周期から予測窓の対応を導出するのが核心。

**最新：番兵を含む継続比較の語レベル定理。** InputSupplyに `signedRead` と `continuation_pair_signed` を追加。重要：encodedの0番はsynthetic gap=2だが、実headの最初の文字から左へ出た番兵はfocusなしでnone。したがってsignedReadは **i≤0をnone**、i>0をword[i.toNat]とする。負だけをnoneにする初案は、この実head対応の違いを確認して修正した。

`continuation_pair_signed` はR<c、2h≤R、旧PalAt、予測と旧右窓の対応、signedReadでの旧不一致から、1≤k≤2hで継続左比較一致↔k<2hを証明する。最後のc−R−1=0という番兵枝も含む。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ、ジョブ終了済み。**まだ実head.readとsignedReadの等式、ScanInvariantからR<cの供給、予測列対応、cycle/only時系列への接続は未完。** 語レベルの番兵対応をcheckPair全体の完成と扱わない。次は実left読出し座標をこの定義へ接続する。全PALは未完。

**最新：only継続の文字比較（鏡映部分）。** InputSupplyに `continuation_pair` を追加。旧PalAt(c,R)、R+1≤c、2h≤R、旧境界word[c−R−1]≠word[c+R+1]、予測k=旧右窓word[c+R+1−2h+k]という対応を前提に、1≤k≤2hでshift後左文字word[c−R−1+2h−k]と予測の一致↔k<2hを証明。内部点は旧回文の鏡映、最後は旧不一致をそのまま使う。全体build9121 jobs成功/exit 0、propext/Quot.soundのみ、終了済み。初回の隣接doc comment構文エラーは修正済み。

**未接続を明記：** 予測列と旧右窓の対応は依然前提で、同じchain周期/継続consumeから導く必要がある。R=cで左がabsent sentinelになる枝はこの定理の対象外。実左head座標とcycle値=2h−k+1を結び、singlePositive判定と合わせる部分、onlyモードの実時系列も未完。checkPair全体や全PALを完成扱いしない。次はこの予測対応を成功watchの周期から供給するか、番兵枝を実Option読出しで補う。

**最新：shift直後のcycleとcycleEnd。** Counterに `singlePositive`（positiveかつpos.tailが空）とCanonical下の `singlePositive_iff`（値=1との同値）を追加。Scala cycleEndのdecoded判定に対応。InputSupplyに `chain_shift_cycle_canonical`、`chain_shift_reset_cycle` を追加し、同じChainShiftRunがreset cycleからh>0回進むと終了cycle値=2h、positive=true、singlePositive=falseを証明。共通Counter依存を含む全体build9121 jobs成功/exit 0、sorryなし、最終ジョブ終了済み。初回の整数算術残ゴールはomegaで修正。

Scala確認：beginShiftはonly=true/cycle.reset、shiftOneはcycle.inc×2、only中matchedはcycle.dec。**cycleEndはshift完了条件ではなく、継続比較の残り1セル判定。** 次の本質はcheckPair（only/watch/lagzero下でcycle>0、左文字とpredictionの一致がcycleEndの否定と同値）の文字列不変条件。算術だけでは証明できていない。mode/output、guardからのWatch.Run成立、全PALも未完。

**最新：chain.shiftOneを同一shift反復へ接続。** InputSupplyに `chainShiftOne`（既存Watch.Stateのcontrol distance/boundary/lastとmarginをdec）、`ChainShiftRun`（既存外側shiftTickとchainShiftOne、cycle.inc×2を同じtickで更新）、`shift_run_chain`、`chain_shift_values` を追加。任意の同じShiftRunと入口watch/cycleから同じ外側終点を持つChainShiftRunを構成できる。n回後のdistance/boundary/last/marginは各−n、cycleは+2n、verifier/period/lagは不変。全体build9121 jobs成功/exit 0、shift_run_chainは公理なし、chain_shift_valuesはpropext/Quot.soundのみ。初回のrecord改行構文エラーは修正済み、最終ジョブ終了済み。

これでshift中のchain私有counter更新のdecoded同期まで対応したが、beginShiftのonly=true/cycle.reset、cycle終了判定、mode=Scan/output、全controller到達性はまだ未接続。shiftRun存在は既存head/scan定理から供給できるが、成功watchと半径条件を実guardから導く課題は残る。全PALは未完。旧「chain.shiftOne同期未完」はこの更新で置き換える。

**最新：shiftの正規形と終了guard。** InputSupplyに `ShiftCanonical`、`shift_tick_canonical`、`shift_run_canonical`、`shift_run_values`、`shift_run_exit` を追加。同じ任意のShiftRunについてremaining/radius/lengthのCanonical保存と値の減少を証明。初期remaining値=nでn回実行した場合、終了zero=trueかつpositive=falseを導出する。これは開始remainingを構文的にofNat nと固定しない終了guardの定理（ただしRunの存在は前提）。全体build9121 jobs成功/exit 0、印字公理は標準公理のみ、終了済み。次は実chain.shiftOne/cycleと同じtickへの合成、または実guardから成功watch等の前提導出。mode=Scan更新・outputおよび全PALは未完。

**さらに最新：外側shift counterを同期。** 同じInputSupplyに `ShiftState`（center/left/remaining/radius/length）、`shiftTick`、`ShiftRun`、`shift_heads_counters`、`shift_scan_counters` を追加。Scala stepShiftのremaining.dec→center.right→left.right×2→radius.dec→length.dec×2をdecoded状態で表す。各tickのremaining正値guardと全head guardを持つh回のRunから、remaining=ofNat 0、radius値がh減少、length値が2h減少を導出。`shift_scan_counters` は比較直後radius値=旧R+1を受け、終了radius値=R+1−h、remaining.zero=true、同じ終了headのScanInvariantを一括で返す。

全体build9121 jobs成功/exit 0、両定理は標準公理のみ、ジョブ終了済み。これは**外側shift状態の射影**。chain.shiftOne（distance/boundary/last/marginのdec、cycleのinc×2）、mode復帰/output、counterの実初期化・Canonicalと実controller到達性はまだ含まない。旧「外側counter同期未完」の記述はこの更新で置き換える。実center配置、成功Watch.Run/半径条件の実guardからの導出、全PALは引き続き未完。次はchain私有counterを同じshiftTickへ接続するか、phase4→半径条件を閉じる。

**保存後の継続による更新：** `GalilScaffoldChainInputSupply.lean` に `ShiftHeads` と `reads_shift_heads` を追加。Scala `ScaffoldGalil.stepShift`（324行付近）のhead更新順に合わせ、各反復で中心right一回→左right二回の全guardを保持した同じh回の遷移を構成する。`shift_scan_resume` と `scan_prediction_shift` の結論にこの遷移を追加済み（署名変更）。独立したReads列しか返さない、という下方の記述は旧状態。

この更新の全体buildは9121 jobs成功/exit 0、`reads_shift_heads` は標準公理のみ。初回buildの不存在補題 `List.length_eq_zero.mp` エラーはリストの場合分けに直して解消。最終buildは終了済み。**同tickのhead射影までであり、radius/remaining/length/counter/chain.shiftOneの同期、実centerと開始verifierの一致、guardからの成功Watch.Run等の導出はまだ未完。** 次はこの関係に実counterとchain状態の更新を接続するか、phase4から半径条件を導出する。大定理は未完。

今回の依頼は進捗保存のみ。証明コードの追加・変更はしていない。以下より後ろの追記は履歴を含み、古い「次は」「未対応」は現在の指示ではない。

### 完了している接続

- `lean-pal/PalPeg/GalilScaffoldChainInputSupply.lean:1260` の `scan_prediction_shift` が最新の合成定理。比較前のScanInvariantとDP候補、成功Watch.Run、lag/半径収支、最後の予測一致から、shift先のPalAtに加え、中心h回・比較後left 2h回の合法Readsと終了ScanInvariantを返す。
- 同ファイルの `shift_scan_resume`（1111行）で移動の終点範囲・表現保存・番兵からの復帰を処理する。`GalilScaffoldChainPrediction.lean` の `watch_period` は同じ成功watchの読出し列に周期2hを与える。
- 初期scan、入力到着、比較一致による半径拡張、DP窓と実入力座標、found→Copy→Back→ready、既知回文半径内の安全な読出しも部品として接続済み。

### 未完の核心と次の作業

1. **別々のReads列をScalaの同一shift実行へ接続する。** 実centerと開始verifierの配置一致を示し、各tickのcenter.right / left.right×2 / radius.dec / chain.shiftOneを同期する。いま証明したのはdecoded headの射影で、全controllerの実行ではない。
2. `scan_prediction_shift` の残る前提を実guardから導く。特に `2h≤R`、予測token有効性、成功Watch.Runの存在、初期lag＋同じmatched数＝半径。phase4とdistanceの関係から半径条件を外せるか調べるのが次の小さい候補。
3. 正lagの内部catch不一致排除、back終了tick直後のlag=0 consume、only=true/cycleによる再shift、restart/fallback/replayを同じ実行へ合成する。
4. 入力到着・実時計・期限・出力認識を閉じ、論理head/FIFOから物理Ref/heap/回路へのrefinementを完成させ、具体的機械を `lean-pal/PalPeg/Main.lean:43` の `pal_in_peg_of_structured` に渡す。**この無条件の最終接続はまだない。**

### 再開時に読む順序と落とし穴

- まず上記InputSupplyの末尾2定理と `shift_scan_resume`。必要な依存だけChainPrediction → ChainWatch/WatchTrace → ChainCredits/Readyへ辿る。
- Scalaは `scala/pal/src/main/scala/pal/ScaffoldGalil.scala` と `ScaffoldChain.scala` で制御順序を確認し、実回路の `ScaffoldCircuitGalil.scala` / `ScaffoldCircuitChain.scala` と対応させる。入力経路はbuildOnline → event buffer → packService → GenerateOnlinePegの生ab入力。
- 比較では不一致判定より先にradiusが増える。shift終了半径は旧Rに対して **R+1−h**。旧中心でPalAt(R+1)やshift途中の各tickのPalAtを仮定しない。
- `acceptedRadius` は受理比較区間の射影。不一致でfallbackする比較のradius.incをfalseとして消してはいけない。replay開始はradius=0なので、開始半径が常に正という仮定も不可。
- Lean側delay=2048とScalaの旧時計較正の整合は残っている。成功列を仮定した時計補題だけで全onlineの期限を証明したことにしない。

### 検証・作業状態

- 直前の検証記録：全体 `lake build` **9121 jobs成功、exit 0**。新しい主要定理の公理監査は標準公理のみ。今回の保存ではソースの署名を照合したが、buildを再実行したとは主張しない。
- 検証コマンド：`lean-pal/` で `lake build`、repoで `git diff --check`。Leanジョブは一度に一つ。`lake env lean` は依存oleanを生成しない。
- この引き継ぎファイル自体を含め多数の重要ファイルがuntracked。削除済み表示の既存ファイルもある。すべて現状を保全し、履歴に戻す操作をしない。commitはしていない。
- サブエージェントは使わない。最終目標までの残りを部品数やテスト数で小さく見せない。再開時は上記1か2を具体的に進め、閉じた前提を報告する。

## 過去のチェックポイント（新しい順・上の要約が優先）

### 再開チェックポイント（2026-09-14・今回の保存）

**最新（予測shift→移動→走査再開）：** `shift_scan_resume` を追加。旧ScanInvariantと新PalAt、0<h≤R、外側right合法から、中心h回/比較後left 2h回の合法Readsを構成し、中心終了表現/focusと終了ScanInvariantを返す。各移動の終点範囲は旧scanから内部導出、sentinel経由も対応。
`scan_prediction_shift`の結論を強化（署名変更）。従来の新PalAtに加え、上記移動列と終了ScanInvariantも同時に返す。比較前scan→最後の予測一致→成功watch拡張→新PalAt→移動→再開まで接続。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
ただしこれはdecoded headの別々のReads列を合成した射影。実centerは開始verifierと同配置であること、同tickでcenter1/left2/radius.dec/chain.shiftOneする順序とcounter/cycle/onlyの同期、2h≤R/予測token有効性/全watch成功性、fallback・期限・物理回路・全PALは未完。

**最新（shift移動guardと番兵復帰）：** `bounded_right_moves`はRepresents/focus存在/position+n<入力長から、n回の合法Reads・終了座標/表現/focusを構成。`left_return_legal`は実leftの直後のrightが合法で元headへ戻ることを保証。
`shifted_left_moves`は比較前head pから、left p（focusなし番兵の場合も含む）を始点としてn+1回の合法Readsを構成し、終了位置=position p+nと表現/focusを返す。shift左2h回にはn=2h−1を渡す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はscan_prediction_shiftの新PalAtとこの移動構成を合わせて、center h回/比較後left 2h回/右head固定の終了ScanInvariantを構成。必要終点範囲を旧scan右端とh≤Rから導く。実同tick順序・counter/only/guardの全controller接続、全PALは未完。

**最新（比較前scan→最後の予測→shift先PalAt）：** `scan_prediction_shift` を追加。比較前ScanInvariant、同じDP窓/Candidate、ready開始成功Watch.Run、初期lag/半径収支、終了lagzero、2h≤R、外側合法右移動後の予測一致から、新中心c+h/半径R+1−hのPalAtを導出。
内部で同位置→Good→末尾true追加Run→count+1/lag保存→watch_shift_palindromeを合成。新右端までの周期/到達距離/短回文は別前提ではない。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は実shiftのcenter+h/left+2h/radius−hをshift_geometryとつなぎ、終了ScanInvariantを構成する。比較直後leftがsentinelに落ちる可能性、実移動guard、phase4から2h≤R、イベント/半径同期、cycle/only再shift・fallback・全PALは未完。

**最新（scanから同位置/最後の予測tick）：** `caught_scan_prediction` を追加。ScanInvariantの右端、同じWatch.Runの開始distance0/lag初期値/終了zero、initialRadius+matched数=現半径から、外側右headとverifierの同位置を内部導出。外側の合法右移動後readとpredictionの一致を渡すとGoodと末尾true追加Runを返す。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はこの追加Runをwatch_shift_palindromeへ一括合成（count追加分=1/lag保存）、その後実shift移動とScanInvariant再開。半径とmatched数の同一イベント対応、予測token有効性、2h≤Rの実guard、全online/全PALは未完。

**最新（最後の予測一致をwatchへ）：** `position_bound`、`canRight_of_bound`、`aligned_prediction_good`、`append_caught_tick` を追加。外側右headとverifierが同じ入力/同位置なら、外側の合法右移動後read=predictionからverifier側のcanRight/成功read、すなわちWatch.Goodを導出。
`append_caught_tick`は終了lagzero/GoodからInternal.idle→Outer.immediateの同じtickを構成し、Runのイベント末尾にtrueを追加。新右端を読む最後のshift予測比較を成功列へ含めるための接続。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はprepared_radius_alignmentからの外側右headとの同位置を実scan状態から導き、この追加tickをwatch_shift_palindromeへ一括合成。cycle/only/beginShiftはWatch射影外なので全shift controller完成と数えない。実guard/全PALは未完。

**最新（同じイベント列のradius counter）：** `acceptedRadius`（true→inc/false→停止）とvalue/Canonical保存を追加。`prepared_radius_alignment`は同じ準備全イベント＋watchイベントで更新したこのcounter値が、終了lagzero時のverifier変位に等しいと証明。開始radiusの自然数値前提も不要（整数valueで直接合成）。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**acceptedRadiusは受理比較区間のcounter射影であり、Scala guardからこのイベント列が生成される証明ではない。** 不一致非shiftの比較はfallbackへ出るので、この列のfalseとしてincを落としてはいけない。次はこの区間の実guard/半径更新対応、最後のshift比較、shift減算・resetとの接続。全PAL未完。

**最新（準備からwatch終点までの収支）：** `prepared_caught_position` を追加。start/copy/done/backの同じCredits.run終了lagをwatch入口に接続し、開始distance0と終了lag値0から、終了verifier位置=開始位置+準備前radius+全準備matched数+watch matched数を証明。start/done各イベントも数えている。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。入口lag=準備run終了lagという同一状態の等式は前提（prepare_pacedが供給するもの）。終端backのready-consume分岐をこの非consume準備モデルへ混ぜない。次は実外側radiusの更新を同じイベント列に同期し、watch_shift_palindromeのhcountへ接続。全online/全PALは未完。

**最新（lagzero→実verifier終点）：** `watch_progress`で同じWatch.Runのdistance+lag増分=bs.count true。`caught_position`は開始distance0/開始lag値=initialRadius/終了lag値0から、終了position=開始position+initialRadius+matched数を導出。
`watch_shift_palindrome`を変更し、旧終了verifier到達前提を削除。代わりに開始lag値・終了lagzero・initialRadius+matched数=旧radius+1を受け取り、到達距離を内部導出する。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの半径/同じmatched数の等式と準備開始lagを実controllerの比較・最後のshift比較に同期する。現定理はそれを前提とし、成功Watch.Run自体/2h≤R/実shift移動/終了ScanInvariant/全PALは未完。

**最新（DP＋同じwatch→shift先PalAt）：** `watch_shift_palindrome` を追加。同じDP窓/Candidate、ready開始成功Watch.Run、verifier開始座標=center、旧PalAt(c,R)、2h≤R、終了verifier位置≥c+R+1からPalAt(c+h,R+1−h)を導出する。短い左回文・全区間周期・右端の入力範囲は内部導出した。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**終了verifier到達条件はまだ前提**。次はdistance+lagの増分=matched数を同じWatch.Runから導き、ready開始distance0/開始lag=開始半径と終了lagzeroから実右端一致へ。外側比較の半径とmatched数（最後のshift比較含む）の同期が必要。2h≤Rの実guard、shift移動/終了ScanInvariant、全PALは未完。

**最新（DP短回文→実入力PalAt）：** `backward_palindrome` と `candidate_short_palindrome` を追加。後者は同じw=Place.stream.take span、実DP Candidateから、letter/gap共通でPalAt(encoded raw,center−h,h)を導く。centerは2L−1/2L。逆向き窓の全添字（先頭0含む）と範囲2h≤centerを内部導出。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はこれをshift_from_rightへ合成し、watch_input_periodの開始位置=centerと終点≥center+R+1を同じ実lagzero/最後の比較から導く。2h≤R、成功watch区間の実時系列、only=true再shift、全online/全PALは未完。

**最新（周期の中心継ぎ目と左鏡映）：** `period_from_right`、`shift_from_right` を追加。旧PalAt(c,R)、2h≤R、短い左PalAt(c−h,h)、右側(c<j,j+2h≤c+R+1)の周期から区間全体の周期2hを導出。中心継ぎ目は短い左回文と旧回文の鏡映、左側は右側周期の鏡映を使用。
`shift_from_right`で0<h/新右端存在を加えてPalAt(c+h,R+1−h)へ合成。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は短い左PalAt(c−h,h)を同じDP Candidateの長さ2h+1回文と窓座標から導く。右側はwatch_input_periodの終了変位がR+1まで届くこと（lagzero/最後の比較）と開始verifier=centerを同期する必要がある。2h≤Rの実guard導出、only=true再shift、全online/全PALは未完。

**最新（watch周期を実入力へ）：** ChainPredictionに `cycles_index`（添字mod往復長）、`cycles_period`、`watch_period` を追加。成功Watch.Runから同じTraceとHasPeriod(actual,2h)を抽出。Wordsを明示import。
ChainInputSupplyに `reads_index` と `watch_input_period` を追加。Readsのi番目=encoded raw[position開始+i+1]を導き、同じwatch終了変位nと、実入力右側でi+2h<nなら周期2hの文字一致を返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。添字加算形のエラーは明示的な等式で修正済み。
次は右側周期を既知PalAtで左側へ反映し、中心近傍の継ぎ目とshift開始の最後の比較を含め、shift_after_predictionの全区間周期へ接続。watch_input_periodは固定raw/成功Watch.Run/ready開始/開始verifier配置を前提とし、lagzeroによる右端一致と全online成功性は未接続。全PAL未完。

**最新（任意長の往復予測）：** ChainPredictionに `cycles`/`cycles_length`/`cycles_run`/`successful_cycles`/`watch_cycles` を追加。round_tripを任意回反復してperiod/方向/brokenを保存。成功列のprefix一意性から、任意有限成功語actualはcycles(bounce,actual.length).take actual.lengthと一致する。
`watch_cycles`は同じWatch.RunからTraceとこの反復prefix等式を一括抽出。二往復以降も対象にした。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの反復prefixから周期2hの添字一致を導き、実入力の右側座標と既知PalAtによる左側への反映を経てshift_after_predictionの区間周期前提を埋める。watch_cyclesは依然「成功Watch.Run/ready開始」の定理で、全online成功性やshift最後の比較との同期は未証明。全PAL未完。

**最新（不一致後のshift先PalAt）：** `shift_after_prediction` を追加。古いPalAt(word,c,R)、0<h≤R、新右端c+R+1の存在、区間[c−R,c+R+1]上の周期2h一致からPalAt(word,c+h,R+1−h)を証明。古い中心でPalAt(R+1)を仮定しない。新中心の左点を古い回文で鏡映し、周期で右点へ渡す。
Scala Chain.canShift/beginShift/shiftOneを再確認。不一致比較でradius.inc済みなので、shift終了半径は旧R+1−h。以前のshift_geometryへ渡すradiusはこの増加後の値。途中microstepごとのPalAtは主張しない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。**重要：区間全体の周期2hは依然前提であり、DP候補・成功watch予測・lagzeroから導出していない。** 次はこの周期前提を同じ実watchの文字列から導き、shift_geometry/終了ScanInvariantへ接続。実guard/半径範囲・fallback・窓・時計・全PALは未完。

**最新（shift幾何とwatch位置）：** Scala Galil 198–252行でshiftのcenter.right/left.right×2/radius.decを確認。`reads_position`で実Readsの長さ=座標変位、`watch_displacement`で同じ成功Watch.Runのverifier変位=distance counter差および入力表現保存を証明。
`shift_geometry`は実centerのh回右移動とleftの2h回右移動（Readsを前提）、h≤radius≤center座標から、終了left=newCenter−(radius−h)、右端newCenter+(radius−h)=旧右端を導出。shift途中の各microstepでPalAtが成立すると仮定しない。移動guard供給とshift先の回文性は別途必要。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次はDP候補/period予測からshift先のPalAt、実shift guardとradius範囲、watch lagと左右位置の同期へ。fallback/窓/時計/期限/物理回路/全PALは未完。

**最新（固定中心の走査不変条件）：** `ScanInvariant raw center radius l r` を追加。左右Represents/focus存在/端点center±radius/PalAtを同時保持。`scan_initial`で同位置radius0、`scan_first`でreset→文字a到着→gap=trueから実right移動の初期化を導出。Scala Input.PlaceHeadの初期gap=trueを現物確認した。
`scan_arrival`は同じ両headへのappendで保存、`scan_matched`は合法rightと実移動後read一致からradius+1の同じ不変条件を返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
これは固定中心の成功走査射影であって全Galil機械ではない。次はshift/fallbackで中心が変わる枝、Search窓/Chain/clock/counterとの同時不変条件へ接続する。最初の文字一つ以外の初期バッファ、失敗・再走査・出力判定・内部catch全域・期限/物理回路/全PALは未完。

**最新（成功比較の移動を合成）：** `right_present`、`left_word`、`comparison_extends` を追加。比較前の同じrawのRepresents/両focus存在/端点center±radius、right.canRight、既知PalAt、実left/right移動後のread一致から、PalAt(radius+1)と両移動後Representsを同時導出する。
半径<center、移動後の端点、右focus存在、左focus存在を内部導出。左focusは右readがsomeであることと一致から導くため、番兵への左移動を成功枝から排除できる。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次はこの成功比較と入力到着保存を同じ到達不変条件へ組み込み、初期化・中心shift/fallback・Search窓と同期する。現在は比較前の端点対応が前提。counter/時計/モード全体、内部catch全域、期限/物理回路/全PALは未完。

**最新（実比較移動の座標）：** `right_position`/`left_position`/`comparison_positions` を追加。実PlaceHead.right（stack/FIFO含む）は座標+1、leftは座標−1。比較前position=center±radiusから、同じ実移動後position=center±(radius+1)を導出する。条件は両head左長正、right.canRight、radius<center。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。次は移動後のRepresents/focus存在を保存してmatched_extendsへ合成。先頭sentinelへ左移動する枝はfocusなしになり得るので、座標更新だけでfocus存在を仮定しない。実center/半径の初期化・shift・窓同期・全PALは未完。

**最新（実read→比較一致→半径拡張）：** `reverse_prefix_read`、`layout_read_coordinate`、`position`、`represented_read`、`matched_extends` を追加。両gapの実head.readを同じencoded raw[position]へ接続。matched_extendsは同じrawを表す左右headのread一致からPalAt(radius+1)を導く。右端範囲はRepresentsから内部導出する。
残る前提は左端非underflow（radius+1≤center）と移動後の左右position=center±(radius+1)。実left/right更新からこの座標を導くのが次。Scala Galil 130–205行を再確認：比較ではright.right→left.left→radius.inc/advanceMatch→read→matchedの順なので、PalAt拡張は成功枝のみ。不一致後にも無条件にPalAtを置かない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。移動・中心shift・窓同期・時計・内部catch全域・全PALは未完。

**最新（入力到着のPalAt保存）：** `palAt_append`、`encoded_arrival`、`palindrome_arrival` を追加。encoded(raw++[a])=encoded(raw)++[letter a,2]なので、以前の末尾gapを含む既知PalAtが保存される。同じInputTrace.append後のReachと、同じhead左長/gap座標におけるPalAtを同時に返す。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
これは入力到着分岐の保存のみ。PalAtの初期化・比較一致による半径拡張・中心移動/shift・Search窓との同期はまだ実Galilの到達不変条件として閉じていない。次は実左右headの読出し座標と比較更新への接続。全PAL未完。

**最新（letter/gap共通化）：** `reachable_mirrored_safe`、`window_mirrored_safe`、`found_window_safe` をgap:Bool引数で一般化した（既存署名変更）。座標はgapなら2L、letterなら2L−1。右供給を場合分けしてPalAtの右端から必要量を導出し、左配置もそれぞれの既存補題から内部導出する。
同じfound→Copy→Back→ready.period→任意n≤radius,4hの安全Runが両中心を扱う。gap版の別経路を追加せず共通定理に統合。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は実Galil到達状態からPalAt/center/radiusとSearch窓一致を導くこと、およびwatchのlag/比較時計・中断の実時系列への同期。focusなし番兵、n>4hの内部catch、shift/restart/期限/物理回路/全PALは未完。gap未対応という下方の記述は旧状態。

**最新（gap左配置）：** `encoded_take`、`gap_left_window_reads`、`candidate_gap_window_layout` を追加。gap座標2Lに対する左stream.drop1の読出しは、同じ拡張入力のleftReadsに一致する。n≤2*xs.length+1およびn≤span−1はDP Candidateとn≤4hから内部導出。全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。
次は既存reachable_gap_supplyとこの配置を合成し、gap/letterを共通安全性定理へ整理してfound_window_safeを両中心へ拡張する。PalAtと窓の実時系列不変条件、内部catch全域、時計・物理回路・全PALは未完。

**最新（gap開始の右供給）：** `rightReads_tail` と `reachable_gap_supply` を追加。letter開始のn+1回Readsから最初のgap読出しを除き、同じHead/gap=trueから正確にn回の合法Reads、座標2*head.left.lengthのrightReads一致、終了Represents保存を導く。条件はReach/focus存在/n≤2*unread.length。末尾gapでn=0も含む。
全体build成功9121 jobs/exit 0、標準公理のみ、ジョブ終了済み。次はgap開始の左stream配置と鏡映安全性へ接続し、letter/gapの共通定理へ整理。gap版のfound安全性、実PalAt/時計/内部catch全域/全PALは未完。先頭focusなしの番兵は対象外。

**最新（found→copy/back→安全Runを合成）：** ChainInputSupplyに `window_mirrored_safe`、`copied_window_head`、`found_window_safe` を追加。window_mirrored_safeは同じlayout/Reachとw=stream.take spanから左右座標を内部導出。copied_window_headはCandidateと実read/copy列からh=xs.length+1および予測head形を導出する。
`found_window_safe` は同じSafeQuanta/found/DP Resultからfound_start_backを使い、同じh・文字列・periodに対するCopyとBack（終点がConsume.ready.period）を保持し、そのreadyから任意n≤radiusかつn≤4hの実verifier Run/broken=false/入力表現保存を返す。右Reads・左右配置・予測head形を外から仮定し直していない。
全体build成功9121 jobs/exit 0、標準公理のみ、終了済み。なお入力Reach、w=同じ左stream.take(span+1)、PalAtは依然前提で、これらとSearch/Chainの実時系列の同期を証明したわけではない。Copy/Backはdecoded無中断射影で、credits/outer matched/clockとの合成も残る。次は実Galilのcenter/radius/左窓の到達不変条件、gap開始と内部catch全域。全PAL未完。

**最新（左窓座標）：** ChainInputSupplyに `pairs_append`/`encoded_reverse`、`leftReads_prefix`、`pairs_gaps`、`left_window`、`left_window_reads`、`candidate_window_layout` を追加。raw=(a::xs).reverse++suffixのletter座標で、拡張入力のprefix反転=Place.stream++[2]。左streamが先頭番兵gapを含まない差を明示した。
`candidate_window_layout` はw=stream.take spanとCandidate/n≤4hから、既存mirrored_candidate_safeの左配置等式を導出。範囲n≤2*xs.lengthとn≤span−1はCandidateの長さ条件から内部導出する。新規定理は標準公理のみ、全体build成功9121 jobs/exit 0、ジョブ終了済み。
次は同じInputTrace.layout/Reachの分解とこの左窓定理を `reachable_mirrored_safe` に一括合成し、実Searchの窓コピー結果に接続。その後実Galilのcenter/radius/PalAt不変条件。左窓定理自体はw=stream.take spanを依然前提とし、全online到達性を証明したものではない。gap開始/内部catch全域/全PALは未完。

**さらに最新：** `reachable_mirrored_safe` を追加し、Reachからの実右読出しを鏡映安全性へ直接合成した。`reads_present` から最後のgap読出しを追加し、`reachable_coordinate_supply` の供給長を `2*unread.length+1` へ拡張。新しい安全性定理では供給長をPalAtの右端条件から内部導出するため、右配置・Reads・独立した供給長の前提は不要。結論は同じverifierのn回Run、broken=false、終了入力表現保存。
全体build成功（9121 jobs、exit 0）、標準公理のみ、終了済み。残る条件はletter開始/focus存在、左DP配置、PalAt、n≤radiusかつn≤4h、DP候補/head形。次は左stream配置と実到達PalAt。末尾gapは対応済み（下記の未対応記述は旧状態）、gap開始は未対応。全online/全PALは未完。

**保存後の自動継続で更新：** ChainInputSupplyに `encoded`、`pairs_length`、`pairs_drop`、`encoded_suffix`、`rightReads_suffix`、`encoded_rightReads`、`represented_position`、`reachable_coordinate_supply` を追加。以下の着手案1とletter位置の右座標接続は実装済みになった。
`reachable_coordinate_supply` は同じrawのReach/focus存在/供給長条件から、合法Reads・正確にn文字・その列のmap someが同じencoded rawのrightReadsと一致・終了Represents保存を返す。Lの正性と入力長以下はRepresentsから内部導出。全体build再実行成功（9121 jobs、exit 0）、標準公理のみ。ジョブ終了済み。
次はこれをmirrored_candidate_safeへ直接合成し、左DP stream配置およびPalAtの実到達不変条件を導く。gap開始/末尾gapは未対応。大定理は未完。以下の「今回コード変更なし」は保存依頼時点の記録で、この追記がそれ以後の現在地。

**この節が現在地。以下の「最新追記」は新しい順の履歴で、下方の旧「次に実装するもの」や旧build件数は現在の指示ではない。**

- 最後に完了したコードは `GalilScaffoldChainInputSupply.lean`。現物を今回再確認した。直前セッションの検証記録は全体 `lake build` 9121 jobs / exit 0、印字公理は標準公理のみ。今回の保存では証明コードを変更せず、全体buildは再実行していない。
- 到達点：DP候補の二回文条件から二往復予測語を導出し、既知 `PalAt` と左右配置等式があれば実verifierの安全なRunへ渡せる。さらに、論理入力の `Reach` から右stack/FIFOを跨ぐ実読出し列を構成済み。
- **まだ無条件のPAL定理には接続していない。** `mirrored_candidate_safe` の左右配置・既知回文半径は依然前提。成功Watch.Runの時計・収支定理も、その成功区間が実online実行で成立することまでは示していない。
- 中断直前は次の座標接続を検討し、関連ソースを読んだだけ。未保存の実装や実行待ちのLeanジョブは引き継いでいない。

#### 次の着手箇所（提案、まだ未実装）

まず `GalilScaffoldChainInputSupply.lean`、`GalilScaffoldChainMirror.lean`、`GalilScaffoldChainVerifyRun.lean` の `pairs`、`GalilScaffoldInputTrace.lean` を読む。

1. 生入力 `raw : List (Fin 2)` の拡張語を `pairs raw ++ [2]` とする座標補題を作る。`pairs` は各文字を **gap=2, letter** に展開する。`pairs_append`、長さ `2 * raw.length`、`drop (2*n)` と生入力の `drop n` の対応が候補。
2. focusが存在するletter位置では `L = head.left.length ≥ 1`、拡張語上の現在位置は `2*L-1`。その右読出しは `pairs (raw.drop L)`。この対応から `ChainMirror.rightReads` への配置等式を導く。`n` 回を主張するには `n ≤ 2*(raw.drop L).length` 等の供給長条件が必要。`take n` だけでは不足時に短くなる。
3. 現供給定理はletter開始限定で最終gapを含めない。gap開始と末尾gap、左DP streamの座標を別途接続する。resetのfocusなしを先頭gapと同一視しない。
4. 同じ実Galil到達状態からcenter/radius/PalAtを導き、内部catchと早期不一致の排除へ進む。座標補題の追加だけをその不変条件の完成と報告しない。

#### 大定理まで残る接続

- 上記配置と回文不変条件、特に `n > 4h` の内部catchも含む安全性。
- back最終tickでwatchへ移行した直後のouter matched/lag=0 consume、失敗後のSearch.start、shift/only=true、fallback・pauseの同一実行への合成。
- 実時計とmatched/availableの対応、成功区間の存在、正例の期限。Lean側delay=2048とScala側の旧時計較正の整合。
- 論理head/list/FIFOから物理Ref/heap/回路・初期化へのrefinement、および具体的機械を `Main.pal_in_peg_of_structured` に渡す全認識証明。

再検証は `cd /home/mizushima/repo/lean4-peg/lean-pal` で `lake build`。一度に一ジョブ、終了を確認して次へ。`lake env lean` は依存oleanを生成しないので依存更新にはbuildが必要。repoで `git diff --check`。多数のuntrackedファイルも引き継ぎ本体なので削除しない。

### 最新追記：reachable inputからstack/FIFOを跨ぐprefix読出し

新規`GalilScaffoldChainInputSupply.lean`（root import済み）。mixed_supplyは右stack→incoming FIFOを跨いでpairs(rs++qs)を読む。
represented_supplyはInputTrace.Representsとfocus存在から、同じ到着済みwordのdrop(head.left.length)をgap/letter化した実Readsを構成。保存領域の分割を外から仮定し直さない。
right_word/reads_wordは同じwordのRepresents保存。reads_split_atで有限prefixへ分割し、reachable_prefix_supplyはInputTrace.Reachから配置前提を導出して、そのprefix Readsと終了word表現を返す。
全体build成功（9121 jobs、exit 0）、標準公理のみ、build終了済み。letter位置(gap=false)/focus存在が条件。prefix takeは不足入力では短くなるのでn回完走と誤認しない。
次はこのpairs(word.drop position)をChainMirror.rightReadsのFin3拡張入力添字へ対応させ、gap開始・左DP streamも同じ座標に接続。PalAt/center/radiusの実Galil到達不変条件・内部catch全域・時計/restart/shift/期限/物理回路/全PALは未完。

### 最新追記：既知回文半径の左右読出しから実verifier安全性へ

ChainVerifier.headRightを既存InputTrace.moveRightのabbrevへ統一（重複定義を除去、既存依存build検証済み）。
新規`GalilScaffoldChainMirror.lean`（root import済み）。leftReads/rightReadsは同じFin3入力wordのcenter±(i+1)をOptionで読む。既存Manacher.PalAtからmirror_readsで半径内の列一致を導く。
mirrored_candidate_safeはn≤既知radiusかつn≤4h、DP Candidate/head prefix、左DP窓・右実Readsが同じword/centerを表す二つの配置等式から、同じverifierのn回Runと終了brokenfalseを構成する。candidate_prefix_safeを実右読出しへ渡した。
全体build成功（9120 jobs、exit 0）、標準公理のみ、build終了済み。
まだ左右の配置等式/PalAt/合法Readsは前提。これらをInputTrace.Representsと実center/left/right/radiusの到達不変条件から導くことが次。n>4hの内部catch、既知半径境界の早期不一致、restart/shift/clock/期限/物理回路/全PALは未完。

### 最新追記：DP回文候補と二往復予測列の文字列一致

新規`GalilScaffoldChainPalindrome.lean`（root import済み）。palindrome_split/palindrome_prefixは奇数長回文を前半+中心+反転前半へ分解。
candidate_wordはCandidate w lower h（h=xs.length+1）とtake(h+1)w=center::(xs++[b])から、take(4h+1)w=center::(bounce++bounce)を証明。長さ2h+1と4h+1の**両方の実DP回文条件**を使用。
candidate_prefix_safeはその既知語のdrop1から任意n≤4hをconsumeするとbrokenfalseを保証。早期不一致排除に必要な予測文字列一致まで到達。
全体build成功（9119 jobs、exit 0）、標準公理のみ、build終了済み。
まだこれはDPの左向き入力窓の語。実verifierの右向き既知履歴が同じprefixになる対応（center周辺で既に一致した範囲/lag）を導く必要がある。未来の任意入力が一致するとは主張しない。次はこの対応を同じReads/consumeへ接続し、内部catch/4h以前の不一致を排除する。全online/期限/物理回路/全PALは未完。

### 最新追記：同じwatch prefixから実verifier不一致のrestart条件を導出

ChainRestart.watch_last_positiveはready入口の同じ成功Watch.Runで距離≥2hなら、成功prefix一意性から一往復を内部導出して終了last.positive=trueを保証。
failed_after_watchは同じWatch.Run/Canonical/ready/balance4h、終了lagzeroと距離≥4h−1からmargin≥−1を導出。実verifier.canRightと同じright後readの不一致にouterMatched(true)を適用し、Right実行・broken・margin非negative/last positive/lagzeroを同じ結果に保証。
旧failed_outer_restartの独立した一往復・margin条件と独立seenを、同じwatchと移動後readへ接続した。
全体build成功（9118 jobs、exit 0）、標準公理のみ、build終了済み。
距離≥4h−1より早い不一致と内部catch中の不一致が到達しない証明はまだ必要。予測token有効性とcanRightも実配置からの導出待ち。次tick Search.start(chain.last)への接続、実clock/shift/only=true、正例期限、物理回路、全PALは未完。

### 最新追記：outer consume失敗からrestart assertionへ

新規`GalilScaffoldChainRestart.lean`（root import済み）。Orderedはlast≤boundary≤distance。consume_order/run_orderで順序とlast単調、consume_canonical/run_canonicalで3counterのCanonicalを保存（不一致含む）。
last_positive_after_bounceは最初の往復後last=h>0が任意suffix（失敗含む）でも保持されると証明。
failed_outer_restartは一往復後のcontrol、lagzero、margin Canonical/value≥−1、予測との不一致seenからouterMatched(true)後broken=true/margin非negative/last positive/lagzeroを同じ結果について導く。失敗時にもmargin.incが先行することを使用。
全体build成功（9118 jobs、exit 0）、標準公理のみ、build終了済み。
まだseenは右移動後のverifierへ接続する必要がある。実到達状態で一往復済み・margin≥−1を導く証明、内部catch中の不一致排除、次tick Search.startへの実状態接続、時計/中断/only=trueは未完。全PAL/期限/物理回路も未完。

### 最新追記：初期margin非負の制約を除去

ChainPrediction.margin_exactで同じWatch.Runの終了margin=開始margin+matched数を証明。
clock_shiftのhm前提を`0≤開始margin+bs.count true`へ一般化（旧開始margin非負から変更）。clock_shift_supplyは開始margin≥−deficit、matched数=同じ時計のcompare数、available数≥2048*deficitからこの条件を内部導出。
clock_shift_readyはreadyのdistance0/balance4h/lag非負からmargin≥−4hを導き、available数≥8192hと区間長≥2k+2（lag≤k）でfreshShiftGuardへ接続。初期marginの前提は不要になった。
全体build成功（9117 jobs、exit 0）、標準公理のみ、build終了済み。
供給条件は保守的な十分条件で、実onlineの完走や期限をまだ保証していない。成功Watch.Runの継続、matched=compare（中断/shift/失敗なし）の実対応、入力供給と初期配置は残る。次は失敗出口/restartのassertionと、実イベントから成功区間または中断を構成する。shift実行/only=true・物理回路・全PALは未完。

### 最新追記：成功prefixを自動導出し時計→shiftを同じRunで合成

新規`GalilScaffoldChainPrediction.lean`（root import済み）。successful_prefixは同じ制御から成功した二列の共通prefix一意性。watch_phaseはWatch.Run/ready入口/距離≥4hから抽出列の二往復prefixを内部導出しphase4/unbrokenを返す。prefix文字列の外部仮定を除去。
margin_monoは同じ成功Watch.Runでmargin単調。clock_shiftはready入口、balance4h、初期margin非負/lag非負≤k、delay2048の同じavailable/compare対応、2k+2以上の成功有効tickからfreshShiftGuard=trueを導出。lagzero/距離≥4h/phase4はすべて内部導出。
全体build成功（9117 jobs、exit 0）、標準公理のみ、build終了済み。
残件は成功Watch.Runの実online到達と継続、初期margin非負（準備直後には負もあり得る）、実matched/clock対応、不一致restart・shift動作/only=true、正例期限、物理回路、全PAL。今回のclock_shiftを無条件の全online認識定理とは扱わない。次は失敗/負marginの枝と準備→watch到達条件へ進む。

### 最新追記：同じwatchのconsume列とphase/shiftを接続

新規`GalilScaffoldChainWatchTrace.lean`（root import済み）。Traceは同じverifier.Reads、終了control=Sweep.run、distance増分=列長、broken保存をまとめる。
internal_trace/outer_trace→tick_trace→run_traceで同じWatch.Runから実consume文字列を抽出。internal→outer順を保持、一tick最大2文字、全長≤2*tick数。
four_prefixはその列が二往復++suffixなら同じ終了controlのphase4/距離≥4h/unbrokenを導出。shift_from_traceはそれを同じWatch.Runのlag/margin収支へ渡してfreshShiftGuardを保証。
全体build成功（9116 jobs、exit 0）、標準公理のみ、build終了済み。
残る重要前提：抽出した成功列の先頭が二往復になること（現在はprefix Traceとして入力）、終了lagzero、準備balance=4h/ready配置。次は成功予測の決定性からprefixを自動導出し、clock_catchesと同じRunで合成する。実時計対応/失敗restart/期限/物理回路/全PALは未完。

### 最新追記：watch lag解消を比較時計のtick上界へ接続

新規`GalilScaffoldChainLag.lean`（root import済み、MatchClockを直接import）。tick_lagは同じWatch.Tickに対して非負保存とlag≤max(0,旧lag−非matched指示値)。matched tickもlagを増やさない。
run_lagは全Watch.Runでlag≤max(0,初期lag−count false)。catchesは非matched tick数≥初期lagからzeroを導出。
clock_catchesはdelay2048/任意初期clock位相、同長available列、matched数≤その時計のcompare数から、初期lag≤kかつ2k+2≤区間長なら終了lagzeroを証明。availableは任意で、compare数上界に時計不変式を使用。
全体build成功（9115 jobs、exit 0）、標準公理のみ、build終了済み。途中のimport/Bool count補題エラーは修正済み。
**連続して有効な成功watch区間の条件付き上界。** 実onlineでそのRunが存在・継続することとmatchedが同じcompareの部分集合である対応はまだ前提。中断/失敗restart、正例期限全体、物理回路、全PALは未完。次は同じWatch.Runのconsume列/phase4へ持上げ、時計対応と失敗時出口を統合する。

### 最新追記：内部catchと外側matchedの同tick収支

新規`GalilScaffoldChainWatch.lean`（root import済み）。Stateは実Verifier.Stateとlag/margin。Goodは同じverifier.canRight・右移動後readと予測token一致。
Internalはpositive lagなら成功consume+lag.dec、それ以外はidle。Outerはmatchedなしidle、lag非zeroならlag/margin.inc、lagzeroなら即時成功consume+margin.inc。TickはInternal→Outerなので一tick二consumeも表現。
run_balanceはdistance+lag−marginの厳密保存。prepared_balanceで準備収支とdistance0からその値=4hを導く。run_canonicalは同じlag/marginのCanonical保存。
shift_readyは同じRunに対し、終了lagzero/distance≥4h/phase4/unbrokenからmargin非negativeを内部導出しfreshShiftGuardへ接続。外側matchedなしという旧Catchの制限をこの成功watch射影では外した。
全体build成功（9114 jobs、exit 0）、標準公理のみ、build終了済み。
これはfresh watch/only=false・成功列で、失敗時restart/shift/fallbackやwatchの有効化・時計生成は未統合。Goodが実入力から成立すること、phase4/距離条件を同じWatch.Runへ持ち上げること、lagが期限内にzeroになる供給上界が次。実物理回路/全PALは未完。

### 最新追記：準備収支からcatch後のmargin/shift条件を導出

ChainCatch.canonical_natはCanonical counterでvalue=nなら実stack表現がofNat nと一致。prepared_marginは同じCredits.runの準備終了margin=lag−4*copy列長。
prepared_shift_guardはlag=4hの準備終了counterからmargin0を導き、別の仮想lagではなくfinal.lagでCatchを構成。
さらにphase4_consume/phase4_runでphase4保存、prepared_shift_afterでlag=4h+suffix.lengthへ一般化。二往復予測列++成功suffixの同じReads/Runから全lagを消費し、margin=suffix.length≥0を準備収支から導出、freshShiftGuard=trueへ接続。
全体build成功（9113 jobs、exit 0）、標準公理のみ、build終了済み。
残る前提：準備counter finalのrun一致、copy長h、実Reads、suffixも含む終了brokenfalse、全読出し長=初期lag。これらの実online供給・clockとouter matchedを伴う到達証明は未接続。Catchは外側比較なしの有効watch列、freshShiftGuardはwatch/only=false射影。次はouter matchedとのinterleavingと準備→watch実到達、失敗時restart条件。全PAL/期限/物理回路は未完。

### 最新追記：同じverifier成功実行のlag catch-upとfresh shift条件

新規`GalilScaffoldChainCatch.lean`（root import済み）。broken_preserved/run_unbrokenで終了brokenfalseから途中のbrokenfalseを導く。
Catchはwatchのpositive lag guard、verifier canRight、consume成功の前後brokenfalse、実lag.decを各tickで要求。catch_runは同じVerifyRun.Run n/終了brokenfalseから、lag=ofNat(n+k)→ofNat kのCatchを構成。
four_boundariesは同じ二往復Readsに適用し4h回Catch→phase4/境界4h/last3h/残lag k。caught_shift_guardはk=0、Canonical非負marginからfreshShiftGuard=trueを導く。
freshShiftGuardは**watch継続・only=falseの射影**で、brokenfalse/lagzero/phase4/margin非negative。全Scala mode/only/shift/replay条件を実controllerから導いたわけではない。
Catchは外側matched/shift/fallbackを挟まない有効watch tick列。初期lag=4hやmargin非負を実準備終了から得ること、途中外側matchedの扱い、時計供給は未接続。marginはこの区間で不変なので、次は準備収支margin=lag−4hとこのcatchを同じ状態へ接続する。
全体build成功（9113 jobs、exit 0）、標準公理のみ、build終了済み。正例期限/全PAL/物理回路は未完。

### 最新追記：同じverifier実行のphase4と格納内容からの供給

新規`GalilScaffoldChainVerifyRun.lean`（root import済み）。ReadsはcanRightと同じright後readを各stepで保証、Runは実Verifier.consumeを反復。realizeはReadsを同じ終了verifier/制御Sweep.runへ持ち上げる。
four_boundariesは二往復列のReadsから4h回の同じRun、終了verifier、period復元/距離境界4h/last3h/phase4を構成。
pairsは二進文字列をgap,letter列へ変換。stack_supply/queue_supplyは具体的右stack/FIFOのprefixからそのReadsを構成し未使用suffixを保持、個々のread一致とcanRightを格納内容から導出。現在はletter位置開始/全prefixが片方の供給元にある場合。
全体build成功（9112 jobs、exit 0）、標準公理のみ、build終了済み。
Runは有効consume呼出しの列で、時計/lagによる有効化はまだ前提層。二往復予測列と実入力prefixの一致、stack→queueを跨ぐ供給、gap位置開始、中断/不一致restart、period左移動guardの全trace化、物理FIFOは残る。次は供給/consumeとlag catch-up・marginを同じ実行で同期しcanShiftへ。全PAL/期限は未完。

### 最新追記：任意開始状態の往復と4境界/phase4

ChainSweep.forward_boundaryは任意開始distance/phase/境界の成功片道。round_tripはreadyと同じperiod/forward=trueを持つ任意Stateから、period復元、distance+=2h、boundary=distance、last=開始distance+h、phase=advancePhase×2、broken保存を証明。
bounce=(xs++[b])++(xs.reverse++[center])。four_boundariesは同じrunへbounceを二回連結し、readyからdistance=boundary=4h、last=3h、phase4、forwardtrue/brokenfalse、period復元を証明（h=xs.length+1）。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
次はこの予測列/境界収支と実verifierの文字列・lag消費・marginへ接続し、phase4だけでなくcanShift全条件を導く。任意入力が一致するという主張ではなく、制御へ同じ予測列を与えた成功実行。中断/不一致restart/正例期限/物理回路/全PALは未完。

### 最新追記：成功した最初の往復でphase2へ到達

ChainSweepにrear/backward_interiorを追加。左向きplain走査はdistance+=長さ、右stackへ逆順積上げ、boundary/last/phase/broken保存でFIRSTに到達。
rear_after_lastで最初のLAST折返しTapeをその同じ逆向き入口へ接続。
first_round_tripはreadyから(xs++[b])++(xs.reverse++[center])を成功走査すると、periodがreadyの位置へ厳密に戻り、distance=boundary=2h、last=h、phase2、forwardtrue/brokenfalseを証明（h=xs.length+1）。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
次は任意開始distance/phaseの往復補題へ一般化して4境界/phase4へ反復し、実verifier・不一致restart条件へ接続する。現在は一致列を与えたConsume制御射影で、未来の一致や物理機械実行を証明していない。正例期限/全PALは未完。

### 最新追記：最初のsemiperiod成功走査と境界更新

新規`GalilScaffoldChainSweep.lean`（root import済み）。runはConsume.consumeへsome文字を逐次供給する制御射影、frontはLASTまでの通常文字列のTape形。
forward_interiorは任意長plain区間の一致走査でdistance+=長さ、period左stackへ逆順積上げ、boundary/last/phase/broken保存、forward=trueを保証。
first_boundaryはready(center,xs,b)からxs++[b]を成功走査するとdistance=boundary=xs.length+1、last=reset、phase1、forwardfalse/brokenfalse、LASTから左移動したTapeになると証明。first_turn_legalはそのLAST左移動の非空stack guardをFIRST残存から導出。
全体build成功（9111 jobs、exit 0）、標準公理のみ、build終了済み。
これは予測と一致した入力列の制御実行で、未来の入力が必ず一致するとは主張しない。実verifierがこの列を読むこと・途中の不一致/restartは別接続。次は左向き走査→FIRST折返し→複数境界のphase/last収支とperiod移動合法性、同じverifier実行への対応。全PAL/正例期限/物理回路は未完。

### 最新追記：verifier右移動からconsumeの読出しを供給

新規`GalilScaffoldChainVerifier.lean`（root import済み）。既存InputHead.Head/PlaceHead上でheadRightは右stack優先、空ならincoming先頭を取る。Right/HeadRight関係とcanRightからのright_realizeを証明。gap=false→gap=trueはhead移動なし、gap=true→falseでheadRight。
stack_read/queue_read/gap_readで供給文字を明示。right_leftは合法な左移動の直後に右へ戻ると元状態と一致。
Verifier.StateはverifierとConsume.Stateを持ち、consumeは同じright後のreadをcontrolへ供給する。consume_realizeは右移動関係を保証、consume_agreesは距離+1/broken保存、consume_mismatchはbroken化。consume_gapは実letter focus→gapの読出しからgap予測との一致を導出。
全体build成功（9110 jobs、exit 0）、標準公理のみ、build終了済み。
incomingは論理FIFOリストで実Queue.work/Ref/heapのrefinementではない。canRightは依然入力条件。次は準備のverifier=center配置とこのRightをつなぎ、文字予測の一致/不一致・period移動合法性を回文/境界不変条件から導く。全watch反復、back最終outer matched合成、正例期限、物理回路、全PALは未完。

### 最新追記：watch consumeとlagゼロのouter matched分岐

新規`GalilScaffoldChainConsume.lean`（root import済み）。Stateはperiod/distance/boundary/last/phase/forward/broken。consumeは**verifier右移動後のseenを引数**に取り、一致時distance.inc→境界ならlast=旧boundary/boundary=新distance/phase増加/方向変更→新方向でperiod移動。不一致はbroken、他の投影状態は保持。
plain/first/last/mismatch各更新式、ready_symbol、ready_one（h=1の最初はLASTで左折・boundary1）、ready_long（plainで右進・phase0）を証明。
`outerMatched`はfresh watch/only=falseの外側処理。disabled不変、lag非zeroは旧Credits.step(false,true)、lagzeroはconsumeしmarginだけinc/lag不変。outer_zero_mismatch/outer_zero_creditsで失敗時もmargin増加・lag保持を保証。
全体build成功（9109 jobs、exit 0）、印字公理は標準のみ、build終了済み。
**まだverifier.right自体とseenの供給のrefinementはない。** readyはback終了Tape形を使うが全controllerのwatch状態の到達定理ではない。任意consumeに対するperiod移動guard/内容不変条件、回文候補からの一致保証、back最後のイベントとの合成が次。正例期限・中断・物理回路・全PALは未完。

### 最新追記：foundの同じ結果から準備全体の契約を構成

新規`GalilScaffoldChainReady.lean`（root import済み）。`Prepared`は実center read、PacedCopy、OUTPUT LEFT/h positive/末尾plainのassertion群、PacedBack、終了Canonical/lag非zero、全matched込み収支、period読出し列/終了walkerをまとめる。
`found_prepared`は同じSafeQuanta/found/Resultから候補hを取り、そのh長copy列とh+1長back列の任意matched配置に対してPreparedを構成。窓配置一致とCanonical/正radiusは依然前提。
**重要な再確認：Scala replay_start(ScaffoldCircuitGalil.scala 271–284付近)はradius.resetしてsearch.startする。よって正radiusを全Search開始の普遍不変条件と置かない。found時の正性は未証明で、ゼロ分岐も必要。**
PacedBack.doneのガードを`b=true → lag.zero=false`へ精密化。matchedがfalseならlagゼロでもconsumeは無効。`pace_back_quiet`は全matched=falseのBackをradius/lagの正性なしで構成する（終了credits不変）。
全体build成功（9108 jobs、exit 0）、標準公理のみ、build終了済み。次はback終端のmatched/lagゼロ分岐をwatch.consumeへ接続し、正radiusを安易に仮定して閉じない。guard/eventの実対応、pause/fallback、正例期限、物理回路、全PALは未完。

### 最新追記：start/copy/done/backの同一credit状態を合成

`ChainCredits.prepare_paced`は同じCopy nとLAST化TapeからのBack(n+1)、正でCanonicalなradius、start/doneのmatched Bool、copy/back各matched列から、同じ中間creditsを使うPacedCopy→doneのstep→PacedBackを構成する。
`prepEvents`はstart(false,sm)::copy列(true,b)++done(false,dm)::back列(false,b)。最終状態=この全列をstart radiusからrunした状態、最終Canonical/lag非zeroを保証。
`prep_value`はその全matched数Mから最終margin=radius−4*copy列長+M、lag=radius+M。start/doneイベントを落としていない。
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。
次はfound_start_backで得た実center/OUTPUT/末尾assertion群をprepare_pacedへ一括接続し、radius正を実Searchの到達状態から導く。prepare_paced単体はCopy/Backとradius正を入力する接続定理で、実mode guard・pause/fallback・全online controllerを証明したわけではない。watch/consume、正例期限、物理回路、全PALは未完。

### 最新追記：copy/backと外側matchedを同じ実行へ同期

ChainCreditsにCopyState(answer/h/walker/period/credits)、copyStep、PacedCopyを追加。各tickは実copy操作とcreditsのdec×4→outer matched加算を一緒に行う。
`pace_copy`は同じChainPeriod.Copyと長さnのmatched Bool列からPacedCopyを構成。`pace_copy_balance`はその終了creditsのCanonical、margin=開始−4n+matched数、lag=開始+matched数を返す。
`PacedBack/pace_back`は同じBackと同長matched列を同期。最後のFIRST→右/watch tickでlag.zero=falseを実関係のガードとして要求し、入口Canonical/lag正からそれを導出する。back途中はmatchedによるlag.inc、periodへの作用なし。
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。これは中断なし・各tick有効のモデル。pause/fallback/shiftは未対応。
次はcopy終了credits→doneのLAST化tick（outer matchedあり）→back入口を同じ状態で合成し、実Chain.startのradius正条件を導く。start tick自身のouter matchedも省略しないこと。watch/consume、正例期限、物理回路、全PALは未完。

### 最新追記：found→start/copy/backの集約と準備counter収支

`ChainPeriod.found_start_back`は同じSafeQuanta/found/Resultとwindow=stream.takeの配置仮定から、center.read=someを導出し、そのcenterのFIRST初期化、同じOUTPUT/h/walker/periodのCopy、末尾plain、OUTPUT LEFT/counter positive、LAST化後h+1回Back、読出し列/終了walkerをまとめる。
`GalilScaffoldChainCredits.lean`新規/root import。Counter実dec×4（copy時）→inc（matched時）の順序でmargin、matched時incでlagを更新。`run_value`はmargin=初期−4*copy数+matched数、lag=初期+matched数、`run_canonical`はCanonical保存。
`lag_not_zero`は初期radiusがCanonicalかつ正なら準備イベント列後lag.zero=false。これはpositive radiusと実guard列対応が前提で、実到達条件からの導出はまだない。
**境界注意：Scalaはback最後のtickでwatchに変えてから外側matchedを呼ぶ。lag.zeroならそのtick中にconsumeしperiod/verifier等がさらに動く。found_start_backの出口は外側matched前であって無条件のtick終了状態ではない。Creditsはpre-watch射影で、shift/fallback/ready-consumeは含まない。**
全体build成功（9107 jobs、exit 0）、標準公理のみ、build終了済み。次は実radius開始条件・copy/backとCreditsの同一イベント列への同期、watch入口/consumeへ進む。正例期限・実heap/bit回路・全PALは未完。

### 最新追記：period copyとLAST化後のbackを接続

新規`GalilScaffoldChainPeriod.lean`、root import済み。Tokenはblank/LEFT/plain(Fin3)/FIRST(Fin3)/LAST(Fin3)の11種、Tapeはdecoded二stack。DPのFin9を流用していない。
`Copy`はOUTPUT/h/Placeの更新とperiod.moveRight→writeを同時に行い、`copy_period`が同じCopyWalkから実行を持ち上げる。
`fill_stack`で書込みのstack内容、`back_exact`でFIRSTまで左移動し最後に右移動する実back traceを証明。
`copy_then_back`は非空CopyWalkから末尾plain文字、同じperiod copy、LAST化したTapeからn+1回のBackを同時に構成する。n回copy→doneでLAST化（別1 tick）→n+1回back。backの終了はFIRSTの一つ右で、FIRSTそのものではない。
全体build成功（9106 jobs、exit 0）、標準公理のみ、build終了済み。途中の長さ補題エラーは修正済み。
まだcenterのread/start assertionはcenter引数との対応が必要。margin/lag、mode更新・pause・外側matchedとのinterleaving、物理StackPoolは未接続。次はfound_copy_walkとcopy_then_backをChain.startの実center読出しへ結び、margin/lag収支とwatch入口へ進む。全PAL/正例期限は未完。

### 最新追記：foundから同じOUTPUT/h/walker実行を構成

`ChainAnswer.CopyWalk`はAnswerCopyと同じmoveLeft/incに、Place.left後のread=someを同期させた関係。
`copy_walk`はn<stream.lengthからその実行を構成し、読出し列=(stream.drop 1).take n、終了stream=stream.drop nを保証。
`found_copy_walk`は同じSafeQuanta/found/Resultから候補hを取得し、候補の4h+1≤窓長からwalker長条件を導出。reset→h counter、OUTPUT LEFT、counter positive、読出し列と終了walkerを一つの実行にまとめた。
前提`w=(stream p).take(span+1)`は実online配置不変条件として残る。Placeは論理射影で、物理InputHeadへの全trace持上げは未実施。
全体build成功（9105 jobs、exit 0）、標準公理のみ、build終了済み。次はperiodのFIRST/plain/LASTを含む書込み・rewindへ進む。Scala period alphabetは11種類で、DP TapeのFin9をそのまま使うと不足する点に注意。margin/lag・正例期限・全PAL機械は未完。

### 最新追記：OUTPUT読出しとh counterのcopy射影が完走

`GalilScaffoldChainAnswer.AnswerCopy`は各copy tickのfocus=8・left非空を要求し、実moveLeft/incを行うOUTPUT/h射影。
`answer_copy_exact`はhead=n≤h、denote=output hからn回の同じ実行を構成し、head0/focusLEFT、counter=ofNat(k+n)を証明。
`answer_copy_done`はhead=h>0、counter resetからh回でLEFTかつcounter.positive=trueを保証し、Scalaのdone assertionに必要なOUTPUT/h条件を満たす。
全体build成功（9105 jobs、exit 0）、印字公理は標準3公理のみ。build終了済み。
これはOUTPUT/h射影であり、walker非None・period書込み・margin/lagを含むChain.copy全体ではない。
**次はこの実行へwalker/periodを加えて、suffix候補からwalkerのh回左移動の有効性とperiod内容を導く。** 下の要約の「OUTPUTをh回読む」はこの追記で完了した部分。

### 再開用の要約（この節を現在地として優先）

- **完成していないもの：無条件のPAL ∈ PEG。** `Main.pal_in_peg_of_structured`に渡す具体的機械と全体の認識証明が残る。
- **直近で閉じたもの：** DP成功結果のOUTPUT内容に加え、ヘッド位置=hを公開。`GalilScaffoldChainAnswer.found_output`で同じSearch実行のfoundから最小候補・OUTPUTの末尾1・左移動可能性まで接続した。Chain全体を証明したわけではない。
- **直前の検証記録：** 全体`lake build`成功（9105 jobs、exit 0）。今回の引き継ぎではソースと記録を照合し、`git diff --check`を再実行して成功。全体buildの再実行はしていない。
- **次に実装するもの：** Scala `ScaffoldCircuitChain.scala`のcopy分岐を読む。`GalilScaffoldChainAnswer.lean`から、OUTPUTをh回左へ読んでLEFTに到達し、同じ実行でh counterがhになる証明へ進む。その後walker/periodの構築、margin/lagの条件を接続する。OUTPUTだけの補題をChain完成と数えない。
- **並行して残る接続：** stage出口の候補意味と反復契約、同一event列のclock引継ぎ、初期radius条件、grow/prepare/run中のfallback・restart、正例期限、実heap/bit回路・FIFO・packing。論理List層の証明を物理回路の証明と扱わない。
- **時計の不一致に注意：** LeanのDP上界は3186N+1683、stage安全性はdelay 2048を使用。Scalaの`buildOnline`側の旧FppCost由来の時計較正は未更新。最終構成で一致させる必要がある。
- 再開時は`GalilScaffoldChainAnswer.lean`、`GalilScaffoldTape.lean`、ScalaのChainを先に読む。巨大な履歴全体を読み直す必要はない。検証手順とScala入口は本書末尾の該当節を参照。

以下は新しい順の作業履歴。各項目の「次」「未接続」はその時点の記録であり、後続作業で解消済みの場合がある。現在地は上の要約と先頭の完了記録を優先する。

### 最新：chainへ渡すOUTPUTヘッド位置をResultへ追加・検証完了

Scala Chain.stepはanswer.focus=1から左へ読み、LEFTで終わる。旧DpCorrect.ResultはOUTPUT内容だけでheadを公開していなかった。
DpCorrect.Resultの成功枝をpc346∧tape11=output h∧pos11=hへ強化し、correct_loopのTracked.outputPosから証明。DpSuffix.Resultも同様に強化。末尾のtape等式は現在tape等式∧位置等式なのでconsumerの分解に注意。
新規ScaffoldChainAnswer.found_outputは同じSafeQuanta/Result/foundから最小候補、OUTPUT内容/head h/focus8/left非空を取り出す接続（root import追加）。
全体build成功（9105 jobs、exit 0）、ChainAnswerも検証済み、標準公理のみ。起動build終了済み。最初のbuildは途中追加したroot importのolean未生成で失敗し、終了後の再buildで新依存を生成して成功。Result変更による既存証明の破綻はない。
次はOUTPUTをh回左へ読みh counterを構成するChain.copy実行へ接続。walker/period/lag/marginと正例期限は未完。最終目標は未完。

### 最新：controller出口をsuffix回文候補へ接続

`DpSuffix.result_of_reverse`を任意の同じResultへ適用できる形で抽出しinitial_correctを再利用する形へ整理。
`SearchRun.quanta_suffix_result/quanta_window_result`がSafeQuantaの同じ終了Machineについてsuffix Result（最小候補・pc・単項OUTPUT）とfound/missed同値を同時保証。
窓はw.drop(w.length-(span+1))。DP入口のw.reverse.take(span+1)とList.take_reverseで厳密に一致する。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。wは論理入力窓の引数で、実center/online inputとの配置対応を新たに証明したわけではない。次はこのsuffix候補/OUTPUTをchainの入口条件へ接続し、stage反復と正例期限へ進む。初期radius/実制御/物理回路は未完。

### 最新：found/missedを同じDP結果へ接続

`SearchRun.TerminalLink`はrun中を除きfound iff pc346、missed iff pc≠346かつfinalStage。call→SafeCalls→SafeQuantaで保存。
`quanta_found_result`は同じ終了MachineのResultからfound iff Candidate存在を導出。
`quanta_missed_result`はmissed iff Candidate不在かつrun入口finalStage=true（finalStage保存を使用）。単なるmode列挙から候補意味との接続へ進んだ。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。CandidateはDP窓の条件で、最終PAL出力/chain正しさの証明ではない。次はstage存在・出口契約へこの意味を組み込み、同じイベント列での反復とclockを接続。初期radius/正例期限/物理回路は未完。

### 最新：run出口とwait処理を一つの分岐契約へ

`SearchRun.quanta_exit_mode`はrun入口から非run終了するSafeQuantaのmodeをfound/missed/wait/doubleに限定。
`StagePrepare.prepared_exit`は同じ準備/run traceから、必要ならwait prefixを実行し、found/missed/idle fallback/NextStageのいずれかを返す。terminal/direct doubleの場合は空wait traceで状態を保持し、waitの場合だけ供給条件を要求。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。mode found/missedとDP Resultの意味的対応（同じ終了Machine）はまだ未接続。次はこの対応、stage存在定理との合成、同じevent列の終了clock引継ぎ。全オンライン制御/初期radius/正例期限/物理回路は未完。

### 最新：NextStage契約から次の安全実行を構成

`StagePrepare.next_stage_safe`は前境界のSearchFinish.State sとNextStageを受け、**Double.Run s**から始まる次stageのdouble→PacedPrepared→SafeQuanta停止/Result/収支/終了Canonical/非負を構成。
runState(restoreState base s)0=sをquarter0から導き、別の仮想入口状態にはしていない。base側program/walkerは保持しprepareでresetする。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。時計生成列一致、double/prepare/runの予算列長、centerは依然入力条件。次はrunのfound/missed/wait/double各出口を分類して反復契約へまとめ、同じevent列と終了clockの対応を接続。実制御/初期radius/正例期限/物理回路は未完。

### 最新：stage→wait離脱から次stage入口をまとめて導出

`StagePrepare.NextStage lower n s clock`はmode.double/work=ofNat n/span0/quarter0/Canonical/debt-clock選言/clock範囲/StageSizeをまとめた契約。
`prepared_wait_next`は同じPacedPrepared→SafeQuantaのwait終了状態から、十分availableを持つWaitInterrupt.Run prefixを構成し、idle中断またはNextStageを返す。個別frame/reset/安全性補題を同じ終了状態へ集約した。
入口Canonical/非負は強化済みstage定理から渡せる。wait開始clockとavailable供給はまだ引数、前runの実event列終了clockとの一致は未接続。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はNextStageからlater_stage_safeへの接続と、run直接double/terminal分岐を含む反復契約。実制御/初期radius/正例期限/物理回路は未完。

### 最新：stage停止結果を次区間へ渡せる形に強化

`SearchRun.dp_quanta_safe/calibrated_quanta_safe`の戻り値に終了Canonical/非負を追加。既存quanta_safeのCanonical保存と消費prefix≤全advance予算から導出。
`StagePrepare.first_stage_safe/later_stage_safe`も同じ終了Canonical/非負を返すよう変更し、呼出し側を更新。**これらの戻り値の末尾は旧debt等式だけではなく等式∧Canonical∧非負。** 次wait入口で非負を仮定し直す必要がない。
`WaitInterrupt.double_reset`は同じRunのwait→double終了にspan reset/quarter0を保証。直接run→doubleとwait経由のreset条件がそろった。
全体build成功（9104 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。次は強化したstage結果→wait離脱→次stage/fallbackを一つの反復契約へまとめる。実制御/初期radius/正例期限/物理回路は未完。

### 最新：wait経由の次doubleへspanを受け渡し

`WaitInterrupt.run_stopped`は非wait入口ならRunが空で状態/clock不変と証明。`tick_span/run_span`は非idle終了ならstageSpan（doubleではwork）を保持し、`double_work`で終了work=wait入口span。
`StagePrepare.prepared_wait_double_work`は同じPacedPrepared→SafeQuanta→WaitInterrupt.Run→doubleから次work=準備入口spanを導く。直接run→doubleとwait経由の両方で受け渡しがそろった。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。まだ全stage存在定理の戻り値にwait入口Canonical/非負やspanなどをまとめて反復する接続は未完。wait→doubleのreset/quarter条件も同じRunへ追加する必要あり。実制御/初期radius/正例期限/物理回路は未完。

### 最新：fallback込みwaitの供給量付き離脱

`WaitInterrupt.tick_debt/run_debt`でfallbackによるmode変更も含めdebt=開始値−同じ実行の比較数を証明。
`supplied_exit`は初期debt=k、available数≥2048*(k+1)から安全Run prefixでmode≠waitを構成。Outcomeよりidle中断かdouble。列末までwaitの枝を収支と時計供給量の矛盾で排除。
これは保守的なavailable-tick上界で、壁時計や全オンラインstep上界ではない。scopeは引き続きscan/chain idle/非replayのSearch射影。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はstage停止後のwait入口条件/保持spanとこの離脱を合成し、double反復またはfallback本体へ接続。初期radius/実制御refinement/正例期限/物理回路は未完。

### 最新：fallback込みwaitを有限イベント列へ拡張

`WaitInterrupt.Run`は各wait入口assertion、tick（wait→advance→fallback）、実clock更新を含む。
`run_prefix`は任意有限(available,equal)列から最初のwait離脱まで（または列末まで）のRunを構成し、used/rest分割、Canonical、clock範囲、idle/非負wait/debt-clock条件付きdoubleのOutcomeを返す。restが残れば終了mode≠wait。
`run_clock`で終了clockが同じusedイベント列をMatchClockへ通した結果と厳密一致。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。scopeはscan/chain idle/非replayのSearch射影。次は十分なavailable供給で「列末wait」の枝を排除し、zero到達/中断の二択を証明、stage/FPP fallbackへ渡す。初期radius/正例期限/物理回路は未完。

### 最新：fallback込みwait tickを分類

新規`GalilScaffoldWaitInterrupt`（root import済み）。scan/chain idle/非replayのSearch射影。Chain.canShiftはwatchを要求するのでidleではfalse（Scala確認）。tickはwaitStep→compareによるadvance→不一致compareならmode.idle。
`safe_tick`は入口wait/Canonical/非負/clock範囲からassertion安全・終了Canonicalと、idle中断 / 非負wait継続 / debt-clock条件付きdouble移行の三分岐を証明。
`fallback_idle`と`uninterrupted`で中断と旧モデルへの一致を明示。idleをwaitの続きとして扱わない。
単体Lean検査・全体build成功（9104 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**有限イベント列で最初の中断/離脱までを構成する反復関係は未実装。fallbackのFPP/heads/g.mode更新全体・replay禁止assertionの到達不変条件も未接続。** 次はこの三分岐をイベント列へ持ち上げる。初期radius/正例期限/物理回路は未完。

### 最新：wait guardのScala対応範囲を確認

Scala ScaffoldCircuitGalil.scala 141–170を再読。search.tickのenabledはscanning && !chainActive && search.active（availableに依存しない）。比較時計はdispatch.scan && available。advanceは比較後Search.activeとchain.idleで判定。
`Wait.active/searchEnabled/advanceGuard`をdecoded定義し、`idle_scan_wait_guards`でscan/chain idle/mode.waitならsearch enabled=true、waitStep後（double移行含む）のadvance guard=available&&clock1を証明。`not_scanning_guards`でscan外は両方false。
**重要：同ファイル後段fallbackはsearch.modeをidleへ上書きする（190行付近）。wait供給定理を無条件のオンラインwait継続・停止と扱ってはいけない。scan継続/chain idle/非fallback区間の不変条件、または中断を含むモデルが必要。** chain active→idle/restartのtickも単純pause扱い不可。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はイベント列を実制御へ接続する前にfallback/restartによる中断の扱いを組み込む。初期radius/正例期限/物理回路は未完。

### 最新：wait→doubleの次イベントを同じ列に固定

`Wait.clock_sequence_double`は2048k availableを供給するbsに1イベントextraを追加したevents=bs++[extra]を用いる。
zero到達prefix nに対しn<events.length、Runのadvance列=events.take nの生成列を保証。double dispatch末尾のavailabilityは別引数ではなくevents[n]!から読む（範囲内を証明済み）。同じprefix終了clockを使用しdouble入口条件を保持。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。全eligible・各dispatch有効というモデル条件は依然残る。終了clockはprefix時計から次イベントを1回更新した定義で、元列take(n+1)との補題化は未実施。次はオンラインenabled/eligible条件とstage間接続。初期radius/正例期限/物理回路は未完。

### 最新：wait prefixの終了時計からdouble入口へ合成

`Wait.clock_prefix_double`がclock_prefix_zeroの同じprefix終了clockをDouble.enter_boundaryへ渡し、次の有効wait dispatch→advance後のdouble入口条件をまとめる。
次work=wait開始span、span reset、quarter0、Canonical、debt≥0または(debt≥−1/clock reset)、clock範囲を保証。
前提はdebt=k、2048k available、prefix全eligibleなど従来の供給条件。**次の有効tickのavailable/eligibleは別引数で、元bsの次要素との一致や途中pauseのrefinementはまだない。**
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は同じオンラインevent列でstage終了→wait prefix→次double stageを組む。初期radius/実guard/正例期限/物理回路は未完。

### 最新：wait停止prefixと同じ時計位相を取得

`AdvanceClock.advances_take`でイベントprefixの生成advance=全生成列のprefix。
`Wait.clock_prefix_zero`はclock_reaches_zeroのusedを元available列bsのtake nへ戻し、n≤bs.length、同じprefixから生成するRun、zero/Canonical/span保存と、同じbs.take nを実行した終了clockの1..2048を同時保証。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はこの終了clockをDouble.enter_boundaryの引数へ渡し、次の有効wait dispatchでdouble入口条件を合成する。実eligible/available供給・初期radius・正例期限・物理回路は未完。

### 最新：waitへのadvance供給を比較時計から導出

`AdvanceClock.advances_append`はイベント区間分割に対し前区間終了clockを後区間へ渡す厳密な生成列等式。
`eligible_compares`で全eligibleならadvance数=比較数、`eligible_supply`で有効clock位相からk*delay個のavailable tickがk advances以上を供給すると証明。
`Wait.clock_reaches_zero`はdelay2048、初期debt=k、available数≥2048kから安全wait prefixのzero到達/span保存を構成。「advanceが十分」という前提は時計供給から導出した。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**全eligibleはモデルの入力条件で、実active/chain idleの証明ではない。available供給と待機prefix終了clockへの接続は未完。** 次は実イベントprefixへ対応させ境界の位相を引き継ぐ。初期radius/正例期限/物理回路も未完。

### 最新：waitの安全なprefixでdebtゼロへ到達

新規`GalilScaffoldWait`（root import済み）。Runは非zero waitの実waitStep→advanceを繰り返し、各入口のnegative禁止assertionを含む。
`reaches_zero`はwait入口Canonical/非負とadvance列count≥入口debt値から、列のprefix usedで同じwait実行がzeroへ到達することを構成。Canonicalとspanを保持し、残り列restを返す。
ゼロ到達後をwait実行として消費しない。次の有効tickのwait_enter/enter_boundaryへ渡す設計。
単体Lean検査・全体build成功（9103 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**十分なadvanceの供給は前提、実clock/eventからの待機時間上界は未接続。** 次は停止prefixのclock位相を追跡してdouble境界へ合成し、stage反復へつなぐ。実event/初期radius/正例期限/物理回路は未完。

### 最新：実doubleから次doubleへ倍増とreset条件を導出

`Double.span_of_run`は任意の同じRunについてspan=ofNat(n+2*length)を証明。
`StagePrepare.double_stage_next_size`はDouble.Run→PacedPrepared→SafeQuanta→doubleの同じtraceから次work=ofNat(2*double列長)とStageSizeを導出。中間span=2nは外部前提ではなくなった。
`SearchRun.double_reset_of_quanta`はrunからdoubleへ終了するSafeQuantaについてspan=reset/quarter0を保証。DoubleResetをfinish/SafeCalls/advanceで保存する。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は同じ終了traceのclock/debt境界条件を合成し、wait経由も含めstage反復へつなぐ。実event/初期radius/正例期限/物理回路は未完。

### 最新：準備span保存と次doubleの数値条件

`PreparePaced.paced_span/prepared_span`が任意advance込み準備実行でspanの厳密保存を保証。
`StagePrepare.prepared_double_work`は同じPacedPrepared→SafeQuantaからdouble終了work=準備入口spanを導く。
`StageSize lower n := 8≤n ∧ n%4=0 ∧ 4*lower≤n`。初回8*max(lower,1)で成立し、倍増で保存。`prepared_double_size`は入口span=ofNat(2n)を持つ実準備/run traceにこの数値条件を接続。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。まだspan=2nを前区間から自動取得する全stage合成やwait経由の反復は未完。double入口span reset/quarter0/clock-debtも同じtraceへまとめる必要がある。実event/初期radius/正例期限/物理回路は未完。

### 最新：run終了時のstage span受け渡し

`SearchRun.stageSpan`はdoubleならwork、それ以外ならspan。`finish_frame`→`safe_calls_frame`→`safe_quanta_frame`でfinalStageとstageSpanを厳密に保存する。
`double_work_of_quanta`はrun入口からdouble終了なら終了work=入口spanを導く。run終了後にspanがresetされるため、単純なspan保存ではなく実workコピーを追跡する。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は準備終了spanの保存とこのframeを合成し、stage間の倍増/4倍数/lower上界を接続。double入口span reset/quarter0とclock/debt境界の同じ実行への合成も必要。実event/初期radius/正例期限/物理回路は未完。

### 最新：run/wait→double境界のdebt/時計条件

`Double.enter`はScalaのwork=span/span reset/quarter0/mode.double。`finish_enter`は非final失敗PC347/debt.zeroから一致、`wait_enter`はwait/zeroから一致。
`enter_boundary`はzeroのCanonical debtと有効clockから、double更新後の実形式advance（available && clock=1 && eligible）を適用し、work/span/quarter/Canonical/次clock範囲と **debt≥0 または(debt≥−1かつ次clock=2048)** を導く。
`wait_positive_advance`はwait入口Canonical/非負/非zeroからwait継続、advance後非負、入口assertion安全を保証。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はこれら境界定理をstage終了状態とlater_stage_safeへ合成し、stage間のspan/lower不変条件を接続する。実event eligibility/初期radius/正例期限/物理回路は未完。

### 最新：後続stageのdouble→prepare→安全なDP停止を合成

`StagePrepare.later_stage_safe`を追加。非reset clockのadvance上界、実double/prepare tick数、calibrated runBudgetを合成しSafeQuanta停止prefix/Result/全debt収支を構成する。run入口debt予算・stage長上界は内部導出。
前提：double入口work=n/span0/quarter0、4|n、n≥8、4lower≤n、Canonical、clock範囲、予算列長と実時計生成列の一致。
入口debt条件は **debt≥0 または(debt≥−1かつclock=2048)**。Scalaはrun/wait→double更新後にもadvanceMatchを行い得るため、入口非負だけでは境界を落とす。リセット直後の時計上界で−1分の余裕も証明した。実到達状態がこの選言を満たす証明はまだ必要。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はrun/wait→double境界のclock/debt不変条件と、初期radius・実event guardへの接続。物理回路/正例期限/全PAL機械は未完。

### 最新：double終了から同じ状態のprepareへ接続

`StagePrepare.restoreState`はSearchFinishのcontroller fieldsを共有Stateへ戻しprogram/walkerを保持。`restore_runState`で射影の往復一致。
`double_then_prepare`はquarter0/work=n/span0/4|nからDouble.Run→PacedPreparedを構成し、正確なDP入口、終了quarter0、Canonical、debt=開始値+n/4-(double列++準備列).countを保証する。
`TimingCost.later_stage_ticks`はn≥8、4lower≤n、m≤2n+1からn+2lower+2m+7+runBudget(2n)≤63*(2n)。
double_then_prepareの単体検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はlater_stage_advancesの全advance≤(2n)/8と収支を合わせ、後続SafeQuantaを構成する。入口debt0/初期lower条件/実clock-event対応は別途必要。

### 最新：後続doubleのquarter/advance収支と完走

新規`GalilScaffoldDouble`（root import済み）。SearchFinish.State上で旧quarter=3を検査し、work.dec/span.inc×2/quarter=(q+1)%4/debt.incを実行後、外側advance減算。
`complete`はwork=ofNat as.lengthから同じas列のRunを構成し、work0/span+2*length/mode.doubleを保証（終了zero dispatchはprepare側）。
`balance`は4*debt+quarterの厳密な収支、`completed_credit`は開始quarter0・回数が4の倍数なら終了quarter0/debt+length/4-countを証明。`canonical`はdebtのCanonical保存。
単体Lean検査・全体build成功（9102 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次はdouble終了の同じ状態からprepareへ接続し、後続stageのclock予算と合成する。実オンラインguard/初期radius/正例期限/物理回路は未完。

### 最新：初回grow→prepare→安全なDP停止を一つに合成

`StagePrepare.first_stage_safe`が共有PacedGrowing/PacedPreparedから、`runState p quarter`と同じp.programを入口とするSafeQuantaの停止prefix、正しいDP Result、全stageの厳密なdebt収支を構成する。
**run入口debt予算とstage時間上界を外部前提から除去**。区間長からfirst_stage_ticks、時計advance総数からfirst_stage_barrier、準備収支からrun入口の残り予算を導く。
残る前提：初期mode/work/span/debtとCanonical、3radius≤5r、各区間の予算長、as++bs++csがdelay2048/reset時計の生成列と一致すること。quarterは引数（初回実装では0）。runStateは共有フィールドの射影で物理回路の証明ではない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は実オンラインguard/eventの対応・初期radius契約と、後続double/wait stageを扱う。全PAL機械/正例期限/heap-bit-FIFO接続は依然未完。

### 最新：時計とDPの予算不一致を解消

`SearchRun.dp_quanta_safe`のhaを「3186*w.length+1683≤64*as.length」へ一般化した（旧50*m+27の等式ではない）。scheduled_correctから任意十分予算の実行を構成する。
`calibrated_quanta_safe`はw.length≤span+1から、TimingCost.runBudget span長のadvance列で安全な停止prefixと正しいResultを構成する。入口Canonical/debt予算はまだ前提。
`TimingCost.first_stage_ticks`は実grow/prepareコスト `max(r,1)+2r+2m+7` とrunBudgetの和≤63*(8max(r,1))をm≤span+1から導出。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は準備終了StateをSearchFinish.Stateへ写し、全stageのadvance列を分割して入口debt予算を導く。実guard対応と初期radius契約は未接続。

### 最新：advance込みrun実行の存在・停止を実DPから構成

`SearchRun.guarded_split`/`guarded_stopped`でGuardedRunを分割し、`realize_quanta`で64呼出しごとにadvanceを挿入するRunQuantaを構成。
与えたadvance列asのprefix usedだけを実行し、as=used++rest、同じ終了Machine、mode≠runを保証。run終了後の外側tickを架空のrun実行で埋めない。
`dp_quanta_safe`は実DPのquantum64_correctから、安全な外側tick実行・正しいResult・厳密なdebt収支を同時構成する。
予算列長は50*w.length+27。初期Canonicalと初期debt値≥as.count trueは前提。実行列の存在/停止は前提から外れた。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。次は共有準備状態からSearchFinish.Stateへの対応と全stage時計予算の接続。
注意：TimingCost.runBudgetはceilのより小さい予算なので、50*m+27を使うこの定理とそのまま同一視しない。scheduled_correctから任意十分予算への一般化が必要。

### 最新：run外側tickのadvance込み安全性

`SearchRun.RunQuanta`/`SafeQuanta`を追加。各tick入口mode.runを要求し、64回のCalls/SafeCallsの後に外側advanceを1回適用する。非run移行後の別dispatchをrun扱いしない。有効tickのみ（pauseの拡張は未実装）。
`quanta_safe`は既存RunQuanta、初期Canonical、初期debt値≥全advance数から全SafeQuanta、終了Canonical、厳密なdebt減算収支を証明する。
単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。**RunQuantaの存在/停止・実clockからの全advance予算・共有PrepareControl.Stateとの接続は未実装。**
次はGuardedRunの64呼出しごとの分割とfinish/debt差替えを扱い、mode.runが続く区間だけをRunQuantaへ構成する。終了tick以降をrun tickで埋めないこと。

### 最新：初回準備終了のdebt assertionを時計上界から導出

`StagePrepare.first_prepared_safe`を追加。共有PacedGrowing→PacedPreparedの実行と正確なDP入口を構成し、終了debtのnegative≠trueを導出。
前提は初期work=max(r,1)/span0/debt=-radius、Canonical、3radius≤5r、advance列がdelay2048/reset時計の生成列と一致すること、イベント長≤63*(8max(r,1))、各区間長。
終了debtのCanonicalは`paced_growing_canonical`と`PreparePaced.spend_canonical`で初期Canonicalから導く。終了debt収支・非負性を外部前提にはしない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。**実イベントguard・初期radius契約・実tick長上界はまだ前提。run中のadvanceや終了時assertionは未接続。**
次はrun区間の外側tick（quantum64内の呼出しとの区別）とadvanceをモデル化し、全stageの時計上界を使用する。

### 最新：共有grow→prepare全体のadvance収支を合成

`GalilScaffoldStagePrepare.PacedGrowing`はpositive grow更新後にadvance減算する共有State実行。
`paced_growing_complete`でwork0/span+8g/debt+2g-countを証明。
`paced_grow_then_prepare`はその同じ終了Stateから`PacedPrepared`へ接続し、
DP初期config/run/done=false/finalStageと **debt値=初期値+2g-(grow列++準備列).count true** を同時保証する。
prepare開始dispatchのadvanceも含む。単体Lean検査・全体build成功（9101 jobs、exit 0）、標準公理のみ。diff check成功、起動build終了済み。
実compare/active/chain guardとの対応・run区間のadvance・初期radius・double quarterは未接続。
次はこの共有実行の収支をAdvanceClockへ接続する。下記の共有Growing未実装という記述は履歴となった。

### 保存後の継続：prepare開始tickのadvanceも接続

`GalilScaffoldPreparePaced.prepared_interleave`を追加。任意の`PreparedRun lower center s n t`と長さnのadvance列から、prepare dispatch直後のadvanceも含む`PacedPrepared`を構成する。
終了状態は厳密に`{t with debt := spend as s.debt}`。既存prepare_completeの証人へ直接適用でき、最初の1 tickを落とさない。
単体Lean検査・全体build成功（9101 jobs、exit 0）、diff check成功、標準公理のみ。起動build終了済み。実guard対応、共有Growingのadvance、runStep非負性は未解決。
次は共有Growingのcredit/advance収支とこの実行を合成する。

### 引き継ぎ確定版（2026-09-14、以下の履歴より優先）

今回の依頼は進捗保存。証明の追加はせず、現物を確認して保存した。
**全体 `lake build` 成功（9101 jobs、exit 0）、`git diff --check` 成功。**
最新の `GalilScaffoldPreparePaced` もroot import済み。今回起動したbuildは終了済み。
既存linter警告はある。commitなし。dirty/untrackedファイルも引き継ぎ対象であり、GitのHEADだけでは再現できない。

現在地を短く言うと、**実FPP/DPの正しさ・線形時間上界と、共有controllerのgrow→準備→DP入口までの局所接続がある。オンライン機械全体の正しさはまだない。**

- `GalilDpCost.initial_correct_cost`: 同じDP実行のResultと命令数 `3186*N+1683` 以下。
- `GalilScaffoldPrepareControl.prepare_complete`: resetからLOWER/SOURCEを準備し、`2*r+2*m+7` tickで正確なDP初期config、mode.run、done=falseへ到達。`m=min(stream.length,span+1)`。
- `GalilScaffoldStagePrepare.grow_then_prepare`: 共有Stateのgrow guardから上記へ接続。advanceなしでspanに8*g、debtに2*gを加算。
- `GalilScaffoldPreparePaced.interleave`: 準備Runへ任意advance列を挿入でき、終了状態のdebt以外は厳密に同じ。実オンラインguardとの対応は未証明。

**次に実装する接続（未実装）**:

1. `PreparePaced.interleave`を`PrepareControl.prepare_complete`へ適用する。prepare自身の1 dispatchにも外側advanceが起こり得るため、本文Runだけに適用して1 tick落とさない。
2. `StagePrepare.Growing`へ同じ共有State上のadvanceを挟み、grow credit込みで `debt=初期値+2*g-advance数` を導出する。既存`GalilScaffoldGrow.paced_stage`は射影モデルなので、そのまま全Stateの実行とは扱わない。
3. `GalilScaffoldAdvanceClock`のイベント列・stage長上界へ接続し、実runStep入口のdebt非負条件を導く。初期radius条件と実active/compare/chain guardは別途必要。

その後もdoubleのquarter更新、全controllerの進捗・正例期限、実heap/bit回路・固定割当・FIFO、packing、具体的StructuredMachineのPAL正しさが残る。
`Main.pal_in_peg_of_structured`は条件付きのまま。完成率や残り時間を裏付けなく述べない。
新DP上界に対応する時計候補はstage係数63・delay2048。**Scalaの`GalilClock.derive`の旧コスト表は未更新**であり、現実装が新上界で検証済みとは言えない。

まず上記4ファイルと`GalilScaffoldAdvanceClock.lean`、Scalaの`ScaffoldCircuitSearch.scala`/`ScaffoldCircuitGalil.scala`を読む。
以下の多数の「最新」「次」は逆時系列の履歴で、古い未完了記述はこの節で上書きする。サブエージェントは使わない。

### 最新：共有準備Runに外側advance減算をinterleave

新規 `GalilScaffoldPreparePaced`：tick_rebaseで全準備Tickがdebt差替えに不変と証明。
PacedRunは準備Tickの後にafterAdvanceでdebt.decする、Scala順序の共有State実行。
interleaveは任意Run x bs yと同長advance列asから、同じbs.zip asのPacedRunを構成し、
終了状態は厳密に{y with debt := spend as c}。他の全フィールドを保持する。
spend_valueでdebt値=開始値-as.count true。任意Bool pause列にも適用可能。
単体Lean検査成功、標準公理のみ。root import済み。

**advance列が実active/compare/chain条件を満たすことは依然別。**
この準備Tickはdebtを読まないため全符号で成立するが、runStep/waitのnegative禁止まで解決したわけではない。
次はprepare_completeの実行へ適用し、grow中のcredit更新＋advanceも共有Stateでinterleave、
初回stage収支とAdvanceClockへ接続。物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：共有Stateのgrow終了guardからprepareへ接続

新規StagePrepare：growStepは共有PrepareControl.Stateのwork/span/debtを更新。
Growingはpositive guardのg tickを実行し、mode.growかつpositive(work)=falseで終わる。
growing_completeはwork0/span=ofNat(span+8g)/debt値+2gを保証。
grow_then_prepareはその同じ終了Stateからprepare_completeへ接続し、正確なDP初期状態、
run/done=false/finalStageとdebt値+2gを保証。準備部分は2r+2m+7 tick、grow部分g tick。
単体Lean検査と全体build成功（9100 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**advance割込みなしの実行であり、実オンラインstage全体の証明ではない。**
次は共有Stateのdebtだけを外側でdecする操作をGrowing/準備Runに挟み、
Counter収支とAdvanceClockのイベント列を接続する。初期radius条件・doubleのquarter更新、
物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：初期prepare更新を含むcontroller準備完走

PrepareControl.prepareはScalaのreset320/walker=center/work=lower/LOWER LEFT-right/mode.lower/final=falseを実装。
PreparedRunはこの1 dispatchと既存Runを合成する関係。
prepare_completeはspan=ofNat spanを前提に、任意旧programから2r+2m+7 tickで
正確なDP初期config/run/done=false/debt保存/finalStageを保証する。
LOWER入口のreset/LEFT条件はprepareの定義から導出し、外部前提ではなくした。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

PreparedRunはprepareの呼出しを記録するが、**grow/doubleの終了guardがその呼出しに到達する証明は未接続**。
次はgrowの共有状態へのliftとprepare呼出し境界、外側advanceの割込みを接続。
reset/counter/Placeは論理解釈で、heap/bit/FIFOや正例期限・最終PAL機械は未完。

### 最新：準備4区間の共有controller完走を合成

PrepareControl.prepared_runがlower入口から同じ共有StateのRunで
**2*lower+2*w.length+6有効tick**後、mode.run、program.config=ScaffoldPreload.initial w lower、
done=false、debt保存、finalStage iff stream終端を保証する。
w=(Place.stream s.walker).take(span+1)。入口はwork=ofNat lower/span=ofNat span、
LOWERがLEFT/right設定後、他テープreset。lower_load/lower_homeのwalker/SOURCE保存を強化し、
source_run_frameでSOURCE区間中のLOWER保存、run_span/run_appendを追加して合成した。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

**初期prepare tick・grow・外側advanceMatchはまだ含めない。**
次はgrow終了のprepare実更新（reset/walkerコピー/work lower/LEFT right）を入口条件へ接続し、
外側advanceによるdebt減算と任意pauseを持つ準備Runへ拡張する。
DP予算との合成は最終configの完全一致を使える。物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：SOURCE Copy/Homeを共有controller Runへlift

PrepareControl.source_copyはPlace.Copyの同じn tickを共有Runへ持ち上げ、mode.home、
正確なwork=ofNat残量/walker/Tape/finalStageを保持。
source_homeはRewindを同じn tickで実startRunへ持ち上げ、mode.run、SOURCE最終Tape、
pc320/done=false、finalStage保存を保証。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.sound。
実行中プロセスなし。git diff --check成功。

4区間のliftがそろった。**まだ全区間合成定理はない。**
次はRun.append、span/walkerのLOWER区間保存、SOURCE区間のLOWER保存などの
phase-specific frameを追加し、lower_ready/place_readyの実行を同じState上で合成する。
既存run_frameは7/10の両方を除外するため、SOURCE処理中の10保存をそのまま導けない点に注意。
正例期限・外側advanceMatch・物理heap/bit/FIFO・最終PAL機械は未完。

### 最新：LOWERの実行を共有controller Runへlift

PrepareControl.lower_loadは既存Lower.Load nを同じn有効tickのRunへ持ち上げ、
lower_home到達・同じwork/LOWER最終Tapeを保証。
lower_homeは既存Rewind nを同じn有効tickでcopy入口へ持ち上げ、LOWER最終Tape、
実work=inc span、SOURCEのLEFT/right設定を同じ共有Stateで保証する。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

次はPlace.Copyを共有StateのcopyBit/copyEndへlift（workはofNat表現を使いzero/dec対応）、
SOURCE RewindをsourceLeft/startRunへlift。その後Run.appendとspan/debt/frame保存で
LOWER→SOURCE→runをつなぎ、具体初期状態から完走証明を得る。
外側advanceMatch・grow・物理heap/bit/FIFO・正例期限・最終PAL機械は未完。

### 最新：準備4モードの共有controller状態を定義

新規 `GalilScaffoldPrepareControl` はmode/program/work/span/debt/walker/finalStageを同じStateに持つ。
TickはlowerBit/lowerEnd/lowerLeft/beginCopy/copyBit/copyEnd/sourceLeft/startRunとdisabled identity。
beginCopyで実work=inc span、copyでPlace.read/left、homeでprogram.start320を更新する。
左移動の非空guardを明示。run_debt/run_frameで任意Tick列がdebtとテープ7/10以外を保存すると証明。
単体Lean検査と全体build成功（9099 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**この新しいRunで任意入力の準備が完走する証明はまだない。**
次は既存Lower.Load/RewindとPlace.Copyをこの共有StateのRunへliftし、phase間で
同じwork/program/walkerが受け渡されることを示す。grow/advance/heap/bit回路は別。
この定義追加を実controller全体の完成と報告しない。正例期限・最終PAL機械は未完。

### 最新：walker準備の全12テープ初期状態とDP開始を接続

SourceReady.prepare_programはreset後にLOWER、SOURCEのLEFT/right設定、同じPlace.Copyと
Rewindを合成し、最終全状態=ScaffoldPreload.initial w lowerを証明。
w=(stream p).take(span+1)。テープ基本操作は3*(lower+w.length)+8。
prepare_then_dpはこの準備結果からstart320を通じ、3186*w.length+1683有効tick以上の
任意スケジュールで正しいResult/doneへ接続する。コピー終端finalStageも保持。
単体Lean検査と全体build成功（9098 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**準備の基本操作数とDPの有効tick数を混ぜて外側経過時間としない。**
controller mode grouping、準備中のCounter/InputHead全状態、外側tickとdebt収支・初期radius、
物理回路/FIFOがまだ残る。resetはここでは既存論理reset後を開始状態とし、そのheap実装は別。
最終PAL機械・正例期限は未完。

### 最新：同じSOURCE実行を12テープへlift、他テープ保存

ScaffoldLower.load_ops/rewind_opsでcontroller groupingを外して同じTape実行の基本操作列を導出。
SourceReady.place_program_opsは同じPlace.CopyとRewindからLoading.Runを構成し、
任意12テープ状態のSOURCEだけを正確なbounded payloadへ更新する。PCと他11テープはputで保存。
開始はSOURCEのLEFT/right設定後。基本操作数3m+2であり、controller tick数2m+3とは別。
単体Lean検査と全体build成功（9098 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

まだLOWER・SOURCE setup2操作・reset/startをこの同じ実行と合成していない。
次は既存Loading.load_programの組立てを使い、SOURCE側にplace_program_opsを差し込み、
最終全状態をScaffoldPreload.initialへ一致させる。その後DP予算契約へ。
controller全mode、heap/FIFO、debt/正例期限、最終PAL機械は未完。

### 最新：Place/InputHead walkerとSOURCE preloadの同一実行接続

新規 `GalilScaffoldSourceReady`：copy_resultは任意Copy実行から正確なコピー長・最終Tape・
finalStageを抽出。place_readyはPlace.runs/copy_soundを通し、同じwalker実行の出力Tapeを
Rewindへ接続。input_readyはInputHead.realize_copyでfocus/左右スタック更新へ持ち上げる。
入力の文字/gapを実際に読むCopy m+1 tickとRewind m+2 tick、正確なbounded payload、
final iff stream長≤span+1を保証。incoming列qは保存され、左移動guardも既存実現証明が保証。
単体Lean検査と全体build成功（9098 jobs、exit 0）、公理propext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

これはlogical InputHeadであり物理Ref/FIFOではない。全12テープのframe・LOWERとの合成、
mode/外側tick/debt/初期radiusの接続は残る。次は準備全体の初期/最終program状態を
既存ScaffoldPreload.initialへ同一状態として結び、DP開始へ渡す。
大定理・正例期限・最終PAL機械は未完。

### 最新：SOURCEコピー/homeを正確なDP preloadへ接続

ScaffoldLower.source_readyを追加。Counter.Copyでwork=span+1からm+1 tick、
実LEFT検査Rewindでm+2 tick、bounded((xs.take(span+1)).map symbol)を構成。
m=min(xs.length,span+1)。残りstreamとworkも正確に保持し、finalStage=true iff xs.length≤span+1。
単体Lean検査と全体build成功（9097 jobs、exit 0）、公理propext/Quot.soundのみ。
実行中プロセスなし。git diff --check成功。

LOWERの2r+3とSOURCEの2m+3は具体Counter/論理Tape操作として接続できた。
まだPlace/InputHeadのwalker実行、全プログラムの他テープframe、mode間遷移、
外側tick/debt収支をひとつの準備実行へ合成していない。入力streamはここでは引数。
既存Place.copy_sound/copy_counter/InputHead.realize_copyの接続を使えるが、
単に同じxsの名前を置くだけでwalker対応済みにしない。
最終PAL機械・正例期限は未完。

### 最新：LOWER書込みとhomeの具体テープ接続

新規 `GalilScaffoldLower`：LoadはCounter.positive/decとwrite8/moveRightを1 controller tickに
まとめ、終了tickでENDを書き込む。load_exactでr+1 tickの正確なテープを証明。
Rewindは実focus=LEFTを停止条件にし、既存Homeの移動数に終了判定1 tickを加える。
lower_readyはprepareのLEFT/right設定からLoad r+1、Rewind r+2で
DPのbounded(replicate r 8)を構成する。計2r+3 tick。
単体Lean検査と全体build成功（9097 jobs、exit 0）、公理propext/Quot.soundのみ。
root import済み。実行中プロセスなし。git diff --check成功。

準備コストのLOWER区間をCounter/論理テープ実操作へ接続できた。
残りはSOURCEコピー/homeとmode間の全状態合成、実外側tick/debt収支、初期radius条件。
物理StackPool回路・FIFO・最終PAL機械は未完。lower_ready自体はheap/circuit評価ではない。

### 最新：grow後のadvanceまで含むCounter収支

ScaffoldGrowにpaced_zero/paced_append/paced_stageを追加。
growAdv.length回のgrowと、その後のlaterAdv列を合成し、最終debt値を
初期debt+2*growAdv.length-(growAdv++laterAdv).count trueと証明。
grow終了後はwork=0でgrow更新せず、advanceのみ減算する射影モデル上の定理。
単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

これで実収支を構成する部品はgrow区間だけでなく後続区間にも使える。
**prepareはworkをlowerへコピーするため、このworkフィールドをそのまま実Search.workと同一視しない。**
後続区間ではgrowを再実行しないこと、debtのみの射影が正しいことを実mode遷移から示す必要がある。
double/restartを跨ぐ適用は不可。実stage時間・初期radius・正例期限・最終PAL機械は未完。

### 最新：初回barrierと後続stageの比較上界

AdvanceClock.first_stage_barrierは3*radius≤5*rとイベント列長≤63*(8*max(r,1))から、
delay2048/reset入口でradius+advance数≤2*max(r,1)を証明。r=0も含む。
first_stage_debtはCanonicalと実収支値=-radius+2*max(r,1)-advance数を前提にnegative禁止を導く。
later_stage_advancesはspan≥16、任意clock∈[1,2048]、列長≤63*spanからadvance数≤span/8。
clock=1で即比較が来る場合も含む。単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**source radius条件・実stage時間・実Counter収支は依然前提。**
それらをオンラインGalil全体から証明したわけではない。数値上のbarrier義務を明示条件から
解いた段階。次は準備/runtime/refinementで列長を、開始/advance/growで収支を満たす実traceを接続。
delay2048は新コスト用の候補設定でありScala既定を変更していない。
最終PAL機械・正例期限は未完。

### 最新：clock由来advance列とgrow収支の接続

新規 `GalilScaffoldAdvanceClock`：各tickの(available,eligible)から
available∧clock=1∧eligibleを出力するadvancesを定義。eligibleはSearch.tick後の
Search.active∧chain.idleに対応させる入力値。advances_length、advances_le_compares、
advances_budgetでreset間のadvance数*delay≤available数を証明。
grow_before_first_compareはes.length<delayかつgrow区間内ならadvance数0を導き、
実Counter収支へ接続してdebt=初期値+2*es.lengthを保証する。
単体Lean検査と全体build成功（9096 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

**eligibleが実Search/chain状態に対応することやreset境界は未接続。**
これは任意長stageのdebt非負性ではない。初期radius条件、grow完了後の準備/run時間、
比較回数の全区間合算が必要。次は短区間だけでなく全stageの収支を明示上界へ接続する。
正例期限・物理回路/FIFO/最終PAL機械は未完。

### 最新：grow中の外側advance列を含む収支

ScaffoldGrowにafterMatch/paced/paced_valuesを追加。positive(work)ならgrow更新し、
その後にBool列のadvanceがtrueならdebt.decするScala順序をモデル化した。
bs.length≤gなら、work=ofNat(g-bs.length)、span値=初期値+8*bs.length、
debt値=初期値+2*bs.length-bs.count trueを証明する。任意prefixに適用可能。
単体Lean検査と全体build成功（9095 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

終端prepare tickとその後の他modeはまだこの定理に含めない。
**bsが実Galilのcompare∧active∧chain.idleに一致することは未証明。**
次はMatchClockのcompare頻度とbs.count上界を接続し、終了tickを含む収支とdebt境界へ進む。
最終PAL機械・正例期限は未完成。

### 最新：growの二スタックCounter更新とtick収支

新規 `GalilScaffoldGrow` はCounter.inc反復add、work.dec/span+8/debt+2のstep、
positive guardを使うGrow関係を定義。grow_exactはwork=ofNat gから終了判定込みg+1回、
work=0、span値+8g、debt値+2g、Canonical保存を証明する。
初期debtは負でもよい。既存Counterの論理二スタック実装に基づき、Nat残量だけのモデルから一段接続。
単体Lean検査と全体build成功（9095 jobs、exit 0）、公理はpropext/Quot.sound。root import済み。
実行中プロセスなし。git diff --check成功。

**外側advanceMatchが途中に挟まる減少分はまだ含めない。**
最終prepare tickのcounterコピー・program.reset/loadや物理StackPoolも別契約。
次はgrow/debtの収支をcompare列と合成するか、lower/home/copy区間の具体counter/head距離を
PrepareClockへ接続する。正例期限・最終PAL機械は未完。

### 最新：準備モードのtick収支を定義・証明

GALIL_CLOCK.mdを読み、Scala Search.stepと照合。grow g回＋終了1、lower r回＋終了1、
lower_home r+1移動＋終了1、copy m回＋終了1、home m+1移動＋終了1で計g+2r+2m+7。
新規 `GalilScaffoldPrepareClock` はPhase/tick/remaining/advanceを定義し、
tick_decreasesとpreparation_ticksでこのdecodedカウント遷移のrun到達を証明した。
単体Lean検査と全体build成功（9094 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

**これは具体counter/tape/walkerのrefinement証明ではない。**
copyのmは実コピー長でありspanと同一視しない。終了理由（walker=None/work=0）、
各head距離、grow/span/debt更新を既存Copy/Counter/Loadingと接続する必要がある。
次はこの収支をspan=8*max(r,1)、m≤span+1へ特殊化しTimingCostへ接続しつつ、
実モード不変条件を証明する。doubleは同じ回数式に入れられてもdebtのquarter更新は別。
正例期限・回路/FIFO・最終PAL機械は未完。

### 最新：主経路のclock導出を再確認、新コストの数値校正

重要な訂正：`ScaffoldCircuitGalil.buildOnlineWithViews` は `GalilClock.derive(quantum)` の
matchDelayを使う。build/buildWithViewsの引数既定256と混同しない。
Scala GalilClock.scalaはFppCost.boundsの旧ledger由来DP係数からstage/clockを導出している。
今回の証明済みDP係数3186/1683を使うなら、quantum64のfirst式はceilで63、
24*63=1512を覆う最小2冪delayは2048。**現Scalaコードの数値を変更したわけではない。**

新規 `GalilScaffoldTimingCost`：runBudget(span)=ceil((3186*(span+1)+1683)/64)、
runBudget_sufficient、first_stage（span≥8で19*span/8+10+runBudget≤63*span）、
later_stage（span≥16で11*span/4+10+runBudget≤63*span）、delay_calibrationを証明。
除算はNat除算。実spanは初回8の倍数・以後倍増だが、そのschedule不変条件は別。
単体Lean検査と全体build成功（9093 jobs、exit 0）、標準公理のみ。root import済み。
実行中プロセスなし。git diff --check成功。

これは**数値式の校正であり、実stage処理の19/8・11/4上界を証明したものではない**。
次はdocs/palindromes-in-peg/GALIL_CLOCK.mdのsource contractと実Searchの
grow/lower/rewind/copy/home/runのtick数を対応させ、外側advanceMatchとの収支を証明する。
旧delayを維持するには旧小さいコストの証明が必要か、別のより鋭い上界が必要。
大定理・正例期限・物理回路/FIFO/最終機械は未完。

### 最新：runStepのdebt assertionを含む安全な呼出し列

SearchRunにfinish_debt、SafeCalls、calls_safe、quantum64_safeを追加。
SafeCallsはenabled∧done時のScala negative禁止を各呼出しに含む。
finishはdebtを保存するので、入口debtがCanonicalかつ非負なら、既存の有界Callsを
安全な呼出し列へ変換し、正しいResult/done/run退出とdebt保存を保証できる。
単体Lean検査と全体build成功（9092 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**入口非負性は仮定であり、online全体から導出したわけではない。**
外側advanceMatchが呼出し間にdebtを減らす履歴には、そのまま適用できない。
次は外側tick間のadvanceMatch回数とrun時間上界の収支へ戻ること。
Search.startのdebt=-radiusを非負扱いしない。debt条件を名前変更して解決済みにしない。
外側tick/正例期限・物理回路/FIFO/最終PAL機械は未完。

### 最新：run呼出し列の有界終了と残余呼出しの不変性

SearchRun.quantum64_exitsは、具体DP preloadとmode.runから
64*(50*N+27)呼出し枠でCallsの終了状態がprogram.done=true、mode≠run、正しいResultを持つと証明。
calls_stoppedは、入口mode≠runならCallsがSearch状態とprogram状態を両方保存すると証明。
単体Lean検査と全体build成功（9092 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

注意：**runStep呼出し列の定理であり、外側tick全体の定理ではない。**
外側tickのstepは非runモードでgrow/lower/copy/wait/double等を動かすため、
calls_stoppedを外側tickの停止と誤解しない。次は入口running保存を持つquantum block対応、
停止に至るまでの外側tick列、その間のdebt/advanceMatchを接続する。
正例期限・物理回路/FIFO・無条件PAL∈PEGは未完。

### 最新：run modeとdoneの対応を呼出し列へ接続

新規 `GalilScaffoldSearchRun`：finish_run_iff、run_call、Calls、realize_callsを追加。
入口で `s.mode=run ↔ x.done=false` のとき、program Tickの後に実finish分岐を適用しても
同じ対応を保つ。GuardedRunの任意呼出し列を、mode.runでguardしfinishを更新するCallsへ
同じ最終program状態のまま実現する。単体Lean検査と全体build成功（9092 jobs、exit 0）。
公理はpropext/Quot.soundのみ。root import済み。実行中プロセスなし。git diff --check成功。

これはrunStepのdecoded program/finish部分。**debtのrequireはまだ含めていない。**
外側tickの入口running保存、非run時の他mode dispatch、各段階の初期run/done対応、
debt境界/正例期限、物理回路/FIFO/最終機械は未完。
次はquantum64_correctのGuardedRunをrealize_callsへ渡し、外側tick境界のrun維持と
停止後slotの無効化を実Scala tickの入口running条件に対応させる。

### 最新：done後の呼出し抑制とquantum64予算

ScaffoldCircuitSearch.scalaのtick/runStepを再確認：入口runningを保存し、step(enabled)の後、
1 until quantumでenabled∧入口running∧現在mode.runを使う。runStepはprogram.step後に
doneならfound/missed/double/waitへ遷移する。
`GalilScaffoldDpCost.GuardedRun` は要求slotのenabledを `b && !x.done` にする実行関係。
`guard_run` で通常Runから同じ終了状態への変換を証明し、`quantum64_correct` で
**64*(50*N+27)個の要求slot**が正しいDP終了に十分と証明した。
単体Lean検査と全体build成功（9091 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**実Search.tickの経過時間を50*N+27以内と証明したわけではない。**
GuardedRunはmode/finishをまだ持たない。次はrun入口からdoneまでmode.runが保持され、
各有効外側tickの64 slotがこの関係に対応することをSearchFinishと結ぶ。
非run→runへの移行tickでは入口running=falseなので追加63呼出しは無効、という差も扱う。
debtのrequire条件・正例期限・物理回路/FIFO/最終機械は未完。

### 最新：明示DP上界をScaffoldの有効tick契約へ接続

`GalilScaffoldDpCost.scheduled_correct` を追加しroot import済み。
具体的な論理テープpreloadから、任意Boolスケジュールbsに対し
`3186*w.length+1683 ≤ bs.count true` ならRunがdone=trueかつ正しいResultに到達する。
DPの同一実行コストとrealize_completed/scheduled_completedを合成。
単体Lean検査と全体build成功（9091 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**これは実Search.tickがその数の有効呼出しを供給する証明ではない。**
次はScala ScaffoldCircuitSearch.tick/runStepのmode・enabled列とquantum呼出し数を形式化し、
実経過tickに対するDP進捗をつなぐ。debt境界/正例期限・物理回路/FIFO・最終PAL機械は未完。

### 最新：DP正しさと時間上界を同じ実行に統合

`GalilDpCost.initial_correct_cost` は実初期状態からのCompletedと
`GalilDpCorrect.Result w lower 0 y`（候補最小性・正確なOUTPUTまたは候補不在）、
**`qs.length ≤ 3186*w.length+1683`** を同じy/qsについて保証する。
`execute_unique` / `completed_unique` を追加し、既存dp_wellFormedのread-key Nodupから
終了状態の決定性を証明して、コスト実行と正しさ実行を一致させた。
単体Lean検査と全体build成功（9090 jobs、exit 0）、標準公理のみ。
GalilDpCostにCorrect/ScaffoldNextPcを追加import。実行中プロセスなし。git diff --check成功。

次はこの定理をScaffold側DP実行・Search.tickの実enabled列へ渡し、
grow/double/compareとdebtの境界上界・正例期限へ接続する。
旧時間定数をこの新しい上界で無検証に再利用しない。
無条件PAL∈PEGはまだ未完成。回路の物理解釈・実スケジュール・FIFO・最終機械も残る。
下の「Resultとの同一実行接続が残る」は解消済みの履歴。

### 最新：DP全体の停止コストを証明

新規 `GalilDpCost.initial_terminated_cost` は任意Fin3入力・任意lowerについて、
実12テープ初期状態からのCompleted、終了PC346または347、
**`qs.length ≤ 3186*w.length+1683`** を保証する。root import済み。
準備3168*N+1661、start6命令、長入力next_candidate15命令＋loop18*(N-1)+19、
短入力short_next≤16を合成。単体moduleおよび全体build成功（9090 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

**次は正しさResultとこの時間上界を同じ実行へ接続する。**
既存 `GalilDpCorrect.initial_correct` は別の存在実行を構成するため、単に両定理を
並べて同じ終了状態と見なさない。選択肢はcorrect_loopへコストを保持して再合成、
または実codeのread-key一意性（ScaffoldNextPc.dp_wellFormedが既存）から
Completedの決定性を証明して終了状態を一致させること。まだどちらも実装していない。
Galil期限・実回路/FIFO/最終機械・無条件PAL∈PEGは未完成。

### 最新：DP準備のコスト付き接続が完了

`GalilDpPreparedCost.prepared_cost` を新規追加しroot import済み。
実12テープ初期状態からPC372まで、既存preparedの全テープ/head契約を保ち、
**`qs.length ≤ 3168*w.length+1661`** を証明。marked変換2倍＋dispatch1命令。
単体Lean検査と全体build成功（9089 jobs、exit 0）、標準公理のみ。
実行中プロセスなし。git diff --check成功。

次は `GalilDpStart.long_terminates` / `short_terminates` と同じ構成で、prepared_costを使う。
`GalilDpLoop.terminates` は既に `18*(w.length-h)+19`、`short_next` は16命令上界を持つ。
`next_candidate` と `start_run` も実traceがある。既存Startはこれらのコストを捨てているので
保持して全DP上界を作る。正しさResultとの同一実行への接続も忘れない。
DP全体コスト・Galil期限・無条件PAL∈PEGはまだ未完成。

### 最新：9テープmarked FPPの全体コストを接続

新規 `GalilFppMarkedCost.lean` の `marked_fpp_exact_cost` は、任意Fin3入力について
実9テープ初期状態からCompleted、pc=0、SOURCE/MARKS head=0、SOURCE保存、
正確なmarksテープ、および **`qs.length ≤ 1584*w.length+830`** を同時に保証する。
準備24*N+42、prepared word長2*N+1、7テープ390*長さ+4、命令変換高々2倍を合成。
単体Lean検査と全体build成功（9088 jobs、exit 0）、標準公理のみ。root import追加済み。
実行中プロセスなし。git diff --check成功。

次の具体箇所：`GalilDpPrepared.prepared` と同じ構成でmarked_fpp_exact_costを用い、
`GalilDpSimulation.completed` の既存2倍上界を保持する。
dispatchは追加1命令なので、DP準備部分は **3168*N+1661** が候補上界。
まだこのDPコスト定理は書いていない。DP探索自体のコスト・Galil期限も未接続。

### 最新：FPP全体の線形時間上界が閉じた

`GalilFppGenerationCost.initial_completed_cost` は任意の `w : List (Fin 4)` に対して、
実Scala由来FPP命令表の `Completed code (initial w) qs y`、正しいborder列出力、
終了pc=0/A-head=0、**`qs.length ≤ 390*w.length+4`** を同時に証明する。
初期化・全入力処理・失敗探索・出力・haltを含む。空入力も含む。
`process_prefix_cost` の帰納ではB advanceの実2命令をpotential付きで保守的に24計上し、
一文字366と合わせ390。`process_all_cost` ではReadyのS≤failureを用い、残ったfailure
potentialで出力側25*failure+2を払う。したがって全体で390*N+4となる。
追加3定理の単体Lean検査と全体build成功（9087 jobs、exit 0）。
公理はpropext/Classical.choice/Quot.soundのみ。git diff --check成功。実行中プロセスなし。

**次はこの全体コストをmarked FPP/DPの実行へ持ち上げ、Galilの正例期限へ接続する。**
旧132*N+12の定数を証明したわけではない。既存quantum/matchDelayで十分かも未検証。
無条件PAL∈PEGは未完成。物理回路・実スケジュール・FIFO・最終機械への接続も残る。
以下の「FPP全体線形上界は未完成」は過去の記録で、この節が更新する。

### 保存後の再開で更新：input_stepの償却上界まで証明済み

`GalilFppGenerationCost.lean` に `execute_potential`、`steps_potential`、
`search_supply_cost`、`input_step_cost` を追加。下に記した未実装案の1〜2と終端合成は完了した。
探索の係数は348。入力一文字の機能契約（Ready/Supply/生成位置/入力テープ/B-head保存）を保ち、
`qs.length + 5*y.pos 5 + 11*x.pos 3 + 348*failure w (N+1)
 ≤ 366 + 5*x.pos 5 + 11*y.pos 3 + 348*failure w N`
を証明した。両分岐を含む実Stepsの上界であり、抽象コストへの置換ではない。
単体Lean検査および全体build成功（9087 jobs、exit 0）、追加定理は標準公理のみ。
実行中のLean/buildプロセスなし。

**次は `advance_input` と `process_prefix` へ持ち上げ、入力列全体でpotentialを相殺する。**
advance_inputの既存契約にはBACK位置保存が明示されていないので、実2命令から保存を取り出すか、
steps_potentialで保守的に計上する。初期化とChain出力まで含めたFPP全体上界はまだ未完成。
旧132*N+12やGalil正例期限は未証明のまま。以下の「今回証明コード変更なし」は最初の保存時点の記録。

今回の依頼は進捗の保存。証明コードは追加せず、以下を引き継ぐ。
**下の時系列ログにある「次は」「未証明」は当時の状態。現在の優先順位はこの節を正とする。**

### 到達点と未完了

- 大定理は未完成。`lean-pal/PalPeg/Main.lean:43` の `pal_in_peg_of_structured` は、具体的な構造化機械とPAL認識証明を引数に取る条件付き定理のまま。
- 実Scala由来のFPP/DP命令表、FPPの停止・生成、DPの候補探索正しさは証明済み。decoded制御からheap実行への局所接続もあるが、実bit回路全体の完成ではない。
- 最新の完了箇所は `GalilFppGenerationCost.lean` の `hit_ready_cost` と `zero_miss_supply_cost`。両終端分岐で、機能契約に加えて同じ償却上界を保持した：
  `qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 18 + 5*x.pos 5 + 11*y.pos 3`。
  BACKはテープ5、Sはテープ3。zero_missの実命令数は8、BACK増加は2。
- `GalilFppReadCost` / `GalilFppSupplyCost` / `GalilFppGenerationCost` は `PalPeg.lean` にimport済み。
- **失敗探索と終端分岐を合わせたinput_stepのコスト、FPP全体線形上界はまだ未証明。** さらにGalilの進捗・正例期限、物理field/bit回路、実制御スケジュール、入力FIFO、具体初期heap、buffer/packから最終機械への接続が残る。

### 次の具体的な一手（未実装の案）

直前は `GalilFppRetry.lean` の失敗探索を読み、`GalilFppInstruction.lean` の
`Execute` / `Steps` を調べるところで停止した。新しい証明の書きかけはない。

1. `Execute` は1命令で高々1ヘッドを1動かすので、BACK/Sの重み付き変化について
   `5*y.pos 5 + 11*x.pos 3 ≤ 11 + 5*x.pos 5 + 11*y.pos 3`
   をケース分けで証明できるか確認する。`Steps` へ帰納して
   `qs.length + 5*y.pos 5 + 11*x.pos 3 ≤ 12*qs.length + 5*x.pos 5 + 11*y.pos 3`
   を導く方針。**この補題はまだ書いていない。**
2. `GalilFppGeneration.search_supply` は既に `qs.length ≤ 29*(failure w N-r)` を持つ。
   上記が通れば探索を係数348のpotential上界にでき、終端分岐の固定費18と合成できる。
3. hitでは次failure=r+1、missではr=0かつ次failure=0を使い、failureにも重みを付けて
   入力列に沿って償却する。`advance_input` の2命令、初期化、最後のChain出力も計上する。
4. これは粗い線形上界を先に閉じる案。**Scala側の旧132*N+12や33*N+3を証明したことにはならない。**
   quantum=64 / matchDelay=256で期限が満たせるかは、得た定数で別途検証が必要。

### 検証と作業状態

- 直前の検証記録：全体 `lake build` 成功（9087 jobs、exit 0）、`git diff --check` 成功。
  印字した追加定理の公理は標準公理のみ。今回の文書保存では全体buildは再実行していない。
- 今回、上記2定理の現物・root import・条件付き最終定理を再確認。実行中のLean/buildプロセスなし。
- commitしていない。多数の既存変更・untrackedファイルをそのまま保持すること。
- 再開は本節→対象3 Costファイル→Generation.search_supply/input_step→Instruction.Execute/Stepsの順で十分。
  下の長い履歴を全部読み直す必要はない。サブエージェントは使わない。

## 作業履歴（新しい順。古い未完了記述は上のスナップショットを優先）

### 最新作業：zero_missも同じ償却形へ

GenerationCostに `zero_miss_supply_cost` を追加。比較4命令と2回のenqueue（各2命令）を
実行合成し、Ready 0/Supply/生成位置/B-head保存を保証する。
命令8＋BACK高さ増加2×potential5で18となり、
`命令数 + 5*終了BACK高さ + 11*開始S位置 ≤ 18+5*開始BACK高さ+11*終了S位置`。
一致分岐と同じ形式になった。次の未接続点は失敗探索の全体コストとinput_stepへの合成。
全体build成功（9087 jobs、exit code 0）、印字した公理は標準公理のみ。`git diff --check`成功。
実行中プロセスなし。

### 最新作業：一致分岐のReady復元とS位置による償却

`GalilFppGenerationCost.hit_ready_cost` を追加。比較2命令をSupplyCostの一致分岐へ合成し、
次入力用Ready/Supply/入力head保存を保ったまま
`命令数 + 5*終了BACK高さ + 11*開始S位置 ≤ 18 + 5*開始BACK高さ + 11*終了S位置`
を証明する。`開始S + delta(failure,p) = 終了S`をReadyから導出し、候補依存deltaを位置差へ変換した。
leaf検査成功、標準公理のみ。
全体build成功（9087 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

次はsearch_supplyの失敗探索とzero_miss分岐にも位置/potential付き上界を付け、input_stepへ合成する。
一致分岐だけなので、全入力・FPP全体の線形上界はまだ未完成。

### 最新作業：一致分岐のSupplyコスト

`GalilFppSupplyCost` を追加。`scan_candidate_cost` は既存Supplyの候補条件からscan償却上界へ接続。
`matched_lazy_cost` はPC62からのenqueue・C移動・scanを合成し、
`qs.length + 5*y.pos 5 ≤ 11*delta(failure w,p)+16+5*x.pos 5` を保証する。
16はscan固定費8＋実命令3＋BACK増加potential5。
`matched_generated_cost` は実生成位置と次failureの条件から同じ上界を保つ。
機能契約（Supply、C/S位置、他テープframe）も保持している。
全体build成功（9086 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

次はGeneration.hit_ready/input_stepへつなぎ、失敗探索で増えるBACKとA/C/Sの移動を合算する。
delta(p)は処理入力番号Nのdeltaとは限らないので、単純なΣdelta(N)への置換は不可。
実際のC/S移動・fallback差との償却が必要。FPP全体線形上界は依然未完成。

### 継続作業：read/scanコストの持ち上げ

`GalilFppReadCost.lean` を新規作成（既存build中に対象ファイルは変更せず、未importの新ファイルで作業）。
dequeue_all_cost、forward_blank_cost、read_cost、scan_costを記述。
六つのread instanceへ7+BACK potential、forward readへ8+potential、delta scanへ11*d+8+potentialを渡す。
旧buildは9084 jobsで成功し終了済み。新ファイルのleaf検査も成功（4定理とも標準公理のみ）。
root importを追加。次はSupply/Generationのmatched/input_stepへコストを持ち上げ、
enqueueのpotential増加とfailure差・delta総和を合算する。全体線形上界はまだ未完成。
最新全体build成功（9085 jobs、exit code 0）。`git diff --check`成功。実行中プロセスなし。

### 最新作業：FPP dequeueの償却コストを復元

FPP全体コストへ戻った。`search_supply` は29*(failure差)の上界を持つが、
LazyForward/Supply/Generationの上位契約はmaterializationの命令数を捨てている。
`GalilFppMaterialize` に `stack_height` と `dequeue_cost` を追加し、既存証明を強化した。
同じ実行結果・Regionに加え `qs.length + 5*y.pos 5 ≤ 7 + 5*x.pos 5` を保証する。
FRONT非空時は5命令でBACK不変、空時は全BACK補充の5*長さ+7をBACK高さの減少で支払う。
旧 `dequeue` は互換wrapperとして残した。leaf検査成功、標準公理のみ。
Materialize変更後の全体buildは9084 jobsで成功。旧session29724は終了済み。
今回の`git diff --check`は成功。

**FPP全体の線形時間上界はまだ未完成。** 次はReadInstances.dequeue_all/forward_blank、
LazyForward.read/scanへこのpotential付き上界を落とさず持ち上げ、enqueueの増加分と合算する。
単にqueue長に比例する上界を各readに掛けると二次上界になるので避ける。

### 最新作業：match clockの比較回数上界

Galil側を確認。search.tickはcompareより前に実行され、advanceSearchは
compare ∧ search.active ∧ chain.idle。compareはavailableなscanでclock=1の時だけ。
clockはmatchDelay周期で減少し、restart/replay_start時にmatchDelayへ戻る。
`GalilScaffoldMatchClock` の `run_invariant` は任意available Bool列でclock範囲と収支
`available数 + 最終clock = 初期clock + compare数*delay` を証明。
初期clock=delayなら `compare_budget` / `compare_remainder` により
`compare数*delay ≤ available数 < (compare数+1)*delay`。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9084 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

これはclock reset間のdecode済み更新。advanceSearchがcompareの部分列である実イベント対応、
search処理進捗・DP/FPP全体時間・restart境界を接続してdebt境界上界を導く作業は残る。
比較頻度だけでdebt非負性や正例期限が閉じたとは言わない。

### 最新作業：debt非負性の必要な範囲と収支

Scalaの全debt更新を確認。startはradiusのpos/negを交換しdebt=-radius、advanceMatchは
radius.inc/debt.dec、growはdebt.incを2回、double中はquarterEndごとにdebt.incを1回。
**debtが常に非負という不変条件は誤り。** 非負性が必要なのはrunStepのfinished時とwait dispatch時。

SearchFinishに `initialDebt` / `initial_balance` / `advance_balance` / `grow_balance` /
`quarter_balance` を追加。debt+radiusはstartで0、advanceで不変、growで+2、quarterEndで+1。
`boundary_guard` はこの収支とradius≤creditsから既存のnegative禁止条件を導く。
まだ全履歴の収支定理・finished/wait時のradius≤creditsというスケジュール上界は未証明。
この上界を仮定の名前変更だけで解決済み扱いしない。Galil側のadvanceSearchと実処理時間を接続する必要がある。
全体build成功（9083 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

### 最新作業：Search.runStep停止後分岐とDP結果

`GalilScaffoldSearchFinish` を追加。Scalaの11 mode、finalStage/span/work/debt/quarterを
持つStateで、program.step後のfinish分岐を記述。enabledかつdoneで、PC346→found、
それ以外はfinalStage→missed、debt.zero→double、残り→wait。
doubleではwork=旧span、span.reset、quarter=0も反映する。
`result_found` は既存DP Resultの下でfoundと候補存在の同値、`failed_no_candidate` は
PC347の現在DP窓内の候補不在を証明する。`debt_guard` はCanonicalかつ非負のdebtで
Scalaのnegative禁止条件を満たすことを示す。
root import後の全体build成功（9083 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

まだpost-program-stepの論理Stateであり、heap側Search counter全体や実mode/Exprには未接続。
finalStage/debtの正しさ・非負性をonline全体から導出する証明、次段階の進捗/期限も残る。
現在窓の候補不在をPAL全体の不受理と報告しない。

### 最新作業：単一ノードinstruction blockとsuffix保存

RawScheduleの `run_other` は指定列にない全heapセルの保存。
`block_suffix_frame` はinstruction prefix終了以降のslot（別ノードを含む）の保存。
`realize_block` は任意Control.Runを同一ノードのslot0..bs.length-1で実現し、
初期prefix未使用性だけから実行とcontroller suffixのセル保存をまとめて保証する。
leaf検査成功、標準公理のみ。
全体build成功（9082 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

Scala `ScaffoldCircuitSearch.tick:144–147` はstep内runStepと `1 until quantum` の追加runStep。
`runStep:68–69` はprogram.stepを一回呼ぶ。正のquantumなら構文的にquantum呼び出し。
ただしこの呼び出し列のenabled/mode更新・controller操作・実instructionIndexとの対応は
まだLeanに接続していない。suffixセル保存はcontroller実行自体の正しさの証明ではない。

### 最新作業：事前固定したAddress列でraw Runを実現

`GalilScaffoldRawSchedule` を追加。`tick_other` は指定割当Address以外のheapセルが不変。
Address列を明示する `Run` と `realize_run` は、Bool予定と同長・Nodup・初期未使用の
固定Address列で任意Control.Runを実現する。途中で新規ノードを選び直す必要はない。
`block node quantum slots hq` は同一ノードのslot0..quantum-1を並べ、長さ・Nodup・
instruction prefix内に収まることを証明する。
root import後の全体build成功（9082 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

実Scalaのtick呼び出し数とinstructionIndex/quantumの対応、controller suffixとの
実割当干渉、複数ノードのスケジュールへの接続はまだ必要。固定列の初期未使用性は前提。
bit回路・field decoding・online全体と最終PEGは依然として未完。

### 最新作業：pause付きraw実行全体と停止への接続

RawTickに `loop_finite` / `tick_finite`、raw `Run`、`realize_run` を追加。
任意の既存Control.Runを同じBool予定列で実現し、最終状態の表現対応とheap有限性を保存。
`scheduled_completed` は既存Program停止traceと、十分な有効tickを持つ任意pause列から、
raw heap実行のdone=true・同じ最終テープ解釈を保証する。
全体build成功（9081 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

WellFormed/初期heap表現/有限性/slots>0は前提。各tickで未使用ノードのslot0を選ぶ存在証明で、
実Scalaの固定slot割当や時間期限を証明したわけではない。bit回路・field decoding・
online Galil/FIFO/packing/最終PEGとの接続は残る。

### 最新作業：decoded raw tickと既存制御を合成

`GalilScaffoldRawTick` にheap Config+doneのMachineと `tick` を追加。
disabled/doneなら不変、haltならPC/テープを保存しdone=true、他命令なら入口focusから
次PCを計算して実順序のテープfoldを適用する。PCまたはread target欠落はNone。
`tick_execute` / `realize_tick` は既存 `GalilScaffoldControl.Tick` のidle/halt/executeをすべて実現する。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9081 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

fresh Addressとread表WellFormedは前提。tick関数自体はallocation/left guardを検査する関数ではなく、
対応する合法実行に対してrefinementが成立する。実Value/Expr bit評価・field decodingとの接続、
全pause付きRunへの持ち上げ、実slot schedule/時間上界はまだ未完。
decoded tickの完成を実Scala回路全体の完成と同一視しない。

### 最新作業：target別イベント集約とlookupの同値

NextPcに `lookup_sound`（lookup結果は実read表の要素）、`Forward`、`TargetEvent` を追加。
TargetEventはScala forward(target,event)のtarget別OR集約を存在量化で表す。
`targetEvent_iff` はWellFormedな選択命令について、targetイベント有効と
active=trueかつlookup/直接targetの計算結果との同値を証明。
`target_unique` は異なる二つのtargetが同時に有効にならないことを導く。
leaf検査成功、印字した公理は標準公理のみ。
全体build成功（9080 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

decode済みPC/focusでの意味論的な集約対応まで。Value(nextPc)のbit符号化・validity、
実Expr OR評価、done/halt更新を含むraw tickとの合成は未完。

### 最新作業：次PCをread表から計算

`GalilScaffoldNextPc` を追加。`lookup` はread表から記号のtargetを返す。
`WellFormed` はread表の記号列Nodup、`lookup_mem` は表内の分岐とlookup結果の一致。
`next_execute` は既存命令実行の次PCを入口focusから計算する。
`realize_next` は計算されたPCでraw tape loopを更新し、既存結果の表現対応を保証する。
`dp_wellFormed` は実 `GalilDpCode.code` の全373命令を `by decide` で検証済み。
leaf検査成功、標準公理のみ。
root import後の全体build成功（9080 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

**ScalaのnextPcターゲット別イベント集約とlookupとの同値はまだ未証明。**
done/halt更新、active/doneを含むraw tick、bit回路のValue選択・validity、field decodingも残る。
lookupの決定性をbit回路全体の検証と取り違えない。大定理はまだ未完成。

### 最新作業：write→left→rightの実順序を合成

`GalilScaffoldRawTapes` を追加。decode済み命令とactiveを入口snapshotとして固定し、
各テープでwriteGroup→moveGroup false→moveGroup trueを実行するfoldを定義。
`loop_write` / `loop_move` は一回のheap操作へ簡約、`loop_read` / `loop_halt` /
`loop_inactive` はテープ無変更を証明する。
`realize_loop` は既存List Programの任意非halt実行に対し、次PCをその意味論から与えれば
この具体的順序のheapループが結果を表現することを証明する。

**nextPcはまだ計算していない。** read分岐のtarget集約・PC/done更新・イベントのdecodeから
この命令snapshotへの対応、bit回路/field get-putは残る。fresh Addressも引数。
初回leaf検査は成功。大定理は依然として未完成。
`realize_loop` のpc射影の型合わせを `GalilScaffoldProgram.changed` の展開で修正し、
最終全体build成功（9079 jobs、exit code 0）。印字した公理は標準公理のみ。
`git diff --check`成功。実行中プロセスなし。

### 最新作業：writeイベントと全テープwriteループ

`GalilScaffoldWriteGuards` を追加。`WriteEvent` はcode.indicesのイベント集約、
`selected_write` は実write命令のtape/symbolとの一致。`writeLoop` はdecode後の入口PCを
固定した全テープfoldで、`loop_write` / `loop_heap_write` が一回の選択writeへ簡約する。
`loop_inactive` / `loop_nonwrite` はinactiveまたは非write命令時の無変更。
root import済み、全体build成功（9078 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

移動ループとはまだ別foldで証明している。Scalaのtapeごとのwrite→left→rightという
interleavingへの合成、nextPc/read分岐・done更新、Value/Exprのbit意味論との接続は残る。
これをraw instructionStep全体の完成と報告しない。

### 最新作業：具体的テープ列と非move時の不変性

MoveGuardsの `keys n = (List.finRange n).product [false,true]` はScalaの各テープ左→右の順序。
`keys_nodup` / `mem_keys` を証明し、`concrete_loop_move` から列のNodup/被覆前提を除いた。
`inactive_loop` はinactive時の無変更、`nonmove_loop` は選択命令がmoveでなければ
全移動ループが無変更であることを証明（read/write/haltにはコンストラクタ不一致で適用可能）。
初回leaf検査成功、標準公理のみ。
全体build成功（9077 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

次はwriteイベント集約・PC/done更新とheap実行の合成。Value/Exprのbit評価、field get/put、
instructionIndex/quantumと実割当、全体online正しさ・時間上界・最終PEGは依然未完。

### 最新作業：moveイベントの逐次ループ合成

`GalilScaffoldMoveGuards` に `dispatch` / `dispatch_absent` / `dispatch_once` を追加。
重複しないtape/directionキー列に選択キーが含まれれば、全ループはその一回の操作に一致。
`dispatch_heap_move` が共有heap moveへ特殊化する。
`eventLoop` は命令入口のcode/pc/activeから集約したMoveEventを評価するfold。
`eventLoop_selected` / `eventLoop_once` が実イベント条件を選択キー一致へ変換し、全foldを簡約する。

キー列のNodup/被覆はまだ引数。Scalaの `tapes.indices` × 左右という具体的列への特殊化、
inactive/halt/read/write時のループ不変、PC/done更新、Value/Exprのbit評価はまだ残る。
guardは入口snapshotに固定している。実回路のsnapshot意味論との対応も別途必要。
最終全体build成功（9077 jobs、exit code 0）、印字した公理は標準公理のみ。実行中プロセスなし。

### 最新作業：raw命令の共有slot排他条件

`ScaffoldCircuitProgram.scala:74–109` を確認。raw instructionStepはactiveかつpc=iの
イベントをtape/direction別に集約し、その呼び出しの共通slotで左右moveを発行する。
`GalilScaffoldMoveGuards` の `MoveEvent` / `event_iff` はこの集約を具体的PCへ簡約。
`move_unique` は有効なtape/directionが高々一つ、`selected_move` は選択moveとの一致を証明。
`exclusive_writes` は排他的な2分岐の同一Address書き込みが選択側のみの書き込みに一致する。

これは具体的にdecodeされた単一PCを前提にした証明。Value/Exprのbit評価・validity、
全tapeループのfold、shared slotのinstructionIndex/quantum上界、controller extraMovesとの
分離、Circuit field get/putへの接続は未完。coarse block実行にはそのまま適用しない。
初回leaf検査成功、印字した公理はpropextのみ。
root import後の全体build成功（9077 jobs、exit code 0）。`git diff --check`成功、実行中プロセスなし。

### 最新作業：heap上の停止traceへの持ち上げ

`GalilScaffoldHeapProgram` に `FiniteHeap`（有限ノード境界以降は未使用）と
`put_finite` / `execute_finite` を追加。`Completed` は同じcode/PC traceを使うheap実行。
`realize_completed` は既存List Programの任意停止traceを、表現対応する有限heap初期状態から
同じPC列・最終List解釈で実現する。slots>0のみ要求し、各stepで新規ノードのslot0を選べる。
終了heapも有限である。leaf検査成功、標準公理のみ。
全体build成功（9076 jobs、exit code 0）、`git diff --check`成功。実行中プロセスなし。

**これは意味論的な割当の存在証明であり、実Scalaの固定ノード/slot配置と一致する証明ではない。**
有限heap初期状態の具体的構成、実Circuit field decoding、predicated schedule、実割当と
時間上界への接続は依然として必要。新規ノードを自由に取れることを実時間制約の解消とみなさない。

### 最新作業：共有heapのProgram命令対応

`GalilScaffoldHeapProgram.lean` を追加。Configは共有heap・pc・全テープrootを持つ。
`moved_right` / `moved_left` / `written_represents` は選択テープを更新し、他の全テープの
List解釈を保存する。`Execute` は同じ `GalilFppWide.Instruction` のread/write/左右moveを使う。
`realize_step` は既存 `GalilScaffoldProgram.Execute` の任意1命令をheap側へ持ち上げる。
左moveのroot非空guardとread分岐のfocus一致は表現関係から導出する。
root import済み。全体build成功（9076 jobs、exit code 0）、印字した公理は標準公理のみ。
実行中プロセスなし。

**fresh Addressはまだ引数。** 全実行列にわたる割当・停止traceへの持ち上げ、実Circuitの
field decodingとpredicated instruction選択、実slot割当の非衝突性は残る。
単一命令の対応をDP全体の物理実装証明と同一視しない。

### 最新作業：heap tapeを既存List tapeへ接続

`GalilScaffoldHeapTape.lean` を追加。左右Rootとfocusを持つTape、heap lookupによるtop、
pop/pushを合成した左右移動を定義。`right_represents` / `left_represents` は既存
`GalilScaffoldTape.moveRight/moveLeft`への対応を証明し、右側空ならblank、左側の合法guardも扱う。
`right_frame` / `left_frame` は他の任意rootのList内容を保存する。
`reset_represents` / `write_represents` も追加。resetはrootを切るだけでheapを消さない。

fresh Addressが前提（前項Allocatorのunused_freshで導出可能）。まだ実Circuitのfield
get/put・tag decodingとは未接続。次はこのheap tapeとProgram全テープ/命令実行の合成、
または実割当/field decodingの残前提を閉じること。新しい別構成へ乗り換えない。
leaf検査・root import後の全体build成功（9075 jobs、exit code 0）。印字した公理は標準公理のみ。
実行中プロセスなし。

### 最新作業：heap割当状態からfreshnessを導出

`GalilScaffoldHeap` に `Allocator`（heap/node/used slots）と `Bounded` を追加。
`unused_fresh` は現在ノードで未使用のslotが空であることを導出。
`allocate_bounded` / `nextNode_bounded` は同一ノードへの追加割当とノード進行で不変条件を保存。
`allocated_push` はこの導出を共有root保存つきpushへ接続する。
`initial_bounded` と `disabled_preserves` も追加し、空heapとdisabled書き込みを扱う。

**未使用slot条件そのものは依然として仮定。** Scalaのlayout/name/index→有限tag対応、
明示slotの再使用と互いに排他的なguardの扱い、実CircuitのNEW/field get-putへの接続が残る。
保守的な予約集合モデルを実Scalaの全ケースと同一とみなさない。
leaf検査と最終全体build成功（9074 jobs、exit code 0）。印字した公理は標準公理のみ。
実行中プロセスなし。

### 最新作業：共有heapのList解釈

`GalilScaffoldHeap.lean` はノード番号×有限slotをAddressとし、below pointer/tagを
一つのRootにまとめ、payloadを任意型としたheap解釈を追加する。
`Models` はrootからの有限List内容。`fresh_preserves` は未使用Addressへの書き込みが
全既存rootを保存すること、`push_with_alias` はpushと共有rootの内容保存、`pop` は
payload/belowの取り出し、`empty_iff` は空rootと空Listの対応を証明する。
根拠は `ScaffoldCircuitStructs.scala` のStackPool.allocateとStack.push/drop/copyFrom。
root import済み、全体build成功（9074 jobs、exit code 0）。印字した公理はpropextのみ、
または公理なし。実行中プロセスなし。

**未使用Addressの条件はまだ仮定。** 実回路のNEWノード・slot割当（同一ノード内の複数書き込みを含む）
がこの条件を満たすこと、tag選択とfieldのget/put、enabled=falseの挙動、既存Tape/Counter/InputHead
のList表現への合成は残る。これはStackPool全体の検証完了ではない。

### 最新作業：online head到達状態の配置不変条件

`GalilScaffoldInputTrace.lean` を追加。`Represents h word` は到着済み入力全体を
`xs.reverse ++ rs ++ incoming` と分解し、focus/左stackを`layout xs`、右stackを
`rs.map some`と対応づける。resetで成立し、append・右stack優先の右移動・FIFOからの
右移動・合法な左移動で保存される。`reachable_represents` は任意の到着/左右移動列に一般化。
`reachable_copy` はその到達状態から、別途layoutを仮定せずstack版copyが実行できることを証明。
この定理単独は停止・実行存在の契約であり、最終DP/PEG認識定理ではない。

**incomingを論理FIFOとして扱っている。Scala Queue.work/pop、物理Ref/StackPool、
predicated circuitとの対応は未証明。** copyFromの共有rootは物理層で扱う必要がある。
leaf検査・root import後の全体build成功（9073 jobs、exit code 0）。印字した公理は
標準公理のみ。実行中プロセスなし。

### 最新作業：focus・左右stackによるcopy実行

`GalilScaffoldInputHead.lean` を追加。`Head` は解釈済み入力参照（Option Fin2）のfocus、
左右Listスタック、抽象incoming Queueを持つ。`layout` は現在から左向きの文字列を
focusと「残りのsome列＋末尾none」の左スタックに配置する。
`moveLeft_at` はScalaと同じ「focusを右へpush、左をpopしてfocusへ」の意味を証明する。
`left_represent` はPlaceHeadのgap分岐を保ち、必要な左スタック非空条件も導出する。
`realize_copy` はPlace版copyの全実行をこの明示的stack版へ、同じ反復数・結果フラグ・
テープ・残量で持ち上げる。右スタックの更新は存在量化し、incoming Queueは不変。
leaf検査成功、印字した公理は標準公理のみ。root import済み、全体buildも成功
（9072 jobs、exit code 0）。`git diff --check`成功。実行中プロセスなし。

**まだ解釈済みListスタックであり、物理Ref/StackPoolの証明ではない。**
`layout` がreset・右移動・入力追加・copyFromで保たれる証明と、実Queue/物理セルのrefinementが残る。
この層の追加をonline入力供給全体の完成とは報告しない。

### 最新作業：letter/gap walkerの論理接続

`GalilScaffoldPlace.lean` を追加。根拠は `ScaffoldCircuitInput.scala` の
`InputHead` と `PlaceHead`、および `ScaffoldCircuitSearch.scala` のcopy分岐。
PlaceHeadは文字だけでなく隙間`s`を読む。gap=trueの左移動はheadを動かさずgap=falseへ、
gap=falseの左移動はInputHeadを左へ動かしてgap=trueへ進む。focus不在ならgapに関係なくNone。

`Place.letters` は現在文字から左向きの文字列を表す論理射影。`read_stream` / `left_stream` が
この2種類の移動と `s,letter,s,letter,...` のstreamを対応づける。
`runs` は任意Place/残量のcopy停止、`copy_sound` は既存Nat版copyへの実行対応を証明。
`copy_counter` は二スタックcounter版へ、`copy_ops` は原始テープ操作へ接続する。
**InputHeadの物理Ref、左右Stack、incoming Queueがこの射影を保つことはまだ未証明。**
したがってonline入力供給全体が完成したという意味ではない。次の実装接続ではこの表現不変条件が必要。
初回leaf検査、root import追加後の全体buildとも成功（9071 jobs、exit code 0）。
印字した4定理の公理は `[propext, Quot.sound]` のみ。実行中プロセスなし。

### 最新：Counterの修正・root検証完了

引き継ぎ後の継続で下記Counterエラーは修正済み。`zero_iff` / `negative_iff` の
`simp_all` 後に `omega` を追加し、leaf検査成功。
`GalilScaffoldCounter.copy_exact` を追加し、Nat版copyの正確なコピー範囲・残stream・残量・
finalStageを二スタックcounter版へ移した。root import済み。
**全体 `lake build` 成功（9070 jobs、exit code 0）。** 印字した公理は標準公理のみ。
実行中プロセスなし。次はonline walker・状態選択・物理StackPoolへの実接続。
Counterは依然として論理List表現であり、物理共有セルを検証したわけではない。

### 前回保存時点の記録（以下のCounterエラーは解消済み）

2026-09-14、ユーザーの引き継ぎ依頼に応じて証明追加を停止し、現物を再確認した。
**最新の作業ファイルは `lean-pal/PalPeg/GalilScaffoldCounter.lean`。未完成・root未import。**
今回 `lake env lean PalPeg/GalilScaffoldCounter.lean` を実行し、exit code 1を確認した。
現在実行中のLean/buildプロセスはない。過去のsession 44782を待つ必要はない。

CounterはScala `ScaffoldCircuitStructs.scala` のpos/neg二スタックを `List Unit` で解釈する。
`inc`/`dec`、整数値、Canonical（少なくとも片方が空）、正負・零判定、`ofNat`、
Nat版copyから二スタック版copyへの `realize_copy` を記述済み。
これは論理スタック表現であり、物理StackPoolの検証ではない。

確認した未解決ゴールは以下の4つだけ（このleaf検査の出力範囲）:

- 46行 `zero_iff`: `¬ -1 + -↑tail.length = 0` と `¬ ↑tail.length + 1 = 0`。
- 54行 `negative_iff`: `-1 < ↑tail.length` と `0 ≤ ↑tail.length + 1`。

両証明末尾の `simp_all [...]` の後に `omega` を適用するのが最初の修正候補。
**この修正はまだ実施・検証していない。** `inc_value` / `dec_value` / `realize_copy` の
公理出力は `[propext, Quot.sound]` だが、ファイル全体は失敗しているので完成扱いしない。

再開手順:

1. 上記2証明を修正し、Counterのleaf検査を通す。
2. 必要なら `realize_copy` と既存 `copy_exact` を合成し、残量・最終フラグまで明示する。
3. `PalPeg.lean` にCounterをimportし、全体 `lake build` と `git diff --check` を実施する。
4. 次の実接続はonline walker・状態選択・物理StackPool。以下の残件一覧に従う。

最後に確認済みの全体buildは **Counter追加前の9069 jobs成功**（以前の検証記録）。
今回の保存作業では全体buildを再実行していない。証明ファイルは変更せず、引き継ぎ文書のみ更新した。

**`GalilScaffoldLoad.lean`の旧型エラーは修正済み。** `load` / `load_source` / `load_lower`のleaf検査は成功し、root importにも追加した。標準公理のうち`[propext, Quot.sound]`だけに依存し、`sorryAx`はない。

修正は`home_exact`のcons枝で、`Home.left`の引数を`by simpa [moveLeft] using hr`として先に型合わせし、その後`convert`で結果のリスト・操作数を正規化したもの。古いエラーを再修正する必要はない。

継続して`GalilScaffoldLoading`を追加し、原始ロードをSOURCE/LOWERを持つプログラム全体へ接続した。
`load_program`は任意の旧状態を論理resetした後、LOWER→SOURCEの順で具体的DP初期配置へ到達する。
原始操作数は3*(lower+入力長)+8。`load_then_dp`がstartとpause付きの正しいDP実行へ接続する。
次はオンラインwalker・counter・copy/homeの状態選択回路との対応。供給payloadはまだ引数であり、controller全体の実装検証ではない。

続けて`GalilScaffoldCopy`を追加。論理streamと残量counterに対するguarded copyループの
コピー範囲・残stream・残量・finalStageを`copy_exact` / `final_iff`で証明し、
`copy_ops`で既存の原始操作へ、`copy_home`でbounded配置への巻き戻しへ接続した。
streamは読み取り順のList、counterはNatという論理表現。実walkerポインタ・物理counter・
predicated回路との対応は未完成。`finalStage`は残量0そのものではなく残stream空で決まる点に注意。

### 検証済みloaderの内容

`ScaffoldCircuitSearch.scala`のLOWER/SOURCEロードは、LEFTを書き、payloadをwrite+rightで並べ、ENDを書き、focusがLEFTになるまでleftする。

`GalilScaffoldLoad`には以下を書いた:

- `fill` / `fill_stack`: write+right列が左スタックへ逆順payloadを積む。
- `Run`: write/right/合法なleftの原始操作列。カウントはテープ操作数でありcontroller tick数ではない。
- `Home`: focus=LEFTなら停止、それ以外なら合法なleftを行うマーカー駆動ループ。
- `home_exact`: 内部payloadにLEFT=4がない場合の正確な巻き戻し。
- `load`: reset後のテープから`bounded xs`へ、原始操作数`3*xs.length+4`で到達する合成定理。reset操作自体のコストはこの値に含まない。
- `load_source` / `load_lower`: 実SOURCEのFin3記号列とunary下限へ特殊化し、LEFTがpayloadに含まれない前提を導出した。

これは供給されたpayloadのロード証明。オンラインwalker・work counter・状態選択回路が実際にそのpayloadを供給することは別途必要。

## 検証済みの到達点

以下はルートimport済みで、標準公理`propext`, `Classical.choice`, `Quot.sound`の範囲で検査済み。有限テストを一般証明の代わりにはしていない。

### 1. 実FPPカーネルとmarked FPP

- `GalilFppCode`: Scala由来の7テープ・228命令。`GalilFppGeneration`が任意入力の生成処理、`GalilFppChain.initial_completed`がborder列出力まで接続。
- `GalilFppMarked.prepared_kernel_exact`: `w ++ [#] ++ reverse w`のborderが、元入力の正の回文prefix長と過不足なく一致。
- `GalilFppMarkedCode`: `FppSubroutine.buildMarkedProgram("abs")`由来の9テープ・321命令、開始PC320。
- `GalilFppMarkTransform` / `GalilFppMarkSimulation`: 元の命令を実marked命令へ持ち上げる。A移動にMARKS移動を追加、emitをMARKSへの1書き込みに置換。
- `GalilFppPreparation`, `GalilFppPrepareCopy`, `...Rewind`, `...Cells`, `...Init`, `...Layout`: SOURCEだけの初期状態から準備・コピー・逆転・巻き戻しまで合成。準備は正確に`24*n+42`命令。
- **`GalilFppMarkedLayout.marked_fpp_exact`**: 任意の`List (Fin 3)`入力で実初期状態から停止し、MARKS全セルが正確。0位置LEFT、1..nは回文prefixなら1・それ以外0、n+1にEND、以後blank。終了PC0、SOURCE/MARKS頭0、SOURCE保存。
- **FPP全体の線形時間上界は未完成。** `GalilFppExecution.instructions_le_four_charges`は命令数≤4×ledger chargesを証明するが、全実行ledgerの線形上界がまだ必要。

### 2. 実DPの正しさ・最小性

- `GalilDpCode`: `DpFinite.buildDpProgram("abs")`由来の12テープ・373命令。開始320、成功halt346、失敗halt347、検索入口372。
- `GalilDpTransform`: 元321命令全検査、MARKS操作をSECONDにも実行する変換とFPP終了時の検索dispatch。
- `GalilDpSimulation`: marked FPPの任意実行をDPへ最大2倍の命令数で持ち上げる。
- `GalilDpFrames`: FPP領域で終了するprefixがLOWER/OUTPUT内容・頭を保存することを実コード領域の閉性から証明。
- `GalilDpPrepared.prepared`: SOURCEとunary LOWERのみを置いた実初期状態からPC372へ到達。両マークテープの正確さ、関連頭位置、LOWER保存、OUTPUT空白を保証。
- `GalilDpSearch`: 成功、下限スキップ、マーク0スキップ、終端失敗の実分岐。
- `GalilDpAdvance`: 出力1追加、MARKS+2、SECOND+4を14命令で行う。範囲内の次候補入口348まで15命令。
- `GalilDpExhaustion`: 範囲外の次候補で最大16命令の失敗停止。`exhausted_of_room`は初回h=0・長さ2以上にも使える。
- `GalilDpLoop.terminates`: 有効な正の候補hから検索ループが停止。検索命令数≤`18*(w.length-h)+19`。
- `GalilDpStart.initial_terminates`: 初回6命令・h=1への接続・長さ0..4を含め、実DP全体が任意入力・任意下限で停止。
- `GalilDpCounters`: OUTPUT全体=`^`+h個の1+blank、出力頭h、LOWER頭=min(cursor,lower+1)を追跡。
- **`GalilDpCorrect.initial_correct`**: 実初期状態から、`h>lower`, `4*h+1≤入力長`, 長さ`2*h+1`と`4*h+1`のprefixが回文、を満たす最小hを正確なunary出力で返す。候補が存在しなければ失敗する。
- `GalilDpSuffix.initial_correct` / `window_correct`: 逆順入力のprefix条件を元窓のsuffix条件へ接続。`w.reverse.take (span+1)`について、対応するsuffix窓内で最小候補を返す。

### 3. Scalaのテープ表現・制御への論理層での接続

- `GalilScaffoldTape`: 左右スタックをList、focusをFin9として解釈。read/focus、write、左右move、resetの非負位置テープ意味論を証明。
- `GalilScaffoldProgram.realize_completed` / `completed_sound`: 同じ命令表で、有限テープ実行と論理2スタック実行を双方向に接続。同じ命令列・命令数・最終テープ解釈。
- `GalilScaffoldControl`: enabled/doneプロトコル。haltでdone、停止後の呼び出しは不変。`scheduled_completed`は任意pauseを含む予定で有効tick数≥命令数なら完了する。`dp_scheduled`はDPの正しさを接続。
- **`GalilScaffoldPreload.scheduled_correct`**: 具体的なSOURCE/LOWERのスタック配置から、初期表現一致を前提とせずDPの正しさと任意pause実行を保証。
- **物理StackPool、共有セル、Scalaのpredicated circuitがこの論理層を実装することは未証明。** 新しい論理意味論を定義しただけで実回路の検証完了とは言わない。

## 本当の残作業と主経路

主経路:

```text
Scala ScaffoldCircuitGalil.buildOnline
  → ScaffoldEventBuffer.bufferSource
  → packService
  → GenerateOnlinePeg（未加工のab入力）
```

1. loaderの型エラー修正・root import、および`GalilScaffoldLoading`による全テープ構成への持ち上げは完了。
2. source/LOWERロードを具体的初期配置と結び、online walker・work counter・copy/home制御・reset/再利用を実装に即して証明する。
3. predicated instruction選択とStackPool/共有セルを論理2スタック実行へrefineする。
4. 実FPPを含む全体資源・時間上界を閉じ、online Galilの進捗・出力正しさ・期限を証明する。
5. 実FIFO、固定packing、最終StructuredMachineとPEGを接続する。

これは細部の残りだけではない。3〜5にはまだ大きな接続義務がある。
負例の回答が遅れること自体を欠陥としない。正例の期限と最終契約を守り、全入力でzero-lagを勝手に追加しない。

`lean-pal/PalPeg/Main.lean:43`の`pal_in_peg_of_structured`は依然として、PALを認識する具体的な`StructuredMachine M`と`hM`を要求する条件付き定理。**その具体例と全証明はまだ揃っていない。**

## Scalaの入口と記号

`scala/pal/src/main/scala/pal/`:

- `FppFinite.scala`, `FppSubroutine.scala`, `DpFinite.scala`: 実有限命令表。
- `ExportFppCode.scala`, `ExportFppCostCertificate.scala`, `ExportMarkedCode.scala`, `ExportDpCode.scala`: 実Scalaからのexporter。表を手で別物へ差し替えない。
- `ScaffoldCircuitGalil.scala`: online制御。DPとmarked FPPの両方を呼ぶ。
- `ScaffoldCircuitSearch.scala`: LOWERロード、walkerを左へ進めるSOURCEコピー、span+1の窓、home、DP run、倍増・待機。
- `ScaffoldCircuitProgram.scala`: start/reset、raw instructionStep、done、オプションのread-block実行。
- `ScaffoldCircuitStructs.scala`: Tapeの左右Stackとfocus。resetはroots clear+blank。左moveは左Stack非空を要求。右moveは空の右Stackからblankを補う。

記号`Fin 9`: a=0, b=1, s=2, #=3, LEFT=4, END=5, blank=6, bit0=7, bit1=8。
テープ: A0 B1 C2 S3 T4 BACK5 FRONT6 SOURCE7 MARKS8 SECOND9 LOWER10 OUTPUT11。
`ScaffoldCircuitGalil`が使用するFIRST等の追加記号や有限回路のalphabet拡張は、既存Fin9モデルとの接続で別途扱う必要がある。

## 検証・作業方法

Lean/buildプロセスは同時に一つ。遅いだけで再起動しない。liveなhandleをpollし、終了確認後に次を動かす。

```sh
cd /home/mizushima/repo/lean4-peg/lean-pal
lake env lean PalPeg/GalilScaffoldLoad.lean
# 成功後、依存ファイルから使う前にoleanを作る:
lake build PalPeg.GalilScaffoldLoad
# root importを追加してから全体検査:
set -o pipefail
lake build 2>&1 | tail -n 8
git diff --check
```

`lake env lean FILE`は`.olean`を作らない。依存変更後は`lake build PalPeg.Module`が必要。
`#print axioms`で`sorryAx`や独自公理を許さない。`native_decide`で証明を置換しない。
既存ファイル全体の無関係なlinter警告は残っている。全体ビルド成功と未importファイルの成功を混同しない。

既知の落とし穴:

- `GalilFppWide.Config`に自動extはない。`GalilScaffoldProgram.wide_ext`を利用できる。`apply wide_ext rfl`は推論で両辺を潰すことがあるので`apply wide_ext`後にpcを`rfl`。
- record更新の複数行で関数引数の継続インデントが浅いとparse errorになる。
- `read`は`MonadReader.read`と曖昧になる。simp内では`GalilScaffoldTape.read`を完全修飾する。
- `simpa using Constructor ... hr`は、内部引数`hr`の型エラーを外側のsimpで直せない。
- `List.replicate_succ`を明示的にsimpする必要がある場合がある。
- 大きな命令表を扱うファイルは`set_option maxRecDepth 100000`。`by decide`の有限証明に局所heartbeat増加がある。
- 初期化証明等が遅くても、同じビルドを複数起動しない。

Scala実行が必要なら`scala/`で一時runtime dirを使用:

```sh
task_runtime_dir=$(mktemp -d /tmp/pal-sbt-runtime.XXXXXX)
XDG_RUNTIME_DIR="$task_runtime_dir" sbt 'pal/runMain pal.ExportDpCode'
```

## 引き継ぎ時の検査範囲

引き継ぎ保存時は`GalilScaffoldPreload`までのroot build成功（9066 jobs）。
その後loaderのleaf検査に成功し、rootへ`GalilScaffoldLoad`を追加した。
**最新の全体ビルドは成功（9069 jobs、exit code 0）。** `GalilScaffoldCopy`を含む。起動したLean/buildプロセスは終了済み。
当時の`git diff --check`も成功。最新の未完成Counterと今回のleaf検査結果は冒頭の「最終保存時点」を参照。
古いsession IDをliveとみなさず、現在のプロセス状態を確認すること。

ユーザーへの報告は「何の前提が外れたか」「何がまだ未証明か」を明確に。追加ファイル数やbuild件数を大定理への距離の代わりにしない。
