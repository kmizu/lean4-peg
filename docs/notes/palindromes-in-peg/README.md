# 回文は PEG 言語である（既知結果の合成）— 2026-09-03 の観察

## 結論

Loff–Moreira–Reis（JCSS 2020）の **Conjecture 7**「偶数長回文 `{ w wᴿ }` には PEG が無い」は、
既に発表されている3つの結果を合成するだけで**偽**になる。

1. **Galil (JCSS 16(2), 1978; Slisenko 1973 の簡略化)**: 入力を1記号ずつ読みながら、各接頭辞が
   回文かどうかを判定する real-time 決定性多テープ TM が存在する（要旨: "a real-time Turing
   machine algorithm which finds all initial palindromes in the input string"）。
2. **real-time 多テープ TM ⊆ SCA**: Kim–Park (arXiv:2608.29592, 2026) の Lean アーティファクト
   `PegSeparation/Common/Compiler/RealTimeTM/{Model,ToSCA,Correctness}.lean` に、任意本数・双方向
   ヘッドの real-time 多テープ TM を scaffolding automaton にコンパイルする
   `recognizedBySCA_of_recognizedBy` が検証済み。
3. **L ∈ PEG ⇔ Lᴿ ∈ SCA**（LMR Theorem 16、同アーティファクトで両方向を検証）。

回文は反転で不変なので、(1)+(2)+(3) から PAL ∈ PEG。偶数長に限っても同じ（Galil の機械に
入力長の偶奇を持たせるだけ）。

## この観察の位置づけ

- Kim–Park 2026 は `CFL ⊄ PEG`（線形 CFL の反例）と反転・連接・Kleene 星・準同型の非閉包を示したが、
  回文については「Loff らの問いに対する witness は我々のものではない」と未解決扱いのまま。
  両論文の著者もこの合成に気づいていない可能性が高い。
- 唯一の非形式化部分は Galil の定理。Galil の "real-time" は「入力1記号あたり定数ステップ」の意味で
  使われることがあるが、多テープ TM ではテープ圧縮（標準の線形高速化）で「1記号あたりちょうど
  1ステップ」に直せるので、アーティファクトの `Machine` モデルに載る。ここを疑うなら、この
  speedup も形式化対象になる。
- したがってこのリポジトリの T7（`Cfg/OpenProblems.lean`）が反例候補として調べていた偶数長回文は、
  `CFL ⊆ PEL` の反例には**なり得ない**（PEL 側にある）。`CFL ⊆ PEL` 自体は Kim–Park の別の
  witness で否定的に解決済み。

## 再現手順

```
curl -L -o artifact.zip \
  'https://zenodo.org/api/records/22099762/files/kimjg1119/peg-separation-artifact-v0.1.0.zip/content'
unzip artifact.zip && cd kimjg1119-peg-separation-artifact-*/
cp <this dir>/Palindromes.lean PegSeparation/Palindromes.lean
lake exe cache get && lake build PegSeparation.Palindromes
```

`#print axioms PegSeparation.palindromes_isPEG_of_realTime` → `[propext, Classical.choice, Quot.sound]`
（Lean v4.31.0 + Mathlib v4.31.0、2026-09-03 に確認）。

主定理:

```lean
theorem recognizedByTotalPEG_of_recognizedBy_of_reverse_eq
    (hrev : Language.reverse L = L) (h : RealTimeTM.RecognizedBy L) : RecognizedByTotalPEG L
theorem palindromes_isPEG_of_realTime
    (hrt : RecognizedBy (Palindromes Terminal)) : RecognizedByTotalPEG (Palindromes Terminal)
theorem evenPalindromes_isPEG_of_realTime
    (hrt : RecognizedBy (EvenPalindromes Terminal)) : RecognizedByTotalPEG (EvenPalindromes Terminal)
```
