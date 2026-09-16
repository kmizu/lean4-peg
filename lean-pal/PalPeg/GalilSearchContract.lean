import PalPeg.GalilCandidateWindow
import PalPeg.GalilMoveLemma

/-!
# 台帳義務 3: 探索契約（fallback 時点の span に短い周期はない）

`galil_move_of_contract`（`PalPeg/GalilMoveLemma.lean`）と
`replay_cost_le_window`（`PalPeg/GalilLedgerObligations.lean`）は仮定

```
contract : ∀ p, 0 < p → HasPeriod P p → k < 2*p
```

を要求する。ここで `P` は長さ `2k+1` の fallback 窓、すなわち
`Span raw C k`。本ファイルはこの契約を DP 探索の失敗分岐から導く。

不一致時に chain が idle のままだったということは、共走していた fpp DP が
窓 `(stream p).take (r+1)` 上で候補を 1 つも報告しなかったこと
（`Result` の失敗分岐 `y.pc = 347`）である。もし span に `2p ≤ r` なる周期
`p` があれば、`encoded_periodOn_even` により `p = 2δ` は偶数で、
`palAt_pair_of_period` が DP が実際に検査する 2 本の回文
（中心 `C-δ` 半径 `δ` と中心 `C-2δ` 半径 `2δ`）を与える。
`stream_prefix_palindrome` でこれを stream の接頭辞の回文性に戻すと
`GalilDpCorrect.Candidate` が成立し、失敗分岐に矛盾する。
`δ ≤ lower`（DP の探索下限より下）の場合だけは組合せ論では潰せないので、
`hlow` として分離してある。
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **台帳義務 3（探索契約）.**  走査が chain idle のまま不一致した時点で、
現在の中心 `C` の半径 `r` の回文の span は `2p ≤ r` なる周期 `p` を持たない。

仮定のうち機械側のものは 2 つだけ:

* `hres` — 共走している fpp DP は、半径 `r` に達した時点で窓
  `(stream ⟨a :: ls, gap⟩).take (r+1)`（頭から `r+1` 箇所）上の探索を
  下限 `lower`・開始 `first = 0` で完了している（DP 進行不変量）。
* `hidle` — その結果が失敗分岐（`pc = 347`）である。これが chain が idle に
  留まった理由。

`hlow` は下限 `lower` 以下の半周期を除く分で、`lower` は直前のラウンドが
確定させた最小周期なので `GalilPrepLeast.prep_least_no_candidate` 系から
供給される。 -/
theorem no_span_period_of_idle_search (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower : ℕ} {y : GalilFppWide.Config 12}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (r+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ)) :
    ∀ p, 0 < p → 2*p ≤ r → ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) p := by
  -- the DP reported no candidate at all
  have hnone : ∀ g, ¬ GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (r+1)) lower g := by
    rcases hres with ⟨k, _, _, _, hpc, _, _⟩ | ⟨_, hn⟩
    · rw [hidle] at hpc; exact absurd hpc (by decide)
    · exact fun g => hn g (Nat.zero_le _)
  intro p hp hpr hper
  have hstream : (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length = C := by
    rw [hC, position_represent]
  have hrle : r ≤ C := hpal.1
  have hlen : C + r < (encoded ((a :: ls).reverse ++ rs ++ q)).length := hpal.2.1
  have espan : Span ((a :: ls).reverse ++ rs ++ q) C r
      = ((encoded ((a :: ls).reverse ++ rs ++ q)).drop (C-r)).take ((C+r)+1-(C-r)) := by
    unfold Span
    rw [show (C+r)+1-(C-r) = 2*r+1 from by omega]
  -- `p` is even: the encoded word alternates separators and letters
  have hpo : PeriodOn (encoded ((a :: ls).reverse ++ rs ++ q)) p (C-r) (C+r) := by
    refine (hasPeriod_slice_iff (x := encoded ((a :: ls).reverse ++ rs ++ q))
      hlen (by omega)).1 ?_
    rw [← espan]
    exact hper
  have heven : p % 2 = 0 := encoded_periodOn_even hpo hp (by omega) hlen
  obtain ⟨δ, rfl⟩ : ∃ δ, p = 2*δ := ⟨p/2, by omega⟩
  have hδ : 0 < δ := by omega
  have h4δ : 4*δ ≤ r := by omega
  by_cases hlg : δ ≤ lower
  · exact hlow δ hδ hlg hper
  · have hlg' : lower < δ := by omega
    obtain ⟨p1, p2⟩ := palAt_pair_of_period hpal h4δ hper
    have q1 : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (2*δ+1)) := by
      refine (stream_prefix_palindrome a ls rs q gap δ (by rw [hstream]; omega)).2 ?_
      rw [hstream]
      exact p1
    have q2 : IsPal ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (4*δ+1)) := by
      rw [show 4*δ+1 = 2*(2*δ)+1 from by omega]
      refine (stream_prefix_palindrome a ls rs q gap (2*δ) (by rw [hstream]; omega)).2 ?_
      rw [hstream]
      exact p2
    refine hnone δ ⟨hlg', ?_, ?_, ?_⟩
    · rw [List.length_take, hstream]
      omega
    · rw [List.take_take, Nat.min_eq_left (by omega)]
      exact q1
    · rw [List.take_take, Nat.min_eq_left (by omega)]
      exact q2

#print axioms no_span_period_of_idle_search

/-- 同じ内容を `galil_move_of_contract` / `replay_cost_le_window` が要求する
形に置き換えたもの: fallback 窓 `Span raw C r`（長さ `2r+1`）の任意の周期 `p`
は `r < 2*p` を満たす。これがそのまま台帳義務 3 の `contract` 引数になる。 -/
theorem search_contract_of_idle_search (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower : ℕ} {y : GalilFppWide.Config 12}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (r+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ)) :
    ∀ p, 0 < p → HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) p → r < 2*p := by
  intro p hp hper
  by_contra hle
  exact no_span_period_of_idle_search a ls rs q gap hC hrC hpal hres hidle hlow p hp
    (by omega) hper

#print axioms search_contract_of_idle_search

/-- 義務 3 を `galil_move_of_contract` に実際に流し込んだ形: fallback 窓が
回文で長さ `2r+1` なら、chosen 半径への移動量は `r ≤ 4*(r+1-chosenRadius)` を
満たす。 -/
theorem galil_move_of_idle_search (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower : ℕ} {y : GalilFppWide.Config 12} (x : Fin 3)
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (r+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ))
    (hP : IsPal (Span ((a :: ls).reverse ++ rs ++ q) C r))
    (hlenP : (Span ((a :: ls).reverse ++ rs ++ q) C r).length = 2*r+1) :
    r ≤ 4*(r + 1 - chosenRadius (x :: Span ((a :: ls).reverse ++ rs ++ q) C r)) :=
  PalPeg.galil_move_of_contract x _ hP r hlenP
    (search_contract_of_idle_search a ls rs q gap hC hrC hpal hres hidle hlow)

#print axioms galil_move_of_idle_search

end PalPeg.GalilScaffoldChainInputSupply
