import PalPeg.GalilSearchContract

/-!
# 台帳義務 3（stage 窓版）: 探索契約を DP の *stage* 窓から導く

`PalPeg/GalilSearchContract.lean` の `search_contract_of_idle_search` は
DP の結果 `hres` が「ちょうど現在の走査半径 `r` に合わせた窓」
`(stream …).take (r+1)` 上で成立していることを要求する。

ところが実際の共走では DP は stage 単位で走り、供給されるのは
`Result ((stream …).take (span+1)) lower 0 y`（`span = 8 * max lower 1` 以上、
失敗分岐は `pc = 347`）という *stage 窓* 上の結果である。

本ファイルはその形のまま同じ結論を出す。証明の骨格は元と同じで、
唯一変わるのは候補 `δ` を作る窓の長さの見積もりである:

* 周期 `p = 2δ` が `2*p ≤ r` を満たすとき `4*δ ≤ r`。
* 候補 `δ` が stage 窓 `take (span+1)` の中に収まるには `4*δ+1 ≤ span+1`、
  すなわち `4*δ ≤ span` が必要。

したがって必要な `r` の上界は **`r ≤ span`** である（`4*δ ≤ r ≤ span`）。
`r ≤ 2*span` では足りない: `span/4 < δ ≤ span/2` の帯域では候補 `δ` の
`4δ+1` 箇所が stage 窓からはみ出し、しかも palindrome の周期構造からは
それより小さい候補を作れないので、失敗分岐と矛盾させられない。
仮定 `8 * max lower 1 ≤ span` はこの論法には不要（`r ≤ span` に吸収される）。

候補はつねに接頭辞 `take (4δ+1)` だけで決まる（`Candidate` の 3 条件は
`w.length` の下界と `w.take (2δ+1)` / `w.take (4δ+1)` の回文性のみ）ので、
`candidate_window_mono` と同様、窓全体は要らず `4δ+1` までの接頭辞で十分。
ここでは候補を stage 窓の上で直接構成している。
-/

set_option autoImplicit false
namespace PalPeg.GalilScaffoldChainInputSupply
open Manacher GalilScaffoldInputHead GalilScaffoldChainVerifier

/-- **台帳義務 3（stage 窓版・素の形）.**  共走している fpp DP が stage 窓
`(stream ⟨a :: ls, gap⟩).take (span+1)` 上で失敗分岐 (`pc = 347`) に落ちていて、
現在の走査半径 `r` が stage 窓に収まっている (`r ≤ span`) なら、
中心 `C` 半径 `r` の span は `2*p ≤ r` なる周期 `p` を持たない。 -/
theorem no_span_period_of_stage (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower span : ℕ} {y : GalilFppWide.Config 12}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hr : r ≤ span)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ)) :
    ∀ p, 0 < p → 2*p ≤ r → ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) p := by
  -- the DP reported no candidate at all on the stage window
  have hnone : ∀ g, ¬ GalilDpCorrect.Candidate
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower g := by
    rcases hres with ⟨k, _, _, _, hpc, _, _⟩ | ⟨_, hn⟩
    · rw [hidle] at hpc; exact absurd hpc (by decide)
    · exact fun g => hn g (Nat.zero_le _)
  intro p hp hpr hper
  have hstream : (GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).length = C := by
    rw [hC, position_represent]
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

#print axioms no_span_period_of_stage

/-- **台帳義務 3（stage 窓版）.**  `galil_move_of_contract` /
`replay_cost_le_window` がそのまま要求する形。 -/
theorem search_contract_of_stage (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower span : ℕ} {y : GalilFppWide.Config 12}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hr : r ≤ span)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ)) :
    ∀ p, 0 < p → HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) p → r < 2*p := by
  intro p hp hper
  by_contra hle
  exact no_span_period_of_stage a ls rs q gap hC hrC hr hpal hres hidle hlow p hp
    (by omega) hper

#print axioms search_contract_of_stage

/-- stage 窓版の探索契約を `galil_move_of_contract` に流し込んだ形。 -/
theorem galil_move_of_stage (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower span : ℕ} {y : GalilFppWide.Config 12} (x : Fin 3)
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (hr : r ≤ span)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ))
    (hP : IsPal (Span ((a :: ls).reverse ++ rs ++ q) C r))
    (hlenP : (Span ((a :: ls).reverse ++ rs ++ q) C r).length = 2*r+1) :
    r ≤ 4*(r + 1 - chosenRadius (x :: Span ((a :: ls).reverse ++ rs ++ q) C r)) :=
  PalPeg.galil_move_of_contract x _ hP r hlenP
    (search_contract_of_stage a ls rs q gap hC hrC hr hpal hres hidle hlow)

#print axioms galil_move_of_stage

/-- 実際の共走が供給する `span = 8 * max lower 1` の形に寄せた特殊化。
`8 * max lower 1 ≤ span` は論法には使わず、必要なのは `r ≤ span` だけ。 -/
theorem search_contract_of_stage' (a : Fin 2) (ls rs q : List (Fin 2)) (gap : Bool)
    {C r lower span : ℕ} {y : GalilFppWide.Config 12}
    (hC : C = position (represent ⟨a :: ls,gap⟩ (rs.map some) q)) (hrC : r < C)
    (_hspan : 8 * max lower 1 ≤ span) (hr : r ≤ span)
    (hpal : PalAt (encoded ((a :: ls).reverse ++ rs ++ q)) C r)
    (hres : GalilDpCorrect.Result
      ((GalilScaffoldPlace.stream ⟨a :: ls,gap⟩).take (span+1)) lower 0 y)
    (hidle : y.pc = 347)
    (hlow : ∀ δ, 0 < δ → δ ≤ lower →
      ¬ HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) (2*δ)) :
    ∀ p, 0 < p → HasPeriod (Span ((a :: ls).reverse ++ rs ++ q) C r) p → r < 2*p :=
  search_contract_of_stage a ls rs q gap hC hrC hr hpal hres hidle hlow

#print axioms search_contract_of_stage'

end PalPeg.GalilScaffoldChainInputSupply
