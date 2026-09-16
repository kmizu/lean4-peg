import PegSeparation.Common.Compiler.RealTimeTM.Correctness
import PegSeparation.Common.Compiler.SCAToPEG.Final
import PalPeg.Basic

/-!
# `PAL ∈ PEG`（厳密実時間 TM の存在を仮定した条件付き定理）

鎖：
```
厳密実時間 TM `M` が `PAL` を認識          (仮定 `hM` — Slisenko 1973 / Galil 1978 の機械)
  ⇒ SCA `toSCA M` が `PAL` を判定           (Kim–Park, `RealTimeTM.toSCA_accepts_iff`)
  ⇒ total PEG `G` が `PALᴿ` を認識          (LMR Thm 16 の十分方向, `SCAToPEG.loffBackward`)
  ⇒ `G` が `PAL` を認識                     (`PALᴿ = PAL`, `PAL_reverse_mem`)
```
成果物の `Closure/PrefixPEG.lean` `pref_isPEG` と同じ形。
-/

namespace PalPeg

open PegSeparation

/-- 成果物の厳密実時間機械 `M`（`t` テープ・`s` 状態・`k` 記号）が `PAL` を認識するならば、
`PAL` を認識する total PEG が存在する。 -/
theorem pal_in_peg_of_realTime {t s k : ℕ}
    (M : RealTimeTM.Machine (Fin 2) t s k) (hM : ∀ w, M.Accepts w ↔ w ∈ PAL) :
    ∃ (n : ℕ) (G : PegGrammar (Fin 2) n),
      G.IsLoffTotal ∧ ∀ w, G.Recognizes w ↔ w ∈ PAL := by
  obtain ⟨n, G, hTotal, hG⟩ := SCAToPEG.loffBackward (RealTimeTM.toSCA M)
  refine ⟨n, G, hTotal, fun w => ?_⟩
  -- `hG wᴿ : (toSCA M).Accepts wᴿ ↔ G.Recognizes wᴿᴿ`；`wᴿᴿ = w` で整える。
  have hGrammar : G.Recognizes w ↔ (RealTimeTM.toSCA M).Accepts w.reverse := by
    have h := (hG w.reverse).symm
    rwa [List.reverse_reverse] at h
  have hSCA : (RealTimeTM.toSCA M).Accepts w.reverse ↔ M.Accepts w.reverse :=
    RealTimeTM.toSCA_accepts_iff M w.reverse
  have hMachine : M.Accepts w.reverse ↔ w.reverse ∈ PAL := hM w.reverse
  have hReverse : w.reverse ∈ PAL ↔ w ∈ PAL := PAL_reverse_mem w
  calc G.Recognizes w
      ↔ (RealTimeTM.toSCA M).Accepts w.reverse := hGrammar
    _ ↔ M.Accepts w.reverse := hSCA
    _ ↔ w.reverse ∈ PAL := hMachine
    _ ↔ w ∈ PAL := hReverse

/-- 言語クラスの言い方：`PAL` が（成果物の意味で）実時間 TM で認識されるならば
`PAL` は total PEG で認識される。 -/
theorem pal_recognizedByTotalPEG (h : RealTimeTM.RecognizedBy PAL) :
    RecognizedByTotalPEG PAL := by
  obtain ⟨t, s, k, M, hM⟩ := h
  exact pal_in_peg_of_realTime M hM

end PalPeg
