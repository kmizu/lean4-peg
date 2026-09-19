import PalPeg.GalilPrepLeast
import PalPeg.CopyPhaseTick

/-!
# found 文脈から `hChainReachesWatch` を出す

`FoundPackCorrected.reachesWatchPhase_of_backgroundRun` の最後の外部入力

    hChainReachesWatch : ∀ es, es.length = n → es.count true = 0 →
      ∃ w, ChainTicks es sP.chain (ChainVM.watch w)

を、`n = 2h+2` として found 文脈から供給する。材料は 2 つだけ:

* `GalilScaffoldChainInputSupply.found_to_watchStart_least` —
  `SafeQuanta` ＋ `GalilDpCorrect.Result` から、**任意の** `bs`（長さ `h`）と
  `cs`（長さ `h+1`）について `ChainTicks (bs ++ dm :: cs) x1 (.watch (watchStart …))`。
  さらに `(denote y.config).pos 11 = h` を持ち出すので `h` は `dm` に依らず一意。
* `CopyPhaseTick.list_split_mid` — 長さ `2h+2` のリストは `bs ++ dm :: cs` に分割できる。

`dm` が `found_to_watchStart_least` の**引数**である点が要注意で、分割で出てくる
実際の中央要素ごとに定理を当て直す。そのとき `h` が揺れないことを保証するのが
`hCursor`（DP 出力カーソル）。**これが無いと `h` の一意性が言えず、
「長さ `2h+2`」という主張そのものが `dm` 依存になって壊れる。**

誕生直後の chain は `ChainMatched (chainStart …) ch`（`CopyPhaseTick.
copyOrBack_of_chainMatched_chainStart` と同じ文脈）なので `sm = true` 側を使う。
一意性は `chainMatched_unique`。

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false

namespace PalPeg.ChainReachesWatchFromFound

open PalPeg PalPeg.GalilScaffoldChainInputSupply PalPeg.GalilScaffoldController
open GalilScaffoldCounter GalilScaffoldChainVerifier GalilScaffoldInputHead
open PalPeg.GalilScaffoldTop

/-- **found 文脈から「長さ `2h+2` の任意のイベント列で watch に着く」。**

`hStart` は誕生した chain `x1` と `chainStart` の関係。`sm = true` が
`ChainMatched` 1 歩を経た形（比較が一致した誕生）、`sm = false` が素の
`chainStart`。 -/
theorem chainReachesWatch_of_found
    {s t : GalilScaffoldSearchFinish.State} {x y : GalilScaffoldControl.Machine 12}
    {as : List Bool} {w : List (Fin 3)} {lower span : ℕ} (p : GalilScaffoldPlace.Place)
    (hw : w = (GalilScaffoldPlace.stream p).take (span + 1))
    (hr : GalilScaffoldSearchRun.SafeQuanta s x as t y) (hs : s.mode = .run) (ht : t.mode = .found)
    (hv : GalilDpCorrect.Result w lower 0 (GalilScaffoldProgram.denote y.config))
    (ver : PlaceHead) (r0 : ℕ) (sm : Bool) {x1 : ChainVM} {h : ℕ}
    (hCursor : (GalilScaffoldProgram.denote y.config).pos 11 = h)
    (hStart : ∀ cen : Fin 3, GalilScaffoldPlace.read p = some cen →
      (if sm then ChainMatched (chainStart (y.config.tapes 11) cen p ver (ofNat (r0 + 1))) x1
        else x1 = chainStart (y.config.tapes 11) cen p ver (ofNat (r0 + 1)))) :
    ∀ es : List Bool, es.length = 2 * h + 2 →
      ∃ wv : GalilScaffoldChainWatch.State, ChainTicks es x1 (ChainVM.watch wv) := by
  intro es hLen
  obtain ⟨bs, dm, cs, hSplit, hbs, hcs⟩ := PalPeg.CopyPhaseTick.list_split_mid es h hLen
  obtain ⟨h', cen, ys, b, hcand, hread, hlen, hpc, hpos, hrest⟩ :=
    found_to_watchStart_least p hw hr hs ht hv ver r0 sm dm
  have hSame : h' = h := by rw [← hpos]; exact hCursor
  subst hSame
  obtain ⟨x1', hx1', hticks⟩ := hrest bs cs hbs hcs
  have hstart := hStart cen hread
  have hEq : x1' = x1 := by
    cases sm with
    | false =>
      simp only [Bool.false_eq_true, if_false] at hx1' hstart
      rw [hx1', hstart]
    | true =>
      simp only [if_true] at hx1' hstart
      exact chainMatched_unique hx1' hstart
  rw [hEq] at hticks
  rw [hSplit]
  exact ⟨_, hticks⟩

#print axioms chainReachesWatch_of_found

end PalPeg.ChainReachesWatchFromFound
