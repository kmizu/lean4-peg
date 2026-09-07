import PalPeg.Basic
import PalPeg.Existence
import PalPeg.EvenLength

/-!
# 公理 guard

主定理の `#print axioms` を `#guard_msgs` で固定する。Lean / Mathlib の標準公理
`propext`, `Classical.choice`, `Quot.sound` 以外（`sorryAx` を含む）が現れれば
このファイルのビルドが失敗する。
-/

/-- info: 'PalPeg.PAL_reverse_mem' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PAL_reverse_mem

/-- info: 'PalPeg.PAL_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.PAL_reverse

/-- info: 'PalPeg.pal_in_peg_of_realTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_in_peg_of_realTime

/-- info: 'PalPeg.pal_recognizedByTotalPEG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.pal_recognizedByTotalPEG

/-- info: 'PalPeg.evenLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenLength_isRegular

/-- info: 'PalPeg.oddLength_isRegular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.oddLength_isRegular

/-- info: 'PalPeg.evenPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenPal_of_pal

/-- info: 'PalPeg.oddPal_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.oddPal_of_pal

/-- info: 'PalPeg.mem_PAL_inf_EvenLength_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.mem_PAL_inf_EvenLength_iff

/-- info: 'PalPeg.evenPal_ww_reverse_of_pal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalPeg.evenPal_ww_reverse_of_pal
