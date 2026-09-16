import PalPeg.GalilPeriodUnion

/-!
# 周期破れ（period break）の符号化語への反映

`found_life` / `chain_life` の終端事象は「外側の比較は一致するのに chain が
`.broken` になる」比較である（`GalilScaffoldTopRoundBreak`、
`GalilScaffoldChainInputSupply.only_scan_terminal_match`）。そこでは

* 外側の左右の読みは一致する（`hmatch`）が、
* 左の読みは chain の予測 `symbol control.period.focus` と食い違う

という 2 つの事実が同時に成り立つ。したがって新しい位置の記号は
`2h` 手前の記号と異なり、**その位置までの区間には周期 `2h` が無い**。

`GalilScaffoldChainReadOrigin.ReadOrigin.joined_input_period` が「chain が
壊れていない限り周期 `2h` が成り立つ」側を与えるのに対して、ここはその
双対、すなわち壊れた瞬間に周期が破れることを与える。

* `no_period_of_break` — 1 点の不一致から `¬ PeriodOn` を得る純粋な補題。
* `break_symbols_differ` — 破れの比較における記号不一致（符号化語の添字で）。
* `break_not_period` — 主定理。`ReadOrigin` の起点から新しい位置までの区間に
  周期 `2*(o.interior.length+1)` が無いこと。
-/

set_option autoImplicit false
namespace PalPeg.GalilBreakPeriod
open GalilScaffoldChainInputSupply GalilScaffoldInputHead GalilScaffoldChainVerifier
  GalilScaffoldChainVerifyRun

/-! ## 純粋な部分：1 点の不一致は区間周期を否定する -/

/-- A single mismatching pair inside `[a, b]` refutes `PeriodOn`. -/
theorem no_period_of_break {x : List (Fin 3)} {p a b j : ℕ} (hj : a ≤ j) (hjb : j + p ≤ b)
    (hne : x[j]? ≠ x[j + p]?) : ¬ PeriodOn x p a b := fun h => hne (h j hj hjb)

/-! ## 破れの比較における記号の不一致 -/

/-- At the terminal (breaking) comparison of an only-mode round the right
endpoint's symbol differs from the chain prediction. This is exactly the
`hbad` fact used inside `caught_scan_terminal_match` to derive `broken = true`,
but stated at the `OnlyCompareState` level, as `reshift_compare` does. -/
theorem break_prediction_mismatch {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true)
    (hmatch : read (left s.left) = read (right s.right)) :
    read (right s.right) ≠
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus := by
  have hcheck := o.check_pair extra hi ht hl
  have hne : read (left s.left) ≠
      GalilScaffoldChainConsume.symbol s.watch.machine.control.period.focus := by
    intro he
    have hf := hcheck.mp he
    simp [hend] at hf
  rw [← hmatch]
  exact hne

/-- The new place sits `2h` above the predicted place, and the two encoded
symbols there differ. `hposition` records the index identity separately so the
caller can reuse it. -/
theorem break_symbols_differ {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hmatch : read (left s.left) = read (right s.right)) :
    position (right s.right) =
        position o.start.machine.verifier + o.pre.length + extra.length + 1 ∧
      4*(o.interior.length+1) ≤ o.pre.length ∧
      position o.watched.machine.verifier =
        position o.start.machine.verifier + o.pre.length ∧
      (encoded raw)[position o.watched.machine.verifier -
          2*(o.interior.length+1) + (extra.length+1)]? ≠
        (encoded raw)[position (right s.right)]? := by
  have hbad := break_prediction_mismatch o extra hi ht hl hend hmatch
  -- the right endpoint really reads the encoded symbol at its position
  have hrrep := right_word s.right raw hi.caught.scan.rightRep hc
  have hrpres := right_present s.right raw hi.caught.scan.rightRep
    hi.caught.scan.rightPresent hc
  have hrpos := right_position s.right hc
    (represented_position s.right.head raw hi.caught.scan.rightRep
      hi.caught.scan.rightPresent).1
  have hreadr : read (right s.right) = (encoded raw)[position (right s.right)]? :=
    represented_read (right s.right) raw hrrep hrpres
  -- positions of the verifier along the round
  have hwrep := reads_word o.reads raw o.represents
  have hwpres := reads_present o.reads o.present
  have hver := (chain_shift_values o.shiftRun).2.2.2.2.2.1
  have hreads2 : Reads o.watched.machine.verifier extra s.watch.machine.verifier := by
    simpa only [hver] using ht.reads
  have hposw : position o.watched.machine.verifier =
      position o.start.machine.verifier + o.pre.length :=
    reads_position o.reads raw o.represents o.present
  have hposs : position s.watch.machine.verifier =
      position o.watched.machine.verifier + extra.length :=
    reads_position hreads2 raw hwrep hwpres
  have halign := hi.caught.aligned
  have hposr : position (right s.right) =
      position o.start.machine.verifier + o.pre.length + extra.length + 1 := by omega
  -- the origin has at least four half periods of history
  have h4 : 4*(o.interior.length+1) ≤ 2*(o.shifts+2)*(o.interior.length+1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hbig : 4*(o.interior.length+1) ≤ o.pre.length := le_trans h4 o.length
  -- the prediction window pins the predicted symbol on the encoded word
  have hsuccess : (GalilScaffoldChainSweep.run o.shifted.machine.control extra).broken
      = false := by
    rw [← ht.control]; exact hi.caught.unbroken
  have hpred := read_prediction_window o.token o.boundary o.interior extra o.reads
    o.offset o.unbroken o.shiftRun raw o.represents o.present o.full hi.available hsuccess
  rw [← ht.control] at hpred
  refine ⟨hposr, hbig, hposw, ?_⟩
  rw [← hpred, ← hreadr]
  exact fun he => hbad he.symm

/-! ## 主定理 -/

/-- **Period break with matching outer symbols.** At the breaking comparison of
the round issued from the read origin `o` — the outer compare matches
(`hmatch`), the cycle is at its last step (`hend`), so the chain prediction is
refuted and `consume` sets `broken = true` — the span from the origin's start
up to the new place has no period `2h`, where `h = o.interior.length+1`. -/
theorem break_not_period {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hmatch : read (left s.left) = read (right s.right)) :
    ¬ PeriodOn (encoded raw) (2*(o.interior.length+1))
      (position o.start.machine.verifier + 1) (position (right s.right)) := by
  obtain ⟨hposr, hbig, hposw, hne⟩ :=
    break_symbols_differ o extra hi ht hl hend hc hmatch
  refine no_period_of_break
    (j := position o.watched.machine.verifier - 2*(o.interior.length+1) + (extra.length+1))
    (by omega) (by omega) ?_
  have hsum : position o.watched.machine.verifier - 2*(o.interior.length+1) +
      (extra.length+1) + 2*(o.interior.length+1) = position (right s.right) := by omega
  rw [hsum]
  exact hne

/-- Existential form, matching the informal reading of `break_not_period`. -/
theorem break_witness {raw : List (Fin 2)} (o : ReadOrigin raw)
    {center radius : ℕ} {s : OnlyCompareState} (extra : List (Fin 3))
    (hi : OnlyScan raw center radius (2*(o.interior.length+1)) extra.length
      s.left s.right s.watch s.cycle)
    (ht : GalilScaffoldChainWatchTrace.Trace o.shifted.machine extra s.watch.machine)
    (hl : LeftMoves o.resumeLeft extra.length s.left)
    (hend : GalilScaffoldCounter.singlePositive s.cycle = true) (hc : canRight s.right)
    (hmatch : read (left s.left) = read (right s.right)) :
    ∃ j, position o.start.machine.verifier < j ∧
      j + 2*(o.interior.length+1) = position (right s.right) ∧
      (encoded raw)[j]? ≠ (encoded raw)[j + 2*(o.interior.length+1)]? := by
  obtain ⟨hposr, hbig, hposw, hne⟩ :=
    break_symbols_differ o extra hi ht hl hend hc hmatch
  refine ⟨position o.watched.machine.verifier - 2*(o.interior.length+1) + (extra.length+1),
    by omega, by omega, ?_⟩
  have hsum : position o.watched.machine.verifier - 2*(o.interior.length+1) +
      (extra.length+1) + 2*(o.interior.length+1) = position (right s.right) := by omega
  rw [hsum]
  exact hne

#print axioms no_period_of_break
#print axioms break_prediction_mismatch
#print axioms break_symbols_differ
#print axioms break_not_period
#print axioms break_witness
end PalPeg.GalilBreakPeriod
