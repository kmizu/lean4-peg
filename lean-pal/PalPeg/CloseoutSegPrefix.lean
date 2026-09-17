import PalPeg.CloseoutSegBudget

/-!
# `SegCrossSplit`, proved: a watch segment has a prefix of any matched count

`CloseoutSegBudget` reduced the terminal head bound (= the `hpos` residue) to
one named fact: when the segment's matched count would take the right head past
the checkpoint, the segment has a prefix that lands exactly on it.

That is pure list arithmetic on the event list.  Each `WatchSegE` constructor
consumes one event — `false` for the two background steps, `true` for the three
matched ones — so an induction on the derivation picks the prefix:

`watchSegE_prefix_count` — for every `n ≤ es.count true` there is a split
`es = es1 ++ es2` with `es1.count true = n` and a `WatchSegE` along `es1`.

`segCrossSplit_proved` is then `SegCrossSplit` with
`n := 2 * m - 1 - position r.right`, and
`GalilLeafPos.reportPointAt_of_seg` makes that prefix's landing the report point
at `m`, which is where the oracle reports instead of continuing.

**全体 build 成功・標準公理のみ・無条件 PAL は未完.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.CloseoutSegPrefix

open PalPeg PalPeg.GalilScaffoldTop PalPeg.GalilScaffoldController
  PalPeg.GalilScaffoldChainInputSupply
open GalilScaffoldCounter GalilScaffoldInputHead GalilScaffoldChainVerifier
open PalPeg.GalilRunSkeleton PalPeg.GalilInvPlus2

/-- **A watch segment has a prefix of any smaller matched count.**  Induction on
the derivation: the two background constructors carry a `false` event and pass
`n` through, the three matched ones carry a `true` event and split on whether
`n` is zero. -/
theorem watchSegE_prefix_count (P : Shared) (q : ℕ) (first : Fin 9) (delay : ℕ) :
    ∀ {es : List Bool} {c c' : Control} {s t : GalilVM},
      WatchSegE P q first delay es c s c' t →
      ∀ n : ℕ, n ≤ es.count true →
        ∃ (es1 es2 : List Bool) (c1 : Control) (t1 : GalilVM),
          es = es1 ++ es2 ∧ es1.count true = n ∧
          WatchSegE P q first delay es1 c s c1 t1 := by
  intro es c c' s t h
  induction h with
  | stop c s =>
    intro n hn
    simp only [List.count_nil, Nat.le_zero_eq] at hn
    exact ⟨[], [], c, s, rfl, by simp [hn], .stop _ _⟩
  | wait c s s0 hm hr hnn hb rest ih =>
    intro n hn
    simp only [List.count_cons] at hn
    obtain ⟨es1, es2, c1, t1, he, hc, hw⟩ := ih n (by simpa using hn)
    exact ⟨false :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hc],
      .wait c s s0 hm hr hnn hb hw⟩
  | count c s s0 hm hr ha hc hb rest ih =>
    intro n hn
    simp only [List.count_cons] at hn
    obtain ⟨es1, es2, c1, t1, he, hcc, hw⟩ := ih n (by simpa using hn)
    exact ⟨false :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hcc],
      .count c s s0 hm hr ha hc hb hw⟩
  | «match» c s vs vq o hm hr ha hc hne hcmp hmt hq ho rest ih =>
    intro n hn
    cases n with
    | zero => exact ⟨[], true :: _, c, s, rfl, by simp, .stop _ _⟩
    | succ n' =>
      simp only [List.count_cons] at hn
      obtain ⟨es1, es2, c1, t1, he, hcc, hw⟩ := ih n' (by simp at hn; omega)
      exact ⟨true :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hcc],
        .match c s vs vq o hm hr ha hc hne hcmp hmt hq ho hw⟩
  | matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro n hn
    cases n with
    | zero => exact ⟨[], true :: _, c, s, rfl, by simp, .stop _ _⟩
    | succ n' =>
      simp only [List.count_cons] at hn
      obtain ⟨es1, es2, c1, t1, he, hcc, hw⟩ := ih n' (by simp at hn; omega)
      exact ⟨true :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hcc],
        .matchIdle c s vs vq o hm hr ha hc hidle hl hrr hvs hmt hq hnf ho hw⟩
  | countR c s s0 hm hr hc hidle hb rest ih =>
    intro n hn
    simp only [List.count_cons] at hn
    obtain ⟨es1, es2, c1, t1, he, hcc, hw⟩ := ih n (by simpa using hn)
    exact ⟨false :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hcc],
      .countR c s s0 hm hr hc hidle hb hw⟩
  | matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho rest ih =>
    intro n hn
    cases n with
    | zero => exact ⟨[], true :: _, c, s, rfl, by simp, .stop _ _⟩
    | succ n' =>
      simp only [List.count_cons] at hn
      obtain ⟨es1, es2, c1, t1, he, hcc, hw⟩ := ih n' (by simp at hn; omega)
      exact ⟨true :: es1, es2, c1, t1, by rw [he]; rfl, by simp [hcc],
        .matchIdleR c s vs vq o hm hr hc ha hidle hl hrr hvs hmt hq hnf ho hw⟩

section
variable (centre : GalilVM → Fin 3) (place : GalilVM → GalilScaffoldPlace.Place)
  (entry q : ℕ) (first : Fin 9)

/-- **`SegCrossSplit` proved.**  Take the prefix whose matched count is exactly
the distance to the checkpoint. -/
theorem segCrossSplit_proved (w : List (Fin 2)) :
    PalPeg.CloseoutSegBudget.SegCrossSplit centre place entry q first w := by
  intro m c c' r t es hm1 hmle hIC hrt hw hgt
  obtain ⟨es1, es2, c1, t1, he, hc, hw1⟩ :=
    watchSegE_prefix_count (PofC centre place entry w) q first 2048 hw
      (2 * m - 1 - position r.right) (by omega)
  exact ⟨es1, es2, c1, t1, he, hw1, by rw [hc]; omega⟩

end

#print axioms watchSegE_prefix_count
#print axioms segCrossSplit_proved

end PalPeg.CloseoutSegPrefix
