import PalPeg.ScaHeadDecompose
import PalPeg.ScaShiftSafe

/-!
# `Decompose k` under the worker's side conditions

`ScaHeadDecompose.decompose_run` as a guarded run (`ScaHeadSafe.iterS`) with the pattern boundary
`W = |x|`: the same steps, each keeping the real matcher worker's side conditions.

* **Orientation** (`DecOrient`): every head `Decompose` copies is copied, directly or through a
  chain of copies, from `Origin` (`copy Cut Origin`, `Initialize`'s `copy A/P/KP Cut`, `copy B P`,
  `copy Walk Cut`, `copy First P`, `copy KFirst B`, `copy Reach B`, `copy Second P`), and `A`, `B`
  are read by `symbols` inside the pattern; so all of `Origin, Cut, A, P, B, KP, First, KFirst,
  Reach, Second, Walk` are reversed. `End` is only compared, never copied, moved or read.
* **Reads**: every `symbols A B` follows a successful `B < End` test, so both heads are `< |x|`.
* **Moves**: every moved non-blind head ends `≤ |x|` — `A`, `B` move only after `B < End`;
  `P` ends at most at `Cut + |x.drop Cut|` in the shifts; `Walk` ends at `First`; `Cut` ends at
  `P`. The one exception is `Initialize`'s `P := Cut + 1` when `Cut = |x|`, which happens only for
  `x = []`: the contract assumes `0 < |x|`.

The shift generators of the non-searching kind (`resetShiftF_runS`, `periodShiftF_runS`) and
`Initialize` (`init_runS`) are ported the same way.
-/
set_option autoImplicit false
namespace PalPeg.ScaDecomposeSafe
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe PalPeg.ScaHeadDecompose

/-- The orientation facts `Decompose` needs: all the heads it copies or reads are reversed. -/
structure DecOrient (ρ : String → Bool) : Prop where
  origin : ρ "Origin" = true
  cut : ρ "Cut" = true
  a : ρ "A" = true
  p : ρ "P" = true
  b : ρ "B" = true
  kp : ρ "KP" = true
  first : ρ "First" = true
  kfirst : ρ "KFirst" = true
  reach : ρ "Reach" = true
  second : ρ "Second" = true
  walk : ρ "Walk" = true

/-! ## One guarded step, as a run combinator -/

section Run
variable {W : ℕ} {ρ : String → Bool} {v : HVM} {c : Config} {c' : Ctl} {n : ℕ} {r : Option HVM}

theorem runS_copy {t s' : String} (hv : v.ctl = .pending c (.copy t s'))
    (hr : (Ctl.pending c (.copy t s')).resume matchTests false = c') (hρ : ρ t = ρ s')
    (h : iterS W ρ n { v with ctl := c', pos := Function.update v.pos t (v.pos s') } = r)
    (hoe : t ≠ OE ∧ s' ≠ OE := by decide) :
    iterS W ρ (n + 1) v = r := by
  simp only [iterS, stepS_eq hv ⟨hρ, hoe.1, hoe.2⟩, step_copy hv, Option.bind_some, hr]
  exact h

theorem runS_move {ms : List Movement} {π : String → ℤ} (hv : v.ctl = .pending c (.move ms))
    (hm : moveSeq blind v.len ms v.pos = some π)
    (hr : (Ctl.pending c (.move ms)).resume matchTests false = c')
    (hok : EvOk W ρ v.pos v.len (.move ms))
    (h : iterS W ρ n { v with ctl := c', pos := π } = r) :
    iterS W ρ (n + 1) v = r := by
  simp only [iterS, stepS_eq hv hok, step_move hv hm, Option.bind_some, hr]
  exact h

theorem runS_move1 {h : String} {d : ℤ} (hv : v.ctl = .pending c (.move [⟨h, d⟩]))
    (hrange : h ∉ blind → 0 ≤ v.pos h + d ∧ v.pos h + d ≤ v.len)
    (hr : (Ctl.pending c (.move [⟨h, d⟩])).resume matchTests false = c')
    (hW : h ∉ blind → ρ h = true → v.pos h + d ≤ W)
    (h' : iterS W ρ n { v with ctl := c', pos := Function.update v.pos h (v.pos h + d) } = r)
    (hoe : h ≠ OE := by decide) :
    iterS W ρ (n + 1) v = r := by
  refine runS_move hv (moveSeq_cons_ok _ _ _ _ _ hrange) hr ?_ h'
  refine evOk_move ?_ (by simpa using fun e => hoe e.symm)
  intro m hm hb hρh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm
  simpa [sumDelta] using hW hb hρh

theorem runS_moveAB (hv : v.ctl = .pending c (.move [⟨"A", 1⟩, ⟨"B", 1⟩]))
    (hA : 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len) (hB : 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len)
    (hr : (Ctl.pending c (.move [⟨"A", 1⟩, ⟨"B", 1⟩])).resume matchTests false = c')
    (hAW : v.pos "A" + 1 ≤ W) (hBW : v.pos "B" + 1 ≤ W)
    (h : iterS W ρ n { v with
      ctl := c'
      pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1) } = r) :
    iterS W ρ (n + 1) v = r := by
  refine runS_move hv (moveSeq_AB _ _ hA hB) hr ?_ h
  refine evOk_move ?_ (by decide)
  intro m hm _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simpa [sumDelta]

theorem runS_less {a b : String} {d : Bool} (hv : v.ctl = .pending c (.less a b))
    (hd : decide (v.pos a < v.pos b) = d)
    (hr : (Ctl.pending c (.less a b)).resume matchTests d = c')
    (h : iterS W ρ n { v with ctl := c' } = r) (hoe : a ≠ OE ∧ b ≠ OE := by decide) :
    iterS W ρ (n + 1) v = r := by
  simp only [iterS, stepS_eq hv hoe, step_less hv, Option.bind_some, hd, hr]
  exact h

theorem runS_equal {a b : String} {d : Bool} (hv : v.ctl = .pending c (.equal a b))
    (hd : decide (v.pos a = v.pos b) = d)
    (hr : (Ctl.pending c (.equal a b)).resume matchTests d = c')
    (h : iterS W ρ n { v with ctl := c' } = r) (hoe : a ≠ OE ∧ b ≠ OE := by decide) :
    iterS W ρ (n + 1) v = r := by
  simp only [iterS, stepS_eq hv hoe, step_equal hv, Option.bind_some, hd, hr]
  exact h

theorem runS_symbols {a b : String} {d : Bool} (hv : v.ctl = .pending c (.symbols a b))
    (ha : v.inRange a) (hb : v.inRange b)
    (hd : decide (v.word[(v.pos a).toNat]? = v.word[(v.pos b).toNat]?) = d)
    (hr : (Ctl.pending c (.symbols a b)).resume matchTests d = c')
    (hρa : ρ a = true) (hρb : ρ b = true) (haW : v.pos a < W) (hbW : v.pos b < W)
    (h : iterS W ρ n { v with ctl := c' } = r) (hoe : a ≠ OE ∧ b ≠ OE := by decide) :
    iterS W ρ (n + 1) v = r := by
  have hok : EvOk W ρ v.pos v.len (.symbols a b) := by
    refine ⟨?_, ?_, hoe.1, hoe.2⟩
    · simp only [OnSide, hρa, if_true]; exact ⟨ha.1, haW⟩
    · simp only [OnSide, hρb, if_true]; exact ⟨hb.1, hbW⟩
  simp only [iterS, stepS_eq hv hok, step_symbols hv ha hb, Option.bind_some, hd, hr]
  exact h

theorem iterS_zero_eq {c : Ctl} {π π' : String → ℤ} (h : π = π') :
    iterS W ρ 0 { v with ctl := c, pos := π } = some { v with ctl := c, pos := π' } := by
  subst h; rfl

/-- A guarded child run, placed inside its caller `f`. -/
theorem runS_child' (f : Frame) (v : HVM) (cs : Config) (e : Event)
    (hv : v.ctl = .pending (f :: cs) e) (hcs : cs ≠ []) (n : ℕ) (val : Value) (π : String → ℤ)
    (hrun : iterS W ρ n { v with ctl := .pending cs e } =
      some { v with ctl := .returned val, pos := π }) (c' : Ctl)
    (hc' : liftCtl f (.returned val) = c') :
    iterS W ρ n v = some { v with ctl := c', pos := π } := by
  have hl := iterS_lift (W := W) (ρ := ρ) f n { v with ctl := .pending cs e } _
    (by simp only [NonEmptyCtl]; exact hcs) hrun
  have e1 : liftVM f { v with ctl := .pending cs e } = v := by
    simp only [liftVM, liftCtl]; rw [← hv]
  have e3 : liftVM f { { v with ctl := .pending cs e } with ctl := .returned val, pos := π } =
      { v with ctl := c', pos := π } := by
    show { v with ctl := liftCtl f (.returned val), pos := π } = _
    rw [hc']
  rw [e1, e3] at hl
  exact hl

end Run

/-! ## `ResetShift k false`, guarded -/

section Shifts
variable {W : ℕ} {ρ : String → Bool}

theorem evOk_rsBackF (π : String → ℤ) (len : ℤ) (hA : π "A" - 1 ≤ W) :
    EvOk W ρ π len (.move [⟨"A", -1⟩]) := by
  refine evOk_move ?_ (by decide)
  intro m hm _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  subst hm; simpa [sumDelta] using hA

theorem evOk_rsShiftF (k : ℕ) (π : String → ℤ) (len : ℤ) (hP : π "P" + 1 ≤ W) :
    EvOk W ρ π len (.move [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) := by
  refine evOk_move ?_ (by simp [OE])
  intro m hm hb _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · simpa [sumDelta] using hP
  · exact absurd (by simp [blind]) hb

theorem rsF_firstS (k : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")) :
    iterS W ρ 1 v = some { v with ctl := rsLoopF k 0 (decide (v.pos "A" ≠ v.pos "Cut")) } :=
  iterS_one hv ⟨by decide, by decide⟩ (stepMatch_of_one (rsF_first k v hv))

theorem rsF_iterS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 < k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hAW : π "A" - j ≤ W) :
    iterS W ρ 2 v = some { v with ctl := rsLoopF k (ph + 1) ne, pos := rsPosF k π (j + 1) s } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPosF, hne]
  refine runS_equal hv hd (rsF_resume_back k ph ne) ?_
  refine runS_move (ms := [⟨"A", -1⟩]) (π := rsPosF k π (j + 1) s) rfl ?_
    (rsF_resume_step k ph ne hph) ?_ ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_back k π j s _ hA
  · show EvOk W ρ v.pos v.len _
    rw [hp]; exact evOk_rsBackF _ _ (by simp [rsPosF]; omega)
  rfl

theorem rsF_wrapS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 = k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len) (hAW : π "A" - j ≤ W)
    (hPW : π "P" + s + 1 ≤ W) :
    iterS W ρ 3 v = some { v with ctl := rsLoopF k 0 ne, pos := rsPosF k π (j + 1) (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPosF, hne]
  refine runS_equal hv hd (rsF_resume_back k ph ne) ?_
  refine runS_move (ms := [⟨"A", -1⟩]) (π := rsPosF k π (j + 1) s) rfl ?_
    (rsF_resume_wrap k ph ne hph) ?_ ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_back k π j s _ hA
  · show EvOk W ρ v.pos v.len _
    rw [hp]; exact evOk_rsBackF _ _ (by simp [rsPosF]; omega)
  refine runS_move (ms := [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) (π := rsPosF k π (j + 1) (s + 1)) rfl ?_
    (rsF_resume_after_wrap k (ph + 1) ne) ?_ ?_
  · show moveSeq blind v.len _ (rsPosF k π (j + 1) s) = _
    exact rsF_move_shift k π (j + 1) s _ hP
  · show EvOk W ρ (rsPosF k π (j + 1) s) v.len _
    exact evOk_rsShiftF k _ _ (by simp [rsPosF]; omega)
  rfl

theorem rsF_exit_shiftS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = true) (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len)
    (hPW : π "P" + s + 1 ≤ W) (hρBP : ρ "B" = ρ "P") :
    iterS W ρ 3 v = some { v with
      ctl := .returned none
      pos := Function.update (rsPosF k π j (s + 1)) "B" (π "P" + (s + 1)) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPosF, he]
  refine runS_equal hv hd (rsF_resume_exit_shift k ph ne h) ?_
  refine runS_move (ms := [⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) (π := rsPosF k π j (s + 1)) rfl ?_
    (rsF_resume_after_exit k ph ne) ?_ ?_
  · show moveSeq blind v.len _ v.pos = _
    rw [hp]; exact rsF_move_shift k π j s _ hP
  · show EvOk W ρ v.pos v.len _
    rw [hp]; exact evOk_rsShiftF k _ _ (by simp [rsPosF]; omega)
  refine runS_copy rfl (rsF_resume_done k ph ne) hρBP ?_
  refine iterS_zero_eq ?_
  simp only [rsPosF_P]

theorem rsF_exit_tailS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoopF k ph ne) (hp : v.pos = rsPosF k π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = false) (hρBP : ρ "B" = ρ "P") :
    iterS W ρ 2 v = some { v with
      ctl := .returned none
      pos := Function.update (rsPosF k π j s) "B" (π "P" + s) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPosF, he]
  refine runS_equal hv hd (rsF_resume_exit_tail k ph ne h) ?_
  refine runS_copy rfl (rsF_resume_done k ph ne) hρBP ?_
  refine iterS_zero_eq ?_
  simp only [hp, rsPosF_P]

theorem rsF_loop_runS (k : ℕ) (hk : 1 ≤ k) (π : String → ℤ) (L : ℤ) (ne : Bool) (q : ℕ)
    (hne : ne = decide (q ≠ 0)) (hAW : π "A" ≤ W) (hPW : π "P" + (q / k : ℕ) + 1 ≤ W)
    (hρBP : ρ "B" = ρ "P") :
    ∀ (m : ℕ) (v : HVM) (j sh : ℕ), j + m = q → sh = j / k → v.ctl = rsLoopF k (j % k) ne →
      v.pos = rsPosF k π j sh → v.len = L →
      π "A" - q = π "Cut" → 0 ≤ π "Cut" → π "A" - j ≤ L → 0 ≤ π "P" →
      π "P" + (q / k : ℕ) + 1 ≤ L →
      ∃ n, n ≤ 3 * m + 3 ∧
        iterS W ρ n v = some { v with
          ctl := .returned none
          pos := Function.update (rsPosF k π q (rsShifts k q : ℕ)) "B"
            (π "P" + (rsShifts k q : ℕ)) }
  | 0, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hP0, hPL => by
    have hj : j = q := by omega
    subst hj
    have hshq : sh = j / k := hsh
    by_cases hx : (!ne || j % k != 0) = true
    · refine ⟨3, by omega, ?_⟩
      rw [rsF_exit_shiftS k (j % k) ne v π j sh hv hp (by omega) hx
        ⟨by positivity, by rw [hshq]; omega⟩ (by rw [hshq]; omega) hρBP]
      have : (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx; simp at hx
        rcases hx with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      simp only [rsShifts, if_pos this, hshq, Nat.cast_add, Nat.cast_one]
    · refine ⟨2, by omega, ?_⟩
      have hx' : (!ne || j % k != 0) = false := by simpa using hx
      rw [rsF_exit_tailS k (j % k) ne v π j sh hv hp (by omega) hx' hρBP]
      have : ¬ (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx'; simp at hx'; omega
      simp only [rsShifts, if_neg this, Nat.add_zero, ← hshq]
  | m + 1, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hP0, hPL => by
    obtain ⟨hs1, hs2⟩ := modstep j k hk
    have hjq : sh ≤ q / k := by rw [hsh]; exact Nat.div_le_div_right (by omega)
    rcases Nat.lt_or_ge (j % k + 1) k with hph | hph
    · obtain ⟨hm1, hd1⟩ := hs1 hph
      have hstep := rsF_iterS (W := W) (ρ := ρ) k (j % k) ne v π j sh hv hp (by omega) hph
        ⟨by omega, by omega⟩ (by omega)
      obtain ⟨n, hn, hrun⟩ := rsF_loop_runS k hk π L ne q hne hAW hPW hρBP m
        { v with ctl := rsLoopF k (j % k + 1) ne, pos := rsPosF k π (↑j + 1) sh } (j + 1) sh
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hP0 hPL
      refine ⟨2 + n, by omega, ?_⟩
      rw [iterS_add, hstep, Option.bind_some, hrun]
    · have hph' : j % k + 1 = k := by have := Nat.mod_lt j (show 0 < k by omega); omega
      obtain ⟨hm1, hd1⟩ := hs2 hph'
      have hj1 : sh + 1 ≤ q / k := by
        rw [hsh, ← hd1]; exact Nat.div_le_div_right (by omega)
      have hstep := rsF_wrapS (W := W) (ρ := ρ) k (j % k) ne v π j sh hv hp (by omega) hph'
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      obtain ⟨n, hn, hrun⟩ := rsF_loop_runS k hk π L ne q hne hAW hPW hρBP m
        { v with ctl := rsLoopF k 0 ne, pos := rsPosF k π (↑j + 1) (↑sh + 1) } (j + 1) (sh + 1)
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hP0 hPL
      refine ⟨3 + n, by omega, ?_⟩
      rw [iterS_add, hstep, Option.bind_some, hrun]

/-- **`ResetShift k false` under the side conditions**: `ScaHeadDecompose.resetShiftF_run`,
guarded; `A` and the shifted `P` stay `≤ W`. -/
theorem resetShiftF_runS (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = .pending [.resetShift k false 0 none 1] (.equal "A" "Cut"))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hP0 : 0 ≤ v.pos "P") (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len)
    (hAW : v.pos "A" ≤ W) (hPW : v.pos "P" + (q / k : ℕ) + 1 ≤ W) (hρBP : ρ "B" = ρ "P") :
    ∃ n, n ≤ 3 * q + 4 ∧
      iterS W ρ n v = some { v with
        ctl := .returned none
        pos := Function.update (rsPosF k v.pos q (rsShifts k q : ℕ)) "B"
          (v.pos "P" + (rsShifts k q : ℕ)) } := by
  have h1 := rsF_firstS (W := W) (ρ := ρ) k v hv
  have hne : decide (v.pos "A" ≠ v.pos "Cut") = decide (q ≠ 0) := by
    simp only [decide_eq_decide]; omega
  rw [hne] at h1
  obtain ⟨n, hn, hrun⟩ := rsF_loop_runS (W := W) (ρ := ρ) k hk v.pos v.len (decide (q ≠ 0)) q rfl
    hAW hPW hρBP q
    { v with ctl := rsLoopF k 0 (decide (q ≠ 0)) } 0 0 (by omega) (by simp) (by simp)
    (by simp [rsPosF_zero]) rfl (by omega) hC (by simp; omega) hP0 hPL
  refine ⟨1 + n, by omega, ?_⟩
  rw [iterS_add, h1, Option.bind_some, hrun]

/-! ## `PeriodShift k false`, guarded -/

theorem evOk_psMoveF (k : ℕ) (π : String → ℤ) (len : ℤ) (hW : π "Walk" + 1 ≤ W)
    (hA : π "A" - 1 ≤ W) (hP : π "P" + 1 ≤ W) :
    EvOk W ρ π len (.move [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩]) := by
  refine evOk_move ?_ (by simp [OE])
  intro m hm hb _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · simpa [sumDelta] using hW
  · simpa [sumDelta] using hA
  · simpa [sumDelta] using hP
  · exact absurd (by simp [blind]) hb

theorem psF_loop_runS (k : ℕ) (π : String → ℤ) (L : ℤ) (hFW : π "First" ≤ W)
    (hAW : π "A" ≤ W) :
    ∀ (m : ℕ) (v : HVM) (i : ℤ), v.ctl = psLoopF k → v.pos = psPosF k π i → v.len = L →
      π "Cut" + i + m = π "First" → 0 ≤ π "Cut" + i → π "First" ≤ L →
      0 ≤ π "A" - (i + m) → π "A" - i ≤ L → 0 ≤ π "P" + i → π "P" + i + m ≤ L → 0 ≤ i →
      π "P" + i + m ≤ W →
      iterS W ρ (2 * m + 1) v = some { v with ctl := .returned none, pos := psPosF k π (i + m) }
  | 0, v, i, hv, hp, _, he, _, _, _, _, _, _, _, _ => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPosF]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPosF]
    refine runS_less hv (d := false) (by simp; omega) (psF_resume_stop k) ?_
    refine iterS_zero_eq ?_
    simp [hp]
  | m + 1, v, i, hv, hp, hL, he, h1, h2, h3, h4, h5, h6, hi, hPW => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPosF]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPosF]
    have hrec := psF_loop_runS k π L hFW hAW m
      { v with ctl := psLoopF k, pos := psPosF k π (i + 1) } (i + 1)
      rfl rfl hL (by push_cast at he; omega) (by omega) h2 (by push_cast at h3; omega) (by omega)
      (by omega) (by push_cast at h6; omega) (by omega) (by push_cast at hPW; omega)
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring]
    refine runS_less hv (d := true) (by simp; omega) (psF_resume_go k) ?_
    refine runS_move (ms := [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", (k : ℤ)⟩])
      (π := psPosF k π (i + 1)) rfl ?_ (psF_resume_moved k) ?_ ?_
    · show moveSeq blind v.len _ v.pos = _
      rw [hp]
      exact psF_move k π i _ ⟨by omega, by omega⟩ ⟨by push_cast at h3; omega, by omega⟩
        ⟨by omega, by push_cast at h6; omega⟩
    · show EvOk W ρ v.pos v.len _
      rw [hp]
      exact evOk_psMoveF k _ _ (by simp [psPosF]; push_cast at he; omega)
        (by simp [psPosF]; omega) (by simp [psPosF]; push_cast at hPW; omega)
    rw [show ((i + (m + 1 : ℕ)) : ℤ) = i + 1 + m by push_cast; ring]
    exact hrec

/-- **`PeriodShift k false` under the side conditions**: `ScaHeadDecompose.periodShiftF_run`,
guarded; `Walk` ends at `First ≤ W`, `P` at `P + t ≤ W`. -/
theorem periodShiftF_runS (k : ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = .pending [.periodShift k false 1] (.copy "Walk" "Cut"))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len)
    (hFW : v.pos "First" ≤ W) (hAW : v.pos "A" ≤ W) (hPW : v.pos "P" + t ≤ W)
    (hρ : ρ "Walk" = ρ "Cut") :
    iterS W ρ (2 * t + 2) v = some { v with ctl := .returned none, pos := psPosF k v.pos t } := by
  rw [show 2 * t + 2 = (2 * t + 1) + 1 by ring]
  refine runS_copy hv (psF_resume_start k) hρ ?_
  have := psF_loop_runS (W := W) (ρ := ρ) k v.pos v.len hFW hAW t
    { v with ctl := psLoopF k, pos := psPosF k v.pos 0 } 0 rfl
    rfl rfl (by omega) (by omega) hF (by omega) (by omega) (by omega) (by omega) le_rfl (by omega)
  rw [psPosF_zero] at this
  simpa using this

/-! ## `Initialize k`, guarded -/

/-- **`Initialize` under the side conditions**: its copies keep the orientation of `Cut`, and
`P = Cut + 1 ≤ W`. -/
theorem init_runS (k : ℕ) (v : HVM) (hv : v.ctl = .pending [.initialize k 1] (.copy "A" "Cut"))
    (hC : 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len) (hCW : v.pos "Cut" + 1 ≤ W)
    (hρA : ρ "A" = ρ "Cut") (hρP : ρ "P" = ρ "Cut") (hρB : ρ "B" = ρ "P")
    (hρK : ρ "KP" = ρ "Cut") :
    iterS W ρ 6 v = some { v with ctl := .returned none, pos := initPos k v.pos } := by
  refine runS_copy hv (c' := .pending [.initialize k 2] (.copy "P" "Cut")) rfl hρA ?_
  refine runS_copy rfl (c' := .pending [.initialize k 3] (mv [("P", 1)])) rfl hρP ?_
  refine runS_move1 rfl (fun _ => by simp only [HVM.len] at hC ⊢; simp; constructor <;> omega)
    (c' := .pending [.initialize k 4] (.copy "B" "P")) rfl (fun _ _ => by simp; omega) ?_
  refine runS_copy rfl (c' := .pending [.initialize k 5] (.copy "KP" "Cut")) rfl hρB ?_
  refine runS_copy rfl (c' := .pending [.initialize k 6] (mv [("KP", (k : ℤ))])) rfl hρK ?_
  refine runS_move1 rfl (fun hb => absurd (by simp [blind]) hb) (c' := .returned none) rfl
    (fun hb => absurd (by simp [blind]) hb) ?_
  refine iterS_zero_eq ?_
  funext h
  by_cases h1 : h = "A" <;> by_cases h2 : h = "P" <;> by_cases h3 : h = "B" <;>
    by_cases h4 : h = "KP" <;> simp_all [initPos]

end Shifts

/-! ## `First k bounded`, guarded -/

section First
variable {W : ℕ} {ρ : String → Bool}

/-- **`First`'s inner loop** (sites 4–7) computes `firstInner`, in fewer than `4·work` steps. -/
theorem first_innerS (k : ℕ) (hk : 1 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s p : ℕ)
    (π0 : String → ℤ) (hp : 0 < p) (hsx : s ≤ x.length) (hE : π0 "End" = x.length)
    (hρ : DecOrient ρ) :
    ∀ (fuel q : ℕ) (v : HVM), v.ctl = .pending [.first k b 4] (.less "B" "End") →
      v.word = x ++ rest → HRel fHeads k s p q π0 v.pos →
      p + q ≤ (x.drop s).length → (x.drop s).length ≤ fuel + q →
      ∃ n π', n + 1 ≤ 4 * firstInnerWork (x.drop s) k p fuel q ∧
        firstInner (x.drop s) k p fuel q + 1 ≤ firstInnerWork (x.drop s) k p fuel q + q ∧
        iterS x.length ρ n v = some { v with
          ctl := .pending [.first k b 8] (.equal "B" "KP")
          pos := π' } ∧
        HRel fHeads k s p (firstInner (x.drop s) k p fuel q) π0 π' := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  have hkp := nat_kp k p hk
  intro fuel
  induction fuel with
  | zero => intro q v _ _ _ hpq hf; omega
  | succ fuel ih =>
    intro q v hv hw hR hpq hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases h1 : p + q < (x.drop s).length
    · by_cases h2 : q < (k - 1) * p
      · by_cases h3 : (x.drop s)[q]? = (x.drop s)[p + q]?
        · have hc : p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
              (x.drop s)[q]? = (x.drop s)[p + q]? := ⟨h1, h2, h3⟩
          obtain ⟨n, π', hn, hq', hrun, hR'⟩ := ih (q + 1)
            { v with
              ctl := .pending [.first k b 4] (.less "B" "End")
              pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
                (v.pos "B" + 1) }
            rfl hw (hrel_AB ⟨hA, hP, hB, hK, hkeep⟩ (by simp [fHeads]) (by simp [fHeads]))
            (by omega) (by omega)
          refine ⟨n + 1 + 1 + 1 + 1, π', ?_, ?_, ?_, ?_⟩
          · rw [firstInnerWork, if_pos hc]; omega
          · rw [firstInnerWork, if_pos hc, firstInner, if_pos hc]; omega
          · refine runS_less hv (d := true) (by simp; omega) (fr4t k b) ?_
            refine runS_less rfl (d := true) (by simp; omega) (fr5t k b) ?_
            refine runS_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
              (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (fr6t k b) hρ.a hρ.b
              (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
            · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
              rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
                (by rw [hB]; push_cast; ring)]
              exact decide_eq_true h3
            refine runS_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
              (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (fr7 k b)
              (show v.pos "A" + 1 ≤ (x.length : ℤ) by omega)
              (show v.pos "B" + 1 ≤ (x.length : ℤ) by omega) ?_
            exact hrun
          · rw [firstInner, if_pos hc]; exact hR'
        · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
              (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h3 h.2.2
          refine ⟨1 + 1 + 1, v.pos, ?_, ?_, ?_, ?_⟩
          · rw [firstInnerWork, if_neg hc]; try omega
          · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
          · refine runS_less hv (d := true) (by simp; omega) (fr4t k b) ?_
            refine runS_less rfl (d := true) (by simp; omega) (fr5t k b) ?_
            refine runS_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
              (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (fr6f k b) hρ.a hρ.b
              (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
            · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
              rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
                (by rw [hB]; push_cast; ring)]
              exact decide_eq_false h3
            exact iterS_zero_eq rfl
          · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩
      · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
            (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h2 h.2.1
        refine ⟨1 + 1, v.pos, ?_, ?_, ?_, ?_⟩
        · rw [firstInnerWork, if_neg hc]; try omega
        · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
        · refine runS_less hv (d := true) (by simp; omega) (fr4t k b) ?_
          refine runS_less rfl (d := false) (by simp; omega) (fr5f k b) ?_
          exact iterS_zero_eq rfl
        · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩
    · have hc : ¬ (p + q < (x.drop s).length ∧ q < (k - 1) * p ∧
          (x.drop s)[q]? = (x.drop s)[p + q]?) := fun h => h1 h.1
      refine ⟨1, v.pos, ?_, ?_, ?_, ?_⟩
      · rw [firstInnerWork, if_neg hc]; try omega
      · rw [firstInnerWork, if_neg hc, firstInner, if_neg hc]; try omega
      · refine runS_less hv (d := false) (by simp; omega) (fr4f k b) ?_
        exact iterS_zero_eq rfl
      · rw [firstInner, if_neg hc]; exact ⟨hA, hP, hB, hK, hkeep⟩

/-- Entering `First`'s inner loop from its outer head: one test, or two when bounded. -/
theorem first_enterS (k : ℕ) (b : Bool) (v : HVM)
    (hv : v.ctl = .pending [.first k b 2] (.less "P" "End"))
    (h1 : v.pos "P" < v.pos "End") (h2 : b = true → v.pos "P" < v.pos "Second")
    (n : ℕ) (r : Option HVM)
    (h : iterS W ρ n { v with ctl := .pending [.first k b 4] (.less "B" "End") } = r) :
    ∃ m, m ≤ 2 ∧ iterS W ρ (n + m) v = r := by
  cases b with
  | false =>
    exact ⟨1, by omega, runS_less hv (d := true) (by simp; omega) (fr2t_false k) h⟩
  | true =>
    refine ⟨2, le_refl _, ?_⟩
    show iterS W ρ (n + 1 + 1) v = r
    refine runS_less hv (d := true) (by simp; omega) (fr2t_true k) ?_
    exact runS_less rfl (d := true) (by simp; exact h2 rfl) (fr3t k) h

set_option maxHeartbeats 1000000 in
/-- **`First`'s outer loop** (sites 2–9) computes `firstOuter`, in `10·work + 2` steps. -/
theorem first_outerS (k : ℕ) (hk : 2 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s bnd : ℕ)
    (π0 : String → ℤ) (hsx : s ≤ x.length) (hC : π0 "Cut" = s) (hE : π0 "End" = x.length)
    (hbT : b = true → π0 "Second" = (s : ℤ) + bnd)
    (hbF : b = false → (x.drop s).length ≤ bnd) (hρ : DecOrient ρ) :
    ∀ (fuel p : ℕ) (v : HVM), v.ctl = .pending [.first k b 2] (.less "P" "End") →
      v.word = x ++ rest → HRel fHeads k s p 0 π0 v.pos →
      0 < p → (x.drop s).length + 1 ≤ fuel + p →
      ∃ n π', n ≤ 10 * firstOuterWork (x.drop s) k bnd fuel p + 2 ∧
        iterS x.length ρ n v = some { v with
          ctl := .returned (some (firstOuter (x.drop s) k bnd fuel p).isSome)
          pos := π' } ∧
        Keeps fHeads π0 π' ∧
        ∀ p₁ m, firstOuter (x.drop s) k bnd fuel p = some (p₁, m) →
          HRel fHeads k s p₁ ((k - 1) * p₁) π0 π' := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  intro fuel
  induction fuel with
  | zero =>
    intro p v hv hw hR hp hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    refine ⟨1, v.pos, by simp [firstOuterWork], ?_, hkeep, by simp [firstOuter]⟩
    exact runS_less hv (d := false) (by simp; omega) (fr2f k b) (iterS_zero_eq rfl)
  | succ fuel ih =>
    intro p v hv hw hR hp hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [fHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hg1 : p < (x.drop s).length
    · by_cases hg2 : p < bnd
      · have hg : p < (x.drop s).length ∧ p < bnd := ⟨hg1, hg2⟩
        obtain ⟨q', hq'⟩ : ∃ q', firstInner (x.drop s) k p ((x.drop s).length + 1) 0 = q' :=
          ⟨_, rfl⟩
        have hqle := firstInner_le (x.drop s) k p ((x.drop s).length + 1) 0 (by omega)
        rw [hq'] at hqle
        obtain ⟨nin, πin, hnin, hqin, hrunin, hRin⟩ := first_innerS k (by omega) b x rest s p π0 hp
          hsx hE hρ ((x.drop s).length + 1) 0
          { v with ctl := .pending [.first k b 4] (.less "B" "End") } rfl hw
          ⟨hA, hP, hB, hK, hkeep⟩ (by omega) (by omega)
        rw [hq'] at hqin hRin
        have hkp := nat_kp k p (by omega)
        have hPS : b = true → v.pos "P" < v.pos "Second" := fun hb => by
          have h1 := hbT hb
          have h2 := hkeep "Second" (by simp [fHeads])
          omega
        obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hRin
        by_cases heq : q' = (k - 1) * p
        · have hfo : firstOuter (x.drop s) k bnd (fuel + 1) p = some (p, p + (k - 1) * p) := by
            rw [firstOuter, if_pos hg, hq', if_pos heq]
          have hwk : firstOuterWork (x.drop s) k bnd (fuel + 1) p =
              1 + firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 := by
            rw [firstOuterWork, if_pos hg, hq', if_pos heq, Nat.add_zero]
          have hC_ := iterS_trans hrunin
            (runS_equal rfl (d := true) (by simp; omega) (fr8t k b) (iterS_zero_eq rfl))
          obtain ⟨m, hm, hD⟩ := first_enterS k b v hv (by omega) hPS _ _ hC_
          refine ⟨nin + (0 + 1) + m, πin, ?_, ?_, hkeep2, ?_⟩
          · rw [hwk]; omega
          · rw [hfo]; exact hD
          · rw [hfo]
            rintro p₁ m' h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rw [← heq]
            exact ⟨hA2, hP2, hB2, hK2, hkeep2⟩
        · have ht := rsShifts_eq k q' (by omega)
          have hfo : firstOuter (x.drop s) k bnd (fuel + 1) p =
              firstOuter (x.drop s) k bnd fuel (p + shiftNoPeriod q' k) := by
            rw [firstOuter, if_pos hg, hq', if_neg heq]
          have hwk : firstOuterWork (x.drop s) k bnd (fuel + 1) p =
              1 + firstInnerWork (x.drop s) k p ((x.drop s).length + 1) 0 +
                firstOuterWork (x.drop s) k bnd fuel (p + shiftNoPeriod q' k) := by
            rw [firstOuterWork, if_pos hg, hq', if_neg heq]
          have hsp1 := shiftNoPeriod_pos q' k
          have hsmax := shiftNoPeriod_le_max q' k (by omega)
          have hdiv : p + q' / k + 1 ≤ (x.drop s).length := by
            rcases Nat.eq_zero_or_pos q' with h0 | h0
            · subst h0; simp; omega
            · have := div_succ_le q' k hk h0; omega
          obtain ⟨nrs, hnrs, hrs⟩ := resetShiftF_runS k (by omega)
            { v with
              ctl := .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin } q' rfl
            (by show πin "A" = πin "Cut" + q'
                have := hkeep2 "Cut" (by simp [fHeads]); omega)
            (by show 0 ≤ πin "Cut"; have := hkeep2 "Cut" (by simp [fHeads]); omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ v.len; omega)
            (by show πin "A" ≤ (x.length : ℤ); omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ (x.length : ℤ); omega) (hρ.b.trans hρ.p.symm)
          rw [ht] at hrs
          have hchild := runS_child' (.first k b 9)
            { v with
              ctl := .pending [.first k b 9, .resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin }
            [.resetShift k false 0 none 1] (.equal "A" "Cut") rfl (by simp) nrs none
            (Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
              (πin "P" + (shiftNoPeriod q' k : ℕ))) hrs _ (fr9 k b)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hrelrec⟩ := ih (p + shiftNoPeriod q' k)
            { v with
              ctl := .pending [.first k b 2] (.less "P" "End")
              pos := Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
                (πin "P" + (shiftNoPeriod q' k : ℕ)) }
            rfl hw
            (hrel_reset (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads])
              (by simp [fHeads]) ⟨hA2, hP2, hB2, hK2, hkeep2⟩ _)
            (by omega) (by omega)
          have hA_ := iterS_trans hchild hrunrec
          have hB_ := runS_equal (v := { v with
              ctl := .pending [.first k b 8] (.equal "B" "KP")
              pos := πin }) rfl (d := false) (by simp; omega) (fr8f k b) hA_
          have hC_ := iterS_trans hrunin hB_
          obtain ⟨m, hm, hD⟩ := first_enterS k b v hv (by omega) hPS _ _ hC_
          refine ⟨nin + (nrs + nrec + 1) + m, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; omega
          · rw [hfo]; exact hD
          · rw [hfo]; exact hrelrec
      · obtain rfl : b = true := by
          cases b
          · exact absurd (hbF rfl) (by omega)
          · rfl
        have hng : ¬ (p < (x.drop s).length ∧ p < bnd) := fun h => hg2 h.2
        have hS : v.pos "Second" = (s : ℤ) + bnd := (hkeep "Second" (by simp [fHeads])).trans (hbT rfl)
        refine ⟨2, v.pos, by omega, ?_, hkeep, ?_⟩
        · rw [firstOuter, if_neg hng]
          show iterS x.length ρ (0 + 1 + 1) v = _
          refine runS_less hv (d := true) (by simp; omega) (fr2t_true k) ?_
          exact runS_less rfl (d := false) (by simp; omega) (fr3f k) (iterS_zero_eq rfl)
        · rw [firstOuter, if_neg hng]; simp
    · have hng : ¬ (p < (x.drop s).length ∧ p < bnd) := fun h => hg1 h.1
      refine ⟨1, v.pos, by omega, ?_, hkeep, ?_⟩
      · rw [firstOuter, if_neg hng]
        exact runS_less hv (d := false) (by simp; omega) (fr2f k b) (iterS_zero_eq rfl)
      · rw [firstOuter, if_neg hng]; simp

/-- **`First k bounded`, from its fresh frame**: it returns whether `firstOuter` finds a period
(`bnd` is `Second − Cut` when bounded, any bound `≥ |x| − s` otherwise), within
`10·firstOuterWork + 8` steps; when it finds `p₁`, `P = s + p₁`, `B = KP = s + k·p₁`. -/
theorem first_runS (k : ℕ) (hk : 2 ≤ k) (b : Bool) (x rest : List (Fin 2)) (s bnd fuel : ℕ)
    (v : HVM) (hv : v.ctl = .pending [.first k b 1, .initialize k 1] (.copy "A" "Cut"))
    (hw : v.word = x ++ rest) (hC : v.pos "Cut" = s) (hE : v.pos "End" = x.length)
    (hsx : s ≤ x.length) (hs1 : s + 1 ≤ x.length)
    (hbT : b = true → v.pos "Second" = (s : ℤ) + bnd)
    (hbF : b = false → (x.drop s).length ≤ bnd) (hf : (x.drop s).length ≤ fuel)
    (hρ : DecOrient ρ) :
    ∃ n π', n ≤ 10 * firstOuterWork (x.drop s) k bnd fuel 1 + 8 ∧
      iterS x.length ρ n v = some { v with
        ctl := .returned (some (firstOuter (x.drop s) k bnd fuel 1).isSome)
        pos := π' } ∧
      Keeps fHeads v.pos π' ∧
      ∀ p₁ m, firstOuter (x.drop s) k bnd fuel 1 = some (p₁, m) →
        HRel fHeads k s p₁ ((k - 1) * p₁) v.pos π' := by
  have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
  have hinit := init_runS (W := x.length) (ρ := ρ) k
    { v with ctl := .pending [.initialize k 1] (.copy "A" "Cut") } rfl
    (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)
    (show v.pos "Cut" + 1 ≤ (x.length : ℤ) by omega) (hρ.a.trans hρ.cut.symm)
    (hρ.p.trans hρ.cut.symm) (hρ.b.trans hρ.p.symm) (hρ.kp.trans hρ.cut.symm)
  have hchild := runS_child' (.first k b 1) v [.initialize k 1] (.copy "A" "Cut") hv (by simp) 6
    none (initPos k v.pos) hinit _ (fr_init k b)
  obtain ⟨n, π', hn, hrun, hkeep, hrel⟩ := first_outerS k hk b x rest s bnd v.pos hsx hC hE hbT
    hbF hρ fuel 1 { v with ctl := .pending [.first k b 2] (.less "P" "End"), pos := initPos k v.pos }
    rfl hw (hrel_init (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads]) (by simp [fHeads])
      k s v.pos hC) (by omega) (by omega)
  exact ⟨6 + n, π', by omega, iterS_trans hchild hrun, hkeep, hrel⟩

end First

/-! ## `Second k`, guarded -/

section Second
variable {W : ℕ} {ρ : String → Bool}

/-- **`Second`'s inner loop** (sites 3–7) computes `secondInner`. -/
theorem second_innerS (k : ℕ) (hk : 1 ≤ k) (x rest : List (Fin 2)) (s p r : ℕ)
    (π0 : String → ℤ) (hp : 0 < p) (hsx : s ≤ x.length) (hE : π0 "End" = x.length)
    (hR0 : π0 "Reach" = (s : ℤ) + r) (hρ : DecOrient ρ) :
    ∀ (fuel q : ℕ) (v : HVM), v.ctl = .pending [.second k 3] (.less "B" "End") →
      v.word = x ++ rest → HRel sHeads k s p q π0 v.pos →
      p + q ≤ (x.drop s).length → (x.drop s).length ≤ fuel + q →
      (∀ q', secondInner (x.drop s) k p r fuel q = some q' →
        ∃ n π', n + 3 ≤ 5 * secondInnerWork (x.drop s) k p r fuel q ∧
          q' + 1 ≤ secondInnerWork (x.drop s) k p r fuel q + q ∧
          iterS x.length ρ n v = some { v with
            ctl := .pending [.second k 8] (.less "A" "KFirst")
            pos := π' } ∧
          HRel sHeads k s p q' π0 π') ∧
      (secondInner (x.drop s) k p r fuel q = none →
        ∃ n π', n ≤ 5 * secondInnerWork (x.drop s) k p r fuel q ∧
          iterS x.length ρ n v = some { v with ctl := .returned (some true), pos := π' } ∧
          Keeps sHeads π0 π' ∧ π' "P" = (s : ℤ) + p) := by
  have hlen : (x.drop s).length = x.length - s := List.length_drop ..
  have hkp := nat_kp k p hk
  intro fuel
  induction fuel with
  | zero => intro q v _ _ _ hpq hf; omega
  | succ fuel ih =>
    intro q v hv hw hR hpq hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    have hR' : v.pos "Reach" = (s : ℤ) + r := (hkeep "Reach" (by simp [sHeads])).trans hR0
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hc : p + q < (x.drop s).length ∧ (x.drop s)[q]? = (x.drop s)[p + q]?
    · obtain ⟨h1, h3⟩ := hc
      -- the three steps to the `Reach < B` test
      have hpre : ∀ (n : ℕ) (rr : Option HVM),
          iterS x.length ρ n { v with
            ctl := .pending [.second k 6] (.less "Reach" "B")
            pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
              (v.pos "B" + 1) } = rr →
          iterS x.length ρ (n + 1 + 1 + 1) v = rr := by
        intro n rr h
        refine runS_less hv (d := true) (by simp; omega) (sr3t k) ?_
        refine runS_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (sr4t k) hρ.a hρ.b
          (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
          rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
            (by rw [hB]; push_cast; ring)]
          exact decide_eq_true h3
        refine runS_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
          (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (sr5 k)
          (show v.pos "A" + 1 ≤ (x.length : ℤ) by omega)
          (show v.pos "B" + 1 ≤ (x.length : ℤ) by omega) ?_
        exact h
      have hR1 := hrel_AB ⟨hA, hP, hB, hK, hkeep⟩ (by simp [sHeads]) (by simp [sHeads])
      by_cases hfire : r < p + (q + 1) ∧ (k - 1) * p ≤ q + 1
      · have hsi : secondInner (x.drop s) k p r (fuel + 1) q = none := by
          rw [secondInner, if_pos ⟨h1, h3⟩, if_pos hfire]
        have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q = 1 := by
          rw [secondInnerWork, if_pos ⟨h1, h3⟩, if_pos hfire]
        refine ⟨fun q' h => by rw [hsi] at h; exact absurd h (by simp), fun _ => ?_⟩
        refine ⟨0 + 1 + 1 + 1 + 1 + 1, _, by rw [hwk], ?_, hR1.2.2.2.2, by simp [hP]⟩
        refine hpre _ _ ?_
        refine runS_less rfl (d := true) (by simp [hR', hB]; omega) (sr6t k) ?_
        refine runS_less rfl (d := false) (by simp [hB, hK]; omega) (sr7f k) ?_
        exact iterS_zero_eq rfl
      · have hsi : secondInner (x.drop s) k p r (fuel + 1) q =
            secondInner (x.drop s) k p r fuel (q + 1) := by
          rw [secondInner, if_pos ⟨h1, h3⟩, if_neg hfire]
        have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q =
            1 + secondInnerWork (x.drop s) k p r fuel (q + 1) := by
          rw [secondInnerWork, if_pos ⟨h1, h3⟩, if_neg hfire]
        -- back at the inner head with `q + 1`, after 4 or 5 steps
        have hback : ∀ (n : ℕ) (rr : Option HVM),
            iterS x.length ρ n { v with
              ctl := .pending [.second k 3] (.less "B" "End")
              pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
                (v.pos "B" + 1) } = rr →
            ∃ m, m ≤ 5 ∧ iterS x.length ρ (n + m) v = rr := by
          intro n rr h
          by_cases h6 : r < p + (q + 1)
          · have h7 : ¬ ((k - 1) * p ≤ q + 1) := fun h' => hfire ⟨h6, h'⟩
            refine ⟨5, le_refl _, ?_⟩
            show iterS x.length ρ (n + 1 + 1 + 1 + 1 + 1) v = rr
            refine hpre _ _ ?_
            refine runS_less rfl (d := true) (by simp [hR', hB]; omega) (sr6t k) ?_
            exact runS_less rfl (d := true) (by simp [hB, hK]; omega) (sr7t k) h
          · refine ⟨4, by omega, ?_⟩
            show iterS x.length ρ (n + 1 + 1 + 1 + 1) v = rr
            refine hpre _ _ ?_
            exact runS_less rfl (d := false) (by simp [hR', hB]; omega) (sr6f k) h
        obtain ⟨ihs, ihn⟩ := ih (q + 1)
          { v with
            ctl := .pending [.second k 3] (.less "B" "End")
            pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B"
              (v.pos "B" + 1) }
          rfl hw hR1 (by omega) (by omega)
        refine ⟨fun q' h => ?_, fun h => ?_⟩
        · rw [hsi] at h
          obtain ⟨n, π', hn, hq', hrun, hR'⟩ := ihs q' h
          obtain ⟨m, hm, hrun'⟩ := hback _ _ hrun
          exact ⟨n + m, π', by rw [hwk]; omega, by rw [hwk]; omega, hrun', hR'⟩
        · rw [hsi] at h
          obtain ⟨n, π', hn, hrun, hkp', hP'⟩ := ihn h
          obtain ⟨m, hm, hrun'⟩ := hback _ _ hrun
          exact ⟨n + m, π', by rw [hwk]; omega, hrun', hkp', hP'⟩
    · have hsi : secondInner (x.drop s) k p r (fuel + 1) q = some q := by
        rw [secondInner, if_neg hc]
      have hwk : secondInnerWork (x.drop s) k p r (fuel + 1) q = 1 := by
        rw [secondInnerWork, if_neg hc]
      refine ⟨fun q' h => ?_, fun h => by rw [hsi] at h; exact absurd h (by simp)⟩
      rw [hsi] at h
      obtain rfl : q = q' := Option.some.inj h
      by_cases h1 : p + q < (x.drop s).length
      · have h3 : ¬ (x.drop s)[q]? = (x.drop s)[p + q]? := fun h' => hc ⟨h1, h'⟩
        refine ⟨0 + 1 + 1, v.pos, by rw [hwk], by rw [hwk]; omega, ?_,
          ⟨hA, hP, hB, hK, hkeep⟩⟩
        refine runS_less hv (d := true) (by simp; omega) (sr3t k) ?_
        refine runS_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (sr4f k) hρ.a hρ.b
          (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
          rw [hw, sym_decide x rest s q (p + q) (by omega) (by omega) _ _ hA
            (by rw [hB]; push_cast; ring)]
          exact decide_eq_false h3
        exact iterS_zero_eq rfl
      · refine ⟨0 + 1, v.pos, by rw [hwk]; omega, by rw [hwk]; omega, ?_, ⟨hA, hP, hB, hK, hkeep⟩⟩
        exact runS_less hv (d := false) (by simp; omega) (sr3f k) (iterS_zero_eq rfl)

/-- From `Second`'s decision point, the reset shift is chosen after one or two tests. -/
theorem second_to_resetS (k : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.second k 8] (.less "A" "KFirst"))
    (hdec : v.pos "A" < v.pos "KFirst" ∨ v.pos "Reach" < v.pos "A") (n : ℕ) (rr : Option HVM)
    (h : iterS W ρ n { v with
      ctl := .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut") } = rr) :
    ∃ m, m ≤ 2 ∧ iterS W ρ (n + m) v = rr := by
  by_cases h1 : v.pos "A" < v.pos "KFirst"
  · exact ⟨1, by omega, runS_less hv (d := true) (by simp; omega) (sr8t k) h⟩
  · have h2 : v.pos "Reach" < v.pos "A" := hdec.resolve_left h1
    refine ⟨2, le_refl _, ?_⟩
    show iterS W ρ (n + 1 + 1) v = rr
    refine runS_less hv (d := false) (by simp; omega) (sr8f k) ?_
    exact runS_less rfl (d := true) (by simp; omega) (sr9t k) h

set_option maxHeartbeats 1000000 in
/-- **`Second`'s outer loop** (sites 2–11) computes `secondOuter`; amortised with the potential
`3q`, it takes at most `8·work + 3q + 1` steps. -/
theorem second_outerS (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (s p₁ r : ℕ)
    (π0 : String → ℤ) (hsx : s ≤ x.length) (hC : π0 "Cut" = s) (hE : π0 "End" = x.length)
    (hF : π0 "First" = (s : ℤ) + p₁) (hKF : π0 "KFirst" = (s : ℤ) + (k : ℤ) * p₁)
    (hR0 : π0 "Reach" = (s : ℤ) + r) (hp₁ : 0 < p₁) (hρ : DecOrient ρ) :
    ∀ (fuel p q : ℕ) (v : HVM), v.ctl = .pending [.second k 2] (.less "P" "End") →
      v.word = x ++ rest → HRel sHeads k s p q π0 v.pos → 0 < p →
      (p < (x.drop s).length → p + q ≤ (x.drop s).length) →
      (x.drop s).length + 1 ≤ fuel + p →
      ∃ n π', n ≤ 8 * secondOuterWork (x.drop s) k p₁ r fuel p q + 3 * q + 1 ∧
        iterS x.length ρ n v = some { v with
          ctl := .returned (some (secondOuter (x.drop s) k p₁ r fuel p q).isSome)
          pos := π' } ∧
        Keeps sHeads π0 π' ∧
        ∀ p₂, secondOuter (x.drop s) k p₁ r fuel p q = some p₂ → π' "P" = (s : ℤ) + p₂ := by
  have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
  intro fuel
  induction fuel with
  | zero =>
    intro p q v hv hw hR hp hinv hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    refine ⟨1, v.pos, by omega, ?_, hkeep, by simp [secondOuter]⟩
    exact runS_less hv (d := false) (by simp; omega) (sr2f k) (iterS_zero_eq rfl)
  | succ fuel ih =>
    intro p q v hv hw hR hp hinv hf
    obtain ⟨hA, hP, hB, hK, hkeep⟩ := hR
    have hE' : v.pos "End" = x.length := (hkeep "End" (by simp [sHeads])).trans hE
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hg : p < (x.drop s).length
    · have hpq := hinv hg
      obtain ⟨ihs, ihn⟩ := second_innerS k (by omega) x rest s p r π0 hp hsx hE hR0 hρ
        ((x.drop s).length + 1) q { v with ctl := .pending [.second k 3] (.less "B" "End") } rfl
        hw ⟨hA, hP, hB, hK, hkeep⟩ hpq (by omega)
      rcases hsi : secondInner (x.drop s) k p r ((x.drop s).length + 1) q with _ | q'
      · obtain ⟨nin, πin, hnin, hrunin, hkeepin, hPin⟩ := ihn hsi
        have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q = some p := by
          rw [secondOuter, if_pos hg]; simp only [hsi]
        have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
            1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q := by
          rw [secondOuterWork, if_pos hg]; simp only [hsi, Nat.add_zero]
        refine ⟨nin + 1, πin, by rw [hwk]; exact so_bound_found _ _ _ hnin, ?_, hkeepin, ?_⟩
        · rw [hso]
          exact runS_less hv (d := true) (by simp; omega) (sr2t k) hrunin
        · rw [hso]; intro p₂ h; simp only [Option.some.injEq] at h; subst h; exact hPin
      · obtain ⟨nin, πin, hnin, hqin, hrunin, hRin⟩ := ihs q' hsi
        have hq'le := secondInner_le (x.drop s) k p r _ q q' hpq hsi
        obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hRin
        have hC2 : πin "Cut" = s := (hkeep2 "Cut" (by simp [sHeads])).trans hC
        have hF2 : πin "First" = (s : ℤ) + p₁ := (hkeep2 "First" (by simp [sHeads])).trans hF
        have hKF2 : πin "KFirst" = (s : ℤ) + (k : ℤ) * p₁ :=
          (hkeep2 "KFirst" (by simp [sHeads])).trans hKF
        have hR2 : πin "Reach" = (s : ℤ) + r := (hkeep2 "Reach" (by simp [sHeads])).trans hR0
        have hkp1 : ((k * p₁ : ℕ) : ℤ) = (k : ℤ) * p₁ := by push_cast; ring
        by_cases hper : k * p₁ ≤ q' ∧ q' ≤ r
        · have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q =
              secondOuter (x.drop s) k p₁ r fuel (p + p₁) (q' - p₁) := by
            rw [secondOuter, if_pos hg]; simp only [hsi, if_pos hper]
          have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
              1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q +
                secondOuterWork (x.drop s) k p₁ r fuel (p + p₁) (q' - p₁) := by
            rw [secondOuterWork, if_pos hg]; simp only [hsi, if_pos hper]
          have hp₁q : p₁ ≤ q' := le_trans (Nat.le_mul_of_pos_left p₁ (by omega)) hper.1
          have hps := periodShiftF_runS (W := x.length) (ρ := ρ) k
            { v with ctl := .pending [.periodShift k false 1] (.copy "Walk" "Cut"), pos := πin } p₁
            rfl (by show πin "Cut" + p₁ = πin "First"; omega) (by show 0 ≤ πin "Cut"; omega)
            (by show πin "First" ≤ v.len; omega) (by show (p₁ : ℤ) ≤ πin "A"; omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + p₁ ≤ v.len; omega)
            (by show πin "First" ≤ (x.length : ℤ); omega) (by show πin "A" ≤ (x.length : ℤ); omega)
            (by show πin "P" + p₁ ≤ (x.length : ℤ); omega) (hρ.walk.trans hρ.cut.symm)
          have hchild := runS_child' (.second k 10)
            { v with
              ctl := .pending [.second k 10, .periodShift k false 1] (.copy "Walk" "Cut")
              pos := πin }
            [.periodShift k false 1] (.copy "Walk" "Cut") rfl (by simp) (2 * p₁ + 2) none
            (psPosF k πin p₁) hps _ (sr10 k)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hPrec⟩ := ih (p + p₁) (q' - p₁)
            { v with ctl := .pending [.second k 2] (.less "P" "End"), pos := psPosF k πin p₁ }
            rfl hw (hrel_period ⟨hA2, hP2, hB2, hK2, hkeep2⟩ hp₁q) (by omega) (by intro _; omega)
            (by omega)
          have h1_ := iterS_trans hchild hrunrec
          have h2_ := runS_less (v := { v with
              ctl := .pending [.second k 9] (.less "Reach" "A")
              pos := πin }) rfl (d := false) (by simp; omega) (sr9f k) h1_
          have h3_ := runS_less (v := { v with
              ctl := .pending [.second k 8] (.less "A" "KFirst")
              pos := πin }) rfl (d := false) (by simp; omega) (sr8f k) h2_
          have h4_ := iterS_trans hrunin h3_
          refine ⟨nin + (2 * p₁ + 2 + nrec + 1 + 1) + 1, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; exact so_bound_period _ _ _ _ _ _ _ hnin hqin hnrec hp₁q
          · rw [hso]; exact runS_less hv (d := true) (by simp; omega) (sr2t k) h4_
          · rw [hso]; exact hPrec
        · have ht := rsShifts_eq k q' (by omega)
          have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q =
              secondOuter (x.drop s) k p₁ r fuel (p + shiftNoPeriod q' k) 0 := by
            rw [secondOuter, if_pos hg]; simp only [hsi, if_neg hper]
          have hwk : secondOuterWork (x.drop s) k p₁ r (fuel + 1) p q =
              1 + secondInnerWork (x.drop s) k p r ((x.drop s).length + 1) q +
                secondOuterWork (x.drop s) k p₁ r fuel (p + shiftNoPeriod q' k) 0 := by
            rw [secondOuterWork, if_pos hg]; simp only [hsi, if_neg hper]
          have hsp1 := shiftNoPeriod_pos q' k
          have hsmax := shiftNoPeriod_le_max q' k (by omega)
          have hdiv : p + q' / k + 1 ≤ (x.drop s).length := by
            rcases Nat.eq_zero_or_pos q' with h0 | h0
            · subst h0; simp; omega
            · have := div_succ_le q' k hk h0; omega
          obtain ⟨nrs, hnrs, hrs⟩ := resetShiftF_runS (W := x.length) (ρ := ρ) k (by omega)
            { v with
              ctl := .pending [.resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin } q' rfl
            (by show πin "A" = πin "Cut" + q'; omega) (by show 0 ≤ πin "Cut"; omega)
            (by show πin "A" ≤ v.len; omega) (by show 0 ≤ πin "P"; omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ v.len; omega)
            (by show πin "A" ≤ (x.length : ℤ); omega)
            (by show πin "P" + (q' / k : ℕ) + 1 ≤ (x.length : ℤ); omega) (hρ.b.trans hρ.p.symm)
          rw [ht] at hrs
          have hchild := runS_child' (.second k 11)
            { v with
              ctl := .pending [.second k 11, .resetShift k false 0 none 1] (.equal "A" "Cut")
              pos := πin }
            [.resetShift k false 0 none 1] (.equal "A" "Cut") rfl (by simp) nrs none
            (Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
              (πin "P" + (shiftNoPeriod q' k : ℕ))) hrs _ (sr11 k)
          obtain ⟨nrec, πrec, hnrec, hrunrec, hkeeprec, hPrec⟩ := ih (p + shiftNoPeriod q' k) 0
            { v with
              ctl := .pending [.second k 2] (.less "P" "End")
              pos := Function.update (rsPosF k πin q' (shiftNoPeriod q' k)) "B"
                (πin "P" + (shiftNoPeriod q' k : ℕ)) }
            rfl hw
            (hrel_reset (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads])
              (by simp [sHeads]) ⟨hA2, hP2, hB2, hK2, hkeep2⟩ _)
            (by omega) (by intro _; omega) (by omega)
          have h1_ := iterS_trans hchild hrunrec
          obtain ⟨m, hm, h3_⟩ := second_to_resetS k
            { v with ctl := .pending [.second k 8] (.less "A" "KFirst"), pos := πin } rfl
            (by
              show πin "A" < πin "KFirst" ∨ πin "Reach" < πin "A"
              rcases not_and_or.mp hper with h | h
              · left; omega
              · right; omega) _ _ h1_
          have h4_ := iterS_trans hrunin h3_
          refine ⟨nin + (nrs + nrec + m) + 1, πrec, ?_, ?_, hkeeprec, ?_⟩
          · rw [hwk]; exact so_bound_reset _ _ _ _ _ _ _ _ hnin hqin hnrs hnrec hm
          · rw [hso]; exact runS_less hv (d := true) (by simp; omega) (sr2t k) h4_
          · rw [hso]; exact hPrec
    · have hso : secondOuter (x.drop s) k p₁ r (fuel + 1) p q = none := by
        rw [secondOuter, if_neg hg]
      refine ⟨1, v.pos, by omega, ?_, hkeep, by rw [hso]; simp⟩
      rw [hso]
      exact runS_less hv (d := false) (by simp; omega) (sr2f k) (iterS_zero_eq rfl)

/-- **`Second k`, from its fresh frame** (with `First = s + p₁`, `KFirst = s + k·p₁`,
`Reach = s + r`): it returns whether `secondOuter` finds a second period `p₂`, within
`8·secondOuterWork + 7` steps, and then `P = s + p₂`. -/
theorem second_runS (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (s p₁ r fuel : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.second k 1, .initialize k 1] (.copy "A" "Cut"))
    (hw : v.word = x ++ rest) (hC : v.pos "Cut" = s) (hE : v.pos "End" = x.length)
    (hF : v.pos "First" = (s : ℤ) + p₁) (hKF : v.pos "KFirst" = (s : ℤ) + (k : ℤ) * p₁)
    (hR0 : v.pos "Reach" = (s : ℤ) + r) (hsx : s ≤ x.length) (hs1 : s + 1 ≤ x.length)
    (hp₁ : 0 < p₁) (hf : (x.drop s).length ≤ fuel) (hρ : DecOrient ρ) :
    ∃ n π', n ≤ 8 * secondOuterWork (x.drop s) k p₁ r fuel 1 0 + 7 ∧
      iterS x.length ρ n v = some { v with
        ctl := .returned (some (secondOuter (x.drop s) k p₁ r fuel 1 0).isSome)
        pos := π' } ∧
      Keeps sHeads v.pos π' ∧
      ∀ p₂, secondOuter (x.drop s) k p₁ r fuel 1 0 = some p₂ → π' "P" = (s : ℤ) + p₂ := by
  have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
  have hinit := init_runS (W := x.length) (ρ := ρ) k
    { v with ctl := .pending [.initialize k 1] (.copy "A" "Cut") } rfl
    (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)
    (show v.pos "Cut" + 1 ≤ (x.length : ℤ) by omega) (hρ.a.trans hρ.cut.symm)
    (hρ.p.trans hρ.cut.symm) (hρ.b.trans hρ.p.symm) (hρ.kp.trans hρ.cut.symm)
  have hchild := runS_child' (.second k 1) v [.initialize k 1] (.copy "A" "Cut") hv (by simp) 6
    none (initPos k v.pos) hinit _ (sr_init k)
  obtain ⟨n, π', hn, hrun, hkeep, hP⟩ := second_outerS k hk x rest s p₁ r v.pos hsx hC hE hF hKF
    hR0 hp₁ hρ fuel 1 0 { v with ctl := .pending [.second k 2] (.less "P" "End"), pos := initPos k v.pos }
    rfl hw (hrel_init (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads]) (by simp [sHeads])
      k s v.pos hC) (by omega) (by intro _; omega) (by omega)
  exact ⟨6 + n, π', by omega, iterS_trans hchild hrun, hkeep, hP⟩

end Second

/-! ## `Decompose k`, guarded -/

section Dec
variable {W : ℕ} {ρ : String → Bool}

/-- **The `reach` extension** (sites 5–7) computes `extendReach`, in `3·work` steps. -/
theorem extend_runS (k : ℕ) (x rest : List (Fin 2)) (s p₁ : ℕ) (hsx : s ≤ x.length)
    (hρ : DecOrient ρ) :
    ∀ (fuel r : ℕ) (v : HVM), v.ctl = .pending [.decompose k 5] (.less "B" "End") →
      v.word = x ++ rest → v.pos "End" = x.length → v.pos "A" = (s : ℤ) + (r - p₁ : ℕ) →
      v.pos "B" = (s : ℤ) + r → p₁ ≤ r → r ≤ (x.drop s).length →
      (x.drop s).length < fuel + r →
      ∃ n π', n ≤ 3 * extendReachWork (x.drop s) p₁ fuel r ∧
        iterS x.length ρ n v = some { v with
          ctl := .pending [.decompose k 8] (.copy "Reach" "B")
          pos := π' } ∧
        π' "B" = (s : ℤ) + extendReach (x.drop s) p₁ fuel r ∧ Keeps ["A", "B"] v.pos π' := by
  have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
  intro fuel
  induction fuel with
  | zero => intro r v _ _ _ _ _ _ hr hf; omega
  | succ fuel ih =>
    intro r v hv hw hE hA hB hpr hr hf
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    by_cases hc : r < (x.drop s).length ∧ (x.drop s)[r - p₁]? = (x.drop s)[r]?
    · obtain ⟨h1, h3⟩ := hc
      obtain ⟨n, π', hn, hrun, hB', hkeep'⟩ := ih (r + 1)
        { v with
          ctl := .pending [.decompose k 5] (.less "B" "End")
          pos := Function.update (Function.update v.pos "A" (v.pos "A" + 1)) "B" (v.pos "B" + 1) }
        rfl hw (by simp [hE]) (by simp [hA]; omega) (by simp [hB]; ring) (by omega) (by omega)
        (by omega)
      refine ⟨n + 1 + 1 + 1, π', ?_, ?_, ?_, ?_⟩
      · rw [extendReachWork, if_pos ⟨h1, h3⟩]; omega
      · refine runS_less hv (d := true) (by simp; omega) (dc5t k) ?_
        refine runS_symbols rfl (d := true) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
          (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (dc6t k) hρ.a hρ.b
          (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
        · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = true
          rw [hw, sym_decide x rest s (r - p₁) r (by omega) (by omega) _ _ hA hB]
          exact decide_eq_true h3
        refine runS_moveAB rfl (show 0 ≤ v.pos "A" + 1 ∧ v.pos "A" + 1 ≤ v.len by omega)
          (show 0 ≤ v.pos "B" + 1 ∧ v.pos "B" + 1 ≤ v.len by omega) (dc7 k)
          (show v.pos "A" + 1 ≤ (x.length : ℤ) by omega)
          (show v.pos "B" + 1 ≤ (x.length : ℤ) by omega) ?_
        exact hrun
      · rw [extendReach, if_pos ⟨h1, h3⟩]; exact hB'
      · exact keeps_trans (keeps_update (by simp) _ (keeps_update (by simp) _ (keeps_refl _ _)))
          hkeep'
    · refine ⟨if r < (x.drop s).length then 2 else 1, v.pos, ?_, ?_, ?_, keeps_refl _ _⟩
      · rw [extendReachWork, if_neg hc]; split_ifs <;> omega
      · by_cases h1 : r < (x.drop s).length
        · have h3 : ¬ (x.drop s)[r - p₁]? = (x.drop s)[r]? := fun h' => hc ⟨h1, h'⟩
          rw [if_pos h1]
          show iterS x.length ρ (0 + 1 + 1) v = _
          refine runS_less hv (d := true) (by simp; omega) (dc5t k) ?_
          refine runS_symbols rfl (d := false) (show 0 ≤ v.pos "A" ∧ v.pos "A" < v.len by omega)
            (show 0 ≤ v.pos "B" ∧ v.pos "B" < v.len by omega) ?_ (dc6f k) hρ.a hρ.b
            (show v.pos "A" < (x.length : ℤ) by omega) (show v.pos "B" < (x.length : ℤ) by omega) ?_
          · show decide (v.word[(v.pos "A").toNat]? = v.word[(v.pos "B").toNat]?) = false
            rw [hw, sym_decide x rest s (r - p₁) r (by omega) (by omega) _ _ hA hB]
            exact decide_eq_false h3
          exact iterS_zero_eq rfl
        · rw [if_neg h1]
          exact runS_less hv (d := false) (by simp; omega) (dc5f k) (iterS_zero_eq rfl)
      · rw [extendReach, if_neg hc]; exact hB

/-- The cut move names one non-blind head, `Cut`. -/
theorem evOk_cutMove (π : String → ℤ) (len : ℤ) (hC : π "Cut" + 1 ≤ W) :
    EvOk W ρ π len (.move [⟨"Cut", 1⟩, ⟨"Second", 1⟩]) := by
  refine evOk_move ?_ (by decide)
  intro m hm hb _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · simpa [sumDelta] using hC
  · exact absurd (by decide) hb

/-- **The cut advance** (sites 12–13): `Cut` and `Second` move `j` cells in lockstep. -/
theorem cut_runS (k : ℕ) :
    ∀ (j : ℕ) (v : HVM), v.ctl = .pending [.decompose k 12] (.less "Cut" "P") →
      v.pos "P" = v.pos "Cut" + j → v.pos "P" ≤ v.len → 0 ≤ v.pos "Cut" → v.pos "P" ≤ W →
      ∃ π', iterS W ρ (2 * j + 1) v = some { v with
          ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
          pos := π' } ∧
        π' "Cut" = v.pos "Cut" + j ∧ π' "Second" = v.pos "Second" + j ∧
        Keeps ["Cut", "Second"] v.pos π'
  | 0, v, hv, hP, _, _, _ => by
    refine ⟨v.pos, ?_, by simp, by simp, keeps_refl _ _⟩
    exact runS_less hv (d := false) (by simp; omega) (dc12f k) (iterS_zero_eq rfl)
  | j + 1, v, hv, hP, hPL, hC0, hPW => by
    obtain ⟨π', hrun, hC', hS', hkeep'⟩ := cut_runS k j
      { v with
        ctl := .pending [.decompose k 12] (.less "Cut" "P")
        pos := Function.update (Function.update v.pos "Cut" (v.pos "Cut" + 1)) "Second"
          (v.pos "Second" + 1) }
      rfl (by simp; omega) (by simp only [HVM.len] at hPL ⊢; simp; omega) (by simp; omega)
      (by simp; omega)
    refine ⟨π', ?_, ?_, ?_, ?_⟩
    · show iterS W ρ (2 * j + 1 + 1 + 1) v = _
      refine runS_less hv (d := true) (by simp; omega) (dc12t k) ?_
      refine runS_move (ms := [⟨"Cut", 1⟩, ⟨"Second", 1⟩]) rfl
        (moveSeq_CS _ _ (show 0 ≤ v.pos "Cut" + 1 ∧ v.pos "Cut" + 1 ≤ v.len by omega)) (dc13 k)
        (evOk_cutMove _ _ (show v.pos "Cut" + 1 ≤ (W : ℤ) by omega)) ?_
      exact hrun
    · rw [hC']; simp; ring
    · rw [hS']; simp; ring
    · exact keeps_trans (keeps_update (by simp) _ (keeps_update (by simp) _ (keeps_refl _ _)))
        hkeep'

/-- **The strip loop** (sites 10–13): `First k true` is re-run from each new cut until it fails;
this computes `stripLoop`. -/
theorem strip_runS (k : ℕ) (hk : 2 ≤ k) (x rest : List (Fin 2)) (p₂ : ℕ) (hρ : DecOrient ρ) :
    ∀ (fuel s : ℕ) (v : HVM),
      v.ctl = .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut") →
      v.word = x ++ rest → v.pos "Cut" = s → v.pos "End" = x.length →
      v.pos "Second" = (s : ℤ) + p₂ → s ≤ x.length → s + 1 ≤ x.length →
      x.length < fuel + s →
      ∃ n π', n ≤ 10 * stripLoopWork x k p₂ fuel s + 11 * (stripLoop x k p₂ fuel s - s) + 8 ∧
        iterS x.length ρ n v = some { v with
          ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
          pos := π' } ∧
        π' "Cut" = stripLoop x k p₂ fuel s ∧ Keeps dHeads v.pos π' := by
  intro fuel
  induction fuel with
  | zero => intro s v _ _ _ _ _ hs _ hf; omega
  | succ fuel ih =>
    intro s v hv hw hC hE hS hs hs1 hf
    have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    obtain ⟨nf, πf, hnf, hrunf, hkeepf, hrelf⟩ := first_runS k hk true x rest s p₂ (x.length + 1)
      { v with ctl := .pending [.first k true 1, .initialize k 1] (.copy "A" "Cut") } rfl hw hC hE
      hs hs1 (fun _ => hS) (fun h => by cases h) (by omega) hρ
    have hCf : πf "Cut" = s := (hkeepf "Cut" (by simp [fHeads])).trans hC
    rcases hfo : firstOuter (x.drop s) k p₂ (x.length + 1) 1 with _ | ⟨p, m⟩
    · rw [hfo] at hrunf
      have hchild := runS_child' (.decompose k 11) v [.first k true 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some false) πf hrunf _ (dc11f k)
      have hsw : stripLoopWork x k p₂ (fuel + 1) s =
          firstOuterWork (x.drop s) k p₂ (x.length + 1) 1 := by
        rw [stripLoopWork, hfo]; rfl
      have hsl : stripLoop x k p₂ (fuel + 1) s = s := by rw [stripLoop, hfo]
      refine ⟨nf, πf, ?_, hchild, ?_, keeps_mono (by simp [fHeads, dHeads]) hkeepf⟩
      · rw [hsw, hsl, Nat.sub_self, Nat.mul_zero, Nat.add_zero]; exact hnf
      · rw [hsl]; exact hCf
    · rw [hfo] at hrunf
      have hchild := runS_child' (.decompose k 11) v [.first k true 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some true) πf hrunf _ (dc11t k)
      obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hrelf p m hfo
      have hplt := firstOuter_lt (x.drop s) k p₂ (x.length + 1) 1 p m (by omega) hfo
      have hsw : stripLoopWork x k p₂ (fuel + 1) s =
          firstOuterWork (x.drop s) k p₂ (x.length + 1) 1 + stripLoopWork x k p₂ fuel (s + p) := by
        rw [stripLoopWork, hfo]
      have hsl : stripLoop x k p₂ (fuel + 1) s = stripLoop x k p₂ fuel (s + p) := by
        rw [stripLoop, hfo]
      have hEf : πf "End" = x.length := (hkeepf "End" (by simp [fHeads])).trans hE
      have hSf : πf "Second" = (s : ℤ) + p₂ := (hkeepf "Second" (by simp [fHeads])).trans hS
      obtain ⟨πc, hrunc, hCc, hSc, hkeepc⟩ := cut_runS (W := x.length) (ρ := ρ) k p
        { v with ctl := .pending [.decompose k 12] (.less "Cut" "P"), pos := πf } rfl
        (by show πf "P" = πf "Cut" + p; omega) (by show πf "P" ≤ v.len; omega)
        (by show 0 ≤ πf "Cut"; omega) (by show πf "P" ≤ (x.length : ℤ); omega)
      have hEc : πc "End" = x.length := (hkeepc "End" (by simp)).trans hEf
      obtain ⟨nrec, πrec, hnrec, hrunrec, hCrec, hkeeprec⟩ := ih (s + p)
        { v with
          ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
          pos := πc }
        rfl hw (by show πc "Cut" = ((s + p : ℕ) : ℤ); rw [hCc]; push_cast; omega) hEc
        (by show πc "Second" = ((s + p : ℕ) : ℤ) + p₂; rw [hSc]; push_cast; omega) (by omega)
        (by omega) (by omega)
      have hge := stripLoop_ge x k p₂ fuel (s + p)
      have hd : stripLoop x k p₂ fuel (s + p) - s = stripLoop x k p₂ fuel (s + p) - (s + p) + p := by
        omega
      refine ⟨nf + (2 * p + 1 + nrec), πrec, ?_, iterS_trans hchild (iterS_trans hrunc hrunrec), ?_, ?_⟩
      · rw [hsw, hsl, hd]; exact strip_bound _ _ _ _ _ _ hnf hnrec hplt.1
      · rw [hsl]; exact hCrec
      · exact keeps_trans (keeps_mono (by simp [fHeads, dHeads]) hkeepf)
          (keeps_trans (keeps_mono (by simp [dHeads]) hkeepc) hkeeprec)

set_option maxHeartbeats 1000000 in
/-- **`Decompose`'s outer loop** (from the call of `First k false`) computes `decomposeLoop`, in
`10·decomposeLoopWork + 38·(|x| − s) + 18` steps. -/
theorem dec_loopS (k : ℕ) (hk : 4 ≤ k) (x rest : List (Fin 2)) (hρ : DecOrient ρ) :
    ∀ (fuel s : ℕ) (v : HVM),
      v.ctl = .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut") →
      v.word = x ++ rest → v.pos "Cut" = s → v.pos "End" = x.length → s ≤ x.length →
      s + 1 ≤ x.length → x.length < fuel + s →
      ∃ n b π', n ≤ 10 * decomposeLoopWork x k fuel s + 38 * (x.length - s) + 18 ∧
        iterS x.length ρ n v = some { v with ctl := .returned (some b), pos := π' } ∧
        Keeps dHeads v.pos π' ∧
        π' "Cut" = (decomposeLoop x k fuel s).1 ∧
        (b = true ↔ (decomposeLoop x k fuel s).2.1 ≠ 0) ∧
        (b = true →
          π' "First" = ((decomposeLoop x k fuel s).1 : ℤ) + (decomposeLoop x k fuel s).2.1 ∧
          π' "KFirst" = ((decomposeLoop x k fuel s).1 : ℤ) +
            (k : ℤ) * (decomposeLoop x k fuel s).2.1 ∧
          π' "Reach" = ((decomposeLoop x k fuel s).1 : ℤ) + (decomposeLoop x k fuel s).2.2) := by
  intro fuel
  induction fuel with
  | zero => intro s v _ _ _ _ hs _ hf; omega
  | succ fuel ih =>
    intro s v hv hw hC hE hs hs1 hf
    have hlen : (x.drop s).length + s = x.length := by rw [List.length_drop]; omega
    have hL : (x.length : ℤ) ≤ v.len := by simp [HVM.len, hw]
    obtain ⟨nf, πf, hnf, hrunf, hkeepf, hrelf⟩ := first_runS k (by omega) false x rest s
      (x.drop s).length ((x.drop s).length + 1)
      { v with ctl := .pending [.first k false 1, .initialize k 1] (.copy "A" "Cut") } rfl hw hC hE
      hs hs1 (fun h => by cases h) (fun _ => le_refl _) (by omega) hρ
    have hCf : πf "Cut" = s := (hkeepf "Cut" (by simp [fHeads])).trans hC
    have hEf : πf "End" = x.length := (hkeepf "End" (by simp [fHeads])).trans hE
    rcases hfp : firstPeriod (x.drop s) k with _ | ⟨p₁, m⟩
    · have hfp' : firstOuter (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 = none := hfp
      rw [hfp'] at hrunf
      have hchild := runS_child' (.decompose k 2) v [.first k false 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some false) πf hrunf _ (dc2f k)
      have hdl : decomposeLoop x k (fuel + 1) s = (s, 0, 0) := by rw [decomposeLoop, hfp]
      have hdw : decomposeLoopWork x k (fuel + 1) s =
          firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 := by
        rw [decomposeLoopWork, decomposeStepWork, hfp]; rfl
      refine ⟨nf, false, πf, ?_, hchild, keeps_mono (by simp [fHeads, dHeads]) hkeepf, ?_, ?_,
        fun h => by cases h⟩
      · rw [hdw]; exact dec_bound_stop _ _ _ hnf
      · rw [hdl]; exact hCf
      · rw [hdl]; simp
    · have hfp' : firstOuter (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 =
          some (p₁, m) := hfp
      obtain ⟨hleast, hm⟩ := firstPeriod_some (x.drop s) k (by omega) hfp
      have hp₁ : 0 < p₁ := hleast.1.1
      have hkp₁len : k * p₁ ≤ (x.drop s).length := hleast.1.2.1
      have hkp := nat_kp k p₁ (by omega)
      obtain ⟨hA2, hP2, hB2, hK2, hkeep2⟩ := hrelf p₁ m hfp'
      rw [hfp'] at hrunf
      have hchild1 := runS_child' (.decompose k 2) v [.first k false 1, .initialize k 1]
        (.copy "A" "Cut") hv (by simp) nf (some true) πf hrunf _ (dc2t k)
      -- the reach extension, from `A = s + (k−1)p₁`, `B = s + k·p₁`
      obtain ⟨ner, πe, hner, hrune, hBe, hkeepe⟩ := extend_runS k x rest s p₁ hs hρ (x.length + 1) m
        { v with
          ctl := .pending [.decompose k 5] (.less "B" "End")
          pos := Function.update (Function.update πf "First" (πf "P")) "KFirst"
            (Function.update πf "First" (πf "P") "B") }
        rfl hw (by simp [hEf]) (by simp [hA2]; rw [hm]; omega)
        (by simp [hB2]; rw [hm]; push_cast; omega) (by rw [hm]; omega) (by rw [hm]; omega)
        (by omega)
      have hrle := (extendReach_spec (x.drop s) p₁ (x.length + 1) m (by omega) (by rw [hm]; omega)
        (by rw [hm]; exact hkp₁len) (by rw [hm]; exact hleast.1.2.2)).1
      -- facts on the heads before `Second`
      have hFe : πe "First" = (s : ℤ) + p₁ := by
        rw [hkeepe "First" (by simp)]; simp [hP2]
      have hKFe : πe "KFirst" = (s : ℤ) + (k : ℤ) * p₁ := by
        have hkpZ : ((k - 1 : ℕ) : ℤ) * p₁ + p₁ = (k : ℤ) * p₁ := by exact_mod_cast hkp
        rw [hkeepe "KFirst" (by simp)]; simp [hB2]; linarith
      have hCe : πe "Cut" = s := by rw [hkeepe "Cut" (by simp)]; simp [hCf]
      have hEe : πe "End" = x.length := by rw [hkeepe "End" (by simp)]; simp [hEf]
      obtain ⟨ns, πs, hns, hruns, hkeeps, hPs⟩ := second_runS k (by omega) x rest s p₁
        (extendReach (x.drop s) p₁ (x.length + 1) m) ((x.drop s).length + 1)
        { v with
          ctl := .pending [.second k 1, .initialize k 1] (.copy "A" "Cut")
          pos := Function.update πe "Reach" (πe "B") }
        rfl hw (by simp [hCe]) (by simp [hEe]) (by simp [hFe]) (by simp [hKFe]) (by simp [hBe])
        hs hs1 hp₁ (by omega) hρ
      have hFs : πs "First" = (s : ℤ) + p₁ := by
        rw [hkeeps "First" (by simp [sHeads])]; simp [hFe]
      have hKFs : πs "KFirst" = (s : ℤ) + (k : ℤ) * p₁ := by
        rw [hkeeps "KFirst" (by simp [sHeads])]; simp [hKFe]
      have hRs : πs "Reach" = (s : ℤ) + extendReach (x.drop s) p₁ (x.length + 1) m := by
        rw [hkeeps "Reach" (by simp [sHeads])]; simp [hBe]
      have hCs : πs "Cut" = s := by rw [hkeeps "Cut" (by simp [sHeads])]; simp [hCe]
      have hEs : πs "End" = x.length := by rw [hkeeps "End" (by simp [sHeads])]; simp [hEe]
      have hkeep_s : Keeps dHeads v.pos πs :=
        keeps_trans (keeps_mono (by simp [fHeads, dHeads]) hkeepf)
          (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
            (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
              (keeps_trans (keeps_mono (by simp [dHeads]) hkeepe)
                (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
                  (keeps_mono (by simp [sHeads, dHeads]) hkeeps)))))
      rcases hsp : secondPeriod (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
        with _ | p₂
      · have hsp' : secondOuter (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
            ((x.drop s).length + 1) 1 0 = none := hsp
        rw [hsp'] at hruns
        have hchild2 := runS_child' (.decompose k 9)
          { v with
            ctl := .pending [.decompose k 9, .second k 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πe "Reach" (πe "B") }
          [.second k 1, .initialize k 1] (.copy "A" "Cut") rfl (by simp) ns (some false) πs hruns _
          (dc9f k)
        have hS2 := runS_copy (v := { v with
            ctl := .pending [.decompose k 8] (.copy "Reach" "B")
            pos := πe }) rfl (dc8 k) (hρ.reach.trans hρ.b.symm) hchild2
        have hE2 := iterS_trans hrune hS2
        have hC2 := runS_copy (v := { v with
            ctl := .pending [.decompose k 3] (.copy "First" "P")
            pos := πf }) rfl (dc3 k) (hρ.first.trans hρ.p.symm)
            (runS_copy rfl (dc4 k) (hρ.kfirst.trans hρ.b.symm) hE2)
        have hall := iterS_trans hchild1 hC2
        have hdl : decomposeLoop x k (fuel + 1) s =
            (s, p₁, extendReach (x.drop s) p₁ (x.length + 1) m) := by
          rw [decomposeLoop, hfp]; simp only [hsp]
        have hdw : decomposeLoopWork x k (fuel + 1) s =
            firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
              (extendReachWork (x.drop s) p₁ (x.length + 1) m +
                secondOuterWork (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
                  ((x.drop s).length + 1) 1 0) := by
          rw [decomposeLoopWork, decomposeStepWork, hfp]; simp only [hsp, Nat.add_zero]
        refine ⟨nf + (ner + (ns + 1) + 1 + 1), true, πs, ?_, hall, hkeep_s, ?_, ?_, ?_⟩
        · rw [hdw]; exact dec_bound_found _ _ _ _ _ _ _ hnf hner hns
        · rw [hdl]; exact hCs
        · rw [hdl]; simp; omega
        · intro _; rw [hdl]; exact ⟨hFs, hKFs, hRs⟩
      · have hsp' : secondOuter (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
            ((x.drop s).length + 1) 1 0 = some p₂ := hsp
        have hP₂ := hPs p₂ hsp'
        rw [hsp'] at hruns
        have hchild2 := runS_child' (.decompose k 9)
          { v with
            ctl := .pending [.decompose k 9, .second k 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πe "Reach" (πe "B") }
          [.second k 1, .initialize k 1] (.copy "A" "Cut") rfl (by simp) ns (some true) πs hruns _
          (dc9t k)
        have hprog := strip_progress x k s hk hs hfp hsp
        have hs'le := stripLoop_le x k p₂ (x.length + 1) s hs
        have hs'lt := stripLoop_lt x k p₂ (x.length + 1) s hprog
        obtain ⟨nst, πst, hnst, hrunst, hCst, hkeepst⟩ := strip_runS k (by omega) x rest p₂ hρ
          (x.length + 1) s
          { v with
            ctl := .pending [.decompose k 11, .first k true 1, .initialize k 1] (.copy "A" "Cut")
            pos := Function.update πs "Second" (πs "P") }
          rfl hw (by simp [hCs]) (by simp [hEs]) (by simp [hP₂]) hs hs1 (by omega)
        have hEst : πst "End" = x.length := by
          rw [hkeepst "End" (by simp [dHeads])]; simp [hEs]
        obtain ⟨nrec, b, πrec, hnrec, hrunrec, hkeeprec, hCrec, hiff, hheads⟩ :=
          ih (stripLoop x k p₂ (x.length + 1) s)
            { v with
              ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
              pos := πst }
            rfl hw hCst hEst hs'le (by omega) (by omega)
        have hA_ := iterS_trans hrunst hrunrec
        have hB_ := runS_copy (v := { v with
            ctl := .pending [.decompose k 10] (.copy "Second" "P")
            pos := πs }) rfl (dc10 k) (hρ.second.trans hρ.p.symm) hA_
        have hC_ := iterS_trans hchild2 hB_
        have hS2 := runS_copy (v := { v with
            ctl := .pending [.decompose k 8] (.copy "Reach" "B")
            pos := πe }) rfl (dc8 k) (hρ.reach.trans hρ.b.symm) hC_
        have hE2 := iterS_trans hrune hS2
        have hC2 := runS_copy (v := { v with
            ctl := .pending [.decompose k 3] (.copy "First" "P")
            pos := πf }) rfl (dc3 k) (hρ.first.trans hρ.p.symm)
            (runS_copy rfl (dc4 k) (hρ.kfirst.trans hρ.b.symm) hE2)
        have hall := iterS_trans hchild1 hC2
        have hdl : decomposeLoop x k (fuel + 1) s =
            decomposeLoop x k fuel (stripLoop x k p₂ (x.length + 1) s) := by
          rw [decomposeLoop, hfp]; simp only [hsp]
        have hdw : decomposeLoopWork x k (fuel + 1) s =
            firstOuterWork (x.drop s) k (x.drop s).length ((x.drop s).length + 1) 1 +
              (extendReachWork (x.drop s) p₁ (x.length + 1) m +
                secondOuterWork (x.drop s) k p₁ (extendReach (x.drop s) p₁ (x.length + 1) m)
                  ((x.drop s).length + 1) 1 0) +
              (stripLoopWork x k p₂ (x.length + 1) s +
                decomposeLoopWork x k fuel (stripLoop x k p₂ (x.length + 1) s)) := by
          rw [decomposeLoopWork, decomposeStepWork, hfp]; simp only [hsp]
        have hd : x.length - s = (stripLoop x k p₂ (x.length + 1) s - s) +
            (x.length - stripLoop x k p₂ (x.length + 1) s) := by omega
        refine ⟨nf + (ner + (ns + (nst + nrec + 1) + 1) + 1 + 1), b, πrec, ?_, hall, ?_, ?_, ?_, ?_⟩
        · rw [hdw, hd]; exact dec_bound_more _ _ _ _ _ _ _ _ _ _ _ _ hnf hner hns hnst hnrec
            (by omega)
        · exact keeps_trans hkeep_s (keeps_trans (keeps_upd1 (by simp [dHeads]) _ _)
            (keeps_trans hkeepst hkeeprec))
        · rw [hdl]; exact hCrec
        · rw [hdl]; exact hiff
        · rw [hdl]; exact hheads

/-- **`Decompose k` under the worker's side conditions** (`W = |x|`): `decompose_run` as a
guarded run. From its fresh frame, on the word `x ++ rest` with `Origin = 0`, `End = |x|`,
`0 < |x|` and the orientation `DecOrient ρ`, every step keeps the side conditions and it returns
a value `b` within `(160k+418)·|x| + (20k+69)` steps, with `Cut = s`, `b` exactly when a period
exists, and then `First = s + p₁`, `KFirst = s + k·p₁`, `Reach = s + r`, where
`(s, p₁, r) = GSPreprocess.decompose x k`. Only the heads of `dHeads` move. -/
theorem decompose_runS (k : ℕ) (hk : 4 ≤ k) (x rest : List (Fin 2)) (v : HVM)
    (hv : v.ctl = Ctl.ofOutcome (next [.decompose k 0] none))
    (hw : v.word = x ++ rest) (hO : v.pos "Origin" = 0) (hE : v.pos "End" = x.length)
    (hx : 0 < x.length) (hρ : DecOrient ρ) :
    ∃ n b π', n ≤ (160 * k + 418) * x.length + (20 * k + 69) ∧
      iterS x.length ρ n v = some { v with ctl := .returned (some b), pos := π' } ∧
      Keeps dHeads v.pos π' ∧ π' "Origin" = 0 ∧ π' "End" = x.length ∧
      π' "Cut" = (decompose x k).1 ∧
      (b = true ↔ (decompose x k).2.1 ≠ 0) ∧
      (b = true →
        π' "First" = ((decompose x k).1 : ℤ) + (decompose x k).2.1 ∧
        π' "KFirst" = ((decompose x k).1 : ℤ) + (k : ℤ) * (decompose x k).2.1 ∧
        π' "Reach" = ((decompose x k).1 : ℤ) + (decompose x k).2.2) := by
  rw [dc0] at hv
  obtain ⟨n, b, π', hn, hrun, hkeep, hC, hiff, hheads⟩ := dec_loopS k hk x rest hρ (x.length + 1) 0
    { v with
      ctl := .pending [.decompose k 2, .first k false 1, .initialize k 1] (.copy "A" "Cut")
      pos := Function.update v.pos "Cut" (v.pos "Origin") }
    rfl hw (by simp [hO]) (by simp [hE]) (Nat.zero_le _)
    (by omega) (by omega)
  have hkeep' : Keeps dHeads v.pos π' :=
    keeps_trans (keeps_upd1 (by simp [dHeads]) _ _) hkeep
  have hwork := decomposeWork_le x k hk
  have e0 : decomposeWork x k = decomposeLoopWork x k (x.length + 1) 0 := rfl
  have e1 : (160 * k + 418) * x.length = 10 * ((16 * k + 38) * x.length) + 38 * x.length := by
    ring
  refine ⟨n + 1, b, π', ?_, runS_copy hv (dc1 k) (hρ.cut.trans hρ.origin.symm) hrun, hkeep', ?_, ?_, hC, hiff, hheads⟩
  · rw [e0] at hwork
    omega
  · rw [hkeep' "Origin" (by simp [dHeads]), hO]
  · rw [hkeep' "End" (by simp [dHeads]), hE]

end Dec

end PalPeg.ScaDecomposeSafe
