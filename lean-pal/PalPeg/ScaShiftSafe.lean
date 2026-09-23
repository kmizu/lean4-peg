import PalPeg.ScaHeadSafe

/-!
# The shift generators under the worker's side conditions

`ScaHeadGen.periodShift_run` / `resetShift_run` as guarded runs (`ScaHeadSafe.iterS`): the same
steps, each keeping the side conditions. The reversed heads the shifts move (`Walk` in
`PeriodShift`, `A` in both) stay inside the pattern; the forward heads (`B`, `P`, `KP`) carry no
condition.
-/
set_option autoImplicit false
namespace PalPeg.ScaShiftSafe
open PalPeg.ScaGsProgram PalPeg.ScaGsCoroutine PalPeg.ScaWorkerCoroutine PalPeg.ScaHeadVM
  PalPeg.ScaHeadRun PalPeg.ScaHeadGen PalPeg.ScaHeadSafe

variable {W : ℕ} {ρ : String → Bool}

/-! ## `PeriodShift k true` -/

theorem ps_firstS (k : ℕ) (v : HVM) (hv : v.ctl = .pending [.periodShift k true 1] (.copy "Walk" "Cut"))
    (hρ : ρ "Walk" = ρ "Cut") :
    iterS W ρ 1 v = some { v with ctl := psLoop k, pos := psPos v.pos 0 } :=
  iterS_one hv ⟨hρ, by decide, by decide⟩ (stepMatch_of_one (ps_first k v hv))

theorem ps_exitS (k : ℕ) (v : HVM) (hv : v.ctl = psLoop k) (hge : v.pos "First" ≤ v.pos "Walk") :
    iterS W ρ 1 v = some { v with ctl := .returned none } :=
  iterS_one (c := [.periodShift k true 2]) (e := .less "Walk" "First") hv ⟨by decide, by decide⟩
    (stepMatch_of_one (ps_exit k v hv hge))

theorem ps_iterS (k : ℕ) (v : HVM) (π : String → ℤ) (i : ℤ) (hv : v.ctl = psLoop k)
    (hp : v.pos = psPos π i) (hlt : π "Cut" + i < π "First")
    (hW : 0 ≤ π "Cut" + i + 1 ∧ π "Cut" + i + 1 ≤ v.len)
    (hA : 0 ≤ π "A" - i - 1 ∧ π "A" - i - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + i + 1 ∧ π "P" + i + 1 ≤ v.len)
    (hi : 0 ≤ i) (hFW : π "First" ≤ W) (hAW : π "A" ≤ W) (hρP : ρ "P" = false)
    (hρK : ρ "KP" = false) :
    iterS W ρ 2 v = some { v with ctl := psLoop k, pos := psPos π (i + 1) } := by
  have hW' : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPos]
  have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPos]
  have hd : decide (v.pos "Walk" < v.pos "First") = true := by simp; omega
  have e1 : stepMatch v = some { v with ctl := .pending [.periodShift k true 3] psMove } := by
    simp only [stepMatch, hv, psLoop, hd]; rfl
  have e2 : stepMatch { v with ctl := .pending [.periodShift k true 3] psMove } =
      some { v with ctl := psLoop k, pos := psPos π (i + 1) } := by
    have := ps_iter k v π i hv hp hlt hW hA hP
    simpa [iterStep, e1] using this
  refine iterS_step (c := [.periodShift k true 2]) (e := .less "Walk" "First") hv
    ⟨by decide, by decide⟩ e1 (iterS_one rfl ?_ e2)
  show EvOk W ρ v.pos _ (.move [⟨"Walk", 1⟩, ⟨"A", -1⟩, ⟨"P", 1⟩, ⟨"KP", -1⟩])
  refine evOk_move ?_ (by decide)
  intro m hm _ hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> simp [sumDelta, hp, psPos] at hr ⊢ <;> simp_all <;> omega

theorem ps_loop_runS (k : ℕ) (π : String → ℤ) (L : ℤ) (hFW : π "First" ≤ W) (hAW : π "A" ≤ W)
    (hρP : ρ "P" = false) (hρK : ρ "KP" = false) :
    ∀ (m : ℕ) (v : HVM) (i : ℤ), v.ctl = psLoop k → v.pos = psPos π i → v.len = L →
      π "Cut" + i + m = π "First" → 0 ≤ π "Cut" + i → π "First" ≤ L →
      0 ≤ π "A" - (i + m) → π "A" - i ≤ L → 0 ≤ π "P" + i → π "P" + i + m ≤ L → 0 ≤ i →
      iterS W ρ (2 * m + 1) v = some { v with ctl := .returned none, pos := psPos π (i + m) }
  | 0, v, i, hv, hp, _, he, _, _, _, _, _, _, _ => by
    have hW : v.pos "Walk" = π "Cut" + i := by rw [hp]; simp [psPos]
    have hF : v.pos "First" = π "First" := by rw [hp]; simp [psPos]
    rw [ps_exitS k v hv (by omega)]
    simp [hp]
  | m + 1, v, i, hv, hp, hL, he, h1, h2, h3, h4, h5, h6, hi => by
    have hstep := ps_iterS (W := W) (ρ := ρ) k v π i hv hp (by omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hi hFW hAW hρP hρK
    rw [show 2 * (m + 1) + 1 = 2 + (2 * m + 1) by ring, iterS_add, hstep, Option.bind_some]
    have := ps_loop_runS k π L hFW hAW hρP hρK m
      { v with ctl := psLoop k, pos := psPos π (i + 1) } (i + 1) rfl rfl
      hL (by push_cast at he; omega) (by omega) h2 (by push_cast at h3; omega) (by omega) (by omega)
      (by push_cast at h6; omega) (by omega)
    rw [this]
    congr 2
    push_cast; ring_nf

/-- **`PeriodShift k true` under the side conditions**: `ScaHeadGen.periodShift_run`, guarded. -/
theorem periodShift_runS (k : ℕ) (v : HVM) (t : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.periodShift k true 0] none))
    (ht : v.pos "Cut" + t = v.pos "First") (h0 : 0 ≤ v.pos "Cut") (hF : v.pos "First" ≤ v.len)
    (hA : t ≤ v.pos "A") (hA' : v.pos "A" ≤ v.len) (hP : 0 ≤ v.pos "P")
    (hP' : v.pos "P" + t ≤ v.len)
    (hFW : v.pos "First" ≤ W) (hAW : v.pos "A" ≤ W) (hρ : ρ "Walk" = ρ "Cut")
    (hρP : ρ "P" = false) (hρK : ρ "KP" = false) :
    iterS W ρ (2 * t + 2) v = some { v with ctl := .returned none, pos := psPos v.pos t } := by
  rw [ps_start] at hv
  rw [show 2 * t + 2 = 1 + (2 * t + 1) by ring, iterS_add, ps_firstS k v hv hρ, Option.bind_some]
  have := ps_loop_runS (W := W) (ρ := ρ) k v.pos v.len hFW hAW hρP hρK t
    { v with ctl := psLoop k, pos := psPos v.pos 0 } 0 rfl rfl
    rfl (by omega) (by omega) hF (by omega) (by omega) (by omega) (by omega) le_rfl
  rw [this]
  simp

/-! ## `ResetShift k true` -/

theorem rs_firstS (k : ℕ) (v : HVM)
    (hv : v.ctl = .pending [.resetShift k true 0 none 1] (.equal "A" "Cut")) :
    iterS W ρ 1 v = some { v with ctl := rsLoop k 0 (decide (v.pos "A" ≠ v.pos "Cut")) } :=
  iterS_one hv ⟨by decide, by decide⟩ (stepMatch_of_one (rs_first k v hv))

/-- The rewind move keeps the side conditions. -/
theorem evOk_rsBack (π : String → ℤ) (len : ℤ) (hAW : π "A" - 1 ≤ W) (hρB : ρ "B" = false) :
    EvOk W ρ π len (.move [⟨"A", -1⟩, ⟨"B", -1⟩]) := by
  refine evOk_move ?_ (by decide)
  intro m hm _ hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;> simp [sumDelta] at hr ⊢ <;> simp_all

/-- The shift move names no reversed head. -/
theorem evOk_rsShift (π : String → ℤ) (len : ℤ) (hρP : ρ "P" = false) (hρB : ρ "B" = false)
    (hρK : ρ "KP" = false) :
    EvOk W ρ π len (.move [⟨"P", 1⟩, ⟨"B", 1⟩, ⟨"KP", -1⟩]) := by
  refine evOk_move ?_ (by decide)
  intro m hm _ hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> simp_all

theorem rs_iterS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 < k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s - 1 ∧ π "B" - j + s - 1 ≤ v.len)
    (hAW : π "A" - j ≤ W) (hρB : ρ "B" = false) :
    iterS W ρ 2 v = some { v with ctl := rsLoop k (ph + 1) ne, pos := rsPos π (j + 1) s } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPos, hne]
  have e1 := step_equal hv
  rw [hd, rs_resume_back] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack } =
      some { v with ctl := rsLoop k (ph + 1) ne, pos := rsPos π (j + 1) s } := by
    have := rs_iter k ph ne v π j s hv hp hne hph hA hB
    simpa [iterStep, e1] using this
  refine iterS_step hv ⟨by decide, by decide⟩ e1 (iterS_one rfl ?_ e2)
  show EvOk W ρ v.pos _ (.move [⟨"A", -1⟩, ⟨"B", -1⟩])
  exact evOk_rsBack _ _ (by rw [hp]; simp [rsPos]; omega) hρB

theorem rs_wrapS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (hne : π "A" - j ≠ π "Cut")
    (hph : ph + 1 = k) (hA : 0 ≤ π "A" - j - 1 ∧ π "A" - j - 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s - 1 ∧ π "B" - j + s - 1 ≤ v.len)
    (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len) (hB' : π "B" - j + s ≤ v.len)
    (hAW : π "A" - j ≤ W) (hρP : ρ "P" = false) (hρB : ρ "B" = false) (hρK : ρ "KP" = false) :
    iterS W ρ 3 v = some { v with ctl := rsLoop k 0 ne, pos := rsPos π (j + 1) (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = false := by rw [hp]; simp [rsPos, hne]
  have e1 := step_equal hv
  rw [hd, rs_resume_back] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack } =
      some { v with
        ctl := .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift
        pos := rsPos π (j + 1) s } := by
    rw [step_move (v := { v with ctl := .pending [.resetShift k true ph (some ne) 3] rsBack })
      (ms := [⟨"A", -1⟩, ⟨"B", -1⟩]) rfl (by simp only [HVM.len]; rw [hp]; exact rs_move_back π j s _ hA hB)]
    rw [show (Ctl.pending [.resetShift k true ph (some ne) 3] (.move [⟨"A", -1⟩, ⟨"B", -1⟩])) =
      .pending [.resetShift k true ph (some ne) 3] rsBack from rfl, rs_resume_wrap k ph ne hph]
  have e3 : stepMatch { v with
        ctl := .pending [.resetShift k true (ph + 1) (some ne) 5] rsShift
        pos := rsPos π (j + 1) s } =
      some { v with ctl := rsLoop k 0 ne, pos := rsPos π (j + 1) (s + 1) } := by
    have := rs_wrap k ph ne v π j s hv hp hne hph hA hB hP hB'
    simpa [iterStep, e1, e2] using this
  refine iterS_step hv ⟨by decide, by decide⟩ e1 (iterS_step rfl ?_ e2 (iterS_one rfl ?_ e3))
  · show EvOk W ρ v.pos _ (.move [⟨"A", -1⟩, ⟨"B", -1⟩])
    exact evOk_rsBack _ _ (by rw [hp]; simp [rsPos]; omega) hρB
  · exact evOk_rsShift _ _ hρP hρB hρK

theorem rs_exit_shiftS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = true) (hP : 0 ≤ π "P" + s + 1 ∧ π "P" + s + 1 ≤ v.len)
    (hB : 0 ≤ π "B" - j + s + 1 ∧ π "B" - j + s + 1 ≤ v.len)
    (hρP : ρ "P" = false) (hρB : ρ "B" = false) (hρK : ρ "KP" = false) :
    iterS W ρ 2 v = some { v with ctl := .returned none, pos := rsPos π j (s + 1) } := by
  have hd : decide (v.pos "A" = v.pos "Cut") = true := by rw [hp]; simp [rsPos, he]
  have e1 := step_equal hv
  rw [hd] at e1
  rw [show (Ctl.pending [.resetShift k true ph (some ne) 2] (.equal "A" "Cut")) = rsLoop k ph ne
    from rfl, rs_resume_exit_shift k ph ne h] at e1
  have e2 : stepMatch { v with ctl := .pending [.resetShift k true ph (some ne) 7] rsShift } =
      some { v with ctl := .returned none, pos := rsPos π j (s + 1) } := by
    have := rs_exit_shift k ph ne v π j s hv hp he h hP hB
    simpa [iterStep, e1] using this
  exact iterS_step hv ⟨by decide, by decide⟩ e1 (iterS_one rfl (evOk_rsShift _ _ hρP hρB hρK) e2)

theorem rs_exit_retS (k ph : ℕ) (ne : Bool) (v : HVM) (π : String → ℤ) (j s : ℤ)
    (hv : v.ctl = rsLoop k ph ne) (hp : v.pos = rsPos π j s) (he : π "A" - j = π "Cut")
    (h : (!ne || ph != 0) = false) :
    iterS W ρ 1 v = some { v with ctl := .returned none } :=
  iterS_one hv ⟨by decide, by decide⟩ (stepMatch_of_one (rs_exit_ret k ph ne v π j s hv hp he h))

theorem rs_loop_runS (k : ℕ) (hk : 1 ≤ k) (π : String → ℤ) (L : ℤ) (ne : Bool) (q : ℕ)
    (hne : ne = decide (q ≠ 0)) (hAW : π "A" ≤ W) (hρP : ρ "P" = false) (hρB : ρ "B" = false)
    (hρK : ρ "KP" = false) :
    ∀ (m : ℕ) (v : HVM) (j sh : ℕ), j + m = q → sh = j / k → v.ctl = rsLoop k (j % k) ne →
      v.pos = rsPos π j sh → v.len = L →
      π "A" - q = π "Cut" → 0 ≤ π "Cut" → π "A" - j ≤ L → (q : ℤ) ≤ π "B" →
      π "B" - j + sh ≤ L → π "B" - q + (rsShifts k q : ℕ) ≤ L → 0 ≤ π "P" →
      π "P" + (q / k : ℕ) + 1 ≤ L →
      ∃ n, n ≤ 3 * m + 2 ∧
        iterS W ρ n v = some { v with ctl := .returned none, pos := rsPos π q (rsShifts k q : ℕ) }
  | 0, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hBL, hBF, hP0, hPL => by
    have hj : j = q := by omega
    subst hj
    have hshq : sh = j / k := hsh
    by_cases hx : (!ne || j % k != 0) = true
    · refine ⟨2, by omega, ?_⟩
      have : (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx; simp at hx
        rcases hx with h0 | h0
        · exact Or.inl h0
        · exact Or.inr h0
      have hrs : rsShifts k j = sh + 1 := by simp only [rsShifts, if_pos this, hshq]
      rw [hrs] at hBF
      rw [rs_exit_shiftS k (j % k) ne v π j sh hv hp (by omega) hx
        ⟨by positivity, by rw [hshq]; omega⟩ ⟨by omega, by push_cast at hBF; omega⟩ hρP hρB hρK]
      simp only [rsShifts, if_pos this, hshq, Nat.cast_add, Nat.cast_one]
    · refine ⟨1, by omega, ?_⟩
      have hx' : (!ne || j % k != 0) = false := by simpa using hx
      rw [rs_exit_retS k (j % k) ne v π j sh hv hp (by omega) hx']
      have : ¬ (j = 0 ∨ j % k ≠ 0) := by
        rw [hne] at hx'; simp at hx'; omega
      simp only [rsShifts, if_neg this, Nat.add_zero, ← hshq, hp]
  | m + 1, v, j, sh, hjm, hsh, hv, hp, hL, he, hC, hAL, hBq, hBL, hBF, hP0, hPL => by
    obtain ⟨hs1, hs2⟩ := modstep j k hk
    have hjq : sh ≤ q / k := by rw [hsh]; exact Nat.div_le_div_right (by omega)
    rcases Nat.lt_or_ge (j % k + 1) k with hph | hph
    · obtain ⟨hm1, hd1⟩ := hs1 hph
      have hstep := rs_iterS (W := W) (ρ := ρ) k (j % k) ne v π j sh hv hp (by omega) hph
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) hρB
      obtain ⟨n, hn, hrun⟩ := rs_loop_runS k hk π L ne q hne hAW hρP hρB hρK m
        { v with ctl := rsLoop k (j % k + 1) ne, pos := rsPos π (↑j + 1) sh } (j + 1) sh
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        (by push_cast; omega) hBF hP0 hPL
      refine ⟨2 + n, by omega, ?_⟩
      rw [iterS_add, hstep, Option.bind_some, hrun]
    · have hph' : j % k + 1 = k := by have := Nat.mod_lt j (show 0 < k by omega); omega
      obtain ⟨hm1, hd1⟩ := hs2 hph'
      have hj1 : sh + 1 ≤ q / k := by
        rw [hsh, ← hd1]; exact Nat.div_le_div_right (by omega)
      have hstep := rs_wrapS (W := W) (ρ := ρ) k (j % k) ne v π j sh hv hp (by omega) hph'
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
        hρP hρB hρK
      obtain ⟨n, hn, hrun⟩ := rs_loop_runS k hk π L ne q hne hAW hρP hρB hρK m
        { v with ctl := rsLoop k 0 ne, pos := rsPos π (↑j + 1) (↑sh + 1) } (j + 1) (sh + 1)
        (by omega) (by rw [hd1, hsh]) (by rw [hm1]) (by push_cast; rfl) hL he hC (by omega) hBq
        (by push_cast; omega) hBF hP0 hPL
      refine ⟨3 + n, by omega, ?_⟩
      rw [iterS_add, hstep, Option.bind_some, hrun]

/-- **`ResetShift k true` under the side conditions**: `ScaHeadGen.resetShift_run`, guarded. -/
theorem resetShift_runS (k : ℕ) (hk : 1 ≤ k) (v : HVM) (q : ℕ)
    (hv : v.ctl = Ctl.ofOutcome (next [.resetShift k true 0 none 0] none))
    (hq : v.pos "A" = v.pos "Cut" + q) (hC : 0 ≤ v.pos "Cut") (hAL : v.pos "A" ≤ v.len)
    (hBq : (q : ℤ) ≤ v.pos "B") (hBL : v.pos "B" ≤ v.len)
    (hBF : v.pos "B" - q + (rsShifts k q : ℕ) ≤ v.len) (hP0 : 0 ≤ v.pos "P")
    (hPL : v.pos "P" + (q / k : ℕ) + 1 ≤ v.len)
    (hAW : v.pos "A" ≤ W) (hρP : ρ "P" = false) (hρB : ρ "B" = false) (hρK : ρ "KP" = false) :
    ∃ n, n ≤ 3 * q + 3 ∧
      iterS W ρ n v = some { v with
        ctl := .returned none
        pos := rsPos v.pos q (rsShifts k q : ℕ) } := by
  rw [rs_start] at hv
  have h1 := rs_firstS (W := W) (ρ := ρ) k v hv
  have hne : decide (v.pos "A" ≠ v.pos "Cut") = decide (q ≠ 0) := by
    simp only [decide_eq_decide]; omega
  rw [hne] at h1
  obtain ⟨n, hn, hrun⟩ := rs_loop_runS (W := W) (ρ := ρ) k hk v.pos v.len (decide (q ≠ 0)) q rfl
    hAW hρP hρB hρK q
    { v with ctl := rsLoop k 0 (decide (q ≠ 0)) } 0 0 (by omega) (by simp) (by simp)
    (by simp [rsPos_zero]) rfl (by omega) hC (by simp; omega) hBq (by simp; omega) hBF hP0 hPL
  refine ⟨1 + n, by omega, ?_⟩
  rw [iterS_add, h1, Option.bind_some, hrun]

end PalPeg.ScaShiftSafe
