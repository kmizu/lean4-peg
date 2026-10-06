import MacroPeg.HigherOrder.Mach.MainCost1

/-!
# The steps of the whole decision

The decision on stacks of order `j ≥ 1` runs in at most `tower j (c · (n + 1)^d)` steps on `n` bits (`mainCost_le`).
The reading and the order stage are polynomial (`readStage_poly`, `ordStage_poly`); the tables and the evaluation
are a tower of a polynomial (`evalStage_tower`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity
open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## The type stack and the tokens of the final reading state -/

set_option linter.unusedSimpArgs false in
/-- One step pushes at most one type number. -/
theorem mc_pstep_ty (s : PSt) : (pstep s).ty.length ≤ s.ty.length + 1 := by
  unfold pstep readExpr readType binDone unDone
  repeat' split
  all_goals first
    | (simp [PSt.fail, PSt.leaf]; done)
    | (simp [PSt.fail, PSt.leaf]; omega)
    | (simp_all [PSt.fail, PSt.leaf]; done)
    | (simp_all [PSt.fail, PSt.leaf]; omega)

theorem mc_run_ty_tk : ∀ (m : Nat) (s : PSt),
    (pruns s m).ty.length ≤ s.ty.length + m ∧ (pruns s m).tk.length ≤ s.tk.length
  | 0, s => by simp [pruns]
  | m + 1, s => by
    rw [pruns_succ]
    have h₁ := mc_pstep_ty s
    have h₂ := rs_pstep_tk s
    have h₃ := mc_run_ty_tk m (pstep s)
    omega

theorem fin_ty (w : List Bool) : (finalSt (ofBits w)).ty.length ≤ 4 * w.length + 1 := by
  have h := (mc_run_ty_tk (4 * (ofBits w).length + 1) (pinit (ofBits w))).1
  have := ofBits_length_le w
  have h0 : (pinit (ofBits w)).ty.length = 0 := rfl
  unfold finalSt; omega

theorem fin_tk (w : List Bool) : (finalSt (ofBits w)).tk.length ≤ w.length := by
  have h := (mc_run_ty_tk (4 * (ofBits w).length + 1) (pinit (ofBits w))).2
  have := ofBits_length_le w
  have h0 : (pinit (ofBits w)).tk = ofBits w := rfl
  rw [h0] at h
  unfold finalSt; omega

/-! ## Encodings -/

theorem encLits_length_le {lt : List (List Nat)} {B : Nat} (h : ∀ l ∈ lt, l.length ≤ B) :
    (encLits lt).length ≤ lt.length * (B + 1) := by
  induction lt with
  | nil => simp [encLits]
  | cons l lt ih =>
    have h₁ := h l List.mem_cons_self
    have h₂ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    simp only [encLits, List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
      List.length_nil] at h₂ ⊢
    rw [Nat.succ_mul]; omega

theorem encBodies_sum_le {bodies : List (List MItem)} {B : Nat} (h13 : 13 ≤ B)
    (h : ∀ it ∈ bodies.flatten, ∀ c ∈ encItem it, c ≤ B) : (encBodies bodies).sum ≤ (encBodies bodies).length * B :=
  sum_le_of_small (fun c hc => by
    simp only [encBodies, encItems, List.mem_flatMap, List.mem_append, List.mem_singleton] at hc
    obtain ⟨b, hb, (⟨it, hit, hc⟩ | rfl)⟩ := hc
    · exact h it (List.mem_flatten.2 ⟨b, hb, hit⟩) c hc
    · exact h13)

theorem encItems_sum_le {l : List MItem} {B : Nat} (h : ∀ it ∈ l, ∀ c ∈ encItem it, c ≤ B) :
    (encItems l).sum ≤ (encItems l).length * B :=
  sum_le_of_small (fun c hc => by
    simp only [encItems, List.mem_flatMap] at hc
    obtain ⟨it, hit, hc⟩ := hc
    exact h it hit c hc)

theorem itemValBound_mono {a b : Nat} (h : a ≤ b) : itemValBound a ≤ itemValBound b := by
  unfold itemValBound
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 100 (show a + 1 ≤ b + 1 by omega))
    (show a + 1 ≤ b + 1 by omega)) (show a + 1 ≤ b + 1 by omega)
  omega

/-- The numbers in the items of an accepted final state are at most `itemValBound n + finS n + 13`. -/
theorem fin_item_entries {w : List Bool} {R : List HO.Ty} {bis : List (List Item)} {is : List Item}
    {x : List Char} (hr : ReadOK (finalSt (ofBits w)) R bis is x) :
    ∀ it ∈ (finalSt (ofBits w)).bodies.flatten ++ (finalSt (ofBits w)).start, ∀ c ∈ encItem it,
      c ≤ itemValBound w.length + finS w.length + 13 := by
  intro it hit c hc
  have ht := (read_tags hr it hit).1
  have hab := finalSt_itemVals (ofBits w) it hit
  have hctx := read_ctx_le hr it hit
  have hm := itemValBound_mono (ofBits_length_le w)
  have hF := fin_tsize w
  unfold tsize at hF
  simp only [encItem, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> omega

/-! ## Polynomials in `n + 1` -/

theorem m_pos (n : Nat) : 1 ≤ n + 1 := by omega

theorem M_pos (n : Nat) : 1 ≤ (n + 1) ^ 8 := by
  have := Nat.pow_le_pow_left (m_pos n) 8; rwa [Nat.one_pow] at this

theorem n_le_M (n : Nat) : n + 1 ≤ (n + 1) ^ 8 := by
  have := Nat.pow_le_pow_right (m_pos n) (show 1 ≤ 8 by decide); rwa [Nat.pow_one] at this

theorem m1 (n : Nat) : n + 1 ≤ 1 * (n + 1) ^ 1 := by simp

theorem pF2 (n : Nat) : finS n ≤ 15 * (n + 1) ^ 2 := by
  have h₁ : 4 * n + 1 ≤ (4 + 1) * (n + 1) ^ 1 := pm_lin 4 1 n
  have h₂ : n + 2 ≤ (1 + 2) * (n + 1) ^ 1 := Nat.le_trans (by omega) (pm_lin 1 2 n)
  exact Nat.le_trans (pm_mul h₁ h₂) (Nat.mul_le_mul_right _ (by decide))

theorem pF (n : Nat) : finS n ≤ 15 * (n + 1) ^ 8 := pm_lift (m_pos n) (pF2 n) (by decide)

theorem pPb (n : Nat) : Pb (finS n) (3 * n + 2) ≤ 21792 * (n + 1) ^ 8 := by
  have hm := m_pos n
  have hF := pF2 n
  have hF1 : finS n + 1 ≤ (15 + 1) * (n + 1) ^ 2 := pm_add hF (pm_lift hm (pm_const 1) (by decide))
  have hF2 : finS n + 2 ≤ (15 + 2) * (n + 1) ^ 2 := pm_add hF (pm_lift hm (pm_const 2) (by decide))
  have hP : polyP (finS n) ≤ ((15 + 1) * (15 + 2)) * (n + 1) ^ (2 + 2) := pm_mul hF1 hF2
  have hPc := pm_mul hP (pm_lin 3 2 n)
  have hPc2 := pm_add hPc (pm_lift hm (pm_const 2) (show 0 ≤ 2 + 2 + 1 by decide))
  have h := pm_lift hm (pm_mul hF1 hPc2) (show 2 + (2 + 2 + 1) ≤ 8 by decide)
  unfold Pb
  exact Nat.le_trans h (Nat.mul_le_mul_right _ (by decide))

theorem pIVB : ∃ k, ∀ n, itemValBound n + finS n + 13 ≤ k * (n + 1) ^ 3 := by
  apply Exists.intro
  intro n
  have hm := m_pos n
  have h₁ := pm_mul (pm_mul (pm_mul (pm_const (m := n + 1) 100) (m1 n)) (m1 n)) (m1 n)
  have h₂ := pm_add (pm_add (pm_add (pm_lift hm (pm_const 1114112) (show 0 ≤ 0 + 1 + 1 + 1 by decide)) h₁)
    (pm_lift hm (pF2 n) (show 2 ≤ 0 + 1 + 1 + 1 by decide)))
    (pm_lift hm (pm_const 13) (show 0 ≤ 0 + 1 + 1 + 1 by decide))
  unfold itemValBound
  exact h₂

theorem pEB2 (n : Nat) : 4 * (4 * n + 1) + finS n ≤ 35 * (n + 1) ^ 2 := by
  have h₁ := pF2 n
  have h₂ : 1 ≤ (n + 1) ^ 2 := by have := Nat.pow_le_pow_left (m_pos n) 2; rwa [Nat.one_pow] at this
  have h₃ : n + 1 ≤ (n + 1) ^ 2 := by
    have := Nat.pow_le_pow_right (m_pos n) (show 1 ≤ 2 by decide); rwa [Nat.pow_one] at this
  omega

theorem pEBs : ∃ k, ∀ n, (4 * (4 * n + 1) + finS n) * (itemValBound n + finS n + 13) ≤ k * (n + 1) ^ 8 := by
  obtain ⟨k, hk⟩ := pIVB
  apply Exists.intro
  intro n
  exact pm_lift (m_pos n) (pm_mul (pEB2 n) (hk n)) (show 2 + 3 ≤ 8 by decide)

theorem pLits : ∃ k, ∀ n, finS n * (n + 1) ≤ k * (n + 1) ^ 8 := by
  apply Exists.intro
  intro n
  exact pm_lift (m_pos n) (pm_mul (pF2 n) (m1 n)) (show 2 + 1 ≤ 8 by decide)

/-! ## The first stage -/

/-- **The reading stage is polynomial.** -/
theorem readStage_poly : ∃ k, ∀ w : List Bool, readStageCost w ≤ k * (w.length + 1) ^ 8 := by
  apply Exists.intro
  intro w
  unfold readStageCost readCost readStepCost frameCost readBound
  have hm := m_pos w.length
  have hL := ofBits_length_le w
  generalize (ofBits w).length = L at hL ⊢
  generalize w.length = n at hm hL ⊢
  have h4L1 : 4 * L + 1 ≤ (4 + 1) * (n + 1) ^ 1 := Nat.le_trans (by omega) (pm_lin 4 1 n)
  have h4L3 : 4 * L + 3 ≤ (4 + 3) * (n + 1) ^ 1 := Nat.le_trans (by omega) (pm_lin 4 3 n)
  have h4L : 4 * L ≤ (4 + 0) * (n + 1) ^ 1 := Nat.le_trans (by omega) (pm_lin 4 0 n)
  have hRB := pm_add (pm_lift hm h4L (show 1 ≤ 1 + 1 by decide)) (pm_mul h4L1 h4L3)
  have hX := pm_add hRB (pm_lift hm (pm_const 1114113) (show 0 ≤ 1 + 1 by decide))
  have hFC := pm_mul (pm_const 100) (pm_mul (pm_mul hX hX) hX)
  have hRS := pm_add (pm_add (pm_add hFC (pm_lift hm (pm_const 30) (by decide))) (pm_lift hm (pm_const 40) (by decide)))
      (pm_lift hm (pm_const 1) (by decide))
  have hRC := pm_add (pm_lift hm (pm_mul h4L1 hRS) (show 1 + (0 + (1 + 1 + (1 + 1) + (1 + 1))) ≤ 8 by decide))
    (pm_lift hm (pm_const 1) (show 0 ≤ 8 by decide))
  have h20 : 20 * (n + 1) ≤ (1 * 20) * (n + 1) ^ 1 := by rw [Nat.pow_one]; omega
  have h100 : 100 * (n + 1) ≤ (1 * 100) * (n + 1) ^ 1 := by rw [Nat.pow_one]; omega
  exact pm_add (pm_add (pm_lift hm h20 (by decide)) (pm_lift hm h100 (by decide))) hRC

/-! ## The order stage -/

/-- **The order stage is polynomial** (with a constant depending on `j`). -/
theorem ordStage_poly (j : Nat) :
    ∃ k, ∀ w : List Bool, ordStageCost j (capOf w) (finalSt (ofBits w)) ≤ k * (w.length + 1) ^ 8 := by
  apply Exists.intro
  intro w
  have hm := m_pos w.length
  have hF2 := pF2 w.length
  have hFt := fin_tsize w
  unfold tsize at hFt
  have hEB := Nat.le_trans (fin_encBodies_length w) (pEB2 w.length)
  have hEI : (encItems (finalSt (ofBits w)).start).length ≤ 20 * (w.length + 1) ^ 1 := by
    have := fin_encItems_length w; rw [Nat.pow_one]; omega
  have htk := fin_tk w
  have hcap : capOf w ≤ 5 * (w.length + 1) ^ 2 := by
    have := pm_lift hm (pm_lin 3 2 w.length) (show 1 ≤ 2 by decide); unfold capOf; exact this
  have c1 : 1 ≤ 1 * (w.length + 1) ^ 2 := pm_lift hm (pm_const 1) (by decide)
  have hL : (finalSt (ofBits w)).tt.length ≤ 15 * (w.length + 1) ^ 2 := by omega
  have hR : (finalSt (ofBits w)).rt.length ≤ 15 * (w.length + 1) ^ 2 := by omega
  have hL1 := pm_add hL c1
  have hLc1 := pm_add (pm_add hL hcap) c1
  have hZ := pm_add (pm_add (pm_add (pm_add (pm_add (pm_lift hm (pm_const j) (show 0 ≤ 2 by decide)) hL) hR) hEB)
    (pm_lift hm hEI (show 1 ≤ 2 by decide))) c1
  have hT₁ := pm_mul (pm_mul (pm_mul (pm_const 1000) hL1) hL1) hL1
  have hT₂ := pm_mul (pm_mul (pm_mul (pm_const 1000) hZ) hZ) hZ
  have hT₃ := pm_mul (pm_mul (pm_mul (pm_const 1000) hLc1) hLc1) hLc1
  have hT₄ : 2 * (finalSt (ofBits w)).tk.length + 1 ≤ (2 + 1) * (w.length + 1) ^ 1 :=
    Nat.le_trans (by omega) (pm_lin 2 1 w.length)
  have hT₅ : 8 * (finalSt (ofBits w)).x.length + 4 ≤ 124 * (w.length + 1) ^ 2 := by omega
  unfold ordStageCost ordCheckCost
  exact pm_add (pm_add (pm_add (pm_add (pm_lift hm hT₁ (by decide)) (pm_lift hm hT₂ (by decide)))
    (pm_lift hm hT₃ (by decide))) (pm_lift hm hT₄ (by decide))) (pm_lift hm hT₅ (by decide))

/-! ## The tables and the evaluation -/

theorem twK {j : Nat} (k : Nat) {M : Nat} (hM : 1 ≤ M) : k ≤ tower j (k * M) :=
  twL (Nat.le_mul_of_pos_right _ hM)

theorem cube (x : Nat) : x ^ 3 = x * x * x := by
  rw [show 3 = 0 + 1 + 1 + 1 from rfl, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

/-- **The tables and the evaluation are at most a tower of height `j` of a polynomial.** -/
theorem evalStage_tower {j : Nat} (hj : 1 ≤ j) :
    ∃ k, ∀ w : List Bool, (finalSt (ofBits w)).ok = true → ordOK j (finalSt (ofBits w)) = true →
      evalStageCost j (capOf w) (finalSt (ofBits w)) ≤ tower j (k * (w.length + 1) ^ 8) := by
  obtain ⟨kLit, hkLit⟩ := pLits
  obtain ⟨kEBs, hkEBs⟩ := pEBs
  apply Exists.intro
  intro w hok ho
  -- the facts about the final state
  obtain ⟨R, bis, is, x, hr⟩ := final_readOK hok
  have hi := finalSt_minv (ofBits w)
  have hEv := evalCost_final hj w hok ho
  have hFt := fin_tsize w
  have hEBl := fin_encBodies_length w
  have hEIl := fin_encItems_length w
  have hty := fin_ty w
  have hent := fin_item_entries hr
  have hlit := finalSt_lit_len (ofBits w)
  have htkn := ofBits_length_le w
  have hM := M_pos w.length
  have hnM := n_le_M w.length
  have hFM := pF w.length
  have hPbM : Pb (finS w.length) (capOf w) ≤ 21792 * (w.length + 1) ^ 8 := pPb w.length
  have hcap1 : 1 ≤ capOf w := by unfold capOf; omega
  have hcapM : capOf w ≤ 5 * (w.length + 1) ^ 8 := by unfold capOf; omega
  have hLitM := hkLit w.length
  have hEBsM := hkEBs w.length
  have hEIsM : 4 * (4 * w.length + 1) * (itemValBound w.length + finS w.length + 13) ≤
      kEBs * (w.length + 1) ^ 8 :=
    Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hEBsM
  generalize finalSt (ofBits w) = st at *
  generalize (w.length + 1) ^ 8 = M at *
  have hsz := hFt
  unfold tsize at hsz
  -- the encodings
  have hEBs : (encBodies st.bodies).sum ≤ kEBs * M := by
    refine Nat.le_trans (encBodies_sum_le (B := itemValBound w.length + finS w.length + 13) (by omega)
      (fun it hit => hent it (List.mem_append_left _ hit))) ?_
    exact Nat.le_trans (Nat.mul_le_mul_right _ hEBl) hEBsM
  have hEIs : (encItems st.start).sum ≤ kEBs * M := by
    refine Nat.le_trans (encItems_sum_le (B := itemValBound w.length + finS w.length + 13)
      (fun it hit => hent it (List.mem_append_right _ hit))) ?_
    exact Nat.le_trans (Nat.mul_le_mul_right _ hEIl) hEIsM
  have hLits : (encLits st.lt).length ≤ kLit * M :=
    Nat.le_trans (encLits_length_le hlit)
      (Nat.le_trans (Nat.mul_le_mul (by omega) (by omega)) hLitM)
  -- towers of the sizes
  have tN : st.x.length ≤ tower j (15 * M) := twL (by omega)
  have tL : st.tt.length ≤ tower j (15 * M) := twL (by omega)
  have tC : st.ct.length ≤ tower j (15 * M) := twL (by omega)
  have tRl : st.rt.length ≤ tower j (15 * M) := twL (by omega)
  have tLl : st.lt.length ≤ tower j (15 * M) := twL (by omega)
  have tcap : capOf w ≤ tower j (5 * M) := twL hcapM
  have tLits : (encLits st.lt).length ≤ tower j (kLit * M) := twL hLits
  have tEBl : (encBodies st.bodies).length ≤ tower j (35 * M) := twL (by omega)
  have tEIl : (encItems st.start).length ≤ tower j (20 * M) := twL (by omega)
  have tEBs : (encBodies st.bodies).sum ≤ tower j (kEBs * M) := twL hEBs
  have tEIs : (encItems st.start).sum ≤ tower j (kEBs * M) := twL hEIs
  -- towers of the tables
  have tV : (valTable j (capOf w) st.x.length st.tt).sum ≤ tower j (21808 * M) :=
    tw_mono' (tb_valSum hj hcap1 hi hFt) (by omega)
  have tCn : (cntTable j (capOf w) st.x.length st.tt).sum ≤ tower j (21808 * M) :=
    tw_mono' (tb_cntSum hj hcap1 hi hFt) (by omega)
  have tE : (envTable j (capOf w) st.x.length st.tt st.ct).sum ≤ tower j (21808 * M) :=
    tw_mono' (tb_envSum hj hcap1 hi hFt) (by omega)
  have tRF : (rowsFlat j (capOf w) st.x.length st.tt).length ≤ tower j (43602 * M) :=
    tw_mono' (tb_rowsFlat hj hcap1 hi hFt) (by omega)
  have tCand : ((List.range (st.tt.length + 1)).map (candNum j (capOf w) st.x.length st.tt)).sum ≤
      tower j (43602 * M) :=
    tw_mono' (tb_candSum hj hcap1 hi hFt) (by omega)
  have tT0 : (zeroT j (capOf w) st).flatten.length ≤ tower j (21807 * M) :=
    tw_mono' (tb_zeroT hj hcap1 hi hFt) (by omega)
  have tFuel : (st.rt.map (valT j (capOf w) st.x.length st.tt)).sum ≤ tower j (21807 * M) :=
    tw_mono' (tb_fuel hj hcap1 hi hFt) (by omega)
  have hT0l : (zeroT j (capOf w) st).length = st.rt.length := by simp [zeroT]
  -- the rows tables
  have tz := twA hM (twA hM (twA hM (twA hM (twA hM (twK 2 hM) tN) tcap) tL) tRF) tCand
  have hRows := twC hj hM 1000 (twM hj hM (twM hj hM (twM hj hM (twM hj hM (twM hj hM tz tz) tz) tz) tz) tz)
  -- the value lengths and the environment counts
  have tv := twA hM (twA hM (twA hM (twA hM (twK 2 hM) tN) tL) tV) tCn
  have hVal := twC hj hM 1000 (twM hj hM (twM hj hM tv tv) tv)
  have te := twA hM (twA hM (twA hM (twA hM (twK 2 hM) tL) tC) tE) tCn
  have hEnv := twC hj hM 1000 (twM hj hM (twM hj hM te te) te)
  -- the clearing
  have hClear : clearCost st ≤ tower j (200 * M) := by
    unfold clearCost
    rw [encItems_length, List.length_reverse]
    exact twL (by omega)
  -- the evaluation
  have tPB := twM hj hM tE (twA hM (twA hM (twA hM tN (twK 1 hM)) tV) tT0)
  have tW := twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM
    (twA hM (twA hM (twK 2 hM) tRF) tT0) tRl) tC) tLl) tLits) tE) tV) tCn) tEBs) tEIs) tN) tL) tPB
  have tY := twM hj hM (twA hM tN (twK 1114116 hM)) (twA hM (twM hj hM (twC hj hM 2 (twA hM tEBl tEIl)) tPB) tW)
  have tK := twC hj hM 1000 (twP5 hj hM tY)
  have tR := twA hM (twA hM (twM hj hM (twA hM (twA hM tK (twK 600 hM)) (twC hj hM 100 tPB)) tEBl)
    (twC hj hM 100 tEBl))
    (twC hj hM 100 (twA hM (twA hM (twA hM (twA hM tEBl tT0) tRl) (twM hj hM tT0 (twA hM tN (twK 2 hM))))
      (twK 1 hM)))
  have tFu := twA hM tFuel (twK 1 hM)
  have tZ := twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM (twA hM tFu tRl) tT0) tV) tEIl)
    (twM hj hM tEIl tPB)) tN) tL) (twK 2 hM)
  have tB := twA hM (twA hM (twM hj hM (twC hj hM 1000 tZ) tZ)
    (twM hj hM (twA hM tFu (twK 1 hM)) (twA hM tR (twK 1 hM)))) (twM hj hM tEIl (twA hM tK (twK 500 hM)))
  unfold evBound evZ evR evFuel evPB itemK evalW pushBound at hEv
  simp only [List.length_map, hT0l] at hEv
  have hEval := Nat.le_trans hEv tB
  unfold evalStageCost rowsCost valCost envCostL
  rw [cube, cube]
  exact twA hM (twA hM (twA hM (twA hM hRows hVal) hEnv) hClear) hEval

/-! ## The whole decision -/

/-- **The decision on stacks of order `j ≥ 1` runs in at most a tower of height `j` of a polynomial.** -/
theorem mainCost_le {j : Nat} (hj : 1 ≤ j) :
    ∃ c d : Nat, ∀ w : List Bool, mainCost j w ≤ tower j (c * (w.length + 1) ^ d) := by
  obtain ⟨kr, hkr⟩ := readStage_poly
  obtain ⟨ko, hko⟩ := ordStage_poly j
  obtain ⟨ke, hke⟩ := evalStage_tower hj
  refine ⟨kr + ko + ke + 4, 8, fun w => ?_⟩
  have hM := M_pos w.length
  have tr : readStageCost w ≤ tower j (kr * (w.length + 1) ^ 8) := twL (hkr w)
  have to : ordStageCost j (capOf w) (finalSt (ofBits w)) ≤ tower j (ko * (w.length + 1) ^ 8) := twL (hko w)
  unfold mainCost
  cases hok : (finalSt (ofBits w)).ok
  · rw [stagesCost_fail]; exact twW tr (by omega)
  · cases hor : ordOK j (finalSt (ofBits w))
    · rw [stagesCost_high]; exact twW (twA hM tr to) (by omega)
    · rw [stagesCost_all]; exact twW (twA hM (twA hM tr to) (hke w hok hor)) (by omega)

end Shallot.MacroPeg.Mach
