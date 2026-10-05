import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# One step of the reading machine on stacks: the frames of the rules

The frames `14` (a rule type or the end of the rule types), `15` (record a rule type) and `16` (a body or the end
of the bodies). Each program starts from `enc { s with ctl := K }` (the frame popped) and ends in `enc (pstep s)`, or
stops rejecting where `pstep` fails.

The frames `14` and `16` branch on the top token (`tokCase`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## Costs -/

/-- The cube in `frameCost`, kept folded so that `omega` sees it as one number. -/
def fcB (N : Nat) : Nat := (N + 1114113) * (N + 1114113) * (N + 1114113)

theorem frameCost_eq (N : Nat) : frameCost N = 100 * fcB N := rfl

theorem chB_le_fcB (N : Nat) : chB N ≤ fcB N :=
  Nat.le_mul_of_pos_right _ (by omega)

/-- A constant number of steps fits in a frame. -/
theorem const_le_frameCost (N c : Nat) (hc : c ≤ 1114113) : c ≤ frameCost N := by
  have h₁ := chB_big N
  have h₂ := chB_le_fcB N
  rw [frameCost_eq]; omega

/-- A comparison of two numbers at most `N`, plus a constant, fits in a frame. -/
theorem cmp_le_frameCost {N a b : Nat} (ha : a ≤ N) (hb : b ≤ N) (c : Nat) (hc : c ≤ 1114113) :
    (a + b + 1) * (2 * a + 6) + c ≤ frameCost N := by
  have hm := Nat.mul_le_mul (show a + b + 1 ≤ 2 * (N + 1114113) by omega)
    (show 2 * a + 6 ≤ 2 * (N + 1114113) by omega)
  rw [Nat.mul_assoc, Nat.mul_left_comm (N + 1114113), ← Nat.mul_assoc] at hm
  have h₁ := chB_big N
  have h₂ := chB_le_fcB N
  have h₃ : (N + 1114113) * (N + 1114113) = chB N := rfl
  rw [h₃] at hm
  rw [frameCost_eq]; omega

/-! ## Small moves -/

theorem enc_tk_K (s : PSt) (K : List Nat) : (enc { s with ctl := K }) TK = s.tk.reverse := rfl

/-- Popping the token `v` leaves the state with the rest `r` of the tokens. -/
theorem enc_pop_tk (s : PSt) (K r : List Nat) :
    (enc { s with ctl := K }).set TK r.reverse = enc { s with ctl := K, tk := r } := by
  rw [enc_with_tk { s with ctl := K } r]

/-- Push one frame. -/
theorem push1_runs (s : PSt) (K : List Nat) (a : Nat) :
    NRuns (npushC CTL a) (enc { s with ctl := K }) (enc { s with ctl := a :: K }) (a + 1) := by
  have e := enc_ctl_snoc s K a
  have x := nruns_pushC CTL (enc { s with ctl := K }) a
  exact e ▸ x

/-- Set the current context to `0`. -/
def curZeroP : NProg NK := .seq (.prim (.pop CUR)) (.prim (.pushZ CUR))

theorem curZeroP_runs (t : PSt) : NRuns curZeroP (enc t) (enc { t with cur := 0 }) 2 := by
  have x₁ := nruns_pop CUR (enc t) (l := []) (v := t.cur) rfl
  have x₂ := nruns_pushZ CUR ((enc t).set CUR [])
  rw [Lists.set_same, Lists.set_set_u] at x₂
  have e : (enc t).set CUR ([] ++ [0]) = enc { t with cur := 0 } := by rw [enc_with_cur t 0]; rfl
  rw [e] at x₂
  exact x₁.seq x₂

/-! ## Branching on the top token -/

/-- Branch on the top token: `p0` on `0`, `p1` on `1` (the token popped); reject otherwise. -/
def tokCase (p0 p1 : NProg NK) : NProg NK := .ite TK .nonempty (caseTop TK [p0, p1] (.halt false)) (.halt false)

theorem tokCase_runs (p0 p1 : NProg NK) (s : PSt) (K : List Nat) {v : Nat} {r : List Nat} (ht : s.tk = v :: r)
    (hv : v < 2) {S' : Lists NK} {T : Nat} (h : NRuns ([p0, p1][v]'(by simp; omega)) (enc { s with ctl := K, tk := r }) S' T) :
    NRuns (tokCase p0 p1) (enc { s with ctl := K }) S' (T + 5) := by
  have hS : (enc { s with ctl := K }) TK = r.reverse ++ [v] := by rw [enc_tk_K, ht, List.reverse_cons]
  have x := caseTop_runs TK [p0, p1] (.halt false) v (by simp; omega) (enc { s with ctl := K }) r.reverse hS S' T
    (by rw [enc_pop_tk]; exact h)
  exact (x.iteT (by rw [hS]; simp)).mono (by omega)

theorem tokCase_halts (p0 p1 : NProg NK) (s : PSt) (K : List Nat) {v : Nat} {r : List Nat} (ht : s.tk = v :: r)
    (hv : v < 2) {S' : Lists NK} {T : Nat}
    (h : NHalts ([p0, p1][v]'(by simp; omega)) (enc { s with ctl := K, tk := r }) false S' T) :
    NHalts (tokCase p0 p1) (enc { s with ctl := K }) false S' (T + 5) := by
  have hS : (enc { s with ctl := K }) TK = r.reverse ++ [v] := by rw [enc_tk_K, ht, List.reverse_cons]
  have x := caseTop_halts TK [p0, p1] (.halt false) v (by simp; omega) (enc { s with ctl := K }) r.reverse hS false
    S' T (by rw [enc_pop_tk]; exact h)
  exact (x.iteT (by rw [hS]; simp)).mono (by omega)

/-- No token, or a token other than `0` and `1`: reject. -/
theorem tokCase_bad (p0 p1 : NProg NK) (s : PSt) (K : List Nat) (ht : ∀ r, s.tk ≠ 0 :: r ∧ s.tk ≠ 1 :: r) :
    ∃ S', NHalts (tokCase p0 p1) (enc { s with ctl := K }) false S' 6 := by
  obtain htk | ⟨w, r, htk⟩ : s.tk = [] ∨ ∃ w r, s.tk = (w + 2) :: r := by
    rcases h : s.tk with _ | ⟨_ | _ | w, r⟩
    · exact .inl rfl
    · exact absurd h (ht r).1
    · exact absurd h (ht r).2
    · exact .inr ⟨w, r, rfl⟩
  · exact ⟨_, ((nhalts_halt false _).iteF (by rw [enc_tk_K, htk]; rfl)).mono (by omega)⟩
  · have hS : (enc { s with ctl := K }) TK = r.reverse ++ [w + [p0, p1].length] := by
      rw [enc_tk_K, htk, List.reverse_cons]; rfl
    have x := caseTop_default TK [p0, p1] (.halt false) w (enc { s with ctl := K }) r.reverse hS false _ 1
      (nhalts_halt false _)
    exact ⟨_, (x.iteT (by rw [hS]; simp)).mono (by simp)⟩

/-! ## Frame `14`: a rule type, or the end of the rule types -/

/-- Token `0`: go to the bodies (`16`); token `1`: read a type, then record it (`1 :: 15`). -/
def frame14P : NProg NK := tokCase (npushC CTL 16) (push2 15 1)

theorem frame14_frame (s : PSt) (K : List Nat) (hc : s.ctl = 14 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame14P s K (frameCost N) := by
  have hT := const_le_frameCost N 30 (by omega)
  rcases htk : s.tk with _ | ⟨_ | _ | v, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)
  · have he : pstep s = { s with tk := r, ctl := 16 :: K } := by simp only [pstep, hc, htk]
    have x := tokCase_runs (npushC CTL 16) (push2 15 1) s K htk (by omega) (push1_runs { s with tk := r } K 16)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · have he : pstep s = { s with tk := r, ctl := 1 :: 15 :: K } := by simp only [pstep, hc, htk]
    have x := tokCase_runs (npushC CTL 16) (push2 15 1) s K htk (by omega) (push2_runs { s with tk := r } K 15 1)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)

/-! ## Frame `15`: record a rule type -/

/-- Move the type on top of `TY` to the rule types, count it, and go back to `14`. -/
def frame15P : NProg NK :=
  .ite TY .nonempty (.seq (nmv TY RTs (by decide)) (.seq (.prim (.inc NRT)) (npushC CTL 14))) (.halt false)

/-- The stacks after recording the rule type `t` (with the rest `r` of the types). -/
theorem frame15_state (s : PSt) (K r : List Nat) (t : Nat) :
    ((((enc { s with ctl := K }).set RTs (s.rt ++ [t])).set TY r.reverse).set NRT [s.rt.length + 1]).set CTL
        (K.reverse ++ [14]) =
      enc { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] } := by
  have e₁ := enc_with_ty { s with ctl := K } r
  have e₂ := enc_with_rt { s with ctl := K, ty := r } (s.rt ++ [t])
  have e₃ := enc_with_ctl { s with ctl := K, ty := r, rt := s.rt ++ [t] } (14 :: K)
  have e : enc { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] } =
      ((((enc { s with ctl := K }).set TY r.reverse).set RTs (s.rt ++ [t])).set NRT [s.rt.length + 1]).set CTL
        (K.reverse ++ [14]) := by
    rw [show enc { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] } =
      enc { ({ s with ctl := K, ty := r, rt := s.rt ++ [t] } : PSt) with ctl := 14 :: K } from rfl, e₃, e₂, e₁]
    simp
  rw [e, Lists.set_comm (show (TY : Fin NK) ≠ RTs by decide)]

theorem frame15_frame (s : PSt) (K : List Nat) (hc : s.ctl = 15 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame15P s K (frameCost N) := by
  have hT := const_le_frameCost N 30 (by omega)
  rcases hty : s.ty with _ | ⟨t, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · have he : pstep s = { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] } := by simp only [pstep, hc, hty]
    let S := enc { s with ctl := K }
    have hTY : S TY = r.reverse ++ [t] := by simp only [S]; rw [enc_ty_K, hty, List.reverse_cons]
    have x₁ := nruns_mv TY RTs (by decide) S hTY
    let S₁ := (S.set RTs (S RTs ++ [t])).set TY r.reverse
    have x₂ := nruns_inc NRT S₁ (l := []) (v := s.rt.length) rfl
    have x₃ := nruns_pushC CTL (S₁.set NRT ([] ++ [s.rt.length + 1])) 14
    have e : (S₁.set NRT ([] ++ [s.rt.length + 1])).set CTL ((S₁.set NRT ([] ++ [s.rt.length + 1])) CTL ++ [14]) =
        enc { s with ctl := 14 :: K, ty := r, rt := s.rt ++ [t] } := by
      rw [← frame15_state s K r t]; rfl
    rw [e] at x₃
    exact frameOK_run he (((x₁.seq (x₂.seq x₃)).iteT (by rw [hTY]; simp)).mono (by omega)) rfl hs

/-! ## Frame `16`: a body, or the end of the bodies -/

/-- Token `0`: all bodies are read (`NB = NRT`), so read the start (`0 :: 18`); token `1`: read a body
(`0 :: 17`). Both in the empty context. -/
def frame16P : NProg NK :=
  tokCase
    (.seq (cmpTop NB NRT 18 19 20 21 (by decide) (by decide))
      (caseTop 21 [.halt false, .seq curZeroP (push2 18 0), .halt false] (.halt false)))
    (.seq curZeroP (push2 17 0))

theorem frame16_frame (s : PSt) (K : List Nat) (hc : s.ctl = 16 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame16P s K (frameCost N) := by
  have hT := const_le_frameCost N 30 (by omega)
  have hbN : s.bodies.length ≤ N := by unfold tsize at hN; omega
  have hrN : s.rt.length ≤ N := by unfold tsize at hN; omega
  have hcmp := cmp_le_frameCost hbN hrN 100 (by omega)
  rcases htk : s.tk with _ | ⟨_ | _ | v, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)
  · -- compare the numbers of bodies and of rule types
    let S := enc { s with ctl := K, tk := r }
    have x₁ := nruns_cmpTop NB NRT 18 19 20 21 (by decide) (by decide) (by decide) S (li := []) (lj := [])
      (a := s.bodies.length) (b := s.rt.length) rfl rfl
    have h21 : S 21 = [] := enc_scratch _ 21 (by decide)
    have hres : S.set 21 (S 21 ++ [cmpRes s.bodies.length s.rt.length]) 21 =
        S 21 ++ [cmpRes s.bodies.length s.rt.length] := Lists.set_same _ _ _
    by_cases hl : s.bodies.length = s.rt.length
    · have he : pstep s = { s with tk := r, ctl := 0 :: 18 :: K, cur := 0 } := by
        simp only [pstep, hc, htk, hl, if_true]
      have y₁ := curZeroP_runs { s with ctl := K, tk := r }
      have y₂ := push2_runs { s with tk := r, cur := 0 } K 18 0
      have hr1 : cmpRes s.bodies.length s.rt.length = 1 := by rw [hl]; exact cmpRes_eq _
      rw [hr1] at x₁ hres
      have x₂ := caseTop_runs (21 : Fin NK) [.halt false, .seq curZeroP (push2 18 0), .halt false] (.halt false) 1
        (by simp) _ (S 21) hres _ _ (by rw [Lists.set_set_u, Lists.set_get_self]; exact y₁.seq y₂)
      have x := tokCase_runs _ (.seq curZeroP (push2 17 0)) s K htk (by omega) (x₁.seq x₂)
      exact frameOK_run he (x.mono (by omega)) rfl hs
    · have he : pstep s = s.fail := by simp only [pstep, hc, htk, hl, if_false]
      have hlt : s.bodies.length < s.rt.length ∨ s.rt.length < s.bodies.length := by omega
      have hcase : ∀ w, w = cmpRes s.bodies.length s.rt.length → w ≠ 1 →
          ∃ S', NHalts (caseTop (21 : Fin NK) [.halt false, .seq curZeroP (push2 18 0), .halt false] (.halt false))
            (S.set 21 (S 21 ++ [cmpRes s.bodies.length s.rt.length])) false S' 8 := by
        intro w hw hw1
        rw [← hw] at hres ⊢
        rcases hlt with h | h
        · have hw0 : w = 0 := by rw [hw]; exact cmpRes_lt h
          subst hw0
          exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 0 (by simp) _ (S 21) hres false _ 1
            (nhalts_halt false _)).mono (by omega)⟩
        · have hw2 : w = 2 := by rw [hw]; exact cmpRes_gt h
          subst hw2
          exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 2 (by simp) _ (S 21) hres false _ 1
            (nhalts_halt false _)).mono (by omega)⟩
      obtain ⟨S', x₂⟩ := hcase _ rfl (by
        rcases hlt with h | h
        · rw [cmpRes_lt h]; omega
        · rw [cmpRes_gt h]; omega)
      have x := tokCase_halts _ (.seq curZeroP (push2 17 0)) s K htk (by omega) (x₁.seqH x₂)
      exact frameOK_halt he ⟨S', x.mono (by omega)⟩
  · have he : pstep s = { s with tk := r, ctl := 0 :: 17 :: K, cur := 0 } := by simp only [pstep, hc, htk]
    have y₁ := curZeroP_runs { s with ctl := K, tk := r }
    have y₂ := push2_runs { s with tk := r, cur := 0 } K 17 0
    have x := tokCase_runs (.seq (cmpTop NB NRT 18 19 20 21 (by decide) (by decide))
      (caseTop 21 [.halt false, .seq curZeroP (push2 18 0), .halt false] (.halt false))) _ s K htk (by omega)
      (y₁.seq y₂)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)

end Shallot.MacroPeg.Mach
