import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# One step of the reading machine on stacks: the frames of the rules

The frames `14` (a rule type or the end of the rule types), `15` (record a rule type) and `16` (a body or the end
of the bodies). Each program starts from `enc { s with ctl := K }` (the frame popped) and ends in `enc (pstep s)`, or
stops rejecting where `pstep` fails.

The frames `14` and `16` branch on the top token (`rulesTokCase`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## Costs -/

/-- The cube in `frameCost`, kept folded so that `omega` sees it as one number. -/
def rulesFcB (N : Nat) : Nat := (N + 1114113) * (N + 1114113) * (N + 1114113)

theorem rulesFrameCost_eq (N : Nat) : frameCost N = 100 * rulesFcB N := rfl

theorem rules_chB_le_fcB (N : Nat) : chB N ≤ rulesFcB N :=
  Nat.le_mul_of_pos_right _ (by omega)

/-- A constant number of steps fits in a frame. -/
theorem rules_const_le_frameCost (N c : Nat) (hc : c ≤ 1114113) : c ≤ frameCost N := by
  have h₁ := chB_big N
  have h₂ := rules_chB_le_fcB N
  rw [rulesFrameCost_eq]; omega

/-- A comparison of two numbers at most `N`, plus a constant, fits in a frame. -/
theorem rules_cmp_le_frameCost {N a b : Nat} (ha : a ≤ N) (hb : b ≤ N) (c : Nat) (hc : c ≤ 1114113) :
    (a + b + 1) * (2 * a + 6) + c ≤ frameCost N := by
  have hm := Nat.mul_le_mul (show a + b + 1 ≤ 2 * (N + 1114113) by omega)
    (show 2 * a + 6 ≤ 2 * (N + 1114113) by omega)
  rw [Nat.mul_assoc, Nat.mul_left_comm (N + 1114113), ← Nat.mul_assoc] at hm
  have h₁ := chB_big N
  have h₂ := rules_chB_le_fcB N
  have h₃ : (N + 1114113) * (N + 1114113) = chB N := rfl
  rw [h₃] at hm
  rw [rulesFrameCost_eq]; omega

/-! ## Small moves -/

theorem rules_enc_tk_K (s : PSt) (K : List Nat) : (enc { s with ctl := K }) TK = s.tk.reverse := rfl

/-- Popping the token `v` leaves the state with the rest `r` of the tokens. -/
theorem rules_enc_pop_tk (s : PSt) (K r : List Nat) :
    (enc { s with ctl := K }).set TK r.reverse = enc { s with ctl := K, tk := r } := by
  rw [enc_with_tk { s with ctl := K } r]

/-- Push one frame. -/
theorem rules_push1_runs (s : PSt) (K : List Nat) (a : Nat) :
    NRuns (npushC CTL a) (enc { s with ctl := K }) (enc { s with ctl := a :: K }) (a + 1) := by
  have e := enc_ctl_snoc s K a
  have x := nruns_pushC CTL (enc { s with ctl := K }) a
  exact e ▸ x

/-- Set the current context to `0`. -/
def rulesCurZeroP : NProg NK := .seq (.prim (.pop CUR)) (.prim (.pushZ CUR))

theorem rules_curZeroP_runs (t : PSt) : NRuns rulesCurZeroP (enc t) (enc { t with cur := 0 }) 2 := by
  have x₁ := nruns_pop CUR (enc t) (l := []) (v := t.cur) rfl
  have x₂ := nruns_pushZ CUR ((enc t).set CUR [])
  rw [Lists.set_same, Lists.set_set_u] at x₂
  have e : (enc t).set CUR ([] ++ [0]) = enc { t with cur := 0 } := by rw [enc_with_cur t 0]; rfl
  rw [e] at x₂
  exact x₁.seq x₂

/-! ## Branching on the top token -/

/-- Branch on the top token: `p0` on `0`, `p1` on `1` (the token popped); reject otherwise. -/
def rulesTokCase (p0 p1 : NProg NK) : NProg NK := .ite TK .nonempty (caseTop TK [p0, p1] (.halt false)) (.halt false)

theorem rules_tokCase_runs (p0 p1 : NProg NK) (s : PSt) (K : List Nat) {v : Nat} {r : List Nat} (ht : s.tk = v :: r)
    (hv : v < 2) {S' : Lists NK} {T : Nat} (h : NRuns ([p0, p1][v]'(by simp; omega)) (enc { s with ctl := K, tk := r }) S' T) :
    NRuns (rulesTokCase p0 p1) (enc { s with ctl := K }) S' (T + 5) := by
  have hS : (enc { s with ctl := K }) TK = r.reverse ++ [v] := by rw [rules_enc_tk_K, ht, List.reverse_cons]
  have x := caseTop_runs TK [p0, p1] (.halt false) v (by simp; omega) (enc { s with ctl := K }) r.reverse hS S' T
    (by rw [rules_enc_pop_tk]; exact h)
  exact (x.iteT (by rw [hS]; simp)).mono (by omega)

theorem rules_tokCase_halts (p0 p1 : NProg NK) (s : PSt) (K : List Nat) {v : Nat} {r : List Nat} (ht : s.tk = v :: r)
    (hv : v < 2) {S' : Lists NK} {T : Nat}
    (h : NHalts ([p0, p1][v]'(by simp; omega)) (enc { s with ctl := K, tk := r }) false S' T) :
    NHalts (rulesTokCase p0 p1) (enc { s with ctl := K }) false S' (T + 5) := by
  have hS : (enc { s with ctl := K }) TK = r.reverse ++ [v] := by rw [rules_enc_tk_K, ht, List.reverse_cons]
  have x := caseTop_halts TK [p0, p1] (.halt false) v (by simp; omega) (enc { s with ctl := K }) r.reverse hS false
    S' T (by rw [rules_enc_pop_tk]; exact h)
  exact (x.iteT (by rw [hS]; simp)).mono (by omega)

/-- No token, or a token other than `0` and `1`: reject. -/
theorem rules_tokCase_bad (p0 p1 : NProg NK) (s : PSt) (K : List Nat) (ht : ∀ r, s.tk ≠ 0 :: r ∧ s.tk ≠ 1 :: r) :
    ∃ S', NHalts (rulesTokCase p0 p1) (enc { s with ctl := K }) false S' 6 := by
  obtain htk | ⟨w, r, htk⟩ : s.tk = [] ∨ ∃ w r, s.tk = (w + 2) :: r := by
    rcases h : s.tk with _ | ⟨_ | _ | w, r⟩
    · exact .inl rfl
    · exact absurd h (ht r).1
    · exact absurd h (ht r).2
    · exact .inr ⟨w, r, rfl⟩
  · exact ⟨_, ((nhalts_halt false _).iteF (by rw [rules_enc_tk_K, htk]; rfl)).mono (by omega)⟩
  · have hS : (enc { s with ctl := K }) TK = r.reverse ++ [w + [p0, p1].length] := by
      rw [rules_enc_tk_K, htk, List.reverse_cons]; rfl
    have x := caseTop_default TK [p0, p1] (.halt false) w (enc { s with ctl := K }) r.reverse hS false _ 1
      (nhalts_halt false _)
    exact ⟨_, (x.iteT (by rw [hS]; simp)).mono (by simp)⟩

/-! ## Frame `14`: a rule type, or the end of the rule types -/

/-- Token `0`: go to the bodies (`16`); token `1`: read a type, then record it (`1 :: 15`). -/
def frame14P : NProg NK := rulesTokCase (npushC CTL 16) (push2 15 1)

theorem frame14_frame (s : PSt) (K : List Nat) (hc : s.ctl = 14 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame14P s K (frameCost N) := by
  have hT := rules_const_le_frameCost N 30 (by omega)
  rcases htk : s.tk with _ | ⟨_ | _ | v, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((rules_tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)
  · have he : pstep s = { s with tk := r, ctl := 16 :: K } := by simp only [pstep, hc, htk]
    have x := rules_tokCase_runs (npushC CTL 16) (push2 15 1) s K htk (by omega) (rules_push1_runs { s with tk := r } K 16)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · have he : pstep s = { s with tk := r, ctl := 1 :: 15 :: K } := by simp only [pstep, hc, htk]
    have x := rules_tokCase_runs (npushC CTL 16) (push2 15 1) s K htk (by omega) (push2_runs { s with tk := r } K 15 1)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((rules_tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)

/-! ## Frame `15`: record a rule type -/

/-- Move the type on top of `TY` to the rule types, count it, and go back to `14`. -/
def frame15P : NProg NK :=
  .ite TY .nonempty (.seq (nmv TY RTs (by decide)) (.seq (.prim (.inc NRT)) (npushC CTL 14))) (.halt false)

/-- The stacks after recording the rule type `t` (with the rest `r` of the types). -/
theorem rules_frame15_state (s : PSt) (K r : List Nat) (t : Nat) :
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
  have hT := rules_const_le_frameCost N 30 (by omega)
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
      rw [← rules_frame15_state s K r t]; rfl
    rw [e] at x₃
    exact frameOK_run he (((x₁.seq (x₂.seq x₃)).iteT (by rw [hTY]; simp)).mono (by omega)) rfl hs

/-! ## Frame `16`: a body, or the end of the bodies -/

/-- Token `0`: all bodies are read (`NB = NRT`), so read the start (`0 :: 18`); token `1`: read a body
(`0 :: 17`). Both in the empty context. -/
def frame16P : NProg NK :=
  rulesTokCase
    (.seq (cmpTop NB NRT 18 19 20 21 (by decide) (by decide))
      (caseTop 21 [.halt false, .seq rulesCurZeroP (push2 18 0), .halt false] (.halt false)))
    (.seq rulesCurZeroP (push2 17 0))

theorem frame16_frame (s : PSt) (K : List Nat) (hc : s.ctl = 16 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame16P s K (frameCost N) := by
  have hT := rules_const_le_frameCost N 30 (by omega)
  have hbN : s.bodies.length ≤ N := by unfold tsize at hN; omega
  have hrN : s.rt.length ≤ N := by unfold tsize at hN; omega
  have hcmp := rules_cmp_le_frameCost hbN hrN 100 (by omega)
  rcases htk : s.tk with _ | ⟨_ | _ | v, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((rules_tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)
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
      have y₁ := rules_curZeroP_runs { s with ctl := K, tk := r }
      have y₂ := push2_runs { s with tk := r, cur := 0 } K 18 0
      have hr1 : cmpRes s.bodies.length s.rt.length = 1 := by rw [hl]; exact cmpRes_eq _
      rw [hr1] at x₁ hres
      have x₂ := caseTop_runs (21 : Fin NK) [.halt false, .seq rulesCurZeroP (push2 18 0), .halt false] (.halt false) 1
        (by simp) _ (S 21) hres _ _ (by rw [Lists.set_set_u, Lists.set_get_self]; exact y₁.seq y₂)
      have x := rules_tokCase_runs _ (.seq rulesCurZeroP (push2 17 0)) s K htk (by omega) (x₁.seq x₂)
      exact frameOK_run he (x.mono (by omega)) rfl hs
    · have he : pstep s = s.fail := by simp only [pstep, hc, htk, hl, if_false]
      have hlt : s.bodies.length < s.rt.length ∨ s.rt.length < s.bodies.length := by omega
      have hcase : ∀ w, w = cmpRes s.bodies.length s.rt.length → w ≠ 1 →
          ∃ S', NHalts (caseTop (21 : Fin NK) [.halt false, .seq rulesCurZeroP (push2 18 0), .halt false] (.halt false))
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
      have x := rules_tokCase_halts _ (.seq rulesCurZeroP (push2 17 0)) s K htk (by omega) (x₁.seqH x₂)
      exact frameOK_halt he ⟨S', x.mono (by omega)⟩
  · have he : pstep s = { s with tk := r, ctl := 0 :: 17 :: K, cur := 0 } := by simp only [pstep, hc, htk]
    have y₁ := rules_curZeroP_runs { s with ctl := K, tk := r }
    have y₂ := push2_runs { s with tk := r, cur := 0 } K 17 0
    have x := rules_tokCase_runs (.seq (cmpTop NB NRT 18 19 20 21 (by decide) (by decide))
      (caseTop 21 [.halt false, .seq rulesCurZeroP (push2 18 0), .halt false] (.halt false))) _ s K htk (by omega)
      (y₁.seq y₂)
    exact frameOK_run he (x.mono (by omega)) rfl hs
  · exact frameOK_halt (by simp only [pstep, hc, htk])
      ((rules_tokCase_bad _ _ s K (by simp [htk])).elim fun S' x => ⟨S', x.mono (by omega)⟩)

/-! ## More costs -/

/-- `N` plus the big constant is at most the square. -/
theorem rules_lin_le_chB (N : Nat) : N + 1114113 ≤ chB N := Nat.le_mul_of_pos_left _ (by omega)

/-- One comparison of numbers at most `N`. -/
theorem rules_cmp_le_chB {N a b : Nat} (ha : a ≤ N) (hb : b ≤ N) : (a + b + 1) * (2 * a + 6) ≤ 4 * chB N := by
  have hm := Nat.mul_le_mul (show a + b + 1 ≤ 2 * (N + 1114113) by omega)
    (show 2 * a + 6 ≤ 2 * (N + 1114113) by omega)
  rw [Nat.mul_assoc, Nat.mul_left_comm (N + 1114113), ← Nat.mul_assoc] at hm
  exact hm

/-- Reading a string of at most `N` tokens. -/
theorem rules_strCost_le {N L : Nat} (hL : L ≤ N) : strCost L ≤ 20 * rulesFcB N := by
  have hc := charCost_mono hL
  have hc' := charCost_eq N
  have hP := rules_lin_le_chB N
  have hX : charCost L + 6 * L + 30 ≤ 20 * chB N := by omega
  have hm := Nat.mul_le_mul (show L + 1 ≤ N + 1114113 by omega) hX
  have key : ∀ P : Nat, P * (20 * (P * P)) = 20 * (P * P * P) := fun P => by
    rw [Nat.mul_left_comm]; congr 1; exact (Nat.mul_assoc _ _ _).symm
  have e : (N + 1114113) * (20 * chB N) = 20 * rulesFcB N := key (N + 1114113)
  rw [e] at hm
  unfold strCost; exact hm

/-! ## Moving and copying stacks -/

theorem rules_encItems_length (l : List MItem) : (encItems l).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [encItems, List.flatMap_cons, List.length_append] at ih ⊢; rw [ih]; simp [encItem]; omega

theorem rules_set_scratch (t : PSt) (i : Fin NK) (h : 18 ≤ i.val) : (enc t).set i [] = enc t := by
  have e := Lists.set_get_self (enc t) i
  rwa [enc_scratch t i h] at e

theorem rules_enc_with_bodies (s : PSt) (v : List (List MItem)) :
    enc { s with bodies := v } = ((enc s).set 10 (encBodies v)).set 11 [v.length] :=
  enc_set₂ (k := 10) (k' := 11) (by omega) (by omega) rfl

/-- Move all of `OUT` onto `dst`, keeping the order, through the scratch stack `tmp`. -/
def rulesMoveOutP (tmp dst : Fin NK) (h₁ : OUT ≠ tmp) (h₂ : tmp ≠ dst) : NProg NK :=
  .seq (nmvAll OUT tmp h₁) (nmvAll tmp dst h₂)

theorem rules_moveOut_runs (t : PSt) (tmp dst : Fin NK) (h₁ : OUT ≠ tmp) (h₂ : tmp ≠ dst) (htmp : 18 ≤ tmp.val)
    (hdo : dst ≠ OUT) :
    NRuns (rulesMoveOutP tmp dst h₁ h₂) (enc t) (((enc t).set OUT []).set dst (enc t dst ++ encItems t.out.reverse))
      (24 * t.out.length + 2) := by
  have hT : enc t tmp = [] := enc_scratch t tmp htmp
  have x₁ := nruns_mvAll OUT tmp h₁ (enc t)
  rw [hT, List.nil_append] at x₁
  have x₂ := nruns_mvAll tmp dst h₂ (((enc t).set tmp (enc t OUT).reverse).set OUT [])
  have e : (((((enc t).set tmp (enc t OUT).reverse).set OUT []).set dst
      ((((enc t).set tmp (enc t OUT).reverse).set OUT []) dst ++
        ((((enc t).set tmp (enc t OUT).reverse).set OUT []) tmp).reverse)).set tmp []) =
      ((enc t).set OUT []).set dst (enc t dst ++ encItems t.out.reverse) := by
    have hdt : dst ≠ tmp := Ne.symm h₂
    funext x
    by_cases hx : x = tmp
    · rw [hx, Lists.set_same, Lists.set_ne _ _ h₂, Lists.set_ne _ _ (Ne.symm h₁), hT]
    · by_cases hy : x = dst
      · rw [hy, Lists.set_ne _ _ hdt, Lists.set_same, Lists.set_same, Lists.set_ne _ _ hdo, Lists.set_ne _ _ hdt,
          Lists.set_ne _ _ (Ne.symm h₁), Lists.set_same, List.reverse_reverse, enc_out]
      · simp [Lists.set, hx, hy]
  rw [e] at x₂
  have hl : ((((enc t).set tmp (enc t OUT).reverse).set OUT []) tmp).length = 4 * t.out.length := by
    rw [Lists.set_ne _ _ (Ne.symm h₁), Lists.set_same, List.length_reverse, enc_out, rules_encItems_length,
      List.length_reverse]
  have hl' : (enc t OUT).length = 4 * t.out.length := by
    rw [enc_out, rules_encItems_length, List.length_reverse]
  rw [hl] at x₂
  rw [hl'] at x₁
  exact (x₁.seq x₂).mono (by omega)

/-- Copy `src` onto `dst`, keeping the order and `src`, through the scratch stack `tmp`. -/
def rulesCopyP (src dst tmp : Fin NK) (h₁ : src ≠ tmp) (h₂ : tmp ≠ src) (h₃ : tmp ≠ dst) : NProg NK :=
  .seq (nmvAll src tmp h₁) (.loop tmp .nonempty (.seq (.prim (.dup tmp src h₂)) (nmv tmp dst h₃)))

theorem rules_copy_runs (src dst tmp : Fin NK) (h₁ : src ≠ tmp) (h₂ : tmp ≠ src) (h₃ : tmp ≠ dst) (h₄ : src ≠ dst)
    (S : Lists NK) (ht : S tmp = []) :
    NRuns (rulesCopyP src dst tmp h₁ h₂ h₃) S (S.set dst (S dst ++ S src)) (7 * (S src).length + 2) := by
  have x₁ := nruns_mvAll src tmp h₁ S
  rw [ht, List.nil_append] at x₁
  let F : Nat → Lists NK := fun m =>
    ((S.set tmp ((S src).drop m).reverse).set src ((S src).take m)).set dst (S dst ++ (S src).take m)
  have hFt : ∀ m, F m tmp = ((S src).drop m).reverse := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ h₃, Lists.set_ne _ _ h₂, Lists.set_same]
  have hFs : ∀ m, F m src = (S src).take m := fun m => by
    simp only [F]; rw [Lists.set_ne _ _ h₄, Lists.set_same]
  have hFd : ∀ m, F m dst = S dst ++ (S src).take m := fun m => by simp only [F, Lists.set_same]
  have h0 : (S.set tmp (S src).reverse).set src [] = F 0 := by
    funext x
    simp only [F, List.drop_zero, List.take_zero, List.append_nil, Lists.set]
    by_cases hx : x = dst
    · subst hx; simp [Ne.symm h₄, Ne.symm h₃]
    · simp [hx]
  have hn : F (S src).length = S.set dst (S dst ++ S src) := by
    funext x
    simp only [F, List.drop_length, List.take_length, List.reverse_nil, Lists.set]
    by_cases hx : x = dst
    · simp [hx]
    · by_cases hy : x = src
      · subst hy; simp [hx]
      · by_cases hz : x = tmp
        · subst hz; simp [hx, hy, ht]
        · simp [hx, hy, hz]
  have hl := nruns_family_const (i := tmp) (c := .nonempty) (p := .seq (.prim (.dup tmp src h₂)) (nmv tmp dst h₃))
    F (S src).length 3
    (fun m hm => by
      rw [hFt]; exact eval_nonempty_ne (by simp; omega))
    (by rw [hFt]; simp)
    (fun m hm => by
      have hd : (S src).drop m = (S src)[m] :: (S src).drop (m + 1) := List.drop_eq_getElem_cons hm
      have hFt' : F m tmp = ((S src).drop (m + 1)).reverse ++ [(S src)[m]] := by rw [hFt, hd, List.reverse_cons]
      have d₁ := nruns_dup tmp src h₂ (F m) hFt'
      have d₂ := nruns_mv tmp dst h₃ ((F m).set src (F m src ++ [(S src)[m]]))
        (l := ((S src).drop (m + 1)).reverse) (v := (S src)[m]) (by rw [Lists.set_ne _ _ h₂, hFt'])
      have e : ((((F m).set src (F m src ++ [(S src)[m]])).set dst
          (((F m).set src (F m src ++ [(S src)[m]])) dst ++ [(S src)[m]])).set tmp ((S src).drop (m + 1)).reverse)
          = F (m + 1) := by
        have ht' : (S src).take (m + 1) = (S src).take m ++ [(S src)[m]] := List.take_succ_eq_append_getElem hm
        rw [Lists.set_ne _ _ (Ne.symm h₄), hFs, hFd]
        funext x
        simp only [F, ht', Lists.set, List.append_assoc]
        by_cases hx : x = tmp
        · subst hx; simp [h₂, h₃]
        · by_cases hy : x = dst
          · subst hy; simp [Ne.symm h₃]
          · by_cases hz : x = src
            · subst hz; simp [hx, hy]
            · simp [hx, hy, hz]
      rw [e] at d₂
      exact (d₁.seq d₂).mono (by omega))
  rw [← h0, hn] at hl
  exact (x₁.seq hl).mono (by omega)

/-! ## Frame `17`: record a body -/

/-- Append the body: drop the checked rule type (`24`) and the body's type, move `OUT` onto `BOD`, end the body by
`13`, count it, and go back to `16`. -/
def rulesAppendBodyP : NProg NK :=
  .seq (.prim (.pop 24)) (.seq (.prim (.pop TY)) (.seq (rulesMoveOutP 25 BOD (by decide) (by decide))
    (.seq (npushC BOD 13) (.seq (.prim (.inc NB)) (npushC CTL 16)))))

theorem rules_appendBody_runs (s : PSt) (K r : List Nat) (σ v : Nat) (hty : s.ty = σ :: r) :
    NRuns rulesAppendBodyP ((enc { s with ctl := K }).set 24 [v])
      (enc { s with ctl := 16 :: K, ty := r, bodies := s.bodies ++ [s.out.reverse], out := [] })
      (24 * s.out.length + 40) := by
  let t : PSt := { s with ctl := K }
  have z₀ := nruns_pop 24 ((enc t).set 24 [v]) (l := []) (v := v) (Lists.set_same _ _ _)
  rw [Lists.set_set_u, rules_set_scratch t 24 (by decide)] at z₀
  have z₁ := nruns_pop TY (enc t) (l := r.reverse) (v := σ) (by rw [enc_ty_K, hty, List.reverse_cons])
  rw [← enc_with_ty t r] at z₁
  let t₁ : PSt := { t with ty := r }
  have z₂ := rules_moveOut_runs t₁ 25 BOD (by decide) (by decide) (by decide) (by decide)
  have e₂ : (enc t₁).set OUT [] = enc { t₁ with out := [] } := by rw [enc_with_out t₁ []]; rfl
  rw [e₂] at z₂
  let t₂ : PSt := { t₁ with out := [] }
  let B := encBodies s.bodies ++ encItems s.out.reverse
  have hB : enc t₁ BOD ++ encItems t₁.out.reverse = B := rfl
  rw [hB] at z₂
  have z₃ := nruns_pushC BOD ((enc t₂).set BOD B) 13
  rw [Lists.set_same, Lists.set_set_u] at z₃
  have z₄ := nruns_inc NB ((enc t₂).set BOD (B ++ [13])) (l := []) (v := s.bodies.length)
    (by rw [Lists.set_ne _ _ (by decide)]; rfl)
  have z₅ := nruns_pushC CTL (((enc t₂).set BOD (B ++ [13])).set NB ([] ++ [s.bodies.length + 1])) 16
  have e : (((enc t₂).set BOD (B ++ [13])).set NB ([] ++ [s.bodies.length + 1])).set CTL
      ((((enc t₂).set BOD (B ++ [13])).set NB ([] ++ [s.bodies.length + 1])) CTL ++ [16]) =
      enc { s with ctl := 16 :: K, ty := r, bodies := s.bodies ++ [s.out.reverse], out := [] } := by
    rw [show enc { s with ctl := 16 :: K, ty := r, bodies := s.bodies ++ [s.out.reverse], out := [] } =
      enc { ({ t₂ with bodies := s.bodies ++ [s.out.reverse] } : PSt) with ctl := 16 :: K } from rfl,
      enc_with_ctl { t₂ with bodies := s.bodies ++ [s.out.reverse] } (16 :: K),
      rules_enc_with_bodies t₂ (s.bodies ++ [s.out.reverse])]
    have hb : encBodies (s.bodies ++ [s.out.reverse]) = B ++ [13] := by simp [B, encBodies]
    rw [hb, Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]
    simp [t₂, t₁, t, enc_ctl]
  rw [e] at z₅
  have hl : t₁.out.length = s.out.length := rfl
  exact (z₀.seq (z₁.seq (z₂.seq (z₃.seq (z₄.seq z₅))))).mono (by omega)

/-- Push the rule type number `bodies.length` (entry of `RTs`) on `24`. -/
def rulesPeekP : NProg NK := .seq (.prim (.dup NB 22 (by decide))) (peekAt RTs 23 22 24 (by decide) (by decide))

theorem rules_peek_runs (t : PSt) (hk : t.bodies.length < t.rt.length) :
    NRuns rulesPeekP (enc t) ((enc t).set 24 [t.rt[t.bodies.length]]) (6 * t.rt.length + 4 * t.bodies.length + 7) := by
  have y₁ := nruns_dup NB 22 (by decide) (enc t) (l := []) (v := t.bodies.length) rfl
  rw [enc_scratch t 22 (by decide), List.nil_append] at y₁
  have hR : ((enc t).set 22 [t.bodies.length]) RTs = t.rt := by rw [Lists.set_ne _ _ (by decide)]; rfl
  have y₂ := nruns_peekAt RTs 23 22 24 (by decide) (by decide) (by decide) ((enc t).set 22 [t.bodies.length])
    (by rw [Lists.set_ne _ _ (by decide)]; exact enc_scratch t 23 (by decide)) (lc := []) (k := t.bodies.length)
    (by rw [Lists.set_same]; rfl) (by rw [hR]; exact hk)
  have e : ((((enc t).set 22 [t.bodies.length]).set 22 []).set 24
      (((enc t).set 22 [t.bodies.length]) 24 ++ [(((enc t).set 22 [t.bodies.length]) RTs)[t.bodies.length]'(by rw [hR]; exact hk)])) =
      (enc t).set 24 [t.rt[t.bodies.length]] := by
    rw [Lists.set_set_u, rules_set_scratch t 22 (by decide)]
    congr 1
  rw [e, hR] at y₂
  exact (y₁.seq y₂).mono (by omega)

/-- Check the type of the body against its rule type, then append the body. -/
def rulesCheckBodyP : NProg NK :=
  .seq rulesPeekP (.seq (cmpTop 24 TY 18 19 20 21 (by decide) (by decide))
    (caseTop 21 [.halt false, rulesAppendBodyP, .halt false] (.halt false)))

/-- The type on top of `TY` must be the rule type of the next body (`bodies.length < rt.length`). -/
def frame17P : NProg NK :=
  .ite TY .nonempty (.seq (cmpTop NB NRT 18 19 20 21 (by decide) (by decide))
    (caseTop 21 [rulesCheckBodyP, .halt false, .halt false] (.halt false))) (.halt false)

theorem frame17_frame (s : PSt) (K : List Nat) (hc : s.ctl = 17 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame17P s K (frameCost N) := by
  have hT := rules_const_le_frameCost N 30 (by omega)
  have hbN : s.bodies.length ≤ N := by unfold tsize at hN; omega
  have hrN : s.rt.length ≤ N := by unfold tsize at hN; omega
  have hoN : s.out.length ≤ N := by unfold tsize at hN; omega
  have htN : s.tt.length ≤ N := by unfold tsize at hN; omega
  have hP := rules_lin_le_chB N
  have hF := rules_chB_le_fcB N
  have hFC := rulesFrameCost_eq N
  have hc₁ := rules_cmp_le_chB hbN hrN
  rcases hty : s.ty with _ | ⟨σ, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  have hσ : σ ≤ s.tt.length := hi.ty σ (by rw [hty]; simp)
  let S := enc { s with ctl := K }
  have hTYne : NTest.nonempty.eval (S TY) = true := by
    simp only [S]; rw [enc_ty_K, hty, List.reverse_cons]; simp
  have x₁ := nruns_cmpTop NB NRT 18 19 20 21 (by decide) (by decide) (by decide) S (li := []) (lj := [])
    (a := s.bodies.length) (b := s.rt.length) rfl rfl
  have hres : (S.set 21 (S 21 ++ [cmpRes s.bodies.length s.rt.length])) 21 =
      S 21 ++ [cmpRes s.bodies.length s.rt.length] := Lists.set_same _ _ _
  by_cases hk : s.bodies.length < s.rt.length
  · rw [cmpRes_lt hk] at x₁ hres
    have hv : s.rt[s.bodies.length]? = some s.rt[s.bodies.length] := List.getElem?_eq_getElem hk
    have y₁ := rules_peek_runs { s with ctl := K } hk
    have hl₁ : ({ s with ctl := K } : PSt).rt.length = s.rt.length := rfl
    have hl₂ : ({ s with ctl := K } : PSt).bodies.length = s.bodies.length := rfl
    have hvN : s.rt[s.bodies.length] ≤ s.tt.length := hi.rt _ (List.getElem_mem hk)
    have hc₂ := rules_cmp_le_chB (Nat.le_trans hvN htN) (Nat.le_trans hσ htN)
    let S₂ := S.set 24 [s.rt[s.bodies.length]]
    have y₂ := nruns_cmpTop 24 TY 18 19 20 21 (by decide) (by decide) (by decide) S₂ (li := [])
      (lj := r.reverse) (a := s.rt[s.bodies.length]) (b := σ) (Lists.set_same _ _ _)
      (by simp only [S₂, S]; rw [Lists.set_ne _ _ (by decide), enc_ty_K, hty, List.reverse_cons])
    have hres₂ : (S₂.set 21 (S₂ 21 ++ [cmpRes s.rt[s.bodies.length] σ])) 21 =
        S₂ 21 ++ [cmpRes s.rt[s.bodies.length] σ] := Lists.set_same _ _ _
    by_cases hvσ : s.rt[s.bodies.length] = σ
    · have he : pstep s = { s with ctl := 16 :: K, ty := r, bodies := s.bodies ++ [s.out.reverse], out := [] } := by
        simp only [pstep, hc, hty, hv, hvσ, if_true]
      have hr1 : cmpRes s.rt[s.bodies.length] σ = 1 := by rw [hvσ]; exact cmpRes_eq _
      rw [hr1] at y₂ hres₂
      have z := rules_appendBody_runs s K r σ s.rt[s.bodies.length] hty
      have y₃ := caseTop_runs (21 : Fin NK) [.halt false, rulesAppendBodyP, .halt false] (.halt false) 1 (by simp)
        _ _ hres₂ _ _ (by rw [Lists.set_set_u, Lists.set_get_self]; exact z)
      have x₂ := caseTop_runs (21 : Fin NK) [rulesCheckBodyP, .halt false, .halt false] (.halt false) 0 (by simp)
        _ _ hres _ _ (by rw [Lists.set_set_u, Lists.set_get_self]; exact y₁.seq (y₂.seq y₃))
      exact frameOK_run he (((x₁.seq x₂).iteT hTYne).mono (by omega)) rfl hs
    · have he : pstep s = s.fail := by
        simp only [pstep, hc, hty, hv, Option.some.injEq, hvσ, if_false]
      have y₃ : ∃ S', NHalts (caseTop (21 : Fin NK) [.halt false, rulesAppendBodyP, .halt false] (.halt false))
          (S₂.set 21 (S₂ 21 ++ [cmpRes s.rt[s.bodies.length] σ])) false S' 8 := by
        rcases Nat.lt_or_gt_of_ne hvσ with h | h
        · rw [cmpRes_lt h] at hres₂ ⊢
          exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 0 (by simp) _ _ hres₂ false _ 1
            (nhalts_halt false _)).mono (by omega)⟩
        · rw [cmpRes_gt h] at hres₂ ⊢
          exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 2 (by simp) _ _ hres₂ false _ 1
            (nhalts_halt false _)).mono (by omega)⟩
      obtain ⟨S', y₃⟩ := y₃
      have x₂ := caseTop_halts (21 : Fin NK) [rulesCheckBodyP, .halt false, .halt false] (.halt false) 0 (by simp)
        _ _ hres false _ _ (by rw [Lists.set_set_u, Lists.set_get_self]; exact y₁.seqH (y₂.seqH y₃))
      exact frameOK_halt he ⟨S', ((x₁.seqH x₂).iteT hTYne).mono (by omega)⟩
  · have hn : s.rt[s.bodies.length]? = none := List.getElem?_eq_none (by omega)
    have he : pstep s = s.fail := by simp only [pstep, hc, hty, hn, reduceCtorEq, if_false]
    have x₂ : ∃ S', NHalts (caseTop (21 : Fin NK) [rulesCheckBodyP, .halt false, .halt false] (.halt false))
        (S.set 21 (S 21 ++ [cmpRes s.bodies.length s.rt.length])) false S' 8 := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hk) with h | h
      · rw [cmpRes_gt h] at hres ⊢
        exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 2 (by simp) _ _ hres false _ 1
          (nhalts_halt false _)).mono (by omega)⟩
      · rw [← h, cmpRes_eq] at hres ⊢
        exact ⟨_, (caseTop_halts (21 : Fin NK) _ (.halt false) 1 (by simp) _ _ hres false _ 1
          (nhalts_halt false _)).mono (by omega)⟩
    obtain ⟨S', x₂⟩ := x₂
    exact frameOK_halt he ⟨S', ((x₁.seqH x₂).iteT hTYne).mono (by omega)⟩

/-! ## Frame `18`: the start and the string -/

/-- Pop the start's type, clear `XS` and `STA`, and copy the tokens to `26`. -/
def rulesFrame18PrefixP : NProg NK :=
  .seq (.prim (.pop TY)) (.seq (nclr XS) (.seq (nclr STA) (rulesCopyP TK 26 27 (by decide) (by decide) (by decide))))

/-- The start must be a parser. Clear `XS` and `STA`, read the string from a copy (`26`) of the tokens into `XS`,
check that nothing follows, and move `OUT` onto `STA`. The tokens stay as they are, as in `pstep`. -/
def frame18P : NProg NK :=
  .ite TY .zero (.seq rulesFrame18PrefixP
      (.seq (parseStrP 26 18 19 20 21 22 23 (by decide) (by decide) (strSink 18 XS (by decide) false))
        (.ite 26 .empty (rulesMoveOutP 24 STA (by decide) (by decide)) (.halt false)))) (.halt false)

/-- The stacks after popping the start's type, clearing `XS` and `STA`, and copying the tokens to `26`. -/
theorem rules_frame18_prefix (s : PSt) (K r : List Nat) (hty : s.ty = 0 :: r) :
    NRuns rulesFrame18PrefixP (enc { s with ctl := K })
      ((enc { s with ctl := K, ty := r, x := [], start := [] }).set 26 s.tk.reverse)
      (2 * s.x.length + 8 * s.start.length + 7 * s.tk.length + 6) := by
  let t : PSt := { s with ctl := K }
  have a₁ := nruns_pop TY (enc t) (l := r.reverse) (v := 0) (by rw [enc_ty_K, hty, List.reverse_cons])
  rw [← enc_with_ty t r] at a₁
  let t₁ : PSt := { t with ty := r }
  have a₂ := nruns_clr XS (enc t₁)
  rw [← enc_with_x t₁ [], show enc t₁ XS = s.x from rfl] at a₂
  let t₂ : PSt := { t₁ with x := [] }
  have a₃ := nruns_clr STA (enc t₂)
  have e₃ : (enc t₂).set STA [] = enc { t₂ with start := [] } := by rw [enc_with_start t₂ []]; rfl
  rw [e₃, show enc t₂ STA = encItems s.start from rfl, rules_encItems_length] at a₃
  let t₃ : PSt := { t₂ with start := [] }
  have a₄ := rules_copy_runs TK 26 27 (by decide) (by decide) (by decide) (by decide) (enc t₃)
    (enc_scratch t₃ 27 (by decide))
  rw [enc_scratch t₃ 26 (by decide), List.nil_append, show enc t₃ TK = s.tk.reverse from rfl,
    List.length_reverse] at a₄
  exact (a₁.seq (a₂.seq (a₃.seq a₄))).mono (by omega)

theorem frame18_frame (s : PSt) (K : List Nat) (hc : s.ctl = 18 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame18P s K (frameCost N) := by
  have hT := rules_const_le_frameCost N 30 (by omega)
  have hkN : s.tk.length ≤ N := by omega
  have hoN : s.out.length ≤ N := by unfold tsize at hN; omega
  have hxN : s.x.length ≤ N := by unfold tsize at hN; omega
  have hsN : s.start.length ≤ N := by unfold tsize at hN; omega
  have hP := rules_lin_le_chB N
  have hF := rules_chB_le_fcB N
  have hFC := rulesFrameCost_eq N
  have hstr := rules_strCost_le hkN
  -- the type on top must be `0`
  rcases hty : s.ty with _ | ⟨_ | v, r⟩
  · exact frameOK_halt (by simp only [pstep, hc, hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  rotate_left
  · exact frameOK_halt (by simp only [pstep, hc, hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty, List.reverse_cons]; simp)).mono (by omega)⟩
  have hTY0 : NTest.zero.eval ((enc { s with ctl := K }) TY) = true := by
    rw [enc_ty_K, hty, List.reverse_cons]; simp
  have a := rules_frame18_prefix s K r hty
  let t₃ : PSt := { s with ctl := K, ty := r, x := [], start := [] }
  let W := (enc t₃).set 26 s.tk.reverse
  have hW : W 26 = s.tk.reverse := Lists.set_same _ _ _
  rcases hp : Shallot.MacroPeg.Flat.parseStr s.tk.length s.tk with _ | ⟨cs, _ | ⟨w, r'⟩⟩
  · have he : pstep s = s.fail := by simp only [pstep, hc, hty, hp]
    obtain ⟨S', b⟩ := parseStrP_fail 26 18 19 20 21 22 23 XS (by decide) (by decide) (by decide) false (by decide) W
      hW (Nat.le_refl _) hp
    exact frameOK_halt he ⟨S', ((a.seqH b.seq).iteT hTY0).mono (by omega)⟩
  · have he : pstep s =
        { s with ctl := K, ty := r, start := s.out.reverse, out := [], x := cs.map Char.toNat } := by
      simp only [pstep, hc, hty, hp]
    have b := parseStrP_ok 26 18 19 20 21 22 23 XS (by decide) (by decide) (by decide) false (by decide) W hW hp
    have eb : (W.set 26 ([] : List Nat).reverse).set XS (W XS ++ cs.map (fun ch => ch.toNat + cond false 1 0)) =
        enc { t₃ with x := cs.map Char.toNat } := by
      rw [enc_with_x t₃ (cs.map Char.toNat), List.reverse_nil, Lists.set_set_u, rules_set_scratch t₃ 26 (by decide)]
      have hx : W XS = [] := by show ((enc t₃).set 26 s.tk.reverse) XS = []; rw [Lists.set_ne _ _ (by decide)]; rfl
      rw [hx]; simp [cond]
    rw [eb] at b
    let t₄ : PSt := { t₃ with x := cs.map Char.toNat }
    have c := rules_moveOut_runs t₄ 24 STA (by decide) (by decide) (by decide) (by decide)
    have ec : ((enc t₄).set OUT []).set STA (enc t₄ STA ++ encItems t₄.out.reverse) =
        enc { s with ctl := K, ty := r, start := s.out.reverse, out := [], x := cs.map Char.toNat } := by
      rw [show enc { s with ctl := K, ty := r, start := s.out.reverse, out := [], x := cs.map Char.toNat } =
        enc { ({ t₄ with out := [] } : PSt) with start := s.out.reverse } from rfl,
        enc_with_start { t₄ with out := [] } s.out.reverse, enc_with_out t₄ []]
      rfl
    rw [ec] at c
    have h26 : NTest.empty.eval ((enc t₄) 26) = true := by rw [enc_scratch t₄ 26 (by decide)]; rfl
    have hl : t₄.out.length = s.out.length := rfl
    exact frameOK_run he (((a.seq (b.seq (c.iteT h26))).iteT hTY0).mono (by omega)) rfl hs
  · have he : pstep s = s.fail := by simp only [pstep, hc, hty, hp]
    have b := parseStrP_ok 26 18 19 20 21 22 23 XS (by decide) (by decide) (by decide) false (by decide) W hW hp
    have h26 : NTest.empty.eval (((W.set 26 (w :: r').reverse).set XS
        (W XS ++ cs.map (fun ch => ch.toNat + cond false 1 0))) 26) = false := by
      rw [Lists.set_ne _ _ (by decide), Lists.set_same, List.reverse_cons]; simp [NTest.eval]
    exact frameOK_halt he ⟨_, ((a.seqH (b.seqH ((nhalts_halt false _).iteF h26))).iteT hTY0).mono (by omega)⟩

end Shallot.MacroPeg.Mach
