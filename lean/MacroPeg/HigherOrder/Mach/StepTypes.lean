import MacroPeg.HigherOrder.Mach.StepSimple

/-!
# One step of the reading machine on stacks: the frames on types

The frames that look at types: `8` (a lambda's binder type is read: enter the extended context), `9` (a lambda's
body is read: register the arrow and emit the lambda), `11` (an application's argument is read: check it against the
function's arrow and emit the application) and `13` (an arrow's two sides are read: register it).
-/

namespace Shallot.MacroPeg.Mach

set_option linter.unusedSimpArgs false

open Complexity

/-! ## Scratch stacks and registering an arrow -/

/-- Scratch stacks of the frames on types (all empty in `enc`). -/
abbrev TypesW : Fin NK := 18
abbrev TypesA : Fin NK := 19
abbrev TypesB : Fin NK := 20
abbrev TypesI : Fin NK := 21
abbrev TypesF : Fin NK := 22
abbrev TypesT : Fin NK := 23
abbrev TypesU : Fin NK := 24
abbrev TypesG : Fin NK := 25
abbrev TypesR : Fin NK := 26
abbrev TypesR2 : Fin NK := 27
abbrev TypesZ : Fin NK := 28
abbrev TypesC : Fin NK := 29
abbrev TypesJ : Fin NK := 30
abbrev TypesD : Fin NK := 31
abbrev TypesE : Fin NK := 32
abbrev TypesO : Fin NK := 33

/-! ## Small facts -/

/-- A stack with its top shown. -/
theorem types_rev_cons_snoc (a : Nat) (r : List Nat) : (a :: r).reverse = r.reverse ++ [a] := List.reverse_cons ..

/-- Every frame program here takes far fewer steps than `frameCost`. -/
theorem types_frameCost_big (N : Nat) : 1114113 ≤ frameCost N := by
  unfold frameCost
  have h₁ : 1114113 ≤ N + 1114113 := Nat.le_add_left _ _
  have h₂ : 1 * 1 ≤ (N + 1114113) * (N + 1114113) := Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_add_left _ _)
  have h₃ : 1 * 1 * 1114113 ≤ (N + 1114113) * (N + 1114113) * (N + 1114113) := Nat.mul_le_mul h₂ h₁
  exact Nat.le_trans h₃ (Nat.le_mul_of_pos_left _ (by decide))

/-- Evaluate stacks updated at named places. -/
syntax "types_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| types_simp) => `(tactic| simp [Lists.set, TK, CTL, TY, OUT, CUR, TTs, CTs, LTs, RTs, BOD, NB, STA, XS,
      NTT, NCT, NLT, NRT, encPairs, encItems, encItem, TypesW, TypesA, TypesB, TypesI, TypesF, TypesT, TypesU, TypesG, TypesR, TypesR2, TypesZ, TypesC,
      TypesJ, TypesD, TypesE, TypesO])
  | `(tactic| types_simp [$xs,*]) => `(tactic| simp [Lists.set, TK, CTL, TY, OUT, CUR, TTs, CTs, LTs, RTs, BOD, NB, STA,
      XS, NTT, NCT, NLT, NRT, encPairs, encItems, encItem, TypesW, TypesA, TypesB, TypesI, TypesF, TypesT, TypesU, TypesG, TypesR, TypesR2, TypesZ,
      TypesC, TypesJ, TypesD, TypesE, TypesO, $xs,*])

/-! ## Primitive moves with the stacks given -/

theorem types_dup_to (i j : Fin NK) (hij : i ≠ j) (S : Lists NK) {li lj : List Nat} {v : Nat} (hi : S i = li ++ [v])
    (hj : S j = lj) : NRuns (.prim (.dup i j hij)) S (S.set j (lj ++ [v])) 1 := by
  rw [← hj]; exact nruns_dup i j hij S hi

theorem types_mv_to (i j : Fin NK) (hij : i ≠ j) (S : Lists NK) {li lj : List Nat} {v : Nat} (hi : S i = li ++ [v])
    (hj : S j = lj) : NRuns (nmv i j hij) S ((S.set j (lj ++ [v])).set i li) 2 := by
  rw [← hj]; exact nruns_mv i j hij S hi

theorem types_pushC_to (i : Fin NK) (S : Lists NK) (c : Nat) {l : List Nat} (hi : S i = l) :
    NRuns (npushC i c) S (S.set i (l ++ [c])) (c + 1) := by
  rw [← hi]; exact nruns_pushC i S c

/-! ## Frame `8`: a lambda's binder type is read -/

/-- Push `cur` and the binder type `a` (moved from `TY`) as frame arguments, push the frames `9` and `0`, extend the
contexts by `(cur, a)` and enter the new context. -/
def frame8P : NProg NK :=
  .ite TY .nonempty
    (.seq (.prim (.dup CUR CTL (by decide))) (.seq (.prim (.dup TY CTL (by decide))) (.seq (push2 9 0)
      (.seq (.prim (.dup CUR CTs (by decide))) (.seq (nmv TY CTs (by decide)) (.seq (.prim (.inc NCT))
        (.seq (.prim (.pop CUR)) (.prim (.dup NCT CUR (by decide))))))))))
    (.halt false)

theorem types_pstep_eight {s : PSt} {K : List Nat} (hc : s.ctl = 8 :: K) {a : Nat} {r : List Nat} (hty : s.ty = a :: r) :
    pstep s = { s with
      ctl := 0 :: 9 :: a :: s.cur :: K
      ty := r
      ct := s.ct ++ [(s.cur, a)]
      cur := s.ct.length + 1 } := by
  simp only [pstep, hc]; rw [hty]

theorem types_pstep_eight_nil {s : PSt} {K : List Nat} (hc : s.ctl = 8 :: K) (hty : s.ty = []) : pstep s = s.fail := by
  simp only [pstep, hc]; rw [hty]

theorem frame8_frame (s : PSt) (K : List Nat) (hc : s.ctl = 8 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame8P s K (frameCost N) := by
  rcases hty : s.ty with _ | ⟨a, r⟩
  · exact frameOK_halt (types_pstep_eight_nil hc hty)
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by have := types_frameCost_big N; omega)⟩
  · -- move `cur` and `a` onto the control stack: the state of the frame arguments
    let E := enc { s with ctl := K }
    have x₁ := nruns_dup CUR CTL (by decide) E (l := []) (v := s.cur) rfl
    have x₂ := nruns_dup TY CTL (by decide) (E.set CTL (K.reverse ++ [s.cur])) (l := r.reverse) (v := a)
      (by rw [Lists.set_ne _ _ (by decide)]; show enc { s with ctl := K } TY = _; rw [enc_ty_K, hty, types_rev_cons_snoc])
    have e₂ : (E.set CTL (K.reverse ++ [s.cur])).set CTL ((E.set CTL (K.reverse ++ [s.cur])) CTL ++ [a]) =
        enc { s with ctl := a :: s.cur :: K } := by
      rw [Lists.set_same, Lists.set_set_u]
      show (enc { s with ctl := K }).set CTL _ = _
      rw [enc_with_ctl s K, enc_with_ctl s (a :: s.cur :: K)]
      exact (Lists.set_set_u _ _ _ _).trans (by simp)
    rw [e₂] at x₂
    have x₃ := push2_runs s (a :: s.cur :: K) 9 0
    -- extend the contexts and enter the new one
    let t : PSt := { s with ctl := 0 :: 9 :: a :: s.cur :: K }
    let T₀ := enc t
    let T₁ := T₀.set CTs (encPairs s.ct ++ [s.cur])
    have y₁ : NRuns _ T₀ T₁ 1 := nruns_dup CUR CTs (by decide) T₀ (l := []) (v := s.cur) rfl
    let T₂ := (T₀.set CTs (encPairs s.ct ++ [s.cur, a])).set TY r.reverse
    have y₂ : NRuns (nmv TY CTs (by decide)) T₁ T₂ 2 := by
      have := nruns_mv TY CTs (by decide) T₁ (l := r.reverse) (v := a)
        (by simp only [T₁, T₀, t]; rw [Lists.set_ne _ _ (by decide), enc_ty, hty, types_rev_cons_snoc])
      simpa [T₁, Lists.set_set_u] using this
    let T₃ := T₂.set NCT [s.ct.length + 1]
    have y₃ : NRuns _ T₂ T₃ 1 := nruns_inc NCT T₂ (l := []) (v := s.ct.length) (by
      simp only [T₂, T₀, t]; rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]; rfl)
    let T₄ := T₃.set CUR []
    have y₄ : NRuns _ T₃ T₄ 1 := nruns_pop CUR T₃ (l := []) (v := s.cur) (by
      simp only [T₃, T₂, T₀, t]
      rw [Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide), Lists.set_ne _ _ (by decide)]; rfl)
    have y₅ := nruns_dup NCT CUR (by decide) T₄ (l := []) (v := s.ct.length + 1)
      (by simp only [T₄, T₃]; rw [Lists.set_ne _ _ (by decide), Lists.set_same]; rfl)
    have e₅ : T₄.set CUR (T₄ CUR ++ [s.ct.length + 1]) = enc (pstep s) := by
      rw [types_pstep_eight hc hty]
      have k₁ := enc_with_ty t r
      have k₂ := enc_with_ct { t with ty := r } (s.ct ++ [(s.cur, a)])
      have k₃ := enc_with_cur { { t with ty := r } with ct := s.ct ++ [(s.cur, a)] } (s.ct.length + 1)
      rw [k₂, k₁] at k₃
      refine Eq.trans ?_ k₃.symm
      funext x
      simp only [T₄, T₃, T₂, T₁]
      by_cases h₁ : x = CUR
      · subst h₁; types_simp
      by_cases h₂ : x = NCT
      · subst h₂; types_simp
      by_cases h₃ : x = CTs
      · subst h₃; types_simp
      by_cases h₄ : x = TY
      · subst h₄; types_simp
      simp [Lists.set, h₁, h₂, h₃, h₄, T₀]
    rw [e₅] at y₅
    exact frameOK_run rfl (((x₁.seq (x₂.seq (x₃.seq (y₁.seq (y₂.seq (y₃.seq (y₄.seq y₅))))))).iteT
      (by show NTest.nonempty.eval (enc { s with ctl := K } TY) = true; rw [enc_ty_K, hty]; simp)).mono
      (by have := types_frameCost_big N; omega)) (by rw [types_pstep_eight hc hty]) hs

/-- Register the arrow `a ⇒ b` (`a` the top of `TypesA`, `b` the top of `TypesB`, both kept) in `TTs`/`NTT` and push its
number on `TY`. -/
def types_internP : NProg NK :=
  internP TTs NTT TypesW TypesA TypesB TY TypesI TypesF TypesT TypesU TypesG TypesR TypesR2 TypesZ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The entries of a well-formed table name smaller types. -/
theorem types_ttwf_bound {tt : List (Nat × Nat)} (hw : TTWF tt) : ∀ q ∈ tt, q.1 ≤ tt.length ∧ q.2 ≤ tt.length := by
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
  have := hw.2 k hk; omega

theorem types_intern_runs (S : Lists NK) {P : List (Nat × Nat)} {la lb ln : List Nat} {a b : Nat}
    (hP : S TTs = encPairs P) (hw : S TypesW = []) (ha : S TypesA = la ++ [a]) (hb : S TypesB = lb ++ [b])
    (hn : S NTT = ln ++ [P.length]) (hwf : TTWF P) (haB : a ≤ P.length) (hbB : b ≤ P.length) :
    NRuns types_internP S (((S.set TTs (encPairs (intern P a b).1)).set NTT (ln ++ [(intern P a b).1.length])).set TY
      (S TY ++ [(intern P a b).2])) (internCost P.length P.length) :=
  internP_runs TTs NTT TypesW TypesA TypesB TY TypesI TypesF TypesT TypesU TypesG TypesR TypesR2 TypesZ _ _ _ _ _ _ _ _ _ (by decide) S hP hw ha hb hn
    (types_ttwf_bound hwf) haB hbB

/-! ## Costs -/

theorem types_cost_aux (n X : Nat) (h : n + 100 ≤ X) :
    internCost n n + (2 * n + 1) * (2 * n + 6) + 100 * n + 1000 ≤ 100 * (X * X * X) := by
  have hA : (2 * n + 1) * (2 * n + 6) ≤ 4 * (X * X) := by
    have := Nat.mul_le_mul (show 2 * n + 1 ≤ 2 * X by omega) (show 2 * n + 6 ≤ 2 * X by omega)
    rw [Nat.mul_mul_mul_comm] at this; exact this
  have hB : (n + 1) * (2 * ((2 * n + 1) * (2 * n + 6)) + 92) ≤ X * (8 * (X * X) + 92) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hC : X * (8 * (X * X) + 92) = 8 * (X * X * X) + 92 * X := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm X 92]
  have hXX : X * 100 ≤ X * X := Nat.mul_le_mul_left X (by omega)
  have hXXX : X * X * 100 ≤ X * X * X := Nat.mul_le_mul_left (X * X) (by omega)
  have hE : 2 * ((2 * n + 1) * (2 * n + 6) + 20) + 22 + 30 = 2 * ((2 * n + 1) * (2 * n + 6)) + 92 := by omega
  unfold internCost internStepCost
  rw [hE]
  omega

/-- Every frame program on types takes at most `frameCost N` steps. -/
theorem types_cost_le {n N : Nat} (hn : n ≤ N) :
    internCost n n + (2 * n + 1) * (2 * n + 6) + 100 * n + 1000 ≤ frameCost N := by
  unfold frameCost; exact types_cost_aux n _ (by omega)

/-! ## Frame `13`: an arrow's two sides are read -/

/-- Move the right side `b` and the left side `a` off `TY`, register `a ⇒ b`, push its number. -/
def frame13P : NProg NK :=
  .ite TY .nonempty
    (.seq (nmv TY TypesB (by decide)) (.ite TY .nonempty
      (.seq (nmv TY TypesA (by decide)) (.seq types_internP (.seq (.prim (.pop TypesA)) (.prim (.pop TypesB)))))
      (.halt false)))
    (.halt false)

theorem types_pstep_thirteen {s : PSt} {K : List Nat} (hc : s.ctl = 13 :: K) {a b : Nat} {r : List Nat}
    (hty : s.ty = b :: a :: r) :
    pstep s = { s with ctl := K, ty := (intern s.tt a b).2 :: r, tt := (intern s.tt a b).1 } := by
  simp only [pstep, hc]; rw [hty]

theorem frame13_frame (s : PSt) (K : List Nat) (hc : s.ctl = 13 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame13P s K (frameCost N) := by
  have hcost := types_cost_le (n := s.tt.length) (N := N) (by unfold tsize at hN; omega)
  rcases hty : s.ty with _ | ⟨b, _ | ⟨a, r⟩⟩
  · exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · have x₁ := nruns_mv TY TypesB (by decide) (enc { s with ctl := K }) (l := []) (v := b) (by rw [enc_ty_K, hty]; rfl)
    exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((x₁.seqH ((nhalts_halt false _).iteF (by types_simp))).iteT (by rw [enc_ty_K, hty]; rfl)).mono
        (by omega)⟩
  · have ⟨hb, hr'⟩ := mem_tail_le hi hty
    have ha := hr' a List.mem_cons_self
    have k₁ := enc_with_tt { s with ctl := K } (intern s.tt a b).1
    have k₂ := enc_with_ty { { s with ctl := K } with tt := (intern s.tt a b).1 } ((intern s.tt a b).2 :: r)
    rw [k₁] at k₂
    refine frameOK_run rfl ?_ (by rw [types_pstep_thirteen hc hty]) hs
    rw [types_pstep_thirteen hc hty]
    refine Eq.subst (motive := fun X => NRuns frame13P _ X _) k₂.symm ?_
    have hTY : (enc { s with ctl := K }) TY = r.reverse ++ [a, b] := by rw [enc_ty_K, hty]; simp
    have hTT : (enc { s with ctl := K }) TTs = encPairs s.tt := rfl
    have hNTT : (enc { s with ctl := K }) NTT = [] ++ [s.tt.length] := rfl
    have hsc : ∀ i : Fin NK, 18 ≤ i.val → (enc { s with ctl := K }) i = [] := fun i h => enc_scratch _ i h
    generalize enc { s with ctl := K } = E at *
    have eA : E TypesA = [] := hsc TypesA (by decide)
    have eB : E TypesB = [] := hsc TypesB (by decide)
    have eW : E TypesW = [] := hsc TypesW (by decide)
    have x₁ := nruns_mv TY TypesB (by decide) E (l := r.reverse ++ [a]) (v := b) (by rw [hTY]; simp)
    rw [eB, List.nil_append] at x₁
    let S₁ := (E.set TypesB [b]).set TY (r.reverse ++ [a])
    have x₂ := nruns_mv TY TypesA (by decide) S₁ (l := r.reverse) (v := a) (by simp only [S₁]; types_simp)
    let S₂ := (S₁.set TypesA [a]).set TY r.reverse
    have x₂' : NRuns (nmv TY TypesA (by decide)) S₁ S₂ 2 := by
      have e : S₁ TypesA = [] := by simp only [S₁]; types_simp [eA]
      rw [e] at x₂; exact x₂
    let i := intern s.tt a b
    have x₃ := types_intern_runs S₂ (P := s.tt) (la := []) (lb := []) (ln := []) (a := a) (b := b)
      (by simp only [S₂, S₁]; types_simp [hTT]) (by simp only [S₂, S₁]; types_simp [eW]) (by simp only [S₂]; types_simp)
      (by simp only [S₂, S₁]; types_simp) (by simp only [S₂, S₁]; types_simp [hNTT]) hi.tt ha hb
    let S₃ := ((S₂.set TTs (encPairs i.1)).set NTT [i.1.length]).set TY (r.reverse ++ [i.2])
    have x₃' : NRuns types_internP S₂ S₃ (internCost s.tt.length s.tt.length) := by
      have e : S₂ TY = r.reverse := by simp only [S₂]; types_simp
      rw [e] at x₃; exact x₃
    have x₄ := nruns_pop TypesA S₃ (l := []) (v := a) (by simp only [S₃, S₂]; types_simp)
    have x₅ := nruns_pop TypesB (S₃.set TypesA []) (l := []) (v := b) (by simp only [S₃, S₂, S₁]; types_simp)
    have e : (S₃.set TypesA []).set TypesB [] =
        ((E.set TTs (encPairs i.1)).set NTT [i.1.length]).set TY (i.2 :: r).reverse := by
      funext x
      simp only [S₃, S₂, S₁]
      by_cases h₁ : x = TY
      · subst h₁; types_simp
      by_cases h₂ : x = TTs
      · subst h₂; types_simp
      by_cases h₃ : x = NTT
      · subst h₃; types_simp
      by_cases h₄ : x = TypesA
      · subst h₄; types_simp [eA]
      by_cases h₅ : x = TypesB
      · subst h₅; types_simp [eB]
      simp [Lists.set, h₁, h₂, h₃, h₄, h₅]
    rw [e] at x₅
    exact ((x₁.seq ((x₂'.seq (x₃'.seq (x₄.seq x₅))).iteT (by types_simp [NTest.eval]))).iteT
      (by rw [hTY]; simp [NTest.eval])).mono (by omega)

/-! ## Frame `9`: a lambda's body is read -/

/-- Take the frame arguments `a` (binder type) and `c` (outer context) off `CTL` and the body type `σ` off `TY`,
register `a ⇒ σ` and push its number, emit `⟨11, a, σ, c⟩`, and return to context `c`. -/
def frame9P : NProg NK :=
  .ite CTL .nonempty
    (.seq (nmv CTL TypesA (by decide)) (.ite CTL .nonempty
      (.ite TY .nonempty
        (.seq (nmv TY TypesB (by decide)) (.seq types_internP (.seq (npushC OUT 11) (.seq (.prim (.dup TypesA OUT (by decide)))
          (.seq (.prim (.dup TypesB OUT (by decide))) (.seq (.prim (.dup CTL OUT (by decide)))
            (.seq (.prim (.pop CUR)) (.seq (nmv CTL CUR (by decide))
              (.seq (.prim (.pop TypesA)) (.prim (.pop TypesB)))))))))))
        (.halt false))
      (.halt false)))
    (.halt false)

theorem types_pstep_nine {s : PSt} {a c : Nat} {K : List Nat} (hc : s.ctl = 9 :: a :: c :: K) {σ : Nat} {r : List Nat}
    (hty : s.ty = σ :: r) :
    pstep s = { s with
      ctl := K
      ty := (intern s.tt a σ).2 :: r
      tt := (intern s.tt a σ).1
      cur := c
      out := ⟨11, a, σ, c⟩ :: s.out } := by
  simp only [pstep, hc]; rw [hty]

theorem frame9_frame (s : PSt) (K : List Nat) (hc : s.ctl = 9 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame9P s K (frameCost N) := by
  have hcost := types_cost_le (n := s.tt.length) (N := N) (by unfold tsize at hN; omega)
  rcases K with _ | ⟨a, _ | ⟨c, K'⟩⟩
  · exact frameOK_halt (by simp only [pstep, hc])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ctl]; rfl)).mono (by omega)⟩
  · have x₁ := nruns_mv CTL TypesA (by decide) (enc { s with ctl := [a] }) (l := []) (v := a) (by rw [enc_ctl]; rfl)
    exact frameOK_halt (by simp only [pstep, hc])
      ⟨_, ((x₁.seqH ((nhalts_halt false _).iteF (by types_simp))).iteT (by rw [enc_ctl]; rfl)).mono (by omega)⟩
  have hk := hi.ctl; rw [hc] at hk; simp only [ctlOK] at hk
  have ha : a ≤ s.tt.length := hk.1
  rcases hty : s.ty with _ | ⟨σ, r⟩
  · have x₁ := nruns_mv CTL TypesA (by decide) (enc { s with ctl := a :: c :: K' }) (l := K'.reverse ++ [c]) (v := a)
      (by rw [enc_ctl]; simp)
    exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((x₁.seqH (((nhalts_halt false _).iteF (by types_simp [enc_ty, hty])).iteT
        (by types_simp [enc_ctl, NTest.eval]))).iteT (by rw [enc_ctl]; simp [NTest.eval])).mono (by omega)⟩
  have hσ : σ ≤ s.tt.length := (mem_tail_le hi hty).1
  let i := intern s.tt a σ
  -- the target, as stacks changed from the start
  let u : PSt := { s with ctl := a :: c :: K' }
  have k₁ := enc_with_ctl u K'
  have k₂ := enc_with_tt { u with ctl := K' } i.1
  have k₃ := enc_with_ty { { u with ctl := K' } with tt := i.1 } (i.2 :: r)
  have k₄ := enc_with_cur { { { u with ctl := K' } with tt := i.1 } with ty := i.2 :: r } c
  have k₅ := enc_with_out { { { { u with ctl := K' } with tt := i.1 } with ty := i.2 :: r } with cur := c }
    (⟨11, a, σ, c⟩ :: s.out)
  rw [k₄, k₃, k₂, k₁] at k₅
  refine frameOK_run rfl ?_ (by rw [types_pstep_nine hc hty]) hs
  rw [types_pstep_nine hc hty]
  refine Eq.subst (motive := fun X => NRuns frame9P _ X _) k₅.symm ?_
  have hCTL : (enc u) CTL = K'.reverse ++ [c, a] := by rw [enc_ctl]; simp [u]
  have hTY : (enc u) TY = r.reverse ++ [σ] := by show s.ty.reverse = _; rw [hty]; simp
  have hTT : (enc u) TTs = encPairs s.tt := rfl
  have hNTT : (enc u) NTT = [] ++ [s.tt.length] := rfl
  have hOUT : (enc u) OUT = encItems s.out.reverse := rfl
  have hCUR : (enc u) CUR = [] ++ [s.cur] := rfl
  have hsc : ∀ i : Fin NK, 18 ≤ i.val → (enc u) i = [] := fun i h => enc_scratch _ i h
  generalize enc u = E at *
  have eA : E TypesA = [] := hsc TypesA (by decide)
  have eB : E TypesB = [] := hsc TypesB (by decide)
  have eW : E TypesW = [] := hsc TypesW (by decide)
  let O := encItems s.out.reverse
  have x₁ := types_mv_to CTL TypesA (by decide) E (li := K'.reverse ++ [c]) (lj := []) (v := a) (by rw [hCTL]; simp) eA
  let S₁ := (E.set TypesA [a]).set CTL (K'.reverse ++ [c])
  have x₂ := types_mv_to TY TypesB (by decide) S₁ (li := r.reverse) (lj := []) (v := σ) (by simp only [S₁]; types_simp [hTY])
    (by simp only [S₁]; types_simp [eB])
  let S₂ := (S₁.set TypesB [σ]).set TY r.reverse
  have x₃ := types_intern_runs S₂ (P := s.tt) (la := []) (lb := []) (ln := []) (a := a) (b := σ)
    (by simp only [S₂, S₁]; types_simp [hTT]) (by simp only [S₂, S₁]; types_simp [eW]) (by simp only [S₂, S₁]; types_simp)
    (by simp only [S₂]; types_simp) (by simp only [S₂, S₁]; types_simp [hNTT]) hi.tt ha hσ
  let S₃ := ((S₂.set TTs (encPairs i.1)).set NTT [i.1.length]).set TY (r.reverse ++ [i.2])
  have x₃' : NRuns types_internP S₂ S₃ (internCost s.tt.length s.tt.length) := by
    have e : S₂ TY = r.reverse := by simp only [S₂]; types_simp
    rw [e] at x₃; exact x₃
  have x₄ := types_pushC_to OUT S₃ 11 (l := O) (by simp only [S₃, S₂, S₁]; types_simp [hOUT, O])
  have x₅ := types_dup_to TypesA OUT (by decide) (S₃.set OUT (O ++ [11])) (li := []) (lj := O ++ [11]) (v := a)
    (by simp only [S₃, S₂, S₁]; types_simp) (by types_simp)
  have x₆ := types_dup_to TypesB OUT (by decide) ((S₃.set OUT (O ++ [11])).set OUT (O ++ [11] ++ [a])) (li := [])
    (lj := O ++ [11] ++ [a]) (v := σ) (by simp only [S₃, S₂, S₁]; types_simp) (by types_simp)
  let S₆ := (((S₃.set OUT (O ++ [11])).set OUT (O ++ [11] ++ [a])).set OUT (O ++ [11] ++ [a] ++ [σ]))
  have x₇ := types_dup_to CTL OUT (by decide) S₆ (li := K'.reverse) (lj := O ++ [11] ++ [a] ++ [σ]) (v := c)
    (by simp only [S₆, S₃, S₂, S₁]; types_simp) (by simp only [S₆]; types_simp)
  let S₇ := S₆.set OUT (O ++ [11] ++ [a] ++ [σ] ++ [c])
  have x₈ := nruns_pop CUR S₇ (l := []) (v := s.cur) (by simp only [S₇, S₆, S₃, S₂, S₁]; types_simp [hCUR])
  have x₉ := types_mv_to CTL CUR (by decide) (S₇.set CUR []) (li := K'.reverse) (lj := []) (v := c)
    (by simp only [S₇, S₆, S₃, S₂, S₁]; types_simp) (by types_simp)
  let S₉ := ((S₇.set CUR []).set CUR ([] ++ [c])).set CTL K'.reverse
  have x₁₀ := nruns_pop TypesA S₉ (l := []) (v := a) (by simp only [S₉, S₇, S₆, S₃, S₂, S₁]; types_simp)
  have x₁₁ := nruns_pop TypesB (S₉.set TypesA []) (l := []) (v := σ) (by simp only [S₉, S₇, S₆, S₃, S₂, S₁]; types_simp)
  have e : (S₉.set TypesA []).set TypesB [] = (((((E.set CTL K'.reverse).set TTs (encPairs i.1)).set NTT [i.1.length]).set
      TY (i.2 :: r).reverse).set CUR [c]).set OUT (encItems (⟨11, a, σ, c⟩ :: s.out).reverse) := by
    funext x
    simp only [S₉, S₇, S₆, S₃, S₂, S₁]
    by_cases h₁ : x = TY
    · subst h₁; types_simp
    by_cases h₂ : x = TTs
    · subst h₂; types_simp
    by_cases h₃ : x = NTT
    · subst h₃; types_simp
    by_cases h₄ : x = TypesA
    · subst h₄; types_simp [eA]
    by_cases h₅ : x = TypesB
    · subst h₅; types_simp [eB]
    by_cases h₆ : x = CTL
    · subst h₆; types_simp
    by_cases h₇ : x = CUR
    · subst h₇; types_simp
    by_cases h₈ : x = OUT
    · subst h₈; types_simp [O]
    simp [Lists.set, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  rw [e] at x₁₁
  have inner := x₂.seq (x₃'.seq (x₄.seq (x₅.seq (x₆.seq (x₇.seq (x₈.seq (x₉.seq (x₁₀.seq x₁₁))))))))
  exact ((x₁.seq ((inner.iteT (i := TY) (c := .nonempty) (q := .halt false)
    (by simp only [S₁]; types_simp [hTY, NTest.eval])).iteT (i := CTL) (c := .nonempty) (q := .halt false)
    (by types_simp [NTest.eval]))).iteT (by rw [hCTL]; simp [NTest.eval])).mono (by omega)

/-! ## Frame `11`: an application's argument is read -/

/-- The application is well typed: move `β` to `TY`, emit `⟨12, α, β, cur⟩`, clear the scratch. -/
def types_app11P : NProg NK :=
  .seq (nmv TypesB TY (by decide)) (.seq (npushC OUT 12) (.seq (.prim (.dup TypesA OUT (by decide)))
    (.seq (.prim (.dup TY OUT (by decide))) (.seq (.prim (.dup CUR OUT (by decide)))
      (.seq (.prim (.pop TypesA)) (.seq (.prim (.pop TypesC)) (.prim (.pop TypesO))))))))

/-- With `α` on `TypesA`: move the function type `k + 1` off `TY`, read the arrow `tt[k] = (α', β)` (entries `2k`,
`2k+1` of `TTs`) onto `TypesO`, `TypesB`, and compare `α'` with `α` (result on `TypesR`). -/
def types_pre11P : NProg NK :=
  .seq (nmv TY TypesC (by decide)) (.seq (.prim (.dec TypesC))
    (.seq (entryP TTs TypesC TypesJ TypesD TypesE TypesO (by decide) (by decide) (by decide) (by decide) false)
    (.seq (entryP TTs TypesC TypesJ TypesD TypesE TypesB (by decide) (by decide) (by decide) (by decide) true)
    (cmpTop TypesO TypesA TypesT TypesU TypesG TypesR (by decide) (by decide)))))

/-- Move the argument type `α` off `TY`; the function type must be an arrow whose left side is `α`. -/
def frame11P : NProg NK :=
  .ite TY .nonempty
    (.seq (nmv TY TypesA (by decide)) (.ite TY .nonempty
      (.ite TY .zero (.halt false) (.seq types_pre11P (caseTop TypesR [.halt false, types_app11P, .halt false] (.halt false))))
      (.halt false)))
    (.halt false)

theorem types_pre11_runs (E : Lists NK) (P : List (Nat × Nat)) {la r : List Nat} {α k : Nat}
    (hTT : E TTs = encPairs P) (hTY : E TY = r.reverse ++ [k + 1]) (hA : E TypesA = la ++ [α]) (hC : E TypesC = [])
    (hE : E TypesE = []) (hO : E TypesO = []) (hB : E TypesB = []) (hR : E TypesR = []) (hkl : k < P.length) :
    NRuns types_pre11P E ((((((E.set TypesC [k + 1]).set TY r.reverse).set TypesC [k]).set TypesO [P[k].1]).set TypesB [P[k].2]).set
      TypesR [cmpRes P[k].1 α])
      (3 + 2 * (12 * P.length + 11 * k + 16) + ((P[k].1 + α + 1) * (2 * P[k].1 + 6) + 20)) := by
  have x₁ := types_mv_to TY TypesC (by decide) E (li := r.reverse) (lj := []) (v := k + 1) hTY hC
  let T₁ := (E.set TypesC [k + 1]).set TY r.reverse
  have x₂ : NRuns (.prim (.dec TypesC)) T₁ (T₁.set TypesC [k]) 1 := by
    have := nruns_dec TypesC T₁ (l := []) (v := k + 1) (by simp only [T₁]; types_simp)
    rw [Nat.add_sub_cancel, List.nil_append] at this; exact this
  let T₂ := T₁.set TypesC [k]
  have hT₂ : T₂ TTs = encPairs P := by simp only [T₂, T₁]; types_simp [hTT]
  have x₃ := entryP_runs TTs TypesC TypesJ TypesD TypesE TypesO (by decide) (by decide) (by decide) (by decide) (by decide) false
    (by decide) T₂ (lc := []) (c := k) (v := P[k].1) (by simp only [T₂]; types_simp)
    (by simp only [T₂, T₁]; types_simp [hE]) (by rw [hT₂]; simpa using encPairs_fst P k hkl)
  have hO₂ : T₂ TypesO = [] := by simp only [T₂, T₁]; types_simp [hO]
  rw [hT₂, hO₂, encPairs_length, List.nil_append] at x₃
  let T₃ := T₂.set TypesO [P[k].1]
  have hT₃ : T₃ TTs = encPairs P := by simp only [T₃, T₂, T₁]; types_simp [hTT]
  have x₄ := entryP_runs TTs TypesC TypesJ TypesD TypesE TypesB (by decide) (by decide) (by decide) (by decide) (by decide) true
    (by decide) T₃ (lc := []) (c := k) (v := P[k].2) (by simp only [T₃, T₂]; types_simp)
    (by simp only [T₃, T₂, T₁]; types_simp [hE]) (by rw [hT₃]; simpa using encPairs_snd P k hkl)
  have hB₃ : T₃ TypesB = [] := by simp only [T₃, T₂, T₁]; types_simp [hB]
  rw [hT₃, hB₃, encPairs_length, List.nil_append] at x₄
  let T₄ := T₃.set TypesB [P[k].2]
  have x₅ := nruns_cmpTop TypesO TypesA TypesT TypesU TypesG TypesR (by decide) (by decide) (by decide) T₄ (li := []) (lj := la)
    (a := P[k].1) (b := α) (by simp only [T₄, T₃]; types_simp) (by simp only [T₄, T₃, T₂, T₁]; types_simp [hA])
  have hR₄ : T₄ TypesR = [] := by simp only [T₄, T₃, T₂, T₁]; types_simp [hR]
  rw [hR₄, List.nil_append] at x₅
  exact (x₁.seq (x₂.seq (x₃.seq (x₄.seq x₅)))).mono (by omega)

theorem types_pstep_eleven {s : PSt} {K : List Nat} (hc : s.ctl = 11 :: K) {α k β : Nat} {r : List Nat}
    (hty : s.ty = α :: (k + 1) :: r) (hk : s.tt[k]? = some (α, β)) :
    pstep s = { s with ctl := K, ty := β :: r, out := ⟨12, α, β, s.cur⟩ :: s.out } := by
  simp only [pstep, hc]; rw [hty]; simp only [hk]; simp

theorem types_pstep_eleven_ne {s : PSt} {K : List Nat} (hc : s.ctl = 11 :: K) {α k α' β : Nat} {r : List Nat}
    (hty : s.ty = α :: (k + 1) :: r) (hk : s.tt[k]? = some (α', β)) (hne : α' ≠ α) : pstep s = s.fail := by
  simp only [pstep, hc]; rw [hty]; simp only [hk]; simp [hne]

theorem frame11_frame (s : PSt) (K : List Nat) (hc : s.ctl = 11 :: K) (hs : s.ok = true) (hi : MInv s) {N : Nat}
    (hN : s.tk.length + tsize s ≤ N) : FrameOK frame11P s K (frameCost N) := by
  have hcost := types_cost_le (n := s.tt.length) (N := N) (by unfold tsize at hN; omega)
  rcases hty : s.ty with _ | ⟨α, _ | ⟨_ | k, r⟩⟩
  · exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · have x₁ := nruns_mv TY TypesA (by decide) (enc { s with ctl := K }) (l := []) (v := α) (by rw [enc_ty_K, hty]; rfl)
    exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((x₁.seqH ((nhalts_halt false _).iteF (by types_simp))).iteT (by rw [enc_ty_K, hty]; rfl)).mono
        (by omega)⟩
  · have x₁ := nruns_mv TY TypesA (by decide) (enc { s with ctl := K }) (l := r.reverse ++ [0]) (v := α)
      (by rw [enc_ty_K, hty]; simp)
    exact frameOK_halt (by simp only [pstep, hc]; rw [hty])
      ⟨_, ((x₁.seqH (((nhalts_halt false _).iteT (by types_simp [NTest.eval])).iteT
        (by types_simp [NTest.eval]))).iteT (by rw [enc_ty_K, hty]; simp [NTest.eval])).mono (by omega)⟩
  -- the arrow `k` exists
  have hφ : k + 1 ≤ s.tt.length := (mem_tail_le hi hty).2 (k + 1) List.mem_cons_self
  have hα : α ≤ s.tt.length := (mem_tail_le hi hty).1
  have hkl : k < s.tt.length := by omega
  have hent := hi.tt.2 k hkl
  have hk : s.tt[k]? = some (s.tt[k].1, s.tt[k].2) := by rw [List.getElem?_eq_getElem hkl]
  have hcmpB : (s.tt[k].1 + α + 1) * (2 * s.tt[k].1 + 6) ≤ (2 * s.tt.length + 1) * (2 * s.tt.length + 6) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hTY : (enc { s with ctl := K }) TY = r.reverse ++ [k + 1, α] := by rw [enc_ty_K, hty]; simp
  have hTT : (enc { s with ctl := K }) TTs = encPairs s.tt := rfl
  have hOUT : (enc { s with ctl := K }) OUT = encItems s.out.reverse := rfl
  have hCUR : (enc { s with ctl := K }) CUR = [] ++ [s.cur] := rfl
  have hsc : ∀ i : Fin NK, 18 ≤ i.val → (enc { s with ctl := K }) i = [] := fun i h => enc_scratch _ i h
  by_cases he : s.tt[k].1 = α
  · -- a well-typed application
    have hp := types_pstep_eleven hc hty (β := s.tt[k].2) (by rw [hk, he])
    have k₁ := enc_with_ty { s with ctl := K } (s.tt[k].2 :: r)
    have k₂ := enc_with_out { { s with ctl := K } with ty := s.tt[k].2 :: r } (⟨12, α, s.tt[k].2, s.cur⟩ :: s.out)
    rw [k₁] at k₂
    refine frameOK_run hp ?_ rfl hs
    refine Eq.subst (motive := fun X => NRuns frame11P _ X _) k₂.symm ?_
    generalize enc { s with ctl := K } = E at *
    have x₁ := types_mv_to TY TypesA (by decide) E (li := r.reverse ++ [k + 1]) (lj := []) (v := α) (by rw [hTY]; simp)
      (hsc TypesA (by decide))
    let S₁ := (E.set TypesA [α]).set TY (r.reverse ++ [k + 1])
    have x₂ := types_pre11_runs S₁ s.tt (la := []) (r := r) (α := α) (k := k) (by simp only [S₁]; types_simp [hTT])
      (by simp only [S₁]; types_simp) (by simp only [S₁]; types_simp) (by simp only [S₁]; types_simp [hsc TypesC (by decide)])
      (by simp only [S₁]; types_simp [hsc TypesE (by decide)]) (by simp only [S₁]; types_simp [hsc TypesO (by decide)])
      (by simp only [S₁]; types_simp [hsc TypesB (by decide)]) (by simp only [S₁]; types_simp [hsc TypesR (by decide)]) hkl
    let S₆ := (((((S₁.set TypesC [k + 1]).set TY r.reverse).set TypesC [k]).set TypesO [s.tt[k].1]).set TypesB
      [s.tt[k].2]).set TypesR [cmpRes s.tt[k].1 α]
    have hc1 : cmpRes s.tt[k].1 α = 1 := cmpRes_one.2 he
    let O := encItems s.out.reverse
    let β := s.tt[k].2
    let S₇ := S₆.set TypesR []
    have y₁ := types_mv_to TypesB TY (by decide) S₇ (li := []) (lj := r.reverse) (v := β) (by simp only [S₇, S₆]; types_simp [β])
      (by simp only [S₇, S₆]; types_simp)
    let S₈ := (S₇.set TY (r.reverse ++ [β])).set TypesB []
    have y₂ := types_pushC_to OUT S₈ 12 (l := O) (by simp only [S₈, S₇, S₆, S₁]; types_simp [hOUT, O])
    have y₃ := types_dup_to TypesA OUT (by decide) (S₈.set OUT (O ++ [12])) (li := []) (lj := O ++ [12]) (v := α)
      (by simp only [S₈, S₇, S₆, S₁]; types_simp) (by types_simp)
    let S₉ := (S₈.set OUT (O ++ [12])).set OUT (O ++ [12] ++ [α])
    have y₄ := types_dup_to TY OUT (by decide) S₉ (li := r.reverse) (lj := O ++ [12] ++ [α]) (v := β)
      (by simp only [S₉, S₈]; types_simp) (by simp only [S₉]; types_simp)
    let S₁₀ := S₉.set OUT (O ++ [12] ++ [α] ++ [β])
    have y₅ := types_dup_to CUR OUT (by decide) S₁₀ (li := []) (lj := O ++ [12] ++ [α] ++ [β]) (v := s.cur)
      (by simp only [S₁₀, S₉, S₈, S₇, S₆, S₁]; types_simp [hCUR]) (by simp only [S₁₀]; types_simp)
    let S₁₁ := S₁₀.set OUT (O ++ [12] ++ [α] ++ [β] ++ [s.cur])
    have y₆ := nruns_pop TypesA S₁₁ (l := []) (v := α) (by simp only [S₁₁, S₁₀, S₉, S₈, S₇, S₆, S₁]; types_simp)
    have y₇ := nruns_pop TypesC (S₁₁.set TypesA []) (l := []) (v := k)
      (by simp only [S₁₁, S₁₀, S₉, S₈, S₇, S₆, S₁]; types_simp)
    have y₈ := nruns_pop TypesO ((S₁₁.set TypesA []).set TypesC []) (l := []) (v := s.tt[k].1)
      (by simp only [S₁₁, S₁₀, S₉, S₈, S₇, S₆, S₁]; types_simp)
    have e : (((S₁₁.set TypesA []).set TypesC []).set TypesO []) =
        (E.set TY (β :: r).reverse).set OUT (encItems (⟨12, α, β, s.cur⟩ :: s.out).reverse) := by
      funext x
      simp only [S₁₁, S₁₀, S₉, S₈, S₇, S₆, S₁]
      by_cases h₁ : x = TY
      · subst h₁; types_simp
      by_cases h₂ : x = OUT
      · subst h₂; types_simp [O]
      by_cases h₃ : x = TypesA
      · subst h₃; types_simp [hsc TypesA (by decide)]
      by_cases h₄ : x = TypesB
      · subst h₄; types_simp [hsc TypesB (by decide)]
      by_cases h₅ : x = TypesC
      · subst h₅; types_simp [hsc TypesC (by decide)]
      by_cases h₆ : x = TypesO
      · subst h₆; types_simp [hsc TypesO (by decide)]
      by_cases h₇ : x = TypesR
      · subst h₇; types_simp [hsc TypesR (by decide)]
      simp [Lists.set, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
    rw [e] at y₈
    have happ : NRuns types_app11P S₇ _ 21 := (y₁.seq (y₂.seq (y₃.seq (y₄.seq (y₅.seq (y₆.seq (y₇.seq y₈))))))).mono
      (by omega)
    have hcase := caseTop_runs TypesR [.halt false, types_app11P, .halt false] (.halt false) 1 (by decide) S₆ []
      (by simp only [S₆]; types_simp [hc1]) _ 21 happ
    exact ((x₁.seq (((x₂.seq hcase).iteF (by simp only [S₁]; types_simp [NTest.eval])).iteT
      (by types_simp [NTest.eval]))).iteT (by rw [hTY]; simp [NTest.eval])).mono (by omega)
  · -- the argument does not fit
    refine frameOK_halt (types_pstep_eleven_ne hc hty hk he) ?_
    generalize enc { s with ctl := K } = E at *
    have x₁ := types_mv_to TY TypesA (by decide) E (li := r.reverse ++ [k + 1]) (lj := []) (v := α) (by rw [hTY]; simp)
      (hsc TypesA (by decide))
    let S₁ := (E.set TypesA [α]).set TY (r.reverse ++ [k + 1])
    have x₂ := types_pre11_runs S₁ s.tt (la := []) (r := r) (α := α) (k := k) (by simp only [S₁]; types_simp [hTT])
      (by simp only [S₁]; types_simp) (by simp only [S₁]; types_simp) (by simp only [S₁]; types_simp [hsc TypesC (by decide)])
      (by simp only [S₁]; types_simp [hsc TypesE (by decide)]) (by simp only [S₁]; types_simp [hsc TypesO (by decide)])
      (by simp only [S₁]; types_simp [hsc TypesB (by decide)]) (by simp only [S₁]; types_simp [hsc TypesR (by decide)]) hkl
    let S₆ := (((((S₁.set TypesC [k + 1]).set TY r.reverse).set TypesC [k]).set TypesO [s.tt[k].1]).set TypesB
      [s.tt[k].2]).set TypesR [cmpRes s.tt[k].1 α]
    have hv : cmpRes s.tt[k].1 α = 0 ∨ cmpRes s.tt[k].1 α = 2 := by
      have h₁ := cmpRes_le s.tt[k].1 α
      have h₂ : cmpRes s.tt[k].1 α ≠ 1 := fun h => he (cmpRes_one.1 h)
      omega
    have hcase : NHalts (caseTop TypesR [.halt false, types_app11P, .halt false] (.halt false)) S₆ false (S₆.set TypesR []) 7 := by
      rcases hv with hv | hv
      · exact (caseTop_halts TypesR [.halt false, types_app11P, .halt false] (.halt false) 0 (by decide) S₆ []
          (by simp only [S₆]; types_simp [hv]) false _ 1 (nhalts_halt false _)).mono (by omega)
      · exact (caseTop_halts TypesR [.halt false, types_app11P, .halt false] (.halt false) 2 (by decide) S₆ []
          (by simp only [S₆]; types_simp [hv]) false _ 1 (nhalts_halt false _)).mono (by omega)
    exact ⟨_, ((x₁.seqH (((x₂.seqH hcase).iteF (by simp only [S₁]; types_simp [NTest.eval])).iteT
      (by types_simp [NTest.eval]))).iteT (by rw [hTY]; simp [NTest.eval])).mono (by omega)⟩

end Shallot.MacroPeg.Mach
