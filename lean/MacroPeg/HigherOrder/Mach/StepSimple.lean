import MacroPeg.HigherOrder.Mach.Inv
import MacroPeg.HigherOrder.Mach.Intern
import MacroPeg.HigherOrder.Mach.TokChar

/-!
# One step of the reading machine on stacks: the simple frames

The stacks of a reading state (`enc`) have names (`TK`, `CTL`, …). The program of a frame `k` starts with `k`
popped from `CTL`, that is from `enc { s with ctl := K }`, and ends in `enc (pstep s)`, or stops rejecting where
`pstep` fails.

This file: the frames that only look at the top of `TY` and push frames (`2`, `4`, `10`, `12`), and the frames that
finish an operator (`3`, `5`, `6`, `7`).
-/

namespace Shallot.MacroPeg.Mach

open Complexity

/-! ## Names of the stacks -/

abbrev TK : Fin NK := 1
abbrev CTL : Fin NK := 2
abbrev TY : Fin NK := 3
abbrev OUT : Fin NK := 4
abbrev CUR : Fin NK := 5
abbrev TTs : Fin NK := 6
abbrev CTs : Fin NK := 7
abbrev LTs : Fin NK := 8
abbrev RTs : Fin NK := 9
abbrev BOD : Fin NK := 10
abbrev NB : Fin NK := 11
abbrev STA : Fin NK := 12
abbrev XS : Fin NK := 13
abbrev NTT : Fin NK := 14
abbrev NCT : Fin NK := 15
abbrev NLT : Fin NK := 16
abbrev NRT : Fin NK := 17

/-! ## Pushing frames -/

/-- Push the frames `a` then `b` (so `b` is on top). -/
def push2 (a b : Nat) : NProg NK := .seq (npushC CTL a) (npushC CTL b)

theorem enc_ctl_snoc (s : PSt) (K : List Nat) (v : Nat) :
    enc { s with ctl := v :: K } = (enc { s with ctl := K }).set CTL (K.reverse ++ [v]) := by
  have h₁ := enc_with_ctl s (v :: K)
  have h₂ := enc_with_ctl s K
  rw [h₁, h₂, Lists.set_set_u]; simp

theorem push2_runs (s : PSt) (K : List Nat) (a b : Nat) :
    NRuns (push2 a b) (enc { s with ctl := K }) (enc { s with ctl := b :: a :: K }) (a + b + 2) := by
  have x₁ := nruns_pushC CTL (enc { s with ctl := K }) a
  have x₂ := nruns_pushC CTL ((enc { s with ctl := K }).set CTL ((enc { s with ctl := K }) CTL ++ [a])) b
  rw [Lists.set_same, Lists.set_set_u] at x₂
  have e : (enc { s with ctl := K }).set CTL ((enc { s with ctl := K }) CTL ++ [a] ++ [b]) =
      enc { s with ctl := b :: a :: K } := by
    have h₁ := enc_with_ctl s (b :: a :: K)
    have h₂ := enc_with_ctl s K
    rw [h₁, h₂, Lists.set_same, Lists.set_set_u]; simp
  rw [e] at x₂
  exact (x₁.seq x₂).mono (by omega)

/-- A bound on the steps of any frame program, for states with at most `N` tokens and table entries. -/
def frameCost (N : Nat) : Nat := 100 * ((N + 1114113) * (N + 1114113) * (N + 1114113))

/-! ## What a frame program does -/

/-- The program `p` of a frame does what `pstep` does from `s`, whose control stack has had its frame popped
(leaving `K`), within `T` steps. -/
def FrameOK (p : NProg NK) (s : PSt) (K : List Nat) (T : Nat) : Prop :=
  ((pstep s).ok = true → NRuns p (enc { s with ctl := K }) (enc (pstep s)) T) ∧
    ((pstep s).ok = false → ∃ S', NHalts p (enc { s with ctl := K }) false S' T)

/-- The program `p` of a token of an expression does what `readExpr` does from `s`, whose token has been popped
(leaving `r`) and whose frame `0` has been popped (leaving `K`), within `T` steps. -/
def TokOK (p : NProg NK) (s : PSt) (K r : List Nat) (T : Nat) : Prop :=
  ((readExpr s K).ok = true → NRuns p (enc { s with ctl := K, tk := r }) (enc (readExpr s K)) T) ∧
    ((readExpr s K).ok = false → ∃ S', NHalts p (enc { s with ctl := K, tk := r }) false S' T)

theorem frameOK_run {p : NProg NK} {s : PSt} {K : List Nat} {T : Nat} {s' : PSt} (he : pstep s = s')
    (h : NRuns p (enc { s with ctl := K }) (enc s') T) (hok : s'.ok = s.ok) (hs : s.ok = true) : FrameOK p s K T :=
  ⟨fun _ => he ▸ h, fun hf => by rw [he, hok, hs] at hf; cases hf⟩

theorem frameOK_halt {p : NProg NK} {s : PSt} {K : List Nat} {T : Nat} (he : pstep s = s.fail)
    (h : ∃ S', NHalts p (enc { s with ctl := K }) false S' T) : FrameOK p s K T :=
  ⟨fun ht => absurd ht (by rw [he]; simp [PSt.fail]), fun _ => h⟩

theorem enc_ty_K (s : PSt) (K : List Nat) : (enc { s with ctl := K }) TY = s.ty.reverse := rfl

/-! ## Frames that push frames -/

/-- After a parser operand of `seq` (`a = 3`) or `alt` (`a = 5`): check it is a parser, then read the second. -/
def pushIfP (a : Nat) : NProg NK := .ite TY .zero (push2 a 0) (.halt false)

theorem pushIfP_frame (s : PSt) (K : List Nat) (a : Nat) (hs : s.ok = true)
    (hok : ∀ r, s.ty = 0 :: r → pstep s = { s with ctl := 0 :: a :: K })
    (hno : (∀ r, s.ty ≠ 0 :: r) → pstep s = s.fail) :
    FrameOK (pushIfP a) s K (a + 3) := by
  rcases hty : s.ty with _ | ⟨_ | v, r⟩
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · exact frameOK_run (hok r hty) (((push2_runs s K a 0).iteT (by rw [enc_ty_K, hty]; simp)).mono (by omega)) rfl hs
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; simp)).mono (by omega)⟩

/-- Frames `10` and `12`: push two frames. -/
theorem push2_frame (s : PSt) (K : List Nat) (a b : Nat) (hs : s.ok = true)
    (he : pstep s = { s with ctl := b :: a :: K }) : FrameOK (push2 a b) s K (a + b + 2) :=
  frameOK_run he (push2_runs s K a b) rfl hs

theorem eval_zero_last (l : List Nat) (a : Nat) : NTest.zero.eval (l ++ [a, 0]) = true := by
  rw [show l ++ [a, 0] = (l ++ [a]) ++ [0] by simp]; exact eval_zero_zero _

/-! ## Emitting an operator -/

/-- Emit the item `⟨tag, 0, 0, cur⟩`. -/
def emitP (tag : Nat) : NProg NK :=
  .seq (npushC OUT tag) (.seq (.prim (.pushZ OUT)) (.seq (.prim (.pushZ OUT)) (.prim (.dup CUR OUT (by decide)))))

theorem emitP_runs (t : PSt) (tag : Nat) :
    NRuns (emitP tag) (enc t) (enc { t with out := ⟨tag, 0, 0, t.cur⟩ :: t.out }) (tag + 4) := by
  have x₁ := nruns_pushC OUT (enc t) tag
  have x₂ := nruns_pushZ OUT ((enc t).set OUT ((enc t) OUT ++ [tag]))
  rw [Lists.set_same, Lists.set_set_u] at x₂
  have x₃ := nruns_pushZ OUT ((enc t).set OUT ((enc t) OUT ++ [tag] ++ [0]))
  rw [Lists.set_same, Lists.set_set_u] at x₃
  have x₄ := nruns_dup CUR OUT (by decide) ((enc t).set OUT ((enc t) OUT ++ [tag] ++ [0] ++ [0])) (l := [])
    (v := t.cur) (by rw [Lists.set_ne _ _ (by decide)]; rfl)
  rw [Lists.set_same, Lists.set_set_u] at x₄
  have e : (enc t).set OUT ((enc t) OUT ++ [tag] ++ [0] ++ [0] ++ [t.cur]) =
      enc { t with out := ⟨tag, 0, 0, t.cur⟩ :: t.out } := by
    rw [enc_with_out t (⟨tag, 0, 0, t.cur⟩ :: t.out)]; congr 1; simp [enc_out, encItems, encItem]
  rw [e] at x₄
  exact (x₁.seq (x₂.seq (x₃.seq x₄))).mono (by omega)

/-- Finish `seq` (`5`) or `alt` (`6`): both operands are parsers. -/
def binP (tag : Nat) : NProg NK :=
  .ite TY .zero (.seq (.prim (.pop TY)) (.ite TY .zero (emitP tag) (.halt false))) (.halt false)

theorem binP_frame (s : PSt) (K : List Nat) (tag : Nat) (hs : s.ok = true)
    (hok : ∀ r, s.ty = 0 :: 0 :: r → pstep s = { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out })
    (hno : (∀ r, s.ty ≠ 0 :: 0 :: r) → pstep s = s.fail) :
    FrameOK (binP tag) s K (tag + 8) := by
  rcases hty : s.ty with _ | ⟨_ | v, r'⟩
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · rcases r' with _ | ⟨_ | w, r⟩
    · have x₁ := nruns_pop TY (enc { s with ctl := K }) (l := []) (v := 0) (by rw [enc_ty_K, hty]; rfl)
      exact frameOK_halt (hno (by simp [hty]))
        ⟨_, ((x₁.seqH ((nhalts_halt false _).iteF (by rw [Lists.set_same]; rfl))).iteT
          (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
    · have x₁ := nruns_pop TY (enc { s with ctl := K }) (l := (r.reverse ++ [0])) (v := 0)
        (by rw [enc_ty_K, hty]; simp)
      have e : (enc { s with ctl := K }).set TY (r.reverse ++ [0]) = enc { s with ctl := K, ty := 0 :: r } := by
        rw [enc_with_ty { s with ctl := K } (0 :: r), List.reverse_cons]
      rw [e] at x₁
      have x₂ := emitP_runs { s with ctl := K, ty := 0 :: r } tag
      exact frameOK_run (hok r hty)
        (((x₁.seq (x₂.iteT (by rw [enc_ty]; simp))).iteT (by rw [enc_ty_K, hty]; simp only [List.reverse_cons, List.append_assoc]; exact eval_zero_last _ _)).mono (by omega)) rfl hs
    · have x₁ := nruns_pop TY (enc { s with ctl := K }) (l := (r.reverse ++ [w + 1])) (v := 0)
        (by rw [enc_ty_K, hty]; simp)
      exact frameOK_halt (hno (by simp [hty]))
        ⟨_, ((x₁.seqH ((nhalts_halt false _).iteF (by rw [Lists.set_same]; simp))).iteT
          (by rw [enc_ty_K, hty]; simp only [List.reverse_cons, List.append_assoc]; exact eval_zero_last _ _)).mono
          (by omega)⟩
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; simp)).mono (by omega)⟩

/-- Finish `star` (`7`) or `!` (`8`): the operand is a parser. -/
def unP (tag : Nat) : NProg NK := .ite TY .zero (emitP tag) (.halt false)

theorem unP_frame (s : PSt) (K : List Nat) (tag : Nat) (hs : s.ok = true)
    (hok : ∀ r, s.ty = 0 :: r → pstep s = { s with ctl := K, out := ⟨tag, 0, 0, s.cur⟩ :: s.out })
    (hno : (∀ r, s.ty ≠ 0 :: r) → pstep s = s.fail) :
    FrameOK (unP tag) s K (tag + 5) := by
  rcases hty : s.ty with _ | ⟨_ | v, r⟩
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; rfl)).mono (by omega)⟩
  · exact frameOK_run (hok r hty) ((emitP_runs { s with ctl := K } tag).iteT (by rw [enc_ty_K, hty]; simp [NTest.eval])) rfl hs
  · exact frameOK_halt (hno (by simp [hty]))
      ⟨_, ((nhalts_halt false _).iteF (by rw [enc_ty_K, hty]; simp [NTest.eval])).mono (by omega)⟩

end Shallot.MacroPeg.Mach
