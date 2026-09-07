import PalPeg.ProgLangLib
import PalPeg.GSScanProg
import PalPeg.GSVerifierProg

/-!
# テープ本数の移送と `Prog` の合成 (`ProgLangSum`)

`PalPeg.ProgLang.Interp` の一般の**移送**（テープ添字の単射 `ι : Fin t₁ ↪ Fin t` に
沿って `t₁` 本テープの解釈を `t` 本テープへ持ち上げる）と、動作・条件識別子を
写す**再ラベリング**、およびその二つを組み合わせた**直和**を与える。

* `Interp.transport` / `exec_transport` … タスク 1 (1)-(2)。
* `Prog.map` / `exec_map` … 動作・条件識別子の再ラベリング（`GSVerifierProg.pmap` の一般化）。
* `Interp.sum` / `exec_sum_inl` / `exec_sum_inr` / `exec_sum_seq` … タスク 1 (3)（直和）。
* `run_transport` … タスク 1 (4)（`trace`/`applyTrace` の整合）。
* `exec_lift_reproduced` … タスク 1 (5)。`GSVerifierProg`（`GSVProg` 名前空間）の
  `exec_lift` の主張を、この一般の移送補題から系として再導出する（`GSVerifierProg.lean`
  は一切編集しない）。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ProgLang

open PegSeparation.RealTimeTM
open PalPeg.Program

/-! ## 1. テープ添字の単射に沿った射影 -/

variable {A C A₁ C₁ A₂ C₂ Terminal Γ : Type} {t₁ t₂ t : ℕ}

/-- `ι` の像への（部分）逆写像。像の外では `none`。 -/
noncomputable def proj (ι : Fin t₁ ↪ Fin t) (j : Fin t) : Option (Fin t₁) :=
  if h : ∃ i, ι i = j then some h.choose else none

@[simp] theorem proj_ι (ι : Fin t₁ ↪ Fin t) (i : Fin t₁) : proj ι (ι i) = some i := by
  unfold proj
  have h : ∃ k, ι k = ι i := ⟨i, rfl⟩
  rw [dif_pos h]
  congr 1
  exact ι.injective h.choose_spec

theorem proj_eq_none (ι : Fin t₁ ↪ Fin t) {j : Fin t} (h : ∀ i, ι i ≠ j) :
    proj ι j = none := by
  unfold proj
  rw [dif_neg]
  rintro ⟨i, hi⟩
  exact h i hi

theorem eq_ι_of_proj_eq_some {ι : Fin t₁ ↪ Fin t} {j : Fin t} {i : Fin t₁}
    (h : proj ι j = some i) : ι i = j := by
  by_cases hex : ∃ k, ι k = j
  · have heq : proj ι j = some hex.choose := by unfold proj; rw [dif_pos hex]
    rw [heq] at h
    have hii : hex.choose = i := by cases h; rfl
    rw [← hii]
    exact hex.choose_spec
  · exfalso
    have heq : proj ι j = none := by unfold proj; rw [dif_neg hex]
    rw [heq] at h
    exact absurd h (by simp)

/-! ## 2. テープ束・動作ベクトルの拡張 -/

/-- `t₁` 本のテープ束 `T` を、`ι` の像の外では `rest` に従うテープ束に拡張する。 -/
noncomputable def extend (ι : Fin t₁ ↪ Fin t) (T : Fin t₁ → STape Γ) (rest : Fin t → STape Γ) :
    Fin t → STape Γ :=
  fun j => match proj ι j with
    | some i => T i
    | none => rest j

@[simp] theorem extend_ι (ι : Fin t₁ ↪ Fin t) (T : Fin t₁ → STape Γ) (rest : Fin t → STape Γ)
    (i : Fin t₁) : extend ι T rest (ι i) = T i := by
  simp [extend]

theorem extend_of_proj_none {ι : Fin t₁ ↪ Fin t} {j : Fin t} (h : proj ι j = none)
    (T : Fin t₁ → STape Γ) (rest : Fin t → STape Γ) : extend ι T rest j = rest j := by
  simp [extend, h]

/-- `t₁` 本分の write+move ベクトル `w` を、`ι` の像の外では `rest` の読みを
書き戻して停留するベクトルへ拡張する。 -/
noncomputable def extendVec (ι : Fin t₁ ↪ Fin t) (rest : Fin t → STape Γ) (w : Fin t₁ → Γ × Move) :
    Fin t → Γ × Move :=
  fun j => match proj ι j with
    | some i => w i
    | none => ((rest j).focus, Move.stay)

@[simp] theorem extendVec_ι (ι : Fin t₁ ↪ Fin t) (rest : Fin t → STape Γ)
    (w : Fin t₁ → Γ × Move) (i : Fin t₁) : extendVec ι rest w (ι i) = w i := by
  simp [extendVec]

theorem extendVec_of_proj_none {ι : Fin t₁ ↪ Fin t} {j : Fin t} (h : proj ι j = none)
    (rest : Fin t → STape Γ) (w : Fin t₁ → Γ × Move) :
    extendVec ι rest w j = ((rest j).focus, Move.stay) := by
  simp [extendVec, h]

theorem applyAction_focus_stay' (blank : Γ) (T : STape Γ) :
    T.applyAction blank (T.focus, Move.stay) = T := rfl

theorem applyAction_extend (ι : Fin t₁ ↪ Fin t) (blank : Γ) (T : Fin t₁ → STape Γ)
    (rest : Fin t → STape Γ) (w : Fin t₁ → Γ × Move) :
    (fun j => (extend ι T rest j).applyAction blank (extendVec ι rest w j))
      = extend ι (fun i => (T i).applyAction blank (w i)) rest := by
  funext j
  rcases h : proj ι j with _ | i
  · rw [extend_of_proj_none h, extendVec_of_proj_none h, extend_of_proj_none h]
    exact applyAction_focus_stay' blank _
  · have hij : ι i = j := eq_ι_of_proj_eq_some h
    subst hij
    simp

theorem applyTrace_extend (ι : Fin t₁ ↪ Fin t) (blank : Γ) (rest : Fin t → STape Γ) :
    ∀ (l : List (Fin t₁ → Γ × Move)) (T : Fin t₁ → STape Γ),
      applyTrace blank (extend ι T rest) (l.map (extendVec ι rest))
        = extend ι (applyTrace blank T l) rest := by
  intro l
  induction l with
  | nil => intro T; rfl
  | cons w l ih =>
      intro T
      rw [List.map_cons, applyTrace_cons, applyTrace_cons, applyAction_extend, ih]

/-! ## 3. `Interp` の移送 -/

/-- **タスク 1 (1)**：`ι` に沿って `t₁` 本テープの解釈を `t` 本テープへ移送する。
`ι` の像の外の添字は「読んで停留」（恒等動作）になる。 -/
noncomputable def Interp.transport (ι : Fin t₁ ↪ Fin t) (I : Interp Terminal A C Γ t₁) :
    Interp Terminal A C Γ t where
  actOf a x σ := fun j =>
    match proj ι j with
    | some i => I.actOf a x (fun k => σ (ι k)) i
    | none => (σ j, Move.stay)
  condOf c σ := I.condOf c (fun k => σ (ι k))

theorem evalConds_transport (ι : Fin t₁ ↪ Fin t) (I : Interp Terminal A C Γ t₁)
    (T : Fin t₁ → STape Γ) (rest : Fin t → STape Γ) :
    evalConds (I.transport ι) (fun j => (extend ι T rest j).focus)
      = evalConds I (fun k => (T k).focus) := by
  funext c
  show (I.transport ι).condOf c (fun j => (extend ι T rest j).focus)
      = I.condOf c (fun k => (T k).focus)
  simp only [Interp.transport]
  congr 1
  funext k
  simp

/-- 動作解釈自体の移送：移送した解釈が算出する write+move ベクトルは、
`ι` の像の外の読みが `T` に依らず `rest` そのものに一致する限り、もとの解釈が
算出したベクトルの `extendVec` にちょうど等しい。 -/
theorem actOf_transport (ι : Fin t₁ ↪ Fin t) (I : Interp Terminal A C Γ t₁)
    (a : A) (x : Option Terminal) (T : Fin t₁ → STape Γ) (rest : Fin t → STape Γ) :
    (I.transport ι).actOf a x (fun j => (extend ι T rest j).focus)
      = extendVec ι rest (I.actOf a x (fun k => (T k).focus)) := by
  funext j
  rcases h : proj ι j with _ | i
  · simp only [Interp.transport, h, extendVec_of_proj_none h, extend_of_proj_none h]
  · have hij : ι i = j := eq_ι_of_proj_eq_some h
    subst hij
    rw [extendVec_ι]
    show (I.transport ι).actOf a x (fun j => (extend ι T rest j).focus) (ι i) = _
    simp only [Interp.transport, proj_ι]
    congr 1
    funext k
    simp

/-- 1 マイクロステップの移送。 -/
theorem microStep_transport (ι : Fin t₁ ↪ Fin t) (I : Interp Terminal A C Γ t₁)
    (blank : Γ) (a : Option Terminal) (rest : Fin t → STape Γ) (s : Stack A C)
    (T : Fin t₁ → STape Γ) :
    microStep (I.transport ι) blank a (s, extend ι T rest)
      = ((microStep I blank a (s, T)).1,
          extend ι (microStep I blank a (s, T)).2 rest) := by
  simp only [microStep]
  rw [evalConds_transport]
  rcases h : (stepStack (evalConds I (fun j => (T j).focus)) s).2 with _ | w
  · simp [h]
  · simp only [h]
    refine Prod.ext rfl ?_
    rw [actOf_transport, applyAction_extend]

/-! ## 4. `trace` / `runInputs` の移送（タスク 1 (4)） -/

theorem run_transport (ι : Fin t₁ ↪ Fin t) (I : Interp Terminal A C Γ t₁)
    (blank : Γ) (rest : Fin t → STape Γ) :
    ∀ (l : List (Option Terminal)) (s : Stack A C) (T : Fin t₁ → STape Γ),
      trace (I.transport ι) blank l (s, extend ι T rest)
          = (trace I blank l (s, T)).map (extendVec ι rest) ∧
        runInputs (I.transport ι) blank l (s, extend ι T rest)
          = ((runInputs I blank l (s, T)).1,
              extend ι (runInputs I blank l (s, T)).2 rest) := by
  intro l
  induction l with
  | nil => intro s T; exact ⟨rfl, rfl⟩
  | cons x l ih =>
      intro s T
      have hev : evalConds (I.transport ι) (fun j => (extend ι T rest j).focus)
          = evalConds I (fun k => (T k).focus) := evalConds_transport ι I T rest
      have hmicro := microStep_transport ι I blank x rest s T
      constructor
      · rw [trace_cons, trace_cons, hev]
        rcases h : (stepStack (evalConds I (fun j => (T j).focus)) s).2 with _ | w
        · simp only [h, List.nil_append, hmicro]
          exact (ih _ _).1
        · simp only [h, hmicro, actOf_transport, List.singleton_append, List.map_cons]
          exact congrArg (List.cons (extendVec ι rest (I.actOf w x fun j => (T j).focus)))
            (ih _ _).1
      · rw [runInputs_cons, runInputs_cons, hmicro]
        exact (ih _ _).2

/-! ## 5. `Exec` の移送（タスク 1 (2)） -/

/-- **タスク 1 (2)**：もとの `t₁` 本テープでの `Exec` は、`ι` に沿って移送した
`t` 本テープでの `Exec` になる。`ι` の像の外のテープ `rest` は一切変化しない。 -/
theorem exec_transport {I : Interp Terminal A C Γ t₁} {blank : Γ} {p : Prog A C}
    {T : Fin t₁ → STape Γ} {acts : List (Fin t₁ → Γ × Move)}
    (h : Exec I blank p T acts) (ι : Fin t₁ ↪ Fin t) (rest : Fin t → STape Γ) :
    Exec (I.transport ι) blank p (extend ι T rest) (acts.map (extendVec ι rest)) := by
  intro r l hl
  rw [List.length_map] at hl
  obtain ⟨htr, s', hrun, hseq⟩ := h r l hl
  obtain ⟨hs1, hs2⟩ := run_transport ι I blank rest l ([p] ++ r) T
  refine ⟨?_, s', ?_, ?_⟩
  · rw [hs1, htr]
  · rw [hs2, hrun, applyTrace_extend]
  · rw [applyTrace_extend]
    show stepStack (evalConds (I.transport ι)
        (fun j => (extend ι (applyTrace blank T acts) rest j).focus)) s'
      = stepStack (evalConds (I.transport ι)
        (fun j => (extend ι (applyTrace blank T acts) rest j).focus)) r
    rw [evalConds_transport]
    exact hseq

/-! ## 6. 動作・条件識別子の再ラベリング（`GSVerifierProg.pmap` の一般化） -/

/-- `Prog` の構文木を、動作識別子・条件識別子の写像 `fa`/`fc` に沿ってそのまま写す
（`GSVerifierProg.pmap` の一般化）。 -/
def Prog.map (fa : A₁ → A₂) (fc : C₁ → C₂) : Prog A₁ C₁ → Prog A₂ C₂
  | .skip => .skip
  | .act a => .act (fa a)
  | .seq p q => .seq (Prog.map fa fc p) (Prog.map fa fc q)
  | .ite c p q => .ite (fc c) (Prog.map fa fc p) (Prog.map fa fc q)
  | .loop c a b => .loop (fc c) (fa a) (Prog.map fa fc b)

/-- **制御スタックの模倣**（`GSVerifierProg.step_sim` の一般化、`fa`/`fc` に
単射性は不要）。 -/
theorem step_sim_map (fa : A₁ → A₂) (fc : C₁ → C₂) (ev1 : C₁ → Bool) (ev2 : C₂ → Bool)
    (h : ∀ c, ev2 (fc c) = ev1 c) :
    ∀ (s : Stack A₁ C₁) (r : Stack A₂ C₂),
      (∀ a, (stepStack ev1 s).2 = some a →
          stepStack ev2 (s.map (Prog.map fa fc) ++ r)
            = ((stepStack ev1 s).1.map (Prog.map fa fc) ++ r, some (fa a))) ∧
        ((stepStack ev1 s).2 = none →
          stepStack ev2 (s.map (Prog.map fa fc) ++ r) = stepStack ev2 r) := by
  intro s
  induction s using stepStack.induct (ev := ev1) with
  | case1 => intro r; exact ⟨by intro a ha; simp at ha, by intro _; simp⟩
  | case2 r' ih =>
      intro r
      have e : (Prog.skip :: r').map (Prog.map fa fc) ++ r
          = Prog.skip :: (r'.map (Prog.map fa fc) ++ r) := rfl
      rw [e, stepStack_skip, stepStack_skip]
      exact ih r
  | case3 a r' =>
      intro r
      have e : (Prog.act a :: r').map (Prog.map fa fc) ++ r
          = Prog.act (fa a) :: (r'.map (Prog.map fa fc) ++ r) := rfl
      rw [e, stepStack_act, stepStack_act]
      exact ⟨by intro b hb; cases hb; rfl, by intro hb; simp at hb⟩
  | case4 p q r' ih =>
      intro r
      have e : (Prog.seq p q :: r').map (Prog.map fa fc) ++ r
          = Prog.seq (Prog.map fa fc p) (Prog.map fa fc q) :: (r'.map (Prog.map fa fc) ++ r) :=
        rfl
      rw [e, stepStack_seq, stepStack_seq]
      have e2 : Prog.map fa fc p :: Prog.map fa fc q :: (r'.map (Prog.map fa fc) ++ r)
          = (p :: q :: r').map (Prog.map fa fc) ++ r := rfl
      rw [e2]
      exact ih r
  | case5 c p q r' ih =>
      intro r
      have e : (Prog.ite c p q :: r').map (Prog.map fa fc) ++ r
          = Prog.ite (fc c) (Prog.map fa fc p) (Prog.map fa fc q)
            :: (r'.map (Prog.map fa fc) ++ r) := rfl
      rw [e, stepStack_ite, stepStack_ite, h c]
      have e2 : (if ev1 c then Prog.map fa fc p else Prog.map fa fc q)
            :: (r'.map (Prog.map fa fc) ++ r)
          = ((if ev1 c then p else q) :: r').map (Prog.map fa fc) ++ r := by
        by_cases hc : ev1 c <;> simp [hc]
      rw [e2]
      exact ih r
  | case6 c a b r' hc =>
      intro r
      have e : (Prog.loop c a b :: r').map (Prog.map fa fc) ++ r
          = Prog.loop (fc c) (fa a) (Prog.map fa fc b) :: (r'.map (Prog.map fa fc) ++ r) := rfl
      rw [e, stepStack_loop, stepStack_loop, h c]
      simp only [if_pos hc]
      refine ⟨?_, ?_⟩
      · intro x hx
        have e2 : Prog.map fa fc b :: Prog.loop (fc c) (fa a) (Prog.map fa fc b)
              :: (r'.map (Prog.map fa fc) ++ r)
            = (b :: Prog.loop c a b :: r').map (Prog.map fa fc) ++ r := rfl
        rw [e2]
        cases hx
        rfl
      · intro hx; exact absurd hx (by simp)
  | case7 c a b r' hc ih =>
      intro r
      have e : (Prog.loop c a b :: r').map (Prog.map fa fc) ++ r
          = Prog.loop (fc c) (fa a) (Prog.map fa fc b) :: (r'.map (Prog.map fa fc) ++ r) := rfl
      rw [e, stepStack_loop, stepStack_loop, h c]
      simp only [if_neg hc]
      exact ih r

section Relabel

variable {I₁ : Interp Terminal A₁ C₁ Γ t} {I₂ : Interp Terminal A₂ C₂ Γ t}
  {fa : A₁ → A₂} {fc : C₁ → C₂}

theorem cond_agree_map (hcond : ∀ c σ, I₂.condOf (fc c) σ = I₁.condOf c σ)
    (c : C₁) (T : Fin t → STape Γ) :
    evalConds I₂ (fun j => (T j).focus) (fc c) = evalConds I₁ (fun j => (T j).focus) c :=
  hcond c _

/-- **実行の模倣**（`GSVerifierProg.run_sim` の一般化：テープ本数は変えず、
動作・条件識別子だけを写す）。 -/
theorem run_sim_map (hcond : ∀ c σ, I₂.condOf (fc c) σ = I₁.condOf c σ)
    (hact : ∀ a x σ, I₂.actOf (fa a) x σ = I₁.actOf a x σ) (blank : Γ) :
    ∀ (l : List (Option Terminal)) (s : Stack A₁ C₁) (T : Fin t → STape Γ)
      (r : Stack A₂ C₂),
      (trace I₁ blank l (s, T)).length = l.length →
      trace I₂ blank l (s.map (Prog.map fa fc) ++ r, T) = trace I₁ blank l (s, T) ∧
        runInputs I₂ blank l (s.map (Prog.map fa fc) ++ r, T)
          = ((runInputs I₁ blank l (s, T)).1.map (Prog.map fa fc) ++ r,
              (runInputs I₁ blank l (s, T)).2) := by
  intro l
  induction l with
  | nil => intro s T r _; exact ⟨rfl, rfl⟩
  | cons x l ih =>
    intro s T r hlen
    have hsome : ∃ w, (stepStack (evalConds I₁ (fun j => (T j).focus)) s).2 = some w := by
      cases hw : (stepStack (evalConds I₁ (fun j => (T j).focus)) s).2 with
      | some w => exact ⟨w, rfl⟩
      | none =>
        exfalso
        rw [trace_cons, hw] at hlen
        have hle := trace_length_le I₁ blank l
          (microStep I₁ blank x (s, T))
        simp only [List.nil_append, List.length_cons] at hlen
        omega
    obtain ⟨w, hw⟩ := hsome
    have hstep2 := (step_sim_map fa fc
        (evalConds I₁ (fun j => (T j).focus)) (evalConds I₂ (fun j => (T j).focus))
        (fun c => cond_agree_map hcond c T) s r).1 w hw
    have hact' := hact w x (fun j => (T j).focus)
    have hmicro : microStep I₂ blank x (s.map (Prog.map fa fc) ++ r, T)
        = ((microStep I₁ blank x (s, T)).1.map (Prog.map fa fc) ++ r,
            (microStep I₁ blank x (s, T)).2) := by
      simp only [microStep, hstep2, hw, hact']
    have hlen' : (trace I₁ blank l (microStep I₁ blank x (s, T))).length = l.length := by
      rw [trace_cons, hw] at hlen
      simp only [List.singleton_append, List.length_cons] at hlen
      omega
    obtain ⟨ih1, ih2⟩ := ih
      (microStep I₁ blank x (s, T)).1 (microStep I₁ blank x (s, T)).2 r hlen'
    simp only [Prod.mk.eta] at ih1 ih2
    refine ⟨?_, ?_⟩
    · rw [trace_cons, trace_cons, hstep2, hw, hmicro]
      simp only [hact', List.singleton_append, List.map_cons]
      exact congrArg _ ih1
    · rw [runInputs_cons, runInputs_cons, hmicro]
      exact ih2

/-- **タスク 1 の再ラベリング補題**：`fa`/`fc` に沿って `I₁` の解釈と `I₂` の解釈が
一致する限り、`I₁` 上の `Exec` は写した `Prog` の `I₂` 上の `Exec` になる
（テープ本数は不変）。 -/
theorem exec_map (hcond : ∀ c σ, I₂.condOf (fc c) σ = I₁.condOf c σ)
    (hact : ∀ a x σ, I₂.actOf (fa a) x σ = I₁.actOf a x σ)
    {blank : Γ} {p : Prog A₁ C₁} {T : Fin t → STape Γ} {acts : List (Fin t → Γ × Move)}
    (h : Exec I₁ blank p T acts) :
    Exec I₂ blank (Prog.map fa fc p) T acts := by
  intro r l hl
  obtain ⟨htr, s', hrun, hseq⟩ := h [] l hl
  rw [show ([p] ++ ([] : Stack A₁ C₁)) = [p] from rfl] at htr hrun
  have hprod : (trace I₁ blank l ([p], T)).length = l.length := by rw [htr, hl]
  obtain ⟨hs1, hs2⟩ := run_sim_map hcond hact blank l [p] T r hprod
  have hmapP : ([p] : Stack A₁ C₁).map (Prog.map fa fc) ++ r = [Prog.map fa fc p] ++ r := rfl
  rw [hmapP] at hs1 hs2
  rw [hrun] at hs2
  refine ⟨by rw [hs1, htr], s'.map (Prog.map fa fc) ++ r, ?_, ?_⟩
  · rw [hs2]
  · show stepStack (evalConds I₂ (fun j => ((applyTrace blank T acts) j).focus))
        (s'.map (Prog.map fa fc) ++ r)
      = stepStack (evalConds I₂ (fun j => ((applyTrace blank T acts) j).focus)) r
    refine (step_sim_map fa fc
        (evalConds I₁ (fun j => ((applyTrace blank T acts) j).focus))
        (evalConds I₂ (fun j => ((applyTrace blank T acts) j).focus))
        (fun c => cond_agree_map hcond c (applyTrace blank T acts)) s' r).2 ?_
    rw [hseq]
    simp

end Relabel

/-! ## 7. 直和（タスク 1 (3)） -/

section Sum

variable {I1 : Interp Terminal A₁ C₁ Γ t₁} {I2 : Interp Terminal A₂ C₂ Γ t₂}

/-- **タスク 1 (3)**：`t₁` 本テープの言語 `I1` と `t₂` 本テープの言語 `I2` の直和。
`Fin (t₁ + t₂)` 上で、動作・条件識別子は `A₁ ⊕ A₂` / `C₁ ⊕ C₂`。 -/
noncomputable def Interp.sum (I1 : Interp Terminal A₁ C₁ Γ t₁) (I2 : Interp Terminal A₂ C₂ Γ t₂) :
    Interp Terminal (A₁ ⊕ A₂) (C₁ ⊕ C₂) Γ (t₁ + t₂) where
  actOf
    | .inl a, x, σ => (I1.transport (Fin.castAddEmb t₂)).actOf a x σ
    | .inr a, x, σ => (I2.transport (Fin.natAddEmb t₁)).actOf a x σ
  condOf
    | .inl c, σ => (I1.transport (Fin.castAddEmb t₂)).condOf c σ
    | .inr c, σ => (I2.transport (Fin.natAddEmb t₁)).condOf c σ

theorem castAdd_ne_natAdd (i : Fin t₁) (k : Fin t₂) :
    Fin.castAdd t₂ i ≠ Fin.natAdd t₁ k := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem extend_castAdd_append (X Y : Fin t₁ → STape Γ) (Z : Fin t₂ → STape Γ) :
    extend (Fin.castAddEmb t₂) X (Fin.append Y Z) = Fin.append X Z := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · have hp : proj (Fin.castAddEmb t₂) (Fin.castAdd t₂ i) = some i := by
      rw [← Fin.castAddEmb_apply]; exact proj_ι _ i
    show extend (Fin.castAddEmb t₂) X (Fin.append Y Z) (Fin.castAdd t₂ i) = _
    simp only [extend, hp, Fin.append_left]
  · have hp : proj (Fin.castAddEmb t₂) (Fin.natAdd t₁ k) = none := by
      apply proj_eq_none
      intro i hcon
      rw [Fin.castAddEmb_apply] at hcon
      exact castAdd_ne_natAdd i k hcon
    show extend (Fin.castAddEmb t₂) X (Fin.append Y Z) (Fin.natAdd t₁ k) = _
    simp only [extend, hp, Fin.append_right]

theorem extend_natAdd_append (X : Fin t₂ → STape Γ) (Y : Fin t₁ → STape Γ)
    (Z : Fin t₂ → STape Γ) :
    extend (Fin.natAddEmb t₁) X (Fin.append Y Z) = Fin.append Y X := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · have hp : proj (Fin.natAddEmb t₁) (Fin.castAdd t₂ i) = none := by
      apply proj_eq_none
      intro k hcon
      rw [Fin.natAddEmb_apply] at hcon
      exact castAdd_ne_natAdd i k hcon.symm
    show extend (Fin.natAddEmb t₁) X (Fin.append Y Z) (Fin.castAdd t₂ i) = _
    simp only [extend, hp, Fin.append_left]
  · have hp : proj (Fin.natAddEmb t₁) (Fin.natAdd t₁ k) = some k := by
      rw [← Fin.natAddEmb_apply]; exact proj_ι _ k
    show extend (Fin.natAddEmb t₁) X (Fin.append Y Z) (Fin.natAdd t₁ k) = _
    simp only [extend, hp, Fin.append_right]

/-- 直和の左枝に住むプログラムの `Exec` の移送。 -/
theorem exec_sum_inl {blank : Γ} {p1 : Prog A₁ C₁} {T1 : Fin t₁ → STape Γ}
    {acts1 : List (Fin t₁ → Γ × Move)} (h1 : Exec I1 blank p1 T1 acts1)
    (rest : Fin (t₁ + t₂) → STape Γ) :
    Exec (Interp.sum I1 I2) blank (Prog.map (Sum.inl (β := A₂)) (Sum.inl (β := C₂)) p1)
      (extend (Fin.castAddEmb t₂) T1 rest)
      (acts1.map (extendVec (Fin.castAddEmb t₂) rest)) :=
  exec_map (fa := (Sum.inl : A₁ → A₁ ⊕ A₂)) (fc := (Sum.inl : C₁ → C₁ ⊕ C₂))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h1 (Fin.castAddEmb t₂) rest)

/-- 直和の右枝に住むプログラムの `Exec` の移送。 -/
theorem exec_sum_inr {blank : Γ} {p2 : Prog A₂ C₂} {T2 : Fin t₂ → STape Γ}
    {acts2 : List (Fin t₂ → Γ × Move)} (h2 : Exec I2 blank p2 T2 acts2)
    (rest : Fin (t₁ + t₂) → STape Γ) :
    Exec (Interp.sum I1 I2) blank (Prog.map (Sum.inr (α := A₁)) (Sum.inr (α := C₁)) p2)
      (extend (Fin.natAddEmb t₁) T2 rest)
      (acts2.map (extendVec (Fin.natAddEmb t₁) rest)) :=
  exec_map (fa := (Sum.inr : A₂ → A₁ ⊕ A₂)) (fc := (Sum.inr : C₂ → C₁ ⊕ C₂))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (exec_transport h2 (Fin.natAddEmb t₁) rest)

/-- **`seq`-合成**：左枝のプログラムを走らせてから右枝のプログラムを走らせるものを、
`t₁ + t₂` 本のテープ上の 1 個の `Exec` として合成する。 -/
theorem exec_sum_seq {blank : Γ} {p1 : Prog A₁ C₁} {T1 : Fin t₁ → STape Γ}
    {acts1 : List (Fin t₁ → Γ × Move)} {p2 : Prog A₂ C₂} {T2 : Fin t₂ → STape Γ}
    {acts2 : List (Fin t₂ → Γ × Move)} (h1 : Exec I1 blank p1 T1 acts1)
    (h2 : Exec I2 blank p2 T2 acts2) :
    Exec (Interp.sum I1 I2) blank
      (Prog.seq (Prog.map (Sum.inl (β := A₂)) (Sum.inl (β := C₂)) p1)
        (Prog.map (Sum.inr (α := A₁)) (Sum.inr (α := C₁)) p2))
      (Fin.append T1 T2)
      (acts1.map (extendVec (Fin.castAddEmb t₂) (Fin.append T1 T2)) ++
        acts2.map (extendVec (Fin.natAddEmb t₁) (Fin.append (applyTrace blank T1 acts1) T2))) := by
  have hL := exec_sum_inl (I2 := I2) h1 (Fin.append T1 T2)
  rw [extend_castAdd_append] at hL
  have step2 : extend (Fin.natAddEmb t₁) T2 (Fin.append (applyTrace blank T1 acts1) T2)
      = Fin.append (applyTrace blank T1 acts1) T2 :=
    extend_natAdd_append T2 (applyTrace blank T1 acts1) T2
  have hmid : applyTrace blank (extend (Fin.castAddEmb t₂) T1 (Fin.append T1 T2))
      (acts1.map (extendVec (Fin.castAddEmb t₂) (Fin.append T1 T2)))
      = extend (Fin.natAddEmb t₁) T2 (Fin.append (applyTrace blank T1 acts1) T2) := by
    rw [applyTrace_extend, extend_castAdd_append, step2]
  rw [extend_castAdd_append] at hmid
  have hR := exec_sum_inr (I1 := I1) h2 (Fin.append (applyTrace blank T1 acts1) T2)
  rw [← hmid] at hR
  exact exec_seq hL hR

end Sum

/-! ## 8. タスク 1 (5)：`GSVerifierProg.exec_lift` の再導出 -/

section GSVerifierCorollary

open PalPeg.GSProg (Act8 Cond8 I8)
open PalPeg.GSVProg (Act10 Cond10 I10 e8 tU tX fa fc pmap comb liftVec
  comb_e8 comb_tU comb_tX liftVec_e8 liftVec_tU liftVec_tX e8_ne_tU e8_ne_tX)

/-- `GSVerifierProg.e8 : Fin 8 → Fin 10` は単射なので、埋め込みとして扱える。 -/
noncomputable def e8Emb : Fin 8 ↪ Fin 10 :=
  ⟨e8, by
    intro i j h
    have hv := congrArg Fin.val h
    simp only [PalPeg.GSVProg.e8] at hv
    exact Fin.ext hv⟩

theorem e8Emb_apply (i : Fin 8) : e8Emb i = e8 i := rfl

theorem proj_e8Emb_tU : proj e8Emb tU = none := by
  apply proj_eq_none
  intro i hcon
  exact e8_ne_tU i hcon

theorem proj_e8Emb_tX : proj e8Emb tX = none := by
  apply proj_eq_none
  intro i hcon
  exact e8_ne_tX i hcon

theorem fin10_cases (j : Fin 10) :
    (∃ i : Fin 8, j = e8 i) ∨ j = tU ∨ j = tX := by
  by_cases h : j.val < 8
  · exact Or.inl ⟨⟨j.val, h⟩, by apply Fin.ext; rfl⟩
  · by_cases h8 : j.val = 8
    · exact Or.inr (Or.inl (Fin.ext h8))
    · exact Or.inr (Or.inr (by
        apply Fin.ext
        have := j.isLt
        simp only [PalPeg.GSVProg.tX]
        omega))

theorem extend_e8Emb_comb {sc : ℕ} (T : Fin 8 → STape (Fin sc)) (U X : STape (Fin sc)) :
    extend e8Emb T (comb (fun _ => U) U X) = comb T U X := by
  funext j
  rcases fin10_cases j with ⟨i, rfl⟩ | rfl | rfl
  · exact (extend_ι e8Emb T (comb (fun _ => U) U X) i).trans (comb_e8 T U X i).symm
  · rw [extend_of_proj_none proj_e8Emb_tU, comb_tU, comb_tU]
  · rw [extend_of_proj_none proj_e8Emb_tX, comb_tX, comb_tX]

theorem extendVec_e8Emb_comb {sc : ℕ} (U X : STape (Fin sc)) (w : Fin 8 → Fin sc × Move) :
    extendVec e8Emb (comb (fun _ => U) U X) w = liftVec U X w := by
  funext j
  rcases fin10_cases j with ⟨i, rfl⟩ | rfl | rfl
  · exact (extendVec_ι e8Emb (comb (fun _ => U) U X) w i).trans (liftVec_e8 U X w i).symm
  · rw [extendVec_of_proj_none proj_e8Emb_tU, comb_tU, liftVec_tU]
  · rw [extendVec_of_proj_none proj_e8Emb_tX, comb_tX, liftVec_tX]

theorem extendVec_e8Emb_comb' {sc : ℕ} (U X : STape (Fin sc)) :
    extendVec e8Emb (comb (fun _ => U) U X) = liftVec U X := by
  funext w
  exact extendVec_e8Emb_comb U X w

theorem progMap_eq_pmap : ∀ (P : Prog Act8 Cond8), Prog.map fa fc P = pmap P
  | .skip => rfl
  | .act _ => rfl
  | .seq p q => by
      show Prog.seq (Prog.map fa fc p) (Prog.map fa fc q) = pmap (.seq p q)
      rw [PalPeg.GSVProg.pmap, progMap_eq_pmap p, progMap_eq_pmap q]
  | .ite c p q => by
      show Prog.ite (fc c) (Prog.map fa fc p) (Prog.map fa fc q) = pmap (.ite c p q)
      rw [PalPeg.GSVProg.pmap, progMap_eq_pmap p, progMap_eq_pmap q]
  | .loop c a b => by
      show Prog.loop (fc c) (fa a) (Prog.map fa fc b) = pmap (.loop c a b)
      rw [PalPeg.GSVProg.pmap, progMap_eq_pmap b]

variable {sc : ℕ} {Terminal : Type} {blank endSym mark startSym : Fin sc}

theorem hcond_gsv (c : Cond8) (σ : Fin 10 → Fin sc) :
    (I10 (Terminal := Terminal) blank endSym mark startSym).condOf (fc c) σ
      = ((I8 (Terminal := Terminal) blank endSym mark startSym).transport e8Emb).condOf c σ := by
  simp only [Interp.transport, e8Emb_apply]
  cases c <;>
    simp [PalPeg.GSVProg.fc, PalPeg.GSVProg.I10, PalPeg.GSVProg.condOf10,
      PalPeg.GSProg.I8, PalPeg.GSProg.condOf8]

theorem hact_gsv (a : Act8) (x : Option Terminal) (σ : Fin 10 → Fin sc) :
    (I10 (Terminal := Terminal) blank endSym mark startSym).actOf (fa a) x σ
      = ((I8 (Terminal := Terminal) blank endSym mark startSym).transport e8Emb).actOf a x σ := by
  funext j
  simp only [Interp.transport]
  rcases h : proj e8Emb j with _ | i
  · have hne : j ≠ e8 a.1 := by
      intro hj
      rw [hj, ← e8Emb_apply, proj_ι] at h
      exact Option.some_ne_none a.1 h
    show (I10 (Terminal := Terminal) blank endSym mark startSym).actOf (fa a) x σ j
        = (σ j, Move.stay)
    simp [PalPeg.GSVProg.fa, PalPeg.GSVProg.I10, PalPeg.GSVProg.actOf10,
      touchVec, hne, Ne.symm hne]
  · have hij : e8Emb i = j := eq_ι_of_proj_eq_some h
    subst hij
    show (I10 (Terminal := Terminal) blank endSym mark startSym).actOf (fa a) x σ (e8Emb i)
        = (I8 (Terminal := Terminal) blank endSym mark startSym).actOf a x
            (fun k => σ (e8Emb k)) i
    simp only [e8Emb_apply, PalPeg.GSVProg.I10, PalPeg.GSVProg.actOf10, PalPeg.GSVProg.fa,
      PalPeg.GSProg.I8, PalPeg.GSProg.actOf8]
    by_cases hia : i = a.1
    · subst hia; simp [touchVec]
    · have hne2 : e8 i ≠ e8 a.1 := by
        intro hcon
        apply hia
        have hv := congrArg Fin.val hcon
        simp only [PalPeg.GSVProg.e8] at hv
        exact Fin.ext hv
      simp [touchVec, hia, hne2]

/-- **タスク 1 (5)**：`GSVerifierProg.exec_lift` の主張が、
一般の `exec_transport`（テープの移送）と `exec_map`（動作・条件識別子の再ラベリング）
の合成として得られることの確認。 -/
theorem exec_lift_reproduced {P : Prog Act8 Cond8} {T : Fin 8 → STape (Fin sc)}
    {U X : STape (Fin sc)} {acts : List (Fin 8 → Fin sc × Move)}
    (h : Exec (I8 (Terminal := Terminal) blank endSym mark startSym) blank P T acts) :
    Exec (I10 (Terminal := Terminal) blank endSym mark startSym) blank (pmap P)
      (comb T U X) (acts.map (liftVec U X)) := by
  have h1 := exec_transport h e8Emb (comb (fun _ => U) U X)
  rw [extend_e8Emb_comb, extendVec_e8Emb_comb'] at h1
  have h2 := exec_map hcond_gsv hact_gsv h1
  rw [progMap_eq_pmap] at h2
  exact h2

end GSVerifierCorollary

end PalPeg.ProgLang

#print axioms PalPeg.ProgLang.exec_transport
#print axioms PalPeg.ProgLang.exec_map
#print axioms PalPeg.ProgLang.exec_sum_seq
#print axioms PalPeg.ProgLang.exec_lift_reproduced
