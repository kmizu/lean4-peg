import PalPeg.ProgLang

/-!
# `Prog` のトレース計算のための再利用可能な補題 (`ProgLangLib`)

`PalPeg.ProgLang` の `Prog` / `trace` / `runInputs` に対して、
**「プログラム `p` は（任意の継続 `r` の下で）ちょうど動作列 `acts` を出して `r` に戻る」**
という合成可能な述語 `Exec` を定義し、構成子ごとの導入規則を与える。

各テープ手続き（`GSScanTapes.program'` など、テープ状態の関数として書かれた
`List (Act …)`）を `Prog` に載せる作業は、この `Exec` の合成規則
（`exec_skip` / `exec_act` / `exec_seq` / `exec_ite_pos` / `exec_ite_neg` /
`exec_loop_stop` / `exec_loop_cont`）だけで機械的に進められる。

* `SEqAt I T s₁ s₂` … 現在のテープ束 `T` のもとで二つの継続スタックが同じ 1 ステップを
  与える（`ite`/`skip`/`seq` の純制御展開を吸収する）。
* `ExecK` / `Exec` … 主定義。
* `touchVec` … 「1 本のテープだけを触り、他は読んだ記号を書き戻して停留」する動作ベクトル。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PalPeg.ProgLang

open PegSeparation.RealTimeTM
open PalPeg.Program

variable {A C Terminal Γ : Type} {t : ℕ}

/-! ## 1. 継続スタックの「その場での」同値 -/

/-- 現在のテープ束 `T` のもとで、二つの継続スタックが同じ 1 マイクロステップを与える。 -/
def SEqAt (I : Interp Terminal A C Γ t) (T : Fin t → STape Γ) (s₁ s₂ : Stack A C) : Prop :=
  stepStack (evalConds I (fun j => (T j).focus)) s₁
    = stepStack (evalConds I (fun j => (T j).focus)) s₂

namespace SEqAt

variable {I : Interp Terminal A C Γ t} {T : Fin t → STape Γ} {s₁ s₂ s₃ : Stack A C}

theorem rfl' (I : Interp Terminal A C Γ t) (T : Fin t → STape Γ) (s : Stack A C) :
    SEqAt I T s s := rfl

theorem symm (h : SEqAt I T s₁ s₂) : SEqAt I T s₂ s₁ := Eq.symm h

theorem trans (h₁ : SEqAt I T s₁ s₂) (h₂ : SEqAt I T s₂ s₃) : SEqAt I T s₁ s₃ :=
  Eq.trans h₁ h₂

end SEqAt

variable {I : Interp Terminal A C Γ t} {blank : Γ}

theorem trace_congr {T : Fin t → STape Γ} {s₁ s₂ : Stack A C} (h : SEqAt I T s₁ s₂)
    (l : List (Option Terminal)) :
    trace I blank l (s₁, T) = trace I blank l (s₂, T) := by
  cases l with
  | nil => rfl
  | cons x l =>
      rw [trace_cons, trace_cons]
      simp only [microStep]
      rw [h]

theorem runInputs_congr {T : Fin t → STape Γ} {s₁ s₂ : Stack A C} (h : SEqAt I T s₁ s₂)
    (x : Option Terminal) (l : List (Option Terminal)) :
    runInputs I blank (x :: l) (s₁, T) = runInputs I blank (x :: l) (s₂, T) := by
  rw [runInputs_cons, runInputs_cons]
  congr 1
  simp only [microStep]
  rw [h]

/-! ## 2. `Exec`：ちょうど `acts` を出して継続に戻る -/

/-- 継続スタック `pre` を（任意の継続 `r` の下で）走らせると、ちょうど `acts` を出して
継続 `r`（と同じ 1 ステップを与えるスタック）に戻る。 -/
def ExecK (I : Interp Terminal A C Γ t) (blank : Γ) (pre : Stack A C)
    (T : Fin t → STape Γ) (acts : List (Fin t → Γ × Move)) : Prop :=
  ∀ (r : Stack A C) (l : List (Option Terminal)), l.length = acts.length →
    trace I blank l (pre ++ r, T) = acts ∧
      ∃ s', runInputs I blank l (pre ++ r, T) = (s', applyTrace blank T acts) ∧
        SEqAt I (applyTrace blank T acts) s' r

/-- 1 プログラム版。 -/
def Exec (I : Interp Terminal A C Γ t) (blank : Γ) (p : Prog A C)
    (T : Fin t → STape Γ) (acts : List (Fin t → Γ × Move)) : Prop :=
  ExecK I blank [p] T acts

theorem Exec.trace_eq {p : Prog A C} {T : Fin t → STape Γ}
    {acts : List (Fin t → Γ × Move)} (h : Exec I blank p T acts)
    (r : Stack A C) (l : List (Option Terminal)) (hl : l.length = acts.length) :
    trace I blank l (p :: r, T) = acts := (h r l hl).1

theorem exec_of_eq {p : Prog A C} {T : Fin t → STape Γ}
    {acts acts' : List (Fin t → Γ × Move)} (h : acts = acts')
    (hE : Exec I blank p T acts) : Exec I blank p T acts' := h ▸ hE

/-- 制御同値なスタックへの移送。 -/
theorem execK_congr {s₁ s₂ : Stack A C} {T : Fin t → STape Γ}
    {acts : List (Fin t → Γ × Move)} (h : ∀ r : Stack A C, SEqAt I T (s₁ ++ r) (s₂ ++ r))
    (hE : ExecK I blank s₂ T acts) : ExecK I blank s₁ T acts := by
  intro r l hl
  refine ⟨by rw [trace_congr (h r) l]; exact (hE r l hl).1, ?_⟩
  obtain ⟨-, s', hs', hEq⟩ := hE r l hl
  cases l with
  | nil =>
      have hacts : acts = [] := by
        cases acts with
        | nil => rfl
        | cons a l => simp at hl
      subst hacts
      refine ⟨s₁ ++ r, rfl, ?_⟩
      have hs2 : s' = s₂ ++ r := by
        have := congrArg Prod.fst hs'
        simpa using this.symm
      simp only [applyTrace_nil] at hEq ⊢
      exact SEqAt.trans (h r) (hs2 ▸ hEq)
  | cons x l =>
      refine ⟨s', ?_, hEq⟩
      rw [runInputs_congr (h r) x l]
      exact hs'

/-! ### 構成子ごとの規則 -/

theorem exec_skip (T : Fin t → STape Γ) :
    Exec I blank (Prog.skip : Prog A C) T [] := by
  intro r l hl
  have hl0 : l = [] := by
    cases l with
    | nil => rfl
    | cons a l => simp at hl
  subst hl0
  refine ⟨rfl, ⟨[Prog.skip] ++ r, rfl, ?_⟩⟩
  show stepStack _ ([Prog.skip] ++ r) = stepStack _ r
  simp

/-- 動作解釈が入力記号を見ない（ラウンド先頭で入力をテープに書かないプログラム用）。 -/
def InputFree (I : Interp Terminal A C Γ t) : Prop :=
  ∀ (a : A) (s : Option Terminal) (σ : Fin t → Γ), I.actOf a s σ = I.actOf a none σ

/-- 動作 `a` がテープ束 `T` の上で行う write+move ベクトル。 -/
def actVec (I : Interp Terminal A C Γ t) (a : A) (T : Fin t → STape Γ) : Fin t → Γ × Move :=
  I.actOf a none (fun j => (T j).focus)

theorem exec_act (hI : InputFree I) (a : A) (T : Fin t → STape Γ) :
    Exec I blank (Prog.act a) T [actVec I a T] := by
  intro r l hl
  obtain ⟨x, rfl⟩ : ∃ x, l = [x] := by
    cases l with
    | nil => simp at hl
    | cons x l =>
        cases l with
        | nil => exact ⟨x, rfl⟩
        | cons y l => simp at hl
  have hstep : stepStack (evalConds I (fun j => (T j).focus)) ([Prog.act a] ++ r)
      = (r, some a) := by
    show stepStack _ (Prog.act a :: r) = _
    simp
  have hmicro : microStep I blank x ([Prog.act a] ++ r, T)
      = (r, fun j => (T j).applyAction blank (actVec I a T j)) := by
    simp only [microStep]
    rw [hstep]
    simp only [actVec]
    rw [hI a x]
  refine ⟨?_, ⟨r, ?_, SEqAt.rfl' _ _ _⟩⟩
  · rw [trace_cons]
    rw [show ([Prog.act a] ++ r, T).1 = [Prog.act a] ++ r from rfl,
      show ([Prog.act a] ++ r, T).2 = T from rfl, hstep, hmicro]
    simp only [actVec]
    rw [hI a x]
    simp
  · rw [runInputs_cons, hmicro, runInputs_nil, applyTrace_cons, applyTrace_nil]

theorem exec_comp {p q : Prog A C} {T : Fin t → STape Γ}
    {A₁ A₂ : List (Fin t → Γ × Move)} (hp : Exec I blank p T A₁)
    (hq : Exec I blank q (applyTrace blank T A₁) A₂) :
    ExecK I blank [p, q] T (A₁ ++ A₂) := by
  intro r l hl
  rw [List.length_append] at hl
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ :
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = A₁.length ∧ l₂.length = A₂.length :=
    ⟨l.take A₁.length, l.drop A₁.length, (List.take_append_drop _ _).symm,
      by simp; omega, by simp; omega⟩
  have hpre : ([p, q] ++ r) = p :: ([q] ++ r) := rfl
  obtain ⟨ht1, s₁, hr1, he1⟩ := hp ([q] ++ r) l₁ h1
  rw [show [p] ++ ([q] ++ r) = p :: ([q] ++ r) from rfl] at ht1 hr1
  have hT1 : applyTrace blank T (A₁ ++ A₂) = applyTrace blank (applyTrace blank T A₁) A₂ :=
    applyTrace_append _ _ _ _
  rw [hpre]
  constructor
  · rw [trace_append, ht1, hr1]
    congr 1
    rw [trace_congr he1 l₂]
    exact ((hq r l₂ h2).1)
  · rw [runInputs_append, hr1, hT1]
    cases l₂ with
    | nil =>
        have hA2 : A₂ = [] := by
          cases A₂ with
          | nil => rfl
          | cons a l => simp at h2
        subst hA2
        refine ⟨s₁, rfl, ?_⟩
        obtain ⟨_, s₂, hr2, he2⟩ := hq r [] (by simp)
        simp only [runInputs_nil] at hr2
        have hs2 : s₂ = [q] ++ r := by
          have := congrArg Prod.fst hr2
          simpa using this.symm
        simp only [applyTrace_nil] at he2 ⊢
        exact SEqAt.trans he1 (hs2 ▸ he2)
    | cons x l' =>
        rw [runInputs_congr he1 x l']
        obtain ⟨_, s₂, hr2, he2⟩ := hq r (x :: l') h2
        exact ⟨s₂, hr2, he2⟩

theorem exec_seq {p q : Prog A C} {T : Fin t → STape Γ}
    {A₁ A₂ : List (Fin t → Γ × Move)} (hp : Exec I blank p T A₁)
    (hq : Exec I blank q (applyTrace blank T A₁) A₂) :
    Exec I blank (Prog.seq p q) T (A₁ ++ A₂) := by
  refine execK_congr (fun r => ?_) (exec_comp hp hq)
  show stepStack _ (Prog.seq p q :: r) = stepStack _ (p :: q :: r)
  simp

theorem exec_ite_pos {c : C} {p q : Prog A C} {T : Fin t → STape Γ}
    {acts : List (Fin t → Γ × Move)} (hc : I.condOf c (fun j => (T j).focus) = true)
    (hp : Exec I blank p T acts) : Exec I blank (Prog.ite c p q) T acts := by
  refine execK_congr (fun r => ?_) hp
  show stepStack _ (Prog.ite c p q :: r) = stepStack _ (p :: r)
  rw [stepStack_ite]
  congr 1
  simp [evalConds, hc]

theorem exec_ite_neg {c : C} {p q : Prog A C} {T : Fin t → STape Γ}
    {acts : List (Fin t → Γ × Move)} (hc : I.condOf c (fun j => (T j).focus) = false)
    (hq : Exec I blank q T acts) : Exec I blank (Prog.ite c p q) T acts := by
  refine execK_congr (fun r => ?_) hq
  show stepStack _ (Prog.ite c p q :: r) = stepStack _ (q :: r)
  rw [stepStack_ite]
  congr 1
  simp [evalConds, hc]

theorem exec_loop_stop {c : C} {a : A} {b : Prog A C} {T : Fin t → STape Γ}
    (hc : I.condOf c (fun j => (T j).focus) = false) :
    Exec I blank (Prog.loop c a b) T [] := by
  intro r l hl
  have hl0 : l = [] := by
    cases l with
    | nil => rfl
    | cons a l => simp at hl
  subst hl0
  refine ⟨rfl, ⟨[Prog.loop c a b] ++ r, rfl, ?_⟩⟩
  show stepStack _ ([Prog.loop c a b] ++ r) = stepStack _ r
  show stepStack _ (Prog.loop c a b :: r) = stepStack _ r
  rw [stepStack_loop, if_neg]
  simp [evalConds, hc]

theorem exec_loop_cont (hI : InputFree I) {c : C} {a : A} {b : Prog A C}
    {T : Fin t → STape Γ} {A₁ A₂ : List (Fin t → Γ × Move)}
    (hc : I.condOf c (fun j => (T j).focus) = true)
    (hb : Exec I blank b (fun j => (T j).applyAction blank (actVec I a T j)) A₁)
    (hl : Exec I blank (Prog.loop c a b)
      (applyTrace blank (fun j => (T j).applyAction blank (actVec I a T j)) A₁) A₂) :
    Exec I blank (Prog.loop c a b) T (actVec I a T :: (A₁ ++ A₂)) := by
  intro r l hlen
  simp only [List.length_cons] at hlen
  obtain ⟨x, l', rfl⟩ : ∃ x l', l = x :: l' := by
    cases l with
    | nil => simp at hlen
    | cons x l' => exact ⟨x, l', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
  have hstep : stepStack (evalConds I (fun j => (T j).focus))
      ([Prog.loop c a b] ++ r) = (b :: Prog.loop c a b :: r, some a) := by
    show stepStack _ (Prog.loop c a b :: r) = _
    rw [stepStack_loop, if_pos (by simp [evalConds, hc])]
  have hmicro : microStep I blank x ([Prog.loop c a b] ++ r, T)
      = (b :: Prog.loop c a b :: r,
          fun j => (T j).applyAction blank (actVec I a T j)) := by
    simp only [microStep]
    rw [hstep]
    simp only [actVec]
    rw [hI a x]
  have hcomp := exec_comp hb hl r l' hlen
  have hpre : ([b, Prog.loop c a b] ++ r) = b :: Prog.loop c a b :: r := rfl
  rw [hpre] at hcomp
  constructor
  · rw [trace_cons, show ([Prog.loop c a b] ++ r, T).1 = [Prog.loop c a b] ++ r from rfl,
      show ([Prog.loop c a b] ++ r, T).2 = T from rfl, hstep, hmicro]
    simp only [actVec] at hcomp ⊢
    rw [hI a x, hcomp.1]
    simp
  · rw [runInputs_cons, hmicro, applyTrace_cons]
    obtain ⟨_, s', hr', he'⟩ := hcomp
    exact ⟨s', hr', he'⟩

/-- **停止**。`acts` を出し切った直後にもう 1 歩進めると、制御スタックは空になる
（＝ラウンドプログラムが確かに終了している）。 -/
theorem exec_halts {p : Prog A C} {T : Fin t → STape Γ}
    {acts : List (Fin t → Γ × Move)} (h : Exec I blank p T acts)
    (l : List (Option Terminal)) (hl : l.length = acts.length) (x : Option Terminal) :
    (runInputs I blank (l ++ [x]) ([p], T)).1 = [] := by
  obtain ⟨-, s', hr, he⟩ := h [] l hl
  rw [show ([p] ++ ([] : Stack A C)) = [p] from rfl] at hr
  rw [runInputs_append, hr, runInputs_cons, runInputs_nil]
  simp only [microStep]
  rw [he]
  simp


/-! ## 3. 1 本のテープだけを触る動作ベクトル -/

/-- テープ `i` に `w` を書いて `m` へ動き、他のテープは読んだ記号を書き戻して停留。 -/
def touchVec [DecidableEq (Fin t)] (i : Fin t) (w : Γ) (m : Move) (σ : Fin t → Γ) :
    Fin t → Γ × Move :=
  fun j => if j = i then (w, m) else (σ j, Move.stay)

variable [DecidableEq (Fin t)]

@[simp] theorem applyAction_focus_stay (T : STape Γ) :
    T.applyAction blank (T.focus, Move.stay) = T := rfl

theorem applyTouch_self (i : Fin t) (w : Γ) (m : Move) (T : Fin t → STape Γ) :
    (fun j => (T j).applyAction blank (touchVec i w m (fun j => (T j).focus) j)) i
      = (T i).applyAction blank (w, m) := by
  simp [touchVec]

theorem applyTouch_ne {i j : Fin t} (w : Γ) (m : Move) (T : Fin t → STape Γ)
    (h : j ≠ i) :
    (fun j => (T j).applyAction blank (touchVec i w m (fun j => (T j).focus) j)) j = T j := by
  simp [touchVec, h]

end PalPeg.ProgLang
