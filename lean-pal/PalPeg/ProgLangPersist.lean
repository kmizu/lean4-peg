import Mathlib
import PalPeg.ProgLang
import PalPeg.ProgLangLib
import PalPeg.ProgramMachine

/-!
# 継続を持ち越す (persistent) 制御をもつプログラム機械 (`ProgLangPersist`)

`PalPeg/ProgLang.lean` の `progMachine` は、ラウンド先頭で制御スタックを
`[prog]` に **リセット** する。したがって「1 ラウンドで終わり切らない長い
プログラム」を扱えない。PAL の機械では、段階前処理 (`decProg`) をラウンドを
またいで一定レートで進める必要があるため、この制限が本質的に効く。

本ファイルは、制御スタックを **ラウンド境界でそのまま持ち越す** 機械
`progMachineP` を与える。
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. 部分項と容量：到達スタックの有限性 -/

namespace PalPeg.ProgLang.Prog

variable {A C : Type}

/-- `p` の部分項（自分自身を含む）。 -/
def subterms : Prog A C → List (Prog A C)
  | .skip => [.skip]
  | .act a => [.act a]
  | .seq p q => .seq p q :: (subterms p ++ subterms q)
  | .ite c p q => .ite c p q :: (subterms p ++ subterms q)
  | .loop c a b => .loop c a b :: subterms b

@[simp] theorem mem_subterms_self (p : Prog A C) : p ∈ p.subterms := by
  cases p <;> simp [subterms]

theorem subterms_trans : ∀ (p q r : Prog A C), q ∈ p.subterms → r ∈ q.subterms →
    r ∈ p.subterms := by
  intro p
  induction p with
  | skip =>
      intro q r hq hr
      simp only [subterms, List.mem_singleton] at hq
      subst hq; exact hr
  | act a =>
      intro q r hq hr
      simp only [subterms, List.mem_singleton] at hq
      subst hq; exact hr
  | seq p q ihp ihq =>
      intro u r hu hr
      simp only [subterms, List.mem_cons, List.mem_append] at hu
      rcases hu with rfl | hu | hu
      · exact hr
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihp _ _ hu hr))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihq _ _ hu hr))
  | ite c p q ihp ihq =>
      intro u r hu hr
      simp only [subterms, List.mem_cons, List.mem_append] at hu
      rcases hu with rfl | hu | hu
      · exact hr
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihp _ _ hu hr))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihq _ _ hu hr))
  | loop c a b ihb =>
      intro u r hu hr
      simp only [subterms, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hr
      · exact List.mem_cons_of_mem _ (ihb _ _ hu hr)

/-- `p` の実行中にスタックが占めうる長さの上界（`p` 自身の 1 枠を含む）。 -/
def cap : Prog A C → ℕ
  | .skip => 1
  | .act _ => 1
  | .seq p q => max (cap p + 1) (cap q)
  | .ite _ p q => max (cap p) (cap q)
  | .loop _ _ b => cap b + 1

theorem one_le_cap (p : Prog A C) : 1 ≤ p.cap := by
  induction p with
  | skip => simp [cap]
  | act a => simp [cap]
  | seq p q ihp ihq => simp only [cap]; omega
  | ite c p q ihp ihq => simp only [cap]; omega
  | loop c a b ihb => simp only [cap]; omega

end PalPeg.ProgLang.Prog

namespace PalPeg.ProgLangPersist

open PegSeparation.RealTimeTM
open PalPeg.Program
open PalPeg.Speedup
open PalPeg.ProgLang

variable {A C : Type}

/-- スタックの容量：`p :: r` を実行する間、`r` の各要素は場所を占め続ける。 -/
def scap : Stack A C → ℕ
  | [] => 0
  | p :: r => max (p.cap + r.length) (scap r)

@[simp] theorem scap_nil : scap ([] : Stack A C) = 0 := rfl

@[simp] theorem scap_cons (p : Prog A C) (r : Stack A C) :
    scap (p :: r) = max (p.cap + r.length) (scap r) := rfl

theorem length_le_scap (s : Stack A C) : s.length ≤ scap s := by
  induction s with
  | nil => simp
  | cons p r ih =>
      have := Prog.one_le_cap p
      simp only [scap_cons, List.length_cons]
      omega

/-- **容量は 1 マイクロステップで増えない。** -/
theorem scap_stepStack (ev : C → Bool) :
    ∀ s : Stack A C, scap (stepStack ev s).1 ≤ scap s := by
  intro s
  induction s using stepStack.induct (ev := ev) with
  | case1 => simp
  | case2 r ih =>
      simp only [stepStack_skip, scap_cons]
      exact le_trans ih (le_max_right _ _)
  | case3 a r =>
      simp only [stepStack_act, scap_cons]
      exact le_max_right _ _
  | case4 p q r ih =>
      simp only [stepStack_seq]
      refine le_trans ih ?_
      simp only [scap_cons, List.length_cons, Prog.cap]
      omega
  | case5 c p q r ih =>
      simp only [stepStack_ite]
      refine le_trans ih ?_
      have hb : Prog.cap (if h : ev c = true then p else q) ≤ max (Prog.cap p) (Prog.cap q) := by
        by_cases hc : ev c = true
        · simp only [dif_pos hc]; exact le_max_left _ _
        · simp only [dif_neg hc]; exact le_max_right _ _
      simp only [scap_cons, Prog.cap]
      omega
  | case6 c a b r h =>
      simp only [stepStack_loop, h, if_true, scap_cons, List.length_cons, Prog.cap]
      omega
  | case7 c a b r h ih =>
      simp only [stepStack_loop, h, Bool.false_eq_true, if_false]
      refine le_trans ih ?_
      simp only [scap_cons, Prog.cap]
      omega

/-- **到達スタックの要素は部分項のまま。** -/
theorem stepStack_forall_mem (ev : C → Bool) (P : Prog A C → Prop)
    (hP : ∀ p : Prog A C, P p → ∀ q ∈ p.subterms, P q) :
    ∀ s : Stack A C, (∀ p ∈ s, P p) → ∀ q ∈ (stepStack ev s).1, P q := by
  intro s
  induction s using stepStack.induct (ev := ev) with
  | case1 => simp
  | case2 r ih =>
      intro h
      simp only [stepStack_skip]
      exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
  | case3 a r =>
      intro h q hq
      simp only [stepStack_act] at hq
      exact h q (List.mem_cons_of_mem _ hq)
  | case4 p q r ih =>
      intro h
      simp only [stepStack_seq]
      have hpq : P (Prog.seq p q) := h _ (List.mem_cons_self ..)
      refine ih ?_
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact hP _ hpq u (List.mem_cons_of_mem _ (List.mem_append_left _ (Prog.mem_subterms_self u)))
      · exact hP _ hpq u (List.mem_cons_of_mem _ (List.mem_append_right _ (Prog.mem_subterms_self u)))
      · exact h u (List.mem_cons_of_mem _ hu)
  | case5 c p q r ih =>
      intro h
      simp only [stepStack_ite]
      have hpq : P (Prog.ite c p q) := h _ (List.mem_cons_self ..)
      have hbr : P (if hc : ev c = true then p else q) := by
        by_cases hc : ev c = true
        · simp only [dif_pos hc]
          exact hP _ hpq p
            (List.mem_cons_of_mem _ (List.mem_append_left _ (Prog.mem_subterms_self p)))
        · simp only [dif_neg hc]
          exact hP _ hpq q
            (List.mem_cons_of_mem _ (List.mem_append_right _ (Prog.mem_subterms_self q)))
      refine ih ?_
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hbr
      · exact h u (List.mem_cons_of_mem _ hu)
  | case6 c a b r h =>
      intro hs q hq
      have hl : P (Prog.loop c a b) := hs _ (List.mem_cons_self ..)
      simp only [stepStack_loop, h, if_true, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · exact hP _ hl q (List.mem_cons_of_mem _ (Prog.mem_subterms_self q))
      · exact hl
      · exact hs q (List.mem_cons_of_mem _ hq)
  | case7 c a b r h ih =>
      intro hs
      simp only [stepStack_loop, h, Bool.false_eq_true, if_false]
      exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))

/-! ## 2. 制御型：到達スタックの有限部分型

`[prog]` から（何歩でも）到達しうるスタックは、
「`prog` の部分項のみからなり、容量が `scap [prog]` 以下のスタック」に含まれる。
この不変条件 `Inv` を制御型の定義そのものに使う。長さは容量以下なので、
`Inv` を満たすスタックは有限個しかない（`allStacks` への埋め込み）。 -/

/-- 制御の不変条件：容量が初期容量以下で、要素はすべて `prog` の部分項。 -/
def Inv (prog : Prog A C) (s : Stack A C) : Prop :=
  scap s ≤ scap [prog] ∧ ∀ p ∈ s, p ∈ prog.subterms

theorem Inv_init (prog : Prog A C) : Inv prog [prog] :=
  ⟨le_rfl, by intro p hp; simp only [List.mem_singleton] at hp; subst hp; simp⟩

theorem Inv_step {prog : Prog A C} {s : Stack A C} (h : Inv prog s) (ev : C → Bool) :
    Inv prog (stepStack ev s).1 :=
  ⟨le_trans (scap_stepStack ev s) h.1,
    stepStack_forall_mem ev (fun p => p ∈ prog.subterms)
      (fun _ hp _ hq => Prog.subterms_trans _ _ _ hp hq) s h.2⟩

theorem Inv_nil (prog : Prog A C) : Inv prog [] := ⟨by simp, by simp⟩

/-- `L` の要素だけからなる長さ `n` 以下のリストの全体。 -/
def listsUpTo : ℕ → List (Prog A C) → List (Stack A C)
  | 0, _ => [[]]
  | n + 1, L => [] :: L.flatMap (fun p => (listsUpTo n L).map (fun s => p :: s))

theorem mem_listsUpTo : ∀ (n : ℕ) (L : List (Prog A C)) (s : Stack A C),
    s.length ≤ n → (∀ p ∈ s, p ∈ L) → s ∈ listsUpTo n L := by
  intro n
  induction n with
  | zero =>
      intro L s hlen _
      have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hs
      simp [listsUpTo]
  | succ n ih =>
      intro L s hlen hmem
      cases s with
      | nil => simp [listsUpTo]
      | cons p r =>
          have hp : p ∈ L := hmem p (List.mem_cons_self ..)
          have hr : r ∈ listsUpTo n L :=
            ih L r (by simp only [List.length_cons] at hlen; omega)
              (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
          simp only [listsUpTo, List.mem_cons, List.mem_flatMap, List.mem_map]
          exact Or.inr ⟨p, hp, r, hr, rfl⟩

/-- `prog` について `Inv` を満たすスタックをすべて含む有限リスト。 -/
def allStacks (prog : Prog A C) : List (Stack A C) :=
  listsUpTo (scap [prog]) prog.subterms

theorem Inv_mem_allStacks {prog : Prog A C} {s : Stack A C} (h : Inv prog s) :
    s ∈ allStacks prog :=
  mem_listsUpTo _ _ _ (le_trans (length_le_scap s) h.1) h.2

/-- **持ち越し制御型**：`prog` から到達しうるスタック（の上界）。 -/
def CtrlS (prog : Prog A C) : Type := { s : Stack A C // Inv prog s }

instance (prog : Prog A C) [DecidableEq A] [DecidableEq C] :
    DecidableEq (CtrlS prog) := fun c d =>
  decidable_of_iff (c.val = d.val) Subtype.ext_iff.symm

noncomputable instance (prog : Prog A C) [DecidableEq A] [DecidableEq C] :
    Fintype (CtrlS prog) :=
  Fintype.ofInjective
    (fun c => (⟨c.val, Inv_mem_allStacks c.2⟩ : { s : Stack A C // s ∈ allStacks prog }))
    (by
      intro c d h
      have : c.val = d.val := by simpa [Subtype.ext_iff] using h
      exact Subtype.ext this)

/-- 初期制御。 -/
def startCtrlS (prog : Prog A C) : CtrlS prog := ⟨[prog], Inv_init prog⟩

/-- 制御の 1 マイクロステップ（クランプ不要：`Inv` が保存される）。 -/
def stepCtrlS (prog : Prog A C) (ev : C → Bool) (c : CtrlS prog) : CtrlS prog :=
  ⟨(stepStack ev c.val).1, Inv_step c.2 ev⟩

@[simp] theorem stepCtrlS_val (prog : Prog A C) (ev : C → Bool) (c : CtrlS prog) :
    (stepCtrlS prog ev c).val = (stepStack ev c.val).1 := rfl

/-! ## 3. 受理フラグつきの解釈と入力到着動作 -/

variable {Terminal Γ : Type} {t B : ℕ}

/-- `Interp` に **受理フラグの書き換え** を足したもの。`flagOf a = some b` の動作は
「受理ビットを `b` にする」（`setAcc b`）を意味し、`none` の動作はフラグを変えない。
`StructuredMachine.accepting : Q → Bool` は制御しか見られないので、答えのビットは
このフラグとして制御に載せる。 -/
structure InterpF (Terminal A C Γ : Type) (t : ℕ) extends Interp Terminal A C Γ t where
  /-- 動作識別子が受理フラグに与える効果。 -/
  flagOf : A → Option Bool

/-- 1 マイクロステップぶんのフラグ更新。 -/
def updFlag (I : InterpF Terminal A C Γ t) (b : Bool) : Option A → Bool
  | none => b
  | some w => (I.flagOf w).getD b

@[simp] theorem updFlag_none (I : InterpF Terminal A C Γ t) (b : Bool) :
    updFlag I b none = b := rfl

@[simp] theorem updFlag_some (I : InterpF Terminal A C Γ t) (b : Bool) (w : A) :
    updFlag I b (some w) = (I.flagOf w).getD b := rfl

/-- 入力記号列に沿ったフラグの発展（`runInputs` と同じ歩調）。 -/
def runFlag (I : InterpF Terminal A C Γ t) (blank : Γ) :
    List (Option Terminal) → Stack A C × (Fin t → STape Γ) → Bool → Bool
  | [], _, b => b
  | a :: l, x, b =>
      runFlag I blank l (microStep I.toInterp blank a x)
        (updFlag I b (stepStack (evalConds I.toInterp (fun j => (x.2 j).focus)) x.1).2)

@[simp] theorem runFlag_nil (I : InterpF Terminal A C Γ t) (blank : Γ)
    (x : Stack A C × (Fin t → STape Γ)) (b : Bool) : runFlag I blank [] x b = b := rfl

@[simp] theorem runFlag_cons (I : InterpF Terminal A C Γ t) (blank : Γ)
    (a : Option Terminal) (l : List (Option Terminal))
    (x : Stack A C × (Fin t → STape Γ)) (b : Bool) :
    runFlag I blank (a :: l) x b =
      runFlag I blank l (microStep I.toInterp blank a x)
        (updFlag I b (stepStack (evalConds I.toInterp (fun j => (x.2 j).focus)) x.1).2) :=
  rfl

/-- **入力到着動作**：入力テープ `inp` に入力記号を書いて右へ 1 歩。
他のテープは読んだ記号を書き戻して `stay`（＝何もしない）。
スタックには一切依存しない、ラウンド先頭固定の動作である。 -/
def inputAct (inp : Fin t) (encT : Terminal → Γ) (a : Option Terminal) (σ : Fin t → Γ) :
    Fin t → Γ × Move :=
  fun j => if j = inp then (a.elim (σ inp) encT, Move.right) else (σ j, Move.stay)

/-- 入力到着後のテープ束。 -/
def arrive (blank : Γ) (inp : Fin t) (encT : Terminal → Γ) (a : Option Terminal)
    (T : Fin t → STape Γ) : Fin t → STape Γ :=
  fun j => (T j).applyAction blank (inputAct inp encT a (fun i => (T i).focus) j)

theorem applyAction_stay_self (blank : Γ) (T : STape Γ) :
    T.applyAction blank (T.focus, Move.stay) = T := by cases T; rfl

/-- 入力到着は入力テープ以外を **一切** 動かさない。 -/
@[simp] theorem arrive_ne (blank : Γ) (inp : Fin t) (encT : Terminal → Γ)
    (a : Option Terminal) (T : Fin t → STape Γ) {j : Fin t} (hj : j ≠ inp) :
    arrive blank inp encT a T j = T j := by
  simp only [arrive, inputAct, if_neg hj]
  exact applyAction_stay_self blank (T j)

/-! ## 4. 持ち越し制御の機械 `progMachineP`

* フェーズ `0`（ラウンド先頭）は **入力到着** 固定動作。制御スタックは触らない。
* フェーズ `1, …, B-1` は **現在のスタックをそのまま** `stepStack` で進める。
  ラウンド末でスタックがどこにあってもリセットしない（＝持ち越す）。 -/

section Machine

variable [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ]

/-- フェーズ本体。 -/
noncomputable def roundBodyP (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (inp : Fin t) (encT : Terminal → Γ) (hB : 0 < B) :
    PhaseBody Terminal (CtrlS prog × Bool) Γ t B :=
  fun c a ph σ =>
    if ph = ⟨0, hB⟩ then (c, inputAct inp encT a σ)
    else
      ((stepCtrlS prog (evalConds I.toInterp σ) c.1,
          updFlag I c.2 (stepStack (evalConds I.toInterp σ) c.1.val).2),
        match (stepStack (evalConds I.toInterp σ) c.1.val).2 with
        | none => fun j => (σ j, Move.stay)
        | some w => I.actOf w a σ)

/-- **持ち越し制御のプログラム機械。** 受理はフラグ（制御の `Bool` 成分）で決まる。 -/
noncomputable def progMachineP (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (inp : Fin t) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    StructuredMachine Terminal ((CtrlS prog × Bool) × Fin B) Γ t B :=
  ofPhases htape hB blank (startCtrlS prog, false) (fun q => q.2)
    (roundBodyP I prog inp encT hB)

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- フェーズ `0`：入力到着だけが起こり、制御は不変。 -/
theorem bodyStepP_zero (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (hB : 0 < B) (blank : Γ) (a : Option Terminal)
    (c : CtrlS prog × Bool) (T : Fin t → STape Γ) :
    bodyStep blank (roundBodyP I prog inp encT hB) ⟨0, hB⟩ a (c, T)
      = (c, arrive blank inp encT a T) := rfl

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- フェーズ `≠ 0`：現在のスタックを 1 歩進める（`microStep` と一致）。 -/
theorem bodyStepP_ne (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (hB : 0 < B) (blank : Γ) (ph : Fin B) (hph : ph ≠ ⟨0, hB⟩)
    (a : Option Terminal) (c : CtrlS prog × Bool) (T : Fin t → STape Γ) :
    bodyStep blank (roundBodyP I prog inp encT hB) ph a (c, T)
      = ((stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
            updFlag I c.2
              (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2),
          (microStep I.toInterp blank a (c.1.val, T)).2) := by
  have h1 : (bodyStep blank (roundBodyP I prog inp encT hB) ph a (c, T)).1
      = (stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
          updFlag I c.2
            (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2) := by
    simp [bodyStep, roundBodyP, hph]
  refine Prod.ext h1 ?_
  simp only [bodyStep, roundBodyP, if_neg hph, microStep]
  cases h : (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2 with
  | none =>
      funext j
      exact applyAction_stay_self blank (T j)
  | some w => simp


/-! ## 5. ラウンドの意味論 -/

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- **フェーズ実行と `runInputs` / `runFlag` の一致**（ラウンド先頭の入力到着より後）。
フェーズ番号が `0` にならない区間では、機械は現在のスタックをそのまま
`stepStack` で進めるだけである。 -/
theorem phaseRunP_eq (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (hB : 0 < B) (blank : Γ) :
    ∀ (l : List (Option Terminal)) (i : ℕ) (ph : Fin B) (c : CtrlS prog × Bool)
      (T : Fin t → STape Γ),
      i + l.length ≤ B → (l ≠ [] → (ph : ℕ) = i) → (l ≠ [] → i ≠ 0) →
      ((phaseRun blank (roundBodyP I prog inp encT hB) l ph (c, T)).1.1.val
            = (runInputs I.toInterp blank l (c.1.val, T)).1 ∧
        (phaseRun blank (roundBodyP I prog inp encT hB) l ph (c, T)).1.2
            = runFlag I blank l (c.1.val, T) c.2 ∧
        (phaseRun blank (roundBodyP I prog inp encT hB) l ph (c, T)).2
            = (runInputs I.toInterp blank l (c.1.val, T)).2) := by
  intro l
  induction l with
  | nil => intro i ph c T _ _ _; exact ⟨rfl, rfl, rfl⟩
  | cons a l ih =>
      intro i ph c T hlen hph hi0
      have hne : (a :: l) ≠ [] := by simp
      have hphi : (ph : ℕ) = i := hph hne
      have hi : i ≠ 0 := hi0 hne
      have hlen' : i + 1 + l.length ≤ B := by simp at hlen; omega
      have hphne : ph ≠ ⟨0, hB⟩ := by
        intro hcon
        exact hi (by rw [← hphi, hcon])
      have hnext : l ≠ [] → ((nextPhase ph : Fin B) : ℕ) = i + 1 := by
        intro hl
        have hpos : 0 < l.length := List.length_pos_iff.2 hl
        have hb : ((ph : ℕ) + 1 < B) := by omega
        simp only [nextPhase, dif_pos hb]
        omega
      have hIH := ih (i + 1) (nextPhase ph)
        (stepCtrlS prog (evalConds I.toInterp (fun j => (T j).focus)) c.1,
          updFlag I c.2 (stepStack (evalConds I.toInterp (fun j => (T j).focus)) c.1.val).2)
        (microStep I.toInterp blank a (c.1.val, T)).2
        hlen' hnext (by intro _; omega)
      rw [phaseRun_cons, bodyStepP_ne I prog inp encT hB blank ph hphne a c T,
        runInputs_cons, runFlag_cons]
      exact hIH

/-- **主定理（1 ラウンド）。**
ラウンド先頭のマイクロステップは入力到着（`arrive`）だけを行い、制御スタックは
そのまま。残り `B-1` マイクロステップは **現在のスタックの続き** を実行し、
ラウンド末でそこに留まる（リセットしない）。 -/
theorem progMachineP_round (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (c : CtrlS prog × Bool) (T : Fin t → STape Γ) (a : Terminal) :
    ((progMachineP I prog inp encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.1.val
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arrive blank inp encT (some a) T)).1 ∧
      ((progMachineP I prog inp encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.1.2
        = runFlag I blank (List.replicate (B - 1) none)
            (c.1.val, arrive blank inp encT (some a) T) c.2 ∧
      ((progMachineP I prog inp encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).tape
        = (runInputs I.toInterp blank (List.replicate (B - 1) none)
            (c.1.val, arrive blank inp encT (some a) T)).2 ∧
      ((progMachineP I prog inp encT htape hB blank).sRound
          { state := (c, ⟨0, hB⟩), tape := T } a).state.2 = ⟨0, hB⟩ := by
  have hround := ofPhases_round htape hB blank (startCtrlS prog, false)
    (fun q : CtrlS prog × Bool => q.2) (roundBodyP I prog inp encT hB) c T a
  have hlist : MultiStepMachine.roundInputs B a
      = some a :: List.replicate (B - 1) (none : Option Terminal) := rfl
  have hnext : List.replicate (B - 1) (none : Option Terminal) ≠ [] →
      ((nextPhase (⟨0, hB⟩ : Fin B)) : ℕ) = 1 := by
    intro hl
    have hpos : 0 < (List.replicate (B - 1) (none : Option Terminal)).length :=
      List.length_pos_iff.2 hl
    rw [List.length_replicate] at hpos
    have hlt : ((⟨0, hB⟩ : Fin B) : ℕ) + 1 < B := by simp; omega
    simp [nextPhase, hlt]
  have hkey := phaseRunP_eq I prog inp encT hB blank
    (List.replicate (B - 1) (none : Option Terminal)) 1 (nextPhase (⟨0, hB⟩ : Fin B))
    c (arrive blank inp encT (some a) T)
    (by rw [List.length_replicate]; omega) hnext (by intro _; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [progMachineP, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepP_zero]
    exact hkey.1
  · rw [progMachineP, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepP_zero]
    exact hkey.2.1
  · rw [progMachineP, hround]
    simp only []
    rw [hlist, phaseRun_cons, bodyStepP_zero]
    exact hkey.2.2
  · rw [progMachineP, hround]


/-! ## 6. ラウンドの反復 -/

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- 配置のイータ展開（フェーズ成分が分かっているとき）。 -/
theorem sconfig_eta {Q : Type} (X : SConfig (Q × Fin B) Γ t) (p : Fin B)
    (h : X.state.2 = p) : X = { state := (X.state.1, p), tape := X.tape } := by
  subst h; rfl

/-- 1 ラウンドぶんの意味論（制御スタック・受理フラグ・テープ束の組に作用）。
`m` は「継続実行に使えるマイクロステップ数」＝ `B - 1`。 -/
def roundSem (I : InterpF Terminal A C Γ t) (inp : Fin t) (encT : Terminal → Γ)
    (blank : Γ) (m : ℕ) (x : (Stack A C × Bool) × (Fin t → STape Γ)) (a : Terminal) :
    (Stack A C × Bool) × (Fin t → STape Γ) :=
  (((runInputs I.toInterp blank (List.replicate m none)
        (x.1.1, arrive blank inp encT (some a) x.2)).1,
      runFlag I blank (List.replicate m none)
        (x.1.1, arrive blank inp encT (some a) x.2) x.1.2),
    (runInputs I.toInterp blank (List.replicate m none)
      (x.1.1, arrive blank inp encT (some a) x.2)).2)

/-- **主定理（ラウンドの反復）。** `n` ラウンドの実行は、1 ラウンドの意味論
`roundSem`（入力到着 → 現在のスタックの継続実行 `B-1` 歩）を語に沿って畳み込んだもの。
制御は各ラウンド境界で **持ち越される**。 -/
theorem progMachineP_rounds (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) :
    ∀ (w : List Terminal) (c : CtrlS prog × Bool) (T : Fin t → STape Γ),
      (((w.foldl (progMachineP I prog inp encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.1.val,
          (w.foldl (progMachineP I prog inp encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).state.1.2),
        (w.foldl (progMachineP I prog inp encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T }).tape)
          = w.foldl (roundSem I inp encT blank (B - 1)) ((c.1.val, c.2), T) ∧
      (w.foldl (progMachineP I prog inp encT htape hB blank).sRound
            { state := (c, ⟨0, hB⟩), tape := T }).state.2 = ⟨0, hB⟩ := by
  intro w
  induction w with
  | nil => intro c T; exact ⟨rfl, rfl⟩
  | cons a w ih =>
      intro c T
      have hr := progMachineP_round I prog inp encT htape hB blank c T a
      have hcfg :
          (progMachineP I prog inp encT htape hB blank).sRound
              { state := (c, ⟨0, hB⟩), tape := T } a
            = { state :=
                  (((progMachineP I prog inp encT htape hB blank).sRound
                      { state := (c, ⟨0, hB⟩), tape := T } a).state.1, ⟨0, hB⟩),
                tape :=
                  ((progMachineP I prog inp encT htape hB blank).sRound
                      { state := (c, ⟨0, hB⟩), tape := T } a).tape } :=
        sconfig_eta _ _ hr.2.2.2
      have hstep : roundSem I inp encT blank (B - 1) ((c.1.val, c.2), T) a
          = ((((progMachineP I prog inp encT htape hB blank).sRound
                  { state := (c, ⟨0, hB⟩), tape := T } a).state.1.1.val,
              ((progMachineP I prog inp encT htape hB blank).sRound
                  { state := (c, ⟨0, hB⟩), tape := T } a).state.1.2),
            ((progMachineP I prog inp encT htape hB blank).sRound
                { state := (c, ⟨0, hB⟩), tape := T } a).tape) := by
        rw [hr.1, hr.2.1, hr.2.2.1]
        rfl
      rw [List.foldl_cons, List.foldl_cons, hstep]
      rw [hcfg]
      exact ih _ _

/-- 初期配置からの実行（`srun`）版。 -/
theorem progMachineP_srun (I : InterpF Terminal A C Γ t) (prog : Prog A C) (inp : Fin t)
    (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ) (w : List Terminal) :
    ((((progMachineP I prog inp encT htape hB blank).srun w).state.1.1.val,
        ((progMachineP I prog inp encT htape hB blank).srun w).state.1.2),
      ((progMachineP I prog inp encT htape hB blank).srun w).tape)
        = w.foldl (roundSem I inp encT blank (B - 1))
            (([prog], false), fun _ => STape.blankTape blank) :=
  (progMachineP_rounds I prog inp encT htape hB blank w (startCtrlS prog, false)
    (fun _ => STape.blankTape blank)).1

/-- **受理判定。** `progMachineP` は `StructuredMachine` なので、そのまま
`StructuredMachine.structured_recognizedBy` に載り、厳密実時間で認識される
言語を定める。受理ビットは制御に載せたフラグ（`flagOf` による `setAcc`）で決まる。 -/
theorem progMachineP_recognizedBy [DecidableEq Terminal] (I : InterpF Terminal A C Γ t)
    (prog : Prog A C) (inp : Fin t) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B)
    (blank : Γ) :
    RecognizedBy { w | (progMachineP I prog inp encT htape hB blank).SAccepts w } :=
  StructuredMachine.structured_recognizedBy hB _

/-- 受理条件は「ラウンド末の受理フラグ」に他ならない。 -/
theorem progMachineP_SAccepts_iff (I : InterpF Terminal A C Γ t) (prog : Prog A C)
    (inp : Fin t) (encT : Terminal → Γ) (htape : 0 < t) (hB : 0 < B) (blank : Γ)
    (w : List Terminal) :
    (progMachineP I prog inp encT htape hB blank).SAccepts w
      ↔ (w.foldl (roundSem I inp encT blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.2 = true := by
  have h := progMachineP_srun I prog inp encT htape hB blank w
  have h2 : ((progMachineP I prog inp encT htape hB blank).srun w).state.1.2
      = (w.foldl (roundSem I inp encT blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.2 :=
    congrArg (fun z => z.1.2) h
  constructor
  · intro hacc
    rw [← h2]
    exact hacc
  · intro hacc
    show ((progMachineP I prog inp encT htape hB blank).srun w).state.1.2 = true
    rw [h2]
    exact hacc


/-! ## 7. 入力テープ非干渉と「挽き潰し」定理 (`grind`)

ラウンド先頭の入力到着はテープ `inp` だけを動かし、プログラム側は `inp` を
（読むだけで）書き換えない、という自然な条件のもとでは、入力到着とプログラム実行は
完全に分離する。すなわち **プログラムから見ると、ラウンド境界はまったく見えず、
`B-1` 歩ずつ均等に挽き潰されていく**。 -/

/-- **入力テープ非干渉。** これが「もっとも素直で正しい」形の仮定である。
プログラムは入力テープを読むことはできるが（`actOf` は全ヘッドの読み `σ` を見る）、
入力テープの内容とヘッドは動かさず、また入力テープの読みで分岐もしない。 -/
structure NoInputTouch (I : InterpF Terminal A C Γ t) (inp : Fin t) : Prop where
  /-- 入力テープには書かない・動かさない。 -/
  actInp : ∀ (w : A) (a : Option Terminal) (σ : Fin t → Γ),
    I.actOf w a σ inp = (σ inp, Move.stay)
  /-- 入力テープ以外への動作は、入力テープの読みに依存しない。 -/
  actOther : ∀ (w : A) (a : Option Terminal) (σ σ' : Fin t → Γ),
    (∀ j, j ≠ inp → σ j = σ' j) → ∀ j, j ≠ inp → I.actOf w a σ j = I.actOf w a σ' j
  /-- 条件は入力テープの読みに依存しない。 -/
  condIgnore : ∀ (c : C) (σ σ' : Fin t → Γ),
    (∀ j, j ≠ inp → σ j = σ' j) → I.condOf c σ = I.condOf c σ'

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- 非干渉なら、入力テープ以外が一致する 2 つのテープ束から出た 1 マイクロステップは
制御を等しく進め、入力テープ以外を一致させたままにする。 -/
theorem microStep_agree {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (blank : Γ) (a : Option Terminal) (s : Stack A C)
    (T T' : Fin t → STape Γ) (hag : ∀ j, j ≠ inp → T j = T' j) :
    (microStep I.toInterp blank a (s, T)).1 = (microStep I.toInterp blank a (s, T')).1 ∧
      ∀ j, j ≠ inp →
        (microStep I.toInterp blank a (s, T)).2 j
          = (microStep I.toInterp blank a (s, T')).2 j := by
  have hfoc : ∀ j, j ≠ inp → (T j).focus = (T' j).focus := by
    intro j hj; rw [hag j hj]
  have hev : evalConds I.toInterp (fun j => (T j).focus)
      = evalConds I.toInterp (fun j => (T' j).focus) := by
    funext c
    exact hni.condIgnore c _ _ hfoc
  refine ⟨by simp only [microStep, hev], ?_⟩
  intro j hj
  simp only [microStep, hev]
  cases h : (stepStack (evalConds I.toInterp (fun j => (T' j).focus)) s).2 with
  | none => simpa using hag j hj
  | some w =>
      dsimp only
      rw [hag j hj, hni.actOther w a _ _ hfoc j hj]

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- 非干渉なら、プログラムの 1 マイクロステップは入力テープを動かさない。 -/
theorem microStep_inp {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (blank : Γ) (a : Option Terminal) (s : Stack A C)
    (T : Fin t → STape Γ) : (microStep I.toInterp blank a (s, T)).2 inp = T inp := by
  simp only [microStep]
  cases h : (stepStack (evalConds I.toInterp (fun j => (T j).focus)) s).2 with
  | none => simp
  | some w =>
      simp only [hni.actInp]
      exact applyAction_stay_self blank (T inp)

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- `microStep_agree` の反復版。 -/
theorem runInputs_agree {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (blank : Γ) :
    ∀ (l : List (Option Terminal)) (s : Stack A C) (T T' : Fin t → STape Γ),
      (∀ j, j ≠ inp → T j = T' j) →
      (runInputs I.toInterp blank l (s, T)).1 = (runInputs I.toInterp blank l (s, T')).1 ∧
        ∀ j, j ≠ inp →
          (runInputs I.toInterp blank l (s, T)).2 j
            = (runInputs I.toInterp blank l (s, T')).2 j := by
  intro l
  induction l with
  | nil => intro s T T' hag; exact ⟨rfl, hag⟩
  | cons a l ih =>
      intro s T T' hag
      have hstep := microStep_agree hni blank a s T T' hag
      simp only [runInputs_cons]
      have h1 : microStep I.toInterp blank a (s, T)
          = ((microStep I.toInterp blank a (s, T)).1,
              (microStep I.toInterp blank a (s, T)).2) := rfl
      have h2 : microStep I.toInterp blank a (s, T')
          = ((microStep I.toInterp blank a (s, T)).1,
              (microStep I.toInterp blank a (s, T')).2) := by
        rw [hstep.1]
      rw [h1, h2]
      exact ih _ _ _ hstep.2

omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- **挽き潰し（一般形）。** 入力到着で入力テープ以外は変わらないので、
`roundSem` を語に沿って畳み込んだ結果の制御スタックと（入力テープ以外の）テープは、
**ラウンド境界を忘れて** `|w| * m` マイクロステップ走らせたものに一致する。 -/
theorem foldl_roundSem_eq {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (encT : Terminal → Γ) (blank : Γ) (m : ℕ) :
    ∀ (w : List Terminal) (x : (Stack A C × Bool) × (Fin t → STape Γ))
      (U : Fin t → STape Γ), (∀ j, j ≠ inp → x.2 j = U j) →
      (w.foldl (roundSem I inp encT blank m) x).1.1
          = (runInputs I.toInterp blank (List.replicate (w.length * m) none) (x.1.1, U)).1 ∧
        ∀ j, j ≠ inp →
          (w.foldl (roundSem I inp encT blank m) x).2 j
            = (runInputs I.toInterp blank (List.replicate (w.length * m) none)
                (x.1.1, U)).2 j := by
  intro w
  induction w with
  | nil =>
      intro x U hag
      simp only [List.foldl_nil, List.length_nil, Nat.zero_mul, List.replicate_zero,
        runInputs_nil]
      exact ⟨trivial, hag⟩
  | cons a w ih =>
      intro x U hag
      have hag' : ∀ j, j ≠ inp → arrive blank inp encT (some a) x.2 j = U j := by
        intro j hj; rw [arrive_ne blank inp encT (some a) x.2 hj]; exact hag j hj
      have hkey := runInputs_agree hni blank (List.replicate m (none : Option Terminal))
        x.1.1 (arrive blank inp encT (some a) x.2) U hag'
      have hIH := ih (roundSem I inp encT blank m x a)
        (runInputs I.toInterp blank (List.replicate m none) (x.1.1, U)).2
        (by
          intro j hj
          simpa only [roundSem] using hkey.2 j hj)
      have hs : (roundSem I inp encT blank m x a).1.1
          = (runInputs I.toInterp blank (List.replicate m none) (x.1.1, U)).1 := by
        simpa only [roundSem] using hkey.1
      rw [hs] at hIH
      have hsplit : List.replicate ((a :: w).length * m) (none : Option Terminal)
          = List.replicate m none ++ List.replicate (w.length * m) none := by
        rw [← List.replicate_add]
        congr 1
        simp [Nat.succ_mul]
        omega
      rw [List.foldl_cons, hsplit, runInputs_append]
      exact hIH


omit [DecidableEq A] [DecidableEq C] [Fintype Γ] [DecidableEq Γ] in
/-- 停止したあとは、いくら走らせても制御もテープも動かない。 -/
theorem runInputs_halt_of_le (I : InterpF Terminal A C Γ t) (blank : Γ) {m₀ m : ℕ}
    (x : Stack A C × (Fin t → STape Γ)) (hle : m₀ ≤ m)
    (hhalt : (runInputs I.toInterp blank (List.replicate m₀ none) x).1 = []) :
    (runInputs I.toInterp blank (List.replicate m none) x).1 = [] ∧
      (runInputs I.toInterp blank (List.replicate m none) x).2
        = (runInputs I.toInterp blank (List.replicate m₀ none) x).2 ∧
      trace I.toInterp blank (List.replicate m none) x
        = trace I.toInterp blank (List.replicate m₀ none) x := by
  have hsplit : List.replicate m (none : Option Terminal)
      = List.replicate m₀ none ++ List.replicate (m - m₀) none := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hx : runInputs I.toInterp blank (List.replicate m₀ none) x
      = ([], (runInputs I.toInterp blank (List.replicate m₀ none) x).2) :=
    Prod.ext hhalt rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, runInputs_append, hx, runInputs_halted]
  · rw [hsplit, runInputs_append, hx, runInputs_halted]
  · rw [hsplit, trace_append, hx, trace_halted, List.append_nil]

/-- **挽き潰し定理 (`grind`)。**
入力テープ非干渉のもとでは、`progMachineP` の `|w|` ラウンドの実行は、
プログラムを **ラウンド境界を意識せずに** `|w| * (B-1)` マイクロステップ
走らせたものにほかならない（制御スタックと、入力テープ以外のテープについて）。
入力到着は入力テープしか触らないので、両者は完全に分離する。 -/
theorem progMachineP_grind {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (prog : Prog A C) (encT : Terminal → Γ) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) (w : List Terminal) :
    ((progMachineP I prog inp encT htape hB blank).srun w).state.1.1.val
        = (runInputs I.toInterp blank (List.replicate (w.length * (B - 1)) none)
            ([prog], fun _ => STape.blankTape blank)).1 ∧
      ∀ j, j ≠ inp →
        ((progMachineP I prog inp encT htape hB blank).srun w).tape j
          = (runInputs I.toInterp blank (List.replicate (w.length * (B - 1)) none)
              ([prog], fun _ => STape.blankTape blank)).2 j := by
  have h := progMachineP_srun I prog inp encT htape hB blank w
  have hfold := foldl_roundSem_eq hni encT blank (B - 1) w
    ((([prog] : Stack A C), false), fun _ => STape.blankTape blank)
    (fun _ => STape.blankTape blank) (fun _ _ => rfl)
  have hs : ((progMachineP I prog inp encT htape hB blank).srun w).state.1.1.val
      = (w.foldl (roundSem I inp encT blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).1.1 :=
    congrArg (fun z => z.1.1) h
  have ht : ((progMachineP I prog inp encT htape hB blank).srun w).tape
      = (w.foldl (roundSem I inp encT blank (B - 1))
          (([prog], false), fun _ => STape.blankTape blank)).2 :=
    congrArg (fun z => z.2) h
  refine ⟨by rw [hs]; exact hfold.1, ?_⟩
  intro j hj
  rw [ht]
  exact hfold.2 j hj

/-- **挽き潰し定理（停止形）。**
プログラムが `m₀` マイクロステップ以内に停止するなら、
`⌈m₀ / (B-1)⌉ ≤ |w|`（＝ `m₀ ≤ |w| * (B-1)`）となるラウンド数を経た時点で
制御スタックは空になっており、入力テープ以外のテープは、プログラムの全トレース
`L` を初期テープに順に適用したものに一致する。 -/
theorem progMachineP_grind_halt {I : InterpF Terminal A C Γ t} {inp : Fin t}
    (hni : NoInputTouch I inp) (prog : Prog A C) (encT : Terminal → Γ) (htape : 0 < t)
    (hB : 0 < B) (blank : Γ) (w : List Terminal) (m₀ : ℕ)
    (hle : m₀ ≤ w.length * (B - 1))
    (hhalt : (runInputs I.toInterp blank (List.replicate m₀ none)
        (([prog] : Stack A C), fun _ => STape.blankTape blank)).1 = []) :
    ((progMachineP I prog inp encT htape hB blank).srun w).state.1.1.val = [] ∧
      ∀ j, j ≠ inp →
        ((progMachineP I prog inp encT htape hB blank).srun w).tape j
          = applyTrace blank (fun _ => STape.blankTape blank)
              (trace I.toInterp blank (List.replicate m₀ none)
                (([prog] : Stack A C), fun _ => STape.blankTape blank)) j := by
  have hgrind := progMachineP_grind hni prog encT htape hB blank w
  have hstop := runInputs_halt_of_le I blank
    (([prog] : Stack A C), fun _ => STape.blankTape blank) hle hhalt
  refine ⟨by rw [hgrind.1, hstop.1], ?_⟩
  intro j hj
  rw [hgrind.2 j hj, hstop.2.1,
    runInputs_snd_eq_applyTrace I.toInterp blank (List.replicate m₀ none) _]

end Machine

/-
主定理の公理チェック（0 エラー・`sorry` なし・`propext / Classical.choice / Quot.sound` のみ）:

```
#print axioms PalPeg.ProgLangPersist.scap_stepStack
#print axioms PalPeg.ProgLangPersist.stepStack_forall_mem
#print axioms PalPeg.ProgLangPersist.Inv_step
#print axioms PalPeg.ProgLangPersist.Inv_mem_allStacks
#print axioms PalPeg.ProgLangPersist.phaseRunP_eq
#print axioms PalPeg.ProgLangPersist.progMachineP_round
#print axioms PalPeg.ProgLangPersist.progMachineP_rounds
#print axioms PalPeg.ProgLangPersist.progMachineP_srun
#print axioms PalPeg.ProgLangPersist.progMachineP_SAccepts_iff
#print axioms PalPeg.ProgLangPersist.progMachineP_recognizedBy
#print axioms PalPeg.ProgLangPersist.foldl_roundSem_eq
#print axioms PalPeg.ProgLangPersist.progMachineP_grind
#print axioms PalPeg.ProgLangPersist.progMachineP_grind_halt
```
-/
