import Complexity.TqbfFrames
import Complexity.TqbfEvalSpec

/-!
# Specification of the quantifier evaluation on a list machine

`evalQP_spec`: the program `evalQP` halts with the value of the QBF (given as resolved matrix `mv` and quantifier
kinds), within the length bound `B`.
-/

namespace Complexity

variable {k : Nat}

/-- Four working tapes hold `a b c d`; every other tape is as in `L0`. -/
def fr_S4 (ks ku fr vs : Fin k) (L0 L : Lists k) (a b c d : List Nat) : Prop :=
  L ks = a ∧ L ku = b ∧ L fr = c ∧ L vs = d ∧ ∀ x, x ≠ ks → x ≠ ku → x ≠ fr → x ≠ vs → L x = L0 x

structure fr_D4 (ks ku fr vs : Fin k) : Prop where
  a : ks ≠ ku
  b : ks ≠ fr
  c : ks ≠ vs
  d : ku ≠ fr
  e : ku ≠ vs
  f : fr ≠ vs

section Instr
variable {ks ku fr vs : Fin k} {B : Nat} {L0 L : Lists k} {a b c d : List Nat}

theorem fr_S4.set_ks (hd : fr_D4 ks ku fr vs) (h : fr_S4 ks ku fr vs L0 L a b c d) (l : List Nat) :
    fr_S4 ks ku fr vs L0 (L.set ks l) l b c d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · rw [Lists.set_ne _ _ hd.a.symm]; exact h2
  · rw [Lists.set_ne _ _ hd.b.symm]; exact h3
  · rw [Lists.set_ne _ _ hd.c.symm]; exact h4
  · intro x hx1 hx2 hx3 hx4; rw [Lists.set_ne _ _ hx1]; exact h5 x hx1 hx2 hx3 hx4

theorem fr_S4.set_ku (hd : fr_D4 ks ku fr vs) (h : fr_S4 ks ku fr vs L0 L a b c d) (l : List Nat) :
    fr_S4 ks ku fr vs L0 (L.set ku l) a l c d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · rw [Lists.set_ne _ _ hd.a]; exact h1
  · rw [Lists.set_ne _ _ hd.d.symm]; exact h3
  · rw [Lists.set_ne _ _ hd.e.symm]; exact h4
  · intro x hx1 hx2 hx3 hx4; rw [Lists.set_ne _ _ hx2]; exact h5 x hx1 hx2 hx3 hx4

theorem fr_S4.set_fr (hd : fr_D4 ks ku fr vs) (h : fr_S4 ks ku fr vs L0 L a b c d) (l : List Nat) :
    fr_S4 ks ku fr vs L0 (L.set fr l) a b l d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, by simp, ?_, ?_⟩
  · rw [Lists.set_ne _ _ hd.b]; exact h1
  · rw [Lists.set_ne _ _ hd.d]; exact h2
  · rw [Lists.set_ne _ _ hd.f.symm]; exact h4
  · intro x hx1 hx2 hx3 hx4; rw [Lists.set_ne _ _ hx3]; exact h5 x hx1 hx2 hx3 hx4

theorem fr_S4.set_vs (hd : fr_D4 ks ku fr vs) (h : fr_S4 ks ku fr vs L0 L a b c d) (l : List Nat) :
    fr_S4 ks ku fr vs L0 (L.set vs l) a b c l := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, by simp, ?_⟩
  · rw [Lists.set_ne _ _ hd.c]; exact h1
  · rw [Lists.set_ne _ _ hd.e]; exact h2
  · rw [Lists.set_ne _ _ hd.f]; exact h3
  · intro x hx1 hx2 hx3 hx4; rw [Lists.set_ne _ _ hx4]; exact h5 x hx1 hx2 hx3 hx4

theorem fr_lenOK_dropLast {B : Nat} {L : Lists k} (hL : LenOK B L) (i : Fin k) :
    LenOK B (L.set i (L i).dropLast) :=
  lenOK_set hL i (by have := hL i; simp [List.length_dropLast]; omega)

theorem fr_step_push_fr (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d) (e : Nat)
    (hb : c.length + 3 ≤ B) :
    Step B 1 (.push fr e) L (fun L' => fr_S4 ks ku fr vs L0 L' a b (c ++ [e]) d) := by
  have e1 : L fr = c := h.2.2.1
  have hl : LenOK B (L.set fr (L fr ++ [e])) := lenOK_set hL fr (by rw [e1]; simp; omega)
  refine ⟨_, runs_push hL hl, hl, ?_⟩
  have := fr_S4.set_fr hd h (c ++ [e])
  dsimp only; rw [e1]; exact this

theorem fr_step_push_vs (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d) (e : Nat)
    (hb : d.length + 3 ≤ B) :
    Step B 1 (.push vs e) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c (d ++ [e])) := by
  have e1 : L vs = d := h.2.2.2.1
  have hl : LenOK B (L.set vs (L vs ++ [e])) := lenOK_set hL vs (by rw [e1]; simp; omega)
  refine ⟨_, runs_push hL hl, hl, ?_⟩
  have := fr_S4.set_vs hd h (d ++ [e])
  dsimp only; rw [e1]; exact this

theorem fr_step_pop_fr (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d) :
    Step B 1 (.pop fr) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c.dropLast d) := by
  have e1 : L fr = c := h.2.2.1
  have hl := fr_lenOK_dropLast hL fr
  refine ⟨_, runs_pop hL hl, hl, ?_⟩
  have := fr_S4.set_fr hd h c.dropLast
  dsimp only; rw [e1]; exact this

theorem fr_step_pop_vs (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d) :
    Step B 1 (.pop vs) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c d.dropLast) := by
  have e1 : L vs = d := h.2.2.2.1
  have hl := fr_lenOK_dropLast hL vs
  refine ⟨_, runs_pop hL hl, hl, ?_⟩
  have := fr_S4.set_vs hd h d.dropLast
  dsimp only; rw [e1]; exact this

theorem fr_step_skip_vs (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d) :
    Step B 1 (skipP vs) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c d) :=
  ⟨L, runs_skip vs hL, hL, h⟩

theorem fr_step_mv_ks_ku (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d)
    (hb : b.length + 3 ≤ B) :
    Step B 2 (moveTop ks ku) L
      (fun L' => fr_S4 ks ku fr vs L0 L' a.dropLast (b ++ a.getLast?.toList) c d) := by
  have e1 : L ks = a := h.1
  have e2 : L ku = b := h.2.1
  obtain ⟨hl1, hl2⟩ := lenOK_moveTop hL hd.a (by rw [e2]; exact hb)
  refine ⟨_, runs_moveTop hd.a hL hl1 hl2, hl2, ?_⟩
  have h1 := fr_S4.set_ku hd h (L ku ++ (L ks).getLast?.toList)
  have h2 := fr_S4.set_ks hd h1 (L ks).dropLast
  unfold Lists.moveTop
  dsimp only
  rw [e1, e2] at h2 ⊢
  exact h2

theorem fr_step_mv_ku_ks (hd : fr_D4 ks ku fr vs) (hL : LenOK B L) (h : fr_S4 ks ku fr vs L0 L a b c d)
    (hb : a.length + 3 ≤ B) :
    Step B 2 (moveTop ku ks) L
      (fun L' => fr_S4 ks ku fr vs L0 L' (a ++ b.getLast?.toList) b.dropLast c d) := by
  have e1 : L ks = a := h.1
  have e2 : L ku = b := h.2.1
  obtain ⟨hl1, hl2⟩ := lenOK_moveTop hL hd.a.symm (by rw [e1]; exact hb)
  refine ⟨_, runs_moveTop hd.a.symm hL hl1 hl2, hl2, ?_⟩
  have h1 := fr_S4.set_ks hd h (L ks ++ (L ku).getLast?.toList)
  have h2 := fr_S4.set_ku hd h1 (L ku).dropLast
  unfold Lists.moveTop
  dsimp only
  rw [e1, e2] at h2 ⊢
  exact h2

end Instr

theorem fr_S4.cast {ks ku fr vs : Fin k} {L0 L : Lists k} {a b c d a' b' c' d' : List Nat}
    (h : fr_S4 ks ku fr vs L0 L a b c d) (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') :
    fr_S4 ks ku fr vs L0 L a' b' c' d' := by
  subst ha hb hc hd; exact h

/-- `Step` with an existential bound. -/
def fr_StepE (B : Nat) (p : LProg k) (L : Lists k) (P : Lists k → Prop) : Prop := ∃ T, Step B T p L P

section fr_StepE
variable {B : Nat} {p q : LProg k} {L : Lists k} {P R : Lists k → Prop}

theorem Step.fr_toE {T : Nat} (h : Step B T p L P) : fr_StepE B p L P := ⟨T, h⟩

theorem fr_StepE.mono (h : fr_StepE B p L P) (hP : ∀ L', P L' → R L') : fr_StepE B p L R :=
  let ⟨T, h⟩ := h; ⟨T, h.mono (Nat.le_refl _) hP⟩

theorem fr_StepE.seq (h : fr_StepE B p L P) (hq : ∀ L₁, LenOK B L₁ → P L₁ → fr_StepE B q L₁ R) :
    fr_StepE B (.seq p q) L R :=
  let ⟨T₁, L₁, hr, hl, hp⟩ := h
  let ⟨T₂, L₂, hr₂, hl₂, hp₂⟩ := hq L₁ hl hp
  ⟨T₁ + T₂, L₂, hr.seq hr₂, hl₂, hp₂⟩

theorem fr_StepE.iteT {i : Fin k} {c : Nat → Bool} (hL : LenOK B L) (hc : c (lastSym (L i)) = true)
    (h : fr_StepE B p L P) : fr_StepE B (.ite i c p q) L P :=
  let ⟨T, h⟩ := h; ⟨T + 1, h.iteT hL hc⟩

theorem fr_StepE.iteF {i : Fin k} {c : Nat → Bool} (hL : LenOK B L) (hc : c (lastSym (L i)) = false)
    (h : fr_StepE B q L P) : fr_StepE B (.ite i c p q) L P :=
  let ⟨T, h⟩ := h; ⟨T + 1, h.iteF hL hc⟩

theorem fr_StepE.loopF {i : Fin k} {c : Nat → Bool} (hL : LenOK B L) (hc : c (lastSym (L i)) = false)
    (hP : P L) : fr_StepE B (.loop i c p) L P :=
  ⟨1, L, ⟨1, Nat.le_refl _, .loopF hL hc⟩, hL, hP⟩

theorem fr_StepE.loopC {i : Fin k} {c : Nat → Bool} (hL : LenOK B L) (hc : c (lastSym (L i)) = true)
    (h : fr_StepE B p L P) (h2 : ∀ L₁, LenOK B L₁ → P L₁ → fr_StepE B (.loop i c p) L₁ R) :
    fr_StepE B (.loop i c p) L R :=
  let ⟨T₁, L₁, ⟨t₁, ht₁, hx₁⟩, hl₁, hp₁⟩ := h
  let ⟨T₂, L₂, ⟨t₂, ht₂, hx₂⟩, hl₂, hp₂⟩ := h2 L₁ hl₁ hp₁
  ⟨T₁ + 1 + T₂, L₂, ⟨t₁ + 1 + t₂, by omega, .loopC hL hc hx₁ hx₂⟩, hl₂, hp₂⟩

end fr_StepE

theorem fr_nonEmpty_stack_cons {α : Type} (f : α → Nat) (x : α) (st : List α) :
    nonEmpty (lastSym (stackL f (x :: st))) = true := by
  rw [lastSym_stack_cons]; simp [nonEmpty]

theorem fr_nonEmpty_stack_nil {α : Type} (f : α → Nat) : nonEmpty (lastSym (stackL f ([] : List α))) = false := by
  simp [stackL, lastSym, nonEmpty]

section Progs
variable {ks ku fr vs : Fin k} {B : Nat} {L0 : Lists k}

theorem fr_step_descend (hd : fr_D4 ks ku fr vs) :
    ∀ (ks' : List Bool) (ctx : List (Bool × Frame)) (L : Lists k) (d : List Nat), LenOK B L →
    fr_S4 ks ku fr vs L0 L (stackL kindElem ks') (stackL kindElem (ctx.map Prod.fst))
      (stackL Frame.elem (ctx.map Prod.snd)) d →
    ks'.length + ctx.length + 2 ≤ B →
    fr_StepE B (descendP ks ku fr) L (fun L' => fr_S4 ks ku fr vs L0 L' (stackL kindElem [])
      (stackL kindElem ((descendCtx ks' ctx).map Prod.fst))
      (stackL Frame.elem ((descendCtx ks' ctx).map Prod.snd)) d)
  | [], ctx, L, d, hL, h, hb => by
    refine fr_StepE.loopF hL (by rw [h.1]; exact fr_nonEmpty_stack_nil _) ?_
    simpa [descendCtx] using h
  | κ :: ks', ctx, L, d, hL, h, hb => by
    have hc : nonEmpty (lastSym (L ks)) = true := by rw [h.1]; exact fr_nonEmpty_stack_cons _ _ _
    have h' : fr_S4 ks ku fr vs L0 L (stackL kindElem ks' ++ [kindElem κ]) (stackL kindElem (ctx.map Prod.fst))
        (stackL Frame.elem (ctx.map Prod.snd)) d := by rw [← stackL_cons]; exact h
    have hlen : ks'.length + ctx.length + 3 ≤ B := by simp at hb; omega
    have s1 := fr_step_mv_ks_ku hd hL h' (by simp [stackL_length]; omega)
    have hbody : fr_StepE B (.seq (moveTop ks ku) (.push fr 20)) L
        (fun L' => fr_S4 ks ku fr vs L0 L' (stackL kindElem ks')
          (stackL kindElem (((κ, Frame.fresh) :: ctx).map Prod.fst))
          (stackL Frame.elem (((κ, Frame.fresh) :: ctx).map Prod.snd)) d) := by
      refine fr_StepE.seq s1.fr_toE (fun L1 hl1 hp1 => ?_)
      have hp1' : fr_S4 ks ku fr vs L0 L1 (stackL kindElem ks') (stackL kindElem (κ :: ctx.map Prod.fst))
          (stackL Frame.elem (ctx.map Prod.snd)) d :=
        hp1.cast (by simp) (by simp [stackL_cons]) rfl rfl
      have := fr_step_push_fr hd hl1 hp1' 20 (by simp [stackL_length]; omega)
      refine this.fr_toE.mono (fun L' hp => ?_)
      exact hp.cast rfl (by simp) (by simp [stackL_cons, Frame.elem]) rfl
    refine fr_StepE.loopC hL hc hbody (fun L1 hl1 hp1 => ?_)
    have := fr_step_descend hd ks' ((κ, Frame.fresh) :: ctx) L1 d hl1 hp1 (by simp at hb ⊢; omega)
    refine this.mono (fun L' hp => ?_)
    have e : descendCtx (κ :: ks') ctx = descendCtx ks' ((κ, Frame.fresh) :: ctx) := by simp [descendCtx]
    rw [e]; exact hp

variable {a b c : List Nat}

theorem fr_step_clear (hd : fr_D4 ks ku fr vs) :
    ∀ (n : Nat) (L : Lists k) (d : List Nat), d.length = n → LenOK B L → fr_S4 ks ku fr vs L0 L a b c d →
    fr_StepE B (clearP vs) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c [])
  | 0, L, d, hn, hL, h => by
    have : d = [] := List.length_eq_zero_iff.1 hn
    subst this
    exact fr_StepE.loopF hL (by rw [h.2.2.2.1]; exact fr_nonEmpty_stack_nil (fun (x : Nat) => x)) h
  | n + 1, L, d, hn, hL, h => by
    obtain ⟨d', x, rfl⟩ : ∃ d' x, d = d' ++ [x] := by
      rcases List.eq_nil_or_concat d with h0 | ⟨d', x, h0⟩
      · subst h0; simp at hn
      · exact ⟨d', x, by simpa using h0⟩
    have hc : nonEmpty (lastSym (L vs)) = true := by
      rw [h.2.2.2.1, lastSym_append]; simp [nonEmpty]
    refine fr_StepE.loopC hL hc (fr_step_pop_vs hd hL h).fr_toE (fun L1 hl1 hp1 => ?_)
    have hp1' : fr_S4 ks ku fr vs L0 L1 a b c d' := hp1.cast rfl rfl rfl (by simp)
    exact fr_step_clear hd n L1 d' (by simpa using hn) hl1 hp1'

theorem fr_step_pushpop (hd : fr_D4 ks ku fr vs) {L : Lists k} (hL : LenOK B L) {x : Nat}
    (h : fr_S4 ks ku fr vs L0 L a b c [x]) (e : Nat) (hB : 3 ≤ B) :
    fr_StepE B (.seq (.pop vs) (.push vs e)) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c [e]) := by
  refine fr_StepE.seq (fr_step_pop_vs hd hL h).fr_toE (fun L1 hl1 hp1 => ?_)
  have := fr_step_push_vs hd hl1 hp1 e (by simp; omega)
  exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp))

theorem fr_step_normalize (hd : fr_D4 ks ku fr vs) {L : Lists k} (hL : LenOK B L) {st : List Bool}
    (h : fr_S4 ks ku fr vs L0 L a b c (stackL sb st)) (hb : st.length + 3 ≤ B) :
    fr_StepE B (normalizeP vs) L (fun L' => fr_S4 ks ku fr vs L0 L' a b c [sb (st.headD false)]) := by
  cases st with
  | nil =>
    refine fr_StepE.iteF hL (by rw [h.2.2.2.1]; exact fr_nonEmpty_stack_nil _) ?_
    have := fr_step_push_vs hd hL h 0 (by simp [stackL_length] at hb ⊢; omega)
    exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp [stackL, sb]))
  | cons x st0 =>
    have hl : lastSym (L vs) = sb x + 4 := by rw [h.2.2.2.1, lastSym_stack_cons]
    refine fr_StepE.iteT hL (by rw [h.2.2.2.1]; exact fr_nonEmpty_stack_cons _ _ _) ?_
    have hbc : 3 ≤ B := by omega
    cases x with
    | true =>
      refine fr_StepE.iteT hL (by simp [hl, symIs, sb]) ?_
      refine fr_StepE.seq (fr_step_clear hd _ L _ rfl hL h) (fun L1 hl1 hp1 => ?_)
      have := fr_step_push_vs hd hl1 hp1 1 (by simp; omega)
      exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp [sb]))
    | false =>
      refine fr_StepE.iteF hL (by simp [hl, symIs, sb]) ?_
      refine fr_StepE.seq (fr_step_clear hd _ L _ rfl hL h) (fun L1 hl1 hp1 => ?_)
      have := fr_step_push_vs hd hl1 hp1 0 (by simp; omega)
      exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp [sb]))

theorem fr_step_combine (hd : fr_D4 ks ku fr vs) {L : Lists k} (hL : LenOK B L) {ks' ctxk : List Bool}
    {ctxf : List Frame} (κ : Bool) (a v : Bool)
    (h : fr_S4 ks ku fr vs L0 L (stackL kindElem ks') (stackL kindElem (κ :: ctxk))
      (stackL Frame.elem (Frame.second a :: ctxf)) [sb v])
    (hb : ks'.length + ctxk.length + 3 ≤ B) :
    fr_StepE B (combineP ks ku fr vs) L (fun L' => fr_S4 ks ku fr vs L0 L' (stackL kindElem (κ :: ks'))
      (stackL kindElem ctxk) (stackL Frame.elem ctxf) [sb (comb κ a v)]) := by
  have hB3 : 3 ≤ B := by omega
  have hfr : lastSym (L fr) = Frame.elem (.second a) + 4 := by rw [h.2.2.1, lastSym_stack_cons]
  have hku : lastSym (L ku) = kindElem κ + 4 := by rw [h.2.1, lastSym_stack_cons]
  have hX : fr_StepE B (.ite fr (symIs 22)
        (.ite ku (symIs 1) (skipP vs) (.seq (.pop vs) (.push vs 1)))
        (.ite ku (symIs 1) (.seq (.pop vs) (.push vs 0)) (skipP vs))) L
      (fun L' => fr_S4 ks ku fr vs L0 L' (stackL kindElem ks') (stackL kindElem (κ :: ctxk))
        (stackL Frame.elem (Frame.second a :: ctxf)) [sb (comb κ a v)]) := by
    cases a <;> cases κ
    · refine fr_StepE.iteF hL (by simp [hfr, symIs, Frame.elem]) (fr_StepE.iteF hL (by simp [hku, symIs, kindElem]) ?_)
      exact (fr_step_skip_vs hL h).fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp [comb]))
    · refine fr_StepE.iteF hL (by simp [hfr, symIs, Frame.elem]) (fr_StepE.iteT hL (by simp [hku, symIs, kindElem]) ?_)
      exact (fr_step_pushpop hd hL h 0 hB3).mono (fun L' hp => hp.cast rfl rfl rfl (by simp [comb, sb]))
    · refine fr_StepE.iteT hL (by simp [hfr, symIs, Frame.elem]) (fr_StepE.iteF hL (by simp [hku, symIs, kindElem]) ?_)
      exact (fr_step_pushpop hd hL h 1 hB3).mono (fun L' hp => hp.cast rfl rfl rfl (by simp [comb, sb]))
    · refine fr_StepE.iteT hL (by simp [hfr, symIs, Frame.elem]) (fr_StepE.iteT hL (by simp [hku, symIs, kindElem]) ?_)
      exact (fr_step_skip_vs hL h).fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp [comb]))
  unfold combineP
  refine fr_StepE.seq hX (fun L1 hl1 hp1 => ?_)
  have hp1' : fr_S4 ks ku fr vs L0 L1 (stackL kindElem ks') (stackL kindElem ctxk ++ [kindElem κ])
      (stackL Frame.elem ctxf ++ [Frame.elem (.second a)]) [sb (comb κ a v)] :=
    hp1.cast rfl (stackL_cons _ _ _) (stackL_cons _ _ _) rfl
  refine fr_StepE.seq (fr_step_pop_fr hd hl1 hp1').fr_toE (fun L2 hl2 hp2 => ?_)
  have hp2' : fr_S4 ks ku fr vs L0 L2 (stackL kindElem ks') (stackL kindElem ctxk ++ [kindElem κ])
      (stackL Frame.elem ctxf) [sb (comb κ a v)] := hp2.cast rfl rfl (by simp) rfl
  have := fr_step_mv_ku_ks hd hl2 hp2' (by simp [stackL_length]; omega)
  exact this.fr_toE.mono (fun L' hp => hp.cast (by simp [stackL_cons]) (by simp) rfl rfl)

theorem fr_step_return (hd : fr_D4 ks ku fr vs) (mv : List VTok) :
    ∀ (ctx : List (Bool × Frame)) (ks' : List Bool) (v : Bool) (L : Lists k), LenOK B L →
    fr_S4 ks ku fr vs L0 L (stackL kindElem ks') (stackL kindElem (ctx.map Prod.fst))
      (stackL Frame.elem (ctx.map Prod.snd)) [sb v] →
    ks'.length + ctx.length + 2 ≤ B →
    fr_StepE B (returnP ks ku fr vs) L (fun L' => ∃ (ctx'' : List (Bool × Frame)) (ks'' : List Bool) (v'' : Bool),
      (ctx'' = [] ∨ ∃ κ ctx0, ctx'' = (κ, Frame.fresh) :: ctx0) ∧
      fin mv ctx ks' v = fin mv ctx'' ks'' v'' ∧
      extra ctx'' ks''.length = extra ctx ks'.length ∧
      ctx''.length + ks''.length = ctx.length + ks'.length ∧
      fr_S4 ks ku fr vs L0 L' (stackL kindElem ks'') (stackL kindElem (ctx''.map Prod.fst))
        (stackL Frame.elem (ctx''.map Prod.snd)) [sb v''])
  | [], ks', v, L, hL, h, hb => by
    refine fr_StepE.loopF hL (by rw [h.2.2.1]; simp [stackL, lastSym, isSecond]) ?_
    exact ⟨[], ks', v, Or.inl rfl, rfl, rfl, rfl, h⟩
  | (κ, .fresh) :: ctx0, ks', v, L, hL, h, hb => by
    refine fr_StepE.loopF hL (by rw [h.2.2.1]; simp [lastSym_stack_cons, isSecond, Frame.elem]) ?_
    exact ⟨_, ks', v, Or.inr ⟨κ, ctx0, rfl⟩, rfl, rfl, rfl, h⟩
  | (κ, .second a) :: ctx0, ks', v, L, hL, h, hb => by
    have hc : isSecond (lastSym (L fr)) = true := by
      rw [h.2.2.1]
      cases a <;> simp [lastSym_stack_cons, isSecond, Frame.elem]
    have hlen : ks'.length + ctx0.length + 3 ≤ B := by simp at hb; omega
    have hcomb := fr_step_combine hd hL (ks' := ks') (ctxk := ctx0.map Prod.fst) (ctxf := ctx0.map Prod.snd)
      κ a v h (by simpa using hlen)
    refine fr_StepE.loopC hL hc hcomb (fun L1 hl1 hp1 => ?_)
    have ih := fr_step_return hd mv ctx0 (κ :: ks') (comb κ a v) L1 hl1 hp1 (by simp at hb ⊢; omega)
    refine ih.mono (fun L' hp => ?_)
    obtain ⟨c2, k2, v2, hs, hf, he, hlen2, hS⟩ := hp
    refine ⟨c2, k2, v2, hs, ?_, ?_, ?_, hS⟩
    · rw [← hf]; rfl
    · rw [he]; simp [extra]
    · simp at hlen2 ⊢; omega

theorem fr_step_refresh (hd : fr_D4 ks ku fr vs) {L : Lists k} (hL : LenOK B L) {ctx0 : List (Bool × Frame)} {κ : Bool}
    {v : Bool}
    (h : fr_S4 ks ku fr vs L0 L a b (stackL Frame.elem (((κ, Frame.fresh) :: ctx0).map Prod.snd)) [sb v])
    (hb : ctx0.length + 3 ≤ B) :
    fr_StepE B (refreshP fr vs) L (fun L' => fr_S4 ks ku fr vs L0 L' a b
      (stackL Frame.elem (((κ, Frame.second v) :: ctx0).map Prod.snd)) []) := by
  have hl : lastSym (L vs) = sb v + 4 := by
    rw [h.2.2.2.1]; simp [lastSym, sb]
  have hh : fr_S4 ks ku fr vs L0 L a b (stackL Frame.elem (ctx0.map Prod.snd) ++ [20]) [sb v] :=
    h.cast rfl rfl (by simp [stackL_cons, Frame.elem]) rfl
  unfold refreshP
  refine fr_StepE.seq (fr_step_pop_fr hd hL hh).fr_toE (fun L1 hl1 hp1 => ?_)
  have hp1' : fr_S4 ks ku fr vs L0 L1 a b (stackL Frame.elem (ctx0.map Prod.snd)) [sb v] :=
    hp1.cast rfl rfl (by simp) rfl
  refine fr_StepE.seq (?_ : fr_StepE B (.ite vs (symIs 1) (.push fr 22) (.push fr 21)) L1
      (fun L' => fr_S4 ks ku fr vs L0 L' a b (stackL Frame.elem (((κ, Frame.second v) :: ctx0).map Prod.snd))
        [sb v])) (fun L2 hl2 hp2 => ?_)
  · have hl1' : lastSym (L1 vs) = sb v + 4 := by rw [hp1'.2.2.2.1]; simp [lastSym, sb]
    cases v
    · refine fr_StepE.iteF hl1 (by simp [hl1', symIs, sb]) ?_
      have := fr_step_push_fr hd hl1 hp1' 21 (by simp [stackL_length]; omega)
      exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl (by simp [stackL_cons, Frame.elem]) rfl)
    · refine fr_StepE.iteT hl1 (by simp [hl1', symIs, sb]) ?_
      have := fr_step_push_fr hd hl1 hp1' 22 (by simp [stackL_length]; omega)
      exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl (by simp [stackL_cons, Frame.elem]) rfl)
  · have := fr_step_pop_vs hd hl2 hp2
    exact this.fr_toE.mono (fun L' hp => hp.cast rfl rfl rfl (by simp))

theorem fr_halts_answer {v : Bool} {L : Lists k} (hL : LenOK B L)
    (h : fr_S4 ks ku fr vs L0 L a b c [sb v]) :
    Halts (LenOK B) (answerP vs) L v L 2 := by
  have hl : lastSym (L vs) = sb v + 4 := by rw [h.2.2.2.1]; simp [lastSym, sb]
  cases v
  · exact Halts.iteF hL (by simp [hl, symIs, sb]) (halts_halt hL)
  · exact Halts.iteT hL (by simp [hl, symIs, sb]) (halts_halt hL)

end Progs

theorem evalQP_spec {ks ku fr ft vs mr mr2 : Fin k} (hd : [ks, ku, fr, ft, vs, mr, mr2].Nodup) {B : Nat}
    (mv : List VTok) (kinds : List Bool) {L : Lists k}
    (hks : L ks = stackL kindElem kinds) (hku : L ku = []) (hfr : L fr = []) (hft : L ft = []) (hvs : L vs = [])
    (hmr : L mr = (toksV mv).reverse) (hmr2 : L mr2 = [])
    (hB : LenOK B L) (hBt : (toksV mv).length + 2 ≤ B) (hBk : kinds.length + 2 ≤ B) (hBs : mv.length + 3 ≤ B) :
    ∃ L' T, Halts (LenOK B) (evalQP ks ku fr ft vs mr mr2) L (qEvalV mv kinds []) L' T := by
  have hd' := hd
  simp [List.nodup_cons] at hd'
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, ⟨n7, n8, n9, n10, n11⟩, ⟨n12, n13, n14, n15⟩, ⟨n16, n17, n18⟩, ⟨n19, n20⟩, n21⟩ := hd'
  have hd4 : fr_D4 ks ku fr vs := ⟨n1, n2, n4, n7, n9, n13⟩
  have hd5 : [mr, mr2, fr, ft, vs].Nodup := by
    simp [List.nodup_cons, n21, Ne.symm n14, Ne.symm n17, Ne.symm n19, Ne.symm n15, Ne.symm n18, Ne.symm n20, n12,
      n13, n16]
  have key := halts_loop_abs (Q := LenOK B) (i := ks) (c := fun _ => true)
    (p := roundP ks ku fr ft vs mr mr2) (α := List (Bool × Frame) × List Bool)
    (fun a L1 => LenOK B L1 ∧ fr_S4 ks ku fr vs L L1 (stackL kindElem a.2) (stackL kindElem (a.1.map Prod.fst))
      (stackL Frame.elem (a.1.map Prod.snd)) [] ∧ a.2.length + a.1.length = kinds.length ∧
      res mv a.1 a.2 = qEvalV mv kinds [])
    (fun a => cnt a.1 a.2.length) (fun b _ => b = qEvalV mv kinds [])
    (fun a L1 h => h.1) (fun a L1 _ hc => by simp at hc) ?_ ([], kinds) L ?_
  · obtain ⟨b, L', T, hh, hb⟩ := key
    subst hb
    exact ⟨L', T, hh⟩
  · rintro ⟨ctx, ks'⟩ L1 ⟨hl, hS, hlen, hres⟩ _
    dsimp only at hS hlen hres
    -- descend
    obtain ⟨T1, L2, hr1, hl2, hp1⟩ := fr_step_descend hd4 ks' ctx L1 [] hl hS (by omega)
    have hdl : (descendCtx ks' ctx).length = kinds.length := by simp [descendCtx]; omega
    -- evaluate the leaf
    have hmr' : L2 mr = (toksV mv).reverse := by
      rw [hp1.2.2.2.2 mr (Ne.symm n5) (Ne.symm n10) (Ne.symm n14) (Ne.symm n19)]; exact hmr
    have hmr2' : L2 mr2 = [] := by
      rw [hp1.2.2.2.2 mr2 (Ne.symm n6) (Ne.symm n11) (Ne.symm n15) (Ne.symm n20)]; exact hmr2
    have hft' : L2 ft = [] := by
      rw [hp1.2.2.2.2 ft (Ne.symm n3) (Ne.symm n8) (Ne.symm n12) n16]; exact hft
    have hvs' : L2 vs = stackL (fun b : Bool => if b then 1 else 0) ([] : List Bool) := by
      rw [hp1.2.2.2.1]; rfl
    obtain ⟨T2, hr2⟩ := evalLeaf_spec hd5 (B := B) mv ((descendCtx ks' ctx).map Prod.snd) [] hmr' hmr2'
      hp1.2.2.1 hft' hvs' hl2 hBt (by simp [hdl]; omega) (by simp; omega)
    have hev := evalV_length_le (((descendCtx ks' ctx).map Prod.snd).map Frame.bit) mv []
    have hl3 : LenOK B (L2.set vs (stackL (fun b : Bool => if b then 1 else 0)
        (evalV (((descendCtx ks' ctx).map Prod.snd).map Frame.bit) mv []))) :=
      lenOK_set hl2 vs (by simp [stackL_length] at hev ⊢; omega)
    have hp3 := fr_S4.set_vs hd4 hp1 (stackL (fun b : Bool => if b then 1 else 0)
        (evalV (((descendCtx ks' ctx).map Prod.snd).map Frame.bit) mv []))
    -- normalize
    obtain ⟨T3, L4, hr3, hl4, hp4⟩ := fr_step_normalize hd4 hl3 (st := evalV (((descendCtx ks' ctx).map Prod.snd).map
      Frame.bit) mv []) hp3 (by simp at hev ⊢; omega)
    -- return
    obtain ⟨T4, L5, hr4, hl5, ctx2, ks2, v2, hs, hf, he, hlen2, hp5⟩ :=
      fr_step_return hd4 mv (descendCtx ks' ctx) [] _ L4 hl4 hp4 (by simp [hdl]; omega)
    have hbits : ((descendCtx ks' ctx).map Prod.snd).map Frame.bit = bitsOf (descendCtx ks' ctx) := by
      simp [bitsOf, List.map_map, Function.comp_def]
    have hfd := fin_descend mv ks' ctx
    have hv0 : (evalV (((descendCtx ks' ctx).map Prod.snd).map Frame.bit) mv []).headD false =
        qEvalV mv [] (bitsOf (descendCtx ks' ctx)) := by
      rw [hbits]; rfl
    rw [hv0] at hf
    have hext := extra_descend ks' ctx
    have hfres : v2 = qEvalV mv kinds [] ∨ ctx2 ≠ [] := by
      by_cases h0 : ctx2 = []
      · left
        subst h0
        have : res mv ctx ks' = v2 := by rw [hfd]; simpa [fin] using hf
        rw [← hres, this]
      · right; exact h0
    rcases hs with h0 | ⟨κ, ctx0, h0⟩
    · subst h0
      right
      have hc : nonEmpty (lastSym (L5 fr)) = false := by rw [hp5.2.2.1]; exact fr_nonEmpty_stack_nil _
      refine ⟨v2, L5, _, Runs.seqH hr1 (Runs.seqH hr2 (Runs.seqH hr3 (Runs.seqH hr4
        (Halts.iteF hl5 hc (fr_halts_answer hl5 hp5))))), ?_⟩
      rcases hfres with h | h
      · exact h
      · exact absurd rfl h
    · subst h0
      left
      have hc : nonEmpty (lastSym (L5 fr)) = true := by rw [hp5.2.2.1]; exact fr_nonEmpty_stack_cons _ _ _
      have hl2' : ctx0.length + 3 ≤ B := by simp at hlen2; omega
      obtain ⟨T6, L6, hr6, hl6, hp6⟩ := fr_step_refresh hd4 hl5 (v := v2) (by simpa using hp5) hl2'
      refine ⟨((κ, Frame.second v2) :: ctx0, ks2), L6, _, Runs.seq hr1 (Runs.seq hr2 (Runs.seq hr3
        (Runs.seq hr4 (Runs.iteT hl5 hc hr6)))), ⟨hl6, hp6, ?_, ?_⟩, ?_⟩
      · simp at hlen2 ⊢; omega
      · dsimp only
        rw [← res_refresh, ← hf, ← hfd]; exact hres
      · show cnt ((κ, Frame.second v2) :: ctx0) ks2.length < cnt ctx ks'.length
        have hext' : extra (descendCtx ks' ctx) 0 + 1 = 2 ^ ks'.length + extra ctx ks'.length := hext
        simp only [List.length_nil] at he
        simp only [extra] at he ⊢
        simp only [cnt, extra]
        omega
  · refine ⟨hB, ⟨hks, by rw [hku]; rfl, by rw [hfr]; rfl, hvs, fun x _ _ _ _ => rfl⟩, by simp, ?_⟩
    simp [res, fin, bitsOf]

end Complexity
