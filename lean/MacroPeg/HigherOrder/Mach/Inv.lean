import MacroPeg.HigherOrder.Mach.Steps
import MacroPeg.HigherOrder.Mach.VarTy

/-!
# What every state of the reading machine satisfies

`MInv`: the tables are well formed, the current context exists, and every type number (on the type stack, among
the rule types, and as the binder type of a pending frame `9`) names an arrow already registered; every context number
of a pending frame `9` exists. It holds at the start (`minv_pinit`) and after every step (`pstep_minv`).

The tables grow by at most one entry per step: `size (pstep s) ≤ size s + 1` (`pstep_size`).
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.Flat

/-- The frames `9` of a control stack carry a type and a context that exist. -/
def ctlOK (nt nc : Nat) : List Nat → Prop
  | 9 :: a :: c :: K => a ≤ nt ∧ c ≤ nc ∧ ctlOK nt nc K
  | _ :: K => ctlOK nt nc K
  | [] => True

theorem ctlOK_cons {nt nc k : Nat} {K : List Nat} (hk : k ≠ 9) : ctlOK nt nc (k :: K) ↔ ctlOK nt nc K := by
  match K with
  | [] => simp [ctlOK]
  | [a] => simp [ctlOK]
  | a :: b :: K' => simp [ctlOK, hk]

theorem ctlOK_mono {nt nc nt' nc' : Nat} (ht : nt ≤ nt') (hc : nc ≤ nc') (K : List Nat) (h : ctlOK nt nc K) :
    ctlOK nt' nc' K := by
  fun_induction ctlOK nt nc K with
  | case1 a c K ih => exact ⟨by have := h.1; omega, by have := h.2.1; omega, ih h.2.2⟩
  | case2 k K hne ih =>
    rw [ctlOK.eq_def]
    split
    · rename_i a c K' heq
      exact absurd heq (by intro e; cases e; exact hne a c K' rfl rfl)
    · rename_i heq; cases heq; exact ih h
    · trivial
  | case3 => trivial

/-- The invariant of the reading machine. -/
structure MInv (s : PSt) : Prop where
  tt : TTWF s.tt
  ct : CTWF s.tt s.ct
  cur : s.cur ≤ s.ct.length
  ty : ∀ t ∈ s.ty, t ≤ s.tt.length
  rt : ∀ t ∈ s.rt, t ≤ s.tt.length
  ctl : ctlOK s.tt.length s.ct.length s.ctl

theorem MInv.fail {s : PSt} (h : MInv s) : MInv s.fail :=
  ⟨h.tt, h.ct, h.cur, h.ty, h.rt, trivial⟩

theorem MInv.leaf {s : PSt} (h : MInv s) {it : MItem} {τ : Nat} {r K : List Nat} (hτ : τ ≤ s.tt.length)
    (hK : ctlOK s.tt.length s.ct.length K) : MInv (s.leaf it τ r K) :=
  ⟨h.tt, h.ct, h.cur, fun t ht => (List.mem_cons.1 ht).elim (fun e => e ▸ hτ) (h.ty t), h.rt, hK⟩

/-- Changing only the tokens and the control stack. -/
theorem MInv.withCtl {s : PSt} (h : MInv s) {r K : List Nat} (hK : ctlOK s.tt.length s.ct.length K) :
    MInv { s with tk := r, ctl := K } :=
  ⟨h.tt, h.ct, h.cur, h.ty, h.rt, hK⟩

/-- The literals do not matter. -/
theorem MInv.withLt {s : PSt} (h : MInv s) (v : List (List Nat)) : MInv { s with lt := v } :=
  ⟨h.tt, h.ct, h.cur, h.ty, h.rt, h.ctl⟩

theorem varTy_le {tt ct : List (Nat × Nat)} (hc : CTWF tt ct) {c i τ : Nat} (hcl : c ≤ ct.length)
    (h : varTy ct c i = some τ) : τ ≤ tt.length := by
  rw [varTy_walk hc i c hcl] at h
  split at h
  · exact absurd h (by simp)
  · have hw := walkCtx_le hc c hcl i
    rw [List.getElem?_eq_getElem (by omega)] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]; exact (hc _ (by omega)).2

theorem readExpr_minv {s : PSt} {K : List Nat} (h : MInv s) (hK : ctlOK s.tt.length s.ct.length K) :
    MInv (readExpr s K) := by
  unfold readExpr
  repeat' split
  all_goals first
    | exact h.fail
    | exact h.leaf (Nat.zero_le _) hK
    | exact h.withCtl (by simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK_cons (show (1 : Nat) ≠ 9 by decide),
        ctlOK_cons (show (2 : Nat) ≠ 9 by decide), ctlOK_cons (show (4 : Nat) ≠ 9 by decide),
        ctlOK_cons (show (6 : Nat) ≠ 9 by decide), ctlOK_cons (show (7 : Nat) ≠ 9 by decide),
        ctlOK_cons (show (8 : Nat) ≠ 9 by decide), ctlOK_cons (show (10 : Nat) ≠ 9 by decide)]; exact hK)
    | exact h.leaf (varTy_le h.ct h.cur ‹_›) hK
    | exact h.leaf (h.rt _ (List.mem_of_getElem? ‹_›)) hK
    | exact (h.leaf (Nat.zero_le _) hK).withLt _
    | done

theorem MInv.ctlTail {s : PSt} (h : MInv s) {k : Nat} {K : List Nat} (hc : s.ctl = k :: K) (hk : k ≠ 9) :
    ctlOK s.tt.length s.ct.length K := by
  have := h.ctl; rw [hc] at this; exact (ctlOK_cons hk).1 this

/-- Changing the control stack, the types (to a part of the old ones, maybe with `0` on top) and the items. -/
theorem MInv.pop {s : PSt} (h : MInv s) {K ty' : List Nat} {o : List MItem}
    (hK : ctlOK s.tt.length s.ct.length K) (hty : ∀ t ∈ ty', t ≤ s.tt.length) :
    MInv { s with ctl := K, ty := ty', out := o } :=
  ⟨h.tt, h.ct, h.cur, hty, h.rt, hK⟩

theorem mem_tail_le {s : PSt} (h : MInv s) {a : Nat} {r : List Nat} (hty : s.ty = a :: r) :
    a ≤ s.tt.length ∧ ∀ t ∈ r, t ≤ s.tt.length :=
  ⟨h.ty a (by rw [hty]; exact List.mem_cons_self), fun t ht => h.ty t (by rw [hty]; exact List.mem_cons_of_mem _ ht)⟩

theorem zero_cons_le {n : Nat} {r : List Nat} (hr : ∀ t ∈ r, t ≤ n) : ∀ t ∈ 0 :: r, t ≤ n :=
  fun t ht => (List.mem_cons.1 ht).elim (fun e => e ▸ Nat.zero_le _) (hr t)

theorem readType_minv {s : PSt} {K : List Nat} (h : MInv s) (hK : ctlOK s.tt.length s.ct.length K) :
    MInv (readType s K) := by
  unfold readType
  split
  · exact ⟨h.tt, h.ct, h.cur, zero_cons_le h.ty, h.rt, hK⟩
  · exact h.withCtl (by simp only [ctlOK_cons (show (1 : Nat) ≠ 9 by decide),
      ctlOK_cons (show (12 : Nat) ≠ 9 by decide)]; exact hK)
  · exact h.fail

/-- Registering an arrow keeps the invariant. -/
theorem MInv.intern {s : PSt} (h : MInv s) {a b c : Nat} {K r : List Nat} {o : List MItem} (ha : a ≤ s.tt.length)
    (hb : b ≤ s.tt.length) (hc : c ≤ s.ct.length) (hr : ∀ t ∈ r, t ≤ s.tt.length)
    (hK : ctlOK s.tt.length s.ct.length K) :
    MInv { s with ctl := K, ty := (Mach.intern s.tt a b).2 :: r, tt := (Mach.intern s.tt a b).1, cur := c, out := o } := by
  obtain ⟨e, he⟩ := intern_prefix s.tt a b
  have hlen : s.tt.length ≤ (Mach.intern s.tt a b).1.length := by rw [he]; simp
  refine ⟨intern_wf h.tt ha hb, h.ct.grow ⟨e, he⟩, hc, ?_, fun t ht => Nat.le_trans (h.rt t ht) hlen,
    ctlOK_mono hlen (Nat.le_refl _) K hK⟩
  intro t ht
  rcases List.mem_cons.1 ht with rfl | ht
  · exact intern_snd_le _ _ _
  · exact Nat.le_trans (hr t ht) hlen

theorem pstep_minv {s : PSt} (h : MInv s) : MInv (pstep s) := by
  unfold pstep
  split
  next => exact h
  next K hc => exact readExpr_minv h (h.ctlTail hc (by decide))
  next K hc => exact readType_minv h (h.ctlTail hc (by decide))
  next K hc =>
    split
    · exact ⟨h.tt, h.ct, h.cur, h.ty, h.rt, by
        simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK_cons (show (3 : Nat) ≠ 9 by decide)]
        exact h.ctlTail hc (by decide)⟩
    · exact h.fail
  next K hc =>
    unfold binDone; split
    next r hty => exact h.pop (h.ctlTail hc (by decide)) (mem_tail_le h hty).2
    next => exact h.fail
  next K hc =>
    split
    · exact ⟨h.tt, h.ct, h.cur, h.ty, h.rt, by
        simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK_cons (show (5 : Nat) ≠ 9 by decide)]
        exact h.ctlTail hc (by decide)⟩
    · exact h.fail
  next K hc =>
    unfold binDone; split
    next r hty => exact h.pop (h.ctlTail hc (by decide)) (mem_tail_le h hty).2
    next => exact h.fail
  next K hc =>
    unfold unDone; split
    next r hty => exact h.pop (h.ctlTail hc (by decide)) (zero_cons_le (mem_tail_le h hty).2)
    next => exact h.fail
  next K hc =>
    unfold unDone; split
    next r hty => exact h.pop (h.ctlTail hc (by decide)) (zero_cons_le (mem_tail_le h hty).2)
    next => exact h.fail
  next K hc =>
    split
    next a r hty =>
      have ⟨ha, hr⟩ := mem_tail_le h hty
      have hK := h.ctlTail hc (by decide)
      refine ⟨h.tt, h.ct.snoc h.cur ha, by simp, hr, h.rt, ?_⟩
      simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK, List.length_append, List.length_singleton]
      exact ⟨ha, by have := h.cur; omega, ctlOK_mono (Nat.le_refl _) (by omega) K hK⟩
    next => exact h.fail
  next a c K hc =>
    split
    next σ r hty =>
      have ⟨hσ, hr⟩ := mem_tail_le h hty
      have hk := h.ctl; rw [hc] at hk; simp only [ctlOK] at hk
      exact h.intern hk.1 hσ hk.2.1 hr hk.2.2
    next => exact h.fail
  next K hc =>
    exact ⟨h.tt, h.ct, h.cur, h.ty, h.rt, by
      simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK_cons (show (11 : Nat) ≠ 9 by decide)]
      exact h.ctlTail hc (by decide)⟩
  next K hc =>
    split
    next α φ r hty =>
      have ⟨_, hr'⟩ := mem_tail_le h hty
      have hr : ∀ t ∈ r, t ≤ s.tt.length := fun t ht => hr' t (List.mem_cons_of_mem _ ht)
      split
      next k =>
        split
        next α' β hk =>
          split
          next =>
            have hlt : k < s.tt.length := (List.getElem?_eq_some_iff.1 hk).1
            have hβ : β ≤ s.tt.length := by
              have := (h.tt.2 k hlt).2
              rw [show s.tt[k] = (α', β) from (List.getElem?_eq_some_iff.1 hk).2] at this; simp at this; omega
            exact h.pop (h.ctlTail hc (by decide)) (fun t ht => (List.mem_cons.1 ht).elim (fun e => e ▸ hβ) (hr t))
          next => exact h.fail
        next => exact h.fail
      next => exact h.fail
    next => exact h.fail
  next K hc =>
    exact ⟨h.tt, h.ct, h.cur, h.ty, h.rt, by
      simp only [ctlOK_cons (show (1 : Nat) ≠ 9 by decide), ctlOK_cons (show (13 : Nat) ≠ 9 by decide)]
      exact h.ctlTail hc (by decide)⟩
  next K hc =>
    split
    next b a r hty =>
      have ⟨hb, hr'⟩ := mem_tail_le h hty
      have ha := hr' a List.mem_cons_self
      have hr : ∀ t ∈ r, t ≤ s.tt.length := fun t ht => hr' t (List.mem_cons_of_mem _ ht)
      exact h.intern (c := s.cur) (o := s.out) ha hb h.cur hr (h.ctlTail hc (by decide))
    next => exact h.fail
  next K hc =>
    have hK := h.ctlTail hc (by decide)
    split
    · exact h.withCtl (by simp only [ctlOK_cons (show (16 : Nat) ≠ 9 by decide)]; exact hK)
    · exact h.withCtl (by simp only [ctlOK_cons (show (1 : Nat) ≠ 9 by decide),
        ctlOK_cons (show (15 : Nat) ≠ 9 by decide)]; exact hK)
    · exact h.fail
  next K hc =>
    have hK := h.ctlTail hc (by decide)
    split
    next t r hty =>
      have ⟨ht, hr⟩ := mem_tail_le h hty
      refine ⟨h.tt, h.ct, h.cur, hr, ?_, by simp only [ctlOK_cons (show (14 : Nat) ≠ 9 by decide)]; exact hK⟩
      intro x hx; rcases List.mem_append.1 hx with hx | hx
      · exact h.rt x hx
      · rw [List.mem_singleton.1 hx]; exact ht
    next => exact h.fail
  next K hc =>
    have hK := h.ctlTail hc (by decide)
    repeat' split
    all_goals first
      | exact h.fail
      | exact ⟨h.tt, h.ct, Nat.zero_le _, h.ty, h.rt, by
          simp only [ctlOK_cons (show (0 : Nat) ≠ 9 by decide), ctlOK_cons (show (18 : Nat) ≠ 9 by decide),
            ctlOK_cons (show (17 : Nat) ≠ 9 by decide)]; exact hK⟩
  next K hc =>
    have hK := h.ctlTail hc (by decide)
    repeat' split
    all_goals first
      | exact h.fail
      | (rename_i σ r hty _; exact ⟨h.tt, h.ct, h.cur, (mem_tail_le h hty).2, h.rt, by
          simp only [ctlOK_cons (show (16 : Nat) ≠ 9 by decide)]; exact hK⟩)
  next K hc =>
    have hK := h.ctlTail hc (by decide)
    split
    next r hty =>
      split
      next => exact ⟨h.tt, h.ct, h.cur, (mem_tail_le h hty).2, h.rt, hK⟩
      next => exact h.fail
    next => exact h.fail
  next => exact h.fail


theorem minv_pinit (tk : List Nat) : MInv (pinit tk) :=
  ⟨TTWF.nil, fun k h => by simp [pinit] at h, by simp [pinit], by simp [pinit], by simp [pinit], by
    simp [pinit, ctlOK]⟩

theorem minv_pruns {s : PSt} (h : MInv s) : ∀ n, MInv (pruns s n)
  | 0 => h
  | n + 1 => by rw [pruns_succ]; exact minv_pruns (pstep_minv h) n

/-! ## The size of the tables -/

/-- The number of entries in all tables. -/
def tsize (s : PSt) : Nat := s.tt.length + s.ct.length + s.lt.length + s.rt.length + s.bodies.length

theorem intern_len_le (tt : List (Nat × Nat)) (a b : Nat) : (Mach.intern tt a b).1.length ≤ tt.length + 1 := by
  unfold Mach.intern; split <;> simp

set_option linter.unusedSimpArgs false in
theorem pstep_size (s : PSt) : tsize (pstep s) ≤ tsize s + 1 := by
  unfold pstep readExpr readType binDone unDone
  repeat' split
  all_goals first
    | (simp [tsize, PSt.fail, PSt.leaf]; done)
    | (simp [tsize, PSt.fail, PSt.leaf]; omega)
    | (simp only [tsize, Mach.intern]; split <;> simp <;> omega)
    | skip

theorem pruns_size (s : PSt) : ∀ n, tsize (pruns s n) ≤ tsize s + n
  | 0 => by simp [pruns]
  | n + 1 => by
    rw [pruns_succ]; have := pruns_size (pstep s) n; have := pstep_size s; omega

end Shallot.MacroPeg.Mach
