import MacroPeg.HigherOrder.Mach.ParseSpec

/-!
# Reading an expression

`readExpr_spec`: from a state whose next tokens are the code of `e` (as read by `parseE`) and whose control stack
asks for an expression, the machine reads `e`, types it in the current context, and emits its items — exactly what
`inferE` computes — or fails exactly when `inferE` fails. The proof follows `parseE`, one case per tag.
-/

namespace Shallot.MacroPeg.Mach

open Shallot.MacroPeg.HO
open Shallot.MacroPeg.Flat

/-! ## One step of each continuation -/

section Steps

variable (s : PSt) (K : List Nat)

theorem step_unDone_ok {tag : Nat} {r : List Nat} (hty : s.ty = 0 :: r) :
    unDone s tag K = { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out } := by
  simp [unDone, hty]

theorem step_unDone_fail {tag i : Nat} {r : List Nat} (hty : s.ty = i :: r) (hi : i ≠ 0) : unDone s tag K = s.fail := by
  unfold unDone; rw [hty]; split <;> simp_all

theorem step_binDone_ok {tag : Nat} {r : List Nat} (hty : s.ty = 0 :: 0 :: r) :
    binDone s tag K = { s with ctl := K, ty := 0 :: r, out := ⟨tag, 0, 0, s.cur⟩ :: s.out } := by
  simp [binDone, hty]

theorem step_binDone_fail {tag i : Nat} {r : List Nat} (hty : s.ty = i :: 0 :: r) (hi : i ≠ 0) :
    binDone s tag K = s.fail := by
  unfold binDone; rw [hty]; split <;> simp_all

end Steps

/-- Reading continues from a state that agrees with `s` except for the given fields. -/
theorem ctxOf_of_grow {s s' : PSt} (hg : Grows s.tt s.ct s.lt s'.tt s'.ct s'.lt) (hw : TTWF s.tt)
    (hc : CTWF s.tt s.ct) {Γ : List HO.Ty} (hΓ : ctxOf s.tt s.ct s.cur = some Γ) (hcur : s'.cur = s.cur) :
    ctxOf s'.tt s'.ct s'.cur = some Γ := by
  rw [hcur]; exact ctxOf_grow hw hc hg.tt hg.ct hΓ

/-- The induction hypothesis: reading any expression parsed with fuel `f`. -/
def IHFun (f : Nat) : Prop :=
  ∀ (l : List Nat) (e : HExp) (rest : List Nat), parseE f l = some (e, rest) →
    ∀ (s : PSt) (K : List Nat) (R Γ : List HO.Ty), s.tk = l → s.ctl = 0 :: K → TTWF s.tt → CTWF s.tt s.ct →
      s.rt.mapM (tyOf s.tt) = some R → ctxOf s.tt s.ct s.cur = some Γ → ExprRes s K rest l.length (inferE R Γ e)

/-- The parts of a finished read. -/
theorem ExprDone.parts {s : PSt} {K rest : List Nat} {n : Nat} {τ : HO.Ty} {is : List Item}
    (h : ExprDone s K rest n τ is) : ∃ s', Reach s s' n ∧ s'.tk = rest ∧ s'.ctl = K ∧ s'.cur = s.cur ∧
      s'.ok = s.ok ∧ s'.rt = s.rt ∧ s'.bodies = s.bodies ∧ s'.start = s.start ∧ s'.x = s.x ∧
      (∃ i, s'.ty = i :: s.ty ∧ tyOf s'.tt i = some τ) ∧
      (∃ outE, s'.out = outE.reverse ++ s.out ∧ itemsOf s'.tt s'.ct s'.lt outE = some is) ∧
      Grows s.tt s.ct s.lt s'.tt s'.ct s'.lt ∧ TTWF s'.tt ∧ CTWF s'.tt s'.ct := h

/-- **`seq`**: read both operands (parsers), then emit the operator. -/
theorem seq_case {f : Nat} (ih : IHFun f) {l l₁ rest : List Nat} {a b : HExp} (ha : parseE f l = some (a, l₁))
    (hb : parseE f l₁ = some (b, rest)) {s : PSt} {K : List Nat} {R Γ : List HO.Ty} (htk : s.tk = 5 :: l)
    (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct) (hR : s.rt.mapM (tyOf s.tt) = some R)
    (hΓ : ctxOf s.tt s.ct s.cur = some Γ) : ExprRes s K rest (l.length + 1) (inferE R Γ (.seq a b)) := by
  let s₁ : PSt := { s with tk := l, ctl := 0 :: 2 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  have hA := ih l a l₁ ha s₁ (2 :: K) R Γ rfl rfl hw hc hR hΓ
  cases hia : inferE R Γ a with
  | none =>
    rw [hia] at hA
    have : inferE R Γ (.seq a b) = none := by simp [inferE, hia]
    rw [this]; exact Fails.of_reach x₁ hA
  | some pa =>
    obtain ⟨τa, ia⟩ := pa
    rw [hia] at hA
    obtain ⟨n₁, hd₁, hn₁⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨i₁, hty₂, hτ₁⟩, ⟨oA, hout₂, hoA⟩, hg₂, hw₂,
      hc₂⟩ := hd₁.parts
    by_cases hp : τa = .p
    · subst hp
      obtain rfl : i₁ = 0 := tyOf_eq_p hτ₁
      let s₃ : PSt := { s₂ with ctl := 0 :: 3 :: K }
      have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, hctl₂, hty₂, s₃]
      have hR₂ : s₂.rt.mapM (tyOf s₂.tt) = some R := by rw [hrt₂]; exact mapM_tyOf_grow hw hg₂.tt hR
      have hΓ₂ : ctxOf s₂.tt s₂.ct s₂.cur = some Γ := ctxOf_of_grow hg₂ hw hc hΓ hcur₂
      have hB := ih l₁ b rest hb s₃ (3 :: K) R Γ htk₂ rfl hw₂ hc₂ hR₂ hΓ₂
      cases hib : inferE R Γ b with
      | none =>
        rw [hib] at hB
        have : inferE R Γ (.seq a b) = none := by simp [inferE, hia, hib]
        rw [this]; exact Fails.of_reach ((x₁.trans x₂).trans x₃) hB
      | some pb =>
        obtain ⟨τb, ib⟩ := pb
        rw [hib] at hB
        obtain ⟨n₂, hd₂, hn₂⟩ := hB
        obtain ⟨s₄, x₄, htk₄, hctl₄, hcur₄, hok₄, hrt₄, hbo₄, hst₄, hx₄, ⟨i₂, hty₄, hτ₂⟩, ⟨oB, hout₄, hoB⟩, hg₄,
          hw₄, hc₄⟩ := hd₂.parts
        by_cases hq : τb = .p
        · subst hq
          obtain rfl : i₂ = 0 := tyOf_eq_p hτ₂
          have hty₄' : s₄.ty = 0 :: 0 :: s.ty := by rw [hty₄, show s₃.ty = s₂.ty from rfl, hty₂]
          let s₅ : PSt := { s₄ with ctl := K, ty := 0 :: s.ty, out := ⟨5, 0, 0, s₄.cur⟩ :: s₄.out }
          have x₅ : Reach s₄ s₅ 1 := by
            show pstep s₄ = s₅; simp only [pstep, hctl₄]; rw [step_binDone_ok s₄ K hty₄']
          have hval : inferE R Γ (.seq a b) = some (.p, ia ++ ib ++ [⟨.seq, Γ⟩]) := by simp [inferE, hia, hib]
          rw [hval]
          have hg : Grows s.tt s.ct s.lt s₄.tt s₄.ct s₄.lt := hg₂.trans hg₄
          have hcur₄' : s₄.cur = s.cur := by rw [hcur₄]; exact hcur₂
          refine ⟨1 + n₁ + 1 + n₂ + 1, ⟨s₅, (((x₁.trans x₂).trans x₃).trans x₄).trans x₅, htk₄, rfl, hcur₄',
            by rw [← hok₂]; exact hok₄, by rw [← hrt₂]; exact hrt₄, by rw [← hbo₂]; exact hbo₄,
            by rw [← hst₂]; exact hst₄, by rw [← hx₂]; exact hx₄, ⟨0, rfl, by rw [tyOf]⟩,
            ⟨oA ++ oB ++ [⟨5, 0, 0, s₄.cur⟩], ?_, ?_⟩, hg, hw₄, hc₄⟩, ?_⟩
          · show ⟨5, 0, 0, s₄.cur⟩ :: s₄.out = _
            rw [hout₄, show s₃.out = s₂.out from rfl, hout₂, show s₁.out = s.out from rfl]; simp
          · refine itemsOf_append (itemsOf_append (itemsOf_grow hw₂ hc₂ hg₄ hoA) hoB)
              (itemsOf_single (itemOf_mk rfl ?_))
            exact ctxOf_of_grow (s := s₂) hg₄ hw₂ hc₂ hΓ₂ hcur₄
          · omega
        · have hi₂ : i₂ ≠ 0 := fun h => hq (by subst h; rw [tyOf] at hτ₂; exact (Option.some.inj hτ₂).symm)
          have hty₄' : s₄.ty = i₂ :: 0 :: s.ty := by rw [hty₄, show s₃.ty = s₂.ty from rfl, hty₂]
          have hval : inferE R Γ (.seq a b) = none := by
            simp only [inferE, hia, hib]; cases τb <;> simp_all
          rw [hval]
          refine Fails.of_reach ((((x₁.trans x₂).trans x₃).trans x₄)) (Fails.of_step ?_)
          simp only [pstep, hctl₄]; rw [step_binDone_fail s₄ K hty₄' hi₂]; exact Fails.fail _
    · have hi₁ : i₁ ≠ 0 := fun h => hp (by subst h; rw [tyOf] at hτ₁; exact (Option.some.inj hτ₁).symm)
      have hval : inferE R Γ (.seq a b) = none := by
        simp only [inferE, hia]; cases τa <;> simp_all
      rw [hval]
      refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
      simp only [pstep, hctl₂, hty₂]
      cases i₁ with
      | zero => exact absurd rfl hi₁
      | succ k => exact Fails.fail _

/-- **`alt`**: the same as `seq`, with its own frames and tag. -/
theorem alt_case {f : Nat} (ih : IHFun f) {l l₁ rest : List Nat} {a b : HExp} (ha : parseE f l = some (a, l₁))
    (hb : parseE f l₁ = some (b, rest)) {s : PSt} {K : List Nat} {R Γ : List HO.Ty} (htk : s.tk = 6 :: l)
    (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct) (hR : s.rt.mapM (tyOf s.tt) = some R)
    (hΓ : ctxOf s.tt s.ct s.cur = some Γ) : ExprRes s K rest (l.length + 1) (inferE R Γ (.alt a b)) := by
  let s₁ : PSt := { s with tk := l, ctl := 0 :: 4 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  have hA := ih l a l₁ ha s₁ (4 :: K) R Γ rfl rfl hw hc hR hΓ
  cases hia : inferE R Γ a with
  | none =>
    rw [hia] at hA
    have : inferE R Γ (.alt a b) = none := by simp [inferE, hia]
    rw [this]; exact Fails.of_reach x₁ hA
  | some pa =>
    obtain ⟨τa, ia⟩ := pa
    rw [hia] at hA
    obtain ⟨n₁, hd₁, hn₁⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨i₁, hty₂, hτ₁⟩, ⟨oA, hout₂, hoA⟩, hg₂, hw₂,
      hc₂⟩ := hd₁.parts
    by_cases hp : τa = .p
    · subst hp
      obtain rfl : i₁ = 0 := tyOf_eq_p hτ₁
      let s₃ : PSt := { s₂ with ctl := 0 :: 5 :: K }
      have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, hctl₂, hty₂, s₃]
      have hR₂ : s₂.rt.mapM (tyOf s₂.tt) = some R := by rw [hrt₂]; exact mapM_tyOf_grow hw hg₂.tt hR
      have hΓ₂ : ctxOf s₂.tt s₂.ct s₂.cur = some Γ := ctxOf_of_grow hg₂ hw hc hΓ hcur₂
      have hB := ih l₁ b rest hb s₃ (5 :: K) R Γ htk₂ rfl hw₂ hc₂ hR₂ hΓ₂
      cases hib : inferE R Γ b with
      | none =>
        rw [hib] at hB
        have : inferE R Γ (.alt a b) = none := by simp [inferE, hia, hib]
        rw [this]; exact Fails.of_reach ((x₁.trans x₂).trans x₃) hB
      | some pb =>
        obtain ⟨τb, ib⟩ := pb
        rw [hib] at hB
        obtain ⟨n₂, hd₂, hn₂⟩ := hB
        obtain ⟨s₄, x₄, htk₄, hctl₄, hcur₄, hok₄, hrt₄, hbo₄, hst₄, hx₄, ⟨i₂, hty₄, hτ₂⟩, ⟨oB, hout₄, hoB⟩, hg₄,
          hw₄, hc₄⟩ := hd₂.parts
        by_cases hq : τb = .p
        · subst hq
          obtain rfl : i₂ = 0 := tyOf_eq_p hτ₂
          have hty₄' : s₄.ty = 0 :: 0 :: s.ty := by rw [hty₄, show s₃.ty = s₂.ty from rfl, hty₂]
          let s₅ : PSt := { s₄ with ctl := K, ty := 0 :: s.ty, out := ⟨6, 0, 0, s₄.cur⟩ :: s₄.out }
          have x₅ : Reach s₄ s₅ 1 := by
            show pstep s₄ = s₅; simp only [pstep, hctl₄]; rw [step_binDone_ok s₄ K hty₄']
          have hval : inferE R Γ (.alt a b) = some (.p, ia ++ ib ++ [⟨.alt, Γ⟩]) := by simp [inferE, hia, hib]
          rw [hval]
          have hg : Grows s.tt s.ct s.lt s₄.tt s₄.ct s₄.lt := hg₂.trans hg₄
          have hcur₄' : s₄.cur = s.cur := by rw [hcur₄]; exact hcur₂
          refine ⟨1 + n₁ + 1 + n₂ + 1, ⟨s₅, (((x₁.trans x₂).trans x₃).trans x₄).trans x₅, htk₄, rfl, hcur₄',
            by rw [← hok₂]; exact hok₄, by rw [← hrt₂]; exact hrt₄, by rw [← hbo₂]; exact hbo₄,
            by rw [← hst₂]; exact hst₄, by rw [← hx₂]; exact hx₄, ⟨0, rfl, by rw [tyOf]⟩,
            ⟨oA ++ oB ++ [⟨6, 0, 0, s₄.cur⟩], ?_, ?_⟩, hg, hw₄, hc₄⟩, ?_⟩
          · show ⟨6, 0, 0, s₄.cur⟩ :: s₄.out = _
            rw [hout₄, show s₃.out = s₂.out from rfl, hout₂, show s₁.out = s.out from rfl]; simp
          · refine itemsOf_append (itemsOf_append (itemsOf_grow hw₂ hc₂ hg₄ hoA) hoB)
              (itemsOf_single (itemOf_mk rfl ?_))
            exact ctxOf_of_grow (s := s₂) hg₄ hw₂ hc₂ hΓ₂ hcur₄
          · omega
        · have hi₂ : i₂ ≠ 0 := fun h => hq (by subst h; rw [tyOf] at hτ₂; exact (Option.some.inj hτ₂).symm)
          have hty₄' : s₄.ty = i₂ :: 0 :: s.ty := by rw [hty₄, show s₃.ty = s₂.ty from rfl, hty₂]
          have hval : inferE R Γ (.alt a b) = none := by
            simp only [inferE, hia, hib]; cases τb <;> simp_all
          rw [hval]
          refine Fails.of_reach ((((x₁.trans x₂).trans x₃).trans x₄)) (Fails.of_step ?_)
          simp only [pstep, hctl₄]; rw [step_binDone_fail s₄ K hty₄' hi₂]; exact Fails.fail _
    · have hi₁ : i₁ ≠ 0 := fun h => hp (by subst h; rw [tyOf] at hτ₁; exact (Option.some.inj hτ₁).symm)
      have hval : inferE R Γ (.alt a b) = none := by
        simp only [inferE, hia]; cases τa <;> simp_all
      rw [hval]
      refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
      simp only [pstep, hctl₂, hty₂]
      cases i₁ with
      | zero => exact absurd rfl hi₁
      | succ k => exact Fails.fail _

/-- **`star`**: read the operand (a parser), then emit the operator. -/
theorem star_case {f : Nat} (ih : IHFun f) {l rest : List Nat} {a : HExp} (ha : parseE f l = some (a, rest))
    {s : PSt} {K : List Nat} {R Γ : List HO.Ty} (htk : s.tk = 7 :: l)
    (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct) (hR : s.rt.mapM (tyOf s.tt) = some R)
    (hΓ : ctxOf s.tt s.ct s.cur = some Γ) : ExprRes s K rest (l.length + 1) (inferE R Γ (.star a)) := by
  let s₁ : PSt := { s with tk := l, ctl := 0 :: 6 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  have hA := ih l a rest ha s₁ (6 :: K) R Γ rfl rfl hw hc hR hΓ
  cases hia : inferE R Γ a with
  | none =>
    rw [hia] at hA
    have : inferE R Γ (.star a) = none := by simp [inferE, hia]
    rw [this]; exact Fails.of_reach x₁ hA
  | some pa =>
    obtain ⟨τa, ia⟩ := pa
    rw [hia] at hA
    obtain ⟨n₁, hd₁, hn₁⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨i₁, hty₂, hτ₁⟩, ⟨oA, hout₂, hoA⟩, hg₂, hw₂,
      hc₂⟩ := hd₁.parts
    by_cases hp : τa = .p
    · subst hp
      obtain rfl : i₁ = 0 := tyOf_eq_p hτ₁
      have hty₂' : s₂.ty = 0 :: s.ty := hty₂
      let s₃ : PSt := { s₂ with ctl := K, ty := 0 :: s.ty, out := ⟨7, 0, 0, s₂.cur⟩ :: s₂.out }
      have x₃ : Reach s₂ s₃ 1 := by
        show pstep s₂ = s₃; simp only [pstep, hctl₂]; rw [step_unDone_ok s₂ K hty₂']
      have hval : inferE R Γ (.star a) = some (.p, ia ++ [⟨.star, Γ⟩]) := by simp [inferE, hia]
      rw [hval]
      refine ⟨1 + n₁ + 1, ⟨s₃, (x₁.trans x₂).trans x₃, htk₂, rfl, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂,
        ⟨0, rfl, by rw [tyOf]⟩, ⟨oA ++ [⟨7, 0, 0, s₂.cur⟩], ?_, ?_⟩, hg₂, hw₂, hc₂⟩, by omega⟩
      · show ⟨7, 0, 0, s₂.cur⟩ :: s₂.out = _
        rw [hout₂, show s₁.out = s.out from rfl]; simp
      · exact itemsOf_append hoA (itemsOf_single (itemOf_mk rfl (ctxOf_of_grow (s := s₁) hg₂ hw hc hΓ hcur₂)))
    · have hi₁ : i₁ ≠ 0 := fun h => hp (by subst h; rw [tyOf] at hτ₁; exact (Option.some.inj hτ₁).symm)
      have hval : inferE R Γ (.star a) = none := by
        simp only [inferE, hia]; cases τa <;> simp_all
      rw [hval]
      refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
      simp only [pstep, hctl₂]; rw [step_unDone_fail s₂ K hty₂ hi₁]; exact Fails.fail _

/-- **`!`**: the same as `star`, with its own frame and tag. -/
theorem notP_case {f : Nat} (ih : IHFun f) {l rest : List Nat} {a : HExp} (ha : parseE f l = some (a, rest))
    {s : PSt} {K : List Nat} {R Γ : List HO.Ty} (htk : s.tk = 8 :: l)
    (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct) (hR : s.rt.mapM (tyOf s.tt) = some R)
    (hΓ : ctxOf s.tt s.ct s.cur = some Γ) : ExprRes s K rest (l.length + 1) (inferE R Γ (.notP a)) := by
  let s₁ : PSt := { s with tk := l, ctl := 0 :: 7 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  have hA := ih l a rest ha s₁ (7 :: K) R Γ rfl rfl hw hc hR hΓ
  cases hia : inferE R Γ a with
  | none =>
    rw [hia] at hA
    have : inferE R Γ (.notP a) = none := by simp [inferE, hia]
    rw [this]; exact Fails.of_reach x₁ hA
  | some pa =>
    obtain ⟨τa, ia⟩ := pa
    rw [hia] at hA
    obtain ⟨n₁, hd₁, hn₁⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨i₁, hty₂, hτ₁⟩, ⟨oA, hout₂, hoA⟩, hg₂, hw₂,
      hc₂⟩ := hd₁.parts
    by_cases hp : τa = .p
    · subst hp
      obtain rfl : i₁ = 0 := tyOf_eq_p hτ₁
      have hty₂' : s₂.ty = 0 :: s.ty := hty₂
      let s₃ : PSt := { s₂ with ctl := K, ty := 0 :: s.ty, out := ⟨8, 0, 0, s₂.cur⟩ :: s₂.out }
      have x₃ : Reach s₂ s₃ 1 := by
        show pstep s₂ = s₃; simp only [pstep, hctl₂]; rw [step_unDone_ok s₂ K hty₂']
      have hval : inferE R Γ (.notP a) = some (.p, ia ++ [⟨.notP, Γ⟩]) := by simp [inferE, hia]
      rw [hval]
      refine ⟨1 + n₁ + 1, ⟨s₃, (x₁.trans x₂).trans x₃, htk₂, rfl, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂,
        ⟨0, rfl, by rw [tyOf]⟩, ⟨oA ++ [⟨8, 0, 0, s₂.cur⟩], ?_, ?_⟩, hg₂, hw₂, hc₂⟩, by omega⟩
      · show ⟨8, 0, 0, s₂.cur⟩ :: s₂.out = _
        rw [hout₂, show s₁.out = s.out from rfl]; simp
      · exact itemsOf_append hoA (itemsOf_single (itemOf_mk rfl (ctxOf_of_grow (s := s₁) hg₂ hw hc hΓ hcur₂)))
    · have hi₁ : i₁ ≠ 0 := fun h => hp (by subst h; rw [tyOf] at hτ₁; exact (Option.some.inj hτ₁).symm)
      have hval : inferE R Γ (.notP a) = none := by
        simp only [inferE, hia]; cases τa <;> simp_all
      rw [hval]
      refine Fails.of_reach (x₁.trans x₂) (Fails.of_step ?_)
      simp only [pstep, hctl₂]; rw [step_unDone_fail s₂ K hty₂ hi₁]; exact Fails.fail _

theorem tyOf_arrow_inv {tt : List (Nat × Nat)} {i : Nat} {a b : HO.Ty} (h : tyOf tt i = some (a ⇒ b)) :
    ∃ m x y, i = m + 1 ∧ tt[m]? = some (x, y) ∧ tyOf tt x = some a ∧ tyOf tt y = some b := by
  cases i with
  | zero => rw [tyOf] at h; cases h
  | succ m =>
    rw [tyOf] at h
    split at h
    · rename_i x y hm
      split at h
      · split at h
        · rename_i σ τ hσ hτ
          simp only [Option.some.injEq, HO.Ty.arr.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨m, x, y, rfl, hm, hσ, hτ⟩
        · cases h
      · cases h
    · cases h

theorem tyOf_eq_of_eq {tt : List (Nat × Nat)} (hw : TTWF tt) {i i' : Nat} {τ : HO.Ty} (h : tyOf tt i = some τ)
    (h' : tyOf tt i' = some τ) : i = i' :=
  tyOf_inj hw (i + i') i i' (Nat.le_refl _) (tyOf_le h) (tyOf_le h') τ h h'

/-- **A lambda**: read the binder type, read the body in the extended context, emit, register the arrow. -/
theorem lam_case {f : Nat} (ih : IHFun f) {l l₁ rest : List Nat} {τ : HO.Ty} {body : HExp}
    (hτp : parseTy f l = some (τ, l₁)) (hb : parseE f l₁ = some (body, rest)) {s : PSt} {K : List Nat}
    {R Γ : List HO.Ty} (htk : s.tk = 11 :: l) (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct)
    (hR : s.rt.mapM (tyOf s.tt) = some R) (hΓ : ctxOf s.tt s.ct s.cur = some Γ) :
    ExprRes s K rest (l.length + 1) (inferE R Γ (.lam τ body)) := by
  let s₁ : PSt := { s with tk := l, ctl := 1 :: 8 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  obtain ⟨n₁, tt₁, i₁, x₂, hw₁, he₁, hi₁, hτ₁, hn₁⟩ := readType_ok f l τ l₁ hτp s₁ (8 :: K) rfl rfl hw
  let s₂ : PSt := { s₁ with tk := l₁, ctl := 8 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
  let s₃ : PSt :=
    { s₂ with
      ctl := 0 :: 9 :: i₁ :: s.cur :: K
      ty := s.ty
      ct := s.ct ++ [(s.cur, i₁)]
      cur := s.ct.length + 1 }
  have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃, s₁]
  have hcl : s.cur ≤ s.ct.length := ctxOf_le hΓ
  have hc₁ : CTWF tt₁ s.ct := hc.grow he₁
  have hΓ₁ : ctxOf tt₁ s.ct s.cur = some Γ := ctxOf_grow hw hc he₁ ⟨[], (List.append_nil _).symm⟩ hΓ
  have hc₃ : CTWF s₃.tt s₃.ct := hc₁.snoc hcl hi₁
  have hΓ₃ : ctxOf s₃.tt s₃.ct s₃.cur = some (τ :: Γ) := ctxOf_snoc hw₁ hc₁ hcl hΓ₁ hτ₁
  have hR₃ : s₃.rt.mapM (tyOf s₃.tt) = some R := mapM_tyOf_grow hw he₁ hR
  have hB := ih l₁ body rest hb s₃ (9 :: i₁ :: s.cur :: K) R (τ :: Γ) rfl rfl hw₁ hc₃ hR₃ hΓ₃
  cases hib : inferE R (τ :: Γ) body with
  | none =>
    rw [hib] at hB
    have : inferE R Γ (.lam τ body) = none := by simp [inferE, hib]
    rw [this]; exact Fails.of_reach ((x₁.trans x₂).trans x₃) hB
  | some pb =>
    obtain ⟨σ, ib⟩ := pb
    rw [hib] at hB
    obtain ⟨n₂, hd₂, hn₂⟩ := hB
    obtain ⟨s₄, x₄, htk₄, hctl₄, hcur₄, hok₄, hrt₄, hbo₄, hst₄, hx₄, ⟨j, hty₄, hσ⟩, ⟨oB, hout₄, hoB⟩, hg₄,
      hw₄, hc₄⟩ := hd₂.parts
    have hτ₄ : tyOf s₄.tt i₁ = some τ := tyOf_grow hw₁ hg₄.tt hτ₁
    let s₅ : PSt :=
      { s₄ with
        ctl := K
        ty := (intern s₄.tt i₁ j).2 :: s.ty
        tt := (intern s₄.tt i₁ j).1
        cur := s.cur
        out := ⟨11, i₁, j, s.cur⟩ :: s₄.out }
    have x₅ : Reach s₄ s₅ 1 := by
      show pstep s₄ = s₅
      simp only [pstep, hctl₄, hty₄]; rfl
    have hval : inferE R Γ (.lam τ body) = some (τ ⇒ σ, ib ++ [⟨.lam τ σ, Γ⟩]) := by simp [inferE, hib]
    rw [hval]
    have hgi : ∃ e, s₅.tt = s₄.tt ++ e := intern_prefix _ _ _
    have hw₅ : TTWF s₅.tt := intern_wf hw₄ (tyOf_le hτ₄) (tyOf_le hσ)
    have hg₅ : Grows s₄.tt s₄.ct s₄.lt s₅.tt s₅.ct s₅.lt := ⟨hgi, ⟨[], (List.append_nil _).symm⟩, ⟨[], (List.append_nil _).symm⟩⟩
    have hg₃ : Grows s.tt s.ct s.lt s₃.tt s₃.ct s₃.lt := ⟨he₁, ⟨[(s.cur, i₁)], rfl⟩, ⟨[], (List.append_nil _).symm⟩⟩
    refine ⟨1 + n₁ + 1 + n₂ + 1, ⟨s₅, (((x₁.trans x₂).trans x₃).trans x₄).trans x₅, htk₄, rfl, rfl, hok₄, hrt₄,
      hbo₄, hst₄, hx₄, ⟨_, rfl, tyOf_intern hw₄ (tyOf_le hτ₄) (tyOf_le hσ) hτ₄ hσ⟩,
      ⟨oB ++ [⟨11, i₁, j, s.cur⟩], ?_, ?_⟩, (hg₃.trans hg₄).trans hg₅, hw₅, hc₄.grow hgi⟩, by omega⟩
    · show ⟨11, i₁, j, s.cur⟩ :: s₄.out = _
      rw [hout₄]; simp; rfl
    · refine itemsOf_append (itemsOf_grow hw₄ hc₄ hg₅ hoB) (itemsOf_single (itemOf_mk ?_ ?_))
      · show opOf s₅.tt s₅.lt ⟨11, i₁, j, s.cur⟩ = some (.lam τ σ)
        simp [opOf, tyOf_grow hw₄ hgi hτ₄, tyOf_grow hw₄ hgi hσ]
      · show ctxOf s₅.tt s₅.ct s.cur = some Γ
        have hΓ₃' : ctxOf s₃.tt s₃.ct s.cur = some Γ := ctxOf_grow hw₁ hc₁ ⟨[], (List.append_nil _).symm⟩ ⟨_, rfl⟩ hΓ₁
        exact ctxOf_grow hw₄ hc₄ hgi ⟨[], (List.append_nil _).symm⟩ (ctxOf_grow hw₁ hc₃ hg₄.tt hg₄.ct hΓ₃')

/-- **An application**: read the function, read the argument, check the argument type, emit. -/
theorem app_case {f : Nat} (ih : IHFun f) {l l₁ rest : List Nat} {fe ye : HExp} (hf : parseE f l = some (fe, l₁))
    (hy : parseE f l₁ = some (ye, rest)) {s : PSt} {K : List Nat} {R Γ : List HO.Ty} (htk : s.tk = 12 :: l)
    (hctl : s.ctl = 0 :: K) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct) (hR : s.rt.mapM (tyOf s.tt) = some R)
    (hΓ : ctxOf s.tt s.ct s.cur = some Γ) : ExprRes s K rest (l.length + 1) (inferE R Γ (.app fe ye)) := by
  let s₁ : PSt := { s with tk := l, ctl := 0 :: 10 :: K }
  have x₁ : Reach s s₁ 1 := by show pstep s = s₁; simp [pstep, hctl, readExpr, htk, s₁]
  have hA := ih l fe l₁ hf s₁ (10 :: K) R Γ rfl rfl hw hc hR hΓ
  cases hif : inferE R Γ fe with
  | none =>
    rw [hif] at hA
    have : inferE R Γ (.app fe ye) = none := by simp [inferE, hif]
    rw [this]; exact Fails.of_reach x₁ hA
  | some pf =>
    obtain ⟨φ, i_f⟩ := pf
    rw [hif] at hA
    obtain ⟨n₁, hd₁, hn₁⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, hok₂, hrt₂, hbo₂, hst₂, hx₂, ⟨k₁, hty₂, hφ⟩, ⟨oA, hout₂, hoA⟩, hg₂, hw₂,
      hc₂⟩ := hd₁.parts
    let s₃ : PSt := { s₂ with ctl := 0 :: 11 :: K }
    have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, hctl₂, s₃]
    have hR₂ : s₂.rt.mapM (tyOf s₂.tt) = some R := by rw [hrt₂]; exact mapM_tyOf_grow hw hg₂.tt hR
    have hΓ₂ : ctxOf s₂.tt s₂.ct s₂.cur = some Γ := ctxOf_of_grow hg₂ hw hc hΓ hcur₂
    have hB := ih l₁ ye rest hy s₃ (11 :: K) R Γ htk₂ rfl hw₂ hc₂ hR₂ hΓ₂
    cases hiy : inferE R Γ ye with
    | none =>
      rw [hiy] at hB
      have : inferE R Γ (.app fe ye) = none := by cases φ <;> simp [inferE, hif, hiy]
      rw [this]; exact Fails.of_reach ((x₁.trans x₂).trans x₃) hB
    | some py =>
      obtain ⟨α, iy⟩ := py
      rw [hiy] at hB
      obtain ⟨n₂, hd₂, hn₂⟩ := hB
      obtain ⟨s₄, x₄, htk₄, hctl₄, hcur₄, hok₄, hrt₄, hbo₄, hst₄, hx₄, ⟨k₂, hty₄, hα⟩, ⟨oB, hout₄, hoB⟩, hg₄,
        hw₄, hc₄⟩ := hd₂.parts
      have hty₄' : s₄.ty = k₂ :: k₁ :: s.ty := by rw [hty₄, show s₃.ty = s₂.ty from rfl, hty₂]
      have hφ₄ : tyOf s₄.tt k₁ = some φ := tyOf_grow hw₂ hg₄.tt hφ
      have hreach : Reach s s₄ (1 + n₁ + 1 + n₂) := ((x₁.trans x₂).trans x₃).trans x₄
      cases φ with
      | p =>
        obtain rfl : k₁ = 0 := tyOf_eq_p hφ₄
        have : inferE R Γ (.app fe ye) = none := by simp [inferE, hif, hiy]
        rw [this]
        refine Fails.of_reach hreach (Fails.of_step ?_)
        simp only [pstep, hctl₄, hty₄']; exact Fails.fail _
      | arr a b =>
        obtain ⟨m, x, y, rfl, hm, hx, hy'⟩ := tyOf_arrow_inv hφ₄
        by_cases hab : a = α
        · subst hab
          obtain rfl : x = k₂ := tyOf_eq_of_eq hw₄ hx hα
          let s₅ : PSt := { s₄ with ctl := K, ty := y :: s.ty, out := ⟨12, x, y, s₄.cur⟩ :: s₄.out }
          have x₅ : Reach s₄ s₅ 1 := by
            show pstep s₄ = s₅
            simp only [pstep, hctl₄, hty₄', hm, if_true]; rfl
          have hval : inferE R Γ (.app fe ye) = some (b, i_f ++ iy ++ [⟨.app a b, Γ⟩]) := by
            simp [inferE, hif, hiy]
          rw [hval]
          have hcur₄' : s₄.cur = s.cur := by rw [hcur₄]; exact hcur₂
          refine ⟨1 + n₁ + 1 + n₂ + 1, ⟨s₅, hreach.trans x₅, htk₄, rfl, hcur₄',
            by rw [← hok₂]; exact hok₄, by rw [← hrt₂]; exact hrt₄, by rw [← hbo₂]; exact hbo₄,
            by rw [← hst₂]; exact hst₄, by rw [← hx₂]; exact hx₄, ⟨y, rfl, hy'⟩,
            ⟨oA ++ oB ++ [⟨12, x, y, s₄.cur⟩], ?_, ?_⟩, hg₂.trans hg₄, hw₄, hc₄⟩, by omega⟩
          · show ⟨12, x, y, s₄.cur⟩ :: s₄.out = _
            rw [hout₄, show s₃.out = s₂.out from rfl, hout₂, show s₁.out = s.out from rfl]; simp
          · refine itemsOf_append (itemsOf_append (itemsOf_grow hw₂ hc₂ hg₄ hoA) hoB)
              (itemsOf_single (itemOf_mk ?_ (ctxOf_of_grow (s := s₂) hg₄ hw₂ hc₂ hΓ₂ hcur₄)))
            show opOf s₄.tt s₄.lt ⟨12, x, y, s₄.cur⟩ = _
            simp [opOf, hx, hy']
        · have hne : x ≠ k₂ := fun e => hab (by rw [e] at hx; exact Option.some.inj (hx.symm.trans hα))
          have : inferE R Γ (.app fe ye) = none := by simp [inferE, hif, hiy, hab]
          rw [this]
          refine Fails.of_reach hreach (Fails.of_step ?_)
          simp only [pstep, hctl₄, hty₄', hm, hne, if_false]; exact Fails.fail _

/-! ## Leaves with a type, variables, rules -/

/-- A leaf of type number `t`. -/
theorem leafT_res {s : PSt} {K r : List Nat} {L t : Nat} {τ : HO.Ty} {it : MItem} {op : Op} {Γ : List HO.Ty}
    (hstep : pstep s = s.leaf it t r K) (ht : tyOf s.tt t = some τ) (hop : opOf s.tt s.lt it = some op)
    (hctx : it.ctx = s.cur) (hΓ : ctxOf s.tt s.ct s.cur = some Γ) (hw : TTWF s.tt) (hc : CTWF s.tt s.ct)
    (hL : 1 + 3 * r.length ≤ 3 * L) : ExprRes s K r L (some (τ, [⟨op, Γ⟩])) :=
  ⟨1, ⟨s.leaf it t r K, hstep, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨t, rfl, ht⟩,
    ⟨[it], rfl, itemsOf_single (itemOf_mk hop (by rw [hctx]; exact hΓ))⟩, Grows.refl _ _ _, hw, hc⟩, hL⟩

theorem varTy_some {tt ct : List (Nat × Nat)} : ∀ (c : Nat) {Γ : List HO.Ty}, ctxOf tt ct c = some Γ → ∀ i,
    (varTy ct c i).isSome = (Γ[i]?).isSome
  | 0, Γ, h, i => by rw [ctxOf] at h; cases h; cases i <;> simp [varTy]
  | k + 1, Γ, h, i => by
    rw [ctxOf] at h
    split at h
    · rename_i par t hk
      split at h
      · rename_i hp
        split at h
        · rename_i τ Δ hτ hΔ
          simp only [Option.some.injEq] at h
          subst h
          cases i with
          | zero => simp [varTy, hk]
          | succ i => simp only [varTy, hk, hp, if_true, List.getElem?_cons_succ]; exact varTy_some par hΔ i
        · cases h
      · cases h
    · cases h

theorem mapM_isSome {α β : Type} {f : α → Option β} : ∀ {l : List α} {bs : List β}, l.mapM f = some bs →
    ∀ i : Nat, (l[i]?).isSome = (bs[i]?).isSome
  | [], bs, h, i => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; simp
  | a :: l, bs, h, i => by
    rw [List.mapM_cons] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, _, bs', hbs, rfl⟩ := h
    cases i with
    | zero => simp
    | succ i => simp only [List.getElem?_cons_succ]; exact mapM_isSome hbs i

theorem parseChar_shorter {l : List Nat} {c : Char} {r : List Nat} (h : parseChar l = some (c, r)) :
    r.length < l.length := by
  have := parseChar_sound h; rw [this]; simp [KExp.serChar, length_serNat]

theorem parseNat_shorter {l : List Nat} {n : Nat} {r : List Nat} (h : parseNat l = some (n, r)) :
    r.length < l.length := by
  have := parseNat_sound h; rw [this]; simp [length_serNat]

theorem parseStr_shorter {f : Nat} {l : List Nat} {str : List Char} {r : List Nat} (h : parseStr f l = some (str, r)) :
    r.length < l.length := by
  have := parseStr_sound h; have := length_serStr_pos str; rw [‹l = _›]; simp; omega

/-! ## The theorem -/

/-- **Reading an expression** agrees with `inferE`. -/
theorem readExpr_spec : ∀ f, IHFun f
  | 0, _, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [parseE] at h
  | _ + 1, [], _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [parseE] at h
  | f + 1, t :: l, e, rest, h, s, K, R, Γ, htk, hctl, hw, hc, hR, hΓ => by
    have ih := readExpr_spec f
    have hrd : pstep s = readExpr s K := by simp [pstep, hctl]
    match t, h with
    | 0, h =>
      simp only [parseE, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact leaf_res (it := ⟨0, 0, 0, s.cur⟩) (by rw [hrd]; simp [readExpr, htk]) rfl rfl hΓ hw hc (by simp; omega)
    | 1, h =>
      simp only [parseE, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact leaf_res (it := ⟨1, 0, 0, s.cur⟩) (by rw [hrd]; simp [readExpr, htk]) rfl rfl hΓ hw hc (by simp; omega)
    | 2, h =>
      simp only [parseE] at h
      obtain ⟨⟨c, r'⟩, hc', he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := parseChar_shorter hc'
      exact leaf_res (it := ⟨2, c.toNat, 0, s.cur⟩) (by rw [hrd]; simp [readExpr, htk, hc'])
        (by simp [opOf, Char.ofNat_toNat]) rfl hΓ hw hc
        (by simp; omega)
    | 3, h =>
      simp only [parseE] at h
      split at h
      · rename_i lo r₁ hlo
        obtain ⟨⟨hi, r'⟩, hhi, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have := parseChar_shorter hlo
        have := parseChar_shorter hhi
        exact leaf_res (it := ⟨3, lo.toNat, hi.toNat, s.cur⟩) (by rw [hrd]; simp [readExpr, htk, hlo, hhi])
          (by simp [opOf, Char.ofNat_toNat]) rfl hΓ hw hc
          (by simp; omega)
      · cases h
    | 4, h =>
      simp only [parseE] at h
      obtain ⟨⟨str, r'⟩, hs, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hsl := parseStr_shorter hs
      have hs' := parseStr_full hs
      let s' : PSt := { s.leaf ⟨4, s.lt.length, 0, s.cur⟩ 0 r' K with lt := s.lt ++ [str.map Char.toNat] }
      have x : Reach s s' 1 := by show pstep s = s'; rw [hrd]; simp [readExpr, htk, hs', s']
      refine ⟨1, ⟨s', x, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, rfl, by rw [tyOf]⟩,
        ⟨[⟨4, s.lt.length, 0, s.cur⟩], rfl, itemsOf_single (itemOf_mk ?_ hΓ)⟩,
        ⟨⟨[], (List.append_nil _).symm⟩, ⟨[], (List.append_nil _).symm⟩, ⟨_, rfl⟩⟩, hw, hc⟩, by simp; omega⟩
      show opOf s.tt (s.lt ++ [str.map Char.toNat]) ⟨4, s.lt.length, 0, s.cur⟩ = _
      simp [opOf, litOf, Function.comp_def, Char.ofNat_toNat]
    | 5, h =>
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact seq_case ih ha hb htk hctl hw hc hR hΓ
      · cases h
    | 6, h =>
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact alt_case ih ha hb htk hctl hw hc hR hΓ
      · cases h
    | 7, h =>
      simp only [parseE] at h
      obtain ⟨⟨a, r'⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact star_case ih ha htk hctl hw hc hR hΓ
    | 8, h =>
      simp only [parseE] at h
      obtain ⟨⟨a, r'⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact notP_case ih ha htk hctl hw hc hR hΓ
    | 9, h =>
      simp only [parseE] at h
      obtain ⟨⟨i, r'⟩, hi, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hsh := parseNat_shorter hi
      have hv := (varTy_ctx s.cur hΓ i).1
      have hvs := varTy_some s.cur hΓ i
      cases hvt : varTy s.ct s.cur i with
      | none =>
        rw [hvt] at hvs
        have hg : Γ[i]? = none := by cases hgi : Γ[i]? <;> simp_all
        have : inferE R Γ (.var i) = none := by simp [inferE, hg]
        rw [this]
        exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, hi, hvt]; exact Fails.fail _)
      | some τn =>
        rw [hvt] at hv hvs
        obtain ⟨τ, hτ⟩ : ∃ τ, Γ[i]? = some τ := by cases hgi : Γ[i]? <;> simp_all
        have ht : tyOf s.tt τn = some τ := by rw [← hτ]; simpa using hv
        have : inferE R Γ (.var i) = some (τ, [⟨.var i, Γ⟩]) := by simp [inferE, hτ]
        rw [this]
        exact leafT_res (it := ⟨9, i, 0, s.cur⟩) (by rw [hrd]; simp [readExpr, htk, hi, hvt]) ht rfl rfl hΓ hw hc
          (by simp; omega)
    | 10, h =>
      simp only [parseE] at h
      obtain ⟨⟨i, r'⟩, hi, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hsh := parseNat_shorter hi
      have hv := mapM_getElem? hR i
      have hvs := mapM_isSome hR i
      cases hrt : s.rt[i]? with
      | none =>
        rw [hrt] at hvs
        have hg : R[i]? = none := by cases hgi : R[i]? <;> simp_all
        have : inferE R Γ (.rule i) = none := by simp [inferE, hg]
        rw [this]
        exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, hi, hrt]; exact Fails.fail _)
      | some τn =>
        rw [hrt] at hv hvs
        obtain ⟨τ, hτ⟩ : ∃ τ, R[i]? = some τ := by cases hgi : R[i]? <;> simp_all
        have ht : tyOf s.tt τn = some τ := by rw [← hτ]; simpa using hv
        have : inferE R Γ (.rule i) = some (τ, [⟨.rule i, Γ⟩]) := by simp [inferE, hτ]
        rw [this]
        exact leafT_res (it := ⟨10, i, 0, s.cur⟩) (by rw [hrd]; simp [readExpr, htk, hi, hrt]) ht rfl rfl hΓ hw hc
          (by simp; omega)
    | 11, h =>
      simp only [parseE] at h
      split at h
      · rename_i τ l₁ hτ
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact lam_case ih hτ hb htk hctl hw hc hR hΓ
      · cases h
    | 12, h =>
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        obtain ⟨⟨b, r'⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact app_case ih ha hb htk hctl hw hc hR hΓ
      · cases h
    | _ + 13, h => simp [parseE] at h

/-! ## Malformed expressions -/

theorem parseE_shorter {f : Nat} {l : List Nat} {e : HExp} {r : List Nat} (h : parseE f l = some (e, r)) :
    r.length < l.length := by
  have := parseE_sound h; have := length_serE_pos e; rw [‹l = _›]; simp; omega

theorem parseStr_none {f : Nat} {l : List Nat} (hl : l.length ≤ f) (h : parseStr f l = none) :
    parseStr l.length l = none := by
  cases hs : parseStr l.length l with
  | none => rfl
  | some p =>
    obtain ⟨str, r⟩ := p
    have hl' := parseStr_sound hs
    have := parseStr_ser str r f (by rw [hl'] at hl; simp at hl; omega)
    rw [← hl'] at this; rw [this] at h; cases h

/-- After a first operand that reads and types to a parser (`frame` checks it), reading continues. -/
theorem fail_after {f : Nat} {s : PSt} {K : List Nat} {R Γ : List HO.Ty} {l l₁ : List Nat} {a : HExp} {fr : Nat}
    (ih : ∀ (s : PSt) (K : List Nat) (R Γ : List HO.Ty), s.tk = l₁ → s.ctl = 0 :: K → TTWF s.tt → CTWF s.tt s.ct →
      s.rt.mapM (tyOf s.tt) = some R → ctxOf s.tt s.ct s.cur = some Γ → Fails s)
    (ha : parseE f l = some (a, l₁)) {s₁ : PSt} (x₁ : Reach s s₁ 1) (htk₁ : s₁.tk = l) (hctl₁ : s₁.ctl = 0 :: fr :: K)
    (hw : TTWF s₁.tt) (hc : CTWF s₁.tt s₁.ct) (hR : s₁.rt.mapM (tyOf s₁.tt) = some R)
    (hΓ : ctxOf s₁.tt s₁.ct s₁.cur = some Γ)
    (hframe : ∀ s₂ : PSt, s₂.ctl = fr :: K → ∀ i τ, s₂.ty = i :: s₁.ty → tyOf s₂.tt i = some τ →
      Fails s₂ ∨ ∃ K', pstep s₂ = { s₂ with ctl := 0 :: K' }) :
    Fails s := by
  have hA := readExpr_spec f l a l₁ ha s₁ (fr :: K) R Γ htk₁ hctl₁ hw hc hR hΓ
  cases hia : inferE R Γ a with
  | none => rw [hia] at hA; exact Fails.of_reach x₁ hA
  | some pa =>
    obtain ⟨τa, ia⟩ := pa
    rw [hia] at hA
    obtain ⟨n₁, hd₁, _⟩ := hA
    obtain ⟨s₂, x₂, htk₂, hctl₂, hcur₂, _, hrt₂, _, _, _, ⟨i₁, hty₂, hτ₁⟩, _, hg₂, hw₂, hc₂⟩ := hd₁.parts
    rcases hframe s₂ hctl₂ i₁ τa hty₂ hτ₁ with hf | ⟨K', hstep⟩
    · exact Fails.of_reach (x₁.trans x₂) hf
    · exact Fails.of_reach (x₁.trans x₂) (Fails.of_step (by
        rw [hstep]
        exact ih _ K' R Γ htk₂ rfl hw₂ hc₂ (by rw [hrt₂]; exact mapM_tyOf_grow hw hg₂.tt hR)
          (ctxOf_of_grow hg₂ hw hc hΓ hcur₂)))

/-- The `seq`/`alt` check of the first operand: a parser goes on, anything else fails. -/
theorem frame_bin {fr fr' : Nat} {K : List Nat} {ty₀ : List Nat}
    (h0 : ∀ s₂ : PSt, s₂.ctl = fr :: K → ∀ r, s₂.ty = 0 :: r → pstep s₂ = { s₂ with ctl := 0 :: fr' :: K })
    (h1 : ∀ s₂ : PSt, s₂.ctl = fr :: K → ∀ k r, s₂.ty = (k + 1) :: r → pstep s₂ = s₂.fail) :
    ∀ s₂ : PSt, s₂.ctl = fr :: K → ∀ i τ, s₂.ty = i :: ty₀ → tyOf s₂.tt i = some τ →
      Fails s₂ ∨ ∃ K', pstep s₂ = { s₂ with ctl := 0 :: K' } := by
  intro s₂ hc i τ hty _
  cases i with
  | zero => exact .inr ⟨fr' :: K, h0 s₂ hc ty₀ hty⟩
  | succ k => exact .inl (Fails.of_step (by rw [h1 s₂ hc k ty₀ hty]; exact Fails.fail _))

/-- **A malformed expression makes the machine fail.** -/
theorem readExpr_fail : ∀ (f : Nat) (l : List Nat), l.length ≤ f → parseE f l = none →
    ∀ (s : PSt) (K : List Nat) (R Γ : List HO.Ty), s.tk = l → s.ctl = 0 :: K → TTWF s.tt → CTWF s.tt s.ct →
      s.rt.mapM (tyOf s.tt) = some R → ctxOf s.tt s.ct s.cur = some Γ → Fails s
  | 0, l, hl, _, s, K, _, _, htk, hctl, _, _, _, _ => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact Fails.of_step (by simp [pstep, hctl, readExpr, htk]; exact Fails.fail _)
  | f + 1, [], _, _, s, K, _, _, htk, hctl, _, _, _, _ =>
    Fails.of_step (by simp [pstep, hctl, readExpr, htk]; exact Fails.fail _)
  | f + 1, t :: l, hl, h, s, K, R, Γ, htk, hctl, hw, hc, hR, hΓ => by
    have hrd : pstep s = readExpr s K := by simp [pstep, hctl]
    have hlf : l.length ≤ f := by simp at hl; omega
    -- the rest of the expression, read from a state after the first part
    have ihr : ∀ l₁ : List Nat, l₁.length < l.length → parseE f l₁ = none →
        ∀ (s : PSt) (K : List Nat) (R Γ : List HO.Ty), s.tk = l₁ → s.ctl = 0 :: K → TTWF s.tt → CTWF s.tt s.ct →
          s.rt.mapM (tyOf s.tt) = some R → ctxOf s.tt s.ct s.cur = some Γ → Fails s :=
      fun l₁ hl₁ h₁ => readExpr_fail f l₁ (by omega) h₁
    match t, h with
    | 0, h | 1, h => simp [parseE] at h
    | 2, h =>
      simp only [parseE, Option.map_eq_none_iff] at h
      exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, h]; exact Fails.fail _)
    | 3, h =>
      simp only [parseE] at h
      split at h
      · rename_i lo r₁ hlo
        simp only [Option.map_eq_none_iff] at h
        exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, hlo, h]; exact Fails.fail _)
      · rename_i hlo
        exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, hlo]; exact Fails.fail _)
    | 4, h =>
      simp only [parseE, Option.map_eq_none_iff] at h
      have := parseStr_none hlf h
      exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, this]; exact Fails.fail _)
    | 5, h =>
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 2 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        simp only [Option.map_eq_none_iff] at h
        exact fail_after (ihr l₁ (parseE_shorter ha) h) ha x₁ rfl rfl hw hc hR hΓ
          (frame_bin (fr' := 3) (fun s₂ hc₂ r hty => by simp [pstep, hc₂, hty])
            (fun s₂ hc₂ k r hty => by simp [pstep, hc₂, hty]))
      · rename_i ha
        exact Fails.of_reach x₁ (readExpr_fail f l hlf ha s₁ _ R Γ rfl rfl hw hc hR hΓ)
    | 6, h =>
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 4 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        simp only [Option.map_eq_none_iff] at h
        exact fail_after (ihr l₁ (parseE_shorter ha) h) ha x₁ rfl rfl hw hc hR hΓ
          (frame_bin (fr' := 5) (fun s₂ hc₂ r hty => by simp [pstep, hc₂, hty])
            (fun s₂ hc₂ k r hty => by simp [pstep, hc₂, hty]))
      · rename_i ha
        exact Fails.of_reach x₁ (readExpr_fail f l hlf ha s₁ _ R Γ rfl rfl hw hc hR hΓ)
    | 12, h =>
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 10 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      simp only [parseE] at h
      split at h
      · rename_i a l₁ ha
        simp only [Option.map_eq_none_iff] at h
        exact fail_after (ihr l₁ (parseE_shorter ha) h) ha x₁ rfl rfl hw hc hR hΓ
          (fun s₂ hc₂ _ _ _ _ => .inr ⟨11 :: K, by simp [pstep, hc₂]⟩)
      · rename_i ha
        exact Fails.of_reach x₁ (readExpr_fail f l hlf ha s₁ _ R Γ rfl rfl hw hc hR hΓ)
    | 7, h =>
      simp only [parseE, Option.map_eq_none_iff] at h
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 6 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      exact Fails.of_reach x₁ (readExpr_fail f l hlf h s₁ _ R Γ rfl rfl hw hc hR hΓ)
    | 8, h =>
      simp only [parseE, Option.map_eq_none_iff] at h
      let s₁ : PSt := { s with tk := l, ctl := 0 :: 7 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      exact Fails.of_reach x₁ (readExpr_fail f l hlf h s₁ _ R Γ rfl rfl hw hc hR hΓ)
    | 9, h | 10, h =>
      simp only [parseE, Option.map_eq_none_iff] at h
      exact Fails.of_step (by rw [hrd]; simp [readExpr, htk, h]; exact Fails.fail _)
    | 11, h =>
      let s₁ : PSt := { s with tk := l, ctl := 1 :: 8 :: K }
      have x₁ : Reach s s₁ 1 := by show pstep s = s₁; rw [hrd]; simp [readExpr, htk, s₁]
      simp only [parseE] at h
      split at h
      · rename_i τ l₁ hτp
        simp only [Option.map_eq_none_iff] at h
        obtain ⟨n₁, tt₁, i₁, x₂, hw₁, he₁, hi₁, hτ₁, _⟩ := readType_ok f l τ l₁ hτp s₁ (8 :: K) rfl rfl hw
        let s₂ : PSt := { s₁ with tk := l₁, ctl := 8 :: K, ty := i₁ :: s₁.ty, tt := tt₁ }
        let s₃ : PSt :=
          { s₂ with
            ctl := 0 :: 9 :: i₁ :: s.cur :: K
            ty := s.ty
            ct := s.ct ++ [(s.cur, i₁)]
            cur := s.ct.length + 1 }
        have x₃ : Reach s₂ s₃ 1 := by show pstep s₂ = s₃; simp [pstep, s₂, s₃, s₁]
        have hcl : s.cur ≤ s.ct.length := ctxOf_le hΓ
        have hc₁ : CTWF tt₁ s.ct := hc.grow he₁
        have hΓ₁ : ctxOf tt₁ s.ct s.cur = some Γ := ctxOf_grow hw hc he₁ ⟨[], (List.append_nil _).symm⟩ hΓ
        have hl₁ := parseTy_shorter hτp
        exact Fails.of_reach ((x₁.trans x₂).trans x₃)
          (ihr l₁ hl₁ h s₃ _ R (τ :: Γ) rfl rfl hw₁ (hc₁.snoc hcl hi₁) (mapM_tyOf_grow hw he₁ hR)
            (ctxOf_snoc hw₁ hc₁ hcl hΓ₁ hτ₁))
      · rename_i hτp
        exact Fails.of_reach x₁ (readType_fail f l hlf hτp s₁ (8 :: K) rfl rfl hw)
    | _ + 13, _ => exact Fails.of_step (by rw [hrd]; simp [readExpr, htk]; exact Fails.fail _)

end Shallot.MacroPeg.Mach
