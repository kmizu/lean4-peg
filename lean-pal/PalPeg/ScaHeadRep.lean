import PalPeg.ScaLocal
import PalPeg.RTQueue

/-!
# One input head over a growing text, on persistent stacks

A head at position `p` over the text `t` read so far (the abstract head of
`ScaWindowWorker`: a cursor into `text`) is stored in ten stacks and a finite control part
(`HCtl`: the queue's phase, four values, and the balance's sign bit):

* `left` holds `(t.take p).reverse` (its top is `t[p-1]`, what a reversed head reads);
* `right ++ toList q = t.drop p`, where `right` is a stack and `q` is a Hood–Melville real-time
  queue (`PalPeg.RTQueue`) holding the letters that arrived after the head last drained it.

The queue's lists (`front`, `rear`, and the four lists of a rotation) are stacks. Its constructor
tag is control (`Phase`). Its counters are **not** stored as such:

* `ok` (the rotation's valid count) is a unary stack `rotValid`;
* `lenf` and `lenr` are replaced by one *signed unary* balance
  `bal = lenf - lenr - pending state` (sign bit in control, magnitude in the stack `balance`),
  where `pending (reversing _ f _ _ _) = 2·|f| + 1` and `0` otherwise. The balance is what the
  rotation test `lenr ≤ lenf` needs, and it changes by at most `±2` per step, whereas `lenf`
  itself jumps to `lenf + lenr` when a rotation starts (a concatenation of unary stacks, which
  is not local).

Every operation is a program `Prog` of primitive stack operations (push / pop / move the top of
one stack onto another / copy / clear / set a control field / sequence / branch on the control
and the top `d` cells). `Prog.toRule` compiles a program to a `ScaLocal.Rule` whose depth and
width are computed from the program, and `Prog.toRule_impl` shows that the rule performs the
program's meaning on the head's stacks and control, leaving every other stack alone.

Constants (`Prog.depth` / `Prog.width`, proved by `simp` in `arriveP_depth` etc.):

| operation | depth `D` | width `E` |
|---|---|---|
| `arrive a` (queue `snoc`) | 14 | 12 |
| `moveRight` | 17 | 12 |
| `moveLeft` | 2 | 1 |
| `copyFrom` | 0 | 0 |
| reads (`readFwd`, `readRev`, `available`) | view of depth 1 | — |

The constants are sums along the program (`Rule.comp` adds them), so they overcount.

Main statements (global level, stacks `Fin K → List Γ`, head control behind a lawful `Lens`):
`arrive_correct`, `moveRight_correct`, `moveLeft_correct`, `readFwd_correct`, `readRev_correct`,
`available_correct`, `copyFrom_correct`, `moveBy_correct`, with `*_isLocal` for each rule, and
`other_head_preserved` (a head's rule leaves any disjoint head's representation intact).

The queue invariant `RTQueue.Inv` is part of `HeadRep` and is carried by `RTQueue.inv_snoc` /
`inv_tail`; the stack programs are proved to compute exactly `snoc` / `tail` (`snocP_spec`,
`tailP_spec`), so no new invariant reasoning about the queue is needed. `check`'s rotation test
reads only the phase and the balance sign/emptiness; it is correct because a rotation in
progress implies `lenr ≤ lenf` (`PInv.rot`).
-/

set_option autoImplicit false

namespace PalPeg.ScaHeadRep

open PalPeg.ScaLocal
open PalPeg.RTQueue

/-! ## Slots, control, lenses -/

/-- The head's stacks. -/
inductive Slot where
  | left | right
  | qFront | qRear
  | rotFront | rotFrontRev | rotRear | rotNewFront | rotValid
  | balance
  deriving DecidableEq, Repr

/-- The queue's rotation phase (the constructor of `RotationState`). -/
inductive Phase where
  | idle | reversing | appending | done
  deriving DecidableEq, Repr

/-- The head's control part. -/
structure HCtl where
  phase : Phase
  balanceNeg : Bool
  deriving DecidableEq, Repr

/-- A lawful lens: where the head's control part sits inside the global control. -/
structure Lens (C H : Type) where
  get : C → H
  set : C → H → C
  get_set : ∀ c h, get (set c h) = h
  set_get : ∀ c, set c (get c) = c
  set_set : ∀ c h h', set (set c h) h' = set c h'

/-- The top `d` cells of each slot. -/
def hview {Γ : Type} (d : ℕ) (hs : Slot → List Γ) : Slot → List Γ := fun s => (hs s).take d

/-! ## Programs of primitive stack operations -/

/-- Straight-line programs with branches, over the head's slots and control. -/
inductive Prog (Γ : Type) : Type where
  | skip
  | push (x : Γ) (a : Slot)
  | pop (a : Slot)
  /-- Push the top of `src` (if any) onto `dst`. -/
  | moveTop (src dst : Slot)
  | copy (src dst : Slot)
  | clear (a : Slot)
  | setPhase (ph : Phase)
  | setNeg (b : Bool)
  | seq (p₁ p₂ : Prog Γ)
  /-- Branch on the control and the top `d` cells of every slot. -/
  | ite (d : ℕ) (cond : HCtl → (Slot → List Γ) → Bool) (p₁ p₂ : Prog Γ)

/-- Sequencing. -/
local infixr:60 " ⨾ " => Prog.seq

namespace Prog

variable {Γ : Type}

/-- The depth of the compiled rule. -/
def depth : Prog Γ → ℕ
  | skip => 0
  | push _ _ => 0
  | pop _ => 1
  | moveTop _ _ => 1
  | copy _ _ => 0
  | clear _ => 0
  | setPhase _ => 0
  | setNeg _ => 0
  | seq p₁ p₂ => p₁.depth + p₂.depth
  | ite d _ p₁ p₂ => max d (max p₁.depth p₂.depth)

/-- The width of the compiled rule. -/
def width : Prog Γ → ℕ
  | skip => 0
  | push _ _ => 1
  | pop _ => 0
  | moveTop _ _ => 1
  | copy _ _ => 0
  | clear _ => 0
  | setPhase _ => 0
  | setNeg _ => 0
  | seq p₁ p₂ => p₁.width + p₂.width
  | ite _ _ p₁ p₂ => max p₁.width p₂.width

/-- The meaning of a program on the head's control and slots. -/
def sem : Prog Γ → HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)
  | skip, hc, hs => (hc, hs)
  | push x a, hc, hs => (hc, Function.update hs a (x :: hs a))
  | pop a, hc, hs => (hc, Function.update hs a (hs a).tail)
  | moveTop b a, hc, hs => (hc, Function.update hs a ((hs b).take 1 ++ hs a))
  | copy b a, hc, hs => (hc, Function.update hs a (hs b))
  | clear a, hc, hs => (hc, Function.update hs a [])
  | setPhase ph, hc, hs => ({ hc with phase := ph }, hs)
  | setNeg b, hc, hs => ({ hc with balanceNeg := b }, hs)
  | seq p₁ p₂, hc, hs => p₂.sem (p₁.sem hc hs).1 (p₁.sem hc hs).2
  | ite d cond p₁ p₂, hc, hs => if cond hc (hview d hs) then p₁.sem hc hs else p₂.sem hc hs

/-- Whether the program may write slot `s`. -/
def touches : Prog Γ → Slot → Bool
  | push _ a, s => decide (a = s)
  | pop a, s => decide (a = s)
  | moveTop _ a, s => decide (a = s)
  | copy _ a, s => decide (a = s)
  | clear a, s => decide (a = s)
  | seq p₁ p₂, s => p₁.touches s || p₂.touches s
  | ite _ _ p₁ p₂, s => p₁.touches s || p₂.touches s
  | _, _ => false

/-- Whether the program may write the phase. -/
def writesPhase : Prog Γ → Bool
  | setPhase _ => true
  | seq p₁ p₂ => p₁.writesPhase || p₂.writesPhase
  | ite _ _ p₁ p₂ => p₁.writesPhase || p₂.writesPhase
  | _ => false

/-- Whether the program may write the balance sign. -/
def writesNeg : Prog Γ → Bool
  | setNeg _ => true
  | seq p₁ p₂ => p₁.writesNeg || p₂.writesNeg
  | ite _ _ p₁ p₂ => p₁.writesNeg || p₂.writesNeg
  | _ => false

theorem sem_frame (p : Prog Γ) (s : Slot) (h : p.touches s = false) (hc : HCtl)
    (hs : Slot → List Γ) : (p.sem hc hs).2 s = hs s := by
  induction p generalizing hc hs with
  | skip => rfl
  | push x a =>
    have : s ≠ a := fun e => by subst e; simp [touches] at h
    simp [sem, Function.update_of_ne this]
  | pop a =>
    have : s ≠ a := fun e => by subst e; simp [touches] at h
    simp [sem, Function.update_of_ne this]
  | moveTop b a =>
    have : s ≠ a := fun e => by subst e; simp [touches] at h
    simp [sem, Function.update_of_ne this]
  | copy b a =>
    have : s ≠ a := fun e => by subst e; simp [touches] at h
    simp [sem, Function.update_of_ne this]
  | clear a =>
    have : s ≠ a := fun e => by subst e; simp [touches] at h
    simp [sem, Function.update_of_ne this]
  | setPhase ph => rfl
  | setNeg b => rfl
  | seq p₁ p₂ ih₁ ih₂ =>
    simp only [touches, Bool.or_eq_false_iff] at h
    simp only [sem]
    rw [ih₂ h.2, ih₁ h.1]
  | ite d cond p₁ p₂ ih₁ ih₂ =>
    simp only [touches, Bool.or_eq_false_iff] at h
    simp only [sem]
    split
    · exact ih₁ h.1 hc hs
    · exact ih₂ h.2 hc hs

theorem sem_phase (p : Prog Γ) (h : p.writesPhase = false) (hc : HCtl) (hs : Slot → List Γ) :
    (p.sem hc hs).1.phase = hc.phase := by
  induction p generalizing hc hs with
  | setPhase ph => simp [writesPhase] at h
  | seq p₁ p₂ ih₁ ih₂ =>
    simp only [writesPhase, Bool.or_eq_false_iff] at h
    simp only [sem]
    rw [ih₂ h.2, ih₁ h.1]
  | ite d cond p₁ p₂ ih₁ ih₂ =>
    simp only [writesPhase, Bool.or_eq_false_iff] at h
    simp only [sem]
    split
    · exact ih₁ h.1 hc hs
    · exact ih₂ h.2 hc hs
  | _ => rfl

theorem sem_neg (p : Prog Γ) (h : p.writesNeg = false) (hc : HCtl) (hs : Slot → List Γ) :
    (p.sem hc hs).1.balanceNeg = hc.balanceNeg := by
  induction p generalizing hc hs with
  | setNeg b => simp [writesNeg] at h
  | seq p₁ p₂ ih₁ ih₂ =>
    simp only [writesNeg, Bool.or_eq_false_iff] at h
    simp only [sem]
    rw [ih₂ h.2, ih₁ h.1]
  | ite d cond p₁ p₂ ih₁ ih₂ =>
    simp only [writesNeg, Bool.or_eq_false_iff] at h
    simp only [sem]
    split
    · exact ih₁ h.1 hc hs
    · exact ih₂ h.2 hc hs
  | _ => rfl

theorem sem_ite_pos {d : ℕ} {cond : HCtl → (Slot → List Γ) → Bool} {p₁ p₂ : Prog Γ} {hc : HCtl}
    {hs : Slot → List Γ} (h : cond hc (hview d hs) = true) :
    (ite d cond p₁ p₂).sem hc hs = p₁.sem hc hs := by
  simp [sem, h]

theorem sem_ite_neg {d : ℕ} {cond : HCtl → (Slot → List Γ) → Bool} {p₁ p₂ : Prog Γ} {hc : HCtl}
    {hs : Slot → List Γ} (h : cond hc (hview d hs) = false) :
    (ite d cond p₁ p₂).sem hc hs = p₂.sem hc hs := by
  simp [sem, h]

/-! ## Compiling a program to a local rule -/

variable {C : Type} {K : ℕ}

/-- A rule that rewrites only stack `k`. -/
def stackRule (D E : ℕ) (k : Fin K) (r : (Fin K → List Γ) → Rewrite Γ K)
    (hpre : ∀ v, (r v).pre.length ≤ E) (hdrop : ∀ v, (r v).drop ≤ D) : Rule Γ C K D E where
  f c v := (c, fun j => if j = k then r v else keep j)
  pre_le c v j := by dsimp only; split <;> simp [hpre, keep]
  drop_le c v j := by dsimp only; split <;> simp [hdrop, keep]

theorem stackRule_run {D E : ℕ} (k : Fin K) (r : (Fin K → List Γ) → Rewrite Γ K)
    (hpre : ∀ v, (r v).pre.length ≤ E) (hdrop : ∀ v, (r v).drop ≤ D) (c : C)
    (st : Fin K → List Γ) :
    (stackRule D E k r hpre hdrop).run c st = (c, Function.update st k (apply st (r (view D st)))) := by
  refine Prod.ext rfl (funext fun j => ?_)
  by_cases hj : j = k
  · subst hj; simp [Rule.run, stackRule]
  · simp [Rule.run, stackRule, hj, apply_keep]

theorem Rule.run_ite {D E : ℕ} (p : C → (Fin K → List Γ) → Bool) (R₁ R₂ : Rule Γ C K D E)
    (c : C) (st : Fin K → List Γ) :
    (Rule.ite p R₁ R₂).run c st = if p c (view D st) then R₁.run c st else R₂.run c st := by
  by_cases h : p c (view D st) <;> simp [Rule.run, Rule.ite, h]

/-- The rule performing a program, for a head whose control is at `lc` and whose slots are the
stacks `ix`. -/
def toRule (lc : Lens C HCtl) (ix : Slot → Fin K) : (p : Prog Γ) → Rule Γ C K p.depth p.width
  | skip => Rule.control (fun c _ => c) 0
  | push x a => stackRule 0 1 (ix a) (fun _ => pushRw x (ix a)) (fun _ => by simp [pushRw])
      (fun _ => by simp [pushRw])
  | pop a => stackRule 1 0 (ix a) (fun _ => popRw (ix a)) (fun _ => by simp [popRw])
      (fun _ => by simp [popRw])
  | moveTop b a => stackRule 1 1 (ix a) (fun v => ⟨(v (ix b)).take 1, some (ix a), 0⟩)
      (fun _ => by simp) (fun _ => by simp)
  | copy b a => stackRule 0 0 (ix a) (fun _ => copyRw (ix b)) (fun _ => by simp [copyRw])
      (fun _ => by simp [copyRw])
  | clear a => stackRule 0 0 (ix a) (fun _ => clearRw) (fun _ => by simp [clearRw])
      (fun _ => by simp [clearRw])
  | setPhase ph => Rule.control (fun c _ => lc.set c { lc.get c with phase := ph }) 0
  | setNeg b => Rule.control (fun c _ => lc.set c { lc.get c with balanceNeg := b }) 0
  | seq p₁ p₂ => (toRule lc ix p₁).comp (toRule lc ix p₂)
  | ite d cond p₁ p₂ =>
    Rule.ite (fun c v => cond (lc.get c) (fun s => (v (ix s)).take d))
      ((toRule lc ix p₁).mono (le_max_of_le_right (le_max_left _ _)) (le_max_left _ _))
      ((toRule lc ix p₂).mono (le_max_of_le_right (le_max_right _ _)) (le_max_right _ _))

/-- `R` performs `F` on the head's control (through `lc`) and slots (through `ix`), and leaves
every other stack unchanged. -/
def Implements (lc : Lens C HCtl) (ix : Slot → Fin K) {D E : ℕ} (R : Rule Γ C K D E)
    (F : HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)) : Prop :=
  ∀ c st, (R.run c st).1 = lc.set c (F (lc.get c) (fun s => st (ix s))).1 ∧
    (fun s => (R.run c st).2 (ix s)) = (F (lc.get c) (fun s => st (ix s))).2 ∧
    ∀ k, (∀ s, ix s ≠ k) → (R.run c st).2 k = st k

theorem update_comp {ix : Slot → Fin K} (hix : Function.Injective ix) (st : Fin K → List Γ)
    (a : Slot) (v : List Γ) :
    (fun s => Function.update st (ix a) v (ix s)) = Function.update (fun s => st (ix s)) a v := by
  funext s
  by_cases h : s = a
  · subst h; simp
  · rw [Function.update_of_ne (hix.ne h), Function.update_of_ne h]

theorem impl_stack (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix) {D E : ℕ}
    (a : Slot) (r : (Fin K → List Γ) → Rewrite Γ K) (hpre : ∀ v, (r v).pre.length ≤ E)
    (hdrop : ∀ v, (r v).drop ≤ D) (val : (Slot → List Γ) → List Γ)
    (hval : ∀ st, apply st (r (view D st)) = val (fun s => st (ix s))) :
    Implements lc ix (stackRule (C := C) D E (ix a) r hpre hdrop)
      (fun hc hs => (hc, Function.update hs a (val hs))) := by
  intro c st
  rw [stackRule_run]
  refine ⟨(lc.set_get c).symm, ?_, fun k hk => Function.update_of_ne (Ne.symm (hk a)) _ _⟩
  rw [update_comp hix, hval]

theorem impl_control (lc : Lens C HCtl) (ix : Slot → Fin K) (D : ℕ) (g : HCtl → HCtl) :
    Implements (Γ := Γ) lc ix (Rule.control (fun c _ => lc.set c (g (lc.get c))) D)
      (fun hc hs => (g hc, hs)) := by
  intro c st
  rw [Rule.run_control]
  exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem impl_skip (lc : Lens C HCtl) (ix : Slot → Fin K) (D : ℕ) :
    Implements (Γ := Γ) lc ix (Rule.control (fun c _ => c) D) (fun hc hs => (hc, hs)) := by
  intro c st
  rw [Rule.run_control]
  exact ⟨(lc.set_get c).symm, rfl, fun _ _ => rfl⟩

theorem impl_comp (lc : Lens C HCtl) (ix : Slot → Fin K) {D₁ E₁ D₂ E₂ : ℕ}
    {R₁ : Rule Γ C K D₁ E₁} {R₂ : Rule Γ C K D₂ E₂}
    {F₁ F₂ : HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)}
    (h₁ : Implements lc ix R₁ F₁) (h₂ : Implements lc ix R₂ F₂) :
    Implements lc ix (R₁.comp R₂) (fun hc hs => F₂ (F₁ hc hs).1 (F₁ hc hs).2) := by
  intro c st
  rw [Rule.run_comp]
  obtain ⟨h1c, h1s, h1f⟩ := h₁ c st
  obtain ⟨h2c, h2s, h2f⟩ := h₂ (R₁.run c st).1 (R₁.run c st).2
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · rw [h2c, h1c, lc.get_set, lc.set_set, h1s]
  · rw [h2s, h1c, lc.get_set, h1s]
  · rw [h2f k hk, h1f k hk]

theorem impl_ite (lc : Lens C HCtl) (ix : Slot → Fin K) {D₁ E₁ D₂ E₂ D E : ℕ} (d : ℕ)
    (hd : d ≤ D) (cond : HCtl → (Slot → List Γ) → Bool)
    {R₁ : Rule Γ C K D₁ E₁} {R₂ : Rule Γ C K D₂ E₂}
    {F₁ F₂ : HCtl → (Slot → List Γ) → HCtl × (Slot → List Γ)}
    (h₁ : Implements lc ix R₁ F₁) (h₂ : Implements lc ix R₂ F₂)
    (hD₁ : D₁ ≤ D) (hE₁ : E₁ ≤ E) (hD₂ : D₂ ≤ D) (hE₂ : E₂ ≤ E) :
    Implements lc ix
      (Rule.ite (fun c v => cond (lc.get c) (fun s => (v (ix s)).take d))
        (R₁.mono hD₁ hE₁) (R₂.mono hD₂ hE₂))
      (fun hc hs => if cond hc (hview d hs) then F₁ hc hs else F₂ hc hs) := by
  intro c st
  rw [Rule.run_ite, Rule.run_mono, Rule.run_mono]
  have hv : (fun s => (view D st (ix s)).take d) = hview d (fun s => st (ix s)) := by
    funext s
    simp only [view, hview, List.take_take]
    congr 1
    omega
  simp only [hv]
  split
  · exact h₁ c st
  · exact h₂ c st

/-- **The compiled rule performs the program.** -/
theorem toRule_impl (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (p : Prog Γ) : Implements lc ix (p.toRule lc ix) p.sem := by
  induction p with
  | skip => exact impl_skip lc ix 0
  | push x a =>
    exact impl_stack lc hix a _ _ _ (fun hs => x :: hs a) (fun st => by simp [apply, pushRw])
  | pop a =>
    exact impl_stack lc hix a _ _ _ (fun hs => (hs a).tail) (fun st => by simp [apply, popRw])
  | moveTop b a =>
    exact impl_stack lc hix a _ _ _ (fun hs => (hs b).take 1 ++ hs a)
      (fun st => by simp [apply, view, depth])
  | copy b a =>
    exact impl_stack lc hix a _ _ _ (fun hs => hs b) (fun st => by simp [apply, copyRw])
  | clear a =>
    exact impl_stack lc hix a _ _ _ (fun _ => []) (fun st => by simp [apply, clearRw])
  | setPhase ph => exact impl_control lc ix 0 (fun hc => { hc with phase := ph })
  | setNeg b => exact impl_control lc ix 0 (fun hc => { hc with balanceNeg := b })
  | seq p₁ p₂ ih₁ ih₂ => exact impl_comp lc ix ih₁ ih₂
  | ite d cond p₁ p₂ ih₁ ih₂ =>
    exact impl_ite lc ix d (le_max_left _ _) cond ih₁ ih₂ _ _ _ _

/-- Transfer a statement about the program's meaning to the compiled rule. -/
theorem transfer (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (p : Prog Γ) {P Q : HCtl → (Slot → List Γ) → Prop}
    (h : ∀ hc hs, P hc hs → Q (p.sem hc hs).1 (p.sem hc hs).2) (c : C) (st : Fin K → List Γ)
    (hP : P (lc.get c) (fun s => st (ix s))) :
    Q (lc.get ((p.toRule lc ix).run c st).1) (fun s => ((p.toRule lc ix).run c st).2 (ix s)) := by
  obtain ⟨hc, hs, _⟩ := toRule_impl lc hix p c st
  rw [hc, lc.get_set, hs]
  exact h _ _ hP

/-- The compiled rule changes the global control only through the lens, so any independent
lens is unaffected. -/
theorem run_ctl_indep (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (p : Prog Γ) {H : Type} (get' : C → H) (hindep : ∀ c h, get' (lc.set c h) = get' c)
    (c : C) (st : Fin K → List Γ) : get' ((p.toRule lc ix).run c st).1 = get' c := by
  rw [(toRule_impl lc hix p c st).1, hindep]

/-- The compiled rule changes no stack outside the head's slots. -/
theorem run_frame (lc : Lens C HCtl) {ix : Slot → Fin K} (hix : Function.Injective ix)
    (p : Prog Γ) (c : C) (st : Fin K → List Γ) (k : Fin K) (hk : ∀ s, ix s ≠ k) :
    ((p.toRule lc ix).run c st).2 k = st k :=
  (toRule_impl lc hix p c st).2.2 k hk

theorem sem_seq (p₁ p₂ : Prog Γ) (hc : HCtl) (hs : Slot → List Γ) :
    (p₁ ⨾ p₂).sem hc hs = p₂.sem (p₁.sem hc hs).1 (p₁.sem hc hs).2 := rfl

end Prog

open Prog

/-! ## The representation -/

section Rep

variable {Γ : Type}

/-- The value of a signed unary counter: sign bit and magnitude stack. -/
def balOf (neg : Bool) (m : List Γ) : ℤ := if neg then -(m.length : ℤ) else m.length

/-- The balance `lenf - lenr - pending state`. -/
def bal (hc : HCtl) (hs : Slot → List Γ) : ℤ := balOf hc.balanceNeg (hs .balance)

/-- The part of `lenf - lenr` still owed by a rotation in progress: each reversing step moves one
letter of `f` and adds `2` to the balance, the last one adds `1`. -/
def pending {α : Type} : RotationState α → ℕ
  | .reversing _ f _ _ _ => 2 * f.length + 1
  | _ => 0

/-- The rotation slots. -/
def isRot : Slot → Bool
  | .rotFront | .rotFrontRev | .rotRear | .rotNewFront | .rotValid => true
  | _ => false

variable (ι : Fin 2 → Γ)

/-- Letters as stack symbols. -/
def enc (l : List (Fin 2)) : List Γ := l.map ι

/-- The rotation state: tag in the control, lists and the unary `ok` in the rotation slots. -/
def SRep (s : RotationState (Fin 2)) (ph : Phase) (hs : Slot → List Γ) : Prop :=
  match s with
  | .idle => ph = .idle
  | .reversing ok f f' r r' => ph = .reversing ∧ (hs .rotValid).length = ok ∧
      hs .rotFront = enc ι f ∧ hs .rotFrontRev = enc ι f' ∧ hs .rotRear = enc ι r ∧
      hs .rotNewFront = enc ι r'
  | .appending ok f' r' => ph = .appending ∧ (hs .rotValid).length = ok ∧
      hs .rotFrontRev = enc ι f' ∧ hs .rotNewFront = enc ι r'
  | .done nf => ph = .done ∧ hs .rotNewFront = enc ι nf

/-- A Hood–Melville queue on stacks. -/
structure QRep (q : Queue (Fin 2)) (hc : HCtl) (hs : Slot → List Γ) : Prop where
  state : SRep ι q.state hc.phase hs
  front : hs .qFront = enc ι q.front
  rear : hs .qRear = enc ι q.rear
  balance : bal hc hs + pending q.state = (q.lenf : ℤ) - q.lenr

/-- **A head at `p` over the text `t`.** -/
structure HeadRep (t : List (Fin 2)) (p : ℕ) (hc : HCtl) (hs : Slot → List Γ) : Prop where
  le : p ≤ t.length
  left : hs .left = enc ι (t.take p).reverse
  queue : ∃ (R : List (Fin 2)) (q : Queue (Fin 2)), Inv q ∧ QRep ι q hc hs ∧
    hs .right = enc ι R ∧ R ++ toList q = t.drop p

variable {ι}

theorem srep_congr {s : RotationState (Fin 2)} {ph : Phase} {hs hs' : Slot → List Γ}
    (h : ∀ sl, isRot sl = true → hs' sl = hs sl) (hS : SRep ι s ph hs) : SRep ι s ph hs' := by
  have e1 := h .rotFront rfl
  have e2 := h .rotFrontRev rfl
  have e3 := h .rotRear rfl
  have e4 := h .rotNewFront rfl
  have e5 := h .rotValid rfl
  cases s <;> simpa [SRep, e1, e2, e3, e4, e5] using hS

theorem qrep_congr {q : Queue (Fin 2)} {hc : HCtl} {hs hs' : Slot → List Γ}
    (h : ∀ sl, sl ≠ .left → sl ≠ .right → hs' sl = hs sl) (hQ : QRep ι q hc hs) :
    QRep ι q hc hs' where
  state := srep_congr (fun sl hsl => h sl (by rintro rfl; simp [isRot] at hsl)
    (by rintro rfl; simp [isRot] at hsl)) hQ.state
  front := by rw [h _ (by simp) (by simp), hQ.front]
  rear := by rw [h _ (by simp) (by simp), hQ.rear]
  balance := by
    have := hQ.balance
    rwa [bal, h _ (by simp) (by simp)]

theorem isEmpty_take_succ (l : List Γ) (n : ℕ) : (l.take (n + 1)).isEmpty = l.isEmpty := by
  cases l <;> simp

@[simp] theorem enc_nil : enc ι [] = [] := rfl
@[simp] theorem enc_cons (x : Fin 2) (l : List (Fin 2)) : enc ι (x :: l) = ι x :: enc ι l := rfl
@[simp] theorem enc_append (l l' : List (Fin 2)) : enc ι (l ++ l') = enc ι l ++ enc ι l' :=
  List.map_append
@[simp] theorem length_enc (l : List (Fin 2)) : (enc ι l).length = l.length := List.length_map _
@[simp] theorem enc_eq_nil (l : List (Fin 2)) : enc ι l = [] ↔ l = [] := List.map_eq_nil_iff

end Rep

/-! ## The signed balance -/

section Balance

variable {Γ : Type} (tk : Γ)

/-- `balance += 1`. -/
def incBal : Prog Γ :=
  .ite 1 (fun hc v => hc.balanceNeg && !(v .balance).isEmpty) (.pop .balance)
    (.setNeg false ⨾ .push tk .balance)

/-- `balance -= 1`. -/
def decBal : Prog Γ :=
  .ite 1 (fun hc v => !hc.balanceNeg && !(v .balance).isEmpty) (.pop .balance)
    (.setNeg true ⨾ .push tk .balance)

theorem incBal_spec (hc : HCtl) (hs : Slot → List Γ) :
    ∃ b m, (incBal tk).sem hc hs = (⟨hc.phase, b⟩, Function.update hs .balance m) ∧
      balOf b m = bal hc hs + 1 := by
  rcases hc with ⟨ph, neg⟩
  rcases hm : hs .balance with _ | ⟨x, m⟩
  · refine ⟨false, [tk], ?_, ?_⟩
    · simp [incBal, Prog.sem, hview, hm]
    · cases neg <;> simp [balOf, bal, hm]
  · cases neg
    · refine ⟨false, tk :: x :: m, ?_, ?_⟩
      · simp [incBal, Prog.sem, hview, hm]
      · simp [balOf, bal, hm]
    · refine ⟨true, m, ?_, ?_⟩
      · simp [incBal, Prog.sem, hview, hm]
      · simp [balOf, bal, hm]

theorem decBal_spec (hc : HCtl) (hs : Slot → List Γ) :
    ∃ b m, (decBal tk).sem hc hs = (⟨hc.phase, b⟩, Function.update hs .balance m) ∧
      balOf b m = bal hc hs - 1 := by
  rcases hc with ⟨ph, neg⟩
  rcases hm : hs .balance with _ | ⟨x, m⟩
  · refine ⟨true, [tk], ?_, ?_⟩
    · simp [decBal, Prog.sem, hview, hm]
    · cases neg <;> simp [balOf, bal, hm]
  · cases neg
    · refine ⟨false, m, ?_, ?_⟩
      · simp [decBal, Prog.sem, hview, hm]
      · simp [balOf, bal, hm]
    · refine ⟨true, tk :: x :: m, ?_, ?_⟩
      · simp [decBal, Prog.sem, hview, hm]
      · simp [balOf, bal, hm]; omega

/-- Two increments. -/
def incBal2 : Prog Γ := incBal tk ⨾ incBal tk

theorem incBal2_spec (hc : HCtl) (hs : Slot → List Γ) :
    ∃ b m, (incBal2 tk).sem hc hs = (⟨hc.phase, b⟩, Function.update hs .balance m) ∧
      balOf b m = bal hc hs + 2 := by
  obtain ⟨b1, m1, e1, v1⟩ := incBal_spec tk hc hs
  obtain ⟨b2, m2, e2, v2⟩ := incBal_spec tk ⟨hc.phase, b1⟩ (Function.update hs .balance m1)
  refine ⟨b2, m2, ?_, ?_⟩
  · rw [incBal2, sem_seq, e1, e2]; simp
  · rw [v2]; simp only [bal, Function.update_self] at v1 ⊢; rw [v1]; ring

/-- A program that writes neither the balance nor its sign keeps the balance. -/
theorem bal_frame (p : Prog Γ) (h₁ : p.touches .balance = false) (h₂ : p.writesNeg = false)
    (hc : HCtl) (hs : Slot → List Γ) : bal (p.sem hc hs).1 (p.sem hc hs).2 = bal hc hs := by
  simp [bal, sem_frame p _ h₁, sem_neg p h₂]

end Balance

/-! ## The queue operations -/

section QueueOps

variable {Γ : Type} (tk : Γ)

/-- The list moves of one reversing step. -/
def revMove : Prog Γ :=
  .moveTop .rotFront .rotFrontRev ⨾ .pop .rotFront ⨾ .moveTop .rotRear .rotNewFront ⨾
    .pop .rotRear ⨾ .push tk .rotValid

/-- `reversing ok (x :: f) f' (y :: r) r' ↦ reversing (ok + 1) f (x :: f') r (y :: r')`. -/
def revStep : Prog Γ := revMove tk ⨾ incBal2 tk

/-- The list moves of the last reversing step. -/
def revLastMove : Prog Γ := .moveTop .rotRear .rotNewFront ⨾ .pop .rotRear ⨾ .setPhase .appending

/-- `reversing ok [] f' [y] r' ↦ appending ok f' (y :: r')`. -/
def revLast : Prog Γ := revLastMove ⨾ incBal tk

/-- `exec` on a reversing state. -/
def execRev : Prog Γ :=
  .ite 2 (fun _ v => !(v .rotFront).isEmpty && !(v .rotRear).isEmpty) (revStep tk)
    (.ite 2 (fun _ v => (v .rotFront).isEmpty && decide ((v .rotRear).length = 1)) (revLast tk)
      .skip)

/-- `appending (ok + 1) (x :: f') r' ↦ appending ok f' (x :: r')`. -/
def appStep : Prog Γ := .moveTop .rotFrontRev .rotNewFront ⨾ .pop .rotFrontRev ⨾ .pop .rotValid

/-- `exec` on an appending state. -/
def execApp : Prog Γ :=
  .ite 1 (fun _ v => (v .rotValid).isEmpty) (.setPhase .done)
    (.ite 1 (fun _ v => !(v .rotFrontRev).isEmpty) appStep .skip)

/-- **`RTQueue.exec`**, one rotation step. -/
def execP : Prog Γ :=
  .ite 0 (fun hc _ => decide (hc.phase = .reversing)) (execRev tk)
    (.ite 0 (fun hc _ => decide (hc.phase = .appending)) execApp .skip)

/-- `invalidate` on an appending state. -/
def invApp : Prog Γ :=
  .ite 1 (fun _ v => (v .rotValid).isEmpty)
    (.ite 1 (fun _ v => !(v .rotNewFront).isEmpty) (.pop .rotNewFront ⨾ .setPhase .done) .skip)
    (.pop .rotValid)

/-- **`RTQueue.invalidate`**. -/
def invP : Prog Γ :=
  .ite 0 (fun hc _ => decide (hc.phase = .reversing)) (.pop .rotValid)
    (.ite 0 (fun hc _ => decide (hc.phase = .appending)) invApp .skip)

/-- Start a rotation: `reversing 0 front [] rear []`, empty rear, balance `0`. -/
def startRot : Prog Γ :=
  .copy .qFront .rotFront ⨾ .clear .rotFrontRev ⨾ .copy .qRear .rotRear ⨾ .clear .rotNewFront ⨾
    .clear .qRear ⨾ .clear .rotValid ⨾ .clear .balance ⨾ .setPhase .reversing ⨾ .setNeg false

/-- The test of `check`: a rotation starts exactly when the queue is idle and `lenr > lenf`,
i.e. the balance is negative. -/
def startP : Prog Γ :=
  .ite 1 (fun hc v => decide (hc.phase = .idle) && hc.balanceNeg && !(v .balance).isEmpty)
    startRot .skip

/-- Install a finished rotation's new front (the `done` case of `exec2`). -/
def finishP : Prog Γ :=
  .ite 0 (fun hc _ => decide (hc.phase = .done)) (.copy .rotNewFront .qFront ⨾ .setPhase .idle)
    .skip

/-- **`RTQueue.check`**. -/
def checkP : Prog Γ := startP ⨾ execP tk ⨾ execP tk ⨾ finishP

/-- **`RTQueue.snoc`**. -/
def snocP (ι : Fin 2 → Γ) (a : Fin 2) : Prog Γ := .push (ι a) .qRear ⨾ decBal tk ⨾ checkP tk

/-- **`RTQueue.tail`**. -/
def tailP : Prog Γ :=
  .ite 1 (fun _ v => (v .qFront).isEmpty) .skip
    (.pop .qFront ⨾ decBal tk ⨾ invP ⨾ checkP tk)

variable {ι : Fin 2 → Γ}

theorem srep_idle {s : RotationState (Fin 2)} {hs : Slot → List Γ} (h : SRep ι s .idle hs) :
    s = .idle := by
  cases s <;> simp_all [SRep]

theorem notDone_of_srep {s : RotationState (Fin 2)} {ph : Phase} {hs : Slot → List Γ}
    (h : SRep ι s ph hs) (hph : ph ≠ .done) : NotDone s := by
  cases s <;> simp_all [SRep, NotDone]

theorem phase_ne_done {s : RotationState (Fin 2)} {ph : Phase} {hs : Slot → List Γ}
    (h : SRep ι s ph hs) (hs' : NotDone s) : ph ≠ .done := by
  cases s <;> simp_all [SRep, NotDone]

theorem execP_spec {s : RotationState (Fin 2)} {hc : HCtl} {hs : Slot → List Γ}
    (hS : SRep ι s hc.phase hs) :
    SRep ι (exec s) ((execP tk).sem hc hs).1.phase ((execP tk).sem hc hs).2 ∧
      bal ((execP tk).sem hc hs).1 ((execP tk).sem hc hs).2 + pending (exec s)
        = bal hc hs + pending s := by
  cases s with
  | idle =>
    have hph : hc.phase = .idle := hS
    rw [execP, sem_ite_neg (by simp [hph]), sem_ite_neg (by simp [hph])]
    exact ⟨hS, rfl⟩
  | done nf =>
    rw [execP, sem_ite_neg (by simp [hS.1]), sem_ite_neg (by simp [hS.1])]
    exact ⟨hS, rfl⟩
  | reversing ok f f' r r' =>
    obtain ⟨hph, hok, hf, hf', hr, hr'⟩ := hS
    rw [execP, sem_ite_pos (by simp [hph]), execRev]
    rcases f with _ | ⟨x, f⟩ <;> rcases r with _ | ⟨y, r⟩
    · rw [sem_ite_neg (by simp [hview, hf]), sem_ite_neg (by simp [hview, hr]), exec_rev_nil_nil]
      exact ⟨⟨hph, hok, hf, hf', hr, hr'⟩, rfl⟩
    · rw [sem_ite_neg (by simp [hview, hf])]
      rcases r with _ | ⟨z, r⟩
      · rw [sem_ite_pos (by simp [hview, hf, hr]), exec_rev_nil]
        obtain ⟨b, m, e, v⟩ := incBal_spec tk ((revLastMove (Γ := Γ)).sem hc hs).1
          ((revLastMove (Γ := Γ)).sem hc hs).2
        rw [revLast, sem_seq, e]
        simp only [revLastMove, Prog.sem, bal, Function.update_self] at v ⊢
        refine ⟨?_, ?_⟩
        · simp [SRep, hok, hf', hr, hr']
        · rw [v]; simp [pending]
      · rw [sem_ite_neg (by simp [hview, hf, hr]), exec_rev_nil_two]
        exact ⟨⟨hph, hok, hf, hf', hr, hr'⟩, rfl⟩
    · rw [sem_ite_neg (by simp [hview, hr]), sem_ite_neg (by simp [hview, hf]),
        exec_rev_cons_nil]
      exact ⟨⟨hph, hok, hf, hf', hr, hr'⟩, rfl⟩
    · rw [sem_ite_pos (by simp [hview, hf, hr]), exec_rev_cons]
      obtain ⟨b, m, e, v⟩ := incBal2_spec tk ((revMove tk).sem hc hs).1 ((revMove tk).sem hc hs).2
      rw [revStep, sem_seq, e]
      simp only [revMove, Prog.sem, bal, Function.update_self] at v ⊢
      refine ⟨?_, ?_⟩
      · simp [SRep, hph, hok, hf, hf', hr, hr']
      · rw [v]; simp [pending]; ring
  | appending ok f' r' =>
    obtain ⟨hph, hok, hf', hr'⟩ := hS
    rw [execP, sem_ite_neg (by simp [hph]), sem_ite_pos (by simp [hph]), execApp]
    rcases ok with _ | k
    · have hv : hs .rotValid = [] := List.eq_nil_of_length_eq_zero hok
      rw [sem_ite_pos (by simp [hview, hv]), exec_app_zero]
      exact ⟨⟨rfl, hr'⟩, by simp [Prog.sem, bal, pending]⟩
    · obtain ⟨v0, vs, hv⟩ := List.exists_cons_of_ne_nil (l := hs .rotValid)
        (fun h => by simp [h] at hok)
      rw [sem_ite_neg (by simp [hview, hv])]
      rcases f' with _ | ⟨x, f'⟩
      · rw [sem_ite_neg (by simp [hview, hf']), exec_app_succ_nil]
        exact ⟨⟨hph, hok, hf', hr'⟩, rfl⟩
      · rw [sem_ite_pos (by simp [hview, hf']), exec_app_succ]
        refine ⟨?_, ?_⟩
        · simp [appStep, Prog.sem, SRep, hph, hf', hr']
          omega
        · simp [appStep, Prog.sem, bal, pending]

theorem pending_invalidate {α : Type} (s : RotationState α) :
    pending (invalidate s) = pending s := by
  cases s with
  | appending ok f' r' => rcases ok with _ | ok <;> rcases r' with _ | ⟨x, r'⟩ <;> rfl
  | _ => rfl

theorem invP_spec {s : RotationState (Fin 2)} {hc : HCtl} {hs : Slot → List Γ}
    (hS : SRep ι s hc.phase hs) :
    SRep ι (invalidate s) ((invP (Γ := Γ)).sem hc hs).1.phase ((invP (Γ := Γ)).sem hc hs).2 := by
  cases s with
  | idle =>
    have hph : hc.phase = .idle := hS
    rw [invP, sem_ite_neg (by simp [hph]), sem_ite_neg (by simp [hph])]
    exact hS
  | done nf =>
    rw [invP, sem_ite_neg (by simp [hS.1]), sem_ite_neg (by simp [hS.1])]
    exact hS
  | reversing ok f f' r r' =>
    obtain ⟨hph, hok, hf, hf', hr, hr'⟩ := hS
    rw [invP, sem_ite_pos (by simp [hph]), inv_rev]
    simp [Prog.sem, SRep, hph, hok, hf, hf', hr, hr']
  | appending ok f' r' =>
    obtain ⟨hph, hok, hf', hr'⟩ := hS
    rw [invP, sem_ite_neg (by simp [hph]), sem_ite_pos (by simp [hph]), invApp]
    rcases ok with _ | k
    · have hv : hs .rotValid = [] := List.eq_nil_of_length_eq_zero hok
      rw [sem_ite_pos (by simp [hview, hv])]
      rcases r' with _ | ⟨x, r'⟩
      · rw [sem_ite_neg (by simp [hview, hr'])]
        exact ⟨hph, hok, hf', hr'⟩
      · rw [sem_ite_pos (by simp [hview, hr']), inv_app_zero]
        simp [Prog.sem, SRep, hr']
    · obtain ⟨v0, vs, hv⟩ := List.exists_cons_of_ne_nil (l := hs .rotValid)
        (fun h => by simp [h] at hok)
      rw [sem_ite_neg (by simp [hview, hv]), inv_app_succ]
      simp [Prog.sem, SRep, hph, hf', hr']
      omega

/-- The queue a rotation starts from (the `else` branch of `check`). -/
def rotStart {α : Type} (q : Queue α) : Queue α :=
  { lenf := q.lenf + q.lenr, front := q.front, state := .reversing 0 q.front [] q.rear [],
    lenr := 0, rear := [] }

theorem check_eq {α : Type} (q : Queue α) :
    check q = exec2 (if q.lenr ≤ q.lenf then q else rotStart q) := by
  unfold check rotStart; split <;> rfl

/-- What `check` needs of its argument (four fields of `RTQueue.PInv`). -/
structure CheckPre {α : Type} (q : Queue α) : Prop where
  lenf_eq : q.lenf = (frontList q.state q.front).length
  lenr_eq : q.lenr = q.rear.length
  le : q.lenr ≤ q.lenf + 1
  rot : q.lenf < q.lenr → q.state = .idle

theorem CheckPre.of_pinv {α : Type} {q : Queue α} (h : PInv q) : CheckPre q :=
  ⟨h.lenf_eq, h.lenr_eq, h.le, h.rot⟩

theorem startP_spec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ}
    (hQ : QRep ι q hc hs) (hpre : CheckPre q) :
    QRep ι (if q.lenr ≤ q.lenf then q else rotStart q) ((startP (Γ := Γ)).sem hc hs).1
      ((startP (Γ := Γ)).sem hc hs).2 := by
  by_cases hle : q.lenr ≤ q.lenf
  · rw [if_pos hle, startP, sem_ite_neg]
    · exact hQ
    · cases hn : hc.balanceNeg
      · simp
      · rcases hm : hs .balance with _ | ⟨x, m⟩
        · simp [hview, hm]
        · have hph : hc.phase ≠ .idle := by
            intro hph
            have hS := hQ.state
            rw [hph] at hS
            have hb := hQ.balance
            rw [srep_idle hS] at hb
            simp [bal, balOf, hn, hm, pending] at hb
            omega
          simp [hview, hm, hph]
  · rw [if_neg hle]
    have hidle : q.state = .idle := hpre.rot (by omega)
    have hph : hc.phase = .idle := by have := hQ.state; rw [hidle] at this; exact this
    have hb := hQ.balance
    have hlenf := hpre.lenf_eq
    rw [hidle] at hb hlenf
    simp only [frontList] at hlenf
    have hlenr := hpre.lenr_eq
    have hle1 := hpre.le
    cases hn : hc.balanceNeg
    · simp [bal, balOf, hn, pending] at hb; omega
    rcases hm : hs .balance with _ | ⟨x, m⟩
    · simp [bal, balOf, hn, hm, pending] at hb; omega
    rw [startP, sem_ite_pos (by simp [hview, hph, hn, hm])]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [startRot, Prog.sem, SRep, rotStart, hQ.front, hQ.rear]
    · simp [startRot, Prog.sem, rotStart, hQ.front]
    · simp [startRot, Prog.sem, rotStart]
    · simp [startRot, Prog.sem, rotStart, bal, balOf, pending]
      omega

theorem finishP_done {q : Queue (Fin 2)} {nf : List (Fin 2)} {hc : HCtl} {hs : Slot → List Γ}
    (hQ : QRep ι q hc hs) (hd : q.state = .done nf) :
    QRep ι { q with front := nf, state := .idle } ((finishP (Γ := Γ)).sem hc hs).1
      ((finishP (Γ := Γ)).sem hc hs).2 := by
  have hS := hQ.state
  rw [hd] at hS
  obtain ⟨hph, hnf⟩ := hS
  have hb := hQ.balance
  rw [hd] at hb
  rw [finishP, sem_ite_pos (by simp [hph])]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Prog.sem, SRep]
  · simp [Prog.sem, hnf]
  · simp [Prog.sem, hQ.rear]
  · simp [Prog.sem, bal, pending] at hb ⊢
    exact hb

theorem finishP_notDone {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ}
    (hQ : QRep ι q hc hs) (hnd : NotDone q.state) : (finishP (Γ := Γ)).sem hc hs = (hc, hs) := by
  rw [finishP, sem_ite_neg (by simp [phase_ne_done hQ.state hnd])]
  rfl

theorem qrep_exec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ} (hQ : QRep ι q hc hs) :
    QRep ι { q with state := exec q.state } ((execP tk).sem hc hs).1 ((execP tk).sem hc hs).2 := by
  obtain ⟨hS, hb⟩ := execP_spec tk hQ.state
  refine ⟨hS, ?_, ?_, ?_⟩
  · rw [sem_frame _ _ rfl, hQ.front]
  · rw [sem_frame _ _ rfl, hQ.rear]
  · have := hQ.balance
    simp only at this ⊢
    linarith

/-- **`RTQueue.exec2`**: two steps and the installation of a finished rotation. -/
theorem exec2P_spec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ} (hQ : QRep ι q hc hs) :
    QRep ι (exec2 q) ((execP tk ⨾ execP tk ⨾ finishP).sem hc hs).1
      ((execP tk ⨾ execP tk ⨾ finishP).sem hc hs).2 := by
  have h2 := qrep_exec tk (qrep_exec tk hQ)
  rw [sem_seq, sem_seq]
  by_cases hd : ∃ nf, exec (exec q.state) = .done nf
  · obtain ⟨nf, hnf⟩ := hd
    rw [exec2_eq_of_done hnf]
    exact finishP_done (q := { q with state := exec (exec q.state) }) h2 hnf
  · have hnd : NotDone (exec (exec q.state)) := by
      cases h : exec (exec q.state) with
      | done nf => exact absurd ⟨nf, h⟩ hd
      | _ => trivial
    rw [exec2_eq_of_not_done rfl hnd,
      finishP_notDone (q := { q with state := exec (exec q.state) }) h2 hnd]
    exact h2

/-- **`RTQueue.check`.** -/
theorem checkP_spec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ} (hQ : QRep ι q hc hs)
    (hpre : CheckPre q) : QRep ι (check q) ((checkP tk).sem hc hs).1 ((checkP tk).sem hc hs).2 := by
  rw [check_eq, checkP, sem_seq]
  exact exec2P_spec tk (startP_spec hQ hpre)

/-- **`RTQueue.snoc`.** -/
theorem snocP_spec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ} (hq : Inv q)
    (hQ : QRep ι q hc hs) (a : Fin 2) :
    QRep ι (snoc q a) ((snocP tk ι a).sem hc hs).1 ((snocP tk ι a).sem hc hs).2 := by
  rw [snocP, sem_seq, sem_seq]
  obtain ⟨b, m, e, v⟩ := decBal_spec tk hc (Function.update hs .qRear (ι a :: hs .qRear))
  simp only [Prog.sem]
  rw [e]
  show QRep ι (check _) _ _
  apply checkP_spec tk _ (CheckPre.of_pinv (snoc_pinv hq a))
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine srep_congr (fun sl hsl => ?_) hQ.state
    cases sl <;> simp_all [isRot]
  · simp [hQ.front]
  · simp [hQ.rear]
  · have hb := hQ.balance
    simp only [bal, Function.update_self] at v hb ⊢
    rw [v, Function.update_of_ne (by simp)]
    push_cast
    linarith

theorem lenf_pos {q : Queue (Fin 2)} {x : Fin 2} {f : List (Fin 2)} (hq : Inv q)
    (hfront : q.front = x :: f) : 1 ≤ q.lenf := by
  obtain ⟨P, hP⟩ := frontList_eq_append hq.sinv hq.nd
  rw [hq.lenf_eq, hP, hfront]
  simp

theorem tail_checkPre {q : Queue (Fin 2)} {x : Fin 2} {f : List (Fin 2)} (hq : Inv q)
    (hfront : q.front = x :: f) :
    CheckPre ({ q with lenf := q.lenf - 1, front := f, state := invalidate q.state } :
      Queue (Fin 2)) := by
  obtain ⟨_, hfl, _⟩ := invalidate_spec hfront hq.sinv hq.nd hq.pot_front
  have hlenf1 := lenf_pos hq hfront
  have hpl := hq.pot_len
  have hle := hq.le
  refine ⟨?_, hq.lenr_eq, ?_, ?_⟩
  · show q.lenf - 1 = (frontList (invalidate q.state) f).length
    rw [hfl, hq.lenf_eq]
    simp
  · show q.lenr ≤ q.lenf - 1 + 1
    omega
  · intro hlt
    replace hlt : q.lenf - 1 < q.lenr := hlt
    show invalidate q.state = .idle
    rw [eq_idle_of_rem_zero hq.nd (by omega)]
    rfl

/-- **`RTQueue.tail`.** -/
theorem tailP_spec {q : Queue (Fin 2)} {hc : HCtl} {hs : Slot → List Γ} (hq : Inv q)
    (hQ : QRep ι q hc hs) : QRep ι (tail q) ((tailP tk).sem hc hs).1 ((tailP tk).sem hc hs).2 := by
  rcases hfront : q.front with _ | ⟨x, f⟩
  · rw [tailP, sem_ite_pos (by simp [hview, hQ.front, hfront])]
    have ht : tail q = q := by unfold tail; rw [hfront]
    rw [ht]
    exact hQ
  · rw [tailP, sem_ite_neg (by simp [hview, hQ.front, hfront])]
    have ht : tail q
        = check { q with lenf := q.lenf - 1, front := f, state := invalidate q.state } := by
      unfold tail; rw [hfront]
    rw [ht, sem_seq, sem_seq, sem_seq]
    obtain ⟨b, m, e, v⟩ := decBal_spec tk hc (Function.update hs .qFront (hs .qFront).tail)
    simp only [Prog.sem]
    rw [e]
    apply checkP_spec tk _ (tail_checkPre hq hfront)
    have hb := hQ.balance
    have hlenf1 := lenf_pos hq hfront
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine invP_spec (srep_congr (fun sl hsl => ?_) hQ.state)
      cases sl <;> simp_all [isRot]
    · rw [sem_frame _ _ rfl]
      simp [hQ.front, hfront]
    · rw [sem_frame _ _ rfl]
      simp [hQ.rear]
    · rw [bal_frame _ rfl rfl]
      simp only [pending_invalidate]
      simp only [bal, Function.update_self] at v hb ⊢
      rw [v, Function.update_of_ne (by simp)]
      push_cast [hlenf1]
      linarith

end QueueOps

/-! ## The head operations -/

section HeadOps

variable {Γ : Type} (tk : Γ)

/-- **Arrival** of a letter `a`: `t ↦ t ++ [a]`, the head stays (queue `snoc`). -/
def arriveP (ι : Fin 2 → Γ) (a : Fin 2) : Prog Γ := snocP tk ι a

/-- **Move right** (`p ↦ p + 1`): pop `right` onto `left`, or, when `right` is empty, move the
queue's head onto `left` and dequeue it. -/
def moveRightP : Prog Γ :=
  .ite 1 (fun _ v => (v .right).isEmpty) (.moveTop .qFront .left ⨾ tailP tk)
    (.moveTop .right .left ⨾ .pop .right)

/-- **Move left** (`p ↦ p - 1`): pop `left` onto `right`. -/
def moveLeftP : Prog Γ := .moveTop .left .right ⨾ .pop .left

/-- **Forward read** `t[p]?`, from a view of depth 1: the top of `right`, else the queue's head. -/
def readFwd (v : Slot → List Γ) : Option Γ := (v .right).head?.or (v .qFront).head?

/-- **Reversed read** `t[p-1]?`, from a view of depth 1: the top of `left`. -/
def readRev (v : Slot → List Γ) : Option Γ := (v .left).head?

/-- **Availability** `p < t.length`, from a view of depth 1. -/
def available (v : Slot → List Γ) : Bool := !(v .right).isEmpty || !(v .qFront).isEmpty

theorem arriveP_depth (ι : Fin 2 → Γ) (a : Fin 2) : (arriveP tk ι a).depth = 14 := by
  simp [arriveP, snocP, checkP, startP, execP, execRev, revStep, revMove, incBal2, incBal, revLast,
    revLastMove, execApp, appStep, finishP, decBal, startRot, Prog.depth]

theorem arriveP_width (ι : Fin 2 → Γ) (a : Fin 2) : (arriveP tk ι a).width = 12 := by
  simp [arriveP, snocP, checkP, startP, execP, execRev, revStep, revMove, incBal2, incBal, revLast,
    revLastMove, execApp, appStep, finishP, decBal, startRot, Prog.width]

theorem moveRightP_depth : (moveRightP tk).depth = 17 := by
  simp [moveRightP, tailP, invP, invApp, checkP, startP, execP, execRev, revStep, revMove, incBal2,
    incBal, revLast, revLastMove, execApp, appStep, finishP, decBal, startRot, Prog.depth]

theorem moveRightP_width : (moveRightP tk).width = 12 := by
  simp [moveRightP, tailP, invP, invApp, checkP, startP, execP, execRev, revStep, revMove, incBal2,
    incBal, revLast, revLastMove, execApp, appStep, finishP, decBal, startRot, Prog.width]

theorem moveLeftP_depth : (moveLeftP (Γ := Γ)).depth = 2 := by simp [moveLeftP, Prog.depth]
theorem moveLeftP_width : (moveLeftP (Γ := Γ)).width = 1 := by simp [moveLeftP, Prog.width]

variable {ι : Fin 2 → Γ}

theorem toList_eq_nil_iff {q : Queue (Fin 2)} (hq : Inv q) : toList q = [] ↔ q.front = [] := by
  have h := head?_eq hq
  constructor
  · intro h0
    rw [h0, head?] at h
    exact List.head?_eq_none_iff.mp h
  · intro h0
    rw [head?, h0] at h
    exact List.head?_eq_none_iff.mp h.symm

theorem take_succ_reverse {t : List (Fin 2)} {k : ℕ} (hk : k < t.length) :
    (t.take (k + 1)).reverse = t[k] :: (t.take k).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp

theorem arrive_sem {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) (a : Fin 2) :
    HeadRep ι (t ++ [a]) p ((arriveP tk ι a).sem hc hs).1 ((arriveP tk ι a).sem hc hs).2 := by
  obtain ⟨hle, hleft, R, q, hq, hQ, hR, hRq⟩ := h
  refine ⟨by simp; omega, ?_, R, snoc q a, inv_snoc hq a, snocP_spec tk hq hQ a, ?_, ?_⟩
  · rw [arriveP, sem_frame _ _ rfl, hleft, List.take_append_of_le_length hle]
  · rw [arriveP, sem_frame _ _ rfl, hR]
  · rw [toList_snoc hq, ← List.append_assoc, hRq, List.drop_append_of_le_length hle]

theorem moveRight_sem {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) (hp : p < t.length) :
    HeadRep ι t (p + 1) ((moveRightP tk).sem hc hs).1 ((moveRightP tk).sem hc hs).2 := by
  obtain ⟨hle, hleft, R, q, hq, hQ, hR, hRq⟩ := h
  have hdrop := List.drop_eq_getElem_cons hp
  have htake := take_succ_reverse hp
  rcases R with _ | ⟨x, R⟩
  · rw [moveRightP, sem_ite_pos (by simp [hview, hR]), sem_seq]
    rw [List.nil_append, hdrop] at hRq
    have hfront : q.front ≠ [] := fun h0 => by
      rw [(toList_eq_nil_iff hq).mpr h0] at hRq
      exact List.cons_ne_nil _ _ hRq.symm
    obtain ⟨y, f, hyf⟩ := List.exists_cons_of_ne_nil hfront
    have hy : y = t[p] := by
      have := head?_eq hq
      rw [head?, hyf, hRq] at this
      simp only [List.head?_cons, Option.some.injEq] at this
      exact this
    refine ⟨by omega, ?_, [], tail q, inv_tail hq, ?_, ?_, ?_⟩
    · rw [sem_frame _ _ rfl]
      simp [Prog.sem, hQ.front, hyf, hy, hleft, htake]
    · apply tailP_spec tk hq
      exact qrep_congr (fun sl h1 _ => by simp [Prog.sem, Function.update_of_ne h1]) hQ
    · rw [sem_frame _ _ rfl]
      simp [Prog.sem, hR]
    · rw [List.nil_append, toList_tail hq, hRq]
      rfl
  · rw [moveRightP, sem_ite_neg (by simp [hview, hR])]
    rw [List.cons_append, hdrop] at hRq
    obtain ⟨hx, hrest⟩ := List.cons.inj hRq
    refine ⟨by omega, ?_, R, q, hq, ?_, ?_, hrest⟩
    · simp [Prog.sem, hR, hleft, htake, hx]
    · exact qrep_congr (fun sl h1 h2 => by
        simp [Prog.sem, Function.update_of_ne h1, Function.update_of_ne h2]) hQ
    · simp [Prog.sem, hR]

theorem moveLeft_sem {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) (hp : 0 < p) :
    HeadRep ι t (p - 1) ((moveLeftP (Γ := Γ)).sem hc hs).1 ((moveLeftP (Γ := Γ)).sem hc hs).2 := by
  obtain ⟨hle, hleft, R, q, hq, hQ, hR, hRq⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  have hk : k < t.length := by omega
  have htake := take_succ_reverse hk
  refine ⟨by omega, ?_, t[k] :: R, q, hq, ?_, ?_, ?_⟩
  · simp [moveLeftP, Prog.sem, hleft, htake]
  · exact qrep_congr (fun sl h1 h2 => by
      simp [moveLeftP, Prog.sem, Function.update_of_ne h1, Function.update_of_ne h2]) hQ
  · simp [moveLeftP, Prog.sem, hleft, htake, hR]
  · rw [Nat.add_sub_cancel, List.cons_append, hRq]
    exact (List.drop_eq_getElem_cons hk).symm

theorem readFwd_eq {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) : readFwd (hview 1 hs) = t[p]?.map ι := by
  obtain ⟨hle, hleft, R, q, hq, hQ, hR, hRq⟩ := h
  rw [← List.head?_drop, ← hRq]
  rcases R with _ | ⟨x, R⟩
  · have := head?_eq hq
    simp only [head?] at this
    simp [readFwd, hview, hR, hQ.front, ← this, enc, List.head?_take, List.head?_map]
  · simp [readFwd, hview, hR]

theorem readRev_eq {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) :
    readRev (hview 1 hs) = (if p = 0 then none else t[p - 1]?).map ι := by
  obtain ⟨hle, hleft, _⟩ := h
  rcases p with _ | k
  · simp [readRev, hview, hleft]
  · have hk : k < t.length := by omega
    simp [readRev, hview, hleft, take_succ_reverse hk, hk]

theorem available_eq {t : List (Fin 2)} {p : ℕ} {hc : HCtl} {hs : Slot → List Γ}
    (h : HeadRep ι t p hc hs) : available (hview 1 hs) = decide (p < t.length) := by
  obtain ⟨hle, hleft, R, q, hq, hQ, hR, hRq⟩ := h
  have e : p < t.length ↔ ¬ (R ++ toList q = []) := by
    rw [hRq, List.drop_eq_nil_iff]
    omega
  rw [Bool.eq_iff_iff, decide_eq_true_eq, e, List.append_eq_nil_iff, toList_eq_nil_iff hq]
  cases R <;> cases hf : q.front <;> simp [available, hview, hR, hQ.front, hf]

end HeadOps

/-! ## The operations as local rules on a configuration -/

section Global

variable {Γ C : Type} {K : ℕ} (ι : Fin 2 → Γ) (tk : Γ)

/-- The head whose control is at `lc` and whose slots are the stacks `ix` represents `(t, p)`. -/
def GHeadRep (lc : Lens C HCtl) (ix : Slot → Fin K) (t : List (Fin 2)) (p : ℕ) (c : C)
    (st : Fin K → List Γ) : Prop :=
  HeadRep ι t p (lc.get c) (fun s => st (ix s))

variable (lc : Lens C HCtl) (ix : Slot → Fin K)

/-- The rule for `arrive a`. -/
def arriveRule (a : Fin 2) : Rule Γ C K (arriveP tk ι a).depth (arriveP tk ι a).width :=
  (arriveP tk ι a).toRule lc ix

/-- The rule for `moveRight`. -/
def moveRightRule : Rule Γ C K (moveRightP tk).depth (moveRightP tk).width :=
  (moveRightP tk).toRule lc ix

/-- The rule for `moveLeft`. -/
def moveLeftRule : Rule Γ C K (moveLeftP (Γ := Γ)).depth (moveLeftP (Γ := Γ)).width :=
  (moveLeftP (Γ := Γ)).toRule lc ix

theorem arrive_isLocal (a : Fin 2) : IsLocal 14 12 (arriveRule ι tk lc ix a).run :=
  IsLocal.mono ⟨_, fun _ _ => rfl⟩ (arriveP_depth tk ι a).le (arriveP_width tk ι a).le

theorem moveRight_isLocal : IsLocal 17 12 (moveRightRule tk lc ix).run :=
  IsLocal.mono ⟨_, fun _ _ => rfl⟩ (moveRightP_depth tk).le (moveRightP_width tk).le

theorem moveLeft_isLocal : IsLocal 2 1 (moveLeftRule (Γ := Γ) lc ix).run :=
  IsLocal.mono ⟨_, fun _ _ => rfl⟩ moveLeftP_depth.le moveLeftP_width.le

/-- **Arrival is correct**: `t ↦ t ++ [a]`, same position. -/
theorem arrive_correct (hix : Function.Injective ix) (a : Fin 2) {t : List (Fin 2)} {p : ℕ}
    {c : C} {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) :
    GHeadRep ι lc ix (t ++ [a]) p ((arriveRule ι tk lc ix a).run c st).1
      ((arriveRule ι tk lc ix a).run c st).2 := by
  unfold GHeadRep arriveRule at *
  exact transfer lc hix (arriveP tk ι a) (P := fun hc hs => HeadRep ι t p hc hs)
    (Q := fun hc hs => HeadRep ι (t ++ [a]) p hc hs) (fun _ _ hr => arrive_sem tk hr a) c st h

/-- **Moving right is correct**: `p ↦ p + 1` when `p < t.length`. -/
theorem moveRight_correct (hix : Function.Injective ix) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) (hp : p < t.length) :
    GHeadRep ι lc ix t (p + 1) ((moveRightRule tk lc ix).run c st).1
      ((moveRightRule tk lc ix).run c st).2 := by
  unfold GHeadRep moveRightRule at *
  exact transfer lc hix (moveRightP tk) (P := fun hc hs => HeadRep ι t p hc hs)
    (Q := fun hc hs => HeadRep ι t (p + 1) hc hs) (fun _ _ hr => moveRight_sem tk hr hp) c st h

/-- **Moving left is correct**: `p ↦ p - 1` when `0 < p`. -/
theorem moveLeft_correct (hix : Function.Injective ix) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) (hp : 0 < p) :
    GHeadRep ι lc ix t (p - 1) ((moveLeftRule lc ix).run c st).1
      ((moveLeftRule lc ix).run c st).2 := by
  unfold GHeadRep moveLeftRule at *
  exact transfer lc hix (moveLeftP (Γ := Γ)) (P := fun hc hs => HeadRep ι t p hc hs)
    (Q := fun hc hs => HeadRep ι t (p - 1) hc hs) (fun _ _ hr => moveLeft_sem hr hp) c st h

/-- **Forward read** from the view of depth 1: `t[p]?`. -/
theorem readFwd_correct {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ}
    (h : GHeadRep ι lc ix t p c st) : readFwd (fun s => view 1 st (ix s)) = t[p]?.map ι :=
  readFwd_eq h

/-- **Reversed read** from the view of depth 1: `t[p-1]?` (nothing at `p = 0`). -/
theorem readRev_correct {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ}
    (h : GHeadRep ι lc ix t p c st) :
    readRev (fun s => view 1 st (ix s)) = (if p = 0 then none else t[p - 1]?).map ι :=
  readRev_eq h

/-- **Availability** from the view of depth 1: `p < t.length`. -/
theorem available_correct {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ}
    (h : GHeadRep ι lc ix t p c st) :
    available (fun s => view 1 st (ix s)) = decide (p < t.length) :=
  available_eq h

/-- Another head (disjoint stacks, independent control) is unaffected by a head's program. -/
theorem other_head_preserved (hix : Function.Injective ix) (prog : Prog Γ) {lB : Lens C HCtl}
    {ixB : Slot → Fin K} (hdisj : ∀ s s', ix s ≠ ixB s')
    (hindep : ∀ c h, lB.get (lc.set c h) = lB.get c) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lB ixB t p c st) :
    GHeadRep ι lB ixB t p ((prog.toRule lc ix).run c st).1 ((prog.toRule lc ix).run c st).2 := by
  unfold GHeadRep at *
  rw [run_ctl_indep lc hix prog lB.get hindep]
  have : (fun s => ((prog.toRule lc ix).run c st).2 (ixB s)) = fun s => st (ixB s) :=
    funext fun s => run_frame lc hix prog c st (ixB s) (fun s' => hdisj s' s)
  rw [this]
  exact h

/-! ### `copyFrom`: the O(1) alias -/

/-- All slots. -/
def allSlots : List Slot :=
  [.left, .right, .qFront, .qRear, .rotFront, .rotFrontRev, .rotRear, .rotNewFront, .rotValid,
    .balance]

/-- The slot a stack holds, if it is one of the head's. -/
def slotOf (ixB : Slot → Fin K) (k : Fin K) : Option Slot :=
  allSlots.find? (fun s => decide (ixB s = k))

theorem slotOf_ix {ixB : Slot → Fin K} (hixB : Function.Injective ixB) (s : Slot) :
    slotOf ixB (ixB s) = some s := by
  cases s <;> simp [slotOf, allSlots, List.find?, hixB.eq_iff]

theorem slotOf_none {ixB : Slot → Fin K} {k : Fin K} (hk : ∀ s, ixB s ≠ k) :
    slotOf ixB k = none := by
  simp [slotOf, List.find?_eq_none, hk]

/-- **`copyFrom`**: head `B` (control at `lB`, slots `ixB`) becomes a copy of head `A`: every
slot of `B` is copied from the same slot of `A`, and `B`'s control from `A`'s. -/
def copyFromRule (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) : Rule Γ C K 0 0 where
  f c _ := (lB.set c (lA.get c), fun k =>
    match slotOf ixB k with
    | some s => copyRw (ixA s)
    | none => keep k)
  pre_le c v k := by dsimp only; split <;> simp [copyRw, keep]
  drop_le c v k := by dsimp only; split <;> simp [copyRw, keep]

theorem copyFrom_isLocal (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) :
    IsLocal 0 0 (copyFromRule (Γ := Γ) lA lB ixA ixB).run := ⟨_, fun _ _ => rfl⟩

/-- The stacks after `copyFrom`. -/
def copyStacks (ixA ixB : Slot → Fin K) (st : Fin K → List Γ) : Fin K → List Γ := fun k =>
  match slotOf ixB k with
  | some s => st (ixA s)
  | none => st k

theorem copyFrom_run (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) (c : C)
    (st : Fin K → List Γ) :
    (copyFromRule lA lB ixA ixB).run c st = (lB.set c (lA.get c), copyStacks ixA ixB st) := by
  refine Prod.ext rfl (funext fun k => ?_)
  cases h : slotOf ixB k <;> simp [Rule.run, copyFromRule, copyStacks, h, apply_copy, apply_keep]

/-- **`copyFrom` is correct**: `B` represents `A`'s `(t, p)`, `A` still does, and no stack
outside `B`'s slots changes. -/
theorem copyFrom_correct {lA lB : Lens C HCtl} {ixA ixB : Slot → Fin K}
    (hixB : Function.Injective ixB) (hdisj : ∀ s s', ixA s ≠ ixB s')
    (hindep : ∀ c h, lA.get (lB.set c h) = lA.get c) {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lA ixA t p c st) :
    GHeadRep ι lB ixB t p ((copyFromRule lA lB ixA ixB).run c st).1
        ((copyFromRule lA lB ixA ixB).run c st).2 ∧
      GHeadRep ι lA ixA t p ((copyFromRule lA lB ixA ixB).run c st).1
        ((copyFromRule lA lB ixA ixB).run c st).2 ∧
      ∀ k, (∀ s, ixB s ≠ k) → ((copyFromRule lA lB ixA ixB).run c st).2 k = st k := by
  rw [copyFrom_run]
  have hB : (fun s => copyStacks ixA ixB st (ixB s)) = fun s => st (ixA s) := by
    funext s; simp [copyStacks, slotOf_ix hixB]
  have hA : (fun s => copyStacks ixA ixB st (ixA s)) = fun s => st (ixA s) := by
    funext s; simp [copyStacks, slotOf_none (fun s' => (hdisj s s').symm)]
  refine ⟨?_, ?_, fun k hk => by simp [copyStacks, slotOf_none hk]⟩
  · unfold GHeadRep at *
    rw [lB.get_set, hB]
    exact h
  · unfold GHeadRep at *
    rw [hindep, hA]
    exact h

/-! ### Moving by a bounded delta -/

/-- One application of a rule, as a map on configurations. -/
def stepOf {D E : ℕ} (R : Rule Γ C K D E) : C × (Fin K → List Γ) → C × (Fin K → List Γ) :=
  fun x => R.run x.1 x.2

theorem moveRightN_isLocal (n : ℕ) :
    IsLocal (17 * n) (12 * n) (fun c st => (stepOf (moveRightRule tk lc ix))^[n] (c, st)) :=
  (moveRight_isLocal tk lc ix).iterate n

theorem moveLeftN_isLocal (n : ℕ) :
    IsLocal (2 * n) (1 * n) (fun c st => (stepOf (moveLeftRule (Γ := Γ) lc ix))^[n] (c, st)) :=
  (moveLeft_isLocal lc ix).iterate n

theorem moveRightN_correct (hix : Function.Injective ix) :
    ∀ (n : ℕ) {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ},
      GHeadRep ι lc ix t p c st → p + n ≤ t.length →
      GHeadRep ι lc ix t (p + n) ((stepOf (moveRightRule tk lc ix))^[n] (c, st)).1
        ((stepOf (moveRightRule tk lc ix))^[n] (c, st)).2
  | 0, _, _, _, _, h, _ => h
  | n + 1, t, p, c, st, h, hn => by
    rw [Function.iterate_succ_apply', show p + (n + 1) = p + n + 1 by omega]
    have hpn : p + n < t.length := by omega
    exact moveRight_correct ι tk lc ix hix (moveRightN_correct hix n h hpn.le) hpn

theorem moveLeftN_correct (hix : Function.Injective ix) :
    ∀ (n : ℕ) {t : List (Fin 2)} {p : ℕ} {c : C} {st : Fin K → List Γ},
      GHeadRep ι lc ix t p c st → n ≤ p →
      GHeadRep ι lc ix t (p - n) ((stepOf (moveLeftRule (Γ := Γ) lc ix))^[n] (c, st)).1
        ((stepOf (moveLeftRule (Γ := Γ) lc ix))^[n] (c, st)).2
  | 0, _, _, _, _, h, _ => h
  | n + 1, t, p, c, st, h, hn => by
    rw [Function.iterate_succ_apply', show p - (n + 1) = p - n - 1 by omega]
    have hpn : 0 < p - n := by omega
    exact moveLeft_correct ι lc ix hix (moveLeftN_correct hix n h (by omega)) hpn

/-- Move the head by `δ` (a fixed integer): `|δ|` right or left steps. -/
def moveBy (δ : ℤ) (c : C) (st : Fin K → List Γ) : C × (Fin K → List Γ) :=
  if 0 ≤ δ then (stepOf (moveRightRule tk lc ix))^[δ.toNat] (c, st)
  else (stepOf (moveLeftRule (Γ := Γ) lc ix))^[(-δ).toNat] (c, st)

/-- **Moving by `δ` is local**, with constants linear in `|δ|`. -/
theorem moveBy_isLocal (δ : ℤ) :
    IsLocal (17 * δ.natAbs) (12 * δ.natAbs) (moveBy tk lc ix δ) := by
  by_cases hδ : 0 ≤ δ
  · have e : moveBy tk lc ix δ
        = fun c st => (stepOf (moveRightRule tk lc ix))^[δ.toNat] (c, st) := by
      funext c st; simp [moveBy, hδ]
    rw [e, show δ.natAbs = δ.toNat by omega]
    exact moveRightN_isLocal tk lc ix δ.toNat
  · have e : moveBy tk lc ix δ
        = fun c st => (stepOf (moveLeftRule (Γ := Γ) lc ix))^[(-δ).toNat] (c, st) := by
      funext c st; simp [moveBy, hδ]
    rw [e, show δ.natAbs = (-δ).toNat by omega]
    exact (moveLeftN_isLocal lc ix _).mono (by omega) (by omega)

/-- **Moving by `δ` is correct** when `0 ≤ p + δ ≤ t.length`. -/
theorem moveBy_correct (hix : Function.Injective ix) {δ : ℤ} {t : List (Fin 2)} {p : ℕ} {c : C}
    {st : Fin K → List Γ} (h : GHeadRep ι lc ix t p c st) (h0 : 0 ≤ (p : ℤ) + δ)
    (h1 : (p : ℤ) + δ ≤ t.length) :
    GHeadRep ι lc ix t ((p : ℤ) + δ).toNat (moveBy tk lc ix δ c st).1
      (moveBy tk lc ix δ c st).2 := by
  by_cases hδ : 0 ≤ δ
  · simp only [moveBy, hδ, if_true]
    rw [show ((p : ℤ) + δ).toNat = p + δ.toNat by omega]
    exact moveRightN_correct ι tk lc ix hix δ.toNat h (by omega)
  · simp only [moveBy, hδ, if_false]
    rw [show ((p : ℤ) + δ).toNat = p - (-δ).toNat by omega]
    exact moveLeftN_correct ι lc ix hix (-δ).toNat h (by omega)

end Global

/-- info: 'PalPeg.ScaHeadRep.arrive_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms arrive_correct

/-- info: 'PalPeg.ScaHeadRep.moveBy_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms moveBy_correct

/-- info: 'PalPeg.ScaHeadRep.copyFrom_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms copyFrom_correct

/-- info: 'PalPeg.ScaHeadRep.other_head_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms other_head_preserved

end PalPeg.ScaHeadRep
