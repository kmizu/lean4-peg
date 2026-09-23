import PalPeg.ScaWindowEncodeTick
import PalPeg.ScaHeadBridge
import PalPeg.ScaWindowInstance

/-!
# The real window workers as stack programs (`WorkerEnc` instances)

`ScaWindowEncode.WorkerEnc` asks for a stack-program encoding of a worker kind. This file gives
one for every `ScaWindowWorker.Worker` (generically in the worker's static data), and
instantiates it for the two real workers `ScaWindowInstance.matcher` / `flagsW`.

## Layout

* **Heads.** `R + 4` heads (`ScaHeadRep`: ten stacks and a finite control part each): the `R`
  reader registers, `begin`, `end`, a head parked at position `0` (read in place of a register
  index that has no register, whose abstract position is `getD _ 0 = 0`), and a scratch head
  holding the copy source's snapshot during a step.
* **Counters.** `2·D + 2` signed unary counters (sign in the control, magnitude a stack of `tok`):
  the `D` distance registers, `D` snapshot counters for `execute`'s simultaneous transfer, the
  `length` key and the `h` key.
* **Flags.** One stack of flag symbols.
* **Control.** `pc` (below `pcBound`), `mode`, `output`, the reader `reverse` bits, the heads'
  control parts, the counters' signs, and two scratch bits (the step's decision, the snapshot's
  `reverse` bit).

## Faults

`WorkerEnc` asks for the representation only after operations that do not fault, and faults are
sticky. The representation therefore includes `fault = false`, and the programs do not compute
the fault bit at all: in a non-faulting run every `require` held (every head move stayed inside
the text, every read was available), which is what the correctness proofs use. `faulted` reads
`false` off the control, which is exact on represented states.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace PalPeg.ScaWorkerEnc
open PalPeg.ScaLocal PalPeg.ScaProg PalPeg.ScaHeadRep PalPeg.ScaHeadBridge
open PalPeg.ScaWindowWorker

/-! ## Symbols -/

/-- Stack symbols: letters, the unary token, flag bits. -/
inductive Sym where
  | letter (a : Fin 2)
  | tok
  | flag (b : Bool)
  deriving DecidableEq

instance : Inhabited Sym := ⟨.tok⟩

instance : Finite Sym :=
  Finite.of_injective
    (fun x : Sym => match x with
      | .letter a => (some (Sum.inl a) : Option (Fin 2 ⊕ Bool))
      | .tok => none
      | .flag b => some (Sum.inr b))
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- Letters as symbols. -/
def ι : Fin 2 → Sym := Sym.letter

theorem ι_inj : Function.Injective ι := fun _ _ h => by cases h; rfl

/-- Decoding a flag symbol. -/
def flagDec : Sym → Bool
  | .flag b => b
  | _ => false

/-! ## Stack layout -/

/-- Slot numbering inside a head's block of ten stacks. -/
def slotNum : Slot → ℕ
  | .left => 0 | .right => 1 | .qFront => 2 | .qRear => 3 | .rotFront => 4
  | .rotFrontRev => 5 | .rotRear => 6 | .rotNewFront => 7 | .rotValid => 8 | .balance => 9

theorem slotNum_lt (s : Slot) : slotNum s < 10 := by cases s <;> decide

theorem slotNum_inj {s s' : Slot} (h : slotNum s = slotNum s') : s = s' := by
  cases s <;> cases s' <;> first | rfl | (simp [slotNum] at h)

/-- Number of stacks: `R + 4` heads of ten stacks, `NC` counters, the flag stack. -/
abbrev KW (R NC : ℕ) : ℕ := 10 * (R + 4) + NC + 1

section Layout
variable {R NC : ℕ}

def ixH (h : Fin (R + 4)) (s : Slot) : Fin (KW R NC) :=
  ⟨10 * h.val + slotNum s, by have := slotNum_lt s; have := h.isLt; dsimp only [KW]; omega⟩

def ixC (j : Fin NC) : Fin (KW R NC) :=
  ⟨10 * (R + 4) + j.val, by have := j.isLt; dsimp only [KW]; omega⟩

def ixF : Fin (KW R NC) := ⟨10 * (R + 4) + NC, by dsimp only [KW]; omega⟩

theorem ixH_inj (h : Fin (R + 4)) : Function.Injective (ixH (NC := NC) h) := by
  intro s s' e
  simp only [ixH, Fin.mk.injEq] at e
  exact slotNum_inj (by omega)

theorem ixH_ne {h h' : Fin (R + 4)} (hh : h ≠ h') (s s' : Slot) :
    ixH (NC := NC) h s ≠ ixH h' s' := by
  intro e
  simp only [ixH, Fin.mk.injEq] at e
  have := slotNum_lt s; have := slotNum_lt s'
  exact hh (Fin.ext (by omega))

theorem ixH_ne_ixC (h : Fin (R + 4)) (s : Slot) (j : Fin NC) : ixH h s ≠ ixC j := by
  intro e
  simp only [ixH, ixC, Fin.mk.injEq] at e
  have := slotNum_lt s; have := h.isLt
  omega

theorem ixH_ne_ixF (h : Fin (R + 4)) (s : Slot) : ixH h s ≠ (ixF : Fin (KW R NC)) := by
  intro e
  simp only [ixH, ixF, Fin.mk.injEq] at e
  have := slotNum_lt s; have := h.isLt
  omega

theorem ixC_ne_ixF (j : Fin NC) : ixC j ≠ (ixF : Fin (KW R NC)) := by
  intro e
  simp only [ixC, ixF, Fin.mk.injEq] at e
  have := j.isLt
  omega

theorem ixC_inj : Function.Injective (ixC (R := R) (NC := NC)) := by
  intro j j' e
  simp only [ixC, Fin.mk.injEq] at e
  exact Fin.ext (by omega)

end Layout

/-! ## Control -/

def phaseNum : Phase → Fin 4
  | .idle => 0
  | .reversing => 1
  | .appending => 2
  | .done => 3

instance : Finite Phase :=
  Finite.of_injective phaseNum (by intro a b h; cases a <;> cases b <;> simp_all [phaseNum])

instance : Finite HCtl :=
  Finite.of_injective (fun x : HCtl => (x.phase, x.balanceNeg))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; simp [h])

def modeNum : Mode → Fin 3
  | .idle => 0
  | .run => 1
  | .done => 2

instance : Finite Mode :=
  Finite.of_injective modeNum (by intro a b h; cases a <;> cases b <;> simp_all [modeNum])

/-- The finite control. -/
structure Ctl (R NC N : ℕ) where
  pc : Fin N
  mode : Mode
  output : Bool
  rev : Fin R → Bool
  hc : Fin (R + 4) → HCtl
  sg : Fin NC → Bool
  dec : Bool
  srev : Bool

instance {R NC N : ℕ} : Finite (Ctl R NC N) :=
  Finite.of_injective
    (fun x : Ctl R NC N => (x.pc, x.mode, x.output, x.rev, x.hc, x.sg, x.dec, x.srev))
    (by intro a b h; cases a; cases b; simp only [Prod.mk.injEq] at h; simp [h])

section Lenses
variable {R NC N : ℕ}

/-- Head `h`'s control part. -/
def hl (h : Fin (R + 4)) : Lens (Ctl R NC N) HCtl where
  get c := c.hc h
  set c x := { c with hc := Function.update c.hc h x }
  get_set c x := by simp
  set_get c := by cases c; simp
  set_set c x y := by simp

/-- Counter `j`'s sign. -/
def sl (j : Fin NC) : Lens (Ctl R NC N) Bool where
  get c := c.sg j
  set c x := { c with sg := Function.update c.sg j x }
  get_set c x := by simp
  set_get c := by cases c; simp
  set_set c x y := by simp

@[simp] theorem sl_get (j : Fin NC) (c : Ctl R NC N) : (sl j).get c = c.sg j := rfl
@[simp] theorem hl_get (h : Fin (R + 4)) (c : Ctl R NC N) : (hl h).get c = c.hc h := rfl

theorem hl_indep {h h' : Fin (R + 4)} (hh : h ≠ h') (c : Ctl R NC N) (x : HCtl) :
    (hl h').get ((hl h).set c x) = (hl h').get c := by
  simp [hl, Function.update_of_ne (Ne.symm hh)]

end Lenses

/-! ## Frames: which stacks a program writes, which control fields it keeps -/

section Frame
variable {Γ C : Type} {K : ℕ}

/-- Every stack the program writes satisfies `S`. -/
def WritesIn (S : Fin K → Prop) : Prog Γ C K → Prop
  | .skip => True
  | .ctl _ => True
  | .push k _ => S k
  | .pop k => S k
  | .copy _ d => S d
  | .clear k => S k
  | .seq p q => WritesIn S p ∧ WritesIn S q
  | .ite _ p q => WritesIn S p ∧ WritesIn S q

/-- Every control update of the program keeps `f`. -/
def CKeeps {α : Type} (f : C → α) : Prog Γ C K → Prop
  | .ctl g => ∀ c v, f (g c v) = f c
  | .seq p q => CKeeps f p ∧ CKeeps f q
  | .ite _ p q => CKeeps f p ∧ CKeeps f q
  | _ => True

theorem eval_st_frame (S : Fin K → Prop) (D : ℕ) :
    ∀ (p : Prog Γ C K), WritesIn S p → ∀ (c : C) (st : Fin K → List Γ) (k : Fin K), ¬ S k →
      (p.eval D c st).2 k = st k
  | .skip, _, _, _, _, _ => rfl
  | .ctl _, _, _, _, _, _ => rfl
  | .push j _, hw, _, _, k, hk => Function.update_of_ne (fun e => hk (by rw [e]; exact hw)) _ _
  | .pop j, hw, _, _, k, hk => Function.update_of_ne (fun e => hk (by rw [e]; exact hw)) _ _
  | .copy _ j, hw, _, _, k, hk => Function.update_of_ne (fun e => hk (by rw [e]; exact hw)) _ _
  | .clear j, hw, _, _, k, hk => Function.update_of_ne (fun e => hk (by rw [e]; exact hw)) _ _
  | .seq p q, hw, c, st, k, hk => by
    simp only [Prog.eval]
    rw [eval_st_frame S D q hw.2 _ _ k hk, eval_st_frame S D p hw.1 _ _ k hk]
  | .ite _ p q, hw, c, st, k, hk => by
    simp only [Prog.eval]
    split
    · exact eval_st_frame S D p hw.1 c st k hk
    · exact eval_st_frame S D q hw.2 c st k hk

theorem eval_ctl_frame {α : Type} (f : C → α) (D : ℕ) :
    ∀ (p : Prog Γ C K), CKeeps f p → ∀ (c : C) (st : Fin K → List Γ),
      f (p.eval D c st).1 = f c
  | .skip, _, _, _ => rfl
  | .ctl g, hk, c, st => hk c _
  | .push _ _, _, _, _ => rfl
  | .pop _, _, _, _ => rfl
  | .copy _ _, _, _, _ => rfl
  | .clear _, _, _, _ => rfl
  | .seq p q, hk, c, st => by
    simp only [Prog.eval]
    rw [eval_ctl_frame f D q hk.2, eval_ctl_frame f D p hk.1]
  | .ite _ p q, hk, c, st => by
    simp only [Prog.eval]
    split
    · exact eval_ctl_frame f D p hk.1 c st
    · exact eval_ctl_frame f D q hk.2 c st

theorem writesIn_mono {S T : Fin K → Prop} (hST : ∀ k, S k → T k) :
    ∀ p : Prog Γ C K, WritesIn S p → WritesIn T p
  | .skip, _ => trivial
  | .ctl _, _ => trivial
  | .push _ _, h => hST _ h
  | .pop _, h => hST _ h
  | .copy _ _, h => hST _ h
  | .clear _, h => hST _ h
  | .seq p q, h => ⟨writesIn_mono hST p h.1, writesIn_mono hST q h.2⟩
  | .ite _ p q, h => ⟨writesIn_mono hST p h.1, writesIn_mono hST q h.2⟩

theorem evalSeq (p q : Prog Γ C K) (D : ℕ) (c : C) (st : Fin K → List Γ) :
    (Prog.seq p q).eval D c st = q.eval D (p.eval D c st).1 (p.eval D c st).2 := rfl

/-- Sequencing a list of programs. -/
def seqList {α : Type} (P : α → Prog Γ C K) (l : List α) : Prog Γ C K :=
  l.foldr (fun a p => .seq (P a) p) .skip

theorem writesIn_seqList {α : Type} {S : Fin K → Prop} {P : α → Prog Γ C K} :
    ∀ l : List α, (∀ a ∈ l, WritesIn S (P a)) → WritesIn S (seqList P l)
  | [], _ => trivial
  | a :: l, h => ⟨h a (by simp), writesIn_seqList l fun b hb => h b (by simp [hb])⟩

theorem ckeeps_seqList {α β : Type} {f : C → β} {P : α → Prog Γ C K} :
    ∀ l : List α, (∀ a ∈ l, CKeeps f (P a)) → CKeeps f (seqList P l)
  | [], _ => trivial
  | a :: l, h => ⟨h a (by simp), ckeeps_seqList l fun b hb => h b (by simp [hb])⟩

theorem writesIn_repeat {S : Fin K → Prop} {p : Prog Γ C K} (hp : WritesIn S p) :
    ∀ n, WritesIn S (repeatProg p n)
  | 0 => trivial
  | n + 1 => ⟨hp, writesIn_repeat hp n⟩

theorem ckeeps_repeat {β : Type} {f : C → β} {p : Prog Γ C K} (hp : CKeeps f p) :
    ∀ n, CKeeps f (repeatProg p n)
  | 0 => trivial
  | n + 1 => ⟨hp, ckeeps_repeat hp n⟩

/-- **Running a list of programs.** Each `P a` turns `A a` into `B a` (given the global `G`), keeps
`G`, and keeps `A b`, `B b` of every other `b`. Then the sequence turns all `A`s into `B`s. -/
theorem seqList_spec {α : Type} (D : ℕ) (P : α → Prog Γ C K)
    (G : C → (Fin K → List Γ) → Prop) (A B : α → C → (Fin K → List Γ) → Prop)
    (hstep : ∀ a c st, G c st → A a c st → B a ((P a).eval D c st).1 ((P a).eval D c st).2)
    (hG : ∀ a c st, G c st → G ((P a).eval D c st).1 ((P a).eval D c st).2)
    (hA : ∀ a b c st, a ≠ b → A b c st → A b ((P a).eval D c st).1 ((P a).eval D c st).2)
    (hB : ∀ a b c st, a ≠ b → B b c st → B b ((P a).eval D c st).1 ((P a).eval D c st).2) :
    ∀ (l : List α), l.Nodup → ∀ c st, G c st → (∀ a ∈ l, A a c st) →
      G ((seqList P l).eval D c st).1 ((seqList P l).eval D c st).2 ∧
      ∀ a ∈ l, B a ((seqList P l).eval D c st).1 ((seqList P l).eval D c st).2
  | [], _, c, st, hg, _ => ⟨hg, fun _ h => by simp at h⟩
  | a :: l, hl, c, st, hg, hA0 => by
    have hnd := List.nodup_cons.mp hl
    have hB1 := hstep a c st hg (hA0 a (by simp))
    have hG1 := hG a c st hg
    have hA1 : ∀ b ∈ l, A b ((P a).eval D c st).1 ((P a).eval D c st).2 := fun b hb =>
      hA a b c st (fun e => hnd.1 (e ▸ hb)) (hA0 b (by simp [hb]))
    obtain ⟨hG2, hB2⟩ := seqList_spec D P G A B hstep hG hA hB l hnd.2 _ _ hG1 hA1
    refine ⟨hG2, fun b hb => ?_⟩
    simp only [List.mem_cons] at hb
    show B b ((seqList P l).eval D ((P a).eval D c st).1 ((P a).eval D c st).2).1
      ((seqList P l).eval D ((P a).eval D c st).1 ((P a).eval D c st).2).2
    rcases hb with rfl | hb
    · -- `B b` survives the rest of the list
      have key : ∀ (l' : List α), b ∉ l' → ∀ c' st', B b c' st' →
          B b ((seqList P l').eval D c' st').1 ((seqList P l').eval D c' st').2 := by
        intro l'
        induction l' with
        | nil => intro _ c' st' h; exact h
        | cons x l' ih =>
          intro hx c' st' h
          simp only [List.mem_cons, not_or] at hx
          exact ih hx.2 _ _ (hB x b c' st' (Ne.symm hx.1) h)
      exact key l hnd.1 _ _ hB1
    · exact hB2 b hb

/-- A predicate kept by every program of a list is kept by the sequence. -/
theorem seqList_keep {α : Type} (D : ℕ) (P : α → Prog Γ C K) (F : C → (Fin K → List Γ) → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∀ c st, F c st → F ((P a).eval D c st).1 ((P a).eval D c st).2) →
      ∀ c st, F c st → F ((seqList P l).eval D c st).1 ((seqList P l).eval D c st).2
  | [], _, _, _, h => h
  | a :: l, hP, c, st, h =>
    seqList_keep D P F l (fun b hb => hP b (by simp [hb])) _ _ (hP a (by simp) c st h)

end Frame

/-! ## Frames of the head programs -/

section HeadFrame
variable {Γ C : Type} {K : ℕ} [Inhabited Γ]

theorem writesIn_toProg (lc : Lens C HCtl) (ix : Slot → Fin K) :
    ∀ p : ScaHeadRep.Prog Γ, WritesIn (fun k => ∃ s, ix s = k) (toProg lc ix p)
  | .skip => trivial
  | .push _ a => ⟨a, rfl⟩
  | .pop a => ⟨a, rfl⟩
  | .moveTop _ a => ⟨trivial, ⟨a, rfl⟩⟩
  | .copy _ a => ⟨a, rfl⟩
  | .clear a => ⟨a, rfl⟩
  | .setPhase _ => trivial
  | .setNeg _ => trivial
  | .seq p q => ⟨writesIn_toProg lc ix p, writesIn_toProg lc ix q⟩
  | .ite _ _ p q => ⟨writesIn_toProg lc ix p, writesIn_toProg lc ix q⟩

theorem ckeeps_toProg {α : Type} (lc : Lens C HCtl) (ix : Slot → Fin K) (f : C → α)
    (hf : ∀ c x, f (lc.set c x) = f c) :
    ∀ p : ScaHeadRep.Prog Γ, CKeeps f (toProg lc ix p)
  | .skip => trivial
  | .push _ _ => trivial
  | .pop _ => trivial
  | .moveTop _ _ => ⟨trivial, trivial⟩
  | .copy _ _ => trivial
  | .clear _ => trivial
  | .setPhase _ => fun c _ => hf c _
  | .setNeg _ => fun c _ => hf c _
  | .seq p q => ⟨ckeeps_toProg lc ix f hf p, ckeeps_toProg lc ix f hf q⟩
  | .ite _ _ p q => ⟨ckeeps_toProg lc ix f hf p, ckeeps_toProg lc ix f hf q⟩

theorem writesIn_moveBy (tk : Γ) (lc : Lens C HCtl) (ix : Slot → Fin K) (δ : ℤ) :
    WritesIn (fun k => ∃ s, ix s = k) (moveByProg tk lc ix δ) := by
  unfold moveByProg
  split
  · exact writesIn_repeat (writesIn_toProg lc ix _) _
  · exact writesIn_repeat (writesIn_toProg lc ix _) _

theorem ckeeps_moveBy {α : Type} (tk : Γ) (lc : Lens C HCtl) (ix : Slot → Fin K) (δ : ℤ)
    (f : C → α) (hf : ∀ c x, f (lc.set c x) = f c) : CKeeps f (moveByProg tk lc ix δ) := by
  unfold moveByProg
  split
  · exact ckeeps_repeat (ckeeps_toProg lc ix f hf _) _
  · exact ckeeps_repeat (ckeeps_toProg lc ix f hf _) _

omit [Inhabited Γ] in
theorem writesIn_copies (ixA ixB : Slot → Fin K) (tail : ScaProg.Prog Γ C K)
    (ht : WritesIn (fun k => ∃ s, ixB s = k) tail) :
    ∀ l : List Slot, WritesIn (fun k => ∃ s, ixB s = k) (copiesProg ixA ixB tail l)
  | [] => ht
  | s :: l => ⟨⟨s, rfl⟩, writesIn_copies ixA ixB tail ht l⟩

omit [Inhabited Γ] in
theorem ckeeps_copies {α : Type} (ixA ixB : Slot → Fin K) (tail : ScaProg.Prog Γ C K) (f : C → α)
    (ht : CKeeps f tail) :
    ∀ l : List Slot, CKeeps f (copiesProg ixA ixB tail l)
  | [] => ht
  | _ :: l => ⟨trivial, ckeeps_copies ixA ixB tail f ht l⟩

omit [Inhabited Γ] in
theorem writesIn_copyFrom (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) :
    WritesIn (fun k => ∃ s, ixB s = k) (copyFromProg (Γ := Γ) lA lB ixA ixB) :=
  writesIn_copies ixA ixB (.ctl fun c _ => lB.set c (lA.get c)) trivial allSlots

omit [Inhabited Γ] in
theorem ckeeps_copyFrom {α : Type} (lA lB : Lens C HCtl) (ixA ixB : Slot → Fin K) (f : C → α)
    (hf : ∀ c x, f (lB.set c x) = f c) :
    CKeeps f (copyFromProg (Γ := Γ) lA lB ixA ixB) :=
  ckeeps_copies ixA ixB (.ctl fun c _ => lB.set c (lA.get c)) f (fun c _ => hf c _) allSlots

end HeadFrame

/-! ## Signed unary counters on the whole machine -/

section Counter
variable {Γ C : Type} {K : ℕ} (tk : Γ)

/-- The signed counter `z`: sign bit `neg`, magnitude as `|z|` tokens. -/
def CRep (z : ℤ) (neg : Bool) (l : List Γ) : Prop :=
  l = List.replicate z.natAbs tk ∧ neg = decide (z < 0)

variable (k : Fin K) (sg : Lens C Bool)

/-- `+1`. -/
def incP : Prog Γ C K :=
  .ite (fun c _ => sg.get c) (.seq (.pop k) (.ctl fun c v => sg.set c (decide (v k ≠ []))))
    (.push k fun _ _ => tk)

/-- `-1`. -/
def decP : Prog Γ C K :=
  .ite (fun c v => !sg.get c && decide (v k ≠ [])) (.pop k)
    (.seq (.push k fun _ _ => tk) (.ctl fun c _ => sg.set c true))

/-- `+δ` for a fixed `δ`. -/
def addP (δ : ℤ) : Prog Γ C K :=
  if 0 ≤ δ then repeatProg (incP tk k sg) δ.toNat else repeatProg (decP tk k sg) (-δ).toNat

/-- `:= 0`. -/
def clrP : Prog Γ C K := .seq (.clear k) (.ctl fun c _ => sg.set c false)

/-- `:= ±src`: copy the magnitude, set the sign (negated when `negate`, zero stays positive). -/
def cpyP (src : Fin K) (sgs : Lens C Bool) (negate : Bool) : Prog Γ C K :=
  .seq (.copy src k)
    (.ctl fun c v => sg.set c (if negate then (!sgs.get c && decide (v src ≠ [])) else sgs.get c))

variable {tk k sg}

theorem view_ne_nil {D : ℕ} (hD : 1 ≤ D) (st : Fin K → List Γ) (j : Fin K) :
    (view D st j ≠ []) ↔ (st j ≠ []) := by
  show (st j).take D ≠ [] ↔ _
  simp only [ne_eq, List.take_eq_nil_iff, not_or]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem crep_nil_iff {z : ℤ} {neg : Bool} {l : List Γ} (h : CRep tk z neg l) :
    l ≠ [] ↔ z ≠ 0 := by
  rw [h.1, ne_eq, ne_eq, List.replicate_eq_nil_iff]
  omega

theorem incP_spec {D : ℕ} (hD : 1 ≤ D) {z : ℤ} {c : C} {st : Fin K → List Γ}
    (h : CRep tk z (sg.get c) (st k)) :
    CRep tk (z + 1) (sg.get ((incP tk k sg).eval D c st).1) (((incP tk k sg).eval D c st).2 k) := by
  obtain ⟨hst, hneg⟩ := h
  by_cases hz : z < 0
  · have hg : sg.get c = true := by rw [hneg]; simpa using hz
    have hn : z.natAbs = (z + 1).natAbs + 1 := by omega
    have hst' : (Function.update st k (st k).tail) k = List.replicate (z + 1).natAbs tk := by
      rw [Function.update_self, hst, hn, List.replicate_succ, List.tail_cons]
    have hv : view D (Function.update st k (st k).tail) k ≠ [] ↔ z + 1 ≠ 0 := by
      rw [view_ne_nil hD, hst', ne_eq, List.replicate_eq_nil_iff]; omega
    simp only [incP, Prog.eval, hg, if_true, sg.get_set]
    refine ⟨hst', ?_⟩
    rw [decide_eq_decide, hv]
    omega
  · have hg : sg.get c = false := by rw [hneg]; simpa using hz
    simp only [incP, Prog.eval, hg, Bool.false_eq_true, if_false, Function.update_self]
    refine ⟨?_, ?_⟩
    · rw [hst, ← List.replicate_succ]; congr 1; omega
    · simp only [false_eq_decide_iff]; omega

theorem decP_spec {D : ℕ} (hD : 1 ≤ D) {z : ℤ} {c : C} {st : Fin K → List Γ}
    (h : CRep tk z (sg.get c) (st k)) :
    CRep tk (z - 1) (sg.get ((decP tk k sg).eval D c st).1) (((decP tk k sg).eval D c st).2 k) := by
  have hne := crep_nil_iff h
  obtain ⟨hst, hneg⟩ := h
  have hv : view D st k ≠ [] ↔ z ≠ 0 := by rw [view_ne_nil hD, hne]
  by_cases hz : 0 < z
  · have hc : (!sg.get c && decide (view D st k ≠ [])) = true := by
      rw [hneg]; simp only [hv]; simp; omega
    simp only [decP, Prog.eval, hc, if_true, Function.update_self]
    have hn : z.natAbs = (z - 1).natAbs + 1 := by omega
    refine ⟨by rw [hst, hn, List.replicate_succ, List.tail_cons], ?_⟩
    rw [hneg]; simp only [decide_eq_decide]; omega
  · have hc : (!sg.get c && decide (view D st k ≠ [])) = false := by
      rw [hneg]; simp only [hv]; simp; omega
    simp only [decP, Prog.eval, hc, Bool.false_eq_true, if_false, Function.update_self,
      sg.get_set]
    refine ⟨?_, ?_⟩
    · rw [hst, ← List.replicate_succ]; congr 1; omega
    · simp only [true_eq_decide_iff]; omega

theorem addP_spec {D : ℕ} (hD : 1 ≤ D) (δ : ℤ) {z : ℤ} {c : C} {st : Fin K → List Γ}
    (h : CRep tk z (sg.get c) (st k)) :
    CRep tk (z + δ) (sg.get ((addP tk k sg δ).eval D c st).1) (((addP tk k sg δ).eval D c st).2 k) := by
  unfold addP
  split
  · rename_i hδ
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, δ = n := ⟨δ.toNat, by omega⟩
    simp only [Int.toNat_natCast]
    clear hδ
    induction n generalizing z c st with
    | zero => simpa [repeatProg, Prog.eval] using h
    | succ n ih =>
      simp only [repeatProg, Prog.eval]
      have := ih (incP_spec hD h)
      rw [show z + ((n + 1 : ℕ) : ℤ) = z + 1 + (n : ℤ) by push_cast; ring]
      exact this
  · rename_i hδ
    obtain ⟨n, hn⟩ : ∃ n : ℕ, δ = -(n : ℤ) := ⟨(-δ).toNat, by omega⟩
    subst hn
    simp only [neg_neg, Int.toNat_natCast]
    clear hδ
    induction n generalizing z c st with
    | zero => simpa [repeatProg, Prog.eval] using h
    | succ n ih =>
      simp only [repeatProg, Prog.eval]
      have := ih (decP_spec hD h)
      rw [show z + -((n + 1 : ℕ) : ℤ) = z - 1 + -(n : ℤ) by push_cast; ring]
      exact this

theorem clrP_spec {D : ℕ} (c : C) (st : Fin K → List Γ) :
    CRep tk 0 (sg.get ((clrP k sg).eval D c st).1) (((clrP k sg).eval D c st).2 k) := by
  simp [clrP, Prog.eval, CRep, sg.get_set]

theorem cpyP_spec {D : ℕ} (hD : 1 ≤ D) {src : Fin K} {sgs : Lens C Bool} (negate : Bool) {z : ℤ}
    {c : C} {st : Fin K → List Γ} (h : CRep tk z (sgs.get c) (st src)) :
    CRep tk (if negate then -z else z) (sg.get ((cpyP k sg src sgs negate).eval D c st).1)
      (((cpyP k sg src sgs negate).eval D c st).2 k) := by
  have hne := crep_nil_iff h
  obtain ⟨hst, hneg⟩ := h
  have hsrc : Function.update st k (st src) src = st src := by
    by_cases e : src = k
    · subst e; simp
    · exact Function.update_of_ne e _ _
  have hv : view D (Function.update st k (st src)) src ≠ [] ↔ z ≠ 0 := by
    rw [view_ne_nil hD, hsrc, hne]
  simp only [cpyP, Prog.eval, sg.get_set, Function.update_self]
  cases negate
  · simp only [Bool.false_eq_true, if_false]
    exact ⟨hst, hneg⟩
  · simp only [if_true]
    refine ⟨by rw [hst, Int.natAbs_neg], ?_⟩
    rw [hneg]
    simp only [hv]
    by_cases hz : z < 0
    · simp [hz]; omega
    · by_cases h0 : z = 0
      · subst h0; simp
      · simp [hz, h0]; omega

theorem writesIn_incP : WritesIn (fun j => j = k) (incP tk k sg) := ⟨⟨rfl, trivial⟩, rfl⟩
theorem writesIn_decP : WritesIn (fun j => j = k) (decP tk k sg) := ⟨rfl, ⟨rfl, trivial⟩⟩

theorem writesIn_addP (δ : ℤ) : WritesIn (fun j => j = k) (addP tk k sg δ) := by
  unfold addP
  split
  · exact writesIn_repeat writesIn_incP _
  · exact writesIn_repeat writesIn_decP _

theorem writesIn_clrP : WritesIn (fun j => j = k) (clrP (Γ := Γ) k sg) := ⟨rfl, trivial⟩

theorem writesIn_cpyP (src : Fin K) (sgs : Lens C Bool) (negate : Bool) :
    WritesIn (fun j => j = k) (cpyP (Γ := Γ) k sg src sgs negate) := ⟨rfl, trivial⟩

variable {α : Type} (f : C → α) (hf : ∀ c x, f (sg.set c x) = f c)
include hf

theorem ckeeps_incP : CKeeps f (incP tk k sg) := ⟨⟨trivial, fun c _ => hf c _⟩, trivial⟩
theorem ckeeps_decP : CKeeps f (decP tk k sg) := ⟨trivial, ⟨trivial, fun c _ => hf c _⟩⟩

theorem ckeeps_addP (δ : ℤ) : CKeeps f (addP tk k sg δ) := by
  unfold addP
  split
  · exact ckeeps_repeat (ckeeps_incP f hf) _
  · exact ckeeps_repeat (ckeeps_decP f hf) _

theorem ckeeps_clrP : CKeeps f (clrP (Γ := Γ) k sg) := ⟨trivial, fun c _ => hf c _⟩

theorem ckeeps_cpyP (src : Fin K) (sgs : Lens C Bool) (negate : Bool) :
    CKeeps f (cpyP (Γ := Γ) k sg src sgs negate) := ⟨trivial, fun c _ => hf c _⟩

end Counter

/-! ## Heads and counters of a worker -/

section Ids
variable {R Dn : ℕ}

def rdH (i : Fin R) : Fin (R + 4) := ⟨i.val, by omega⟩
def begH : Fin (R + 4) := ⟨R, by omega⟩
def endH : Fin (R + 4) := ⟨R + 1, by omega⟩
def zeroH : Fin (R + 4) := ⟨R + 2, by omega⟩
def scrH : Fin (R + 4) := ⟨R + 3, by omega⟩

theorem rdH_inj {i j : Fin R} (h : rdH i = rdH j) : i = j := by
  simp only [rdH, Fin.mk.injEq] at h; exact Fin.ext h

theorem rdH_ne_begH (i : Fin R) : rdH i ≠ begH := by
  simp only [rdH, begH, ne_eq, Fin.mk.injEq]; omega
theorem rdH_ne_endH (i : Fin R) : rdH i ≠ endH := by
  simp only [rdH, endH, ne_eq, Fin.mk.injEq]; omega
theorem rdH_ne_zeroH (i : Fin R) : rdH i ≠ zeroH := by
  simp only [rdH, zeroH, ne_eq, Fin.mk.injEq]; omega
theorem rdH_ne_scrH (i : Fin R) : rdH i ≠ scrH := by
  simp only [rdH, scrH, ne_eq, Fin.mk.injEq]; omega
theorem begH_ne_endH : (begH : Fin (R + 4)) ≠ endH := by
  simp only [begH, endH, ne_eq, Fin.mk.injEq]; omega
theorem begH_ne_zeroH : (begH : Fin (R + 4)) ≠ zeroH := by
  simp only [begH, zeroH, ne_eq, Fin.mk.injEq]; omega
theorem begH_ne_scrH : (begH : Fin (R + 4)) ≠ scrH := by
  simp only [begH, scrH, ne_eq, Fin.mk.injEq]; omega
theorem endH_ne_zeroH : (endH : Fin (R + 4)) ≠ zeroH := by
  simp only [endH, zeroH, ne_eq, Fin.mk.injEq]; omega
theorem endH_ne_scrH : (endH : Fin (R + 4)) ≠ scrH := by
  simp only [endH, scrH, ne_eq, Fin.mk.injEq]; omega
theorem zeroH_ne_scrH : (zeroH : Fin (R + 4)) ≠ scrH := by
  simp only [zeroH, scrH, ne_eq, Fin.mk.injEq]; omega

/-- The head a register index reads: its own reader, or the head parked at `0`. -/
def headOf (i : ℕ) : Fin (R + 4) := if h : i < R then rdH ⟨i, h⟩ else zeroH

theorem headOf_ne_scrH (i : ℕ) : (headOf i : Fin (R + 4)) ≠ scrH := by
  unfold headOf; split
  · exact rdH_ne_scrH _
  · exact zeroH_ne_scrH

def regC (i : Fin Dn) : Fin (2 * Dn + 2) := ⟨i.val, by omega⟩
def snapC (i : Fin Dn) : Fin (2 * Dn + 2) := ⟨Dn + i.val, by omega⟩
def lenC : Fin (2 * Dn + 2) := ⟨2 * Dn, by omega⟩
def hC : Fin (2 * Dn + 2) := ⟨2 * Dn + 1, by omega⟩

theorem regC_inj {i j : Fin Dn} (h : regC i = regC j) : i = j := by
  simp only [regC, Fin.mk.injEq] at h; exact Fin.ext h
theorem snapC_inj {i j : Fin Dn} (h : snapC i = snapC j) : i = j := by
  simp only [snapC, Fin.mk.injEq] at h; exact Fin.ext (by omega)
theorem regC_ne_snapC (i j : Fin Dn) : regC i ≠ snapC j := by
  simp only [regC, snapC, ne_eq, Fin.mk.injEq]; omega
theorem regC_ne_lenC (i : Fin Dn) : regC i ≠ lenC := by
  simp only [regC, lenC, ne_eq, Fin.mk.injEq]; omega
theorem regC_ne_hC (i : Fin Dn) : regC i ≠ hC := by
  simp only [regC, hC, ne_eq, Fin.mk.injEq]; omega
theorem snapC_ne_lenC (i : Fin Dn) : snapC i ≠ lenC := by
  simp only [snapC, lenC, ne_eq, Fin.mk.injEq]; omega
theorem snapC_ne_hC (i : Fin Dn) : snapC i ≠ hC := by
  simp only [snapC, hC, ne_eq, Fin.mk.injEq]; omega
theorem lenC_ne_hC : (lenC : Fin (2 * Dn + 2)) ≠ hC := by
  simp only [lenC, hC, ne_eq, Fin.mk.injEq]; omega

end Ids

section Rep
variable (w : Worker)

abbrev nR : ℕ := w.spec.readers.registers
abbrev nD : ℕ := w.spec.distances.registers

/-- A bound on every `pc` a worker can reach: the start and every row's successors. -/
def pcBound : ℕ := (w.table.toList.map fun f => f.yes + f.no).sum + w.spec.program.start + 1

abbrev WCtl := Ctl (nR w) (2 * nD w + 2) (pcBound w)
abbrev WK : ℕ := KW (nR w) (2 * nD w + 2)
abbrev WSt := Fin (WK w) → List Sym

theorem pcBound_pos : 0 < pcBound w := by unfold pcBound; omega

theorem start_lt_pcBound : w.spec.program.start < pcBound w := by unfold pcBound; omega

theorem mem_table_le {f : Fields} (hf : f ∈ w.table.toList) :
    f.yes + f.no ≤ (w.table.toList.map fun f => f.yes + f.no).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨f, hf, rfl⟩)

theorem fields_succ_lt (pc : ℕ) :
    (w.fields pc).yes < pcBound w ∧ (w.fields pc).no < pcBound w := by
  have key : ∀ f : Fields, (f ∈ w.table.toList ∨ (f.yes = 0 ∧ f.no = 0)) →
      f.yes < pcBound w ∧ f.no < pcBound w := by
    intro f hf
    rcases hf with hf | ⟨h1, h2⟩
    · have := mem_table_le w hf; unfold pcBound; omega
    · have := pcBound_pos w; omega
  apply key
  unfold Worker.fields
  simp only [Array.getD_eq_getD_getElem?]
  cases h : w.table[pc]? with
  | some f => exact Or.inl (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h))
  | none =>
    simp only [Option.getD_none]
    cases h0 : w.table[0]? with
    | some f => exact Or.inl (Array.mem_toList_iff.mpr (Array.mem_of_getElem? h0))
    | none => exact Or.inr ⟨rfl, rfl⟩

/-- A successor `pc` as an element of the control's range. -/
def toPc (n : ℕ) : Fin (pcBound w) := ⟨n % pcBound w, Nat.mod_lt _ (pcBound_pos w)⟩

theorem toPc_val {n : ℕ} (h : n < pcBound w) : (toPc w n).val = n := Nat.mod_eq_of_lt h

variable {w}

/-- Head `h` over the text `t` at position `p`. -/
abbrev GH (h : Fin (nR w + 4)) (t : List (Fin 2)) (p : ℕ) (c : WCtl w) (st : WSt w) : Prop :=
  GHeadRep ι (hl h) (ixH h) t p c st

/-- **The worker `s` is represented by the control `c` and the stacks `st`.** -/
structure Rep (s : WorkerState) (c : WCtl w) (st : WSt w) : Prop where
  fault : s.fault = false
  pc : c.pc.val = s.pc
  mode : c.mode = s.mode
  output : c.output = s.output
  dlen : s.data.length = nR w
  rlen : s.reverse.length = nR w
  glen : s.regs.length = nD w
  rd : ∀ i : Fin (nR w), GH (rdH i) s.text (s.data.getD i 0) c st
  rv : ∀ i : Fin (nR w), c.rev i = s.reverse.getD i false
  beg : GH begH s.text s.begin c st
  en : GH endH s.text s.end c st
  zero : GH zeroH s.text 0 c st
  reg : ∀ i : Fin (nD w), CRep Sym.tok (s.regs.getD i 0) (c.sg (regC i)) (st (ixC (regC i)))
  len : CRep Sym.tok s.length (c.sg lenC) (st (ixC lenC))
  hh : CRep Sym.tok s.h (c.sg hC) (st (ixC hC))
  flags : st ixF = s.flags.map Sym.flag

theorem gh_frame {h : Fin (nR w + 4)} {t : List (Fin 2)} {p : ℕ} {c c' : WCtl w} {st st' : WSt w}
    (H : GH h t p c st) (hc : c'.hc h = c.hc h) (hs : ∀ sl, st' (ixH h sl) = st (ixH h sl)) :
    GH h t p c' st' := by
  unfold GH GHeadRep at *
  have e1 : (hl h).get c' = (hl h).get c := hc
  have e2 : (fun s => st' (ixH h s)) = fun s => st (ixH h s) := funext hs
  rw [e1, e2]
  exact H

/-- The head that register index `i` reads is at `s.data.getD i 0`. -/
theorem Rep.headOf {s : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st) (i : ℕ) :
    GH (headOf i) s.text (s.data.getD i 0) c st := by
  unfold ScaWorkerEnc.headOf
  split
  · rename_i hi
    exact h.rd ⟨i, hi⟩
  · rename_i hi
    have : s.data.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [h.dlen]; omega)]; rfl
    rw [this]
    exact h.zero

/-- The `reverse` bit of register index `i`, from the control. -/
def revOf (c : WCtl w) (i : ℕ) : Bool := if h : i < nR w then c.rev ⟨i, h⟩ else false

theorem Rep.revOf {s : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st) (i : ℕ) :
    revOf c i = s.reverse.getD i false := by
  unfold ScaWorkerEnc.revOf
  split
  · rename_i hi
    exact h.rv ⟨i, hi⟩
  · rename_i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [h.rlen]; omega)]; rfl

end Rep

/-! ## Footprints of the building blocks -/

section Foot
variable {w : Worker}

abbrev Prg (w : Worker) := Prog Sym (WCtl w) (WK w)

/-- The control fields no counter or head program touches. -/
def Misc (c : WCtl w) : Fin (pcBound w) × Mode × Bool × (Fin (nR w) → Bool) × Bool × Bool :=
  (c.pc, c.mode, c.output, c.rev, c.dec, c.srev)

/-- A program on counter `j` only. -/
def CntProg (j : Fin (2 * nD w + 2)) (p : Prg w) : Prop :=
  WritesIn (fun k => k = ixC j) p ∧
    ∀ (α : Type) (f : WCtl w → α), (∀ c x, f ((sl j).set c x) = f c) → CKeeps f p

/-- A program on head `h` only. -/
def HeadProg (h : Fin (nR w + 4)) (p : Prg w) : Prop :=
  WritesIn (fun k => ∃ s, ixH h s = k) p ∧
    ∀ (α : Type) (f : WCtl w → α), (∀ c x, f ((hl h).set c x) = f c) → CKeeps f p

theorem cntProg_incP (j : Fin (2 * nD w + 2)) : CntProg j (incP Sym.tok (ixC j) (sl j)) :=
  ⟨writesIn_incP, fun _ f hf => ckeeps_incP f hf⟩
theorem cntProg_decP (j : Fin (2 * nD w + 2)) : CntProg j (decP Sym.tok (ixC j) (sl j)) :=
  ⟨writesIn_decP, fun _ f hf => ckeeps_decP f hf⟩
theorem cntProg_addP (j : Fin (2 * nD w + 2)) (δ : ℤ) :
    CntProg j (addP Sym.tok (ixC j) (sl j) δ) :=
  ⟨writesIn_addP δ, fun _ f hf => ckeeps_addP f hf δ⟩
theorem cntProg_clrP (j : Fin (2 * nD w + 2)) : CntProg j (clrP (Γ := Sym) (ixC j) (sl j)) :=
  ⟨writesIn_clrP, fun _ f hf => ckeeps_clrP f hf⟩
theorem cntProg_cpyP (j j' : Fin (2 * nD w + 2)) (negate : Bool) :
    CntProg j (cpyP (Γ := Sym) (ixC j) (sl j) (ixC j') (sl j') negate) :=
  ⟨writesIn_cpyP _ _ _, fun _ f hf => ckeeps_cpyP f hf _ _ _⟩
theorem cntProg_seq {j : Fin (2 * nD w + 2)} {p q : Prg w} (hp : CntProg j p) (hq : CntProg j q) :
    CntProg j (.seq p q) :=
  ⟨⟨hp.1, hq.1⟩, fun α f hf => ⟨hp.2 α f hf, hq.2 α f hf⟩⟩

theorem headProg_toProg (h : Fin (nR w + 4)) (p : ScaHeadRep.Prog Sym) :
    HeadProg h (toProg (hl h) (ixH h) p) :=
  ⟨writesIn_toProg _ _ p, fun _ f hf => ckeeps_toProg _ _ f hf p⟩
theorem headProg_moveBy (h : Fin (nR w + 4)) (δ : ℤ) :
    HeadProg h (moveByProg Sym.tok (hl h) (ixH h) δ) :=
  ⟨writesIn_moveBy _ _ _ δ, fun _ f hf => ckeeps_moveBy _ _ _ δ f hf⟩
theorem headProg_copyFrom (h' h : Fin (nR w + 4)) :
    HeadProg h (copyFromProg (Γ := Sym) (hl h') (hl h) (ixH h') (ixH h)) :=
  ⟨writesIn_copyFrom _ _ _ _, fun _ f hf => ckeeps_copyFrom _ _ _ _ f hf⟩

variable {D : ℕ}

theorem CntProg.misc {j : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) (c : WCtl w)
    (st : WSt w) : Misc (p.eval D c st).1 = Misc c :=
  eval_ctl_frame Misc D p (hp.2 _ Misc fun _ _ => rfl) c st

theorem CntProg.hc {j : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) (c : WCtl w)
    (st : WSt w) : (p.eval D c st).1.hc = c.hc :=
  eval_ctl_frame (fun c : WCtl w => c.hc) D p (hp.2 _ _ fun _ _ => rfl) c st

theorem CntProg.sg {j : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) (c : WCtl w)
    (st : WSt w) (j' : Fin (2 * nD w + 2)) (hj : j' ≠ j) : (p.eval D c st).1.sg j' = c.sg j' :=
  eval_ctl_frame (fun c : WCtl w => c.sg j') D p
    (hp.2 _ _ fun c x => by simp [sl, Function.update_of_ne hj]) c st

theorem CntProg.st {j : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) (c : WCtl w)
    (st : WSt w) (k : Fin (WK w)) (hk : k ≠ ixC j) : (p.eval D c st).2 k = st k :=
  eval_st_frame _ D p hp.1 c st k hk

theorem HeadProg.misc {h : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p) (c : WCtl w)
    (st : WSt w) : Misc (p.eval D c st).1 = Misc c :=
  eval_ctl_frame Misc D p (hp.2 _ Misc fun _ _ => rfl) c st

theorem HeadProg.sg {h : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p) (c : WCtl w)
    (st : WSt w) : (p.eval D c st).1.sg = c.sg :=
  eval_ctl_frame (fun c : WCtl w => c.sg) D p (hp.2 _ _ fun _ _ => rfl) c st

theorem HeadProg.hc {h : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p) (c : WCtl w)
    (st : WSt w) (h' : Fin (nR w + 4)) (hh : h' ≠ h) : (p.eval D c st).1.hc h' = c.hc h' :=
  eval_ctl_frame (fun c : WCtl w => c.hc h') D p
    (hp.2 _ _ fun c x => by simp [hl, Function.update_of_ne hh]) c st

theorem HeadProg.st {h : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p) (c : WCtl w)
    (st : WSt w) (k : Fin (WK w)) (hk : ∀ s, ixH h s ≠ k) : (p.eval D c st).2 k = st k :=
  eval_st_frame _ D p hp.1 c st k (fun ⟨s, e⟩ => hk s e)

/-- Another head survives a head program. -/
theorem HeadProg.gh {h h' : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p) (hh : h' ≠ h)
    {t : List (Fin 2)} {q : ℕ} {c : WCtl w} {st : WSt w} (H : GH h' t q c st) :
    GH h' t q (p.eval D c st).1 (p.eval D c st).2 :=
  gh_frame H (hp.hc c st h' hh) (fun sl => hp.st c st _ (fun s => ixH_ne (Ne.symm hh) s sl))

/-- A head survives a counter program. -/
theorem CntProg.gh {j : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) {h : Fin (nR w + 4)}
    {t : List (Fin 2)} {q : ℕ} {c : WCtl w} {st : WSt w} (H : GH h t q c st) :
    GH h t q (p.eval D c st).1 (p.eval D c st).2 :=
  gh_frame H (by rw [hp.hc c st]) (fun sl => hp.st c st _ (ixH_ne_ixC h sl j))

/-- Another counter survives a counter program. -/
theorem CntProg.crep {j j' : Fin (2 * nD w + 2)} {p : Prg w} (hp : CntProg j p) (hj : j' ≠ j)
    {z : ℤ} {c : WCtl w} {st : WSt w} (H : CRep Sym.tok z (c.sg j') (st (ixC j'))) :
    CRep Sym.tok z ((p.eval D c st).1.sg j') ((p.eval D c st).2 (ixC j')) := by
  rw [hp.sg c st j' hj, hp.st c st _ (fun e => hj (ixC_inj e))]
  exact H

/-- A counter survives a head program. -/
theorem HeadProg.crep {h : Fin (nR w + 4)} {p : Prg w} (hp : HeadProg h p)
    {j : Fin (2 * nD w + 2)} {z : ℤ} {c : WCtl w} {st : WSt w}
    (H : CRep Sym.tok z (c.sg j) (st (ixC j))) :
    CRep Sym.tok z ((p.eval D c st).1.sg j) ((p.eval D c st).2 (ixC j)) := by
  rw [hp.sg c st, hp.st c st _ (fun s => ixH_ne_ixC h s j)]
  exact H

end Foot

/-! ## Updating one component of the representation -/

section RepUpd
variable {w : Worker} {D : ℕ}

theorem misc_eq {a b : WCtl w} (h : Misc a = Misc b) :
    a.pc = b.pc ∧ a.mode = b.mode ∧ a.output = b.output ∧ a.rev = b.rev ∧ a.dec = b.dec ∧
      a.srev = b.srev := by
  simp only [Misc, Prod.mk.injEq] at h; exact h

theorem getD_set_self {α : Type} (l : List α) {i : ℕ} (hi : i < l.length) (a d : α) :
    (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_set_ne {α : Type} (l : List α) {i j : ℕ} (hij : i ≠ j) (a d : α) :
    (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, hij]

variable {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem Rep.setLen {p : Prg w} (hp : CntProg lenC p) (h : Rep s c st) {z : ℤ}
    (hnew : CRep Sym.tok z ((p.eval D c st).1.sg lenC) ((p.eval D c st).2 (ixC lenC))) :
    Rep { s with length := z } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen, glen := h.glen,
    rd := fun i => hp.gh (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh h.beg, en := hp.gh h.en, zero := hp.gh h.zero,
    reg := fun i => hp.crep (regC_ne_lenC i) (h.reg i), len := hnew,
    hh := hp.crep (Ne.symm lenC_ne_hC) h.hh,
    flags := (by rw [hp.st c st _ (ixC_ne_ixF _).symm]; exact h.flags) }

theorem Rep.setH {p : Prg w} (hp : CntProg hC p) (h : Rep s c st) {z : ℤ}
    (hnew : CRep Sym.tok z ((p.eval D c st).1.sg hC) ((p.eval D c st).2 (ixC hC))) :
    Rep { s with h := z } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen, glen := h.glen,
    rd := fun i => hp.gh (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh h.beg, en := hp.gh h.en, zero := hp.gh h.zero,
    reg := fun i => hp.crep (regC_ne_hC i) (h.reg i), len := hp.crep lenC_ne_hC h.len,
    hh := hnew, flags := (by rw [hp.st c st _ (ixC_ne_ixF _).symm]; exact h.flags) }

theorem Rep.setReg (i : Fin (nD w)) {p : Prg w} (hp : CntProg (regC i) p) (h : Rep s c st)
    {z : ℤ}
    (hnew : CRep Sym.tok z ((p.eval D c st).1.sg (regC i)) ((p.eval D c st).2 (ixC (regC i)))) :
    Rep { s with regs := s.regs.set i z } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  refine {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := (by simp [h.glen]),
    rd := fun i => hp.gh (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh h.beg, en := hp.gh h.en, zero := hp.gh h.zero,
    reg := fun i' => ?_, len := hp.crep (Ne.symm (regC_ne_lenC i)) h.len,
    hh := hp.crep (Ne.symm (regC_ne_hC i)) h.hh,
    flags := (by rw [hp.st c st _ (ixC_ne_ixF _).symm]; exact h.flags) }
  by_cases hi : i' = i
  · subst hi
    dsimp only
    rw [getD_set_self _ (by rw [h.glen]; exact i'.isLt)]
    exact hnew
  · dsimp only
    rw [getD_set_ne _ (fun e => hi (Fin.ext e.symm))]
    exact hp.crep (fun e => hi (regC_inj e)) (h.reg i')

/-- Writing a snapshot counter is invisible to the representation. -/
theorem Rep.snap (i : Fin (nD w)) {p : Prg w} (hp : CntProg (snapC i) p) (h : Rep s c st) :
    Rep s (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen, glen := h.glen,
    rd := fun i => hp.gh (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh h.beg, en := hp.gh h.en, zero := hp.gh h.zero,
    reg := fun i' => hp.crep (regC_ne_snapC i' i) (h.reg i'),
    len := hp.crep (Ne.symm (snapC_ne_lenC i)) h.len,
    hh := hp.crep (Ne.symm (snapC_ne_hC i)) h.hh,
    flags := (by rw [hp.st c st _ (ixC_ne_ixF _).symm]; exact h.flags) }

theorem Rep.setData (i : Fin (nR w)) {p : Prg w} (hp : HeadProg (rdH i) p) (h : Rep s c st)
    {q : ℕ} (hnew : GH (rdH i) s.text q (p.eval D c st).1 (p.eval D c st).2) :
    Rep { s with data := s.data.set i q } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  refine {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := (by simp [h.dlen]), rlen := h.rlen,
    glen := h.glen, rd := fun i' => ?_, rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh (Ne.symm (rdH_ne_begH i)) h.beg, en := hp.gh (Ne.symm (rdH_ne_endH i)) h.en,
    zero := hp.gh (Ne.symm (rdH_ne_zeroH i)) h.zero,
    reg := fun i => hp.crep (h.reg i), len := hp.crep h.len, hh := hp.crep h.hh,
    flags := (by rw [hp.st c st _ (fun s => ixH_ne_ixF _ s)]; exact h.flags) }
  by_cases hi : i' = i
  · subst hi
    dsimp only
    rw [getD_set_self _ (by rw [h.dlen]; exact i'.isLt)]
    exact hnew
  · dsimp only
    rw [getD_set_ne _ (fun e => hi (Fin.ext e.symm))]
    exact hp.gh (fun e => hi (rdH_inj e)) (h.rd i')

theorem Rep.setBegin {p : Prg w} (hp : HeadProg begH p) (h : Rep s c st) {q : ℕ}
    (hnew : GH begH s.text q (p.eval D c st).1 (p.eval D c st).2) :
    Rep { s with begin := q } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := h.glen, rd := fun i => hp.gh (rdH_ne_begH i) (h.rd i),
    rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hnew, en := hp.gh (Ne.symm begH_ne_endH) h.en,
    zero := hp.gh (Ne.symm begH_ne_zeroH) h.zero,
    reg := fun i => hp.crep (h.reg i), len := hp.crep h.len, hh := hp.crep h.hh,
    flags := (by rw [hp.st c st _ (fun s => ixH_ne_ixF _ s)]; exact h.flags) }

/-- Writing the scratch head is invisible to the representation. -/
theorem Rep.scr {p : Prg w} (hp : HeadProg scrH p) (h : Rep s c st) :
    Rep s (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := h.glen, rd := fun i => hp.gh (rdH_ne_scrH i) (h.rd i),
    rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh begH_ne_scrH h.beg, en := hp.gh endH_ne_scrH h.en,
    zero := hp.gh zeroH_ne_scrH h.zero,
    reg := fun i => hp.crep (h.reg i), len := hp.crep h.len, hh := hp.crep h.hh,
    flags := (by rw [hp.st c st _ (fun s => ixH_ne_ixF _ s)]; exact h.flags) }

/-- A control-only update that keeps the fields the representation reads. -/
theorem Rep.ctl (h : Rep s c st) (c' : WCtl w) (e1 : c'.pc = c.pc) (e2 : c'.mode = c.mode)
    (e3 : c'.output = c.output) (e4 : c'.rev = c.rev) (e5 : c'.hc = c.hc) (e6 : c'.sg = c.sg) :
    Rep s c' st := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH h t q c st → GH h t q c' st :=
    fun H => gh_frame H (by rw [e5]) (fun _ => rfl)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := h.glen, rd := fun i => hg (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hg h.beg, en := hg h.en, zero := hg h.zero,
    reg := fun i => (by rw [e6]; exact h.reg i), len := (by rw [e6]; exact h.len),
    hh := (by rw [e6]; exact h.hh), flags := h.flags }

end RepUpd

/-! ## The flag stack and the plain control fields -/

section Plain
variable {w : Worker} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

/-- Changing only the flag stack. -/
theorem Rep.flagStack (h : Rep s c st) (l : List Bool) (st' : WSt w)
    (hst : ∀ k, k ≠ ixF → st' k = st k) (hF : st' ixF = l.map Sym.flag) :
    Rep { s with flags := l } c st' := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH h t q c st → GH h t q c st' :=
    fun H => gh_frame H rfl (fun sl => hst _ (ixH_ne_ixF _ sl))
  exact {
    fault := h.fault, pc := h.pc, mode := h.mode, output := h.output, dlen := h.dlen,
    rlen := h.rlen, glen := h.glen, rd := fun i => hg (h.rd i), rv := h.rv,
    beg := hg h.beg, en := hg h.en, zero := hg h.zero,
    reg := fun i => by rw [hst _ (ixC_ne_ixF _)]; exact h.reg i,
    len := by rw [hst _ (ixC_ne_ixF _)]; exact h.len,
    hh := by rw [hst _ (ixC_ne_ixF _)]; exact h.hh, flags := hF }

theorem Rep.clearFlags (h : Rep s c st) :
    Rep { s with flags := [] } ((Prog.clear ixF : Prg w).eval D c st).1
      ((Prog.clear ixF : Prg w).eval D c st).2 :=
  h.flagStack [] _ (fun k hk => Function.update_of_ne hk _ _) (by simp [Prog.eval])

theorem Rep.pushFlag (h : Rep s c st) (b : Bool) :
    Rep { s with flags := b :: s.flags }
      ((Prog.push ixF fun _ _ => Sym.flag b : Prg w).eval D c st).1
      ((Prog.push ixF fun _ _ => Sym.flag b : Prg w).eval D c st).2 :=
  h.flagStack _ _ (fun k hk => Function.update_of_ne hk _ _) (by simp [Prog.eval, h.flags])

theorem Rep.setMode (h : Rep s c st) (m : Mode) :
    Rep { s with mode := m } { c with mode := m } st := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH h t q c st →
      GH h t q { c with mode := m } st := fun H => gh_frame H rfl (fun _ => rfl)
  exact {
    fault := h.fault, pc := h.pc, mode := rfl, output := h.output, dlen := h.dlen,
    rlen := h.rlen, glen := h.glen, rd := fun i => hg (h.rd i), rv := h.rv,
    beg := hg h.beg, en := hg h.en, zero := hg h.zero, reg := h.reg, len := h.len, hh := h.hh,
    flags := h.flags }

theorem Rep.setPc (h : Rep s c st) (n : ℕ) (q : Fin (pcBound w)) (hq : q.val = n) :
    Rep { s with pc := n } { c with pc := q } st := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q' : ℕ}, GH h t q' c st →
      GH h t q' { c with pc := q } st := fun H => gh_frame H rfl (fun _ => rfl)
  exact {
    fault := h.fault, pc := hq, mode := h.mode, output := h.output, dlen := h.dlen,
    rlen := h.rlen, glen := h.glen, rd := fun i => hg (h.rd i), rv := h.rv,
    beg := hg h.beg, en := hg h.en, zero := hg h.zero, reg := h.reg, len := h.len, hh := h.hh,
    flags := h.flags }

theorem Rep.setOutput (h : Rep s c st) (b : Bool) :
    Rep { s with output := b } { c with output := b } st := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH h t q c st →
      GH h t q { c with output := b } st := fun H => gh_frame H rfl (fun _ => rfl)
  exact {
    fault := h.fault, pc := h.pc, mode := h.mode, output := rfl, dlen := h.dlen,
    rlen := h.rlen, glen := h.glen, rd := fun i => hg (h.rd i), rv := h.rv,
    beg := hg h.beg, en := hg h.en, zero := hg h.zero, reg := h.reg, len := h.len, hh := h.hh,
    flags := h.flags }

theorem Rep.setRev (h : Rep s c st) (i : Fin (nR w)) (b : Bool) :
    Rep { s with reverse := s.reverse.set i b } { c with rev := Function.update c.rev i b } st := by
  have hg : ∀ {h : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH h t q c st →
      GH h t q { c with rev := Function.update c.rev i b } st := fun H => gh_frame H rfl (fun _ => rfl)
  refine {
    fault := h.fault, pc := h.pc, mode := h.mode, output := h.output, dlen := h.dlen,
    rlen := by simp [h.rlen], glen := h.glen, rd := fun i => hg (h.rd i), rv := fun i' => ?_,
    beg := hg h.beg, en := hg h.en, zero := hg h.zero, reg := h.reg, len := h.len, hh := h.hh,
    flags := h.flags }
  by_cases hi : i' = i
  · subst hi
    simp only [Function.update_self]
    rw [getD_set_self _ (by rw [h.rlen]; exact i'.isLt)]
  · simp only [Function.update_of_ne hi]
    rw [getD_set_ne _ (fun e => hi (Fin.ext e.symm))]
    exact h.rv i'

/-- The scratch bits are invisible. -/
theorem Rep.setScratch (h : Rep s c st) (d r : Bool) :
    Rep s { c with dec := d, srev := r } st :=
  h.ctl _ rfl rfl rfl rfl rfl rfl

end Plain

/-! ## `mark` and `resetFlags` -/

section MarkReset
variable (w : Worker)

def markP (b : Bool) : Prg w := if b then clrP (ixC hC) (sl hC) else .skip

def resetP (b : Bool) : Prg w :=
  if b then
    .seq (copyFromProg (hl endH) (hl begH) (ixH endH) (ixH begH))
      (.seq (clrP (ixC lenC) (sl lenC))
        (.seq (clrP (ixC hC) (sl hC))
          (.seq (.clear ixF) (.ctl fun c _ => { c with mode := .idle }))))
  else .skip

variable {w} {D : ℕ}

theorem rep_mark (b : Bool) {s : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st) :
    Rep (mark w b s) ((markP w b).eval D c st).1 ((markP w b).eval D c st).2 := by
  cases b
  · exact h
  · exact h.setH (cntProg_clrP hC) (clrP_spec c st)

/-- `begin := end` by copying the `end` head. -/
theorem Rep.copyEndToBegin {s : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st) :
    Rep { s with begin := s.end }
      ((copyFromProg (hl endH) (hl begH) (ixH endH) (ixH begH) : Prg w).eval D c st).1
      ((copyFromProg (hl endH) (hl begH) (ixH endH) (ixH begH) : Prg w).eval D c st).2 := by
  have hc := copyFromProg_correct (ι := ι) (lA := hl endH) (lB := hl begH) (ixH_inj begH)
    (fun s s' => ixH_ne (Ne.symm begH_ne_endH) s s') (fun c x => hl_indep begH_ne_endH c x) D
    h.en
  exact h.setBegin (headProg_copyFrom endH begH) hc.1

theorem rep_resetFlags (b : Bool) {s : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st) :
    Rep (resetFlags w b s) ((resetP w b).eval D c st).1 ((resetP w b).eval D c st).2 := by
  cases b
  · exact h
  · have h1 := h.copyEndToBegin (D := D)
    have h2 := h1.setLen (D := D) (cntProg_clrP lenC) (clrP_spec _ _)
    have h3 := h2.setH (D := D) (cntProg_clrP hC) (clrP_spec _ _)
    have h4 := h3.clearFlags (D := D)
    have h5 := h4.setMode Mode.idle
    exact h5

end MarkReset

/-! ## `arrive` -/

section Arrive
variable (w : Worker)

/-- Every head receives the letter. -/
def arriveAll (a : Fin 2) : Prg w :=
  seqList (fun h => arriveProg ι Sym.tok (hl h) (ixH h) a) (List.finRange (nR w + 4))

def arriveP (a : Fin 2) : Prg w :=
  .seq (arriveAll w a)
    (.seq (moveRightProg Sym.tok (hl endH) (ixH endH))
      (.seq (incP Sym.tok (ixC lenC) (sl lenC))
        (.seq (if w.spec.isFlags then incP Sym.tok (ixC hC) (sl hC) else .skip)
          (.ctl fun c _ => { c with output := false }))))

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

/-- Where the representation puts head `h`. -/
def posOf (s : WorkerState) (h : Fin (nR w + 4)) : ℕ :=
  if h.val < nR w then s.data.getD h.val 0
  else if h = begH then s.begin else if h = endH then s.end else 0

theorem Rep.gh_posOf (hr : Rep s c st) (h : Fin (nR w + 4)) (hs : h ≠ scrH) :
    GH h s.text (posOf s h) c st := by
  unfold posOf
  split
  · rename_i hlt
    have e : h = rdH ⟨h.val, hlt⟩ := Fin.ext rfl
    rw [e]; exact hr.rd _
  · rename_i hge
    split
    · rename_i hb; subst hb; exact hr.beg
    · rename_i hb
      split
      · rename_i he; subst he; exact hr.en
      · rename_i he
        have e : h = zeroH := by
          apply Fin.ext
          have h1 : h.val ≠ nR w := fun e' => hb (Fin.ext e')
          have h2 : h.val ≠ nR w + 1 := fun e' => he (Fin.ext e')
          have h3 : h.val ≠ nR w + 3 := fun e' => hs (Fin.ext e')
          have := h.isLt
          show h.val = nR w + 2
          omega
        rw [e]; exact hr.zero

theorem posOf_rdH (s : WorkerState) (i : Fin (nR w)) : posOf s (rdH i) = s.data.getD i 0 := by
  unfold posOf; rw [if_pos (by simp [rdH])]; rfl

theorem posOf_begH (s : WorkerState) : posOf (w := w) s begH = s.begin := by
  unfold posOf; rw [if_neg (by simp [begH]), if_pos rfl]

theorem posOf_endH (s : WorkerState) : posOf (w := w) s endH = s.end := by
  unfold posOf
  rw [if_neg (by simp [endH]), if_neg (Ne.symm begH_ne_endH), if_pos rfl]

theorem posOf_zeroH (s : WorkerState) : posOf (w := w) s zeroH = 0 := by
  unfold posOf
  rw [if_neg (by simp [zeroH]), if_neg (Ne.symm begH_ne_zeroH), if_neg (Ne.symm endH_ne_zeroH)]

theorem rep_arriveAll (hD : 14 ≤ D) (a : Fin 2) (hr : Rep s c st) :
    Rep { s with text := s.text ++ [a] } ((arriveAll w a).eval D c st).1
      ((arriveAll w a).eval D c st).2 := by
  let P : Fin (nR w + 4) → Prg w := fun h => arriveProg ι Sym.tok (hl h) (ixH h) a
  have hP : ∀ h, HeadProg h (P h) := fun h => headProg_toProg h _
  let G : WCtl w → WSt w → Prop := fun c' st' =>
    Misc c' = Misc c ∧ c'.sg = c.sg ∧ ∀ k, (∀ h sl, ixH h sl ≠ k) → st' k = st k
  let A : Fin (nR w + 4) → WCtl w → WSt w → Prop := fun h c' st' =>
    h ≠ scrH → GH h s.text (posOf s h) c' st'
  let B : Fin (nR w + 4) → WCtl w → WSt w → Prop := fun h c' st' =>
    h ≠ scrH → GH h (s.text ++ [a]) (posOf s h) c' st'
  have key := seqList_spec D P G A B
    (fun h c' st' _ hA hne => arriveProg_correct (ι := ι) (ixH_inj h) a hD (hA hne))
    (fun h c' st' hG => ⟨((hP h).misc c' st').trans hG.1, ((hP h).sg c' st').trans hG.2.1,
      fun k hk => ((hP h).st c' st' k (fun sl => hk h sl)).trans (hG.2.2 k hk)⟩)
    (fun h h' c' st' hne hA hs => (hP h).gh (Ne.symm hne) (hA hs))
    (fun h h' c' st' hne hB hs => (hP h).gh (Ne.symm hne) (hB hs))
    (List.finRange (nR w + 4)) (List.nodup_finRange _) c st ⟨rfl, rfl, fun _ _ => rfl⟩
    (fun h _ hs => hr.gh_posOf h hs)
  obtain ⟨⟨hmisc, hsg, hst⟩, hB⟩ := key
  change Misc ((arriveAll w a).eval D c st).1 = Misc c at hmisc
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq hmisc
  have hB' : ∀ h, h ≠ scrH →
      GH h (s.text ++ [a]) (posOf s h) ((arriveAll w a).eval D c st).1
        ((arriveAll w a).eval D c st).2 :=
    fun h hs => hB h (List.mem_finRange h) hs
  have hcnt : ∀ j, ((arriveAll w a).eval D c st).2 (ixC j) = st (ixC j) :=
    fun j => hst _ (fun h sl => ixH_ne_ixC h sl j)
  exact {
    fault := hr.fault,
    pc := (by rw [e1]; exact hr.pc),
    mode := (by rw [e2]; exact hr.mode),
    output := (by rw [e3]; exact hr.output),
    dlen := hr.dlen, rlen := hr.rlen, glen := hr.glen,
    rd := fun i => (by
      have := hB' (rdH i) (rdH_ne_scrH i)
      rwa [posOf_rdH] at this),
    rv := fun i => (by rw [e4]; exact hr.rv i),
    beg := (by
      have := hB' begH begH_ne_scrH
      rwa [posOf_begH] at this),
    en := (by
      have := hB' endH endH_ne_scrH
      rwa [posOf_endH] at this),
    zero := (by
      have := hB' zeroH zeroH_ne_scrH
      rwa [posOf_zeroH] at this),
    reg := fun i => (by
      change ((arriveAll w a).eval D c st).1.sg = c.sg at hsg
      rw [hsg, hcnt]; exact hr.reg i),
    len := (by
      change ((arriveAll w a).eval D c st).1.sg = c.sg at hsg
      rw [hsg, hcnt]; exact hr.len),
    hh := (by
      change ((arriveAll w a).eval D c st).1.sg = c.sg at hsg
      rw [hsg, hcnt]; exact hr.hh),
    flags := (hst ixF (fun h sl => ixH_ne_ixF h sl)).trans hr.flags }

theorem Rep.setEnd {p : Prg w} (hp : HeadProg endH p) (h : Rep s c st) {q : ℕ}
    (hnew : GH endH s.text q (p.eval D c st).1 (p.eval D c st).2) :
    Rep { s with «end» := q } (p.eval D c st).1 (p.eval D c st).2 := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq (hp.misc c st)
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := h.glen, rd := fun i => hp.gh (rdH_ne_endH i) (h.rd i),
    rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hp.gh begH_ne_endH h.beg, en := hnew,
    zero := hp.gh (Ne.symm endH_ne_zeroH) h.zero,
    reg := fun i => hp.crep (h.reg i), len := hp.crep h.len, hh := hp.crep h.hh,
    flags := (by rw [hp.st c st _ (fun s => ixH_ne_ixF _ s)]; exact h.flags) }

theorem arrive_eq (a : Fin 2) (hnf : (arrive w a s).fault = false) :
    arrive w a s = { s with
      text := s.text ++ [a], output := false, «end» := s.end + 1,
      length := s.length + 1, h := if w.spec.isFlags then s.h + 1 else s.h } := by
  unfold arrive at hnf ⊢
  cases hF : w.spec.isFlags <;> simp only [hF] at hnf ⊢
  all_goals simp at hnf
  all_goals simp only [hnf.2, Bool.not_true, Bool.or_false]
  all_goals simp

theorem rep_arrive (hD : 17 ≤ D) (a : Fin 2) (hr : Rep s c st)
    (hnf : (arrive w a s).fault = false) :
    Rep (arrive w a s) ((arriveP w a).eval D c st).1 ((arriveP w a).eval D c st).2 := by
  rw [arrive_eq a hnf]
  have h1 := rep_arriveAll (D := D) (by omega) a hr
  have hle : s.end < (s.text ++ [a]).length := by
    have := hr.en.le; simp only [List.length_append, List.length_singleton] at this ⊢; omega
  have h2 := h1.setEnd (D := D) (headProg_toProg endH _)
    (moveRightProg_correct (ι := ι) (tk := Sym.tok) (ixH_inj endH) hD h1.en hle)
  have h3 := h2.setLen (D := D) (cntProg_incP lenC) (incP_spec (by omega) h2.len)
  cases hF : w.spec.isFlags
  · have h5 := h3.setOutput false
    simp only [arriveP, hF, Bool.false_eq_true, if_false]
    exact h5
  · have h4 := h3.setH (D := D) (cntProg_incP hC) (incP_spec (by omega) h3.hh)
    have h5 := h4.setOutput false
    simp only [arriveP, hF, if_true]
    exact h5

end Arrive

/-! ## `start`: reader starts and distance initialisation -/

section Start
variable (w : Worker)

/-- `rawStart head (position of src) rv true`. -/
def rawStartP (name : String) (src : Fin (nR w + 4)) (rv : Bool) : Prg w :=
  match lookupFirst name w.spec.readers.colors with
  | none => .skip
  | some i =>
    if h : i < nR w then
      .seq (copyFromProg (hl src) (hl (rdH ⟨i, h⟩)) (ixH src) (ixH (rdH ⟨i, h⟩)))
        (.ctl fun c _ => { c with rev := Function.update c.rev ⟨i, h⟩ rv })
    else .skip

/-- Load counter `dst := ±key`. -/
def loadKeyP (dst : Fin (2 * nD w + 2)) (k : DistKey) (negate : Bool) : Prg w :=
  match k with
  | .reg j =>
    if hj : j < nD w then cpyP (ixC dst) (sl dst) (ixC (regC ⟨j, hj⟩)) (sl (regC ⟨j, hj⟩)) negate
    else clrP (ixC dst) (sl dst)
  | .length => cpyP (ixC dst) (sl dst) (ixC lenC) (sl lenC) negate
  | .h => cpyP (ixC dst) (sl dst) (ixC hC) (sl hC) negate

/-- One entry of `initializeValues`. -/
def entryP (e : Pair × Option (DistKey × ℤ)) : Prg w :=
  match lookupFirst e.1 w.spec.distances.colors with
  | none => .skip
  | some i =>
    if h : i < nD w then
      match e.2 with
      | none => clrP (ixC (regC ⟨i, h⟩)) (sl (regC ⟨i, h⟩))
      | some (k, sign) => loadKeyP w (regC ⟨i, h⟩) k (decide (sign = -1))
    else .skip

def initP (mapping : List (Pair × Option (DistKey × ℤ))) : Prg w := seqList (entryP w) mapping

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem set_oob {α : Type} (l : List α) {i : ℕ} (h : l.length ≤ i) (a : α) : l.set i a = l :=
  List.set_eq_of_length_le h

theorem rep_rawStart (name : String) {src : Fin (nR w + 4)} (hsrc : ∀ i, src ≠ rdH i)
    (rv : Bool) {q : ℕ} (hr : Rep s c st) (hq : GH src s.text q c st) :
    Rep (rawStart w name q rv true s) ((rawStartP w name src rv).eval D c st).1
      ((rawStartP w name src rv).eval D c st).2 := by
  unfold rawStart rawStartP
  cases hlk : lookupFirst name w.spec.readers.colors with
  | none => exact hr
  | some i =>
    dsimp only
    rw [if_pos rfl]
    split
    · rename_i hi
      have hc := copyFromProg_correct (ι := ι) (lA := hl src) (lB := hl (rdH ⟨i, hi⟩))
        (ixA := ixH src) (ixB := ixH (rdH ⟨i, hi⟩)) (ixH_inj _)
        (fun s s' => ixH_ne (hsrc ⟨i, hi⟩) s s') (fun c x => hl_indep (Ne.symm (hsrc ⟨i, hi⟩)) c x)
        D hq
      have h1 := hr.setData (D := D) ⟨i, hi⟩ (headProg_copyFrom src _) hc.1
      exact h1.setRev ⟨i, hi⟩ rv
    · rename_i hi
      have e1 : s.data.set i q = s.data := set_oob _ (by rw [hr.dlen]; omega) _
      have e2 : s.reverse.set i rv = s.reverse := set_oob _ (by rw [hr.rlen]; omega) _
      simp only [e1, e2]
      exact hr

theorem rep_loadKey (hD : 1 ≤ D) (i : Fin (nD w)) (k : DistKey) (negate : Bool)
    (hr : Rep s c st) :
    Rep { s with regs := s.regs.set i (if negate then -s.getDist k else s.getDist k) }
      ((loadKeyP w (regC i) k negate).eval D c st).1
      ((loadKeyP w (regC i) k negate).eval D c st).2 := by
  cases k with
  | reg j =>
    by_cases hj : j < nD w
    · have e : loadKeyP w (regC i) (.reg j) negate =
          cpyP (ixC (regC i)) (sl (regC i)) (ixC (regC ⟨j, hj⟩)) (sl (regC ⟨j, hj⟩)) negate := by
        simp only [loadKeyP, dif_pos hj]
      rw [e]
      exact hr.setReg i (cntProg_cpyP _ _ _) (cpyP_spec hD negate (hr.reg ⟨j, hj⟩))
    · have e' : loadKeyP w (regC i) (.reg j) negate = clrP (ixC (regC i)) (sl (regC i)) := by
        simp only [loadKeyP, dif_neg hj]
      rw [e']
      have e : s.getDist (.reg j) = 0 := by
        show s.regs.getD j 0 = 0
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hr.glen]; omega)]; rfl
      rw [e]
      have := hr.setReg (D := D) i (cntProg_clrP _) (clrP_spec c st)
      cases negate <;> simpa using this
  | length => exact hr.setReg i (cntProg_cpyP _ _ _) (cpyP_spec hD negate hr.len)
  | h => exact hr.setReg i (cntProg_cpyP _ _ _) (cpyP_spec hD negate hr.hh)

theorem rep_entry (hD : 1 ≤ D) (e : Pair × Option (DistKey × ℤ)) (hr : Rep s c st) :
    Rep (initializeValues w.spec [e] true s) ((entryP w e).eval D c st).1
      ((entryP w e).eval D c st).2 := by
  obtain ⟨pair, value⟩ := e
  unfold initializeValues entryP
  simp only [if_true, List.foldl_cons, List.foldl_nil]
  cases hlk : lookupFirst pair w.spec.distances.colors with
  | none => exact hr
  | some i =>
    by_cases hi : i < nD w
    · simp only [dif_pos hi]
      cases value with
      | none => exact hr.setReg ⟨i, hi⟩ (cntProg_clrP _) (clrP_spec c st)
      | some ks =>
        obtain ⟨k, sign⟩ := ks
        have := rep_loadKey hD ⟨i, hi⟩ k (decide (sign = -1)) hr
        simp only [decide_eq_true_eq] at this
        exact this
    · simp only [dif_neg hi]
      cases value with
      | none =>
        show Rep { s with regs := s.regs.set i 0 } c st
        rw [set_oob _ (by rw [hr.glen]; omega)]; exact hr
      | some ks =>
        obtain ⟨k, sign⟩ := ks
        show Rep { s with regs := s.regs.set i _ } c st
        rw [set_oob _ (by rw [hr.glen]; omega)]; exact hr

/-- Rep through a list of programs following a left fold. -/
theorem rep_seqList_foldl {α : Type} (P : α → Prg w) (f : WorkerState → α → WorkerState)
    (hstep : ∀ a s c st, Rep s c st → Rep (f s a) ((P a).eval D c st).1 ((P a).eval D c st).2) :
    ∀ (l : List α) (s : WorkerState) (c : WCtl w) (st : WSt w), Rep s c st →
      Rep (l.foldl f s) ((seqList P l).eval D c st).1 ((seqList P l).eval D c st).2
  | [], _, _, _, h => h
  | a :: l, s, c, st, h => rep_seqList_foldl P f hstep l _ _ _ (hstep a s c st h)

theorem initializeValues_cons (mapping : List (Pair × Option (DistKey × ℤ)))
    (e : Pair × Option (DistKey × ℤ)) (s : WorkerState) :
    initializeValues w.spec (e :: mapping) true s =
      initializeValues w.spec mapping true (initializeValues w.spec [e] true s) := by
  simp [initializeValues]

theorem rep_init (hD : 1 ≤ D) :
    ∀ (mapping : List (Pair × Option (DistKey × ℤ))) (s : WorkerState) (c : WCtl w) (st : WSt w),
      Rep s c st →
      Rep (initializeValues w.spec mapping true s) ((initP w mapping).eval D c st).1
        ((initP w mapping).eval D c st).2
  | [], s, c, st, h => by simpa [initializeValues, initP, seqList, Prog.eval] using h
  | e :: l, s, c, st, h => by
    rw [initializeValues_cons]
    exact rep_init hD l _ _ _ (rep_entry hD e h)

end Start

section StartOp
variable (w : Worker)

/-- The flag worker's `initializeValues` mapping. -/
def flagMap : List (Pair × Option (DistKey × ℤ)) :=
  [(("Lower", "Upper"), some (.h, -1)),
   (("Origin", "OriginalEnd"), some (.length, -1)),
   (("Origin", "Upper"), some (.length, -1)),
   (("OriginalEnd", "Lower"), some (.h, 1)),
   (("OriginalEnd", "TextOrigin"), some (.length, 1)),
   (("OriginalEnd", "Upper"), none)]

/-- The matcher's `initializeValues` mapping. -/
def tailMap : List (Pair × Option (DistKey × ℤ)) := [(("Origin", "Tail"), some (.length, -1))]

def runP : Prg w := .ctl fun c _ => { c with pc := toPc w w.spec.program.start, mode := .run }

def startP (b : Bool) : Prg w :=
  if b then
    if w.spec.isFlags then
      .seq (rawStartP w "Origin" begH false)
        (.seq (rawStartP w "TextOrigin" endH true)
          (.seq (rawStartP w "OriginalEnd" begH true)
            (.seq (initP w (flagMap))
              (.seq (.clear ixF) (runP w)))))
    else
      .seq (rawStartP w "Origin" endH true)
        (.seq (rawStartP w "Tail" endH false)
          (.seq (initP w tailMap) (runP w)))
  else .skip

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem rawStart_fault (n : String) (q : ℕ) (rv en : Bool) (s : WorkerState) :
    (rawStart w n q rv en s).fault = s.fault := by
  unfold rawStart; split
  · rfl
  · split <;> rfl

theorem setDist_fault (s : WorkerState) (k : DistKey) (v : ℤ) : (s.setDist k v).fault = s.fault := by
  cases k <;> rfl

theorem initializeValues_fault (spec : PalPeg.ScaGsProgram.WorkerSpec) (en : Bool) :
    ∀ (mapping : List (Pair × Option (DistKey × ℤ))) (s : WorkerState),
      (initializeValues spec mapping en s).fault = s.fault := by
  intro mapping
  cases en
  · intro s; rfl
  · induction mapping with
    | nil => intro s; rfl
    | cons e l ih =>
      intro s
      have := ih
      unfold initializeValues at this ⊢
      simp only [if_true, List.foldl_cons] at this ⊢
      rw [this]
      split
      · rfl
      · split
        · exact setDist_fault _ _ _
        · exact setDist_fault _ _ _

theorem start_fault (b : Bool) (s : WorkerState) :
    (start w b s).fault = (s.fault || (w.spec.isFlags && b && decide (s.mode = .run))) := by
  unfold start
  cases hF : w.spec.isFlags <;> cases b <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;>
    simp only [initializeValues_fault, rawStart_fault] <;> simp

theorem start_flags_eq (hF : w.spec.isFlags = true) (hs : s.fault = false) (hm : s.mode ≠ .run) :
    start w true s = { { initializeValues w.spec flagMap true
        (rawStart w "OriginalEnd" s.begin true true (rawStart w "TextOrigin" s.end true true
          (rawStart w "Origin" s.begin false true s))) with flags := [] } with
        pc := w.spec.program.start, mode := .run } := by
  have e : { s with fault := s.fault || (true && decide (s.mode = .run)) } = s := by
    cases s; simp_all
  unfold start
  simp only [hF, if_true]
  rw [e]
  rfl

theorem start_matcher_eq (hF : w.spec.isFlags = false) :
    start w true s = { initializeValues w.spec tailMap true
        (rawStart w "Tail" s.end false true (rawStart w "Origin" s.end true true s)) with
        pc := w.spec.program.start, mode := .run } := by
  unfold start
  simp only [hF]
  rfl

theorem start_false : start w false s = s := by
  unfold start
  cases hF : w.spec.isFlags
  · simp only [Bool.false_eq_true, if_false]
    unfold initializeValues rawStart
    simp only [Bool.false_eq_true, if_false]
    split <;> split <;> rfl
  · simp only [Bool.false_eq_true, if_false, if_true]
    unfold initializeValues rawStart
    simp only [Bool.false_eq_true, if_false, Bool.false_and, Bool.or_false]
    split <;> split <;> split <;> rfl

theorem rawStart_begin (n : String) (q : ℕ) (rv en : Bool) (s : WorkerState) :
    (rawStart w n q rv en s).begin = s.begin ∧ (rawStart w n q rv en s).end = s.end ∧
      (rawStart w n q rv en s).text = s.text := by
  unfold rawStart; split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

theorem Rep.run (h : Rep s c st) :
    Rep { s with pc := w.spec.program.start, mode := .run } ((runP w).eval D c st).1
      ((runP w).eval D c st).2 :=
  (h.setMode .run).setPc _ _ (toPc_val w (start_lt_pcBound w))

theorem rep_start (hD : 1 ≤ D) (b : Bool) (hr : Rep s c st) (hnf : (start w b s).fault = false) :
    Rep (start w b s) ((startP w b).eval D c st).1 ((startP w b).eval D c st).2 := by
  cases b
  · rw [start_false]; exact hr
  · cases hF : w.spec.isFlags
    · rw [start_matcher_eq hF]
      have h1 := rep_rawStart (D := D) "Origin" (src := endH) (fun i => (rdH_ne_endH i).symm) true
        hr hr.en
      have h2 := rep_rawStart (D := D) "Tail" (src := endH) (fun i => (rdH_ne_endH i).symm) false
        (q := s.end) h1 (by
          obtain ⟨-, e2, e3⟩ := rawStart_begin (w := w) "Origin" s.end true true s
          have := h1.en; rw [e2] at this; rw [e3]; rw [e3] at this; exact this)
      have h3 := rep_init (D := D) hD tailMap _ _ _ h2
      have h4 := h3.run (D := D)
      simp only [startP, hF, if_true, Bool.false_eq_true, if_false]
      exact h4
    · have hfs := start_fault (w := w) true s
      rw [hnf, hF] at hfs
      have hm : s.mode ≠ .run := by
        intro e; simp [e] at hfs
      rw [start_flags_eq hF hr.fault hm]
      have h1 := rep_rawStart (D := D) "Origin" (src := begH) (fun i => (rdH_ne_begH i).symm)
        false hr hr.beg
      obtain ⟨b1, e1, t1⟩ := rawStart_begin (w := w) "Origin" s.begin false true s
      have h2 := rep_rawStart (D := D) "TextOrigin" (src := endH) (fun i => (rdH_ne_endH i).symm)
        true (q := s.end) h1 (by have := h1.en; rw [e1] at this; rw [t1]; rw [t1] at this; exact this)
      obtain ⟨b2, e2, t2⟩ := rawStart_begin (w := w) "TextOrigin" s.end true true
        (rawStart w "Origin" s.begin false true s)
      have h3 := rep_rawStart (D := D) "OriginalEnd" (src := begH) (fun i => (rdH_ne_begH i).symm)
        true (q := s.begin) h2 (by
          have := h2.beg; rw [b2, b1] at this; rw [t2, t1]; rw [t2, t1] at this; exact this)
      have h4 := rep_init (D := D) hD flagMap _ _ _ h3
      have h5 := h4.clearFlags (D := D)
      have h6 := h5.run (D := D)
      simp only [startP, hF, if_true]
      exact h6

end StartOp

/-! ## One step: the decision -/

section Decision
variable {w : Worker}

/-- The step's decision (`ScaffoldWindowWorkers.scala:132-139`) on the abstract state. -/
def decA (f : Fields) (s : WorkerState) : Bool :=
  let e := f.event
  let (equal, less) := ScaWindowWorker.compare f s
  let (a, _) := s.readAt f.dataLeft
  let (b, _) := s.readAt f.dataRight
  let available := s.availableAt f.dataLeft
  if isOp e "equal" then equal
  else if isOp e "less" then less
  else if isOp e "available" then available
  else decide (a = b)

/-- The tested distance register is zero. -/
def eqC (f : Fields) (_ : WCtl w) (v : WSt w) : Bool :=
  match f.distanceTest with
  | none => true
  | some i => if h : i < nD w then (v (ixC (regC ⟨i, h⟩))).isEmpty else true

/-- The tested distance register is negative (positive when `distance.reverse`). -/
def lessC (f : Fields) (c : WCtl w) (v : WSt w) : Bool :=
  match f.distanceTest with
  | none => false
  | some i =>
    if h : i < nD w then
      if f.distanceReverse then (!c.sg (regC ⟨i, h⟩) && !(v (ixC (regC ⟨i, h⟩))).isEmpty)
      else c.sg (regC ⟨i, h⟩)
    else false

def availC (f : Fields) (_ : WCtl w) (v : WSt w) : Bool :=
  match f.dataLeft with
  | none => false
  | some i => available (headView (ixH (headOf i)) v)

def rdC (x : Option ℕ) (c : WCtl w) (v : WSt w) : Option Sym :=
  match x with
  | none => none
  | some i =>
    if revOf c i then readRev (headView (ixH (headOf i)) v) else readFwd (headView (ixH (headOf i)) v)

def decC (f : Fields) (c : WCtl w) (v : WSt w) : Bool :=
  if isOp f.event "equal" then eqC f c v
  else if isOp f.event "less" then lessC f c v
  else if isOp f.event "available" then availC f c v
  else decide (rdC f.dataLeft c v = rdC f.dataRight c v)

variable {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem isEmpty_view (hD : 1 ≤ D) (st : WSt w) (k : Fin (WK w)) :
    (view D st k).isEmpty = (st k).isEmpty := by
  show ((st k).take D).isEmpty = _
  cases h : st k with
  | nil => simp
  | cons x l => obtain ⟨m, rfl⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩; rfl

theorem crep_isEmpty {z : ℤ} {neg : Bool} {l : List Sym} (h : CRep Sym.tok z neg l) :
    l.isEmpty = decide (z = 0) := by
  rw [h.1]
  cases hz : z.natAbs with
  | zero => simp [Int.natAbs_eq_zero.mp hz]
  | succ n =>
    have : z ≠ 0 := by intro e; subst e; simp at hz
    simp [List.replicate_succ, this]

theorem selectReg_oob (hr : Rep s c st) {i : ℕ} (hi : ¬ i < nD w) : selectReg s.regs (some i) = 0 := by
  show s.regs.getD i 0 = 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hr.glen]; omega)]; rfl

theorem eqC_eq (hD : 1 ≤ D) (hr : Rep s c st) (f : Fields) :
    eqC f c (view D st) = (ScaWindowWorker.compare f s).1 := by
  unfold eqC ScaWindowWorker.compare
  cases ht : f.distanceTest with
  | none => simp [selectReg]
  | some i =>
    dsimp only
    split
    · rename_i hi
      rw [isEmpty_view hD, crep_isEmpty (hr.reg ⟨i, hi⟩)]; rfl
    · rename_i hi
      rw [selectReg_oob hr hi]; rfl

theorem lessC_eq (hD : 1 ≤ D) (hr : Rep s c st) (f : Fields) :
    lessC f c (view D st) = (ScaWindowWorker.compare f s).2 := by
  unfold lessC ScaWindowWorker.compare
  cases ht : f.distanceTest with
  | none => cases f.distanceReverse <;> simp [selectReg]
  | some i =>
    dsimp only
    split
    · rename_i hi
      have hc := hr.reg ⟨i, hi⟩
      rw [isEmpty_view hD, crep_isEmpty hc, hc.2]
      show _ = (if f.distanceReverse = true then decide (0 < s.regs.getD i 0)
        else decide (s.regs.getD i 0 < 0))
      generalize s.regs.getD i 0 = z
      cases f.distanceReverse
      · simp
      · rcases lt_trichotomy z 0 with h | h | h
        · simp [h, show ¬ (0 < z) by omega, show z ≠ 0 by omega]
        · subst h; simp
        · simp [h, show ¬ (z < 0) by omega, show z ≠ 0 by omega]
    · rename_i hi
      rw [selectReg_oob hr hi]; cases f.distanceReverse <;> rfl

theorem availC_eq (hD : 1 ≤ D) (hr : Rep s c st) (f : Fields) :
    availC f c (view D st) = s.availableAt f.dataLeft := by
  unfold availC
  cases f.dataLeft with
  | none => rfl
  | some i => exact available_view hD (hr.headOf i)

theorem rdC_eq (hD : 1 ≤ D) (hr : Rep s c st) (x : Option ℕ) :
    rdC x c (view D st) = (s.readAt x).1.map ι := by
  unfold rdC WorkerState.readAt
  cases x with
  | none => rfl
  | some i =>
    dsimp only
    rw [hr.revOf i]
    have hle := (hr.headOf i).le
    split
    · rw [readRev_view hD (hr.headOf i)]
      split
      · simp [*]
      · rename_i h0
        split
        · rfl
        · rename_i hlt
          rw [List.getElem?_eq_none (by omega)]
    · rw [readFwd_view hD (hr.headOf i)]
      split
      · rfl
      · rename_i hlt
        rw [List.getElem?_eq_none (by omega)]

theorem decC_eq (hD : 1 ≤ D) (hr : Rep s c st) (f : Fields) :
    decC f c (view D st) = decA f s := by
  unfold decC decA
  rw [eqC_eq hD hr, lessC_eq hD hr, availC_eq hD hr, rdC_eq hD hr, rdC_eq hD hr]
  have hinj : ∀ a b : Option (Fin 2), (a.map ι = b.map ι) = (a = b) :=
    fun a b => propext (Option.map_injective ι_inj).eq_iff
  simp only [hinj]

end Decision

/-! ## One step: the abstract pieces -/

section StepPieces
variable (w : Worker)

/-- Statements 132-146 of `step` (active): the fault bits and the matcher's output. -/
def s1A (f : Fields) (s : WorkerState) : WorkerState :=
  let active := true
  let e := f.event
  let (equal, _) := ScaWindowWorker.compare f s
  let symbolTest := active && isOp e "symbols"
  let (_, okA) := s.readAt f.dataLeft
  let (_, okB) := s.readAt f.dataRight
  let fault := s.fault || (symbolTest && !okA) || (symbolTest && !okB)
  let fault := fault || (active && isOp e "assert_equal" && !equal)
  let (fault, output) :=
    if w.spec.isFlags then (fault, s.output)
    else
      let matched := active && isOp e "match"
      let bReg := lookupFirst "B" w.spec.readers.colors
      (fault || (matched && s.availableAt bReg), s.output || matched)
  { s with fault, output }

/-- One iteration of the head-move loop (statements 148-160, active). -/
def moveBody (f : Fields) (srcPos : Option Nat) (srcRev : Option Bool) (s : WorkerState)
    (i : Nat) : WorkerState :=
  let active := true
  let e := f.event
  let p := s.data.getD i 0
  let r := s.reverse.getD i false
  let raw := f.dataDelta.getD i 0
  let δ := if r then -raw else raw
  let moving := active && δ ≠ 0
  let s := { s with fault := s.fault || (moving && !s.canMoveTo p δ),
                    data := if moving then s.data.set i ((p : Int) + δ).toNat else s.data }
  let copying := active && isOp e "copy" && f.dataTarget = some i
  match copying, srcPos, srcRev with
  | true, some q, some rv => { s with data := s.data.set i q, reverse := s.reverse.set i rv }
  | _, _, _ => s

/-- The head-move loop, with the copy source's snapshot. -/
def movesA (f : Fields) (s : WorkerState) : WorkerState :=
  let srcPos := f.dataSource.map fun j => s.data.getD j 0
  let srcRev := f.dataSource.map fun j => s.reverse.getD j false
  (List.range w.spec.readers.registers).foldl (moveBody f srcPos srcRev) s

/-- Statements 161-166 (active): flag push, halt. -/
def flagA (f : Fields) (s : WorkerState) : WorkerState :=
  let active := true
  let e := f.event
  if w.spec.isFlags then
    let s := if active && isOp e "flag" then { s with flags := f.bit :: s.flags } else s
    if active && isOp e "halt" then { s with mode := .done } else s
  else { s with fault := s.fault || (active && isOp e "halt") }

/-- **An active step, piece by piece.** -/
theorem step_true_eq (s : WorkerState) :
    step w true s =
      { flagA w (w.fields s.pc) (movesA w (w.fields s.pc)
          (execute (w.fields s.pc) true (s1A w (w.fields s.pc) s))) with
        pc := if decA (w.fields s.pc) s then (w.fields s.pc).yes else (w.fields s.pc).no } := rfl

theorem foldl_eta (l : List Nat) (s : WorkerState) :
    l.foldl (fun s _ => ({
        text := s.text, begin := s.begin, «end» := s.end, data := s.data,
        reverse := s.reverse, regs := s.regs, length := s.length, h := s.h, pc := s.pc,
        mode := s.mode, output := s.output, flags := s.flags, fault := s.fault } : WorkerState)) s = s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => exact ih s

/-- **An inactive step does nothing.** -/
theorem step_false (s : WorkerState) : step w false s = s := by
  unfold step execute
  simp only [Bool.false_and, Bool.or_false, if_false, Bool.false_eq_true, ite_self, foldl_eta]

/-- Two states that differ at most in the fault bit, the new one clear. -/
theorem Rep.of_fault {s s' : WorkerState} {c : WCtl w} {st : WSt w} (h : Rep s c st)
    (he : { s' with fault := false } = { s with fault := false }) (hf : s'.fault = false) :
    Rep s' c st := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := s
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := s'
  simp only [WorkerState.mk.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
  simp only at hf
  subst hf
  have := h.fault
  simp only at this
  subst this
  exact h

end StepPieces

/-! ## One step: the programs -/

section StepProgs
variable (w : Worker)

/-- Record the decision, update the matcher's output. -/
def decCtlP (f : Fields) : Prg w :=
  .ctl fun c v => { c with
    dec := decC f c v,
    output := if w.spec.isFlags then c.output else (c.output || isOp f.event "match") }

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem s1A_output (f : Fields) (s : WorkerState) :
    (s1A w f s).output =
      if w.spec.isFlags then s.output else (s.output || isOp f.event "match") := by
  unfold s1A; cases w.spec.isFlags <;> simp

theorem s1A_eta (f : Fields) (s : WorkerState) :
    { s1A w f s with fault := false } = { s with output := (s1A w f s).output, fault := false } := by
  unfold s1A; cases w.spec.isFlags <;> simp

theorem rep_decCtl (hD : 1 ≤ D) (f : Fields) (h : Rep s c st) (hnf : (s1A w f s).fault = false) :
    Rep (s1A w f s) ((decCtlP w f).eval D c st).1 ((decCtlP w f).eval D c st).2 ∧
      ((decCtlP w f).eval D c st).1.dec = decA f s := by
  refine ⟨?_, decC_eq hD h f⟩
  have h1 := h.setOutput (s1A w f s).output
  have h2 := h1.ctl { c with output := (s1A w f s).output, dec := decC f c (view D st) }
    rfl rfl rfl rfl rfl rfl
  have h3 := Rep.of_fault w h2 (s' := s1A w f s) (by rw [s1A_eta]) hnf
  have e : (s1A w f s).output =
      (if w.spec.isFlags then c.output else (c.output || isOp f.event "match")) := by
    rw [s1A_output, h.output]
  simp only [decCtlP, Prog.eval]
  rw [← e]
  exact h3

end StepProgs

/-! ## One step: `execute` (the simultaneous register transfer) -/

section Execute
variable (w : Worker)

def snapOneP (i : Fin (nD w)) : Prg w :=
  cpyP (ixC (snapC i)) (sl (snapC i)) (ixC (regC i)) (sl (regC i)) false

def loadP (u : RegUpdate) (i : Fin (nD w)) : Prg w :=
  match u.source with
  | none => clrP (ixC (regC i)) (sl (regC i))
  | some j =>
    if hj : j < nD w then
      cpyP (ixC (regC i)) (sl (regC i)) (ixC (snapC ⟨j, hj⟩)) (sl (snapC ⟨j, hj⟩)) u.reverse
    else clrP (ixC (regC i)) (sl (regC i))

def updOneP (f : Fields) (i : Fin (nD w)) : Prg w :=
  match f.regs[i.val]? with
  | none => .skip
  | some u => .seq (loadP w u i) (addP Sym.tok (ixC (regC i)) (sl (regC i)) u.delta)

/-- Snapshot every register, then load every register from the snapshots. -/
def execP (f : Fields) : Prg w :=
  .seq (seqList (snapOneP w) (List.finRange (nD w))) (seqList (updOneP w f) (List.finRange (nD w)))

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

/-- The new value of register `i`. -/
def newReg (f : Fields) (s : WorkerState) (i : ℕ) : ℤ :=
  match f.regs[i]? with
  | none => s.regs.getD i 0
  | some u =>
    let v := selectReg s.regs u.source
    (if u.reverse then -v else v) + u.delta

theorem execute_regs (f : Fields) (s : WorkerState) (i : ℕ) (hi : i < s.regs.length) :
    (execute f true s).regs.getD i 0 = newReg f s i := by
  simp only [execute, if_true, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some, newReg]
  cases f.regs[i]? with
  | none => simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  | some u => rfl

theorem cntProg_skip (j : Fin (2 * nD w + 2)) : CntProg j (.skip : Prg w) :=
  ⟨trivial, fun _ _ _ => trivial⟩

theorem cntProg_updOne (f : Fields) (i : Fin (nD w)) : CntProg (regC i) (updOneP w f i) := by
  unfold updOneP
  split
  · exact cntProg_skip _
  · refine cntProg_seq ?_ (cntProg_addP _ _)
    unfold loadP
    split
    · exact cntProg_clrP _
    · split
      · exact cntProg_cpyP _ _ _
      · exact cntProg_clrP _

theorem rep_snaps (hD : 1 ≤ D) (h : Rep s c st) :
    Rep s ((seqList (snapOneP w) (List.finRange (nD w))).eval D c st).1
        ((seqList (snapOneP w) (List.finRange (nD w))).eval D c st).2 ∧
      ∀ j : Fin (nD w), CRep Sym.tok (s.regs.getD j 0)
        (((seqList (snapOneP w) (List.finRange (nD w))).eval D c st).1.sg (snapC j))
        (((seqList (snapOneP w) (List.finRange (nD w))).eval D c st).2 (ixC (snapC j))) := by
  have key := seqList_spec D (snapOneP w) (fun c st => Rep s c st) (fun _ _ _ => True)
    (fun j c st => CRep Sym.tok (s.regs.getD j 0) (c.sg (snapC j)) (st (ixC (snapC j))))
    (fun j c st hG _ => by
      have := cpyP_spec (D := D) (k := ixC (snapC j)) (sg := sl (snapC j))
        (src := ixC (regC j)) (sgs := sl (regC j)) hD false (hG.reg j)
      simpa [snapOneP] using this)
    (fun j c st hG => hG.snap (D := D) j (cntProg_cpyP _ _ _))
    (fun _ _ _ _ _ _ => trivial)
    (fun a b c st hab hB => (cntProg_cpyP (snapC a) (regC a) false).crep
      (fun e => hab (snapC_inj e).symm) hB)
    (List.finRange (nD w)) (List.nodup_finRange _) c st h (fun _ _ => trivial)
  exact ⟨key.1, fun j => key.2 j (List.mem_finRange j)⟩

theorem rep_updates (hD : 1 ≤ D) (f : Fields) {c0 : WCtl w} {st0 : WSt w} (h : Rep s c0 st0)
    (hsnap : ∀ j : Fin (nD w), CRep Sym.tok (s.regs.getD j 0) (c0.sg (snapC j))
      (st0 (ixC (snapC j)))) :
    Rep (execute f true s) ((seqList (updOneP w f) (List.finRange (nD w))).eval D c0 st0).1
      ((seqList (updOneP w f) (List.finRange (nD w))).eval D c0 st0).2 := by
  let G : WCtl w → WSt w → Prop := fun c st =>
    Misc c = Misc c0 ∧ c.hc = c0.hc ∧ (∀ j, (∀ i, j ≠ regC i) → c.sg j = c0.sg j) ∧
      (∀ k, (∀ i, k ≠ ixC (regC i)) → st k = st0 k)
  have hsnapG : ∀ c st, G c st → ∀ j : Fin (nD w),
      CRep Sym.tok (s.regs.getD j 0) (c.sg (snapC j)) (st (ixC (snapC j))) := by
    intro c st hG j
    rw [hG.2.2.1 _ (fun i => (regC_ne_snapC i j).symm),
      hG.2.2.2 _ (fun i e => regC_ne_snapC i j (ixC_inj e).symm)]
    exact hsnap j
  have key := seqList_spec D (updOneP w f) G
    (fun i c st => CRep Sym.tok (s.regs.getD i 0) (c.sg (regC i)) (st (ixC (regC i))))
    (fun i c st => CRep Sym.tok (newReg f s i) (c.sg (regC i)) (st (ixC (regC i))))
    (fun i c st hG hA => by
      unfold updOneP newReg
      split
      · exact hA
      · rename_i u hu
        have hl : CRep Sym.tok (if u.reverse then -selectReg s.regs u.source
            else selectReg s.regs u.source) (((loadP w u i).eval D c st).1.sg (regC i))
            (((loadP w u i).eval D c st).2 (ixC (regC i))) := by
          unfold loadP
          cases hs : u.source with
          | none =>
            have := clrP_spec (tk := Sym.tok) (D := D) (k := ixC (regC i)) (sg := sl (regC i)) c st
            simpa [selectReg] using this
          | some j =>
            dsimp only
            by_cases hj : j < nD w
            · simp only [dif_pos hj]
              exact cpyP_spec (k := ixC (regC i)) (sg := sl (regC i)) (src := ixC (snapC ⟨j, hj⟩))
                (sgs := sl (snapC ⟨j, hj⟩)) hD u.reverse (hsnapG c st hG ⟨j, hj⟩)
            · simp only [dif_neg hj]
              have := clrP_spec (tk := Sym.tok) (D := D) (k := ixC (regC i)) (sg := sl (regC i)) c st
              rw [selectReg_oob h hj]
              simpa using this
        exact addP_spec (k := ixC (regC i)) (sg := sl (regC i)) hD u.delta hl)
    (fun i c st hG => by
      have hp := cntProg_updOne (w := w) f i
      refine ⟨(hp.misc c st).trans hG.1, (hp.hc c st).trans hG.2.1, fun j hj => ?_, fun k hk => ?_⟩
      · exact (hp.sg c st j (hj i)).trans (hG.2.2.1 j hj)
      · exact (hp.st c st k (hk i)).trans (hG.2.2.2 k hk))
    (fun a b c st hab hA => (cntProg_updOne f a).crep (fun e => hab (regC_inj e).symm) hA)
    (fun a b c st hab hB => (cntProg_updOne f a).crep (fun e => hab (regC_inj e).symm) hB)
    (List.finRange (nD w)) (List.nodup_finRange _) c0 st0 ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    (fun i _ => h.reg i)
  obtain ⟨⟨hmisc, hhc, hsg, hst⟩, hB⟩ := key
  obtain ⟨e1, e2, e3, e4, -, -⟩ := misc_eq hmisc
  have hg : ∀ {hd : Fin (nR w + 4)} {t : List (Fin 2)} {q : ℕ}, GH hd t q c0 st0 →
      GH hd t q ((seqList (updOneP w f) (List.finRange (nD w))).eval D c0 st0).1
        ((seqList (updOneP w f) (List.finRange (nD w))).eval D c0 st0).2 :=
    fun H => gh_frame H (by rw [hhc]) (fun sl => hst _ (fun i => ixH_ne_ixC _ sl _))
  exact {
    fault := h.fault, pc := (by rw [e1]; exact h.pc), mode := (by rw [e2]; exact h.mode),
    output := (by rw [e3]; exact h.output), dlen := h.dlen, rlen := h.rlen,
    glen := (by simp [execute, h.glen]),
    rd := fun i => hg (h.rd i), rv := fun i => (by rw [e4]; exact h.rv i),
    beg := hg h.beg, en := hg h.en, zero := hg h.zero,
    reg := fun i => (by
      rw [execute_regs f s i (by rw [h.glen]; exact i.isLt)]
      exact hB i (List.mem_finRange i)),
    len := (by
      rw [hsg _ (fun i => (regC_ne_lenC i).symm), hst _ (fun i e => regC_ne_lenC i (ixC_inj e).symm)]
      exact h.len),
    hh := (by
      rw [hsg _ (fun i => (regC_ne_hC i).symm), hst _ (fun i e => regC_ne_hC i (ixC_inj e).symm)]
      exact h.hh),
    flags := (by rw [hst _ (fun i => (ixC_ne_ixF _).symm)]; exact h.flags) }

theorem rep_execute (hD : 1 ≤ D) (f : Fields) (h : Rep s c st) :
    Rep (execute f true s) ((execP w f).eval D c st).1 ((execP w f).eval D c st).2 := by
  obtain ⟨h1, h2⟩ := rep_snaps (w := w) hD h
  exact rep_updates hD f h1 h2

end Execute

/-! ## One step: the head moves and the copy -/

section Moves
variable (w : Worker)

/-- The copy source's snapshot on the scratch head (`srcPos` / `srcRev`, statement 148). -/
def snapP (f : Fields) : Prg w :=
  match f.dataSource with
  | none => .skip
  | some j =>
    .seq (copyFromProg (hl (headOf j)) (hl scrH) (ixH (headOf j)) (ixH scrH))
      (.ctl fun c _ => { c with srev := revOf c j })

/-- Copy the snapshot into reader `i`. -/
def copyIntoP (f : Fields) (i : Fin (nR w)) : Prg w :=
  if (isOp f.event "copy" && decide (f.dataTarget = some i.val) && f.dataSource.isSome) then
    .seq (copyFromProg (hl scrH) (hl (rdH i)) (ixH scrH) (ixH (rdH i)))
      (.ctl fun c _ => { c with rev := Function.update c.rev i c.srev })
  else .skip

/-- One iteration of the loop: move reader `i` by its (reversed) delta, then the copy. -/
def moveOneP (f : Fields) (i : ℕ) : Prg w :=
  if h : i < nR w then
    .seq (.ite (fun c _ => c.rev ⟨i, h⟩)
        (moveByProg Sym.tok (hl (rdH ⟨i, h⟩)) (ixH (rdH ⟨i, h⟩)) (-(f.dataDelta.getD i 0)))
        (moveByProg Sym.tok (hl (rdH ⟨i, h⟩)) (ixH (rdH ⟨i, h⟩)) (f.dataDelta.getD i 0)))
      (copyIntoP w f ⟨i, h⟩)
  else .skip

def movesP (f : Fields) : Prg w := seqList (moveOneP w f) (List.range (nR w))

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

/-- The scratch head and bit hold the snapshot. -/
def ScrAt (t : List (Fin 2)) (sp : Option ℕ) (sr : Option Bool) (c : WCtl w) (st : WSt w) : Prop :=
  ∀ q rv, sp = some q → sr = some rv → GH scrH t q c st ∧ c.srev = rv

def deltaOf (f : Fields) (s : WorkerState) (i : ℕ) : ℤ :=
  if s.reverse.getD i false then -(f.dataDelta.getD i 0) else f.dataDelta.getD i 0

/-- The move half of an iteration. -/
def mvA (f : Fields) (s : WorkerState) (i : ℕ) : WorkerState :=
  { s with
    fault := s.fault || (decide (deltaOf f s i ≠ 0) &&
      !s.canMoveTo (s.data.getD i 0) (deltaOf f s i)),
    data := if decide (deltaOf f s i ≠ 0) then
      s.data.set i (((s.data.getD i 0 : ℕ) : ℤ) + deltaOf f s i).toNat else s.data }

/-- The copy half of an iteration. -/
def cpA (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState) (i : ℕ) : WorkerState :=
  match (true && isOp f.event "copy" && decide (f.dataTarget = some i)), sp, sr with
  | true, some q, some rv => { s with data := s.data.set i q, reverse := s.reverse.set i rv }
  | _, _, _ => s

theorem moveBody_eq (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState) (i : ℕ) :
    moveBody f sp sr s i = cpA f sp sr (mvA f s i) i := rfl

theorem cpA_fault (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState) (i : ℕ) :
    (cpA f sp sr s i).fault = s.fault ∧ (cpA f sp sr s i).text = s.text := by
  unfold cpA; split <;> exact ⟨rfl, rfl⟩

theorem moveBody_fault (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState) (i : ℕ)
    (h : (moveBody f sp sr s i).fault = false) : s.fault = false := by
  rw [moveBody_eq, (cpA_fault _ _ _ _ _).1] at h
  simp only [mvA, Bool.or_eq_false_iff] at h
  exact h.1

theorem moveBody_text (f : Fields) (sp : Option ℕ) (sr : Option Bool) (s : WorkerState) (i : ℕ) :
    (moveBody f sp sr s i).text = s.text := by
  rw [moveBody_eq, (cpA_fault _ _ _ _ _).2]; rfl

theorem set_getD_self {α : Type} (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.set i (l.getD i d) = l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

theorem rep_snapP (f : Fields) (h : Rep s c st) :
    Rep s ((snapP w f).eval D c st).1 ((snapP w f).eval D c st).2 ∧
      ScrAt s.text (f.dataSource.map fun j => s.data.getD j 0)
        (f.dataSource.map fun j => s.reverse.getD j false)
        ((snapP w f).eval D c st).1 ((snapP w f).eval D c st).2 := by
  unfold snapP
  cases hsrc : f.dataSource with
  | none => exact ⟨h, fun q rv hq _ => by simp at hq⟩
  | some j =>
    dsimp only
    have hc := copyFromProg_correct (ι := ι) (lA := hl (headOf j)) (lB := hl scrH)
      (ixA := ixH (headOf j)) (ixB := ixH scrH) (ixH_inj _)
      (fun s s' => ixH_ne (headOf_ne_scrH j) s s')
      (fun c x => hl_indep (Ne.symm (headOf_ne_scrH j)) c x) D (h.headOf j)
    have h1 := h.scr (D := D) (headProg_copyFrom (headOf j) scrH)
    set c1 := ((copyFromProg (hl (headOf j)) (hl scrH) (ixH (headOf j)) (ixH scrH) : Prg w).eval
      D c st).1
    set st1 := ((copyFromProg (hl (headOf j)) (hl scrH) (ixH (headOf j)) (ixH scrH) : Prg w).eval
      D c st).2
    refine ⟨h1.ctl { c1 with srev := revOf c1 j } rfl rfl rfl rfl rfl rfl, ?_⟩
    intro q rv hq hrv
    simp only [Option.map_some, Option.some.injEq] at hq hrv
    subst hq hrv
    exact ⟨gh_frame hc.1 rfl (fun _ => rfl), h1.revOf j⟩

theorem rep_moveOne (hD : 17 ≤ D) (f : Fields) {sp : Option ℕ} {sr : Option Bool}
    (hsp : sp.isSome = f.dataSource.isSome) (hsr : sr.isSome = f.dataSource.isSome)
    {i : ℕ} (hi : i < nR w) (h : Rep s c st) (hscr : ScrAt s.text sp sr c st)
    (hnf : (moveBody f sp sr s i).fault = false) :
    Rep (moveBody f sp sr s i) ((moveOneP w f i).eval D c st).1 ((moveOneP w f i).eval D c st).2 ∧
      ScrAt s.text sp sr ((moveOneP w f i).eval D c st).1 ((moveOneP w f i).eval D c st).2 := by
  rw [moveBody_eq] at hnf ⊢
  have hmvf : (mvA f s i).fault = false := by rw [← (cpA_fault f sp sr _ i).1]; exact hnf
  set p := s.data.getD i 0 with hp
  set δ := deltaOf f s i with hδ
  -- the move stays inside the text
  have hbounds : 0 ≤ (p : ℤ) + δ ∧ (p : ℤ) + δ ≤ s.text.length := by
    have hle := (h.rd ⟨i, hi⟩).le
    by_cases h0 : δ = 0
    · rw [h0]; simp only [add_zero]; exact ⟨by omega, by exact_mod_cast hle⟩
    · simp only [mvA, Bool.or_eq_false_iff] at hmvf
      have hm := hmvf.2
      rw [← hδ, ← hp] at hm
      simp only [h0, decide_true, ne_eq, not_false_eq_true, Bool.true_and,
        Bool.not_eq_false'] at hm
      simp only [WorkerState.canMoveTo, Bool.and_eq_true, decide_eq_true_eq] at hm
      exact hm
  -- the move program
  let P1 : Prg w := .ite (fun c _ => c.rev ⟨i, hi⟩)
    (moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) (-(f.dataDelta.getD i 0)))
    (moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) (f.dataDelta.getD i 0))
  have hP1 : P1.eval D c st =
      (moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ).eval D c st := by
    simp only [P1, Prog.eval, h.rv ⟨i, hi⟩, hδ, deltaOf]
    split <;> rfl
  have hmp : HeadProg (rdH ⟨i, hi⟩) (moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ) :=
    headProg_moveBy _ _
  have hmv := moveByProg_correct (ι := ι) (tk := Sym.tok) (ixH_inj (rdH ⟨i, hi⟩)) hD
    (h.rd ⟨i, hi⟩) hbounds.1 hbounds.2
  have h1 := h.setData (D := D) ⟨i, hi⟩ hmp hmv
  have hmvA : mvA f s i = { s with data := s.data.set i ((p : ℤ) + δ).toNat } := by
    simp only [mvA, Bool.or_eq_false_iff] at hmvf
    simp only [mvA, hmvf.2, hmvf.1, Bool.or_false]
    rw [← hδ, ← hp]
    by_cases h0 : δ = 0
    · simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
        add_zero, Int.toNat_natCast]
      rw [hp, set_getD_self _ (by rw [h.dlen]; exact hi)]
    · simp [h0]
  rw [← hmvA] at h1
  have hscr1 : ScrAt s.text sp sr ((moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ).eval
      D c st).1 ((moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ).eval D c st).2 := by
    intro q rv hq hrv
    obtain ⟨hg, hs⟩ := hscr q rv hq hrv
    refine ⟨hmp.gh (Ne.symm (rdH_ne_scrH _)) hg, ?_⟩
    rw [← hs]; exact (misc_eq (hmp.misc c st)).2.2.2.2.2
  -- the copy
  have htext : (mvA f s i).text = s.text := rfl
  have e : moveOneP w f i = .seq P1 (copyIntoP w f ⟨i, hi⟩) := by
    unfold moveOneP; rw [dif_pos hi]
  rw [e, evalSeq, hP1]
  set c1 := ((moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ : Prg w).eval D c st).1
  set st1 := ((moveByProg Sym.tok (hl (rdH ⟨i, hi⟩)) (ixH (rdH ⟨i, hi⟩)) δ : Prg w).eval D c st).2
  unfold copyIntoP cpA
  by_cases hcond : (isOp f.event "copy" && decide (f.dataTarget = some i) && f.dataSource.isSome) = true
  · rw [if_pos hcond]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨⟨hcp, htg⟩, hsome⟩ := hcond
    obtain ⟨q, rfl⟩ := Option.isSome_iff_exists.mp (hsp.trans hsome)
    obtain ⟨rv, rfl⟩ := Option.isSome_iff_exists.mp (hsr.trans hsome)
    simp only [hcp, htg, decide_true, Bool.true_and]
    obtain ⟨hg, hs⟩ := hscr1 q rv rfl rfl
    have hc := copyFromProg_correct (ι := ι) (lA := hl scrH) (lB := hl (rdH ⟨i, hi⟩))
      (ixA := ixH scrH) (ixB := ixH (rdH ⟨i, hi⟩)) (ixH_inj _)
      (fun s s' => ixH_ne (Ne.symm (rdH_ne_scrH _)) s s')
      (fun c x => hl_indep (rdH_ne_scrH _) c x) D hg
    have h2 := h1.setData (D := D) ⟨i, hi⟩ (headProg_copyFrom scrH (rdH ⟨i, hi⟩)) (q := q)
      (by rw [htext]; exact hc.1)
    set c2 := ((copyFromProg (hl scrH) (hl (rdH ⟨i, hi⟩)) (ixH scrH) (ixH (rdH ⟨i, hi⟩)) : Prg w).eval
      D c1 st1).1
    have hsrev : c2.srev = rv := by
      rw [← hs]; exact (misc_eq ((headProg_copyFrom scrH (rdH ⟨i, hi⟩)).misc c1 st1)).2.2.2.2.2
    have h3' := h2.setRev ⟨i, hi⟩ rv
    have h3 := Rep.ctl h3' { c2 with rev := Function.update c2.rev ⟨i, hi⟩ c2.srev } rfl rfl rfl
      (by rw [hsrev]) rfl rfl
    refine ⟨h3, ?_⟩
    intro q' rv' hq' hrv'
    simp only [Option.some.injEq] at hq' hrv'
    subst hq' hrv'
    refine ⟨gh_frame hc.2.1 rfl (fun _ => rfl), hsrev⟩
  · rw [if_neg hcond]
    refine ⟨?_, hscr1⟩
    have hsplit : (true && isOp f.event "copy" && decide (f.dataTarget = some i)) = false ∨
        (sp = none ∧ sr = none) := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcond
      by_cases hc1 : (isOp f.event "copy" && decide (f.dataTarget = some i)) = true
      · right
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc1
        have hn := hcond hc1
        have e1 : sp.isSome = false := by rw [hsp]; simpa using hn
        have e2 : sr.isSome = false := by rw [hsr]; simpa using hn
        exact ⟨Option.isSome_eq_false_iff.mp e1 |> fun h => by simpa using h,
          Option.isSome_eq_false_iff.mp e2 |> fun h => by simpa using h⟩
      · left; simpa using hc1
    rcases hsplit with hc | ⟨rfl, rfl⟩
    · rw [hc]; exact h1
    · split <;> first | exact h1 | (rename_i hh; simp at hh)

end Moves

section MovesFold
variable {w : Worker} {D : ℕ}

theorem fold_moveBody_fault (f : Fields) (sp : Option ℕ) (sr : Option Bool) :
    ∀ (l : List ℕ) (s : WorkerState), (l.foldl (moveBody f sp sr) s).fault = false →
      s.fault = false
  | [], _, h => h
  | a :: l, s, h => moveBody_fault f sp sr s a (fold_moveBody_fault f sp sr l _ h)

theorem rep_movesFold (hD : 17 ≤ D) (f : Fields) {sp : Option ℕ} {sr : Option Bool}
    (hsp : sp.isSome = f.dataSource.isSome) (hsr : sr.isSome = f.dataSource.isSome)
    (t : List (Fin 2)) :
    ∀ (l : List ℕ), (∀ i ∈ l, i < nR w) → ∀ (s : WorkerState) (c : WCtl w) (st : WSt w),
      s.text = t → Rep s c st → ScrAt t sp sr c st → (l.foldl (moveBody f sp sr) s).fault = false →
      Rep (l.foldl (moveBody f sp sr) s) ((seqList (moveOneP w f) l).eval D c st).1
        ((seqList (moveOneP w f) l).eval D c st).2
  | [], _, _, _, _, _, h, _, _ => h
  | a :: l, hl, s, c, st, ht, h, hscr, hnf => by
    have hf1 : (moveBody f sp sr s a).fault = false := fold_moveBody_fault f sp sr l _ hnf
    rw [← ht] at hscr
    obtain ⟨h1, hs1⟩ := rep_moveOne hD f hsp hsr (hl a (by simp)) h hscr hf1
    exact rep_movesFold hD f hsp hsr t l (fun i hi => hl i (by simp [hi])) _ _ _
      ((moveBody_text f sp sr s a).trans ht) h1 (ht ▸ hs1) hnf

theorem rep_moves (hD : 17 ≤ D) (f : Fields) {s : WorkerState} {c : WCtl w} {st : WSt w}
    (h : Rep s c st)
    (hscr : ScrAt s.text (f.dataSource.map fun j => s.data.getD j 0)
      (f.dataSource.map fun j => s.reverse.getD j false) c st)
    (hnf : (movesA w f s).fault = false) :
    Rep (movesA w f s) ((movesP w f).eval D c st).1 ((movesP w f).eval D c st).2 :=
  rep_movesFold hD f (by cases f.dataSource <;> rfl) (by cases f.dataSource <;> rfl) s.text
    (List.range (nR w)) (fun i hi => List.mem_range.mp hi) s c st rfl h hscr hnf

end MovesFold

/-! ## One step: flags, `pc`, the whole row -/

section Row
variable (w : Worker)

def flagP (f : Fields) : Prg w :=
  if w.spec.isFlags then
    .seq (if isOp f.event "flag" then .push ixF (fun _ _ => Sym.flag f.bit) else .skip)
      (if isOp f.event "halt" then .ctl (fun c _ => { c with mode := .done }) else .skip)
  else .skip

def pcP (f : Fields) : Prg w := .ctl fun c _ => { c with pc := toPc w (if c.dec then f.yes else f.no) }

/-- **The program of one active step at a row.** -/
def rowP (f : Fields) : Prg w :=
  .seq (decCtlP w f) (.seq (execP w f) (.seq (snapP w f) (.seq (movesP w f)
    (.seq (flagP w f) (pcP w f)))))

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem flagA_fault (f : Fields) (s : WorkerState) (h : (flagA w f s).fault = false) :
    s.fault = false := by
  unfold flagA at h
  cases hF : w.spec.isFlags
  · simp only [hF, Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at h; exact h.1
  · simp only [hF, if_true] at h
    split at h <;> (split at h <;> exact h)

theorem movesA_fault (f : Fields) (s : WorkerState) (h : (movesA w f s).fault = false) :
    s.fault = false :=
  fold_moveBody_fault f _ _ _ s h

theorem rep_flag (f : Fields) (h : Rep s c st) (hnf : (flagA w f s).fault = false) :
    Rep (flagA w f s) ((flagP w f).eval D c st).1 ((flagP w f).eval D c st).2 := by
  unfold flagA flagP
  cases hF : w.spec.isFlags
  · simp only [Bool.false_eq_true, if_false]
    refine Rep.of_fault w h (by rfl) ?_
    unfold flagA at hnf; simpa [hF] using hnf
  · simp only [if_true, Bool.true_and]
    rw [evalSeq]
    have h1 : Rep (if isOp f.event "flag" = true then { s with flags := f.bit :: s.flags } else s)
        ((if isOp f.event "flag" = true then .push ixF (fun _ _ => Sym.flag f.bit) else .skip :
          Prg w).eval D c st).1
        ((if isOp f.event "flag" = true then .push ixF (fun _ _ => Sym.flag f.bit) else .skip :
          Prg w).eval D c st).2 := by
      split
      · exact h.pushFlag f.bit
      · exact h
    split
    · exact h1.setMode .done
    · exact h1

theorem rep_pc (f : Fields) (hf : f.yes < pcBound w ∧ f.no < pcBound w) (h : Rep s c st) :
    Rep { s with pc := if c.dec then f.yes else f.no } ((pcP w f).eval D c st).1
      ((pcP w f).eval D c st).2 :=
  h.setPc _ _ (toPc_val w (by split <;> omega))

theorem ckeeps_dec_exec (f : Fields) : CKeeps (fun c : WCtl w => c.dec) (execP w f) :=
  ⟨ckeeps_seqList _ (fun _ _ => (cntProg_cpyP _ _ _).2 _ _ (fun _ _ => rfl)),
    ckeeps_seqList _ (fun i _ => (cntProg_updOne f i).2 _ _ (fun _ _ => rfl))⟩

theorem ckeeps_dec_snap (f : Fields) : CKeeps (fun c : WCtl w => c.dec) (snapP w f) := by
  unfold snapP; split
  · trivial
  · exact ⟨(headProg_copyFrom _ _).2 _ _ (fun _ _ => rfl), fun _ _ => rfl⟩

theorem ckeeps_dec_moves (f : Fields) : CKeeps (fun c : WCtl w => c.dec) (movesP w f) := by
  refine ckeeps_seqList _ (fun i _ => ?_)
  unfold moveOneP; split
  · refine ⟨⟨(headProg_moveBy _ _).2 _ _ (fun _ _ => rfl), (headProg_moveBy _ _).2 _ _
      (fun _ _ => rfl)⟩, ?_⟩
    unfold copyIntoP; split
    · exact ⟨(headProg_copyFrom _ _).2 _ _ (fun _ _ => rfl), fun _ _ => rfl⟩
    · trivial
  · trivial

theorem ckeeps_dec_flag (f : Fields) : CKeeps (fun c : WCtl w => c.dec) (flagP w f) := by
  unfold flagP; split
  · refine ⟨?_, ?_⟩
    · split <;> trivial
    · split
      · exact fun _ _ => rfl
      · trivial
  · trivial

/-- **One active step.** -/
theorem rep_row (hD : 17 ≤ D) (h : Rep s c st) (hnf : (step w true s).fault = false) :
    Rep (step w true s) ((rowP w (w.fields s.pc)).eval D c st).1
      ((rowP w (w.fields s.pc)).eval D c st).2 := by
  set f := w.fields s.pc with hfdef
  rw [step_true_eq] at hnf ⊢
  have nf4 : (flagA w f (movesA w f (execute f true (s1A w f s)))).fault = false := hnf
  have nf3 : (movesA w f (execute f true (s1A w f s))).fault = false := flagA_fault f _ nf4
  have nf2 : (execute f true (s1A w f s)).fault = false := movesA_fault f _ nf3
  have nf1 : (s1A w f s).fault = false := by
    have : (execute f true (s1A w f s)).fault = (s1A w f s).fault := rfl
    rw [← this]; exact nf2
  obtain ⟨h1, hdec⟩ := rep_decCtl (D := D) (by omega) f h nf1
  set c1 := ((decCtlP w f).eval D c st).1
  set st1 := ((decCtlP w f).eval D c st).2
  have h2 := rep_execute (D := D) (by omega) f h1
  set c2 := ((execP w f).eval D c1 st1).1
  set st2 := ((execP w f).eval D c1 st1).2
  obtain ⟨h3, hscr⟩ := rep_snapP (D := D) f h2
  set c3 := ((snapP w f).eval D c2 st2).1
  set st3 := ((snapP w f).eval D c2 st2).2
  have h4 := rep_moves hD f h3 hscr nf3
  set c4 := ((movesP w f).eval D c3 st3).1
  set st4 := ((movesP w f).eval D c3 st3).2
  have h5 := rep_flag (D := D) f h4 nf4
  set c5 := ((flagP w f).eval D c4 st4).1
  set st5 := ((flagP w f).eval D c4 st4).2
  have hd5 : c5.dec = decA f s := by
    rw [← hdec]
    have e2 : c2.dec = c1.dec := eval_ctl_frame (fun c : WCtl w => c.dec) D _ (ckeeps_dec_exec f) c1 st1
    have e3 : c3.dec = c2.dec := eval_ctl_frame (fun c : WCtl w => c.dec) D _ (ckeeps_dec_snap f) c2 st2
    have e4 : c4.dec = c3.dec :=
      eval_ctl_frame (fun c : WCtl w => c.dec) D _ (ckeeps_dec_moves f) c3 st3
    have e5 : c5.dec = c4.dec := eval_ctl_frame (fun c : WCtl w => c.dec) D _ (ckeeps_dec_flag f) c4 st4
    rw [e5, e4, e3, e2]
  have h6 := rep_pc (D := D) f (fields_succ_lt w s.pc) h5
  rw [hd5] at h6
  exact h6

end Row

/-! ## `step` and `service` -/

section Service
variable (w : Worker)

/-- Dispatch on `pc` over the rows. -/
def dispatchP (l : List ℕ) : Prg w :=
  l.foldr (fun n p => .ite (fun c _ => decide (c.pc.val = n)) (rowP w (w.fields n)) p) .skip

/-- `step(mode = run)`. -/
def stepP : Prg w :=
  .ite (fun c _ => decide (c.mode = .run)) (dispatchP w (List.range (pcBound w))) .skip

/-- `service()`: `quantum` steps. -/
def serviceP : Prg w := repeatProg (stepP w) w.spec.quantum

variable {w} {D : ℕ} {s : WorkerState} {c : WCtl w} {st : WSt w}

theorem dispatch_eval (c : WCtl w) (st : WSt w) :
    ∀ l : List ℕ, c.pc.val ∈ l →
      (dispatchP w l).eval D c st = (rowP w (w.fields c.pc.val)).eval D c st
  | [], h => by simp at h
  | n :: l, h => by
    simp only [dispatchP, List.foldr_cons, Prog.eval]
    by_cases e : c.pc.val = n
    · rw [if_pos (decide_eq_true e), e]
    · rw [if_neg (by simpa using e)]
      exact dispatch_eval c st l (by simpa [e] using h)

theorem step_fault_mono (a : Bool) (s : WorkerState) (h : (step w a s).fault = false) :
    s.fault = false := by
  cases a
  · rwa [step_false] at h
  · rw [step_true_eq] at h
    have nf4 : (flagA w _ (movesA w _ (execute _ true (s1A w (w.fields s.pc) s)))).fault = false :=
      h
    have nf2 := movesA_fault _ _ (flagA_fault _ _ nf4)
    have nf1 : (s1A w (w.fields s.pc) s).fault = false := nf2
    unfold s1A at nf1
    cases hF : w.spec.isFlags <;> simp_all

theorem rep_stepP (hD : 17 ≤ D) (h : Rep s c st)
    (hnf : (step w (decide (s.mode = .run)) s).fault = false) :
    Rep (step w (decide (s.mode = .run)) s) ((stepP w).eval D c st).1
      ((stepP w).eval D c st).2 := by
  by_cases hm : s.mode = .run
  · have hcm : c.mode = .run := h.mode.trans hm
    simp only [hm, decide_true] at hnf ⊢
    simp only [stepP, Prog.eval, hcm, decide_true, if_true]
    rw [dispatch_eval c st _ (List.mem_range.mpr c.pc.isLt), h.pc]
    exact rep_row hD h hnf
  · have hcm : c.mode ≠ .run := fun e => hm (h.mode.symm.trans e)
    simp only [hm, decide_false] at hnf ⊢
    simp only [stepP, Prog.eval, hcm, decide_false, Bool.false_eq_true, if_false, step_false]
    exact h

theorem foldl_range_iterate (g : WorkerState → WorkerState) :
    ∀ (n : ℕ) (s : WorkerState), (List.range n).foldl (fun s _ => g s) s = g^[n] s
  | 0, _ => rfl
  | n + 1, s => by
    rw [List.range_succ, List.foldl_append, foldl_range_iterate g n s, List.foldl_cons,
      List.foldl_nil, Function.iterate_succ_apply']

theorem service_eq (s : WorkerState) :
    service w s = (fun s => step w (decide (s.mode = .run)) s)^[w.spec.quantum] s :=
  foldl_range_iterate _ _ s

theorem iterate_fault (n : ℕ) :
    ∀ s : WorkerState, ((fun s => step w (decide (s.mode = .run)) s)^[n] s).fault = false →
      s.fault = false := by
  induction n with
  | zero => intro s h; exact h
  | succ n ih =>
    intro s h
    rw [Function.iterate_succ_apply] at h
    exact step_fault_mono _ s (ih _ h)

theorem rep_iterate (hD : 17 ≤ D) (n : ℕ) :
    ∀ (s : WorkerState) (c : WCtl w) (st : WSt w), Rep s c st →
      ((fun s => step w (decide (s.mode = .run)) s)^[n] s).fault = false →
      Rep ((fun s => step w (decide (s.mode = .run)) s)^[n] s) ((repeatProg (stepP w) n).eval D c st).1
        ((repeatProg (stepP w) n).eval D c st).2 := by
  induction n with
  | zero => intro s c st h _; exact h
  | succ n ih =>
    intro s c st h hnf
    rw [Function.iterate_succ_apply] at hnf ⊢
    have h1 := rep_stepP hD h (iterate_fault n _ hnf)
    exact ih _ _ _ h1 hnf

theorem rep_service (hD : 17 ≤ D) (h : Rep s c st) (hnf : (service w s).fault = false) :
    Rep (service w s) ((serviceP w).eval D c st).1 ((serviceP w).eval D c st).2 := by
  rw [service_eq] at hnf ⊢
  exact rep_iterate hD _ s c st h hnf

theorem service_fault_mono (s : WorkerState) (h : (service w s).fault = false) : s.fault = false := by
  rw [service_eq] at h; exact iterate_fault _ s h

end Service

/-! ## The encodings -/

section Enc
variable (w : Worker)

theorem arrive_fault_mono (a : Fin 2) (s : WorkerState) (h : (arrive w a s).fault = false) :
    s.fault = false := by
  unfold arrive at h
  cases hF : w.spec.isFlags <;> simp_all

theorem sticky_of_mono {g : WorkerState → WorkerState}
    (mono : ∀ s, (g s).fault = false → s.fault = false) (s : WorkerState) (hs : s.fault = true) :
    (g s).fault = true := by
  cases h : (g s).fault
  · rw [mono s h] at hs; exact hs
  · rfl

/-- **Any worker, as stack programs** (at any peek `D ≥ 17`). -/
def workerEnc (D : ℕ) (hD : 17 ≤ D) :
    ScaWindowEncode.WorkerEnc WorkerState (ScaWindowInstance.opsOf w) Sym (WCtl w) (WK w) D where
  Rep := Rep
  arrive a := arriveP w a
  resetFlags b := resetP w b
  start b := startP w b
  mark b := markP w b
  service := serviceP w
  output c := c.output
  modeDone c := decide (c.mode = .done)
  faulted _ := false
  flagsIdx := ixF
  flagSym := Sym.flag
  flagDecode := flagDec
  flagDecode_sym _ := rfl
  rep_arrive a _ _ _ h hnf := rep_arrive hD a h hnf
  rep_resetFlags b _ _ _ h _ := rep_resetFlags b h
  rep_start b _ _ _ h hnf := rep_start (by omega) b h hnf
  rep_mark b _ _ _ h _ := rep_mark b h
  rep_service _ _ _ h hnf := rep_service hD h hnf
  sticky_arrive a := sticky_of_mono (arrive_fault_mono w a)
  sticky_resetFlags b := sticky_of_mono (fun s h => by cases b <;> exact h)
  sticky_start b := sticky_of_mono (fun s h => by
    have h' : (start w b s).fault = false := h
    have := start_fault (w := w) b s
    rw [h'] at this
    exact (Bool.or_eq_false_iff.mp this.symm).1)
  sticky_mark b := sticky_of_mono (fun s h => by cases b <;> exact h)
  sticky_service := sticky_of_mono (service_fault_mono (w := w))
  rep_output _ _ _ h := h.output.symm
  rep_modeDone _ _ _ h := by
    show decide (_ = Mode.done) = decide (_ = Mode.done)
    rw [h.mode]
  rep_faulted _ _ _ h := h.fault
  rep_flags _ _ _ h := h.flags

/-- The initial control: `pc` at the start, every head and counter at rest. -/
def initCtl : WCtl w where
  pc := toPc w w.spec.program.start
  mode := .idle
  output := false
  rev := fun _ => false
  hc := fun _ => ⟨.idle, false⟩
  sg := fun _ => false
  dec := false
  srev := false

theorem gh_empty (h : Fin (nR w + 4)) : GH h [] 0 (initCtl w) (fun _ => []) :=
  ⟨le_rfl, rfl, ⟨[], RTQueue.empty, RTQueue.inv_empty,
    ⟨rfl, rfl, rfl, by simp [bal, balOf, pending, RTQueue.empty, initCtl, hl]⟩, rfl, rfl⟩⟩

theorem getD_replicate {α : Type} (n i : ℕ) (a : α) : (List.replicate n a).getD i a = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- **The initial worker is represented by the initial control and empty stacks.** -/
theorem rep_initial : Rep (WorkerState.initial w.spec) (initCtl w) (fun _ => []) where
  fault := rfl
  pc := toPc_val w (start_lt_pcBound w)
  mode := rfl
  output := rfl
  dlen := List.length_replicate
  rlen := List.length_replicate
  glen := List.length_replicate
  rd i := by
    show GH _ [] ((List.replicate _ 0).getD i 0) _ _
    rw [getD_replicate]; exact gh_empty w _
  rv i := by
    show false = (List.replicate _ false).getD i false
    rw [getD_replicate]
  beg := gh_empty w _
  en := gh_empty w _
  zero := gh_empty w _
  reg i := by
    show CRep Sym.tok ((List.replicate _ 0).getD i 0) false []
    rw [getD_replicate]; exact ⟨rfl, rfl⟩
  len := ⟨rfl, rfl⟩
  hh := ⟨rfl, rfl⟩
  flags := rfl

end Enc

/-! ## The two real workers -/

open PalPeg.ScaWindowInstance

/-- **The real GS matcher as stack programs.** -/
def matcherEnc :
    ScaWindowEncode.WorkerEnc WorkerState matcherOps Sym (WCtl matcher) (WK matcher) 17 :=
  workerEnc matcher 17 le_rfl

/-- **The real GS flag worker as stack programs.** -/
def flagsEnc :
    ScaWindowEncode.WorkerEnc WorkerState flagsOps Sym (WCtl flagsW) (WK flagsW) 17 :=
  workerEnc flagsW 17 le_rfl

theorem matcherEnc_init : matcherEnc.Rep matcherInit (initCtl matcher) fun _ => [] :=
  rep_initial matcher

theorem flagsEnc_init : flagsEnc.Rep flagsInit (initCtl flagsW) fun _ => [] :=
  rep_initial flagsW

example : Finite Sym := inferInstance
example : Inhabited Sym := inferInstance
example : Finite (WCtl matcher) := inferInstance
example : Finite (WCtl flagsW) := inferInstance

open PalPeg.ScaWindowPal in
/-- **`PAL ∈ PEG` from the real workers**: `ScaWindowEncode.pal_in_peg_of_workers` with the two
encodings of this file. What remains are the four worker obligations of `ScaWindowTop`. -/
theorem pal_in_peg_of_real_workers
    (hmatch : ∀ w : List (Fin 2), 4 ≤ w.length →
      (matcherOps.output ((run matcherOps flagsOps matcherInit flagsInit w).matchers
          (ScaWindowSchedule.idx (Nat.log 2 w.length))) = true ↔
        occursAt (w.take (stageOf w.length)).reverse w))
    (hmiddle : ∀ w : List (Fin 2), 4 ≤ w.length →
      (((run matcherOps flagsOps matcherInit flagsInit w).stages
          (ScaWindowSchedule.idx (Nat.log 2 w.length))).middle = true ↔
        IsPal ((w.drop (stageOf w.length)).take (w.length - 2 * stageOf w.length))))
    (hclean : ∀ u : List (Fin 2),
      ScaWindowFault.ctlViolation (run matcherOps flagsOps matcherInit flagsInit u) = false)
    (hworkers : ∀ (w : List (Fin 2)) (i : Fin 2),
      matcherOps.faulted ((run matcherOps flagsOps matcherInit flagsInit w).matchers i) = false ∧
        flagsOps.faulted ((run matcherOps flagsOps matcherInit flagsInit w).flags i) = false) :
    PegSeparation.RecognizedByTotalPEG PalPeg.PAL :=
  ScaWindowEncode.pal_in_peg_of_workers matcherEnc flagsEnc (by norm_num) matcherInit flagsInit
    (initCtl matcher) (initCtl flagsW) matcherEnc_init flagsEnc_init hmatch hmiddle hclean hworkers

/-- info: 'PalPeg.ScaWorkerEnc.matcherEnc_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matcherEnc_init

/-- info: 'PalPeg.ScaWorkerEnc.matcherEnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms matcherEnc

/-- info: 'PalPeg.ScaWorkerEnc.flagsEnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flagsEnc

/-- info: 'PalPeg.ScaWorkerEnc.flagsEnc_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flagsEnc_init

/-- info: 'PalPeg.ScaWorkerEnc.pal_in_peg_of_real_workers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pal_in_peg_of_real_workers

end PalPeg.ScaWorkerEnc
